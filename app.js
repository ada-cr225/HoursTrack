/*
 * Hours Clock — offline-first phone app for the Google Sheets hours log.
 *
 * Every tap is saved on the phone first (localStorage) with its own ID and the time it
 * happened, then sent to the sheet. If there is no signal it stays queued and is retried
 * automatically; the server ignores duplicates, so retries can never double-count.
 * The screen is always computed from what the sheet last confirmed plus what is still
 * waiting to sync, so it works the same with or without a connection.
 */
(() => {
  'use strict';

  const VERSION = '1.0.0';
  const TZ = 'Europe/London';
  const KEYS = { cfg: 'hc.cfg', queue: 'hc.queue', failed: 'hc.failed', snap: 'hc.snapshot', prefs: 'hc.prefs', lastTap: 'hc.lastTap' };
  const UNDO_MS = 2 * 60 * 1000;        // the server allows 3 minutes; keep a margin
  const TIMEOUT_MS = 15000;
  const RETRY_MS = 15000;
  const REFRESH_MS = 60000;
  const TAP_LOCK_MS = 1500;             // ignore a second tap this soon after the first
  const REST_MS = 11 * 3600e3;
  const BREAK_MIN_MS = 20 * 60e3;
  const BREAK_WARN_MS = 5.5 * 3600e3;
  const BREAK_DUE_MS = 6 * 3600e3;
  const WINDOW = { from: 7 * 60, to: 22 * 60 }; // timeline span (07:00–22:00 London), matches the labels

  /* ---------------- storage ---------------- */

  let storageBroken = false;
  const store = {
    get(k, fallback) {
      try { const v = localStorage.getItem(k); return v == null ? fallback : JSON.parse(v); } catch (e) { return fallback; }
    },
    set(k, v) {
      try { localStorage.setItem(k, JSON.stringify(v)); return true; } catch (e) { storageBroken = true; return false; }
    },
  };
  // Probe once: Safari private mode and full storage both throw on write.
  try { localStorage.setItem('hc.probe', '1'); localStorage.removeItem('hc.probe'); } catch (e) { storageBroken = true; }
  if (navigator.storage && navigator.storage.persist) navigator.storage.persist().catch(() => {});

  let cfg = store.get(KEYS.cfg, null);
  let prefs = Object.assign({ location: 'Office', target: 8 }, store.get(KEYS.prefs, {}));
  let queue = store.get(KEYS.queue, []);
  let failed = store.get(KEYS.failed, []);
  let snap = store.get(KEYS.snap, null);           // last overview the server confirmed
  let lastTap = store.get(KEYS.lastTap, null);     // { id, ts, action } for undo

  const saveQueue = () => store.set(KEYS.queue, queue);
  const saveFailed = () => store.set(KEYS.failed, failed);

  /* ---------------- time helpers (always London time) ---------------- */

  const partsFmt = new Intl.DateTimeFormat('en-GB', {
    timeZone: TZ, year: 'numeric', month: '2-digit', day: '2-digit',
    hour: '2-digit', minute: '2-digit', second: '2-digit', hourCycle: 'h23',
  });
  function parts(ms) {
    const o = {};
    partsFmt.formatToParts(new Date(ms)).forEach(p => { o[p.type] = p.value; });
    return { y: +o.year, mo: +o.month, d: +o.day, h: +o.hour, mi: +o.minute, s: +o.second };
  }
  const two = n => String(n).padStart(2, '0');
  const dayKey = ms => { const p = parts(ms); return p.y + '-' + two(p.mo) + '-' + two(p.d); };
  const hm = ms => { const p = parts(ms); return two(p.h) + ':' + two(p.mi); };
  const minuteOfDay = ms => { const p = parts(ms); return p.h * 60 + p.mi + p.s / 60; };
  const clock = ms => {
    const s = Math.max(0, Math.floor(ms / 1000));
    return Math.floor(s / 3600) + ':' + two(Math.floor(s % 3600 / 60)) + ':' + two(s % 60);
  };
  const hours = ms => { const m = Math.round(ms / 60000); return Math.floor(m / 60) + 'h ' + two(m % 60) + 'm'; };

  /** Converts a London wall-clock date and time to epoch ms, whatever the phone's time zone. */
  function londonToEpoch(dateStr, timeStr) {
    const [y, mo, d] = dateStr.split('-').map(Number);
    const [h, mi] = timeStr.split(':').map(Number);
    const guess = Date.UTC(y, mo - 1, d, h, mi);
    const offset = ms => { const p = parts(ms); return Date.UTC(p.y, p.mo - 1, p.d, p.h, p.mi, p.s) - ms; };
    let ms = guess - offset(guess);
    ms = guess - offset(ms);
    return ms;
  }

  function uuid() {
    if (window.crypto && crypto.randomUUID) return crypto.randomUUID();
    const b = crypto.getRandomValues(new Uint8Array(16));
    b[6] = (b[6] & 0x0f) | 0x40; b[8] = (b[8] & 0x3f) | 0x80;
    const h = [...b].map(x => x.toString(16).padStart(2, '0')).join('');
    return h.slice(0, 8) + '-' + h.slice(8, 12) + '-' + h.slice(12, 16) + '-' + h.slice(16, 20) + '-' + h.slice(20);
  }

  const esc = s => String(s == null ? '' : s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));

  /* ---------------- the day model ---------------- */

  /** Same rules as the server: stray duplicate taps are ignored. */
  function computeDay(events, now) {
    let start = null, finish = null, since = null, lastOut = null, location = '';
    let working = false, breakMs = 0, workedMs = 0, longestBreak = 0;
    const segments = [];
    events.forEach(e => {
      if (e.action === 'IN') {
        if (working) return;
        if (start === null) start = e.ts;
        if (lastOut !== null) { const gap = e.ts - lastOut; breakMs += gap; longestBreak = Math.max(longestBreak, gap); }
        lastOut = null; working = true; since = e.ts;
        if (e.location) location = e.location;
      } else if (e.action === 'OUT') {
        if (!working) return;
        workedMs += e.ts - since;
        segments.push({ from: since, to: e.ts });
        finish = e.ts; lastOut = e.ts; working = false; since = null;
      }
    });
    if (working) {
      finish = null;
      workedMs += Math.max(0, now - since);
      segments.push({ from: since, to: now, live: true });
    }
    return { start, finish, since, working, breakMs, workedMs, longestBreak, location, segments, lastOut };
  }

  /** What the sheet confirmed for today, plus anything still waiting to sync. */
  function model(now = Date.now()) {
    const today = dayKey(now);
    const voided = new Set(queue.filter(q => q.op === 'void').map(q => q.target));
    const confirmed = (snap && snap.date === today ? snap.events : [])
      .filter(e => !voided.has(e.id))
      .map(e => Object.assign({}, e, { pending: false }));
    const known = new Set(confirmed.map(e => e.id));
    const pending = queue
      .filter(q => q.op === 'event' && dayKey(q.ts) === today && !known.has(q.id))
      .map(q => ({ id: q.id, ts: q.ts, action: q.action, location: q.loc || '', note: q.note || '', source: q.manual ? 'manual' : 'app', pending: true }));
    const events = confirmed.concat(pending).sort((a, b) => a.ts - b.ts);
    return Object.assign({ today, events }, computeDay(events, now));
  }

  /* ---------------- network ---------------- */

  class ApiError extends Error {
    constructor(message, kind) { super(message); this.kind = kind; }
  }

  async function api(params) {
    if (!cfg) throw new ApiError('Not set up yet.', 'setup');
    const q = new URLSearchParams(Object.assign({}, params, { k: cfg.key }));
    const ctl = new AbortController();
    const timer = setTimeout(() => ctl.abort(), TIMEOUT_MS);
    let text;
    try {
      const resp = await fetch(cfg.url + '?' + q.toString(), { cache: 'no-store', redirect: 'follow', signal: ctl.signal });
      text = await resp.text();
    } catch (e) {
      throw new ApiError(navigator.onLine === false ? 'No internet connection' : 'Couldn\'t reach Google', 'network');
    } finally {
      clearTimeout(timer);
    }
    try {
      return JSON.parse(text);
    } catch (e) {
      throw new ApiError('Google returned a web page instead of data. Check the deployment is set to "Anyone" and the URL ends in /exec.', 'config');
    }
  }

  function paramsFor(item) {
    if (item.op === 'void') return { api: 'void', id: item.id, target: item.target, ts: String(item.ts) };
    const p = { api: 'event', id: item.id, action: item.action, ts: String(item.ts) };
    if (item.loc) p.loc = item.loc;
    if (item.note) p.note = item.note;
    if (item.manual) p.manual = '1';
    return p;
  }

  let syncing = false;
  let inflightId = null;
  let syncState = { kind: snap ? 'ok' : 'idle', message: '', at: snap ? snap.receivedAt : 0 };
  let lastRefresh = 0;

  function applySnapshot(res) {
    if (!res || !Array.isArray(res.events)) return;
    // event/void/overview responses carry the full overview; plain state responses don't.
    snap = Object.assign({}, snap || {}, res, { receivedAt: Date.now() });
    store.set(KEYS.snap, snap);
    lastRefresh = Date.now();
  }

  function setSync(kind, message) {
    syncState = { kind, message: message || '', at: Date.now() };
    renderSync();
  }

  async function sync() {
    if (syncing || !cfg) return;
    syncing = true;
    setSync('syncing');
    let rerun = false;
    try {
      while (queue.length) {
        const item = queue[0];
        inflightId = item.id;
        let res;
        try {
          res = await api(paramsFor(item));
        } catch (e) {
          setSync(e.kind === 'network' ? 'offline' : 'error', e.message);
          return;
        } finally {
          inflightId = null;
        }
        if (res.ok) {
          queue = queue.filter(q => q.id !== item.id);
          saveQueue();
          applySnapshot(res);
          continue;
        }
        if (res.code === 'auth') { setSync('auth', res.error); return; }
        if (res.code === 'rejected') {
          queue = queue.filter(q => q.id !== item.id && !(item.op === 'event' && q.op === 'void' && q.target === item.id));
          failed.push(Object.assign({}, item, { error: res.error, failedAt: Date.now() }));
          saveQueue(); saveFailed();
          continue;
        }
        setSync('error', res.error || 'The sheet reported an error. Retrying.');
        return;
      }

      let res;
      try {
        res = await api({ api: 'overview' });
      } catch (e) {
        setSync(e.kind === 'network' ? 'offline' : 'error', e.message);
        return;
      }
      if (res.ok) { applySnapshot(res); setSync('ok'); }
      else if (res.code === 'auth') setSync('auth', res.error);
      else setSync('error', res.error);
    } finally {
      syncing = false;
      rerun = queue.length > 0 && (syncState.kind === 'ok' || syncState.kind === 'syncing');
      renderAll();
      if (rerun) setTimeout(sync, 0); // something was tapped while we were busy
    }
  }

  /* ---------------- actions ---------------- */

  function enqueue(item) {
    queue.push(item);
    const saved = saveQueue();
    renderAll();
    sync();
    return saved;
  }

  let tapLockedUntil = 0;
  function onToggle() {
    const now = Date.now();
    if (now < tapLockedUntil) return;
    tapLockedUntil = now + TAP_LOCK_MS;
    flashDisable($('toggle'), TAP_LOCK_MS);

    const m = model(now);
    const action = m.working ? 'OUT' : 'IN';

    if (action === 'IN' && m.events.length === 0 && snap && snap.prevFinish && now - snap.prevFinish < REST_MS) {
      const ok = window.confirm('It\'s less than 11 hours since you finished at ' + hm(snap.prevFinish) +
        '. You\'re entitled to 11 hours\' rest. Clock in anyway?\n\n(If you were asked to start, clock in so it\'s recorded.)');
      if (!ok) return;
    }

    const item = { op: 'event', id: uuid(), action, ts: now, loc: action === 'IN' ? prefs.location : '' };
    enqueue(item);
    lastTap = { id: item.id, ts: now, action };
    store.set(KEYS.lastTap, lastTap);
    if (navigator.vibrate) navigator.vibrate(15);
    showToast();
  }

  function onUndo() {
    if (!lastTap || Date.now() - lastTap.ts > UNDO_MS) { hideToast(); return; }
    const target = lastTap.id;
    const waiting = queue.some(q => q.id === target);
    if (waiting && inflightId !== target) {
      queue = queue.filter(q => q.id !== target && !(q.op === 'void' && q.target === target));
      saveQueue();
    } else {
      enqueue({ op: 'void', id: uuid(), target, ts: Date.now() });
    }
    lastTap = null;
    store.set(KEYS.lastTap, null);
    hideToast();
    renderAll();
    sync();
  }

  function onNote() {
    const input = $('noteText');
    const text = input.value.trim();
    if (!text) return;
    enqueue({ op: 'event', id: uuid(), action: 'NOTE', ts: Date.now(), note: text.slice(0, 300) });
    input.value = '';
    input.blur();
  }

  function onManual() {
    const err = $('mErr');
    err.textContent = '';
    const d = $('mDate').value, t = $('mTime').value, action = $('mAction').value, reason = $('mReason').value.trim();
    if (!d || !t) { err.textContent = 'Choose a date and time.'; return; }
    if (!reason) { err.textContent = 'Add a short reason — it is recorded in your log.'; return; }
    const ts = londonToEpoch(d, t);
    if (ts > Date.now() + 60000) { err.textContent = 'That time is in the future.'; return; }
    enqueue({ op: 'event', id: uuid(), action, ts, loc: action === 'IN' ? prefs.location : '', note: reason.slice(0, 200), manual: true });
    $('mReason').value = '';
    $('manualBox').open = false;
  }

  /* ---------------- rendering ---------------- */

  const $ = id => document.getElementById(id);

  function flashDisable(el, ms) {
    el.disabled = true;
    setTimeout(() => { el.disabled = false; }, ms);
  }

  function renderSync() {
    const pill = $('syncPill'), text = $('syncText');
    const waiting = queue.length;
    pill.className = 'pill';
    if (!cfg) { text.textContent = 'Not set up'; return; }
    if (failed.length) { pill.classList.add('bad'); text.textContent = failed.length + ' not recorded'; return; }
    switch (syncState.kind) {
      case 'syncing':
        pill.classList.add('wait'); text.textContent = waiting ? 'Syncing ' + waiting + '…' : 'Updating…'; break;
      case 'offline':
        pill.classList.add('wait'); text.textContent = waiting ? 'Offline · ' + waiting + ' saved on phone' : 'Offline'; break;
      case 'auth':
        pill.classList.add('bad'); text.textContent = 'Key rejected'; break;
      case 'error':
        pill.classList.add(waiting ? 'wait' : 'bad'); text.textContent = waiting ? waiting + ' waiting · retrying' : 'Sync problem'; break;
      default:
        if (waiting) { pill.classList.add('wait'); text.textContent = waiting + ' waiting'; }
        else { pill.classList.add('ok'); text.textContent = 'Synced' + (snap && snap.receivedAt ? ' ' + hm(snap.receivedAt) : ''); }
    }
  }

  function renderBanners(m, now) {
    const out = [];
    if (storageBroken) {
      out.push(['bad', 'This phone isn\'t letting the app save data', 'Taps can\'t be kept if you lose signal. Turn off Private Browsing and open the app from your Home Screen.']);
    }
    if (navigator.standalone === false) {
      out.push(['info', 'Add this app to your Home Screen', 'In Safari tap Share › Add to Home Screen, then use the icon. Set it up there — it keeps its own storage.']);
    }
    if (syncState.kind === 'auth') {
      out.push(['bad', 'Your access key was rejected', 'Taps are being kept on your phone. Update the key in Settings to send them.']);
    } else if (syncState.kind === 'error' && syncState.message) {
      out.push(['warn', 'The sheet couldn\'t take your last change', syncState.message + ' Your taps are saved on this phone and will be retried.']);
    }
    if (m.working && m.longestBreak < BREAK_MIN_MS) {
      if (m.workedMs >= BREAK_DUE_MS) {
        out.push(['bad', 'Break due', 'You\'ve worked ' + hours(m.workedMs) + ' today without a 20-minute break. Over 6 hours, you\'re entitled to one.']);
      } else if (m.workedMs >= BREAK_WARN_MS) {
        out.push(['warn', 'Break coming up', 'At 6 hours you\'re entitled to a 20-minute uninterrupted break.']);
      }
    }
    if (!m.working && m.finish) {
      out.push(['info', 'Rest period', 'With 11 hours\' rest, your earliest next start is ' + hm(m.finish + REST_MS) + (dayKey(m.finish + REST_MS) !== m.today ? ' tomorrow.' : '.')]);
    } else if (!m.working && !m.events.length && snap && snap.prevFinish && now - snap.prevFinish < REST_MS) {
      out.push(['warn', 'Still in your rest period', 'You finished at ' + hm(snap.prevFinish) + '. 11 hours\' rest ends at ' + hm(snap.prevFinish + REST_MS) + '.']);
    }
    const html = out.map(([k, t, b]) => '<div class="banner ' + k + '"><div><strong>' + esc(t) + '</strong>' + esc(b) + '</div></div>').join('');
    const el = $('banners');
    if (el.dataset.html !== html) { el.innerHTML = html; el.dataset.html = html; }
  }

  function renderTick() {
    if (!cfg) return;
    const now = Date.now();
    const m = model(now);

    const st = $('status');
    st.className = 'status' + (m.working ? ' working' : m.start !== null ? ' paused' : '');
    $('statusText').textContent = m.working ? 'Working since ' + hm(m.since) : m.start !== null ? 'Clocked out' : 'Not clocked in today';
    $('timer').textContent = clock(m.workedMs);

    const bits = [];
    if (m.start !== null) bits.push('Started ' + hm(m.start));
    if (m.breakMs >= 60000) bits.push('Breaks ' + Math.round(m.breakMs / 60000) + 'm');
    if (m.location) bits.push(m.location);
    $('detail').textContent = bits.length ? bits.join(' · ') : 'Tap below when you start work';

    const target = Math.max(1, Number(prefs.target) || 8) * 3600e3;
    const pct = Math.min(100, (m.workedMs / target) * 100);
    const tb = $('targetBar');
    tb.className = 'bar' + (m.workedMs > target ? ' warn' : '');
    tb.firstElementChild.style.width = pct.toFixed(1) + '%';
    $('targetLeft').textContent = hours(m.workedMs) + ' of ' + (target / 3600e3) + 'h target';
    $('targetRight').textContent = m.workedMs > target ? '+' + hours(m.workedMs - target) + ' over' : '';

    const span = WINDOW.to - WINDOW.from;
    const pos = ms => Math.max(0, Math.min(100, (minuteOfDay(ms) - WINDOW.from) / span * 100));
    let tl = '';
    for (let h = 10; h < 22; h += 3) tl += '<b style="left:' + ((h * 60 - WINDOW.from) / span * 100).toFixed(2) + '%"></b>';
    m.segments.forEach(s => {
      const a = pos(s.from), b = pos(s.to);
      tl += '<i class="' + (s.live ? 'live' : '') + '" style="left:' + a.toFixed(2) + '%;width:' + Math.max(0.6, b - a).toFixed(2) + '%"></i>';
    });
    $('timeline').innerHTML = tl;

    const btn = $('toggle');
    btn.textContent = m.working ? 'Clock out / pause' : m.start !== null ? 'Resume work' : 'Clock in';
    btn.classList.toggle('stop', m.working);

    document.querySelectorAll('.seg button').forEach(b => b.classList.toggle('on', b.dataset.loc === prefs.location));

    renderBanners(m, now);
    renderToast(now);
  }

  function renderTaps() {
    const m = model();
    const el = $('taps');
    if (!m.events.length) { el.innerHTML = '<li class="empty">No taps yet today.</li>'; return; }
    el.innerHTML = m.events.slice().reverse().map(e => {
      const label = e.action === 'IN' ? 'Clocked in' + (e.location ? ' · ' + e.location : '')
        : e.action === 'OUT' ? 'Clocked out' : e.note;
      const tags = [];
      if (e.pending) tags.push('<span class="chip wait">on phone</span>');
      if (e.source === 'manual') tags.push('<span class="chip muted">manual</span>');
      if (e.source === 'app-offline') tags.push('<span class="chip muted">synced late</span>');
      return '<li><span class="t num">' + hm(e.ts) + '</span><span class="grow">' + esc(label) + '</span>' + tags.join('') + '</li>';
    }).join('');
  }

  function renderMonth() {
    const el = $('month');
    const mo = snap && snap.month;
    if (!mo) {
      el.innerHTML = '<p class="empty">Open the app with signal to load this month\'s pay check.</p>';
      return;
    }
    const title = new Intl.DateTimeFormat('en-GB', { month: 'long', year: 'numeric', timeZone: TZ }).format(new Date(mo.month + '-15T12:00:00Z'));
    $('monthTitle').textContent = title;
    const hrs = mo.hours || 0, max = mo.maxHours || 0;
    const pct = max ? Math.min(100, hrs / max * 100) : 0;
    const under = mo.status === 'UNDERPAID';
    const cls = under ? 'bad' : pct > 85 ? 'warn' : '';
    const pendingEvents = queue.filter(q => q.op === 'event').length;
    el.innerHTML =
      '<div class="kv"><span>Hours worked</span><b class="num">' + hrs.toFixed(1) + ' h</b></div>' +
      '<div style="margin-top:10px"><div class="bar ' + cls + '"><i style="width:' + pct.toFixed(1) + '%"></i></div>' +
      '<div class="barlabel"><span>' + (max ? (Math.max(0, max - hrs)).toFixed(1) + ' h left before pay drops below minimum wage' : '') + '</span></div></div>' +
      '<div class="kv"><span>Effective rate</span><b class="num">' + (mo.rate ? '£' + mo.rate.toFixed(2) + '/h' : '—') + '</b></div>' +
      '<div class="kv"><span>Minimum wage</span><span class="num">' + (mo.minimumWage ? '£' + mo.minimumWage.toFixed(2) + '/h' : '—') + '</span></div>' +
      '<div class="kv"><span>Status</span><span class="chip ' + (under ? 'bad' : mo.status === 'OK' ? 'ok' : 'muted') + '">' + esc(mo.status || '—') + '</span></div>' +
      (under && mo.shortfall ? '<div class="kv"><span>Shortfall</span><b class="num" style="color:var(--out)">£' + mo.shortfall.toFixed(2) + '</b></div>' : '') +
      '<p class="note">From your sheet' + (snap.receivedAt ? ', updated ' + hm(snap.receivedAt) : '') +
      '. Counts finished days; today is added when you clock out.' +
      (pendingEvents ? ' ' + pendingEvents + ' tap' + (pendingEvents > 1 ? 's' : '') + ' still on your phone aren\'t included yet.' : '') + '</p>';
  }

  function renderHistory() {
    const el = $('history');
    const days = snap && snap.days;
    if (!days || !days.length) { el.innerHTML = '<p class="empty">Nothing to show yet.</p>'; return; }
    el.innerHTML = '<table class="hist">' + days.map(d => {
      const span = d.start ? esc(d.start) + '–' + esc(d.finish || '…') : '<span class="empty">—</span>';
      return '<tr><td>' + esc(d.day) + ' ' + esc(d.date) +
        (d.flags ? '<span class="flag">' + esc(d.flags) + '</span>' : '') + '</td>' +
        '<td>' + span + '</td><td class="r num">' + (d.hours ? esc(d.hours) + ' h' : '') + '</td></tr>';
    }).join('') + '</table>' +
      (snap.receivedAt ? '<p class="note">From your sheet, updated ' + hm(snap.receivedAt) + '.</p>' : '');
  }

  function renderFailed() {
    const card = $('failedCard');
    card.classList.toggle('hidden', !failed.length);
    if (!failed.length) return;
    $('failed').innerHTML = failed.map((f, i) => {
      const what = f.op === 'void' ? 'Undo' : f.action === 'IN' ? 'Clock-in' : f.action === 'OUT' ? 'Clock-out' : 'Note';
      const when = new Intl.DateTimeFormat('en-GB', { timeZone: TZ, day: 'numeric', month: 'short', hour: '2-digit', minute: '2-digit', hourCycle: 'h23' }).format(new Date(f.ts));
      return '<li><span class="grow"><b>' + esc(what) + ' · ' + esc(when) + '</b><br><span class="sub">' + esc(f.error) + '</span></span>' +
        '<button class="btn ghost small" data-dismiss="' + i + '" type="button">Dismiss</button></li>';
    }).join('');
  }

  function renderToast(now) {
    const live = lastTap && now - lastTap.ts < UNDO_MS;
    const t = $('toast');
    if (!live) { t.classList.add('hidden'); return; }
    t.classList.remove('hidden');
    const left = Math.ceil((UNDO_MS - (now - lastTap.ts)) / 1000);
    const what = lastTap.action === 'IN' ? 'Clocked in' : 'Clocked out';
    $('toastText').textContent = what + ' at ' + hm(lastTap.ts) + ' · undo ' + Math.floor(left / 60) + ':' + two(left % 60);
  }
  function showToast() { renderToast(Date.now()); }
  function hideToast() { $('toast').classList.add('hidden'); }

  function renderSettings() {
    $('target').value = prefs.target;
    if (cfg) $('fallback').href = cfg.url + '?k=' + encodeURIComponent(cfg.key);
    $('about').textContent = 'Version ' + VERSION + '. Taps are saved on this phone first and sent to your sheet when there is signal.';
  }

  function renderAll() {
    $('setup').classList.toggle('hidden', !!cfg && !setupOpen);
    $('main').classList.toggle('hidden', !cfg || setupOpen);
    renderSync();
    if (!cfg) return;
    renderTick();
    renderTaps();
    renderMonth();
    renderHistory();
    renderFailed();
    renderSettings();
  }

  /* ---------------- setup ---------------- */

  let setupOpen = false;
  const URL_RE = /^https:\/\/script\.google\.com\/(a\/[^/]+\/)?macros\/s\/[A-Za-z0-9_-]+\/exec$/;
  const KEY_RE = /^[0-9a-f]{64}$/;

  function readSetup() {
    const url = $('setupUrl').value.trim().split('?')[0].replace(/\/+$/, '');
    const key = $('setupKey').value.trim().replace(/^\?k=|^k=/, '');
    if (!URL_RE.test(url)) return { error: 'That doesn\'t look like a web app URL. It should start with https://script.google.com/macros/s/ and end in /exec.' };
    if (!KEY_RE.test(key)) return { error: 'The access key should be 64 characters of 0–9 and a–f, without "?k=".' };
    return { url, key };
  }

  async function onConnect() {
    const err = $('setupErr');
    err.textContent = '';
    $('setupForce').classList.add('hidden');
    const c = readSetup();
    if (c.error) { err.textContent = c.error; return; }
    const prev = cfg;
    cfg = c;
    $('setupConnect').disabled = true;
    try {
      const res = await api({ api: 'overview' });
      if (!res.ok) {
        cfg = prev;
        err.textContent = res.code === 'auth' ? 'The sheet rejected that access key.' : (res.error || 'The sheet returned an error.');
        return;
      }
      store.set(KEYS.cfg, cfg);
      applySnapshot(res);
      setSync('ok');
      setupOpen = false;
      renderAll();
      sync();
    } catch (e) {
      cfg = prev;
      err.textContent = e.message;
      if (e.kind === 'network') $('setupForce').classList.remove('hidden');
    } finally {
      $('setupConnect').disabled = false;
    }
  }

  function onForceSave() {
    const c = readSetup();
    if (c.error) { $('setupErr').textContent = c.error; return; }
    cfg = c;
    store.set(KEYS.cfg, cfg);
    setupOpen = false;
    renderAll();
  }

  function openSetup() {
    setupOpen = true;
    $('setupUrl').value = cfg ? cfg.url : '';
    $('setupKey').value = cfg ? cfg.key : '';
    $('setupCancel').classList.toggle('hidden', !cfg);
    $('setupErr').textContent = '';
    renderAll();
    window.scrollTo(0, 0);
  }

  /* ---------------- backup ---------------- */

  async function onBackup() {
    const pending = queue.map(q => ({
      what: q.op === 'void' ? 'undo' : q.action, time: new Date(q.ts).toISOString(), london: dayKey(q.ts) + ' ' + hm(q.ts),
      location: q.loc || '', note: q.note || '', manual: !!q.manual, id: q.id,
    }));
    const text = pending.length ? JSON.stringify(pending, null, 2) : 'No taps are waiting to sync.';
    try {
      await navigator.clipboard.writeText(text);
      alert(pending.length ? pending.length + ' waiting tap(s) copied. Paste them into a note or email to keep a copy.' : text);
    } catch (e) {
      prompt('Copy this:', text);
    }
  }

  /* ---------------- wiring ---------------- */

  function wire() {
    $('toggle').addEventListener('click', onToggle);
    $('toastUndo').addEventListener('click', onUndo);
    $('noteAdd').addEventListener('click', onNote);
    $('noteText').addEventListener('keydown', e => { if (e.key === 'Enter') onNote(); });
    $('mAdd').addEventListener('click', onManual);
    $('syncPill').addEventListener('click', () => sync());
    $('syncNow').addEventListener('click', () => sync());
    $('backup').addEventListener('click', onBackup);
    $('reconnect').addEventListener('click', openSetup);
    $('setupConnect').addEventListener('click', onConnect);
    $('setupForce').addEventListener('click', onForceSave);
    $('setupCancel').addEventListener('click', () => { setupOpen = false; renderAll(); });
    $('target').addEventListener('change', e => {
      const v = Math.min(16, Math.max(1, Number(e.target.value) || 8));
      prefs.target = v; store.set(KEYS.prefs, prefs); renderTick();
    });
    document.querySelectorAll('.seg button').forEach(b => b.addEventListener('click', () => {
      prefs.location = b.dataset.loc; store.set(KEYS.prefs, prefs); renderTick();
    }));
    $('failed').addEventListener('click', e => {
      const i = e.target.getAttribute('data-dismiss');
      if (i === null) return;
      if (!confirm('Dismiss this? Make sure you\'ve re-entered it first — it is not in your log.')) return;
      failed.splice(Number(i), 1); saveFailed(); renderAll();
    });

    const today = dayKey(Date.now());
    $('mDate').value = today;
    $('mDate').max = today;

    window.addEventListener('online', () => sync());
    document.addEventListener('visibilitychange', () => { if (!document.hidden) { renderAll(); sync(); } });
    window.addEventListener('pageshow', () => renderAll());
    // Another copy of the app (e.g. a second tab) changed storage: reload our view of it.
    window.addEventListener('storage', () => {
      queue = store.get(KEYS.queue, []); failed = store.get(KEYS.failed, []);
      snap = store.get(KEYS.snap, null); lastTap = store.get(KEYS.lastTap, null);
      renderAll();
    });

    setInterval(() => { if (!document.hidden) renderTick(); }, 1000);
    setInterval(() => {
      if (!cfg || document.hidden) return;
      if (queue.length || Date.now() - lastRefresh > REFRESH_MS) sync();
    }, RETRY_MS);
  }

  if ('serviceWorker' in navigator) {
    navigator.serviceWorker.register('sw.js').catch(() => {});
  }

  wire();
  if (!cfg) openSetup();
  renderAll();
  sync();

  // Exposed for automated tests only.
  window.__hoursClock = { computeDay, model, londonToEpoch, dayKey, get queue() { return queue; }, get failed() { return failed; }, sync };
})();
