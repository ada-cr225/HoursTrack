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

  const VERSION = '1.5.0';
  const TZ = 'Europe/London';
  const KEYS = { cfg: 'hc.cfg', queue: 'hc.queue', failed: 'hc.failed', snap: 'hc.snapshot', prefs: 'hc.prefs', lastTap: 'hc.lastTap', cal: 'hc.calendar', pay: 'hc.payments', leave: 'hc.leave', docs: 'hc.docs', docCache: 'hc.docCache' };
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

  /** POST (used for file uploads). text/plain keeps it a "simple" request, so no CORS preflight. */
  async function apiPost(body) {
    if (!cfg) throw new ApiError('Not set up yet.', 'setup');
    const ctl = new AbortController();
    const timer = setTimeout(() => ctl.abort(), 90000); // reading a payslip can take a while
    let text;
    try {
      const resp = await fetch(cfg.url, {
        method: 'POST', cache: 'no-store', redirect: 'follow', signal: ctl.signal,
        headers: { 'Content-Type': 'text/plain;charset=utf-8' },
        body: JSON.stringify(Object.assign({}, body, { k: cfg.key })),
      });
      text = await resp.text();
    } catch (e) {
      throw new ApiError(navigator.onLine === false ? 'No internet connection' : 'Couldn\'t reach Google', 'network');
    } finally {
      clearTimeout(timer);
    }
    try { return JSON.parse(text); } catch (e) {
      throw new ApiError('Google returned a web page instead of data. Check the deployment is set to "Anyone".', 'config');
    }
  }

  /* Files waiting to upload live in IndexedDB (localStorage is too small for PDFs and photos). */
  const fileStore = (() => {
    let dbp = null;
    const open = () => dbp || (dbp = new Promise((res, rej) => {
      if (!('indexedDB' in window)) return rej(new Error('This phone can\'t store files offline.'));
      const r = indexedDB.open('hours-clock-files', 1);
      r.onupgradeneeded = () => r.result.createObjectStore('files');
      r.onsuccess = () => res(r.result);
      r.onerror = () => rej(r.error || new Error('Couldn\'t open file storage.'));
    }));
    const tx = async (mode, fn) => {
      const db = await open();
      return new Promise((res, rej) => {
        const t = db.transaction('files', mode);
        const req = fn(t.objectStore('files'));
        t.oncomplete = () => res(req && req.result);
        t.onerror = () => rej(t.error || new Error('File storage error.'));
        t.onabort = () => rej(t.error || new Error('File storage was full or blocked.'));
      });
    };
    return {
      put: (id, blob) => tx('readwrite', st => st.put(blob, id)),
      get: id => tx('readonly', st => st.get(id)),
      del: id => tx('readwrite', st => st.delete(id)).catch(() => {}),
    };
  })();

  const blobToBase64 = blob => new Promise((res, rej) => {
    const r = new FileReader();
    r.onload = () => res(String(r.result).split(',')[1] || '');
    r.onerror = () => rej(r.error || new Error('Couldn\'t read the file.'));
    r.readAsDataURL(blob);
  });

  function paramsFor(item) {
    if (item.op === 'void') return { api: 'void', id: item.id, target: item.target, ts: String(item.ts) };
    if (item.op === 'paymentDelete') return { api: 'paymentDelete', id: item.id };
    if (item.op === 'leaveDelete') return { api: 'leaveDelete', id: item.id };
    if (item.op === 'leave') {
      const p = { api: 'leaveSave', id: item.id };
      Object.keys(item.fields).forEach(k => { if (item.fields[k] !== '' && item.fields[k] != null) p[k] = String(item.fields[k]); });
      return p;
    }
    if (item.op === 'payment') {
      const p = { api: 'payment', id: item.id };
      Object.keys(item.fields).forEach(k => { if (item.fields[k] !== '' && item.fields[k] != null) p[k] = String(item.fields[k]); });
      return p;
    }
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

  let syncAgain = false;
  async function sync() {
    if (!cfg) return;
    if (syncing) { syncAgain = true; return; } // e.g. signal came back mid-attempt: run again as soon as this one ends
    syncing = true;
    syncAgain = false;
    setSync('syncing');
    let rerun = false;
    try {
      while (queue.length) {
        const item = queue[0];
        inflightId = item.id;
        let res;
        try {
          if (item.op === 'upload') {
            let blob;
            try { blob = await fileStore.get(item.fileKey); } catch (e) { blob = null; }
            if (!blob) {
              res = { ok: false, code: 'rejected', error: 'The file is no longer on this phone. Upload it again.' };
            } else {
              res = await apiPost({ api: item.api || 'upload', id: item.id, filename: item.filename, mimeType: item.mime, data: await blobToBase64(blob) });
            }
          } else {
            res = await api(paramsFor(item));
          }
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
          if (res.payments) applyPayments(res);
          if (res.allowance !== undefined && res.entries) { applyLeave(res); lastCalLoad = 0; }
          if (item.op === 'upload' && item.api === 'docUpload') { await onDocUploaded(item, res); }
          else if (item.op === 'upload') { fileStore.del(item.fileKey); onUploadDone(item, res); }
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
      if (res.ok) {
        applySnapshot(res); setSync('ok');
        if (view === 'calendar') loadCalendar(false);
        if (view === 'pay') loadPayments(false);
        if (view === 'leave') loadLeave(false);
        if (view === 'docs' || Date.now() - lastDocsLoad > 6 * 3600e3) loadDocs(false); // keeps offline copies fresh
      }
      else if (res.code === 'auth') setSync('auth', res.error);
      else setSync('error', res.error);
    } finally {
      syncing = false;
      rerun = syncAgain || (queue.length > 0 && (syncState.kind === 'ok' || syncState.kind === 'syncing'));
      syncAgain = false;
      renderAll();
      if (rerun) setTimeout(sync, 0); // something was tapped, or signal returned, while we were busy
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
    if (snap && snap.leave && snap.leave.today && snap.date === m.today) {
      const t = snap.leave.today;
      out.push(['info', 'On ' + t.type.toLowerCase() + ' today' + (t.partFrom ? ' (' + t.partFrom + '–' + t.partTo + ')' : ''),
        'If you\'re asked to work anyway, clock in so it\'s recorded — and note who asked.']);
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

  function tapItem(e) {
    const label = e.action === 'IN' ? 'Clocked in' + (e.location ? ' · ' + e.location : '')
      : e.action === 'OUT' ? 'Clocked out' : e.note;
    const tags = [];
    if (e.pending) tags.push('<span class="chip wait">on phone</span>');
    if (e.source === 'manual') tags.push('<span class="chip muted">manual</span>');
    if (e.source === 'app-offline') tags.push('<span class="chip muted">synced late</span>');
    return '<li><span class="t num">' + hm(e.ts) + '</span><span class="grow">' + esc(label) + '</span>' + tags.join('') + '</li>';
  }

  function renderTaps() {
    const m = model();
    const el = $('taps');
    if (!m.events.length) { el.innerHTML = '<li class="empty">No taps yet today.</li>'; return; }
    el.innerHTML = m.events.slice().reverse().map(tapItem).join('');
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
      (mo.leavePay ? '<div class="kv"><span>Paid leave left out of the check</span><span class="num">£' + mo.leavePay.toFixed(2) + '</span></div>' : '') +
      (snap.leave ? '<div class="kv"><span>Holiday left</span><span class="num">' + nDays(snap.leave.remaining) + ' days (' + nDays(snap.leave.availableNow) + ' bookable now)</span></div>' +
        (snap.leave.next ? '<div class="kv"><span>Next</span><span>' + esc(snap.leave.next.type) + ' ' + esc(dShort(snap.leave.next.from)) + (snap.leave.next.to !== snap.leave.next.from ? ' – ' + esc(dShort(snap.leave.next.to)) : '') + '</span></div>' : '') : '') +
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
      const what = f.op === 'void' ? 'Undo' : f.op === 'upload' ? (f.api === 'docUpload' ? 'Document upload (' : 'Payslip upload (') + (f.filename || 'file') + ')'
        : f.op === 'payment' ? 'Payment' : f.op === 'paymentDelete' ? 'Payment removal'
        : f.op === 'leave' ? 'Leave (' + (f.fields.type || '') + ' ' + (f.fields.from || '') + ')' : f.op === 'leaveDelete' ? 'Leave removal'
        : f.action === 'IN' ? 'Clock-in' : f.action === 'OUT' ? 'Clock-out' : 'Note';
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

  let contractDirty = false;

  function renderContract() {
    const st = snap && snap.settings;
    if (st && !contractDirty) {
      $('cStart').value = st.start || '';
      $('cEnd').value = st.end || '';
      $('cSalary').value = st.salary != null ? st.salary : '';
    }
    const box = $('mw');
    if (!st) { box.innerHTML = '<p class="empty">Open with signal to load your contract settings.</p>'; return; }
    const today = dayKey(Date.now());
    const fmtDay = k => new Intl.DateTimeFormat('en-GB', { day: 'numeric', month: 'short', year: 'numeric', timeZone: 'UTC' }).format(new Date(k + 'T12:00:00Z'));
    const upcoming = (st.rates || []).filter(r => r.from > today);
    const rs = st.rateStatus;
    let status;
    if (!rs) {
      status = '<span style="color:var(--warn)">Not linked to GOV.UK yet. In your sheet, run <b>Hours Clock › Set up minimum wage updates</b> once.</span>';
    } else if (rs.ok) {
      status = 'Confirmed with GOV.UK ' + new Intl.DateTimeFormat('en-GB', { timeZone: TZ, day: 'numeric', month: 'short', hour: '2-digit', minute: '2-digit', hourCycle: 'h23' }).format(new Date(rs.checkedAt)) + '.';
    } else {
      status = '<span style="color:var(--out)">' + esc(rs.message) + '</span>';
    }
    box.innerHTML = '<div class="mwbox">' +
      '<div class="big-rate">' + (st.minimumWage != null ? '£' + st.minimumWage.toFixed(2) + '<span class="sub"> /hour, 21 and over</span>' : '—') + '</div>' +
      (upcoming.length ? '<div class="sub" style="margin-top:4px">' + upcoming.map(r => 'Rises to £' + r.rate.toFixed(2) + ' from ' + esc(fmtDay(r.from))).join('<br>') + '</div>' : '') +
      '<p class="note" style="margin-top:8px">' + status + ' Each month is checked against the rate in force that month. ' +
      '<a href="' + esc(st.rateSource) + '" target="_blank" rel="noopener">Source: GOV.UK</a></p></div>';
  }

  async function onContractSave() {
    const msg = $('cMsg');
    msg.className = 'err'; msg.textContent = '';
    const start = $('cStart').value, end = $('cEnd').value, salary = Number($('cSalary').value);
    if (!start || !end) { msg.textContent = 'Choose a start and end date.'; return; }
    if (end < start) { msg.textContent = 'The end date must be after the start date.'; return; }
    if (!isFinite(salary) || salary < 1000 || salary > 500000) { msg.textContent = 'Enter an annual salary between £1,000 and £500,000.'; return; }
    const st = snap && snap.settings;
    if (st && st.start && st.start !== start) {
      const ok = confirm('Changing the start date moves every row on your Log tab.\n\nYour hours will be rebuilt from your recorded taps. Anything typed directly into the Log tab\'s yellow cells will be cleared. Taps are never deleted.\n\nContinue?');
      if (!ok) return;
    }
    if (queue.length) {
      msg.textContent = 'Sync your waiting taps first (they need signal), then save.';
      sync();
      return;
    }
    const btn = $('cSave');
    btn.disabled = true; btn.textContent = 'Saving…';
    try {
      const res = await api({ api: 'updateSettings', start, end, salary: String(salary) });
      if (!res.ok) { msg.textContent = res.code === 'auth' ? 'Your access key was rejected.' : res.error; return; }
      applySnapshot(res);
      contractDirty = false;
      msg.className = 'okmsg'; msg.textContent = res.message || 'Saved.';
      renderAll();
      loadCalendar(true);
    } catch (e) {
      msg.textContent = e.kind === 'network' ? 'You need signal to change settings. Nothing was changed.' : e.message;
    } finally {
      btn.disabled = false; btn.textContent = 'Save to sheet';
    }
  }

  async function onRateCheck() {
    const btn = $('mwCheck');
    btn.disabled = true; btn.textContent = 'Checking GOV.UK…';
    try {
      const res = await api({ api: 'refreshRate' });
      if (res.ok) { applySnapshot(res); renderAll(); }
      else alert(res.error);
    } catch (e) {
      alert(e.kind === 'network' ? 'You need signal to check GOV.UK.' : e.message);
    } finally {
      btn.disabled = false; btn.textContent = 'Check GOV.UK now';
    }
  }

  function renderSettings() {
    renderContract();
    $('target').value = prefs.target;
    if (cfg) $('fallback').href = cfg.url + '?k=' + encodeURIComponent(cfg.key);
    $('about').textContent = 'Version ' + VERSION + '. Taps are saved on this phone first and sent to your sheet when there is signal.';
  }

  function renderAll() {
    $('setup').classList.toggle('hidden', !!cfg && !setupOpen);
    $('main').classList.toggle('hidden', !cfg || setupOpen);
    $('tabs').classList.toggle('hidden', !cfg || setupOpen);
    $('viewToday').classList.toggle('hidden', view !== 'today');
    $('viewCal').classList.toggle('hidden', view !== 'calendar');
    $('viewPay').classList.toggle('hidden', view !== 'pay');
    $('viewLeave').classList.toggle('hidden', view !== 'leave');
    $('viewDocs').classList.toggle('hidden', view !== 'docs');
    document.querySelectorAll('.tabs button').forEach(b => b.classList.toggle('on', b.dataset.view === view));
    renderSync();
    if (!cfg) return;
    if (view === 'calendar') renderCalendar();
    if (view === 'pay') renderPay();
    if (view === 'leave') renderLeave();
    if (view === 'docs') renderDocs();
    renderTick();
    renderTaps();
    renderMonth();
    renderHistory();
    renderFailed();
    renderSettings();
  }

  /* ---------------- calendar ---------------- */

  let cal = store.get(KEYS.cal, null);
  const VIEWS = ['today', 'calendar', 'pay', 'leave', 'docs'];
  let view = VIEWS.indexOf(prefs.view) >= 0 ? prefs.view : 'today';
  let calMonth = null;   // 'yyyy-MM' being shown
  let calSel = null;     // 'yyyy-MM-dd' selected
  let calErr = '';
  let calLoading = false;
  let lastCalLoad = 0;

  async function loadCalendar(force) {
    if (!cfg || calLoading) return;
    if (!force && Date.now() - lastCalLoad < 30000) return;
    calLoading = true;
    renderCalFresh();
    try {
      const res = await api({ api: 'calendar' });
      if (res.ok) {
        cal = Object.assign({}, res, { receivedAt: Date.now() });
        store.set(KEYS.cal, cal);
        calErr = '';
        lastCalLoad = Date.now();
      } else {
        calErr = res.error || 'The sheet returned an error.';
      }
    } catch (e) {
      calErr = e.message;
    } finally {
      calLoading = false;
      if (view === 'calendar') renderCalendar();
    }
  }

  function shiftMonth(mk, delta) {
    let [y, m] = mk.split('-').map(Number);
    m += delta;
    while (m > 12) { m -= 12; y++; }
    while (m < 1) { m += 12; y--; }
    return y + '-' + two(m);
  }
  const monthName = mk => new Intl.DateTimeFormat('en-GB', { month: 'long', year: 'numeric', timeZone: 'UTC' }).format(new Date(mk + '-15T12:00:00Z'));
  const longDate = key => new Intl.DateTimeFormat('en-GB', { weekday: 'long', day: 'numeric', month: 'long', timeZone: 'UTC' }).format(new Date(key + 'T12:00:00Z'));
  const fmtH = h => (h < 10 ? h.toFixed(1) : String(Math.round(h))) + 'h';

  function calRange(todayKey) {
    const months = (cal && cal.days ? cal.days.map(d => d.date.slice(0, 7)) : []).concat([todayKey.slice(0, 7)]);
    months.sort();
    return { min: months[0], max: months[months.length - 1] };
  }

  function renderCalFresh() {
    const el = $('calFresh');
    if (!el) return;
    if (calLoading) { el.textContent = 'Updating calendar…'; return; }
    const when = cal && cal.receivedAt
      ? new Intl.DateTimeFormat('en-GB', { timeZone: TZ, day: 'numeric', month: 'short', hour: '2-digit', minute: '2-digit', hourCycle: 'h23' }).format(new Date(cal.receivedAt))
      : null;
    el.textContent = calErr
      ? 'Couldn\'t update (' + calErr + ').' + (when ? ' Showing the copy saved ' + when + '.' : '')
      : when ? 'Calendar from your sheet, updated ' + when + '. Today updates live.' : 'Open with signal to load your calendar.';
  }

  function renderCalendar() {
    const now = Date.now();
    const m = model(now);
    const todayKey = m.today;
    if (!calMonth) calMonth = todayKey.slice(0, 7);
    if (!calSel) calSel = todayKey;
    const range = calRange(todayKey);
    if (calMonth < range.min) calMonth = range.min;
    if (calMonth > range.max) calMonth = range.max;

    $('calTitle').textContent = monthName(calMonth);
    $('calPrev').disabled = calMonth <= range.min;
    $('calNext').disabled = calMonth >= range.max;

    const dayMap = {};
    (cal && cal.days ? cal.days : []).forEach(d => { dayMap[d.date] = d; });
    const hoursFor = key => {
      if (key === todayKey) return m.workedMs / 3600e3;
      const d = dayMap[key];
      return d && typeof d.hours === 'number' ? d.hours : 0;
    };

    const [y, mo] = calMonth.split('-').map(Number);
    const firstDow = (new Date(Date.UTC(y, mo - 1, 1)).getUTCDay() + 6) % 7;
    const dim = new Date(Date.UTC(y, mo, 0)).getUTCDate();
    const cells = [];
    for (let i = 0; i < firstDow; i++) cells.push(null);
    for (let d = 1; d <= dim; d++) cells.push(calMonth + '-' + two(d));
    while (cells.length % 7) cells.push(null);

    const lv = leaveByDay();
    const rest = (cal && cal.weekRest) || {};
    const restIssues = [];
    let html = '';
    for (let w = 0; w < cells.length; w += 7) {
      let weekTotal = 0;
      const anyKey = cells.slice(w, w + 7).find(Boolean);
      const monday = anyKey ? dAdd(anyKey, -((dDow(anyKey) + 6) % 7)) : null;
      cells.slice(w, w + 7).forEach(key => {
        if (!key) { html += '<span class="cell blank"></span>'; return; }
        const d = dayMap[key];
        const h = hoursFor(key);
        weekTotal += h;
        const cls = ['cell'];
        const l = (lv[key] || [])[0];
        if (!d && key !== todayKey && !l) cls.push('out');
        if (h > 10) cls.push('w4'); else if (h > 8) cls.push('w3'); else if (h >= 4) cls.push('w2'); else if (h > 0) cls.push('w1');
        else if (l) cls.push(l.type === 'Sick' ? 'sick' : 'hol');
        if (l && l.status === 'Requested') cls.push('req');
        if (key === todayKey) cls.push('today');
        if (key === calSel) cls.push('sel');
        html += '<button type="button" class="' + cls.join(' ') + '" data-key="' + key + '">' +
          (key === todayKey && m.working ? '<span class="live"></span>' : '') +
          (d && d.flags ? '<span class="flag"></span>' : '') +
          '<span class="d">' + Number(key.slice(8)) + '</span>' +
          (h >= 0.05 ? '<span class="h">' + fmtH(h) + '</span>'
            : l ? '<span class="lv">' + ({ 'Holiday': 'HOL', 'Bank holiday': 'BH', 'Sick': 'SICK', 'Unpaid': 'UNP' }[l.type] || 'LV') + '</span>' : '<span class="h"></span>') +
          '</button>';
      });
      const r = monday ? rest[monday] : null;
      const rc = r && r.status === 'breach' ? ' rest-bad' : r && r.status === 'watch' ? ' rest-watch' : '';
      if (r && (r.status === 'breach' || r.status === 'watch')) restIssues.push([monday, r]);
      html += '<span class="wk' + (weekTotal > 48 ? ' over' : '') + rc + '"' + (r ? ' title="Longest break this week: ' + r.longestGapH + 'h"' : '') + '><b>' + (weekTotal >= 0.05 ? fmtH(weekTotal) : '–') + '</b>' +
        (rc ? '<span class="rest">' + (r.status === 'breach' ? 'no 24h off' : 'need 48h off') + '</span>' : '') + '</span>';
    }
    $('calGrid').innerHTML = html;
    $('restNote').innerHTML = restIssues.length
      ? restIssues.map(([mk, r]) => '<b style="color:' + (r.status === 'breach' ? 'var(--out)' : 'var(--warn)') + '">Week of ' + esc(dShort(mk)) + ':</b> longest break ' + r.longestGapH + 'h. ' +
        (r.status === 'breach' ? 'You\'re entitled to 24 hours off in each week, or 48 hours across the fortnight — you got neither.' : 'No 24-hour break this week, so you need 48 hours off together before the fortnight ends.')).join('<br>')
      : '';

    renderCalMonth(dayMap, todayKey);
    renderDay(calSel, dayMap[calSel], calSel === todayKey, m);
    renderCalFresh();
  }

  function renderCalMonth(dayMap, todayKey) {
    $('calMonthTitle').textContent = monthName(calMonth);
    const fromCal = cal && cal.months ? cal.months.find(x => x.month === calMonth) : null;
    const mo = (snap && snap.month && snap.month.month === calMonth && snap.receivedAt > ((cal && cal.receivedAt) || 0)) ? snap.month : fromCal;
    const days = Object.values(dayMap).filter(d => d.date.slice(0, 7) === calMonth);
    const worked = days.filter(d => typeof d.hours === 'number' && d.hours > 0).length;
    const flagged = days.filter(d => d.flags).length;
    if (!mo) {
      $('calMonth').innerHTML = days.length ? '<p class="empty">No pay figures for this month yet.</p>' : '<p class="empty">This month is outside your contract dates.</p>';
      return;
    }
    const under = mo.status === 'UNDERPAID';
    $('calMonth').innerHTML =
      '<div class="facts">' +
        '<div class="fact"><span>Hours</span><b>' + (mo.hours != null ? mo.hours.toFixed(1) : '—') + '</b></div>' +
        '<div class="fact"><span>Rate</span><b>' + (mo.rate ? '£' + mo.rate.toFixed(2) : '—') + '</b></div>' +
        '<div class="fact"><span>Days worked</span><b>' + worked + '</b></div>' +
      '</div>' +
      '<div class="kv"><span>Gross pay used</span><span class="num">' + (mo.pay != null ? '£' + mo.pay.toFixed(2) : '—') + '</span></div>' +
      (mo.leavePay ? '<div class="kv"><span>Less pay for paid leave</span><span class="num">−£' + mo.leavePay.toFixed(2) + '</span></div>' : '') +
      '<div class="kv"><span>Minimum-wage ceiling</span><span class="num">' + (mo.maxHours != null ? mo.maxHours.toFixed(1) + ' h' : '—') + '</span></div>' +
      '<div class="kv"><span>Days with break/rest flags</span><span class="num"' + (flagged ? ' style="color:var(--out);font-weight:700"' : '') + '>' + flagged + '</span></div>' +
      '<div class="kv"><span>Status</span><span class="chip ' + (under ? 'bad' : mo.status === 'OK' ? 'ok' : 'muted') + '">' + esc(mo.status || '—') + '</span></div>' +
      (under && mo.shortfall ? '<div class="kv"><span>Shortfall</span><b class="num" style="color:var(--out)">£' + mo.shortfall.toFixed(2) + '</b></div>' : '') +
      (calMonth === todayKey.slice(0, 7) ? '<p class="note">Today is added to these totals when you clock out.</p>' : '');
  }

  function renderDay(key, d, isToday, m) {
    $('dayTitle').textContent = longDate(key) + (isToday ? ' · today' : '');
    const el = $('dayDetail');
    let start, finish, hrs, breakMin, loc, events;
    if (isToday) {
      start = m.start !== null ? hm(m.start) : '';
      finish = m.working ? 'now' : (m.finish !== null ? hm(m.finish) : '');
      hrs = m.workedMs / 3600e3;
      breakMin = m.breakMs / 60000;
      loc = m.location;
      events = m.events;
    } else {
      start = d ? d.start : '';
      finish = d ? d.finish : '';
      hrs = d && typeof d.hours === 'number' ? d.hours : 0;
      breakMin = d && typeof d.breakMins === 'number' ? d.breakMins : 0;
      loc = d ? d.location : '';
      events = (cal && cal.events && cal.events[key]) || [];
    }
    const lvs = leaveByDay()[key] || [];
    const lvHtml = lvs.map(e => '<div class="banner ' + (e.type === 'Sick' ? 'warn' : 'info') + '" style="margin:0 0 10px"><div><strong>' + esc(e.type) +
      (e.partFrom ? ' ' + esc(e.partFrom) + '–' + esc(e.partTo) : '') + ' · ' + esc(String(e.status).toLowerCase()) + '</strong>' +
      esc(e.status === 'Approved' ? (e.approvedBy ? 'Approved by ' + e.approvedBy : 'No approver recorded') + (e.approvalRef ? ' — ' + e.approvalRef : '') : 'Waiting for approval') +
      '</div></div>').join('');
    if (!d && !isToday && !lvs.length) { el.innerHTML = '<p class="empty">Outside your contract dates.</p>'; return; }
    if (!start && !events.length) { el.innerHTML = lvHtml + '<p class="empty">No time recorded' + (isToday ? ' yet today.' : '.') + '</p>'; return; }
    el.innerHTML = lvHtml +
      '<div class="facts">' +
        '<div class="fact"><span>Start</span><b>' + esc(start || '—') + '</b></div>' +
        '<div class="fact"><span>Finish</span><b>' + esc(finish || '—') + '</b></div>' +
        '<div class="fact"><span>Hours</span><b>' + (hrs > 0 ? hours(hrs * 3600e3) : '—') + '</b></div>' +
      '</div>' +
      '<div class="kv"><span>Breaks</span><span class="num">' + Math.round(breakMin) + ' min</span></div>' +
      (loc ? '<div class="kv"><span>Location</span><span>' + esc(loc) + '</span></div>' : '') +
      (d && d.flags ? '<div class="banner bad" style="margin:12px 0 0"><div><strong>Flagged</strong>' + esc(d.flags) + '</div></div>' : '') +
      (d && d.notes ? '<p class="note"><b>Notes:</b> ' + esc(d.notes) + '</p>' : '') +
      (events.length ? '<ul class="list" style="margin-top:8px">' + events.map(tapItem).join('') + '</ul>' : '');
  }

  function setView(v) {
    view = VIEWS.indexOf(v) >= 0 ? v : 'today';
    prefs.view = view;
    store.set(KEYS.prefs, prefs);
    renderAll();
    window.scrollTo(0, 0);
    if (view === 'calendar') loadCalendar(false);
    if (view === 'pay') loadPayments(false);
    if (view === 'leave') loadLeave(false);
    if (view === 'docs') loadDocs(true);
  }

  /* ---------------- payments ---------------- */

  let pay = store.get(KEYS.pay, null);   // last payments view from the sheet
  let payLoading = false, payErr = '', lastPayLoad = 0;
  let editing = null;                     // { id, isNew, reading }
  const MAX_UPLOAD = 15 * 1024 * 1024;
  const money = v => (v == null || v === '' || isNaN(Number(v)) ? '—' : '£' + Number(v).toFixed(2));
  const monthLabel = mk => mk ? new Intl.DateTimeFormat('en-GB', { month: 'long', year: 'numeric', timeZone: 'UTC' }).format(new Date(mk + '-15T12:00:00Z')) : '';
  const shortDate = k => k ? new Intl.DateTimeFormat('en-GB', { day: 'numeric', month: 'short', year: 'numeric', timeZone: 'UTC' }).format(new Date(k + 'T12:00:00Z')) : '';

  function applyPayments(res) {
    pay = { payments: res.payments, months: res.months, ocrAvailable: res.ocrAvailable, receivedAt: Date.now() };
    store.set(KEYS.pay, pay);
    lastPayLoad = Date.now();
    payErr = ''; // fresh data from the sheet: any earlier "couldn't update" no longer applies
  }

  async function loadPayments(force) {
    if (!cfg || payLoading) return;
    if (!force && Date.now() - lastPayLoad < 30000) return;
    payLoading = true;
    try {
      const res = await api({ api: 'payments' });
      if (res.ok) { applyPayments(res); payErr = ''; } else payErr = res.error;
    } catch (e) { payErr = e.message; }
    finally { payLoading = false; if (view === 'pay') renderPay(); }
  }

  /** Server list with anything still waiting on the phone laid over the top. */
  function payList() {
    const byId = {};
    ((pay && pay.payments) || []).forEach(p => { byId[p.id] = Object.assign({}, p); });
    const n = v => (v === '' || v == null ? null : Number(v));
    queue.forEach(q => {
      if (q.op === 'payment') {
        byId[q.id] = Object.assign({}, byId[q.id] || {}, q.fields, {
          id: q.id, status: 'Confirmed', pendingSave: true,
          amount: n(q.fields.amount), gross: n(q.fields.gross), net: n(q.fields.net),
          tax: n(q.fields.tax), ni: n(q.fields.ni), pension: n(q.fields.pension),
        });
      }
      if (q.op === 'paymentDelete') delete byId[q.id];
      if (q.op === 'upload' && q.api !== 'docUpload' && !byId[q.id]) {
        byId[q.id] = { id: q.id, uploading: true, filename: q.filename, received: dayKey(q.ts), status: 'Waiting to upload' };
      }
    });
    return Object.values(byId).sort((a, b) => ((b.received || b.period || '') > (a.received || a.period || '') ? 1 : -1));
  }

  function renderPay() {
    const list = payList();
    const waitingUploads = queue.filter(q => q.op === 'upload' && q.api !== 'docUpload').length;
    if (waitingUploads && (syncState.kind === 'offline' || syncState.kind === 'error' || syncState.kind === 'auth')) {
      $('payErr').className = 'okmsg';
      $('payErr').textContent = waitingUploads + ' payslip' + (waitingUploads > 1 ? 's' : '') +
        ' saved on your phone — ' + (waitingUploads > 1 ? 'they\'ll' : 'it\'ll') + ' upload and be read when you have signal.';
    }
    const ul = $('payList');
    if (!list.length) {
      ul.innerHTML = '<li class="empty">No payments yet. Upload a payslip or enter one manually.</li>';
    } else {
      ul.innerHTML = list.map(p => {
        const chip = p.uploading ? '<span class="chip wait">' + (syncState.kind === 'syncing' ? 'uploading…' : 'on phone') + '</span>'
          : p.pendingSave ? '<span class="chip wait">on phone</span>'
          : p.status === 'Confirmed' ? '<span class="chip ok">confirmed</span>'
          : '<span class="chip wait">needs review</span>';
        const title = p.uploading ? esc(p.filename || 'Payslip')
          : '<span class="payamt">' + money(p.amount) + '</span>' + (p.period ? ' · ' + esc(monthLabel(p.period)) : '');
        const meta = p.uploading ? 'Will upload and be read when you have signal'
          : [p.received ? 'Received ' + shortDate(p.received) : '', p.gross != null ? 'gross ' + money(p.gross) : '',
            p.source === 'upload' ? 'payslip attached' : ''].filter(Boolean).join(' · ');
        const doc = p.docUrl ? ' · <a href="' + esc(p.docUrl) + '" target="_blank" rel="noopener" data-doc="1">open payslip</a>' : '';
        return '<li class="' + (p.uploading ? '' : 'click') + '" data-pay="' + esc(p.id) + '"><span class="grow">' + title +
          '<br><span class="paymeta">' + esc(meta) + doc + '</span></span>' + chip + '</li>';
      }).join('');
    }

    const months = (pay && pay.months) || [];
    $('payMonths').innerHTML = months.length ? months.map(m =>
      '<div style="padding:8px 0;border-bottom:1px solid var(--line)"><div class="kv" style="margin:0"><b>' + esc(monthLabel(m.month)) + '</b>' +
      (m.flags.length ? '<span class="chip bad">' + m.flags.length + ' to check</span>' : '<span class="chip ok">matches</span>') + '</div>' +
      '<div class="paymeta">Received ' + money(m.received) + ' · payslip gross ' + money(m.gross) +
      (m.estimate != null ? ' · contract implies ' + money(m.estimate) : '') + '</div>' +
      m.flags.map(f => '<div class="flagline">' + esc(f) + '</div>').join('') + '</div>').join('')
      : '<p class="empty">Checks appear once you confirm a payment.</p>';

    $('payFresh').textContent = payErr
      ? 'Couldn\'t update (' + payErr + ').' + (pay ? ' Showing the copy saved ' + hm(pay.receivedAt) + '.' : '')
      : pay ? 'From your sheet, updated ' + hm(pay.receivedAt) + '.' +
        (pay.ocrAvailable === false ? ' Automatic reading is off — turn on the Drive API service in Apps Script.' : '')
      : 'Open with signal to load your payments.';
  }

  const FIELDS = [['pReceived', 'received'], ['pAmount', 'amount'], ['pPeriod', 'period'], ['pGross', 'gross'], ['pNet', 'net'],
    ['pTax', 'tax'], ['pNi', 'ni'], ['pPension', 'pension'], ['pPayDate', 'payDate'], ['pPayer', 'payer'],
    ['pRef', 'reference'], ['pNotes', 'notes']];

  function openPayForm(p, opts = {}) {
    editing = { id: p.id, isNew: !!opts.isNew, reading: opts.reading || null };
    const r = opts.reading;
    const read = r ? Object.keys(r.fields || {}).filter(k => r.fields[k] != null) : [];
    const autoFor = { received: 'payDate', amount: 'net' };
    FIELDS.forEach(([el, k]) => {
      const v = p[k];
      $(el).value = v == null ? '' : String(v);
      $(el).classList.toggle('auto', read.indexOf(k) >= 0 || read.indexOf(autoFor[k]) >= 0);
    });
    if (!$('pReceived').value) $('pReceived').value = dayKey(Date.now());
    if (!$('pPeriod').value && $('pReceived').value) $('pPeriod').value = $('pReceived').value.slice(0, 7);
    $('payFormTitle').textContent = opts.isNew ? 'New payment' : p.status === 'Needs review' ? 'Check the figures' : 'Edit payment';
    $('payDelete').classList.toggle('hidden', !!opts.isNew);
    $('payFormErr').textContent = '';
    const notes = r ? r.notes : (p.readingNotes ? [p.readingNotes] : []);
    const heading = r ? {
      high: 'Read automatically — please check',
      medium: 'Read automatically — check carefully',
      low: 'Only partly read — fill in the rest',
      none: 'Couldn\'t read this payslip — enter the figures',
    }[r.confidence] : 'Payslip attached';
    $('payReading').innerHTML = (r || p.docUrl)
      ? '<div class="banner ' + (r && r.confidence === 'high' ? 'info' : 'warn') + '" style="margin:0"><div><strong>' + esc(heading) + '</strong>' +
        esc(notes.join(' ')) +
        (p.docUrl ? ' <a href="' + esc(p.docUrl) + '" target="_blank" rel="noopener">Open payslip</a>' : '') +
        (read.length ? '<br><span class="paymeta">Highlighted boxes were filled from the payslip.</span>' : '') + '</div></div>'
      : '';
    $('payForm').classList.remove('hidden');
    $('payForm').scrollIntoView({ behavior: 'smooth', block: 'start' });
  }

  function closePayForm() {
    editing = null;
    $('payForm').classList.add('hidden');
    const m = $('payErr');
    if (/Check the figures/.test(m.textContent)) m.textContent = ''; // the review prompt is done with
  }

  function onPaySave() {
    const err = $('payFormErr');
    err.textContent = '';
    if (!editing) return;
    const f = {};
    FIELDS.forEach(([el, k]) => { f[k] = $(el).value.trim(); });
    if (!f.received) { err.textContent = 'Enter the date the money arrived.'; return; }
    if (f.amount === '' || !(Number(f.amount) >= 0)) { err.textContent = 'Enter the amount received.'; return; }
    if (!/^\d{4}-\d{2}$/.test(f.period)) { err.textContent = 'Choose the month this payment covers.'; return; }
    for (const k of ['amount', 'gross', 'net', 'tax', 'ni', 'pension']) {
      if (f[k] !== '' && !(Number(f[k]) >= 0)) { err.textContent = 'Check the ' + k + ' amount.'; return; }
    }
    if (f.gross !== '' && f.net !== '' && Number(f.net) > Number(f.gross)) {
      err.textContent = 'Net pay can\'t be more than gross pay — check the figures.'; return;
    }
    const id = editing.id;
    queue = queue.filter(q => !(q.op === 'payment' && q.id === id));
    closePayForm();
    enqueue({ op: 'payment', id, ts: Date.now(), fields: f });
  }

  function onPayDelete() {
    if (!editing) return;
    if (!confirm('Remove this payment? It stays in your sheet marked as deleted, and its payslip stays in your Drive.')) return;
    const id = editing.id;
    const onlyOnPhone = !((pay && pay.payments) || []).some(p => p.id === id);
    queue = queue.filter(q => !(q.op === 'payment' && q.id === id));
    closePayForm();
    if (onlyOnPhone) { saveQueue(); renderAll(); } else enqueue({ op: 'paymentDelete', id, ts: Date.now() });
  }

  /** Photos are shrunk before upload: smaller and faster, and still easily readable. */
  async function prepareFile(file) {
    if (!/^image\//.test(file.type) || !window.createImageBitmap) return file;
    try {
      const bmp = await createImageBitmap(file);
      const scale = Math.min(1, 2200 / Math.max(bmp.width, bmp.height));
      const c = document.createElement('canvas');
      c.width = Math.round(bmp.width * scale); c.height = Math.round(bmp.height * scale);
      c.getContext('2d').drawImage(bmp, 0, 0, c.width, c.height);
      const out = await new Promise(r => c.toBlob(r, 'image/jpeg', 0.85));
      return out && out.size < file.size ? new File([out], file.name.replace(/\.\w+$/, '') + '.jpg', { type: 'image/jpeg' }) : file;
    } catch (e) {
      return file; // a format this browser can't decode: send the original
    }
  }

  async function onFileChosen(e) {
    const msg = $('payErr');
    msg.className = 'err'; msg.textContent = '';
    const input = e.target;
    const file = input.files && input.files[0];
    input.value = '';
    if (!file) return;
    if (!/^application\/pdf$|^image\/(jpeg|png|heic|heif|webp)$/.test(file.type)) {
      msg.textContent = 'Upload a PDF or a photo (JPEG, PNG or HEIC).'; return;
    }
    const prepared = await prepareFile(file);
    if (prepared.size > MAX_UPLOAD) { msg.textContent = 'That file is larger than 15 MB.'; return; }
    const id = uuid();
    try {
      await fileStore.put(id, prepared);
    } catch (e2) {
      msg.textContent = 'This phone wouldn\'t store the file (' + e2.message + '). Try again.';
      return;
    }
    msg.className = 'okmsg';
    msg.textContent = navigator.onLine === false
      ? 'Saved on your phone — it will upload and be read when you have signal.'
      : 'Uploading and reading your payslip…';
    enqueue({ op: 'upload', id, fileKey: id, filename: prepared.name || 'payslip', mime: prepared.type, size: prepared.size, ts: Date.now() });
  }

  function onUploadDone(item, res) {
    const p = (res.payments || []).find(x => x.id === item.id);
    if (view === 'pay' && p && !editing && p.status === 'Needs review') {
      openPayForm(p, { reading: res.reading });
      $('payErr').className = 'okmsg';
      $('payErr').textContent = 'Payslip stored in your Drive. Check the figures below and confirm.';
    }
  }

  /* ---------------- holidays and leave ---------------- */

  let leave = store.get(KEYS.leave, null);   // last leave view from the sheet
  let leaveLoading = false, leaveErr = '', lastLeaveLoad = 0;
  let leaveEditing = null;                    // { id, isNew }
  const LEAVE_TYPES = ['Holiday', 'Bank holiday', 'Sick', 'Unpaid', 'Other paid leave'];
  const LEAVE_STATUSES = ['Requested', 'Approved', 'Refused', 'Cancelled'];
  const LEAVE_HOW = ['Email', 'Slack', 'HR system', 'In person', 'Phone', 'Other'];
  const dfmt = (k, opts) => new Intl.DateTimeFormat('en-GB', Object.assign({ timeZone: 'UTC' }, opts)).format(new Date(k + 'T12:00:00Z'));
  const dShort = k => dfmt(k, { weekday: 'short', day: 'numeric', month: 'short' });
  const dAdd = (k, n) => new Date(Date.parse(k + 'T12:00:00Z') + n * 86400000).toISOString().slice(0, 10);
  const dRange = (a, b) => { const out = []; for (let k = a; k <= b && out.length < 400; k = dAdd(k, 1)) out.push(k); return out; };
  const dDow = k => new Date(k + 'T12:00:00Z').getUTCDay();
  const nDays = x => (Math.round(x * 100) / 100).toString().replace(/\.0+$/, '').replace(/(\.\d)0$/, '$1');
  const dayWord = x => nDays(x) + ' day' + (x === 1 ? '' : 's');

  function applyLeave(res) {
    leave = { entries: res.entries, allowance: res.allowance, bankHolidays: res.bankHolidays, contract: res.contract, receivedAt: Date.now() };
    store.set(KEYS.leave, leave);
    lastLeaveLoad = Date.now();
  }

  async function loadLeave(force) {
    if (!cfg || leaveLoading) return;
    if (!force && Date.now() - lastLeaveLoad < 30000) return;
    leaveLoading = true;
    try {
      const res = await api({ api: 'leave' });
      if (res.ok) { applyLeave(res); leaveErr = ''; } else leaveErr = res.error;
    } catch (e) { leaveErr = e.message; }
    finally { leaveLoading = false; if (view === 'leave') renderLeave(); }
  }

  /** Mirrors the server's default: hours ÷ 8 for part of a day, else Mon–Fri dates (all dates if none). */
  function defaultDays(from, to, pf, pt) {
    if (!from || !to || to < from) return '';
    if (pf && pt) {
      const mins = t => { const [h, m] = t.split(':').map(Number); return h * 60 + m; };
      return Math.max(0, Math.min(1, Math.round((mins(pt) - mins(pf)) / 60 / 8 * 100) / 100));
    }
    const all = dRange(from, to);
    return all.filter(k => dDow(k) >= 1 && dDow(k) <= 5).length || all.length;
  }

  /** Server entries with anything still waiting on the phone laid over the top. */
  function leaveList() {
    const byId = {};
    ((leave && leave.entries) || []).forEach(e => { byId[e.id] = Object.assign({}, e); });
    queue.forEach(q => {
      if (q.op === 'leave') {
        const f = q.fields;
        byId[q.id] = Object.assign({}, byId[q.id] || {}, f, {
          id: q.id, pendingSave: true, to: f.to || f.from, days: f.days === '' ? defaultDays(f.from, f.to || f.from, f.partFrom, f.partTo) : Number(f.days),
          counts: f.counts === '1',
        });
      }
      if (q.op === 'leaveDelete') delete byId[q.id];
    });
    return Object.values(byId).sort((a, b) => (a.from < b.from ? 1 : -1));
  }

  /** date -> [{type, status, partFrom, partTo}] for the calendar, including changes still on the phone. */
  function leaveByDay() {
    const out = {};
    leaveList().filter(e => e.status === 'Approved' || e.status === 'Requested').forEach(e => {
      dRange(e.from, e.to).forEach(k => { (out[k] = out[k] || []).push(e); });
    });
    return out;
  }

  function renderLeave() {
    const a = leave && leave.allowance;
    const pending = queue.filter(q => q.op === 'leave' || q.op === 'leaveDelete').length;
    const el = $('leaveAllowance');
    if (!a) {
      el.innerHTML = '<p class="empty">Open with signal to load your allowance.</p>';
    } else {
      const higher = a.basis === 'contract' ? 'contract' : 'legal minimum';
      el.innerHTML =
        '<div class="bigfig">' +
          '<div><span>Can book now</span><b>' + nDays(a.availableNow) + '</b></div>' +
          '<div><span>Left in contract</span><b' + (a.remaining < 0 ? ' style="color:var(--out)"' : '') + '>' + nDays(a.remaining) + '</b></div>' +
          '<div><span>Taken</span><b>' + nDays(a.taken) + '</b></div>' +
        '</div>' +
        '<table class="cmp"><tr><th></th><th>Contract</th><th>Legal minimum</th></tr>' +
          '<tr><td>Allowance for your contract</td><td' + (a.basis === 'contract' ? ' style="font-weight:800"' : '') + '>' + dayWord(a.contract) + '</td><td' + (a.basis !== 'contract' ? ' style="font-weight:800"' : '') + '>' + dayWord(a.statutory) + '</td></tr>' +
          '<tr><td>Built up so far</td><td>' + dayWord(a.accruedContract) + '</td><td>' + dayWord(a.accruedStatutory) + '</td></tr>' +
          '<tr><td>Taken / booked</td><td colspan="2" style="text-align:right">' + nDays(a.taken) + ' / ' + nDays(a.booked) + (a.requested ? ' (+' + nDays(a.requested) + ' requested)' : '') + '</td></tr>' +
          '<tr><td>Paid at the end if not taken</td><td colspan="2" style="text-align:right">' + money(a.payAtEnd) + '</td></tr>' +
        '</table>' +
        '<p class="note">You get the higher of the two — here the ' + higher + ' (' + dayWord(a.entitlement) + '). ' +
          (a.contractBasis === 'contract' ? 'Contract figure: 8 days for the whole contract, as Fuse told you (clause 6.1). ' : 'Contract figure: 8 days a year, pro rata (clause 6.1). ') +
          'A day\'s holiday pay is ' + money(a.dayRate) + ' (1/260 of salary, clause 6.2).' +
          (contractDoc() ? ' <a href="#" data-opencontract="1">Open your contract</a>' : '') + '</p>' +
        (a.basis !== 'contract' ? '<div class="banner warn" style="margin:12px 0 0"><div><strong>Your contract gives less than the law</strong>' +
          'The legal minimum (5.6 weeks a year, pro rata) applies instead: ' + dayWord(a.statutory) + '.</div></div>' : '') +
        (a.overEntitlement > 0 ? '<div class="banner bad" style="margin:12px 0 0"><div><strong>More than your allowance</strong>' + dayWord(a.overEntitlement) +
          ' beyond your ' + dayWord(a.entitlement) + ' is taken or booked. Unless Fuse agrees extra holiday in writing, clause 6.4 lets them deduct ' + money(a.clawback) + ' at the end.</div></div>' : '') +
        '<p class="note">"Can book now" is what has built up so far (the higher of the two ways it builds up). Figures are from your sheet' +
        (pending ? '; ' + pending + ' change' + (pending > 1 ? 's' : '') + ' still on your phone aren\'t included yet.' : '.') + ' I\'m not a lawyer — check with Acas before relying on these.</p>';
    }

    // Bank holidays
    const bank = (leave && leave.bankHolidays) || [];
    const local = leaveByDay();
    $('leaveBank').innerHTML = bank.length ? '<ul class="list">' + bank.map(b => {
      const mine = (local[b.date] || []).find(e => e.type === 'Bank holiday');
      const state = mine ? (mine.status === 'Approved' ? 'day off' : 'requested') : b.state;
      const chip = state === 'day off' ? '<span class="chip ok">day off</span>' : state === 'requested' ? '<span class="chip wait">requested</span>'
        : state === 'worked' ? '<span class="chip wait">worked</span>' : state === 'upcoming' ? '<span class="chip muted">upcoming</span>' : '<span class="chip bad">not recorded</span>';
      const act = mine ? '' : '<button class="btn ghost small" type="button" data-bank="' + esc(b.date) + '" data-name="' + esc(b.name) + '">Day off</button>';
      return '<li><span class="grow"><b>' + esc(dShort(b.date)) + '</b><br><span class="paymeta">' + esc(b.name) + '</span></span>' + chip + act + '</li>';
    }).join('') + '</ul><p class="note">Your contract doesn\'t say whether bank holidays are given on top of your allowance. If you get one off with pay, mark it as a day off — by default it uses your allowance (Fuse is allowed to count it). Untick "Uses allowance" if they confirm it\'s extra.</p>'
      : '<p class="empty">' + (leave ? 'No bank holidays fall in your contract dates.' : 'Open with signal to load bank holidays.') + '</p>';

    // Entries
    const list = leaveList();
    $('leaveList').innerHTML = list.length ? list.map(e => {
      const chip = e.pendingSave ? '<span class="chip wait">on phone</span>'
        : e.status === 'Approved' ? '<span class="chip ok">approved</span>' : e.status === 'Requested' ? '<span class="chip wait">requested</span>'
        : '<span class="chip muted">' + esc(String(e.status || '').toLowerCase()) + '</span>';
      const span = e.from === e.to ? dShort(e.from) + (e.partFrom ? ' ' + e.partFrom + '–' + e.partTo : '') : dShort(e.from) + ' – ' + dShort(e.to);
      const approval = e.status === 'Approved'
        ? (e.approvedBy || e.approvedHow || e.approvedOn ? 'Approved' + (e.approvedBy ? ' by ' + e.approvedBy : '') + (e.approvedHow ? ' (' + e.approvedHow.toLowerCase() + ')' : '') + (e.approvedOn ? ' on ' + dShort(e.approvedOn) : '') : 'No approval details yet')
        : '';
      return '<li class="click" data-leave="' + esc(e.id) + '"><span class="grow"><b>' + esc(e.type) + '</b> · ' + esc(span) +
        '<br><span class="paymeta">' + esc([dayWord(Number(e.days) || 0) + (e.counts ? '' : ' (not from allowance)'), approval].filter(Boolean).join(' · ')) + '</span>' +
        (e.status === 'Approved' && !e.approvedBy && !e.approvalRef ? '<br><span class="flagline" style="margin-top:2px;font-size:13px">Add who approved it and where</span>' : '') +
        '</span>' + chip + '</li>';
    }).join('') : '<li class="empty">Nothing recorded yet.</li>';

    $('leaveFresh').textContent = leaveErr
      ? 'Couldn\'t update (' + leaveErr + ').' + (leave ? ' Showing the copy saved ' + hm(leave.receivedAt) + '.' : '')
      : leave ? 'From your sheet, updated ' + hm(leave.receivedAt) + '.' : '';
  }

  function fillSelect(el, opts, value) {
    el.innerHTML = opts.map(o => '<option' + (o === value ? ' selected' : '') + '>' + esc(o) + '</option>').join('');
  }

  function openLeaveForm(e, opts = {}) {
    leaveEditing = { id: e.id, isNew: !!opts.isNew };
    fillSelect($('lType'), LEAVE_TYPES, e.type || 'Holiday');
    fillSelect($('lStatus'), LEAVE_STATUSES, e.status || 'Requested');
    $('lHow').innerHTML = '<option value=""></option>' + LEAVE_HOW.map(o => '<option' + (o === e.approvedHow ? ' selected' : '') + '>' + o + '</option>').join('');
    $('lFrom').value = e.from || '';
    $('lTo').value = e.to || e.from || '';
    $('lPart').checked = !!e.partFrom;
    $('lPartFrom').value = e.partFrom || '';
    $('lPartTo').value = e.partTo || '';
    $('lDays').value = e.days != null && e.days !== '' ? String(e.days) : '';
    $('lDays').dataset.auto = opts.isNew || e.days === '' ? '1' : '';
    $('lCounts').checked = e.counts != null ? !!e.counts : (e.type || 'Holiday') === 'Holiday' || e.type === 'Bank holiday';
    $('lCounts').dataset.auto = opts.isNew ? '1' : '';
    $('lRequestedOn').value = e.requestedOn || '';
    $('lApprovedOn').value = e.approvedOn || '';
    $('lApprovedBy').value = e.approvedBy || '';
    $('lRef').value = e.approvalRef || '';
    $('lNotes').value = e.notes || '';
    $('leaveFormTitle').textContent = opts.isNew ? 'Record leave' : 'Edit leave';
    $('leaveDelete').classList.toggle('hidden', !!opts.isNew);
    $('leaveFormErr').textContent = '';
    onLeaveFormChange();
    $('leaveForm').classList.remove('hidden');
    $('leaveForm').scrollIntoView({ behavior: 'smooth', block: 'start' });
  }

  function closeLeaveForm() { leaveEditing = null; $('leaveForm').classList.add('hidden'); }

  /** Keeps the form consistent as you type: part-day times, default days, the "uses allowance" default, hints. */
  function onLeaveFormChange(ev) {
    const part = $('lPart').checked;
    document.querySelectorAll('#leaveForm .partonly').forEach(x => x.classList.toggle('hidden', !part));
    if (part && $('lFrom').value) $('lTo').value = $('lFrom').value;
    $('lTo').disabled = part;
    if (ev && ev.target === $('lFrom') && (!$('lTo').value || $('lTo').value < $('lFrom').value)) $('lTo').value = $('lFrom').value;
    if (ev && ev.target === $('lDays')) $('lDays').dataset.auto = '';
    if (ev && ev.target === $('lCounts')) $('lCounts').dataset.auto = '';
    const type = $('lType').value;
    if ($('lCounts').dataset.auto) $('lCounts').checked = type === 'Holiday' || type === 'Bank holiday';
    if ($('lDays').dataset.auto) {
      const d = defaultDays($('lFrom').value, $('lTo').value || $('lFrom').value, part ? $('lPartFrom').value : '', part ? $('lPartTo').value : '');
      $('lDays').value = d === '' ? '' : String(d);
    }
    const status = $('lStatus').value;
    const hints = [];
    if (type === 'Sick') hints.push('Your contract pays Statutory Sick Pay only (clause 7.2): tell them by 10am on the first day; a doctor\'s note is needed after 7 days.');
    if (status === 'Approved' && !$('lApprovedBy').value.trim() && !$('lRef').value.trim()) hints.push('Add who approved it and where (e.g. the email subject) — clause 6.1 needs prior approval.');
    if (status === 'Requested') hints.push('Change the status to Approved when they confirm, with the date and where.');
    if (type === 'Bank holiday') hints.push('Untick "Uses allowance" only if Fuse confirms bank holidays are on top of your allowance.');
    $('lHint').textContent = hints.join(' ');
  }

  function onLeaveSave() {
    const err = $('leaveFormErr');
    err.textContent = '';
    if (!leaveEditing) return;
    const part = $('lPart').checked;
    const f = {
      type: $('lType').value, status: $('lStatus').value,
      from: $('lFrom').value, to: part ? $('lFrom').value : ($('lTo').value || $('lFrom').value),
      partFrom: part ? $('lPartFrom').value : '', partTo: part ? $('lPartTo').value : '',
      days: $('lDays').value.trim(), counts: $('lCounts').checked ? '1' : '0',
      requestedOn: $('lRequestedOn').value, approvedOn: $('lApprovedOn').value, approvedBy: $('lApprovedBy').value.trim(),
      approvedHow: $('lHow').value, approvalRef: $('lRef').value.trim(), notes: $('lNotes').value.trim(),
    };
    if (!f.from) { err.textContent = 'Choose the first day.'; return; }
    if (f.to < f.from) { err.textContent = 'The last day is before the first day.'; return; }
    if (part && (!f.partFrom || !f.partTo)) { err.textContent = 'Enter both times for part of a day.'; return; }
    if (part && f.partTo <= f.partFrom) { err.textContent = 'The end time must be after the start time.'; return; }
    if (f.days !== '' && !(Number(f.days) >= 0)) { err.textContent = 'Check the days counted.'; return; }
    if (f.days !== '' && Number(f.days) > dRange(f.from, f.to).length) { err.textContent = 'Days counted can\'t be more than the number of dates.'; return; }
    const c = leave && leave.contract;
    if (c && c.start && c.end && (f.to < c.start || f.from > c.end)) { err.textContent = 'Those dates are outside your contract (' + dShort(c.start) + ' – ' + dShort(c.end) + ').'; return; }
    if (f.status === 'Approved' || f.status === 'Requested') {
      const clash = leaveList().find(x => x.id !== leaveEditing.id && (x.status === 'Approved' || x.status === 'Requested') && x.from <= f.to && x.to >= f.from &&
        !(x.partFrom && f.partFrom && (x.partTo <= f.partFrom || x.partFrom >= f.partTo)));
      if (clash) { err.textContent = 'That overlaps ' + clash.type.toLowerCase() + ' already recorded for ' + dShort(clash.from) + (clash.to !== clash.from ? ' – ' + dShort(clash.to) : '') + '.'; return; }
    }
    const id = leaveEditing.id;
    queue = queue.filter(q => !(q.op === 'leave' && q.id === id));
    closeLeaveForm();
    $('leaveErr').className = 'okmsg';
    $('leaveErr').textContent = syncState.kind === 'offline' ? 'Saved on your phone — it will reach your sheet when you have signal.' : 'Saved.';
    enqueue({ op: 'leave', id, ts: Date.now(), fields: f });
  }

  function onLeaveDelete() {
    if (!leaveEditing) return;
    if (!confirm('Remove this? It stays in your sheet marked as deleted.')) return;
    const id = leaveEditing.id;
    const onlyOnPhone = !((leave && leave.entries) || []).some(e => e.id === id);
    queue = queue.filter(q => !(q.op === 'leave' && q.id === id));
    closeLeaveForm();
    if (onlyOnPhone) { saveQueue(); renderAll(); } else enqueue({ op: 'leaveDelete', id, ts: Date.now() });
  }

  /* ---------------- documents ---------------- */

  let docs = store.get(KEYS.docs, null);          // last list from the sheet's folder
  let docCache = store.get(KEYS.docCache, {});    // driveId -> { updated, name, mime, size } kept on this phone
  let docsLoading = false, docsErr = '', lastDocsLoad = 0, caching = false, cachingId = null;
  const DOC_MIME = /^(application\/pdf|image\/(jpeg|png|heic|heif|webp)|application\/vnd\.openxmlformats-officedocument\.wordprocessingml\.document|application\/msword|text\/plain)$/;
  const saveDocCache = () => store.set(KEYS.docCache, docCache);
  const kb = n => (n >= 1048576 ? (n / 1048576).toFixed(1) + ' MB' : Math.max(1, Math.round(n / 1024)) + ' KB');
  const docDate = ms => new Intl.DateTimeFormat('en-GB', { timeZone: TZ, day: 'numeric', month: 'short', year: 'numeric' }).format(new Date(ms));

  function applyDocs(res) {
    docs = { docs: res.docs, folder: res.folder, receivedAt: Date.now() };
    store.set(KEYS.docs, docs);
    lastDocsLoad = Date.now();
  }

  async function loadDocs(force) {
    if (!cfg || docsLoading) return;
    if (!force && Date.now() - lastDocsLoad < 30000) return;
    docsLoading = true;
    try {
      const res = await api({ api: 'docs' });
      if (res.ok) { applyDocs(res); docsErr = ''; } else docsErr = res.error;
    } catch (e) { docsErr = e.message; }
    finally { docsLoading = false; if (view === 'docs') renderDocs(); }
    cacheDocs();
  }

  /** Keeps a copy of every document on the phone, so they open with no signal. Newer versions replace older ones. */
  async function cacheDocs() {
    if (caching || !docs || !docs.docs) return;
    caching = true;
    try {
      const ids = new Set(docs.docs.map(d => d.id));
      for (const id of Object.keys(docCache)) {
        if (!ids.has(id)) { await fileStore.del('doc:' + id); delete docCache[id]; saveDocCache(); }
      }
      for (const d of docs.docs) {
        if (!d.offline || (docCache[d.id] && docCache[d.id].updated === d.updated)) continue;
        cachingId = d.id;
        if (view === 'docs') renderDocs();
        let res;
        try { res = await api({ api: 'docFile', id: d.id }); } catch (e) { break; } // no signal: try again later
        if (!res.ok) continue;
        const bytes = Uint8Array.from(atob(res.data), c => c.charCodeAt(0));
        try {
          await fileStore.put('doc:' + d.id, new Blob([bytes], { type: res.mime }));
        } catch (e) { break; } // phone storage full
        docCache[d.id] = { updated: res.updated, name: res.name, mime: res.mime, size: bytes.length };
        saveDocCache();
      }
    } finally {
      caching = false; cachingId = null;
      if (view === 'docs') renderDocs();
    }
  }

  /** After an upload, the copy already on the phone becomes the offline copy — no need to download it again. */
  async function onDocUploaded(item, res) {
    applyDocs(res);
    const d = res.focus && res.docs.find(x => x.id === res.focus);
    try {
      const blob = await fileStore.get(item.fileKey);
      if (d && blob) {
        await fileStore.put('doc:' + d.id, blob);
        docCache[d.id] = { updated: d.updated, name: d.name, mime: d.mime, size: blob.size };
        saveDocCache();
      }
    } catch (e) { /* it will be downloaded instead */ }
    fileStore.del(item.fileKey);
    if (view === 'docs') {
      $('docErr').className = 'okmsg';
      $('docErr').textContent = 'Saved to ' + ((res.folder && res.folder.name) || 'your Drive') + ' and kept on this phone.';
    }
  }

  function renderDocs() {
    const waiting = queue.filter(q => q.op === 'upload' && q.api === 'docUpload');
    const list = (docs && docs.docs) || [];
    const rows = waiting.map(q => '<li><span class="grow"><b>' + esc(q.filename) + '</b><br><span class="paymeta">' +
        (syncState.kind === 'syncing' ? 'Uploading…' : 'Will upload when you have signal') + '</span></span><span class="chip wait">on phone</span></li>')
      .concat(list.map(d => {
        const local = docCache[d.id] && docCache[d.id].updated === d.updated;
        const chip = local ? '<span class="chip ok">on phone</span>' : cachingId === d.id ? '<span class="chip wait">saving…</span>'
          : d.offline ? '<span class="chip muted">not saved yet</span>' : '<span class="chip muted">Drive only</span>';
        const isContract = /contract|agreement|docusign/i.test(d.name);
        return '<li class="doc"><div class="docname"><b>' + esc(d.name) + '</b>' + (isContract ? ' <span class="chip ok">contract</span>' : '') + '</div>' +
          '<div class="docrow"><span class="paymeta grow">' + esc(docDate(d.created) + ' · ' + kb(d.size)) + ' · <a href="' + esc(d.url) + '" target="_blank" rel="noopener">Drive</a></span>' + chip + '</div>' +
          '<div class="docrow"><button class="btn small" type="button" data-open="' + esc(d.id) + '" style="flex:1">Open</button>' +
          (local ? '<button class="btn ghost small" type="button" data-share="' + esc(d.id) + '" style="flex:1">Save / share</button>' : '') + '</div></li>';
      }));
    $('docList').innerHTML = rows.length ? rows.join('') : '<li class="empty">' + (docs ? 'No documents yet. Add your contract above.' : 'Open with signal to load your documents.') + '</li>';
    $('docFresh').textContent = docsErr
      ? 'Couldn\'t update (' + docsErr + ').' + (docs ? ' Showing the list saved ' + hm(docs.receivedAt) + '.' : '')
      : docs ? 'From ' + ((docs.folder && docs.folder.name) || 'your folder') + ', updated ' + hm(docs.receivedAt) + '.' : '';
  }

  const contractDoc = () => ((docs && docs.docs) || []).find(d => /contract|docusign/i.test(d.name)) || null;

  async function localDoc(id) {
    const c = docCache[id];
    if (!c) return null;
    try {
      const blob = await fileStore.get('doc:' + id);
      return blob ? new File([blob], c.name, { type: c.mime || blob.type }) : null;
    } catch (e) { return null; }
  }

  /** Opens the phone's copy (works offline); falls back to Drive. */
  async function openDoc(id) {
    const d = ((docs && docs.docs) || []).find(x => x.id === id);
    // Open the window first, inside the tap, so iOS doesn't block it as a pop-up.
    const win = window.open('', '_blank');
    const file = await localDoc(id);
    if (file) {
      const url = URL.createObjectURL(file);
      if (win) win.location.href = url; else location.href = url;
      setTimeout(() => URL.revokeObjectURL(url), 60000);
      return;
    }
    if (d && navigator.onLine !== false) { if (win) win.location.href = d.url; else location.href = d.url; return; }
    if (win) win.close();
    $('docErr').className = 'err';
    $('docErr').textContent = 'That document isn\'t saved on this phone yet. Open the app once with signal and it will be.';
  }

  /** Share sheet: Save to Files, AirDrop, Mail… (works offline). */
  async function shareDoc(id) {
    const file = await localDoc(id);
    if (!file) return;
    if (navigator.canShare && navigator.canShare({ files: [file] })) {
      try { await navigator.share({ files: [file], title: file.name }); } catch (e) { /* cancelled */ }
    } else {
      const a = document.createElement('a');
      a.href = URL.createObjectURL(file); a.download = file.name; a.click();
      setTimeout(() => URL.revokeObjectURL(a.href), 60000);
    }
  }

  async function onDocChosen(e) {
    const msg = $('docErr');
    msg.className = 'err'; msg.textContent = '';
    const input = e.target;
    const file = input.files && input.files[0];
    input.value = '';
    if (!file) return;
    const mime = file.type || (/\.docx$/i.test(file.name) ? 'application/vnd.openxmlformats-officedocument.wordprocessingml.document' : /\.pdf$/i.test(file.name) ? 'application/pdf' : '');
    if (!DOC_MIME.test(mime)) { msg.textContent = 'Add a PDF, a photo or a Word document.'; return; }
    if (file.size > MAX_UPLOAD) { msg.textContent = 'That file is larger than 15 MB.'; return; }
    const id = uuid();
    try { await fileStore.put(id, file); } catch (e2) { msg.textContent = 'This phone wouldn\'t store the file (' + e2.message + '). Try again.'; return; }
    msg.className = 'okmsg';
    msg.textContent = syncState.kind === 'offline' ? 'Saved on your phone — it will upload when you have signal.' : 'Uploading…';
    enqueue({ op: 'upload', api: 'docUpload', id, fileKey: id, filename: file.name, mime, size: file.size, ts: Date.now() });
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
      what: q.op === 'void' ? 'undo' : q.op === 'upload' ? (q.api === 'docUpload' ? 'document upload: ' : 'payslip upload: ') + q.filename : q.op === 'payment' ? 'payment'
        : q.op === 'paymentDelete' ? 'payment removal' : q.op === 'leave' ? 'leave' : q.op === 'leaveDelete' ? 'leave removal' : q.action,
      time: q.ts ? new Date(q.ts).toISOString() : '', london: q.ts ? dayKey(q.ts) + ' ' + hm(q.ts) : '', fields: q.fields || undefined,
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
    ['cStart', 'cEnd', 'cSalary'].forEach(id => $(id).addEventListener('input', () => { contractDirty = true; }));
    $('cSave').addEventListener('click', onContractSave);
    $('payFile').addEventListener('change', onFileChosen);
    $('payManual').addEventListener('click', () => openPayForm({ id: uuid() }, { isNew: true }));
    $('payCancel').addEventListener('click', closePayForm);
    $('paySave').addEventListener('click', onPaySave);
    $('payDelete').addEventListener('click', onPayDelete);
    $('payList').addEventListener('click', e => {
      if (e.target.closest('[data-doc]')) return; // let "open payslip" links work
      const li = e.target.closest('[data-pay]');
      if (!li || !li.classList.contains('click')) return;
      const p = payList().find(x => x.id === li.dataset.pay);
      if (p) openPayForm(p);
    });
    $('mwCheck').addEventListener('click', onRateCheck);
    $('docFile').addEventListener('change', onDocChosen);
    $('leaveAllowance').addEventListener('click', e => {
      if (!e.target.closest('[data-opencontract]')) return;
      e.preventDefault();
      const c = contractDoc(); if (c) openDoc(c.id);
    });
    $('docList').addEventListener('click', e => {
      if (e.target.closest('a')) return;
      const o = e.target.closest('[data-open]'); if (o) { openDoc(o.dataset.open); return; }
      const sh = e.target.closest('[data-share]'); if (sh) shareDoc(sh.dataset.share);
    });
    $('leaveNew').addEventListener('click', () => { $('leaveErr').textContent = ''; openLeaveForm({ id: uuid(), from: dayKey(Date.now()) }, { isNew: true }); });
    $('leaveCancel').addEventListener('click', closeLeaveForm);
    $('leaveSave').addEventListener('click', onLeaveSave);
    $('leaveDelete').addEventListener('click', onLeaveDelete);
    ['lType', 'lStatus', 'lFrom', 'lTo', 'lPart', 'lPartFrom', 'lPartTo', 'lDays', 'lCounts', 'lApprovedBy', 'lRef']
      .forEach(id => { $(id).addEventListener('input', onLeaveFormChange); $(id).addEventListener('change', onLeaveFormChange); });
    $('leaveList').addEventListener('click', e => {
      const li = e.target.closest('[data-leave]');
      if (!li) return;
      const x = leaveList().find(y => y.id === li.dataset.leave);
      if (x) openLeaveForm(x);
    });
    $('leaveBank').addEventListener('click', e => {
      const b = e.target.closest('[data-bank]');
      if (!b) return;
      openLeaveForm({ id: uuid(), type: 'Bank holiday', status: 'Approved', from: b.dataset.bank, to: b.dataset.bank, notes: b.dataset.name }, { isNew: true });
    });
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
    document.querySelectorAll('.tabs button').forEach(b => b.addEventListener('click', () => setView(b.dataset.view)));
    $('calPrev').addEventListener('click', () => { calMonth = shiftMonth(calMonth, -1); calSel = calMonth + '-01'; renderCalendar(); });
    $('calNext').addEventListener('click', () => { calMonth = shiftMonth(calMonth, 1); calSel = calMonth + '-01'; renderCalendar(); });
    $('calGrid').addEventListener('click', e => {
      const btn = e.target.closest('[data-key]');
      if (!btn) return;
      calSel = btn.dataset.key;
      renderCalendar();
      $('dayTitle').scrollIntoView({ behavior: 'smooth', block: 'start' });
    });
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
    document.addEventListener('visibilitychange', () => {
      if (document.hidden) return;
      renderAll();
      sync();
      if (view === 'calendar') loadCalendar(false);
      if (view === 'pay') loadPayments(false);
      if (view === 'leave') loadLeave(false);
      if (view === 'docs') loadDocs(false);
    });
    window.addEventListener('pageshow', () => renderAll());
    // Another copy of the app (e.g. a second tab) changed storage: reload our view of it.
    window.addEventListener('storage', () => {
      queue = store.get(KEYS.queue, []); failed = store.get(KEYS.failed, []);
      snap = store.get(KEYS.snap, null); lastTap = store.get(KEYS.lastTap, null); cal = store.get(KEYS.cal, null); pay = store.get(KEYS.pay, null); leave = store.get(KEYS.leave, null);
      docs = store.get(KEYS.docs, null); docCache = store.get(KEYS.docCache, {});
      renderAll();
    });

    let ticks = 0;
    setInterval(() => {
      if (document.hidden) return;
      renderTick();
      if (view === 'calendar' && ++ticks % 30 === 0) renderCalendar();
    }, 1000);
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
  if (cfg && view === 'calendar') loadCalendar(true);
  if (cfg && view === 'pay') loadPayments(true);

  // Exposed for automated tests only.
  window.__hoursClock = { computeDay, model, londonToEpoch, dayKey, setView, get queue() { return queue; }, get failed() { return failed; }, sync };
})();
