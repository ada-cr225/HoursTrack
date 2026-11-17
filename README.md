# Hours Clock

An offline-first phone app for clocking in and out, synced to a Google Sheets hours log.

Every tap is saved on the phone first, with its own ID and the time it happened, then sent to
the sheet. With no signal it waits on the phone and is retried automatically. The sheet ignores
repeats, so a retry can never double-count. Taps that arrive late are marked "synced late" in
the sheet, so the record stays honest.

This repository holds only the app's code. Your sheet's URL and access key are typed into the
app on your phone and stored there. They are never in this repository.

## Files

| File | Purpose |
|---|---|
| `index.html` | The app's layout and styles |
| `app.js` | The app: offline queue, sync, timer, pay check |
| `sw.js` | Service worker that keeps the app available with no signal |
| `manifest.webmanifest`, `icons/` | Home Screen name and icon |

## Updating

1. Edit the files.
2. Bump `CACHE` in `sw.js` (for example `hours-clock-v1.0.1`) so phones fetch the new version.
3. Commit. GitHub Pages republishes in about a minute.
4. Close and reopen the app twice: the first launch downloads the update, the second runs it.
