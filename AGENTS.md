# Rook Solitaire repository instructions

These instructions apply to the entire repository.

- Treat `index.html` as the complete Rook Solitaire application. Preserve its existing HTML, CSS, JavaScript, gameplay, settings, sounds, animations, and browser `localStorage` behavior unless the user explicitly requests a change.
- Keep the app static and self-contained. Do not introduce a framework, build step, or server unless the user explicitly requests one.
- After every requested repository change, verify the edited files, commit the completed change directly to `main` with a concise descriptive message, and push `main` to `origin` before ending the task.
- Never force-push, rewrite published history, or discard unrelated user changes.
- If a push is rejected because the remote changed, fetch and integrate the remote safely, then retry. If authentication or a real conflict blocks the push, preserve the local commit and report the exact next step.

