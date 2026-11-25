# Working in this repository

- **Commit straight to `main`.** No feature branches and no pull requests are needed
  for this project. "Commit and push" means commit on `main` and push `main`.
- **"Remember X" means write it into the repository** (the README or another project
  file), not only into an assistant's private memory, unless told otherwise.
- **The typeset (LaTeX) statement changes notation, never the statement.** See
  "A rule for the typeset statement" in the README before touching
  `public/lean-latex.js`.
- Tests: `node --disable-warning=ExperimentalWarning --test`. Write the test first.
- The database is not in git. After a change to `lib/graphdb.js` or `lib/reach.js`
  that affects what is stored, run `node build.js` again and restart `node server.js`.
