# Snapshot adoption after #343 (2026-11-16)

#343 (gate 150, R4 kind 3: padding through `Build/EmitIterEmbed`, `embedCfg`/`emitCfg` field
equations) merged at the commit in ADOPTION.json. Gate 150's replay was the merged-tree replay:
it rebuilt the 227-module downstream closure of the four owners on `oleans-cc011` (227 passed, 0
failed, 28 pre-existing admissions), and the merge's Lean equals its prospective tree `57994ff1`.
No separate adoption replay was run. Its output is adopted as `oleans-cf8187` (874 objects,
rehashed on disk against the replay's map). `oleans-cc011` is kept as fallback. See ADOPTION.json.
