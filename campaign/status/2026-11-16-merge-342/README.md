# Snapshot adoption after #342 (2026-11-16)

#342 (gate 149, R4-2: `ClassNP/CleanCall`) merged at the commit in ADOPTION.json. Gate 149's replay
was the merged-tree replay: it rebuilt the 53-module downstream closure of the four owners on
`oleans-cc2ad` (53 passed, 0 failed, 0 admissions), and the merge's Lean equals its prospective
tree `2408eb32`. No separate adoption replay was run. Its output is adopted as `oleans-cc011`
(874 objects, one more than before for the new module; rehashed on disk against the replay's
map). `oleans-cc2ad` is kept as fallback. See ADOPTION.json.
