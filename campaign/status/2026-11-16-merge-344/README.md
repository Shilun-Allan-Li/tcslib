# Snapshot adoption after #344 (2026-11-16)

#344 (gate 151, C1E-1 trims in `ClassNP/ExhaustiveReplay`) merged at the commit in ADOPTION.json,
after #343. Its merged-tree replay on `oleans-cf8187` (the #343 merge's snapshot) rebuilt the
4-module downstream closure (4 passed, 0 failed, 0 admissions), and the merge's Lean equals that
replay's prospective tree `6a905753`. No separate adoption replay was run. Its output is adopted
as `oleans-cfb6f2` (874 objects, rehashed on disk against the replay's map). `oleans-cf8187` is
kept as fallback. See ADOPTION.json.
