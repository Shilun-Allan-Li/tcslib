# Snapshot adoption after #335 (2026-11-16)

#335 (gate 146, R4 UH) merged at the commit in ADOPTION.json. Its merged-tree replay (gate 146,
`evidence/merged-tree/`) rebuilt the 28-module downstream closure of `CookLevin/Hardness` on
`oleans-c56ab`: 28 passed, 0 failed, 0 admissions. The merge's Lean (`.lean` files, toolchain and
manifest) equals that replay's prospective tree `f427699f`, so no separate adoption replay was
run. Its output is adopted as `oleans-cc2ad` (873 objects, rehashed on disk against the replay's
map). `oleans-c56ab` is kept as fallback. See ADOPTION.json.
