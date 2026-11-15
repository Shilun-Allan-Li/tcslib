# #320 merge and snapshot adoption (2026-11-15)

Seyoon merged #320 (Ladner fill 3: target 1 part A, through `ladner_candidate_FP`, with the private dedup helpers) at
`1320a5c8ce93f4644c2c92ed32e2768ed07ea9bb`. Outside `campaign/` it equals the gate 138 replay's tree `f46a0aed`, so that
replay's output becomes the campaign snapshot (`oleans-c1320`, 876 objects, each rehashed on disk against the replay's map).
`oleans-cfe8a` is kept as the fallback. See `ADOPTION.json`.
