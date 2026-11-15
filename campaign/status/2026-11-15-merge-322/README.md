# #322 merge and snapshot adoption (2026-11-15)

Seyoon merged #322 (Ladner fills 5 and 6: target 2 `SAT_H_mem_NP` and target 5 `SAT_mem_P_of_padSAT_NPHard`) at
`d811bdaaf5e923b2a57f0453135af5c7ee37713a`. Outside `campaign/` it equals the gate 140 replay's tree `a25f1e98`, so that
replay's output becomes the campaign snapshot (`oleans-cd811`, 876 objects, each rehashed on disk against the replay's map).
`oleans-c3464` is kept as the fallback. Ladner has one admitted target left, `SAT_H_intermediate`. See `ADOPTION.json`.
