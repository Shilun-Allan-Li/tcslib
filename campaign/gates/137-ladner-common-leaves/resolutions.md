# Gate 137 resolutions for #310

Round 1 audited `07272ed4d91b22357b5a81a1f65d6787c6210e93` and returned **HOLD (0 blockers,
1 major, 1 minor, 9 notes)**, recorded verbatim as `findings.md` (SHA-256 `4553f712506de595b8597c2c5aed1f9695879454d4e5992e488807da857c3ff3`).

| Finding | Resolution |
| --- | --- |
| G137-01 · `ladner_parse_prefix`'s inline `hr` re-proves `BinArith.uRest_encodeNat` (major) | **Fixed in Lean** (`3b45471c`). Seyoon approved (2026-11-14) the reader `BoolCircuit.encodeNat_eq (k) : encodeNat k = List.replicate k true ++ [false]`, beside `encodeNat` in `CircuitComplexity/UnaryCode.lean`, not `@[simp]`, proved by `rfl`. `hr` is now `uRest_encodeNat n w` rewritten through it (`List.append_assoc`, `List.singleton_append`), with no induction. UnaryCode becomes a fifth owner, and the replay closure grows accordingly. The delivery report's claim that nothing proved was copied was inaccurate on this point; the report is data and stays as delivered. |
| G137-02 · Basic, AddSub and Words absent from the carrier (minor) | **Fixed in the round-2 carrier.** It holds every wide-screen population file at BASE and HEAD under `screen-wide/<side>/population/`, each checked against the screened export; identical copies share one blob. |

Notes G137-03 to G137-11 need no action. G137-09 asked that G137-01 be recorded, which this table does. Round 2 follows (`pack-r2.md`).
