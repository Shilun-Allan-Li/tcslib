# Learning: one public-negligibility reader repair

**UNAPPLIED; native elaboration and sealing pending.** Frozen Gate06 head supplied by root:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`. The source matches the completed V3 manifest's
frozen fingerprint. No library edit, Lean/cache command, Git command, or app was used here.

Exact target: `TCSlib.Cryptography.Randomness.not_weakLearnsUnder_prfConcept`.
The two valid-seal diagnostics at **probe line 172** map to **frozen source line 122**
through `source_to_probe_lines`. Thus 172 is the probe coordinate, not the original source line.
The first diagnostic applies `predictAdv_prfConcept_negligible F hF A m` to exponent `1` while
its result has sealed foreign type `Negligible ...`. The `rcases` failure at that same location
cascades from the invalid application. INSTALL and EOF markers verify all 1,625 requests
(1,606 active, 19 already irreducible), so these are source diagnostics, not harness failures.

The proposal changes only this existing proof block: retain the negligibility result as local
`hneg`, rewrite its type through public `negligible_iff`, and then extract the exponent-one
bound. The remaining quantitative contradiction/PAC argument is unchanged. The reader is the
existing theorem at `Foundations/Negligible.lean:62`; no foreign definition is unfolded.

All public headers, hypotheses, algorithms and admissions are unchanged. The theorem still
depends on the admitted `predictAdv_prfConcept_negligible`; no substantive learning/security
proof is filled. No new helper declaration or tactic block is introduced. Static one-hunk
application in memory reproduced the proposed bytes, and all bytes outside the target block,
its public header, and admission counts were checked unchanged.

| Artifact | SHA-256 |
|---|---|
| Frozen `Learning.lean` | `d2657df0a9e1a17c466e93ba434c465545cc5ae589f82d6b399482b443e710ae` |
| Proposed `Learning.lean` | `f5beda733b7cf1014146237eea3953ae43f340d628a1827534ae1246e5fbcc1a` |
| Proposal patch | `7418e24ea8a841ebf77fc2d45bd65643ececb656c191075fd39ecf4f09008396` |
| Public reader home `Negligible.lean` | `5e6d2c9e69dbfe012c36a92bad05ec27e691c044dae73a7277b9599902074e1a` |
| Completed V3 probe log | `d6044e20febc1a86db99b33d85a311c64cbd07549344debfcd86efe41e13181f` |
| V3 seal manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_022_TCSlib_Cryptography_Randomness_Learning_HarnessV3.log`.
Root retains application and serial native checking. This proposal addresses the two original
Learning diagnostics by source inspection; it does not claim a passing repaired seal.
