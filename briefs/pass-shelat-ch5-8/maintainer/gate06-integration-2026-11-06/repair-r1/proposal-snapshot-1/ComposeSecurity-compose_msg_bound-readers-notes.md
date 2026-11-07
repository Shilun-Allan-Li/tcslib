# ComposeSecurity: composed-message bound reader proposal

One unapplied existing-proof repair for `HybridProtocol.compose_msg_bound` in `TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean` (frozen source lines 198–268).

- Frozen Git context: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
- Frozen source SHA256: `c65f891eaab90cbcd765766ab64b2ec19c740187d4ea830e4125bbfc1093164e`.
- Prior main-phase patch SHA256: `907503b8fcf3504c67c7b2c1dca73cde26586b36a6aeb3a1647116d9acdeecc5`.
- Prior run-phase patch SHA256: `165f782c1798627ebce33e8d176b1b403467158c48392dca5c3c35f2532680c9`.
- Input after composing those two only in memory: `2e578fd4004864bbdb0eeecc3777e7c29e40855f591028913b46fc9714b57e5f`.
- Combined proposed full source SHA256: `efce7ecd7331db2c434308d2f3aebb3af6bbbc7b5a46e1e5f880928efeafd17a`.
- This separate patch SHA256: `e2015ed45fadd7b7ea955e80964a666b671d6028a255adb1b4abf9404657f50f`.

Both earlier patches were reconstructed and matched byte-for-byte against their saved artifacts. This patch is generated from that intermediate source to the next source. No mutable library source was used as the patch base or edited.

## Observed root and changes within the same proof

The valid V3 seal 025 reports the predicate-destructuring error at original source 204 (probe 254): `H.PolyTime F` is not inductive while sealed. Read it through `(HybridProtocol.polyTime_iff H F).mp hH`, preserving the existing destructuring pattern. The subsequent `hρ` destructuring has the same issue for `Functionality.PolyTime`; use `(Functionality.polyTime_iff G ρ).mp hρ`.

The original proof stopped at 204, so the following are static latent-read diagnoses rather than additional observed diagnostics. At original 212 and 217, `rfl` computes the composed protocol's tape lengths through sealed `compose` and `Strategy.coinLen` (and ultimately `composeP`/`composeV`). Replace each two-line length proof with `simpa only [List.length_ofFn, Strategy.coinLen_eq] using` the existing `H.compose_P_coinLen ρ ...` or `H.compose_V_coinLen ρ ...` theorem. The public length theorem supplies the structure-field equation; the simplification uses only published equation lemmas, on both the target and supplied equation. No ordinary foreign body is read.

## Exact contracts and remaining proof review

Existing frozen owner APIs:

- `HybridProtocol.polyTime_iff` (`SecureComputation/Hybrid.lean:232`): `H.PolyTime F` iff efficient main parties, the two polynomial-time call-input clauses, and the main-message bound for all answer strings of the required lengths.
- `Functionality.polyTime_iff` (`SecureComputation/Defs.lean:161`): `G.PolyTime ρ` iff efficient parties and its honest-message bound.
- `HybridProtocol.compose_P_coinLen` (`SecureComputation/Compose.lean:440`): `(H.compose ρ).P.coinLen n = H.main.P.coinLen n + H.calls.eval n * ρ.P.coinLen n`.
- `HybridProtocol.compose_V_coinLen` (`Compose.lean:444`): `(H.compose ρ).V.coinLen n = H.main.V.coinLen n + H.calls.eval n * ρ.V.coinLen n`.
- `Strategy.coinLen_eq` (`ZeroKnowledge/Interaction.lean:126`): `S.coinLen n = S.coins.eval n`.

Review of the remaining same proof found its TCSlib reads already use theorem interfaces: the two repaired transcript-existence lemmas; `runMsg_mem`; `compose_transcript`; and `slotFromB_eq`/`slotFromA_eq`. The branch splits treat `moverIsV` opaquely. Filler bounds reduce only the core empty list. The arithmetic argument uses the established tape-length equations. `PolyExpr.eval_add` remains a published evaluation reader for approved polynomial notation. No new owner reader, host, helper, Fin transport, or premise is required.

## Static checks and limits

The diff changes only four sites inside this one existing proof. It preserves its header, every source byte outside the proof, its number of tactic blocks, all algorithms/data fields/definitions, and the admission census. Its mathematical proof sketch remains accurate. `polyTime_compose` is unchanged and remains the next separate invocation.

Only this patch and notes were saved under the ignored Gate06 repairs directory. No library/Git/evidence mutation, Lean/cache/build command, computer app, or native process occurred. In particular, the proposed `simpa only` applicability is uncompiled and needs root's later native check.

**Ready to run**
