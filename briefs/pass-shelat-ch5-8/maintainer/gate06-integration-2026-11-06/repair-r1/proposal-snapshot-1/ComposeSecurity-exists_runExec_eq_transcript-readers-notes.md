# ComposeSecurity: run-phase transcript proof reader proposal

Unapplied proposal for one existing proof: `HybridProtocol.exists_runExec_eq_transcript` in `TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean` (frozen source lines 145–171).

- Frozen Git context: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
- Frozen source SHA256: `c65f891eaab90cbcd765766ab64b2ec19c740187d4ea830e4125bbfc1093164e`.
- Prior main-phase patch SHA256: `907503b8fcf3504c67c7b2c1dca73cde26586b36a6aeb3a1647116d9acdeecc5`.
- In-memory input after the prior patch SHA256: `c1313684273e4ec0196163bdf9fb477bef801d061f3c5166f0f15b63968ccb25`.
- Combined proposed full source SHA256: `2e578fd4004864bbdb0eeecc3777e7c29e40855f591028913b46fc9714b57e5f`.
- This separate patch SHA256: `165f782c1798627ebce33e8d176b1b403467158c48392dca5c3c35f2532680c9`.

The prior main-phase proposal was reconstructed and compared byte-for-byte to its saved patch, then composed only in memory. This patch is a diff from that intermediate source to the next source. The current mutable library file was neither read as the patch base nor written.

## Root and repair

The valid V3 ComposeSecurity seal has run-phase diagnostics at probe 215, 218, 221, corresponding to original source 165, 168, 171. The tape-length equations prove equality with `ρ.P.coins.eval` and `ρ.V.coins.eval`; `exists_ofFn_eq` requests equality with the corresponding sealed `coinLen`. Compose the existing `length_runTape hrA hj`/`hrB` equations with the symmetric public `Strategy.coinLen_eq` equations. These are term expressions inside the existing proof; no new tactic block is introduced.

The final `rfl` attempted to reduce foreign `Protocol.transcript` and `transcriptWith`. Replace it with rewrites by the existing `Protocol.transcript_eq_transcriptWith` and `Protocol.transcriptWith_eq`. Both sides then contain exactly the same `exec` and explicit coin lists; only the projections of the explicit coin pair reduce.

Existing public contracts, all present in the frozen import closure:

- `Compose.length_runTape` in `SecureComputation/Compose.lean:179`: if `r.length = c₀ + L * c` and `j < L`, then `(runTape c₀ c j r).length = c`.
- `Strategy.coinLen_eq` in `ZeroKnowledge/Interaction.lean:126`: `S.coinLen n = S.coins.eval n`.
- `Protocol.transcript_eq_transcriptWith` at `Interaction.lean:422`: the honest transcript equals `transcriptWith` against the honest prover.
- `Protocol.transcriptWith_eq` at `Interaction.lean:410`: `transcriptWith` equals `exec` on the two coin lists and protocol move count.

No missing owner reader, Fin transport, new premise, or helper definition is needed. The existing run-input and `runExec_eq` reader uses are preserved. The theorem header, scale, premises, algorithmic definitions, data fields, admissions, and proof sketch are unchanged.

## Static validation and limits

The generated diff changes only this one existing proof. Its header and all source outside its body are identical to the in-memory intermediate version; its number of tactic blocks is unchanged. The admission census is unchanged. Neither predicate proof was repaired: `compose_msg_bound` and `polyTime_compose` remain for separate invocations, with their public-iff roots recorded in the prior notes.

Only this patch and these notes were saved under ignored Gate06 repairs. No library/Git/evidence mutation, Lean/cache/build command, computer app, or native process was used. This proposal remains uncompiled; root must apply/check separately.

**Ready to run**
