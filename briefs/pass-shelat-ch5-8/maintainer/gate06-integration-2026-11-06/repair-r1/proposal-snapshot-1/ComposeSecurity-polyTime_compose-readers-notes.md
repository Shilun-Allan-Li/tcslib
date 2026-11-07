# ComposeSecurity: final polynomial-time constructor reader proposal

One unapplied existing term-proof repair for `HybridProtocol.polyTime_compose` in `TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean` (original source 304–306).

- Frozen Git context: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
- Frozen source SHA256: `c65f891eaab90cbcd765766ab64b2ec19c740187d4ea830e4125bbfc1093164e`.
- Input after composing the three previous reader proposals only in memory: `efce7ecd7331db2c434308d2f3aebb3af6bbbc7b5a46e1e5f880928efeafd17a`.
- Combined proposed full source SHA256: `040577e7d6e02546a02c7bd55b92c2b1e894ab46fca16e5abd2fc23b80f0e23f`.
- This separate patch SHA256: `8c96cc500bb7fa74642f1d34157090eaa23bec96d26a10003249e6ecacb3787c`.

The previous three patches were hash-checked and applied by a strict in-memory unified-diff parser, validating every context line and hunk count. The input source was obtained from the exact frozen Git object; the current mutable library file was not used as the base or edited.

## Root and complete repair of this term proof

The valid V3 seal 025 reports the original tuple constructor at source 306 (probe 356): sealed `F.PolyTime (H.compose ρ)` is not inductive. First use `(Functionality.polyTime_iff F (H.compose ρ)).mpr` to construct the conjunction through its published contract.

That conjunction's strategy clauses mention `(H.compose ρ).P` and `(H.compose ρ).V`, while the existing efficiency results mention `H.composeP ρ` and `H.composeV ρ`. The old constructor also relied on reducing the sealed composed protocol to match those types. Transport each proof with `Eq.mpr` applied to `congrArg Strategy.Efficient` of the public `H.compose_P ρ` or `H.compose_V ρ` equation. This treats the efficiency predicate as an opaque function on strategies; it does not inspect or unfold its definition. The message-bound result already has exactly the public conjunction's final clause and is reused unchanged.

Exact frozen owner interfaces:

- `Functionality.polyTime_iff` (`SecureComputation/Defs.lean:161`): `F.PolyTime π ↔ π.P.Efficient ∧ π.V.Efficient ∧` the existential uniform polynomial honest-message bound.
- `HybridProtocol.compose_P` (`SecureComputation/Compose.lean:421`): `(H.compose ρ).P = H.composeP ρ`.
- `HybridProtocol.compose_V` (`Compose.lean:424`): `(H.compose ρ).V = H.composeV ρ`.

No remaining part of this term proof requires a foreign definition's body. The hypotheses are passed unchanged to existing theorems. No missing owner reader, helper definition, tactic block, premise, or Fin transport is added. The theorem header and all data/algorithm/security statements are preserved.

## Validation and limits

The generated diff changes only the term proof of `polyTime_compose`; its header and all source outside that proof are byte-identical to the intermediate input. The diff was replayed in memory and reproduced the proposed source exactly. No new tactic block is introduced and the admission census is unchanged. The existing admitted efficiency proofs and composition security proof remain admitted; this proposal makes no stronger claim about their status.

Only this patch and these notes were saved under ignored Gate06 repairs. No library/Git/evidence mutation, Lean/cache/build command, computer app, or native process occurred. In particular, the proposed term's elaboration is uncompiled and requires root's later native check.

**Ready to run**
