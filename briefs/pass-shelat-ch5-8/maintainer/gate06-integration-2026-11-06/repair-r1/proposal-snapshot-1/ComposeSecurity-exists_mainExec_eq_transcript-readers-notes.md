# ComposeSecurity: first transcript proof reader proposal

Unapplied, single-existing-proof proposal against frozen Git `e9d64158461bfe24ddc88ab885bc4017899b4c16` only.

- Target: `TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean`, `HybridProtocol.exists_mainExec_eq_transcript` (source lines 111–135).
- Frozen source SHA256: `c65f891eaab90cbcd765766ab64b2ec19c740187d4ea830e4125bbfc1093164e`.
- Proposed full source SHA256, calculated in memory: `c1313684273e4ec0196163bdf9fb477bef801d061f3c5166f0f15b63968ccb25`.
- Patch SHA256: `907503b8fcf3504c67c7b2c1dca73cde26586b36a6aeb3a1647116d9acdeecc5`.
- The current mutable library file was not used as the patch base and was not edited.

## Evidence and shared roots

Read as data:
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_025_TCSlib_Cryptography_SecureComputation_ComposeSecurity_HarnessV3.log`

Log SHA256: `d17288c1f5fa1cf74a5356e58deacb207e04d998a12ed9870963c10ffc1629aa`.
The complete installation and EOF markers both verify 632 names (632 active, zero already irreducible). The generic result records exit 1, eight source diagnostics, no fresh object, and unchanged probe SHA256 `9d974ba9d8369761905ccd3d002878b02554517cc0a3f3884bf3e49bfeab49ac`. Its prepared V3 line map adds 50 lines at all eight sites.

| Original source | Probe | Existing proof | Public-reader root |
|---|---|---|---|
| 129, 132 | 179, 182 | `exists_mainExec_eq_transcript` | Tape length is proved as `coins.eval` against requested `coinLen`; `Strategy.coinLen_eq` gives their equality. |
| 135 | 185 | `exists_mainExec_eq_transcript` | Final `rfl` reads sealed `Protocol.transcript` and `transcriptWith`; the two published transcript readers expose exactly the execution. |
| 165, 168 | 215, 218 | `exists_runExec_eq_transcript` | Run-tape length has the same `coins.eval` versus `coinLen` mismatch. |
| 171 | 221 | `exists_runExec_eq_transcript` | Same two transcript readers. |
| 204 | 254 | `compose_msg_bound` | Direct destructuring of sealed `HybridProtocol.PolyTime`; use its existing `polyTime_iff`. The subsequent `hρ` destructuring likewise needs `Functionality.polyTime_iff`. |
| 306 | 356 | `polyTime_compose` | Tuple notation directly constructs sealed `Functionality.PolyTime`; its `polyTime_iff` exposes the target conjunction. `compose_P`/`compose_V` give the composed strategy fields. |

No failure is exempted. The patch repairs only the first three diagnostics' existing proof block. The other three proofs remain unchanged.

## Exact existing contracts used

At each existing length subproof, rewriting `Strategy.coinLen_eq` and then `List.length_take` makes the original `Nat.min_eq_left hrA`/`hrB` have exactly the required type. The final equality uses the two existing transcript readers; afterward both sides contain the identical `exec`, with only projections of the explicit coin pair reducing. No execution definition is unfolded.

```lean
-- TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:126
Strategy.coinLen_eq (S : Strategy) (n : ℕ) :
  S.coinLen n = S.coins.eval n

-- Interaction.lean:422
Protocol.transcript_eq_transcriptWith (π : Protocol) (x y z : List Bool)
  (r : π.ExecCoins π.P x) :
  π.transcript x y z r = π.transcriptWith π.P x y z r

-- Interaction.lean:410
Protocol.transcriptWith_eq (π : Protocol) (P' : Strategy) (x y z : List Bool)
  (r : π.ExecCoins P' x) :
  π.transcriptWith P' x y z r =
    exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
      (π.rounds.eval x.length)
```

The pre-existing `mainExec_eq` use is preserved. `HybridProtocol.Coins` and `Protocol.ExecCoins` are abbreviations, so this proof needs no new Fin transport or owner-side reader. No owner module changes are proposed. All theorem headers, premises, algorithms, data fields, definitions, admissions, and the existing proof sketch are preserved.

## Remaining work and limits

The other three proofs require later invocations. Once `compose_msg_bound` can destruct its predicates, its `rfl` steps at source 212 and 217 are likely further sealed reads. Existing `compose_P_coinLen`/`compose_V_coinLen` and `Strategy.coinLen_eq` expose the required tape lengths. This is a static prediction, not an additional observed diagnostic: the recorded proof stopped at 204. For `polyTime_compose`, the efficient-strategy conclusions must also be transported through `compose_P`/`compose_V`.

Static verification regenerated the unified diff from the exact frozen bytes: only three lines within one existing proof change, the theorem header and every byte outside the proof are preserved, and the admission census is unchanged. The proposed full source exists only in memory. No library source, Git state, native object, or active evidence file was changed. No Lean/cache/build command or computer app was used. The proposed tactic applicability remains uncompiled; root must apply and check separately.

**Ready to run**
