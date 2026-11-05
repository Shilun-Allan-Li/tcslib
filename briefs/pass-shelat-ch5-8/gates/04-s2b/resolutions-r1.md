# Gate 04 (S2b, #195): round 1 resolutions

- **Round 1:** findings `findings/gate04-s2b-findings.md`, verbatim, SHA-256
  `24949274f226fb42bc5ea4d69e39feb50e7c4bee5e3aec56c04d0a9625054246`; head
  `afe5982f612081bba2fbcec9ab41adcbbc118b13`. Counts: **0 blockers, 2 majors (F01, F02), 4 minors
  (F03–F06).**
- **Review:** `review/gate04-review.md`: all six true, severities agreed. It adds N1 (proposed major:
  T1/T2 do not cover the reductions they are cited for) and N2–N7 (minor).
- **Rulings (user, 2026-11-05):** R-04-1 strict unary decoding with converses; R-04-2 every
  equation lemma S2b's proofs consume, in #195 (S2b's, S2a's and ch. 2–4's `Interaction.lean`);
  R-04-3 extend T0–T2 before the efficiency fill.
- **Repairs:** two commits on #195's branch after `afe5982f`:
  - `f6d573075e6e71f00d3f8e29a8285a585482d589`: F01–F04, F06, N5, N6 (19 files, +832/−78);
  - `243598b7cb0c3fdd50b22a92a011f1b77f55c8c6`: R-04-3 (N1) (`Games/Efficiency.lean`, the
    `Games/Bridges.lean` facade).

| Item | Severity | Resolution |
|---|---|---|
| F01 | major | **Fixed** (R-04-1). `decodeIdx` requires `iw = List.replicate iw.length true`; `decodeIdx_replicate` re-proved; converses `decodeIdx_eq_some_iff`, `decodeIdx_eq_none_iff`, `decodeBitMove_eq_query_iff`, `decodeBitMove_of_not_canonical`; `encodeBitMove` with `decodeBitMove_encodeBitMove` and `encodeBitMove_injective`. No statement text changes; no notion changes meaning (every one quantifies over all adversaries). |
| F02 | major | **Fixed** (R-04-2). 91 public equation lemmas next to their definitions in 14 files (BitCodec 16, Protocols 10, Efficiency 9, Machines 8, PRF 7, `Interaction` 7, Simulate 6, Bridges/Machines 6, Bridges/Strategies 6, OracleAdversary 5, OracleComp 4, Advantage 3, Bridges/QueryTree 3, Bridges/Experiments 1); the 16 consumer proofs re-pointed, plus `Hopping.prob_eq_until_bad`. A rule-10 seal check (`attribute [local irreducible]` on other files' definitions) passes on the re-pointed files, and fails on the old versions. |
| F03 | minor | **Fixed.** `PolyHandler.answer`'s componentwise default and `InteractiveHandler`'s joint default stated (N6 folded in). |
| F04 | minor | **Fixed.** "at most `perCall(n)` outer queries, in at most `perCall(n) + 1` rounds". |
| F05 | minor | **Fixed at staging:** the evidence is regenerated at the new head (`evidence-r2/`). The round 1 attestation should have read 237 public theorems, 235 standard and T1/T2 with `sorryAx`; the 14 private theorems are covered by the replay. |
| F06 | minor | **Fixed.** Six docstrings made to match their statements (`multiMsgAdv_boundedBy`, `decodeFin_runAt_prfDec_of_not_wf`, `pairFstD_pairFstD_histBlock`, `take_drop_ofFn_blocks`, `exists_queryChain_nuppt`, `tableDist`/`ggmDist`). |
| N1 | major (proposed) | **Fixed** (R-04-3). `seedIn` (the context `⟨1^n, ⟨z, ω⟩⟩`); `PolyHandler` gains `advIn` and `out`, `InteractiveHandler` gains `advIn`, `outLen`, `finCall` and `finRun`, each with equation lemmas. T1 restated with exact output; T2 with the finalization and budget `q·perCall + finCall`; the companion `exists_toCompOn_of_toComp` and T4 `exists_toOracleAdversary_of_bitCodec` stated. All four are `sorry` (the fill's targets). The eight prong sketches are re-cited at integration (table below). |
| N2 | minor | **Fixed at staging:** check 8 and the seal evidence are in `evidence-r2/`. |
| N3 | minor | **Recorded:** `Bridges/Strategies.lean`'s promise of later results is reworded at integration with the prongs that supply them. |
| N4 | minor | **Recorded:** `take_drop_ofFn_blocks` is ledgered with the `blocks` family (G3-5; DL-9 onward), paid back in the ch. 2–4 clean-up PR. |
| N5 | minor | **Fixed.** `Option.elim_none`/`_some` replace `simp [Option.elim]`. |
| N6 | minor | **Fixed** with F03. |
| N7 | minor | **Fixed at staging** with N2. |

**Prerequisites recorded for the efficiency fill** (rule 10; ch. 2–4 clean-up PR): `NUPPT.coinLen_eq`
beside `coinLen` (`Complexity/Randomized/PPT.lean`), and `decodeOracleMove`'s case lemmas beside its
definition.

**The eight prong sketches to re-cite** (docstrings only; no statement changes):

| Site | Must cite |
|---|---|
| Thm 135.4, prong A `PRFMAC.lean` | the companion (input-free forger), then **T2** (forwarding handler; `finish` with `finCall = 1`: query at `m`, freshness from the state; `outLen = 1`; budget `q + 1`), then **T4** to reach `OracleEnsemble.Indist` |
| Thm 137.2, `Lamport.lean` | **T1**: `advIn` builds `pk` from `y = z` and the seed; answer or abort; `out` returns `σ'_i` |
| Thm 144.1 `B`, `HashAndSign.lean` | **T1**: `advIn = ⟨pk, i⟩`; `out = (m, m′)` |
| Thm 144.1 `C`, `HashAndSign.lean` | **T2**: `advIn = ⟨pk, i⟩`; queries forwarded as `h_i(m)` (`perCall = 1`); `finish` with `finCall = 0` |
| Thm 168.2, prong C `PRFScheme.lean` | **T2** (Enc and the challenge by oracle queries; `b` in the seed; `finish` compares the guess with `b`) + **T4** (+ the companion) |
| Thm 170.4, `CCA2Scheme.lean` | **T2** (`Enc′`/`Dec′` through the oracle; `k₁` in the seed) + **T4** (+ the companion), lengths `2n` |
| Thm 175.9 (⇒), `NonMalleable.lean` | **T2**: `advIn = pk`; `Dec` forwarded; `finish` with `finCall = ℓ` then `D` (advice through `z`; `exists_withAdvice`/`exists_comp`); budget `q + ℓ` |
| `padded_cpa`, `PublicKey.lean` | **T1**: `advIn = pk` from `z = ⟨pk, c⟩`; the challenge answered with `padCt L c`; `out` flips or zeroes the bit |
