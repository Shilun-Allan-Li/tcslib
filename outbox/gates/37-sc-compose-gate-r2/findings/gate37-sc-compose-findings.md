# Pass–shelat Gate 37 — sc-compose

**Verdict: HOLD.** **0 blockers, 2 majors, 1 minor.** The proof audit found no mathematical defect in the three targets. Two exact public-lemma duplicates remain outside the disclosed relations and DL-49. LE-doc also leaves eleven reader docstrings with incomplete formulas.

| Item | Audited revision |
|---|---|
| [Draft PR #324](https://github.com/Shilun-Allan-Li/tcslib/pull/324) | `a6eaebd78c48e7fdfd06263edb84b70bc00ec593` |
| Exchange | `5fab5874b1411ab7a4f8343e6dd4e1add234516b` |
| Campaign records | `c44557596ee5c714e1277891591cc8b5d51a0ab0` |
| PR base / issue base | `6ce4658db08a1dc2a03a149987197660db078011` / `107f1e8c218733eac12d6b9bee6fece441271317` |

## Findings

Paths below are under `TCSlib/Cryptography/`. Both existing public lemmas were verified at the **issue base**, so these are not overlaps introduced by parallel work.

| ID | Severity | File · declaration | Finding and evidence | Proposed fix |
|---|---|---|---|---|
| G37-01 | major | `SecureComputation/ComposeSecurity/Machines.lean:143` · `ComposeMachines.encodeMsgs_append` | Re-proves public `CommitmentLemmas.encodeMsgs_append`, `ZeroKnowledge/CommitmentLemmas.lean:233`. Their complete headers are identical after renaming the two bound arguments. Checkpoint 1's overlap table instead cites `ThreeColoring/Machines.encodeMsgs_eq_flatMap` and calls the append form **new**. The exact public duplicate is not disclosed and is not a DL-49 item. | Obtain an approved import or shared placement and re-derive this declaration directly from the existing public lemma, preserving its header. Correct the overlap record and refresh affected checks. An additional debt disposition would require the user's explicit ruling. |
| G37-02 | major | `SecureComputation/ComposeSecurity/Bounds.lean:53` · `ComposeBound.length_encodeMsgs_le` | Re-proves public `CommitmentLemmas.length_encodeMsgs_le`, `ZeroKnowledge/CommitmentLemmas.lean:241`, with the same hypotheses and conclusion modulo bound names. Checkpoint 2's table reports the derivation through `BinArith.length_encWords_le`, but omits this exact existing public statement. DL-49 does not cover it. | Re-derive from the existing public lemma through an approved import or shared placement, preserving the header; correct the overlap record and refresh affected checks. |
| G37-03 | minor | Eleven reader docstrings; representative: `SecureComputation/ComposeSecurity/Runs.lean:330` · `goodRuns_iff` | A defining-equation/property label followed by an unfinished Lean prefix ending in `…` does not state the complete formula. For example, `goodRuns_iff` cuts off before the first output equality is completed and omits Bob's conjunct entirely. The eleven locations are listed below and in `evidence/docs-duplicates.json`. | Give each reader a complete equation/property, using compact explained subexpressions or wrapping the full formula. Keep the declarations and proofs unchanged. |

The G37-01/02 declarations are named in the reports; what is missing is disclosure of their **exact existing public equivalents**. G37-01 is additionally classified as new. These omissions violate the brief's requirement to identify the nearest existing relative and disclose every overlap. The listed DL-49 debt is not reopened.

The eleven G37-03 locations are:

| Helper file | Readers, with declaration line |
|---|---|
| `Assembly.lean` | `asmView_eq:163`, `asmW_eq:204` |
| `Efficiency.lean` | `runW_eq:117`, `ansW_eq:221`, `composePW_eq:360`, `composeVW_eq:403` |
| `Runs.lean` | `goodRuns_iff:330` |
| `SideA.lean`, `SideB.lean` | `sampleA_eq:114`, `sampleB_eq:112` |
| `Sim.lean`, `Template.lean` | `phiV_eq:108`, `hybW_eq:76` |

**Record correction:** LE-doc contains **20** truncated formula insertions, not the pack's 15; they represent 16 distinct prefixes. All 70 inserted formulas match their declarations/readers in argument order, with truncation where applied. The other truncated entries have substantive accompanying descriptions; G37-03 concerns the eleven label-and-prefix readers above.

## Proof assessment

The author-hosted [Goldreich chapter draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/prot.ps), §7.3.1, Theorem 7.3.3, confirms the citation and simulator-composition argument. The deterministic functionalities, calls-first layout, uniform input bounds and `hM` restriction are explicit adaptations of the frozen interface.

**Efficiency:** `composeP_next_eq_composePW` and `composeV_next_eq_composeVW` hold for every history. The raw functions obtain the count, call inputs, interleaved histories, run tapes, padded answers and main activation through polynomial-time operations. `Efficient.exists_polyTime` and `GI.efficient_of_polyTime` supply the two extraction directions. The run branches establish positive run length before division bounds are used.

**Security:** the delivered proof establishes the five steps:

1. `exists_simulator` constructs each simulator before choosing the distinguisher. `phiV` recomputes call inputs from the simulated main view, uses the answer and fresh-coin blocks, and assembles the view; `phiD` preserves the other party's output.
2. `exists_correct` uses worst-input advice to bound the joint output-error event uniformly. `uprob_not_goodRuns_le` gives the union bound `L(n) ε_c(n)`. Under `GoodRuns`, the real sample equals the assembled sample. The output equalities use `hM`.
3. `exists_hyb_step` resamples one coordinate and fixes the remaining coordinates; `abs_chain_le` telescopes the chain. `exists_gap_le` chooses one worst instance per length and stores its polynomially bounded template as advice, yielding one reduction and a bound uniform over all inputs and indices. The existing multicopy interface is restricted to identical independent samplers; the disclosed generalization here permits shared main coins and index-dependent samplers.
4. `acceptProb_realA_dPhi` / `acceptProb_realB_dPhi` and `acceptProb_post_pre` identify the fully simulated sample and simulator sample with the two hybrid-model samples under the same processing. Hybrid security supplies `ε₃`.
5. Each side is bounded by `L(n)(ε_c(n) + ε₂(n)) + ε₃(n)`, which is negligible. `hbcSecure_compose` chooses `ε = ε_A + ε_B` for each distinguisher and derives nonnegativity from the bounded advantages before bounding both sides by this sum.

Bob's proof uses `ρ.V`'s coins, Alice's received moves, `G.outB`, and `H.lead` fillers. Zero calls leave an empty hybrid-instance family and zero union/chain costs; zero run rounds leave empty message chunks. Real tape cuts are exact, `padFin` is read back through published lemmas, and the documented zero-main-round counterexample explains the necessary `hM` hypothesis.

## Verification

These are source checks and rechecks of the supplied evidence, **not a fresh Lean build**.

| Check | Result |
|---|---|
| Pack integrity | All 20 outer manifest entries, 120 verification entries and 850 review-evidence entries verify; each extracted file set equals its manifest plus `SHA256SUMS`. |
| Source provenance | All 28 bundle sections agree with their pinned git objects; all 98 source-closure files agree with the audited head. The diff reproduces with 16 paths, +4580/−60. |
| Frozen declarations | All 11 pre-existing headers and their order are byte-identical. Replayed decls2: **185 ADDED, 0 CHANGED, 0 REMOVED**. Frozen check at LE-doc: 0 differences. At the head, only the approved `polyTime_compose` sentence changes outside the targets' sketches. |
| Landing edits | LE-doc changes 70 docstrings in 13 files; LE-prose changes one docstring in one file. Removing doc comments leaves identical code in both comparisons. |
| Builds | Raw logs verify 279/279 build results and 18/18 edit-build results, all rc 0 and zero errors in both diagnostic forms. The effective 279 source hashes match LE-doc; 278 match the head, with only the approved owned-file docstring differing. |
| Rule 10 | All **64 head** and **4 base** probes pass. Probe bytes, executed-source hashes, requested names, install records and EOF records agree. Coe-A is canonical. Canonical paired controls replay as ALL_OK: 14 probes, 16 sealed negatives. Strict controls have 24 sealed negatives and exactly the eight documented `ctlCoeReader` positive failures. |
| Axioms and attributes | All 258 census rows use only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, new simp attribute or instance. The three reported abbreviations are generated match auxiliaries. |
| Documentation and sketches | The 12 `PolyTimeComputable` propositions are valid statement formulas. The three no-sketch flags are `rfl` readers with long headers. Substantive long proofs have sketches and step comments. G37-03 remains. |
| Scope and size | Only the authorized 16 paths change. Every line is at most 100 characters; every file is below 1000 lines. The supplied lint line-set comparison is unchanged. |

The published readers, coin/block readbacks, history readings and explicit-unfold evidence support the Rule-10 result. The `getD` uses singled out in the pack read filtered ranges, coin blocks or template word lists; they do not independently re-prove the generic `ofFn` readback. The disclosed private `exists_ofFn_eq` restatement is not treated as undisclosed copying.

The head integration rebuild and the required shared-downstream rebuilds with #313, #318, #319 or #323 remain **maintainer merge conditions**, as dispatched. Their absence is not an audit finding. No PR, branch or dispatch record was modified by this audit.

The gate remains **HOLD until G37-01 and G37-02 are resolved**. G37-03 is a documentation repair, not a proof-correctness objection.

**Notation:** `H`: hybrid protocol; `ρ`: subprotocol; `F`, `G`: target and called functionalities; `n`: security parameter; `L(n) = H.calls.eval n`; `Φ`: view/sample processing; `ε_c`, `ε₂`, `ε₃`: correctness, single-step and hybrid-model bounds; `ε_A`, `ε_B`: the two final party bounds.
