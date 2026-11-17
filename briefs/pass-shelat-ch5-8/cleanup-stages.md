# Pass–shelat cleanup: the three stages (Seyoon, 2026-11-17)

The remaining Pass–shelat cleanup runs in three stages. Rebuilds and gates happen only between stages. The GSW and IBE
items, including DL-50, are out of scope here.

## Stage 1: promotions (additive only)
- Publish the general forms named by the duplication ledger in their natural shared homes:
  - `Games`: the ETT simulation and coin-tape forms (DL-40).
  - `Asymptotic/Sampling`: `statClose_of_uprob_ne` (DL-51).
  - One common `encodeMsgs_eq_encWords` (DL-49, extended).
  - The generic getD reader (DL-47).
  - `length_ofFn_coins` at the `NUPPT` layer (DL-48).
  - The general forms of DL-35 and DL-41 to DL-46.
  - DW-9's view versions of `host_dispatch`, `host_branch` and `host_halt`.
- Every new public declaration has readers, a formula docstring and a proof. No existing proof is touched.
- **Gate:** a statement-style audit of the new public API. Is each lemma general, correctly homed, and free of duplication?

## Stage 2: re-point and prune (proof-only)
- Re-point every ledgered copy to its promoted form (DL-35, DL-38 to DL-49, DL-51, DL-52). This includes the
  `OTAnswerWords` pair against #324's `HybridProtocol.length_answers*`, and the ETT averaging-bound copy against the bb1-sim
  promotion in `Games/Probability`.
- Delete the dead private copies and the public host lemmas left unused by DW-5.
- Clear DW-9's 26 seal failures and `Uniform.lean`'s 4 inherited failures (SY-F07) through readers.
- Sweep in small lint and doc nits, such as the `BobIO` unnecessary `simpa`.
- **Gate:** a proof audit, plus the full Rule 10 seal sweep over every touched owner. Target: every Pass–shelat ledger row
  closed, and no seal failure in any touched file.

## Stage 3: closure (Run 4)
- The PS10 ch. 5–8 ingest (DW-8; docs-only, may run externally during Stage 1 or 2), and a citation pass against it.
- The census and axiom prints, the lint baseline, and the drift attestation.
- The completion record.
- **Gate:** the closure audit. Then the merge to `main`.

## Preconditions and order
- **#347 (DW-5) merges before Stage 1,** because both touch the host files.
- **Stage 1 starts after the bb1-sim Games statement PR merges.** That PR promotes the averaging bound into
  `Games/Probability` (part of DL-40), and Stage 1 should not race the GSW/IBE PRs on shared files.
- Each stage is one external job, or two with disjoint file sets. Each is validated by one merged-tree replay on the
  snapshot (`workflow.md` §6.1).
- **Out of scope:** DW-1/DW-2 (uniform simulators), which Seyoon ruled "probably after merging into `main`", and DW-3 (notes).

## Parallel with the GSW/IBE work (Seyoon, 2026-11-17)
Seyoon asked for the cleanup to run in parallel with the GSW/IBE work "to the extent possible". So:

- **Stage 1 starts now** as an external job. It owns no file that the running GSW/IBE jobs edit: not
  `Games/Probability.lean` or `Games/Relational.lean`, not `Pairing/Group.lean`, not `Complexity/CircuitComplexity/**` or
  `Complexity/BranchingPrograms/**`, not `ComputationalModels.lean` or `machine-library-design.md`, and nothing under
  `AdvancedEncryption/**`. Facade import lines may be edited, since they merge as unions. The averaging bound (part of
  DL-40) is left to the bb1-sim promotion.
- **Stage 1 is stacked on #347 (DW-5),** because DW-9's view versions live in the same host files. Gate 47 audits #347 and
  Stage 1 together.
- **The PS10 ch. 5–8 ingest runs now** as a separate external docs job. Stage 3 folds it in.
- **Stage 2 starts after Stage 1 and the bb1-sim Games PR merge.**

## Stage 1 rulings CS1-Q1 to CS1-Q12 (Seyoon, 2026-11-17)

| # | Ruling |
|---|---|
| CS1-Q1 | **Include DL-39** in Stage 1: the 14 `FinDist` facts, protected, in `InformationTheory/{FinDist,Samples,Entropy}.lean`. |
| CS1-Q2 | **The six statement/body changes are approved now.** Stage 2 removes both DL-35 aliases of `blocks`, the private one and the public one in `EnsemblesLemmas.lean`. The gate checks the six changes explicitly. *(changed: was private only)* |
| CS1-Q3 | Stage 2 moves `MachineCodec.ext_of_fields` verbatim to its shared home. |
| CS1-Q4 | The `fwdHandler` generalization is taken out of the cleanup. Hosts change only by their own gated design. |
| CS1-Q5 | DL-41: the `splitBits` word readers `Authentication.ofFn_splitBits_fst/_snd` in `Authentication/Encoding.lean`. |
| CS1-Q6 | DL-48: `NUPPT.length_ofFn_coins` in `Complexity/Randomized/PPT.lean`, beside `Coins`. |
| CS1-Q7 | DL-51: `StatClose.of_uprob_ne` in `Asymptotic/Sampling.lean`. |
| CS1-Q8 | **DL-49's ThreeColoring helpers move to a shared machine layer.** Stage 1 adds them additively to a shared machine-layer module that both `ThreeColoring/Machines` and `ComposeSecurity/Machines` can import; Stage 2 re-points both. The helpers include `encodeMsgs_eq_flatMap`, `msgAt_encodeMsgs`, the `padTo` family, `polyTimeComputable_flatMap_range`, `flatMap_range_ite` and `iterSnd_poly`. *(changed: was importing ThreeColoring/Machines)* |
| CS1-Q9 | **DL-43's `mul_prob_le_expect` goes to `Games/Probability.lean` in Stage 2**, after the bb1-sim Games PR merges and frees that file. It is a small additive exception to Stage 2. Lamport is then re-pointed. It is not in Stage 1. |
| CS1-Q10 | Near relatives that are not instances get no target; they stay as notes. |
| CS1-Q11 | Promotion requests with no ledgered copy are declined for now. |
| CS1-Q12 | DL-47: the Complexity-side inline chains stay as they are; only the Cryptography-side copies are re-pointed. |

## PS10 citation fixes go into Stage 2 (2026-11-17)
The `ps10-cite-check` delivery (exchange `69add654`; `ingests/ps10-cite-check-final-r1/REPORT.md`) found 40 content mismatches at 40 sites under 15 locators (Tier A: 19 under Theorem 180.1, 17 of them one recurring "step 4" label) and 21 advisory notes (Tier B). All 67 locators exist with the cited kind and page. The Tier A corrections, docstring-only, are part of Stage 2; the Tier B notes are applied where they change what a reader is told.

## Historical seal debt (DW-10; Seyoon, 2026-11-17)
The plan had omitted the #248 historical seal ledger and the inherited-seal repairs deferred on 2026-11-10. Ruling: run a fresh canonical-seal inventory of all Pass–shelat-owned files at the tip now, reconcile it with the #248 ledger, and fold the fixes into **Stage 2**. Seal-B-only items (Yao and sc-garble `PolyExpr.eval`) and non-campaign files (`Complexity/TuringMachine/CodeSimulator.lean`) are listed, then handled by separate ruling.

**Stage 2 handover, a seventh change for Seyoon to confirm:** removing the public `EnsembleLemmas.blocks` alias also needs the body of `ETTGame.dTape` (`EncryptThenTag/Handler.lean:178`) changed. It is of the same kind as the six approved under CS1-Q2.

**Seventh change approved (Seyoon, 2026-11-17):** the body of `ETTGame.dTape` (`EncryptThenTag/Handler.lean:178`). Stage 2 makes all seven DL-35 changes, and its gate checks each one.
