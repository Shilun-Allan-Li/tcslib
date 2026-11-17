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
