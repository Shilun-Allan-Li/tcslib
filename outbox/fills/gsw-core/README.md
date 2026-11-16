# Claude fill `gsw-core` (GSW phase 5: F1 Gadget, F2 Noise, F3 Scheme, F7 Symmetric, F4 Eval)

Claude is the worker, a lead with up to 2 sub-agents (Seyoon's ruling, 2026-11-16: GSW fill wave, 2 Claude jobs).
The job proves the 29 admitted targets of `TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/`
`{Gadget,Noise,Scheme,Symmetric,Eval}.lean` (plan §G7 units F1, F2, F3, F7, F4; about 760 lines). The parallel job
`gsw-security` (F5, F6) starts from the same base; each cites the other's targets as frozen statements.

**Base.** `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, the gate-closed head of draft PR #333 (`stmt/gsw`; Gate 41
closed by disposition; its last commit is the docstring-only LE-gate41).

**F0 / #332 decision (no ruling needed).** #333 is stacked on #332: `git merge-base --is-ancestor 94eae71b 486f44f8`
holds, `486f44f8~3` is #332's head `94eae71b779c4ca0f76c138d699f4d737dbd6cee`, and #333's `DAGCircuit.lean` diff is
exactly #332's. So the issue base already contains F0's `DAGGate.getD_lt_depth` and `runWith_rel` **proved**
(standard axioms only; Gate 41 audited them as proofs, CLEAR), with the depth readers. F4 uses them as published
lemmas of the frozen `DAGCircuit.lean`: no combined base, and nothing proved-modulo about F0. Both PRs merge
first (#332, then #333); the maintainer rebases the fills onto the then records tip at landing.

Integration check of #333 on the current tip: pending at issue; the maintainer records the result in the plan.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 31 TCSlib modules, generated at the base: the upstream closure of the modules
  downstream of the five owned files (`Security`, the three facades) and of `Pseudorandom/Indistinguishability`,
  which the owned files may import.
- [Mathlib roots](roots.txt): 38.
- [Source hashes](SOURCE-SHA256SUMS) at the base.
- [Base admissions](base-sorries.txt): 35 declarations in 7 modules (all GSW). The only change must be the removal
  of the 29 targets (F1 5, F2 12, F3 6, F7 2, F4 4, as in plan §G7); 6 remain, in `Columns` and `Security`.

Claude returns checkpoints (at least one mid-way) and the final payload only at `inbox/fills/gsw-core/` on the
exchange. Seyoon dispatches.

**Ready to dispatch**
