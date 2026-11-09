# Incremental cleanup checkpoint

The [final verification](final-r1/README.md) records the repaired head and merge clearance.

[PR #248](https://github.com/Shilun-Allan-Li/tcslib/pull/248) is draft. The
[approved cleanup plan](../../CLEANUP-PLAN.md) specifies incremental
acceptance and the deferred ledger.

The checked candidate `f36e1e4164f1fb77a19c3fae9509efa5ff53e855` integrates the 13 attributed worker
commits and the maintainer repairs with `b9f39f118efa40f4d76e0ebe8d7db59555b11735` after #232.
Reconciliation resolved 21 conflict hunks in 13 files. It reuses the audited
equation lemmas on the merged base, preserves the shared `coinBlock`, and
keeps the distinct reader and proof changes. The first ordinary replay found
four outdated reader references in `Closeness.lean`. The follow-up uses the
merged public equations and preserves the theorem statements.

All 1,075 local modules in scope pass ordinary Lean verification, including
`TCSlib` and campaign Checks. The final epoch rechecked 447 and verified the
source and dependency identities of 628 retained objects. The original 150
successful checks and the failed Closeness attempt are preserved. The 34
unexported modules outside the build have no dependency on an edited path.

The baseline has 168 valid seal harnesses. Of these, 126 are fresh and 42
reuse exact source, import closure and request data from verified #232.
Seventy-four sealed sources pass, and the other sources produce 657 raw
diagnostics. This is a baseline count for the scoped regression review.
The candidate's seals, declaration and axiom comparison, and inherited-read
dispositions are pending.

`native-and-baseline-summary.zip` holds the module receipts, source and
import pins, and baseline seal selection. Its SHA-256 is
`8a7a9900e142669a1f2c491346262d67f2883e38e74a6937a93edf4a49804265`.

**Not yet clear to merge — native compilation passes and the seal regression review is pending.**
