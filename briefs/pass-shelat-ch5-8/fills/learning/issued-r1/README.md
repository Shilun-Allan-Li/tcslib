# Claude fill `learning` (Theorem 179.1 (b))

Claude is the worker (Seyoon's standing ruling, 2026-11-11). The job proves the admitted `Randomness.predictAdv_prfConcept_negligible` in
`TCSlib/Cryptography/Randomness/Learning.lean` [PS10, §8.1, Theorem 179.1]. The base is `107f1e8c218733eac12d6b9bee6fece441271317` on
`cryptography/pass-shelat-ch2-4`, the records tip after #303, #305, #306, #308 and #309. #307 (dl-crh) is not merged,
and this unit touches none of its files.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 246 TCSlib modules. These are the upstream closure of the owned module and of the modules helpers may import, plus the owned module's downstream modules.
- [Mathlib roots](roots.txt): 82.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 20 declarations in 10 modules. The only change must be the removal of
  `predictAdv_prfConcept_negligible`.

Claude returns checkpoints and the final payload only at `inbox/fills/learning/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
