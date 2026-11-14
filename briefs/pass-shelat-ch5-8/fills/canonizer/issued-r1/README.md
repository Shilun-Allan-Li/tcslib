# Claude fill `canonizer` (`exists_canonizerExp`)

Claude is the worker (Seyoon's standing ruling, 2026-11-11). The job proves the admitted `exists_canonizerExp` in
`TCSlib/Cryptography/Asymptotic/Universal.lean` [PS10, §2.13] (run-3 audit P3-4; DESIGN D11). The base is `107f1e8c218733eac12d6b9bee6fece441271317` on
`cryptography/pass-shelat-ch2-4`, the records tip after #303, #305, #306, #308 and #309. #307 (dl-crh) is not merged,
and this unit touches none of its files.

**Scope note.** The route almost certainly needs two `rfl` readers in the frozen machine-library
files `CodeFormat.lean` and `CodeSimulator.lean` (brief, checkpoint 1). Seyoon can approve them at
dispatch, or the maintainer can land them by PR first.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 183 TCSlib modules. These are the upstream closure of the owned module and of the modules helpers may import, plus the owned module's downstream modules.
- [Mathlib roots](roots.txt): 80.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 19 declarations in 9 modules. The only change must be the removal of
  `exists_canonizerExp`.

Claude returns checkpoints and the final payload only at `inbox/fills/canonizer/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
