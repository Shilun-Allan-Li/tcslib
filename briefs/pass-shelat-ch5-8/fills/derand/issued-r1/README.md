# Claude fill `derand` (Theorem 180.1)

Claude is the worker (Seyoon's standing ruling, 2026-11-11). The job proves the admitted `Randomness.bpp_subset_dtime_subexp` in
`TCSlib/Cryptography/Randomness/Derandomization.lean` [PS10, §8.2, Theorem 180.1]. The base is `107f1e8c218733eac12d6b9bee6fece441271317` on
`cryptography/pass-shelat-ch2-4`, the records tip after #303, #305, #306, #308 and #309. #307 (dl-crh) is not merged,
and this unit touches none of its files.

**Maintainer recommendation: hold.** The package is complete, but step 4 needs a counting
enumeration host that does not exist, and *Hosts come first* (policy §1) requires its contract
to be statement-gated first. See the brief's *Feasibility* section. If Seyoon dispatches anyway,
checkpoint 1 is the host contract as a scope request.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 203 TCSlib modules. These are the upstream closure of the owned module, plus the owned module's downstream modules.
- [Mathlib roots](roots.txt): 80.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 20 declarations in 10 modules. The only change must be the removal of
  `bpp_subset_dtime_subexp`.

Claude returns checkpoints and the final payload only at `inbox/fills/derand/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
