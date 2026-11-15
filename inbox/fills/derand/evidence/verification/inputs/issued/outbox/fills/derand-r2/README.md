# Claude fill `derand`, issued-r2 (H17 and Theorem 180.1)

Claude is the worker (Seyoon's standing ruling, 2026-11-11). This reissue replaces `issued-r1`, which was held until
the counting enumeration host was statement-gated. The host is now **H17** (Gate 28 CLEAR; #312 merged at
`8f0b34c9a5a52f57677f16243370dfed3f811ac4`). The job proves three admitted statements:

- `Complexity.exists_seedMajorityTM`, the H17 machine contract, and `Complexity.seedMajority_mem_DTIME`, its
  corollary, in `TCSlib/Complexity/Randomized/SeedMajority.lean` [AB09, §7.1, p. 126];
- `TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp` in
  `TCSlib/Cryptography/Randomness/Derandomization.lean` [PS10, §8.2, Theorem 180.1].

The base is `01de2d8baed9113e4a099e13c5d50c81e6dbc66f` on `cryptography/pass-shelat-ch2-4`, the records tip after #303, #305–#309, #311 and #312.

**Scope note.** Seyoon pre-approved exactly three additions to frozen shared files (2026-11-15): the generic-fuel
`computesFunInTime_find` in `Complexity/Randomized/Build/IterateFind.lean`, and the readers `mem_DTIME_iff` and
`FinTM.decidesInTime_iff` in `Complexity/ClassP/DTIME.lean`. Their downstream modules outside this order
(480 for `ClassP/DTIME`, 222 for `IterateFind`) are rebuilt by the maintainer at review.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md). Verify the package with
`shasum -a 256 -c SHA256SUMS` from this directory.

- [Build order](order.txt): 377 TCSlib modules. These are the upstream closure of the modules downstream of the two
  owned files, and of `IterateFind` and `ClassP/DTIME`.
- [Mathlib roots](roots.txt): 129.
- [Source hashes](SOURCE-SHA256SUMS) at the issue base.
- [Base admissions](base-sorries.txt): 26 declarations in 12 modules. The only change must be the removal of
  `exists_seedMajorityTM`, `seedMajority_mem_DTIME` and `bpp_subset_dtime_subexp` (or, under the brief's
  proved-modulo rule, of the last two only).

Claude returns checkpoints and the final payload only at `inbox/fills/derand/` on the exchange. Seyoon
dispatches.

**Ready to dispatch**
