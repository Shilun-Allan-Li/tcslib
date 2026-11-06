# Gate 03g (3-colouring zero knowledge): round 1 resolutions

- **Round:** findings `findings/gate03g-findings.md`, SHA-256 `09f349307f40468c95945b2beb41a648e6d95e5bb32c126ffdc36115a5f7f1f2`; pin `0c348ff9`. **0 blockers, 2 majors, 4 minors**; the three admissions a, a, b. Review `review/gate03g-review.md`: all six true (#2 and #5 understated); `col_zk` provable as stated in D8's scope (the reviewer records its verdict as (a) in that scope). No ruling.
- **Repair:** the gate 03 repair batch, PR [#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206) (head `73751f5747d8c0a57aba9939cac8bb16f87ba2ba`, merged by `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; evidence `evidence-repairs/03-batch/`), plus the records commits of 2026-11-06.

| Finding | Severity | Resolution |
|---|---|---|
| #1, #2, M1 | major | **Fixed** (#206, item E). `col_zk`'s sketch is replaced by the review's §2.3: the leading term `N²·ε_B(⌊√N⌋)`; the bridge from ideal coins to a machine that fixes the attempt table with `CommitmentLemmas.exists_fixCoins`, so the hiding machine makes one verifier call and one call to `D`; the `m = 0` / `n ≥ 1` and `n = 0` cases; the advice bound; the use of `Lz`. `statClose_sampleColorPair` is named as a lemma still to add. Docstring only. |
| #3 | minor | **Fixed.** `Negligible.comp_sqrt`'s sketch threshold (`K = max(n₀, 4^c, 1)`, `N ≥ K²`). |
| #4 | minor | **Fixed.** `sampleEdgeIdx`'s docstring: `m < 2^k ≤ 2m` for `m > 0`. |
| #5 | minor | **Fixed.** The four truncation sites now say that Algorithm 128.7 itself stops after `n|E|` attempts (`Simulator.lean`'s module docstring, `colSim`, `col_zk`'s deviation; the inventory in the records). GI's truncation stays a declared deviation. |
| #6 | minor | **Fixed (records).** DESIGN D8 erratum and §5 item 11 (3COL is computational); an as-built note under §2.15 (G3-3's `complete` and `boundedP`); inventory Thm-124.1 (A), Claim-124.d, Def-124.a. |
| M2 | (review) | **Fixed.** `Simulator.lean` quotes "`S'` [sic: `S''`]"; DESIGN §7 item 46 records the source typo. |
| M3 | (review) | **Scheduled:** the seven-step ladder for `col_zk` is in the 3-colouring fill notes (`fills/3col/brief-notes.md`). |
| M4 | (review) | **Recorded** (optional): `Negligible.comp_sqrt` could move to `Defs.lean`; not done. |
