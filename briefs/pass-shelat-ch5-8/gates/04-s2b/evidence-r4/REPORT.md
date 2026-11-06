# Gate 04 round 4 (PR #195, S2b): R3-01 repair and the complete rule-10 seal

(Saved by the maintainer from the worker's hand-back; the worker could not write report files.)

- Base `27ae72da62119ebdde380b8cb2d8c183b59fa2bf`; merge base `a3c5fa8b72e50939822f22364647dc844a3914a0`.
- Commit `947606fecf1142997661651701f04c3912ba7551` on `wip/g04r4` (`SP/wt-g04r4`): 5 files, +38/−21,
  proof bodies only; 13 declarations re-proved; no statement, docstring, `@[simp]` or `sorry` change.
- Fixes (each now through published equations): `ProbComp.expect_bind` (R3-01);
  `Games/Protocols.lean`'s three `example`s, `Party.stepT_fst`, `closeT_fst`, `execT_outcome`
  (`OracleComp.bind` by `rfl`, missed by r3's hand-picked seal row);
  `LazySampling.lean`'s `evalLazy_congr`, `evalLazy_comp`, `uprob_evalLazy_aux`;
  `MultiMessage.lean`'s `boundedBy_chainTree`; `MultiMessageLemmas.lean`'s
  `acceptProb_oracleDist_congr_equiv`, `prfAdv_congr_equiv` (statement's universe binders changed
  by #195, so treated as changed).
- Seal at the final commit: **26 of 26 files PASS** with automatically collected candidates
  (`seal-evidence.log`); `$BASE` control fails exactly at the fixed declarations
  (`seal-control-base.log`); plain seal failures are exactly the named entries (`seal-plain.log`).
- Named entries (`exclusions.md`): section A, 48 inherited, unchanged ch. 2–4 definitional reads;
  section B, 75 explicit unfolds the seal cannot see (all inherited, unchanged); section C, 29
  type-level reads of `Games.QueryImpl` and `Games.OracleSpec.add` in the S2a/S2b layer
  (statements and definition bodies), which no re-proof can remove. Check: 0 entries in A or B on
  a declaration #195 added or changed.
- Decision needed: make `QueryImpl` and `OracleSpec.add` `abbrev` (tested in a shadow copy, not
  committed: 30 downstream modules plus `Checks` rc=0 and all 14 `Games/` files seal with no
  entry; `abbrev-experiment.log`), or accept section C as recorded exceptions.
- Replay: 22 downstream modules plus `Checks`, rc=0, sorry counts equal to the r3 logs
  (`replay.log`, `replay-cmp.txt`). Axioms: 114 public theorems of the 5 files, all standard
  (`axioms.log`). Lint: 0 findings on all 26 files; check 8b on `Games/` 0 FAIL, 0 WARN
  (`lint.log`).
- Method and tools: `tools/` (collector `collect_body.lean`, `seal.py`, `scan.py`, `exclude.py`,
  `exclusions_md.py`), cross-check with r3's names (`seal-r3union.log`).

## Update: R-04-4 applied (second commit)

- `a588adfed01eefe6971abd0846e3938ad02e8624` changes only two headers, `def` → `abbrev`, for
  `Games.QueryImpl` (`Simulate.lean`) and `Games.OracleSpec.add` (`OracleComp.lean`).
- At `a588adfe`: the seal passes on all 26 files; the 14 `Games/` files need no entry (the plain
  seal passes on each); section C of `exclusions.md` is empty; sections A and B unchanged (48 and
  75 entries, all on declarations #195 did not change). `$BASE` control fails at the re-proved
  declarations and at the former section-C ones.
- Replay of the 30 modules downstream of the two files plus `Checks`: rc=0, sorry counts equal to
  the base (`Games/Efficiency` 4, others 0). Axioms: 155 public theorems of the 7 changed files,
  all standard. Lint 0 on all 26 files; check 8b on `Games/` 0/0.
- The table and section C above describe the first commit only; the refreshed logs are at
  `a588adfe` (round-1 evidence kept in `intermediate/r1/`).
