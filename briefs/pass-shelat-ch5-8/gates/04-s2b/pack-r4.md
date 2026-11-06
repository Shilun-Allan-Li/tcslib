# Gate 04 (Pass–shelat ch. 5–8, S2b), round 4: closing audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#195](https://github.com/Shilun-Allan-Li/tcslib/pull/195)
at its head `a588adfed01eefe6971abd0846e3938ad02e8624`. That is two commits on round 3's
`27ae72da`:
- `947606fe`, the rule-10 re-proofs;
- `a588adfe`, ruling R-04-4: `Games.QueryImpl` and `Games.OracleSpec.add` become `abbrev`.

In the bundle:
- round 3's findings (`gate04-s2b-r3-findings.md`) and resolutions (`resolutions-r3.md`);
- the repair diff from `27ae72da` (`evidence-r4/repair.diff.txt`);
- **the complete seal evidence**:
  - the seal at the head (`seal-evidence.log`);
  - the `$BASE` control (`seal-control-base.log`);
  - the seal without entries (`seal-plain.log`);
  - the cross-check with round 3's names (`seal-r3union.log`);
  - the source scan at the head and at the base (`scan.log`, `scan-base.log`);
  - the named exclusions (`exclusions.md`);
  - the tools (`tool-*.txt`);
  - the worker's report (`REPORT.md`);
- replay, axioms and lint (`replay.log`, `replay-first-commit.log`, `axioms.log`, `lint.log`);
- every Lean file the two commits change, at the head.

The deliverable is **`gate04-s2b-r4-findings.md`**.

## Brief for the auditor

1. **Verify round 3's resolutions:** for R3-01, R3-02, F02 and N7, say fixed, recorded or not
   resolved (and why).
2. **Audit the changed surface:**
   - The re-proved declarations (`repair.diff.txt`) must read no other file's definition and must
     keep their statements. The seal output and the control are the evidence.
   - Check the seal's method (`tool-collect_body.lean.txt`, `tool-seal.py.txt`, `tool-scan.py.txt`):
     does its candidate collection really cover every foreign definition a declaration can reduce?
     What can it miss? (The tool says the source scan covers `unfold`/`simp [d]`, which a seal
     cannot see.)
   - The two `abbrev` headers: is treating these two type formers as notation sound under policy §1,
     given their reading lemmas (`queryImpl_def`, `OracleSpec.add_dom_inl/_inr`, `add_rng_inl/_inr`)?
     Does making them reducible change any statement's meaning? (It should not.)
   - The exclusions (`exclusions.md`, sections A and B): are they all in declarations #195 did not
     change (status SAME)? Is the claim "0 entries on any declaration #195 added or changed" true?
3. **Look for regressions.** Do not give a blanket approval.

## Attestations (maintainer; `evidence-r4/`)

- **Change set:** 26 Lean files, excluding the root facade (`changed-files.txt`). This corrects
  round 3's "25".
- **Elaboration:**
  - `replay-first-commit.log`: the 22 modules downstream of the first commit's five files, then
    `Checks`; 23 of 23 pass.
  - `replay.log`: after the second commit, the 29 modules downstream of `OracleComp.lean` and
    `Simulate.lean`, then `Checks`; 30 of 30 pass.
  - The `sorry` counts equal round 3's: `Games/Efficiency` 4, all others 0.
- **Axioms** (`axioms.log`): the 155 public theorems of the 7 files the two commits change. All are
  standard; none depends on `sorryAx`. Round 3's print of the other changed files stands, with
  `sorryAx` exactly in T1, T2, `exists_toCompOn_of_toComp` and T4.
- **Lint** (`lint.log`): 0 findings on each of the 26 files; check 8b on `Games/`: 0 FAIL, 0 WARN.
- **Seal** (`seal-evidence.log`): 26 of 26 pass, with automatic candidates. The 14 `Games/` files
  need no entry. The named entries cover only inherited ch. 2–4 declarations.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per item: `R3-01: fixed / recorded / not resolved — <reason>` (also R3-02, F02, N7).
Severity guide as in rounds 1–3. The gate closes at **0 blockers and 0 majors**.
