# Gate 07 (Pass–shelat ch. 2–8), round 2: the equation-lemma PR — API, statement and rule-10 audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#210](https://github.com/Shilun-Allan-Li/tcslib/pull/210)
at its head `037075b01ca348266d50735cd22526a96fc131bf`, on base `05fe903fc736ac8036c161ad159dc8bdddcd6ee2`
(`cryptography/pass-shelat-ch2-4`; no Lean change on the base since). Round 1 audited
`fff0430c7c9db136e60ed14b069e972c2ea56fc8`. This round covers the repair of round 1's findings
and the follow-up rounds (`16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1`, `286aee54ae17ffec36225a318f0c714cf9bb7393`, `037075b01ca348266d50735cd22526a96fc131bf`):
27 commits since round 1 (`evidence-r2/commits.txt`); 68 Lean files changed against the base, `+3063 −482` (`evidence-r2/repair.diff.txt`
from `fff0430c`; `evidence-r2/full.diff.txt` from the base).

**Why it exists.** Policy §1, rule 10: no proof, and no statement, may read a definition from
another file; consumers go through published lemmas beside the definition. User rulings:
- **R-04-5 (A), zero exclusions (2026-11-06):** every definition a consumer reads gets its
  equation lemma; statements that elaborate only by reducing another file's definition are
  restated; the definition-body reads are fixed as well (overnight ruling 1);
- **published domain equivalences:** each concrete collection exposes its domain field through
  `…_domEquiv i : C.D i ≃ T i` (`Equiv.refl`);
- **Q1 (2026-11-07): `PolyExpr.eval` is notation.** It could not be made `@[reducible]` (that breaks
  `simp` on the `eval_*` lemmas; `evidence-r2/replay-eval-reducible-attempt.log`), so it stays
  semireducible, is never sealed, and its docstring records the ruling;
- **factoring D1 (A):** the shared statements S1–S3 (sorried here; filled by the factoring fill);
- **size exceptions:** `Candidates/RSA.lean`, `Candidates/Rabin.lean`, `Asymptotic/Collections.lean`,
  `Asymptotic/PublicKey.lean`, `Candidates/DiscreteLog.lean`, `ZeroKnowledge/ThreeColoring/Protocol.lean`.

**The source** is [PS10], 3rd ed., January 2010: `Pass–Shelat.pdf` at the root of
`cryptography/pass-shelat-ch2-4` (SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`). Book page = PDF page − 12.

- **The deliverable:** **`gate07-eqlemmas-r2-findings.md`**, committed as
  `inbox/gate07-eqlemmas-r2-findings.md` on the exchange branch `exchange/pass-shelat-ch5-8` and
  pushed (the protocol is that branch's `README.md`: write only that file, `git pull --rebase`
  before pushing, never force-push, no PR).

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
You may also read the PR's branch at `037075b01ca348266d50735cd22526a96fc131bf` directly.

## Brief for the auditor

1. **Verify round 1's resolutions** (`resolutions-r1.md`, round 1's findings): for F01, F02 and F03,
   say fixed, recorded or not resolved, and why.
2. **The statement changes** (`evidence-r2/decls-vs-r1.tsv`: 167 ADDED, 54 CHANGED, 2 REMOVED against round 1's head;
   `evidence-r2/decls-vs-base.tsv`: 350 / 57 / 2 against the base; the worker's old → new table with
   reasons for the 36 changed since `16a7d02d` is `evidence-r2/r6/statement-changes.tsv` and §
   "Restatements" of `worker-reports/E1-round5-REPORT.md`; the 18 changed between round 1 and
   `16a7d02d` are in `evidence/` of that round and `sweep/REPORT.md`). For each: is the new form the same proposition as the old (the
   predicate composed with an `Equiv.refl`/`finCongr`, a length along a proved equality, `ofFn`
   injectivity, `PermFamily.HardCore` defined as `HardCore P.toFunFamily (h ∘ domEquiv)` with
   `hardCore_iff := Iff.rfl`)? Does it still say what its docstring and [PS10] say? Is any
   consumer's meaning changed? The two REMOVED (`NUPPT.Uniform` lemmas) must reappear unchanged in
   `PPT.lean`.
3. **The added declarations** (`decls.tsv` ADDED): each equation states exactly the defining
   equation of its definition (no hidden hypothesis, no case left out), sits in the definition's
   own file, is public, not `@[simp]`, with a docstring stating the formula; each equivalence is
   `Equiv.refl` or `finCongr` of the right types; none duplicates an existing lemma, and none is a
   number-theory fact Mathlib has (`mathlib-overlap-nt.md`).
4. **Definition bodies changed without a type change** (`E1-round5-REPORT.md` § "Restatements" item 9;
   `E1-round6-REPORT.md` § 1): `prodInverter`, `vTapeSplit`, `giBitEquiv`, `gniTapes`, `giRepCoins`, `predCoins`,
   `oddCoins`, `sampleAll`, `owfFamily`, `Collection.glPad`, `TrapdoorCollection.glPad`, the
   correctness fields of `bitwise` and `prgScheme`. Is each the same function (value) as before?
   Do the `noncomputable` additions matter to any consumer?
5. **Rule-10 evidence.** Three layers; check each shows what it claims:
   - the **statement and definition-body sweep** over all 136 `Cryptography` files and `Checks`
     (`evidence-r5/sweep2-*.tsv`, `evidence-r5/final-reads.tsv`; round 6's sweep of the 17 files it
     changed, `evidence-r2/r6/sweep-*.tsv`, `sweep.out`; method and tools in `sweep/`): every read left is
     either in #195's 26 files (fixed on #195, gate 04) or none;
   - the **whole-file proof seal** (`evidence-r2/r6/proofseal/`, `touched.py`): declarations this PR adds or changes
     have 0 reads; the 173 rows in untouched proofs (`proofseal/final-b.tsv`) are recorded for clean-up, not
     fixed here — is that classification (`touched.py`) right?;
   - the **explicit-unfold scan** of touched declarations (round 6b, `evidence-r2/r6b/`, #195's
     gate-04 scanner in `r6b/tools/`): reads through equation lemmas that a seal cannot see; 18
     hits before (`hits-touched.tsv`), 0 after (`scan-final.log`).
   Controls: do the sealed probes (`evidence-r2/r6/probes/` and `r6b/probes/`: `Final6Pass` 47 examples, `Final6Control` 30
   old readings each failing once sealed, `Final6OpenControl` the same unsealed; round 5's in
   `evidence-r5/probes/`)
   pass and fail as claimed?
6. **The interface for the fills.** The fills (`fills/*/delivery-review-*.md`) land on this head
   with the landing edits their reviews list; check the published names they need exist with
   those statements (`msgAt_eq`, `edgeIdxOfMsg_eq`, `OneWay.yaoB_apply`,
   `NUPPT.Uniform.advice_eq`, `prodInverter_eq`, `PRG.expand_G_stretch` for #195).
7. **Look for regressions.** Do not give a blanket approval.

## Attestations (maintainer; `evidence-r2/`)

- **Replay.** Each round replayed every module downstream of the files it changed, on the previous
  round's tree, then `audits/pass-shelat/Checks`: round 5, 233 modules plus Checks
  (`evidence-r5/replay-head*.log`); round 6, 69 plus Checks, and the 18 modules round 5 could not
  replay (136 upstream modules built from source; `r6/build-missing2.log`, `r6/replay-head.log`);
  round 6b, 64 plus Checks (`r6b/replay-head.log`). **All pass, 0 errors.** `sorry` counts of the
  changed files equal the base's (`evidence-r5/sorry-compare.txt`).
- **Axioms** (`evidence-r5/probes/Axioms.log`, `r6/probes/Axioms.log`, `r6b/probes/Axioms6b.log`): every
  added and changed declaration within `propext`, `Classical.choice`, `Quot.sound`; `sorryAx`
  only where the base has it (`zk_proof_of_mem_NP_of_owp`, `zk_proof_of_owp_levinReduction`,
  `factoringCollection_index`/`rsaCollection_index` through sorried collections in their types,
  `R3COL_witnessRelation` through its fill-target `sorry`) and in S1–S3.
- **Lint** (`r6/style-lint-*.log`, `r6/check8b-diff.log`): no new finding except the approved size
  lines (Collections, PublicKey, RSA, ThreeColoring/Protocol); `HardCore`, `OneWay` and
  `HardCoreLemmas` kept at ≤ 1000 lines; check-8 FAIL count unchanged.
- **Statements:** above (`decls-vs-r1.tsv`, `decls-vs-base.tsv`; `decls.py` as fixed after gate 03l
  round 3). The two REMOVED rows are the `NUPPT.Uniform` lemmas, re-added unchanged in `PPT.lean`.
- **Rule 10:** the statement and definition-body sweep leaves only rows in #195's 26 files
  (fixed on #195 at `4d99b0cb7241b1f431476e1b7cf2f5a551d57d62`, audited by gate 04); the proof seal leaves 0 reads in
  touched declarations; the unfold scan leaves 0. `PolyExpr.eval` is never sealed (Q1).

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round-1 item: `F01: fixed / recorded / not resolved — <reason>` (also F02, F03).
Severity: **blocker** (a false or unusable statement, or a change outside scope), **major** (a
wrong interface lemma, a missed read in a declaration this PR adds or changes, evidence that does
not show what it claims), **minor** (docstring, naming, evidence presentation), **note**. The gate
closes at **0 blockers and 0 majors**.
