# Gate 07 (Pass–shelat ch. 2–8), round 2: the equation-lemma PR — API, statement and rule-10 audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#210](https://github.com/Shilun-Allan-Li/tcslib/pull/210)
at its head `@HEAD@`, on base `05fe903fc736ac8036c161ad159dc8bdddcd6ee2`
(`cryptography/pass-shelat-ch2-4`; no Lean change on the base since). Round 1 audited
`fff0430c7c9db136e60ed14b069e972c2ea56fc8`. This round covers the repair of round 1's findings
and the follow-up rounds (`16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1`, `286aee54ae17ffec36225a318f0c714cf9bb7393`, `@HEAD@`):
`@COMMITS@` commits, `@FILES@` Lean files, `@STAT@` against the base (`evidence-r2/repair.diff.txt`
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
You may also read the PR's branch at `@HEAD@` directly.

## Brief for the auditor

1. **Verify round 1's resolutions** (`resolutions-r1.md`, round 1's findings): for F01, F02 and F03,
   say fixed, recorded or not resolved, and why.
2. **The statement changes** (`evidence-r2/statement-changes.tsv`: old → new for each of the 36
   CHANGED declarations against `16a7d02d`, plus the round-1 three; `decls.tsv` for the full
   ADDED/CHANGED/REMOVED lists). For each: is the new form the same proposition as the old (the
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
4. **Definition bodies changed without a type change** (report §§ "Restatements" item 9, round 6
   item 1): `prodInverter`, `vTapeSplit`, `giBitEquiv`, `gniTapes`, `giRepCoins`, `predCoins`,
   `oddCoins`, `sampleAll`, `owfFamily`, `Collection.glPad`, `TrapdoorCollection.glPad`, the
   correctness fields of `bitwise` and `prgScheme`. Is each the same function (value) as before?
   Do the `noncomputable` additions matter to any consumer?
5. **Rule-10 evidence.** Three layers; check each shows what it claims:
   - the **statement and definition-body sweep** over all 136 `Cryptography` files and `Checks`
     (`sweep2/`, `final-reads.tsv`; round 6's sweep of the files it changed): every read left is
     either in #195's 26 files (fixed on #195, gate 04) or none;
   - the **whole-file proof seal** (`proofseal/`, round 6): declarations this PR adds or changes
     have 0 reads; the 173 rows in untouched proofs (`final-b.tsv`) are recorded for clean-up, not
     fixed here — is that classification (`touched.py`) right?;
   - the **explicit-unfold scan** of touched declarations (round 6b): reads through equation
     lemmas that a seal cannot see.
   Controls: do the sealed probes (`Final6Pass`, `Final6Control`, `Final6OpenControl`, and round 5's)
   pass and fail as claimed?
6. **The interface for the fills.** The fills (`fills/*/delivery-review-*.md`) land on this head
   with the landing edits their reviews list; check the published names they need exist with
   those statements (`msgAt_eq`, `edgeIdxOfMsg_eq`, `OneWay.yaoB_apply`,
   `NUPPT.Uniform.advice_eq`, `prodInverter_eq`, `PRG.expand_G_stretch` for #195).
7. **Look for regressions.** Do not give a blanket approval.

## Attestations (maintainer; `evidence-r2/`)

- **Replay:** `@REPLAY@`.
- **Axioms:** `@AXIOMS@`.
- **Lint:** `@LINT@`.
- **Statements** (`decls.tsv` against `16a7d02d`, extractor `decls.py` as fixed after gate 03l
  round 3): `@DECLS@`.
- **Seal:** `@SEAL@`.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round-1 item: `F01: fixed / recorded / not resolved — <reason>` (also F02, F03).
Severity: **blocker** (a false or unusable statement, or a change outside scope), **major** (a
wrong interface lemma, a missed read in a declaration this PR adds or changes, evidence that does
not show what it claims), **minor** (docstring, naming, evidence presentation), **note**. The gate
closes at **0 blockers and 0 majors**.
