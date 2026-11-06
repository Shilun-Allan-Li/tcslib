# Gate 07 (Pass–shelat ch. 2–8): the equation-lemma PR — API and statement audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#210](https://github.com/Shilun-Allan-Li/tcslib/pull/210)
at its head `fff0430c7c9db136e60ed14b069e972c2ea56fc8`, on base `05fe903fc736ac8036c161ad159dc8bdddcd6ee2`
(`cryptography/pass-shelat-ch2-4`; no Lean change on the base since). Eight commits, 33 Lean files,
`+1291 −47` (`evidence/repair.diff.txt`).

**Why it exists.** Policy §1, rule 10: no proof, and no statement, may read a definition from
another file; consumers go through published lemmas beside the definition. User rulings of
2026-11-06:
- **R-04-5 (A), zero exclusions:** every definition a consumer reads gets its equation lemma;
  statements that elaborate only by reducing another file's definition are restated;
- **published domain equivalences:** each concrete collection exposes its domain field through
  `…_domEquiv i : C.D i ≃ T i` (`Equiv.refl`), with its value-field equations stated through it;
- **factoring D1 (A):** three shared facts that two fill units need are added as sorried public
  statements here, so that this gate audits them as statements;
- **size exceptions:** `Candidates/RSA.lean`, `Candidates/Rabin.lean` and
  `Asymptotic/Collections.lean` may exceed the 1000-line limit.

**The source** is [PS10], 3rd ed., January 2010: `Pass–Shelat.pdf` at the root of
`cryptography/pass-shelat-ch2-4` (SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`). Book page = PDF page − 12.
You need it only for the three shared statements (§2.3–2.4 and §2.6–2.7: Algorithm 50.16,
Lemma 51.17, Theorem 51.1, Theorem 53.2).

- **The deliverable:** **`gate07-eqlemmas-findings.md`**, committed as
  `inbox/gate07-eqlemmas-findings.md` on the exchange branch `exchange/pass-shelat-ch5-8` and
  pushed (the protocol is that branch's `README.md`: write only that file, `git pull --rebase`
  before pushing, never force-push, no PR).

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.

## Brief for the auditor

1. **The added declarations (183).** For each group (`evidence/decls.tsv`, the worker reports'
   tables), check that:
   - each lemma states exactly the defining equation of its definition (or, for `_iff`, its
     body), with nothing added or lost — in particular no hidden hypothesis, and no case of a
     definition by cases left out;
   - it sits in the definition's own file, is public, is not `@[simp]`, and has a docstring
     stating the formula;
   - the `…_domEquiv` equivalences are `Equiv.refl` of the right types, and the field equations
     stated through them (`C.f i x = F i (φ x)`, `encD`, `decD` with `Option.map φ.symm`, `perm`,
     `inv`, the `uprob` transport) are correct for every collection;
   - none duplicates an existing lemma under another name (the workers grepped; spot-check), and
     none is a number-theory fact that Mathlib already has (`mathlib-overlap-nt.md`, records).
2. **The three shared statements** (sorried; `Factoring.lean`: `polyTimeComputable_samplePrimeL`,
   `statClose_samplePrimeL_pair`; `RSA.lean`: `statClose_sampleUnitL`). Are they true as stated,
   at every parameter (including `n < 2`, `N = 1`, and when the coin budget is not met)? Do the
   bounds (`2·(1/2)^n + 2n/2^n`; `e^{-n}`) follow from the cited facts? Are the citations and
   proof sketches accurate? Are they the right interface for their users (the factoring fill
   brief, `fills/factoring-candidates/brief.md`)?
3. **The three restated statements:** `Candidates.fullDLCollection_hardCore`,
   `TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure`,
   `TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`. Is each new form the same
   proposition as the old (the predicate composed with an `Equiv.refl`)? Does it still say what
   its docstring and [PS10] say? Was any other statement of the same kind (a statement-level
   read of another file's definition) missed — check the probes (`evidence/e1a/`,
   `evidence/e1b/stmtprobe/`) and their method.
4. **The non-additive changes:** `Closure.lean`'s re-pointed proofs, the two `PublicKey.lean`
   proofs, the docstring edits for the 3-colouring lint findings, and the restated sketch wording.
   No statement other than the three may change, and no docstring other than those may change.
5. **Rule-10 evidence.** Do the sealed probes (pass and control) show what they claim? Are the
   controls real (they pass unsealed and fail sealed)?
6. **Look for regressions.** Do not give a blanket approval.

## Attestations (maintainer; `evidence/`)

- **Replay** (`replay-head.log`): the 116 modules downstream of the 33 changed files
  (`downstream2.py`, facades excluded), then `audits/pass-shelat/Checks`: **117 of 117 pass,
  0 errors.** Base counted on the same modules (`replay-base.log`, `replay-base-fix.log`: three
  base oleans were missing from the snapshot and were rebuilt from base sources).
  `sorry-compare.txt`: equal except `Candidates/Factoring` 8 → 10 and `Candidates/RSA` 9 → 10, the
  three shared statements. The `Checks` output is identical to the base.
- **Axioms** (`axioms.log`, `axioms-summary.txt`, `direct-sorry.log`, `axioms-base-defs.log`): 186
  declarations (183 added, 3 changed). None outside `propext`, `Classical.choice`, `Quot.sound`,
  `sorryAx`. `sorryAx` occurs in a declaration's own terms only for the three shared statements
  and the still-sorried `fullDLCollection_hardCore`; the other prints inherit it from collection
  definitions that already rest on sorried targets at the base.
- **Lint** (`style-lint-{base,head}.log`, `check8b-diff.log`): no new finding except the three
  approved size findings; check-8 lists only shrink.
- **Statements** (`decls.tsv`, extractor `decls.py` as fixed after gate 03l round 3): 183 ADDED,
  3 CHANGED, 0 REMOVED.
- **Seal:** the units' probes (`e1a/`, `e1b/`) and the final probes (`probe-*.log`,
  `probes/*.txt`): every lemma group is exercised sealed with controls; the restated statements
  elaborate sealed and their old forms fail sealed.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity: **blocker** (a false or unusable statement, or a change outside scope), **major** (a
wrong interface lemma, a missed statement-level read, evidence that does not show what it
claims), **minor** (docstring, naming, evidence presentation), **note**. The gate closes at
**0 blockers and 0 majors**.
