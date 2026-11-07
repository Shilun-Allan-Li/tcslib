# Gate 08 (Pass–shelat): shared lemmas for the landed fills (S1) and the rejection-loop host contract

**What is audited:** PR [Shilun-Allan-Li/tcslib#227](https://github.com/Shilun-Allan-Li/tcslib/pull/227)
at its head `c6affb3a92535d3f1de2e0a52c205a84c0cff551`, on base `8dcdc8a56382289b5739e13fd18c4d5bd9b67c47`
(`cryptography/pass-shelat-ch2-4`; later base commits are records only). 14 commits, 15 Lean files,
`+572 −906` (`evidence/pr.diff.txt`).

**Why it exists.**
- The eight fill units landed in #224–#226 (Candidates DL, factoring, RSA, Rabin; 3-colouring) carry
  private copies of each other's helpers, of private library lemmas and of Mathlib lemmas
  (`duplication-ledger.md` DL-23…DL-29).
- The design (`fills/shared-lemmas/design.md`) gives one public home per group.
- User rulings of 2026-11-07:
  - **Q1 (A):** this one gate round audits S1's new statements and S2's host **contract** before
    its proof.
  - **Q3 (A):** the host lives in `Candidates/Concrete.lean`.
  - **Q4 (B):** the host's proof is an external fill after this gate.
  - **Q5 (A):** the four tier-2 lemmas are included.
  - **Q6 (A):** `ColZK.pushesUniform_restrict` is deleted.
  - **Q8 (A):** numeral constants and calculi stay private.
- Policy §1, rule 10, applies: no proof reads another file's definition. Notation by user ruling is
  never sealed: `PolyExpr.eval` and `glNeed`.

**The source** is [PS10], 3rd ed., January 2010: `Pass–Shelat.pdf` at the root of
`cryptography/pass-shelat-ch2-4` (SHA-256
`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`; book page = PDF page − 12). You need it
for the host's citations (Theorems 52.3, 53.2, 61.7, 63.10).

- **The deliverable:** **`gate08-shared-findings.md`**, committed as `inbox/gate08-shared-findings.md`
  on the exchange branch `exchange/pass-shelat-ch5-8` and pushed (protocol: that branch's `README.md`;
  write only that file, `git pull --rebase` first, never force-push, no PR).

## Brief for the auditor

1. **The 22 new public lemmas and the 2 visibility changes** (`evidence/statement-diff.txt`; the PR
   description's table). For each, check that:
   - it is **true and exactly stated**: no missing hypothesis, edge cases (`n = 0`, empty lists,
     modulus 0) handled as stated;
   - it is **proved without reading another file's definition**, through published equations only;
   - it sits in the design's home, which every consumer imports;
   - it is public, not `@[simp]`, and has a docstring with the formula;
   - it **duplicates nothing** already public in TCSlib or Mathlib. Grep: a public copy found here is a
     finding.

   The two visibility changes (`foldl_bits_eq`, `abs_uexp_sub_le`) must keep their statements.
2. **The host contract** `Candidates.polyTimeComputable_rejectBlocksL` (`Concrete.lean`, sorried).
   - Is it **true**?
   - Is it **sufficient** for its four consumers? They are dl-a's `polyTimeComputable_expSampleRaw`,
     dl-c's three generator/encryption machines, rsa's `polyTimeComputable_unitSampleStr`/`rsaGenRaw`
     and rabin's generators; the design's §4 maps them.
   - Can each consumer use it reading only published equations (`sampleBelowL_eq_rejectBlocksL`,
     `rejectBlocksL_eq`, `sampleUnitL_eq`, `unitSampleStr_eq`, rabin's `samplePrimePL`)?
   - Is the existential form right, given that its machine is hidden so that no consumer can read
     it?
   - Is the length bound adequate?
   - Are the citations and the deviation note (truncation to `T` trials) accurate?
   - Is the **Proof sketch** followable by a fill worker?
3. **Re-points and deletions** (`evidence/pr.diff.txt`).
   - Every re-pointed fill proof keeps its statement; no statement changes at all (`CHANGED: none`).
   - The deletion of `ColZK.pushesUniform_restrict` and of the `PublicKeyLemmas` copy leaves no
     dangling use.
   - rsa's E4 is applied as reviewed.
   - Docstrings that named a deleted helper are updated, and no other docstring changes.
4. **Rule-10 evidence** (`evidence/seal/`): the touched list, the collection from elaborated terms
   (89 names), the whole-file seals, and the base control.
   - Six untouched base declarations fail sealed, identically at the base: `primesPairEquiv_apply_val`,
     `ExpGroupGen.FullLength.exists_fullLengthExcept`, `rabinCollection_index`,
     `rabinBlumTrapdoor_index`, `uexp_mono`, `exists_plantFactorer`. Is that classification right?
   - Check 13 controls and the unfold scan.
5. **Checks** (`evidence/`): `replay.log` (97 + Checks), the `sorry` census (+1, the host), axioms,
   lint and line counts.
6. **Look for regressions.** Do not give a blanket approval.

## Attestations (maintainer; `evidence/`, `REPORT.md`)

- **Replay:** 98/98, 0 errors.
- **`sorry`:** 507 → 508 in `TCSlib/`, the host only.
- **Statements:** 25 ADDED (18 tier 1, 4 tier 2, 1 host, 2 visibility), 2 REMOVED, 0 CHANGED.
- **Axioms:** standard on all touched and new declarations except the host's `sorryAx`.
- **Seal:** touched declarations clean; the six failures are untouched and identical at the base;
  13/13 controls.
- **Lint:** only the approved size lines; all six fill-owned files shrink.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity: **blocker** (a false or unusable statement, or a change outside scope), **major** (a wrong
or insufficient interface, a duplicate of an existing public lemma, a rule-10 read in a touched
declaration, evidence that does not show what it claims), **minor** (docstring, naming, presentation),
**note**. The gate closes at **0 blockers and 0 majors**.
