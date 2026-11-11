# Gate 13 · public-key CPA bridge proof (`padded_cpa`)

Round 1. Auditor Codex (Seyoon's choice, 2026-11-11). Draft
[PR #288](https://github.com/Shilun-Allan-Li/tcslib/pull/288) at
`892a3f3c78abcde8bdf822a3b4168ab3302b4272` on branch `land/pass-shelat-padded-cpa`, targeting
`cryptography/pass-shelat-ch2-4` on base `2950c4a74c45b98185a5eaf4601cf8b88a7528c2`. That base
has the post-#286 Lean content `ed0f7238`; later base commits are records only.

This proof audit covers the formerly admitted
`BitPublicKeyScheme.SingleBitSecure.padded_cpa` (`Encryption/PublicKey/OracleSecurity.lean`)
and the two new helper modules `OracleSecurity/ChallengeSim.lean` and
`OracleSecurity/RecordHandler.lean`. The statement passed Gate 04. The issued fill brief, in the
bundle, fixes the route and discipline. The source is [PS10], R. Pass and a. shelat, *A Course in
Cryptography*, third edition, January 2010: Definition 171.5 and the claim after it (book
pp. 171–172).

## The proof

The proof establishes an exact identity, at every `n`:
`advantage(IND_0, IND_1) = distAdv(⟨pk, Enc_pk(0)⟩, ⟨pk, Enc_pk(1)⟩, D)`. Check the steps
independently:

1. **Eager coins.** `expect_simulate_indImpl_cpa` swaps the lazily sampled challenge coins for
   coins sampled up front. Check the induction, and check that coins drawn but never used
   marginalize out.
2. **First-challenge congruence.** `chRun_congr` and `firstQ` show that the run depends on the
   challenge answer only through the first challenge query, and that `firstQ` does not depend on
   the answer function.
3. **The recording handler.** `recHandler`, with `seedLen 0`, three state bits, `Dec` answered
   `00`, every challenge answered `padCt L(n) c`, and the first query recorded. Its `out` returns
   `[a]`, `[¬a]` or `[0]`. It is fed to `Games.exists_handlerMachine` (T1, proved in #285) with
   `k = 2`.
   - Check codec alignment: `recDin`/`recDout` against `inLens`/`outLens`, and the transport
     `chRun_toCompOn_transport`.
   - Check the coin transport `NUPPT.coinsCongr (padEnc_coins …)`, T1's coin equivalence and the
     empty seed.
4. **The identity.** `padded_cpa_advantage_eq` and the pointwise case split
   `expect_indicator_sub` over `(0,1)`, `(1,0)`, equal messages, and no challenge.
   - Check repeated challenges, budget `q = 0` and the timeout output.

## Interfaces and discipline

- **Statement freeze.** The target header and every older declaration must be unchanged; 41 new
  public declarations are added.
- **Rule 10.** No touched declaration may read another file's definition. The brief allows
  `OracleSecurity.lean`'s own definitions to be crossed. The new helper modules are separate files
  and must not unfold `OracleSecurity` (they do not import it) or any other file's definitions.
- **API quality.** Check names, docstrings with formulas, proof sketches, the absence of
  `@[simp]`, and the precise imports.
- **Recorded follow-up debt, not findings of this gate unless you disagree with the
  disposition:**
  - the generic `ProbComp` lemmas left in `ChallengeSim` (DL-30);
  - the `ofFn_padFin_of_length` copies (DL-31).
- **Landing edits.** The maintainer's landing-edit commit must change no statement and no proof
  route.

## Evidence

- `worker-report.md`: the Claude worker's final report.
- `review.md`: the maintainer's independent delivery review.
- `verification.zip`: the review's raw evidence, run on the issue base before the landing edits:
  - integrity and a fresh build (233/233);
  - the admission census (31 → 30) and the statement comparison;
  - axioms;
  - whole-file closure seals of all three files with a base control;
  - 17 controls and the explicit-reader scan.
- `landing/`: on this PR's head:
  - `closure-build.jsonl`: a fresh build of the 233-module closure, 0 errors;
  - `root-checks.jsonl`: the downstream modules through `TCSlib` and `Checks` on the full tree;
  - `axioms.log`: `padded_cpa` and `TrapdoorCollection.tdpBitScheme_padded_cpa` print
    `[propext, Classical.choice, Quot.sound]`.
- `sources.zip`: the 151-module source closure at the head.

## Findings delivery

Return `gate13-padded-cpa-findings.md` as a Markdown file in this chat. For multiple evidence
files, return a ZIP. The user dispatches and merges.

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Severities:
- **blocker:** a false or unusable statement, or a scope violation;
- **major:** an incomplete argument, a forbidden new read in a touched declaration, a statement
  change, or necessary evidence that cannot be verified;
- **minor:** documentation or API defects;
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero
majors.
