# Gate 14 · the PRF scheme is not CCA2-secure (`prfFixedScheme_not_cca2`)

Round 1. Auditor Codex (Seyoon's choice, 2026-11-11). Draft
[PR #289](https://github.com/Shilun-Allan-Li/tcslib/pull/289) at
`7960d6d4c3254797fdec191fff72c8d4c0147e1a` on branch `land/pass-shelat-not-cca2`, targeting
`cryptography/pass-shelat-ch2-4` on base `fe757f17aa6bda2f711e69abe7e2470ce5872e04`. That base has the
post-#286 Lean content `ed0f7238`; later base commits are records only.

This proof audit covers the formerly admitted `Composability.prfFixedScheme_not_cca2`
(`Encryption/PrivateKey/OracleFromPRF.lean`) and the corollary `not_prfFixedScheme_cca2`, which now has
no admission. It also covers the authorized reader additions:
- `prfScheme_dec` in `PrivateKey/FromPRF.lean`;
- six specification-typed readers in `PrivateKey/OracleSecurity.lean`.

The source is [PS10], R. Pass and a. shelat, *A Course in Cryptography*, third edition, January 2010:
§7.1.3, p. 169 (Claim 169.a) and Algorithm 99.1. The fill ran in two rounds:
- **Round 1 (Codex):** delivered the adversary and the encryption frontier, then escalated a missing
  reader (`worker-report-r1.md`).
- **Round 2 (Claude):** added the readers authorized by the round-2 brief and completed the proof
  (`worker-report-r2.md`).

The bundle includes both briefs.

## The proof

1. **The adversary.** `cca2Next` and `cca2Adversary`: a uniform machine built with
   `ofPolyTimeUniform … (.const 0)`. Check the three activations:
   - on the empty log it asks the challenge on `⟨0ⁿ, 1ⁿ⟩`;
   - on one entry it asks `Dec` on the challenge with its last bit flipped;
   - on two entries it outputs the complement of the last message bit of the `Dec` answer.

   Check also the polynomial-time proof `cca2Next_poly`, built from closure combinators.
2. **The run.** `cca2Run` is stated for any `FixedLengthScheme` with a decryption hypothesis.
   - With budget `.const 2`, check that the third activation's output is read and the timeout is
     never reached.
   - Check that `Enc` is never queried.
   - Check that CCA2 answers the altered query because `c' ≠ c` (`cca2Alter_ne`; the width
     `3n + 2` is positive).
3. **The encryption frontier.** For `n > 0` the challenge is `⟨r, bⁿ ⊕ f_k(r)⟩`, padded to its
   exact width. Its last bit lies in the second component. Decryption of the altered ciphertext is
   `⟨1, bⁿ ⊕ e_{n−1}⟩` (`cca2Cipher`, `cca2Decrypt`, `cca2FlipBits_unmask`, `cca2LastBit`). Check
   that `n > 0` is used only for the last-bit position.
4. **The advantage.** For every key and coins the run returns `b`, so `IND_b` accepts with
   probability `if b then 1 else 0` and the advantage is `|0 − 1| = 1`.

## Interfaces and discipline

- **Statement freeze.** The target header and every older declaration are unchanged; 7 public
  declarations are added.
- **The readers.**
  - Each must state its equation exactly, be public, not `@[simp]`, and have a docstring with its
    formula. `indImpl_dec_onSpec` casts the valid answer along `indSpec_decRng`; the review judged
    that the right form for sealed consumers. Do you agree?
  - The worker omitted `indImpl_enc_onSpec` and `indImpl_challenge_repeat_onSpec` as unused, per the
    brief. `_repeat_onSpec` is deferred to the `_cpa`/`_cca1` fills.
- **Rule 10.** No touched declaration may read another file's definition. Only `OracleFromPRF.lean`'s
  own `prfFixedScheme` may be unfolded; it is not.
  - Casts are removed only through `cast_cast` and `cast_eq` on explicit double casts.
  - `cca2OfFn_cast` uses the width equalities from published readers.
- **Landing-edit commit.** It changes no statement and no route:
  - the docstrings now say the claim is proved;
  - the unused helper `cca2Unmask` is deleted;
  - the private copy of `GGMRed.ofFn_padFin_of_length` is replaced by that lemma (DL-31).

## Evidence

- `review.md`: the maintainer's independent review.
- `verification.zip`: its raw evidence:
  - integrity, and a fresh build of the 238-module closure on the landing branch before the edits;
  - the admission census, statement comparison and axiom census;
  - whole-file closure seals of the three files with base seals;
  - controls and the explicit-reader scan.
- `landing/` (on the PR head):
  - `closure-build.jsonl`: the review's 238-module build, before the landing edits;
  - `edit-rebuild.jsonl`: the 4 modules affected by the edits, rebuilt;
  - `root-checks.jsonl`: 18 downstream modules through `TCSlib` and `Checks` on the full tree;
  - `axioms.log`: the target, the corollary and two readers print
    `[propext, Classical.choice, Quot.sound]`. The probe's `prfScheme_dec` line used a wrong
    namespace; the review's axiom census covers it.
- `sources.zip`: the source closure at the head (129 modules plus the facade).

## Findings delivery

Return `gate14-not-cca2-findings.md` as a Markdown file in this chat. For multiple evidence files,
return a ZIP. The user dispatches and merges.

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
