# Gate 15 · CPA pilot proofs (`adaptive_cpa`, `bitwise_padded_cpa`)

Round 1. Auditor Codex. Seyoon ruled on 2026-11-11 for one combined audit of both PRs. It covers
two draft PRs:

- [PR #290](https://github.com/Shilun-Allan-Li/tcslib/pull/290) at
  `95df0b4fa15e140ffd8f692699c66d0683fc916d` (branch `land/pass-shelat-adaptive-cpa`), targeting
  `cryptography/pass-shelat-ch2-4` on base `eedf7c1b13a244513c2c90e30bc2344291c077aa`. That base is the
  campaign after #287–#289; later base commits are records only.
- [PR #291](https://github.com/Shilun-Allan-Li/tcslib/pull/291) at
  `c286bc6a9b372036f959a033729d841ce10dfa16` (branch `land/pass-shelat-bitwise-cpa`), **stacked on #290**.
  Its base is #290's head.

Together they prove the two statements frozen by Gate 12 (#287):

- `Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa` (`PublicKey/AdaptiveCPA.lean`). Single-challenge
  CPA security gives security in the adaptive multi-challenge game.
- `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa` (`PublicKey/BitwiseCPA.lean`). Single-bit security
  gives CPA security of the padded bitwise scheme with key-dependent n-bit messages.

With them, **`SingleBitSecure.exists_adaptive_cpa`** is admission-free: some scheme with n-bit messages and the
same key generator is adaptively CPA-secure. This is the generic core of the first Implications
catalog route. The source is [PS10], R. Pass and a. shelat, *A Course in Cryptography*, third edition, January
2010: Definition 171.5 and the bitwise scheme and hybrid argument of p. 103. The adaptive extension is
added reasoning; [Pas09, Theorem 2] covers the fixed-vector case.

## #290: the adaptive lift

The owned file imports four helpers in `PublicKey/AdaptiveCPA/`: `Hybrid`, `Handler`, `Games` and
`Reduction`. Check each step independently.

1. **Hybrids.** `H_i` (`acHyb`) answers the first `i` fresh challenges with the right message.
   - `castImpl_adaptiveIndImpl` reads the adaptive oracle through the published equations only.
   - `acHyb_lt_zero` and `acHyb_lt_cap` give the two endpoints.
2. **The T2 handler.** `acHandler` takes `perCall = 1` and `finCall = 0`.
   - Its state holds the challenge count, the hybrid index `i⋆` and the latest ciphertext.
   - Its seed is `cap` encryption tapes.
   - Check its call equations (`_impl_dec`, `_full`, `_eager`, `_forward`) and its polynomial-time
     proof.
3. **`B`'s game equals `H_{i⋆+b}`.**
   - The composite simulation is abstracted by history (`acAbs`, `comp_acAbs`, `simulate_eq_of_abs`).
   - Eager and lazy tapes are related by `expect_tapeImpl` and `expect_sample_update`.
   - At `i⋆` the selector is `b`.
4. **The bound.**
   - `exists_advantage_hybrid_gap` at `cap(n) > 0`, with `choose` for the advice.
   - `cap(n) = 0` has advantage 0.
   - `h` is applied at budget `q·perCall + finCall`.
   - `Negligible.polyExpr_mul` with `cap` concludes. Nothing is assumed about `n`.

## #291: bitwise CPA

The owned file imports three helpers in `PublicKey/BitwiseCPA/`: `Eager`, `Planted` and `QueryHandler`. It
follows the `padded_cpa` proof (Gate 13).

1. **Bit hybrids.** `H_j` uses eager coins. `accept_indGame_eq` gives the endpoints. At `n = 0` the
   advantage is 0.
2. **The T1 distinguisher.**
   - The query-recording handler `qHandler` records the first challenge and repeats its answer.
   - The planted tuple (`plantTuple_spec`) puts block `j⋆` as the input ciphertext `c` and encrypts the
     other blocks on its seed tapes.
   - The output rule is flip/zero.
   - The advice `bwAux` has length `bwLaux`.
3. **The exact signed identity.** `hyb_advantage_eq` covers the case split over `(0,1)`, `(1,0)`, equal
   bits and no challenge.
4. **The bound.** `n · distAdv`, from `singleBitSecure_iff` and `Negligible.polyExpr_mul .var`.

## Both

- **Statement freeze.** The two targets and both corollaries keep their headers. No older declaration
  changes.
- **Rule 10.** No touched declaration reads another file's definition. The helper modules count as foreign
  to each other and to `AdaptiveSecurity`, `OracleSecurity`, `EnsembleSecurity` and `Efficiency`.
- **API.** Check names, formula docstrings, sketches, the absence of `@[simp]`, and file sizes.
- **Duplication.** Generic material recorded for later promotion is DL-30–DL-33 (in the bundle). It is
  not a finding unless you disagree with the deferral or find an undisclosed copy.
- **Landing edits.**
  - #290: docstrings and `## Contents`, a private copy removed, an unused simp argument removed.
  - #291: two duplicates of #290's lemmas removed, a `convert` speed fix, docstrings, `## Contents`,
    reflow.

  These must change no statement and no proof route.
- **Edge cases.** Budget 0, cap 0, repeated challenges or ciphertexts, no challenge, the forwarded
  challenge never reached, and the timeout output.

## Evidence

- `review-290.md`, `review-291.md`: the maintainer's independent reviews.
- `verification-290.zip`, `verification-291.zip`: their raw evidence, run on the landing branches before the
  landing edits:
  - integrity and fresh builds (201 and 204 modules, 0 errors);
  - admission census, statement comparison and axiom census;
  - whole-file closure seals with base controls, 55 and 60 negative controls, and the explicit-reader scan.
- `landing-290/`, `landing-291/`: logs on the final heads.
  - The affected modules rebuilt after the landing edits.
  - The downstream modules checked through `TCSlib` and `audits/pass-shelat/Checks` on the full-library tree.
  - `landing-291/axioms-head.log`: `adaptive_cpa`, `bitwise_padded_cpa`, `bitwise_padded_adaptive_cpa` and
    `exists_adaptive_cpa` at #291's head each print `[propext, Classical.choice, Quot.sound]`.
- `worker-report-290.md`, `worker-report-291.md`, `pr290.diff.txt`, `pr291.diff.txt`, `source-head.json` (#291 head).
- `sources.zip`: the 161-module source closure at #291's head.

## Findings delivery

Return `gate15-cpa-pilot-proofs-findings.md` as a Markdown file in this chat. For multiple evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Severities:
- **blocker:** a false or unusable statement, or a scope violation;
- **major:** an incomplete argument, a forbidden new read in a touched declaration, a statement change, or
  necessary evidence that cannot be verified;
- **minor:** documentation or API defects;
- **note:** anything else.

Report the audited heads and counts by severity, per PR if they differ. The gate closes at zero blockers and zero
majors.
