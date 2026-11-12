# Gate 17 · CPA and CCA1 security of the PRF scheme (`prfFixedScheme_cpa`, `prfFixedScheme_cca1`)

Round 1. Auditor Codex (standing ruling, 2026-11-11: Codex for audits and reviews).

- **PR:** draft [PR #293](https://github.com/Shilun-Allan-Li/tcslib/pull/293) at
  `63ca0eb3dccb65542e90c181b7ceb0a4a4a46272` (branch `land/pass-shelat-pk-cpa-cca1`).
- **Target and base:** it targets `cryptography/pass-shelat-ch2-4` on base
  `ce22c4da63633601aa068dcc26dc0fcb7b6907f9`. The fill was issued on `8c3afbff69ad1273446750f47c05d424ab13ebe2`
  (after #292). Every commit between the two is records only, and so are later base commits.
- **Commits:** the worker's 8 commits (Claude fill `pk-cpa-cca1`), then one maintainer commit of landing edits.
- **Scope:** this is a proof audit. The two statements passed Gate 04 and are unchanged.

## The targets

They live in `PrivateKey/OracleFromPRF.lean`, namespace `TCSlib.Cryptography.Composability`. The section variables
are `F`, an evaluator `E`, `hE : PolyTimeComputable E` and the agreement `hFE`.

```lean
theorem prfFixedScheme_cpa (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cpa
theorem prfFixedScheme_cca1 (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cca1
```

The source is [PS10, Theorem 168.2]: R. Pass and a. shelat, *A Course in Cryptography*, third edition, January
2010. The scheme is Algorithm 99.1, `Enc_k(m) = ⟨r, m ⊕ f_k(r)⟩` with fresh `r`. The game is
`FixedLengthScheme.indGame` (`PrivateKey/OracleSecurity.lean`) with three oracles:
- `Enc`: fresh coins per query.
- `Dec`: `⊥` under CPA; answered only before the challenge under CCA1.
- `Challenge`: answered once, then repeated.

The proved CCA2 counterexample `prfFixedScheme_not_cca2` / `not_prfFixedScheme_cca2` (#289) is in the same file
and must be unchanged.

## The proof (check each step independently)

The bound, for each adversary with budget `q`, is (`prf_advantage_le`):

`advantage ≤ prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1)·2⁻ⁿ`

1. **PRF → random function** (`OracleFromPRF/Handler`, `Reduction`, `Transfer`, `Games`).
   - For each bit `b` there is a reduction `D_b`:
     - T2 (`exists_interactiveHandlerMachine`) for the handler `pkHandler q atkBit b`;
     - then the input-free companion `exists_toCompOn_of_toComp`;
     - then T4 (`exists_toOracleAdversary_of_bitCodec`).
   - For **every** `f`, `D_b` accepts against `f` exactly when `A` outputs 1 in `fImpl … f`, the IND oracles
     with pad function `f` (`exists_prfReduction`).
   - The handler's seed is `q(n)` nonce tapes. Its run matches the eager experiment `eImpl` while fewer than
     `q(n)` tapes are used (`simulate_eq_of_abs_bounded`, `comp_pkAbs`, `expect_eImpl`).
   - `expect_indImpl_fImpl` matches the scheme's oracles call by call. `accept_prf_indGame` (for `n > 0`)
     averages over the key.
   - Check:
     - the CCA1 decryption path (`pkHandler_impl_dec_open/_closed`, `runAt_prfDec`,
       `decodeFin_runAt_prfDec_of_not_wf`);
     - the budget `qRed q = q·1 + 0`;
     - the width transports.
2. **The random-function experiment** (`Lazy`, `Collision`).
   - `expect_lazyImpl` turns the average over a uniform `R` into a lazy table.
   - The bad flag is raised when the challenge's `r*` is already a table point (an earlier `Enc` nonce or, under
     CCA1, a pre-challenge `Dec` nonce), or when a later `Enc` uses `r*`.
   - `lazyImpl_agree` and `identical_until_bad` handle the good states, changing the pad by
     `y ↦ y ⊕ m₀ ⊕ m₁` (`xorPerm`).
   - Per query, `lazyImpl_step` bounds the probability by `(|T| + 1)/2ⁿ` and `lazyImpl_grow` adds at most one
     point. `prob_bad_le` (a potential argument) then gives `q²/2ⁿ`.
   - Check that the bad event covers every way `b` can be read, including repeated challenges and `Dec` of the
     challenge ciphertext. The worker's report §1 explains why one draw against `q` points is not enough.
3. **The bound** (`prf_advantage_le`, `prf_indSecure`).
   - For `n > 0`, the triangle inequality through the two random-function experiments; for `n = 0`,
     `advantage ≤ 1`.
   - Negligibility follows from `PRF.negligible_prfAdv` twice at budget `qRed q`,
     `EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg` and `Negligible.add`.
   - Nothing is assumed about `n`.

**Deviations from the brief.** Both are recorded in the target docstrings, and the brief allows them ("or the
exact form you prove"):
- one reduction per bit instead of the bit in the seed;
- a `q²` collision term instead of `q`.

Is either a weakening?

## Also check

- **Statement freeze.** The two targets are byte-identical to the base, and so are `prfFixedScheme_not_cca2`,
  `not_prfFixedScheme_cca2` and every other existing declaration.
- **Authorized readers.** `PrivateKey/OracleSecurity.lean` has exactly four additions:
  - `indSpec_encDom` and `indSpec_encRng`;
  - `indImpl_enc_onSpec`;
  - `indImpl_challenge_repeat_onSpec`.

  Each must be public, not `@[simp]`, with a formula docstring, and there must be no other change.
- **Rule 10.** No touched declaration reads another file's definition, including generated matchers and
  projections. The six helper modules count as foreign to each other and to `OracleSecurity`, `FromPRF`, the PRF
  `Defs`, `LazySampling`, `Efficiency`, `Hopping` and the `PublicKey/AdaptiveCPA` helpers.
- **API.** Check the names, formula docstrings and sketches (policy §3), the absence of `@[simp]`, file sizes
  (all under 1000 lines; the owned file has 885), and the facade's `## Contents`.
- **Duplication.** The generic material the review found (DL-34, deferred to the DL-30–DL-34 consolidation
  PR) is not a finding unless you disagree with deferring it or find an undisclosed copy that DL-34 misses.
- **Landing edits** (`63ca0eb3`, review findings 1–5 and 8). They must change no statement and no proof route:
  - two copies removed (`toComp_costBoundedBy` re-pointed to `NUPPT`, `eq_of_ofFn_eq` replaced by
    `List.ofFn_injective`);
  - formula docstrings and proof sketches added;
  - three long lines wrapped;
  - the `fImpl` docstring qualified with "under CPA and CCA1".
- **Edge cases:**
  - budget 0;
  - `n = 0`;
  - no challenge;
  - repeated challenges;
  - `Dec` on the challenge ciphertext or on malformed strings;
  - the timeout output.

## Evidence

- `review.md`: the maintainer's independent review (ACCEPT WITH LANDING EDITS), with its findings table and
  dispositions.
- `verification.zip`: the review's raw evidence, run before the landing edits:
  - integrity;
  - fresh build of 251 modules, 0 errors;
  - admission census (29 → 27);
  - statement comparison (134 added, 0 changed, 0 removed);
  - axiom census of 434 constants;
  - whole-file closure seals of all 8 files, with base controls and 226 negative controls;
  - the explicit-reader scan;
  - lint.

  `PROVENANCE.txt` and the inner `SHA256SUMS` describe it.
- `landing/`: logs at the final head.
  - `edit-rebuild.jsonl`: the 10 affected modules rebuilt after the landing edits, rc 0, with each row's
    `source_sha256` matching `source-head.json`.
  - `root-checks.jsonl`, `root-order.txt`: the 28 downstream modules through `TCSlib`, rc 0, on the full-library
    tree. All 8 changed files are hash-bound. `audits/pass-shelat/Checks` does not import Encryption, so it is
    not downstream.
  - `axioms-head.log`: at the head, `prfFixedScheme_cpa`, `prfFixedScheme_cca1`, `prfFixedScheme_not_cca2` and
    `not_prfFixedScheme_cca2` each print `[propext, Classical.choice, Quot.sound]`.
- `worker-report.md`: the worker's report, which is its `REPORT.md` at exchange `5285ea8a`.
- `pr.diff.txt`: `git diff` base..head.
- `source-head.json`: the head hashes of the 8 changed files.
- `sources.zip`: the 168-module source closure of `OracleFromPRF` at the head.

## Findings delivery

Return `gate17-pk-cpa-cca1-findings.md` as a Markdown file in this chat. For multiple evidence files, return a
ZIP. The user dispatches and merges.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Severities:
- **blocker:** a false or unusable statement, or a scope violation.
- **major:** an incomplete argument, a forbidden new read in a touched declaration, a statement change, or
  necessary evidence that cannot be verified.
- **minor:** documentation or API defects.
- **note:** anything else.

Report the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
