## ===== briefs/pass-shelat-ch5-8/gates/17-pk-cpa-cca1/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/17-pk-cpa-cca1/review.md =====

# pk-cpa-cca1 · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS** (0 blockers, 0 majors, 1 medium, 4 low, 6 info).

Delivery: Claude worker, exchange `5285ea8a` (`inbox/fills/pk-cpa-cca1/`), 8 patches on
`8c3afbff69ad1273446750f47c05d424ab13ebe2`. Independent review on the landing branch (parent = campaign
`ce22c4da`, 0 Lean changes since the base); evidence `review-evidence.zip` (SHA-256 `f36b9eaa624883fa030435f888b17cca5f93dbb30e52f6e61b93af1d818570ab`;
`PROVENANCE.txt`; inner `SHA256SUMS` 527 entries).

## Checks (re-run by the reviewer)
- Integrity: payload sums 101/101; `git am` reproduces `src/` and the worker's tree.
- Build: the `PrivateKey/OracleSecurity` closure plus downstream (251 modules; the issued order missed the two
  Implications modules) 251/251, 0 errors; touched modules 0 warnings.
- Admissions 29 → 27 (exactly the two targets). Statements: 134 ADDED, 0 CHANGED, 0 REMOVED; the four
  OracleSecurity readers match the brief's names and the `_onSpec` form.
- Axioms: both targets, `not_prfFixedScheme_cca2`, and all 434 stored constants of the 8 modules standard.
- Rule 10: whole-file closure seals 8/8 (678–2,281 requests) with base controls; 16 probes, 226 negatives
  ALL_OK; explicit scan 1,376 items, 0 foreign. Lint 0 FAIL (same 5 WARN as base).
- The worker's deviations (one reduction per bit; bound `prfAdv(D₀)+prfAdv(D₁)+(q²+1)2⁻ⁿ`) are sound and
  within the brief; `q²` is needed because later encryptions can hit `r*`.

## Findings and dispositions
| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | medium | `PRFGame.toComp_costBoundedBy` copies `NUPPT.toComp_costBoundedBy`. | **Landing edit:** removed, re-pointed. |
| 2 | low | `PRFGame.eq_of_ofFn_eq` = `List.ofFn_injective`. | **Landing edit.** |
| 3 | low | Prose-only lemma docstrings (Collision, Lazy, Transfer). | **Landing edit:** formulas added. |
| 4 | low | Long proofs without sketches (Handler, Collision, Lazy). | **Landing edit:** sketches added. |
| 5 | nit | Three lines over 100 characters. | **Landing edit.** |
| 6 | low | Undisclosed copies of private AdaptiveCPA handler pieces in `Handler.lean`; `ofFn_pkTapes` re-proves `ofFn_acTapes`. | Ledger DL-34. |
| 7 | info | Private-key `indCodec_eq_bitCodec`; `mem_keys_of_lookup_isSome` near core. | Ledger DL-34. |
| 8 | info | `fImpl` docstring said "oracles of IND_b" without the attack qualifier. | **Landing edit:** "under CPA and CCA1". |
| 9 | info | Public `abbrev LState` has no `_eq` lemma. | No action (abbreviation). |
| 10 | info | The worker's reported seal failure came from sealing `PolyExpr.eval` (notation by ruling). | No action. |
| 11 | info | Bound soundness confirmed. | — |

## Landing
Branch `land/pass-shelat-pk-cpa-cca1` at `63ca0eb3dccb65542e90c181b7ceb0a4a4a46272` (8 delivered commits + landing
edits). After the edits: 10 affected modules rebuilt (0 errors, hash-bound); 28 downstream modules through
`TCSlib` rc 0 on the full tree (`landing/`). PR #293 (draft).

## ===== briefs/pass-shelat-ch5-8/gates/17-pk-cpa-cca1/worker-report.md =====

# Fill report · `pk-cpa-cca1` · final

**Worker** Claude (external fill, exchange push route). **Issue base**
`8c3afbff69ad1273446750f47c05d424ab13ebe2` on `cryptography/pass-shelat-ch2-4`. **Proof branch**
local `fill/pk-cpa-cca1` at `79f34dadd` (8 commits over the base; never pushed). **Pack** read at
exchange `db04fd415`; `sha256sum -c SHA256SUMS` in `outbox/fills/pk-cpa-cca1/`: all 7 OK
(`evidence/logs/pack-sha256.log`). Source hashes: `sha256sum -c SOURCE-SHA256SUMS` at the base,
242/242 OK (`evidence/logs/source-sha256.log`). Checkpoint 1: exchange `d458a5848`; checkpoint 2:
exchange `d9e7bcce1`.

## 1. Result

**`Composability.prfFixedScheme_cpa` and `Composability.prfFixedScheme_cca1` are proved.** No
admission remains in the touched files. Both statements are byte-identical to the base (only the
bodies and the sketches changed). Axioms of both targets: `[propext, Classical.choice,
Quot.sound]`. No escalation: both targets are true as stated, and every reader the proof needs is
published (the four authorized `OracleSecurity` readers, plus readers in my own helper modules).

**The bound.** For an adversary `A` with budget `q` and the attack `atkOf atkBit` (`CPA` for
`false`, `CCA1` for `true`), there are PRF distinguishers `D₀`, `D₁` with, for every `n`,

`advantage(IND₀, IND₁) ≤ prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) · 2⁻ⁿ`

(`prf_advantage_le`). The right side is negligible (`prf_indSecure`).

| Brief step | Delivered as |
|---|---|
| 1 PRF → random function | `PRFGame.exists_prfReduction` (`OracleFromPRF/Reduction.lean`). For each bit `b` there is a next-query machine `D_b`: T4 (`exists_toOracleAdversary_of_bitCodec`) of T2's machine (`exists_interactiveHandlerMachine`) for the handler `PRFGame.pkHandler q atkBit b`, through the input-free companion of `A` (`exists_toCompOn_of_toComp`). For **every** `f`, `D_b` with budget `qRed q` accepts against `f` exactly when `A` outputs `1` in the experiment `PRFGame.fImpl … f` (the IND oracles with pad function `f`). The handler's seed is `q(n)` nonce tapes (`pkTapes`). Its state counts the tapes used and records the challenge. Composed with the outer oracle `f`, its run is the experiment with the tapes in advance (`eImpl`) while fewer than `q(n)` tapes are used (`simulate_eq_of_abs_bounded`, `comp_pkAbs`); uniform tapes are fresh nonces (`expect_eImpl`). In the owned file, `accept_prf_indGame` (`n > 0`) shows the IND game is `fImpl … (F n k)` averaged over the key; `expect_indImpl_fImpl` in `Transfer.lean` matches the scheme's oracles call by call. `prfAdv_prfReduction` gives `prfAdv(F_n, D_b) = \|Pr[IND_b = 1] − 𝔼_R Pr[A → 1 against fImpl … R]\|`. |
| 2 random-function game | `PRFGame.expect_lazyImpl` (`Lazy.lean`): averaging over a uniform `R` is the lazy experiment `lazyImpl` (a table, the challenge record and a bad flag). The flag is raised when the challenge's `r*` is already a point of the table (an earlier encryption's nonce or, for CCA1, a pre-challenge decryption's), or a later encryption uses `r*`. `lazyImpl_agree` + `identical_until_bad` (`Collision.lean`): from a good state the two bits give good successors the same law. At the first challenge the pad is changed by `y ↦ y ⊕ m₀ ⊕ m₁` (`xorPerm`, `ctOf_xorPerm`, `expect_sample_equiv`). Decryption is refused after the challenge (`decOpen` for CPA and CCA1). `lazyImpl_step`: from a good state a query raises the flag with probability at most `(\|T\| + 1)/2ⁿ`. This uses `prob_mem_le` through `expect_sample_mem_le`: on the table's keys for the first challenge, and on `[r*]` for an encryption. `lazyImpl_grow`: a query adds at most one point. `prob_bad_le` (a potential argument) gives `Pr[bad] ≤ q · q / 2ⁿ`. Hence `abs_prob_lazyImpl_sub_le` and `abs_expect_fImpl_sub_le`: the two random-function experiments differ by at most `q(n)² / 2ⁿ`. |
| 3 the bound | `prf_advantage_le` (owned, private). For `n > 0`, use the triangle inequality through the two random-function experiments. For `n = 0`, `advantage ≤ 1 ≤ q(0)² + 1`. `prf_indSecure`: `ε n = prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + ((q·q + 1)(n)) · (2⁻¹)ⁿ` is negligible. This follows from `PRF.negligible_prfAdv` (twice, budget `qRed q`), `EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg` and `Negligible.add`. The targets are `prf_indSecure` at `atkBit = false` and `true` (`atkOf_false`, `atkOf_true`). |

**Deviation from the brief's route.** Both target docstrings record this.
- **The bit.** The brief puts the challenge bit in the reduction's seed, with a finalization that compares the guess with it. Instead I hard-wire the bit: one reduction per bit, each forwarding the adversary's guess.
- **The bound.** The brief's bound is `2 · prfAdv + q(n)/2ⁿ`; mine is `prfAdv(D₀) + prfAdv(D₁) + …`. The brief allows this ("or the exact form you prove").
- **The collision term** is `q(n)²/2ⁿ`. The bad event is bounded query by query: at most `q` steps can raise it, each against at most `q` recorded points. A single draw against `q` points is not enough, because the adversary's later encryptions can also hit `r*`.
- **The `+ 1`** covers `n = 0`.

**Edge cases.**
- **Budget and timeout.** The proof treats the adversary's computation abstractly, so it holds for every budget and for the codec's timeout output.
  - `q = 0` is included: `prob_bad_le` gives `0`.
  - The same `A.toComp` run appears in the game, the reduction and the lazy experiments.
  - The reduction's own budget `qRed q = q · 1 + 0` covers that run (`toComp_costBoundedBy`, `simulate_eq_of_abs_bounded`).
  - The handler's finalization asks nothing and returns `A`'s bit (`pkHandler_finish`).
- **`n = 0`:** `advantage ≤ 1` (see the step 3 row above).
- **No challenge:** the record stays `none` and the experiments never read `b`. The challenge never raises the flag.
- **Repeated challenges** return the recorded ciphertext:
  - in the game (`indImpl_challenge_repeat_onSpec`);
  - in `fImpl` and `lazyImpl` (`_challenge_some`);
  - in the handler (`pkHandler_impl_challenge_some`).
- **`Dec` on the challenge:** after the challenge, CPA and CCA1 answer `⊥` (`decOpen_atkOf`), as the game does.
- **`Dec` on malformed strings:** the answer is `⊥`. See `decWF`, `ofFn_prf_decAnswer` (via `decodeFin_runAt_prfDec_of_not_wf`) and `pkHandler_impl_dec_closed`.

**Checkpoints.**
- 1 (`d458a5848`): step 1.
- 2 (`d9e7bcce1`): step 2.
- Final: step 3, the seal fixes (§6) and all checks.

## 2. Changed files and declarations

`git diff --stat 8c3afbff6..79f34dadd`: 8 files, 2975 insertions, 24 deletions.

| File | Lines | Change |
|---|---|---|
| `PrivateKey/OracleFromPRF.lean` (owned) | 579 → 885 | Imports the six helpers. Module docstring: the title's "(statement phase)" is dropped; the status lines of the two targets are updated; a `## Contents` list is added, because `OracleFromPRF/` now exists and the lint treats the file as a facade. Adds the private section `PRFStep` before the targets. Changes the two sketches and bodies. |
| `PrivateKey/OracleSecurity.lean` (authorized readers) | 345 → 374 | Adds `indSpec_encDom`, `indSpec_encRng`, `indImpl_enc_onSpec` and `indImpl_challenge_repeat_onSpec`: public, not `@[simp]`, with formula docstrings, beside the existing `_onSpec` readers. Nothing else changed (0 removed lines). |
| `…/OracleFromPRF/Games.lean` (new) | 327 | Ciphertexts `ctOf`, `decWF`, `decAns`. The experiment with a pad function (`fImpl`) and with nonce tapes (`eImpl`). `expect_simulate_congr`, `simulate_eImpl_congr`, `expect_eImpl`. |
| `…/OracleFromPRF/Handler.lean` (new) | 741 | Lengths `ctP`, `pkDin`, `pkDout`, `pkOut` (abbrev), `pkStLen`. State `recBits`, `pkState`, `pkHState`. Tapes `pkTapes`, `pkSeedTapes`. The T2 handler `pkHandler` (`simps`, `isSimp := false`) and its answers. |
| `…/OracleFromPRF/Reduction.lean` (new) | 372 | `simulate_eq_of_abs_bounded`, `fOuter`, `atkOf`, `qRed`, `pkAbs`, `comp_pkAbs`, the width transports, `toComp_costBoundedBy`, `exists_prfReduction`. |
| `…/OracleFromPRF/Transfer.lean` (new) | 205 | Vector readings. `expect_indImpl_fImpl`: a scheme with `ctOf`-shaped encryption and `decWF`-shaped decryption is `fImpl`, call by call. `indCodec_eq_bitCodec`, `expect_fImpl_transport`. |
| `…/OracleFromPRF/Lazy.lean` (new) | 473 | `LState`, `rStar`, `padAt`, `look`, `ovr`, `addPt`, `hitStar`, `lazyImpl`; `expect_lazyImpl`. |
| `…/OracleFromPRF/Collision.lean` (new) | 498 | `prob_bad_le`, `expect_sample_mem_le`, the `b`-independence lemmas, `xorPerm`, `lazyImpl_agree`/`_stick`/`_grow`/`_step`, `abs_prob_lazyImpl_sub_le`, `abs_expect_fImpl_sub_le`. |

Every file is under 1000 lines. `Handler.lean` is over the lint's 600-line target (INFO only).

**New public declarations.** Each has a formula docstring, and a proof sketch when nontrivial. Definitions have `_eq`, `_apply` or case lemmas.
- **`Games`:**
  - `ctOf` (+ `_eq`, `length_ctOf`), `decWF` (+ `_eq`), `decAns` (+ `_eq`);
  - `expect_simulate_congr`;
  - `fImpl` (+ `_enc`, `_dec`, `_challenge_none`, `_challenge_some`) and `eImpl` (+ the same four);
  - `simulate_eImpl_congr`, `expect_eImpl`.
- **`Handler`:**
  - lengths: `ctP` (+ `_eval`), `pkDin` (+ `_zero/_one/_two`), `pkDout` (+ `_zero/_one/_two`), `pkOut` (+ `_eq`), `pkStLen` (+ `_eq`);
  - state: `recBits` (+ `_none`, `_some`, `length_recBits`), `pkState` (+ `_eq`), `pkHState` (+ `_eq`);
  - tapes: `pkTapes` (+ `_apply`, `ofFn_pkTapes`), `pkSeedTapes` (+ `_eq`);
  - the handler: `pkHandler` with its `simps` equations, `pkHandler_init_eq`, `pkHandler_init_hstate`, `pkHandler_finish`, and the answers `pkHandler_impl_enc`, `_impl_dec_open`, `_impl_dec_closed`, `_impl_challenge_some`, `_impl_challenge_none`;
  - 33 private helpers: the round function `pkRun`, `pkFin`, their polynomial-time proofs and their reading lemmas.
- **`Reduction`:**
  - `simulate_eq_of_abs_bounded`;
  - `fOuter` (+ `_apply`; private `fOuter_tape`), `atkOf` (+ `_false`, `_true`, `decOpen_atkOf`), `qRed` (+ `_eval`), `pkAbs` (+ `_eq`);
  - `comp_pkAbs`, `ofFn_evalFn_toCompOn`, `expect_fImpl_width`, `eval_toOracleAdversary_width`, `toComp_costBoundedBy`, `exists_prfReduction`.
- **`Transfer`:** `ofFn_arrowCongr_finCongr`, `padFin_replicate_false`, `padFin_nil`, `eq_of_ofFn_eq`, `expect_indImpl_fImpl`, `indCodec_eq_bitCodec`, `expect_fImpl_transport`.
- **`Lazy`:**
  - the state: `LState`, `rStar` (+ `_eq`, `rStar_ctOf`), `padAt` (+ `_eq`, `padAt_ctOf`), `look` (+ `_none`, `_some`, `look_flag`), `ovr` (+ `_apply`), `addPt` (+ `_eq`), `hitStar` (+ `_some`, `_none`);
  - the experiment: `lazyImpl` (+ `_enc`, `_dec_open`, `_dec_closed`, `_challenge_some`, `_challenge_none`);
  - recorded values: `zipWith_xor_cancel_left`, `ovr_addPt_of_isSome`, `ovr_addPt_of_none`, `ovr_addPt_self`, `ovr_record_of_none`, `ovr_record_of_some`;
  - `expect_lazyImpl`.
- **`Collision`:**
  - generic: `prob_bad_le`, `expect_sample_mem_le`, `mem_keys_of_lookup_isSome`, `abs_expect_sub_le`;
  - state readings: `length_addPt_le`, `flag_addPt`, `look_eq_of_hitStar`, `isSome_look_eq`, `addPt_eq_of`, `ovr_init`;
  - the change of variables: `xorPerm` (+ `_apply`, `ctOf_xorPerm`);
  - the lazy experiment: `lazyImpl_agree`, `lazyImpl_stick`, `lazyImpl_grow`, `lazyImpl_step`, `abs_prob_lazyImpl_sub_le`, `abs_expect_fImpl_sub_le`.

**New private declarations in `OracleFromPRF.lean`** (section `PRFStep`): `prf_gen_runAt`,
`prfKeyEq`, `ofFn_prfKeyEq`, `prfNonceEq`, `ofFn_prfNonceEq`, `ofFn_prf_encryptAt`,
`ofFn_prf_decAnswer`, `prf_ctLen_eval`, `prf_inLens`, `prf_outLens`, `accept_prf_indGame`,
`prfAdv_prfReduction`, `prf_advantage_le`, `prf_indSecure`.

**Sketch edits.** Both target docstrings keep their first paragraph (the statement prose). Each gets a
`**Deviation:**` paragraph (see §1) and a `**Proof sketch.**` describing the delivered proof, replacing
"Proof sketch (the source's)". The module docstring's status lines now say "proved" and give the bound.

## 3. Promotion, duplication and reader requests (DL-30 to DL-33)

**Promotion requests.** These generic facts are in my helper modules because every other file is
frozen. The proposed homes:
1. **`Games/Probability.lean`** (with DL-30): `Collision.abs_expect_sub_le` (expectations of pointwise
   `ε`-close functions are `ε`-close).
2. **`Games/Hopping.lean`:**
   - `Collision.prob_bad_le`: a bad event raised with probability at most `(size + 1)·δ` per query, by queries that grow the size by at most one, has probability at most `q·(size + q)·δ`. This is the potential argument the brief's "adaptive repeated-nonce event" needs.
   - `Collision.expect_sample_mem_le`: `prob_mem_le` for a fixed list.
3. **`Games/Simulate.lean`** (with DL-32's `simulate_eq_of_abs`):
   - `Games.expect_simulate_congr`: implementations with equal per-call expectations simulate alike.
   - `Reduction.simulate_eq_of_abs_bounded`: DL-32's `AdaptiveCPA.simulate_eq_of_abs` with a counter budget and deterministic steps. It generalizes that lemma's use in this unit.
4. **`Games/Machines.lean` or `Games/Bridges`:** `Reduction.toComp_costBoundedBy`,
   `ofFn_evalFn_toCompOn`, `eval_toOracleAdversary_width`.
5. **Beside `padFin` in `Asymptotic/Adversary.lean`** (with DL-31 and DL-32): `Transfer.padFin_nil`,
   `padFin_replicate_false`, `eq_of_ofFn_eq`, `ofFn_arrowCongr_finCongr`.
6. **A shared list module:** `Lazy.zipWith_xor_cancel_left` and `Collision.mem_keys_of_lookup_isSome`.
   For Bool vectors: `Collision.xorPerm`.
7. **Readers of `OracleSecurity` derived from published ones:** `Transfer.indCodec_eq_bitCodec` for
   the private-key `indCodec`. The public-key one is DL-32's reader request.

**Uses joining open ledger entries.** This fill adds new uses of:
- `GGMRed.ofFn_padFin_of_length` (DL-31);
- `AdaptiveCPA.ofFn_cast` (DL-32);
- `ChallengeSim.expect_sample_equiv`, `_comm` and `_prod` (DL-30);
- `BitwiseSim.expect_sample_update` and `AdaptiveCPA.expect_sample_update` (DL-33);
- `AdaptiveCPA.msgOf`, `extTape`, `ofFn_splitHalf_fst`/`_snd` and `headD_ofFn_one` (DL-32 candidates).

**Duplication inside the owned file.** My private `prf_gen_runAt`, `ofFn_prf_encryptAt` and
`ofFn_prf_decAnswer` overlap the pre-existing private CCA2 helpers `cca2Gen`, `cca2Encrypt`,
`cca2Cipher` and `cca2Decrypt` of the same file. I did not reuse those helpers, for three reasons:
- they are frozen;
- they are stated for the CCA2 adversary's shapes;
- two of them (`cca2Encrypt`, `cca2Gen`) read `PolyExpr.eval` definitionally (see §6).

A consolidation could state one set of readers for the key, encryption and decryption, and prove
both parts from it.

**Reader requests.** None blocking. The four authorized `OracleSecurity` readers were all used.

## 4. Environment, cache and bootstrap

- **Preflight** (`evidence/logs/preflight.log`): `nproc` is 4.
  - Memory: the cgroup v1 limit is the unlimited sentinel, so the headroom is `MemAvailable` = 15.22 GiB (floor 4 GiB): PASS.
  - Disk: the clone's filesystem is ext4 with 18.79 GiB free (floor 12 GiB): PASS.
- **One clone** (`/home/user/fill`): the clone and `.lake/packages` this session used for the earlier
  CPA fills on this host. The toolchain and manifest are identical. For the patch check I added a
  temporary detached `git worktree` of that clone at the base, ran no Lean in it, and removed it.
- **Cache and packages.**
  - The store held 2,372 files (118,543,444 bytes) before the fetch, written by those earlier fills; nothing was downloaded.
  - Narrowed `lake exe cache get` for the 97 roots (identical to `roots.txt`) printed "No files to download", "Decompressing 2370 file(s)" and "Completed successfully!", exit 0 (`cache-get.log`).
  - The cache probe passed (`cache-probe.log`).
  - Packages PASS before and after the fetch (`packages.log`). `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean` are ABSENT; the order list imports none of them.
- **Bootstrap** into a fresh olean tree `.lake/pk-oleans`:
  - the 128-module closure of `PrivateKey/OracleFromPRF`, in the order list's order (`bootstrap.log`, `bootstrap-closure.txt`);
  - then the 21 + 11 further upstream modules the helpers import, in dependency order (`bootstrap-extra*.log`, `bootstrap-extra*.txt`).

  The sweep rebuilt everything.
- **Process discipline.** One Lean process at a time; every check went through
  `scripts/lean_check_tree.sh` (`evidence/tools/chk.sh` logs start, end, status, elapsed time and
  maximum child RSS). No `lake build`. Two deviations:
  - **A hung check.** One development check of `Collision` ran past the tool runner's 10-minute foreground limit, and I stopped it. The cause was an `exact` whose type check unfolded `ovr` through `fImpl`; I replaced that step with explicit rewrites (`ovr_init`). Afterwards I wrapped some single development checks in `timeout` (15–25 min) as a guard. None timed out.
  - **An aborted sweep.** I aborted a first full sweep after 18 modules because the seal (§6) required source changes. It had just removed `Build/Loop.olean`, which I rebuilt alone before the next check (`logs/dev/sweep-aborted.log`, `logs/dev/loop-rebuild.log`). The reported sweep was then run once at the final head.

  Development logs are in `evidence/logs/dev/`.

## 5. Checks

| Check | Result | Evidence |
|---|---|---|
| Owned and helper modules | `OracleFromPRF`, `OracleFromPRF/{Games, Handler, Reduction, Transfer, Lazy, Collision}`, `OracleSecurity`: no errors, no warnings | `logs/sweep.log` |
| Sweep (final head `79f34dadd`) | `order-new.txt`, 249 modules, one `lean_check_tree.sh` call each: **249 passed, 0 failed** (01:02–01:20 UTC; peak child RSS 2,946 MiB) | `logs/sweep.log` |
| `sorry` census | **27** (base 29); removed vs base: exactly `prfFixedScheme_cpa` and `prfFixedScheme_cca1`; added: none | `logs/sorry-census.txt` |
| Axioms | `prfFixedScheme_cpa` and `prfFixedScheme_cca1`, and the untouched `prfFixedScheme_not_cca2` and `not_prfFixedScheme_cca2`: `[propext, Classical.choice, Quot.sound]` | `logs/axioms.log`, `probe/Axioms.lean` |
| Lint | `campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`: 0 FAIL, 5 WARN over 16 files. The base has the same 5 WARN (10 files), all in untouched files. | `logs/lint-after.log`, `lint-before.log` |
| Patches | `git am` of `patches/` (8 patches) onto a clean base worktree gives the proof branch's tree (`5def29bb…` = `5def29bb…`, 0 diff lines) | `logs/patch-reproduce.log` |
| Preservation | `OracleSecurity.lean`: 0 removed lines. Owned file: of the base's 77 declaration and docstring blocks, all are verbatim in the head except the module docstring and the two targets' docstring-and-body blocks. The target statement lines are unchanged. | §2 |

## 6. Readings: scan, seal, controls, explicit unfolds

- **Scan** (`seal/SealScan.lean`, `logs/seal-scan.log`).
  - Roots: every declaration of the six helper modules, the owned file's 14 private `PRFStep` declarations and two targets, and the four authorized readers. That is 177 roots; 248 declarations were scanned with their auxiliaries.
  - A definition is foreign when it lives in another module. So each helper's definitions are foreign to the other helpers.
  - 116 foreign TCSlib definitions are used. 86 are regular; these are the seal candidates (`seal/candidates.txt`). 30 are reducible: abbrevs such as `bitSpec`, `bitSpecAt`, `indSpec`, `NUPPT.Coins`, `LState` and `pkOut`, and structure projections.
  - **TCSlib instances used: 0.**
- **Seal** (`seal/Seal{Games, Handler, Reduction, Transfer, Lazy, Collision, OracleFromPRF, OracleSecurity}.lean`, `logs/seal.log`).
  - Each is a verbatim copy of one of the eight changed or new files, with `attribute [local irreducible]` on every regular foreign definition its roots use (12, 24, 41, 30, 14, 24, 51 and 4 definitions, in that order). The attribute applies from the namespace's first `open` on, so each whole file is sealed.
  - **Seven compile.** `SealOracleFromPRF` fails at exactly two pre-existing, unchanged private CCA2 helpers, `cca2Encrypt` and `cca2Gen`. They read `PolyExpr.eval .var` definitionally: they identify `Fin (PolyExpr.var.eval n)` with `Fin n`.
  - **The failure predates the fill.** `SealOracleFromPRFBase.lean` is the base's copy of the owned file, sealed with the 43 candidates that exist at the base. It fails at the same two declarations and nowhere else.
  - **Every declaration of the fill is sealed.** `SealOracleFromPRFTail.lean` is the head's sealed copy with `PolyExpr.eval` alone re-opened just before `cca2Encrypt`, which comes after both targets and all of `PRFStep`. It compiles.
  - I did not change the CCA2 proofs, because the brief freezes every other declaration. A one-line fix for each would rewrite with `PolyExpr.eval_var`.
- **Findings and fixes.** The first sealed run, at commit `fa1dea766`, failed in all six helpers and in
  the owned file's new code. Several `rfl` and `exact` proofs read definitions directly: `simulate`,
  `CostBoundedBy`, `PolyExpr.eval`, `outLens`/`inLens` (through the `cast` orientation), `INDSecure`,
  `atkOf`, `addPt`, `look`, `lazyImpl`, `fImpl`, `pkHandler` (its `stateLen` and `finCall`) and
  `pkOut`. Commit `79f34dadd` routes each through published readers:
  - `simulate_pure`, `costBoundedBy_query` and `PolyExpr.eval_*`;
  - `inLens_*`/`outLens_*`, with the cast in the reader's direction;
  - `INDSecure_iff` and the new `atkOf_false`/`atkOf_true`;
  - `addPt_eq`, `look_none`, `lazyImpl_*`, and `fImpl_challenge_some` with `Option.map_some`;
  - `pkHandler_finCall`;
  - a handler-typed state `pkHState` (+ `pkHState_eq`, `pkHandler_init_hstate`) for the reduction's state abstraction;
  - `pkOut` made an `abbrev`.

  The sweep, seals, scans and controls were redone at that head.
- **Controls** (`seal/SealControls{Unsealed,Sealed}.lean`, `logs/seal-controls.log`). There are twelve readings through definition bodies: `PolyExpr.eval`, `outLens`, `CostBoundedBy`, `simulate` and `INDSecure`, and the new helpers `atkOf`, `fImpl`, `pkHandler`, `pkHState`, `look`, `addPt` and `lazyImpl`.
  - Unsealed: all pass (0 errors).
  - Sealed with the full candidate list: all twelve fail (12 errors, one per example). **12/12.**
- **Explicit-unfold scan** (`seal/RwIds*.lean`, `logs/rwids-raw.log`, `logs/rwids-files.tsv`).
  - The scan collects every identifier the added lines pass to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`, `dsimp` or `unfold`. Each is resolved in its file's namespace with the file's `open`s: 540 entries over the eight files.
  - **No foreign definition is passed.** The definitions passed are each file's own, plus the `↓reduceIte` simproc:
    - `Handler`: `ctP`, `pkTapes`, and the private `pkRun`, `pkFin`;
    - `Reduction`: `atkOf`, `fOuter`, `qRed`;
    - owned file: the private `prfKeyEq`, `prfNonceEq`.
  - Unresolved names are local hypotheses, private lemmas of the same file, or theorem names qualified by a local scheme (`S.inLens_zero` etc.).

## 7. Order and roots

`evidence/logs/order-new.txt` (built by `evidence/tools/order.py`) has 249 modules. It is the
issued 242-module order with the six helpers and `Games/Hopping` added. Every module of the import
closure is inserted before its first consumer, by a stable post-order walk, so every module's
TCSlib imports precede it.

The owned module moves after its new upstream dependencies, which the issued list placed after
it: `AdaptiveCPA/{Hybrid, Handler, Games}`, `BitwiseCPA/Eager`, `OracleSecurity/ChallengeSim`,
`Games/Bridges/*`, `Games/Efficiency*` and others.

The Mathlib roots of the extended order are unchanged: 97, identical to `roots.txt`
(`logs/roots-new.txt`).

**Final payload delivered — ready for maintainer review**

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== briefs/pass-shelat-ch5-8/fills/pk-cpa-cca1/issued-r1/brief.md =====

# Claude fill · private-key CPA and CCA1 from a PRF (`prfFixedScheme_cpa`, `prfFixedScheme_cca1`)

**Issue base** `8c3afbff69ad1273446750f47c05d424ab13ebe2` on `cryptography/pass-shelat-ch2-4` (after #292).
**Unit** `pk-cpa-cca1`. **Worker** Claude (standing ruling, 2026-11-11). **Lean** 4.25.0 and the Mathlib revision
in that commit's `lake-manifest.json`.

Prove the two admitted theorems of [PS10, Theorem 168.2] in
`TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean`. They say that if `F` is a pseudorandom function
family, the scheme of Algorithm 99.1 (`Enc_k(m) = ⟨r, m ⊕ f_k(r)⟩` with fresh `r`) is CPA-secure and CCA1-secure.
The statements passed Gate 04. The CCA2 counterexample `prfFixedScheme_not_cca2` in the same file is proved
(#289); keep it.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/pk-cpa-cca1` at the exact issue base.
  Record the base in `REPORT.md`, and keep the proof branch local.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/pk-cpa-cca1/` on `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`, the whole `git format-patch` series from the issue base;
  - `src/`, the changed files;
  - `evidence/`.

  Commit as `fill pk-cpa-cca1: checkpoint N` and `fill pk-cpa-cca1: final`. Pull with rebase before pushing,
  push only your delivery path, and never force-push. Campaign changes land by a maintainer PR for Seyoon's
  approval.

## Targets (frozen; quoted from the issue base)

```lean
theorem prfFixedScheme_cpa (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cpa := by
  sorry

theorem prfFixedScheme_cca1 (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cca1 := by
  sorry
```

The section variables are `F`, an evaluator `E` with `hE : PolyTimeComputable E` and the agreement `hFE`. The game
is `FixedLengthScheme.indGame` (`PrivateKey/OracleSecurity.lean`). It has three oracles:
- `Enc` (index 0, fresh coins per query);
- `Dec` (index 1; under CPA always `⊥`; under CCA1 answered only before the challenge);
- `Challenge` (index 2, answered once, then repeated).

## Published interfaces

| Interface | Provider |
|---|---|
| `PRF`, `PRF.negligible_prfAdv`, `prfAdv_toOracleAdversary`, `OracleEnsemble.Indist`/`indist_iff`, `OracleEnsemble.keyed`/`random`, `acceptProb_random_eq(_lazy)`, `oracle_hybrid_lemma`, `NUPPT.toOracleAdversary(_eq/_boundedBy)`, `buildTree_*`, `decodeOracleMove_*` | `Pseudorandom/Functions/Asymptotic/Defs.lean` |
| Lazy random-function sampling (`evalLazy_*`, `uprob_evalLazy`, `lazyDist_apply`) | `Pseudorandom/Functions/LazySampling.lean` |
| `Games.exists_interactiveHandlerMachine` (T2), `Games.exists_toOracleAdversary_of_bitCodec` (T4), `exists_toCompOn_of_toComp` and the handler readers | `Games/Efficiency.lean` |
| `identical_until_bad`, `prob_eq_until_bad`, `prob_mem_le`, `abs_prob_sub_le_of_agree`, `simulate_allOutputs_bad` | `Games/Hopping.lean` |
| `indImpl_enc/_dec/_challenge_none/_challenge_repeat/_dec_cpa`, `decOpen_cpa/_cca1`, `encryptAt_eq`, `decAnswer_*`, `splitHalf_*`, `indCodec_*`, `indGame_eq`, `INDSecure_iff`, and the specification-typed readers from #289 (`indSpec_decDom/_decRng/_challengeDom/_challengeRng`, `indImpl_dec_onSpec`, `indImpl_challenge_none_onSpec`) | `PrivateKey/OracleSecurity.lean` |
| `prfScheme_gen/_enc/_dec`, `runAt_prfEnc`, `runAt_prfDec`, `decodeFin_runAt_prfDec_of_not_wf`, `polyTimeComputable_prfEncFun/_prfDecFun` | `PrivateKey/FromPRF.lean` |
| `prfFixedScheme_gen/_enc/_dec`, the private helpers of the not-CCA2 proof (reusable patterns) | `PrivateKey/OracleFromPRF.lean` (owned) |
| `Negligible.*`, `Negligible.polyExpr_mul`, probability readers, `simulate`/`OracleComp` laws, `NUPPT` run/coin/closure lemmas | `Foundations/Negligible.lean`, `Asymptotic/ReductionSupport.lean`, `Games/*`, `Complexity/Randomized/*` |
| The adaptive and CPA-pilot proofs (`PublicKey/AdaptiveCPA/`, `PublicKey/BitwiseCPA/`, `PublicKey/OracleSecurity/ChallengeSim`) | worked models of T2 handlers, eager coins and cast transport; reuse their public lemmas where their contracts apply |

## Authorized reader additions

In `TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean`, beside the existing `_onSpec` readers and in
the same form, you may add:
- `indSpec_encDom`, `indSpec_encRng`;
- `indImpl_enc_onSpec`;
- `indImpl_challenge_repeat_onSpec`.

Each must be public, not `@[simp]`, and carry a docstring with its formula. Add only those you use, and change
nothing else in that file.

## Proof route and checkpoints

The docstring sketches give the route. The CCA1 proof extends the CPA proof.

1. **PRF → random function.** Build the reduction `D` as an oracle machine for `OracleEnsemble.Indist`.
   - Use T2 and the input-free companion, then T4, as the CPA sketch says. `D` answers the game's `Enc` and
     challenge queries by querying its own function oracle at a fresh `r`. For CCA1 it also answers decryption
     queries before the challenge (`runAt_prfDec`; `⊥` on malformed queries by
     `decodeFin_runAt_prfDec_of_not_wf`).
   - The challenge bit `b` goes in the seed, and the finalization compares the guess with `b`.
   - Show: the game with `f_k` equals `D` against the keyed ensemble, and the game with a random function equals
     `D` against the random ensemble.

   Send checkpoint 1.
2. **The random-function game.**
   - Define the bad event: the challenge's `r*` collides with the `r` of an earlier `Enc` answer, a later one,
     or (CCA1) a pre-challenge decryption query.
   - Bound its probability by `q(n)/2^n` with `prob_mem_le`: one fresh uniform draw against at most `q` others.
   - Off the bad event, `m_b ⊕ RF(r*)` is uniform for both `b` (lazy sampling, `identical_until_bad`).

   Send checkpoint 2.
3. **The bound.** `A`'s advantage is at most `2 · prfAdv + q(n)/2^n`, or the exact form you prove. Both terms are
   negligible: the first by `PRF.negligible_prfAdv` at the reduction's polynomial budget, the second by the
   `Negligible` API. Close both targets.

   Send the final delivery.

Check the edge cases: budget 0; `n = 0` (the advantage is trivially bounded, or the collision bound is ≥ 1); no
challenge; repeated challenges; `Dec` on the challenge or on malformed strings; and the timeout output.

## Scope and proof discipline

- **Owned file.** Own `OracleFromPRF.lean`: replace the two proof bodies and add helpers there.
- **Helper modules.** Generic helper modules are permitted under `TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/`.
  The owned file imports them precisely, and its module docstring gets a `## Contents` list if it becomes a facade.
- **Size.** Keep every file below 1000 lines (the owned file is 579 now).
- **Frozen.** Do not edit any other file except the authorized readers. If a lemma belongs in an existing file,
  put it in your helper module and list it in `REPORT.md` as a promotion request.
- **Duplication.** Generic probability, simulation or list facts go on the promotion list (duplication ledger
  DL-30 to DL-33 in `briefs/pass-shelat-ch5-8/duplication-ledger.md`). Grep first and reuse existing lemmas; the
  four CPA-pilot fills left many candidates.
- **Statements.** You may edit the targets' sketches to describe the delivered proofs. Preserve the statements,
  every other declaration (including `prfFixedScheme_not_cca2` and `not_prfFixedScheme_cca2`), the statement
  prose and the global simp attributes. Update the module docstring's status lines for the two targets.
- **Docstrings.** Public helpers get docstrings with their formulas, and proof sketches when nontrivial
  (policy §3). Lemma docstrings must state the formula, not just "the defining equation of …".
- **Rule 10.** Use only published readers for other files' definitions, including generated matchers and
  projections.
- **Escalation.** If a target appears false, or a required reader is missing with no clean route, record the
  exact failing obligation and the smallest proposed correction in `REPORT.md`, then push a checkpoint.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` and the narrow `roots.txt` per the addendum. Check one module per
  `scripts/lean_check_tree.sh` call, with one Lean process per olean tree. Insert helper modules before their
  consumers, and recalculate roots if imports change.
- **Sweep.** Recheck the owned modules, then sweep the supplied order. Compare `sorry` warnings with
  `base-sorries.txt`: the only change must be the removal of `prfFixedScheme_cpa` and `prfFixedScheme_cca1`.
- **Axioms.** Print the axioms of both targets. Expect only `propext`, `Classical.choice` and `Quot.sound`.
- **Rule 10 evidence.**
  - Run whole-file seals of every changed or new file over its full TCSlib import closure, with controls that
    pass unsealed and fail sealed.
  - Run the explicit-unfold scan.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PrivateKey --check8b`.
- **Report.** Give the base, both targets' status, the changed files and sketch edits, the new declarations, any
  promotion or reader requests, and the evidence.

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/duplication-ledger.md =====

# Duplication ledger: Pass–shelat ch. 5–8

Accepted debt, each entry acknowledged by the user, with its scheduled resolution.

| ID | New declaration (where) | Existing copy (where) | Status | Resolution |
|---|---|---|---|---|
| DL-1 | `TCSlib.InformationTheory.abs_probTrue_sub_le_statDist` (#183, `InformationTheory/Extractors.lean`, for `main`) | `TCSlib.Cryptography.abs_sum_sub_le_statDist` (`Foundations/Experiments.lean`, Garg's concrete layer, on `cryptography/pass-shelat-ch2-4` and `cryptography/garg-ch1-3`; not on `main`) | accepted 2026-11-04 (user) | No copy on `main` today. When the concrete layer lands on `main`, its lemma becomes a one-line corollary of #183's (a `Finset` test is the `Bool` test `(· ∈ T)`) or is removed. Gate 01 pack erratum E1. |

## Inherited with ch. 2–4 (found 2026-11-05; acknowledged 2026-11-05 by the user: clean up now)

This campaign owns ch. 2–4 since 2026-11-05 (plan, decision log). These duplicates predate it.

| ID | Copies (where) | Status | Proposed resolution |
|---|---|---|---|
| DL-2 | XOR of encodings is the encoding of the Boolean sum, `zipWith xor (ofFn a) (ofFn b) = ofFn (a + b)`, stated three times: `TCSlib.Cryptography.zipWith_xor_ofFn_add` (`Asymptotic/HardCoreLoops.lean`; it was `zipWith_xor_ofFn`, renamed by the base repair to end the name clash with `Encryption.lean`'s different lemma); `TCSlib.Cryptography.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessage.lean`); `TCSlib.Cryptography.MultiMsg.zipWith_xor_ofFn_eq_add` (`Asymptotic/MultiMessageLemmas.lean`) | accepted; scheduled now | Keep the most upstream copy (`HardCoreLoops`) and point the other two at it, in a ch. 2–4 cleanup PR. |
| DL-3 | `pairEncode a b ≠ []`, stated four times: `GGMRed.pairEncode_ne_nil` (`Asymptotic/GGMReduction.lean`), `GI.pairEncode_ne_nil` (`ZeroKnowledge/GraphIsomorphism/Proofs.lean`), `ColMachines.pairEncode_ne_nil` (`ZeroKnowledge/ThreeColoring/Machines.lean`); and, on `main`, `Complexity.pairEncode_ne_nil` (`Complexity/SpaceComplexity/Logspace/InputAccess.lean`), the copy that made the merge's ambiguity | accepted; scheduled now | `main` is merged (#186). Remove the three local copies in favour of `Complexity.pairEncode_ne_nil`, in the same cleanup PR. |
| DL-4 | Not a copy (different carriers): the sampler-based `StatClose` (`Asymptotic/Sampling.lean`) and `main`'s `EpsClose` on `FinDist` (`InformationTheory/Extractors.lean`, #183) | accepted; scheduled now | A bridge lemma, in the same cleanup PR (user, 2026-11-05). |
| DL-5 | Not a copy (different carriers; found by the gate 02 round 2 review): `Games.guessAdv_eq_half_advantage` and `Games.accept_guessGame` (games) and the concrete layer's `predict_eq` (`Asymptotic/Ensembles.lean`, on `uprob` over seed spaces), both the identity behind [PS10, Lemma 73.8] | disclosed in the docstring (gate 02 closing commit) | Derive one from the other through bridge B2 when ch. 2–4 lands on `main`. |

## Found in the ch. 5–8 statement phase (2026-11-05)

| # | Statement | Copies | Status | Resolution |
|---|---|---|---|---|
| DL-6 | Coin-tape slices `(r.drop (j * c)).take c` in global/GI-shadow graph isomorphism, Lamport and sequential ZK, alongside the former BlockEncryptor home | historical duplicates found by the Lamport worker/maintainer | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | One `TCSlib.Cryptography.coinBlock`, `coinBlock_eq` and `length_coinBlock` live in `Asymptotic/Adversary.lean`. The BlockEncryptor definition moved upstream; global/shadow `coinSlice` and sequential ZK's `phaseSlice`/unused length lemma are retired. Lamport already used the public BlockEncryptor `coinBlock`; its length lemma moved upstream. Consumers use the shared name and published reader. |
| DL-7 | Equal-length padding: Lamport's `ofFn_padFin_of_length`, and the inline step in `Composability.length_eval_of_length` (`CCA2Scheme.lean`) | General equation `Collection.ofFn_padFin_of_le` in **`Asymptotic/CollectionsHelpers.lean`**, not `Collections.lean` | **Implemented at `e9d64158461bfe24ddc88ab885bc4017899b4c16`; final source `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` is checked in draft PR #232. Native and layered Rule10 reconciliation identify zero new/touched reads; all older failures remain recorded. External gates and landing pending.** | Lamport's duplicate theorem is deleted. Its uses and CCA2's two padding steps use the general equation, whose conclusion is `List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false`; at `w.length = ℓ`, simplify `Nat.sub_self`, `List.replicate_zero` and `List.append_nil`. |
| DL-8 | `SecureComputation.PRFOut ℓ₂` (prong B, `SpecialEncryptionSecurity.lean`): ch. 2–4's `PRF` with `ℓ₂(n)`-bit outputs; `PRF` is its case `ℓ₂ = n` | resolved 2026-11-05 | `prfOut_var_iff : PRFOut .var F ↔ PRF F` proved beside `PRFOut` (prong B). The ch. 2–4 layer is unchanged. |


## Found by gate 03 (2026-11-05; rulings G3-5 and R-03l-1: clean up in the gate 03 clean-up PR, after #195)

Most copies trace to helpers that are `private` in pack 03a's and 03l's files. The clean-up makes
one copy public in the most upstream file and re-points the rest.

| Id | Copies | Status | Payback |
|---|---|---|---|
| DL-9 | The coin-block bijection `blocks` (`Fin (m · c) → Bool ≃ Fin m → Fin c → Bool`) and its lemmas, copies and an inverse: `FunFamily.blocks`, `OneWayYao.blocksE`, `blocksEquiv`, `blocksEquivX`, `EnsembleLemmas.blocks`, `SoundnessRep.blocksEquiv`, and `Ensemble.blocks` (private, `Asymptotic/Ensembles.lean`, which calls itself a copy of `FunFamily.blocks`; added on gate 03a round 2, R2-4); with S2b's public duplicate `take_drop_ofFn_blocks` of `EnsembleLemmas.take_drop_ofFn_blocks` (gate 04 N4) | accepted; scheduled (G3-5) | One `FunFamily.blocks` in a low file; re-point 03h, 03i, 03k's statements, `Ensembles.lean` (03a) and S2b's copy. |
| DL-10 | `ptc_comp` (composition of polynomial-time functions in a convenient form), six private or public copies (`Closure`/`Repetition` helpers, `Universal*`, `ThreeColoring/Machines`, …) | accepted; scheduled (G3-5) | Public once in 03a's `Closure.lean`; delete the copies. |
| DL-11 | The state loop `stateFind` (private in `Repetition.lean`) and its copies `GI.stateFind`, `EncodingMachines.polyTimeComputable_stateFind`, `GGMRed.stateLoopFun`, and the variant `stateIterate` | accepted; **half done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`polyTimeComputable_stateFind` public, prose fixed); the copies are re-pointed in clean-up part 2 | `polyTimeComputable_stateFind` public in `Repetition.lean`; re-point; update the prose that calls it private (`StringLoops.lean:36–38`, `HardCoreLoops.lean:68`). |
| DL-12 | `abs_uexp_sub_le`, two copies (`PublicKeyLemmas` and a private one) | accepted; scheduled (G3-5) | One public copy. |
| DL-13 | `negligible_zero` (`Foundations/Negligible.lean` since G3-7a) and `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) | accepted; scheduled (G3-5) | Delete `negligible_const_zero` (2 uses). |
| DL-14 | `forall_of_uprob_eq_one`, two copies | accepted; scheduled (G3-5) | One public copy. |
| DL-15 | `decodeFin_eq_some_iff`, a private copy in `Collections.lean` and a public one in `GGMReductionEval.lean` (`GGMRed.decodeFin_eq_some_iff`; making the `Collections.lean` copy public must avoid the namespace clash, gate 03b review #12c), and the new forward lemma `ofFn_of_decodeFin_eq_some` (`CollectionsHelpers.lean`, #198); S2b's private `eq_ofFn_of_decodeFin` | accepted; scheduled (G3-5) | One public `decodeFin_eq_some_iff` in `Asymptotic/Adversary.lean`; the forward lemma derived from it. |
| DL-16 | `IterateFindHost` (03l) copies 26 declarations of `main`'s private module layer in `Complexity/ClassNP/SAT.lean` (ten now public); the new host is missing from the policy's host registry (§14) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)**: one public host `Turing.ModuleHost` (`TuringMachine/Build/ModuleHost.lean`), consumed by `SAT.lean` and `IterateFindHost.lean`; registry row H14 | Make `SAT.lean`'s layer public on the ch. 2–4 branch and re-point `IterateFindHost`; register the host. |
| DL-17 | `StateLoop` (03l) restates five `main` lemmas, plus `tail_poly` and `xor_poly` (arrived with the `main` merge, #186) | accepted; scheduled (R-03l-1) | Use `main`'s lemmas. |
| DL-18 | `UnaryMul` (03l) privately copies `PairSplit`'s parser | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (`Turing.PairParse` in `PairSplit.lean`) | Use `PairSplit`'s. |
| DL-19 | Not a copy yet: a latent name clash between `StateLoop.BlockLoop` and `main`'s `Complexity.BlockLoop` (nothing uses it) | **done in [#203](https://github.com/Shilun-Allan-Li/tcslib/pull/203)** (renamed `StateLoop.BlockMapLoop`) | Rename or merge in the same PR. |
| DL-20 | `main`'s `TuringMachine/Build/Loop.lean` keeps a private `loop_first_halt`, the same lemma as the new public `Turing.ModuleHost.first_halt` (found by #203's worker). `Loop.lean` is upstream of the host, so it cannot consume it | noted | Move `first_halt` and `live_prefix` down into `Loop.lean` (or the machine core) at the `main` landing, and have `Loop.lean` use them. |
| DL-21 | Elementary number theory that Mathlib already has (audit `mathlib-overlap-nt.md`, 2026-11-06, Mathlib pin `029db123`): 6 DUP (`QR` = `(powMonoidHom 2).range`, `crtUnits` (keep as alias, `rfl`), `coprime_of_ne` = `(Nat.coprime_primes hp hq).2`, `powOneSubgroup` = `(powMonoidHom m).ker`, `rsaPerm` ≈ `powCoprime` (optional), `IsGenerator` ≈ `∀ x, x ∈ zpowers g`) and 9 WRAP (shorter proofs from Mathlib: `units_val_mem`, `pow_mod_totient_modEq`, `units_pow_eq_one_iff`, `two_mul_card_le_of_ne_top`, `card_units_eq_mul_card_QR`, `card_QR_prime`, `sq_pow_div_four_succ`, `fmultNat_eq_mul_prime`; and the core of the sorried `elGamal_correct`) | accepted; scheduled (user direction 2026-11-06: Mathlib first) | Replace by Mathlib's (alias where a name is load-bearing), clean-up part 2 item M; rows in fill-owned files (`Candidates/*`) after those fills land, as landing edits. The fill briefs cite the report's Mathlib names. |
| DL-22 | TCSlib's Chebyshev lower bound (`NumberTheory/Chebyshev.lean`) and Korselt-type facts are in newer Mathlib (`Chebyshev.pi_ge`, `theta_ge`, `psi_ge`; `Nat.isCarmichael_iff_korselt`; master `94f43000`, Lean v4.36.0-rc2), not at our pin | noted | Replace at the next Mathlib bump (repository-wide, `main`'s pin). At the same bump, the hypothesis `BlumDensity` (`Rabin.lean`) can be discharged in its eventual form (`n ≥ n₀`): apply `WienerIkehara.tendsto_sum_range_div` (master only) to `vonMangoldt.residueClass 3` mod 4, with the continuation `vonMangoldt.continuousOn_LFunctionResidueClassAux` (already at our pin) and Chebyshev's `ψ(x) ≪ x` (master), to get `ψ(x; 4, 3) ~ x/2`; then `θ ≥ ψ − (ψ − θ)` (`Chebyshev.psi_sub_theta_le_mul_sqrt`) and `π(x; 4, 3) ≥ θ(x; 4, 3)/log x`. This changes the Rabin statements that take `BlumDensity` (they would take nothing, or `n ≥ n₀`); a statement gate then. |
| DL-23 | fac fill (`Candidates/Factoring.lean`, delivery review 2026-11-07): private near-copies of public lemmas: `fac_chunkEquiv` = `FunFamily.blocks`; `fac_arrowCongr` = `finCastEquiv`; `fac_ofFn_halves` repeats a private `OneWay` lemma (half is `ofFn_block_eq_take_drop`); `fac_listToNat_inj` repeats a private `Sampling` lemma; plus the REPORT's three near-duplicates and small numeral facts re-proved across the fac, rsa and dl-a fills | noted | Clean-up part 2: re-point to the public lemmas; publish the two private ones beside their files and share the numeral facts. |
| DL-24 | col-b fill (delivery review 2026-11-07): `ColZK.acceptProb_seed_to_coins` = `acceptProb_bind` reversed and `ColZK.findSome?_map_option` = core `List.map_findSome?` (removed by landing edits E3–E4); a third copy of `pushesUniform_restrict` across fill units (dl-a has one); `table_index_*` vs `finProdFinEquiv`; `polyTimeComputable_next` repeats `reply_poly`'s proof (review finding 6 has the full list) | E3–E4 at landing; rest noted | Clean-up part 2: publish one `pushesUniform_restrict`, re-point the rest. |
| DL-25 | dl-b fill (`DiscreteLogHardcore.lean`, delivery review 2026-11-07): `dlb_statClose_pi` copies the public `OneWay.statClose_pi` (removed by landing edit E1); `dlb_stateIterate_poly` (from `HardCoreLoops`), `dlb_count_ofFn` (from `HardCoreGL`; relative of `List.count_ofFn`), the `listToNat` fold lemmas, `two_pow_size_le` (dl-a and 3-col have inline `2^size m ≤ 2m` bounds), `pushesUniform_castLE` copies (review D1) | E1 at landing; rest noted | Clean-up part 2: publish one copy of each beside its source; missing equations `HardcoreBit.majority_eq` (`PairwiseIndependence.lean`) and `expSampler_coins` (`DiscreteLog.lean`) at the next shared-file window. |
| DL-26 | col-a fill (delivery review 2026-11-07): `colRep_xor_poly` = `StateLoop.xor_poly`, `eq_of_xor_eq_false` = core `bne_eq_false_iff_eq`, `pushesUniform_blockRead` rebuilds `FunFamily.blocks` (removed by landing edits E2–E4); `ColRep.exec_four_mul`'s step repeats `GI.exec_repViews`'s proof (promote `exec_four_mul`, request R-3); cross-unit near-copies with col-b's `ColZK.pushesUniform_offsetTable`, `ColZK.ofFn_drop_take` | E2–E4 at landing; rest noted | Clean-up part 2: promote `exec_four_mul`, share the col-a/col-b helpers; requests R-2 (`(decGraph x).1` equation), R-5 endorsed. Base reading for #210's next round: `R3COL_witnessRelation`'s `bounded` clause destructures `R3COL` instead of using `R3COL_iff`. |
| DL-27 | rsa fill (delivery review 2026-11-07): 151 lines copied verbatim from dl-a's private helpers (`dla_findSome?_ite`, `dla_find?_range_lt`, `dla_listToNat_append`, `dla_drop_natToList_zero_append`, `dla_ss*`); `rsa_appendEquiv` = Mathlib `Fin.appendEquiv` (landing edit E1); `rsa_comp`/`ptc_congr` copies of the private `ptc_comp` family; loop lemmas descend from Primality's private `spStep`; near-copies of `findSome?_eq_bind_find?`, `find?_range_eq_map_find?_finRange`; parallels with fac (`fac_natToList_mod`, `fac_pairDec`) | E1 at landing; shared-lemma PR planned | **Landing order:** (1) dl-a lands; (2) a shared-lemma PR publishes `PolyTimeComputable.comp'`/`.congr` (`PolyTime.lean`), `IterateFind.find?_range_and_lt` (`IterateFind.lean`), nine `listToNat`/`natToList` lemmas (`Arithmetic.lean`), `rejectBlocksL_eq_find?` (`Concrete.lean`), removing dl-a's copies; (3) rsa lands with E1–E3 and E4 (cites them; checked against stubs); (4) a statement-gated `polyTimeComputable_rejectBlocksL` retires the copied loops in dl-a, rsa, rabin (and dl-c, pending its review). |
| DL-28 | dl-c fill (delivery review 2026-11-07): near-verbatim copies of the trial loop and numeral helpers shared with dl-a and rsa (and dl-b's own modular-numeral layer); `dlc_abs_uexp_sub_le` duplicates `Sampling.lean`'s private lemma and its public copy in `PublicKeyLemmas.lean` (review D1) | noted | Folds into DL-27's shared-lemma PR. The review's D2 homes: generic `polyTimeComputable_rejectBlocksL` (`Concrete.lean`), `listToNat` lemmas, width lemmas (`Arithmetic.lean`), `find?_range` (`Repetition.lean`), `PolyTimeComputable.congr` (`PolyTime.lean`), `abs_uexp_sub_le` public in `Sampling.lean`, `finCastEquiv` to `CollectionsHelpers.lean`. Reconcile with DL-27's homes when that PR is drafted. |
| DL-29 | rabin fill (delivery review 2026-11-07): `rabin_appendEquiv` = Mathlib `Fin.appendEquiv` and `rabin_pushesUniform_prod` (re-proved from `PushesUniform.prodMap`) handled by landing edits E1–E2; undisclosed copies: `rabin_statClose_one` = dl-a's `dla_statClose_one`; `rabin_listToNat_mulStr`, `rabin_prime_poly` copy rsa helpers; `rabin_rS`/`_rQ`/`_rTest` ≈ rsa's `rsa_fS`/`_fQ`/`_fTest`; the block loop is a fourth copy (with dl-a, rsa, dl-c `dlc_ss*`); `rabin_drop_zeros_append`'s step = fac's `fac_natToList_mod` | E1–E2 at landing; rest noted | Folds into DL-27/DL-28's shared-lemma PR and the `polyTimeComputable_rejectBlocksL` host PR. Base reads `rabinCollection_index`, `rabinBlumTrapdoor_index` (through `show`; re-point via `Collection.index_eq`) go to clean-up part 2's (b) list. |
| DL-30 | padded-cpa fill (delivery review 2026-11-11): generic `ProbComp` facts published in a public-key helper as `Composability.ChallengeSim.expect_sample_equiv`, `expect_sample_comm`, `expect_sample_unique`, `expect_sub` (`PublicKey/OracleSecurity/ChallengeSim.lean`); `expect_sample_prod` repeated `Bridge.expect_sample_pair`'s proof. | `ChallengeSim.lean` only | Open (deferred) | Landing edit re-proved `expect_sample_prod` from `Bridge.expect_sample_pair`. Promote the four lemmas to `ProbComp` in `Games/Probability.lean` and re-point their uses. |
| DL-31 | `ofFn_padFin_of_length` (`List.ofFn (padFin d w) = w` when `w.length = d`): `GGMRed.ofFn_padFin_of_length` (`GGM/Run.lean`), copy in `Asymptotic/HardCoreGLColl.lean`, private copy in `ElGamal.lean`; padded-cpa's `RecordHandler.lean` uses the GGM one through a transitive import. | 3 | Open (deferred) | Promote one public lemma beside `padFin` in `Asymptotic/Adversary.lean`; re-point all uses and delete the copies. |
| DL-32 | `List.ofFn (cast h f) = List.ofFn f` for a width equality: public `Composability.AdaptiveCPA.ofFn_cast` (`PublicKey/AdaptiveCPA/Games.lean`) and private `cca2OfFn_cast` (`PrivateKey/OracleFromPRF.lean`, #289). adaptive-cpa review also lists for promotion: `expect_sample_update` (→ `Games/Probability.lean`, with DL-30), `simulate_eq_of_abs` and the `castImpl` family (→ `Games/Simulate.lean`), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length` join DL-31. | 2 (+ candidates) | Open (deferred) | Promote one generic `ofFn_cast` beside `padFin`/`BitCodec`; re-point both; promote the listed generic lemmas. |
| DL-33 | bitwise-cpa fill (delivery review 2026-11-11): `BitwiseSim.expect_sample_update` vs `AdaptiveCPA.expect_sample_update` (two forms, same name); generic `BitwiseSim.expect_simulate_eager` and public near-copy `BitwiseSim.expect_simulate_indImpl_cpa` of the private lemma in `PublicKey/OracleSecurity.lean`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport`; `BitwiseSim.headD_drop` = public `CommitmentLemmas.headD_drop` (and private `headD_drop_ofFn` in `Pseudorandom/NextBit.lean`); `flatten_ofFn_singleton` = private `flatten_ofFn_one` (`Yao.lean`); `decodeFin_nil_getD` (→ `Games/BitCodec`); `padded_enc_runAt/_coins` (→ beside the padded readers); `qDin/qDout` third copy of the two-oracle length vector (`recDin/recDout`, `acDin/acDout`); private `ofFn_half`, `bitwise_runAtL` re-prove published facts; reader request `HybridMachine.hybridPre_eq`. | several | Open (deferred) | One consolidation PR with DL-30–DL-32: promote to `Games/Probability`, `Games/Simulate`, `ChallengeSim`, `BitCodec`, a shared list module; re-point and delete copies. |
| DL-34 | pk-cpa-cca1 fill (delivery review 2026-11-12): `OracleFromPRF/Handler.lean` copies private AdaptiveCPA handler pieces (`ofFn_padFin_eq_padL`, round-input readers `rU`…`rCnt`, `impl_of_ret`, `replicate_one`); public `ofFn_pkTapes` re-proves `AdaptiveCPA.ofFn_acTapes` (a generic `⟦blocks q ℓ ω j⟧ = (⟦ω⟧.drop (j·ℓ)).take ℓ` belongs beside `FunFamily.blocks`, input-layout readers beside `InteractiveHandler.input`); private-key `indCodec_eq_bitCodec` (DL-32 reader request); `mem_keys_of_lookup_isSome` (core `List.lookup_isSome_iff`); promotion candidates `simulate_eq_of_abs_bounded` (generalizes `AdaptiveCPA.simulate_eq_of_abs`), `expect_simulate_congr` (→ `Games/Simulate`), `abs_expect_sub_le` (→ `Games/Probability`), `prob_bad_le`, `expect_sample_mem_le` (→ `Games/Hopping`), `padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr` (→ beside `padFin`), `zipWith_xor_cancel_left`, `xorPerm` (shared list/vector module); owned-file private overlaps with the `cca2*` helpers. | several | Open (deferred) | Fold into the DL-30–DL-34 consolidation PR. |

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Transfer
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Lazy
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Collision
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The §3.9 scheme under chosen-plaintext and chosen-ciphertext attacks

[PS10, Theorem 168.2]: the scheme of Algorithm 99.1 (the ch. 2–4 layer's `prfScheme`:
`Enc_k(m) = ⟨r, m ⊕ f_k(r)⟩` for a fresh uniform `r`) is CPA- and CCA1-secure when `F` is a PRF.
[PS10, §7.1.3, Claim 169.a in the inventory]: it is not CCA2-secure, whatever `F`.

The CCA1 statement relies on `Dec` refusing malformed ciphertexts (`prfDecWF`): the evaluator `E`
agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`, and a decryption query must not reach it
elsewhere.

## Main definitions

* `Composability.prfFixedScheme`: `prfScheme`, whose ciphertexts have `3n + 2` bits.

## Main results

* `Composability.prfFixedScheme_cpa`, `Composability.prfFixedScheme_cca1` (Thm 168.2, proved): the
  advantage is at most `prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) / 2ⁿ`.
* `Composability.prfFixedScheme_not_cca2` (Claim 169.a, proved): an explicit adversary with
  advantage `1`.
* `Composability.not_prfFixedScheme_cca2`: hence the scheme is not CCA2-secure (proved from the
  claim).

## Contents

The proof of Thm 168.2 uses the helper modules under `OracleFromPRF/`:

* `OracleFromPRF.Games`: the IND experiment with a pad function (`PRFGame.fImpl`), and with
  nonce tapes in advance (`eImpl`).
* `OracleFromPRF.Handler`: the reduction's T2 handler (`PRFGame.pkHandler`).
* `OracleFromPRF.Reduction`: the PRF reduction (`PRFGame.exists_prfReduction`).
* `OracleFromPRF.Transfer`: the scheme's oracles as the pad-function experiment.
* `OracleFromPRF.Lazy`: the lazily sampled random function (`PRFGame.expect_lazyImpl`).
* `OracleFromPRF.Collision`: identical until bad and the bad event's bound
  (`PRFGame.abs_expect_fImpl_sub_le`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 99.1, Theorem 168.2 and §7.1.3 (book pp. 99, 168–169; the theorem calls the algorithm
  "construction 99.1").
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (E : List Bool → List Bool) (hE : PolyTimeComputable E)
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))

/-- **The §3.9 scheme with fixed-length ciphertexts**: `⟨r, m ⊕ f_k(r)⟩` with `r` and `m` of `n`
bits has `2n + 2 + n = 3n + 2` bits. -/
noncomputable def prfFixedScheme : FixedLengthScheme where
  toPrivateKeyScheme := prfScheme F E hE hFE
  ctLen := .add (.mul (.const 3) .var) (.const 2)
  enc_length := by
    simp only [prfScheme_gen, prfScheme_enc]
    intro n rg m r
    have hlen : ∀ {f : List Bool → List Bool} (hf : PolyTimeComputable f),
        (NUPPT.ofPolyTimeUniform hf .var).coinLen n = n :=
      fun {f} hf => (NUPPT.coinLen_eq (NUPPT.ofPolyTimeUniform hf .var) n).trans
        ((congrArg (fun p : PolyExpr => p.eval n)
          (NUPPT.coins_ofPolyTimeUniform hf .var)).trans (PolyExpr.eval_var n))
    let k : Fin n → Bool := fun j =>
      rg (Fin.cast (hlen polyTimeComputable_pairSndD).symm j)
    let x : Fin n → Bool := fun j =>
      r (Fin.cast (hlen (polyTimeComputable_prfEncFun hE)).symm j)
    have hk : List.ofFn rg = List.ofFn k :=
      List.ofFn_congr (hlen polyTimeComputable_pairSndD) rg
    have hx : List.ofFn r = List.ofFn x :=
      List.ofFn_congr (hlen (polyTimeComputable_prfEncFun hE)) r
    rw [runAt_coinKey, runAt_prfEnc hE, hk, hx, hFE, length_pairEncode]
    simp only [List.length_zipWith, List.length_ofFn, Nat.min_self, PolyExpr.eval_add,
      PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega

attribute [simps (config := { isSimp := false }) toPrivateKeyScheme ctLen] prfFixedScheme

/-- The fixed-length scheme uses the key generator of `prfScheme`. -/
theorem prfFixedScheme_gen :
    (prfFixedScheme F E hE hFE).gen = (prfScheme F E hE hFE).gen :=
  congrArg PrivateKeyScheme.gen (prfFixedScheme_toPrivateKeyScheme F E hE hFE)

/-- The fixed-length scheme uses the encryption machine of `prfScheme`. -/
theorem prfFixedScheme_enc :
    (prfFixedScheme F E hE hFE).enc = (prfScheme F E hE hFE).enc :=
  congrArg PrivateKeyScheme.enc (prfFixedScheme_toPrivateKeyScheme F E hE hFE)

/-- The fixed-length scheme uses the decryption machine of `prfScheme`. -/
theorem prfFixedScheme_dec :
    (prfFixedScheme F E hE hFE).dec = (prfScheme F E hE hFE).dec :=
  congrArg PrivateKeyScheme.dec (prfFixedScheme_toPrivateKeyScheme F E hE hFE)

/-! ### Step 1: the game is the experiment with pad function `f_k` -/

section PRFStep

open PRFGame ChallengeSim ProbComp

/-- **The key generator outputs its coins:** `Gen(1^n; rg) = ⟦rg⟧` (`runAt_coinKey`). -/
private theorem prf_gen_runAt (n : ℕ) :
    ∀ rg : (prfFixedScheme F E hE hFE).gen.Coins n,
      (prfFixedScheme F E hE hFE).gen.runAt n [] rg = List.ofFn rg := by
  rw [prfFixedScheme_gen, prfScheme_gen]
  intro rg
  exact runAt_coinKey .var n rg

/-- The key coins as an `n`-bit key, keeping the string. -/
private noncomputable def prfKeyEq (n : ℕ) :
    (prfFixedScheme F E hE hFE).gen.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [prfFixedScheme_gen, prfScheme_gen]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- `⟦prfKeyEq n rg⟧ = ⟦rg⟧`. -/
private theorem ofFn_prfKeyEq (n : ℕ) (rg : (prfFixedScheme F E hE hFE).gen.Coins n) :
    List.ofFn (prfKeyEq F E hE hFE n rg) = List.ofFn rg := by
  rw [prfKeyEq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-- The encryption coins as an `n`-bit nonce, keeping the string. -/
private noncomputable def prfNonceEq (n : ℕ) :
    (prfFixedScheme F E hE hFE).enc.Coins n ≃ (Fin n → Bool) :=
  (NUPPT.coinsCongr (by rw [prfFixedScheme_enc, prfScheme_enc]) n).trans
    ((NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var n).trans
      (Equiv.arrowCongr (finCongr (PolyExpr.eval_var n)) (Equiv.refl Bool)))

/-- `⟦prfNonceEq n re⟧ = ⟦re⟧`. -/
private theorem ofFn_prfNonceEq (n : ℕ) (re : (prfFixedScheme F E hE hFE).enc.Coins n) :
    List.ofFn (prfNonceEq F E hE hFE n re) = List.ofFn re := by
  rw [prfNonceEq, Equiv.trans_apply, Equiv.trans_apply, ofFn_arrowCongr_finCongr,
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsCongr_ofFn]

/-- **Encryption with the key `k` and the coins `re`** is the ciphertext `⟨r, m ⊕ F_k(r)⟩` with the
nonce `r = prfNonceEq re` (`runAt_prfEnc`, `hFE`). -/
private theorem ofFn_prf_encryptAt (n : ℕ) (k m : Fin n → Bool)
    (re : (prfFixedScheme F E hE hFE).enc.Coins n) :
    List.ofFn ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m re) =
      ctOf (prfNonceEq F E hE hFE n re) (List.ofFn m)
        (F n k (prfNonceEq F E hE hFE n re)) := by
  have hx : List.ofFn re = List.ofFn (prfNonceEq F E hE hFE n re) :=
    (ofFn_prfNonceEq F E hE hFE n re).symm
  generalize prfNonceEq F E hE hFE n re = x at hx
  revert re
  simp only [FixedLengthScheme.encryptAt_eq, prfFixedScheme_ctLen]
  rw [prfFixedScheme_enc, prfScheme_enc]
  intro re hx
  rw [runAt_prfEnc hE, hx, hFE, ctOf_eq]
  apply GGMRed.ofFn_padFin_of_length
  simp only [length_pairEncode, List.length_ofFn, List.length_zipWith, Nat.min_self,
    PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- **Decryption with the key `k`**, for `n > 0`: on a well-formed `w = ⟨x, v⟩` the answer is
`⟨1, v ⊕ F_k(x)⟩`, and otherwise `⊥` (`runAt_prfDec`, `decodeFin_runAt_prfDec_of_not_wf`). -/
private theorem ofFn_prf_decAnswer (n : ℕ) (hn : 0 < n) (k : Fin n → Bool) (w : List Bool)
    (rd : (prfFixedScheme F E hE hFE).dec.Coins n) :
    List.ofFn (FixedLengthScheme.decAnswer (decodeFin n
        ((prfFixedScheme F E hE hFE).dec.runAt n (pairEncode (List.ofFn k) w) rd))) =
      if decWF n w then
        true :: List.zipWith xor (pairSndD w) (List.ofFn (F n k (padFin n (pairFstD w))))
      else List.replicate (n + 1) false := by
  revert rd
  rw [prfFixedScheme_dec, prfScheme_dec]
  intro rd
  by_cases hw : decWF n w = true
  · rw [if_pos hw]
    rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw
    have hne : pairFstD w ≠ [] := by
      intro h
      have := hw.1
      rw [h, List.length_nil] at this
      omega
    have hx : pairFstD w = List.ofFn (padFin n (pairFstD w)) :=
      (GGMRed.ofFn_padFin_of_length hw.1).symm
    have hv : List.zipWith xor (pairSndD w) (List.ofFn (F n k (padFin n (pairFstD w)))) =
        List.ofFn (padFin n (List.zipWith xor (pairSndD w)
          (List.ofFn (F n k (padFin n (pairFstD w)))))) :=
      (GGMRed.ofFn_padFin_of_length (by
        rw [List.length_zipWith, List.length_ofFn, hw.2, Nat.min_self])).symm
    conv_lhs => rw [eq_pairEncode_of_pairFstD_ne hne]
    rw [runAt_prfDec hE _ n _ _ _ hw.1 hw.2, hx, hFE, ← hx, hv, decodeFin_ofFn,
      FixedLengthScheme.decAnswer_some, List.ofFn_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
  · rw [if_neg hw, decodeFin_runAt_prfDec_of_not_wf hE _ n _ w (by
      rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw
      exact hw), FixedLengthScheme.decAnswer_none, ofFn_zeroBits]

/-- The scheme's ciphertexts have `ctP(n) = 3n + 2` bits. -/
private theorem prf_ctLen_eval (n : ℕ) :
    (prfFixedScheme F E hE hFE).ctLen.eval n = ctP.eval n := by
  rw [prfFixedScheme_ctLen, ctP_eval, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
    PolyExpr.eval_const, PolyExpr.eval_var]

/-- The scheme's query lengths are the reduction's: `inLens n = fun i => (pkDin i).eval n`. -/
private theorem prf_inLens (n : ℕ) :
    (prfFixedScheme F E hE hFE).inLens n = fun i => (pkDin i).eval n := by
  funext i
  match i with
  | 0 => rw [FixedLengthScheme.inLens_zero, pkDin_zero, PolyExpr.eval_var]
  | 1 => rw [FixedLengthScheme.inLens_one, pkDin_one, prf_ctLen_eval]
  | 2 => rw [FixedLengthScheme.inLens_two, pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var]

/-- The scheme's answer lengths are the reduction's: `outLens n = fun i => (pkDout i).eval n`. -/
private theorem prf_outLens (n : ℕ) :
    (prfFixedScheme F E hE hFE).outLens n = fun i => (pkDout i).eval n := by
  funext i
  match i with
  | 0 => rw [FixedLengthScheme.outLens_zero, pkDout_zero, prf_ctLen_eval]
  | 1 =>
    rw [FixedLengthScheme.outLens_one, pkDout_one, PolyExpr.eval_add, PolyExpr.eval_var,
      PolyExpr.eval_const]
  | 2 => rw [FixedLengthScheme.outLens_two, pkDout_two, prf_ctLen_eval]

/-- **The IND experiment of the scheme is the experiment with pad function `F_k`** (step 1,
`n > 0`, CPA or CCA1): `Pr[IND_b = 1] = 𝔼_k 𝔼_r Pr[A outputs 1 against fImpl … (F n k)]`, on the
reduction's lengths.

**Proof sketch.** The key generator outputs its uniform coins (`prf_gen_runAt`, `prfKeyEq`); for
every key, the oracles of `IND_b` and `fImpl … (F n k)` have the same laws call by call
(`expect_indImpl_fImpl`, from `ofFn_prf_encryptAt` and `ofFn_prf_decAnswer`), so the simulations
agree (`PRFGame.expect_simulate_congr`); the game's codec and lengths are the reduction's
(`indCodec_eq_bitCodec`, `prf_inLens`, `prf_outLens`, `prf_ctLen_eval`). -/
private theorem accept_prf_indGame (atkBit b : Bool) (A : NUPPT) (Q n : ℕ) (hn : 0 < n) :
    accept ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A Q b n) =
      expect (ProbComp.sample (Fin n → Bool)) fun k =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
              (ctP.eval n) n (atkOf atkBit) b (F n k))
              (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n Q r)
              none)
            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  have hct : (prfFixedScheme F E hE hFE).ctLen.eval n = 3 * n + 2 := by
    rw [prf_ctLen_eval, ctP_eval]
  rw [accept_eq, FixedLengthScheme.indGame_eq, prob_bind,
    ← expect_sample_equiv (prfKeyEq F E hE hFE n)]
  refine congrArg _ (funext fun rg => ?_)
  have hk : (prfFixedScheme F E hE hFE).gen.runAt n [] rg =
      List.ofFn (prfKeyEq F E hE hFE n rg) := by
    rw [prf_gen_runAt, ofFn_prfKeyEq]
  rw [hk, prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind]
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin ((prfFixedScheme F E hE hFE).ctLen.eval n) →
      Bool) => ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => if (List.ofFn res.1).headD false = true then (1 : ℝ) else 0 := by
    funext res
    rw [prob_pure, AdaptiveCPA.headD_ofFn_one]
  rw [h1, expect_simulate_congr _ _ (fun i x s g => expect_indImpl_fImpl _ atkBit b n _ _ hct
      (prfNonceEq F E hE hFE n) (fun m re => ofFn_prf_encryptAt F E hE hFE n _ m re)
      (fun w rd => ofFn_prf_decAnswer F E hE hFE n hn _ w rd) i x s g),
    indCodec_eq_bitCodec]
  exact expect_fImpl_transport (prf_inLens F E hE hFE n) (prf_outLens F E hE hFE n)
    (prf_ctLen_eval F E hE hFE n) n _ b _ A Q r

/-- **The reduction's PRF advantage is the gap between the experiments with `F_k` and with a
random function** (step 1): for the machine `D` of `exists_prfReduction` and `n > 0`,
`prfAdv (F n) D = |Pr[IND_b = 1] − 𝔼_R 𝔼_r Pr[A outputs 1 against fImpl … R]|`.

**Proof sketch.** `prfAdv_def`, `distAdv_def`; each acceptance probability is an average over the
key (resp. the function table) and `D`'s coins (`Bridge.acceptProb_eq`, `acceptGame_eq`,
`oracleDist_apply`, `randomFunction_apply`), which `D`'s defining property turns into the
experiment with that function; with the key it is the game (`accept_prf_indGame`). -/
private theorem prfAdv_prfReduction (atkBit b : Bool) (A : NUPPT) (q : PolyExpr) (D : NUPPT)
    (hD : ∀ (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)),
      expect (ProbComp.sample (D.Coins n))
          (fun c => if (D.toOracleAdversary n n n ((qRed q).eval n) c).eval f = true
            then (1 : ℝ) else 0) =
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
              (ctP.eval n) n (atkOf atkBit) b f)
              (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
                (q.eval n) r) none)
            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0))
    (n : ℕ) (hn : 0 < n) :
    prfAdv (F n) (D.toOracleAdversary n n n ((qRed q).eval n)) =
      |accept ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A (q.eval n) b n) -
        expect (ProbComp.sample ((Fin n → Bool) → (Fin n → Bool))) fun R =>
          expect (ProbComp.sample (A.Coins n)) fun r =>
            expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
                (ctP.eval n) n (atkOf atkBit) b R)
                (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
                  (q.eval n) r) none)
              (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)| := by
  rw [prfAdv_def, distAdv_def, accept_prf_indGame F E hE hFE atkBit b A _ n hn,
    Bridge.acceptProb_eq, Bridge.acceptProb_eq, accept_eq, accept_eq, Bridge.acceptGame_eq,
    Bridge.acceptGame_eq, prob_bind, prob_bind]
  congr 2
  · refine congrArg _ (funext fun k => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply]
    exact hD n (F n k)
  · refine congrArg _ (funext fun R => ?_)
    simp only [prob_bind, prob_pure, oracleDist_apply, randomFunction_apply]
    exact hD n R

/-- **The bound at each security parameter** (steps 1–3 of [PS10, Thm 168.2]): for CPA or CCA1
there are PRF distinguishers `D₀`, `D₁` (one per bit) with
`adv_n ≤ prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) / 2ⁿ`.

**Proof sketch.** `D_b` is `exists_prfReduction` for the bit `b`. For `n > 0`, the triangle
inequality through the experiments with a uniform random function: each game is within
`prfAdv(F_n, D_b)` of its random-function experiment (`prfAdv_prfReduction`), and the two
random-function experiments are within `q(n)² / 2ⁿ` (`PRFGame.abs_expect_fImpl_sub_le`; the
adversary makes at most `q(n)` queries, `NUPPT.toComp_costBoundedBy`). For `n = 0`, `adv ≤ 1`. -/
private theorem prf_advantage_le (atkBit : Bool) (A : NUPPT) (q : PolyExpr) :
    ∃ D₀ D₁ : NUPPT, ∀ n,
      advantage ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A (q.eval n) false n)
          ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A (q.eval n) true n) ≤
        prfAdv (F n) (D₀.toOracleAdversary n n n ((qRed q).eval n)) +
          prfAdv (F n) (D₁.toOracleAdversary n n n ((qRed q).eval n)) +
          ((((q.mul q).add (.const 1)).eval n : ℕ) : ℝ) * (2⁻¹ : ℝ) ^ n := by
  obtain ⟨D₀, hD₀⟩ := exists_prfReduction A q atkBit false
  obtain ⟨D₁, hD₁⟩ := exists_prfReduction A q atkBit true
  refine ⟨D₀, D₁, fun n => ?_⟩
  have hp : ∀ D : NUPPT, 0 ≤ prfAdv (F n) (D.toOracleAdversary n n n ((qRed q).eval n)) :=
    fun D => by rw [prfAdv_def, distAdv_def]; exact abs_nonneg _
  have hQ : ((((q.mul q).add (.const 1)).eval n : ℕ) : ℝ) * (2⁻¹ : ℝ) ^ n =
      ((q.eval n : ℝ) ^ 2 + 1) / 2 ^ n := by
    rw [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, inv_pow]
    push_cast
    ring
  have hQ1 : ((q.eval n : ℝ) ^ 2) / 2 ^ n ≤ ((q.eval n : ℝ) ^ 2 + 1) / 2 ^ n :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  rw [hQ]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : (1 : ℝ) ≤ ((q.eval 0 : ℝ) ^ 2 + 1) / 2 ^ 0 := by
      rw [pow_zero, div_one]
      nlinarith [sq_nonneg (q.eval 0 : ℝ)]
    linarith [advantage_le_one ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A (q.eval 0)
      false 0) ((prfFixedScheme F E hE hFE).indGame (atkOf atkBit) A (q.eval 0) true 0), hp D₀,
      hp D₁]
  · have key : ∀ a₀ a₁ X₀ X₁ K : ℝ, |X₀ - X₁| ≤ K → |a₀ - a₁| ≤ |a₀ - X₀| + |a₁ - X₁| + K :=
      fun a₀ a₁ X₀ X₁ K h => by
        have t1 := abs_sub_le a₀ X₀ a₁
        have t2 := abs_sub_le X₀ X₁ a₁
        rw [abs_sub_comm X₁ a₁] at t2
        linarith
    rw [advantage_eq, prfAdv_prfReduction F E hE hFE atkBit false A q D₀ hD₀ n hn,
      prfAdv_prfReduction F E hE hFE atkBit true A q D₁ hD₁ n hn]
    refine key _ _ _ _ _ (le_trans ?_ hQ1)
    exact abs_expect_fImpl_sub_le (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
      (ctP.eval n) n (atkOf atkBit) (by rw [decOpen_atkOf, Bool.not_true, Bool.and_false])
      (ctP_eval n)
      (by show (pkDin 2).eval n = n + n; rw [pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var])
      (fun r => A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
        (q.eval n) r) (fun a => (List.ofFn a).headD false = true) (q.eval n)
      (fun r => A.toComp_costBoundedBy _ n _ r)

/-- **Theorem 168.2 for CPA (`atkBit = false`) and CCA1 (`atkBit = true`).**

**Proof sketch.** `prf_advantage_le` bounds the advantage by
`prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) · 2⁻ⁿ`, which is negligible: both PRF advantages
are (`PRF.negligible_prfAdv`, budget `qRed q`), and so is a polynomial times `2⁻ⁿ`
(`EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg`); sums of negligible functions
are negligible (`Negligible.add`). -/
private theorem prf_indSecure (atkBit : Bool) (hF : PRF F) :
    (prfFixedScheme F E hE hFE).INDSecure (atkOf atkBit) := by
  rw [FixedLengthScheme.INDSecure_iff]
  intro A q
  obtain ⟨D₀, D₁, h⟩ := prf_advantage_le F E hE hFE atkBit A q
  exact ⟨_, ((hF.negligible_prfAdv D₀ (qRed q)).add (hF.negligible_prfAdv D₁ (qRed q))).add
    (EnsembleLemmas.negligible_polyExpr_mul _ negligible_two_pow_neg), h⟩

end PRFStep

/-- **Theorem 168.2 (CPA)** [PS10]: if `F` is a pseudorandom function family, the §3.9 scheme is
CPA-secure.

**Deviation:** the source's bound is `2 · prfAdv + q(n)/2ⁿ` with one reduction carrying the
challenge bit in its seed. Here there is one reduction per bit (the bit hard-wired) and the bound is
`prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) / 2ⁿ`: the bad event is bounded query by query
(at most `q` steps, each against at most `q` points), and the `+ 1` covers `n = 0`.

**Proof sketch.**
1. *PRF → random function* (`PRFGame.exists_prfReduction`, `prfAdv_prfReduction`): for each bit
   `b`, a reduction `D_b` built with T2 (`Games.exists_interactiveHandlerMachine`, the handler
   `PRFGame.pkHandler`), the input-free companion and T4
   (`Games.exists_toOracleAdversary_of_bitCodec`) answers `Enc` and the challenge by querying its
   function oracle at a fresh `r`. With `f_k` it accepts exactly when the IND experiment does;
   with a random function `R`, exactly when the experiment with pad `R` does. So each game is within
   `prfAdv(F_n, D_b)` of its random-function experiment.
2. *The random-function experiment* (`PRFGame.abs_expect_fImpl_sub_le`): sample `R` lazily
   (`PRFGame.expect_lazyImpl`). The bad event is that the challenge's `r*` was already asked or
   a later `Enc` uses it; a query raises it with probability at most `(q + 1) / 2ⁿ` (`prob_mem_le`),
   so it has probability at most `q(n)² / 2ⁿ` (`PRFGame.prob_bad_le`). Off the bad event,
   `m_b ⊕ R(r*)` is uniform for both `b` (identical until bad, `identical_until_bad`, with the pad
   changed by `y ↦ y ⊕ m₀ ⊕ m₁`).
3. *The bound* (`prf_advantage_le`, `prf_indSecure`): the triangle inequality gives the bound
   above (`advantage ≤ 1` at `n = 0`); it is negligible (`PRF.negligible_prfAdv`,
   `EnsembleLemmas.negligible_polyExpr_mul`, `negligible_two_pow_neg`). -/
theorem prfFixedScheme_cpa (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cpa := by
  rw [← PRFGame.atkOf_false]
  exact prf_indSecure F E hE hFE false hF

/-- **Theorem 168.2 (CCA1)** [PS10]: if `F` is a pseudorandom function family, the §3.9 scheme
is CCA1-secure.

**Deviation:** as for CPA, one reduction per bit and the bound
`prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1) / 2ⁿ`.

**Proof sketch.** As for CPA, with the reduction also answering decryption queries before the
challenge with its oracle (`Dec_k(⟨r, c⟩) = c ⊕ f_k(r)` on well-formed ciphertexts,
`PRFGame.pkHandler_impl_dec_open`; `⊥` on the others, `pkHandler_impl_dec_closed`; the scheme's
answers are matched by `runAt_prfDec` and `decodeFin_runAt_prfDec_of_not_wf`). In the lazy
experiment a pre-challenge decryption enters its nonce in the table, so the bad event adds the case
that it is the challenge's `r*`, again bounded by `prob_mem_le` because `r*` is drawn after those
queries; after the challenge CCA1 refuses decryption, so it never reads `b`. -/
theorem prfFixedScheme_cca1 (hF : PRF F) : (prfFixedScheme F E hE hFE).INDSecure .cca1 := by
  rw [← PRFGame.atkOf_true]
  exact prf_indSecure F E hE hFE true hF

/-- Reverse the word, negate its first bit, and reverse back: on a nonempty word this
flips exactly its last bit. -/
private def cca2FlipLast (w : List Bool) : List Bool :=
  ([!w.reverse.headD false] ++ w.reverse.drop 1).reverse

/-- Flipping the last bit is polynomial-time by reversal, head, tail and negation. -/
private theorem cca2FlipLast_poly : PolyTimeComputable cca2FlipLast := by
  exact (BinArith.polyTimeComputable_reverse.comp
    ((polyTimeComputable_not (polyTimeComputable_headD.comp
      BinArith.polyTimeComputable_reverse)).append
        (polyTimeComputable_tail.comp BinArith.polyTimeComputable_reverse)))

/-- On a word ending in `b`, the flip replaces that bit by `!b`. -/
private theorem cca2FlipLast_snoc (w : List Bool) (b : Bool) :
    cca2FlipLast (w ++ [b]) = w ++ [!b] := by
  simp only [cca2FlipLast, List.reverse_append, List.reverse_nil, List.nil_append,
    List.singleton_append, List.headD_cons, List.drop_succ_cons, List.drop_zero,
    List.reverse_cons, List.reverse_reverse]

/-- A nonempty suffix contains the last bit, so a prefix is unchanged by the flip. -/
private theorem cca2FlipLast_append (u v : List Bool) (hv : v ≠ []) :
    cca2FlipLast (u ++ v) = u ++ cca2FlipLast v := by
  rcases List.eq_nil_or_concat' v with h | ⟨v, b, rfl⟩
  · exact (hv h).elim
  · simp only [← List.append_assoc, cca2FlipLast_snoc]

/-- Flipping a nonempty ciphertext payload preserves the nonce and pairing delimiter. -/
private theorem cca2FlipLast_pair (u v : List Bool) (hv : v ≠ []) :
    cca2FlipLast (pairEncode u v) = pairEncode u (cca2FlipLast v) := by
  rw [pairEncode_eq, pairEncode_eq, cca2FlipLast_append _ v hv]

/-- The modified word has its original length whenever that word is nonempty. -/
private theorem cca2FlipLast_length (w : List Bool) (hw : w ≠ []) :
    (cca2FlipLast w).length = w.length := by
  rcases List.eq_nil_or_concat' w with h | ⟨w, b, rfl⟩
  · exact (hw h).elim
  · simp only [cca2FlipLast_snoc, List.length_append, List.length_singleton]

/-- The flipped word differs from the original at its last bit. -/
private theorem cca2FlipLast_ne (w : List Bool) (hw : w ≠ []) :
    cca2FlipLast w ≠ w := by
  rcases List.eq_nil_or_concat' w with h | ⟨w, b, rfl⟩
  · exact (hw h).elim
  · rw [cca2FlipLast_snoc]
    intro he
    have hb := congrArg (fun v : List Bool => v.getLastD false) he
    simp only [List.getLastD_concat] at hb
    cases b <;> cases hb

/-- Negate precisely the bit whose index is one less than the vector length. -/
private def cca2FlipBits {n : ℕ} (m : Fin n → Bool) : Fin n → Bool :=
  fun i => if i.val + 1 = n then !m i else m i

/-- The list and vector versions of the last-bit flip agree at positive lengths. -/
private theorem cca2FlipLast_ofFn {n : ℕ} (hn : 0 < n) (m : Fin n → Bool) :
    cca2FlipLast (List.ofFn m) = List.ofFn (cca2FlipBits m) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [List.ofFn_succ_last, cca2FlipLast_snoc, List.ofFn_succ_last]
    congr 1
    · apply congrArg List.ofFn
      funext i
      have hi : i.val + 1 ≠ n + 1 := by omega
      change m i.castSucc = if i.val + 1 = n + 1 then !m i.castSucc else m i.castSucc
      rw [if_neg hi]
    · change [!m (Fin.last n)] =
        [if n + 1 = n + 1 then !m (Fin.last n) else m (Fin.last n)]
      rw [if_pos rfl]

/-- Flipping one bit commutes with removing an exclusive-or pad. -/
private theorem cca2FlipBits_unmask {n : ℕ} (m p : Fin n → Bool) :
    cca2FlipBits (m + p) + p = cca2FlipBits m := by
  funext i
  change xor (if i.val + 1 = n then !(xor (m i) (p i)) else xor (m i) (p i)) (p i) =
    if i.val + 1 = n then !m i else m i
  split <;> cases m i <;> cases p i <;> rfl

/-- The attack's next activation asks the challenge, asks decryption of the modified
challenge, or negates the last bit of the second answer, according to the log. -/
private def cca2Next (z : List Bool) : List Bool :=
  let h := NUPPT.inArg z
  if h = [] then
    pairEncode [false] (pairEncode [true, true]
      (List.zipWith xor (NUPPT.inParam z) (NUPPT.inParam z) ++ NUPPT.inParam z))
  else if pairSndD h = [] then
    pairEncode [false] (pairEncode [true]
      (cca2FlipLast (pairSndD (pairSndD (pairFstD h)))))
  else pairEncode [true]
    [!(pairSndD (pairSndD (pairFstD (pairSndD h)))).getLastD false]

/-- The three activations are polynomial-time: projections, emptiness tests, pairing,
exclusive-or, the last-bit flip, and a last-bit test followed by negation. -/
private theorem cca2Next_poly : PolyTimeComputable cca2Next := by
  have ha := NUPPT.polyTimeComputable_inArg
  have hp := NUPPT.polyTimeComputable_inParam
  have ht := polyTimeComputable_pairSndD.comp ha
  have hz : PolyTimeComputable (fun z =>
      List.zipWith xor (NUPPT.inParam z) (NUPPT.inParam z)) :=
    (polyTimeComputable_pairXor.comp (hp.pairEncode hp)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hans : PolyTimeComputable (fun z => pairSndD (pairSndD (pairFstD z))) :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp ha)
    ((polyTimeComputable_const [false]).pairEncode
      ((polyTimeComputable_const [true, true]).pairEncode
        (hz.append hp)))
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp ht)
      ((polyTimeComputable_const [false]).pairEncode
        ((polyTimeComputable_const [true]).pairEncode
          (cca2FlipLast_poly.comp (hans.comp ha))))
      ((polyTimeComputable_const [true]).pairEncode
        (polyTimeComputable_not (BinArith.polyTimeComputable_lastBit.comp (hans.comp ht)))))
  exact h.congr fun z => by
    simp only [cca2Next, Function.comp_apply, decide_eq_true_eq]

/-- The uniform deterministic machine implementing the three activations. -/
private noncomputable def cca2Adversary : NUPPT :=
  NUPPT.ofPolyTimeUniform cca2Next_poly (.const 0)

/-- An activation reads only its argument and the unary parameter; its coins are ignored. -/
private theorem cca2Adversary_run (n : ℕ) (h : List Bool) (r : cca2Adversary.Coins n) :
    cca2Adversary.runAt n h r =
      if h = [] then
        pairEncode [false] (pairEncode [true, true]
          (List.replicate n false ++ List.replicate n true))
      else if pairSndD h = [] then
        pairEncode [false] (pairEncode [true]
          (cca2FlipLast (pairSndD (pairSndD (pairFstD h)))))
      else pairEncode [true]
        [!(pairSndD (pairSndD (pairFstD (pairSndD h)))).getLastD false] := by
  unfold cca2Adversary
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, cca2Next]
  simp only [NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, List.zipWith_replicate,
    Nat.min_self, Bool.xor_self]

/-- A one-entry log makes the second activation query the flipped challenge answer. -/
private theorem cca2Adversary_one (n : ℕ) (i x c : List Bool)
    (r : cca2Adversary.Coins n) :
    cca2Adversary.runAt n (pairEncode (pairEncode i (pairEncode x c)) []) r =
      pairEncode [false] (pairEncode [true] (cca2FlipLast c)) := by
  rw [cca2Adversary_run]
  have hn : pairEncode (pairEncode i (pairEncode x c)) [] ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [length_pairEncode, List.length_nil] at hh
    omega
  simp only [hn, ite_false, pairFstD_pairEncode, pairSndD_pairEncode, ite_true]

/-- A two-entry log makes the final activation negate the last bit of its second answer. -/
private theorem cca2Adversary_two (n : ℕ) (i x c j y d : List Bool)
    (r : cca2Adversary.Coins n) :
    cca2Adversary.runAt n
      (pairEncode (pairEncode i (pairEncode x c))
        (pairEncode (pairEncode j (pairEncode y d)) [])) r =
      pairEncode [true] [!d.getLastD false] := by
  rw [cca2Adversary_run]
  have hn : ∀ a b : List Bool, pairEncode a b ≠ [] := by
    intro a b he
    have hh := congrArg List.length he
    simp only [length_pairEncode, List.length_nil] at hh
    omega
  simp only [hn, ite_false, pairFstD_pairEncode, pairSndD_pairEncode]

/-- For every encryption tape there is an `n`-bit nonce `x`; the ciphertext is exactly
the pair of that nonce and the message masked by `F n k x`. -/
private theorem cca2Encrypt (n : ℕ) (k m : Fin n → Bool)
    (r : (prfFixedScheme F E hE hFE).enc.Coins n) :
    ∃ x : Fin n → Bool, List.ofFn r = List.ofFn x ∧
      List.ofFn ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r) =
        pairEncode (List.ofFn x) (List.ofFn (m + F n k x)) := by
  revert r
  simp only [FixedLengthScheme.encryptAt_eq, prfFixedScheme_ctLen]
  rw [prfFixedScheme_enc, prfScheme_enc]
  intro r
  let x := NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var n r
  have hx : List.ofFn x = List.ofFn r :=
    NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n r
  refine ⟨x, hx.symm, ?_⟩
  rw [runAt_prfEnc hE, ← hx, hFE, zipWith_xor_ofFn_add]
  apply GGMRed.ofFn_padFin_of_length
  simp only [length_pairEncode, List.length_ofFn, PolyExpr.eval_add,
    PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- The challenge query concatenates the all-false and all-true messages. -/
private def cca2Messages (n : ℕ) : Fin (n + n) → Bool :=
  Fin.append (fun _ => false) (fun _ => true)

/-- The challenge query's word is `0^n ++ 1^n`. -/
private theorem cca2Messages_ofFn (n : ℕ) :
    List.ofFn (cca2Messages n) = List.replicate n false ++ List.replicate n true := by
  rw [cca2Messages, List.ofFn_fin_append, List.ofFn_const, List.ofFn_const]

/-- Selecting challenge half `b` selects the constant message `b`. -/
private theorem cca2Messages_choice (n : ℕ) (b : Bool) :
    (if b then (FixedLengthScheme.splitHalf (cca2Messages n)).2
      else (FixedLengthScheme.splitHalf (cca2Messages n)).1) = fun _ => b := by
  cases b with
  | false =>
    change (FixedLengthScheme.splitHalf (cca2Messages n)).1 = fun _ => false
    rw [FixedLengthScheme.splitHalf_fst]
    funext i
    exact Fin.append_left _ _ i
  | true =>
    change (FixedLengthScheme.splitHalf (cca2Messages n)).2 = fun _ => true
    rw [FixedLengthScheme.splitHalf_snd]
    funext i
    exact Fin.append_right _ _ i

/-- The modified fixed-width ciphertext reads the word with its last bit flipped. -/
private def cca2Alter {d : ℕ} (c : Fin d → Bool) : Fin d → Bool :=
  padFin d (cca2FlipLast (List.ofFn c))

/-- At positive width the modified ciphertext has exactly the flipped word. -/
private theorem cca2Alter_ofFn {d : ℕ} (hd : 0 < d) (c : Fin d → Bool) :
    List.ofFn (cca2Alter c) = cca2FlipLast (List.ofFn c) := by
  apply GGMRed.ofFn_padFin_of_length
  rw [cca2FlipLast_length]
  · exact List.length_ofFn
  · intro he
    have hh := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at hh
    omega

/-- At positive width the modified ciphertext differs from the recorded challenge. -/
private theorem cca2Alter_ne {d : ℕ} (hd : 0 < d) (c : Fin d → Bool) :
    cca2Alter c ≠ c := by
  intro he
  have hh := congrArg List.ofFn he
  rw [cca2Alter_ofFn hd] at hh
  apply cca2FlipLast_ne (List.ofFn c) ?_ hh
  intro hc
  have hl := congrArg List.length hc
  simp only [List.length_ofFn, List.length_nil] at hl
  omega

/-- The ciphertext width evaluates to `3 * n + 2`. -/
private theorem cca2CtLen (n : ℕ) :
    (prfFixedScheme F E hE hFE).ctLen.eval n = 3 * n + 2 := by
  rw [prfFixedScheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul,
    PolyExpr.eval_const, PolyExpr.eval_const, PolyExpr.eval_var]

/-- Every generated key is an `n`-bit word. -/
private theorem cca2Gen (n : ℕ) (rg : (prfFixedScheme F E hE hFE).gen.Coins n) :
    ∃ k : Fin n → Bool, (prfFixedScheme F E hE hFE).gen.runAt n [] rg = List.ofFn k := by
  revert rg
  rw [prfFixedScheme_gen, prfScheme_gen]
  intro rg
  rw [runAt_coinKey]
  exact ⟨NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n rg,
    (NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n rg).symm⟩

/-- The actual encrypted word is well formed, and its last-bit modification is a
distinct, well-formed pair with the same nonce and the flipped masked payload. -/
private theorem cca2Cipher (n : ℕ) (hn : 0 < n) (k m : Fin n → Bool)
    (r : (prfFixedScheme F E hE hFE).enc.Coins n) :
    ∃ x : Fin n → Bool,
      List.ofFn ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r) =
        pairEncode (List.ofFn x) (List.ofFn (m + F n k x)) ∧
      List.ofFn (cca2Alter ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r)) =
        pairEncode (List.ofFn x) (List.ofFn (cca2FlipBits (m + F n k x))) ∧
      cca2Alter ((prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r) ≠
        (prfFixedScheme F E hE hFE).encryptAt n (List.ofFn k) m r := by
  obtain ⟨x, -, hc⟩ := cca2Encrypt F E hE hFE n k m r
  have hd : 0 < (prfFixedScheme F E hE hFE).ctLen.eval n := by
    rw [cca2CtLen]
    omega
  have hp : List.ofFn (m + F n k x) ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at hh
    omega
  refine ⟨x, hc, ?_, cca2Alter_ne hd _⟩
  rw [cca2Alter_ofFn hd, hc, cca2FlipLast_pair _ _ hp, cca2FlipLast_ofFn hn]

/-- Decrypting a pair `⟨x, v⟩` of `n`-bit words under the key `k` unmasks it:
`Dec_k(⟨x, v⟩) = v ⊕ F n k x`, read as an `n`-bit message. -/
private theorem cca2Decrypt (n : ℕ) (k x v : Fin n → Bool)
    (rd : (prfFixedScheme F E hE hFE).dec.Coins n) :
    decodeFin n ((prfFixedScheme F E hE hFE).dec.runAt n
      (pairEncode (List.ofFn k) (pairEncode (List.ofFn x) (List.ofFn v))) rd) =
        some (v + F n k x) := by
  revert rd
  rw [prfFixedScheme_dec, prfScheme_dec]
  intro rd
  rw [runAt_prfDec hE _ n _ _ _ List.length_ofFn List.length_ofFn, hFE, zipWith_xor_ofFn_add,
    decodeFin_ofFn]

/-- Transporting a bit vector along a width equality does not change its word:
`List.ofFn (cast h f) = List.ofFn f` when `h` comes from `a = b`. -/
private theorem cca2OfFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
  subst hab
  rfl

/-- At `n > 0`, the valid answer `⟨1, b^n ⊕ e_{n-1}⟩` ends in `!b`. -/
private theorem cca2LastBit {n : ℕ} (hn : 0 < n) (b : Bool) :
    (List.ofFn (Fin.cons (α := fun _ => Bool) true (cca2FlipBits (n := n) fun _ => b))).getLastD
      false = !b := by
  rw [List.ofFn_succ, Fin.cons_zero]
  simp only [Fin.cons_succ]
  rw [← cca2FlipLast_ofFn hn, List.ofFn_const]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.replicate_succ', cca2FlipLast_snoc, ← List.cons_append, List.getLastD_concat]

/-- **The attack against any fixed-length scheme.** Let `A = cca2Adversary` run with budget `2`
in `IND_b` under CCA2 with the key `k`. Suppose ciphertexts are nonempty and, for every challenge
`c = Enc_k(b^n)`, every decryption of `c` with its last bit flipped is a message `v` with
`⟨1, v⟩` ending in `!b`. Then `A` outputs `b` with probability one.

**Proof sketch.** Follow the three activations through `buildComp` and `simulate`.
1. On the empty log `A` asks `Challenge ⟨0^n, 1^n⟩`; the oracle samples `re`, answers
   `c = Enc_k(b^n)` (`cca2Messages_choice`) and records it.
2. On the one-entry log `A` asks `Dec` on `c'`, the flip of `c`; `c' ≠ c` (`cca2Alter_ne`), so
   CCA2's `Dec` samples `rd` and answers `⟨1, v⟩`.
3. On the two-entry log `A` outputs `¬(last bit of ⟨1, v⟩) = b`, within the budget.
Each sampled step is averaged by `expect_const`. -/
private theorem cca2Run (S : FixedLengthScheme) (n : ℕ) (hd : 0 < S.ctLen.eval n)
    (b : Bool) (k : List Bool)
    (hdec : ∀ (re : S.enc.Coins n) (rd : S.dec.Coins n), ∃ v : Fin n → Bool,
      decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn
        (cca2Alter (S.encryptAt n k (fun _ => b) re)))) rd) = some v ∧
      (List.ofFn (Fin.cons (α := fun _ => Bool) true v)).getLastD false = !b)
    (r : cca2Adversary.Coins n) :
    ProbComp.prob ((simulate (S.indImpl .cca2 b n k) (cca2Adversary.toComp (S.indCodec n) n 2 r)
      none).bind fun res => .pure (res.1 0)) (· = true) = if b = true then 1 else 0 := by
  obtain ⟨x, hx⟩ : ∃ x : (S.indSpec n).dom 2,
      x = cast (S.indSpec_challengeDom n).symm (cca2Messages n) := ⟨_, rfl⟩
  have h1 : (S.indCodec n).decodeMove
      (cca2Adversary.runAt n ((S.indCodec n).encodeLog []) r) = .query 2 x := by
    rw [MachineCodec.encodeLog_nil, cca2Adversary_run, if_pos rfl,
      FixedLengthScheme.indCodec_decodeMove]
    have hw : List.ofFn x = List.replicate n false ++ List.replicate n true := by
      rw [hx, cca2OfFn_cast (S.inLens_two n).symm, cca2Messages_ofFn]
    rw [← hw]
    exact decodeBitMove_query (S.inLens n) (S.outLens n) 1 2 x
  rw [NUPPT.toComp_eq, buildComp_succ_of_query (next := fun hist => (S.indCodec n).decodeMove
    (cca2Adversary.runAt n ((S.indCodec n).encodeLog hist) r)) h1, simulate_query,
    FixedLengthScheme.indImpl_challenge_none_onSpec]
  have hxc : cast (S.indSpec_challengeDom n) x = cca2Messages n := by
    rw [hx, cast_cast, cast_eq]
  simp only [hxc, cca2Messages_choice, OracleComp.bind_assoc, OracleComp.pure_bind,
    List.nil_append]
  rw [ProbComp.prob_bind]
  refine (congrArg (ProbComp.expect _) (funext fun re => ?_)).trans (ProbComp.expect_const _ _)
  have hne := cca2Alter_ne hd (S.encryptAt n k (fun _ => b) re)
  have h2 : (S.indCodec n).decodeMove (cca2Adversary.runAt n ((S.indCodec n).encodeLog
      [⟨2, x, cast (S.indSpec_challengeRng n).symm (S.encryptAt n k (fun _ => b) re)⟩]) r) =
      .query 1 (cast (S.indSpec_decDom n).symm
        (cca2Alter (S.encryptAt n k (fun _ => b) re))) := by
    simp only [MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
      FixedLengthScheme.indCodec_encodeEntry, cca2Adversary_one,
      FixedLengthScheme.indCodec_decodeMove]
    rw [cca2OfFn_cast (S.outLens_two n).symm, ← cca2Alter_ofFn hd,
      ← cca2OfFn_cast (S.inLens_one n).symm (S.indSpec_decDom n).symm]
    exact decodeBitMove_query (S.inLens n) (S.outLens n) 1 1 _
  rw [buildComp_succ_of_query (next := fun hist => (S.indCodec n).decodeMove
    (cca2Adversary.runAt n ((S.indCodec n).encodeLog hist) r)) h2, simulate_query,
    FixedLengthScheme.indImpl_dec_onSpec]
  have hcc : cast (S.indSpec_decDom n) (cast (S.indSpec_decDom n).symm
      (cca2Alter (S.encryptAt n k (fun _ => b) re))) =
        cca2Alter (S.encryptAt n k (fun _ => b) re) := by
    rw [cast_cast, cast_eq]
  have hopen : (FixedLengthScheme.decOpen .cca2
      (some (S.encryptAt n k (fun _ => b) re)).isSome && !decide
        (some (S.encryptAt n k (fun _ => b) re) =
          some (cca2Alter (S.encryptAt n k (fun _ => b) re)))) = true := by
    simp only [FixedLengthScheme.decOpen_cca2, Option.some.injEq,
      Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    exact fun h => hne h.symm
  rw [hcc, if_pos hopen]
  simp only [OracleComp.bind_assoc, OracleComp.pure_bind]
  rw [ProbComp.prob_bind]
  refine (congrArg (ProbComp.expect _) (funext fun rd => ?_)).trans (ProbComp.expect_const _ _)
  obtain ⟨v, hv, hlast⟩ := hdec re rd
  rw [hv, FixedLengthScheme.decAnswer_some]
  have h3 : (S.indCodec n).decodeMove (cca2Adversary.runAt n ((S.indCodec n).encodeLog
      ([⟨2, x, cast (S.indSpec_challengeRng n).symm (S.encryptAt n k (fun _ => b) re)⟩] ++
        [⟨1, cast (S.indSpec_decDom n).symm (cca2Alter (S.encryptAt n k (fun _ => b) re)),
          cast (S.indSpec_decRng n).symm (Fin.cons (α := fun _ => Bool) true v)⟩])) r) =
      .ret fun _ => b := by
    simp only [List.singleton_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
      FixedLengthScheme.indCodec_encodeEntry, cca2Adversary_two,
      FixedLengthScheme.indCodec_decodeMove]
    rw [cca2OfFn_cast (S.outLens_one n).symm, hlast, Bool.not_not]
    have hb : [b] = List.ofFn (fun _ : Fin 1 => b) := by
      rw [List.ofFn_const, List.replicate_one]
    rw [hb]
    exact decodeBitMove_ret (S.inLens n) (S.outLens n) 1 _
  rw [buildComp_zero_of_ret (next := fun hist => (S.indCodec n).decodeMove
    (cca2Adversary.runAt n ((S.indCodec n).encodeLog hist) r)) h3, simulate_pure,
    OracleComp.pure_bind, ProbComp.prob_pure]

/-- **Claim 169.a: the §3.9 scheme is not CCA2-secure** [PS10, §7.1.3, p. 169], whatever the
family `F`. Some adversary, with a constant query budget, has advantage `1` at every `n > 0`.

The source's attack asks `Dec` for "`c + 1`", the challenge plus one. Read as an exclusive-or with
a fixed nonzero string, it flips the last bit of the challenge. The result is a different, still
well-formed ciphertext, which CCA2's `Dec` therefore answers.

**Proof sketch.**
1. The machine `A` reads its log. With an empty log, it asks the challenge on `⟨0^n, 1^n⟩`. With
   one entry, the challenge answer `c`, it asks `Dec` on `c` with its last bit flipped. With two
   entries, the second a `Dec` answer `⟨v, m'⟩`, it outputs `¬ m'_{n-1}`. It is polynomial-time
   (`NUPPT.ofPolyTimeUniform`); its query budget is `2`, so the third activation's output is read.
2. In `IND_b` the challenge is `c = ⟨r, b^n ⊕ f_k(r)⟩`. For `n > 0` its last bit lies in the
   second component, so the flipped string `c'` is `⟨r, b^n ⊕ e_{n-1} ⊕ f_k(r)⟩`: well-formed,
   and not `c`. CCA2's `Dec` answers `⟨1, b^n ⊕ e_{n-1}⟩` (`runAt_prfDec`).
3. So, for every key and all coins, `A` outputs `b` (`cca2Run`): `IND_b` accepts with probability
   `1` if `b = 1` and `0` if `b = 0`, and the advantage is `|0 − 1| = 1`. -/
theorem prfFixedScheme_not_cca2 :
    ∃ (A : NUPPT) (q : PolyExpr), ∀ n, 0 < n →
      advantage ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) false n)
        ((prfFixedScheme F E hE hFE).indGame .cca2 A (q.eval n) true n) = 1 := by
  refine ⟨cca2Adversary, .const 2, fun n hn => ?_⟩
  have hd : 0 < (prfFixedScheme F E hE hFE).ctLen.eval n := by
    rw [cca2CtLen]
    omega
  have hacc : ∀ b : Bool, accept ((prfFixedScheme F E hE hFE).indGame .cca2 cca2Adversary
      ((PolyExpr.const 2).eval n) b n) = if b = true then 1 else 0 := by
    intro b
    rw [PolyExpr.eval_const, accept_eq, FixedLengthScheme.indGame_eq, ProbComp.prob_bind]
    refine (congrArg (ProbComp.expect _) (funext fun rg => ?_)).trans (ProbComp.expect_const _ _)
    obtain ⟨kv, hk⟩ := cca2Gen F E hE hFE n rg
    rw [ProbComp.prob_bind]
    refine (congrArg (ProbComp.expect _) (funext fun r => ?_)).trans (ProbComp.expect_const _ _)
    rw [hk]
    refine cca2Run _ n hd b _ (fun re rd => ?_) r
    obtain ⟨xr, -, hc, -⟩ := cca2Cipher F E hE hFE n hn kv (fun _ => b) re
    refine ⟨cca2FlipBits (fun _ => b), ?_, cca2LastBit hn b⟩
    rw [hc, cca2Decrypt, cca2FlipBits_unmask]
  rw [advantage_eq, hacc, hacc]
  norm_num

/-- **The §3.9 scheme is not CCA2-secure** in the sense of Definition 168.1: an advantage equal
to `1` at every positive `n` is not negligible (Claim 169.a). -/
theorem not_prfFixedScheme_cca2 : ¬ (prfFixedScheme F E hE hFE).INDSecure .cca2 := by
  intro h
  rw [FixedLengthScheme.INDSecure_iff] at h
  obtain ⟨A, q, hA⟩ := prfFixedScheme_not_cca2 F E hE hFE
  obtain ⟨ε, hε, hle⟩ := h A q
  rw [negligible_iff] at hε
  obtain ⟨n₀, hn₀⟩ := hε 0
  have h1 := hn₀ (n₀ + 1) (by omega)
  have h2 := hle (n₀ + 1)
  rw [hA (n₀ + 1) (by omega)] at h2
  simp only [pow_zero, div_one] at h1
  linarith [le_abs_self (ε (n₀ + 1))]

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Collision.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Lazy
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bad event of the lazy experiment

Step 2 of [PS10, Theorem 168.2]: in the IND experiment with a lazily sampled random function
(`lazyImpl`), the two values of the bit `b` give the same law until the bad flag is raised, and
the flag is raised with probability at most `q(n)² / 2ⁿ` for an adversary making at most `q(n)`
queries.

* *Identical until bad.* Before the challenge the experiment does not read `b`. At the first
  challenge with a new nonce `r*`, the ciphertext `⟨r*, m_b ⊕ y⟩` has a uniform pad `y`; the
  change of variables `y ↦ y ⊕ m₀ ⊕ m₁` (`xorPerm`) maps the ciphertext for `b = 0` to that for
  `b = 1`, and the record `⟨m₀ ‖ m₁, c⟩` is the same. After the challenge, `b` is read only at
  `r*`: by an encryption with nonce `r*`, which raises the flag, or by a decryption, which CPA and
  CCA1 refuse after the challenge (`lazyImpl_agree`).
* *The bad probability.* A query from a good state raises the flag with probability at most
  `(|T| + 1) / 2ⁿ` (`lazyImpl_step`; the first challenge's nonce hits one of the `|T|` points of
  the table, `prob_mem_le`, or an encryption's nonce hits `r*`), and adds at most one point to the
  table (`lazyImpl_grow`). A potential argument sums these over `q` queries (`prob_bad_le`).

## Main results

* `PRFGame.prob_bad_le`: a bad event raised with probability at most `(size + 1) · δ` per query,
  by queries that grow the size by at most one, has probability at most `q · (size + q) · δ`.
* `PRFGame.lazyImpl_agree`, `lazyImpl_stick`, `lazyImpl_step`, `lazyImpl_grow`.
* `PRFGame.abs_prob_lazyImpl_sub_le`: the two bits' lazy experiments differ by at most `q² / 2ⁿ`.
* `PRFGame.abs_expect_fImpl_sub_le`: hence so do the experiments with a uniform random function.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 168.2 (book p. 168), the proof's bad event.
* [BR06] M. Bellare, P. Rogaway, *The Security of Triple Encryption and a Framework for
  Code-Based Game-Playing Proofs*, EUROCRYPT 2006 (identical until bad).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

/-! ### A potential bound on a bad event -/

section Potential

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- **A bad event raised a little at each query:** if from a good state each query raises `bad`
with probability at most `(sz s + 1) · δ` and grows the size `sz` by at most one, then from a good
state `s` a computation making at most `m` queries ends in a bad state with probability at most
`m · (sz s + m) · δ`.

**Proof sketch.** Induction on the computation. At a query, a bad successor contributes at most
its probability; a good successor `s'` has `sz s' ≤ sz s + 1` and, by induction, contributes at
most `(m - 1) · (sz s + m) · δ`. Add `(sz s + 1) · δ ≤ (sz s + m) · δ`. -/
theorem prob_bad_le {impl : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
    (sz : σ → ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hstep : ∀ i x s, ¬ bad s → prob (impl i x s) (fun ys => bad ys.2) ≤ (sz s + 1) * δ)
    (hgrow : ∀ i x s, (impl i x s).AllOutputs fun ys => sz ys.2 ≤ sz s + 1)
    {α : Type} (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ)
    (hs : ¬ bad s) :
    prob (simulate impl c s) (fun r => bad r.2) ≤ m * (sz s + m) * δ := by
  induction c generalizing m s with
  | pure a =>
    rw [simulate_pure, prob_pure, if_neg hs]
    exact mul_nonneg (by positivity) hδ
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hk' : ∀ y, (k y).CostBoundedBy (fun _ => 1) m' := fun y => by
      simpa using hk y
    have hm0 : (0 : ℝ) ≤ m' := Nat.cast_nonneg m'
    set K : ℝ := m' * (sz s + (m' + 1)) * δ with hK
    have hK0 : 0 ≤ K := mul_nonneg (by positivity) hδ
    rw [simulate_query, prob_bind]
    calc expect (impl i x s) (fun ys => prob (simulate impl (k ys.1) ys.2) (fun r => bad r.2))
        ≤ expect (impl i x s) (fun ys => (if bad ys.2 then (1 : ℝ) else 0) + K) := by
          refine expect_mono_of_allOutputs (hgrow i x s) fun ys hys => ?_
          by_cases hb : bad ys.2
          · rw [if_pos hb]
            have h1 := prob_le_one (simulate impl (k ys.1) ys.2) (fun r => bad r.2)
            linarith
          · rw [if_neg hb, zero_add]
            refine (ih ys.1 m' (hk' ys.1) ys.2 hb).trans ?_
            have hys' : (sz ys.2 : ℝ) ≤ sz s + 1 := by exact_mod_cast hys
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hm0) hδ
      _ = prob (impl i x s) (fun ys => bad ys.2) + K := by
          rw [expect_add (impl i x s) (fun ys => if bad ys.2 then (1 : ℝ) else 0) (fun _ => K),
            expect_const, prob_eq_expect]
      _ ≤ ((m' + 1 : ℕ) : ℝ) * (sz s + ((m' + 1 : ℕ) : ℝ)) * δ := by
          have h3 := hstep i x s hs
          have h4 : ((sz s : ℝ) + 1) * δ ≤ (sz s + (m' + 1)) * δ :=
            mul_le_mul_of_nonneg_right (by linarith) hδ
          have e : ((m' : ℝ) + 1) * (sz s + (m' + 1)) * δ = K + (sz s + (m' + 1)) * δ := by
            rw [hK]; ring
          push_cast
          linarith

end Potential

/-! ### Hitting a list with a uniform sample -/

/-- A uniform element of `T` lies in a list `L` with probability at most `|L| / |T|`
(`prob_mem_le` for a fixed list). -/
theorem expect_sample_mem_le {T : Type} [Fintype T] [Nonempty T] [DecidableEq T] (L : List T) :
    expect (sample T) (fun t => if t ∈ L then (1 : ℝ) else 0) ≤ L.length / Fintype.card T := by
  have h := prob_mem_le (OracleComp.pure L : ProbComp (List T)) (q := L.length)
    (OracleComp.allOutputs_pure.2 le_rfl)
  rw [prob_bind, expect_pure, prob_bind] at h
  refine Eq.trans_le ?_ h
  refine congrArg _ (funext fun t => ?_)
  rw [prob_pure]

/-- A key with a value in an association list is one of its keys:
`(T.lookup x).isSome → x ∈ T.map Prod.fst`. -/
theorem mem_keys_of_lookup_isSome {α β : Type} [DecidableEq α] (T : List (α × β)) (x : α)
    (h : (T.lookup x).isSome = true) : x ∈ T.map Prod.fst := by
  induction T with
  | nil => simp at h
  | cons p T ih =>
    obtain ⟨k, v⟩ := p
    rw [List.map_cons]
    by_cases hx : x = k
    · rw [hx]
      exact List.mem_cons_self
    · have hb : (x == k) = false := beq_eq_false_iff_ne.mpr hx
      simp only [List.lookup_cons, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

/-! ### The state readings -/

section Records

variable {n d : ℕ}

/-- Adding a point grows the table by at most one: `|(addPt b st x y hit).1| ≤ |st.1| + 1`. -/
theorem length_addPt_le (b : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool) :
    (addPt b st x y hit).1.length ≤ st.1.length + 1 := by
  rw [addPt_eq]
  split <;> simp

/-- Adding a point raises the flag by `hit`: `(addPt b st x y hit).2.2 = (st.2.2 || hit)`. -/
theorem flag_addPt (b : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool) :
    (addPt b st x y hit).2.2 = (st.2.2 || hit) := by
  rw [addPt_eq]

/-- Away from the challenge's nonce the recorded values do not depend on `b`:
`hitStar st x = false → look b st x = look b' st x`. -/
theorem look_eq_of_hitStar (b b' : Bool) (st : LState n d) (x : Fin n → Bool)
    (h : hitStar st x = false) : look b st x = look b' st x := by
  obtain ⟨T, ch, bd⟩ := st
  cases ch with
  | none => rw [look_none, look_none]
  | some p =>
    obtain ⟨ml, c⟩ := p
    rw [hitStar_some, decide_eq_false_iff_not] at h
    rw [look_some, look_some, if_neg h, if_neg h]

/-- Which points have a recorded value does not depend on `b`:
`(look b st x).isSome = (look b' st x).isSome`. -/
theorem isSome_look_eq (b b' : Bool) (st : LState n d) (x : Fin n → Bool) :
    (look b st x).isSome = (look b' st x).isSome := by
  obtain ⟨T, ch, bd⟩ := st
  cases ch with
  | none => rw [look_none, look_none]
  | some p =>
    obtain ⟨ml, c⟩ := p
    rw [look_some, look_some]
    by_cases h : x = rStar c
    · rw [if_pos h, if_pos h]; rfl
    · rw [if_neg h, if_neg h]

/-- Adding a point does not depend on `b`: `addPt b st x y hit = addPt b' st x y hit`. -/
theorem addPt_eq_of (b b' : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool) :
    addPt b st x y hit = addPt b' st x y hit := by
  rw [addPt_eq, addPt_eq, isSome_look_eq b b']

/-- Exclusive-or with a fixed vector `v`, as a permutation of `{0,1}ⁿ`. -/
def xorPerm (v : Fin n → Bool) : Equiv.Perm (Fin n → Bool) :=
  Function.Involutive.toPerm (fun y i => xor (y i) (v i)) fun y => funext fun i => by
    simp

/-- `xorPerm v y = y ⊕ v`. -/
theorem xorPerm_apply (v y : Fin n → Bool) : xorPerm v y = fun i => xor (y i) (v i) := rfl

/-- **The change of variables at the challenge:** with `|m₀| = |m₁| = n`,
`⟨r, m₀ ⊕ y⟩ = ⟨r, m₁ ⊕ (y ⊕ m₀ ⊕ m₁)⟩`.

**Proof sketch.** Both are `pairEncode ⟦r⟧ _`; compare the second components position by
position: `m₀ᵢ ⊕ yᵢ = m₁ᵢ ⊕ (yᵢ ⊕ m₀ᵢ ⊕ m₁ᵢ)` by cases on the three bits. -/
theorem ctOf_xorPerm (r : Fin n → Bool) {m₀ m₁ : List Bool} (h₀ : m₀.length = n)
    (h₁ : m₁.length = n) (y : Fin n → Bool) :
    ctOf r m₀ y = ctOf r m₁ (xorPerm (padFin n (List.zipWith xor m₀ m₁)) y) := by
  rw [ctOf_eq, ctOf_eq]
  congr 1
  have hv : List.ofFn (padFin n (List.zipWith xor m₀ m₁)) = List.zipWith xor m₀ m₁ :=
    GGMRed.ofFn_padFin_of_length (by simp [h₀, h₁])
  have hY : ∀ v : Fin n → Bool,
      List.ofFn (xorPerm v y) = List.zipWith xor (List.ofFn y) (List.ofFn v) := fun v => by
    apply List.ext_getElem
    · simp
    · intro i _ _
      simp [xorPerm_apply]
  rw [hY, hv]
  apply List.ext_getElem
  · simp [h₀, h₁]
  · intro i hi _
    have hi' : i < n := by simp [h₀] at hi; omega
    have i0 : i < m₀.length := by rw [h₀]; exact hi'
    have i1 : i < m₁.length := by rw [h₁]; exact hi'
    have iy : i < (List.ofFn y).length := by rw [List.length_ofFn]; exact hi'
    simp only [List.getElem_zipWith]
    cases m₀[i] <;> cases m₁[i] <;> cases (List.ofFn y)[i] <;> rfl

/-- The empty state records no value: `ovr b ([], none, false) R = R`. -/
theorem ovr_init (b : Bool) (R : (Fin n → Bool) → (Fin n → Bool)) :
    ovr b (([], none, false) : LState n d) R = R := by
  funext x
  rw [ovr_apply, look_none, List.lookup_nil, Option.getD_none]

end Records

/-! ### The lazy experiment until the bad event -/

section Agree

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (atk : Attack)

/-- **The two bits agree until bad:** for CPA and CCA1 (decryption refused after the challenge)
and `2n`-bit challenge queries, from a good state the lazy experiments for `b` and `b'` give the
same law to good successors: for every `g`,
`𝔼[ys.2.2.2 ? 0 : g ys] (lazyImpl … b i x s) = 𝔼[ys.2.2.2 ? 0 : g ys] (lazyImpl … b' i x s)`.

**Proof sketch.** An encryption reads `b` only at the challenge's nonce, where it raises the flag
(`look_eq_of_hitStar`, `addPt_eq_of`). A decryption is refused after the challenge and before it
reads the table only. A repeated challenge repeats the record. At the first challenge with a new
nonce, change the pad by `xorPerm (m₀ ⊕ m₁)` (`expect_sample_equiv`, `ctOf_xorPerm`). -/
theorem lazyImpl_agree (hatk : FixedLengthScheme.decOpen atk true = false) (hi2 : ins 2 = n + n)
    (b b' : Bool) (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : LState n d)
    (hs : ¬ s.2.2 = true) (g : (bitSpec ins outs).rng i × LState n d → ℝ) :
    expect (lazyImpl ins outs d n atk b i x s) (fun ys => if ys.2.2.2 = true then 0 else g ys) =
      expect (lazyImpl ins outs d n atk b' i x s)
        (fun ys => if ys.2.2.2 = true then 0 else g ys) := by
  match i, x, g with
  | 0, m, g =>
    simp only [lazyImpl_enc, expect_bind, expect_pure, addPt_eq_of b b' s]
    refine congrArg _ (funext fun r => congrArg _ (funext fun y => ?_))
    cases h : hitStar s r
    · rw [look_eq_of_hitStar b b' s r h]
    · simp [flag_addPt]
  | 1, c, g =>
    obtain ⟨T, ch, bd⟩ := s
    cases ch with
    | some p =>
      have hcl : (FixedLengthScheme.decOpen atk ((T, some p, bd) : LState n d).2.1.isSome &&
          decWF n (List.ofFn c)) = false := by
        show (FixedLengthScheme.decOpen atk true && _) = false
        rw [hatk, Bool.false_and]
      rw [lazyImpl_dec_closed ins outs d n atk b c _ hcl,
        lazyImpl_dec_closed ins outs d n atk b' c _ hcl]
    | none =>
      by_cases hop : (FixedLengthScheme.decOpen atk ((T, none, bd) : LState n d).2.1.isSome &&
          decWF n (List.ofFn c)) = true
      · rw [lazyImpl_dec_open ins outs d n atk b c _ hop,
          lazyImpl_dec_open ins outs d n atk b' c _ hop]
        simp only [look_none, addPt_eq_of b b' ((T, none, bd) : LState n d)]
      · rw [lazyImpl_dec_closed ins outs d n atk b c _ (Bool.eq_false_iff.2 hop),
          lazyImpl_dec_closed ins outs d n atk b' c _ (Bool.eq_false_iff.2 hop)]
  | 2, mm, g =>
    obtain ⟨T, ch, bd⟩ := s
    cases ch with
    | some p =>
      obtain ⟨ml, c⟩ := p
      rw [lazyImpl_challenge_some, lazyImpl_challenge_some]
    | none =>
      have hbd : bd = false := Bool.eq_false_iff.2 hs
      subst hbd
      have hml : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, hi2]
      have hm : ∀ b₀, (AdaptiveCPA.msgOf n b₀ (List.ofFn mm)).length = n := fun b₀ => by
        rw [AdaptiveCPA.msgOf_eq]
        cases b₀ <;> simp [hml]
      simp only [lazyImpl_challenge_none, expect_bind, expect_pure, look_none]
      refine congrArg _ (funext fun r => ?_)
      cases hr : T.lookup r with
      | some y₀ => simp
      | none =>
        simp only [Option.getD_none, Option.isSome_none, Bool.or_false, Bool.false_eq_true,
          if_false]
        refine Eq.trans ?_ (expect_sample_equiv (xorPerm (padFin n (List.zipWith xor
          (AdaptiveCPA.msgOf n b (List.ofFn mm)) (AdaptiveCPA.msgOf n b' (List.ofFn mm))))) _)
        refine congrArg _ (funext fun y => ?_)
        rw [ctOf_xorPerm r (hm b) (hm b') y]

/-- **The flag stays raised:** if `s.2.2 = true`, every outcome `ys` of
`lazyImpl … b i x s` has `ys.2.2.2 = true`.

**Proof sketch.** By the oracle: every branch keeps the flag or ors it with a new bit
(`addPt_eq`, `lazyImpl_*`). -/
theorem lazyImpl_stick (b : Bool) (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : LState n d)
    (hs : s.2.2 = true) :
    (lazyImpl ins outs d n atk b i x s).AllOutputs fun ys => ys.2.2.2 = true := by
  match i, x with
  | 0, m =>
    rw [lazyImpl_enc]
    exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ =>
      OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
        OracleComp.allOutputs_pure.2 (by rw [flag_addPt, hs, Bool.true_or])
  | 1, c =>
    by_cases hop : (FixedLengthScheme.decOpen atk s.2.1.isSome && decWF n (List.ofFn c)) = true
    · rw [lazyImpl_dec_open ins outs d n atk b c s hop]
      exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
        OracleComp.allOutputs_pure.2 (by rw [flag_addPt, hs, Bool.true_or])
    · rw [lazyImpl_dec_closed ins outs d n atk b c s (Bool.eq_false_iff.2 hop)]
      exact OracleComp.allOutputs_pure.2 hs
  | 2, mm =>
    obtain ⟨T, ch, bd⟩ := s
    cases ch with
    | some p =>
      obtain ⟨ml, c⟩ := p
      rw [lazyImpl_challenge_some]
      exact OracleComp.allOutputs_pure.2 hs
    | none =>
      have hbd : bd = true := hs
      subst hbd
      rw [lazyImpl_challenge_none]
      exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ =>
        OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
          OracleComp.allOutputs_pure.2 rfl

/-- **Each query grows the table by at most one point:** every outcome `ys` of
`lazyImpl … b i x s` has `|ys.2.1| ≤ |s.1| + 1`.

**Proof sketch.** By the oracle: encryptions and open decryptions add at most one point
(`length_addPt_le`); challenges, closed decryptions and repeats keep the table. -/
theorem lazyImpl_grow (b : Bool) (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : LState n d) :
    (lazyImpl ins outs d n atk b i x s).AllOutputs fun ys => ys.2.1.length ≤ s.1.length + 1 := by
  match i, x with
  | 0, m =>
    rw [lazyImpl_enc]
    exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ =>
      OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
        OracleComp.allOutputs_pure.2 (length_addPt_le b s r y _)
  | 1, c =>
    by_cases hop : (FixedLengthScheme.decOpen atk s.2.1.isSome && decWF n (List.ofFn c)) = true
    · rw [lazyImpl_dec_open ins outs d n atk b c s hop]
      exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
        OracleComp.allOutputs_pure.2 (length_addPt_le b s _ y _)
    · rw [lazyImpl_dec_closed ins outs d n atk b c s (Bool.eq_false_iff.2 hop)]
      exact OracleComp.allOutputs_pure.2 (Nat.le_succ _)
  | 2, mm =>
    obtain ⟨T, ch, bd⟩ := s
    cases ch with
    | some p =>
      obtain ⟨ml, c⟩ := p
      rw [lazyImpl_challenge_some]
      exact OracleComp.allOutputs_pure.2 (Nat.le_succ _)
    | none =>
      rw [lazyImpl_challenge_none]
      exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun r _ =>
        OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
          OracleComp.allOutputs_pure.2 (Nat.le_succ _)

/-- **Each query raises the flag with probability at most `(|T| + 1) / 2ⁿ`.** An encryption raises
it when its nonce is the challenge's (probability `1 / 2ⁿ`); the first challenge when its nonce is
one of the table's `|T|` points (`prob_mem_le`); decryptions and repeated challenges never.

**Proof sketch.** Write the probability as an expectation over the sampled nonce and bound the
indicator of the flag by the indicator of membership in a list of at most `|T| + 1` points;
conclude with `expect_sample_mem_le`. -/
theorem lazyImpl_step (b : Bool) (i : Fin 3) (x : (bitSpec ins outs).dom i) (s : LState n d)
    (hs : ¬ s.2.2 = true) :
    prob (lazyImpl ins outs d n atk b i x s) (fun ys => ys.2.2.2 = true) ≤
      (s.1.length + 1) * (1 / 2 ^ n) := by
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by simp
  have hpos : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
  obtain ⟨T, ch, bd⟩ := s
  have hbd : bd = false := Bool.eq_false_iff.2 hs
  subst hbd
  have hrhs : (0 : ℝ) ≤ ((T, ch, false) : LState n d).1.length + 1 := by positivity
  match i, x with
  | 0, m =>
    rw [prob_eq_expect]
    simp only [lazyImpl_enc, expect_bind, expect_pure, flag_addPt, Bool.false_or, expect_const]
    cases ch with
    | none =>
      simp only [hitStar_none, Bool.false_eq_true, if_false, expect_const]
      exact mul_nonneg hrhs hpos
    | some p =>
      obtain ⟨ml, c⟩ := p
      refine (expect_mono _ fun r => ?_).trans ((expect_sample_mem_le [rStar c]).trans ?_)
      · rw [hitStar_some]
        by_cases h : r = rStar c <;> simp [h]
      · rw [hcard, List.length_singleton, Nat.cast_one, one_div]
        rw [← one_div]
        exact le_mul_of_one_le_left hpos (by simp)
  | 1, c =>
    rw [prob_eq_zero_of_allOutputs]
    · exact mul_nonneg hrhs hpos
    · by_cases hop : (FixedLengthScheme.decOpen atk ch.isSome && decWF n (List.ofFn c)) = true
      · rw [lazyImpl_dec_open ins outs d n atk b c _ hop]
        exact OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun y _ =>
          OracleComp.allOutputs_pure.2 (by rw [flag_addPt]; simp)
      · rw [lazyImpl_dec_closed ins outs d n atk b c _ (Bool.eq_false_iff.2 hop)]
        exact OracleComp.allOutputs_pure.2 (by simp)
  | 2, mm =>
    cases ch with
    | some p =>
      obtain ⟨ml, c⟩ := p
      rw [lazyImpl_challenge_some, prob_eq_zero_of_allOutputs
        (OracleComp.allOutputs_pure.2 (by simp))]
      exact mul_nonneg hrhs hpos
    | none =>
      rw [prob_eq_expect]
      simp only [lazyImpl_challenge_none, expect_bind, expect_pure, look_none, Bool.false_or]
      refine (expect_mono _ fun r => ?_).trans ((expect_sample_mem_le (T.map Prod.fst)).trans ?_)
      · by_cases h : (T.lookup r).isSome = true
        · simp only [h, ↓reduceIte, expect_const, if_pos (mem_keys_of_lookup_isSome T r h),
            le_refl]
        · rw [Bool.not_eq_true] at h
          simp only [h, Bool.false_eq_true, ↓reduceIte, expect_const]
          split_ifs <;> norm_num
      · rw [hcard, List.length_map, div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_right (by simp) hpos

/-- **The two bits' lazy experiments differ by at most `q² / 2ⁿ`** [PS10, Thm 168.2, proof]:
for CPA and CCA1, `2n`-bit challenge queries and a computation making at most `q` queries, the
probabilities of any event on its output differ by at most `q² / 2ⁿ`.

**Proof sketch.** Identical until bad (`identical_until_bad` with `lazyImpl_agree`,
`lazyImpl_stick`), and the potential bound on the flag (`prob_bad_le` with `lazyImpl_step`,
`lazyImpl_grow`) from the empty table. -/
theorem abs_prob_lazyImpl_sub_le (hatk : FixedLengthScheme.decOpen atk true = false)
    (hi2 : ins 2 = n + n) {α : Type} (c : OracleComp (bitSpec ins outs) α) (P : α → Prop)
    (q : ℕ) (hc : c.CostBoundedBy (fun _ => 1) q) :
    |prob (simulate (lazyImpl ins outs d n atk false) c (([], none, false) : LState n d))
          (fun r => P r.1) -
        prob (simulate (lazyImpl ins outs d n atk true) c (([], none, false) : LState n d))
          (fun r => P r.1)| ≤ q ^ 2 / 2 ^ n := by
  have h1 := identical_until_bad (fun st : LState n d => st.2.2 = true)
    (fun i x s hs g => lazyImpl_agree ins outs d n atk hatk hi2 false true i x s hs g)
    (fun i x s hs => lazyImpl_stick ins outs d n atk false i x s hs)
    (fun i x s hs => lazyImpl_stick ins outs d n atk true i x s hs) c P
    (s := (([], none, false) : LState n d)) Bool.false_ne_true
  have h2 := prob_bad_le (impl := lazyImpl ins outs d n atk false)
    (fun st : LState n d => st.2.2 = true) (fun st => st.1.length) (δ := 1 / 2 ^ n)
    (by positivity) (fun i x s hs => lazyImpl_step ins outs d n atk false i x s hs)
    (fun i x s => lazyImpl_grow ins outs d n atk false i x s) c q hc
    (([], none, false) : LState n d) Bool.false_ne_true
  refine h1.trans (h2.trans (le_of_eq ?_))
  simp only [List.length_nil, Nat.cast_zero, zero_add]
  ring

/-- Expectations of functions `ε`-close at every point are `ε`-close:
`(∀ x, |f x - g x| ≤ ε) → |𝔼_c f - 𝔼_c g| ≤ ε`. -/
theorem abs_expect_sub_le {ρ : Type} (c : ProbComp ρ) {f g : ρ → ℝ} {ε : ℝ}
    (h : ∀ x, |f x - g x| ≤ ε) : |expect c f - expect c g| ≤ ε := by
  have h1 : expect c f ≤ expect c g + ε :=
    calc expect c f ≤ expect c (fun x => g x + ε) :=
          expect_mono c fun x => by linarith [(abs_le.1 (h x)).2]
      _ = expect c g + ε := by rw [expect_add c g (fun _ => ε), expect_const]
  have h2 : expect c g ≤ expect c f + ε :=
    calc expect c g ≤ expect c (fun x => f x + ε) :=
          expect_mono c fun x => by linarith [(abs_le.1 (h x)).1]
      _ = expect c f + ε := by rw [expect_add c f (fun _ => ε), expect_const]
  rw [abs_le]
  constructor <;> linarith

/-- **Step 2 of [PS10, Thm 168.2]: with a random function the bit is hidden up to `q² / 2ⁿ`.**
For CPA and CCA1, `d = 3n + 2`, `2n`-bit challenge queries and computations `C r` (over coins
`r`) making at most `q` queries, the experiments with a uniform random function for `b = 0` and
`b = 1` accept with probabilities at most `q² / 2ⁿ` apart.

**Proof sketch.** For each `b` and coins `r`, averaging over the function is the lazy experiment
from the empty state (`expect_lazyImpl`; the override of the empty state is the function itself);
pointwise in `r` the lazy experiments differ by at most `q² / 2ⁿ` (`abs_prob_lazyImpl_sub_le`);
average over `r` (`abs_expect_sub_le`). -/
theorem abs_expect_fImpl_sub_le (hatk : FixedLengthScheme.decOpen atk true = false)
    (hd : d = 3 * n + 2) (hi2 : ins 2 = n + n) {ρ α : Type} [Fintype ρ] [Nonempty ρ]
    (C : ρ → OracleComp (bitSpec ins outs) α) (P : α → Prop) [DecidablePred P] (q : ℕ)
    (hC : ∀ r, (C r).CostBoundedBy (fun _ => 1) q) :
    |expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R => expect (sample ρ) fun r =>
        expect (simulate (fImpl ins outs d n atk false R) (C r) none)
          (fun p => if P p.1 then (1 : ℝ) else 0)) -
      expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R => expect (sample ρ) fun r =>
        expect (simulate (fImpl ins outs d n atk true R) (C r) none)
          (fun p => if P p.1 then (1 : ℝ) else 0))| ≤ q ^ 2 / 2 ^ n := by
  have key : ∀ (b : Bool) (r : ρ),
      expect (sample ((Fin n → Bool) → (Fin n → Bool))) (fun R =>
          expect (simulate (fImpl ins outs d n atk b R) (C r) none)
            (fun p => if P p.1 then (1 : ℝ) else 0)) =
        prob (simulate (lazyImpl ins outs d n atk b) (C r) (([], none, false) : LState n d))
          (fun p => P p.1) := fun b r => by
    have h := expect_lazyImpl ins outs d n atk b hd hi2 (fun a => if P a then (1 : ℝ) else 0) (C r)
      (([], none, false) : LState n d)
    simp only [ovr_init, Option.map_none] at h
    rw [h, prob_eq_expect]
  rw [expect_sample_comm, expect_sample_comm (α := (Fin n → Bool) → (Fin n → Bool))]
  simp only [key]
  exact abs_expect_sub_le _ fun r =>
    abs_prob_lazyImpl_sub_le ins outs d n atk hatk hi2 (C r) P q (hC r)

end Agree

end TCSlib.Cryptography.Composability.PRFGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Games.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The CPA and CCA1 games of the §3.9 scheme with an arbitrary pad function

The scheme of [PS10, Algorithm 99.1] encrypts `m` as `⟨r, m ⊕ f(r)⟩` with a fresh `n`-bit `r`,
where `f = f_k` is the keyed function. The proof of [PS10, Theorem 168.2] replaces `f_k` by other
functions; this file states the IND experiment's oracles with `f` an arbitrary function
`{0,1}^n → {0,1}^n`, on bit-string oracles of arbitrary lengths (`bitSpec ins outs`; oracle `0` is
`Enc`, `1` is `Dec`, `2` is `Challenge`), with ciphertexts read at width `d`.

* `fImpl … f` samples a fresh `r` for every encryption and for the first challenge (the
  experiment of Definition 168.1 with `f` in place of `f_k`).
* `eImpl … f T` takes the `j`-th fresh `r` from the tape `T j` given in advance (the run of the
  reduction, whose seed holds the tapes); the state counts the tapes used.

Drawing `κ` tapes uniformly gives the distribution of `fImpl` for every computation with at most
`κ` queries (`expect_eImpl`); the proof resamples one tape at a time
(`AdaptiveCPA.expect_sample_update`), using that the run from the counter `j` ignores the tapes
below `j` (`simulate_eImpl_congr`).

## Main definitions

* `PRFGame.ctOf`: the ciphertext `⟨r, m ⊕ y⟩`.
* `PRFGame.decAns`: the decryption answer `⟨1, v ⊕ f(x)⟩` on a well-formed `⟨x, v⟩`, else `⊥`.
* `PRFGame.fImpl`, `PRFGame.eImpl`: the oracles with fresh and with given nonces.

## Main results

* `PRFGame.fImpl_enc`, `_dec`, `_challenge_none`, `_challenge_some` and the same for `eImpl`.
* `PRFGame.simulate_eImpl_congr`: the run from counter `j` ignores the tapes below `j`.
* `PRFGame.expect_eImpl`: tapes in advance have the distribution of fresh nonces.
* `PRFGame.expect_simulate_congr`: implementations with the same laws simulate alike.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 99.1 and Theorem 168.2 (book pp. 99, 168).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! ### Ciphertexts and decryption answers -/

/-- **The ciphertext** `⟨r, m ⊕ y⟩` of the message list `m` with nonce `r` and pad `y`. -/
def ctOf {n : ℕ} (r : Fin n → Bool) (m : List Bool) (y : Fin n → Bool) : List Bool :=
  pairEncode (List.ofFn r) (List.zipWith xor m (List.ofFn y))

/-- `ctOf r m y = pairEncode ⟦r⟧ (m ⊕ ⟦y⟧)`. -/
theorem ctOf_eq {n : ℕ} (r : Fin n → Bool) (m : List Bool) (y : Fin n → Bool) :
    ctOf r m y = pairEncode (List.ofFn r) (List.zipWith xor m (List.ofFn y)) :=
  rfl

/-- A ciphertext of an `n`-bit message has `3n + 2` bits: `|ctOf r m y| = 3n + 2` when
`|m| = n`. -/
theorem length_ctOf {n : ℕ} (r : Fin n → Bool) {m : List Bool} (hm : m.length = n)
    (y : Fin n → Bool) : (ctOf r m y).length = 3 * n + 2 := by
  rw [ctOf_eq, length_pairEncode, List.length_ofFn, List.length_zipWith, List.length_ofFn, hm,
    Nat.min_self]
  omega

/-- **Well-formedness of a decryption query** `w`: both components of the pair have `n` bits,
`decWF n w = (|pairFstD w| = n && |pairSndD w| = n)`. -/
def decWF (n : ℕ) (w : List Bool) : Bool :=
  decide ((pairFstD w).length = n) && decide ((pairSndD w).length = n)

/-- `decWF n w = (decide (|pairFstD w| = n) && decide (|pairSndD w| = n))`. -/
theorem decWF_eq (n : ℕ) (w : List Bool) :
    decWF n w = (decide ((pairFstD w).length = n) && decide ((pairSndD w).length = n)) :=
  rfl

/-- **The decryption answer** with pad function `f`, when the oracle is open (`op`): on a
well-formed `w = ⟨x, v⟩` it is `true :: (v ⊕ f(x))`, and otherwise the empty list (read as `⊥`,
all-`false`). -/
def decAns (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (op : Bool) (w : List Bool) :
    List Bool :=
  if op && decWF n w then
    true :: List.zipWith xor (pairSndD w) (List.ofFn (f (padFin n (pairFstD w))))
  else []

/-- `decAns n f op w = if op && decWF n w then true :: (pairSndD w ⊕ ⟦f (padFin n (pairFstD w))⟧)
else []`. -/
theorem decAns_eq (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (op : Bool) (w : List Bool) :
    decAns n f op w =
      if op && decWF n w then
        true :: List.zipWith xor (pairSndD w) (List.ofFn (f (padFin n (pairFstD w))))
      else [] :=
  rfl

/-! ### Simulation congruence -/

/-- **Implementations with the same laws simulate alike:** if every call of `impl₀` and `impl₁`
has the same expectation of every function `g` of the answer and the new state, the simulations
of every computation have the same expectation of every function `G` of the output and the final
state: `𝔼[G] (simulate impl₀ c s) = 𝔼[G] (simulate impl₁ c s)`.

**Proof sketch.** Induction on `c`; at a query, both sides are the expectation over the call of the
continuation's expectation (`simulate_query`, `expect_bind`), equal by induction and the
hypothesis. -/
theorem expect_simulate_congr {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    (impl₀ impl₁ : QueryImpl spec σ unifSpec)
    (h : ∀ i x s (g : spec.rng i × σ → ℝ), expect (impl₀ i x s) g = expect (impl₁ i x s) g)
    (c : OracleComp spec α) (s : σ) (G : α × σ → ℝ) :
    expect (simulate impl₀ c s) G = expect (simulate impl₁ c s) G := by
  induction c generalizing s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    rw [simulate_query, simulate_query, expect_bind, expect_bind, h]
    exact congrArg _ (funext fun p => ih p.1 p.2)

/-! ### The oracles with fresh nonces -/

section Oracles

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (atk : Attack) (b : Bool)
  (f : (Fin n → Bool) → (Fin n → Bool))

/-- **The oracles of `IND_b` with pad function `f`** and fresh nonces: `Enc` on `m` samples `r` and
answers `⟨r, m ⊕ f(r)⟩`; `Dec` answers `decAns` when `decOpen atk` lets it; `Challenge` on
`⟨m₀, m₁⟩` the first time samples `r`, answers `c = ⟨r, m_b ⊕ f(r)⟩` and records it, and later
repeats `c`. Lengths are adjusted with `padFin`; the state is the recorded challenge. These are the
oracles of `IND_b` under CPA and CCA1 (`expect_indImpl_fImpl`); under CCA2 `Dec` here does not
refuse the challenge ciphertext. -/
noncomputable def fImpl : QueryImpl (bitSpec ins outs) (Option (Fin d → Bool)) unifSpec
  | 0, m, s => (ProbComp.sample (Fin n → Bool)).bind fun r =>
      .pure (padFin _ (ctOf r (List.ofFn m) (f r)), s)
  | 1, c, s => .pure (padFin _ (decAns n f (FixedLengthScheme.decOpen atk s.isSome)
      (List.ofFn c)), s)
  | 2, mm, s =>
    match s with
    | some c => .pure (padFin _ (List.ofFn c), some c)
    | none => (ProbComp.sample (Fin n → Bool)).bind fun r =>
        .pure (padFin _ (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f r)),
          some (padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f r))))

/-- An encryption query samples a nonce `r` and answers `⟨r, m ⊕ f(r)⟩`. -/
theorem fImpl_enc (m : Fin (ins 0) → Bool) (s : Option (Fin d → Bool)) :
    fImpl ins outs d n atk b f 0 m s = (ProbComp.sample (Fin n → Bool)).bind fun r =>
      .pure (padFin _ (ctOf r (List.ofFn m) (f r)), s) :=
  rfl

/-- A decryption query is answered by `decAns`, open as `decOpen atk` says, and keeps the state. -/
theorem fImpl_dec (c : Fin (ins 1) → Bool) (s : Option (Fin d → Bool)) :
    fImpl ins outs d n atk b f 1 c s =
      .pure (padFin _ (decAns n f (FixedLengthScheme.decOpen atk s.isSome) (List.ofFn c)), s) :=
  rfl

/-- The first challenge `mm` samples `r`, answers `c = ⟨r, m_b ⊕ f(r)⟩` and records it. -/
theorem fImpl_challenge_none (mm : Fin (ins 2) → Bool) :
    fImpl ins outs d n atk b f 2 mm none = (ProbComp.sample (Fin n → Bool)).bind fun r =>
      .pure (padFin _ (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f r)),
        some (padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f r)))) :=
  rfl

/-- A later challenge repeats the recorded ciphertext `c`. -/
theorem fImpl_challenge_some (mm : Fin (ins 2) → Bool) (c : Fin d → Bool) :
    fImpl ins outs d n atk b f 2 mm (some c) = .pure (padFin _ (List.ofFn c), some c) :=
  rfl

/-! ### The oracles with nonces given in advance -/

/-- **The oracles of `IND_b` with pad function `f` and the nonces `T` in advance:** as `fImpl`, but
the `j`-th fresh nonce (an encryption or the first challenge) is `T j`; the state is the counter
`j` and the recorded challenge. All answers are deterministic. -/
noncomputable def eImpl (T : ℕ → Fin n → Bool) :
    QueryImpl (bitSpec ins outs) (ℕ × Option (Fin d → Bool)) unifSpec
  | 0, m, s => .pure (padFin _ (ctOf (T s.1) (List.ofFn m) (f (T s.1))), (s.1 + 1, s.2))
  | 1, c, s => .pure (padFin _ (decAns n f (FixedLengthScheme.decOpen atk s.2.isSome)
      (List.ofFn c)), s)
  | 2, mm, s =>
    match s.2 with
    | some c => .pure (padFin _ (List.ofFn c), s)
    | none => .pure (padFin _ (ctOf (T s.1) (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f (T s.1))),
        (s.1 + 1, some (padFin d (ctOf (T s.1) (AdaptiveCPA.msgOf n b (List.ofFn mm))
          (f (T s.1))))))

variable (T : ℕ → Fin n → Bool)

/-- An encryption query uses the nonce `T j` and advances the counter `j`. -/
theorem eImpl_enc (m : Fin (ins 0) → Bool) (j : ℕ) (s : Option (Fin d → Bool)) :
    eImpl ins outs d n atk b f T 0 m (j, s) =
      .pure (padFin _ (ctOf (T j) (List.ofFn m) (f (T j))), (j + 1, s)) :=
  rfl

/-- A decryption query is answered by `decAns` and keeps the state. -/
theorem eImpl_dec (c : Fin (ins 1) → Bool) (j : ℕ) (s : Option (Fin d → Bool)) :
    eImpl ins outs d n atk b f T 1 c (j, s) =
      .pure (padFin _ (decAns n f (FixedLengthScheme.decOpen atk s.isSome) (List.ofFn c)),
        (j, s)) :=
  rfl

/-- The first challenge uses the nonce `T j`, records the ciphertext and advances the counter. -/
theorem eImpl_challenge_none (mm : Fin (ins 2) → Bool) (j : ℕ) :
    eImpl ins outs d n atk b f T 2 mm (j, none) =
      .pure (padFin _ (ctOf (T j) (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f (T j))),
        (j + 1, some (padFin d (ctOf (T j) (AdaptiveCPA.msgOf n b (List.ofFn mm)) (f (T j)))))) :=
  rfl

/-- A later challenge repeats the recorded ciphertext and keeps the state. -/
theorem eImpl_challenge_some (mm : Fin (ins 2) → Bool) (j : ℕ) (c : Fin d → Bool) :
    eImpl ins outs d n atk b f T 2 mm (j, some c) = .pure (padFin _ (List.ofFn c), (j, some c)) :=
  rfl

/-- **The run from the counter `j` ignores the tapes below `j`:** if `T m = T' m` for every
`m ≥ j`, the runs of `eImpl` with `T` and `T'` from `(j, s)` agree.

**Proof sketch.** Induction on the computation: a fresh nonce at counter `j' ≥ j` reads `T j'`
and moves to `j' + 1`; the other queries keep the counter. -/
theorem simulate_eImpl_congr (T' : ℕ → Fin n → Bool) {α : Type}
    (c : OracleComp (bitSpec ins outs) α) (j : ℕ) (s : Option (Fin d → Bool))
    (hT : ∀ m, j ≤ m → T m = T' m) :
    simulate (eImpl ins outs d n atk b f T) c (j, s) =
      simulate (eImpl ins outs d n atk b f T') c (j, s) := by
  induction c generalizing j s with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, simulate_query, eImpl_enc, eImpl_enc, OracleComp.pure_bind,
        OracleComp.pure_bind, hT j le_rfl]
      exact ih _ _ _ fun m hm => hT m (by omega)
    | 1, x, k, ih =>
      rw [simulate_query, simulate_query, eImpl_dec, eImpl_dec, OracleComp.pure_bind,
        OracleComp.pure_bind]
      exact ih _ _ _ hT
    | 2, x, k, ih =>
      cases s with
      | some c =>
        rw [simulate_query, simulate_query, eImpl_challenge_some, eImpl_challenge_some,
          OracleComp.pure_bind, OracleComp.pure_bind]
        exact ih _ _ _ hT
      | none =>
        rw [simulate_query, simulate_query, eImpl_challenge_none, eImpl_challenge_none,
          OracleComp.pure_bind, OracleComp.pure_bind, hT j le_rfl]
        exact ih _ _ _ fun m hm => hT m (by omega)

/-- **Nonces in advance have the distribution of fresh nonces:** for a computation with at most
`m` queries, a counter `j` with `j + m ≤ κ`, and every function `G` of the output,
`𝔼_{T ← ({0,1}^n)^κ} 𝔼[G (simulate (eImpl (extTape T)) c (j, s))] =
𝔼[G (simulate (fImpl) c s)]`.

**Proof sketch.** Induction on `c`, generalizing the counter, the state and the budget. A query
costs one unit, so a fresh nonce is read at a counter `j < κ`. There it reads `T j`, and the
continuation runs from `j + 1`, so it ignores `T j` (`simulate_eImpl_congr`, `extTape_update`);
`AdaptiveCPA.expect_sample_update` replaces `T j` by the fresh sample of `fImpl`. The other
queries are answered alike. -/
theorem expect_eImpl (κ : ℕ) {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α)
    (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (j : ℕ) (hj : j + m ≤ κ)
    (s : Option (Fin d → Bool)) :
    expect (ProbComp.sample (Fin κ → Fin n → Bool))
        (fun T => expect (simulate (eImpl ins outs d n atk b f (AdaptiveCPA.extTape T)) c (j, s))
          (fun p => G p.1)) =
      expect (simulate (fImpl ins outs d n atk b f) c s) (fun p => G p.1) := by
  induction c generalizing m j s with
  | pure a =>
    simp only [simulate_pure, expect_pure]
    exact expect_const _ _
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    have hjk : j < κ := by omega
    have hrest : j + 1 + (m - 1) ≤ κ := by omega
    -- a fresh nonce at counter `j`: resample the tape `j`
    have fresh : ∀ (ans : (Fin n → Bool) → (bitSpec ins outs).rng i)
        (st : (Fin n → Bool) → Option (Fin d → Bool)),
        (∀ r, expect (ProbComp.sample (Fin κ → Fin n → Bool)) (fun T =>
          expect (simulate (eImpl ins outs d n atk b f (AdaptiveCPA.extTape T)) (k (ans r))
            (j + 1, st r)) (fun p => G p.1)) =
          expect (simulate (fImpl ins outs d n atk b f) (k (ans r)) (st r)) (fun p => G p.1)) →
        expect (ProbComp.sample (Fin κ → Fin n → Bool)) (fun T =>
          expect (simulate (eImpl ins outs d n atk b f (AdaptiveCPA.extTape T))
            (k (ans (AdaptiveCPA.extTape T j))) (j + 1, st (AdaptiveCPA.extTape T j)))
              (fun p => G p.1)) =
          expect (ProbComp.sample (Fin n → Bool)) (fun r =>
            expect (simulate (fImpl ins outs d n atk b f) (k (ans r)) (st r))
              (fun p => G p.1)) := by
      intro ans st hih
      let jj : Fin κ := ⟨j, hjk⟩
      have hT : ∀ T : Fin κ → Fin n → Bool, AdaptiveCPA.extTape T j = T jj :=
        fun T => AdaptiveCPA.extTape_of_lt T hjk
      simp only [hT]
      refine (AdaptiveCPA.expect_sample_update jj (fun r T => expect (simulate
        (eImpl ins outs d n atk b f (AdaptiveCPA.extTape T)) (k (ans r)) (j + 1, st r))
          (fun p => G p.1)) ?_).trans ?_
      · intro r r' T
        refine congrArg (fun c => expect c (fun p => G p.1))
          (simulate_eImpl_congr ins outs d n atk b f _ _ _ _ _ fun m' hm' => ?_)
        exact AdaptiveCPA.extTape_update T jj r' (by
          intro h
          have : m' = j := h
          omega)
      · exact congrArg _ (funext hih)
    match i, x, k, ih, hk with
    | 0, x, k, ih, hk =>
      rw [simulate_query, fImpl_enc, OracleComp.bind_assoc, expect_bind]
      simp only [simulate_query, eImpl_enc, OracleComp.pure_bind]
      exact fresh (fun r => padFin _ (ctOf r (List.ofFn x) (f r))) (fun _ => s)
        fun r => ih _ (m - 1) (hk _) (j + 1) hrest s
    | 1, x, k, ih, hk =>
      simp only [simulate_query, eImpl_dec, fImpl_dec, OracleComp.pure_bind]
      exact ih _ (m - 1) (hk _) j (by omega) s
    | 2, x, k, ih, hk =>
      cases s with
      | some c =>
        simp only [simulate_query, eImpl_challenge_some, fImpl_challenge_some,
          OracleComp.pure_bind]
        exact ih _ (m - 1) (hk _) j (by omega) (some c)
      | none =>
        rw [simulate_query, fImpl_challenge_none, OracleComp.bind_assoc, expect_bind]
        simp only [simulate_query, eImpl_challenge_none, OracleComp.pure_bind]
        exact fresh (fun r => padFin _ (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn x)) (f r)))
          (fun r => some (padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn x)) (f r))))
          fun r => ih _ (m - 1) (hk _) (j + 1) hrest _

end Oracles

end TCSlib.Cryptography.Composability.PRFGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Handler.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The handler of the PRF reduction for the §3.9 scheme

The first step of [PS10, Theorem 168.2] replaces `f_k` by a random function: a reduction with
oracle access to a function `f` runs the IND adversary and answers its queries with `f` in place
of `f_k`. This file builds that reduction as a `Games.InteractiveHandler` (`pkHandler`) with one
outer oracle (the function), so that T2 (`Games.exists_interactiveHandlerMachine`) and T4
(`Games.exists_toOracleAdversary_of_bitCodec`) make it a next-query machine.

The handler's seed is `q(n)` nonce tapes of `n` bits (`pkTapes`), one per fresh nonce; its state
counts the tapes used and records the challenge (`pkState`).
- `Enc` on `m`: ask `f` at the next tape `r`, answer `⟨r, m ⊕ f(r)⟩`, count.
- `Dec` on `w`: when open (`atk = CCA1` and no challenge yet) and `w = ⟨x, v⟩` is well formed, ask
  `f` at `x` and answer `⟨1, v ⊕ f(x)⟩`; otherwise answer `⊥`.
- `Challenge` on `⟨m₀, m₁⟩`: the first time, ask `f` at the next tape `r`, answer
  `c = ⟨r, m_b ⊕ f(r)⟩`, record `c` and count; later repeat `c`.
The finalization asks nothing and outputs the adversary's bit.

## Main definitions

* `PRFGame.ctP`, `pkDin`, `pkDout`, `pkStLen`: the lengths.
* `PRFGame.recBits`, `pkState`: the encoded state.
* `PRFGame.pkTapes`: the seed as nonce tapes.
* `PRFGame.pkHandler q atkBit b`: the handler.

## Main results

* `PRFGame.pkHandler_impl_enc`, `_impl_dec_open`, `_impl_dec_closed`, `_impl_challenge_some`,
  `_impl_challenge_none`: its answers on encoded states.
* `PRFGame.pkHandler_finish`, `pkHandler_init_eq`: the finalization and the initial state.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 99.1 and Theorem 168.2 (book pp. 99, 168).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Lengths and states -/

/-- The ciphertext length `3n + 2`. -/
def ctP : PolyExpr := .add (.mul (.const 3) .var) (.const 2)

/-- `ctP.eval n = 3n + 2`. -/
theorem ctP_eval (n : ℕ) : ctP.eval n = 3 * n + 2 := by
  rw [ctP, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- The query lengths: `n`-bit messages to `Enc`, `(3n + 2)`-bit ciphertexts to `Dec`, `2n`-bit
challenge queries. -/
def pkDin : Fin 3 → PolyExpr
  | 0 => .var
  | 1 => ctP
  | 2 => .add .var .var

/-- `Enc` queries have `n` bits: `pkDin 0 = var`. -/
theorem pkDin_zero : pkDin 0 = .var := rfl

/-- `Dec` queries have `3n + 2` bits: `pkDin 1 = ctP`. -/
theorem pkDin_one : pkDin 1 = ctP := rfl

/-- Challenge queries have `2n` bits: `pkDin 2 = var + var`. -/
theorem pkDin_two : pkDin 2 = .add .var .var := rfl

/-- The answer lengths: ciphertexts, `(n + 1)`-bit decryption answers, ciphertexts. -/
def pkDout : Fin 3 → PolyExpr
  | 0 => ctP
  | 1 => .add .var (.const 1)
  | 2 => ctP

/-- `Enc` answers are ciphertexts: `pkDout 0 = ctP`. -/
theorem pkDout_zero : pkDout 0 = ctP := rfl

/-- `Dec` answers have `n + 1` bits: `pkDout 1 = var + 1`. -/
theorem pkDout_one : pkDout 1 = .add .var (.const 1) := rfl

/-- Challenge answers are ciphertexts: `pkDout 2 = ctP`. -/
theorem pkDout_two : pkDout 2 = ctP := rfl

/-- The outer oracle: `n`-bit queries and answers. -/
abbrev pkOut : Fin 1 → PolyExpr := fun _ => .var

/-- `pkOut j = var`. -/
theorem pkOut_eq (j : Fin 1) : pkOut j = .var := rfl

variable (q : PolyExpr)

/-- The state length `2q + 3 + (3n + 2)`. -/
def pkStLen : PolyExpr := .add (.add (.mul (.const 2) q) (.const 3)) ctP

/-- `pkStLen q = 2q + 3 + ctP`. -/
theorem pkStLen_eq : pkStLen q = .add (.add (.mul (.const 2) q) (.const 3)) ctP := rfl

/-- The record of the challenge: `1 :: c` once recorded, `0^{1 + ct(n)}` before. -/
def recBits (n : ℕ) : Option (Fin (ctP.eval n) → Bool) → List Bool
  | none => false :: List.replicate (ctP.eval n) false
  | some c => true :: List.ofFn c

/-- `recBits n none = 0^{1 + ct(n)}`. -/
theorem recBits_none (n : ℕ) : recBits n none = false :: List.replicate (ctP.eval n) false := rfl

/-- `recBits n (some c) = 1 :: ⟦c⟧`. -/
theorem recBits_some (n : ℕ) (c : Fin (ctP.eval n) → Bool) :
    recBits n (some c) = true :: List.ofFn c := rfl

/-- The record has `1 + ct(n)` bits. -/
theorem length_recBits (n : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    (recBits n o).length = ctP.eval n + 1 := by
  cases o with
  | none => rw [recBits_none, List.length_cons, List.length_replicate]
  | some c => rw [recBits_some, List.length_cons, List.length_ofFn]

/-- **The encoded state** after `j` fresh nonces, with the challenge record `o`:
`⟨1^j, recBits o⟩`, padded with `false` to the state length. -/
def pkState (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    Fin ((pkStLen q).eval n) → Bool :=
  padFin _ (pairEncode (List.replicate j true) (recBits n o))

/-- `pkState q n j o = padFin _ ⟨1^j, recBits n o⟩`. -/
theorem pkState_eq (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    pkState q n j o = padFin _ (pairEncode (List.replicate j true) (recBits n o)) :=
  rfl

/-- **The seed as nonce tapes:** `q(n) · n` bits as `q(n)` blocks of `n` bits. -/
def pkTapes (n : ℕ) : (Fin ((q.mul .var).eval n) → Bool) ≃ (Fin (q.eval n) → Fin n → Bool) :=
  (Equiv.arrowCongr (finCongr (by rw [PolyExpr.eval_mul, PolyExpr.eval_var]))
    (Equiv.refl Bool)).trans (EnsembleLemmas.blocks (q.eval n) n)

/-- **Bit `k` of tape `j` is bit `j·n + k` of the seed:**
`pkTapes q n ω j k = ω (finProdFinEquiv (j, k))`, read at the seed's length. -/
theorem pkTapes_apply (n : ℕ) (ω : Fin ((q.mul .var).eval n) → Bool) (j : Fin (q.eval n))
    (k : Fin n) :
    pkTapes q n ω j k = ω (Fin.cast (by rw [PolyExpr.eval_mul, PolyExpr.eval_var])
      (finProdFinEquiv (j, k))) := by
  unfold pkTapes
  rw [Equiv.trans_apply, EnsembleLemmas.blocks_apply]
  rfl

/-- **Tape `j` is the `j`-th block of the seed:** `⟦pkTapes q n ω j⟧ = (⟦ω⟧.drop (j·n)).take n`.

**Proof sketch.** Position `k` of block `j` is position `j·n + k` of `ω` (`blocks_apply`,
`finProdFinEquiv_apply_val`), which is position `k` of the dropped and truncated list. -/
theorem ofFn_pkTapes (n : ℕ) (ω : Fin ((q.mul .var).eval n) → Bool) (j : Fin (q.eval n)) :
    List.ofFn (pkTapes q n ω j) = ((List.ofFn ω).drop (j * n)).take n := by
  have hlen : (q.mul .var).eval n = q.eval n * n := by rw [PolyExpr.eval_mul, PolyExpr.eval_var]
  have hj := j.isLt
  have hle : (j : ℕ) * n + n ≤ q.eval n * n := by
    have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at this
    exact this
  refine List.ext_getElem ?_ fun k h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · have hpt : ∀ k' : Fin n, pkTapes q n ω j k' =
        ω (Fin.cast hlen.symm (finProdFinEquiv (j, k'))) := fun k' => pkTapes_apply q n ω j k'
    simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop, hpt]
    congr 1
    refine Fin.ext ?_
    rw [Fin.coe_cast, finProdFinEquiv_apply_val]
    show k + n * j = j * n + k
    rw [Nat.mul_comm]
    omega

/-! ### Strings -/

/-- `⟦padFin k a⟧ = padL k a`. -/
private theorem ofFn_padFin_eq_padL (k : ℕ) (a : List Bool) :
    List.ofFn (padFin k a) = EnsembleLemmas.padL k a := by
  rw [EnsembleLemmas.padL_eq, ofFn_padFin_eq_take]

/-- The fields of an encoded state with `j ≤ q(n)`: the count `1^j`, the flag and the record. -/
private theorem fields_pkState (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool))
    (hj : j ≤ q.eval n) :
    pairFstD (List.ofFn (pkState q n j o)) = List.replicate j true ∧
      (pairSndD (List.ofFn (pkState q n j o))).headD false = o.isSome ∧
      ((pairSndD (List.ofFn (pkState q n j o))).drop 1).take (ctP.eval n) =
        (recBits n o).drop 1 := by
  have hlen : (pairEncode (List.replicate j true) (recBits n o)).length ≤ (pkStLen q).eval n := by
    rw [length_pairEncode, List.length_replicate, length_recBits, pkStLen_eq, PolyExpr.eval_add,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const]
    omega
  rw [pkState_eq, Collection.ofFn_padFin_of_le hlen, ← GGMRed.pairEncode_append_right]
  rw [pairFstD_pairEncode, pairSndD_pairEncode]
  refine ⟨rfl, ?_, ?_⟩
  · cases o <;> rfl
  · cases o with
    | none =>
      rw [recBits_none, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_replicate]
    | some c =>
      rw [recBits_some, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_ofFn]

/-! ### The round function -/

/-- The parameter `1^n` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
private def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
/-- The seed `ω`. -/
private def rW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))
/-- The state `s`. -/
private def rS (w : List Bool) : List Bool := pairFstD (pairSndD w)
/-- The oracle index `1^i`. -/
private def rI (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
/-- The query `x`. -/
private def rX (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
/-- The outer log `L` of the call. -/
private def rL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
/-- The count `1^j` of the state. -/
private def rCnt (w : List Bool) : List Bool := pairFstD (rS w)
/-- The challenge flag of the state. -/
private def rFlag (w : List Bool) : Bool := (pairSndD (rS w)).headD false
/-- The recorded challenge of the state. -/
private def rRec (w : List Bool) : List Bool :=
  ((pairSndD (rS w)).drop 1).take (ctP.eval (rU w).length)
/-- The outer answer recorded in the log `⟨⟨[], ⟨x, y⟩⟩, []⟩`. -/
private def rY (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rL w)))
/-- Tape `j` of the seed. -/
private def rNonce (w : List Bool) : List Bool :=
  ((rW w).drop ((rCnt w).length * (rU w).length)).take (rU w).length
/-- The ciphertext `⟨r, m ⊕ y⟩` with the tape `r` and the outer answer `y`. -/
private def rCt (w m : List Bool) : List Bool :=
  pairEncode (rNonce w) (List.zipWith xor m (rY w))
/-- The selected challenge message `m_b`. -/
private def rMsg (b : Bool) (w : List Bool) : List Bool :=
  if b then (rX w).drop (rU w).length else (rX w).take (rU w).length
/-- Whether the decryption query `⟨x, v⟩` is well formed. -/
private def rWF (w : List Bool) : Bool :=
  decide ((pairFstD (rX w)).length = (rU w).length) &&
    decide ((pairSndD (rX w)).length = (rU w).length)
/-- The new state after a fresh nonce: count `j + 1`, record `t`. -/
private def rNew (w t : List Bool) : List Bool :=
  EnsembleLemmas.padL ((pkStLen q).eval (rU w).length) (pairEncode (true :: rCnt w) t)

/-- **One round of the handler** (see the module docstring), for the attack bit `atkBit` (`true`
for CCA1) and the challenge bit `b`. A first round asks the outer oracle; the second round, with
the answer `y` in the log, returns the answer and the new state. -/
private def pkRun (atkBit b : Bool) (w : List Bool) : List Bool :=
  if (rI w).headD false then
    if ((rI w).drop 1).headD false then
      if rFlag w then pairEncode [true] (rRec w ++ rS w)
      else if decide (rL w = []) then pairEncode [false] (pairEncode [] (rNonce w))
      else pairEncode [true] (rCt w (rMsg b w) ++ rNew q w (true :: rCt w (rMsg b w)))
    else
      if atkBit && !rFlag w && rWF w then
        if decide (rL w = []) then pairEncode [false] (pairEncode [] (pairFstD (rX w)))
        else pairEncode [true] ((true :: List.zipWith xor (pairSndD (rX w)) (rY w)) ++ rS w)
      else pairEncode [true]
        (List.replicate ((PolyExpr.add .var (.const 1)).eval (rU w).length) false ++ rS w)
  else
    if decide (rL w = []) then pairEncode [false] (pairEncode [] (rNonce w))
    else pairEncode [true] (rCt w (rX w) ++ rNew q w (rFlag w :: rRec w))

/-- The round function is polynomial-time.

**Proof sketch.** Pair projections; the tape by `unaryMulPair`, `dropPrefixByLength` and
`pairTakePoly`; the exclusive-or by `pairXor`; the well-formedness test by `lenEq_poly`; the
padded new state by `padL`; and `polyTimeComputable_ite` for the cases. -/
private theorem polyTimeComputable_pkRun (atkBit b : Bool) :
    PolyTimeComputable (pkRun q atkBit b) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hU : PolyTimeComputable rU := hF.comp hF
  have hW : PolyTimeComputable rW := hD.comp (hD.comp hF)
  have hS : PolyTimeComputable rS := hF.comp hD
  have hI : PolyTimeComputable rI := hF.comp (hF.comp (hD.comp hD))
  have hX : PolyTimeComputable rX := hD.comp (hF.comp (hD.comp hD))
  have hL : PolyTimeComputable rL := hD.comp (hD.comp hD)
  have hCnt : PolyTimeComputable rCnt := hF.comp hS
  have hT : PolyTimeComputable fun w => pairSndD (rS w) := hD.comp hS
  have hFlag : PolyTimeComputable fun w => [rFlag w] := polyTimeComputable_headD.comp hT
  have hRec : PolyTimeComputable rRec :=
    ((polyTimeComputable_pairTakePoly ctP).comp
      (hU.pairEncode (polyTimeComputable_tail.comp hT))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hY : PolyTimeComputable rY := hD.comp (hD.comp (hF.comp hL))
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((rCnt w).length * (rU w).length) true :=
    (OneWay.polyTimeComputable_unaryMulPair.comp (hCnt.pairEncode hU)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hDrop : PolyTimeComputable fun w => (rW w).drop ((rCnt w).length * (rU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
  have hNonce : PolyTimeComputable rNonce :=
    ((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hDrop)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
        PolyExpr.eval_var]; rfl
  have hXor : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
      PolyTimeComputable fun w => List.zipWith xor (m w) (rY w) := fun hm =>
    (polyTimeComputable_pairXor.comp (hm.pairEncode hY)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hCt : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
      PolyTimeComputable fun w => rCt w (m w) := fun hm => hNonce.pairEncode (hXor hm)
  have hMsg : PolyTimeComputable (rMsg b) :=
    polyTimeComputable_ite (polyTimeComputable_const [b])
      (((polyTimeComputable_pairDropPoly .var).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          PolyExpr.eval_var])
      (((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          PolyExpr.eval_var])
  have hWF : PolyTimeComputable fun w => [rWF w] :=
    polyTimeComputable_and (EffFill.lenEq_poly (hF.comp hX) hU)
      (EffFill.lenEq_poly (hD.comp hX) hU)
  have hNew : ∀ {t : List Bool → List Bool}, PolyTimeComputable t →
      PolyTimeComputable fun w => rNew q w (t w) := fun ht =>
    EnsembleLemmas.polyTimeComputable_padL (pkStLen q) hU
      (((polyTimeComputable_const [true]).append hCnt).pairEncode ht)
  have hRet : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [true] (f w) := fun hf =>
    (polyTimeComputable_const [true]).pairEncode hf
  have hQry : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [false] (pairEncode [] (f w)) := fun hf =>
    (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hf)
  have cNil : PolyTimeComputable fun w => [decide (rL w = [])] := polyTimeComputable_isNil.comp hL
  have cOpen : PolyTimeComputable fun w => [atkBit && !rFlag w && rWF w] :=
    polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_const [atkBit])
      (polyTimeComputable_not hFlag)) hWF
  have hZeros : PolyTimeComputable fun w =>
      List.replicate ((PolyExpr.add .var (.const 1)).eval (rU w).length) false :=
    EnsembleLemmas.polyTimeComputable_zeros _ hU
  have hChal := polyTimeComputable_ite hFlag (hRet (hRec.append hS))
    (polyTimeComputable_ite cNil (hQry hNonce)
      (hRet ((hCt hMsg).append (hNew ((polyTimeComputable_const [true]).append (hCt hMsg))))))
  have hDec := polyTimeComputable_ite cOpen
    (polyTimeComputable_ite cNil (hQry (hF.comp hX))
      (hRet (((polyTimeComputable_const [true]).append (hXor (hD.comp hX))).append hS)))
    (hRet (hZeros.append hS))
  have hKeep : PolyTimeComputable fun w => rFlag w :: rRec w :=
    (hFlag.append hRec).congr fun _ => rfl
  have hEnc := polyTimeComputable_ite cNil (hQry hNonce) (hRet ((hCt hX).append (hNew hKeep)))
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hI)
    (polyTimeComputable_ite (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hI))
      hChal hDec) hEnc

/-- The finalization's round: output `A`'s bit, `⟨[true], a⟩` on `⟨ctx, ⟨s, ⟨a, L⟩⟩⟩`. -/
private def pkFin (w : List Bool) : List Bool :=
  pairEncode [true] (pairFstD (pairSndD (pairSndD w)))

/-- The finalization's round is polynomial-time. -/
private theorem polyTimeComputable_pkFin : PolyTimeComputable pkFin :=
  (polyTimeComputable_const [true]).pairEncode
    (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-! ### The handler -/

/-- **The handler of the PRF reduction** for the budget `q`, the attack bit `atkBit` (`true` for
CCA1, `false` for CPA) and the challenge bit `b`: state `pkState j o` (initially `j = 0` and no
record), seed `q · n` bits (the tapes `pkTapes`), one outer call per inner query, the adversary
run on the reduction input (ignored), and the finalization outputting the adversary's bit. -/
noncomputable def pkHandler (atkBit b : Bool) :
    InteractiveHandler 3 pkDin pkDout 1 pkOut pkOut where
  stateLen := pkStLen q
  seedLen := q.mul .var
  perCall := .const 1
  init n := pkState q n 0 none
  run := pkRun q atkBit b
  poly := polyTimeComputable_pkRun q atkBit b
  advIn ctx := pairFstD (pairSndD ctx)
  advIn_poly := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  outLen := .const 1
  finCall := .const 0
  finRun := pkFin
  finRun_poly := polyTimeComputable_pkFin

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init outLen finCall]
  pkHandler

/-- The handler's initial state is the empty count and no record:
`(pkHandler q atkBit b).init n = pkState q n 0 none`. -/
theorem pkHandler_init_eq (atkBit b : Bool) (n : ℕ) :
    (pkHandler q atkBit b).init n = pkState q n 0 none :=
  rfl

/-- The handler's seed as nonce tapes (`pkTapes`), at the handler's seed type. -/
def pkSeedTapes (atkBit b : Bool) (n : ℕ) :
    (Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool) ≃ (Fin (q.eval n) → Fin n → Bool) :=
  pkTapes q n

/-- The encoded state at the handler's state type: `pkHState q atkBit b n j o = pkState q n j o`. -/
def pkHState (atkBit b : Bool) (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    Fin ((pkHandler q atkBit b).stateLen.eval n) → Bool :=
  pkState q n j o

/-- `pkHState q atkBit b n j o = pkState q n j o`. -/
theorem pkHState_eq (atkBit b : Bool) (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    pkHState q atkBit b n j o = pkState q n j o :=
  rfl

/-- The initial state is the encoded `(0, none)`: `(pkHandler q atkBit b).init n =
pkHState q atkBit b n 0 none`. -/
theorem pkHandler_init_hstate (atkBit b : Bool) (n : ℕ) :
    (pkHandler q atkBit b).init n = pkHState q atkBit b n 0 none :=
  rfl

/-- `pkSeedTapes q atkBit b n = pkTapes q n`. -/
theorem pkSeedTapes_eq (atkBit b : Bool) (n : ℕ) : pkSeedTapes q atkBit b n = pkTapes q n :=
  rfl

/-- The finalization outputs the adversary's bit and asks nothing:
`(pkHandler q atkBit b).finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
theorem pkHandler_finish (atkBit b : Bool) (n : ℕ) (z : List Bool)
    (ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool)
    (s : Fin ((pkHandler q atkBit b).stateLen.eval n) → Bool)
    (a : Fin ((PolyExpr.const 1).eval n) → Bool) :
    (pkHandler q atkBit b).finish n z ω s a =
      .pure (padFin ((pkHandler q atkBit b).outLen.eval n) (List.ofFn a)) := by
  rw [InteractiveHandler.finish_eq]
  have h0 : (pkHandler q atkBit b).finCall.eval n = 0 := by
    rw [pkHandler_finCall, PolyExpr.eval_const]
  rw [h0]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ (pkFin _) = _
  rw [pkFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
  have hw : List.ofFn (padFin ((pkHandler q atkBit b).outLen.eval n) (List.ofFn a)) =
      List.ofFn a :=
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, pkHandler_outLen])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### Answers of the handler -/

section Answers

variable (atkBit b : Bool) (n : ℕ) (z : List Bool)
  (ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool)

/-- A call whose first round returns `y ‖ s'` is answered `y` with new state `s'`. -/
private theorem impl_of_ret {i : Fin 3} (x : Fin ((pkDin i).eval n) → Bool)
    (s : Fin ((pkStLen q).eval n) → Bool) (y : Fin ((pkDout i).eval n) → Bool)
    (s' : Fin ((pkStLen q).eval n) → Bool)
    (h : pkRun q atkBit b (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x) []) = pairEncode [true] (List.ofFn y ++ List.ofFn s')) :
    (pkHandler q atkBit b).impl n z ω i x s = .pure (y, s') := by
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, pkHandler_perCall,
    PolyExpr.eval_const]
  rw [buildComp_succ_of_ret (a := Fin.append y s') (by
    show decodeBitMove _ _ _ (pkRun q atkBit b _) = _
    rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
    exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind]
  congr 2
  · funext j
    exact Fin.append_left y s' j
  · funext j
    exact Fin.append_right y s' j

/-- The outer log after one outer query `x'` answered `y`. -/
private theorem encodeLog_one (x' y : Fin ((pkOut 0).eval n) → Bool) :
    (bitCodec (fun j => (pkOut j).eval n) (fun j => (pkOut j).eval n) 0).encodeLog
        ([] ++ [⟨0, x', y⟩]) =
      pairEncode (pairEncode [] (pairEncode (List.ofFn x') (List.ofFn y))) [] := by
  rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
    bitCodec_encodeEntry]
  rfl

/-- A call whose first round asks `x'` of the outer oracle, and whose second round, with the
answer `y` in the log, returns `ans y ‖ s' y`, is the query `x'` followed by `(ans y, s' y)`. -/
private theorem impl_of_query {i : Fin 3} (x : Fin ((pkDin i).eval n) → Bool)
    (s : Fin ((pkStLen q).eval n) → Bool) (x' : Fin ((pkOut 0).eval n) → Bool)
    (ans : (Fin ((pkOut 0).eval n) → Bool) → Fin ((pkDout i).eval n) → Bool)
    (s' : (Fin ((pkOut 0).eval n) → Bool) → Fin ((pkStLen q).eval n) → Bool)
    (h1 : pkRun q atkBit b (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x) []) = pairEncode [false] (pairEncode [] (List.ofFn x')))
    (h2 : ∀ y, pkRun q atkBit b (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x) (pairEncode (pairEncode [] (pairEncode (List.ofFn x') (List.ofFn y))) [])) =
        pairEncode [true] (List.ofFn (ans y) ++ List.ofFn (s' y))) :
    (pkHandler q atkBit b).impl n z ω i x s =
      .query 0 x' fun y => .pure (ans y, s' y) := by
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, pkHandler_perCall,
    PolyExpr.eval_const]
  rw [buildComp_succ_of_query (i := 0) (x := x') (by
    show decodeBitMove _ _ _ (pkRun q atkBit b _) = _
    rw [MachineCodec.encodeLog_nil, h1]
    exact decodeBitMove_query (fun j => (pkOut j).eval n) (fun j => (pkOut j).eval n) _ 0 x'),
    OracleComp.query_bind]
  congr 1
  funext y
  rw [buildComp_zero_of_ret (a := Fin.append (ans y) (s' y)) (by
    show decodeBitMove _ _ _ (pkRun q atkBit b _) = _
    rw [encodeLog_one, h2, ← List.ofFn_fin_append]
    exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind]
  congr 2
  · funext k
    exact Fin.append_left (ans y) (s' y) k
  · funext k
    exact Fin.append_right (ans y) (s' y) k

/-- The round input of a call, field by field, on an encoded state with `j ≤ q(n)`. -/
private theorem fields_input {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n) :
    let w := InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o)) i x L
    rU w = List.replicate n true ∧ rW w = List.ofFn ω ∧
      rS w = List.ofFn (pkState q n j o) ∧ rI w = List.replicate i true ∧ rX w = x ∧
      rL w = L ∧ rCnt w = List.replicate j true ∧ rFlag w = o.isSome ∧
      rRec w = (recBits n o).drop 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := fields_pkState q n j o hj
  simp only [InteractiveHandler.input_eq, rU, rW, rS, rI, rX, rL, rCnt, rFlag, rRec,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, h₁, h₂, h₃, and_self]

/-- The tape at the count `j < q(n)` is the `j`-th block of the seed. -/
private theorem rNonce_fields {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j < q.eval n) :
    rNonce (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o)) i x L) =
      List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) := by
  obtain ⟨hU, hW, -, -, -, -, hCnt, -, -⟩ := fields_input q atkBit b n z ω (i := i) x L j o hj.le
  rw [rNonce, hU, hW, hCnt, List.length_replicate, List.length_replicate, pkSeedTapes_eq]
  exact (ofFn_pkTapes q n ω ⟨j, hj⟩).symm

/-- The new state after a fresh nonce from `pkState j o`, with record `t`. -/
private theorem rNew_fields {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o o' : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n) :
    rNew q (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o)) i x L)
        (recBits n o') = List.ofFn (pkState q n (j + 1) o') := by
  obtain ⟨hU, -, -, -, -, -, hCnt, -, -⟩ := fields_input q atkBit b n z ω (i := i) x L j o hj
  rw [rNew, hU, hCnt, List.length_replicate, pkState_eq, ofFn_padFin_eq_padL, List.replicate_succ]

/-- The flag and the record rebuild the record bits: `rFlag :: rRec = recBits o`. -/
private theorem recBits_fields (o : Option (Fin (ctP.eval n) → Bool)) :
    o.isSome :: (recBits n o).drop 1 = recBits n o := by
  cases o <;> rfl

/-- The outer answer recorded in a one-entry log. -/
private theorem rY_one (w : List Bool) (x' y : List Bool)
    (hL : rL w = pairEncode (pairEncode [] (pairEncode x' y)) []) : rY w = y := by
  rw [rY, hL, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]

/-- The index word of oracle `1`. -/
private theorem replicate_one : List.replicate ((1 : Fin 3) : ℕ) true = [true] := rfl

/-- The index word of oracle `2`. -/
private theorem replicate_two : List.replicate ((2 : Fin 3) : ℕ) true = [true, true] := rfl

/-- The index word of oracle `0`. -/
private theorem replicate_zero' : List.replicate ((0 : Fin 3) : ℕ) true = [] := rfl

/-- A one-entry log is not empty. -/
private theorem log_ne_nil (x' y : List Bool) :
    decide (pairEncode (pairEncode [] (pairEncode x' y)) [] = []) = false :=
  decide_eq_false (pairEncode_ne_nil _ _)

/-- **Encryption with the next tape:** from `pkState j o` with `j < q(n)`, the query `m` asks the
outer oracle at the tape `r = T_j`, and its answer `y` gives the ciphertext `⟨r, m ⊕ y⟩` and the
state `pkState (j + 1) o`.

**Proof sketch.** Read the round input field by field (`fields_input`); the first round, with an
empty log, asks the outer oracle at the tape `T_j` (`rNonce_fields`); the second, with the answer
`y` in the log (`rY_one`), returns `⟨T_j, m ⊕ y⟩` and the state with count `j + 1`
(`rNew_fields`); `impl_of_query` assembles the two rounds. -/
theorem pkHandler_impl_enc (x : Fin ((pkDin 0).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j < q.eval n) :
    (pkHandler q atkBit b).impl n z ω 0 x (pkState q n j o) =
      .query 0 (padFin _ (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) fun y =>
        .pure (padFin _ (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (List.ofFn x)
          (padFin n (List.ofFn y))), pkState q n (j + 1) o) := by
  have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
  have hT : List.ofFn (padFin ((pkOut 0).eval n)
      (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) =
      List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) :=
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
  refine impl_of_query q atkBit b n z ω x _ _ _ _ ?_ ?_
  · obtain ⟨-, -, -, hI, -, hL, -, -, -⟩ :=
      fields_input q atkBit b n z ω (i := 0) (List.ofFn x) [] j o hj.le
    rw [pkRun, hI, hL, hT, rNonce_fields q atkBit b n z ω (i := 0) _ _ j o hj]
    rfl
  · intro y
    obtain ⟨-, -, -, hI, hX, hL, -, hFlag, hRec⟩ :=
      fields_input q atkBit b n z ω (i := 0) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)))) (List.ofFn y))) []) j o hj.le
    have hY := rY_one _ _ _ hL
    have hy : List.ofFn (padFin n (List.ofFn y)) = List.ofFn y :=
      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
    have hct : List.ofFn (padFin ((pkDout 0).eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
        (List.ofFn x) (padFin n (List.ofFn y)))) =
        ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (List.ofFn x) (padFin n (List.ofFn y)) :=
      GGMRed.ofFn_padFin_of_length (by
        rw [length_ctOf _ (by rw [List.length_ofFn, pkDin_zero, PolyExpr.eval_var]), pkDout_zero,
          ctP_eval])
    rw [pkRun, hI, replicate_zero', List.headD_nil, if_neg Bool.false_ne_true, hL, log_ne_nil,
      if_neg Bool.false_ne_true, hct, rCt, rNonce_fields q atkBit b n z ω (i := 0) _ _ j o hj,
      hX, hY, hFlag, hRec, recBits_fields, rNew_fields q atkBit b n z ω (i := 0) _ _ j o o hj.le,
      ctOf_eq, hy]

/-- **Open decryption:** if the oracle is open (`atkBit`, no record) and `w = ⟦x⟧ = ⟨x₀, v⟩` is
well formed, the query asks the outer oracle at `x₀`, and its answer `y` gives `⟨1, v ⊕ y⟩`; the
state is kept.

**Proof sketch.** As for `pkHandler_impl_enc`: the open test reads `atkBit`, the flag and the
well-formedness of `⟦x⟧` (`fields_input`); the first round asks the outer oracle at `x₀`, the second
returns `⟨1, v ⊕ y⟩` with the state unchanged (`impl_of_query`). -/
theorem pkHandler_impl_dec_open (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n)
    (hop : (atkBit && !o.isSome && decWF n (List.ofFn x)) = true) :
    (pkHandler q atkBit b).impl n z ω 1 x (pkState q n j o) =
      .query 0 (padFin _ (pairFstD (List.ofFn x))) fun y =>
        .pure (padFin _ (true :: List.zipWith xor (pairSndD (List.ofFn x)) (List.ofFn y)),
          pkState q n j o) := by
  have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
  have hwf : decWF n (List.ofFn x) = true := by
    simp only [Bool.and_eq_true] at hop
    exact hop.2
  rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf
  have hx0 : List.ofFn (padFin ((pkOut 0).eval n) (pairFstD (List.ofFn x))) =
      pairFstD (List.ofFn x) := GGMRed.ofFn_padFin_of_length (by rw [hwf.1, hn])
  have hc : ((1 : Fin 3) : ℕ) = 1 := rfl
  refine impl_of_query q atkBit b n z ω x _ _ _ _ ?_ ?_
  · obtain ⟨hU, -, -, hI, hX, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 1) (List.ofFn x) [] j o hj
    have hWF : rWF (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o))
        (1 : Fin 3)
        (List.ofFn x) []) = decWF n (List.ofFn x) := by
      rw [rWF, hU, hX, List.length_replicate, decWF_eq]
    rw [pkRun, hI, replicate_one, hFlag, hWF, hop, hL, hX, hx0]
    rfl
  · intro y
    obtain ⟨hU, -, hS, hI, hX, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 1) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (pairFstD (List.ofFn x)))) (List.ofFn y))) []) j o hj
    have hWF : rWF (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o))
        (1 : Fin 3)
        (List.ofFn x) (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (pairFstD (List.ofFn x)))) (List.ofFn y))) [])) = decWF n (List.ofFn x) := by
      rw [rWF, hU, hX, List.length_replicate, decWF_eq]
    have hY := rY_one _ _ _ hL
    have hans : List.ofFn (padFin ((pkDout 1).eval n)
        (true :: List.zipWith xor (pairSndD (List.ofFn x)) (List.ofFn y))) =
        true :: List.zipWith xor (pairSndD (List.ofFn x)) (List.ofFn y) :=
      GGMRed.ofFn_padFin_of_length (by
        rw [List.length_cons, List.length_zipWith, List.length_ofFn, hwf.2, hn, Nat.min_self,
          pkDout_one, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const])
    rw [pkRun, hI, replicate_one, hFlag, hWF, hop, hL, log_ne_nil, if_neg Bool.false_ne_true,
      hans, hS, hX, hY]
    rfl

/-- **Closed decryption:** if the oracle is closed (CPA, or a record exists) or the query is not
well formed, the answer is `⊥` (all-`false`) and the state is kept. -/
theorem pkHandler_impl_dec_closed (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n)
    (hcl : (atkBit && !o.isSome && decWF n (List.ofFn x)) = false) :
    (pkHandler q atkBit b).impl n z ω 1 x (pkState q n j o)
        = .pure (zeroBits _, pkState q n j o) := by
  refine impl_of_ret q atkBit b n z ω x _ _ _ ?_
  obtain ⟨hU, -, hS, hI, hX, -, -, hFlag, -⟩ :=
    fields_input q atkBit b n z ω (i := 1) (List.ofFn x) [] j o hj
  have hWF : rWF (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o))
      (1 : Fin 3)
      (List.ofFn x) []) = decWF n (List.ofFn x) := by
    rw [rWF, hU, hX, List.length_replicate, decWF_eq]
  rw [pkRun, hI, replicate_one, hFlag, hWF, hcl, hU, hS, List.length_replicate, ofFn_zeroBits,
    pkDout_one]
  rfl

/-- **A recorded challenge is repeated:** from `pkState j (some c)`, a challenge is answered `c` and
the state is kept. -/
theorem pkHandler_impl_challenge_some (x : Fin ((pkDin 2).eval n) → Bool) (j : ℕ)
    (c : Fin (ctP.eval n) → Bool) (hj : j ≤ q.eval n) :
    (pkHandler q atkBit b).impl n z ω 2 x (pkState q n j (some c)) =
      .pure (padFin _ (List.ofFn c), pkState q n j (some c)) := by
  refine impl_of_ret q atkBit b n z ω x _ _ _ ?_
  obtain ⟨-, -, hS, hI, -, -, -, hFlag, hRec⟩ :=
    fields_input q atkBit b n z ω (i := 2) (List.ofFn x) [] j (some c) hj
  have hc : List.ofFn (padFin ((pkDout 2).eval n) (List.ofFn c)) = List.ofFn c :=
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, pkDout_two])
  rw [pkRun, hI, replicate_two, hFlag, hRec, hS, hc]
  rfl

/-- **The first challenge with the next tape:** from `pkState j none` with `j < q(n)`, the
challenge `⟨m₀, m₁⟩` asks the outer oracle at the tape `r = T_j`, and its answer `y` gives the
ciphertext `c = ⟨r, m_b ⊕ y⟩`, recorded in the state `pkState (j + 1) (some c)`.

**Proof sketch.** As for `pkHandler_impl_enc`, with the selected half `m_b` (`rMsg`, `msgOf_eq`)
and the new record `recBits (some c)` written into the state (`rNew_fields`). -/
theorem pkHandler_impl_challenge_none (x : Fin ((pkDin 2).eval n) → Bool) (j : ℕ)
    (hj : j < q.eval n) :
    (pkHandler q atkBit b).impl n z ω 2 x (pkState q n j none) =
      .query 0 (padFin _ (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) fun y =>
        .pure (padFin _ (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
            (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y))),
          pkState q n (j + 1) (some (padFin (ctP.eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
            (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y)))))) := by
  have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
  have hT : List.ofFn (padFin ((pkOut 0).eval n)
      (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) =
      List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) :=
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
  have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
    have hx : (List.ofFn x).length = n + n := by
      rw [List.length_ofFn, pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
    rw [AdaptiveCPA.msgOf_eq]
    cases b <;> simp [hx]
  refine impl_of_query q atkBit b n z ω x _ _ _ _ ?_ ?_
  · obtain ⟨-, -, -, hI, -, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 2) (List.ofFn x) [] j none hj.le
    rw [pkRun, hI, replicate_two, hFlag, hL, hT,
      rNonce_fields q atkBit b n z ω (i := 2) _ _ j none hj]
    rfl
  · intro y
    obtain ⟨hU, -, -, hI, hX, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 2) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)))) (List.ofFn y))) []) j none hj.le
    have hY := rY_one _ _ _ hL
    have hy : List.ofFn (padFin n (List.ofFn y)) = List.ofFn y :=
      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
    have hlen : (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (AdaptiveCPA.msgOf n b (List.ofFn x))
        (padFin n (List.ofFn y))).length = ctP.eval n := by
      rw [length_ctOf _ hmsg, ctP_eval]
    have hct : List.ofFn (padFin ((pkDout 2).eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
        (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y)))) =
        ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (AdaptiveCPA.msgOf n b (List.ofFn x))
          (padFin n (List.ofFn y)) :=
      GGMRed.ofFn_padFin_of_length (by rw [hlen, pkDout_two])
    have hrec : true :: ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
        (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y)) =
        recBits n (some (padFin (ctP.eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
          (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y))))) := by
      rw [recBits_some, GGMRed.ofFn_padFin_of_length hlen]
    have hMsg : rMsg b (InteractiveHandler.input n z (List.ofFn ω)
        (List.ofFn (pkState q n j none)) (2 : Fin 3) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)))) (List.ofFn y))) [])) =
        AdaptiveCPA.msgOf n b (List.ofFn x) := by
      rw [rMsg, hU, hX, List.length_replicate, AdaptiveCPA.msgOf_eq]
    have hctOf : ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (AdaptiveCPA.msgOf n b (List.ofFn x))
        (padFin n (List.ofFn y)) = pairEncode (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))
          (List.zipWith xor (AdaptiveCPA.msgOf n b (List.ofFn x)) (List.ofFn y)) := by
      rw [ctOf_eq, hy]
    rw [pkRun, hI, replicate_two]
    simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero, if_true]
    rw [hFlag, hL, log_ne_nil]
    simp only [Option.isSome_none, Bool.false_eq_true, if_false]
    rw [hMsg, hct, rCt, rNonce_fields q atkBit b n z ω (i := 2) _ _ j none hj, hY, ← hctOf, hrec,
      rNew_fields q atkBit b n z ω (i := 2) _ _ j none _ hj.le]

end Answers

end TCSlib.Cryptography.Composability.PRFGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Lazy.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Eager

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The experiment with a lazily sampled random function

Step 2 of [PS10, Theorem 168.2] runs the IND experiment with a random function `R` in place of
`f_k`. This file samples `R` lazily (`lazyImpl`): a table records the points asked so far, a new
point gets a fresh uniform value, and a repeated point its recorded value. The challenge's point
`r*` is not entered in the table; its value is recomputed from the recorded challenge `⟨r*, c⟩`
and messages `⟨m₀, m₁⟩` as `c ⊕ m_b` (`look`), so that the state does not depend on `b` except
through that recomputation. A flag records the bad events of step 2: `r*` was already in the
table, or a later encryption uses `r*`.

Averaging the experiment with `R` over a uniform `R` gives the lazy experiment
(`expect_lazyImpl`): at a new point, resampling `R` there (`BitwiseSim.expect_sample_update`) is
the lazy sample; the table and the record determine `R` elsewhere (`ovr`).

## Main definitions

* `PRFGame.LState`: the state (table, challenge record, flag).
* `PRFGame.rStar`, `padAt`, `look`, `ovr`: the challenge's point and pad, the lazy function's
  recorded values, and `R` overridden by them.
* `PRFGame.lazyImpl`: the lazy experiment.

## Main results

* `PRFGame.lazyImpl_enc`, `_dec_open`, `_dec_closed`, `_challenge_none`, `_challenge_some`.
* `PRFGame.expect_lazyImpl`: the random function sampled in advance is the lazy one.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (the two descriptions of a random function) and Theorem 168.2 (book pp. 95, 168).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

/-! ### The state and the recorded values -/

/-- The state of the lazy experiment: the table of asked points and values, the challenge record
`⟨m₀ ‖ m₁, c⟩` once asked, and the bad flag. -/
abbrev LState (n d : ℕ) :=
  List ((Fin n → Bool) × (Fin n → Bool)) × Option (List Bool × (Fin d → Bool)) × Bool

section State

variable {n d : ℕ}

/-- The challenge's nonce: the first component of the ciphertext `c`, read at `n` bits. -/
def rStar (c : Fin d → Bool) : Fin n → Bool := padFin n (pairFstD (List.ofFn c))

/-- `rStar c = padFin n (pairFstD ⟦c⟧)`. -/
theorem rStar_eq (c : Fin d → Bool) : rStar (n := n) c = padFin n (pairFstD (List.ofFn c)) := rfl

/-- The challenge's pad `c₂ ⊕ m_b` recomputed from the ciphertext `c = ⟨r*, c₂⟩` and the
challenge query `ml = m₀ ‖ m₁`. -/
def padAt (b : Bool) (ml : List Bool) (c : Fin d → Bool) : Fin n → Bool :=
  padFin n (List.zipWith xor (pairSndD (List.ofFn c)) (AdaptiveCPA.msgOf n b ml))

/-- `padAt b ml c = padFin n (pairSndD ⟦c⟧ ⊕ msgOf n b ml)`. -/
theorem padAt_eq (b : Bool) (ml : List Bool) (c : Fin d → Bool) :
    padAt (n := n) b ml c =
      padFin n (List.zipWith xor (pairSndD (List.ofFn c)) (AdaptiveCPA.msgOf n b ml)) := rfl

/-- **The lazy function's recorded value** at `x`: the challenge's pad at `r*`, else the table's
value. -/
def look (b : Bool) (st : LState n d) (x : Fin n → Bool) : Option (Fin n → Bool) :=
  match st.2.1 with
  | some (ml, c) => if x = rStar c then some (padAt b ml c) else st.1.lookup x
  | none => st.1.lookup x

/-- Without a challenge record, the recorded values are the table's:
`look b (T, none, bd) x = T.lookup x`. -/
theorem look_none (b : Bool) (T : List ((Fin n → Bool) × (Fin n → Bool))) (bd : Bool)
    (x : Fin n → Bool) : look b ((T, none, bd) : LState n d) x = T.lookup x := rfl

/-- With the challenge record `⟨ml, c⟩`, the value at `r*` is the pad, elsewhere the table's:
`look b (T, some (ml, c), bd) x = if x = rStar c then some (padAt b ml c) else T.lookup x`. -/
theorem look_some (b : Bool) (T : List ((Fin n → Bool) × (Fin n → Bool))) (ml : List Bool)
    (c : Fin d → Bool) (bd : Bool) (x : Fin n → Bool) :
    look b ((T, some (ml, c), bd) : LState n d) x =
      if x = rStar c then some (padAt b ml c) else T.lookup x := rfl

/-- **`R` overridden by the recorded values:** `ovr b st R x = (look b st x).getD (R x)`. -/
def ovr (b : Bool) (st : LState n d) (R : (Fin n → Bool) → (Fin n → Bool)) :
    (Fin n → Bool) → (Fin n → Bool) :=
  fun x => (look b st x).getD (R x)

/-- `ovr b st R x = (look b st x).getD (R x)`. -/
theorem ovr_apply (b : Bool) (st : LState n d) (R : (Fin n → Bool) → (Fin n → Bool))
    (x : Fin n → Bool) : ovr b st R x = (look b st x).getD (R x) := rfl

/-- The state after a lazily answered point `x` with fresh value `y`: `(x, y)` is added to the
table unless `x` already has a value; the flag is raised by `hit`. -/
def addPt (b : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool) : LState n d :=
  (if (look b st x).isSome then st.1 else (x, y) :: st.1, st.2.1, st.2.2 || hit)

/-- `addPt b st x y hit = (if (look b st x).isSome then T else (x, y) :: T, ch, bd || hit)`. -/
theorem addPt_eq (b : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool) :
    addPt b st x y hit =
      (if (look b st x).isSome then st.1 else (x, y) :: st.1, st.2.1, st.2.2 || hit) := rfl

/-- Whether `x` is the challenge's nonce. -/
def hitStar (st : LState n d) (x : Fin n → Bool) : Bool :=
  match st.2.1 with
  | some (_, c) => decide (x = rStar c)
  | none => false

/-- `hitStar (T, some (ml, c), bd) x = decide (x = rStar c)`
and `hitStar (T, none, bd) x = false`. -/
theorem hitStar_some (T : List ((Fin n → Bool) × (Fin n → Bool))) (ml : List Bool)
    (c : Fin d → Bool) (bd : Bool) (x : Fin n → Bool) :
    hitStar ((T, some (ml, c), bd) : LState n d) x = decide (x = rStar c) := rfl

/-- `hitStar (T, none, bd) x = false`. -/
theorem hitStar_none (T : List ((Fin n → Bool) × (Fin n → Bool))) (bd : Bool) (x : Fin n → Bool) :
    hitStar ((T, none, bd) : LState n d) x = false := rfl

end State

/-! ### The lazy experiment -/

section Lazy

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (atk : Attack) (b : Bool)

/-- **The IND experiment with a lazily sampled random function:** as `fImpl`, with the function's
value at a point `x` the recorded `look b st x` if any, else a fresh uniform `y`, recorded in the
table (`addPt`). An encryption raises the flag on the challenge's nonce (`hitStar`); the first
challenge raises it when its nonce already has a value, and records `⟨m₀ ‖ m₁, c⟩` without
entering its nonce in the table. -/
noncomputable def lazyImpl : QueryImpl (bitSpec ins outs) (LState n d) unifSpec
  | 0, m, st => (ProbComp.sample (Fin n → Bool)).bind fun r =>
      (ProbComp.sample (Fin n → Bool)).bind fun y =>
        .pure (padFin _ (ctOf r (List.ofFn m) ((look b st r).getD y)),
          addPt b st r y (hitStar st r))
  | 1, c, st =>
    if FixedLengthScheme.decOpen atk st.2.1.isSome && decWF n (List.ofFn c) then
      (ProbComp.sample (Fin n → Bool)).bind fun y =>
        .pure (padFin _ (true :: List.zipWith xor (pairSndD (List.ofFn c))
            (List.ofFn ((look b st (padFin n (pairFstD (List.ofFn c)))).getD y))),
          addPt b st (padFin n (pairFstD (List.ofFn c))) y false)
    else .pure (zeroBits _, st)
  | 2, mm, st =>
    match st with
    | (T, some (ml, c), bd) => .pure (padFin _ (List.ofFn c), (T, some (ml, c), bd))
    | (T, none, bd) => (ProbComp.sample (Fin n → Bool)).bind fun r =>
        (ProbComp.sample (Fin n → Bool)).bind fun y =>
          .pure (padFin _ (List.ofFn (padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm))
              ((look b ((T, none, bd) : LState n d) r).getD y)))),
            (T, some (List.ofFn mm, padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm))
              ((look b ((T, none, bd) : LState n d) r).getD y))),
                bd || (look b ((T, none, bd) : LState n d) r).isSome))

/-- An encryption samples a nonce `r` and a fresh value `y`, answers `⟨r, m ⊕ R(r)⟩` with the lazy
value, and records the point. -/
theorem lazyImpl_enc (m : Fin (ins 0) → Bool) (st : LState n d) :
    lazyImpl ins outs d n atk b 0 m st = (ProbComp.sample (Fin n → Bool)).bind fun r =>
      (ProbComp.sample (Fin n → Bool)).bind fun y =>
        .pure (padFin _ (ctOf r (List.ofFn m) ((look b st r).getD y)),
          addPt b st r y (hitStar st r)) :=
  rfl

/-- An open decryption of a well-formed `⟨x, v⟩` answers `⟨1, v ⊕ R(x)⟩` with the lazy value and
records the point. -/
theorem lazyImpl_dec_open (c : Fin (ins 1) → Bool) (st : LState n d)
    (h : (FixedLengthScheme.decOpen atk st.2.1.isSome && decWF n (List.ofFn c)) = true) :
    lazyImpl ins outs d n atk b 1 c st = (ProbComp.sample (Fin n → Bool)).bind fun y =>
      .pure (padFin _ (true :: List.zipWith xor (pairSndD (List.ofFn c))
          (List.ofFn ((look b st (padFin n (pairFstD (List.ofFn c)))).getD y))),
        addPt b st (padFin n (pairFstD (List.ofFn c))) y false) := by
  show (if _ then _ else _) = _
  rw [if_pos h]

/-- Otherwise a decryption answers `⊥` and keeps the state. -/
theorem lazyImpl_dec_closed (c : Fin (ins 1) → Bool) (st : LState n d)
    (h : (FixedLengthScheme.decOpen atk st.2.1.isSome && decWF n (List.ofFn c)) = false) :
    lazyImpl ins outs d n atk b 1 c st = .pure (zeroBits _, st) := by
  show (if _ then _ else _) = _
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- A repeated challenge returns the recorded ciphertext. -/
theorem lazyImpl_challenge_some (mm : Fin (ins 2) → Bool)
    (T : List ((Fin n → Bool) × (Fin n → Bool))) (ml : List Bool) (c : Fin d → Bool) (bd : Bool) :
    lazyImpl ins outs d n atk b 2 mm (T, some (ml, c), bd) =
      .pure (padFin _ (List.ofFn c), (T, some (ml, c), bd)) :=
  rfl

/-- The first challenge samples `r` and `y`, answers `c = ⟨r, m_b ⊕ R(r)⟩` with the lazy value,
records `⟨m₀ ‖ m₁, c⟩` and raises the flag if `r` already has a value. -/
theorem lazyImpl_challenge_none (mm : Fin (ins 2) → Bool)
    (T : List ((Fin n → Bool) × (Fin n → Bool))) (bd : Bool) :
    lazyImpl ins outs d n atk b 2 mm (T, none, bd) =
      (ProbComp.sample (Fin n → Bool)).bind fun r =>
        (ProbComp.sample (Fin n → Bool)).bind fun y =>
          .pure (padFin _ (List.ofFn (padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm))
              ((look b ((T, none, bd) : LState n d) r).getD y)))),
            (T, some (List.ofFn mm, padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm))
              ((look b ((T, none, bd) : LState n d) r).getD y))),
                bd || (look b ((T, none, bd) : LState n d) r).isSome)) :=
  rfl

end Lazy

/-! ### The recorded values along the lazy experiment -/

section Records

variable {n d : ℕ}

/-- Exclusive-or with the same list twice cancels: `(a ⊕ c) ⊕ a = c` for `|a| = |c|`. -/
theorem zipWith_xor_cancel_left {a c : List Bool} (h : a.length = c.length) :
    List.zipWith xor (List.zipWith xor a c) a = c := by
  apply List.ext_getElem
  · simp [h]
  · intro i h₁ h₂
    simp only [List.getElem_zipWith]
    cases a[i] <;> cases c[i] <;> rfl

/-- The record of a ciphertext `⟨r, m ⊕ y⟩` (with `|m| = n` and `d = 3n + 2`) has nonce `r`. -/
theorem rStar_ctOf (hd : d = 3 * n + 2) (r : Fin n → Bool) {m : List Bool} (hm : m.length = n)
    (y : Fin n → Bool) : rStar (padFin d (ctOf r m y)) = r := by
  rw [rStar_eq, GGMRed.ofFn_padFin_of_length (by rw [length_ctOf r hm, hd]), ctOf_eq,
    pairFstD_pairEncode, padFin_ofFn]

/-- The record of a challenge ciphertext `⟨r, m_b ⊕ y⟩` has pad `y`. -/
theorem padAt_ctOf (hd : d = 3 * n + 2) (b : Bool) (r : Fin n → Bool) (ml : List Bool)
    (hm : (AdaptiveCPA.msgOf n b ml).length = n) (y : Fin n → Bool) :
    padAt b ml (padFin d (ctOf r (AdaptiveCPA.msgOf n b ml) y)) = y := by
  rw [padAt_eq, GGMRed.ofFn_padFin_of_length (by rw [length_ctOf r hm, hd]), ctOf_eq,
    pairSndD_pairEncode, zipWith_xor_cancel_left (by rw [hm, List.length_ofFn]), padFin_ofFn]

/-- The flag does not change the recorded values: `look b (st.1, st.2.1, bd) = look b st`. -/
theorem look_flag (b : Bool) (st : LState n d) (bd : Bool) :
    look b ((st.1, st.2.1, bd) : LState n d) = look b st := by
  obtain ⟨T, ch, bd'⟩ := st
  cases ch <;> rfl

/-- **A point with a value is not recorded again:** if `look b st x` is some value, adding `x`
changes no recorded value, so `ovr` is unchanged: `ovr b (addPt b st x y hit) R = ovr b st R`. -/
theorem ovr_addPt_of_isSome (b : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool)
    (hx : (look b st x).isSome = true) (R : (Fin n → Bool) → (Fin n → Bool)) :
    ovr b (addPt b st x y hit) R = ovr b st R := by
  rw [addPt_eq, if_pos hx]
  funext z
  rw [ovr_apply, ovr_apply, look_flag]

/-- **A new point is a resampled value:** if `x` has no value, adding `(x, y)` gives the recorded
values of `st` with `R` resampled to `y` at `x`:
`ovr b (addPt b st x y hit) R = ovr b st (Function.update R x y)`.

**Proof sketch.** At `z = x` both sides read `y` (the new table entry, resp. the update); at
`z ≠ x` the new entry is skipped by `lookup` and the update is not read (`look_none`, `look_some`,
`List.lookup_cons`, `Function.update_of_ne`). -/
theorem ovr_addPt_of_none (b : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool)
    (hx : look b st x = none) (R : (Fin n → Bool) → (Fin n → Bool)) :
    ovr b (addPt b st x y hit) R = ovr b st (Function.update R x y) := by
  rw [addPt_eq, if_neg (by rw [hx]; exact Bool.false_ne_true)]
  funext z
  obtain ⟨T, ch, bd⟩ := st
  rw [ovr_apply, ovr_apply]
  by_cases hz : z = x
  · subst hz
    rw [hx, Option.getD_none, Function.update_self]
    cases ch with
    | none => simp [look_none]
    | some p =>
      obtain ⟨ml, c⟩ := p
      have hne : ¬ z = rStar c := by
        intro h
        rw [look_some, if_pos h] at hx
        exact Option.noConfusion hx
      simp [look_some, hne]
  · rw [Function.update_of_ne hz]
    have hzb : (z == x) = false := beq_eq_false_iff_ne.mpr hz
    cases ch with
    | none => simp [look_none, List.lookup_cons, hzb]
    | some p =>
      obtain ⟨ml, c⟩ := p
      simp only [look_some]
      split
      · rfl
      · simp [List.lookup_cons, hzb]

/-- After a fresh point `x` with value `y`, the value at `x` is `y`. -/
theorem ovr_addPt_self (b : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool)
    (hx : look b st x = none) (R : (Fin n → Bool) → (Fin n → Bool)) :
    ovr b (addPt b st x y hit) R x = y := by
  rw [ovr_addPt_of_none b st x y hit hx, ovr_apply, hx, Option.getD_none, Function.update_self]

/-- **The challenge record holds the challenge's value:** from `(T, none, bd)`, recording the
challenge ciphertext `c = ⟨r, m_b ⊕ y⟩` gives the recorded values with the value `y` at `r`, so
`ovr` of the new state is `ovr` of the old one with `R` resampled at `r` (if `r` had no value). -/
theorem ovr_record_of_none (hd : d = 3 * n + 2) (b : Bool)
    (T : List ((Fin n → Bool) × (Fin n → Bool))) (bd bd' : Bool) (ml : List Bool)
    (hm : (AdaptiveCPA.msgOf n b ml).length = n) (r y : Fin n → Bool)
    (hr : look b ((T, none, bd) : LState n d) r = none) (R : (Fin n → Bool) → (Fin n → Bool)) :
    ovr b ((T, some (ml, padFin d (ctOf r (AdaptiveCPA.msgOf n b ml) y)), bd') : LState n d) R =
      ovr b ((T, none, bd) : LState n d) (Function.update R r y) := by
  funext z
  rw [ovr_apply, ovr_apply, look_some, rStar_ctOf hd r hm, padAt_ctOf hd b r ml hm, look_none]
  rw [look_none] at hr
  by_cases hz : z = r
  · subst hz
    rw [if_pos rfl, hr, Option.getD_some, Option.getD_none, Function.update_self]
  · rw [if_neg hz, Function.update_of_ne hz]

/-- If the challenge's nonce `r` already has the value `y₀`, recording `⟨r, m_b ⊕ y₀⟩` changes no
recorded value. -/
theorem ovr_record_of_some (hd : d = 3 * n + 2) (b : Bool)
    (T : List ((Fin n → Bool) × (Fin n → Bool))) (bd bd' : Bool) (ml : List Bool)
    (hm : (AdaptiveCPA.msgOf n b ml).length = n) (r y₀ : Fin n → Bool)
    (hr : look b ((T, none, bd) : LState n d) r = some y₀) (R : (Fin n → Bool) → (Fin n → Bool)) :
    ovr b ((T, some (ml, padFin d (ctOf r (AdaptiveCPA.msgOf n b ml) y₀)), bd') : LState n d) R =
      ovr b ((T, none, bd) : LState n d) R := by
  funext z
  rw [ovr_apply, ovr_apply, look_some, rStar_ctOf hd r hm, padAt_ctOf hd b r ml hm, look_none]
  rw [look_none] at hr
  by_cases hz : z = r
  · subst hz
    rw [if_pos rfl, hr]
  · rw [if_neg hz]

end Records

/-! ### Sampling the random function in advance or lazily -/

section LazyEq

variable (ins outs : Fin 3 → ℕ) (d n : ℕ) (atk : Attack) (b : Bool)

/-- **The random function sampled in advance is the lazy one** (the two descriptions of a random
function [PS10, §3.8.1], inside the IND experiment): with `d = 3n + 2` and `2n`-bit challenge
queries, for every computation `c`, state `st` and function `G` of the output,
`𝔼_R 𝔼[G] (simulate (fImpl … (ovr b st R)) c (record of st)) = 𝔼[G] (simulate (lazyImpl …) c st)`.

**Proof sketch.** Induction on `c`. At a point `x` with a recorded value both sides use it and the
recorded values do not change (`ovr_addPt_of_isSome`, `ovr_record_of_some`). At a new point,
resample `R` at `x` (`BitwiseSim.expect_sample_update`): `R(x)` becomes the lazy sample `y`, and
`R` resampled is the override of the new state (`ovr_addPt_of_none`, `ovr_record_of_none`);
exchange the samples (`expect_sample_comm`) and apply the induction hypothesis. Closed
decryptions and repeated challenges are answered alike. -/
theorem expect_lazyImpl (hd : d = 3 * n + 2) (hi2 : ins 2 = n + n) {α : Type} (G : α → ℝ)
    (c : OracleComp (bitSpec ins outs) α) (st : LState n d) :
    expect (ProbComp.sample ((Fin n → Bool) → (Fin n → Bool))) (fun R =>
        expect (simulate (fImpl ins outs d n atk b (ovr b st R)) c (st.2.1.map Prod.snd))
          (fun p => G p.1)) =
      expect (simulate (lazyImpl ins outs d n atk b) c st) (fun p => G p.1) := by
  induction c generalizing st with
  | pure a =>
    simp only [simulate_pure, expect_pure]
    exact expect_const _ _
  | query i x k ih =>
    match i, x, k, ih with
    | 0, m, k, ih =>
      simp only [simulate_query, fImpl_enc, lazyImpl_enc, OracleComp.bind_assoc, expect_bind,
        OracleComp.pure_bind]
      rw [expect_sample_comm]
      refine congrArg _ (funext fun r => ?_)
      cases hr : look b st r with
      | some y₀ =>
        have hval : ∀ R, ovr b st R r = y₀ := fun R => by rw [ovr_apply, hr, Option.getD_some]
        have hsome : (look b st r).isSome = true := by rw [hr]; rfl
        have hst : ∀ y, addPt b st r y (hitStar st r) = addPt b st r y₀ (hitStar st r) :=
          fun y => by rw [addPt_eq, addPt_eq, if_pos hsome, if_pos hsome]
        simp only [hval, Option.getD_some, hst]
        refine Eq.trans ?_ (expect_const _ _).symm
        exact (congrArg _ (funext fun R => by
          rw [← ovr_addPt_of_isSome b st r y₀ (hitStar st r) hsome R]; rfl)).trans (ih _ _)
      | none =>
        rw [← BitwiseSim.expect_sample_update r]
        simp only [Option.getD_none]
        have hU : ∀ R y, ovr b st (Function.update R r y) =
            ovr b (addPt b st r y (hitStar st r)) R :=
          fun R y => (ovr_addPt_of_none b st r y _ hr R).symm
        have hV : ∀ R y, ovr b (addPt b st r y (hitStar st r)) R r = y :=
          fun R y => ovr_addPt_self b st r y _ hr R
        simp only [hU, hV]
        rw [expect_sample_comm]
        exact congrArg _ (funext fun y => ih _ _)
    | 1, c, k, ih =>
      by_cases hop : (FixedLengthScheme.decOpen atk st.2.1.isSome && decWF n (List.ofFn c)) = true
      · have hop' : (FixedLengthScheme.decOpen atk (st.2.1.map Prod.snd).isSome &&
            decWF n (List.ofFn c)) = true := by rw [Option.isSome_map]; exact hop
        simp only [simulate_query, fImpl_dec, lazyImpl_dec_open _ _ _ _ _ _ c st hop,
          OracleComp.bind_assoc, expect_bind, OracleComp.pure_bind, decAns_eq,
          if_pos hop']
        cases hr : look b st (padFin n (pairFstD (List.ofFn c))) with
        | some y₀ =>
          have hval : ∀ R, ovr b st R (padFin n (pairFstD (List.ofFn c))) = y₀ :=
            fun R => by rw [ovr_apply, hr, Option.getD_some]
          have hsome : (look b st (padFin n (pairFstD (List.ofFn c)))).isSome = true := by
            rw [hr]; rfl
          have hst : ∀ y, addPt b st (padFin n (pairFstD (List.ofFn c))) y false =
              addPt b st (padFin n (pairFstD (List.ofFn c))) y₀ false :=
            fun y => by rw [addPt_eq, addPt_eq, if_pos hsome, if_pos hsome]
          simp only [hval, Option.getD_some, hst]
          refine Eq.trans ?_ (expect_const _ _).symm
          exact (congrArg _ (funext fun R => by
            rw [← ovr_addPt_of_isSome b st _ y₀ false hsome R]; rfl)).trans (ih _ _)
        | none =>
          rw [← BitwiseSim.expect_sample_update (padFin n (pairFstD (List.ofFn c)))]
          simp only [Option.getD_none]
          have hU : ∀ R y, ovr b st (Function.update R (padFin n (pairFstD (List.ofFn c))) y) =
              ovr b (addPt b st (padFin n (pairFstD (List.ofFn c))) y false) R :=
            fun R y => (ovr_addPt_of_none b st _ y _ hr R).symm
          have hV : ∀ R y, ovr b (addPt b st (padFin n (pairFstD (List.ofFn c))) y false) R
              (padFin n (pairFstD (List.ofFn c))) = y :=
            fun R y => ovr_addPt_self b st _ y _ hr R
          simp only [hU, hV]
          rw [expect_sample_comm]
          exact congrArg _ (funext fun y => ih _ _)
      · rw [Bool.not_eq_true] at hop
        have hop' : (FixedLengthScheme.decOpen atk (st.2.1.map Prod.snd).isSome &&
            decWF n (List.ofFn c)) = false := by rw [Option.isSome_map]; exact hop
        have hz0 : padFin (outs 1) [] = zeroBits (outs 1) := by
          funext k
          simp only [padFin_def, List.getD_nil, zeroBits_apply]
        simp only [simulate_query, fImpl_dec, lazyImpl_dec_closed _ _ _ _ _ _ c st hop,
          OracleComp.pure_bind, decAns_eq, hop', Bool.false_eq_true, if_false, hz0]
        exact ih _ st
    | 2, mm, k, ih =>
      obtain ⟨T, ch, bd⟩ := st
      cases ch with
      | some p =>
        obtain ⟨ml, c⟩ := p
        simp only [simulate_query, lazyImpl_challenge_some, OracleComp.pure_bind, Option.map_some,
          fImpl_challenge_some]
        exact ih _ _
      | none =>
        have hm : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
          have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, hi2]
          rw [AdaptiveCPA.msgOf_eq]
          cases b <;> simp [this]
        have hpad : ∀ r y, List.ofFn (padFin d (ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) y)) =
            ctOf r (AdaptiveCPA.msgOf n b (List.ofFn mm)) y := fun r y =>
          GGMRed.ofFn_padFin_of_length (by rw [length_ctOf r hm, hd])
        simp only [simulate_query, Option.map_none, fImpl_challenge_none, lazyImpl_challenge_none,
          OracleComp.bind_assoc, expect_bind, OracleComp.pure_bind, hpad]
        rw [expect_sample_comm]
        refine congrArg _ (funext fun r => ?_)
        cases hr : look b ((T, none, bd) : LState n d) r with
        | some y₀ =>
          have hval : ∀ R, ovr b ((T, none, bd) : LState n d) R r = y₀ :=
            fun R => by rw [ovr_apply, hr, Option.getD_some]
          simp only [hval, Option.getD_some, Option.isSome_some]
          refine Eq.trans ?_ (expect_const _ _).symm
          exact (congrArg _ (funext fun R => by
            rw [← ovr_record_of_some hd b T bd (bd || true) (List.ofFn mm) hm r y₀
                hr R]; rfl)).trans
            (ih _ _)
        | none =>
          rw [← BitwiseSim.expect_sample_update r]
          simp only [Option.getD_none, Option.isSome_none]
          have hU : ∀ R y, ovr b ((T, none, bd) : LState n d) (Function.update R r y) =
              ovr b ((T, some (List.ofFn mm, padFin d (ctOf r (AdaptiveCPA.msgOf n b
                (List.ofFn mm)) y)), bd || false) : LState n d) R :=
            fun R y => (ovr_record_of_none hd b T bd _ _ hm r y hr R).symm
          have hV : ∀ R y, ovr b ((T, some (List.ofFn mm, padFin d (ctOf r (AdaptiveCPA.msgOf n b
              (List.ofFn mm)) y)), bd || false) : LState n d) R r = y := fun R y => by
            rw [← hU, ovr_apply, hr, Option.getD_none, Function.update_self]
          simp only [hU, hV]
          rw [expect_sample_comm]
          exact congrArg _ (funext fun y => ih _ _)

end LazyEq

end TCSlib.Cryptography.Composability.PRFGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Reduction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Handler
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The PRF reduction for the §3.9 scheme

The reduction of [PS10, Theorem 168.2], step 1, as a next-query oracle machine: T2
(`Games.exists_interactiveHandlerMachine`) applied to the handler `pkHandler` (through the
input-free companion `Games.exists_toCompOn_of_toComp`), then T4
(`Games.exists_toOracleAdversary_of_bitCodec`). Its acceptance probability against any function
`f` is the acceptance probability of the IND experiment with `f` in place of `f_k`
(`exists_prfReduction`).

The proof answers the handler's outer queries by `f` (`fOuter`) and composes the two
implementations (`QueryImpl.comp`). Each composed call, from the encoded state `pkState j o`, is
the call of `eImpl` from `(j, o)` with the handler's tapes in advance (`comp_pkAbs`), as long as
`j` is below the number `q(n)` of tapes; the adversary asks at most `q(n)` queries, so this holds
along every run (`simulate_eq_of_abs_bounded`). Drawing the seed uniformly then gives fresh
nonces (`PRFGame.expect_eImpl`).

## Main definitions

* `PRFGame.fOuter`: the outer oracle answering with `f`.
* `PRFGame.atkOf`: the attack of the attack bit.
* `PRFGame.qRed`: the reduction's query budget.

## Main results

* `PRFGame.simulate_eq_of_abs_bounded`: simulation through a state abstraction along runs with a
  query budget.
* `PRFGame.exists_prfReduction`: the reduction.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 168.2 (book p. 168).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

/-! ### Simulation through a state abstraction along bounded runs -/

/-- **Simulation through a state abstraction, along runs with a query budget:** let every call of
`impl₂` from a state `s` with `cnt s < κ` be a deterministic answer `(y, s')` with
`cnt s' ≤ cnt s + 1`, and the call of `impl₁` from `f s` be `(y, f s')`. Then for a computation
`c` with at most `m` queries and `cnt s + m ≤ κ`,
`simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.

**Proof sketch.** Induction on `c`. A query costs one unit, so it is asked from a state with
`cnt s < κ`; both calls return the same answer, and the continuation runs from `s'` with one unit
less, where `cnt s' + (m - 1) ≤ κ`. -/
theorem simulate_eq_of_abs_bounded {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
    (f : σ₂ → σ₁) (cnt : σ₂ → ℕ) (κ : ℕ)
    (h : ∀ i x s, cnt s < κ → ∃ (y : spec.rng i) (s' : σ₂), impl₂ i x s = .pure (y, s') ∧
      cnt s' ≤ cnt s + 1 ∧ impl₁ i x (f s) = .pure (y, f s'))
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ₂)
    (hs : cnt s + m ≤ κ) :
    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
  induction c generalizing m s with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    obtain ⟨hm, hk⟩ := (OracleComp.costBoundedBy_query _ _ _ _ _).1 hc
    have hm1 : 1 ≤ m := hm
    obtain ⟨y, s', h₂, hcnt, h₁⟩ := h i x s (by omega)
    rw [simulate_query, simulate_query, h₁, h₂, OracleComp.pure_bind, OracleComp.pure_bind]
    exact ih y (m - 1) (hk y) s' (by omega)

/-! ### The outer oracle and the composed calls -/

/-- **The outer oracle answering with `f`:** a query `x` is answered `f x`, lengths adjusted. -/
noncomputable def fOuter (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) :
    QueryImpl (bitSpecAt pkOut pkOut n) Unit unifSpec :=
  QueryImpl.ofComp fun _ x => .pure (padFin _ (List.ofFn (f (padFin n (List.ofFn x)))))

/-- `fOuter n f i x s = pure (padFin _ ⟦f (padFin n ⟦x⟧)⟧, s)`. -/
theorem fOuter_apply (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)) (i : Fin 1)
    (x : (bitSpecAt pkOut pkOut n).dom i) (s : Unit) :
    fOuter n f i x s = .pure (padFin _ (List.ofFn (f (padFin n (List.ofFn x)))), s) := by
  rw [fOuter, QueryImpl.ofComp_apply, OracleComp.pure_bind]

/-- The attack of the attack bit: CCA1 for `true`, CPA for `false`. -/
def atkOf (atkBit : Bool) : Attack := if atkBit then .cca1 else .cpa

/-- `atkOf false = CPA`. -/
theorem atkOf_false : atkOf false = .cpa := rfl

/-- `atkOf true = CCA1`. -/
theorem atkOf_true : atkOf true = .cca1 := rfl

/-- The decryption oracle of `atkOf atkBit` is open exactly when `atkBit` holds and no challenge
was recorded: `decOpen (atkOf atkBit) c = (atkBit && !c)`. -/
theorem decOpen_atkOf (atkBit c : Bool) :
    FixedLengthScheme.decOpen (atkOf atkBit) c = (atkBit && !c) := by
  cases atkBit
  · rw [atkOf, if_neg Bool.false_ne_true, FixedLengthScheme.decOpen_cpa, Bool.false_and]
  · rw [atkOf, if_pos rfl, FixedLengthScheme.decOpen_cca1, Bool.true_and]

/-- The reduction's query budget `q · 1 + 0` (T2's `q · perCall + finCall`). -/
def qRed (q : PolyExpr) : PolyExpr := .add (.mul q (.const 1)) (.const 0)

/-- `(qRed q).eval n = q(n) · 1 + 0`. -/
theorem qRed_eval (q : PolyExpr) (n : ℕ) :
    (qRed q).eval n = q.eval n * (PolyExpr.const 1).eval n + (PolyExpr.const 0).eval n := by
  rw [qRed, PolyExpr.eval_add, PolyExpr.eval_mul]

section Composed

variable (q : PolyExpr) (atkBit b : Bool) (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool))
  (z : List Bool) (ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool)

/-- The handler's state and the (trivial) outer state, as functions of `eImpl`'s state. -/
def pkAbs (s : ℕ × Option (Fin (ctP.eval n) → Bool)) :
    (Fin ((pkHandler q atkBit b).stateLen.eval n) → Bool) × Unit :=
  (pkHState q atkBit b n s.1 s.2, ())

/-- `pkAbs q atkBit b n s = (pkHState q atkBit b n s.1 s.2, ())`. -/
theorem pkAbs_eq (s : ℕ × Option (Fin (ctP.eval n) → Bool)) :
    pkAbs q atkBit b n s = (pkHState q atkBit b n s.1 s.2, ()) :=
  rfl

/-- Reading a tape through the outer oracle's padding: `f` at the tape `r`. -/
private theorem fOuter_tape (r : Fin n → Bool) :
    padFin n (List.ofFn (padFin ((pkOut 0).eval n) (List.ofFn (f (padFin n (List.ofFn
      (padFin ((pkOut 0).eval n) (List.ofFn r)))))))) = f r := by
  have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
  rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn]), padFin_ofFn,
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn]), padFin_ofFn]

/-- **One composed call is a call of `eImpl` with the tapes in advance:** from the encoded state
`pkState j o` with `j < q(n)`, the handler composed with `fOuter f` answers as `eImpl` with pad
function `f` and the tapes `extTape (pkSeedTapes ω)` from `(j, o)`, both deterministic, with the
new state abstracted; the counter grows by at most one.

**Proof sketch.** By the oracle and the record: encryption and a fresh challenge ask `f` at the
tape `T_j` (`pkHandler_impl_enc`, `pkHandler_impl_challenge_none`); an open decryption asks `f`
at the nonce of the query (`pkHandler_impl_dec_open`); a closed decryption and a repeated
challenge answer directly. The outer oracle answers `f` (`fOuter_apply`, `fOuter_tape`). -/
theorem comp_pkAbs (i : Fin 3) (x : (bitSpecAt pkDin pkDout n).dom i)
    (s : ℕ × Option (Fin (ctP.eval n) → Bool)) (hs : s.1 < q.eval n) :
    ∃ (y : (bitSpecAt pkDin pkDout n).rng i) (s' : ℕ × Option (Fin (ctP.eval n) → Bool)),
      eImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) (ctP.eval n) n
          (atkOf atkBit) b f (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) i x s =
        .pure (y, s') ∧ s'.1 ≤ s.1 + 1 ∧
      (fOuter n f).comp ((pkHandler q atkBit b).impl n z ω) i x (pkAbs q atkBit b n s) =
        .pure (y, pkAbs q atkBit b n s') := by
  obtain ⟨j, o⟩ := s
  have hj : j < q.eval n := hs
  have hT : AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω) j =
      pkSeedTapes q atkBit b n ω ⟨j, hj⟩ := AdaptiveCPA.extTape_of_lt _ hj
  match i, x with
  | 0, x =>
    refine ⟨_, _, eImpl_enc (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
        (ctP.eval n) n (atkOf atkBit) b f
        (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) x j o, le_rfl, ?_⟩
    rw [QueryImpl.comp_apply, pkAbs_eq, pkHState_eq, pkHandler_impl_enc q atkBit b n z ω x j o hj,
      simulate_query, fOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind,
      pkAbs_eq, pkHState_eq, hT, fOuter_tape]
  | 1, x =>
    by_cases hop : (atkBit && !o.isSome && decWF n (List.ofFn x)) = true
    · refine ⟨_, _, eImpl_dec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
        (ctP.eval n) n (atkOf atkBit) b f
          (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) x j o, Nat.le_succ _, ?_⟩
      have hwf : decWF n (List.ofFn x) = true := by
        simp only [Bool.and_eq_true] at hop
        exact hop.2
      have hwf' := hwf
      rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf'
      have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
      have hx0 : padFin n (List.ofFn (padFin ((pkOut 0).eval n) (pairFstD (List.ofFn x)))) =
          padFin n (pairFstD (List.ofFn x)) := by
        rw [GGMRed.ofFn_padFin_of_length (by rw [hwf'.1, hn])]
      rw [QueryImpl.comp_apply, pkAbs_eq, pkHState_eq,
        pkHandler_impl_dec_open q atkBit b n z ω x j o hj.le hop,
        simulate_query, fOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind,
        hx0, GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn]; exact hn.symm),
        decOpen_atkOf, decAns_eq]
      simp only [Bool.and_eq_true] at hop
      rw [if_pos (by simp only [Bool.and_eq_true]; exact ⟨hop.1, hwf⟩)]
    · refine ⟨_, _, eImpl_dec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
        (ctP.eval n) n (atkOf atkBit) b f
          (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) x j o, Nat.le_succ _, ?_⟩
      rw [Bool.not_eq_true] at hop
      rw [QueryImpl.comp_apply, pkAbs_eq, pkHState_eq,
        pkHandler_impl_dec_closed q atkBit b n z ω x j o hj.le hop,
        simulate_pure, OracleComp.pure_bind, decOpen_atkOf, decAns_eq,
        if_neg (by rw [hop]; exact Bool.false_ne_true)]
      have hz : padFin ((pkDout 1).eval n) [] = zeroBits _ := by
        funext k
        simp only [padFin_def, List.getD_nil, zeroBits_apply]
      rw [hz]
  | 2, x =>
    cases o with
    | some c =>
      refine ⟨_, _, eImpl_challenge_some (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
          (ctP.eval n) n (atkOf atkBit) b f
        (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) x j c, Nat.le_succ _, ?_⟩
      rw [QueryImpl.comp_apply, pkAbs_eq, pkHState_eq,
        pkHandler_impl_challenge_some q atkBit b n z ω x j c hj.le, simulate_pure,
        OracleComp.pure_bind]
    | none =>
      refine ⟨_, _, eImpl_challenge_none (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
          (ctP.eval n) n (atkOf atkBit) b f
        (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)) x j, le_rfl, ?_⟩
      rw [QueryImpl.comp_apply, pkAbs_eq, pkHState_eq,
        pkHandler_impl_challenge_none q atkBit b n z ω x j hj,
        simulate_query, fOuter_apply, OracleComp.pure_bind, simulate_pure, OracleComp.pure_bind,
        pkAbs_eq, pkHState_eq, hT, fOuter_tape]

end Composed

/-! ### Transport along output widths and oracle widths -/

/-- **A machine's evaluation does not see its output width:** for `d = d'`, the outputs (as lists)
of `M`'s computations through `bitCodec I O d` and `bitCodec I O d'`, evaluated with `F`, agree.

**Proof sketch.** Substitute `d = d'`. -/
theorem ofFn_evalFn_toCompOn {k : ℕ} {I O : Fin k → ℕ} {d d' : ℕ} (hd : d = d') (M : NUPPT)
    (n q : ℕ) (z : List Bool) (r : M.Coins n) (F : ∀ i, (bitSpec I O).dom i → (bitSpec I O).rng i) :
    List.ofFn ((M.toCompOn (bitCodec I O d) n q z r).evalFn F) =
      List.ofFn ((M.toCompOn (bitCodec I O d') n q z r).evalFn F) := by
  subst hd
  rfl

/-- **The game with pad function `f` does not see the output width:** for `d = d'`, the
expected first output bit of the run through `bitCodec ins outs d` and through
`bitCodec ins outs d'` agree.

**Proof sketch.** Substitute `d = d'`. -/
theorem expect_fImpl_width {ins outs : Fin 3 → ℕ} {d d' : ℕ} (hd : d = d') (c n : ℕ)
    (atk : Attack) (b : Bool) (f : (Fin n → Bool) → (Fin n → Bool)) (A : NUPPT) (q : ℕ)
    (r : A.Coins n) :
    expect (simulate (fImpl ins outs c n atk b f) (A.toComp (bitCodec ins outs d) n q r) none)
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
      expect (simulate (fImpl ins outs c n atk b f) (A.toComp (bitCodec ins outs d') n q r) none)
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  subst hd
  rfl

/-- **An oracle adversary read at an equal width:** for `m = n`, running
`D.toOracleAdversary n n n q c` against `f` is running `D.toOracleAdversary n m m q c` against `f`
with its inputs and outputs read at width `m`.

**Proof sketch.** Substitute `m = n`; the readings are identities (`padFin_ofFn`). -/
theorem eval_toOracleAdversary_width (D : NUPPT) (n q : ℕ) (c : D.Coins n) {m : ℕ} (hm : m = n)
    (f : (Fin n → Bool) → (Fin n → Bool)) :
    (D.toOracleAdversary n n n q c).eval f =
      (D.toOracleAdversary n m m q c).eval
        (fun x => padFin m (List.ofFn (f (padFin n (List.ofFn x))))) := by
  subst hm
  have h : (fun x => padFin m (List.ofFn (f (padFin m (List.ofFn x))))) = f := by
    funext x
    rw [padFin_ofFn, padFin_ofFn]
  rw [h]

/-! ### The reduction -/

/-- **The PRF reduction** [PS10, Theorem 168.2, step 1]: for a machine adversary `A` with budget
`q`, an attack bit (`atkOf`) and a challenge bit `b`, there is a next-query machine `D` such that,
at every `n` and for every function `f : {0,1}^n → {0,1}^n`, `D` with budget `qRed q` accepts
against `f` with the probability that `A` outputs `1` in the IND experiment with `f` in place of
`f_k` (the oracles `fImpl`, on the lengths `pkDin`, `pkDout`):
`𝔼_c [D^f(c) = 1] = 𝔼_r 𝔼[⟦A's output⟧₀ = 1 | simulate (fImpl … f) (A.toComp … r) none]`.

**Proof sketch.** `D` is T4 applied to T2's machine `B` for `pkHandler` and the input-free
companion `A'` of `A`. Its coins are, through the bijections of T4, T2 and the companion, a seed
`ω` and `A`'s coins `r` (`expect_sample_equiv`, `expect_sample_prod`, `expect_sample_comm`). For
fixed `ω` and `r`, T4 and T2 turn `D`'s run against `f` into the evaluation, with `f`, of the
reduction; evaluation is simulation with `fOuter f` (`simulate_ofComp_pure`), which composes with
the handler (`simulate_bind`, `simulate_comp`, `pkHandler_finish`); along `A`'s run (at most
`q(n)` queries, `NUPPT.toComp_costBoundedBy`) the composite is `eImpl` with the tapes of `ω`
(`simulate_eq_of_abs_bounded`, `comp_pkAbs`). Drawing `ω` uniformly gives fresh nonces
(`expect_eImpl`). Widths are transported by `ofFn_evalFn_toCompOn`, `expect_fImpl_width` and
`eval_toOracleAdversary_width`. -/
theorem exists_prfReduction (A : NUPPT) (q : PolyExpr) (atkBit b : Bool) :
    ∃ D : NUPPT, ∀ (n : ℕ) (f : (Fin n → Bool) → (Fin n → Bool)),
      expect (ProbComp.sample (D.Coins n))
          (fun c => if (D.toOracleAdversary n n n ((qRed q).eval n) c).eval f = true
            then (1 : ℝ) else 0) =
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (simulate (fImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
              (ctP.eval n) n (atkOf atkBit) b f)
              (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) 1) n
                (q.eval n) r) none)
            (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  obtain ⟨A', -, hA'⟩ := exists_toCompOn_of_toComp A
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A' q pkDin pkDout pkOut pkOut (.const 1)
    (pkHandler q atkBit b)
  obtain ⟨D, -, hD⟩ := exists_toOracleAdversary_of_bitCodec B .var .var
  refine ⟨D, fun n f => ?_⟩
  obtain ⟨φ₀, hφ₀⟩ := hA' n
  obtain ⟨φ₂, hφ₂⟩ := hB n
  obtain ⟨φ₄, hφ₄⟩ := hD n
  have hQ : q.eval n * (pkHandler q atkBit b).perCall.eval n +
      (pkHandler q atkBit b).finCall.eval n = (qRed q).eval n := by
    rw [pkHandler_perCall, pkHandler_finCall, qRed_eval]
  have hout : (pkHandler q atkBit b).outLen.eval n = 1 := by
    rw [pkHandler_outLen, PolyExpr.eval_const]
  -- `D`'s coins are a seed and `A`'s coins.
  rw [← expect_sample_equiv φ₄, ← expect_sample_equiv φ₂, expect_sample_prod, expect_sample_comm,
    ← expect_sample_equiv φ₀]
  refine congrArg _ (funext fun r => ?_)
  -- One run of `D` is the reduction evaluated with `f`.
  have hrun : ∀ ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool,
      (if (D.toOracleAdversary n n n ((qRed q).eval n) (φ₄ (φ₂ (ω, φ₀ r)))).eval f = true
        then (1 : ℝ) else 0) =
      expect (simulate (eImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
          (ctP.eval n) n (atkOf atkBit) b f (AdaptiveCPA.extTape (pkSeedTapes q atkBit b n ω)))
          (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) r) (0, none))
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
    intro ω
    have key : ∀ g : Fin 1 → Bool, (if g 0 = true then (1 : ℝ) else 0) =
        if (List.ofFn g).headD false = true then 1 else 0 := fun g => by
      rw [AdaptiveCPA.headD_ofFn_one]
    have h2 : _ = B.toCompOn (bitCodec (fun _ : Fin 1 => PolyExpr.var.eval n)
        (fun _ => PolyExpr.var.eval n) ((pkHandler q atkBit b).outLen.eval n)) n
        (q.eval n * (pkHandler q atkBit b).perCall.eval n + (pkHandler q atkBit b).finCall.eval n)
        [] (φ₂ (ω, φ₀ r)) := hφ₂ [] ω (φ₀ r)
    rw [eval_toOracleAdversary_width D n _ _ (PolyExpr.eval_var n), hφ₄, ← hQ, key,
      ofFn_evalFn_toCompOn hout.symm B n _ [] (φ₂ (ω, φ₀ r)), ← h2, InteractiveHandler.advInput_eq,
      hφ₀]
    have hev : simulate (fOuter n f) ((simulate ((pkHandler q atkBit b).impl n [] ω)
        (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
          ((PolyExpr.const 1).eval n)) n (q.eval n) r) ((pkHandler q atkBit b).init n)).bind
        (fun res => (pkHandler q atkBit b).finish n [] ω res.2 res.1)) () = _ :=
      simulate_ofComp_pure _ _ _
    have h1 := congrArg (fun c => expect c
      (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)) hev
    simp only [expect_pure] at h1
    refine h1.symm.trans ?_
    rw [simulate_bind, simulate_comp, OracleComp.bind_assoc, expect_bind]
    simp only [OracleComp.pure_bind, pkHandler_finish, simulate_pure, expect_pure]
    rw [pkHandler_init_hstate, show (pkHState q atkBit b n 0 none, ()) =
        pkAbs q atkBit b n (0, none) from (pkAbs_eq q atkBit b n (0, none)).symm,
      simulate_eq_of_abs_bounded _ _ (pkAbs q atkBit b n) (fun s => s.1) (q.eval n)
        (fun i x s hs => comp_pkAbs q atkBit b n f [] ω i x s hs) _ (q.eval n)
        (A.toComp_costBoundedBy _ n (q.eval n) r) (0, none) (Nat.zero_add _).le,
      expect_bind]
    simp only [expect_pure]
    refine congrArg _ (funext fun p => ?_)
    rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, pkHandler_outLen])]
  simp only [hrun]
  rw [expect_sample_equiv (pkSeedTapes q atkBit b n) (fun T => expect (simulate
      (eImpl (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n) (ctP.eval n) n (atkOf atkBit)
        b f (AdaptiveCPA.extTape T))
      (A.toComp (bitCodec (fun i => (pkDin i).eval n) (fun i => (pkDout i).eval n)
        ((PolyExpr.const 1).eval n)) n (q.eval n) r) (0, none))
      (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0)),
    expect_eImpl _ _ _ _ _ _ _ (q.eval n)
      (fun a => if (List.ofFn a).headD false = true then (1 : ℝ) else 0) _ (q.eval n)
      (A.toComp_costBoundedBy _ n (q.eval n) r) 0 (by omega) none]
  exact expect_fImpl_width (PolyExpr.eval_const 1 n) _ n _ b f A _ r

end TCSlib.Cryptography.Composability.PRFGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Transfer.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From the IND experiment to the experiment with a pad function

Generic transfer lemmas for step 1 of [PS10, Theorem 168.2]: a fixed-length private-key scheme
whose encryption with a key is `⟨r, m ⊕ f(r)⟩` with a uniform nonce `r`, and whose decryption is
`⟨1, v ⊕ f(x)⟩` on well-formed `⟨x, v⟩` and `⊥` otherwise, has, call by call, the oracles
`PRFGame.fImpl` with the pad function `f` under CPA and CCA1 (`expect_indImpl_fImpl`). The game's
codec is a bit codec (`indCodec_eq_bitCodec`), and the experiment with `f` is transported along
equal lengths (`expect_fImpl_transport`).

## Main results

* `PRFGame.expect_indImpl_fImpl`: one call of `IND_b` has the law of `fImpl`.
* `PRFGame.indCodec_eq_bitCodec`, `PRFGame.expect_fImpl_transport`.
* `PRFGame.padFin_nil`, `padFin_replicate_false`, `ofFn_arrowCongr_finCongr`:
  vector readings.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 99.1 and Theorem 168.2 (book pp. 99, 168).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

/-- Reading a vector at an equal width keeps its word:
`⟦(arrowCongr (finCongr h) (refl Bool)) v⟧ = ⟦v⟧`. -/
theorem ofFn_arrowCongr_finCongr {a b : ℕ} (h : a = b) (v : Fin a → Bool) :
    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) v) = List.ofFn v := by
  subst h
  rfl


/-- An all-`false` list reads as the all-`false` vector at every width:
`padFin d (List.replicate m false) = zeroBits d`. -/
theorem padFin_replicate_false (d m : ℕ) : padFin d (List.replicate m false) = zeroBits d := by
  rw [← ofFn_zeroBits, AdaptiveCPA.padFin_ofFn_zeroBits]

/-- The empty list reads as the all-`false` vector: `padFin d [] = zeroBits d`. -/
theorem padFin_nil (d : ℕ) : padFin d [] = zeroBits d := padFin_replicate_false d 0


/-- **One call of `IND_b` with the key `key` has the law of `fImpl` with the pad function `fk`**
(CPA or CCA1), for every function `g` of the answer and the new state, for a scheme `S` whose
encryption with `key` is `ctOf` with the nonce `ν re` of a bijection `ν` (`henc`), whose
decryption is `⟨1, v ⊕ fk(x)⟩` on well-formed `⟨x, v⟩` and `⊥` otherwise (`hdec`), with
`(3n + 2)`-bit ciphertexts:
`𝔼[g] (S.indImpl (atkOf atkBit) b n key i x s) = 𝔼[g] (fImpl … fk i x s)`.

**Proof sketch.** By the oracle (the `_onSpec` readers). Encryption and the first challenge
sample the coins of `Enc`, which are the nonce (`expect_sample_equiv ν`), and encrypt as `ctOf`;
the selected half is `msgOf` (`ofFn_splitHalf_fst`, `_snd`). Decryption is open only before the
challenge (CCA1) or never (CPA), so the refusal of the challenge is vacuous; its coins are unused
(`expect_const`). A repeated challenge returns the record. -/
theorem expect_indImpl_fImpl (S : FixedLengthScheme) (atkBit b : Bool) (n : ℕ)
    (key : List Bool) (fk : (Fin n → Bool) → (Fin n → Bool)) (hct : S.ctLen.eval n = 3 * n + 2)
    (ν : S.enc.Coins n ≃ (Fin n → Bool))
    (henc : ∀ (m : Fin n → Bool) (re : S.enc.Coins n),
      List.ofFn (S.encryptAt n key m re) = ctOf (ν re) (List.ofFn m) (fk (ν re)))
    (hdec : ∀ (w : List Bool) (rd : S.dec.Coins n),
      List.ofFn (FixedLengthScheme.decAnswer (decodeFin n
          (S.dec.runAt n (pairEncode key w) rd))) =
        if decWF n w then
          true :: List.zipWith xor (pairSndD w) (List.ofFn (fk (padFin n (pairFstD w))))
        else List.replicate (n + 1) false)
    (i : Fin 3) (x : (S.indSpec n).dom i) (s : Option (Fin (S.ctLen.eval n) → Bool))
    (g : (S.indSpec n).rng i × Option (Fin (S.ctLen.eval n) → Bool) → ℝ) :
    expect (S.indImpl (atkOf atkBit) b n key i x s) g =
      expect (fImpl (S.inLens n) (S.outLens n) (S.ctLen.eval n) n (atkOf atkBit) b (fk) i x s)
        g := by
  have hlenCt : ∀ (r : Fin n → Bool) {m : List Bool}, m.length = n → ∀ y : Fin n → Bool,
      (ctOf r m y).length = S.ctLen.eval n := fun r m hm y => by rw [length_ctOf r hm, hct]
  match i, x with
  | 0, m =>
    rw [S.indImpl_enc_onSpec, fImpl_enc, expect_bind, expect_bind, ← expect_sample_equiv ν]
    refine congrArg _ (funext fun re => ?_)
    rw [expect_pure, expect_pure]
    have hm : List.ofFn (cast (S.indSpec_encDom n) m) = List.ofFn m :=
      AdaptiveCPA.ofFn_cast (S.inLens_zero n) _ m
    have hm' : cast (S.indSpec_encDom n) m = padFin n (List.ofFn m) :=
      List.ofFn_injective (by rw [hm, GGMRed.ofFn_padFin_of_length (by
        rw [List.length_ofFn, S.inLens_zero])])
    congr 2
    refine List.ofFn_injective ?_
    rw [AdaptiveCPA.ofFn_cast (S.outLens_zero n).symm _ _, hm', henc,
      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, S.inLens_zero]),
      GGMRed.ofFn_padFin_of_length (by
        rw [hlenCt _ (by rw [List.length_ofFn, S.inLens_zero]), S.outLens_zero])]
  | 1, c =>
    rw [S.indImpl_dec_onSpec, fImpl_dec, decOpen_atkOf]
    have hc : List.ofFn (cast (S.indSpec_decDom n) c) = List.ofFn c :=
      AdaptiveCPA.ofFn_cast (S.inLens_one n) _ c
    by_cases hop : (atkBit && !s.isSome) = true
    · have hs : s = none := by
        cases s with
        | none => rfl
        | some _ => simp at hop
      subst hs
      rw [if_pos (by simpa using hop), expect_bind]
      refine (congrArg _ (funext fun rd => ?_)).trans (expect_const _ _)
      rw [expect_pure, expect_pure]
      congr 2
      refine List.ofFn_injective ?_
      rw [AdaptiveCPA.ofFn_cast (S.outLens_one n).symm _ _, hc, hdec, decAns_eq, hop, Bool.true_and]
      by_cases hw : decWF n (List.ofFn c) = true
      · rw [if_pos hw, if_pos hw]
        rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hw
        rw [GGMRed.ofFn_padFin_of_length (by
          rw [List.length_cons, List.length_zipWith, List.length_ofFn, hw.2, Nat.min_self,
            S.outLens_one])]
      · rw [if_neg hw, if_neg hw, padFin_nil, ofFn_zeroBits, S.outLens_one]
    · rw [Bool.not_eq_true] at hop
      rw [if_neg (by rw [hop, Bool.false_and]; exact Bool.false_ne_true), decAns_eq, hop,
        Bool.false_and, if_neg Bool.false_ne_true, expect_pure, expect_pure, padFin_nil]
  | 2, mm =>
    have hmm : List.ofFn (cast (S.indSpec_challengeDom n) mm) = List.ofFn mm :=
      AdaptiveCPA.ofFn_cast (S.inLens_two n) _ mm
    have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn mm)).length = n := by
      have : (List.ofFn mm).length = n + n := by rw [List.length_ofFn, S.inLens_two]
      rw [AdaptiveCPA.msgOf_eq]
      cases b <;> simp [this]
    have hsel : (if b then (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) mm)).2 else (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) mm)).1) =
        padFin n (AdaptiveCPA.msgOf n b (List.ofFn mm)) := by
      refine List.ofFn_injective ?_
      rw [GGMRed.ofFn_padFin_of_length hmsg, AdaptiveCPA.msgOf_eq, ← hmm]
      cases b
      · exact AdaptiveCPA.ofFn_splitHalf_fst _
      · exact AdaptiveCPA.ofFn_splitHalf_snd _
    cases s with
    | some c =>
      rw [S.indImpl_challenge_repeat_onSpec, fImpl_challenge_some, expect_pure, expect_pure]
      congr 2
      refine List.ofFn_injective ?_
      rw [AdaptiveCPA.ofFn_cast (S.outLens_two n).symm _ _,
        GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, S.outLens_two])]
    | none =>
      rw [S.indImpl_challenge_none_onSpec, fImpl_challenge_none, expect_bind, expect_bind,
        ← expect_sample_equiv ν]
      refine congrArg _ (funext fun re => ?_)
      simp only [expect_pure]
      have henc' : List.ofFn (S.encryptAt n key (if b then (FixedLengthScheme.splitHalf
          (cast (S.indSpec_challengeDom n) mm)).2 else (FixedLengthScheme.splitHalf
          (cast (S.indSpec_challengeDom n) mm)).1) re) =
          ctOf (ν re) (AdaptiveCPA.msgOf n b (List.ofFn mm)) (fk (ν re)) := by
        rw [hsel, henc, GGMRed.ofFn_padFin_of_length hmsg]
      congr 2
      · refine List.ofFn_injective ?_
        rw [AdaptiveCPA.ofFn_cast (S.outLens_two n).symm _ _, henc',
          GGMRed.ofFn_padFin_of_length (by rw [hlenCt _ hmsg, S.outLens_two])]
      · congr 1
        refine List.ofFn_injective ?_
        rw [henc', GGMRed.ofFn_padFin_of_length (hlenCt _ hmsg _)]


/-- **The game's codec is the bit codec of its lengths:**
`S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1` (the three codec readers and structure
eta). -/
theorem indCodec_eq_bitCodec (S : FixedLengthScheme) (n : ℕ) :
    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := by
  have hd : (S.indCodec n).decodeMove = (bitCodec (S.inLens n) (S.outLens n) 1).decodeMove :=
    funext fun w => (S.indCodec_decodeMove n w).trans (bitCodec_decodeMove _ _ _ w).symm
  have he : (S.indCodec n).encodeEntry = (bitCodec (S.inLens n) (S.outLens n) 1).encodeEntry :=
    funext fun e => (S.indCodec_encodeEntry n e).trans (bitCodec_encodeEntry _ _ _ e).symm
  have ht : (S.indCodec n).timeout = (bitCodec (S.inLens n) (S.outLens n) 1).timeout :=
    (S.indCodec_timeout n).trans (bitCodec_timeout _ _ _).symm
  calc S.indCodec n = ⟨(S.indCodec n).decodeMove, (S.indCodec n).encodeEntry,
        (S.indCodec n).timeout⟩ := rfl
    _ = ⟨(bitCodec (S.inLens n) (S.outLens n) 1).decodeMove,
        (bitCodec (S.inLens n) (S.outLens n) 1).encodeEntry,
        (bitCodec (S.inLens n) (S.outLens n) 1).timeout⟩ := by rw [hd, he, ht]
    _ = bitCodec (S.inLens n) (S.outLens n) 1 := rfl


/-- **The game with pad function `f` along equal lengths:** for `ins = ins'`, `outs = outs'` and
`d = d'`, the expected first output bit of `A`'s run against `fImpl` agrees.

**Proof sketch.** Substitute the equalities. -/
theorem expect_fImpl_transport {ins ins' outs outs' : Fin 3 → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d') (n : ℕ) (atk : Attack) (b : Bool)
    (f : (Fin n → Bool) → (Fin n → Bool)) (A : NUPPT) (Q : ℕ) (r : A.Coins n) :
    expect (simulate (fImpl ins outs d n atk b f) (A.toComp (bitCodec ins outs 1) n Q r) none)
        (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) =
      expect (simulate (fImpl ins' outs' d' n atk b f) (A.toComp (bitCodec ins' outs' 1) n Q r)
        none) (fun p => if (List.ofFn p.1).headD false = true then (1 : ℝ) else 0) := by
  subst hi ho hd
  rfl

end TCSlib.Cryptography.Composability.PRFGame

## ===== TCSlib/Cryptography/Encryption/PrivateKey/OracleSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Encryption.PrivateKey.Scheme
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CPA, CCA1 and CCA2 security of private-key encryption (definitions)

[PS10, Definition 168.1], the first definition of ch. 7 (prong C of the ch. 5–8 campaign), stated
as a game of the `Games` framework over the ch. 2–4 layer's `PrivateKeyScheme`.

**The experiment** `IND_b^{O₁,O₂}(Π, A, n)`: `k ← Gen(1^n)`; `(m₀, m₁, state) ← A^{O₁(k)}(1^n)`;
`c ← Enc_k(m_b)`; output `A^{O₂(k)}(c, state)`. The oracle pairs are `[Enc; Enc]` (CPA),
`[Enc, Dec; Enc]` (CCA1) and `[Enc, Dec; Enc, Dec]` (CCA2). Under CCA2, `Dec` returns `⊥` on the
challenge `c`.

**Its encoding.** One machine plays both phases against three bit-string oracles:
- `Enc` (`n`-bit messages, `ct(n)`-bit ciphertexts);
- `Dec` (`ct(n)`-bit ciphertexts; an `(n + 1)`-bit answer, a validity flag followed by the message);
- `Challenge`, which takes `⟨m₀, m₁⟩` and returns `c ← Enc_k(m_b)`.

The oracles' state remembers the challenge, once asked. That state decides the phase: `Dec` answers
never (CPA), before the challenge only (CCA1), or always, except on `c` itself (CCA2). A refused
`Dec` query, or a repeated challenge, gets a fixed answer. The machine's final output is one bit.

**Deviations, declared once here.**
- **One machine for both phases.** The source's two-phase adversary passes `state` from phase 1
  to phase 2. Here a single next-move machine plays both phases, and its query log (which includes
  the challenge `c`) is that state. Either form simulates the other, at polynomial cost.
- **Fixed-length ciphertexts.** The scheme's ciphertexts at parameter `n` have exactly `ct(n)`
  bits (`FixedLengthScheme`), as the oracle codec needs.
- **Query budgets.** The adversary's number of oracle queries is an explicit polynomial `q`,
  universally quantified, as in the ch. 2–4 layer's `OracleEnsemble.Indist`.
- **Indistinguishability** of the two one-bit outputs is a negligible distinguishing advantage
  between the games for `b = 0` and `b = 1`.

## Main definitions

* `Composability.Attack`: CPA, CCA1, CCA2.
* `Composability.FixedLengthScheme`: a `PrivateKeyScheme` with fixed-length ciphertexts.
* `FixedLengthScheme.indImpl`, `FixedLengthScheme.indGame`: the oracles and the experiment
  `IND_b`.
* `FixedLengthScheme.INDSecure`: [PS10, Definition 168.1].

## Main results

* `indImpl_dec_cpa`, `indImpl_dec_cca2_challenge`, `indImpl_challenge_repeat`: sanity checks of
  the oracles (CPA's `Dec` is closed; CCA2's `Dec` refuses the challenge; a challenge is asked
  once).

The theorems on these notions (Thms 168.2 and 170.4, Claim 169.a) are stated in the statement
phase of prong C, in their own modules.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.1, Definition 168.1 (book p. 168).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-- The three attacks of [PS10, Definition 168.1]. -/
inductive Attack : Type where
  /-- Chosen-plaintext: `[Enc; Enc]`. -/
  | cpa
  /-- Non-adaptive chosen-ciphertext: `[Enc, Dec; Enc]`. -/
  | cca1
  /-- Adaptive chosen-ciphertext: `[Enc, Dec; Enc, Dec]`, `Dec` refusing the challenge. -/
  | cca2
  deriving DecidableEq

/-- A **private-key encryption scheme with fixed-length ciphertexts**: every encryption of an
`n`-bit message under a generated key has exactly `ct(n)` bits. -/
structure FixedLengthScheme extends PrivateKeyScheme where
  /-- The ciphertext length `ct(n)`. -/
  ctLen : PolyExpr
  /-- Ciphertexts of `n`-bit messages under generated keys have `ct(n)` bits. -/
  enc_length : ∀ n (rg : gen.Coins n) (m : Fin n → Bool) (r : enc.Coins n),
    (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) r).length = ctLen.eval n

namespace FixedLengthScheme

variable (S : FixedLengthScheme)

/-- The query lengths of the three oracles `Enc`, `Dec`, `Challenge` at parameter `n`. -/
def inLens (n : ℕ) : Fin 3 → ℕ
  | 0 => n
  | 1 => S.ctLen.eval n
  | 2 => n + n

/-- The encryption oracle accepts `n`-bit messages. -/
theorem inLens_zero (n : ℕ) : S.inLens n 0 = n := rfl

/-- The decryption oracle accepts ciphertexts of the fixed ciphertext length. -/
theorem inLens_one (n : ℕ) : S.inLens n 1 = S.ctLen.eval n := rfl

/-- The challenge oracle accepts a pair of `n`-bit messages. -/
theorem inLens_two (n : ℕ) : S.inLens n 2 = n + n := rfl

/-- The answer lengths of the three oracles at parameter `n`; `Dec`'s answer is a validity flag
followed by the message. -/
def outLens (n : ℕ) : Fin 3 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => n + 1
  | 2 => S.ctLen.eval n

/-- Encryption returns the fixed ciphertext length. -/
theorem outLens_zero (n : ℕ) : S.outLens n 0 = S.ctLen.eval n := rfl

/-- Decryption returns a validity bit followed by an `n`-bit message. -/
theorem outLens_one (n : ℕ) : S.outLens n 1 = n + 1 := rfl

/-- The challenge returns the fixed ciphertext length. -/
theorem outLens_two (n : ℕ) : S.outLens n 2 = S.ctLen.eval n := rfl

/-- The three oracles of the experiment at parameter `n`. -/
abbrev indSpec (n : ℕ) : OracleSpec (Fin 3) := bitSpec (S.inLens n) (S.outLens n)

/-- The IND oracle specification has the published input and output lengths. -/
theorem indSpec_eq (n : ℕ) : S.indSpec n = bitSpec (S.inLens n) (S.outLens n) := rfl

/-- Whether `Dec` answers, given the attack and whether the challenge has been asked. -/
def decOpen : Attack → Bool → Bool
  | .cpa, _ => false
  | .cca1, challenged => !challenged
  | .cca2, _ => true

/-- CPA never opens the decryption oracle. -/
theorem decOpen_cpa (challenged : Bool) : decOpen .cpa challenged = false := rfl

/-- CCA1 opens decryption exactly before the challenge. -/
theorem decOpen_cca1 (challenged : Bool) : decOpen .cca1 challenged = !challenged := rfl

/-- CCA2 always opens decryption, with the challenge refusal checked separately. -/
theorem decOpen_cca2 (challenged : Bool) : decOpen .cca2 challenged = true := rfl

/-- The ciphertext `Enc_k(m)` with coins `r`, read at `ct(n)` bits. -/
def encryptAt (n : ℕ) (k : List Bool) (m : Fin n → Bool) (r : S.enc.Coins n) :
    Fin (S.ctLen.eval n) → Bool :=
  padFin _ (S.enc.runAt n (pairEncode k (List.ofFn m)) r)

/-- Encryption is the padded reading of the underlying encryption machine's output. -/
theorem encryptAt_eq (n : ℕ) (k : List Bool) (m : Fin n → Bool) (r : S.enc.Coins n) :
    S.encryptAt n k m r = padFin (S.ctLen.eval n)
      (S.enc.runAt n (pairEncode k (List.ofFn m)) r) := rfl

/-- `Dec`'s answer `⟨1, m⟩` on a valid decryption `m`, and the all-`false` `⊥` otherwise. -/
def decAnswer {n : ℕ} : Option (Fin n → Bool) → (Fin (n + 1) → Bool)
  | some m => Fin.cons (α := fun _ => Bool) true m
  | none => zeroBits _

/-- A successful decryption is prefixed by its `true` validity bit. -/
theorem decAnswer_some {n : ℕ} (m : Fin n → Bool) :
    decAnswer (some m) = Fin.cons (α := fun _ => Bool) true m := rfl

/-- Failed decryption is the all-false answer. -/
theorem decAnswer_none (n : ℕ) : decAnswer (n := n) none = zeroBits (n + 1) := rfl

/-- The first and the second `n` bits of a `2n`-bit query: the challenge messages `m₀, m₁`. -/
def splitHalf {n : ℕ} (x : Fin (n + n) → Bool) : (Fin n → Bool) × (Fin n → Bool) :=
  (fun i => x (Fin.castAdd n i), fun j => x (Fin.natAdd n j))

/-- The first half of a challenge query consists of its first `n` bits. -/
theorem splitHalf_fst {n : ℕ} (x : Fin (n + n) → Bool) :
    (splitHalf x).1 = fun i => x (Fin.castAdd n i) := rfl

/-- The second half of a challenge query consists of its final `n` bits. -/
theorem splitHalf_snd {n : ℕ} (x : Fin (n + n) → Bool) :
    (splitHalf x).2 = fun j => x (Fin.natAdd n j) := rfl

/-- **The oracles of `IND_b`** at parameter `n`, for the key `k`; the state is the challenge,
once asked.
- `Enc` answers `Enc_k(m)` with fresh coins.
- `Dec` answers `⟨1, Dec_k(c)⟩` with fresh coins when it is open (`decOpen`) and `c` is not the
  challenge, and `⊥` (all `false`) otherwise; a ciphertext that fails to decrypt is `⊥` as well.
- `Challenge` answers `Enc_k(m_b)` on `⟨m₀, m₁⟩` the first time it is asked, and records it;
  later it repeats the recorded challenge. -/
noncomputable def indImpl (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool) :
    QueryImpl (S.indSpec n) (Option (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, m, s => (ProbComp.sample (S.enc.Coins n)).bind fun r => .pure (S.encryptAt n k m r, s)
  | 1, c, s =>
    if decOpen atk s.isSome && !decide (s = some c) then
      (ProbComp.sample (S.dec.Coins n)).bind fun r =>
        .pure (decAnswer (decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn c)) r)), s)
    else .pure (zeroBits _, s)
  | 2, mm, s =>
    match s with
    | some c => .pure (c, s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (c, some c)

/-- An encryption query samples fresh encryption coins and preserves the challenge state. -/
theorem indImpl_enc (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (m : Fin n → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 0 m st =
      (ProbComp.sample (S.enc.Coins n)).bind fun r => .pure (S.encryptAt n k m r, st) := rfl

/-- Decryption queries test oracle availability and refuse the recorded challenge before
running the decryption machine. -/
theorem indImpl_dec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 1 c st =
      if decOpen atk st.isSome && !decide (st = some c) then
        (ProbComp.sample (S.dec.Coins n)).bind fun r =>
          .pure (decAnswer (decodeFin n (S.dec.runAt n (pairEncode k (List.ofFn c)) r)), st)
      else .pure (zeroBits _, st) := rfl

/-- A first challenge query encrypts the selected half and records that ciphertext. -/
theorem indImpl_challenge_none (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : Fin (n + n) → Bool) :
    S.indImpl atk b n k 2 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (c, some c) := rfl

/-- Under CPA, `Dec` never answers: every decryption query gets `⊥`. -/
theorem indImpl_dec_cpa (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl .cpa b n k 1 c s = .pure (zeroBits _, s) := by
  simp [indImpl, decOpen]

/-- Under CCA2, `Dec` refuses the challenge: on the recorded challenge `c` it answers `⊥`. -/
theorem indImpl_dec_cca2_challenge (b : Bool) (n : ℕ) (k : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl .cca2 b n k 1 c (some c) = .pure (zeroBits _, some c) := by
  simp [indImpl, decOpen]

/-- A repeated challenge query returns the recorded challenge and changes nothing. -/
theorem indImpl_challenge_repeat (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : Fin (n + n) → Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n k 2 mm (some c) = .pure (c, some c) := rfl

/-- The encryption oracle accepts an `n`-bit message:
`(S.indSpec n).dom 0 = (Fin n → Bool)`. -/
theorem indSpec_encDom (n : ℕ) : (S.indSpec n).dom 0 = (Fin n → Bool) := by
  rw [S.indSpec_eq, bitSpec_dom, S.inLens_zero]

/-- The encryption oracle answers a ciphertext at the fixed ciphertext width:
`(S.indSpec n).rng 0 = (Fin (S.ctLen.eval n) → Bool)`. -/
theorem indSpec_encRng (n : ℕ) : (S.indSpec n).rng 0 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_rng, S.outLens_zero]

/-- The decryption oracle accepts a ciphertext at the fixed ciphertext width:
`(S.indSpec n).dom 1 = (Fin (S.ctLen.eval n) → Bool)`. -/
theorem indSpec_decDom (n : ℕ) : (S.indSpec n).dom 1 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_dom, S.inLens_one]

/-- The decryption oracle answers a validity bit followed by an `n`-bit message:
`(S.indSpec n).rng 1 = (Fin (n + 1) → Bool)`. -/
theorem indSpec_decRng (n : ℕ) : (S.indSpec n).rng 1 = (Fin (n + 1) → Bool) := by
  rw [S.indSpec_eq, bitSpec_rng, S.outLens_one]

/-- A challenge query contains two `n`-bit messages:
`(S.indSpec n).dom 2 = (Fin (n + n) → Bool)`. -/
theorem indSpec_challengeDom (n : ℕ) : (S.indSpec n).dom 2 = (Fin (n + n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_dom, S.inLens_two]

/-- The challenge oracle answers a ciphertext at the fixed ciphertext width:
`(S.indSpec n).rng 2 = (Fin (S.ctLen.eval n) → Bool)`. -/
theorem indSpec_challengeRng (n : ℕ) : (S.indSpec n).rng 2 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_eq, bitSpec_rng, S.outLens_two]

/-- The decryption equation on the query specification's type: with `c' = cast _ c` the
ciphertext read at width `ct(n)`, `S.indImpl atk b n k 1 c st` is
`if decOpen atk st.isSome && !decide (st = some c')` then a fresh `r ← Dec.Coins n` and the answer
`cast _ (decAnswer (decodeFin n (Dec.runAt n ⟨k, c'⟩ r)))` with state `st`, else `⊥` with `st`. -/
theorem indImpl_dec_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (c : (S.indSpec n).dom 1) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 1 c st =
      if decOpen atk st.isSome && !decide (st = some (cast (S.indSpec_decDom n) c)) then
        (ProbComp.sample (S.dec.Coins n)).bind fun r =>
          .pure (cast (S.indSpec_decRng n).symm (decAnswer (decodeFin n
            (S.dec.runAt n (pairEncode k (List.ofFn (cast (S.indSpec_decDom n) c))) r))), st)
      else .pure (zeroBits _, st) := by
  simpa only [cast_eq] using S.indImpl_dec atk b n k c st

/-- The fresh challenge equation on the query specification's type: with
`⟨m₀, m₁⟩ = splitHalf (cast _ mm)`, `S.indImpl atk b n k 2 mm none` draws `r ← Enc.Coins n`,
sets `c = S.encryptAt n k m_b r`, and returns `cast _ c` with the state `some c`. -/
theorem indImpl_challenge_none_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : (S.indSpec n).dom 2) :
    S.indImpl atk b n k 2 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let halves := splitHalf (cast (S.indSpec_challengeDom n) mm)
        let c := S.encryptAt n k (if b then halves.2 else halves.1) r
        .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_none atk b n k mm

/-- The encryption equation on the query specification's type: with `m' = cast _ m` the message
read at width `n`, `S.indImpl atk b n k 0 m st` draws `r ← Enc.Coins n` and answers
`cast _ (S.encryptAt n k m' r)`, keeping the state `st`. -/
theorem indImpl_enc_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (m : (S.indSpec n).dom 0) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n k 0 m st =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        .pure (cast (S.indSpec_encRng n).symm (S.encryptAt n k (cast (S.indSpec_encDom n) m) r),
          st) := by
  simpa only [cast_eq] using S.indImpl_enc atk b n k m st

/-- The repeated challenge equation on the query specification's type:
`S.indImpl atk b n k 2 mm (some c) = pure (cast _ c, some c)`, the recorded ciphertext `c` read at
the challenge oracle's answer type. -/
theorem indImpl_challenge_repeat_onSpec (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool)
    (mm : (S.indSpec n).dom 2) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n k 2 mm (some c) = .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_repeat atk b n k mm c

/-- The codec of the adversary: the three oracles, and a one-bit final output. -/
def indCodec (n : ℕ) : MachineCodec (S.indSpec n) (Fin 1 → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) 1

/-- The IND codec decodes a move using the bit-string decoder at its oracle lengths. -/
theorem indCodec_decodeMove (n : ℕ) (w : List Bool) :
    (S.indCodec n).decodeMove w = decodeBitMove (S.inLens n) (S.outLens n) 1 w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) 1 w

/-- The IND codec records a log entry as the oracle index paired with its query and answer. -/
theorem indCodec_encodeEntry (n : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.indCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) 1 e

/-- The IND codec returns the false verdict when its budget expires. -/
theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
  bitCodec_timeout (S.inLens n) (S.outLens n) 1

/-- **The experiment `IND_b^{O₁,O₂}(Π, A, n)`** [PS10, Definition 168.1] for the attack `atk`, with
query budget `q`: sample `k ← Gen(1^n)` and `A`'s coins, run `A` against the oracles of `IND_b`
from the unchallenged state, and output its bit. -/
noncomputable def indGame (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.indImpl atk b n (S.gen.runAt n [] rg)) (A.toComp (S.indCodec n) n q r) none).bind
    fun res => .pure (res.1 0)

/-- The IND experiment samples keys and adversary coins, simulates the recorded oracle
interaction from the unchallenged state, and returns the final bit. -/
theorem indGame_eq (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.indGame atk A q b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.indImpl atk b n (S.gen.runAt n [] rg))
        (A.toComp (S.indCodec n) n q r) none).bind fun res => .pure (res.1 0) := rfl

/-- **CPA, CCA1 or CCA2 security** [PS10, Definition 168.1]: for every non-uniform PPT `A` and
every polynomial query budget, `IND_0` and `IND_1` are indistinguishable: `A`'s advantage between
them is negligible. -/
def INDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.indGame atk A (q.eval n) false n) (S.indGame atk A (q.eval n) true n) ≤ ε n

/-- IND security is exactly negligible advantage for every PPT adversary and polynomial
query budget, uniformly over the security parameter. -/
theorem INDSecure_iff (atk : Attack) :
    S.INDSecure atk ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, advantage (S.indGame atk A (q.eval n) false n)
        (S.indGame atk A (q.eval n) true n) ≤ ε n := Iff.rfl

end FixedLengthScheme

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Encryption/PrivateKey/FromPRF.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreLoops
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Multi-message secure encryption from a pseudorandom function

The key generator samples a key. The encryptor samples an independent point, masks the
message with the function value at that point, and returns the point with the masked message.
Decryption recomputes the mask and checks the ciphertext format [PS10, Algorithm 99.1].

## Main definitions

* `prfEncFun`, `prfDecFun` and `prfScheme` implement the scheme from a polynomial-time evaluator.
* `encodeTuple` encodes the fixed vector of ciphertext pairs as a string.

## Main results

* `prfScheme_multiEncDist` identifies the ciphertext sampler with the encoded real hybrid.
* `prfScheme_multiMessageSecure` lifts the six-hybrid bound to a negligible advantage against
  non-uniform polynomial-time distinguishers [PS10, Theorem 99.2].
* `exists_multiMessageSecure_of_prf` and `exists_multiMessageSecure_of_exists_prg` give the
  existence results from a PRF and, via GGM, from a PRG.

## Contents

* `FromPRF.Hybrid` proves the concrete six-hybrid bound.
* `FromPRF.HybridLemmas` supplies the collision and coin-relabelling estimates.
* `FromPRF.ReductionMachine` implements the next-query reduction and proves its run agreement.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### The scheme of [PS10, Algorithm 99.1] -/

/-- The raw string function of `Enc` of [PS10, Algorithm 99.1]: on the machine layout
`⟨⟨⟨1^n, ⟨k, w⟩⟩, α⟩, r⟩` output the pair `⟨r, w ⊕ E(⟨k, r⟩)⟩`, where `E` evaluates the PRF on
`⟨key, input⟩` and the coin string `r` is the fresh point. -/
def prfEncFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode (NUPPT.inCoins z)
    (List.zipWith xor (pairSndD (NUPPT.inArg z))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (NUPPT.inCoins z))))

/-- Whether the ciphertext `⟨r, c⟩` of the layout `⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` has `n`-bit
components: the domain of `Dec` in [PS10, Algorithm 99.1]. -/
def prfDecWF (z : List Bool) : Bool :=
  decide ((pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length) &&
    decide ((pairSndD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length)

/-- The raw string function of `Dec` of [PS10, Algorithm 99.1]: on the layout
`⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` with `n`-bit `r` and `c`, output `c ⊕ E(⟨k, r⟩)`; on any other
ciphertext, output `⊥`, here the `(n + 1)`-bit string `1^{n+1}`, which decodes to no message.

The source defines `Dec` on pairs of `n`-bit strings only. The guard matters under
chosen-ciphertext attacks: `E` agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`, so without it a
malformed ciphertext would evaluate `E` where it is unconstrained, and there it may reveal the
key. -/
def prfDecFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  if prfDecWF z then
    List.zipWith xor (pairSndD (pairSndD (NUPPT.inArg z)))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))))
  else true :: NUPPT.inParam z

/-- `prfEncFun E` is polynomial-time when `E` is: projections, one evaluation of `E`, one
bitwise exclusive-or (`Complexity.polyTimeComputable_pairXor`) and one pairing. -/
theorem polyTimeComputable_prfEncFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfEncFun E) := by
  have h := NUPPT.polyTimeComputable_inCoins.pairEncode
    (polyTimeComputable_pairXor.comp
      ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
          NUPPT.polyTimeComputable_inCoins))))
  convert h using 1
  funext z
  simp [prfEncFun, Function.comp_apply]

/-- The well-formedness test of `Dec` is polynomial-time: two length comparisons
(`Complexity.polyTimeComputable_lenEq`). -/
theorem polyTimeComputable_prfDecWF : PolyTimeComputable (fun z => [prfDecWF z]) := by
  have hl : ∀ g : List Bool → List Bool, PolyTimeComputable g →
      PolyTimeComputable (fun z => [decide ((g z).length = (NUPPT.inParam z).length)]) := by
    intro g hg
    convert polyTimeComputable_lenEq.comp (hg.pairEncode NUPPT.polyTimeComputable_inParam)
      using 1
    funext z
    simp [Function.comp_apply]
  exact polyTimeComputable_and
    (hl _ ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))
    (hl _ ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))

/-- `prfDecFun E` is polynomial-time when `E` is: the guard, then the branch of the old `Dec`
(`Complexity.polyTimeComputable_ite`). -/
theorem polyTimeComputable_prfDecFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfDecFun E) := by
  refine polyTimeComputable_ite polyTimeComputable_prfDecWF ?_
    ((polyTimeComputable_const [true]).append NUPPT.polyTimeComputable_inParam)
  have h := polyTimeComputable_pairXor.comp
    (((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
        NUPPT.polyTimeComputable_inArg).pairEncode
      (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
          NUPPT.polyTimeComputable_inArg))))
  convert h using 1
  funext z
  simp [prfDecFun, Function.comp_apply]

/-- The activation of the encryption machine on `⟨k, w⟩` with coins `r` is
`⟨r, w ⊕ E(⟨k, r⟩)⟩`. -/
theorem runAt_prfEnc {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k w : List Bool)
    (r : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).runAt n (pairEncode k w) r =
      pairEncode (List.ofFn r) (List.zipWith xor w (E (pairEncode k (List.ofFn r)))) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfEncFun, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- The activation of the decryption machine on `⟨k, ⟨r, c⟩⟩` with `n`-bit `r` and `c` is
`c ⊕ E(⟨k, r⟩)`. -/
theorem runAt_prfDec {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k r c : List Bool) (hr : r.length = n) (hc : c.length = n)
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k (pairEncode r c)) r' =
      List.zipWith xor c (E (pairEncode k r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfDecFun, prfDecWF, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq, hr, hc]

/-- On a ciphertext `w` whose two projections `pairFstD w` and `pairSndD w` are not both `n` bits
long, the decryption machine outputs `⊥`: a string that decodes to no `n`-bit message. -/
theorem decodeFin_runAt_prfDec_of_not_wf {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (coins : PolyExpr) (n : ℕ) (k w : List Bool)
    (hw : ¬ ((pairFstD w).length = n ∧ (pairSndD w).length = n))
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    decodeFin n ((NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k w) r') = none := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  have hf : prfDecWF (pairEncode (pairEncode (NUPPT.advInput n (pairEncode k w)) [])
      (List.ofFn r')) = false := by
    simp only [prfDecWF, NUPPT.inArg_eq, NUPPT.inParam_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
      pairSndD_pairEncode, List.length_replicate, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    tauto
  rw [prfDecFun, hf]
  simp [decodeFin_eq, NUPPT.inParam_eq, NUPPT.advInput_eq]

/-- Masking twice with the same pad (at least as long as the message) is the identity
(private copy of the helper of `Encryption/PrivateKey/FromPRG.lean`). -/
private theorem zipWith_xor_xor_self : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, b :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases b <;> rfl, zipWith_xor_xor_self m p (by simpa using h)⟩

/-- **The many-message encryption scheme of [PS10, Algorithm 99.1]** for a function family
`F` with polynomial-time evaluator `E` on `⟨s, x⟩`: `Gen(1^n)` outputs a uniform `n`-bit key
`k` (its coin string); `Enc_k(m)` draws `r ← U_n` (its coin string) and outputs
`⟨r, m ⊕ f_k(r)⟩`; `Dec_k(⟨r, c⟩) = c ⊕ f_k(r)` (deterministic, coins `const 0`). Correctness is
`(m ⊕ p) ⊕ p = m` with the `n`-bit pad `p = f_k(r)`.

**Deviation:** `prfScheme`: the key is the `n`-bit coin string of `Gen`; `Enc` draws its `n`-bit
`r` as its coin string; the evaluator `E` of the PRF is an explicit argument rather than
extracted from `PRF.easy`; ciphertexts are the pair `⟨r, m ⊕ f_k(r)⟩`. -/
noncomputable def prfScheme (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    PrivateKeyScheme where
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  enc := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var
  dec := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    rw [runAt_coinKey, runAt_prfEnc hE]
    have h : E (pairEncode (List.ofFn rg) (List.ofFn re)) =
        List.ofFn (F n (NUPPT.coinsEquiv_ofPolyTimeUniform _ _ n rg)
          (NUPPT.coinsEquiv_ofPolyTimeUniform _ _ n re)) := by
      rw [← hFE, NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn]
    have hre : (List.ofFn re).length = n := by
      rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n re, List.length_ofFn, PolyExpr.eval_var]
    rw [h, runAt_prfDec hE _ _ _ _ _ hre (by simp), h,
      zipWith_xor_xor_self _ _ (by simp), decodeFin_ofFn]

/-- The key generator of `prfScheme` is the uniform machine returning its coin string
[PS10, Algorithm 99.1]. -/
theorem prfScheme_gen (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).gen = NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var := rfl

/-- The encryptor of `prfScheme` uses its raw encryption function and `n` coins
[PS10, Algorithm 99.1]. -/
theorem prfScheme_enc (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).enc =
      NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var := rfl

/-- The decryption machine of `prfScheme F E hE hFE` is
`NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0)`. -/
theorem prfScheme_dec (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
      List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).dec =
      NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0) := rfl

/-- The encoding of a tuple of ciphertext pairs `(r_j, c_j)_j` as the string handed to a
distinguisher: `encodeList` of the pairs `⟨r_j, c_j⟩`. -/
def encodeTuple {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))

/-- `encodeList l` is the concatenation of the self-delimited chunks `⟨c, []⟩`, `c ∈ l`. -/
private theorem encodeList_eq_flatMap : ∀ l : List (List Bool),
    PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
  | [] => by rw [PrivateKeyScheme.encodeList_nil, List.flatMap_nil]
  | c :: l => by
    rw [PrivateKeyScheme.encodeList_cons, List.flatMap_cons, encodeList_eq_flatMap l]
    simp [pairEncode_eq]

/-- The encoded ciphertext tuple is the concatenation of the chunks `⟨⟨r_j, c_j⟩, []⟩` (the
form in which the next-query machine of `MultiMsg.exists_queryChain_nuppt` produces it). -/
theorem encodeTuple_eq_flatten {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :
    encodeTuple v =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten := by
  rw [encodeTuple, encodeList_eq_flatMap, MultiMsg.flatMap_ofFn]

/-- **The coins of the multi-message experiment of Algorithm 99.1 are bit strings**: the key
coins of `Gen` and the `q + 1` coin strings of `Enc` are `n`-bit strings,
`gen.Coins n × (Fin (q + 1) → enc.Coins n) ≃ {0,1}^n × ({0,1}^n)^{q+1}` (the published coin
identifications `NUPPT.coinsEquiv_ofPolyTimeUniform`; they keep every coin string). -/
noncomputable def prfScheme_coinsEquiv (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ) :
    (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n) ≃
      (Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) :=
  (NUPPT.coinsEquiv_ofPolyTimeUniform polyTimeComputable_pairSndD .var n).prodCongr
    (Equiv.piCongrRight fun _ =>
      NUPPT.coinsEquiv_ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var n)

/-- The coin equivalence of the multi-message experiment keeps every coin string: the key,
`List.ofFn (prfScheme_coinsEquiv … r).1 = List.ofFn r.1`, and each point,
`List.ofFn ((prfScheme_coinsEquiv … r).2 j) = List.ofFn (r.2 j)`. -/
theorem prfScheme_coinsEquiv_ofFn (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ)
    (r : (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n)) :
    List.ofFn (prfScheme_coinsEquiv F E hE hFE n q r).1 = List.ofFn r.1 ∧
      ∀ j, List.ofFn ((prfScheme_coinsEquiv F E hE hFE n q r).2 j) = List.ofFn (r.2 j) :=
  ⟨NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n r.1,
    fun j => NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn _ _ n (r.2 j)⟩

/-- **The ciphertext tuple of Algorithm 99.1** is the encoding of the hybrid `H¹`: for the key
`k` and the points `r_j` read off the coins `r` (`prfScheme_coinsEquiv`),
`multiEncDist n q m r = encodeTuple (prfEncReal (F n) m (prfScheme_coinsEquiv … r))`.

**Proof sketch.** `multiEncDist_apply` writes the left side as `encodeList` of the encryptions
`Enc_k(m_j; r_j)`; the key machine outputs its coin string (`runAt_coinKey`) and the encryption
machine outputs `⟨r_j, m_j ⊕ E(⟨k, r_j⟩)⟩` (`runAt_prfEnc`). The coin strings are those of
`prfScheme_coinsEquiv … r` (`prfScheme_coinsEquiv_ofFn`), so `hFE` turns `E(⟨k, r_j⟩)` into
`F n k r_j` and `zipWith_xor_ofFn_add` gives the `j`-th pair of `prfEncReal`. -/
theorem prfScheme_multiEncDist (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool)
    (r : (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n)) :
    (prfScheme F E hE hFE).multiEncDist n q m r =
      encodeTuple (prfEncReal (F n) m (prfScheme_coinsEquiv F E hE hFE n q r)) := by
  rw [PrivateKeyScheme.multiEncDist_apply, encodeTuple]
  congr 1
  congr 1
  funext j
  show (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var).runAt n
    (pairEncode ((NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var).runAt n [] r.1)
      (List.ofFn (m j))) (r.2 j) = _
  rw [runAt_coinKey, runAt_prfEnc hE]
  have h1 : List.ofFn r.1 = List.ofFn (prfScheme_coinsEquiv F E hE hFE n q r).1 :=
    (prfScheme_coinsEquiv_ofFn F E hE hFE n q r).1.symm
  have h2 : List.ofFn (r.2 j) = List.ofFn ((prfScheme_coinsEquiv F E hE hFE n q r).2 j) :=
    ((prfScheme_coinsEquiv_ofFn F E hE hFE n q r).2 j).symm
  rw [h1, h2, hFE, zipWith_xor_ofFn_add, prfEncReal_apply]

/-- **[PS10, Theorem 99.2]: the scheme of Algorithm 99.1 is multi-message secure** when `F` is
a pseudorandom function family.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Fix a non-uniform PPT `D` and a budget polynomial `q`. At each `n` choose a
pair of message vectors `(mⁿ, m'ⁿ)` maximizing
`distAdv (multiEncDist n (q n) m) (multiEncDist n (q n) m') (D.distinguisherL n)` over the finite
type of pairs (`Finset.exists_max_image`; the text: "there exists messages `m̄`, `m̄'` … for
infinitely many `n`", hard-wired as advice). *Concrete step:* by `prfScheme_multiEncDist` both
samplers are `encodeTuple ∘ prfEncReal (F n) mⁿ` resp. `m'ⁿ` on the seed space
`K × (Fin (q n + 1) → {0,1}^n)` (the gen coins are the `n`-bit key and the enc coins the points,
definitionally), so with `Dⁿ v c := D.distinguisherL n (encodeTuple v) c` the sunglass identity
`distAdv_comp` and `distAdv_prfEncReal_le` bound the advantage at `n` by
`prfAdv (F n) (multiMsgAdv mⁿ Dⁿ) + prfAdv (F n) (multiMsgAdv m'ⁿ Dⁿ) + 2 · C(q n + 1, 2) / 2^n`
— the six hybrids `H¹, …, H⁶` of the text. *Machine step* (Thm-99.2.1 as an `NUPPT`): for
`v ∈ {m, m'}` the next-query machine `B_v` has advice `⟨encodeList (ofFn (ofFn ∘ vⁿ)), D.advice n⟩`
(`NUPPT.exists_withAdvice`, bound `.add (.mul (.add q (.const 1)) (.add (.mul (.const 2) .var) (.const 2))) D.adv`-style),
coins `(q + 1) · var + D.coins` (`NUPPT.exists_split` with `p := .mul (.add q (.const 1)) .var`: the
first `(q n + 1) n` coins are the points `r₀ … r_{q n}`, read as blocks by
`Complexity.polyTimeComputable_blockMap .var`), and on the encoded history `hist` outputs: if
`|hist| ≤ q n` the query `⟨[false], r_{|hist|}⟩` (history length by `polyTimeComputable_blockMap`
counting, `pairDecode`/`decodeFin` are FP), else the verdict `[true, b]` where `b` is `D`'s
verdict on `encodeTuple (r_j, v_j ⊕ ans_j)_j` (`polyTimeComputable_pairXor` blockwise,
`NUPPT.exists_comp`). By induction on the history, `buildTree` with budget `q n + 1` from `[]`
is the chain `chainTree (q n + 1) r (…)`, i.e.
`B_v.toOracleAdversary n n n (q n + 1) = multiMsgAdv vⁿ Dⁿ` up to the coin bijection
`B_v.Coins n ≃ (Fin (q n + 1) → {0,1}^n) × D.Coins n` (`FunFamily.blocks`, `Fin.appendEquiv`),
so `acceptProb_comp_equiv` gives `prfAdv (F n) (B_v^{(q n + 1)}) = prfAdv (F n) (multiMsgAdv vⁿ Dⁿ)`.
*Asymptotic step:* `hF.negligible_prfAdv B_v (.add q (.const 1))` makes both PRF terms
negligible; the collision term is negligible by `negligible_two_pow_neg` and
`Negligible.mul_pow`/`Negligible.const_mul` with `C(q n + 1, 2) ≤ (q n + 1)^2 ≤ C'(n + 1)^{2d}`
from `PolyExpr.eval_le` (`Nat.choose_le_pow`); `Negligible.add` twice, and by maximality
`ε n := ` this sum bounds the advantage for every `n, m, m'`. -/
theorem prfScheme_multiMessageSecure (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).MultiMessageSecure := by
  refine (PrivateKeyScheme.multiMessageSecure_iff _).2 fun D q => ?_
  -- the worst message pair at each parameter (hard-wired into the reductions)
  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
      ∀ w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n) ≤
          distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.1)
            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.2) (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) =>
        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
          ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun w => hp w (Finset.mem_univ w)⟩
  choose μ hμ using hmax
  -- the next-query machines of Thm-99.2.1 for the two hard-wired message vectors
  obtain ⟨B₀, hB₀⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).1
  obtain ⟨B₁, hB₁⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).2
  refine ⟨fun n => prfAdv (F n) (B₀.toOracleAdversary n n n (q.eval n + 1)) +
      prfAdv (F n) (B₁.toOracleAdversary n n n (q.eval n + 1)) +
      2 * ((Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n), ?_, fun n m m' => ?_⟩
  · -- the asymptotic step: two PRF advantages and the collision term
    simpa only [PolyExpr.eval_add, PolyExpr.eval_const] using
      ((hF.negligible_prfAdv B₀ (.add q (.const 1))).add
        (hF.negligible_prfAdv B₁ (.add q (.const 1)))).add
        ((MultiMsg.negligible_choose_div_two_pow q).const_mul 2)
  · refine (hμ n (m, m')).trans ?_
    -- the concrete step: the ciphertext tuples are `encodeTuple ∘ prfEncReal`
    have key : ∀ m₀ : Fin (q.eval n + 1) → Fin n → Bool,
        (prfScheme F E hE hFE).multiEncDist n (q.eval n) m₀ =
          fun r => encodeTuple (prfEncReal (F n) m₀ (prfScheme_coinsEquiv F E hE hFE n (q.eval n) r)) :=
      fun m₀ => funext fun r => prfScheme_multiEncDist F E hE hFE n (q.eval n) m₀ r
    -- the machine step: the oracle adversaries of `B₀`, `B₁` are the `multiMsgAdv`
    have hadv : ∀ (B : NUPPT) (v : Fin (q.eval n + 1) → Fin n → Bool)
        (φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n),
        (∀ (g : (Fin n → Bool) → (Fin n → Bool)) ρ c,
          (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
            decide (D.runAt n (List.ofFn fun j =>
              pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten c =
                [true])) →
        prfAdv (F n) (B.toOracleAdversary n n n (q.eval n + 1)) =
          prfAdv (F n) (multiMsgAdv v fun w c => D.distinguisherL n (encodeTuple w) c) := by
      intro B v φ hφ
      refine MultiMsg.prfAdv_congr_equiv (F n) _ _ φ fun g w => ?_
      rw [hφ g w.1 w.2, eval_multiMsgAdv, NUPPT.distinguisherL_eq, encodeTuple_eq_flatten]
    obtain ⟨φ₀, hφ₀⟩ := hB₀ n
    obtain ⟨φ₁, hφ₁⟩ := hB₁ n
    dsimp only
    rw [hadv B₀ (μ n).1 φ₀ hφ₀, hadv B₁ (μ n).2 φ₁ hφ₁, key, key, distAdv_def,
      acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
        (fun s => encodeTuple (prfEncReal (F n) (μ n).1 s)),
      acceptProb_comp_equiv (prfScheme_coinsEquiv F E hE hFE n (q.eval n))
        (fun s => encodeTuple (prfEncReal (F n) (μ n).2 s)), ← distAdv_def]
    exact (distAdv_comp encodeTuple (prfEncReal (F n) (μ n).1) (prfEncReal (F n) (μ n).2)
      (D.distinguisherL n)).symm.trans_le (distAdv_prfEncReal_le (F n) (μ n).1 (μ n).2
        (fun w c => D.distinguisherL n (encodeTuple w) c))

/-- **Multi-message secure private-key encryption exists if a PRF exists** ([PS10, §3.9]):
the scheme of Algorithm 99.1 with the evaluator of `PRF.easy`. -/
theorem exists_multiMessageSecure_of_prf {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) : ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨E, hE, hFE⟩ := hF.easy
  ⟨prfScheme F E hE hFE, prfScheme_multiMessageSecure F hF E hE hFE⟩

/-- **Multi-message secure private-key encryption exists if a PRG exists** ([PS10, Theorems
97.3 and 99.2] combined): GGM gives a PRF, Algorithm 99.1 gives the scheme. -/
theorem exists_multiMessageSecure_of_exists_prg (h : ∃ P : PRG, P.Secure) :
    ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨_, hF⟩ := exists_prf_of_exists_prg h
  exists_multiMessageSecure_of_prf hF

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Pseudorandom.Functions.Defs
import TCSlib.Cryptography.Pseudorandom.Functions.LazySampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Asymptotic oracle indistinguishability and pseudorandom functions

An oracle ensemble samples functions at each parameter. The next-query machine
sees the encoded history, uses one coin tape for the interaction, and runs within
an explicit query budget. The pseudorandom function contract combines an efficient
evaluator with indistinguishability from the random oracle [PS10, Definitions 96.1
and 96.2].

The concrete adversaries, random functions, and lazy runs come from [Gar26, §3.4].
The decoder treats malformed moves as rejection. A query after the budget is spent
also gives verdict `false` (foundation decision D7 of `PassShelatChapter2-4Plan.md`).

## Main definitions

* `TCSlib.Cryptography.OracleEnsemble` samples functions from finite seed types.
  `OracleEnsemble.random` uses the function table and `OracleEnsemble.keyed` uses a key.
* `TCSlib.Cryptography.OracleMove`, `decodeOracleMove`, and `encodeHist` specify the
  interface for a next-query machine. `buildTree` and `Complexity.NUPPT.toOracleAdversary`
  turn such a machine into a bounded query tree.
* `TCSlib.Cryptography.OracleEnsemble.Indist` gives the oracle indistinguishability
  condition. `TCSlib.Cryptography.PRF` packages that condition with efficient evaluation.

## Main results

* `TCSlib.Cryptography.acceptProb_random_eq_lazy` equates the two descriptions of a
  random function, by its table and by lazy sampling [PS10, §3.8.1].
* `Complexity.NUPPT.toOracleAdversary_boundedBy` gives the query bound.
* `TCSlib.Cryptography.OracleEnsemble.indist_iff` expresses the contract through
  negligible advantage. `TCSlib.Cryptography.oracle_hybrid_lemma` gives the
  finite hybrid bound for oracle ensembles.
* `TCSlib.Cryptography.prfAdv_toOracleAdversary` and `PRF.negligible_prfAdv`
  connect the PRF contract to the concrete advantage.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.8.1 and §3.8.2, Definitions 96.1 and 96.2.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (Definitions 3.6–3.9).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Oracle ensembles and random functions [PS10, §3.8.1, Definition 96.1] -/

/-- An **oracle ensemble** [PS10, Definition 96.1]: for every parameter `n` a probability
distribution over functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, given (D6/D7) as the pushforward
of the uniform distribution on a finite seed type `σ n` along a sampler `O n`. For the
random-function ensemble the seed is the function table itself (exponentially long, which is
immaterial at the concrete level); for a keyed family the seed is the key.

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries. -/
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where
  /-- The seed type at parameter `n`. -/
  σ : ℕ → Type
  /-- The seed types are finite. -/
  [fintype : ∀ n, Fintype (σ n)]
  /-- The sampler: the oracle determined by a seed. -/
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)

attribute [instance] OracleEnsemble.fintype

/-- **The random function ensemble** `RF_n` [PS10, §3.8.1, combinatorial description]: the
uniform distribution on functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, sampled by its function
table (the "long array" of the text; `randomFunction I O = id`). The text's count
`2^{n 2^n}` of random functions is `Fintype.card_fun`. -/
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂ where
  σ n := (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
  O _ := randomFunction _ _

/-- **A keyed family as an oracle ensemble**: `{s ← U_n : f_s}` for a family
`F n : {0,1}^n → {0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}` (the first clause of the pseudorandomness
condition of [PS10, Definition 96.2]); the seed is the `n`-bit key. -/
def OracleEnsemble.keyed {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) :
    OracleEnsemble ℓ₁ ℓ₂ where
  σ n := Fin n → Bool
  O n := F n

/-- Unfolding: the random-function ensemble samples by the identity on tables. -/
@[simp] theorem OracleEnsemble.random_O (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (R : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) :
    (OracleEnsemble.random ℓ₁ ℓ₂).O n R = R :=
  randomFunction_apply _ _ R

/-- Unfolding: the keyed ensemble samples by `F n`. -/
@[simp] theorem OracleEnsemble.keyed_O {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) (n : ℕ)
    (s : Fin n → Bool) : (OracleEnsemble.keyed F).O n s = F n s := rfl

/-- Acceptance against the random oracle ensemble is acceptance against a uniform function
table, with the same oracle adversary and its coins. -/
theorem OracleEnsemble.acceptProb_random_eq {ρ : Type*} [Fintype ρ] (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (A : OracleAdversary ρ (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) :
    acceptProb ((OracleEnsemble.random ℓ₁ ℓ₂).O n) (oracleDist A) =
      acceptProb (randomFunction (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) (oracleDist A) :=
  rfl

/-- **The two descriptions of a random function agree** [PS10, §3.8.1, "both of the above
descriptions of a random function give rise to identical distributions"] (Claim-95.b): for an
oracle adversary making at most `q` queries, the probability of accepting with the function
table `RF_n` as oracle equals the probability of accepting when every *new* query is answered
by a fresh uniform value and repeated queries by the recorded answer (the computational
description, `QueryTree.evalLazy` with `q` fresh values `extendStream W`).

**Proof sketch.** Both sides are averages over the adversary's coins `r` (Fubini,
`uprob_prod` after swapping the factors with `uprob_prod_comm`); for each fixed `r` the two
inner probabilities agree by the concrete lazy-sampling theorem `QueryTree.uprob_evalLazy`
applied to the tree `A r`. -/
theorem acceptProb_random_eq_lazy {ρ : Type*} [Fintype ρ] (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (A : OracleAdversary ρ (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) {q : ℕ}
    (hA : A.BoundedBy q) :
    acceptProb ((OracleEnsemble.random ℓ₁ ℓ₂).O n) (oracleDist A) =
      acceptProb (fun W : Fin q → (Fin (ℓ₂.eval n) → Bool) => extendStream W) (lazyDist A) := by
  rw [acceptProb_def, acceptProb_def,
    uprob_prod_comm (fun R (r : ρ) => oracleDist A ((OracleEnsemble.random ℓ₁ ℓ₂).O n R) r = true),
    uprob_prod_comm (fun W (r : ρ) => lazyDist A (extendStream W) r = true),
    uprob_prod, uprob_prod]
  congr 1
  funext r
  simp only [OracleEnsemble.random_O, oracleDist_apply, lazyDist_apply]
  exact (QueryTree.uprob_evalLazy (· = true) ((OracleAdversary.boundedBy_iff A q).1 hA r)).symm

/-! ### Next-query machines as oracle adversaries (D7) -/

/-- A move of a next-query oracle machine: either the next query `x ∈ {0,1}^{ℓ₁}` or the
final verdict `b`. -/
inductive OracleMove (ℓ₁ : ℕ)
  /-- Ask the oracle at `x`. -/
  | query (x : Fin ℓ₁ → Bool)
  /-- Stop with the verdict `b`. -/
  | ret (b : Bool)

/-- Decoding of a machine output as a move: `⟨[false], x⟩` with `x` an `ℓ₁`-bit string is the
query `x`; the two-bit string `[true, b]` is the verdict `b`; any other output is the verdict
`false` (D7: ill-formed outputs count as rejection). -/
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁ :=
  match pairDecode w, w with
  | some ([false], x), _ => match decodeFin ℓ₁ x with
    | some x => .query x
    | none => .ret false
  | _, [true, b] => .ret b
  | _, _ => .ret false

/-- The two-bit word `[true, b]` is not a pair: its decoding would start with a doubled bit
(at least four bits) or with the separator `01`. -/
theorem pairDecode_true_two (b : Bool) : pairDecode [true, b] = none := by
  cases h : pairDecode [true, b] with
  | none => rfl
  | some p =>
    obtain ⟨u, v⟩ := p
    have hz := eq_pairEncode_of_pairDecode _ u v h
    rw [pairEncode_eq] at hz
    cases u with
    | nil => simp at hz
    | cons x u =>
      have hl := congrArg List.length hz
      simp only [List.length_cons, List.length_append, List.flatMap_cons, List.length_nil] at hl
      omega

/-- Decoding a pair `⟨[false], x⟩`: the query `x` when `x` has `ℓ₁` bits, else the verdict
`false`: `decodeOracleMove ℓ₁ (pairEncode [false] x) =
match decodeFin ℓ₁ x with | some y => .query y | none => .ret false`. -/
theorem decodeOracleMove_pairEncode_false (ℓ₁ : ℕ) (x : List Bool) :
    decodeOracleMove ℓ₁ (pairEncode [false] x) =
      match decodeFin ℓ₁ x with
      | some y => .query y
      | none => .ret false := by
  unfold decodeOracleMove
  rw [pairDecode_pairEncode, pairEncode_eq]
  rfl

/-- Decoding the two-bit word `[true, b]`: the verdict `b`,
`decodeOracleMove ℓ₁ [true, b] = .ret b`. -/
theorem decodeOracleMove_true_two (ℓ₁ : ℕ) (b : Bool) :
    decodeOracleMove ℓ₁ [true, b] = .ret b := by
  unfold decodeOracleMove
  rw [pairDecode_true_two]

/-- Decoding a well-formed query word: for every `ℓ₁`-bit string `x` (`ℓ₁ = 0` included),
`decodeOracleMove ℓ₁ (pairEncode [false] (List.ofFn x)) = .query x`. -/
theorem decodeOracleMove_pairEncode_ofFn (ℓ₁ : ℕ) (x : Fin ℓ₁ → Bool) :
    decodeOracleMove ℓ₁ (pairEncode [false] (List.ofFn x)) = .query x := by
  rw [decodeOracleMove_pairEncode_false, decodeFin_ofFn]

/-- Decoding a query-shaped word of the wrong length: if `|x| ≠ ℓ₁` then
`decodeOracleMove ℓ₁ (pairEncode [false] x) = .ret false`. -/
theorem decodeOracleMove_pairEncode_false_of_length_ne (ℓ₁ : ℕ) {x : List Bool}
    (hx : x.length ≠ ℓ₁) : decodeOracleMove ℓ₁ (pairEncode [false] x) = .ret false := by
  rw [decodeOracleMove_pairEncode_false]
  cases h : decodeFin ℓ₁ x with
  | none => rfl
  | some y => exact absurd (length_eq_of_decodeFin_eq_some h) hx

/-- **The malformed branch**: a word that is neither a query-shaped pair `⟨[false], x⟩` (for any
string `x`) nor a two-bit verdict word `[true, b]` decodes to the verdict `false`:
`decodeOracleMove ℓ₁ w = .ret false`. Together with `decodeOracleMove_pairEncode_ofFn`,
`decodeOracleMove_pairEncode_false_of_length_ne` and `decodeOracleMove_true_two` this covers every
word, for every `ℓ₁`.

**Proof sketch.** Along the match of `decodeOracleMove`: a decoding
`pairDecode w = some ([false], x)` gives `w = ⟨[false], x⟩` (`eq_pairEncode_of_pairDecode`),
excluded; the word `[true, b]` is excluded; the remaining branch is `.ret false`. -/
theorem decodeOracleMove_of_ne (ℓ₁ : ℕ) {w : List Bool} (hq : ∀ x, w ≠ pairEncode [false] x)
    (hv : ∀ b, w ≠ [true, b]) : decodeOracleMove ℓ₁ w = .ret false := by
  unfold decodeOracleMove
  split
  · rename_i w' o w'' x hx
    exact absurd (eq_pairEncode_of_pairDecode w' _ _ hx) (hq x)
  · rename_i o w' b hp
    exact absurd rfl (hv b)
  · rfl

/-- The encoding of the history of (query, answer) pairs handed to a next-query machine: the
nested pair `⟨⟨x₁, y₁⟩, ⟨⟨x₂, y₂⟩, ⟨…, []⟩⟩⟩`. -/
def encodeHist {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool :=
  h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) acc) []

/-- The empty history is encoded as the empty string: `encodeHist [] = []`. -/
theorem encodeHist_nil {ℓ₁ ℓ₂ : ℕ} :
    encodeHist ([] : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) = [] :=
  rfl

/-- A history is encoded pair by pair:
`encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h)`. -/
theorem encodeHist_cons {ℓ₁ ℓ₂ : ℕ} (p : (Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))
    (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) :
    encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) :=
  rfl

/-- The query tree of a next-query function `next` (the machine's move on a history) with the
query budget `q`, started from the history `hist`: a verdict stops; a query within budget
becomes a `query` node whose continuation appends the answer to the history; a query when the
budget is exhausted is the forced verdict `false` (D7). -/
def buildTree {ℓ₁ ℓ₂ : ℕ} (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ℕ → List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
  | 0, hist => match next hist with
    | .ret b => .ret b
    | .query _ => .ret false
  | q + 1, hist => match next hist with
    | .ret b => .ret b
    | .query x => .query x (fun o => buildTree next q (hist ++ [(x, o)]))

section BuildTree

variable {ℓ₁ ℓ₂ : ℕ} {next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁}
  {hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))}

/-- With the budget spent, a verdict stops the tree: `buildTree next 0 hist = ret b` when
`next hist = ret b`. -/
theorem buildTree_zero_of_ret {b : Bool} (h : next hist = .ret b) :
    buildTree next 0 hist = .ret b := by
  rw [buildTree, h]

/-- With the budget spent, a query gives the forced verdict `false`:
`buildTree next 0 hist = ret false` when `next hist = query x`. -/
theorem buildTree_zero_of_query {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
    buildTree next 0 hist = .ret false := by
  rw [buildTree, h]

/-- Within budget, a verdict stops the tree: `buildTree next (q + 1) hist = ret b` when
`next hist = ret b`. -/
theorem buildTree_succ_of_ret {q : ℕ} {b : Bool} (h : next hist = .ret b) :
    buildTree next (q + 1) hist = .ret b := by
  rw [buildTree, h]

/-- Within budget, a query becomes a query node whose continuation appends the answer:
`buildTree next (q + 1) hist = query x (fun o => buildTree next q (hist ++ [(x, o)]))` when
`next hist = query x`. -/
theorem buildTree_succ_of_query {q : ℕ} {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
    buildTree next (q + 1) hist = .query x (fun o => buildTree next q (hist ++ [(x, o)])) := by
  rw [buildTree, h]

end BuildTree

/-- The tree built with budget `q` makes at most `q` queries, from every starting history. -/
theorem buildTree_boundedBy {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ∀ (q : ℕ) (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))),
      (buildTree next q hist).BoundedBy q
  | 0, hist => by
    cases h : next hist with
    | ret b => rw [buildTree_zero_of_ret h]; exact QueryTree.boundedBy_ret b 0
    | query x => rw [buildTree_zero_of_query h]; exact QueryTree.boundedBy_ret false 0
  | q + 1, hist => by
    cases h : next hist with
    | ret b => rw [buildTree_succ_of_ret h]; exact QueryTree.boundedBy_ret b (q + 1)
    | query x =>
      rw [buildTree_succ_of_query h]
      exact (QueryTree.boundedBy_query_succ x _ q).2
        fun o => buildTree_boundedBy next q (hist ++ [(x, o)])

/-- The query tree of the next-query machine `D` at parameter `n` with budget `q`
([PS10, Definition 96.1]; D7: no oracle tapes, one activation per query on the history). The
machine `D(1^n, ·)` is run, with one random tape `r` for the whole interaction, on the
encoded history; its output is decoded as a query or a verdict. -/
def _root_.Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
  fun r => buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []

/-- The tree of `D` on the coins `r` is built from the empty history, the next move being `D`'s
output on the encoded history, decoded:
`D.toOracleAdversary n ℓ₁ ℓ₂ q r =
buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []`. -/
theorem _root_.Complexity.NUPPT.toOracleAdversary_eq (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ)
    (r : D.Coins n) :
    D.toOracleAdversary n ℓ₁ ℓ₂ q r =
      buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q [] :=
  rfl

/-- The oracle adversary of a next-query machine with budget `q` makes at most `q` queries on
every coin string (the hypothesis `BoundedBy` of `ggm_prfAdv_le` and `exists_ggmBits_dist`).
Induction on the budget (`buildTree_boundedBy`). -/
theorem _root_.Complexity.NUPPT.toOracleAdversary_boundedBy (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q :=
  (OracleAdversary.boundedBy_iff _ q).2 fun r => by
    rw [NUPPT.toOracleAdversary_eq]
    exact buildTree_boundedBy _ q []

/-! ### Oracle indistinguishability [PS10, Definition 96.1] -/

/-- **Oracle indistinguishability** [PS10, Definition 96.1]: `{O_n} ≈ {O'_n}` iff for every
non-uniform PPT oracle machine `D` (a next-query `NUPPT`) and every polynomial query budget
`q`, the function `n ↦ |Pr[F ← O_n : D^F(1^n) = 1] − Pr[F ← O'_n : D^F(1^n) = 1]|` is
negligible, where `D^F(1^n)` is the run of the query tree `D.toOracleAdversary n ℓ₁(n) ℓ₂(n) q(n)`
against `F`. (The text writes `{O'_n} ≈ {O'_n}`, a typo.)

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries. -/
def OracleEnsemble.Indist {ℓ₁ ℓ₂ : PolyExpr} (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n =>
    distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))

/-- Oracle ensembles are indistinguishable iff the oracle advantage is negligible for
each next-query machine and polynomial query budget. -/
theorem OracleEnsemble.indist_iff {ℓ₁ ℓ₂ : PolyExpr} (O O' : OracleEnsemble ℓ₁ ℓ₂) :
    O.Indist O' ↔ ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n =>
      distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) :=
  Iff.rfl

/-- **Reflexivity of oracle indistinguishability** (non-vacuity of
[PS10, Definition 96.1]): every oracle ensemble is indistinguishable from itself, the
advantage being identically `0`. -/
theorem OracleEnsemble.Indist.refl {ℓ₁ ℓ₂ : PolyExpr} (O : OracleEnsemble ℓ₁ ℓ₂) : O.Indist O := by
  intro D q
  have h : (fun n => distAdv (O.O n) (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))) = fun _ => 0 := by
    funext n
    simp [distAdv_def]
  rw [h]
  exact negligible_zero

/-- **Symmetry of oracle indistinguishability**: the advantage is symmetric in the two
ensembles (`abs_sub_comm`). -/
theorem OracleEnsemble.Indist.symm {ℓ₁ ℓ₂ : PolyExpr} {O O' : OracleEnsemble ℓ₁ ℓ₂}
    (h : O.Indist O') : O'.Indist O := by
  intro D q
  have e : (fun n => distAdv (O'.O n) (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))) =
      fun n => distAdv (O.O n) (O'.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) := by
    funext n
    rw [distAdv_def, distAdv_def]
    exact abs_sub_comm _ _
  rw [e]
  exact h D q

/-- **Transitivity of oracle indistinguishability** (the two-step case of the hybrid lemma
for oracles, [PS10, §3.8.2, "oracle indistinguishability satisfies … the Hybrid Lemma"]): the
advantage between `O` and `O''` is at most the sum of the advantages between `O, O'` and
`O', O''` (triangle inequality `abs_sub_le`), and sums of negligible functions are negligible
(`Negligible.add`, `Negligible.mono`). -/
theorem OracleEnsemble.Indist.trans {ℓ₁ ℓ₂ : PolyExpr} {O O' O'' : OracleEnsemble ℓ₁ ℓ₂}
    (h₁ : O.Indist O') (h₂ : O'.Indist O'') : O.Indist O'' := by
  intro D q
  refine ((h₁ D q).add (h₂ D q)).mono ⟨0, fun n _ => ?_⟩
  simp only [distAdv_def, abs_abs]
  exact (abs_sub_le _ _ _).trans (le_abs_self _)

/-- **The hybrid lemma for oracles** [PS10, §3.8.2, "oracle indistinguishability satisfies …
the Hybrid Lemma"] (Claim-96.b), at one parameter: if the oracle adversary `A` distinguishes
the oracle distributions `H 0` and `H m` with advantage `ε`, then it distinguishes some
consecutive pair `H i, H (i+1)` (`i < m`) with advantage at least `ε / m`. Apply the
finite hybrid bound `exists_hybrid_gap` to the acceptance probabilities for `oracleDist A`. -/
theorem oracle_hybrid_lemma {σ : Type*} {I O : Type} {ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
    (H : ℕ → σ → (I → O)) (A : OracleAdversary ρ I O) :
    ∃ i < m, distAdv (H 0) (H m) (oracleDist A) / m ≤ distAdv (H i) (H (i + 1)) (oracleDist A) := by
  simpa only [distAdv_def] using exists_hybrid_gap (fun i => acceptProb (H i) (oracleDist A)) hm

/-! ### Pseudorandom functions [PS10, Definition 96.2] -/

/-- **Pseudorandom function family** [PS10, Definition 96.2]: a family
`{f_s : {0,1}^{|s|} → {0,1}^{|s|}}` given as `F n : {0,1}^n → {0,1}^n → {0,1}^n` (key, input,
output) is pseudorandom iff (1) *easy to compute*: a polynomial-time string function computes
`f_s(x)` from the pair `⟨s, x⟩`; (2) *pseudorandom*: the keyed oracle ensemble `{s ← U_n : f_s}`
is oracle-indistinguishable from the random functions `{F ← RF_n : F}`.

**Deviation:** clause (1) is a deterministic polynomial-time evaluator on `⟨s, x⟩` instead of
a PPT computing `f_s(x)` with probability one (equivalent by `Complexity.NUPPT.Computes` and
`ofPolyTimeUniform`, as for `FunFamily.Easy`); the key length is the parameter `n`
(`{0,1}^{|s|}` with `|s| = n`). -/
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where
  /-- Clause (1): `f_s(x)` is polynomial-time computable from `⟨s, x⟩`. -/
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  /-- Clause (2): `{s ← U_n : f_s} ≈ {F ← RF_n : F}` as oracle ensembles. -/
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)

/-- The advantage of the next-query machine `D` with budget `q` between the keyed family `F`
and the random functions is the concrete PRF advantage `prfAdv` of [Gar26, Definition 3.9]
(definitional: `prfAdv F A = distAdv F (randomFunction I O) (oracleDist A)`). -/
theorem prfAdv_toOracleAdversary (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).O n) ((OracleEnsemble.random .var .var).O n)
        (oracleDist (D.toOracleAdversary n n n q)) =
      prfAdv (F n) (D.toOracleAdversary n n n q) := by
  rw [prfAdv_def]
  rfl

/-- **Pseudorandomness unfolded**: for a PRF `F`, every next-query machine `D` with every
polynomial budget `q` has negligible concrete PRF advantage `prfAdv (F n) (D^{(q n)})` — the
form in which the Garg-layer reductions consume [PS10, Definition 96.2]. -/
theorem PRF.negligible_prfAdv {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n n (q.eval n)) := by
  exact (congrArg Negligible (funext fun n => prfAdv_toOracleAdversary F D n (q.eval n))).mp
    (hF.pseudorandom D q)

end TCSlib.Cryptography
