## ===== briefs/pass-shelat-ch5-8/gates/15-cpa-pilot-proofs/pack.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/15-cpa-pilot-proofs/review-290.md =====

# adaptive-cpa · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS** (0 blockers, 0 majors, 4 minors, 5 notes).

Delivery: Claude worker, exchange `35b16407` (`inbox/fills/adaptive-cpa/`), 5 patches on
`4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27`. Independent review on the landing branch (parent =
campaign after #289); evidence `review-evidence.zip` (SHA-256 `0a4c83d499d7c5b355327af61eeb60e3df8154142e9afceec63b44b4c742e976`; `PROVENANCE.txt`, inner
`SHA256SUMS` 357 files).

## Checks (re-run by the reviewer)
- Integrity: payload sums 487/487; `git am` reproduces `src/` byte for byte (1 modified, 4 added).
- Build: 201-module closure (issued 197 + 4 helpers, 92 roots) 201/201, 0 errors, fresh tree.
- Admissions: issued base 27, landing parent 26 (#289), head 25: only `INDSecure.adaptive_cpa` removed.
- Statements: 69 ADDED, 0 CHANGED, 0 REMOVED.
- Axioms: `adaptive_cpa` and all 175 stored constants of the five modules standard;
  `bitwise_padded_adaptive_cpa`/`exists_adaptive_cpa` carry `sorryAx` via the bitwise target.
- Rule 10: whole-file closure seals of all five files (685 / 2,125 / 2,167 / 2,172 / 2,174 requests)
  PASS; base control PASS; 10 control probes, 55 negatives ALL_OK; explicit-reader scan 627 items,
  0 foreign. Lint 0 FAIL (same 6 WARN as base).

## Findings and dispositions
| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | minor | Stale "stated; a `sorry`" in `AdaptiveCPA.lean`; facade lacks `## Contents`. | **Landing edit.** |
| 2 | minor | Private `Handler.pairEncode_append` copies `GGMRed.pairEncode_append_right` (report said no duplication). | **Landing edit:** removed and re-pointed. |
| 3 | minor | Nine lemma docstrings without their formula (Hybrid, Games). | **Landing edit.** |
| 4 | minor | Unused simp argument (`Handler.lean:266`). | **Landing edit.** |
| 5 | note | Public `AdaptiveCPA.ofFn_cast` = private `cca2OfFn_cast` (#289, landed after the issue base). | New ledger row DL-32. |
| 6 | note | Generic material to promote: `expect_sample_update` (Probability), `simulate_eq_of_abs` and the `castImpl` family (Simulate), `padFin_ofFn_zeroBits`, `headD_ofFn_one`, `ofFn_splitHalf_fst/_snd`; reader request `indCodec_eq_bitCodec`; new uses of `GGMRed.ofFn_padFin_of_length`. | Added to DL-30 / DL-31 follow-up. |
| 7 | note | `Handler.lean` 601 lines (596 after edits). | No action. |
| 8 | note | Proof and API review: no defects (hybrid endpoints, handler equations and poly proof, state abstraction, eager/lazy tapes, bound incl. cap 0, edge cases). | — |
| 9 | note | Downstream: `BitwiseCPA`, facades, root; `Checks` does not import it. | Root/Checks run by the maintainer. |

## Landing
Branch `land/pass-shelat-adaptive-cpa` at `95df0b4fa15e140ffd8f692699c66d0683fc916d` (5 delivered commits +
landing edits). After the edits: 8 affected modules rebuilt (0 errors); 22 modules through
`TCSlib` and `audits/pass-shelat/Checks` rc 0 on the full tree (`landing/`). PR #290 (draft).

## ===== briefs/pass-shelat-ch5-8/gates/15-cpa-pilot-proofs/review-291.md =====

# bitwise-cpa · maintainer delivery review (r1)

**Verdict: ACCEPT WITH LANDING EDITS** (0 blockers, 0 majors, 2 medium, 3 low, 3 info).

Delivery: Claude worker, exchange `4aa36699` (`inbox/fills/bitwise-cpa/`), 3 patches on
`4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27`. Reviewed on a landing branch stacked on #290
(`land/pass-shelat-adaptive-cpa` at `95df0b4f`); evidence `review-evidence.zip` (SHA-256 `d3fd1750ace71d0111c0415fc823b728ae574df50f8fbb4a0f1a238e59b69ca4`;
`PROVENANCE.txt`, inner `SHA256SUMS` 380 files).

## Checks (re-run by the reviewer)
- Integrity: payload sums 63/63; `git am` reproduces `src/` byte for byte.
- Build: 204-module closure, fresh tree, 204/204 rc 0, 0 errors.
- Admissions: issued base 27 → landing parent 25 → head 24 (removed `prfFixedScheme_not_cca2` by #289,
  `adaptive_cpa` by #290, `bitwise_padded_cpa` here; none added).
- Statements: 43 ADDED, 0 CHANGED, 0 REMOVED (plus `simps` readers of `qHandler`; 13 private).
- Axioms: `bitwise_padded_cpa`, `bitwise_padded_adaptive_cpa`, **`exists_adaptive_cpa`**,
  `adaptive_cpa` and all 97 stored constants of the four modules standard.
- Rule 10: whole-file closure seals of the four files (2,021 / 2,125 / 2,125 / 2,185) rc 0; base
  control rc 0; 8 control probes, 60 negatives ALL_OK; explicit-reader scan 412 items, 0 foreign.
- Lint 0 FAIL (same 6 WARN as base).

## Findings and dispositions
| # | Severity | Finding | Disposition |
|---|---|---|---|
| 1 | medium | `BitwiseSim.ofFn_cast`, `BitwiseSim.indCodec_eq_bitCodec` duplicate the parallel adaptive-cpa fill's lemmas. | **Landing edit:** removed; uses re-pointed to `AdaptiveCPA.*`. |
| 2 | medium | `Planted.lean` 152 s, almost all in three `convert … using 1` blocks. | **Landing edit:** `PolyTimeComputable.congr`; 2.4 s. |
| 3 | low | Docstrings without formulas (QueryHandler, Planted, Eager). | **Landing edit.** |
| 4 | low | Facade lacks `## Contents`. | **Landing edit.** |
| 5 | low | Three lines over 100 characters. | **Landing edit.** |
| 6 | info | Promotion and duplication candidates: two forms of `expect_sample_update`; generic eager-coins lemma vs the private one in `OracleSecurity`; `chRun_toCompOn_transport_list` generalizes `ChallengeSim`'s; list lemmas `headD_drop`, `flatten_ofFn_singleton` (copies elsewhere); `decodeFin_nil_getD`; `padded_enc_runAt/_coins`; a third copy of the two-oracle length-vector pattern; new DL-31 uses; small private re-proofs; reader request `HybridMachine.hybridPre_eq`. | Ledger row DL-33. |
| 7 | info | Proof and API review: no defects (hybrid endpoints, `n = 0`, handler, advice length, planted layout, signed identity, bound, edge cases). | — |
| 8 | info | No separate checkpoints 2–3 (checkpoint 1 already had the full proof); the worker's own seal was root-scoped, the review's closure seals are stronger. | Recorded. |

## Landing
Branch `land/pass-shelat-bitwise-cpa` at `c286bc6a9b372036f959a033729d841ce10dfa16` (on #290's branch; 3 delivered
commits + landing edits). After the edits: 6 affected modules rebuilt (0 errors, 0 warnings); downstream
through `TCSlib` rc 0 on the full tree (`Checks` does not import these modules). PR #291 (draft, base
#290's branch).

## ===== briefs/pass-shelat-ch5-8/gates/15-cpa-pilot-proofs/worker-report-290.md =====

# Fill `adaptive-cpa` — final

**Worker:** Claude (external). **Issue base:** `4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27` on
`cryptography/pass-shelat-ch2-4`. **Local proof branch:** `fill/adaptive-cpa`, head
`52f3e3a1c`, never pushed; the whole series from the base is in `patches/`. **Pack:** read at exchange
`f4737d78e`; `SHA256SUMS` 7/7 OK; `SOURCE-SHA256SUMS` as issued. **Checkpoints on the exchange:**
`b1270dd47` (checkpoint 1: hybrids), `a797df9bd` (checkpoint 2: steps 2–3, target compiling;
there is no separate checkpoint 3 because steps 2 and 3 finished together).

## Target status

`Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa` is **proved**. `#print axioms`
(`evidence/logs/axioms-final.log`):

- `INDSecure.adaptive_cpa`: `[propext, Classical.choice, Quot.sound]`;
- `SingleBitSecure.bitwise_padded_adaptive_cpa`: `[propext, sorryAx, Classical.choice, Quot.sound]`;
- `SingleBitSecure.exists_adaptive_cpa`: `[propext, sorryAx, Classical.choice, Quot.sound]`.

The last two still depend on the `bitwise-cpa` target (`bitwise_padded_cpa`), as the brief expects.

## Changed files

| File | Change |
|---|---|
| `PublicKey/AdaptiveCPA.lean` (owned) | 7 imports added (the four helpers, `Games.Advantage`, `Games.Efficiency`, `Asymptotic.ReductionSupport`); the target's proof sketch rewritten to describe the delivered proof; the proof body. Statement, statement prose and the module docstring unchanged. |
| `PublicKey/AdaptiveCPA/Hybrid.lean` (new, 407 lines) | generic hybrid oracles, transport, sampling |
| `PublicKey/AdaptiveCPA/Handler.lean` (new, 601 lines) | the reduction's `InteractiveHandler` and its call equations |
| `PublicKey/AdaptiveCPA/Games.lean` (new, 296 lines) | the hybrid games `H_i`; `H_0`, `H_cap` are the adaptive games |
| `PublicKey/AdaptiveCPA/Reduction.lean` (new, 274 lines) | `B`'s game is `H_{i⋆+b}` |

No other file is touched. The parent file imports every child (the style lint's facade check
requires it). The new modules sit before `PublicKey/AdaptiveCPA` in `evidence/order.txt` (201
modules). They import no Mathlib module directly, so the roots are unchanged (92).

## The proof (brief steps 1–4)

1. **Hybrids** (`Hybrid`, `Games`). `hybImpl κ E sel` answers the `j`-th fresh challenge
   (`j < κ`) with `E (sel j) mm r` for fresh coins `r`. It records the ciphertext in a history,
   repeats `h.headD 0` at the cap, and answers `Dec` with `0`. `H_i := acHyb S A q κ n
   (· < i)` runs `A` on T2's codec (`bitCodec` of `acDin`/`acDout`). Read along T2's lengths
   (`castImpl`), `S.adaptiveIndImpl .cpa b` is `hybImpl` with the constant selector
   (`castImpl_adaptiveIndImpl`). It uses only `adaptiveIndImpl_dec_issued/_dec_other`,
   `indImpl_dec_onSpec` with `decOpen_cpa`, `_challenge_encrypt`, `_challenge_full` with
   `indImpl_challenge_repeat_onSpec`, and `_challenge_zero`. Then `adaptiveIndGame_eq_acHyb`
   (codec transport `simulate_castImpl_toCompOn`, `indCodec_eq_bitCodec`), and `acHyb_lt_zero`
   and `acHyb_lt_cap` (`H_0` = `b = false`, `H_cap` = `b = true`).
2. **The reduction** (`Handler`). `acHandler S cap ist : InteractiveHandler 2 acDin acDout 2
   acDin acDout`:
   - `perCall = 1`, `finCall = 0`, `outLen = 1`;
   - the state is `⟨1^j, ⟨1^{i⋆(n)}, c⟩⟩`, padded to `4·cap + 4 + ctLen` bits, with `i⋆(n)` in
     `init`;
   - the seed is `cap · ρ` bits, read as `cap` encryption tapes (`acTapes`,
     `FunFamily.blocks`);
   - the adversary runs on the reduction input `pk`.

   The round function is polynomial-time. It uses `Enc`'s output function (`enc_uniform`,
   `NUPPT.Uniform.runAt_eq`), unary multiplication for the tape offset, prefix splitting, `padL`
   and the `lenLe`/`lenEq`/`isNil` tests. Its call equations:
   - `acHandler_impl_dec`: `⊥`;
   - `_impl_full`: repeats the latest ciphertext;
   - `_impl_eager`: its own `Enc` of `m_{[j < i⋆]}` with tape `j`;
   - `_impl_forward`: one outer `Challenge` query with the same `x`, its answer recorded.

   `acHandler_advInput` gives the adversary's input `pk`, and `acHandler_finish` gives `A`'s bit
   with no outer query. T2 (`exists_interactiveHandlerMachine` with `dα = 1`) makes `B`.
   **Codec alignment** is done once and generically: `castImpl`, `simulate_castImpl_toCompOn`
   and `expect_simulate_castImpl_toCompOn`, by `subst` on the length functions, as in
   `chRun_toCompOn_transport`.
3. **`B`'s game is `H_{i⋆+b}`** (`Reduction.accept_indGame_acHyb`). Compose the handler with the
   outer oracles (`simulate_bind`, `simulate_comp`). The composite's state is a function of the
   hybrid history `h` (`acAbs`): the handler state counts `min |h| κ` with latest `h.headD 0`, and
   the outer challenge state is `h.reverse[i⋆]?`. One call of the composite is then one call of
   `tapeImpl` (the hybrid with the handler's tapes as coins in advance and a lazy slot at `i⋆`)
   (`comp_acAbs`), and `simulate_eq_of_abs` lifts this to whole runs. `B`'s coins are `(ω, r)`
   through T2's `φ`. Uniform tapes give the lazy hybrid (`expect_tapeImpl`, proved by resampling
   one coordinate, `expect_sample_update`, with `simulate_tapeImpl_congr`). At `i⋆` the outer
   oracle encrypts `m_b`, which is the selector `[i⋆ < i⋆ + b] = b`.
4. **The bound** (owned file).
   - At each `n`, `exists_advantage_hybrid_gap` gives `i⋆(n) < cap(n)` with
     `adv(H_0, H_cap) ≤ cap(n) · adv(H_{i⋆}, H_{i⋆+1})`. At `cap(n) = 0`, `i⋆(n) = 0` and the
     left side is `advantage_self = 0`.
   - `choose` gives `i⋆` as a function of `n`, which is the handler's advice.
   - `h` is applied to `B` at the polynomial outer budget `(q·perCall) + finCall`, giving `ε`.
   - `A`'s advantage is at most `cap(n) · ε(n)`, negligible by `Negligible.polyExpr_mul`. No
     assumption `n > 0` is made.

**Edge cases the brief names:**
- **Query budget 0, and the timeout output:** every lemma is stated for an arbitrary budget, by
  induction on the computation. The timeout output `zeroBits 1` is part of `toCompOn` and is
  transported with it. `B`'s output is `A`'s output, whatever it is (`acHandler_finish`).
- **Cap 0:** `castImpl_adaptiveIndImpl` handles the empty history with `_challenge_zero`. The
  handler's full branch answers its latest field, which is `0` initially. The gap step gives
  advantage `0`.
- **Repeated fresh ciphertext values:** the history is a list and the handler counts challenges,
  not distinct values. The outer state is read by position (`h.reverse[i⋆]?`), and `Dec` under
  CPA refuses whatever the history.
- **A run that never reaches the `i⋆`-th fresh challenge:** the lazy slot is never used. The
  outer oracle is then never queried and its state stays `none = h.reverse[i⋆]?`. Both sides are
  handled by the same inductions, branch by branch.

## New declarations

- **Hybrid:**
  - `castImpl`, `castImpl_eq`, `castImpl_self`;
  - `simulate_castImpl_toCompOn`, `expect_simulate_castImpl_toCompOn`, `simulate_eq_of_abs`;
  - `hybImpl` with `_zero`, `_fresh`, `_full`, `_congr`;
  - `tapeImpl` with `_zero`, `_lazy`, `_eager`, `_full`, and `simulate_tapeImpl_congr`;
  - `extTape` with `_of_lt`, `_update`;
  - `expect_sample_update`, `expect_tapeImpl`.
- **Handler:**
  - `msgOf`/`_eq`, `acDin` with `_zero`/`_one`, `acDout` with `_zero`/`_one`, `acStLen`/`_eq`,
    `acState`/`_eq`;
  - `acTapes` with `_apply`, `ofFn_acTapes`;
  - `acHandler` (with `simps` field readers), `acHState`/`_eq`, `acHandler_init_eq`,
    `acSeedTapes`/`_eq`;
  - `acHandler_advInput`, `acHandler_finish`, and `acHandler_impl_dec`, `_full`, `_eager`,
    `_forward`;
  - private string functions `rU`…`rEnc`, `acRun` and `acFin` with their polynomial-time proofs,
    plus private helpers.
- **Games:**
  - `indCodec_eq_bitCodec`, `acDin_eval`, `acDout_eval`;
  - `ofFn_cast`, `ofFn_splitHalf_fst`/`_snd`, `padFin_ofFn_zeroBits`, `headD_ofFn_one`,
    `ofFn_select`;
  - `acEnc`/`_eq`, `acHyb`/`_eq`, `acHyb_congr`;
  - `castImpl_adaptiveIndImpl`, `adaptiveIndGame_eq_acHyb`, `acHyb_lt_zero`, `acHyb_lt_cap`.
- **Reduction:**
  - `castImpl_indImpl_challenge`, `accept_indGame_acHyb`;
  - private: `getElem?_reverse_cons`, `acAbs`, `sel_ist`, `sel_ne`, `comp_acAbs`, `init_acAbs`,
    `prob_red_tape`.

Every public declaration has a docstring with its formula, and the nontrivial ones have a proof
sketch. No new `@[simp]` attribute.

## Promotion requests, reader requests and duplication

- **Promotion (generic):**
  - `expect_sample_update` → `Games/Probability.lean` (DL-30);
  - `simulate_eq_of_abs`, `castImpl`, `simulate_castImpl_toCompOn` and
    `expect_simulate_castImpl_toCompOn` → `Games/Simulate.lean` or `BitCodec.lean`;
  - `ofFn_cast`, `ofFn_splitHalf_fst/_snd`, `padFin_ofFn_zeroBits` and `headD_ofFn_one` →
    `BitCodec.lean` or `PrivateKey/OracleSecurity.lean`.
- **Reader request:** `indCodec_eq_bitCodec` (`S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1`)
  is proved here from the three published field readers. It would sit naturally beside
  `indCodec_decodeMove` in `PublicKey/OracleSecurity.lean`. No reader was missing.
- **Duplication:** none retained. Two string lemmas I first wrote were found to exist already.
  I now use `Collection.ofFn_padFin_of_le` (`Asymptotic/CollectionsHelpers`) and
  `ofFn_padFin_eq_take` (`Asymptotic/CollectionsLemmas`). One private one-line bridge to `padL`
  remains (`ofFn_padFin_eq_padL`, by `padL_eq` and `ofFn_padFin_eq_take`).

## Checks

- **Preflight** (`logs/preflight.log`, before any cache or Lean work):
  - `nproc` 4;
  - cgroup v1 with no effective limit (`memory.limit_in_bytes` 9223372036854771712), so the
    headroom is `MemAvailable` = 16,331,972,608 B (floor 4 GiB: PASS). Memory in use
    (`usage − total_cache + total_shmem`) was 218,099,712 B;
  - the clone, payload, toolchain and `/tmp` are on ext4 `/dev/vda`, with 19,485,560,832 B free
    (floor 12 GiB: PASS). No tmpfs was used.
- **Toolchain:** the official Lean 4.25.0 toolchain already installed by this session on this
  host (SHA-256 `97bee7bd…6abb8a`, recorded in the not-cca2 delivery). All Python ran as
  `python3 -I`.
- **Cache:**
  - The archive store `~/.cache/mathlib` already held 2,383 files (118,965,639 B), left by this
    host's earlier not-cca2 fill session (`logs/cache-store.log`).
  - The narrowed `lake exe cache get` over the 92 roots (identical to `roots.txt`) reported "No
    files to download", decompressed 2,345 files and exited 0.
  - Package pins: PASS. `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean` are ABSENT, and
    the order imports none of them.
  - No zero-size `.olean` (2,390 present); the root probe passed.
  - The clone is the same one used for not-cca2, with the same manifest pins. A fresh olean tree
    `.lake/acpa-oleans` was used for this unit.
- **Bootstrap:** the issued `order.txt` (197 modules), one module per
  `scripts/lean_check_tree.sh`: ALL PASS, 27 `sorry` warnings, peak RSS 3,093,332 KiB
  (`logs/bootstrap.tsv`).
- **Sweep:** the order with the four helpers inserted before `PublicKey/AdaptiveCPA`
  (`evidence/order.txt`, 201 modules), from a full re-check after the last edit: ALL PASS. It
  took 865.8 s of Lean time, peak RSS 3,011,224 KiB (`logs/sweep.tsv`, `logs/sweep/`).
- **Admissions:** 26 against 27 in `base-sorries.txt`. Removed: exactly
  `PublicKey/AdaptiveCPA: INDSecure.adaptive_cpa`. Added: none (`logs/sweep-admissions.log`).
- **Axioms:** as listed above (`logs/axioms-final.log`, probe `probes/Axioms.lean`).
- **Rule 10, seals:**
  - **Census** (`logs/refs-final.log`, `probes/Refs.lean`): the 175 touched declarations are
    every declaration of the four helpers and the target, including generated matchers, equation
    and `simps` lemmas and proof auxiliaries. Their foreign TCSlib references are listed in
    `seal-candidates.json`. Reducible abbreviations and primitive projections are skipped, and
    `PolyExpr.eval` is exempt as notation.
  - **Instance-aware seal of each file**, the whole body copied into a probe with every remaining
    candidate `local irreducible` (`logs/seal-summary.log`):

    | File | Definitions sealed | Result |
    |---|---|---|
    | Hybrid | 8 | pass |
    | Handler | 26 | pass |
    | Games | 28 | pass |
    | Reduction | 37 | pass |
    | owned | 18 | pass |

    The owned file's seal covers the four helpers' definitions as foreign. No sealed candidate
    is an instance.
  - **Controls:** each passes before the seal and fails after it at `rfl`:

    | File | Control |
    |---|---|
    | Hybrid | `padFin ℓ w i = w.getD i false` |
    | Handler | `InteractiveHandler.input … = ⟨⟨1^n, ⟨z, ω⟩⟩, …⟩` |
    | Games | `S.inLens n 0 = S.ctLen.eval n` |
    | Reduction | `acDout S 1 = S.ctLen` |
    | owned | `(acHandler S cap ist).perCall = .const 1` |
  - **Explicit-unfold scan:** PASS (`logs/explicit-unfold-scan.log`).
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey
  --check8b` gives **0 FAIL, 6 WARN** over 23 files. The six warnings are identical to the base's
  (`logs/style-lint-base.log`), all on files outside this fill. No line exceeds 100 characters,
  `git diff --check` is clean, and every file is below 1000 lines.
- **Patch replay:** `git am` of `patches/0001-0005` on the base reproduces all five files of
  `src/` byte for byte (`logs/patch-replay-final.log`).
- **Process discipline:**
  - One Lean process at a time, every check through `scripts/lean_check_tree.sh` wrapped by
    `tools/time_check.py` (UTC start and end, elapsed time, max RSS).
  - No `lake build` and no unfiltered cache get.
  - The proof branch stayed local.

## For the maintainer

1. **Stale module docstring sentence.** The owned file's module docstring still says
   "`INDSecure.adaptive_cpa` (stated; a `sorry` under its sketch)". The brief allows editing only
   the target's proof sketch, so this sentence still needs changing to "proved".
2. The parent file now imports its four children, as the style lint's facade check requires. Its
   module docstring has no `## Contents` list for them, because that docstring was outside the
   edits the brief allows.
3. The seal first failed in three places, which are now fixed and recorded in the patch series
   (`0005`):
   - an `rfl` that unfolded `simulate`;
   - a width cast read in the direction that needed `outLens` to unfold;
   - `acHandler_finish`, whose `pure` sat at the adversary's output type.

   The earlier checkpoints carry the unfixed versions.

## Payload

- `REPORT.md` and `patches/` (the whole `format-patch` series from the base);
- `src/`, the five files at their repository paths;
- `evidence/`:
  - `inputs/`: the pack, the exchange README and `policy.md`;
  - `logs/`: preflight, cache store, cache get, pins, validation, probe, bootstrap, sweep,
    admissions, axioms, census, seal candidates, seals, controls, unfold scan, lint and patch
    replay;
  - `probes/`, `tools/`;
  - `seal-candidates.json`, `order.txt`, `bootstrap-order.txt`;
- `SHA256SUMS` over the payload.

## ===== briefs/pass-shelat-ch5-8/gates/15-cpa-pilot-proofs/worker-report-291.md =====

# Fill report · `bitwise-cpa` · final

**Worker** Claude (external fill, exchange push route). **Issue base**
`4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27` on `cryptography/pass-shelat-ch2-4`. **Proof branch**
local `fill/bitwise-cpa` at `4cc388aba` (3 commits over the base; never pushed). **Pack** read at
exchange `f4737d78e`; `sha256sum -c SHA256SUMS` in `outbox/fills/bitwise-cpa/`: all 7 OK
(`evidence/logs/pack-sha256.log`). Source hashes: `sha256sum -c SOURCE-SHA256SUMS` at the base,
197/197 OK (`evidence/logs/source-sha256.log`). Checkpoint 1: exchange `43a16abd1`.

## 1. Result

**`BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa` is proved.** No admission remains in the
touched files. The frozen statement is byte-identical to the base (only the body and the sketch
changed). Axioms of the target: `[propext, Classical.choice, Quot.sound]`. No escalation: the
target is true and every reading goes through published readers (one reading found by the seal
was rerouted, §5).

The proof follows the brief's route; step 3 is an exact identity: with `j = j⋆(n) < n`,
`advantage(H_j, H_{j+1}) = distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n)`
(`hyb_advantage_eq`), and then `advantage(Ind_0, Ind_1) = advantage(H_0, H_n) ≤ n · distAdv`.

| Brief step | Delivered as |
|---|---|
| 1 bit hybrids | `hybGame S L hL hmsg A q n j` (private): sample `rg`, `A`'s coins `r`, and `n` single-bit encryption tapes `v : Fin n → S.enc.Coins n`; run `A` with `ChallengeSim.chRun` whose challenge `mm` is answered by `padCt L(n)` of `hybCt` (block `i` = `Enc(pk, [l_{n+i}]; v_i)` if `i < j`, `Enc(pk, [l_i]; v_i)` otherwise, `l = ofFn mm = m₀ ‖ m₁`). `accept_indGame_eq`: `Pr[Ind_b = 1] = Pr[H_{b ? n : 0} = 1]`, by eager coins (`BitwiseSim.expect_simulate_indImpl_cpa`), `padded_enc_runAt`, the coin bijection `bitwiseEncCoins` then `coinsCongr`, the layout `bitwise_enc_runAtL` (via `bitwise_enc`), `bitwiseEncCoins_ofFn` and `coinBlock_ofFn_coinBlocks`. At `n = 0` the two ends are the same hybrid and the advantage is `0`. |
| 2 distinguisher `D` (T1) | `BitwiseSim.exists_qHandlerMachine` (T1 for the new generic `qHandler`): lengths `din = [L, n+n]`, `dout = [n+1, L]`, `dα = 1`; seed `n·B(n)` bits (`mul var S.enc.coins`); state `⟨aux, asked :: x⟩` with advice `aux = bwAux S js n = ⟨1^{j⋆}, ⟨1^{(j⋆+1)·B}, 0…⟩⟩` padded to `bwLaux S` bits; `Dec` answered `⊥`; the first challenge recorded and every challenge answered `BitwiseSim.plantAns` of the recorded one (`T₁ ‖ ⟨c, T₂⟩` from the published `blockEncFun`, then `padCt`); output `BitwiseSim.plantOut`: `[a]` for `(0,1)`, `[¬a]` for `(1,0)`, `[0]` for equal bits or no challenge. `j⋆` is chosen per `n` from `exists_advantage_hybrid_gap` (`choose`). |
| 3 exact identity | `hyb_advantage_eq`: both hybrids depend only on the first challenge (`chRun_congr`); `D`'s output (`hrun`) is the post-processed bit of `A`'s run against the planted tuple `W β v re l` (`plantTuple_spec`, `plantOut_recorded`, `plantOut_init`, transport by `indCodec_eq_bitCodec`); resampling coin block `j` (`expect_sample_update`) turns `H_j` into `W (l_j)` and `H_{j+1}` into `W (l_{n+j})` (`planted_eq`, `hybCt_update`); the seed is reindexed by `coinBlocks` and `finCongr (bitwise_enc_coinLen n)`; the signed case split is `ChallengeSim.expect_indicator_sub`. |
| 4 bound | `ε n = n · distAdv(…, D)`: `((singleBitSecure_iff S).1 h D).polyExpr_mul .var`; for `n > 0`, `div_le_iff₀` on the gap. |

**Edge cases.** The computation is treated abstractly, so the proof is uniform in the budget
(`q = 0` included) and in the codec's timeout output `zeroBits 1`, which is just `A`'s output on
both sides. A run with no challenge is the `firstQ = none` branch: both hybrids give `F []`, `D`
outputs `[0]` (`plantOut_init`). Repeated challenges get the recorded answer in the hybrids
(`chRun_query_one_some`) and the same assembled tuple in the handler (`qRun_recorded`,
`simulate_qHandler_recorded`). At `n = 0` the bound is `0 ≤ 0`.

**Checkpoints.** All four steps were completed together, so checkpoint 1 (exchange `43a16abd1`,
proof-branch `1f83fc508`) already carried the complete proof with the checks pending; commit 3
(`4cc388aba`) is the seal fix of §5. Checkpoints 2 and 3 were not sent separately.

## 2. Changed files and declarations

`git diff --stat 4a9b2c91..4cc388aba`: 4 files, 1370 insertions, 19 deletions.

| File | Lines | Change |
|---|---|---|
| `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean` (owned) | 105 → 553 | 3 imports; new private section `BitwiseCPAProof` before the target; target body and sketch; the module docstring's status phrase |
| `…/PublicKey/BitwiseCPA/QueryHandler.lean` (new helper) | 395 | generic query-recording handler with advice, its simulation, transport, machine by T1 |
| `…/PublicKey/BitwiseCPA/Planted.lean` (new helper) | 316 | the planted tuple, padded answer and final bit (generic in the encryptor), list identities |
| `…/PublicKey/BitwiseCPA/Eager.lean` (new helper) | 192 | eager coins (generic and for `indImpl`), coordinate resampling, readers |

The helpers import neither `BitwiseCPA` nor anything downstream of it; `BitwiseCPA` imports all
three explicitly. All files are below 1000 lines. `AdaptiveCPA.lean`, `OracleSecurity.lean`, the
`OracleSecurity/` helpers, `EnsembleSecurity.lean` and every other existing file are unchanged.
Statements, other declarations (including the two proved corollaries), the statement prose and
global simp attributes are unchanged. **Sketch edits:** the target's `**Proof sketch.**` now
describes the delivered proof; the module docstring's "Main results" line lost "(stated; a `sorry`
under its sketch)" and names the three helpers.

**New public declarations** (namespace `TCSlib.Cryptography.Composability.BitwiseSim`; each with a
formula docstring, and a proof sketch when nontrivial; definitions with `_eq` or case lemmas, the
structure with `simps` field equations, `isSimp := false`):
- `QueryHandler`: `qDin` (+ `_zero`, `_one`), `qDout` (+ `_zero`, `_one`), `qRun` (+ `qRun_eq`,
  `qRun_dec`, `qRun_fresh`, `qRun_recorded`, `polyTimeComputable_qRun`), `qHandler` (+ `simps`
  equations), `decodeFin_nil_getD`, `qHandler_answer_dec`, `simulate_qHandler_recorded`,
  `simulate_qHandler_init`, `chRun_toCompOn_transport_list`, `exists_qHandlerMachine`.
- `Planted`: `ofFn_const_of_eq_one`, `flatten_ofFn_singleton`, `take_ofFn_flatten`,
  `drop_ofFn_flatten`, `headD_drop`, `plantTuple` (+ `_eq`, `polyTimeComputable_plantTuple`,
  `plantTuple_spec`), `plantAns` (+ `_eq`, `polyTimeComputable_plantAns`), `plantOut` (+ `_eq`,
  `plantOut_init`, `plantOut_recorded`, `polyTimeComputable_plantOut`).
- `Eager`: `expect_simulate_eager`, `expect_simulate_indImpl_cpa`, `ofFn_cast`,
  `expect_sample_update`, `indCodec_eq_bitCodec`, `padded_enc_runAt`, `padded_enc_coins`.

**New private declarations in `BitwiseCPA.lean`:** `hybCt`, `hybGame`, `bitwise_runAtL`,
`bitwise_runAt_blocks`, `ofFn_half`, `ofFn_getD_split`, `accept_indGame_eq`, `planted_eq`,
`hybCt_update`, `bwLaux`, `bwAux`, `bwAux_length`, `hyb_advantage_eq`.

## 3. Promotion, duplication and reader requests (DL-30)

**Promotion requests.**
1. `BitwiseSim.expect_simulate_eager` / `expect_simulate_indImpl_cpa`: the eager-coins lemma. The
   `padded_cpa` proof has it as a private lemma of `OracleSecurity.lean`; this copy is restated
   for a generic CPA-shaped oracle and instantiated through `indImpl_*_onSpec`, because a verbatim
   copy outside `OracleSecurity` would read `inLens`/`outLens` definitionally. Proposed home:
   the generic form in `OracleSecurity/ChallengeSim.lean`, the instance as a public lemma of
   `OracleSecurity.lean` (replacing its private one).
2. `indCodec_eq_bitCodec`, `padded_enc_runAt`, `padded_enc_coins`: readers of
   `FixedLengthPKScheme.indCodec` and `PublicKeyScheme.padded` derived from the published ones;
   they belong beside `indCodec_*` and `padded_*` in `OracleSecurity.lean`.
3. `expect_sample_update` (resampling one coordinate of a uniform tuple) belongs with the
   sampling identities of `ChallengeSim` or in `Games/Probability.lean`.
4. `chRun_toCompOn_transport_list` generalizes `ChallengeSim.chRun_toCompOn_transport` to a
   query-dependent answer; it belongs beside it.
5. `ofFn_cast`, `ofFn_const_of_eq_one`, `flatten_ofFn_singleton`, `take_ofFn_flatten`,
   `drop_ofFn_flatten`: generic list facts for a shared list module.

**Duplication.** `headD_drop` (`(l.drop k).headD false = l.getD k false`) duplicates the public
`headD_drop` of `ZeroKnowledge/CommitmentLemmas.lean` (with a general default) and
`getD_eq_headD_drop` of `ZeroKnowledge/GraphIsomorphism/EfficiencyRep.lean`; I did not import them
because that would pull the zero-knowledge closure into this unit. Mathlib's
`ofFn_take_eq_take_ofFn` (`Mathlib/Data/Fin/Tuple/Take.lean`) is close to `take_ofFn_flatten` but
is outside the roots. A search found no other existing lemma of these forms.

**Reader requests (none blocking).** `HybridMachine.hybridPre` has no published `_eq` reader, so
its proved polynomial-time bound could not be used; `plantTuple` rebuilds the planted assembly from
`blockEncFun` (with readers `blockState_eq`, `blockEncFun_flatten`, `encodeList_ofFn_split`,
`coinBlock_drop`). A `hybridPre_eq` would let the two share one function.

## 4. Environment, cache and bootstrap

- **Preflight** (`evidence/logs/preflight.log`): `nproc` 4. The cgroup is v1 and
  `memory.limit_in_bytes` is the unlimited sentinel (2^63 − 4096), so the headroom is
  `MemAvailable` = 15,939,212 kB = 15.20 GiB (floor 4 GiB): PASS. The clone's filesystem is ext4
  on `/dev/vda` with 20,396,564,480 B = 19.00 GiB free (floor 12 GiB): PASS; the scratch
  directories are on the same filesystem (no tmpfs).
- **One clone**: `/home/user/fill`, a worktree of the session's checkout, with its own `.lake`.
  It is the clone (and `.lake/packages`) this session used for the `padded-cpa` fill earlier on
  this host; the toolchain and `lake-manifest.json` are identical between the two bases. Nothing
  was copied, moved or deduplicated.
- **Cache**: store before the fetch `/root/.cache/mathlib`, 2,372 files, 118,543,444 bytes
  (`evidence/logs/cache-store.log`), written by the cache tool during that earlier fill; none were
  downloaded by this fill. Narrowed `TAR_OPTIONS=--no-same-owner lake exe cache get` for the 92
  roots (identical to `roots.txt`): "No files to download", "Decompressing 2345 file(s)",
  "Completed successfully!", exit 0 (`evidence/logs/cache-get.log`). No empty `.olean`. Cache
  probe `import Mathlib.Algebra.BigOperators.Field`: passed (`evidence/logs/cache-probe.log`).
- **Packages**: `package check: PASS (0 mismatches)` before and after the fetch; ABSENT
  `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`, none imported by the order list
  (`evidence/logs/packages.log`).
- **Bootstrap**: a fresh olean tree (`TCSLIB_OLEANS=.lake/bw-oleans`). The 153-module upstream
  closure of `PublicKey/BitwiseCPA`, in the order list's order, all passed
  (`evidence/logs/bootstrap.log`, `bootstrap-closure.txt`); the remaining modules were built by
  the sweep.
- **Process discipline**: one Lean process at a time, every check through
  `scripts/lean_check_tree.sh` (`evidence/tools/chk.sh` logs start, end, status, elapsed time and
  maximum child RSS). No `lake build`. **Deviation:** one development check of the
  owned module hung in a looping tactic and was stopped after about 40 minutes by the tool
  runner's background limit (no Lean exit code, no output). To locate it I set
  `maxHeartbeats 400000` in the owned file during development and ran that one check under a
  25-minute `timeout` (it finished in 28 s); the cap is gone (the file keeps the base's
  `maxHeartbeats 0`), and no other check was wrapped in a timeout. Development logs:
  `evidence/logs/dev/`.

## 5. Checks

| Check | Result | Evidence |
|---|---|---|
| Owned and helper modules | `BitwiseCPA`, `BitwiseCPA/{QueryHandler, Planted, Eager}`: no errors, no warnings | `logs/sweep.log` |
| Sweep (final head `4cc388aba`) | `order-new.txt`, 200 modules, one `lean_check_tree.sh` call each: **200 passed, 0 failed** | `logs/sweep.log` |
| `sorry` census | **26** (base 27); removed vs base: exactly `bitwise_padded_cpa`; added: none | `logs/sorry-census.txt` |
| Axioms | `bitwise_padded_cpa`: `[propext, Classical.choice, Quot.sound]`; `bitwise_padded_adaptive_cpa` and `exists_adaptive_cpa`: `[propext, sorryAx, Classical.choice, Quot.sound]` (the `sorryAx` is the parallel `adaptive-cpa` target `INDSecure.adaptive_cpa`) | `logs/axioms.log`, `probe/Axioms.lean` |
| Lint | `campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`: 0 FAIL, 6 WARN over 22 files; the same 6 WARN at the base (19 files), all in untouched files; the helper subdirectory alone: 0 FAIL, 0 WARN | `logs/lint-after.log`, `lint-before.log`, `lint-subdirs.log` |
| Patches | `git apply` of `patches/` onto a clean base worktree reproduces all four `src/` files byte for byte | `logs/patch-reproduce.log` |

An earlier full sweep at `1f83fc508` (before the seal fix) also passed 200/200 with the same census
(`logs/sweep-1.log`, `sorry-census-1.txt`). Resources: peak child RSS 2,945 MiB over all checks;
`BitwiseCPA/Planted` takes about 220 s unsealed (2–3 s sealed, so the time goes to definitional
unfolding attempts that the proof does not need); the owned module takes 25 s.

## 6. Readings: scan, seal, controls, explicit unfolds

- **Scan** (`seal/SealScan.lean`, `logs/seal-scan.log`): roots are the target, its 13 private
  helpers and every declaration of the three helper modules (67 roots, 92 declarations scanned
  with their auxiliaries). 95 foreign TCSlib definitions are used: 66 regular (the seal
  candidates, `seal/candidates.txt`) and 29 reducible (abbrevs such as `bitSpec`, `bitSpecAt`,
  `indSpec`, `NUPPT.Coins`, `padEnc`, and structure projections). **TCSlib instances used: 0.**
- **Seal** (`seal/Seal{QueryHandler,Planted,Eager,BitwiseCPA}.lean`, `logs/seal.log`): verbatim
  copies of the four files with `attribute [local irreducible]` on every regular foreign definition
  their roots use (23, 17, 26 and 48), from each namespace's first `open` on, so the whole file
  including the target and the untouched corollaries is sealed. **All four compile.**
- **Finding and fix.** The first sealed run failed in `SealQueryHandler`: `qHandler`'s
  `advIn_poly` field read the body of the published `RecordHandler.recAdvIn` definitionally. It
  now goes through `recAdvIn_eq` (proof-branch commit 3, `4cc388aba`); the sweep, seal and scans
  were redone at that head. During development the same discipline led me to restate the eager
  coins through `indImpl_*_onSpec`, `indSpec_challengeDom`/`_challengeRng` and `inLens_one`/
  `outLens_one` (`ofFn_cast`) instead of identifying `Fin (inLens n 1)` with
  `Fin (msgLen + msgLen)` by unfolding.
- **Controls** (`seal/SealControls{Unsealed,Sealed}.lean`): eight readings through definition
  bodies, namely `inLens`, `outLens`, `PolyExpr.eval`, `padCt`, `seedIn`, `ChallengeSim.chRun`, and the
  new helpers `qDin` and `plantAns`. Unsealed: all pass. Sealed with the full candidate list: all
  eight fail (8 errors). **8/8.**
- **Explicit-unfold scan** (`seal/RwIds*.lean`, `logs/rwids.log`, `logs/rwids-files.tsv`): every
  identifier the added lines pass to `rw`, `rwa`, `erw`, `simp`, `simp only`, `simp_rw`, `simpa`,
  `dsimp` or `unfold`, resolved in each file's namespace (245 entries). **No foreign definition is
  passed**: the resolved names are theorems, and the only definitions passed are the owned file's
  own private `hybGame`, `hybCt`, `bwAux` and `bwLaux` (listed unresolved because private, with
  local hypotheses).

## 7. Order and roots

`evidence/logs/order-new.txt`: the issued 197-module order with the three helpers inserted
immediately before `PublicKey/BitwiseCPA` (`…/BitwiseCPA/Eager`, `…/Planted`, `…/QueryHandler`),
200 modules; every module's TCSlib imports precede it, and the upstream closure of
`PublicKey/BitwiseCPA` is contained in it. The helpers import no Mathlib module directly; the
Mathlib roots of the extended order are unchanged (92, identical to `roots.txt`).

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

## ===== briefs/pass-shelat-ch5-8/fills/adaptive-cpa/issued-r1/brief.md =====

# Claude fill · adaptive CPA lift (`adaptive_cpa`)

**Issue base** `4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27` on `cryptography/pass-shelat-ch2-4`
(the merges of #287 and #288). **Unit** `adaptive-cpa`. **Worker** Claude. **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorem `Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa` in
`TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA.lean`: single-challenge CPA security of a
fixed-length public-key scheme gives security in the adaptive left-or-right multi-challenge CPA
game [PS10, Definition 171.5; the single-to-many hybrid argument of p. 103, extended to adaptive
challenges]. The statement passed Gate 12. With the parallel `bitwise-cpa` fill it completes the
first catalog route (`SingleBitSecure.exists_adaptive_cpa`). The `bitwise-cpa` fill does not
touch this file, and this fill does not touch `BitwiseCPA.lean`.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/adaptive-cpa` at the exact
  issue base above. Record the base in `REPORT.md`. Keep the local branch at that ancestry.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/adaptive-cpa/` on
  `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`, the whole `git format-patch` series from the issue base;
  - `src/`, the owned paths;
  - `evidence/`.

  Use the commit messages `fill adaptive-cpa: checkpoint N` and `fill adaptive-cpa: final`. Pull
  with rebase before pushing, push only your delivery path, and never force-push. Keep the proof
  branch local. Campaign changes land by a maintainer PR for Seyoon's approval.

## Target

The statement is frozen. This quote comes from the issue base:

```lean
theorem INDSecure.adaptive_cpa {S : FixedLengthPKScheme} (h : S.INDSecure .cpa) :
    S.AdaptiveINDSecure .cpa := by
  sorry
```

The games:
- `S.indGame .cpa B q b n` (`PublicKey/OracleSecurity.lean`) is the single-challenge game.
- `S.adaptiveIndGame .cpa A q cap b n` (`PublicKey/AdaptiveSecurity.lean`) is the adaptive game.
  It keeps a history of fresh challenges:
  - each fresh challenge below the cap prepends one entry, even when the ciphertext value repeats;
  - a challenge at the cap repeats the latest ciphertext;
  - with cap 0 and an empty history, every challenge returns `zeroBits`;
  - under CPA, `Dec` returns the refusal reply whatever the history.

## Published interfaces

Read every definition of another file through these published lemmas (policy §1, rule 10).

| Interface | Provider |
|---|---|
| `adaptiveIndImpl_dec_issued`, `_dec_other`, `_challenge_fresh`, `_challenge_encrypt`, `_challenge_full`, `_challenge_zero`, `adaptiveIndGame_eq`, `adaptiveINDSecure_iff`, `adaptiveIndGame_one`, `simulate_adaptiveIndImpl_one` | `PublicKey/AdaptiveSecurity.lean` |
| `indImpl_dec_cpa`, `indImpl_dec(_onSpec)`, `indImpl_challenge_none(_onSpec)`, `indImpl_challenge_repeat(_onSpec)`, `indSpec_eq`, `indSpec_dom/_rng`, `indSpec_decDom`, `indSpec_challengeDom/_Rng`, `inLens_*`, `outLens_*`, `indCodec_*`, `indGame_eq`, `INDSecure_iff` | `PublicKey/OracleSecurity.lean` |
| `ChallengeSim` (`chRun`, `firstQ`, their equations, `chRun_toCompOn_transport`, `expect_sample_*`, `expect_sub`) and `RecordHandler` (a worked `PolyHandler` with readers) | `PublicKey/OracleSecurity/` (from #288; reuse their patterns) |
| `Games.exists_interactiveHandlerMachine` (T2); `InteractiveHandler.input_eq`, `advInput_eq`, `call_eq`, `impl_apply`, `finInput_eq`, `finish_eq` | `Games/Efficiency.lean` |
| `Games.exists_advantage_hybrid_gap`, `advantage_eq`, `advantage_triangle`, `accept_eq` | `Games/Advantage.lean` |
| `Negligible.polyExpr_mul` | `Asymptotic/ReductionSupport.lean` |
| `prob_*`, `expect_*`, `sample_eq`, `Bridge.expect_sample_pair` | `Games/Probability.lean`, `Games/Bridges/Experiments.lean` |
| `simulate` equations, `OracleComp` laws, `NUPPT.toCompOn_eq`, `buildComp` cases, `bitCodec_*`, `decodeBitMove_*` | `Games/Simulate.lean`, `OracleComp.lean`, `Machines.lean`, `BitCodec.lean` |
| `NUPPT` run, coin and closure lemmas | `Complexity/Randomized/PPT.lean`, `NonUniform.lean`, `Closure.lean` |

`NUPPT.Coins`, `bitSpecAt`, `bitSpec`, `QueryImpl`, `OracleSpec.add` and `indSpec` are
abbreviations; `PolyExpr.eval` is notation. If a needed equation has no published reader, record
it in `REPORT.md` and use the escalation route below; do not unfold the foreign definition.

## Proof route and checkpoints

Gate 12's auditor confirmed this route. The docstring sketch is authoritative.

1. **Hybrids.** For `i ≤ cap(n)`, define `H_i` (a private game, or a family of oracle
   implementations) in which the first `i` fresh challenges encrypt the right message and later
   ones the left. Prove that `H_0` and `H_{cap(n)}` equal the `b = false` and `b = true` adaptive
   games. Read the cap semantics through the published equations. Send checkpoint 1.
2. **The reduction `B`.**
   - Build `B` through T2 with `perCall = 1` and `finCall = 0`. The handler state holds the
     fresh-challenge count, the latest ciphertext and the advised index `i⋆(n)`, placed in
     `InteractiveHandler.init`, which may be any function of `n`.
   - The seed is `cap(n)` encryption tapes.
   - The handler answers fresh challenges below `i⋆` with `Enc` of the right message and those
     above it with `Enc` of the left message, using `pk` and its own tapes. It forwards challenge
     `i⋆ + 1` to its outer `Challenge`, repeats the latest ciphertext past the cap, answers `Dec`
     with the refusal reply, and finishes with `A`'s bit.
   - Its run must be polynomial-time: `Enc` is uniform and polynomial-time.
   - **Codec alignment** is a known obligation: T2 states its simulation with
     `bitCodec (fun i => (din i).eval n) …`, while the games use `S.indCodec n`. Transport once,
     generically, as `chRun_toCompOn_transport` does.

   Send checkpoint 2.
3. **`B`'s game is `H_{i⋆+b}`.**
   - Prove that `B`'s single-challenge game with bit `b` has the same output distribution as
     `H_{i⋆(n)+b}`.
   - Independent seed tapes must reproduce the fresh-encryption distribution of the adaptive game.
     This includes branches that never reach challenge `i⋆ + 1`; there both sides agree.
   - Use T2's coin equivalence and the sampling identities.

   Send checkpoint 3.
4. **The bound.**
   - Apply `h` to `B` with the polynomial outer budget `q·perCall + finCall`.
   - With `exists_advantage_hybrid_gap` at `cap(n) > 0`, `A`'s advantage is at most
     `cap(n) · ε(n)`. Cap 0 gives advantage 0.
   - `Negligible.polyExpr_mul` with `cap` concludes.
   - Do not assume `n > 0`: a general scheme can have nonempty messages at `n = 0`.

   Send the final delivery.

Check: query budget 0, cap 0, repeated fresh ciphertext values, a run that never reaches
challenge `i⋆ + 1`, and the timeout output.

## Scope and proof discipline

- **Owned files.** Own `TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA.lean`. Replace the one
  proof body and add helpers there. Generic helper modules are permitted under
  `TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/`, imported precisely by the owned file.
  Keep every file below 1000 lines.
- **Frozen.** Do not edit `BitwiseCPA.lean`, the `OracleSecurity/` helpers or any other existing
  file. If you need a lemma that belongs in an existing file, put it in your helper module and
  list it in `REPORT.md` as a promotion request.
- **Generic lemmas.** Put generic probability facts in a helper module and list them for promotion
  to `Games/Probability.lean` (duplication ledger DL-30). Do not copy existing lemmas; grep first.
- **Edits allowed.** You may edit the target's proof sketch to describe the delivered proof.
  Preserve the statement, every other declaration, the statement prose and the global simp
  attributes. Public helpers get a docstring with their formula, and a proof sketch when
  nontrivial (policy §3).
- **Reading definitions.** Use published readers for other files' definitions, in tactics and in
  term elaboration, including generated matchers and projections. For core and Mathlib, use their
  equation lemmas in `simp`, `rw` and `unfold`.
- **Escalation.** If the target appears false, or a required reader is missing with no clean
  route, write the exact failing obligation and the smallest proposed correction in `REPORT.md`,
  then push a checkpoint.

## Checks and report

- **Bootstrap.** Bootstrap from `order.txt` and the narrow `roots.txt`, following the environment
  addendum. Insert any new helper module before its consumer, and recalculate the roots if imports
  change. Check one module per `scripts/lean_check_tree.sh` invocation, with one Lean process per
  olean tree.
- **Sweep.** Recheck the owned modules, then sweep the supplied order. Compare `sorry` warnings with
  `base-sorries.txt`; the only change must be the removed `INDSecure.adaptive_cpa`.
- **Axioms.** Print the axioms of `adaptive_cpa` (expected: only `propext`, `Classical.choice`,
  `Quot.sound`). Also print those of `SingleBitSecure.bitwise_padded_adaptive_cpa` and
  `exists_adaptive_cpa`, and report exactly what they print. They still depend on the
  `bitwise-cpa` target.
- **Rule 10.**
  - Collect foreign references from the elaborated new proofs, including generated matcher and
    projection helpers.
  - Run an instance-aware seal of the touched declarations with the full candidate list.
  - Add controls that pass before sealing and fail after.
  - Run the explicit-unfold scan.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`.
- **Report.** Give the issue base, the target's status, the exact changed files and sketch edits,
  the new declarations, any promotion or reader requests, and the resource, cache, bootstrap,
  sweep, axiom, seal and lint evidence.

**Ready to dispatch**

## ===== briefs/pass-shelat-ch5-8/fills/bitwise-cpa/issued-r1/brief.md =====

# Claude fill · padded bitwise CPA (`bitwise_padded_cpa`)

**Issue base** `4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27` on `cryptography/pass-shelat-ch2-4`
(the merges of #287 and #288). **Unit** `bitwise-cpa`. **Worker** Claude. **Lean** 4.25.0 and the
Mathlib revision in that commit's `lake-manifest.json`.

Prove the admitted theorem `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa` in
`TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean`. It says: if a single-bit public-key
scheme is secure, the padded bitwise scheme with `n`-bit messages is CPA-secure in the game of
[PS10, Definition 171.5], where the adversary chooses its messages after seeing the public key
[PS10, the bitwise scheme and hybrid argument of p. 103]. The statement passed Gate 12. With the
parallel `adaptive-cpa` fill it completes `SingleBitSecure.exists_adaptive_cpa`, which is already
proved from the two targets. The `adaptive-cpa` fill does not touch this file, and this fill does
not touch `AdaptiveCPA.lean`.

## Checkout and delivery

- Fetch `cryptography/pass-shelat-ch2-4` and start a local branch `fill/bitwise-cpa` at the exact
  issue base above. Record the base in `REPORT.md`. Keep the local branch at that ancestry.
- Read `policy.md`, the attached environment addendum and `README.md`.
- Deliver every checkpoint and the final payload under `inbox/fills/bitwise-cpa/` on
  `exchange/pass-shelat-ch5-8`:
  - `REPORT.md`;
  - `patches/`: the whole `git format-patch` series from the issue base;
  - `src/`: the owned paths;
  - `evidence/`.

  Use the commit messages `fill bitwise-cpa: checkpoint N` and `fill bitwise-cpa: final`. Pull with
  rebase before pushing, push only your delivery path, and never force-push. Keep the proof branch
  local. Campaign changes land by a maintainer PR for Seyoon's approval.

## Target

The statement is frozen. This quote comes from the issue base.

```lean
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).INDSecure .cpa := by
  sorry
```

## The worked precedent

`BitPublicKeyScheme.SingleBitSecure.padded_cpa` (`PublicKey/OracleSecurity.lean`, landed in #288,
Gate 13 CLEAR) proves the one-bit case of this argument. Its proof shows an exact identity:
`advantage = distAdv` for a distinguisher built by T1. It uses three steps:
- eager challenge coins (`expect_simulate_indImpl_cpa`);
- first-challenge congruence (`ChallengeSim.chRun_congr`);
- a recording handler (`RecordHandler.recHandler`).

This fill reuses that pattern with a hybrid over the `n` message bits. Study it first.
`ChallengeSim` and `RecordHandler` are public. Reuse them where their contracts apply. Where they
do not (`RecordHandler` records 2-bit challenges), write a new handler in your helper module.

## Published interfaces

| Interface | Provider |
|---|---|
| `bitwise_gen`, `bitwise_enc`, `bitwise_dec`, `bitwise_enc_runAt`, `bitwise_enc_runAtL`, `bitwiseEncCoins`, `bitwiseEncCoins_ofFn`, `bitwise_enc_coinLen`, `singleBitSecure_iff`, `pkEncDist_eq` | `PublicKey/EnsembleSecurity.lean` |
| `PublicKeyScheme.padded_msgLen/_ctLen/_gen/_enc/_dec`, `padCt_eq`, `length_padCt`, `pairFstD_padCt`, `padEnc_coins`, `runAt_padEnc`, `padEncFun_eq`, `indImpl_*` (incl. `_onSpec`), `indSpec_*`, `inLens_*`, `outLens_*`, `indCodec_*`, `indGame_eq`, `INDSecure_iff`; the `padded_cpa` proof's private helpers are a model, not an interface | `PublicKey/OracleSecurity.lean` |
| `ChallengeSim.*`, `RecordHandler.*` | `PublicKey/OracleSecurity/` |
| `Games.exists_handlerMachine` (T1) and the `PolyHandler` readers | `Games/Efficiency.lean` |
| `Games.exists_advantage_hybrid_gap`, `advantage_eq`, `accept_eq` | `Games/Advantage.lean` |
| `Negligible.polyExpr_mul` | `Asymptotic/ReductionSupport.lean` |
| `NUPPT.distinguisherL_eq`, `Bridge.distAdv_eq`, `acceptProb_eq`, `expect_sample_pair` | `Asymptotic/Adversary.lean`, `Games/Bridges/Experiments.lean` |
| `prob_*`, `expect_*`, `simulate` equations, `OracleComp` laws, `NUPPT` run/coin/closure lemmas, `encodeList` readers | `Games/*`, `Complexity/Randomized/*`, `PrivateKey/Scheme.lean` |

The same abbreviation, notation and escalation rules apply as in the `padded_cpa` fill.

## Proof route and checkpoints

The docstring sketch, confirmed by Gate 12's auditor, is authoritative.

1. **Bit hybrids.** For `j ≤ n`, let `H_j` be the CPA experiment whose challenge encrypts, with
   independent coins per bit, the first `j` bits of the right message and the rest of the left.
   - Prove `H_0` and `H_n` are the `b = false` and `b = true` games.
   - Read the bitwise layout through `bitwise_enc_runAt`, and the coin blocks through
     `bitwiseEncCoins_ofFn`.
   - At `n = 0` both messages are empty and the advantage is `0`.

   Send checkpoint 1.
2. **The single-bit distinguisher `D` (T1).**
   - On `⟨pk, c⟩`, `D` runs `A`. It answers the challenge `⟨m₀, m₁⟩` with the padded bitwise
     ciphertext whose block `j⋆` is `c`. It encrypts the other blocks itself on `pk` and its seed
     tapes: bits of `m₁` before `j⋆`, bits of `m₀` after.
   - It records the first challenge. Repeated challenges get the same assembled ciphertext.
   - Its output is `A`'s bit, flipped when `(m₀_{j⋆}, m₁_{j⋆}) = (1, 0)`, and `[0]` when the two
     bits agree or no challenge was asked.
   - `j⋆(n)` is in the handler's initial state (any function of `n`). The seed is `n` single-bit
     encryption tapes.

   Send checkpoint 2.
3. **The exact identity.** Prove that `advantage(H_{j⋆}, H_{j⋆+1})` equals `D`'s single-bit
   advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`.
   - Use eager coins and the first-challenge congruence, as in `padded_cpa`.
   - The signed case split is the same as Gate 12's table: `(0,1)`, `(1,0)`, equal bits, and no
     challenge.

   Send checkpoint 3.
4. **The bound.**
   - `exists_advantage_hybrid_gap` at `n > 0` gives `A`'s advantage `≤ n ·` `D`'s advantage.
   - `singleBitSecure_iff` makes the latter negligible.
   - `Negligible.polyExpr_mul` with `PolyExpr.var` concludes.

   Send the final delivery.

Check: budget `q = 0`, no challenge, repeated challenges, the timeout output, and `n = 0`.

## Scope and proof discipline

- **Owned files.** Own `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean`: replace the one
  proof body and add helpers there. Generic helper modules are permitted under
  `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/`, imported precisely by the owned file. Keep
  every file below 1000 lines.
- **Frozen.** Do not edit `AdaptiveCPA.lean`, `OracleSecurity.lean`, the `OracleSecurity/` helpers,
  `EnsembleSecurity.lean` or any other existing file. If a lemma belongs in an existing file, put it
  in your helper module and list it in `REPORT.md` as a promotion request.
- **Generic lemmas.** List generic probability facts for promotion (duplication ledger DL-30), and
  reuse existing ones; grep first.
- **Edits allowed.** You may edit the target's sketch to describe the delivered proof. Preserve the
  statement, every other declaration (including the proved corollaries), the statement prose and
  the global simp attributes. Public helpers get formula docstrings and proof sketches (policy §3).
- **Reading definitions.** Use published readers for other files' definitions, in tactics and in
  term elaboration, including generated matchers and projections.
- **Escalation.** If the target appears false or a required reader is missing with no clean route,
  record the exact failing obligation and the smallest proposed correction in `REPORT.md`, then push
  a checkpoint.

## Checks and report

- **Bootstrap.** Use `order.txt` and the narrow `roots.txt` per the addendum. Insert new helper
  modules before their consumer. Check one module per `scripts/lean_check_tree.sh` call, with one
  Lean process per olean tree.
- **Sweep.** Recheck the owned modules, then sweep the supplied order. Compare `sorry` warnings with
  `base-sorries.txt`: the only change must be the removed `bitwise_padded_cpa`.
- **Axioms.** Print the axioms of `bitwise_padded_cpa` (only `propext`, `Classical.choice`,
  `Quot.sound`). Also print them for `bitwise_padded_adaptive_cpa` and `exists_adaptive_cpa`, and
  report exactly what they print: they still depend on the `adaptive-cpa` target.
- **Seal and scan.** Run an instance-aware seal of the touched declarations with the full candidate
  list and controls, and the explicit-unfold scan.
- **Lint.** Run `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Encryption/PublicKey --check8b`.
- **Report.** Give the base, the status, the changed files and sketch edits, the new declarations,
  any promotion or reader requests, and the evidence.

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

## ===== TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Reduction
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.ReductionSupport

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# From one challenge to adaptively many under chosen-plaintext attack

For a public-key scheme, security in the single-challenge CPA game of [PS10, Definition 171.5]
implies security in the adaptive left-or-right game with a polynomial number of fresh
challenges (`FixedLengthPKScheme.AdaptiveINDSecure`). The argument is the single-to-many hybrid
lifting of [PS10, p. 103] and [Pas09, Theorem 2], stated there for fixed message vectors and
extended here to adaptively chosen challenges: the adversary holds the public key, so a
reduction can produce every challenge but one itself.

## Main results

* `Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa`: single-challenge CPA security
  gives adaptive multi-challenge CPA security.

## Contents

* `AdaptiveCPA/Hybrid`: the hybrid challenge oracles, transport along equal lengths, simulation
  through a state abstraction, and coins in advance against lazy coins.
* `AdaptiveCPA/Handler`: the reduction's handler for T2 and its call equations.
* `AdaptiveCPA/Games`: the hybrid games; the end hybrids are the adaptive games.
* `AdaptiveCPA/Reduction`: the reduction's single-challenge game is a hybrid.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 171.5 (book p. 171) and the single-to-many hybrid argument (book p. 103).
* [Pas09] R. Pass, *Cornell CS 6830, lecture 13* (2009), §1 and Theorem 2.
-/

namespace TCSlib.Cryptography.Composability.FixedLengthPKScheme

open Complexity Turing TCSlib.Cryptography.Games

/-- **Single-challenge CPA security gives adaptive multi-challenge CPA security**: if every
efficient adversary has negligible advantage in the CPA game with one challenge, then every
efficient adversary has negligible advantage in the adaptive left-or-right CPA game with a
polynomial challenge cap `cap(n)` and query budget `q(n)` [PS10, Definition 171.5; the
single-to-many hybrid argument of p. 103, extended to adaptive challenges].

**Proof sketch.**
1. Fix `A`, `q` and `cap`. For `i ≤ cap(n)` let `H_i` be the adaptive CPA experiment in which the
   first `i` fresh challenges encrypt the right message and the later ones the left message
   (`AdaptiveCPA.acHyb` with the selector `j ↦ [j < i]`, run on T2's codec). Then `H_0` is the
   experiment with `b = false` and `H_{cap(n)}` the one with `b = true`
   (`AdaptiveCPA.acHyb_lt_zero`, `AdaptiveCPA.acHyb_lt_cap`): the adaptive oracles are the
   hybrid with a constant selector (`AdaptiveCPA.castImpl_adaptiveIndImpl`, from
   `adaptiveIndImpl_challenge_encrypt`, `_full`, `_zero`, `_dec_issued`, `_dec_other` and
   `indImpl_dec_onSpec`), and the selector matters only below the cap
   (`AdaptiveCPA.acHyb_congr`).
2. By `Games.exists_advantage_hybrid_gap`, at each `n` with `cap(n) > 0` some `i⋆(n) < cap(n)`
   has `advantage(H_{i⋆}, H_{i⋆+1}) ≥ advantage(H_0, H_{cap(n)}) / cap(n)`; the case `cap(n) = 0`
   has advantage `0`, and there `i⋆(n) = 0`.
3. The single-challenge adversary `B` is T2's machine (`Games.exists_interactiveHandlerMachine`)
   for the handler `AdaptiveCPA.acHandler S cap i⋆`: its state holds the challenge count, the
   latest ciphertext and `i⋆(n)` (its initial state), its seed is `cap(n)` encryption tapes, it
   answers `Dec` with `⊥`, the `j`-th fresh challenge with its own encryption of `m_{[j < i⋆]}`
   for `j ≠ i⋆`, forwards the `i⋆`-th to its one outer `Challenge` call (`perCall = 1`), repeats
   the latest ciphertext past the cap, and outputs `A`'s bit (`finCall = 0`). Its round function
   is polynomial-time because `Enc` is uniform and polynomial-time. `B`'s game with bit `b`
   accepts with the probability of `H_{i⋆+b}` (`AdaptiveCPA.accept_indGame_acHyb`): the
   handler composed with the outer oracles is, through an abstraction of its states, the hybrid
   with the handler's tapes as coins in advance, and uniform tapes give the lazy hybrid
   (`AdaptiveCPA.expect_tapeImpl`).
4. `B` makes at most `q(n)·perCall + finCall` outer queries, a polynomial, so `h` bounds its
   advantage by a negligible `ε`. Hence `A`'s advantage is at most `cap(n) · ε(n)`, negligible
   by `Negligible.polyExpr_mul` (`Asymptotic/ReductionSupport`) with the polynomial `cap`. -/
theorem INDSecure.adaptive_cpa {S : FixedLengthPKScheme} (h : S.INDSecure .cpa) :
    S.AdaptiveINDSecure .cpa := by
  rw [S.adaptiveINDSecure_iff]
  rw [S.INDSecure_iff] at h
  intro A q cap
  -- Step 2: at each `n` the hybrid lemma advises an index `i⋆(n) ≤ cap(n)`.
  have hgap : ∀ n, ∃ i, i ≤ cap.eval n ∧
      advantage (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < 0))
          (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < cap.eval n)) ≤
        (cap.eval n : ℝ) *
          advantage (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < i))
            (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < i + 1)) := by
    intro n
    rcases Nat.eq_zero_or_pos (cap.eval n) with h0 | hpos
    · refine ⟨0, Nat.zero_le _, ?_⟩
      rw [h0, advantage_self, Nat.cast_zero, zero_mul]
    · obtain ⟨i, hi, hle⟩ := exists_advantage_hybrid_gap
        (fun i => AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < i)) hpos
      refine ⟨i, hi.le, ?_⟩
      rw [div_le_iff₀ (Nat.cast_pos.2 hpos)] at hle
      rw [mul_comm]
      exact hle
  choose ist hist hgap using hgap
  -- Step 3: the reduction is T2's machine for the handler with the advised index.
  obtain ⟨B, hB⟩ := exists_interactiveHandlerMachine A q (AdaptiveCPA.acDin S)
    (AdaptiveCPA.acDout S) (AdaptiveCPA.acDin S) (AdaptiveCPA.acDout S) (.const 1)
    (AdaptiveCPA.acHandler S cap ist)
  -- Step 4: single-challenge security bounds `B`'s advantage at the polynomial outer budget.
  obtain ⟨ε, hε, hεB⟩ := h B ((q.mul (AdaptiveCPA.acHandler S cap ist).perCall).add
    (AdaptiveCPA.acHandler S cap ist).finCall)
  refine ⟨fun n => (cap.eval n : ℝ) * ε n, hε.polyExpr_mul cap, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hB n
  have hred : ∀ b : Bool, accept (S.indGame .cpa B
      (((q.mul (AdaptiveCPA.acHandler S cap ist).perCall).add
        (AdaptiveCPA.acHandler S cap ist).finCall).eval n) b n) =
      accept (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n
        fun j => decide (j < ist n + b.toNat)) := by
    intro b
    rw [PolyExpr.eval_add, PolyExpr.eval_mul]
    exact AdaptiveCPA.accept_indGame_acHyb S cap ist A q n B φ (hist n) hφ b
  have hB' : advantage
      (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < ist n))
      (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < ist n + 1)) ≤ ε n := by
    have hb := hεB n
    rw [advantage_eq, hred false, hred true, Bool.toNat_false, Bool.toNat_true,
      Nat.add_zero] at hb
    rw [advantage_eq]
    exact hb
  calc advantage (S.adaptiveIndGame .cpa A (q.eval n) (cap.eval n) false n)
        (S.adaptiveIndGame .cpa A (q.eval n) (cap.eval n) true n) =
      advantage (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < 0))
        (AdaptiveCPA.acHyb S A (q.eval n) (cap.eval n) n fun j => decide (j < cap.eval n)) := by
        rw [AdaptiveCPA.acHyb_lt_zero, AdaptiveCPA.acHyb_lt_cap]
    _ ≤ _ := hgap n
    _ ≤ (cap.eval n : ℝ) * ε n := mul_le_mul_of_nonneg_left hB' (Nat.cast_nonneg _)

end TCSlib.Cryptography.Composability.FixedLengthPKScheme

## ===== TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Games.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hybrid games of the adaptive CPA lift

For a fixed-length public-key scheme `S`, an adversary `A`, a query budget `q` and a challenge cap
`κ`, the hybrid game `acHyb S A q κ n sel` runs `A` against the hybrid oracles `hybImpl κ E sel`
of `AdaptiveCPA.Hybrid`, where `E β mm r` encrypts the message `m_β` of the challenge query `mm`
under the generated public key with the coins `r`. The game is stated on the codec of T2
(`bitCodec` of the polynomial lengths `acDin`, `acDout`), on which the reduction of
`AdaptiveCPA.Handler` runs the adversary.

With the selector `j ↦ [j < i]` the first `i` fresh challenges encrypt the right message: this is
the hybrid `H_i` of the single-to-many argument [PS10, p. 103]. The constant selectors give the
adaptive left-or-right games (`adaptiveIndGame_eq_acHyb`), so `H_0` is the game with `b = false`
and `H_κ` the game with `b = true` (`acHyb_lt_zero`, `acHyb_lt_cap`).

## Main definitions

* `AdaptiveCPA.acEnc`: the encryption of the selected message.
* `AdaptiveCPA.acHyb`: the hybrid game with a selector.

## Main results

* `AdaptiveCPA.indCodec_eq_bitCodec`: the adversary codec is a `bitCodec`.
* `AdaptiveCPA.acDin_eval`, `acDout_eval`: the lengths of T2's codec are the game's.
* `AdaptiveCPA.castImpl_adaptiveIndImpl`: the adaptive CPA oracles, read on T2's codec, are the
  hybrid with the constant selector.
* `AdaptiveCPA.adaptiveIndGame_eq_acHyb`, `acHyb_congr`, `acHyb_lt_zero`, `acHyb_lt_cap`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 171.5 and the single-to-many hybrid argument (book p. 103).
-/

namespace TCSlib.Cryptography.Composability.AdaptiveCPA

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

variable (S : FixedLengthPKScheme)

/-! ### Codecs and lengths -/

/-- **The adversary codec is a bit codec:** `S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1`.

**Proof sketch.** Both are codecs with the same three fields (`indCodec_decodeMove`,
`indCodec_encodeEntry`, `indCodec_timeout` against the `bitCodec` readers). -/
theorem indCodec_eq_bitCodec (n : ℕ) :
    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := by
  have h1 := S.indCodec_decodeMove n
  have h2 := S.indCodec_encodeEntry n
  have h3 := S.indCodec_timeout n
  generalize S.indCodec n = c at h1 h2 h3
  cases c with
  | mk d e t =>
    have hd : d = (bitCodec (S.inLens n) (S.outLens n) 1).decodeMove :=
      funext fun w => (h1 w).trans (bitCodec_decodeMove _ _ _ w).symm
    have he : e = (bitCodec (S.inLens n) (S.outLens n) 1).encodeEntry :=
      funext fun en => (h2 en).trans (bitCodec_encodeEntry _ _ _ en).symm
    have ht : t = (bitCodec (S.inLens n) (S.outLens n) 1).timeout :=
      h3.trans (bitCodec_timeout _ _ _).symm
    rw [hd, he, ht]

/-- The query lengths of T2's codec are the game's: `(acDin S · ).eval n = S.inLens n`. -/
theorem acDin_eval (n : ℕ) : (fun i => (acDin S i).eval n) = S.inLens n := by
  funext i
  match i with
  | 0 => rw [acDin_zero, S.inLens_zero]
  | 1 => rw [acDin_one, PolyExpr.eval_add, S.inLens_one]

/-- The answer lengths of T2's codec are the game's: `(acDout S · ).eval n = S.outLens n`. -/
theorem acDout_eval (n : ℕ) : (fun i => (acDout S i).eval n) = S.outLens n := by
  funext i
  match i with
  | 0 => rw [acDout_zero, PolyExpr.eval_add, PolyExpr.eval_const, S.outLens_zero]
  | 1 => rw [acDout_one, S.outLens_one]

/-! ### Strings of the oracles -/

/-- Reading a bit vector across an equality of widths keeps its string:
`⟦cast h f⟧ = ⟦f⟧` when `a = b`. -/
theorem ofFn_cast {a b : ℕ} (hab : a = b) (h : (Fin a → Bool) = (Fin b → Bool))
    (f : Fin a → Bool) : List.ofFn (cast h f) = List.ofFn f := by
  subst hab
  rfl

/-- The first half of a `2m`-bit query is its first `m` bits:
`⟦(splitHalf y).1⟧ = ⟦y⟧.take m`. -/
theorem ofFn_splitHalf_fst {m : ℕ} (y : Fin (m + m) → Bool) :
    List.ofFn (FixedLengthScheme.splitHalf y).1 = (List.ofFn y).take m := by
  rw [FixedLengthScheme.splitHalf_fst]
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_take]; omega)
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_take, List.getElem_ofFn]
  rfl

/-- The second half of a `2m`-bit query is its last `m` bits:
`⟦(splitHalf y).2⟧ = ⟦y⟧.drop m`. -/
theorem ofFn_splitHalf_snd {m : ℕ} (y : Fin (m + m) → Bool) :
    List.ofFn (FixedLengthScheme.splitHalf y).2 = (List.ofFn y).drop m := by
  rw [FixedLengthScheme.splitHalf_snd]
  refine List.ext_getElem (by simp only [List.length_ofFn, List.length_drop]; omega)
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_drop, List.getElem_ofFn]
  rfl

/-- The all-`false` answer, read at any width, is all-`false`:
`padFin d ⟦zeroBits m⟧ = zeroBits d`. -/
theorem padFin_ofFn_zeroBits (d m : ℕ) : padFin d (List.ofFn (zeroBits m)) = zeroBits d := by
  funext i
  rw [padFin_apply, ofFn_zeroBits, zeroBits_apply]
  by_cases hi : (i : ℕ) < m
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hi), List.getElem_replicate]
  · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; omega)]

/-- The bit of a one-bit output is the head of its string: `⟦f⟧.headD false = f 0`. -/
theorem headD_ofFn_one (f : Fin 1 → Bool) : (List.ofFn f).headD false = f 0 := by
  rw [List.ofFn_succ, List.headD_cons]

/-! ### The hybrid games -/

/-- **The encryption of the selected message:** `E β mm r = padFin (Enc_pk(m_β); r)` for the
challenge query `mm = m₀ ‖ m₁` (`msgOf`). -/
def acEnc (n : ℕ) (pk : List Bool) (β : Bool) (mm : Fin ((acDin S 1).eval n) → Bool)
    (r : S.enc.Coins n) : Fin (S.ctLen.eval n) → Bool :=
  padFin _ (S.enc.runAt n (pairEncode pk (msgOf (S.msgLen.eval n) β (List.ofFn mm))) r)

/-- `acEnc S n pk β mm r = padFin _ (S.enc.runAt n ⟨pk, msgOf m β ⟦mm⟧⟩ r)`. -/
theorem acEnc_eq (n : ℕ) (pk : List Bool) (β : Bool) (mm : Fin ((acDin S 1).eval n) → Bool)
    (r : S.enc.Coins n) :
    acEnc S n pk β mm r =
      padFin _ (S.enc.runAt n (pairEncode pk (msgOf (S.msgLen.eval n) β (List.ofFn mm))) r) :=
  rfl

/-- **The hybrid game with selector `sel`**: sample the key pair and `A`'s coins, run `A` on `pk`
through T2's codec against `hybImpl κ (acEnc S n pk) sel` from the empty history, and output its
bit. -/
noncomputable def acHyb (A : NUPPT) (q κ n : ℕ) (sel : ℕ → Bool) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (hybImpl (outs := fun i => (acDout S i).eval n) κ
      (acEnc S n (pairFstD (S.gen.runAt n [] rg))) sel)
      (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
        ((PolyExpr.const 1).eval n)) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
    fun res => .pure ((List.ofFn res.1).headD false)

/-- The defining equation of `acHyb`: sample `rg` and `r`, let `pk = ⟨S.gen.runAt n [] rg⟩₁`,
simulate `hybImpl κ (acEnc S n pk) sel` from `[]` on `A.toCompOn` (T2's codec) at `pk`, and
return `⟦output⟧.headD false`. -/
theorem acHyb_eq (A : NUPPT) (q κ n : ℕ) (sel : ℕ → Bool) :
    acHyb S A q κ n sel =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (hybImpl (outs := fun i => (acDout S i).eval n) κ
          (acEnc S n (pairFstD (S.gen.runAt n [] rg))) sel)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((PolyExpr.const 1).eval n)) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
        fun res => .pure ((List.ofFn res.1).headD false) :=
  rfl

/-- **Only the selector below the cap matters** (`hybImpl_congr`): if `sel j = sel' j` for every
`j < κ`, then `acHyb S A q κ n sel = acHyb S A q κ n sel'`. -/
theorem acHyb_congr (A : NUPPT) (q κ n : ℕ) {sel sel' : ℕ → Bool}
    (hsel : ∀ j < κ, sel j = sel' j) : acHyb S A q κ n sel = acHyb S A q κ n sel' := by
  rw [acHyb_eq, acHyb_eq]
  congr 1
  funext rg
  congr 1
  funext r
  rw [hybImpl_congr κ _ sel hsel]

/-- The message selected from a challenge query by the game's oracle is `msgOf`: for the query
`x` of T2's codec, the half `b` of `splitHalf (cast (padFin ⟦x⟧))` has the string
`msgOf m b ⟦x⟧`. -/
theorem ofFn_select (n : ℕ) (x : Fin ((acDin S 1).eval n) → Bool) (b : Bool) :
    List.ofFn (if b then (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) (padFin (S.inLens n 1) (List.ofFn x)))).2
      else (FixedLengthScheme.splitHalf
        (cast (S.indSpec_challengeDom n) (padFin (S.inLens n 1) (List.ofFn x)))).1) =
      msgOf (S.msgLen.eval n) b (List.ofFn x) := by
  have hx : List.ofFn (cast (S.indSpec_challengeDom n) (padFin (S.inLens n 1) (List.ofFn x))) =
      List.ofFn x := by
    rw [ofFn_cast (S.inLens_one n), GGMRed.ofFn_padFin_of_length (by
      rw [List.length_ofFn, acDin_one, PolyExpr.eval_add, S.inLens_one])]
  cases b
  · rw [if_neg Bool.false_ne_true, ofFn_splitHalf_fst, hx, msgOf_eq, if_neg Bool.false_ne_true]
  · rw [if_pos rfl, ofFn_splitHalf_snd, hx, msgOf_eq, if_pos rfl]

/-- **The adaptive CPA oracles on T2's codec are a hybrid:** read along the lengths of T2's codec,
`S.adaptiveIndImpl .cpa b n pk sk κ` is `hybImpl κ (acEnc S n pk) (fun _ => b)`.

**Proof sketch.** Oracle by oracle, through the published equations of `AdaptiveSecurity`.
Decryption answers `⊥` whether or not the query was issued (`adaptiveIndImpl_dec_issued`,
`_dec_other`, `indImpl_dec_onSpec`, `decOpen_cpa`). A fresh challenge below the cap encrypts
`m_b` with fresh coins (`adaptiveIndImpl_challenge_encrypt`; the halves of the query are
`msgOf`). At the cap the latest ciphertext is repeated (`_challenge_full`,
`indImpl_challenge_repeat_onSpec`), and an empty history has cap `0` (`_challenge_zero`). Every
width cast keeps the strings (`ofFn_cast`). -/
theorem castImpl_adaptiveIndImpl (b : Bool) (n : ℕ) (pk sk : List Bool) (κ : ℕ) :
    castImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
        (S.adaptiveIndImpl .cpa b n pk sk κ) =
      hybImpl κ (acEnc S n pk) (fun _ => b) := by
  funext i x h
  match i, x with
  | 0, x =>
    rw [castImpl_eq, hybImpl_zero]
    have hdec : S.adaptiveIndImpl .cpa b n pk sk κ 0 (padFin (S.inLens n 0) (List.ofFn x)) h =
        .pure (zeroBits _, h) := by
      by_cases hc : cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x)) ∈ h
      · exact S.adaptiveIndImpl_dec_issued .cpa b n pk sk κ _ h hc
      · rw [S.adaptiveIndImpl_dec_other .cpa b n pk sk κ _ h hc, S.indImpl_dec_onSpec,
          FixedLengthScheme.decOpen_cpa, Bool.false_and, if_neg Bool.false_ne_true,
          OracleComp.pure_bind]
    rw [hdec, OracleComp.pure_bind, padFin_ofFn_zeroBits]
  | 1, x =>
    by_cases hh : h.length < κ
    · rw [castImpl_eq, S.adaptiveIndImpl_challenge_encrypt .cpa b n pk sk κ _ h hh,
        hybImpl_fresh (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
          κ _ _ x h hh, OracleComp.bind_assoc]
      congr 1
      funext r
      dsimp only
      rw [OracleComp.pure_bind, acEnc_eq, ofFn_select, ofFn_cast (S.outLens_one n).symm]
    · cases h with
      | nil =>
        have hκ : κ = 0 := by
          rw [List.length_nil] at hh
          omega
        subst hκ
        rw [castImpl_eq, S.adaptiveIndImpl_challenge_zero, OracleComp.pure_bind,
          hybImpl_full (ins := fun i => (acDin S i).eval n)
          (outs := fun i => (acDout S i).eval n) 0 _ _ x [] le_rfl, List.headD_nil,
          padFin_ofFn_zeroBits,
          padFin_ofFn_zeroBits]
      | cons c t =>
        rw [castImpl_eq, S.adaptiveIndImpl_challenge_full .cpa b n pk sk κ _ (c :: t)
            (Nat.le_of_not_lt hh) c rfl, S.indImpl_challenge_repeat_onSpec, OracleComp.pure_bind,
          OracleComp.pure_bind, hybImpl_full (ins := fun i => (acDin S i).eval n)
          (outs := fun i => (acDout S i).eval n) κ _ _ x (c :: t) (Nat.le_of_not_lt hh),
          List.headD_cons, ofFn_cast (S.outLens_one n).symm]

/-- **The adaptive game is the hybrid game with a constant selector:**
`S.adaptiveIndGame .cpa A q κ b n = acHyb S A q κ n (fun _ => b)`.

**Proof sketch.** Fix the key-generation and adversary coins. The adversary codec is a bit codec
(`indCodec_eq_bitCodec`), its one-bit output is the head of its string (`headD_ofFn_one`), and
the run transports to T2's codec, whose lengths are equal (`simulate_castImpl_toCompOn`), where the
oracles are the hybrid (`castImpl_adaptiveIndImpl`). -/
theorem adaptiveIndGame_eq_acHyb (A : NUPPT) (q κ : ℕ) (b : Bool) (n : ℕ) :
    S.adaptiveIndGame .cpa A q κ b n = acHyb S A q κ n (fun _ => b) := by
  rw [S.adaptiveIndGame_eq, acHyb_eq]
  congr 1
  funext rg
  congr 1
  funext r
  rw [← castImpl_adaptiveIndImpl S b n (pairFstD (S.gen.runAt n [] rg))
    (pairSndD (S.gen.runAt n [] rg)) κ, indCodec_eq_bitCodec]
  have key := simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n)
    (PolyExpr.eval_const 1 n)
    (S.adaptiveIndImpl .cpa b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg))
      κ) A n q (pairFstD (S.gen.runAt n [] rg)) r []
  calc _ = ((simulate (S.adaptiveIndImpl .cpa b n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) κ)
          (A.toCompOn (bitCodec (S.inLens n) (S.outLens n) 1) n q
            (pairFstD (S.gen.runAt n [] rg)) r) []).bind
          (fun p => .pure (List.ofFn p.1, p.2))).bind
          (fun p => .pure (p.1.headD false)) := by
        rw [OracleComp.bind_assoc]
        refine congrArg _ (funext fun p => ?_)
        rw [OracleComp.pure_bind, headD_ofFn_one]
    _ = _ := by
        rw [← key, OracleComp.bind_assoc]
        refine congrArg _ (funext fun p => ?_)
        rw [OracleComp.pure_bind]

/-- **The first hybrid is the game with `b = false`:** with the selector `j ↦ [j < 0]` no fresh
challenge encrypts the right message. -/
theorem acHyb_lt_zero (A : NUPPT) (q κ n : ℕ) :
    acHyb S A q κ n (fun j => decide (j < 0)) = S.adaptiveIndGame .cpa A q κ false n := by
  rw [adaptiveIndGame_eq_acHyb]
  exact acHyb_congr S A q κ n fun j _ => decide_eq_false (Nat.not_lt_zero j)

/-- **The last hybrid is the game with `b = true`:** with the selector `j ↦ [j < κ]` every fresh
challenge below the cap encrypts the right message. -/
theorem acHyb_lt_cap (A : NUPPT) (q κ n : ℕ) :
    acHyb S A q κ n (fun j => decide (j < κ)) = S.adaptiveIndGame .cpa A q κ true n := by
  rw [adaptiveIndGame_eq_acHyb]
  exact acHyb_congr S A q κ n fun j hj => decide_eq_true hj

end TCSlib.Cryptography.Composability.AdaptiveCPA

## ===== TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Handler.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Complexity.ClassNP.PolyTimePrefix

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The handler of the adaptive CPA reduction

The reduction from adaptive multi-challenge CPA security to single-challenge CPA security
[PS10, the single-to-many hybrid argument of p. 103, extended to adaptive challenges] runs the
adversary `A` once, on the public key `pk`. It answers decryption queries with `⊥`, the `j`-th
fresh challenge `⟨m₀, m₁⟩` with an encryption of `m₁` (`j < i⋆`) or `m₀` (`j > i⋆`) under its own
coins, forwards the `i⋆`-th fresh challenge to its own challenge oracle, and repeats the latest
ciphertext once the cap `κ = cap(n)` is reached. This file builds that reduction as a
`Games.InteractiveHandler` (`acHandler`), so that T2 (`Games.exists_interactiveHandlerMachine`)
makes it an oracle machine, and states its answers on the encoded states `acState j c` (the
count `j` of fresh challenges, the latest ciphertext `c` and the advised index `i⋆(n)`).

Its seed is `κ` encryption tapes, read as blocks of `ρ(n)` bits (`acTapes`). Its one outer call
per inner query is the forwarded challenge; its finalization asks nothing and outputs `A`'s bit.

## Main definitions

* `AdaptiveCPA.msgOf`: the message selected from a challenge query.
* `AdaptiveCPA.acDin`, `acDout`, `acStLen`: the oracle lengths and the state length.
* `AdaptiveCPA.acState`: the encoded state.
* `AdaptiveCPA.acTapes`: the seed as `κ` encryption tapes.
* `AdaptiveCPA.acHandler S cap ist`: the handler, with the advised index `ist n`.

## Main results

* `AdaptiveCPA.acHandler_impl_dec`, `_impl_full`, `_impl_eager`, `_impl_forward`: its answers.
* `AdaptiveCPA.acHandler_advInput`, `acHandler_finish`: the adversary's input and the output.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 171.5 and the single-to-many hybrid argument (book p. 103).
-/

namespace TCSlib.Cryptography.Composability.AdaptiveCPA

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Messages, lengths and states -/

/-- The message selected by the bit `β` from the challenge query `l = m₀ ‖ m₁` with `m`-bit
messages: `m₁ = l.drop m` for `β = true`, `m₀ = l.take m` for `β = false`. -/
def msgOf (m : ℕ) (β : Bool) (l : List Bool) : List Bool := if β then l.drop m else l.take m

/-- `msgOf m β l = if β then l.drop m else l.take m`. -/
theorem msgOf_eq (m : ℕ) (β : Bool) (l : List Bool) :
    msgOf m β l = if β then l.drop m else l.take m :=
  rfl

variable (S : FixedLengthPKScheme) (cap : PolyExpr) (ist : ℕ → ℕ)

/-- The query lengths of the two oracles: ciphertexts for `Dec`, two messages for `Challenge`. -/
def acDin : Fin 2 → PolyExpr
  | 0 => S.ctLen
  | 1 => S.msgLen.add S.msgLen

/-- `Dec` queries are ciphertexts: `acDin S 0 = S.ctLen`. -/
theorem acDin_zero : acDin S 0 = S.ctLen := rfl

/-- `Challenge` queries are two messages: `acDin S 1 = S.msgLen + S.msgLen`. -/
theorem acDin_one : acDin S 1 = S.msgLen.add S.msgLen := rfl

/-- The answer lengths: a validity flag and a message for `Dec`, a ciphertext for `Challenge`. -/
def acDout : Fin 2 → PolyExpr
  | 0 => S.msgLen.add (.const 1)
  | 1 => S.ctLen

/-- `Dec` answers a flag and a message: `acDout S 0 = S.msgLen + 1`. -/
theorem acDout_zero : acDout S 0 = S.msgLen.add (.const 1) := rfl

/-- `Challenge` answers a ciphertext: `acDout S 1 = S.ctLen`. -/
theorem acDout_one : acDout S 1 = S.ctLen := rfl

/-- The state length `4·cap + 4 + ctLen`, room for `⟨1^j, ⟨1^{i⋆}, c⟩⟩` with `j, i⋆ ≤ cap`. -/
def acStLen : PolyExpr := (((PolyExpr.const 4).mul cap).add (.const 4)).add S.ctLen

/-- `acStLen S cap = 4·cap + 4 + ctLen`. -/
theorem acStLen_eq : acStLen S cap = (((PolyExpr.const 4).mul cap).add (.const 4)).add S.ctLen :=
  rfl

/-- **The encoded state** after `j` fresh challenges with latest ciphertext `c`, for the advised
index `ist n`: the string `⟨1^j, ⟨1^{ist n}, c⟩⟩`, padded with `false` to the state length. -/
def acState (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) : Fin ((acStLen S cap).eval n) → Bool :=
  padFin _ (pairEncode (List.replicate j true) (pairEncode (List.replicate (ist n) true)
    (List.ofFn c)))

/-- `acState S cap ist n j c = padFin _ ⟨1^j, ⟨1^{ist n}, c⟩⟩`. -/
theorem acState_eq (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) :
    acState S cap ist n j c = padFin _ (pairEncode (List.replicate j true)
      (pairEncode (List.replicate (ist n) true) (List.ofFn c))) :=
  rfl

/-- **The seed as encryption tapes:** `cap(n) · ρ(n)` bits as `cap(n)` blocks of `ρ(n)` bits, each
read as coins of `Enc` (`FunFamily.blocks` and `NUPPT.coinsEquivPoly`). -/
def acTapes (n : ℕ) :
    (Fin ((cap.mul S.enc.coins).eval n) → Bool) ≃ (Fin (cap.eval n) → S.enc.Coins n) :=
  (FunFamily.blocks (cap.eval n) (S.enc.coins.eval n)).trans
    (Equiv.arrowCongr (Equiv.refl _) (NUPPT.coinsEquivPoly rfl n).symm)

/-- `acTapes S cap n ω j = (coinsEquivPoly rfl n).symm (FunFamily.blocks _ _ ω j)`. -/
theorem acTapes_apply (n : ℕ) (ω : Fin ((cap.mul S.enc.coins).eval n) → Bool)
    (j : Fin (cap.eval n)) :
    acTapes S cap n ω j =
      (NUPPT.coinsEquivPoly rfl n).symm (FunFamily.blocks (cap.eval n) (S.enc.coins.eval n) ω j) :=
  rfl

/-- **Tape `j` is the `j`-th block of the seed:**
`⟦acTapes S cap n ω j⟧ = (⟦ω⟧.drop (j·ρ(n))).take ρ(n)`.

**Proof sketch.** The coin equivalence keeps the string (`coinsEquivPoly_symm_ofFn`); position `k`
of block `j` is position `k + ρ·j` of `ω` (`FunFamily.blocks_apply`), which is position `k` of the
dropped and truncated list. -/
theorem ofFn_acTapes (n : ℕ) (ω : Fin ((cap.mul S.enc.coins).eval n) → Bool)
    (j : Fin (cap.eval n)) :
    List.ofFn (acTapes S cap n ω j) =
      ((List.ofFn ω).drop (j * S.enc.coins.eval n)).take (S.enc.coins.eval n) := by
  rw [acTapes, Equiv.trans_apply, Equiv.arrowCongr_apply, Function.comp_apply, Function.comp_apply,
    Equiv.refl_symm, Equiv.refl_apply, NUPPT.coinsEquivPoly_symm_ofFn]
  have hj := j.isLt
  have hle : (j : ℕ) * S.enc.coins.eval n + S.enc.coins.eval n ≤
      cap.eval n * S.enc.coins.eval n := by
    have := Nat.mul_le_mul_right (S.enc.coins.eval n) (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at this
    exact this
  refine List.ext_getElem ?_ fun k h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop, PolyExpr.eval_mul]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine (FunFamily.blocks_apply _ _ ω j ⟨k, _⟩).trans ?_
    congr 1
    refine Fin.ext ?_
    rw [finProdFinEquiv_apply_val]
    show k + S.enc.coins.eval n * j = j * S.enc.coins.eval n + k
    rw [Nat.mul_comm]
    omega

/-! ### Strings -/

/-- `⟦padFin k a⟧ = padL k a`, the first `k` bits of `a ++ 0^k` (`ofFn_padFin_eq_take`). -/
private theorem ofFn_padFin_eq_padL (k : ℕ) (a : List Bool) :
    List.ofFn (padFin k a) = EnsembleLemmas.padL k a := by
  rw [EnsembleLemmas.padL_eq, ofFn_padFin_eq_take]

/-- The fields of an encoded state. -/
private theorem fields_acState (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) (hj : j ≤ cap.eval n)
    (hi : ist n ≤ cap.eval n) :
    pairFstD (List.ofFn (acState S cap ist n j c)) = List.replicate j true ∧
      pairFstD (pairSndD (List.ofFn (acState S cap ist n j c))) =
        List.replicate (ist n) true ∧
      (pairSndD (pairSndD (List.ofFn (acState S cap ist n j c)))).take (S.ctLen.eval n) =
        List.ofFn c := by
  have hlen : (pairEncode (List.replicate j true) (pairEncode (List.replicate (ist n) true)
      (List.ofFn c))).length ≤ (acStLen S cap).eval n := by
    simp only [length_pairEncode, List.length_replicate, List.length_ofFn, acStLen_eq,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  rw [acState_eq, Collection.ofFn_padFin_of_le hlen, ← GGMRed.pairEncode_append_right,
    ← GGMRed.pairEncode_append_right]
  refine ⟨by rw [pairFstD_pairEncode], by rw [pairSndD_pairEncode, pairFstD_pairEncode], ?_⟩
  rw [pairSndD_pairEncode, pairSndD_pairEncode]
  exact List.take_left' List.length_ofFn

/-! ### The round function -/

/-- The parameter `1^n` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
private def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
/-- The reduction input `z` (the public key). -/
private def rZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))
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
/-- The advised index `1^{i⋆}` of the state. -/
private def rIst (w : List Bool) : List Bool := pairFstD (pairSndD (rS w))
/-- The latest ciphertext of the state. -/
private def rLat (w : List Bool) : List Bool :=
  (pairSndD (pairSndD (rS w))).take (S.ctLen.eval (rU w).length)
/-- The outer answer recorded in the log `⟨⟨1, ⟨x, y⟩⟩, []⟩`. -/
private def rFwd (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rL w)))
/-- The new state `⟨1^{j+1}, ⟨1^{i⋆}, y⟩⟩`, padded. -/
private def rNew (w y : List Bool) : List Bool :=
  EnsembleLemmas.padL ((acStLen S cap).eval (rU w).length)
    (pairEncode (true :: rCnt w) (pairEncode (rIst w) y))
/-- The selected message: `m₁` below the advised index, `m₀` above it. -/
private def rMsg (w : List Bool) : List Bool :=
  if decide ((rCnt w).length < (rIst w).length) then (rX w).drop (S.msgLen.eval (rU w).length)
  else (rX w).take (S.msgLen.eval (rU w).length)
/-- Tape `j` of the seed. -/
private def rTape (w : List Bool) : List Bool :=
  ((rW w).drop ((rCnt w).length * S.enc.coins.eval (rU w).length)).take
    (S.enc.coins.eval (rU w).length)
/-- The handler's own encryption of the selected message with tape `j`, padded. -/
private def rEnc (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (rU w).length)
    (S.enc.output (pairEncode (pairEncode (pairEncode (rU w) (pairEncode (rZ w) (rMsg S w))) [])
      (rTape S w)))

/-- **One round of the handler.** A decryption query is answered `0^{m+1}`, keeping the state. A
challenge at the cap repeats the latest ciphertext. The fresh challenge `j = i⋆` is forwarded
to the outer challenge oracle and answered with the outer answer. Any other fresh challenge is
answered with the handler's own encryption. A fresh challenge records its answer and counts. -/
private def acRun (w : List Bool) : List Bool :=
  if (rI w).headD false then
    if decide (cap.eval (rU w).length ≤ (rCnt w).length) then pairEncode [true] (rLat S w ++ rS w)
    else if decide ((rCnt w).length = (rIst w).length) then
      if decide (rL w = []) then pairEncode [false] (pairEncode [true] (rX w))
      else pairEncode [true] (rFwd w ++ rNew S cap w (rFwd w))
    else pairEncode [true] (rEnc S w ++ rNew S cap w (rEnc S w))
  else pairEncode [true] (List.replicate ((S.msgLen.add (.const 1)).eval (rU w).length) false ++
    rS w)

/-- The round function is polynomial-time. -/
private theorem polyTimeComputable_acRun : PolyTimeComputable (acRun S cap) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hU : PolyTimeComputable rU := hF.comp hF
  have hZ : PolyTimeComputable rZ := hF.comp (hD.comp hF)
  have hW : PolyTimeComputable rW := hD.comp (hD.comp hF)
  have hS : PolyTimeComputable rS := hF.comp hD
  have hI : PolyTimeComputable rI := hF.comp (hF.comp (hD.comp hD))
  have hX : PolyTimeComputable rX := hD.comp (hF.comp (hD.comp hD))
  have hL : PolyTimeComputable rL := hD.comp (hD.comp hD)
  have hCnt : PolyTimeComputable rCnt := hF.comp hS
  have hIst : PolyTimeComputable rIst := hF.comp (hD.comp hS)
  have hLat : PolyTimeComputable (rLat S) :=
    ((polyTimeComputable_pairTakePoly S.ctLen).comp (hU.pairEncode (hD.comp (hD.comp hS)))).congr
      fun w => by simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hFwd : PolyTimeComputable rFwd := hD.comp (hD.comp (hF.comp hL))
  have hNew : ∀ {y : List Bool → List Bool}, PolyTimeComputable y →
      PolyTimeComputable fun w => rNew S cap w (y w) := fun hy =>
    EnsembleLemmas.polyTimeComputable_padL (acStLen S cap) hU
      (((polyTimeComputable_const [true]).append hCnt).pairEncode (hIst.pairEncode hy))
  have hLt : PolyTimeComputable fun w => [decide ((rCnt w).length < (rIst w).length)] :=
    (polyTimeComputable_not (polyTimeComputable_lenLe.comp (hCnt.pairEncode hIst))).congr
      fun w => by
        simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.cons.injEq, and_true]
        by_cases h : (rCnt w).length < (rIst w).length
        · rw [decide_eq_true h, decide_eq_false (by omega)]
          rfl
        · rw [decide_eq_false h, decide_eq_true (by omega)]
          rfl
  have hMsg : PolyTimeComputable (rMsg S) :=
    polyTimeComputable_ite hLt
      (((polyTimeComputable_pairDropPoly S.msgLen).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
      (((polyTimeComputable_pairTakePoly S.msgLen).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((rCnt w).length * S.enc.coins.eval (rU w).length) true :=
    (OneWay.polyTimeComputable_unaryMulPair.comp
      (hCnt.pairEncode ((polyTimeComputable_unaryPoly S.enc.coins).comp hU))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  have hDrop : PolyTimeComputable fun w =>
      (rW w).drop ((rCnt w).length * S.enc.coins.eval (rU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
  have hTape : PolyTimeComputable (rTape S) :=
    ((polyTimeComputable_pairTakePoly S.enc.coins).comp (hU.pairEncode hDrop)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hEnc : PolyTimeComputable (rEnc S) :=
    EnsembleLemmas.polyTimeComputable_padL S.ctLen hU (S.enc.polyTimeComputable_output.comp
      (((hU.pairEncode (hZ.pairEncode hMsg)).pairEncode (polyTimeComputable_const [])).pairEncode
        hTape))
  have hRet : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [true] (f w) := fun hf =>
    (polyTimeComputable_const [true]).pairEncode hf
  have cFull : PolyTimeComputable fun w =>
      [decide (cap.eval (rU w).length ≤ (rCnt w).length)] :=
    (polyTimeComputable_lenLe.comp (hCnt.pairEncode
      ((polyTimeComputable_unaryPoly cap).comp hU))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  have cEq : PolyTimeComputable fun w => [decide ((rCnt w).length = (rIst w).length)] :=
    EffFill.lenEq_poly hCnt hIst
  have cNil : PolyTimeComputable fun w => [decide (rL w = [])] := polyTimeComputable_isNil.comp hL
  have hZeros : PolyTimeComputable fun w =>
      List.replicate ((S.msgLen.add (.const 1)).eval (rU w).length) false :=
    EnsembleLemmas.polyTimeComputable_zeros _ hU
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hI)
    (polyTimeComputable_ite cFull (hRet (hLat.append hS))
      (polyTimeComputable_ite cEq
        (polyTimeComputable_ite cNil
          ((polyTimeComputable_const [false]).pairEncode
            ((polyTimeComputable_const [true]).pairEncode hX))
          (hRet (hFwd.append (hNew hFwd))))
        (hRet (hEnc.append (hNew hEnc)))))
    (hRet (hZeros.append hS))

/-- The finalization's round: output `A`'s bit, `⟨[true], a⟩` on `⟨ctx, ⟨s, ⟨a, L⟩⟩⟩`. -/
private def acFin (w : List Bool) : List Bool :=
  pairEncode [true] (pairFstD (pairSndD (pairSndD w)))

/-- The finalization's round is polynomial-time. -/
private theorem polyTimeComputable_acFin : PolyTimeComputable acFin :=
  (polyTimeComputable_const [true]).pairEncode
    (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-! ### The handler -/

/-- **The handler of the adaptive CPA reduction** for the scheme `S`, the cap `cap` and the advised
index `ist`: state `acState j c` (initially `j = 0`, `c = 0`), seed `cap · ρ` bits (the tapes
`acTapes`), one outer call per inner query, the adversary run on the reduction input, and the
finalization outputting the adversary's bit without outer queries. -/
def acHandler : InteractiveHandler 2 (acDin S) (acDout S) 2 (acDin S) (acDout S) where
  stateLen := acStLen S cap
  seedLen := cap.mul S.enc.coins
  perCall := .const 1
  init n := acState S cap ist n 0 (zeroBits _)
  run := acRun S cap
  poly := polyTimeComputable_acRun S cap
  advIn ctx := pairFstD (pairSndD ctx)
  advIn_poly := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  outLen := .const 1
  finCall := .const 0
  finRun := acFin
  finRun_poly := polyTimeComputable_acFin

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init advIn outLen finCall]
  acHandler

/-- The handler's state `acState S cap ist n j c`, at the handler's state type. -/
def acHState (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) :
    Fin ((acHandler S cap ist).stateLen.eval n) → Bool :=
  acState S cap ist n j c

/-- `acHState S cap ist n j c = acState S cap ist n j c`. -/
theorem acHState_eq (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) :
    acHState S cap ist n j c = acState S cap ist n j c :=
  rfl

/-- The handler starts from no fresh challenge and the all-`false` ciphertext:
`(acHandler S cap ist).init n = acHState S cap ist n 0 0`. -/
theorem acHandler_init_eq (n : ℕ) :
    (acHandler S cap ist).init n = acHState S cap ist n 0 (zeroBits _) :=
  rfl

/-- The handler's seed as encryption tapes (`acTapes`). -/
def acSeedTapes (n : ℕ) :
    (Fin ((acHandler S cap ist).seedLen.eval n) → Bool) ≃ (Fin (cap.eval n) → S.enc.Coins n) :=
  acTapes S cap n

/-- `acSeedTapes S cap ist n = acTapes S cap n`. -/
theorem acSeedTapes_eq (n : ℕ) : acSeedTapes S cap ist n = acTapes S cap n :=
  rfl

/-- Tape `j` of the handler's seed is its `j`-th block (`ofFn_acTapes`). -/
private theorem ofFn_acSeedTapes (n : ℕ) (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)
    (j : Fin (cap.eval n)) :
    List.ofFn (acSeedTapes S cap ist n ω j) =
      ((List.ofFn ω).drop (j * S.enc.coins.eval n)).take (S.enc.coins.eval n) :=
  ofFn_acTapes S cap n ω j

/-- The adversary runs on the reduction input: `(acHandler S cap ist).advInput n z ω = z`. -/
theorem acHandler_advInput (n : ℕ) (z : List Bool)
    (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool) :
    (acHandler S cap ist).advInput n z ω = z := by
  rw [InteractiveHandler.advInput_eq, acHandler_advIn, seedIn_eq, pairSndD_pairEncode,
    pairFstD_pairEncode]

/-- The finalization outputs the adversary's bit and asks nothing:
`(acHandler S cap ist).finish n z ω s a = pure (padFin _ ⟦a⟧)`, the bit `a` read at the output
width. -/
theorem acHandler_finish (n : ℕ) (z : List Bool)
    (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)
    (s : Fin ((acHandler S cap ist).stateLen.eval n) → Bool)
    (a : Fin ((PolyExpr.const 1).eval n) → Bool) :
    (acHandler S cap ist).finish n z ω s a =
      .pure (padFin ((acHandler S cap ist).outLen.eval n) (List.ofFn a)) := by
  rw [InteractiveHandler.finish_eq]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ (acFin _) = _
  rw [acFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
  have hw : List.ofFn (padFin ((acHandler S cap ist).outLen.eval n) (List.ofFn a)) = List.ofFn a :=
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, acHandler_outLen])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### Answers of the handler -/

section Answers

variable (n : ℕ) (z : List Bool) (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)

/-- A call whose first round returns `y ‖ s'` is answered `y` with new state `s'`. -/
private theorem impl_of_ret {i : Fin 2} (x : Fin ((acDin S i).eval n) → Bool)
    (s : Fin ((acStLen S cap).eval n) → Bool) (y : Fin ((acDout S i).eval n) → Bool)
    (s' : Fin ((acStLen S cap).eval n) → Bool)
    (h : acRun S cap (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [true] (List.ofFn y ++ List.ofFn s')) :
    (acHandler S cap ist).impl n z ω i x s = .pure (y, s') := by
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, acHandler_perCall,
    PolyExpr.eval_const]
  rw [buildComp_succ_of_ret (a := Fin.append y s') (by
    show decodeBitMove _ _ _ (acRun S cap _) = _
    rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
    exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind]
  congr 2
  · funext j
    exact Fin.append_left y s' j
  · funext j
    exact Fin.append_right y s' j

/-- The index word of a challenge query is `[true]`. -/
private theorem replicate_one : List.replicate ((1 : Fin 2) : ℕ) true = [true] := rfl

/-- The round input of a call, field by field. -/
private theorem fields_input {i : Fin 2} (x : List Bool) (L : List Bool) (j : ℕ)
    (c : Fin (S.ctLen.eval n) → Bool) (hj : j ≤ cap.eval n) (hi : ist n ≤ cap.eval n) :
    let w := InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (acState S cap ist n j c)) i x L
    rU w = List.replicate n true ∧ rZ w = z ∧ rW w = List.ofFn ω ∧
      rS w = List.ofFn (acState S cap ist n j c) ∧ rI w = List.replicate i true ∧ rX w = x ∧
      rL w = L ∧ rCnt w = List.replicate j true ∧ rIst w = List.replicate (ist n) true ∧
      rLat S w = List.ofFn c := by
  obtain ⟨h₁, h₂, h₃⟩ := fields_acState S cap ist n j c hj hi
  simp only [InteractiveHandler.input_eq, rU, rZ, rW, rS, rI, rX, rL, rCnt, rIst, rLat,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, h₁, h₂, h₃, and_self]

/-- **Decryption is refused:** `(acHandler S cap ist).impl n z ω 0 x s = pure (0, s)`. -/
theorem acHandler_impl_dec (x : Fin ((acDin S 0).eval n) → Bool)
    (s : Fin ((acHandler S cap ist).stateLen.eval n) → Bool) :
    (acHandler S cap ist).impl n z ω 0 x s = .pure (zeroBits _, s) := by
  refine impl_of_ret S cap ist n z ω x s _ _ ?_
  have hI : rI (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) (0 : Fin 2) (List.ofFn x)
      []) =
      [] := by
    simp only [InteractiveHandler.input_eq, rI, pairFstD_pairEncode, pairSndD_pairEncode]
    rfl
  have hU : rU (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) (0 : Fin 2) (List.ofFn x)
      []) =
      List.replicate n true := by
    simp only [InteractiveHandler.input_eq, rU, pairFstD_pairEncode]
  have hS : rS (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) (0 : Fin 2) (List.ofFn x)
      []) =
      List.ofFn s := by
    simp only [InteractiveHandler.input_eq, rS, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [acRun, hI, List.headD_nil, if_neg Bool.false_ne_true, hU, hS, List.length_replicate,
    ofFn_zeroBits, acDout_zero]

/-- **At the cap, the latest ciphertext is repeated:** from the state `acState κ c` with
`κ = cap(n)`, a challenge is answered `c` and the state is kept. -/
theorem acHandler_impl_full (x : Fin ((acDin S 1).eval n) → Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (hi : ist n ≤ cap.eval n) :
    (acHandler S cap ist).impl n z ω 1 x (acHState S cap ist n (cap.eval n) c) =
      .pure (padFin ((acDout S 1).eval n) (List.ofFn c), acHState S cap ist n (cap.eval n) c) := by
  rw [acHState_eq]
  refine impl_of_ret S cap ist n z ω x _ _ _ ?_
  obtain ⟨hU, -, -, hS, hI, -, -, hCnt, -, hLat⟩ :=
    fields_input S cap ist n z ω (i := 1) (List.ofFn x) [] (cap.eval n) c le_rfl hi
  have hh : ([true].headD false = true) := rfl
  have hc : decide (cap.eval n ≤ cap.eval n) = true := decide_eq_true le_rfl
  rw [acRun, hI, replicate_one, hU, hCnt, hS, hLat, List.length_replicate, List.length_replicate,
    if_pos hh, if_pos hc, GGMRed.ofFn_padFin_of_length (List.length_ofFn)]

/-- **A fresh challenge other than the advised one is encrypted by the handler:** from the state
`acState j c` with `j < cap(n)` and `j ≠ i⋆(n)`, the challenge `x` is answered with
`c' = padFin (Enc_z(m_{[j < i⋆]}); tape j)`, recorded in the state `acState (j + 1) c'`. -/
theorem acHandler_impl_eager (x : Fin ((acDin S 1).eval n) → Bool) (j : ℕ)
    (c : Fin (S.ctLen.eval n) → Bool) (hj : j < cap.eval n) (hne : j ≠ ist n)
    (hi : ist n ≤ cap.eval n) :
    (acHandler S cap ist).impl n z ω 1 x (acHState S cap ist n j c) =
      .pure (padFin ((acDout S 1).eval n) (List.ofFn (padFin (S.ctLen.eval n) (S.enc.runAt n
          (pairEncode z (msgOf (S.msgLen.eval n) (decide (j < ist n)) (List.ofFn x)))
          (acSeedTapes S cap ist n ω ⟨j, hj⟩)))),
        acHState S cap ist n (j + 1) (padFin (S.ctLen.eval n) (S.enc.runAt n
          (pairEncode z (msgOf (S.msgLen.eval n) (decide (j < ist n)) (List.ofFn x)))
          (acSeedTapes S cap ist n ω ⟨j, hj⟩)))) := by
  rw [acHState_eq, acHState_eq]
  obtain ⟨c', hc'⟩ : ∃ c' : Fin (S.ctLen.eval n) → Bool, c' = padFin (S.ctLen.eval n)
      (S.enc.runAt n (pairEncode z (msgOf (S.msgLen.eval n) (decide (j < ist n)) (List.ofFn x)))
        (acSeedTapes S cap ist n ω ⟨j, hj⟩)) := ⟨_, rfl⟩
  rw [← hc']
  refine impl_of_ret S cap ist n z ω x _ _ _ ?_
  obtain ⟨hU, hZ, hW, hS, hI, hX, -, hCnt, hIst, -⟩ :=
    fields_input S cap ist n z ω (i := 1) (List.ofFn x) [] j c hj.le hi
  have hEnc : rEnc S (InteractiveHandler.input n z (List.ofFn ω)
      (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x) []) = List.ofFn c' := by
    rw [hc', ofFn_padFin_eq_padL, rEnc, hU, List.length_replicate, NUPPT.Uniform.runAt_eq
      S.enc_uniform, NUPPT.advInput_eq, ofFn_acSeedTapes, rTape, rMsg, hZ, hW, hCnt, hIst, hU, hX,
      List.length_replicate, List.length_replicate, List.length_replicate, msgOf_eq]
  have hNew : rNew S cap (InteractiveHandler.input n z (List.ofFn ω)
      (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x) []) (List.ofFn c') =
      List.ofFn (acState S cap ist n (j + 1) c') := by
    rw [rNew, hU, hCnt, hIst, List.length_replicate, acState_eq, ofFn_padFin_eq_padL,
      List.replicate_succ]
  have hh : ([true].headD false = true) := rfl
  have hc1 : ¬ (decide (cap.eval n ≤ j) = true) := by rw [decide_eq_true_eq]; omega
  have hc2 : ¬ (decide (j = ist n) = true) := by rw [decide_eq_true_eq]; exact hne
  rw [acRun, hI, replicate_one, hU, hCnt, hIst, hEnc, hNew, List.length_replicate,
    List.length_replicate, List.length_replicate, if_pos hh, if_neg hc1, if_neg hc2,
    GGMRed.ofFn_padFin_of_length (List.length_ofFn)]

/-- **The advised fresh challenge is forwarded:** from the state `acState j c` with
`j = i⋆(n) < cap(n)`, the challenge `x` is asked to the outer challenge oracle, and its answer `y`
is returned and recorded in the state `acState (j + 1) y`. -/
theorem acHandler_impl_forward (x : Fin ((acDin S 1).eval n) → Bool) (j : ℕ)
    (c : Fin (S.ctLen.eval n) → Bool) (hj : j < cap.eval n) (heq : j = ist n) :
    (acHandler S cap ist).impl n z ω 1 x (acHState S cap ist n j c) =
      .query 1 x fun y =>
        .pure (y, acHState S cap ist n (j + 1) (padFin (S.ctLen.eval n) (List.ofFn y))) := by
  simp only [acHState_eq]
  have hi : ist n ≤ cap.eval n := heq ▸ hj.le
  have hlen : ∀ m : ℕ, (List.replicate m true).length = m := fun m => List.length_replicate
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, acHandler_perCall,
    PolyExpr.eval_const]
  rw [buildComp_succ_of_query (i := 1) (x := x) (by
    show decodeBitMove _ _ _ (acRun S cap _) = _
    obtain ⟨hU, -, -, -, hI, hX, hL, hCnt, hIst, -⟩ :=
      fields_input S cap ist n z ω (i := 1) (List.ofFn x)
        ((bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog [])
        j c hj.le hi
    have hh : ([true].headD false = true) := rfl
    have hc1 : ¬ (decide (cap.eval n ≤ j) = true) := by rw [decide_eq_true_eq]; omega
    have hc2 : decide (j = ist n) = true := decide_eq_true heq
    have hc3 : decide (([] : List Bool) = []) = true := decide_eq_true rfl
    rw [acRun, hI, replicate_one, hU, hCnt, hIst, hL, hX, MachineCodec.encodeLog_nil, hlen, hlen,
      hlen, if_pos hh, if_neg hc1, if_pos hc2, if_pos hc3, ← replicate_one]
    exact decodeBitMove_query (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) _ 1 x),
    OracleComp.query_bind]
  congr 1
  funext y
  obtain ⟨s', hs'⟩ : ∃ s' : Fin ((acStLen S cap).eval n) → Bool,
      s' = acState S cap ist n (j + 1) (padFin (S.ctLen.eval n) (List.ofFn y)) := ⟨_, rfl⟩
  rw [← hs']
  rw [buildComp_zero_of_ret (a := Fin.append y s') (by
    show decodeBitMove _ _ _ (acRun S cap _) = _
    obtain ⟨hU, -, -, -, hI, -, hL, hCnt, hIst, -⟩ :=
      fields_input S cap ist n z ω (i := 1) (List.ofFn x)
        ((bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog
          ([] ++ [⟨1, x, y⟩])) j c hj.le hi
    have hlog : (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog
        ([] ++ [⟨1, x, y⟩]) = pairEncode (pairEncode [true] (pairEncode (List.ofFn x)
          (List.ofFn y))) [] := by
      rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
        bitCodec_encodeEntry]
      rfl
    have hNew : rNew S cap (InteractiveHandler.input n z (List.ofFn ω)
        (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x)
        ((bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog
          ([] ++ [⟨1, x, y⟩]))) (List.ofFn y) = List.ofFn s' := by
      rw [rNew, hU, hCnt, hIst, List.length_replicate, hs', acState_eq, ofFn_padFin_eq_padL,
        List.replicate_succ, GGMRed.ofFn_padFin_of_length (List.length_ofFn)]
    have hFwd : rFwd (InteractiveHandler.input n z (List.ofFn ω)
        (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x)
        ((bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog
          ([] ++ [⟨1, x, y⟩]))) = List.ofFn y := by
      rw [rFwd, hL, hlog, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
    have hh : ([true].headD false = true) := rfl
    have hc1 : ¬ (decide (cap.eval n ≤ j) = true) := by rw [decide_eq_true_eq]; omega
    have hc2 : decide (j = ist n) = true := decide_eq_true heq
    have hc3 : ¬ (decide (pairEncode (pairEncode [true] (pairEncode (List.ofFn x) (List.ofFn y)))
        [] = []) = true) := by
      rw [decide_eq_true_eq]
      exact pairEncode_ne_nil _ _
    rw [acRun, hI, replicate_one, hU, hCnt, hIst, hFwd, hNew, hL, hlog, hlen, hlen, hlen,
      if_pos hh, if_neg hc1, if_pos hc2, if_neg hc3, ← List.ofFn_fin_append]
    exact decodeBitMove_ret _ _ _ _)]
  rw [OracleComp.pure_bind]
  congr 2
  · funext k
    exact Fin.append_left y s' k
  · funext k
    exact Fin.append_right y s' k

end Answers

end TCSlib.Cryptography.Composability.AdaptiveCPA

## ===== TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Hybrid.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hybrid challenge oracles under CPA

The single-to-many hybrid argument of [PS10, p. 103], extended to adaptive challenges, compares
experiments in which the `j`-th fresh challenge `⟨m₀, m₁⟩` is answered by an encryption of
`m_{sel j}` for a selector `sel : ℕ → Bool`. This file studies those oracles generically, on
bit-string oracles of arbitrary lengths (`bitSpec ins outs`), with the encryption an arbitrary
function `E` of the selected side, the query and the coins. Under CPA the decryption oracle
answers all-`false`.

* `hybImpl κ E sel` samples fresh coins for each of the first `κ` fresh challenges and records
  the ciphertexts in a history; once the cap `κ` is reached it repeats the latest ciphertext
  (all-`false` for an empty history).
* `tapeImpl κ E sel T kst` answers the `j`-th fresh challenge with the coins `T j` given in
  advance, except the `kst`-th, for which it samples coins. Drawing `T` uniformly gives the
  distribution of `hybImpl` (`expect_tapeImpl`); the proof resamples one coordinate at a time
  (`expect_sample_update`), using that the run from a history of length `j + 1` ignores the
  coins `T j` (`simulate_tapeImpl_congr`).

Two generic tools complete the file: `castImpl` transports an implementation along equal
length functions (`simulate_castImpl_toCompOn`), and `simulate_eq_of_abs` relates two
implementations through an abstraction of their states.

## Main definitions

* `AdaptiveCPA.castImpl`: an implementation read along equal length functions.
* `AdaptiveCPA.hybImpl`, `AdaptiveCPA.tapeImpl`: the hybrid challenge oracles.
* `AdaptiveCPA.extTape`: a finite family of coins, extended to every index.

## Main results

* `AdaptiveCPA.simulate_castImpl_toCompOn`: transport of a machine's run between two codecs.
* `AdaptiveCPA.simulate_eq_of_abs`: simulation through a state abstraction.
* `AdaptiveCPA.hybImpl_congr`: only the selector's values below the cap matter.
* `AdaptiveCPA.expect_sample_update`: resampling one coordinate of a uniform tuple.
* `AdaptiveCPA.expect_tapeImpl`: coins given in advance have the lazy distribution.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  the single-to-many hybrid argument (book p. 103) and Definition 171.5.
-/

namespace TCSlib.Cryptography.Composability.AdaptiveCPA

open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

/-! ### Transport along equal lengths -/

section Transport

variable {k : ℕ} {σ : Type}

/-- **An implementation read along length functions:** answer the query `x` to oracle `i` of
`bitSpec ins outs` by asking `O` the query `padFin (ins' i) ⟦x⟧` and reading its answer `y` as
`padFin (outs i) ⟦y⟧`. When `ins = ins'` and `outs = outs'` this is `O` itself
(`castImpl_self`). -/
def castImpl {ins ins' outs outs' : Fin k → ℕ} (O : QueryImpl (bitSpec ins' outs') σ unifSpec) :
    QueryImpl (bitSpec ins outs) σ unifSpec :=
  fun i x s => (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
    .pure (padFin (outs i) (List.ofFn p.1), p.2)

/-- The defining equation of `castImpl`: `castImpl O i x s =
(O i (padFin (ins' i) ⟦x⟧) s).bind fun p => pure (padFin (outs i) ⟦p.1⟧, p.2)`. -/
theorem castImpl_eq {ins ins' outs outs' : Fin k → ℕ}
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (i : Fin k) (x : Fin (ins i) → Bool)
    (s : σ) :
    castImpl (ins := ins) (outs := outs) O i x s =
      (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
        .pure (padFin (outs i) (List.ofFn p.1), p.2) :=
  rfl

/-- Read along the same lengths, an implementation is unchanged: `castImpl O = O`. -/
theorem castImpl_self {ins outs : Fin k → ℕ} (O : QueryImpl (bitSpec ins outs) σ unifSpec) :
    castImpl (ins := ins) (outs := outs) O = O := by
  funext i x s
  rw [castImpl_eq, padFin_ofFn]
  simp only [padFin_ofFn]
  exact OracleComp.bind_pure _

/-- **Transport of a machine's run:** if `ins = ins'`, `outs = outs'` and `d = d'`, simulating
`castImpl O` on the run of `M` through `bitCodec ins outs d` gives, with outputs read as lists,
the simulation of `O` on the run of `M` through `bitCodec ins' outs' d'`.

**Proof sketch.** Substitute the equalities; then `castImpl O = O` (`castImpl_self`). -/
theorem simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) :
    (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) =
      (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) := by
  subst hi ho hd
  rw [castImpl_self]

/-- **Transport of a machine's run, in expectation:** for every function `G` of the output (read
as a list) and the final state, `simulate_castImpl_toCompOn` in the form
`𝔼[G (⟦p.1⟧, p.2)]` over the two simulations. -/
theorem expect_simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) (G : List Bool × σ → ℝ) :
    expect (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s) (fun p => G (List.ofFn p.1, p.2)) =
      expect (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) := by
  have h := congrArg (fun c => expect c G) (simulate_castImpl_toCompOn hi ho hd O M n q x r s)
  simp only [expect_bind, expect_pure] at h
  exact h

end Transport

/-! ### Simulation through a state abstraction -/

/-- **Simulation through an abstraction of the state:** if every call of `impl₁` from the
abstract state `f s` is the call of `impl₂` from `s` with its new state abstracted, the same holds
for whole simulations: `simulate impl₁ c (f s) =
(simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.

**Proof sketch.** Induction on `c`; at a query, rewrite the call by the hypothesis and use the
induction hypothesis on each continuation after associativity. -/
theorem simulate_eq_of_abs {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
    (f : σ₂ → σ₁) (h : ∀ i x s, impl₁ i x (f s) = (impl₂ i x s).bind fun p => .pure (p.1, f p.2))
    (c : OracleComp spec α) (s : σ₂) :
    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
  induction c generalizing s with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    rw [simulate_query, simulate_query, h, OracleComp.bind_assoc, OracleComp.bind_assoc]
    congr 1
    funext p
    rw [OracleComp.pure_bind]
    exact ih p.1 p.2

/-! ### The hybrid oracles -/

section Hybrid

variable {ins outs : Fin 2 → ℕ} {L : ℕ} {C : Type} [Fintype C] [Nonempty C]

/-- **The `sel`-hybrid of the adaptive CPA oracles** with cap `κ` and encryption `E`, on the
history `h` of issued ciphertexts:
- oracle `0` (decryption) answers all-`false`;
- oracle `1` (challenge) on `mm`, below the cap (`|h| < κ`), samples coins `r`, answers the
  ciphertext `c = E (sel |h|) mm r` (read at width `outs 1`) and records it, `h ↦ c :: h`;
- at the cap it repeats the latest ciphertext `h.headD 0`, all-`false` for `h = []`. -/
noncomputable def hybImpl (κ : ℕ) (E : Bool → (Fin (ins 1) → Bool) → C → (Fin L → Bool))
    (sel : ℕ → Bool) : QueryImpl (bitSpec ins outs) (List (Fin L → Bool)) unifSpec
  | 0, _, h => .pure (zeroBits _, h)
  | 1, mm, h =>
    if h.length < κ then
      (ProbComp.sample C).bind fun r =>
        .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm r)), E (sel h.length) mm r :: h)
    else .pure (padFin (outs 1) (List.ofFn (h.headD (zeroBits L))), h)

variable (κ : ℕ) (E : Bool → (Fin (ins 1) → Bool) → C → (Fin L → Bool)) (sel : ℕ → Bool)

/-- Decryption answers all-`false` and keeps the history:
`hybImpl κ E sel 0 x h = pure (0, h)`. -/
theorem hybImpl_zero (x : Fin (ins 0) → Bool) (h : List (Fin L → Bool)) :
    hybImpl (outs := outs) κ E sel 0 x h = .pure (zeroBits _, h) :=
  rfl

/-- A challenge below the cap samples coins `r` and records `c = E (sel |h|) mm r`:
`hybImpl κ E sel 1 mm h = (sample C).bind fun r => pure (padFin (outs 1) ⟦c⟧, c :: h)`. -/
theorem hybImpl_fresh (mm : Fin (ins 1) → Bool) (h : List (Fin L → Bool)) (hh : h.length < κ) :
    hybImpl (outs := outs) κ E sel 1 mm h =
      (ProbComp.sample C).bind fun r =>
        .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm r)),
          E (sel h.length) mm r :: h) := by
  rw [hybImpl, if_pos hh]

/-- At the cap a challenge repeats the latest ciphertext:
`hybImpl κ E sel 1 mm h = pure (padFin (outs 1) ⟦h.headD 0⟧, h)` when `κ ≤ |h|`. -/
theorem hybImpl_full (mm : Fin (ins 1) → Bool) (h : List (Fin L → Bool)) (hh : κ ≤ h.length) :
    hybImpl (outs := outs) κ E sel 1 mm h =
      .pure (padFin (outs 1) (List.ofFn (h.headD (zeroBits L))), h) := by
  rw [hybImpl, if_neg (Nat.not_lt_of_ge hh)]

/-- **Only the selector below the cap matters:** if `sel j = sel' j` for every `j < κ`, the two
hybrids are the same implementation.

**Proof sketch.** The selector is read only at `|h|` in a fresh challenge, where `|h| < κ`. -/
theorem hybImpl_congr {sel' : ℕ → Bool} (hsel : ∀ j < κ, sel j = sel' j) :
    hybImpl (outs := outs) κ E sel = hybImpl κ E sel' := by
  funext i x h
  match i, x with
  | 0, x => rw [hybImpl_zero, hybImpl_zero]
  | 1, x =>
    by_cases hh : h.length < κ
    · rw [hybImpl_fresh κ E sel x h hh, hybImpl_fresh κ E sel' x h hh, hsel _ hh]
    · rw [hybImpl_full κ E sel x h (Nat.le_of_not_lt hh),
        hybImpl_full κ E sel' x h (Nat.le_of_not_lt hh)]

/-- **The hybrid with coins given in advance:** as `hybImpl κ E sel`, except that the `j`-th fresh
challenge uses the coins `T j`, unless `j = kst`, where it samples coins. -/
noncomputable def tapeImpl (T : ℕ → C) (kst : ℕ) :
    QueryImpl (bitSpec ins outs) (List (Fin L → Bool)) unifSpec
  | 0, _, h => .pure (zeroBits _, h)
  | 1, mm, h =>
    if h.length < κ then
      if h.length = kst then
        (ProbComp.sample C).bind fun r =>
          .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm r)), E (sel h.length) mm r :: h)
      else
        .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm (T h.length))),
          E (sel h.length) mm (T h.length) :: h)
    else .pure (padFin (outs 1) (List.ofFn (h.headD (zeroBits L))), h)

variable (T : ℕ → C) (kst : ℕ)

/-- With coins in advance, decryption answers all-`false` and keeps the history:
`tapeImpl κ E sel T kst 0 x h = pure (0, h)`. -/
theorem tapeImpl_zero (x : Fin (ins 0) → Bool) (h : List (Fin L → Bool)) :
    tapeImpl (outs := outs) κ E sel T kst 0 x h = .pure (zeroBits _, h) :=
  rfl

/-- The `kst`-th fresh challenge samples its coins:
`tapeImpl κ E sel T kst 1 mm h = (sample C).bind fun r => pure (padFin (outs 1) ⟦c⟧, c :: h)`
with `c = E (sel |h|) mm r`, when `|h| < κ` and `|h| = kst`. -/
theorem tapeImpl_lazy (mm : Fin (ins 1) → Bool) (h : List (Fin L → Bool)) (hh : h.length < κ)
    (hk : h.length = kst) :
    tapeImpl (outs := outs) κ E sel T kst 1 mm h =
      (ProbComp.sample C).bind fun r =>
        .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm r)),
          E (sel h.length) mm r :: h) := by
  rw [tapeImpl, if_pos hh, if_pos hk]

/-- Another fresh challenge uses its coins in advance:
`tapeImpl κ E sel T kst 1 mm h = pure (padFin (outs 1) ⟦c⟧, c :: h)` with
`c = E (sel |h|) mm (T |h|)`, when `|h| < κ` and `|h| ≠ kst`. -/
theorem tapeImpl_eager (mm : Fin (ins 1) → Bool) (h : List (Fin L → Bool)) (hh : h.length < κ)
    (hk : h.length ≠ kst) :
    tapeImpl (outs := outs) κ E sel T kst 1 mm h =
      .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm (T h.length))),
        E (sel h.length) mm (T h.length) :: h) := by
  rw [tapeImpl, if_pos hh, if_neg hk]

/-- At the cap a challenge repeats the latest ciphertext, as in `hybImpl_full`:
`tapeImpl κ E sel T kst 1 mm h = pure (padFin (outs 1) ⟦h.headD 0⟧, h)` when `κ ≤ |h|`. -/
theorem tapeImpl_full (mm : Fin (ins 1) → Bool) (h : List (Fin L → Bool)) (hh : κ ≤ h.length) :
    tapeImpl (outs := outs) κ E sel T kst 1 mm h =
      .pure (padFin (outs 1) (List.ofFn (h.headD (zeroBits L))), h) := by
  rw [tapeImpl, if_neg (Nat.not_lt_of_ge hh)]

/-- **The run ignores the coins of challenges already issued:** if `T` and `T'` agree at every
index `m ≥ |h|`, the runs from the history `h` agree.

**Proof sketch.** Induction on the computation. A fresh challenge from a history `h'` with
`|h| ≤ |h'|` reads only `T |h'|`, and moves to a longer history. -/
theorem simulate_tapeImpl_congr {α : Type} (T' : ℕ → C) (c : OracleComp (bitSpec ins outs) α)
    (h : List (Fin L → Bool)) (hT : ∀ m, h.length ≤ m → T m = T' m) :
    simulate (tapeImpl κ E sel T kst) c h = simulate (tapeImpl κ E sel T' kst) c h := by
  induction c generalizing h with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, simulate_query, tapeImpl_zero, tapeImpl_zero, OracleComp.pure_bind,
        OracleComp.pure_bind]
      exact ih _ h hT
    | 1, x, k, ih =>
      have hT' : ∀ m, (h.length + 1) ≤ m → T m = T' m := fun m hm => hT m (by omega)
      by_cases hh : h.length < κ
      · by_cases hk : h.length = kst
        · rw [simulate_query, simulate_query, tapeImpl_lazy κ E sel T kst x h hh hk,
            tapeImpl_lazy κ E sel T' kst x h hh hk, OracleComp.bind_assoc,
            OracleComp.bind_assoc]
          congr 1
          funext r
          rw [OracleComp.pure_bind, OracleComp.pure_bind]
          exact ih _ _ hT'
        · rw [simulate_query, simulate_query, tapeImpl_eager κ E sel T kst x h hh hk,
            tapeImpl_eager κ E sel T' kst x h hh hk, OracleComp.pure_bind,
            OracleComp.pure_bind, hT h.length le_rfl]
          exact ih _ _ hT'
      · rw [simulate_query, simulate_query, tapeImpl_full κ E sel T kst x h (Nat.le_of_not_lt hh),
          tapeImpl_full κ E sel T' kst x h (Nat.le_of_not_lt hh), OracleComp.pure_bind,
          OracleComp.pure_bind]
        exact ih _ h hT

end Hybrid

/-! ### Coins in advance have the lazy distribution -/

section Eager

variable {C : Type} [Nonempty C]

/-- A family of `κ` coin strings, extended to every index by an arbitrary value:
`extTape T m = T m` for `m < κ`. -/
noncomputable def extTape {κ : ℕ} (T : Fin κ → C) (m : ℕ) : C :=
  if hm : m < κ then T ⟨m, hm⟩ else Classical.arbitrary C

/-- Below `κ` the extended family is the family: `extTape T m = T ⟨m, hm⟩`. -/
theorem extTape_of_lt {κ : ℕ} (T : Fin κ → C) {m : ℕ} (hm : m < κ) :
    extTape T m = T ⟨m, hm⟩ := by
  rw [extTape, dif_pos hm]

/-- Changing one coordinate `j` of `T` changes its extension only at `j`:
`extTape (T[j ↦ r]) m = extTape T m` for `m ≠ j`. -/
theorem extTape_update {κ : ℕ} (T : Fin κ → C) (j : Fin κ) (r : C) {m : ℕ} (hm : m ≠ j) :
    extTape (Function.update T j r) m = extTape T m := by
  by_cases h : m < κ
  · rw [extTape_of_lt _ h, extTape_of_lt _ h, Function.update_of_ne]
    exact fun h' => hm (congrArg Fin.val h')
  · rw [extTape, extTape, dif_neg h, dif_neg h]

variable [Fintype C]

/-- **Resampling one coordinate of a uniform tuple:** if `F r T` ignores the coordinate `j` of
`T`, then `𝔼_T F (T j) T = 𝔼_r 𝔼_T F r T`.

**Proof sketch.** The map `(T, r) ↦ (T[j ↦ r], T j)` is an involution of `(Fin κ → C) × C`, so
it preserves the uniform average (`expect_sample_equiv`). It carries `F (T j) T` to
`F r (T[j ↦ r]) = F r T`. Split the products (`expect_sample_prod`), drop the unused sample
(`expect_const`) and exchange the order (`expect_sample_comm`). -/
theorem expect_sample_update {κ : ℕ} (j : Fin κ) (F : C → (Fin κ → C) → ℝ)
    (hF : ∀ r r' T, F r (Function.update T j r') = F r T) :
    expect (sample (Fin κ → C)) (fun T => F (T j) T) =
      expect (sample C) fun r => expect (sample (Fin κ → C)) fun T => F r T := by
  let e : (Fin κ → C) × C ≃ (Fin κ → C) × C :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := fun p => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      right_inv := fun p => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }
  have he := expect_sample_equiv e (fun p => F (p.1 j) p.1)
  have hl : (fun p : (Fin κ → C) × C => F ((e p).1 j) (e p).1) = fun p => F p.2 p.1 := by
    funext p
    show F ((Function.update p.1 j p.2) j) (Function.update p.1 j p.2) = F p.2 p.1
    rw [Function.update_self, hF]
  rw [hl, expect_sample_prod, expect_sample_prod] at he
  rw [← expect_sample_comm, he]
  refine congrArg _ (funext fun T => ?_)
  exact (expect_const _ _).symm

variable {ins outs : Fin 2 → ℕ} {L : ℕ}

/-- **Coins in advance have the lazy distribution:** for every `kst` and every function `G` of
the output and the final history, averaging over uniform coins `T` in advance gives the lazy
hybrid: `𝔼_T 𝔼[G (simulate (tapeImpl κ E sel (extTape T) kst) c h)] =
𝔼[G (simulate (hybImpl κ E sel) c h)]`.

**Proof sketch.** Induction on `c`, generalizing the history. Decryption queries and challenges
at the cap are answered alike. The `kst`-th fresh challenge samples coins on both sides; exchange
the order of the two samples (`expect_sample_comm`) and apply the induction hypothesis. Another
fresh challenge, the `j`-th, reads `T j` on the left; the continuation runs from a history of
length `j + 1`, so it ignores `T j` (`simulate_tapeImpl_congr`, `extTape_update`), and
`expect_sample_update` replaces `T j` by fresh coins; then apply the induction hypothesis. -/
theorem expect_tapeImpl (κ : ℕ) (E : Bool → (Fin (ins 1) → Bool) → C → (Fin L → Bool))
    (sel : ℕ → Bool) (kst : ℕ) {α : Type} (G : α × List (Fin L → Bool) → ℝ)
    (c : OracleComp (bitSpec ins outs) α) (h : List (Fin L → Bool)) :
    expect (sample (Fin κ → C))
        (fun T => expect (simulate (tapeImpl κ E sel (extTape T) kst) c h) G) =
      expect (simulate (hybImpl κ E sel) c h) G := by
  induction c generalizing h with
  | pure a =>
    simp only [simulate_pure, expect_pure]
    exact expect_const _ _
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      simp only [simulate_query, tapeImpl_zero, hybImpl_zero, OracleComp.pure_bind]
      exact ih _ h
    | 1, x, k, ih =>
      by_cases hh : h.length < κ
      · rw [simulate_query, hybImpl_fresh κ E sel x h hh, OracleComp.bind_assoc, expect_bind]
        simp only [OracleComp.pure_bind]
        by_cases hk : h.length = kst
        · simp only [simulate_query, tapeImpl_lazy κ E sel _ kst x h hh hk, OracleComp.bind_assoc,
            expect_bind, OracleComp.pure_bind]
          rw [expect_sample_comm]
          exact congrArg _ (funext fun r => ih _ _)
        · simp only [simulate_query, tapeImpl_eager κ E sel _ kst x h hh hk, OracleComp.pure_bind]
          let j : Fin κ := ⟨h.length, hh⟩
          have hj : ∀ T : Fin κ → C, extTape T h.length = T j := fun T => extTape_of_lt T hh
          simp only [hj]
          refine (expect_sample_update j (fun r T => expect (simulate
            (tapeImpl κ E sel (extTape T) kst) (k (padFin (outs 1) (List.ofFn
              (E (sel h.length) x r)))) (E (sel h.length) x r :: h)) G) ?_).trans ?_
          · intro r r' T
            refine congrArg (fun c => expect c G)
              (simulate_tapeImpl_congr κ E sel _ kst _ _ _ fun m hm => ?_)
            rw [List.length_cons] at hm
            exact extTape_update T j r' (by
              intro hmj
              have : m = h.length := hmj
              omega)
          · exact congrArg _ (funext fun r => ih _ _)
      · simp only [simulate_query, tapeImpl_full κ E sel _ kst x h (Nat.le_of_not_lt hh),
          hybImpl_full κ E sel x h (Nat.le_of_not_lt hh), OracleComp.pure_bind]
        exact ih _ h

end Eager

end TCSlib.Cryptography.Composability.AdaptiveCPA

## ===== TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/Reduction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The reduction's game is a hybrid

Let `B` be the machine that T2 (`Games.exists_interactiveHandlerMachine`) builds from the
adversary `A` and the handler `acHandler S cap ist`. This file proves that `B`'s single-challenge
CPA game with bit `b` has the acceptance probability of the hybrid `H_{i⋆(n)+b}`
(`accept_indGame_acHyb`): the first `i⋆` fresh challenges encrypt the right message (the
handler's own encryptions), the `i⋆`-th encrypts `m_b` (the forwarded outer challenge), and the
later ones encrypt the left message.

The proof composes the handler with the outer oracles (`QueryImpl.comp`) and relates the composite,
state by state, to the hybrid with coins given in advance (`tapeImpl`): the handler's state and
the outer challenge state are functions of the hybrid's history (`acAbs`; the outer state is the
`i⋆`-th issued ciphertext once it exists). The handler's tapes, drawn uniformly, then give the lazy
hybrid (`expect_tapeImpl`). Both ends of the run are transported between the game's codec and T2's
(`expect_simulate_castImpl_toCompOn`).

## Main results

* `AdaptiveCPA.castImpl_indImpl_challenge`: the outer challenge oracle on T2's codec.
* `AdaptiveCPA.accept_indGame_acHyb`: `B`'s game with bit `b` is the hybrid `H_{i⋆+b}`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 171.5 and the single-to-many hybrid argument (book p. 103).
-/

namespace TCSlib.Cryptography.Composability.AdaptiveCPA

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

variable (S : FixedLengthPKScheme)

/-- **The outer challenge oracle on T2's codec:** the first challenge `x` samples coins `r`,
answers `c = acEnc S n pk b x r` (read at T2's width) and records it. -/
theorem castImpl_indImpl_challenge (b : Bool) (n : ℕ) (pk sk : List Bool)
    (x : Fin ((acDin S 1).eval n) → Bool) :
    castImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
        (S.indImpl .cpa b n pk sk) 1 x none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        .pure (padFin ((acDout S 1).eval n) (List.ofFn (acEnc S n pk b x r)),
          some (acEnc S n pk b x r)) := by
  rw [castImpl_eq, S.indImpl_challenge_none_onSpec, OracleComp.bind_assoc]
  congr 1
  funext r
  dsimp only
  rw [OracleComp.pure_bind, ofFn_cast (S.outLens_one n).symm, acEnc_eq, ofFn_select]

/-- The `i`-th issued ciphertext after one more: `(c :: h).reverse[i]?` is `c` at `i = |h|` and
`h.reverse[i]?` otherwise. -/
private theorem getElem?_reverse_cons {α : Type} (c : α) (h : List α) (i : ℕ) :
    (c :: h).reverse[i]? = if i = h.length then some c else h.reverse[i]? := by
  rw [List.reverse_cons]
  by_cases hi : i < h.length
  · rw [List.getElem?_append_left (by rw [List.length_reverse]; exact hi), if_neg (by omega)]
  · rw [List.getElem?_append_right (by rw [List.length_reverse]; omega), List.length_reverse]
    by_cases he : i = h.length
    · rw [if_pos he, he, Nat.sub_self]
      rfl
    · rw [if_neg he, List.getElem?_eq_none (by rw [List.length_singleton]; omega),
        List.getElem?_eq_none (by rw [List.length_reverse]; omega)]

variable (cap : PolyExpr) (ist : ℕ → ℕ)

/-- **The state abstraction:** after the history `h` of issued ciphertexts, the handler's state
records `min |h| κ` fresh challenges and the latest ciphertext `h.headD 0`, and the outer
challenge state is the `i⋆`-th issued ciphertext, if any. -/
private def acAbs (n : ℕ) (h : List (Fin (S.ctLen.eval n) → Bool)) :
    (Fin ((acHandler S cap ist).stateLen.eval n) → Bool) × Option (Fin (S.ctLen.eval n) → Bool) :=
  (acHState S cap ist n (min h.length (cap.eval n)) (h.headD (zeroBits _)), h.reverse[ist n]?)

/-- The selector of `H_{i⋆+b}` at the advised index is `b`. -/
private theorem sel_ist (b : Bool) (m : ℕ) : decide (m < m + b.toNat) = b := by
  cases b
  · rw [Bool.toNat_false, Nat.add_zero, decide_eq_false (Nat.lt_irrefl m)]
  · rw [Bool.toNat_true, decide_eq_true (Nat.lt_succ_self m)]

/-- Away from the advised index the selector of `H_{i⋆+b}` is `[j < i⋆]`. -/
private theorem sel_ne (b : Bool) {j m : ℕ} (h : j ≠ m) :
    decide (j < m + b.toNat) = decide (j < m) := by
  cases b
  · rw [Bool.toNat_false, Nat.add_zero]
  · rw [Bool.toNat_true]
    exact decide_eq_decide.2 ⟨fun h' => by omega, fun h' => by omega⟩

/-- **One call of the composite is one call of the hybrid with coins in advance**, abstracted:
the handler composed with the outer oracles of bit `b`, from `acAbs h`, is the hybrid
`H_{i⋆+b}` with the handler's tapes and the lazy slot `i⋆`, from `h`, with its new history
abstracted.

**Proof sketch.** Decryption: both refuse and keep the state. At the cap: both repeat the
latest ciphertext. Below the cap, away from `i⋆`: the handler encrypts with its tape, which is
the hybrid's coin in advance, and the outer state is unchanged. At `i⋆`: the handler forwards the
challenge, the outer oracle samples coins and encrypts `m_b`, which is the hybrid's lazy slot, and
the outer state becomes the new ciphertext. -/
private theorem comp_acAbs (b : Bool) (n : ℕ) (hist : ist n ≤ cap.eval n) (pk sk : List Bool)
    (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool) (i : Fin 2)
    (x : (bitSpecAt (acDin S) (acDout S) n).dom i) (h : List (Fin (S.ctLen.eval n) → Bool)) :
    (castImpl (S.indImpl .cpa b n pk sk)).comp ((acHandler S cap ist).impl n pk ω) i x
        (acAbs S cap ist n h) =
      (tapeImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
          (cap.eval n) (acEnc S n pk) (fun j => decide (j < ist n + b.toNat))
          (extTape (acSeedTapes S cap ist n ω)) (ist n) i x h).bind
        fun p => .pure (p.1, acAbs S cap ist n p.2) := by
  match i, x with
  | 0, x =>
    rw [QueryImpl.comp_apply, tapeImpl_zero, OracleComp.pure_bind, acAbs]
    dsimp only
    rw [acHandler_impl_dec, simulate_pure, OracleComp.pure_bind]
  | 1, x =>
    rw [QueryImpl.comp_apply]
    by_cases hh : h.length < cap.eval n
    · have hmin : min h.length (cap.eval n) = h.length := Nat.min_eq_left hh.le
      by_cases hk : h.length = ist n
      · -- the advised challenge: forwarded to the outer oracle, the hybrid's lazy slot
        have h2 : h.reverse[ist n]? = none :=
          List.getElem?_eq_none (by rw [List.length_reverse]; omega)
        have hsel : decide (h.length < ist n + b.toNat) = b := by
          rw [hk]
          exact sel_ist b (ist n)
        rw [tapeImpl_lazy (ins := fun i => (acDin S i).eval n)
          (outs := fun i => (acDout S i).eval n) _ _ _ _ _ x h hh hk,
          hsel, acAbs]
        dsimp only
        rw [hmin, h2, acHandler_impl_forward S cap ist n pk ω x h.length _ hh hk, simulate_query,
          castImpl_indImpl_challenge, OracleComp.bind_assoc, OracleComp.bind_assoc,
          OracleComp.bind_assoc]
        congr 1
        funext r
        simp only [OracleComp.pure_bind, simulate_pure]
        have he : padFin (S.ctLen.eval n) (List.ofFn (padFin ((acDout S 1).eval n)
            (List.ofFn (acEnc S n pk b x r)))) = acEnc S n pk b x r := by
          rw [GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, acDout_one]), padFin_ofFn]
        rw [he, acAbs, List.length_cons, Nat.min_eq_left (by omega), List.headD_cons,
          getElem?_reverse_cons, if_pos hk.symm]
      · -- another fresh challenge: the handler's own encryption with its tape
        rw [tapeImpl_eager (ins := fun i => (acDin S i).eval n)
          (outs := fun i => (acDout S i).eval n) _ _ _ _ _ x h hh hk,
          OracleComp.pure_bind, acAbs]
        dsimp only
        rw [hmin, acHandler_impl_eager S cap ist n pk ω x h.length _ hh hk hist, simulate_pure,
          OracleComp.pure_bind, sel_ne b hk, extTape_of_lt _ hh, acAbs, List.length_cons,
          Nat.min_eq_left (by omega), List.headD_cons, getElem?_reverse_cons,
          if_neg (fun e => hk e.symm), acEnc_eq]
    · -- at the cap: the latest ciphertext is repeated
      have hmin : min h.length (cap.eval n) = cap.eval n := Nat.min_eq_right (Nat.le_of_not_lt hh)
      rw [tapeImpl_full (ins := fun i => (acDin S i).eval n)
        (outs := fun i => (acDout S i).eval n) _ _ _ _ _ x h
        (Nat.le_of_not_lt hh), OracleComp.pure_bind, acAbs]
      dsimp only
      rw [hmin, acHandler_impl_full S cap ist n pk ω x _ hist, simulate_pure, OracleComp.pure_bind]

/-- The handler starts from the abstraction of the empty history. -/
private theorem init_acAbs (n : ℕ) :
    ((acHandler S cap ist).init n, (none : Option (Fin (S.ctLen.eval n) → Bool))) =
      acAbs S cap ist n [] := by
  rw [acAbs, acHandler_init_eq, List.length_nil, Nat.zero_min, List.headD_nil, List.reverse_nil,
    List.getElem?_nil]

section Game

variable (A : NUPPT) (q : PolyExpr) (n : ℕ) (B : NUPPT)
  (φ : (Fin ((acHandler S cap ist).seedLen.eval n) → Bool) × A.Coins n ≃ B.Coins n)

/-- **One run of `B`'s game is a run of the hybrid with coins in advance:** with the keys, the
adversary's coins `r` and the handler's seed `ω` fixed, the probability that `B`'s CPA run against
the oracles of bit `b` outputs `1` is the expectation of `A`'s bit against `H_{i⋆+b}` with the
handler's tapes in advance and the lazy slot `i⋆`.

**Proof sketch.** Transport `B`'s run to T2's codec (`indCodec_eq_bitCodec`,
`expect_simulate_castImpl_toCompOn`), replace it by the reduction (T2's equation `hφ`, with
`acHandler_advInput` and `acHandler_finish`), compose the two simulations (`simulate_bind`,
`simulate_comp`) and pass to the hybrid through the state abstraction (`init_acAbs`,
`simulate_eq_of_abs`, `comp_acAbs`). -/
private theorem prob_red_tape (hist : ist n ≤ cap.eval n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((acHandler S cap ist).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) ((acHandler S cap ist).advInput n z ω) r)
          ((acHandler S cap ist).init n)).bind
          (fun res => (acHandler S cap ist).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n)
          ((acHandler S cap ist).outLen.eval n)) n
          (q.eval n * (acHandler S cap ist).perCall.eval n + (acHandler S cap ist).finCall.eval n)
          z (φ (ω, r)))
    (b : Bool) (pk sk : List Bool) (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)
    (r : A.Coins n) :
    ProbComp.prob ((simulate (S.indImpl .cpa b n pk sk) (B.toCompOn (S.indCodec n) n
        (q.eval n * (acHandler S cap ist).perCall.eval n + (acHandler S cap ist).finCall.eval n)
        pk (φ (ω, r))) none).bind fun res => .pure (res.1 0)) (· = true) =
      expect (simulate (tapeImpl (ins := fun i => (acDin S i).eval n)
          (outs := fun i => (acDout S i).eval n) (cap.eval n) (acEnc S n pk)
          (fun j => decide (j < ist n + b.toNat)) (extTape (acSeedTapes S cap ist n ω)) (ist n))
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) pk r) [])
        (fun p => if (List.ofFn p.1).headD false = true then 1 else 0) := by
  have hd : (acHandler S cap ist).outLen.eval n = 1 := by
    rw [acHandler_outLen, PolyExpr.eval_const]
  have h1 : (fun res : (Fin 1 → Bool) × Option (Fin (S.ctLen.eval n) → Bool) =>
      ProbComp.prob (.pure (res.1 0)) (· = true)) =
      fun res => if (List.ofFn res.1).headD false = true then (1 : ℝ) else 0 := by
    funext res
    rw [prob_pure, headD_ofFn_one]
  rw [prob_bind, indCodec_eq_bitCodec, h1]
  refine (expect_simulate_castImpl_toCompOn (acDin_eval S n) (acDout_eval S n) hd
    (S.indImpl .cpa b n pk sk) B n _ pk (φ (ω, r)) none
    (fun p => if p.1.headD false = true then (1 : ℝ) else 0)).symm.trans ?_
  rw [← hφ pk ω r, acHandler_advInput]
  simp only [acHandler_finish]
  rw [simulate_bind, simulate_comp, OracleComp.bind_assoc, expect_bind]
  simp only [OracleComp.pure_bind, simulate_pure, expect_pure]
  rw [init_acAbs,
    simulate_eq_of_abs _ _ (acAbs S cap ist n) (comp_acAbs S cap ist b n hist pk sk ω),
    expect_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [expect_pure, GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, acHandler_outLen])]

/-- **`B`'s game is the hybrid `H_{i⋆+b}`:** if `B` is the machine of T2 for the handler
`acHandler S cap ist` (with the coin bijection `φ` at `n`) and `i⋆(n) ≤ cap(n)`, then `B`'s
single-challenge CPA game with bit `b` and `A`'s hybrid game with the selector `j ↦ [j < i⋆ + b]`
accept with the same probability.

**Proof sketch.** Fix the key-generation coins. `B`'s coins are the handler's seed `ω` and `A`'s
coins `r` (`expect_sample_equiv φ`, `expect_sample_prod`). For fixed `ω` and `r` the run is the
hybrid with the handler's tapes in advance (`prob_red_tape`). The tapes are uniform
(`expect_sample_equiv (acSeedTapes …)`), so averaging over them gives the lazy hybrid
(`expect_tapeImpl`). -/
theorem accept_indGame_acHyb (hist : ist n ≤ cap.eval n)
    (hφ : ∀ (z : List Bool) (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)
      (r : A.Coins n),
      (simulate ((acHandler S cap ist).impl n z ω)
          (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
            ((PolyExpr.const 1).eval n)) n (q.eval n) ((acHandler S cap ist).advInput n z ω) r)
          ((acHandler S cap ist).init n)).bind
          (fun res => (acHandler S cap ist).finish n z ω res.2 res.1) =
        B.toCompOn (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n)
          ((acHandler S cap ist).outLen.eval n)) n
          (q.eval n * (acHandler S cap ist).perCall.eval n + (acHandler S cap ist).finCall.eval n)
          z (φ (ω, r)))
    (b : Bool) :
    accept (S.indGame .cpa B
        (q.eval n * (acHandler S cap ist).perCall.eval n + (acHandler S cap ist).finCall.eval n)
        b n) =
      accept (acHyb S A (q.eval n) (cap.eval n) n (fun j => decide (j < ist n + b.toNat))) := by
  rw [accept_eq, accept_eq, S.indGame_eq, acHyb_eq, prob_bind, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind, prob_bind, ← expect_sample_equiv φ, expect_sample_prod, expect_sample_comm]
  refine congrArg _ (funext fun r => ?_)
  simp only [prob_red_tape S cap ist A q n B φ hist hφ b]
  refine (expect_sample_equiv (acSeedTapes S cap ist n) (fun T => expect (simulate
    (tapeImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
      (cap.eval n) (acEnc S n (pairFstD (S.gen.runAt n [] rg)))
      (fun j => decide (j < ist n + b.toNat)) (extTape T) (ist n))
    (A.toCompOn (bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
      ((PolyExpr.const 1).eval n)) n (q.eval n) (pairFstD (S.gen.runAt n [] rg)) r) [])
    (fun p => if (List.ofFn p.1).headD false = true then 1 else 0))).trans ?_
  rw [expect_tapeImpl, prob_bind]
  simp only [prob_pure]

end Game

end TCSlib.Cryptography.Composability.AdaptiveCPA

## ===== TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Eager
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Planted
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.QueryHandler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bitwise scheme under chosen-plaintext attack

The bitwise scheme of [PS10, p. 103] encrypts an `n`-bit message one bit at a time with a
single-bit scheme (such as the trapdoor scheme of Algorithm 104.3, secure by Theorem 104.4).
Padded to fixed-length ciphertexts (`PublicKeyScheme.padded`), it is a fixed-length scheme with
`n`-bit messages. If the single-bit scheme is secure, the padded bitwise scheme is CPA-secure in
the game of [PS10, Definition 171.5], where the adversary chooses its two messages after seeing
the public key, and hence secure in the adaptive multi-challenge game.

Ensemble security of the bitwise scheme for message pairs fixed in advance
(`BitPublicKeyScheme.SingleBitSecure.bitwise`) is not enough here: there the messages cannot
depend on the public key. The proof below therefore goes back to single-bit security.

## Main results

* `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa`: the padded bitwise scheme is
  CPA-secure.
* `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_adaptive_cpa`: and adaptively CPA-secure.
* `BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa`: a fixed-length scheme with `n`-bit
  messages and the same key generator is adaptively CPA-secure.

## Contents

* `BitwiseCPA/Eager`: eager challenge coins under CPA, resampling one coordinate of a uniform
  tuple, and readers of the padded encryptor.
* `BitwiseCPA/Planted`: the planted bitwise challenge answer and the reduction's final bit.
* `BitwiseCPA/QueryHandler`: the query-recording handler with advice and its machine by T1.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 (the bitwise scheme and the hybrid argument); Algorithm 104.3 and Theorem 104.4 (the
  single-bit trapdoor scheme, book pp. 104–105); Definition 171.5 (book p. 171).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### The hybrid argument -/

section BitwiseCPAProof

open ChallengeSim BitwiseSim ProbComp

/-- The tuple of hybrid `j` on the challenge `l = m₀ ‖ m₁`: block `i` encrypts, with the coins
`v_i`, bit `i` of the right message (`l_{n+i}`) if `i < j` and of the left message (`l_i`)
otherwise. -/
private def hybCt (S : BitPublicKeyScheme) (n j : ℕ) (pk : List Bool)
    (v : Fin n → S.enc.Coins n) (l : List Bool) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
    S.enc.runAt n (pairEncode pk [if (i : ℕ) < j then l.getD (n + i) false else l.getD i false])
      (v i))

/-- **The hybrid `H_j`** (step 1): sample the keys, `A`'s coins and `n` single-bit encryption
tapes `v`, run `A` against the CPA oracles whose first challenge `⟨m₀, m₁⟩` is answered with the
padded tuple of hybrid `j` (`hybCt`, later challenges repeat it), and output `A`'s bit. -/
private noncomputable def hybGame (S : BitPublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) (A : NUPPT) (q n j : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (ProbComp.sample (Fin n → S.enc.Coins n)).bind fun v =>
  .pure ((chRun (fun mm => padCt (L.eval n)
      (hybCt S n j (pairFstD (S.gen.runAt n [] rg)) v (List.ofFn mm)))
    (A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n q
      (pairFstD (S.gen.runAt n [] rg)) r) none).1 0)

/-- The bitwise encryptor on a coin list: the tuple of the single-bit encryptions with the
consecutive coin segments (`bitwise_enc`, `bitwise_enc_runAtL`). -/
private theorem bitwise_runAtL (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool)
    (m : Fin n → Bool) (r : List Bool) :
    S.bitwise.enc.runAtL n (pairEncode pk (List.ofFn m)) r =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAtL n (pairEncode pk [m i]) (coinBlock (S.enc.coinLen n) i r)) := by
  rw [BitPublicKeyScheme.bitwise_enc]
  exact BitPublicKeyScheme.bitwise_enc_runAtL S n pk m r

/-- The bitwise encryptor on the coin blocks `v`: the tuple of the single-bit encryptions with
coins `v_i` (`bitwiseEncCoins_ofFn`, `coinBlock_ofFn_coinBlocks`). -/
private theorem bitwise_runAt_blocks (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool)
    (m : Fin n → Bool) (v : Fin n → S.enc.Coins n) :
    S.bitwise.enc.runAt n (pairEncode pk (List.ofFn m)) (S.bitwiseEncCoins n v) =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAt n (pairEncode pk [m i]) (v i)) := by
  rw [NUPPT.runAt_eq, bitwise_runAtL, BitPublicKeyScheme.bitwiseEncCoins_ofFn]
  refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
  rw [coinBlock_ofFn_coinBlocks, ← NUPPT.runAt_eq]

/-- The selected half of a challenge query, as the list of its `n` bits read from the query. -/
private theorem ofFn_half {k n : ℕ} (hk : k = n) (b : Bool) (mm : Fin (k + k) → Bool) :
    List.ofFn (if b then (FixedLengthScheme.splitHalf mm).2
      else (FixedLengthScheme.splitHalf mm).1) =
      List.ofFn (fun i : Fin n => (List.ofFn mm).getD ((if b then n else 0) + i) false) := by
  subst hk
  apply List.ext_getElem
  · cases b <;> simp
  · intro t h₁ h₂
    have ht : t < k := by cases b <;> simpa using h₂
    cases b
    · simp [FixedLengthScheme.splitHalf_fst, List.getD_eq_getElem?_getD]
      rw [dif_pos (by omega)]
      rfl
    · simp [FixedLengthScheme.splitHalf_snd, List.getD_eq_getElem?_getD]
      exact congrArg mm (Fin.ext (Nat.add_comm _ _))

/-- A list of `n + n` bits is its first and its last `n` bits. -/
private theorem ofFn_getD_split {n : ℕ} (l : List Bool) (hl : l.length = n + n) :
    l = List.ofFn (fun i : Fin n => l.getD i false) ++
      List.ofFn (fun i : Fin n => l.getD (n + i) false) := by
  apply List.ext_getElem
  · simp [hl]
  · intro t h₁ h₂
    rw [List.getElem_append]
    split
    · next h => simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]
    · next h =>
      simp only [List.getElem_ofFn, List.length_ofFn] at h ⊢
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      congr 1
      omega

/-- **The ends of the hybrids are the CPA games** (step 1):
`Pr[Ind_b = 1] = Pr[H_{j_b} = 1]` with `j_0 = 0`, `j_1 = n`.

**Proof sketch.** Eager coins (`expect_simulate_indImpl_cpa`); the padded bitwise encryptor pads
the tuple of single-bit encryptions (`padded_enc_runAt`, `bitwise_runAt_blocks`) on the coin
blocks `v` (the bijection `bitwiseEncCoins`, then `coinsCongr`), and bit `i` of the selected
half is `l_{n+i}` for `b = 1` and `l_i` for `b = 0` (`ofFn_half`). -/
private theorem accept_indGame_eq (S : BitPublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) (A : NUPPT) (q n : ℕ) (b : Bool) :
    accept ((S.bitwise.padded L hL hmsg).indGame .cpa A q b n) =
      accept (hybGame S L hL hmsg A q n (if b then n else 0)) := by
  have hgen : (S.bitwise.padded L hL hmsg).gen = S.gen :=
    (PublicKeyScheme.padded_gen _ _ _ _).trans (BitPublicKeyScheme.bitwise_gen S)
  have hk : (S.bitwise.padded L hL hmsg).msgLen.eval n = n := by
    rw [PublicKeyScheme.padded_msgLen, PolyExpr.eval_var]
  rw [accept_eq, accept_eq, FixedLengthPKScheme.indGame_eq, hgen]
  unfold hybGame
  rw [prob_bind, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind, prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind, prob_bind]
  refine (expect_simulate_indImpl_cpa _ b n _ _
    (fun a : Fin 1 → Bool => ProbComp.prob (.pure (a 0)) (· = true)) _).trans ?_
  rw [← expect_sample_equiv ((S.bitwiseEncCoins n).trans
    (NUPPT.coinsCongr (padded_enc_coins S.bitwise L hL hmsg) n))]
  refine congrArg _ (funext fun v => ?_)
  refine congrArg (fun g => ProbComp.prob (.pure ((chRun g
    (A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r)
      none).1 0)) (· = true)) (funext fun mm => ?_)
  rw [padded_enc_runAt, Equiv.trans_apply, NUPPT.coinsCongr_ofFn,
    ofFn_half hk b (cast ((S.bitwise.padded L hL hmsg).indSpec_challengeDom n) mm),
    AdaptiveCPA.ofFn_cast ((S.bitwise.padded L hL hmsg).inLens_one n), ← NUPPT.runAt_eq,
    bitwise_runAt_blocks]
  unfold hybCt
  refine congrArg (fun l => padCt (L.eval n) (PrivateKeyScheme.encodeList (List.ofFn l)))
    (funext fun i => ?_)
  cases b <;> simp [i.isLt]

/-- **Planting a bit is resampling a coin block**: the tuple whose block `j` is `Enc(β; re)` and
whose other blocks are those of hybrid `j` with coins `v` is the bitwise tuple of the message
with bit `j` replaced by `β`, with coin block `j` replaced by `re`. -/
private theorem planted_eq (S : BitPublicKeyScheme) (n j : ℕ) (hj : j < n) (pk : List Bool)
    (v : Fin n → S.enc.Coins n) (re : S.enc.Coins n) (β : Bool) (l : List Bool) :
    PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        if (i : ℕ) < j then S.enc.runAt n (pairEncode pk [l.getD (n + i) false]) (v i)
        else if (i : ℕ) = j then S.enc.runAt n (pairEncode pk [β]) re
        else S.enc.runAt n (pairEncode pk [l.getD i false]) (v i)) =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAt n (pairEncode pk [if (i : ℕ) < j then l.getD (n + i) false
          else if (i : ℕ) = j then β else l.getD i false]) (Function.update v ⟨j, hj⟩ re i)) := by
  refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
  by_cases h₁ : (i : ℕ) < j
  · have hne : i ≠ ⟨j, hj⟩ := fun h => by rw [h] at h₁; exact lt_irrefl _ h₁
    simp only [h₁, if_true, Function.update_of_ne hne]
  · by_cases h₂ : (i : ℕ) = j
    · have heq : i = ⟨j, hj⟩ := Fin.ext h₂
      subst heq
      simp only [h₁, if_false, if_true, Function.update_self]
    · have hne : i ≠ ⟨j, hj⟩ := fun h => h₂ (by rw [h])
      simp only [h₁, h₂, if_false, Function.update_of_ne hne]

/-- **Hybrids `j` and `j + 1` with coin block `j` resampled** plant `Enc(l_j; re)`
(`t = false`) and `Enc(l_{n+j}; re)` (`t = true`) at block `j` (`planted_eq`). -/
private theorem hybCt_update (S : BitPublicKeyScheme) (n j : ℕ) (hj : j < n) (pk : List Bool)
    (v : Fin n → S.enc.Coins n) (re : S.enc.Coins n) (l : List Bool) (t : Bool) :
    hybCt S n (if t then j + 1 else j) pk (Function.update v ⟨j, hj⟩ re) l =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        if (i : ℕ) < j then S.enc.runAt n (pairEncode pk [l.getD (n + i) false]) (v i)
        else if (i : ℕ) = j then
          S.enc.runAt n (pairEncode pk [if t then l.getD (n + j) false else l.getD j false]) re
        else S.enc.runAt n (pairEncode pk [l.getD i false]) (v i)) := by
  rw [planted_eq S n j hj]
  unfold hybCt
  refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
  refine congrArg (fun b => S.enc.runAt n (pairEncode pk [b]) (Function.update v ⟨j, hj⟩ re i)) ?_
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · have h' : (i : ℕ) < j + 1 := by omega
    cases t <;> simp [h, h']
  · cases t <;> simp [h]
  · have h₁ : ¬ (i : ℕ) < j := by omega
    have h₂ : (i : ℕ) ≠ j := by omega
    have h₃ : ¬ (i : ℕ) < j + 1 := by omega
    cases t <;> simp [h₁, h₂, h₃]

/-- The advice length of the reduction's handler: `2n + 2(n + 1)·B(n) + 4`. -/
private def bwLaux (S : BitPublicKeyScheme) : PolyExpr :=
  .add (.add (.mul (.const 2) .var) (.mul (.const 2) (.mul (.add .var (.const 1)) S.enc.coins)))
    (.const 4)

/-- The reduction's advice at `n`: `⟨1^{j⋆(n)}, ⟨1^{(j⋆(n)+1)·B(n)}, 0^…⟩⟩`, padded with zeros to
`bwLaux S` bits. -/
private def bwAux (S : BitPublicKeyScheme) (js : ℕ → ℕ) (n : ℕ) : List Bool :=
  pairEncode (List.replicate (js n) true)
    (pairEncode (List.replicate ((js n + 1) * S.enc.coinLen n) true)
      (List.replicate ((bwLaux S).eval n - (2 * js n + 2 * ((js n + 1) * S.enc.coinLen n) + 4))
        false))

/-- The advice has `bwLaux S` bits when `j⋆(n) ≤ n`. -/
private theorem bwAux_length (S : BitPublicKeyScheme) (js : ℕ → ℕ) (hjs : ∀ n, js n ≤ n)
    (n : ℕ) : (bwAux S js n).length = (bwLaux S).eval n := by
  have h := Nat.mul_le_mul_right (S.enc.coinLen n) (Nat.add_le_add_right (hjs n) 1)
  have h' := hjs n
  simp only [bwAux, bwLaux, length_pairEncode, List.length_replicate, PolyExpr.eval_add,
    PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, ← NUPPT.coinLen_eq]
  omega

/-- **The exact identity of step 3.** Let `D` be the machine of `exists_qHandlerMachine` for the
handler with advice `bwAux S js` (the index `j = j⋆(n)`), answer `plantAns` and final bit
`plantOut`. At `n` with `j < n`, the advantage between the hybrids `H_j` and `H_{j+1}` equals
`D`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`.

**Proof sketch.** Fix `n`, the keys and `A`'s coins. Both hybrids answer `A`'s first challenge
`l = m₀ ‖ m₁` only (`chRun_congr`). On `z = ⟨pk, Enc(β; re)⟩` with seed blocks `v`, `D` runs `A`
answering the planted tuple `W β v re l` (`plantTuple_spec`) and outputs
`(l_j ≠ l_{n+j}) ∧ (a ≠ l_j)` (`plantOut_recorded`), or `0` without a challenge
(`plantOut_init`). Resampling coin block `j` (`expect_sample_update`) turns hybrid `j` into
`W (l_j)` and hybrid `j + 1` into `W (l_{n+j})` (`hybCt_update`), and the case split on
`(l_j, l_{n+j})` (`expect_indicator_sub`) matches the two differences. -/
private theorem hyb_advantage_eq {S : BitPublicKeyScheme} (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) (A : NUPPT) (q : PolyExpr) (js : ℕ → ℕ) (D : NUPPT) (n : ℕ)
    (hj : js n < n)
    (φ : (Fin ((PolyExpr.mul .var S.enc.coins).eval n) → Bool) × A.Coins n ≃ D.Coins n)
    (hφ : ∀ (ins outs : Fin 2 → ℕ), (fun i => (qDin L (.add .var .var) i).eval n) = ins →
      (fun i => (qDout (.add .var (.const 1)) L i).eval n) = outs →
      ∀ (z : List Bool) (ω : Fin ((PolyExpr.mul .var S.enc.coins).eval n) → Bool)
        (r : A.Coins n),
        (∀ y : List Bool, y.length = (PolyExpr.add .var .var).eval n →
          (plantAns S.enc L (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (bwAux S js n) y))).length = L.eval n) →
        D.runAt n z (φ (ω, r)) =
          plantOut (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (pairEncode (bwAux S js n)
              ((firstQ (A.toCompOn (bitCodec ins outs 1) n (q.eval n) (pairFstD z) r)).elim
                (false :: List.replicate ((PolyExpr.add .var .var).eval n) false) (true :: ·)))
              (List.ofFn (chRun (fun y => plantAns S.enc L (pairEncode (seedIn n z (List.ofFn ω))
                  (pairEncode (bwAux S js n) (List.ofFn y))))
                (A.toCompOn (bitCodec ins outs 1) n (q.eval n) (pairFstD z) r) none).1)))) :
    advantage (hybGame S L hL hmsg A (q.eval n) n (js n))
        (hybGame S L hL hmsg A (q.eval n) n (js n + 1)) =
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n) := by
  -- Notation: the game's computation, `A`'s bit, and the planted padded tuple.
  let comp : S.gen.Coins n → A.Coins n →
      OracleComp ((S.bitwise.padded L hL hmsg).indSpec n) (Fin 1 → Bool) := fun rg r =>
    A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n (q.eval n)
      (pairFstD (S.gen.runAt n [] rg)) r
  let F : S.gen.Coins n → A.Coins n → List Bool → Bool := fun rg r w =>
    (chRun (fun _ => w) (comp rg r) none).1 0
  let W : Bool → S.gen.Coins n → (Fin n → S.enc.Coins n) → S.enc.Coins n → List Bool →
      List Bool := fun β rg v re l =>
    padCt (L.eval n) (PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
      if (i : ℕ) < js n then
        S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [l.getD (n + i) false]) (v i)
      else if (i : ℕ) = js n then
        S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [β]) re
      else S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [l.getD i false]) (v i)))
  -- The handler's lengths are the game's.
  have hins : (fun i => (qDin L (.add .var .var) i).eval n) =
      (S.bitwise.padded L hL hmsg).inLens n := by
    funext i
    match i with
    | 0 => rw [qDin_zero, FixedLengthPKScheme.inLens_zero, PublicKeyScheme.padded_ctLen]
    | 1 =>
      rw [qDin_one, FixedLengthPKScheme.inLens_one, PublicKeyScheme.padded_msgLen,
        PolyExpr.eval_add]
  have houts : (fun i => (qDout (.add .var (.const 1)) L i).eval n) =
      (S.bitwise.padded L hL hmsg).outLens n := by
    funext i
    match i with
    | 0 =>
      rw [qDout_zero, FixedLengthPKScheme.outLens_zero, PublicKeyScheme.padded_msgLen,
        PolyExpr.eval_add, PolyExpr.eval_const]
    | 1 => rw [qDout_one, FixedLengthPKScheme.outLens_one, PublicKeyScheme.padded_ctLen]
  -- The seed is `n` coin blocks.
  let seedE : (Fin n → S.enc.Coins n) ≃ (Fin ((PolyExpr.mul .var S.enc.coins).eval n) → Bool) :=
    (coinBlocks n (S.enc.coinLen n)).trans
      (Equiv.arrowCongr (finCongr (S.bitwise_enc_coinLen n)) (Equiv.refl Bool))
  have hseed : ∀ v, List.ofFn (seedE v) = List.ofFn (coinBlocks n (S.enc.coinLen n) v) :=
    fun v => (List.ofFn_congr (S.bitwise_enc_coinLen n) _).symm
  have hL' : ∀ (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m))
        re).length + 2 ≤ L.eval n := by
    have h := hL n
    rw [BitPublicKeyScheme.bitwise_gen] at h
    exact h
  -- The handler's answer to a challenge `l` is the planted padded tuple.
  have hans : ∀ (β : Bool) (rg : S.gen.Coins n) (re : S.enc.Coins n) (v : Fin n → S.enc.Coins n)
      (l : List Bool), l.length = n + n →
      plantAns S.enc L (pairEncode (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
        (pairEncode (bwAux S js n) l)) = W β rg v re l := by
    intro β rg re v l hl
    rw [plantAns_eq, BitPublicKeyScheme.pkEncDist_eq, hseed v, bwAux]
    conv_lhs => rw [ofFn_getD_split l hl]
    rw [plantTuple_spec S.enc S.enc_uniform n (js n) hj, seedIn_eq, pairFstD_pairEncode,
      pairFstD_pairEncode, List.length_replicate]
  have hw : ∀ (β : Bool) (rg : S.gen.Coins n) (re : S.enc.Coins n) (v : Fin n → S.enc.Coins n)
      (y : List Bool), y.length = (PolyExpr.add .var .var).eval n →
      (plantAns S.enc L (pairEncode (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
        (pairEncode (bwAux S js n) y))).length = L.eval n := by
    intro β rg re v y hy
    rw [PolyExpr.eval_add, PolyExpr.eval_var] at hy
    rw [hans β rg re v y hy]
    show (padCt (L.eval n) _).length = L.eval n
    refine length_padCt ?_
    rw [planted_eq S n (js n) hj, ← bitwise_runAt_blocks]
    exact hL' rg _ _
  -- Step 3, distinguisher side: `D`'s verdict.
  have hpt : ∀ (β : Bool) (rg : S.gen.Coins n) (r : A.Coins n) (re : S.enc.Coins n)
      (v : Fin n → S.enc.Coins n),
      D.distinguisherL n (S.pkEncDist n β (rg, re)) (φ (seedE v, r)) =
        (firstQ (comp rg r)).elim false fun l =>
          (l.getD (js n) false != l.getD (n + js n) false) &&
            (F rg r (W β rg v re l) != l.getD (js n) false) := by
    intro β rg r re v
    have hz : pairFstD (S.pkEncDist n β (rg, re)) = pairFstD (S.gen.runAt n [] rg) := by
      rw [BitPublicKeyScheme.pkEncDist_eq, pairFstD_pairEncode]
    have ha : List.ofFn (chRun (fun y => plantAns S.enc L (pairEncode
        (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
          (pairEncode (bwAux S js n) (List.ofFn y))))
        (A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n (q.eval n)
          (pairFstD (S.gen.runAt n [] rg)) r) none).1 =
        [F rg r ((firstQ (comp rg r)).elim [] fun l => plantAns S.enc L (pairEncode
          (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
            (pairEncode (bwAux S js n) l)))] := by
      rw [chRun_congr _ (fun _ => (firstQ (comp rg r)).elim [] fun l => plantAns S.enc L
        (pairEncode (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
          (pairEncode (bwAux S js n) l))) _ fun mm hmm => by rw [hmm, Option.elim_some],
        List.ofFn_succ, List.ofFn_zero]
    have hrun : D.runAt n (S.pkEncDist n β (rg, re)) (φ (seedE v, r)) =
        [(firstQ (comp rg r)).elim false fun l =>
          (l.getD (js n) false != l.getD (n + js n) false) &&
            (F rg r (W β rg v re l) != l.getD (js n) false)] := by
      rw [hφ _ _ hins houts _ _ _ (hw β rg re v), hz, ← AdaptiveCPA.indCodec_eq_bitCodec, ha]
      cases hq : firstQ (comp rg r) with
      | none => simp only [Option.elim_none, plantOut_init]
      | some l =>
        have hl : l.length = n + n := by
          rw [length_of_firstQ_eq_some _ hq, FixedLengthPKScheme.inLens_one,
            PublicKeyScheme.padded_msgLen, PolyExpr.eval_var]
        simp only [Option.elim_some]
        rw [hans β rg re v l hl, bwAux, plantOut_recorded, List.headD_cons]
    rw [NUPPT.distinguisherL_eq, hrun]
    generalize ((firstQ (comp rg r)).elim false fun l =>
      (l.getD (js n) false != l.getD (n + js n) false) &&
        (F rg r (W β rg v re l) != l.getD (js n) false)) = x
    cases x <;> rfl
  have hD : ∀ β : Bool, acceptProb (S.pkEncDist n β) (D.distinguisherL n) =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (Fin n → S.enc.Coins n)) fun v =>
            expect (ProbComp.sample (S.enc.Coins n)) fun re =>
              if ((firstQ (comp rg r)).elim false fun l =>
                (l.getD (js n) false != l.getD (n + js n) false) &&
                  (F rg r (W β rg v re l) != l.getD (js n) false)) = true then 1 else 0 := by
    intro β
    rw [Bridge.acceptProb_eq, accept_eq, Bridge.acceptGame_eq, prob_bind, expect_sample_prod]
    refine congrArg _ (funext fun rg => ?_)
    simp only [prob_bind, prob_pure]
    rw [expect_sample_comm, ← expect_sample_equiv φ, expect_sample_prod, expect_sample_comm]
    refine congrArg _ (funext fun r => ?_)
    rw [← expect_sample_equiv seedE]
    refine congrArg _ (funext fun v => congrArg _ (funext fun re => ?_))
    rw [hpt β rg r re v]
  -- Step 3, hybrid side: only the first challenge matters.
  have hH : ∀ j' : ℕ, accept (hybGame S L hL hmsg A (q.eval n) n j') =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (Fin n → S.enc.Coins n)) fun v =>
            if F rg r ((firstQ (comp rg r)).elim [] fun l =>
              padCt (L.eval n) (hybCt S n j' (pairFstD (S.gen.runAt n [] rg)) v l)) = true
            then 1 else 0 := by
    intro j'
    rw [accept_eq]
    unfold hybGame
    rw [prob_bind]
    refine congrArg _ (funext fun rg => ?_)
    rw [prob_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [prob_bind]
    refine congrArg _ (funext fun v => ?_)
    rw [prob_pure]
    congr 2
    exact congrArg (fun p : (Fin 1 → Bool) ×
        Option (Fin ((S.bitwise.padded L hL hmsg).outLens n 1) → Bool) => p.1 0)
      (chRun_congr _ _ _ fun mm hmm => by rw [hmm, Option.elim_some])
  -- Assemble: both differences are `𝔼_{rg, r}` of equal pointwise differences.
  rw [advantage_eq, distAdv_def, hH (js n), hH (js n + 1), hD false, hD true]
  congr 1
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun rg => ?_)
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun r => ?_)
  cases hq : firstQ (comp rg r) with
  | none => simp only [Option.elim_none, Bool.false_eq_true, if_false, sub_self]
  | some l =>
    simp only [Option.elim_some]
    rw [← expect_sample_update (⟨js n, hj⟩ : Fin n) (fun v => if F rg r (padCt (L.eval n)
        (hybCt S n (js n) (pairFstD (S.gen.runAt n [] rg)) v l)) = true then (1 : ℝ) else 0),
      ← expect_sample_update (⟨js n, hj⟩ : Fin n) (fun v => if F rg r (padCt (L.eval n)
        (hybCt S n (js n + 1) (pairFstD (S.gen.runAt n [] rg)) v l)) = true then (1 : ℝ) else 0)]
    have h₀ := fun v re =>
      hybCt_update S n (js n) hj (pairFstD (S.gen.runAt n [] rg)) v re l false
    have h₁ := fun v re =>
      hybCt_update S n (js n) hj (pairFstD (S.gen.runAt n [] rg)) v re l true
    simp only [Bool.false_eq_true, if_false, if_true] at h₀ h₁
    simp only [h₀, h₁]
    have key := expect_indicator_sub (ρ := (Fin n → S.enc.Coins n) × S.enc.Coins n)
      (fun β p => F rg r (W β rg p.1 p.2 l)) (l.getD (js n) false) (l.getD (n + js n) false)
    rw [expect_sample_prod, expect_sample_prod, expect_sample_prod, expect_sample_prod] at key
    exact key

end BitwiseCPAProof

/-- **The padded bitwise scheme is CPA-secure** when its single-bit scheme is secure
[PS10, the hybrid argument of p. 103, in the CPA game of Definition 171.5]. The bound `hL`
covers every ciphertext of the bitwise scheme, so `S.bitwise.padded L hL hmsg` has `n`-bit
messages and `L(n)`-bit ciphertexts.

**Proof sketch.**
1. Fix `A` and `q`. For `j ≤ n` let `H_j` be the CPA experiment whose challenge encrypts, bit by
   bit with independent coins `v_i`, the first `j` bits of the right message and the remaining
   bits of the left message (`hybGame`, with the encryption coins sampled in advance). `H_0` and
   `H_n` have the acceptance probabilities of the experiments with `b = false` and `b = true`
   (`accept_indGame_eq`: eager coins `BitwiseSim.expect_simulate_indImpl_cpa`, the bitwise
   layout `bitwise_enc_runAtL` and the coin blocks `bitwiseEncCoins_ofFn`).
2. By `Games.exists_advantage_hybrid_gap`, at each `n > 0` some `j⋆(n) < n` has
   `advantage(H_{j⋆}, H_{j⋆+1}) ≥ advantage(H_0, H_n) / n`; at `n = 0` the two ends coincide and
   the advantage is `0`.
3. The distinguisher `D` on `⟨pk, c⟩` runs `A` on `pk`, answers every `Dec` query with `⊥`, answers
   the first challenge `⟨m₀, m₁⟩` (and every later one) with the padded bitwise ciphertext whose
   block `j⋆` is `c` and whose other blocks it encrypts itself (bits of `m₁` before `j⋆`, of `m₀`
   after) on `pk` and its seed of `n` single-bit encryption tapes (`BitwiseSim.plantAns`), and
   outputs `A`'s bit, flipped when `(m₀_{j⋆}, m₁_{j⋆}) = (1, 0)` and replaced by `0` when the two
   bits agree or no challenge was asked (`BitwiseSim.plantOut`). `D` is a machine by T1 for the
   query-recording handler with `j⋆(n)` in its initial state (`BitwiseSim.exists_qHandlerMachine`).
   Then `advantage(H_{j⋆}, H_{j⋆+1})` equals `D`'s single-bit advantage between `⟨pk, Enc_pk(0)⟩`
   and `⟨pk, Enc_pk(1)⟩` exactly (`hyb_advantage_eq`): only the first challenge matters
   (`ChallengeSim.chRun_congr`); resampling coin block `j⋆` turns the two hybrids into the
   planted tuples with `Enc(m₀_{j⋆})` and `Enc(m₁_{j⋆})` (`BitwiseSim.expect_sample_update`); and
   the signed case split on `(m₀_{j⋆}, m₁_{j⋆})` is `ChallengeSim.expect_indicator_sub`.
4. So `A`'s advantage is at most `n` times `D`'s advantage, negligible by `singleBitSecure_iff`;
   the product is negligible by `Negligible.polyExpr_mul` with `PolyExpr.var`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).INDSecure .cpa := by
  rw [FixedLengthPKScheme.INDSecure_iff]
  intro A q
  -- Steps 1–2: the hybrids and, for `n > 0`, an index `j⋆(n) < n` of a largest gap.
  have hgap : ∀ n, ∃ j ≤ n, 0 < n → j < n ∧
      advantage (hybGame S L hL hmsg A (q.eval n) n 0) (hybGame S L hL hmsg A (q.eval n) n n) /
          n ≤
        advantage (hybGame S L hL hmsg A (q.eval n) n j)
          (hybGame S L hL hmsg A (q.eval n) n (j + 1)) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨j, hj, hgj⟩ := exists_advantage_hybrid_gap (hybGame S L hL hmsg A (q.eval n) n) hn
      exact ⟨j, hj.le, fun _ => ⟨hj, hgj⟩⟩
    · exact ⟨0, Nat.zero_le _, fun h => absurd h hn⟩
  choose js hjle hjs using hgap
  -- Step 2: the distinguisher `D`, by T1 for the query-recording handler.
  obtain ⟨D, hD⟩ := BitwiseSim.exists_qHandlerMachine A q L (.add .var .var) (.add .var (.const 1))
    (bwLaux S) (.mul .var S.enc.coins) (bwAux S js) (bwAux_length S js hjle)
    (BitwiseSim.plantAns S.enc L) (BitwiseSim.polyTimeComputable_plantAns S.enc L)
    BitwiseSim.plantOut BitwiseSim.polyTimeComputable_plantOut
  refine ⟨fun n => (PolyExpr.var.eval n : ℝ) *
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n),
    ((BitPublicKeyScheme.singleBitSecure_iff S).1 h D).polyExpr_mul .var, fun n => ?_⟩
  -- Step 1: the ends of the hybrids are the two games.
  rw [advantage_eq, accept_indGame_eq, accept_indGame_eq, ← advantage_eq]
  simp only [Bool.false_eq_true, ↓reduceIte, PolyExpr.eval_var]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [advantage_eq, sub_self, abs_zero, Nat.cast_zero, zero_mul]
  · -- Steps 3–4: the exact identity and the bound `n · ε(n)`.
    obtain ⟨φ, hφ⟩ := hD n
    rw [← hyb_advantage_eq L hL hmsg A q js D n (hjs n hn).1 φ hφ]
    have h1 := (hjs n hn).2
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn'] at h1
    linarith

/-- **The padded bitwise scheme is adaptively CPA-secure** when its single-bit scheme is secure:
`bitwise_padded_cpa` followed by the hybrid lifting
`Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_adaptive_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).AdaptiveINDSecure .cpa :=
  (h.bitwise_padded_cpa L hL hmsg).adaptive_cpa

/-- **A secure single-bit scheme yields an adaptively CPA-secure scheme with `n`-bit messages**:
some fixed-length scheme with message length `PolyExpr.var` and the same key generator is
secure in the adaptive multi-challenge CPA game. The padding bound comes from
`PublicKeyScheme.exists_padBound`.

**Proof sketch.** Take `L`, `hL` and `hmsg` from `S.bitwise.exists_padBound`; the witness is
`S.bitwise.padded L hL hmsg` (`PublicKeyScheme.padded_msgLen`, `PublicKeyScheme.padded_gen`, and
the generator of `S.bitwise` is `S.gen`), secure by `bitwise_padded_adaptive_cpa`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) :
    ∃ S' : FixedLengthPKScheme, S'.msgLen = .var ∧ S'.gen = S.gen ∧
      S'.AdaptiveINDSecure .cpa := by
  obtain ⟨L, hL, hmsg⟩ := S.bitwise.exists_padBound
  exact ⟨S.bitwise.padded L hL hmsg, PublicKeyScheme.padded_msgLen _ _ _ _,
    (PublicKeyScheme.padded_gen _ _ _ _).trans (BitPublicKeyScheme.bitwise_gen S),
    h.bitwise_padded_adaptive_cpa L hL hmsg⟩

end TCSlib.Cryptography.Composability

## ===== TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Eager.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Eager challenge coins and readers for the CPA game

Generic facts used by the hybrid argument for the bitwise scheme under chosen-plaintext attack
[PS10, p. 103, in the game of Definition 171.5]: under CPA the encryption coins of the challenge
may be sampled in advance (`expect_simulate_indImpl_cpa`, through the oracle equations
`indImpl_*_onSpec`); resampling one coordinate of a uniform tuple leaves it uniform
(`expect_sample_update`); and the padded encryptor of a padded public-key scheme pads the
original encryptor's output (`padded_enc_runAt`). All are read from the published lemmas of
`OracleSecurity` and `ChallengeSim`. The CPA game's codec is the bit codec of the scheme's
lengths by `AdaptiveCPA.indCodec_eq_bitCodec`, and casts are read by `AdaptiveCPA.ofFn_cast`.

## Main results

* `BitwiseSim.expect_simulate_eager`, `expect_simulate_indImpl_cpa`: eager challenge coins under
  CPA, generically and for `indImpl`.
* `BitwiseSim.expect_sample_update`: resampling a coordinate.
* `BitwiseSim.padded_enc_runAt`, `BitwiseSim.padded_enc_coins`: readers of the padded scheme.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 and §7.1.4, Definition 171.5 (book p. 171).
-/

namespace TCSlib.Cryptography.Composability.BitwiseSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim ProbComp

/-- **Eager challenge coins, for any CPA-shaped oracle.** Let `impl` answer oracle `0`
all-`false`, a challenge from a recorded state `c` with `c`, and the first challenge `mm` by
sampling `re` and answering (and recording) `padFin d (g mm re)`; the state holds `d`-bit
strings, `d = outs 1`, read through the cast `e`. Then for every `G`,
`𝔼[G ∘ fst] (simulate impl c s) = 𝔼_{re} G (chRun (fun mm => g mm re) c (s.map (cast e))).1`.

**Proof sketch.** Substitute `d = outs 1`, so that the casts are identities. Induction on the
computation: decryption queries and repeated challenges are deterministic in both; at the first
challenge the lazy side samples `re` and continues from the recorded answer, by the induction
hypothesis an average over coins `re'` on which the recorded run does not depend
(`chRun_some_congr`), so `re'` marginalizes out (`expect_const`). -/
theorem expect_simulate_eager {ins outs : Fin 2 → ℕ} {d : ℕ} (hd : outs 1 = d)
    (e : (Fin d → Bool) = (Fin (outs 1) → Bool)) {R : Type} [Fintype R] [Nonempty R]
    (impl : QueryImpl (bitSpec ins outs) (Option (Fin d → Bool)) unifSpec)
    (g : (Fin (ins 1) → Bool) → R → List Bool)
    (h0 : ∀ x s, impl 0 x s = .pure (zeroBits _, s))
    (hrep : ∀ mm c, impl 1 mm (some c) = .pure (cast e c, some c))
    (hnew : ∀ mm, impl 1 mm none = (ProbComp.sample R).bind fun re =>
      .pure (cast e (padFin d (g mm re)), some (padFin d (g mm re))))
    {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α) (s : Option (Fin d → Bool)) :
    expect (simulate impl c s) (fun p => G p.1) =
      expect (ProbComp.sample R) fun re =>
        G (chRun (fun mm => g mm re) c (s.map (cast e))).1 := by
  subst hd
  have hc : ∀ x : Fin (outs 1) → Bool, cast e x = x := fun x => cast_eq e x
  have hmap : ∀ s : Option (Fin (outs 1) → Bool), s.map (cast e) = s := fun s => by
    cases s <;> simp
  simp only [hc] at hrep hnew
  simp only [hmap]
  induction c generalizing s with
  | pure a =>
    rw [simulate_pure, expect_pure]
    simp only [chRun_pure]
    exact (expect_const _ _).symm
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, h0, OracleComp.pure_bind]
      simp only [chRun_query_zero]
      exact ih _ s
    | 1, x, k, ih =>
      cases s with
      | some C =>
        rw [simulate_query, hrep, OracleComp.pure_bind]
        simp only [chRun_query_one_some]
        exact ih _ _
      | none =>
        rw [simulate_query, hnew, OracleComp.bind_assoc, expect_bind]
        refine congrArg _ (funext fun re => ?_)
        rw [OracleComp.pure_bind, ih, chRun_query_one_none]
        dsimp only
        exact (congrArg _ (funext fun re' =>
          congrArg (fun p : α × Option (Fin (outs 1) → Bool) => G p.1)
            (chRun_some_congr (fun mm => g mm re') (fun mm => g mm re) _ _))).trans
          (expect_const _ _)

/-- **Eager challenge coins under CPA.** Simulating the oracles of `Ind_b` from the unchallenged
state has, for every `G`, the expectation of first sampling the encryption coins `re` and then
running the deterministic oracles whose challenge `mm` is answered with `Enc(⟨pk, m_b⟩; re)`,
the halves read through `indSpec_challengeDom`:
`𝔼[G ∘ fst] (simulate (indImpl .cpa b n pk sk) c none) = 𝔼_{re} G (chRun g_re c none).1`.

**Proof sketch.** `expect_simulate_eager` with `d = ctLen(n)` (`outLens_one`), the cast
`indSpec_challengeRng`, and the oracle equations `indImpl_dec_onSpec` (with `decOpen_cpa`),
`indImpl_challenge_repeat_onSpec` and `indImpl_challenge_none_onSpec`. -/
theorem expect_simulate_indImpl_cpa (S : FixedLengthPKScheme) (b : Bool) (n : ℕ)
    (pk sk : List Bool) {α : Type} (G : α → ℝ) (c : OracleComp (S.indSpec n) α) :
    expect (simulate (S.indImpl .cpa b n pk sk) c none) (fun p => G p.1) =
      expect (ProbComp.sample (S.enc.Coins n)) fun re =>
        G (chRun (fun mm => S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).2
            else (FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)).1))) re)
          c none).1 :=
  expect_simulate_eager (S.outLens_one n) (S.indSpec_challengeRng n).symm _ _
    (fun x s => by
      rw [S.indImpl_dec_onSpec]
      simp only [FixedLengthScheme.decOpen_cpa, Bool.false_and, Bool.false_eq_true, if_false])
    (fun mm C => S.indImpl_challenge_repeat_onSpec .cpa b n pk sk mm C)
    (fun mm => S.indImpl_challenge_none_onSpec .cpa b n pk sk mm) G c none

/-- **Resampling one coordinate of a uniform tuple leaves it uniform**:
`𝔼_{v} 𝔼_{b} f (update v j b) = 𝔼_{v} f v`.

**Proof sketch.** The map `(v, b) ↦ (update v j b, v j)` is an involution of
`(ι → β) × β` (`Function.update_idem`, `Function.update_eq_self`); reindexing the product sample
along it (`expect_sample_equiv`, `expect_sample_prod`) turns the left side into
`𝔼_{v} 𝔼_{b} f v = 𝔼_{v} f v` (`expect_const`). -/
theorem expect_sample_update {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [Nonempty β]
    (j : ι) (f : (ι → β) → ℝ) :
    (expect (sample (ι → β)) fun v => expect (sample β) fun b => f (Function.update v j b)) =
      expect (sample (ι → β)) f := by
  let e : (ι → β) × β ≃ (ι → β) × β :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  rw [← expect_sample_prod (fun p : (ι → β) × β => f (Function.update p.1 j p.2))]
  have h := expect_sample_equiv e (fun p : (ι → β) × β => f p.1)
  refine h.trans ?_
  rw [expect_sample_prod]
  exact congrArg _ (funext fun v => expect_const (sample β) (f v))

/-- **The padded encryptor pads the original encryptor's output**: for a padded public-key
scheme, `Enc'(1^n, y; r) = padCt L(n) (Enc(1^n, y; r))`, with the coin string read as a list
(`PublicKeyScheme.padded_enc`, `runAt_padEnc`, `NUPPT.coinsCongr_ofFn`). -/
theorem padded_enc_runAt (S : PublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) (n : ℕ) (y : List Bool)
    (r : (S.padded L hL hmsg).enc.Coins n) :
    (S.padded L hL hmsg).enc.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
  have key : ∀ E : NUPPT, E = padEnc S.enc L → ∀ r : E.Coins n,
      E.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
    rintro E rfl r
    rw [runAt_padEnc S.enc_uniform L n y r, NUPPT.runAt_eq, NUPPT.coinsCongr_ofFn]
  exact key _ (PublicKeyScheme.padded_enc S L hL hmsg) r

/-- The padded scheme's encryptor has the coin polynomial of the original encryptor:
`S.enc.coins = (S.padded L hL hmsg).enc.coins`. -/
theorem padded_enc_coins (S : PublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : S.enc.coins = (S.padded L hL hmsg).enc.coins := by
  rw [PublicKeyScheme.padded_enc, padEnc_coins]

end TCSlib.Cryptography.Composability.BitwiseSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Planted.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.HybridMachine
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The planted bitwise ciphertext of the hybrid reduction

In the hybrid argument for the bitwise scheme under chosen-plaintext attack [PS10, p. 103, in
the game of Definition 171.5], the reduction holds a single-bit challenge ciphertext `c` and
answers the adversary's challenge `⟨m₀, m₁⟩` with the tuple whose block `j` is `c`, whose
blocks before `j` encrypt the bits of `m₁` and whose blocks after `j` encrypt the bits of `m₀`,
each with its own coin block. This file builds that answer, padded, as a polynomial-time string
function of the reduction's context and advice (`plantAns`), and the reduction's final bit
(`plantOut`), with their unfoldings.

## Main definitions

* `BitwiseSim.plantTuple`: the planted tuple, from the block encryptor `blockEncFun`.
* `BitwiseSim.plantAns`: the planted tuple padded with `padCt`.
* `BitwiseSim.plantOut`: the final bit, from the recorded bits `m₀_j`, `m₁_j`.

## Main results

* `BitwiseSim.plantTuple_spec`: the planted tuple on the hybrid layout.
* `BitwiseSim.plantOut_init`, `plantOut_recorded`: the final bit.
* `BitwiseSim.polyTimeComputable_plantAns`, `polyTimeComputable_plantOut`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 (the bitwise scheme and the hybrid argument) and §7.1.4, Definition 171.5.
-/

namespace TCSlib.Cryptography.Composability.BitwiseSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### List identities -/

/-- `List.ofFn` of a constant on a one-element type is a singleton:
`List.ofFn (fun _ : Fin p => b) = [b]` when `p = 1`. -/
theorem ofFn_const_of_eq_one {p : ℕ} (hp : p = 1) (b : Bool) :
    List.ofFn (fun _ : Fin p => b) = [b] := by
  subst hp
  rfl

/-- Flattening singletons: `(List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten =
List.ofFn f` when `p = 1`. -/
theorem flatten_ofFn_singleton {p : ℕ} (hp : p = 1) :
    ∀ {k : ℕ} (f : Fin k → Bool),
      (List.ofFn fun i => List.ofFn fun _ : Fin p => f i).flatten = List.ofFn f := by
  intro k
  induction k with
  | zero => intro f; rfl
  | succ k ih =>
    intro f
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, ih (fun i => f i.succ),
      ofFn_const_of_eq_one hp]
    rfl

/-- The first `j` bits of `List.ofFn m`, as a flattening of singletons (`p = 1`):
`(ofFn m).take j = (ofFn fun i : Fin j => ofFn fun _ : Fin p => m i).flatten`. -/
theorem take_ofFn_flatten {p n j : ℕ} (hp : p = 1) (m : Fin n → Bool) (hj : j ≤ n) :
    (List.ofFn m).take j =
      (List.ofFn fun i : Fin j => List.ofFn fun _ : Fin p => m (Fin.castLE hj i)).flatten := by
  rw [flatten_ofFn_singleton hp]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
    omega
  · intro t h₁ h₂
    simp only [List.getElem_take, List.getElem_ofFn]
    rfl

/-- The bits of `List.ofFn m` after the first `j + 1`, as a flattening of singletons (`p = 1`):
`(ofFn m).drop (j + 1) =
(ofFn fun i : Fin (n - j - 1) => ofFn fun _ : Fin p => m (j + 1 + i)).flatten`. -/
theorem drop_ofFn_flatten {p n j : ℕ} (hp : p = 1) (m : Fin n → Bool) (hj : j < n) :
    (List.ofFn m).drop (j + 1) =
      (List.ofFn fun i : Fin (n - j - 1) => List.ofFn fun _ : Fin p =>
        m ⟨j + 1 + i, by omega⟩).flatten := by
  rw [flatten_ofFn_singleton hp]
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_ofFn]
    omega
  · intro t h₁ h₂
    simp only [List.getElem_drop, List.getElem_ofFn]

/-- The head of a suffix is an entry: `(l.drop k).headD false = l.getD k false`. -/
theorem headD_drop (l : List Bool) (k : ℕ) : (l.drop k).headD false = l.getD k false := by
  induction l generalizing k with
  | nil => simp
  | cons b l ih => cases k <;> simp

/-! ### The planted tuple -/

/-- **The planted tuple** on `⟨⟨u, ⟨⟨pk, c⟩, ω⟩⟩, ⟨⟨u_j, ⟨u_b, Z⟩⟩, x⟩⟩` (unary parameter
`u = 1^n`, public key `pk`, single-bit ciphertext `c`, coins `ω`, `u_j = 1^j`,
`u_b = 1^{(j+1)·B(n)}`, challenge `x = m₀ ‖ m₁`): `T₁ ++ ⟨c, T₂⟩`, where `T₁` is the block
encryption (`blockEncFun`, one-bit blocks) of the first `j` bits of `m₁` with the coins `ω`,
and `T₂` that of the bits of `m₀` after the first `j + 1` with the coins of `ω` after the first
`(j + 1)·B(n)`. -/
def plantTuple (Enc : NUPPT) (w : List Bool) : List Bool :=
  blockEncFun Enc.output (.const 1) Enc.coins
      (blockState (pairFstD (pairFstD w)) (pairFstD (pairFstD (pairSndD (pairFstD w))))
        (((pairSndD (pairSndD w)).drop (pairFstD (pairFstD w)).length).take
          (pairFstD (pairFstD (pairSndD w))).length)
        (pairSndD (pairSndD (pairFstD w)))) ++
    pairEncode (pairSndD (pairFstD (pairSndD (pairFstD w))))
      (blockEncFun Enc.output (.const 1) Enc.coins
        (blockState (pairFstD (pairFstD w)) (pairFstD (pairFstD (pairSndD (pairFstD w))))
          (((pairSndD (pairSndD w)).take (pairFstD (pairFstD w)).length).drop
            ((pairFstD (pairFstD (pairSndD w))).length + 1))
          ((pairSndD (pairSndD (pairFstD w))).drop
            (pairFstD (pairSndD (pairFstD (pairSndD w)))).length)))

/-- The defining equation of `plantTuple`. -/
theorem plantTuple_eq (Enc : NUPPT) (w : List Bool) :
    plantTuple Enc w =
      blockEncFun Enc.output (.const 1) Enc.coins
          (blockState (pairFstD (pairFstD w)) (pairFstD (pairFstD (pairSndD (pairFstD w))))
            (((pairSndD (pairSndD w)).drop (pairFstD (pairFstD w)).length).take
              (pairFstD (pairFstD (pairSndD w))).length)
            (pairSndD (pairSndD (pairFstD w)))) ++
        pairEncode (pairSndD (pairFstD (pairSndD (pairFstD w))))
          (blockEncFun Enc.output (.const 1) Enc.coins
            (blockState (pairFstD (pairFstD w)) (pairFstD (pairFstD (pairSndD (pairFstD w))))
              (((pairSndD (pairSndD w)).take (pairFstD (pairFstD w)).length).drop
                ((pairFstD (pairFstD (pairSndD w))).length + 1))
              ((pairSndD (pairSndD (pairFstD w))).drop
                (pairFstD (pairSndD (pairFstD (pairSndD w)))).length))) := rfl

/-- The planted tuple is polynomial-time.

**Proof sketch.** Pair projections for the slots; `polyTimeComputable_pairTakePoly` and
`polyTimeComputable_pairDropPoly` (`p := var`) cut the challenge and the coins at the unary
lengths; `blockEncFun_poly` encrypts; `append` and `pairEncode` assemble. -/
theorem polyTimeComputable_plantTuple (Enc : NUPPT) : PolyTimeComputable (plantTuple Enc) := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  have hu := hF.comp hF
  have hpk := hF.comp (hF.comp (hS.comp hF))
  have hc := hS.comp (hF.comp (hS.comp hF))
  have hω := hS.comp (hS.comp hF)
  have huj := hF.comp (hF.comp hS)
  have hub := hF.comp (hS.comp (hF.comp hS))
  have hx := hS.comp hS
  have hm₁ := (polyTimeComputable_pairDropPoly .var).comp (hu.pairEncode hx)
  have hm₀ := (polyTimeComputable_pairTakePoly .var).comp (hu.pairEncode hx)
  have hM₁ := (polyTimeComputable_pairTakePoly .var).comp (huj.pairEncode hm₁)
  have hM₂ := (polyTimeComputable_pairDropPoly .var).comp
    (((polyTimeComputable_const [true]).append huj).pairEncode hm₀)
  have hω₂ := (polyTimeComputable_pairDropPoly .var).comp (hub.pairEncode hω)
  have hE := blockEncFun_poly Enc.polyTimeComputable_output (.const 1) Enc.coins
  have hT₁ := hE.comp (hu.pairEncode (hpk.pairEncode (hM₁.pairEncode hω)))
  have hT₂ := hE.comp (hu.pairEncode (hpk.pairEncode (hM₂.pairEncode hω₂)))
  have h := hT₁.append (hc.pairEncode hT₂)
  refine h.congr fun w => ?_
  simp only [plantTuple_eq, blockState_eq, Function.comp_apply, pairFstD_pairEncode,
    pairSndD_pairEncode, PolyExpr.eval_var, List.cons_append, List.nil_append, List.length_cons]

/-- **The planted tuple on the hybrid layout.** With `u = 1^n`, coins `ω = coinBlocks v` (the
blocks `v_i` of `Enc`), `u_j = 1^j`, `u_b = 1^{(j+1)·B(n)}` (`j < n`) and challenge
`List.ofFn m₀ ++ List.ofFn m₁`, the planted tuple is the tuple
`⟨c_0, …, c_{n-1}⟩` with `c_i = Enc(1^n, ⟨pk, [m₁ i]⟩; v_i)` for `i < j`, `c_j = c`, and
`c_i = Enc(1^n, ⟨pk, [m₀ i]⟩; v_i)` for `i > j`.

**Proof sketch.** The cut challenge pieces are flattenings of singletons
(`take_ofFn_flatten`, `drop_ofFn_flatten`), so `blockEncFun_flatten` unfolds both block
encryptions with coin segments `coinBlock B i ω` and `coinBlock B i (ω.drop ((j+1)·B))`; these
are the blocks `v_i` and `v_{j+1+i}` (`coinBlock_ofFn_coinBlocks`, `coinBlock_drop`), and the
whole tuple splits at `j` (`encodeList_ofFn_split`). -/
theorem plantTuple_spec (Enc : NUPPT) (hEnc : Enc.Uniform) (n j : ℕ) (hj : j < n)
    (pk c Z : List Bool) (v : Fin n → Enc.Coins n) (m₀ m₁ : Fin n → Bool) :
    plantTuple Enc (pairEncode
        (seedIn n (pairEncode pk c) (List.ofFn (coinBlocks n (Enc.coinLen n) v)))
        (pairEncode (pairEncode (List.replicate j true)
            (pairEncode (List.replicate ((j + 1) * Enc.coinLen n) true) Z))
          (List.ofFn m₀ ++ List.ofFn m₁))) =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        if (i : ℕ) < j then Enc.runAt n (pairEncode pk [m₁ i]) (v i)
        else if (i : ℕ) = j then c
        else Enc.runAt n (pairEncode pk [m₀ i]) (v i)) := by
  have h1 : (PolyExpr.const 1).eval n = 1 := PolyExpr.eval_const 1 n
  have hlen : (List.ofFn m₀).length = n := List.length_ofFn
  simp only [plantTuple_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
  rw [List.drop_left' hlen, List.take_left' hlen, take_ofFn_flatten h1 m₁ hj.le,
    drop_ofFn_flatten h1 m₀ hj,
    blockEncFun_flatten Enc hEnc (.const 1) n (by rw [h1]; exact Nat.one_pos) pk j,
    blockEncFun_flatten Enc hEnc (.const 1) n (by rw [h1]; exact Nat.one_pos) pk (n - j - 1),
    encodeList_ofFn_split _ ⟨j, hj⟩]
  congr 1
  · refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
    have hi : (i : ℕ) < j := i.isLt
    rw [ofFn_const_of_eq_one h1, ← Fin.coe_castLE hj.le i, coinBlock_ofFn_coinBlocks,
      ← NUPPT.runAt_eq]
    simp only [Fin.coe_castLE, hi, if_true]
  · congr 1
    · simp
    · refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
      have hidx : coinBlock (Enc.coinLen n) (j + 1 + i)
          (List.ofFn (coinBlocks n (Enc.coinLen n) v)) =
          List.ofFn (v ⟨j + 1 + i, by have := i.isLt; omega⟩) :=
        coinBlock_ofFn_coinBlocks n (Enc.coinLen n) v ⟨j + 1 + i, by have := i.isLt; omega⟩
      rw [ofFn_const_of_eq_one h1, coinBlock_drop, hidx, ← NUPPT.runAt_eq]
      simp only [Fin.val_mk]
      rw [if_neg (by omega), if_neg (by omega)]

/-! ### The padded answer -/

/-- **The reduction's challenge answer**: the planted tuple padded to `L(n)` bits, with `n` read
from the unary parameter. -/
def plantAns (Enc : NUPPT) (L : PolyExpr) (w : List Bool) : List Bool :=
  padCt (L.eval (pairFstD (pairFstD w)).length) (plantTuple Enc w)

/-- The defining equation of `plantAns`. -/
theorem plantAns_eq (Enc : NUPPT) (L : PolyExpr) (w : List Bool) :
    plantAns Enc L w = padCt (L.eval (pairFstD (pairFstD w)).length) (plantTuple Enc w) := rfl

/-- The padded answer is polynomial-time (`padCt_eq`: the padding is a cut of `1^{L(n)}`). -/
theorem polyTimeComputable_plantAns (Enc : NUPPT) (L : PolyExpr) :
    PolyTimeComputable (plantAns Enc L) := by
  have ht := polyTimeComputable_plantTuple Enc
  have h := ht.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
    ((ht.pairEncode (polyTimeComputable_const [])).pairEncode
      ((polyTimeComputable_unaryPoly L).comp
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD))))
  refine h.congr fun w => ?_
  simp [plantAns_eq, padCt_eq, Function.comp_apply, length_pairEncode]

/-! ### The final bit -/

/-- **The reduction's final bit** on `⟨ctx, ⟨⟨aux, t⟩, a⟩⟩` with `ctx = ⟨1^n, …⟩`,
`aux = ⟨1^j, …⟩` and `t = asked :: x`: with `b₀ = x_j`, `b₁ = x_{n+j}` (the bits `m₀_j`, `m₁_j`
of the recorded challenge), `[a]` if `(b₀, b₁) = (0, 1)`, `[¬a]` if `(b₀, b₁) = (1, 0)`, and `[0]`
if `b₀ = b₁` or no challenge was asked. -/
def plantOut (w : List Bool) : List Bool :=
  if (pairSndD (pairFstD (pairSndD w))).headD false then
    if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop
        (pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then
      if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop ((pairFstD (pairFstD w)) ++
          pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then [false]
      else [!(pairSndD (pairSndD w)).headD false]
    else
      if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop ((pairFstD (pairFstD w)) ++
          pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then
        [(pairSndD (pairSndD w)).headD false]
      else [false]
  else [false]

/-- The defining equation of `plantOut`. -/
theorem plantOut_eq (w : List Bool) :
    plantOut w =
      if (pairSndD (pairFstD (pairSndD w))).headD false then
        if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop
            (pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then
          if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop ((pairFstD (pairFstD w)) ++
              pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then [false]
          else [!(pairSndD (pairSndD w)).headD false]
        else
          if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop ((pairFstD (pairFstD w)) ++
              pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then
            [(pairSndD (pairSndD w)).headD false]
          else [false]
      else [false] := rfl

/-- Without a recorded challenge the final bit is `[0]`:
`plantOut ⟨ctx, ⟨⟨aux, 0 :: y⟩, a⟩⟩ = [false]`. -/
theorem plantOut_init (ctx aux y a : List Bool) :
    plantOut (pairEncode ctx (pairEncode (pairEncode aux (false :: y)) a)) = [false] := by
  simp only [plantOut_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons,
    Bool.false_eq_true, if_false]

/-- With the challenge `l` recorded and the advice `⟨1^j, …⟩`, the final bit is
`(l_j ≠ l_{n+j}) ∧ (a ≠ l_j)`. -/
theorem plantOut_recorded (n j : ℕ) (z ω rest l a : List Bool) :
    plantOut (pairEncode (seedIn n z ω)
        (pairEncode (pairEncode (pairEncode (List.replicate j true) rest) (true :: l)) a)) =
      [(l.getD j false != l.getD (n + j) false) && (a.headD false != l.getD j false)] := by
  simp only [plantOut_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons,
    if_true, List.drop_succ_cons, List.drop_zero, List.length_append, List.length_replicate,
    headD_drop]
  cases l.getD j false <;> cases l.getD (n + j) false <;> cases a.headD false <;> rfl

/-- The final bit is polynomial-time. -/
theorem polyTimeComputable_plantOut : PolyTimeComputable plantOut := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  have ht : PolyTimeComputable fun w => pairSndD (pairFstD (pairSndD w)) := hS.comp (hF.comp hS)
  have hx : PolyTimeComputable fun w => (pairSndD (pairFstD (pairSndD w))).drop 1 :=
    polyTimeComputable_tail.comp ht
  have huj : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD (pairSndD w))) :=
    hF.comp (hF.comp (hF.comp hS))
  have hb₀ := polyTimeComputable_headD.comp
    ((polyTimeComputable_pairDropPoly .var).comp (huj.pairEncode hx))
  have hb₁ := polyTimeComputable_headD.comp
    ((polyTimeComputable_pairDropPoly .var).comp (((hF.comp hF).append huj).pairEncode hx))
  have ha : PolyTimeComputable fun w => [(pairSndD (pairSndD w)).headD false] :=
    polyTimeComputable_headD.comp (hS.comp hS)
  have h := polyTimeComputable_ite (polyTimeComputable_headD.comp ht)
    (polyTimeComputable_ite hb₀
      (polyTimeComputable_ite hb₁ (polyTimeComputable_const [false]) (polyTimeComputable_not ha))
      (polyTimeComputable_ite hb₁ ha (polyTimeComputable_const [false])))
    (polyTimeComputable_const [false])
  refine h.congr fun w => ?_
  simp only [plantOut_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var]

end TCSlib.Cryptography.Composability.BitwiseSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/QueryHandler.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A query-recording handler with advice

A reduction from CPA security whose challenge answer depends on the challenge query
[PS10, the hybrid argument of p. 103 in the game of Definition 171.5] runs the adversary once. It
answers every decryption query with `⊥` and the first challenge query `x` with a string computed
from its context, a fixed advice string `aux` and `x`; it records `x` and answers every later
challenge query as it answered the first. This file builds that handler as a `Games.PolyHandler`
(`qHandler`), generic in the lengths, the advice, the answer and the finalization, and combines
it with T1 (`Games.exists_handlerMachine`): the resulting machine's output is the finalization of
the deterministic run `ChallengeSim.chRun` with the answer function, on the advice and the
first challenge query (`exists_qHandlerMachine`).

## Main definitions

* `BitwiseSim.qDin`, `qDout`: the query and answer lengths of the two oracles.
* `BitwiseSim.qRun`: the handler's step as a string function.
* `BitwiseSim.qHandler`: the handler; its state is `⟨aux, asked :: x⟩`.

## Main results

* `BitwiseSim.simulate_qHandler_recorded`, `simulate_qHandler_init`: the handler's simulation is
  the deterministic run with the answer function, and its final state records the first
  challenge query.
* `BitwiseSim.chRun_toCompOn_transport_list`: transport of a run with a query-dependent answer
  along equal lengths.
* `BitwiseSim.exists_qHandlerMachine`: the machine of the handler, by T1.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 (the hybrid argument) and §7.1.4, Definition 171.5 (book p. 171).
-/

namespace TCSlib.Cryptography.Composability.BitwiseSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games ChallengeSim

/-! ### Lengths -/

/-- The query lengths: `Lc(n)`-bit ciphertexts to oracle `0` (decryption), `Lq(n)`-bit challenge
queries to oracle `1`. -/
def qDin (Lc Lq : PolyExpr) : Fin 2 → PolyExpr
  | 0 => Lc
  | 1 => Lq

/-- Decryption queries have `Lc(n)` bits: `qDin Lc Lq 0 = Lc`. -/
theorem qDin_zero (Lc Lq : PolyExpr) : qDin Lc Lq 0 = Lc := rfl

/-- Challenge queries have `Lq(n)` bits: `qDin Lc Lq 1 = Lq`. -/
theorem qDin_one (Lc Lq : PolyExpr) : qDin Lc Lq 1 = Lq := rfl

/-- The answer lengths: `Ld(n)`-bit decryption answers and `Lc(n)`-bit challenge ciphertexts. -/
def qDout (Ld Lc : PolyExpr) : Fin 2 → PolyExpr
  | 0 => Ld
  | 1 => Lc

/-- Decryption answers have `Ld(n)` bits: `qDout Ld Lc 0 = Ld`. -/
theorem qDout_zero (Ld Lc : PolyExpr) : qDout Ld Lc 0 = Ld := rfl

/-- Challenge answers have `Lc(n)` bits: `qDout Ld Lc 1 = Lc`. -/
theorem qDout_one (Ld Lc : PolyExpr) : qDout Ld Lc 1 = Lc := rfl

/-! ### The step function -/

/-- **One step of the handler** on `⟨ctx, ⟨s, ⟨1^i, x⟩⟩⟩` with state `s = ⟨aux, t⟩`. A challenge
query (`i = 1`) is answered with `ans ⟨ctx, ⟨aux, y⟩⟩`, where `y` is the recorded query
`t.drop 1` if the flag `t.headD false` is set, and `x` otherwise; in the second case the new
state is `⟨aux, 1 :: x⟩`, else the state is kept. A decryption query (`i = 0`) is answered with
the empty string (decoded as all-`false`) and keeps the state. -/
def qRun (ans : List Bool → List Bool) (w : List Bool) : List Bool :=
  if (pairFstD (pairSndD (pairSndD w))).headD false then
    if (pairSndD (pairFstD (pairSndD w))).headD false then
      pairEncode (ans (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
          ((pairSndD (pairFstD (pairSndD w))).drop 1))))
        (pairFstD (pairSndD w))
    else
      pairEncode (ans (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
          (pairSndD (pairSndD (pairSndD w))))))
        (pairEncode (pairFstD (pairFstD (pairSndD w))) (true :: pairSndD (pairSndD (pairSndD w))))
  else pairEncode [] (pairFstD (pairSndD w))

/-- The defining equation of `qRun`. -/
theorem qRun_eq (ans : List Bool → List Bool) (w : List Bool) :
    qRun ans w =
      if (pairFstD (pairSndD (pairSndD w))).headD false then
        if (pairSndD (pairFstD (pairSndD w))).headD false then
          pairEncode (ans (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
              ((pairSndD (pairFstD (pairSndD w))).drop 1))))
            (pairFstD (pairSndD w))
        else
          pairEncode (ans (pairEncode (pairFstD w) (pairEncode (pairFstD (pairFstD (pairSndD w)))
              (pairSndD (pairSndD (pairSndD w))))))
            (pairEncode (pairFstD (pairFstD (pairSndD w)))
              (true :: pairSndD (pairSndD (pairSndD w))))
      else pairEncode [] (pairFstD (pairSndD w)) := rfl

/-- A decryption query is answered with the empty string and keeps the state:
`qRun ans ⟨ctx, ⟨s, ⟨[], x⟩⟩⟩ = ⟨[], s⟩`. -/
theorem qRun_dec (ans : List Bool → List Bool) (ctx s x : List Bool) :
    qRun ans (pairEncode ctx (pairEncode s (pairEncode [] x))) = pairEncode [] s := by
  simp only [qRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_nil,
    Bool.false_eq_true, if_false]

/-- The first challenge query `x` (flag unset) is answered with `ans ⟨ctx, ⟨aux, x⟩⟩` and recorded
as the state `⟨aux, 1 :: x⟩`. -/
theorem qRun_fresh (ans : List Bool → List Bool) (ctx aux t x : List Bool)
    (ht : t.headD false = false) :
    qRun ans (pairEncode ctx (pairEncode (pairEncode aux t) (pairEncode [true] x))) =
      pairEncode (ans (pairEncode ctx (pairEncode aux x))) (pairEncode aux (true :: x)) := by
  simp only [qRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, if_true, ht,
    Bool.false_eq_true, if_false]

/-- A later challenge query (state `⟨aux, 1 :: x⟩`) is answered with `ans ⟨ctx, ⟨aux, x⟩⟩` and
keeps the state. -/
theorem qRun_recorded (ans : List Bool → List Bool) (ctx aux x y : List Bool) :
    qRun ans (pairEncode ctx (pairEncode (pairEncode aux (true :: x)) (pairEncode [true] y))) =
      pairEncode (ans (pairEncode ctx (pairEncode aux x))) (pairEncode aux (true :: x)) := by
  simp only [qRun_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, if_true,
    List.drop_succ_cons, List.drop_zero]

/-- The step function is polynomial-time when `ans` is.

**Proof sketch.** Pair projections, `polyTimeComputable_headD` for the two tests,
`polyTimeComputable_tail` for the recorded query, and `polyTimeComputable_ite` for the cases. -/
theorem polyTimeComputable_qRun {ans : List Bool → List Bool} (hans : PolyTimeComputable ans) :
    PolyTimeComputable (qRun ans) := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  have hs : PolyTimeComputable fun w => pairFstD (pairSndD w) := hF.comp hS
  have haux : PolyTimeComputable fun w => pairFstD (pairFstD (pairSndD w)) := hF.comp hs
  have ht : PolyTimeComputable fun w => pairSndD (pairFstD (pairSndD w)) := hS.comp hs
  have hx : PolyTimeComputable fun w => pairSndD (pairSndD (pairSndD w)) := hS.comp (hS.comp hS)
  have hi : PolyTimeComputable fun w => [(pairFstD (pairSndD (pairSndD w))).headD false] :=
    polyTimeComputable_headD.comp (hF.comp (hS.comp hS))
  have hflag : PolyTimeComputable fun w => [(pairSndD (pairFstD (pairSndD w))).headD false] :=
    polyTimeComputable_headD.comp ht
  have hrec := (hans.comp (hF.pairEncode
    (haux.pairEncode (polyTimeComputable_tail.comp ht)))).pairEncode hs
  have hnew := (hans.comp (hF.pairEncode (haux.pairEncode hx))).pairEncode
    (haux.pairEncode ((polyTimeComputable_const [true]).append hx))
  exact polyTimeComputable_ite hi (polyTimeComputable_ite hflag hrec hnew)
    ((polyTimeComputable_const []).pairEncode hs)

/-! ### The handler -/

/-- **The query-recording handler** with ciphertext length `Lc`, challenge-query length `Lq`,
decryption-answer length `Ld`, advice `aux` (of length `Laux(n)`), seed length `Lseed`, answer
`ans` and finalization `fin`: state `⟨aux n, asked :: x⟩`, initially `⟨aux n, 0^{1 + Lq(n)}⟩`;
the adversary runs on `pk`, the first component of the reduction input; the step is `qRun ans`
and the output is `fin`. -/
noncomputable def qHandler (Lc Lq Ld Laux Lseed : PolyExpr) (aux : ℕ → List Bool)
    (ans : List Bool → List Bool) (hans : PolyTimeComputable ans)
    (fin : List Bool → List Bool) (hfin : PolyTimeComputable fin) :
    PolyHandler 2 (qDin Lc Lq) (qDout Ld Lc) where
  stateLen := .add (.add (.mul (.const 2) Laux) (.const 3)) Lq
  seedLen := Lseed
  init n := padFin _ (pairEncode (aux n) (false :: List.replicate (Lq.eval n) false))
  run := qRun ans
  poly := polyTimeComputable_qRun hans
  advIn := recAdvIn
  advIn_poly := by
    have h : PolyTimeComputable fun ctx => pairFstD (pairFstD (pairSndD ctx)) :=
      polyTimeComputable_pairFstD.comp
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
    rw [show recAdvIn = fun ctx => pairFstD (pairFstD (pairSndD ctx)) from funext recAdvIn_eq]
    exact h
  out := fin
  out_poly := hfin

attribute [simps (config := { isSimp := false }) stateLen seedLen init run advIn out] qHandler

/-! ### The handler's simulation -/

/-- An empty answer decodes to all-`false` at every length:
`(decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ`. -/
theorem decodeFin_nil_getD (ℓ : ℕ) : (decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ := by
  rw [decodeFin_eq]
  split
  · next h =>
    subst h
    funext i
    exact absurd i.isLt (Nat.not_lt_zero _)
  · rfl

section Simulation

variable {α : Type} (Lc Lq Ld Laux Lseed : PolyExpr) (aux : ℕ → List Bool)
  {ans : List Bool → List Bool} (hans : PolyTimeComputable ans)
  {fin : List Bool → List Bool} (hfin : PolyTimeComputable fin)
  (n : ℕ) (z : List Bool)
  (ω : Fin ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).seedLen.eval n) → Bool)

/-- A decryption query is answered all-`false` and keeps the state:
`(qHandler …).answer n z ω s 0 x = (zeroBits _, s)`. -/
theorem qHandler_answer_dec
    (s : Fin ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).stateLen.eval n) → Bool)
    (x : Fin ((qDin Lc Lq 0).eval n) → Bool) :
    (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).answer n z ω s 0 x = (zeroBits _, s) := by
  have h : pairDecode ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).run
      (PolyHandler.input n z (List.ofFn ω) (List.ofFn s) (0 : Fin 2) (List.ofFn x))) =
      some ([], List.ofFn s) := by
    rw [qHandler_run, PolyHandler.input_eq]
    exact (congrArg pairDecode (qRun_dec ans _ _ _)).trans (pairDecode_pairEncode _ _)
  rw [PolyHandler.answer_of_pairDecode_eq_some _ h, decodeFin_nil_getD, decodeFin_ofFn,
    Option.getD_some]

/-- **After the challenge `mm` is recorded**, the handler's simulation is the deterministic run
with the answer function `g y = ans ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨aux n, y⟩⟩` from the recorded state
`padFin (g mm)`, and the handler's state does not change. Requires `|g y| = Lc(n)`.

**Proof sketch.** Induction on the computation. A decryption query is answered all-`false`
(`qRun_dec`), the answer of `chRun`; a challenge query is answered `g mm` (`qRun_recorded`),
which is `padFin (g mm)` at length `Lc(n)`; the state is kept in both cases. -/
theorem simulate_qHandler_recorded
    (hw : ∀ y : List Bool, y.length = Lq.eval n →
      (ans (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (aux n) y))).length = Lc.eval n)
    (c : OracleComp (bitSpecAt (qDin Lc Lq) (qDout Ld Lc) n) α)
    (mm : Fin ((qDin Lc Lq 1).eval n) → Bool)
    (s : Fin ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).stateLen.eval n) → Bool)
    (hs : List.ofFn s = pairEncode (aux n) (true :: List.ofFn mm)) :
    simulate ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).impl n z ω) c s =
      .pure ((chRun (fun y => ans (pairEncode (seedIn n z (List.ofFn ω))
        (pairEncode (aux n) (List.ofFn y)))) c
        (some (padFin _ (ans (pairEncode (seedIn n z (List.ofFn ω))
          (pairEncode (aux n) (List.ofFn mm))))))).1, s) := by
  induction c with
  | pure a => rw [simulate_pure, chRun_pure]
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, PolyHandler.impl_apply, qHandler_answer_dec, OracleComp.pure_bind,
        chRun_query_zero]
      exact ih _
    | 1, x, k, ih =>
      have hlen : (List.ofFn mm).length = Lq.eval n := by simp only [List.length_ofFn, qDin_one]
      have hans1 : (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).answer n z ω s 1 x =
          (padFin _ (ans (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (aux n) (List.ofFn mm)))), s) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [qHandler_run, PolyHandler.input_eq, GGMRed.ofFn_padFin_of_length (by
          rw [hw _ hlen, qDout_one]), hs, seedIn_eq]
        exact qRun_recorded ans _ _ _ _
      rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
        chRun_query_one_some]
      exact ih _

/-- **The handler's simulation from its initial state** is the deterministic run with the answer
function `g y = ans ⟨⟨1^n, ⟨z, ω⟩⟩, ⟨aux n, y⟩⟩` from the unchallenged state, and its final
state is `⟨aux n, 0^{1 + Lq(n)}⟩` if no challenge was asked and `⟨aux n, 1 :: mm⟩` for the first
challenge query `mm` (`firstQ`). Requires `|aux n| = Laux(n)` and `|g y| = Lc(n)`.

**Proof sketch.** Induction on the computation. Decryption queries are answered all-`false` and
keep the initial state. The first challenge query `x` is answered `g x`, which is
`padFin (g x)`, and records the state `⟨aux n, 1 :: x⟩` (`qRun_fresh`); from there
`simulate_qHandler_recorded` applies. -/
theorem simulate_qHandler_init (haux : (aux n).length = Laux.eval n)
    (hw : ∀ y : List Bool, y.length = Lq.eval n →
      (ans (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (aux n) y))).length = Lc.eval n)
    (c : OracleComp (bitSpecAt (qDin Lc Lq) (qDout Ld Lc) n) α) :
    ∃ s : Fin ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).stateLen.eval n) → Bool,
      simulate ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).impl n z ω) c
          ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).init n) =
          .pure ((chRun (fun y => ans (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (aux n) (List.ofFn y)))) c none).1, s) ∧
        List.ofFn s = pairEncode (aux n)
          ((firstQ c).elim (false :: List.replicate (Lq.eval n) false) (true :: ·)) := by
  have hinit : List.ofFn ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).init n) =
      pairEncode (aux n) (false :: List.replicate (Lq.eval n) false) := by
    rw [show (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).init n =
        padFin _ (pairEncode (aux n) (false :: List.replicate (Lq.eval n) false)) from
      funext (qHandler_init Lc Lq Ld Laux Lseed aux ans hans fin hfin n)]
    refine GGMRed.ofFn_padFin_of_length ?_
    rw [qHandler_stateLen, length_pairEncode, List.length_cons, List.length_replicate, haux]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  induction c with
  | pure a => exact ⟨_, by rw [simulate_pure, chRun_pure], by rw [firstQ_pure]; exact hinit⟩
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      obtain ⟨s, hsim, hs⟩ := ih (zeroBits _)
      refine ⟨s, ?_, ?_⟩
      · rw [simulate_query, PolyHandler.impl_apply, qHandler_answer_dec, OracleComp.pure_bind,
          chRun_query_zero]
        exact hsim
      · rw [firstQ_query_zero]
        exact hs
    | 1, x, k, _ =>
      have hxlen : (List.ofFn x).length = Lq.eval n := by simp only [List.length_ofFn, qDin_one]
      have hlen : (pairEncode (aux n) (true :: List.ofFn x)).length =
          (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).stateLen.eval n := by
        rw [qHandler_stateLen, length_pairEncode, List.length_cons, hxlen, haux]
        simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
        omega
      have hans1 : (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).answer n z ω
          ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).init n) 1 x =
          (padFin _ (ans (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (aux n) (List.ofFn x)))),
            padFin _ (pairEncode (aux n) (true :: List.ofFn x))) := by
        refine PolyHandler.answer_of_run_eq _ ?_
        rw [qHandler_run, PolyHandler.input_eq, GGMRed.ofFn_padFin_of_length (by
          rw [hw _ hxlen, qDout_one]), GGMRed.ofFn_padFin_of_length hlen, hinit, seedIn_eq]
        exact qRun_fresh ans _ _ _ _ rfl
      refine ⟨padFin _ (pairEncode (aux n) (true :: List.ofFn x)), ?_, ?_⟩
      · rw [simulate_query, PolyHandler.impl_apply, hans1, OracleComp.pure_bind,
          chRun_query_one_none]
        exact simulate_qHandler_recorded Lc Lq Ld Laux Lseed aux hans hfin n z ω hw _ x _
          (GGMRed.ofFn_padFin_of_length hlen)
      · rw [GGMRed.ofFn_padFin_of_length hlen, firstQ_query_one]
        rfl

end Simulation

/-! ### Transport and the machine -/

/-- **Transport of a run with a query-dependent answer along equal lengths:** for a machine
adversary run through `bitCodec`, if `ins = ins'`, `outs = outs'` and `d = d'`, then for every
`G : List Bool → List Bool`,
`List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1`, and
the two runs have the same `firstQ`.

**Proof sketch.** Substitute the equalities; both sides become identical. -/
theorem chRun_toCompOn_transport_list {ins outs ins' outs' : Fin 2 → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool)
    (r : A.Coins n) (G : List Bool → List Bool) :
    List.ofFn (chRun (ins := ins) (outs := outs) (fun y => G (List.ofFn y))
        (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
      List.ofFn (chRun (ins := ins') (outs := outs') (fun y => G (List.ofFn y))
        (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
    firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) := by
  subst hi ho hd
  exact ⟨rfl, rfl⟩

/-- **The machine of the query-recording handler** (T1 for `qHandler`). For a machine adversary
`A` with query budget `q` and one-bit output, there is a machine `D` and, at every parameter, a
bijection `φ` from (seed, `A`'s coins) to `D`'s coins with the following property. For lengths
`ins`, `outs` equal to those of `qDin Lc Lq`, `qDout Ld Lc`, let `c` be `A`'s computation on
`pairFstD z` with coins `r` through `bitCodec ins outs 1`, `ctx = ⟨1^n, ⟨z, ω⟩⟩` and
`g y = ans ⟨ctx, ⟨aux n, y⟩⟩`. If `|aux n| = Laux(n)` and `|g y| = Lc(n)` for every
`Lq(n)`-bit `y`, then `D` on `z` with coins `φ (ω, r)` outputs
`fin ⟨ctx, ⟨⟨aux n, t⟩, chRun g c⟩⟩`, where `t` is `1 :: mm` for the first challenge query `mm`
of `c` and `0^{1 + Lq(n)}` without one.

**Proof sketch.** T1 (`Games.exists_handlerMachine`) for `qHandler` with `dα = 1`; the handler's
simulation is `simulate_qHandler_init`; its adversary input is `pairFstD z` (`recAdvIn_eq`); the
run and the first challenge query transport to the lengths `ins`, `outs`
(`chRun_toCompOn_transport_list`). -/
theorem exists_qHandlerMachine (A : NUPPT) (q : PolyExpr) (Lc Lq Ld Laux Lseed : PolyExpr)
    (aux : ℕ → List Bool) (haux : ∀ n, (aux n).length = Laux.eval n)
    (ans : List Bool → List Bool) (hans : PolyTimeComputable ans)
    (fin : List Bool → List Bool) (hfin : PolyTimeComputable fin) :
    ∃ D : NUPPT, ∀ n : ℕ, ∃ φ : (Fin (Lseed.eval n) → Bool) × A.Coins n ≃ D.Coins n,
      ∀ (ins outs : Fin 2 → ℕ), (fun i => (qDin Lc Lq i).eval n) = ins →
        (fun i => (qDout Ld Lc i).eval n) = outs →
        ∀ (z : List Bool) (ω : Fin (Lseed.eval n) → Bool) (r : A.Coins n),
          (∀ y : List Bool, y.length = Lq.eval n →
            (ans (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (aux n) y))).length =
              Lc.eval n) →
          D.runAt n z (φ (ω, r)) =
            fin (pairEncode (seedIn n z (List.ofFn ω))
              (pairEncode (pairEncode (aux n)
                ((firstQ (A.toCompOn (bitCodec ins outs 1) n (q.eval n) (pairFstD z) r)).elim
                  (false :: List.replicate (Lq.eval n) false) (true :: ·)))
                (List.ofFn (chRun (fun y => ans (pairEncode (seedIn n z (List.ofFn ω))
                    (pairEncode (aux n) (List.ofFn y))))
                  (A.toCompOn (bitCodec ins outs 1) n (q.eval n) (pairFstD z) r) none).1))) := by
  obtain ⟨D, hD⟩ := exists_handlerMachine A q (qDin Lc Lq) (qDout Ld Lc) (.const 1)
    (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin)
  refine ⟨D, fun n => ?_⟩
  obtain ⟨φ, hφ⟩ := hD n
  refine ⟨φ, fun ins outs hi ho z ω r hw => ?_⟩
  obtain ⟨a, s, hsim, hrun⟩ := hφ z ω r
  have hadv : (qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).advInput n z ω = pairFstD z := by
    rw [PolyHandler.advInput_eq, qHandler_advIn, recAdvIn_eq, seedIn_eq, pairSndD_pairEncode,
      pairFstD_pairEncode]
  obtain ⟨s', hsim', hs'⟩ := simulate_qHandler_init Lc Lq Ld Laux Lseed aux hans hfin n z ω
    (haux n) hw _
  rw [hsim, OracleComp.pure.injEq, Prod.mk.injEq] at hsim'
  obtain ⟨rfl, rfl⟩ := hsim'
  obtain ⟨h₁, h₂⟩ := chRun_toCompOn_transport_list hi ho (PolyExpr.eval_const 1 n) A n (q.eval n)
    ((qHandler Lc Lq Ld Laux Lseed aux ans hans fin hfin).advInput n z ω) r
    (fun y => ans (pairEncode (seedIn n z (List.ofFn ω)) (pairEncode (aux n) y)))
  rw [hadv] at h₁ h₂ hs'
  refine hrun.trans ?_
  rw [PolyHandler.result_eq, qHandler_out, hadv, hs', h₂, h₁]

end TCSlib.Cryptography.Composability.BitwiseSim

## ===== TCSlib/Cryptography/Encryption/PublicKey/AdaptiveSecurity.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Adaptive left-or-right public-key security

An extension of the fixed-length game of [PS10, Definition 171.5] with one hidden bit,
one generated key pair, and a polynomial cap on fresh challenges. The adversary may
choose each pair of messages after seeing the earlier answers. In the CCA2 game the
decryptor refuses every ciphertext already issued as a challenge.

## Main definitions

* `FixedLengthPKScheme.adaptiveIndImpl` implements the two oracles and their history.
* `FixedLengthPKScheme.adaptiveIndGame` runs the existing adversary codec with those oracles.
* `FixedLengthPKScheme.AdaptiveINDSecure` is the negligible-advantage condition.

## Main results

* `FixedLengthPKScheme.adaptiveIndGame_one` recovers the exact single-challenge game.
* `FixedLengthPKScheme.AdaptiveINDSecure.single` specializes the security predicate.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

namespace TCSlib.Cryptography.Composability.FixedLengthPKScheme

open Complexity Turing TCSlib.Cryptography.Games

variable (S : FixedLengthPKScheme)

/-- Extend [PS10, Definition 171.5] to a bounded list of fresh left-or-right challenges.
The history records each issued challenge. A decryption query in the history receives
the existing refusal reply. Once the challenge cap is reached the game repeats the
latest ciphertext, with a zero reply for a zero cap and empty history. The history is
a list so a repeated ciphertext still consumes one fresh challenge. -/
noncomputable def adaptiveIndImpl (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (cap : ℕ) : QueryImpl (S.indSpec n) (List (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, c, history =>
    if cast (S.indSpec_decDom n) c ∈ history then
      .pure (zeroBits _, history)
    else
      (S.indImpl atk b n pk sk 0 c history.head?).bind fun res => .pure (res.1, history)
  | 1, mm, history =>
    if history.length < cap then
      (S.indImpl atk b n pk sk 1 mm none).bind fun res => .pure (res.1, res.2.toList ++ history)
    else
      match history.head? with
      | none => .pure (zeroBits _, history)
      | some c =>
        (S.indImpl atk b n pk sk 1 mm (some c)).bind fun res => .pure (res.1, history)

/-- Decryption refuses every ciphertext recorded in the challenge history. -/
theorem adaptiveIndImpl_dec_issued (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (c : (S.indSpec n).dom 0)
    (history : List (Fin (S.ctLen.eval n) → Bool))
    (hc : cast (S.indSpec_decDom n) c ∈ history) :
    S.adaptiveIndImpl atk b n pk sk cap 0 c history = .pure (zeroBits _, history) := by
  rw [adaptiveIndImpl, if_pos hc]

/-- A challenge below the cap uses the single game's fresh challenge branch, then
adds that ciphertext to the history. -/
theorem adaptiveIndImpl_challenge_fresh (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : history.length < cap) :
    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
      (S.indImpl atk b n pk sk 1 mm none).bind
        (fun res => .pure (res.1, res.2.toList ++ history)) := by
  rw [adaptiveIndImpl, if_pos h]

/-- A fresh challenge samples an encryption tape, returns the selected encryption, and
prepends exactly that ciphertext to the history.

**Proof sketch.** Read the original game's first-challenge equation on the specification's
type, then simplify the continuation that saves the returned ciphertext. -/
theorem adaptiveIndImpl_challenge_encrypt (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : history.length < cap) :
    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let halves := FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n
          (pairEncode pk (List.ofFn (if b then halves.2 else halves.1))) r)
        .pure (cast (S.indSpec_challengeRng n).symm c, c :: history) := by
  rw [S.adaptiveIndImpl_challenge_fresh atk b n pk sk cap mm history h,
    S.indImpl_challenge_none_onSpec, OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind, Option.toList_some, List.singleton_append]

/-- A positive cap of one issues a fresh first challenge, as in Definition 171.5. -/
private theorem adaptiveIndImpl_one_empty (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (mm : (S.indSpec n).dom 1) :
    S.adaptiveIndImpl atk b n pk sk 1 1 mm [] =
      (S.indImpl atk b n pk sk 1 mm none).bind (fun res => .pure (res.1, res.2.toList)) := by
  rw [S.adaptiveIndImpl_challenge_fresh atk b n pk sk 1 mm []
    (by simp only [List.length_nil, Nat.zero_lt_one])]
  simp only [List.append_nil]

/-- At a full challenge cap, repeat the latest ciphertext without adding to the history. -/
theorem adaptiveIndImpl_challenge_full (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (mm : (S.indSpec n).dom 1)
    (history : List (Fin (S.ctLen.eval n) → Bool)) (h : cap ≤ history.length)
    (c : Fin (S.ctLen.eval n) → Bool) (hc : history.head? = some c) :
    S.adaptiveIndImpl atk b n pk sk cap 1 mm history =
      (S.indImpl atk b n pk sk 1 mm (some c)).bind
        (fun res => .pure (res.1, history)) := by
  rw [adaptiveIndImpl, if_neg (Nat.not_lt_of_ge h), hc]

/-- A zero challenge cap keeps the initial history empty and returns the zero reply. -/
theorem adaptiveIndImpl_challenge_zero (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (mm : (S.indSpec n).dom 1) :
    S.adaptiveIndImpl atk b n pk sk 0 1 mm [] = .pure (zeroBits _, []) := by
  rw [adaptiveIndImpl, if_neg (Nat.not_lt_zero _)]
  rfl

/-- Decryption outside the history uses the original oracle's availability and decoding
rules. Its answer leaves the full history unchanged. -/
theorem adaptiveIndImpl_dec_other (atk : Attack) (b : Bool) (n : ℕ)
    (pk sk : List Bool) (cap : ℕ) (c : (S.indSpec n).dom 0)
    (history : List (Fin (S.ctLen.eval n) → Bool))
    (hc : cast (S.indSpec_decDom n) c ∉ history) :
    S.adaptiveIndImpl atk b n pk sk cap 0 c history =
      (S.indImpl atk b n pk sk 0 c history.head?).bind (fun res => .pure (res.1, history)) := by
  rw [adaptiveIndImpl, if_neg hc]

/-- At cap one, each oracle call agrees with the old game when the optional challenge is
represented as a list.

**Proof sketch.** Split by oracle and old challenge state. For decryption the
single-game state is preserved. A fresh challenge creates one list entry, and a repeat
returns the same state. -/
theorem adaptiveIndImpl_one (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (i : Fin 2) (x : (S.indSpec n).dom i) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.adaptiveIndImpl atk b n pk sk 1 i x s.toList =
      (S.indImpl atk b n pk sk i x s).bind (fun res => .pure (res.1, res.2.toList)) := by
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> decide
  rcases hi with rfl | rfl
  · cases s with
    | none =>
      rw [Option.toList_none, S.adaptiveIndImpl_dec_other atk b n pk sk 1 x []
        List.not_mem_nil, List.head?_nil, S.indImpl_dec_onSpec]
      split <;> simp only [OracleComp.pure_bind, Option.toList_none]
    | some c =>
      by_cases h : cast (S.indSpec_decDom n) x = c
      · rw [S.adaptiveIndImpl_dec_issued atk b n pk sk 1 x (some c).toList (by
          simp only [Option.toList_some, List.mem_singleton]; exact h)]
        rw [S.indImpl_dec_onSpec, h]
        simp
      · rw [S.adaptiveIndImpl_dec_other atk b n pk sk 1 x (some c).toList (by
          simp only [Option.toList_some, List.mem_singleton]; exact h)]
        simp only [Option.toList_some, List.head?_cons, S.indImpl_dec_onSpec]
        split <;> simp only [OracleComp.pure_bind, Option.toList_some]
  · cases s with
    | none => exact S.adaptiveIndImpl_one_empty atk b n pk sk x
    | some c =>
      rw [S.adaptiveIndImpl_challenge_full atk b n pk sk 1 x (some c).toList (by simp) c (by simp),
        S.indImpl_challenge_repeat_onSpec]
      simp only [OracleComp.pure_bind]

/-- Cap-one simulation is the single-challenge simulation with its final state encoded
as a list.

**Proof sketch.** Induct over the adversary's query tree and apply the per-call equality. -/
theorem simulate_adaptiveIndImpl_one (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    {α : Type} (t : OracleComp (S.indSpec n) α) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    simulate (S.adaptiveIndImpl atk b n pk sk 1) t s.toList =
      (simulate (S.indImpl atk b n pk sk) t s).bind
        (fun res => .pure (res.1, res.2.toList)) := by
  induction t generalizing s with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    simp only [simulate_query, S.adaptiveIndImpl_one, OracleComp.bind_assoc, OracleComp.pure_bind]
    congr 1
    funext res
    exact ih res.1 res.2

/-- The left-or-right game uses one key and hidden bit across the adaptive queries. -/
noncomputable def adaptiveIndGame (atk : Attack) (A : NUPPT) (q cap : ℕ) (b : Bool) (n : ℕ) :
    ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.adaptiveIndImpl atk b n (pairFstD (S.gen.runAt n [] rg))
      (pairSndD (S.gen.runAt n [] rg)) cap)
      (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
    fun res => .pure (res.1 0)

/-- The experiment's only sampled keys come from one activation of key generation. -/
theorem adaptiveIndGame_eq (atk : Attack) (A : NUPPT) (q cap : ℕ) (b : Bool) (n : ℕ) :
    S.adaptiveIndGame atk A q cap b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.adaptiveIndImpl atk b n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)) cap)
          (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) []).bind
        fun res => .pure (res.1 0) := rfl

/-- The cap-one experiment and the existing single-challenge experiment return the same bit
on the same sampled generator and adversary tapes.

**Proof sketch.** Fix both sampled tapes and apply the simulation correspondence.
Both experiments read the same bit of the simulation's result. -/
theorem adaptiveIndGame_one (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.adaptiveIndGame atk A q 1 b n = S.indGame atk A q b n := by
  simp only [S.adaptiveIndGame_eq, S.indGame_eq]
  congr 1
  funext rg
  congr 1
  funext r
  rw [← Option.toList_none (α := Fin (S.ctLen.eval n) → Bool), S.simulate_adaptiveIndImpl_one,
    OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind]

/-- The adversary's left-or-right advantage is negligible for polynomial total and
challenge budgets. The first catalog witnesses will have message length equal to the
security parameter. -/
def AdaptiveINDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q cap : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    advantage (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) false n)
      (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) true n) ≤ ε n

/-- The adaptive predicate quantifies over both the total query and challenge budgets. -/
theorem adaptiveINDSecure_iff (atk : Attack) :
    S.AdaptiveINDSecure atk ↔
      ∀ (A : NUPPT) (q cap : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
        advantage (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) false n)
          (S.adaptiveIndGame atk A (q.eval n) (cap.eval n) true n) ≤ ε n :=
  Iff.rfl

/-- Adaptive security entails security in the original game.

**Proof sketch.** Use the constant cap one and the exact simulation equation. -/
theorem AdaptiveINDSecure.single {atk : Attack} (h : S.AdaptiveINDSecure atk) :
    S.INDSecure atk := by
  rw [S.adaptiveINDSecure_iff] at h
  rw [S.INDSecure_iff]
  intro A q
  obtain ⟨ε, hε, hb⟩ := h A q (.const 1)
  refine ⟨ε, hε, fun n => ?_⟩
  simpa only [PolyExpr.eval_const, S.adaptiveIndGame_one] using hb n

end TCSlib.Cryptography.Composability.FixedLengthPKScheme
