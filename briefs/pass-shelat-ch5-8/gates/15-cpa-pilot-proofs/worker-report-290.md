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
