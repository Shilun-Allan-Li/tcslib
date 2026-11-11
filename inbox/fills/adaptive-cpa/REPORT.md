# Fill `adaptive-cpa` — checkpoint 1

**Worker:** Claude (external). **Issue base:** `4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27` on
`cryptography/pass-shelat-ch2-4`. **Local proof branch:** `fill/adaptive-cpa` (never pushed); this
checkpoint's head is in `patches/`. **Pack:** read at exchange `f4737d78e`, `SHA256SUMS` 7/7 OK.

**Target status:** `Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa` is still `sorry`
(statement and prose unchanged). The owned file only gained an import of the helper modules.

## Step 1 (hybrids): done

New helper modules under `TCSlib/Cryptography/Encryption/PublicKey/AdaptiveCPA/`, imported by the
owned file:

- `Hybrid.lean` (generic): `hybImpl κ E sel`, the `sel`-hybrid of the adaptive CPA oracles on
  `bitSpec ins outs` (fresh challenge `j < κ` encrypts `m_{sel j}` with fresh coins and records
  it; at the cap the latest ciphertext, all-`false` for an empty history; `Dec` answers `⊥`);
  `tapeImpl`, the same with coins given in advance except one lazy slot, and
  `expect_tapeImpl` (coins in advance have the lazy distribution, by one-coordinate resampling
  `expect_sample_update`); `castImpl` with `simulate_castImpl_toCompOn` (generic codec
  transport, as `chRun_toCompOn_transport`); `simulate_eq_of_abs` (simulation through a state
  abstraction).
- `Games.lean`: `acHyb S A q κ n sel`, the hybrid game on T2's codec. `H_i` is
  `acHyb … (fun j => decide (j < i))`. Proved: `castImpl_adaptiveIndImpl` (the adaptive CPA
  oracles read on T2's codec are `hybImpl` with the constant selector, through the published
  `adaptiveIndImpl_*` equations, including cap `0` and the empty history),
  `adaptiveIndGame_eq_acHyb`, and **`acHyb_lt_zero` (`H_0` = game `b = false`) and
  `acHyb_lt_cap` (`H_cap` = game `b = true`)**, by `acHyb_congr` (the selector is read only below
  the cap).

## Step 2 (the reduction): handler built

- `Handler.lean`: `acHandler S cap ist`, an `InteractiveHandler` with `perCall = 1`,
  `finCall = 0`, `outLen = 1`, state `⟨1^j, ⟨1^{i⋆(n)}, c⟩⟩` padded to `4·cap + 4 + ctLen` bits
  (`init` holds `i⋆(n)`), seed `cap · ρ` bits read as `cap` encryption tapes (`acTapes`). Its
  round function is polynomial-time (`Enc`'s output function, unary arithmetic, prefix
  splitting). Proved call equations: `acHandler_impl_dec`, `_impl_full`, `_impl_eager` (own
  encryption with tape `j` of `m_{[j < i⋆]}`), `_impl_forward` (one outer challenge query, its
  answer recorded), `acHandler_advInput` (the adversary runs on `pk`), `acHandler_finish`
  (outputs `A`'s bit with no outer query).

Next: checkpoint 2 (T2 applied, codec alignment on the outer game), then checkpoint 3.

## Checks so far

- Preflight (`evidence/logs/preflight.log`): `nproc` 4; cgroup v1 with no effective limit, so
  the headroom is `MemAvailable` = 16,331,972,608 B (PASS); ext4 `/dev/vda`, 19,485,560,832 B free
  (PASS, floor 12 GiB). No tmpfs used.
- Cache: archive store `~/.cache/mathlib` held 2,383 files (118,965,639 B) left by this host's
  earlier not-cca2 fill session; the narrowed `lake exe cache get` over the 92 roots (identical to
  `roots.txt`) reported "No files to download", decompressed 2,345 files, exit 0. Package pins:
  PASS (doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean ABSENT). No zero-size oleans; root probe
  passed.
- Bootstrap: the full `order.txt` (197 modules), one module per `scripts/lean_check_tree.sh`,
  ALL PASS, 27 `sorry` warnings, peak RSS 3,093,332 KiB (`logs/bootstrap.tsv`).
- The three new modules and the owned file check clean (`logs/checkpoint1/`). The order with
  the helpers inserted before `PublicKey/AdaptiveCPA` is `evidence/order.txt` (200 modules); the
  Mathlib roots are unchanged (92).
