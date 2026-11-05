# The logarithmic bounds at #181's round-4 head `227d92ee`: every candidate site, classified

## The facts

- **LS-1**, `logSpace n ≤ n + 1`. In the logarithm's terms it is `Nat.log 2 m + 1 ≤ m + 1`, or
  `Nat.log 2 m ≤ m`, at any argument `m`, because `logSpace n = Nat.log 2 n + 1` (`logSpace_eq`).
- **LS-2**, the bound by the binary length: `logSpace n ≤ Nat.size n + 1`, equivalently
  `logSpace n ≤ |bits n| + 1` (`Nat.size_eq_bits_len`). Its converse is
  `|bits n| ≤ Nat.log 2 n + 1`, which is `LogProg.length_bits_le_log` (`Machines/Bin`), equivalently
  `Nat.size n ≤ logSpace n`.
- **LS-3**, the equality `|bits n| = Nat.log 2 n + 1` for `n ≠ 0`. No public lemma states it.

A copy is a step that derives one of these facts without citing the lemma that states it. It may
unfold `logSpace` directly, use a local alias, or work by reduction.

## The searches

1. **`ls1search.py`** covers every code line of `TCSlib/**/*.lean`, comments and docstrings
   skipped, of two kinds:
   - **(A)** a line that touches `logSpace`'s definition: an `unfold`, `delta`, `change` or `show`
     step, `logSpace` in a rewrite or simp list, `logSpace_eq`, `logSpace.eq_*`, or a local alias
     `:= logSpace`;
   - **(B)** a line that cites a Mathlib upper bound of `Nat.log` by its argument or by a power:
     `log_le_self`, `log_lt_self`, `log_lt_of_lt_pow`, `log_le_of_lt_pow`, `log_lt_iff_lt_pow`,
     `lt_pow_iff_log_lt` or `log_le_of_le_pow`. The regex also matches `pow_log_le_self` and
     `clog_le_iff_le_pow`.

   A proof of a `logSpace` bound has three routes: cite a lemma, unfold `logSpace` (A), or reach it
   by reduction through a (B) lemma. At the head the search finds 91 lines in 60 declarations
   (`candidates.tsv`; each declaration in context in `context.txt`). Round 3's list had used
   `Nat.log_le_self` alone and missed `arm_decides`, which used `Nat.log_lt_self` under the alias
   `Ls`.
2. **`bitsweep.sh`, the binary-length sweep.** It lists every use of `Nat.size_le`,
   `Nat.size_le_size`, `Nat.lt_size`, `Nat.lt_size_self`, `Nat.size_eq_bits_len`,
   `Nat.lt_pow_succ_log_self`, the `length_bits_le*` lemmas, `logSpace_le_size_succ` and
   `size_le_logSpace`, each with its declaration. At the head that is 189 lines in 132
   declarations (`bitsweep.tsv`, grouped in `bitsweep-decls.txt`; each declaration in context in
   `bitsweep-context.txt`, by `bitcontext.py`). It finds the copies of LS-2's
   converse and of LS-3, which use no `logSpace` step.

Lemmas are cited by their declaration lines and inline steps by their hit lines.

## 1. LS-1: proved once, cited at nine sites

| Site | Class |
|---|---|
| `SpaceComplexity/Basic:200` `logSpace_le_succ` | **the published lemma** |
| `Constructible:529`, `:685`; `SpaceClasses:84` | citation (round 1) |
| `Machines/NARMProof:216`; `Machines/NARMLogspace:95` | citation (round 2) |
| `ImplicitPoly:379`; `Logspace/PreimageHost:788` | citation through `logSpace_eq` (round 3) |
| `Machines/ARMProof:249` (`arm_decides`) | citation (round 4). **It was a copy:** `simp only [hLs, logSpace]` and `Nat.log_lt_self` (round 3's finding 1) |
| `SavitchARM/Reach:166` | citation (it predates #181) |

## 2. LS-2 and its converse: each proved once

| Site | Class |
|---|---|
| `Basic:210` `logSpace_le_size_succ` | **the published lemma** (round 4, moved verbatim from `Logspace/ISCountMath`) |
| `Logspace/ISCountGenCorrect:66` | citation (it predates #181; the name now resolves to `Basic`'s lemma) |
| `Randomized/BPLInP:397` (`two_pow_codes_le`), `:443` (`BPL_subset_P`) | citation (round 4). **Both were copies**, each through `Nat.lt_size` and `Nat.pow_log_le_self` |
| `Randomized/SpaceAmplifyPoly:258` `logSpace_le_ell` (`ell n = |bits n| + 1`) | citation (round 4). **It was a copy**, through `Nat.log_lt_of_lt_pow` |
| `Machines/Bin:132` `LogProg.length_bits_le_log` | **the converse's published lemma** |
| `Logspace/ISCountGenCorrect:216` (private `size_le_logSpace`, `Nat.size n ≤ logSpace n`) | citation of `length_bits_le_log` (round 4). **It was a copy**, through `Nat.size_le` and `Nat.lt_pow_succ_log_self` |
| The converse's other uses: `Codec/Layout:58`, `Codec/Word:434`, `Constructible:80`, `:444`, `ExpBFS/Main:609`, `ImplicitPoly:308`, `Logspace/InputAccess:2117`, `PreimageHost:780`, `:787`, `ARMKit:86`, `DblLang:352`, `NARMLogspace:122`, `NARMProof:258` | citations of `length_bits_le_log` |

## 3. LS-3, the equality: three private copies, ledgered

`Constructible:77` `b3a_bits_length` (`n ≠ 0`, `|bits n| = logSpace n`), `QuasiPolyHierarchy:59`
`length_bits_eq` (`|bits n| = if n = 0 then 0 else Nat.log 2 n + 1`) and `NTimeDiagonalizer:440`
`qy_log_bits` (`1 ≤ n`, `Nat.log 2 n + 1 = |bits n|`). All three are private, and no public lemma
states the fact. `NTimeDiagonalizer:424` `qy_two_pow_bits_le` also proves `Nat.size n = Nat.log 2 n + 1`
inline. **Ledgered as LS-3** (user, 2026-11-04): debt for the dedup window, because
`NTimeDiagonalizer` is E-D's file, in flight.

## 4. Other facts about `logSpace` (class A)

| Site | What the step proves |
|---|---|
| `Basic:195` `logSpace_eq` | the definition's equation |
| `Basic:221` `logSpace_le_of_le_mul_two_pow`; `Basic:260` `logSpace_mono` | the published bound under `v ≤ A·2ˢ`, and monotonicity |
| **Positivity, `1 ≤ logSpace n`**, one `simp [logSpace]` each: `ARMProof:248`, `ImplicitPoly:369`, `PreimageHost:772`, `MARMTime:356`, `NARMLogspace:92`, `NARMExample:98`, `NARMProof:213`; through `S ≥ logSpace`, `ARMWidth:173` and `ISCountGenCorrect:250`; `ISCountGenCorrect:281` (`1 ≤ logSpace n + W n`); `Constructible:503` (`logSpace n + 1 ≤ 2 logSpace n`) | a lower bound. No lemma states it, so there is nothing to copy |
| `PathHard:78` `logSpace_le_ell` (`ell m = |bits (m + 1)|`) | `logSpace m ≤ Nat.size (m + 1)`. This is stronger than LS-2 (at `m ≥ 1`, `logSpace m = Nat.size m`), so LS-2 does not give it |
| `Constructible:89` `b3a_word_length` | the counter word's length, through `b3a_bits_length` (§3) |
| **The logarithm of a polynomial bound** (`log_poly_bound`'s constant): `ARMProof:306`, `NARMProof:232`, `:262`, `NARMLogspace:114`, `:126`, `ARMKit:90`, `ImplicitPoly:374`, `:393`, `PreimageHost:777`, `:783`, `Logspace/InputAccess:2120`, `Machines/DblLang:355` | `logSpace` of a register value, a call's virtual input or a width, bounded by `K · logSpace n` through `Nat.log_mono_right` |
| `MARMTime:375` (`count_bound`, `logSpace y ≤ L + W + m + 3` through `Nat.log_lt_of_lt_pow`), `MARMTime:512` (`marm_dtime`, monotonicity) | other bounds |
| `Codec/Word:441` (`length_cfgWord_le`) | `wP |x| ≤ logSpace |x| + 1`, through `Nat.log_mul_base` |
| `ExpTime:95`, `:100` (`NL_subset_P`); `ExpBFS/Run:373` `logSpace_le_lgv`, `:380` `lgv_le` | the exponential side (`2 ^ Nat.log 2 n ≤ n + 1`), and the relation between `lgv` and `logSpace` |

## 5. The strict form `Nat.log 2 k < k` (Mathlib's `Nat.log_lt_self`): a different fact

`logSpace_le_succ` gives `Nat.log 2 k + 1 ≤ k + 1`. The strict form gives `Nat.log 2 k + 1 ≤ k` for
`k ≠ 0`, which LS-1 does not imply:
- `ExpBFS/Run:385` `lgv_le_succ`: `lgv n ≤ n + 1`, where `lgv n = 1 + hv n`, `hv 0 = 0` and
  `hv k = Nat.log 2 k + 1` otherwise. This is `hv n ≤ n`. Round 4 makes `setup_run` (`:442`),
  which had re-derived `hv |x| ≤ |x|` inline, cite it;
- `Codec/Layout:57` `wP_le`: `|bits (n + 1)| ≤ n + 1`.

## 6. `Nat.log` without `logSpace` (class B only): other facts

`Lupanov:213`, `:228`, `:237`, `:269`; `LupanovGates:230`, `:287`, `:338`, `:496`, `:552`; `NCAC:184`;
`Parity:349`; `TreeNCAC:466`; `PrimeFind:68`, `:76`, `:122`, `:268`; `NTimeDiagonalizer:434`,
`:445`, `:3780`, `:5164`; `BiasedCoinHalting:337`, `:445`; `QuasiPolyHierarchy:64`, `:83`;
`ConfigCount:430`; `ExpBFS/Main:544`; `CommunicationComplexity/…/DetRectangle:561`, `…/Rank:208`;
`GilbertVarshamov:319`; `Halving:161`; `Programs/Light/Lib/Logs:99`.

None of these mentions `logSpace` or combines a bound into `Nat.log 2 m + 1 ≤ m + 1`. They are
Mathlib's own facts cited for other purposes: `pow_log_le_self`, `clog_le_iff_le_pow`,
`log_lt_of_lt_pow` at other bounds, `Lupanov`'s `L ≤ n` and its predecessor, `NTimeDiagonalizer`'s
stage arithmetic, and `BiasedCoinHalting`'s minimum.

## 7. The binary-length sweep's other lines: BL-1, ledgered

The sweep's remaining lines state elementary bounds on the binary length. They take a `Nat.size`
fact from Mathlib and carry it over through `Nat.size_eq_bits_len`; none involves `logSpace` or
`Nat.log`. Where a published lemma states such a bound, the inline transports restate it. They are
**ledgered as BL-1** (user, 2026-11-04): debt for the dedup window. The ledger entry lists the
sites. This gate does not claim them retired.

## Conclusion

- **LS-1** is proved once, in `Basic`, and cited at nine sites.
- **LS-2** is proved once, in `Basic`, and cited at four sites. Its converse is proved once, in
  `Machines/Bin`, and cited at fourteen sites.
- **LS-3 and BL-1** are ledgered for the dedup window.
- **Every other candidate proves a different fact:** positivity, the polynomial width, the
  exponential side, the strict form, or `Nat.log` without `logSpace`.
