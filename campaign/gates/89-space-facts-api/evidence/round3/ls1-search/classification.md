# LS-1 at #181's round-3 head `b8add1ac`: every candidate site, classified

The raw search is `ls1-search-raw.txt`. LS-1's fact is `logSpace n ≤ n + 1`. In the logarithm's own
terms it reads `Nat.log 2 m + 1 ≤ m + 1`, at any argument `m`, through `logSpace n = Nat.log 2 n + 1`
(`logSpace_eq`). A step that derives either form is a copy. Citing Mathlib's `Nat.log_le_self`
(`Nat.log b n ≤ n`) for another purpose is not.

| Site | What it proves | Class |
|---|---|---|
| `SpaceComplexity/Basic:198` `logSpace_le_succ` | `logSpace n ≤ n + 1` | **the published lemma** |
| `Constructible:529`, `:685`; `SpaceClasses:84`; `SavitchARM/Reach:166`; `Machines/NARMProof:216`; `Machines/NARMLogspace:95` | cite `logSpace_le_succ` | citation (round 1 for `Constructible` and `SpaceClasses`, round 2 for the two NARM files; `Reach` predates #181) |
| `SpaceComplexity/ImplicitPoly:379` (`ImplicitlyLogspaceComputable.computesInSpace`) | `W ≤ F + 2` with `W = Nat.log 2 (F + 1) + 1` | **was a copy** (round 2's finding 1); round 3 cites `logSpace_le_succ (F + 1)` through `logSpace_eq` |
| `Logspace/PreimageHost:788` (`mem_LOGSPACE_preimage`) | `Nat.log 2 (m + 1) + 1 ≤ m + 2`, `m = |f x|` | **was a copy** (round 2's finding 1); round 3 cites `logSpace_le_succ (m + 1)` through `logSpace_eq` |
| `CircuitComplexity/Lupanov:213` | `L ≤ n` with `L = Nat.log 2 n` | Mathlib's `Nat.log_le_self` itself; no `logSpace`, no `+ 1` |
| `CircuitComplexity/Lupanov:269` | `Nat.log 2 n - 1 ≤ n` | a different fact (a predecessor) |
| `Diagonalization/NTimeDiagonalizer:5164` | `Nat.log 2 |x| ≤ |x|`, a hypothesis for `omega` | Mathlib's fact itself, cited; it is not combined into a `logSpace`-shaped bound (the file is E-D's owned file, in flight) |
| `Randomized/BiasedCoinHalting:445` | `min n (Nat.log b n) = Nat.log b n` | a different fact |
| `Randomized/BPLInP:396` | `logSpace n ≤ |bits n| + 1` | a different fact: a bound by the binary length, not by `n` |
| `ExpBFS/Main:527`, `Logspace/ISCountGenCorrect:273`, `Machines/MARMTime:353` | `n + 1 ≤ 2 ^ logSpace n` | a different fact: the exponential side, from `Nat.lt_pow_succ_log_self` |
| `Codec/Word:439` | a width bound through `Nat.log_mono_right` | a different fact (monotonicity) |
| `RAMSimulation/Classes:80`, `Constructible:521`, `:624`, `Hierarchy:280`, `NARMProof:346`, `SpaceClasses:79` | docstring text | prose, no proof step |

So after round 3, `logSpace n ≤ n + 1` is proved once, in `Basic`, and cited at eight sites.
