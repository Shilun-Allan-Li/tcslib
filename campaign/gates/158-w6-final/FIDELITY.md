# Statement-vs-book fidelity table (W6, draft 2026-11-17)

This table covers the 27 headline theorems of the closeout plan (PLAN §1), taken from campaign Lean `179c8c9c` (the
#356 merge). Each row puts the Lean statement beside AB09's statement and records every divergence.

**Standing conventions** apply to every row and are not repeated below:

- **Classes.** A class `C(f)` means "decided within `c · f(n)` steps or cells for some constant
  `c`" (Definitions 1.12, 2.5, 4.1).
- **Machines and languages.** Machines are finite, multi-tape and over the binary alphabet, and
  languages are sets of binary words.
- **Constructibility.** Time-constructible (§1.3) includes `T(n) ≥ n` and allows constant slack in
  the computing machine's time. Space-constructible (§4.1, p. 79) includes the book's standing
  `S(n) > log n` as a domination of `logSpace`, again with constant slack. Each module docstring
  justifies its slack.
- **Asymptotics.** `∀ A, ∃ N, ∀ n ≥ N, A · f(n) ≤ g(n)` is the book's `f = o(g)`.

| # | Lean (file) | AB09 | Book statement | Lean statement | Divergence |
|---|---|---|---|---|---|
| 1 | `time_hierarchy` (TimeHierarchy/Diagonal) | Thm 3.1 | For time-constructible `f, g` with `f log f = o(g)`: `DTIME(f) ⊊ DTIME(g)` | For any diagonal simulator `S` with overhead `Φ` (`t ≤ Φ t n`), time-constructible `g` and `Φ(f(n), n) = o(g(n))`: `DTIME f ⊂ DTIME (g + 1)` | **Generalized.** The overhead is a parameter, and `f` need not be time-constructible. The book form is `time_hierarchy_book` (`f(n) ≥ n`, `f log f = o(g)`), an instance with the two-tape self-simulator, and `time_hierarchy_book_of_pos` gives `DTIME g` for positive `g`. Using `g + 1` covers `g(n) = 0`. |
| 2 | `P_ssubset_EXP` (TimeHierarchy/Separation) | §3.1 (consequence of Thm 3.1; inclusion Claim 2.4) | `P ⊊ EXP` | `P ⊂ EXP` | None. |
| 3 | `ntime_hierarchy` (Diagonalization/NTimeHierarchy) | Thm 3.2 | For time-constructible `f, g` with `f(n+1) = o(g(n))`: `NTIME(f) ⊊ NTIME(g)` | Time-constructible `f, g` with `f(n+1) + f(n) + n + 1 = o(g(n))`: `NTIME f ⊂ NTIME (g + 1)` | The hypothesis adds `f(n) + n + 1`. This is harmless for monotone time-constructible `f`, since then `f(n), n ≤ f(n+1)`, but it is a stronger statement of the condition. `g + 1` as in row 1. |
| 4 | `NTIME_linear_ssubset_square` (same) | §3.2 example after Thm 3.2 | `NTIME(n) ⊊ NTIME(n²)` | `NTIME (n+1) ⊂ NTIME ((n+1)²)` | `n + 1` for `n` (the same classes up to the constant, except at `n = 0`). |
| 5 | `exists_not_timeConstructible` (Diagonalization/NotTimeConstructible) | Ex 3.5 | Some `T : ℕ → ℕ` with `T(n) ≥ n` is not time-constructible | `∃ T, (∀ n, n ≤ T n) ∧ ¬TimeConstructible T` | None. |
| 6 | `POracle_EXPCOM_eq_EXP` (Diagonalization/EXPCOM) | Ex 3.6(3) | `P^EXPCOM = EXP` | `POracle EXPCOM = EXP` | None. |
| 7 | `NPOracle_EXPCOM_eq_EXP` (same) | Ex 3.6(3) | `NP^EXPCOM = EXP` | `NPOracle EXPCOM = EXP` | None. |
| 8 | `exists_oracle_ne` (Diagonalization/Relativization) | Thm 3.7 (`B` half) | There is `B` with `U_B ∈ NP^B \ P^B` | `∃ B, unaryWitnessLang B ∈ NPOracle B ∧ unaryWitnessLang B ∉ POracle B` | None; `unaryWitnessLang` is `U_B`. Exercise 3.3 (`B ∈ EXP`) is deferred (W8). |
| 9 | `baker_gill_solovay` (same) | Thm 3.7 | There are oracles `A, B` with `P^A = NP^A` and `P^B ≠ NP^B` | `(∃ A, POracle A = NPOracle A) ∧ ∃ B, POracle B ≠ NPOracle B` | None. |
| 10 | `NP_subset_PSPACE` (SpaceComplexity/Inclusions) | Ex 4.6 | `NP ⊆ PSPACE` | `NP ⊆ PSPACE` | None. |
| 11 | `NSPACE_subset_exp_dtime` (SpaceComplexity/ExpTime) | Thm 4.2 (third inclusion) | `NSPACE(S) ⊆ DTIME(2^{O(S)})` for space-constructible `S` | `NSPACE S ⊆ ⋃ c, DTIME (2^{c(S n + 1)})` | `S + 1` in the exponent covers `S = 0`. |
| 12 | `NL_subset_P` (same) | §4.1.2 (Ex 4.3's premise) | `NL ⊆ P` | `NL ⊆ P` | None. |
| 13 | `savitch` (SpaceComplexity/Savitch) | Thm 4.14 | `NSPACE(S) ⊆ SPACE(S²)` for space-constructible `S ≥ log n` | `NSPACE S ⊆ SPACE (S · S)` for space-constructible `S` | None (`S ≥ log n` is part of space-constructibility). |
| 14 | `PSPACE_eq_NPSPACE` (same) | §4.2.1 | `PSPACE = NPSPACE` | `PSPACE = NPSPACE` | None. |
| 15 | `TQBF_mem_PSPACE` (ClassPSPACE/TQBF) | Thm 4.13 (membership) | `TQBF ∈ PSPACE` | `TQBF ∈ PSPACE` | None. |
| 16 | `TQBF_PSPACEHard` (same) | Thm 4.13 (hardness) | `TQBF` is PSPACE-hard under polynomial-time reductions | `PSPACEHard TQBF` | None (Karp reductions, Def 4.9). |
| 17 | `TQBF_PSPACEComplete` (same) | Thm 4.13 | `TQBF` is PSPACE-complete | `PSPACEComplete TQBF` | None. |
| 18 | `space_universal` (SpaceComplexity/Hierarchy) | Ex 4.1 | A universal TM simulating `M` with space overhead `C_M · s` | One machine `SU`. For each code `α` there is `C > 0` such that whenever `M_α` computes `y` from `x` in time `t` using at most `s` cells, `SU` computes `y` from `⟨bin(s), ⟨α, x⟩⟩` in at most `C · s` cells | `SU` receives the space bound `s` in binary as part of its input; the book leaves the interface open. The constant depends on `α`, as in the book. |
| 19 | `space_hierarchy` (same) | Thm 4.8 | For space-constructible `f, g` with `f = o(g)`: `SPACE(f) ⊊ SPACE(g)` | Space-constructible `f, g` with `f = o(g)`: `SPACE f ⊂ SPACE g` | None. |
| 20 | `LOGSPACE_ssubset_PSPACE` (same) | §4.3.2 | `L ⊊ PSPACE` | `LOGSPACE ⊂ PSPACE` | None. |
| 21 | `SPACE_linear_ne_NP` (same) | Ex 3.2 (as cited) | `SPACE(n) ≠ NP` | `SPACE (n+1) ≠ NP` | `n + 1` for `n` (row 4). The docstring cites Exercise 3.2; the auditor may confirm the exercise number. |
| 22 | `PATH_mem_NL` (SpaceComplexity/Logspace/Path) | §4.1.2 | `PATH ∈ NL` | `PATH ∈ NL` | None. |
| 23 | `PATH_NLComplete` (same) | Thm 4.18 | `PATH` is NL-complete (logspace reductions) | `NLComplete PATH` | None. |
| 24 | `compl_PATH_mem_NL` (Logspace/ImmermanSzelepcsenyi) | Thm 4.20 | `¬PATH ∈ NL` | `PATHᶜ ∈ NL` | None. |
| 25 | `NL_eq_coNL` (same) | §4.3.2 | `NL = coNL` | `NL = coNL` | None. |
| 26 | `NSPACE_compl_eq` (same) | Cor 4.21 (Ex 4.11) | `NSPACE(S) = coNSPACE(S)` for space-constructible `S > log n` | `{L \| Lᶜ ∈ NSPACE S} = NSPACE S` for space-constructible `S` | None (`coNSPACE` written out). |
| 27 | `ladner` (Diagonalization/Ladner) | Thm 3.3 | If `P ≠ NP`, some `L ∈ NP \ P` is not NP-complete | `P ≠ NP → ∃ L ∈ NP, L ∉ P ∧ ¬NPComplete L` | None. `SAT_H_intermediate` gives the explicit `SAT_H`. Ex 3.6(a)(b) is covered (D2). |

**Summary.** 21 rows match the book exactly. Three rows (4, 11, 21) use `n + 1` or `S + 1` to
cover the degenerate value 0. Row 1 is a generalization, with the book form as a separate
theorem. Row 3 strengthens the hypothesis harmlessly. Row 18 fixes an interface that the book
leaves open. No statement is weaker than the book's.
