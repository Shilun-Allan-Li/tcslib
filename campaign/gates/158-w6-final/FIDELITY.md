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
| 1 | `Complexity.time_hierarchy` (TimeHierarchy/Diagonal:550); book form `Complexity.time_hierarchy_book` (:786) and `time_hierarchy_book_of_pos` (:799); the parameterized core is `Complexity.TimeHierarchy.DiagSimulator.time_hierarchy` (:310) | Thm 3.1 | For time-constructible `f, g` with `f log f = o(g)`: `DTIME(f) ⊊ DTIME(g)` | The tracked headline `time_hierarchy`: time-constructible `g` and `(f(n) + n + 1)² = o(g(n))` give `DTIME f ⊂ DTIME (g + 1)` | **The tracked headline is weaker than the book: it has quadratic overhead.** The book's strength is supplied by the companions. `time_hierarchy_book` gives `DTIME f ⊂ DTIME (g + 1)` for time-constructible `g`, `n ≤ f(n)` and `f(n)·log f(n) = o(g(n))`; `time_hierarchy_book_of_pos` gives `DTIME g` for positive `g`. Both are covered by the extras probe, with standard axioms. (G158-02) |
| 2 | `P_ssubset_EXP` (TimeHierarchy/Separation) | §3.1 (consequence of Thm 3.1; inclusion Claim 2.4) | `P ⊊ EXP` | `P ⊂ EXP` | None. |
| 3 | `Complexity.ntime_hierarchy` (Diagonalization/NTimeHierarchy:1796); positive form `ntime_hierarchy_of_pos` (:1884). Added after round 1, for monotone `f`: `ntime_hierarchy_book` and `ntime_hierarchy_book_of_pos` (:1934 and :1946 at the repair head) | Thm 3.2 | For time-constructible `f, g` with `f(n+1) = o(g(n))`: `NTIME(f) ⊊ NTIME(g)` | Time-constructible `f, g` with `f(n+1) + f(n) + n + 1 = o(g(n))`: `NTIME f ⊂ NTIME (g + 1)` | **A genuine restriction** (G158-01). The extra `f(n) = o(g(n))` follows from the book's hypothesis when `f` is monotone, since then `n ≤ f(n) ≤ f(n+1)`. Neither `TimeConstructible` nor the theorem assumes monotonicity, and the auditor's parity-selected counterexample satisfies the book's hypothesis but not ours. Disposition: §Major below. |
| 4 | `Complexity.NTIME_linear_ssubset_square` (same, :1912) | §3.2, p. 70 (illustration after Thm 3.2) | `NTIME(n) ⊊ NTIME(n^{1.5})` | `NTIME (n+1) ⊂ NTIME ((n+1)²)` | **A weaker illustration** (G158-03): the larger class has exponent 2, not 1.5, as the Lean docstring discloses (no ℕ-valued constructible normal form of the fractional power was adopted). `n + 1` for `n` normalizes length 0. |
| 5 | `Complexity.exists_not_timeConstructible` (Diagonalization/NotTimeConstructible) | Ex 3.5 | Some function `T : ℕ → ℕ` is not time-constructible | `∃ T, (∀ n, n ≤ T n) ∧ ¬TimeConstructible T` | **A strengthening** (G158-08): Lean also supplies `T(n) ≥ n`, so the failure is not explained by the `T(n) ≥ n` clause of the definition. |
| 6 | `POracle_EXPCOM_eq_EXP` (Diagonalization/EXPCOM) | Ex 3.6(3) | `P^EXPCOM = EXP` | `POracle EXPCOM = EXP` | None. |
| 7 | `NPOracle_EXPCOM_eq_EXP` (same) | Ex 3.6(3) | `NP^EXPCOM = EXP` | `NPOracle EXPCOM = EXP` | None. |
| 8 | `exists_oracle_ne` (Diagonalization/Relativization) | Thm 3.7 (`B` half) | There is `B` with `U_B ∈ NP^B \ P^B` | `∃ B, unaryWitnessLang B ∈ NPOracle B ∧ unaryWitnessLang B ∉ POracle B` | None; `unaryWitnessLang` is `U_B`. Exercise 3.3 (`B ∈ EXP`) is deferred (W8). |
| 9 | `baker_gill_solovay` (same) | Thm 3.7 | There are oracles `A, B` with `P^A = NP^A` and `P^B ≠ NP^B` | `(∃ A, POracle A = NPOracle A) ∧ ∃ B, POracle B ≠ NPOracle B` | None. |
| 10 | `NP_subset_PSPACE` (SpaceComplexity/Inclusions) | Ex 4.6 | `NP ⊆ PSPACE` | `NP ⊆ PSPACE` | None. |
| 11 | `Complexity.NSPACE_subset_exp_dtime` (SpaceComplexity/ExpTime) | Thm 4.2 (third inclusion) | `NSPACE(S) ⊆ DTIME(2^{O(S)})` for space-constructible `S` | `NSPACE S ⊆ ⋃ c, DTIME (2^{c(S n + 1)})` | None in substance (G158-08). `SpaceConstructible S` forces `S(n) ≥ logSpace(n) ≥ 1`, so `S(n) + 1 ≤ 2S(n)` and the `+1` is absorbed into `c`. It is written so, as the Lean docstring explains, to match the input-head bound. |
| 12 | `NL_subset_P` (same) | §4.1.2 (Ex 4.3's premise) | `NL ⊆ P` | `NL ⊆ P` | None. |
| 13 | `savitch` (SpaceComplexity/Savitch) | Thm 4.14 | `NSPACE(S) ⊆ SPACE(S²)` for space-constructible `S ≥ log n` | `NSPACE S ⊆ SPACE (S · S)` for space-constructible `S` | None (`S ≥ log n` is part of space-constructibility). |
| 14 | `PSPACE_eq_NPSPACE` (same) | §4.2.1 | `PSPACE = NPSPACE` | `PSPACE = NPSPACE` | None. |
| 15 | `TQBF_mem_PSPACE` (ClassPSPACE/TQBF) | Thm 4.13 (membership) | `TQBF ∈ PSPACE` | `TQBF ∈ PSPACE` | None. |
| 16 | `TQBF_PSPACEHard` (same) | Thm 4.13 (hardness) | `TQBF` is PSPACE-hard under polynomial-time reductions | `PSPACEHard TQBF` | None (Karp reductions, Def 4.9). |
| 17 | `TQBF_PSPACEComplete` (same) | Thm 4.13 | `TQBF` is PSPACE-complete | `PSPACEComplete TQBF` | None. |
| 18 | `Complexity.space_universal` (SpaceComplexity/Hierarchy:989) | Ex 4.1, p. 93 | A universal TM `SU(α, t, x)` that, given the space budget `t`, simulates `M_α` on `x` within `C_α · t` space | One machine `SU`. For each code `α` there is `C > 0` such that whenever `M_α` computes `y` from `x` in time `t` using at most `s` cells, `SU` computes `y` from `⟨bin(s), ⟨α, x⟩⟩` in at most `C · s` cells | None in substance (G158-04). The book supplies the budget too; Lean fixes its binary encoding and the pairing order. |
| 19 | `space_hierarchy` (same) | Thm 4.8 | For space-constructible `f, g` with `f = o(g)`: `SPACE(f) ⊊ SPACE(g)` | Space-constructible `f, g` with `f = o(g)`: `SPACE f ⊂ SPACE g` | None. |
| 20 | `LOGSPACE_ssubset_PSPACE` (same) | §4.3.2 | `L ⊊ PSPACE` | `LOGSPACE ⊂ PSPACE` | None. |
| 21 | `SPACE_linear_ne_NP` (same) | Ex 3.2 (as cited) | `SPACE(n) ≠ NP` | `SPACE (n+1) ≠ NP` | `n + 1` for `n` (row 4). The docstring cites Exercise 3.2; the auditor may confirm the exercise number. |
| 22 | `PATH_mem_NL` (SpaceComplexity/Logspace/Path) | §4.1.2 | `PATH ∈ NL` | `PATH ∈ NL` | None. |
| 23 | `PATH_NLComplete` (same) | Thm 4.18 | `PATH` is NL-complete (logspace reductions) | `NLComplete PATH` | None. |
| 24 | `compl_PATH_mem_NL` (Logspace/ImmermanSzelepcsenyi) | Thm 4.20 | `¬PATH ∈ NL` | `PATHᶜ ∈ NL` | None. |
| 25 | `NL_eq_coNL` (same) | §4.3.2 | `NL = coNL` | `NL = coNL` | None. |
| 26 | `NSPACE_compl_eq` (same) | Cor 4.21 (Ex 4.11) | `NSPACE(S) = coNSPACE(S)` for space-constructible `S > log n` | `{L \| Lᶜ ∈ NSPACE S} = NSPACE S` for space-constructible `S` | None (`coNSPACE` written out). |
| 27 | `ladner` (Diagonalization/Ladner) | Thm 3.3 | If `P ≠ NP`, some `L ∈ NP \ P` is not NP-complete | `P ≠ NP → ∃ L ∈ NP, L ∉ P ∧ ¬NPComplete L` | None. `SAT_H_intermediate` gives the explicit `SAT_H`. Ex 3.6(a)(b) is covered (D2). |

**Summary (corrected after gate 158 round 1).** Rows 2, 6–10, 12–17 and 19–27 match the book
under the standing conventions; the auditor checked them (G158-N6). Rows 11 and 18 match in
substance; their earlier divergence notes were wrong. Row 5 is a strengthening. Row 4 is a
weaker illustration, as its docstring discloses. Row 1's tracked headline has quadratic overhead,
and the book's strength comes from `time_hierarchy_book`. **Row 3 is a genuine restriction** for
non-monotone `f`; for monotone `f` the book form is `ntime_hierarchy_book`, added after round 1
(§Major).

## Major (G158-01): Theorem 3.2's hypothesis

AB09 states Theorem 3.2 for time-constructible `f, g` with `f(n+1) = o(g(n))`. The campaign's
`ntime_hierarchy` also needs `f(n) + n + 1 = o(g(n))`. That follows from the book's hypothesis
for monotone `f`, where `n ≤ f(n) ≤ f(n+1)`, but not in general (the auditor's parity-selected
counterexample).

**Disposition (Seyoon, 2026-11-17): add the book form for monotone `f`.** The repair PR adds
two theorems to `Diagonalization/NTimeHierarchy`, mirroring Theorem 3.1's
`time_hierarchy_book` pair:
- `Complexity.ntime_hierarchy_book`: time-constructible `f, g`, `f` monotone and
  `f(n+1) = o(g(n))` give `NTIME f ⊊ NTIME (g + 1)`;
- `Complexity.ntime_hierarchy_book_of_pos`: the same with `g` never 0, giving the book's
  `NTIME f ⊊ NTIME g`.

Both are corollaries of the existing pair through a private lemma: `f(n) ≤ f(n+1)` and
`n + 1 ≤ f(n+1)` give `f(n+1) + f(n) + n + 1 ≤ 3·f(n+1)`. The book does not state
monotonicity, so row 3 now matches the book for monotone `f` and stays a restriction for
non-monotone `f`. The module docstring now records the counterexample. It no longer says that
the linear overhead alone puts the theorem at book strength.
