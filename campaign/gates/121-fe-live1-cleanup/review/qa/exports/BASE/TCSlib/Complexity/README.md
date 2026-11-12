# `TCSlib/Complexity`

Computational complexity theory, following S. Arora and B. Barak, *Computational Complexity: A
Modern Approach* (Cambridge University Press, 2009; cited as [AB09] in the docstrings). Every
result's docstring names its source in the book.

## Chapters 3–4: what is proved

The headline theorems of [AB09] chapters 3 (diagonalization) and 4 (space complexity) that the
library states, with their status. **Proved** means that `#print axioms` reports only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`. Paths are relative to
this directory.

**19 of 26 are proved.**

| Theorem | [AB09] | File | Status |
|---|---|---|---|
| `Complexity.time_hierarchy` | Theorem 3.1 | `TimeHierarchy/Diagonal.lean` | proved |
| `Complexity.P_ssubset_EXP` | §3.1, from Theorem 3.1 | `TimeHierarchy/Separation.lean` | proved |
| `Complexity.exists_not_timeConstructible` | Exercise 3.5 | `Diagonalization/NotTimeConstructible.lean` | proved |
| `Complexity.ntime_hierarchy` | Theorem 3.2 | `Diagonalization/NTimeHierarchy.lean` | open (see below) |
| `Complexity.NTIME_linear_ssubset_square` | §3.2, the displayed instance | `Diagonalization/NTimeHierarchy.lean` | open (see below) |
| `Complexity.POracle_EXPCOM_eq_EXP` | Example 3.6(3) | `Diagonalization/EXPCOM.lean` | proved |
| `Complexity.NPOracle_EXPCOM_eq_EXP` | Example 3.6(3) | `Diagonalization/EXPCOM.lean` | proved |
| `Complexity.baker_gill_solovay` | Theorem 3.7 | `Diagonalization/Relativization.lean` | proved |
| `Complexity.exists_oracle_ne` | Theorem 3.7 | `Diagonalization/Relativization.lean` | proved |
| `Complexity.NSPACE_subset_exp_dtime` | Theorem 4.2 | `SpaceComplexity/ExpTime.lean` | proved |
| `Complexity.NL_subset_P` | §4.1.2 | `SpaceComplexity/ExpTime.lean` | proved |
| `Complexity.NP_subset_PSPACE` | Example 4.6 | `SpaceComplexity/Inclusions.lean` | proved |
| `Complexity.space_hierarchy` | Theorem 4.8 | `SpaceComplexity/Hierarchy.lean` | open |
| `Complexity.LOGSPACE_ssubset_PSPACE` | §4.3.2 | `SpaceComplexity/Hierarchy.lean` | open |
| `Complexity.SPACE_linear_ne_NP` | Exercise 3.2 | `SpaceComplexity/Hierarchy.lean` | open |
| `Complexity.space_universal` | Exercise 4.1 | `SpaceComplexity/Hierarchy.lean` | open |
| `Complexity.TQBF_mem_PSPACE` | Theorem 4.13 | `ClassPSPACE/TQBF.lean` | proved |
| `Complexity.TQBF_PSPACEHard` | Theorem 4.13 | `ClassPSPACE/TQBF.lean` | proved |
| `Complexity.TQBF_PSPACEComplete` | Theorem 4.13 | `ClassPSPACE/TQBF.lean` | proved |
| `Complexity.savitch` | Theorem 4.14 | `SpaceComplexity/Savitch.lean` | open |
| `Complexity.PSPACE_eq_NPSPACE` | §4.2.1 | `SpaceComplexity/Savitch.lean` | proved |
| `Complexity.PATH_mem_NL` | §4.1.2 | `SpaceComplexity/Logspace/Path.lean` | proved |
| `Complexity.PATH_NLComplete` | Theorem 4.18 | `SpaceComplexity/Logspace/Path.lean` | proved |
| `Complexity.compl_PATH_mem_NL` | Theorem 4.20 | `SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean` | proved |
| `Complexity.NSPACE_compl_eq` | Corollary 4.21 | `SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean` | proved |
| `Complexity.NL_eq_coNL` | §4.3.2 | `SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean` | proved |

**The open items.**
- `ntime_hierarchy` and `NTIME_linear_ssubset_square` are proved from two lemmas whose proofs are
  in progress: the lazy diagonalizer `Turing.NTimeDiag.exists_diagonalizer`
  (`Diagonalization/NTimeDiagonalizer.lean`) and the linear-overhead normal form of a
  nondeterministic machine, `Turing.FinNDTM.exists_codeNDTM_accepts_linear`
  (`ClassNP/NDNormalForm.lean`).
- `space_hierarchy`, `LOGSPACE_ssubset_PSPACE`, `SPACE_linear_ne_NP`, `space_universal` and the
  general `savitch` (for every space-constructible bound) are stated, with proof sketches, and not
  yet proved. `PSPACE_eq_NPSPACE` is proved directly, without the general `savitch`.

Other statements in the directory may also be unproved; `#print axioms` on any declaration
settles its status.

## What else is here

- **Machines** (`TuringMachine/`): multi-tape deterministic, nondeterministic and oracle machines,
  their runs, codes and universal machines, and a construction library (`TuringMachine/Build/`) of
  machines with their run contracts: copies, scans, counters, clocks, seams and phase hosts.
- **Classes and their readings**: time (`ClassP/`, `ClassNP/`), space (`SpaceComplexity/`),
  oracles (`ClassOracle/`), `PSPACE` (`ClassPSPACE/`) and the polynomial hierarchy
  (`PolyHierarchy/`). The classes come with lemmas stating their definitions as equivalences
  (for instance `Complexity.mem_SPACE_iff`, `Complexity.mem_NP_iff_exists_length_le`), so that
  proofs elsewhere need not unfold them.
- **Reductions and completeness**: Karp reductions and the closure of `P` under them
  (`ClassNP/Reductions.lean`), Cook–Levin (`CookLevin/`), and further `NP`-complete problems
  (`NPReductions/`).
- **Other chapters**: circuits (`CircuitComplexity/`), randomized computation (`Randomized/`),
  expanders (`Expanders/`) and uncomputability (`Uncomputability/`).
