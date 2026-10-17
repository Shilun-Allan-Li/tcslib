# PR #120's body, as retrieved 2026-10-17 (head `6d18902f`)

**C1's normal form gets its own module.** Per the user's ruling of 2026-10-17 (C1's fill plan, question 3, `audits/evidence/c1/C1-fill-plan.md`), `Turing.FinNDTM.exists_codeNDTM_accepts_linear` (NF, the linear-overhead coded normal form) moves from `Diagonalization/NTimeHierarchy` into a new `ClassNP/NDNormalForm`. Two workers cannot share a file, and `NTimeHierarchy` also holds the universal machine's brief (UN with BF, H′ and S). After the move, NF's fill can run alongside it. **It gets a short gate before it merges.**

**Stacked on #119** (so the replays chain): **merge #118, then #119, first.**

| File | Change |
|---|---|
| `ClassNP/NDNormalForm` (new) | NF's declaration with its docstring, byte-identical (2,599 characters), still `sorry`; imports `ClassNP/NTIME` and `TuringMachine/NDCodes`, as `ExhaustiveReplay` does; a module docstring |
| `Diagonalization/NTimeHierarchy` | the declaration removed; `import TCSlib.Complexity.ClassNP.NDNormalForm`; the Main-results and design paragraphs point to the new home |
| `ClassNP` (facade) | lists the new module |

**About the plan's wording:** the plan described a copy under a new name, with `NTimeHierarchy`'s theorem becoming a one-line citation. This PR moves the declaration itself instead, under its existing name, so the library keeps one public statement rather than two identical ones. Consumers reach it through the new import. If you prefer the citation form, it's a two-line change.

**Checks (maintainer, against `oleans-lbapi4`):**

| Check | Result |
|---|---|
| Move | the moved declaration is byte-identical to the old one (asserted) |
| Elaboration | `NDNormalForm` alone: 0 errors, 1 warning (NF's `sorry`). The two modules' bodies in one check file (since `NDNormalForm` has no olean yet): 0 errors, the six `sorry` warnings of the base `NTimeHierarchy` |
| Freeze | `NTimeHierarchy`: public removed `exists_codeNDTM_accepts_linear` only; `NDNormalForm`: public added the same |
| Lint | 0 FAIL; `ClassNP/` 15 WARN, as before (21 files), `Diagonalization/` 1 WARN, as before |

**Replay (user):** `replay-lndnf.sh`, the new module, `NTimeHierarchy` and the two facades (4 modules), from `oleans-lndapi` (#119's replay).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

