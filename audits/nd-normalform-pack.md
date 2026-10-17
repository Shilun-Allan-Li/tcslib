# External audit pack — C1's normal form in its own module (PR #120)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09, Theorem
3.2]). C1's fill plan (`audits/evidence/c1/C1-fill-plan.md`) puts each stub of `NTimeHierarchy` in
front of a fill worker, and two workers cannot share a file. The user's ruling of 2026-10-17 (the
plan's question 3) moves the linear-overhead coded normal form (NF) into a new module, so its fill
(2.5–5k lines) can run beside the universal machine's (UN, with BF, H′ and S) in `NTimeHierarchy`.

- **The head:** `lean/nd-normalform` at `6d18902f`: one commit (`95a3b6a0`) on #119's first commit,
  merged with #119's two later commits. Its Lean diff from #119's head `1e45f50a` is three files.

| File | Change |
|---|---|
| `ClassNP/NDNormalForm` (new) | `Turing.FinNDTM.exists_codeNDTM_accepts_linear` with its docstring, byte-identical, still `sorry`; imports `ClassNP/NTIME` and `TuringMachine/NDCodes`, as `ClassNP/ExhaustiveReplay` does; a module docstring |
| `Diagonalization/NTimeHierarchy` | the declaration removed; `import TCSlib.Complexity.ClassNP.NDNormalForm`; the Main-results and design paragraphs point to the new home |
| `ClassNP` (facade) | lists the new module |

- **A disclosed deviation from the plan's wording:** the plan described a copy under a new name with
  `NTimeHierarchy`'s theorem as a one-line citation. The PR moves the declaration itself, under its
  existing name, so the library keeps one public statement, not two identical ones.
- **Evidence:** `audits/evidence/nd-normalform/` (NOTES, the move script, the logs, the freeze, the
  lint, the replay closure and script, the patch).
- **The bundle** also contains `ClassNP/NDNormalForm`, `Diagonalization/NTimeHierarchy` and the
  `ClassNP` facade at the head, the old `NTimeHierarchy` at #119's head, and the P3.3 statement gate's
  records for NF's statement.

## Brief for the auditor

1. **The move is exact.** The declaration and its docstring are byte-identical in the new module
   (`move.py.txt` asserts it). No statement changes, nothing else is removed, and the new module's
   imports suffice. Is the moved statement's meaning unchanged? Check the namespaces (`Turing.FinNDTM`)
   and the elaboration context: the options, and the imports' definitions of `CodeNDTM`,
   `FinNDTM.AcceptsWithin`.
2. **No consumer breaks.** Every use of the name resolves through the new import. The hierarchy's
   sketch cites NF by name.
3. **Placement.** Is `ClassNP/` the right home, beside `ExhaustiveReplay`, given that NF's statement
   lives at the `FinNDTM` level and its acceptance comes from `ClassNP/NTIME`?
4. **The deviation** above: is moving rather than copying acceptable?
5. **Records:** do the NOTES, this pack and the PR body agree with the evidence?

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lbapi4`): `NDNormalForm` alone has 0 errors and 1 warning (NF's
  `sorry`). The two modules' bodies in one check file have 0 errors and the six `sorry` warnings of
  the base `NTimeHierarchy`, because the new module has no olean before the replay.
- **Freeze:** `NTimeHierarchy` loses only NF's public, and `NDNormalForm` adds it.
- **Lint:** 0 FAIL. `ClassNP/` stays at 15 WARN (now over 21 files), and `Diagonalization/` at 1 WARN.
- **Replay:** `replay-lndnf.sh`, 4 modules, chained from `oleans-lndapi` (#119's replay).
  ⟨REPLAY RESULT⟩

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/nd-normalform-findings.md`. The gate closes when it has zero blockers and zero majors.
