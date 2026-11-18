# Gate 163 · RAM tier 3: the nine class corollaries (PR #373)

**Not yet clear to merge.** PR #373 is a draft into `complexity/ram-simulation`. Seyoon
dispatches and merges.

- **Lean head:** `1ababb822cd0aff5fa841239e140f0fb60a77f48` (branch `ram/fill-classes`): one commit
  on the RAM branch's Lean `adb694d2` (#371 merged), landing the Codex fill `fill-ram-classes`
  unchanged.
- **Delivery** (exchange `arora-barak-ch3-4/inbox/fill-ram-classes/`): `fill-ram-classes.zip`
  SHA-256 `8f7d8c1274ec46727d711cecba0040ad9fc2b93b5571cf5c4bb4f86abede7279`.
  - Its manifest verifies.
  - The patch applies to its base and reproduces the delivered file byte for byte.
  - The report is bundled (`evidence/REPORT-tier3.md`).
- **Base:** the fill was built on #371's head `24aa4050`. `Classes.lean` is byte-identical
  between that base and the RAM branch after #371's merge, and the fill's recorded base copy
  matches it.

## What changes

`RAMSimulation/Classes.lean` (360 lines, +203/−35). All nine corollaries are proved:
- `mem_DTIME_of_decides`, `mem_P_of_decides`, `mem_P_of_decides_logWord`;
- `mem_SPACE_of_decides`, `mem_LOGSPACE_of_decides`, `computesInSpace_of_computes`,
  `mem_SPACE_mul_of_decides`;
- `mem_NSPACE_of_accepts`, `mem_NL_of_accepts`.

**How they are proved:**
- Each applies `exists_simulation` (verdict or function mode) or `exists_ndSimulation`. It reads
  the output, deadline and space through the readers of #370, and packages the witness through
  the class readers with the constant `(A + 1)·a`.
- Four private arithmetic lemmas: `simulation_constant_bound`, `simulation_space_bound`,
  `logarithmic_space_bound`, `polynomial_time_bound`.
- The P grade uses tier 0's `HaltsWithin.touches_le` and `HaltsWithin.mono`. The logarithmic and
  Savitch grades use tier 1's two word-size witnesses.

**Freeze:** statements, imports, options and the header are byte-identical (`SOURCE.json`: 1
owner; 13 changed or added declarations, all bodies or the 4 private lemmas; none added
publicly, none removed; no header or definition change). Only the proof sketches and the module
docstring's "proofs pending" note changed.

**Admissions:** after this PR the RAM work's only admissions are the two tier 2 targets, whose
statements are frozen. Every corollary still reaches one of them:

| Target | Admitted declarations reached |
|---|---|
| the seven deterministic grades | `WordRAM.exists_simulation` only |
| `mem_NSPACE_of_accepts`, `mem_NL_of_accepts` | `WordRAM.exists_ndSimulation` only |

This is the maintainer's own dependency walk on the replay's output (`evidence/AdmissionWalk.out`,
probe `AdmissionWalk.lean.txt`): every constant reachable from a target, whose type or value uses
`sorryAx`. It agrees with the fill's walk (`REPORT-tier3.md`).

## Brief for the auditor

1. **Proofs.** Check each of the nine proofs and its sketch, and the four private lemmas. The
   arithmetic must hold at every `n`, `n = 0` included, and for `c = 0`, `F₀ = 0`, `d = 0`.
2. **Readers (rule 10).** The report lists the 26 foreign definitions reached and the reader
   used for each. The evidence below seals them.
3. **Freeze.** Check that the nine statements and the file's header are byte-identical to the
   base.
4. **Admissions.** Check that each target reaches only the admission shown above, so that the
   corollaries become unconditional exactly when tier 2 lands.
5. **Duplication.** Review the three copy-screen pairs and their dispositions.

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay of the owner's downstream closure (the file and the
  `RAMSimulation` facade) on `oleans-cl161-cl160`, the branch's build after #371. 2 modules:
  2 passed, 0 failed, 0 inherited admissions in the replayed sources.
- **Seals:** the 13 changed proofs pass with every foreign definition they reach sealed (26
  heads).
- **Controls:** 37 definitions and 74 identities, each native-PASS and sealed-FAIL.
- **The metadata check** now admits `sorryAx` in a proof's axioms only when the gate names the
  inherited admissions (`gate.json`: `exists_simulation`, `exists_ndSimulation`). The dependency
  walk above shows which admission each proof reaches. This is a kit change made at this gate.
- **Sweeps:**
  - the proof-syntax sweep: 13 roots, 0 read candidates;
  - the Lean-backed sweep: no foreign definition among the owner's identifiers.
- **Citation homes** (`CITATION-HOMES.json`, plus those cited in dot notation, which the probe
  does not resolve, gate 161's G161-01): every home is in the bundle.
  - Simulation, WordSize and Extended;
  - ClassP/DTIME and ClassP/P;
  - SpaceComplexity/Basic, Constructible, NSPACE and SpaceClasses;
  - TuringMachine/Finite.
- **Copy screen** (population: the owner): 0 → 3 directed pairs, all within the file, each
  dispositioned (`pair-notes.json`). The LOGSPACE and NL grades, and the DTIME and SPACE grades,
  instantiate the same simulation witness through the same readers.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate163-ram-fill-classes-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
