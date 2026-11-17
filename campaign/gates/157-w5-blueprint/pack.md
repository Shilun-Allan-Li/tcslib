# Gate 157 · W5: the blueprint for chapters 3–4 (PR to be opened from `closeout/w5-blueprint`)

**A light audit** (PLAN W5) of a records-and-blueprint PR. It contains no Lean change. Seyoon
dispatches and merges.

- **Head:** branch `closeout/w5-blueprint`; the dispatch prompt gives the commit. It is based on
  campaign Lean `179c8c9c` (the #356 merge, W4), and its Lean equals that merge's.
- **Writers:** Seyoon chose Claude in this session (2026-11-17), using the repository's
  `/blueprint-extract` pipeline: one `blueprint-writer` subagent per module or module part, at
  most five at once. The maintainer reviewed each chapter as it came in.
- **Scope:** Seyoon chose all declarations, private ones included (2026-11-17), to match the
  pipeline default and the existing chapters.

## What changes

The scope is the chapter scope of the closeout plan (PLAN §1): the modules under ClassOracle,
ClassPSPACE, Diagonalization, SpaceComplexity and TimeHierarchy. 36 of them had undocumented
declarations, **896 in all**: Diagonalization 490, SpaceComplexity 389, TimeHierarchy 17.
ClassOracle and ClassPSPACE were already covered. 214 of the 896 are public and 682 are private.
The pipeline's planner now finds **no undocumented declaration in scope**.

- **New chapters (5):**
  - `Diagonalization/NTimeDiagonalizer.tex`, 318 entries, written in 4 sequential parts;
  - `Diagonalization/Ladner.tex`, 152 entries, in 2 parts;
  - `SpaceComplexity/Padding.tex`, 52 entries;
  - `SpaceComplexity/SavitchARM/Deepen.tex`, 45 entries;
  - `SpaceComplexity/SavitchARM/Window.tex`, 6 entries.

  They are mapped in `blueprint/organization.json`: Ladner and NTimeDiagonalizer under "Time
  hierarchies and diagonalization", Padding under "Space bounds and complexity classes", Deepen
  and Window under "Savitch's theorem". `scripts/blueprint_assemble.py` regenerated the three
  textbook wrappers (`chapter/textbook/*.tex`).
- **Appended to 31 existing chapters:** 323 entries. The large ones are WindowClock 64,
  SpaceComplexity/Hierarchy 61, Codec/Machine 37, TimeHierarchy/Diagonal 17 and NTimeHierarchy
  20. Existing entries are unchanged, except for the fixes below.
- **Stale existing entries fixed:**
  - In Codec/Machine, `CMode` now has five modes, the `CpId`, `ScId` and `IcId` label lists match
    the Lean, and `jLen`/`jBit` had a broken `\text` repaired.
  - **71 entries removed** whose declarations no longer exist: the 64 `ConfigCodec` entries in
    TQBF (the RD-2 removal, #328), `expcom_all_true`, `bits_succ_le` and `drop_pairEncode`, plus
    four whose declarations moved to homes that already have entries.
  - **6 entries retargeted** to moved declarations: `Codec.two_pow_bits_le` became
    `LogProg.two_pow_bits_le` (NatBits), and `oracleRelabel*` became `Turing.OracleTM.relabel*`
    (stage 1, MIG-10). Their statements are unchanged.
  - `\uses` references follow: 22 rewritten, 3 dropped (`evidence/ORPHAN-FIX.json`).
- **Net:** 51 files, +825 entries (896 written − 71 removed).
- **Entry format:** `\lean{<name>}`, `\label{<name>}`, `\leanok`, `\uses{…}` (the planner's
  intra-project dependency list), and `\difficulty` on theorems and lemmas only. Descriptions
  state the claim, never the proof, and each introduces its own objects.

## Brief for the auditor

1. **Fidelity.** For each new or changed entry, check that the prose states what the Lean
   declaration says: hypotheses, conclusion, and, for definitions, the object defined. The Lean
   sources of the documented modules are in the bundle. Sample as you see fit; a full check is
   not required for a light audit. The writers flagged these as their least exact (summaries,
   not misstatements):
   - Ladner: `ladner_query_budget`, `ladner_simulation_on_image`, `ladner_memo_readout`;
   - NTimeDiagonalizer: `qy_clocked_call`, `QyClockSpec`, `qy_clockHost_finish`,
     `qy_clockHost_timeout`, `qy_expandHost`, `qy_seekHost`, `qy_main_long`, `qy_main_short`,
     `qy_loop`, `dz_kit_exists`, `DzKit`, `dzQRed`, `DzQPh`, `DzPPh`;
   - Padding: `epadValCode`, `epadBA`, `EPadBX`;
   - Hierarchy: the `f6_*` lemmas and `sph_runner_run`, `sph_initial_record`,
     `sph_record_size`;
   - Codec/Machine (new entries): the label `icL`;
   - TimeHierarchy/Diagonal: `code₂`, `twoTapeSelfSimulator_W`.
2. **Removals and retargets.** Confirm that each removed entry's declaration is absent from the
   Lean at `179c8c9c`, and that each retargeted entry's prose matches its new declaration.
3. **Mechanics.** Check the evidence below: validation, coverage and the dependency graph.

## Evidence (`evidence/`)

- **`VALIDATE.txt`:** `scripts/blueprint_validate.py`, run against the refreshed dependency
  graph.
  - **0 dangling `\uses`, 0 duplicate bindings, 0 `\uses` cycles.**
  - **1,572 "orphan" labels**, none in the chapter scope. Corrected in round 2: see
    `resolutions.md` G157-03 and `evidence/ORPHANS-CLASSIFIED.json`.
- **`COVERAGE.json`:** the 896 declarations by module.
- **`WORKPLAN.json`:** the 40 writer jobs and their order.
- **`DEP-GRAPH.json`:** how the graph the planner reads was rebuilt.
  - **Ilean pass:** each of the snapshot's 898 library modules was compiled once more with
    Lean's `-i` flag, to write the reference index. All passed, with a pool of 3 and the same
    slot locks (`leanelab-i.sh.txt`, the approved `leanelab.sh` plus `-i`).
  - **Graph:** `build_tcslib_graph.py.txt` rebuilt the TCSlib part of `dep_graph.json` from those
    files. Entries for other projects and for modules outside the snapshot were kept.
  - **Kept out of the PR:** the committed `dep_graph.json` is unchanged, because the repository's
    builder also expects an external dataset project (FABL) that is not available here. Its
    SHA-256 is recorded.
- **No Lean, so no replay, seals, controls or copy screen.**

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate157-w5-blueprint-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
