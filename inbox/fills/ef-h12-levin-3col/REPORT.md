# EF-H12 `ef-h12-levin-3col` — checkpoint 1

**Head:** `d2272e8e4711abff21ee1547de767a04ddde75a2` on local `fill/ef-h12-levin-3col`.
**Base:** REC `cf6a2266e9556ca8ad61e56f7232266ccc6d4e62`, tree `d52cf05bb20c08b6547468d1bd489f1cf0d2e442`.
The commit and tree were checked with `git rev-parse`; no E-BASE.
**Worker:** Claude (cloud). Lead plus three sub-agents, A, B and C.

## Status

**Claimed by this checkpoint:** steps 1 and 2 compile, with no `sorry` and standard axioms only. Steps 3 and 4 also compile, but only partly.

| File | Content | State |
|---|---|---|
| `LevinHardness/Relations.lean` | `R_CKT`, `R_3SAT` and their readers | done |
| `LevinHardness/Verifier.lean` | step 1: certificate, verifier in `P`, tableau instance map, `exists_tabReduction` | **done** |
| `LevinHardness/CircuitWitness.lean` | step 2: wire values as a poly-time witness, `R_3SAT_wireValues`, `exists_R_3SAT_iff` | **done** |
| `LevinHardness/Gadget.lean` | the `Fin N` layout of the course gadget graph | done |
| `LevinHardness/ColoringWitness.lean` | step 4: the explicit colouring (re-derived, disclosed), properness, poly-time `colorWord` | done |
| `LevinHardness/ColoringGraph.lean` | step 3: `memS`/`goodS` specs, `k4`, `colorInst`, the adjacency emitter, `vertexEquiv` | partial |
| `LevinHardness/Bridge.lean` | quarantined readers for frozen definitions that have none (user ruling, below) | done |

Step 3 is partial because the unconditional poly-time `memS`/`goodS` are still in progress with sub-agent B (`ColoringParse.lean`). The iso to `ReductionGraph` and step 5 (padding, assembly, headline, corollaries) are outlined below. The facades are not yet written.

## Base check, environment, pool

- **Inputs.** All nine SHA-256 values in COMMON §1 match, read at records commit `54dcb3021a389831e7f94c3f82616cb7594fa574`.
- **Preflight** (`evidence/logs/preflight.log`):
  - `nproc` = 4.
  - cgroup v1 limit = no limit, so the headroom is `MemAvailable` ≈ 15.6 GB (≥ 4 GiB).
  - `/` ext4 had 21.4 GB free (≥ 12 GiB).
  - elan was installed with toolchain `v4.25.0`.
- **Cache** (narrowed fetch only):
  - 78 roots: 2107 files downloaded and decompressed. The store was empty before (`cache-store.log`).
  - Extension of 7 roots: 3 files downloaded, 905 decompressed.
  - No zero-size oleans.
  - Packages check `PACKAGES CHECK: PASS`. `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean` are ABSENT.
- **Bootstrap.**
  - 289 modules, built in dependency order: 207 + 82 (`order-prefix2.txt`).
  - Pool of 3 = min(4, MemAvailable/4 GB).
  - 0 failures. Peak RSS was 2.94 GB (`ThreeColoring/Simulator`).
- **Pool sharing.** The pool is a `flock` semaphore with 3 slots (`tools/lean_slot.sh`), shared by the lead and every sub-agent. Each agent has its own olean tree. Sub-agent trees were seeded from the lead tree only for modules with byte-identical sources. See `evidence/logs/pool.log` and `pool-slot-usage.log`.
- **Builds.** `lake build` was never run, nor an unfiltered `cache get`. Every module was compiled through `scripts/lean_check_tree.sh`.

## Who did what

| Agent | Work |
|---|---|
| Lead | Relations, Gadget, Verifier, Bridge; integration, all commits, checks, delivery. Re-pointed A's target 2 to `Bridge.toCNF_eq`. |
| A | `CircuitWitness.lean`, reviewed and integrated by the lead |
| B | `ColoringGraph.lean` (in progress: `ColoringParse.lean`, `UnaryArith.lean`) |
| C | `ColoringWitness.lean` |

Sub-agent reports are in `evidence/subagents/<X>/`. A's and B's hand-backs were recorded by the lead, because their harness refused the file write.

## E-SCOPE and the user's ruling (Rule 10)

**The problem.** The headline needs to read definitions in frozen files that publish no readers:
- all of `NPReductions/ThreeSATToColoring.lean` (course material);
- `CNF.WidthAtMost`, `CNF.numVars` (`Formulas/CNF.lean`);
- `DAGCircuit.toCNF` (`DAGCircuitSat.lean`);
- the CNF serialization, `decode`/`fallback` and `syntaxStep`/`syntaxOK` (`Formulas/CNFEncoding.lean`).

**What I avoid.** I route around the missing readers of `Complexity.SAT3`, `DAGCircuit.Satisfiable` and `CktSatReduction.descTail`, and never read those definitions.

**Ruling.** I raised the E-SCOPE with the user, who ruled **"Readers in our files"**. Each missing reader is stated once, with the content its owner would publish, proved by `rfl`/`Iff.rfl`, in the quarantined `LevinHardness/Bridge.lean`.
- `Bridge.lean` is the only file of the job that sees through these definitions.
- Its module docstring tabulates every reader with its owner file.
- These are **scope requests**: an owner PR adding the same one-line readers lets `Bridge.lean` be deleted and its consumers re-pointed one-for-one.

## Target map (so far)

| Brief target | Declaration |
|---|---|
| `certOf`, readers | `certOf`, `certOf_eq`, `length_certOf`, `splitAtLastTrue_certOf` |
| `decodeCert` | not defined: it would wrap `Turing.splitAtLastTrue` (no-wrapper rule). `splitAtLastTrue_certOf` is the reader. |
| verifier in `P` | `verTest`, `verTest_pairEncode`, `polyTimeComputable_verTest`, `verLang_mem_P` |
| `f₁`, poly-time, membership, witness | `tabInst`, `polyTimeComputable_tabInst`, `tabInst_eq`, `tabCkt_eval`, `exists_tabReduction` |
| `R_CKT`, `R_3SAT` | `Relations.lean` |
| `w₂` (wire values) | `wireValues`, `wireValues_getD`, `polyTimeComputable_wireValues`, `R_3SAT_wireValues`, `exists_R_3SAT_iff` |
| `mem_SAT3_iff_exists_R_3SAT` | **replaced** (Statement changes) |
| `c_a`, properness, `w₃` | `gadgetColor`, `properColoring_gadgetColor`, `colorWord`, `polyTimeComputable_colorWord` |
| gadget graph, `f₃` | `gadgetGraph` (Gadget), `colorInst`, `encGraph_gadgetGraph`, `polyTimeComputable_colorInst_of` (conditional, pending) |

Polynomials of step 1:
- certificate length `m = q + 1`, where `q` is the `WitnessRelation.bounded` polynomial;
- tableau time `t(n) = verTime C c m n = C (2n + 3 + m(n))^c + 1`, where `C (N + 1)^c` is the verifier machine's time bound.

## Statement changes

1. **`mem_SAT3_iff_exists_R_3SAT` is replaced.**
   - Reason: `Complexity.SAT3` has no reader.
   - New form: `exists_R_3SAT_iff : C.IsFaninTwo → ((∃ a, R_3SAT (dagCktSatToSAT3 C.encode) a) ↔ ∃ x, C.eval x = true)`.
   - The composite membership never mentions `SAT3`. It runs `x ∈ L ↔` (tableau satisfiable) `↔ ∃ a, R_3SAT … ↔` (`f₃ … ∈ L3COL`).
2. **The verifier language does not test `|u| = m(|x|)`.** The circuit has exactly `m(|x|)` inputs, so the test is redundant.
3. **The hard-wired prefix is `⟨x, []⟩`, not `x`.** The verifier then reads a pair (`BinArith.pairEncode_nil_append`) and needs no length-split search.

## Overlap and reuse (so far)

- **(a)** `Verifier.lean` re-instantiates the core of `dagCktSatLang_NPHard`'s proof (`CircuitSatNPHard.lean:93-127`). This is disclosed in its module docstring.
- **(b)** `ColoringWitness.lean` re-derives `sat3Coloring`/`clauseGadgetColor`/`SATtoColorCompleteness` (`ThreeSATToColoring.lean:163-193`), per Q-H12-3 A. This is disclosed.
- **(c)** `R_3SAT` states publicly the convention of the private `satAssignment` (`ClassNP/SAT.lean`).
- **Bridge.** Disclosed Rule-10 exception per the user's ruling.
- **Reused:**
  - from the catalog: `computesFunInTime_stripLast` and `pairValid`;
  - `PolyHierarchy.splitAtLastTrue_marker`, `CircuitEval.ofFn_getD_eq_take`, `ComposeMachines.polyTimeComputable_flatMap_range` (the tabulation host);
  - `CVALPrefix`'s verdict machine, `TQBFHard.dagCktSatToSAT3_encode`, `toCNF_extension_iff`;
  - EncodingMachines unary rows.
- **Known private cross-file duplicates, to remove before the final:** the unary helpers in C's and B's files (div/mod by a constant, `clauseLit`/`litVal` at unary indices). B is moving them to a public `UnaryArith.lean`.
- **Flag: sorried rows in FormulaKit.** `polyTimeComputable_unary_sub/mul/le/div/mod` in `FormulaKit/Emit.lean:216-271` are `sorry`. They are not used here; the EncodingMachines rows are used instead.

## Outlines of the remaining steps

**Step 3** (B, in progress):
- an unconditional poly-time `memS`/`goodS`: the grammar automaton through `polyTimeComputable_transduce`, a bounded search over formula-level boundaries for the clause record, and widths;
- the variable bound through `Bridge.numVars_eq` and `numVars_decode_le`;
- then `polyTimeComputable_colorInst`.

**Iso** (lead), from `Bridge` readers:
- the statement is `gadgetSimpleGraph K mem ≃g ReductionGraph ((finRange ((2K)^3)).filter mem).map (clauseEquiv K)` along `vertexEquiv K`;
- membership: colourable gadget graph ⇒ `IsSatisfiable` ⇒ the CNF is satisfied.

**Step 5** (lead, `Padding.lean` + `Hardness.lean`):
- pad with isolated vertices to exactly `B(|x|)` vertices, where `B(n) = gadgetN(P(n)) + n + 4` and `P` bounds `|f₂(f₁ x)|` (`PolyTimeComputable.output_length_le`);
- then `p = B²`;
- colouring padding with colour 0;
- `levinNPHard_L3COL` and the two `_unconditional` corollaries.

## Questions for Seyoon

- **EF-H12-W1.** Approve the bridge readers as a recorded Rule-10 exception until owner PRs add them? **(A, recommended)** Yes, scope requests listed. (B) Hold the line for owner PRs first.

## Evidence

- `evidence/build/summary.txt` (rc, errors, `sorry` warnings, SHA-256 bound to `git show HEAD`) and per-module logs;
- `evidence/axioms/cp1.log`;
- `evidence/logs/*` (preflight, cache, packages, bootstrap, pool, C13 replay);
- `evidence/subagents/*`, `evidence/tools/*`.
- `patches/` + `COMMITS.tsv` reproduce the head at the base (`evidence/logs/c13-replay.txt`).
