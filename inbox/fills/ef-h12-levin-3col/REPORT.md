# EF-H12 `ef-h12-levin-3col` — final

**Head:** `c8d5b3c7f8733f3ea87fc701fbc83abc53bdb338` on local `fill/ef-h12-levin-3col` (never pushed). The payload's `patches/` reproduce it at the base.

**Base:** REC `cf6a2266e9556ca8ad61e56f7232266ccc6d4e62`, tree `d52cf05bb20c08b6547468d1bd489f1cf0d2e442`. Checked with `git rev-parse`; no E-BASE.

**Worker:** Claude, cloud. One lead and three sub-agents (A, B, C).

**Merge-tree (information only):** `git merge-tree --write-tree <head> <records tip>` gives ``1bc03206b652f3411c88606b4e30364169358024` (records tip `b7bc1011ba674727816a6e30eb80aa9a7a32bfa4`; a tree hash means no conflict, `evidence/logs/merge-tree.txt`)`.

## Outcome

**`TCSlib.Cryptography.levinNPHard_L3COL : LevinNPHard L3COL R3COL` is proved.** Its axioms are exactly
`[propext, Classical.choice, Quot.sound]`. The proof uses the circuit route of Q-H12-1 A.

The two unconditional corollaries are proved with the same axioms:
- `TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp_unconditional`
- `TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp_unconditional`

R18 therefore moves from MH to M.

**Rule-10 exception (user ruling, disclosed).** The proof reads frozen definitions that publish no reader. The user
ruled "readers in our files" on the E-SCOPE raised during the job. Each missing reader is stated once, by
`rfl`/`Iff.rfl`, in the quarantined `LevinHardness/Bridge.lean`; the scope requests are below. `NP.lean`, every
`Complexity/**` file and every existing ZeroKnowledge file are unchanged.

## Files

| File | Lines | Content | Author |
|---|---|---|---|
| `ZeroKnowledge/LevinHardness/Relations.lean` | 77 | `R_CKT`, `R_3SAT` and their readers | lead |
| `…/Bridge.lean` | 224 | 27 quarantined readers of frozen definitions (table in the module docstring) | lead |
| `…/Verifier.lean` | 335 | step 1: `certOf`, `verTest` in `P`, `tabCkt`/`tabInst`, `exists_tabReduction` | lead |
| `…/CircuitWitness.lean` | 426 | step 2: `retarget`, `wireValues` (poly-time), `R_3SAT_wireValues`, `exists_R_3SAT_iff` | A, lead |
| `…/Gadget.lean` | 181 | the course gadget graph laid out on `Fin N` (`gadgetN`, `gadgetEdge`, `gadgetAdj`, `gadgetGraph`, `litVal`, `clauseSat`) | lead |
| `…/UnaryArith.lean` | 112 | public unary rows (div/mod, constants, power, `clauseLit`, `litVal`) | B |
| `…/ColoringGraph.lean` | 668 | step 3: codes, `memS`/`goodS` specs, `k4`, `colorInst`, emitter, equivalences to the course vertex type | B |
| `…/ColoringParse.lean` | 720 | step 3: poly-time `memS`/`goodS` (finite-automaton host, boundary search), `polyTimeComputable_colorInst` | B |
| `…/ColoringWitness.lean` | 393 | step 4: `gadgetColor` (re-derived, disclosed), `properColoring_gadgetColor`, `colorWord` (poly-time) | C, lead |
| `…/Soundness.lean` | 258 | soundness transported from `SATtoColorReduction` along a homomorphism | lead |
| `…/Padding.lean` | 250 | isolated-vertex padding of graphs and colourings, string level and poly-time | C |
| `…/Hardness.lean` | 300 | assembly, `levinNPHard_L3COL`, the two corollaries | lead |
| `ZeroKnowledge/LevinHardness.lean` | 53 | facade with `## Contents` | lead |
| `ZeroKnowledge.lean` | +3 | one import and its `## Contents` entry | lead |

There are 14 paths and 4,000 new lines. Every file is under 1000 lines.

## Base, environment, pool

**Inputs.** All nine COMMON §1 SHA-256 values match, read at `54dcb3021a389831e7f94c3f82616cb7594fa574`.

**Preflight** (`evidence/logs/preflight.log`):
- `nproc` = 4.
- cgroup v1 with no limit, so the headroom is `MemAvailable` ≈ 15.6 GB (≥ 4 GiB).
- 21.4 GB free (≥ 12 GiB).
- elan with `v4.25.0` was installed after the preflight.

**Cache** (narrowed only; the store was empty before, `cache-store.log`):

| Roots | Downloaded | Decompressed |
|---|---|---|
| 78 | 2107 | 2107 |
| +7 | 3 | 905 |
| +294 (root build) | 1497 | 3596 |

- Zero-size oleans: 0.
- `PACKAGES CHECK: PASS` (before and after); `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean` are ABSENT.

**Pool.**
- Size 3 = min(4, MemAvailable/4 GB): a `flock` semaphore of 3 slots (`tools/lean_slot.sh`) shared by the lead and all sub-agents.
- Peak RSS: 2.94 GB (bootstrap), 4.66 GB (`Build/ZoneRebalance`, root build) (root build).
- `evidence/logs/pool.log`, `pool-slot-usage.log`.

**Olean trees.** One per agent (`ol-lead`, `ol-A/B/C`). Sub-agent trees were seeded from the lead tree only for byte-identical sources.

**Builds.** No `lake build`, no unfiltered cache get. Every module was compiled with `scripts/lean_check_tree.sh`.

**Bootstrap.** 289 modules in dependency order (`order-prefix2.txt`), 0 failures. The root build is C2 below.

## Who did what

**Lead:** the design; the shared rules (`evidence/subagents/SUBAGENT-RULES.md`); Relations, Bridge, Verifier, Gadget, Soundness and Hardness; the facades; all integration, commits, checks and delivery.

**A:** CircuitWitness. The lead re-pointed it to `Bridge.toCNF_eq` and wrapped two lines.

**B:** ColoringGraph, ColoringParse and UnaryArith.

**C:** ColoringWitness and Padding. The lead later replaced C's private unary copies by UnaryArith.

**Reports:** `evidence/subagents/<X>/`. A's report was recorded by the lead because A's harness refused the file write; B's two hand-backs are summarized there too.

## Target map

| Brief target | Declaration(s) |
|---|---|
| `levinNPHard_L3COL` | `TCSlib.Cryptography.levinNPHard_L3COL` (`Hardness.lean`) |
| `exists_levinReduction_L3COL` | not stated: through `Bridge.levinNPHard_iff` it is a restatement of the headline (brief: "keep only one") |
| `…_of_owp_unconditional` (×2) | `zk_proof_of_witnessRelation_of_owp_unconditional`, `zk_proof_of_mem_NP_of_owp_unconditional` |
| `certOf`, `decodeCert` | `certOf`, `certOf_eq`, `length_certOf`, `splitAtLastTrue_certOf`, `polyTimeComputable_certOf` (`decodeCert` would only wrap `Turing.splitAtLastTrue`, so it is not defined) |
| verifier language in `P` | `verTest`, `verTest_pairEncode`, `polyTimeComputable_verTest`, `verLang_mem_P` |
| `f₁`, poly-time, membership, witness | `tabInst`, `tabCkt`, `polyTimeComputable_tabInst`, `tabInst_eq`, `tabCkt_eval`, `exists_tabReduction` |
| `R_CKT`, `R_3SAT` | `Relations.lean` |
| `w₂` and its witness lemma | `wireValues`, `wireValues_getD`, `polyTimeComputable_wireValues`, `R_3SAT_wireValues` |
| `mem_SAT3_iff_exists_R_3SAT` | replaced by `exists_R_3SAT_iff` (Statement changes 1) |
| `Fin N` gadget graph | `gadgetGraph`, `gadgetAdj`, `gadgetEdge`, `gadgetN` (`Gadget.lean`), `gadgetSimpleGraph` |
| `f₃`, poly-time, membership | `colorInst`, `polyTimeComputable_colorInst`, `exists_R_3SAT_iff_padWord` |
| membership through `SATtoColorReduction` | `reductionGraphHom`, `isSatisfiable_of_colorable`, `exists_clauseSat_of_colorable` (`Soundness.lean`) |
| colouring `c_a`, `w₃` | `gadgetColor`, `properColoring_gadgetColor`, `colorWord`, `polyTimeComputable_colorWord` |
| padding and assembly | `padGraph`, `padColoring`, `padWord`, `padColWord` (+ `_encGraph`/`_encColoring`, poly-time), `R3COL_padWord`, `levinNPHard_L3COL` |

## Polynomials

`m`, `T` and `B` are explicit in shape. Their coefficients come from the decider constants of the given witness relation, so they are explicit only up to those constants, as in `dagCktSatLang_NPHard`.

**Certificate length:** `m(n) = q(n) + 1`. Here `q` is `WitnessRelation.bounded`'s polynomial.

**Tableau time:** `T(n) = verTime C c m n = C (2n + 3 + m(n))^c + 1`. Here `C (N + 1)^c` bounds the time of the verifier-test machine, and `2n + 2 + m(n) = |⟨x, u⟩|`.

**Vertex count before padding:**
- `N(s) = gadgetN |s| = 3 + 2|s| + 6 (2|s|)³` when `goodS s`, else `4` (`K₄`).
- Here `s = dagCktSatToSAT3 (f₁ x)`.

**Padded vertex count:**
- `B(n) = A (n + 1)^a + n + 1`, where `(A, a)` is `PolyTimeComputable.output_length_le` of `x ↦ colorInst (s x)`.
- So `A (n+1)^a ≥ N(s)² ≥ N(s)`.

**Length polynomial:**
- `p = B²`, so `|f x| = B(|x|)²` exactly for every `x` (`length_padWord`).
- `p(n) ≥ n + 1 > n`.

## Statement changes (old → new, reason)

1. **`mem_SAT3_iff_exists_R_3SAT` → `exists_R_3SAT_iff`.** The new form: for fan-in-two `C`, `(∃ a, R_3SAT (dagCktSatToSAT3 C.encode) a) ↔ ∃ x, C.eval x = true`. Reason: `Complexity.SAT3` has no reader. The composite chain never needs `SAT3`; it runs `x ∈ L ↔` tableau satisfiable `↔ ∃ a, R_3SAT … ↔ f x ∈ L3COL`.
2. **The verifier language does not test `|u| = m(|x|)`.** The circuit has exactly `m(|x|)` inputs.
3. **The hard-wired prefix is `⟨x, []⟩`, not `x`.** The verifier then reads the pair `⟨x, u⟩` (`BinArith.pairEncode_nil_append`) and needs no length-split search.
4. **Isomorphism → homomorphism.** The brief's "explicit isomorphism to `ReductionGraph`" becomes the homomorphism `reductionGraphHom : ReductionGraph (gadgetFormula K mem) →g gadgetSimpleGraph K mem`, along the explicit vertex equivalence `vertexEquiv K` (B). Soundness needs only this direction; completeness is the explicit colouring. The course theorem is still the only soundness proof.
5. **One gadget for every clause code.** The gadget graph has a gadget for every clause code `c < (2K)³`, exactly the vertex type `OutputVertex (Fin K)` of `ReductionGraph`, which has a gadget for every clause. It is not one gadget per de-duplicated clause of the formula, and `K = |s|`. Clauses are widened by repeating the last literal. A string failing the width test (an empty clause, a clause wider than 3, or malformed input) maps to `K₄`.
6. **`exists_levinReduction_L3COL` is not stated separately** (see the target map).
7. **`properColoring_padGraph` has no `n ≤ B` hypothesis.** It is not needed.

## Checks

**C1 Build** (`evidence/build/summary.txt`). All 14 modules at the head give rc 0, errors 0 (both forms), `sorry` warnings 0. Every source SHA-256 equals `git show HEAD:<path>`.

**C2 Downstream.** The only importer of the `ZeroKnowledge` facade is `TCSlib.lean`, so C2 is the root build: 1,458 modules, of which 1,170 were built at the head. **Root step incomplete (environment, not a finding):** 1,149 of 1,170 modules built with rc 0, among them every `LevinHardness` module, `Cryptography/ZeroKnowledge` and all of `Cryptography`. Three modules (`CommunicationComplexity/NewmanTheorem/{Newman, Entropy/Basic, FuncDisjointnessLowerBound/HardSample}`) fail with `unknown module prefix 'PFR'`: the PFR package is cloned at its manifest pin, but the narrowed Mathlib cache does not ship its oleans and building a package would need `lake build` (banned). Their 18 downstream modules, including the root `TCSlib`, were skipped (addendum item 8: no checks against missing prerequisites). None of the 20 non-root modules imports a changed file; the root `TCSlib` imports the changed facade and is the one downstream check left open (every module it imports from `Cryptography` was built); the last module checked and the tail are in `logs/rootbuild-tail.txt` (`evidence/logs/rootbuild/summary.tsv`, `rootbuild.log`).

**C3 Statements.**
- `decls2.py . <base> <14 files>`: 245 ADDED, 0 CHANGED, 0 REMOVED (`checks/c3-decls2.txt`).
- StmtDump probe (`probes/StmtAx.lean`): 245 public constants with full names and types (`axioms/stmtdump.txt`).

**C4 Admissions.**
- No `sorry`, `admit`, `native_decide`, `axiom`, `opaque` or `@[simp]` in the 14 files (`checks/c4-admissions.txt`).
- No base file is changed except the facade, so the base's `sorry` set is unchanged.

**C5 Axioms.** All 245 public constants use standard axioms only; non-standard: 0 (`axioms/stmtdump.txt`; checkpoint `axioms/cp1.log`).

**C6 Rule 10** (`evidence/seals/`).
- *Candidates.* Collected from the elaborated terms by the gate-04 collector (`candidates/`, 444 rows).
- *Strict seal.* Every candidate sealed `local irreducible`. All 11 non-bridge files **PASS** (`plain/results_plain.txt`).
- *Bridge.* Each of its 27 declarations is unsealed for exactly its own target, everything else sealed: **PASS** (`bridge/`, `unseal-bridge.json`).
- *Seal variants.* The gate tool's exact "seal B" and "coe" variants are not among my inputs. A strict whole-file seal of statements and bodies implies both weaker variants (coe leaves coercions unsealed; seal B covers statements only). Recorded as such.
- *Paired controls* on the 9 owners with definitions: the foreign `rfl` read passes unsealed and fails sealed exactly once (line 5), and the read through the published reader passes sealed (`controls/controls-summary.txt`).
- *Explicit-unfold scan.* 0 foreign unfolds outside the bridge's 7 disclosed `simp [EdgeRelation]` proofs. 3 hits are false positives (arguments or `show` terms), adjudicated in `unfold-scan.txt`.
- *Reader census.* `reader-census.tsv`. MISSING readers are exactly the bridge set (Scope requests).

**C7 Frozen files.**
- `ZeroKnowledge.lean`: 3 allowed insertions, 0 other differences, **PASS**.
- The one-character control gives exactly one difference, FAIL.
- `git diff --stat <base>` lists only the 14 paths (`checks/c7-frozen.txt`).

**C8 Lint.**
- `style_lint.py` on the 14 files: 0 findings.
- `campaign_style_lint.py TCSlib/Cryptography --check8b`: base 92 FAIL / 103 WARN over 531 files (equals the maintainer's), head 92 FAIL / 103 WARN over 544 files. The FAIL and WARN line sets are identical (`checks/c8-*`).

**C9 Sizes.** Every file is under 1000 lines, with maximum width ≤ 100 (`checks/c9-sizes.txt`).

**C10 Clashes.**
- 0 full-name clashes against TCSlib/ and audits/ at REC, IO `5ed465f6…`, #377 `7563734a…` and S2-A `c119a3c4…`.
- Two shared short names: `decode_eq` (LWE, Lossy) and `padGraph` (`Randomized.padGraph`). They live in different namespaces, and no downstream module opens `LevinHardness`, so no resolution changes (`checks/c10-clashes.txt`).

**C11 Reuse and overlap.** See the section below and `checks/c11-searches.txt`.

**C12 Probes** (`probes/ProbeH12.lean`, kernel `decide`, evidence only). For `K = 1` (53 vertices):
- the satisfying assignment gives a proper colouring;
- the falsifying assignment does not;
- `{x₀, ¬x₀}` is not coloured by `x₀ = true`;
- padding to `B = 60` gives exactly 3600 bits.

**C13 Reproduction.** `git am` of `patches/` at the base with `COMMITS.tsv`'s committer data reproduces every hash, and `src/` equals the head byte for byte (`logs/c13-replay.txt`).

**H12-P1/P2 (string level).** Not executable:
- `tabInst` uses a decider machine chosen by `Classical.choice` (and `tabEmit` is `noncomputable`), so no `#eval`.
- Even for `|x| ≤ 2` the tableau circuit has thousands of gates, the Tseitin string has `|s| ≫ 10³` bits and `gadgetN |s| ≥ 48|s|³`, beyond any kernel `decide`.

Instead:
- the length law `|f x| = B(|x|)²` is the proved field `length_eq` for **every** `x`;
- witness correctness is the proved field `witness`;
- C12 checks the graph stages on concrete instances.

**H12-P3.** `#print axioms` gives the standard axioms only for `levinNPHard_L3COL` and both corollaries (`axioms/stmtdump.txt`).

## Overlap and reuse

**Searches.** `checks/c11-searches.txt` lists the `git grep` commands at the base and their hit counts:
- `levinNPHard`, an all-wire evaluator, `wireValues` and the `toCNF`/`widthAtMost`/`levinNPHard` readers: 0 hits.
- `withOutput`/`retarget`: prose only.
- `padGraph`: only the unrelated `Randomized.padGraph`.

**Disclosed overlaps (the brief's three):**
- **(a)** `Verifier.lean` re-instantiates the core of `dagCktSatLang_NPHard` (`CircuitSatNPHard.lean:93-127`).
- **(b)** `ColoringWitness.lean` re-derives `sat3Coloring`/`clauseGadgetColor` (`ThreeSATToColoring.lean:163-193`, Q-H12-3 A).
- **(c)** `R_3SAT` states the private `satAssignment` convention (`ClassNP/SAT.lean`).

**Further near-relatives (disclosed; none is a restatement of a public lemma):**
- *Bridge readers.* `Bridge.lean`'s 27 readers state reader content of frozen definitions (user ruling).
- *Private SAT.lean copies.* `polyTimeComputable_foldl_accept` (ColoringParse, public, generic finite-automaton acceptance) relates to the private `satSyntax_poly` (`ClassNP/SAT.lean:306`). `var_lt_length_of_mem_decode` relates to the private `sat_literal_lt_numVars` (`SAT.lean:820`) + `numVars_decode_le`.
- *Private CNF copies.* `le_foldr_max_zero` (private glue, ColoringParse) is a copy of the private `le_foldr_max_of_mem` (`Formulas/CNF.lean:112`). `serializeClause_append_inj` relates to the private `parseClause_serializeClause` (`CNFEncoding.lean`).
- *Circuit encoding.* `parts_of_encode_eq` (private glue, CircuitWitness) is the parts form of `DAGCircuit.eq_of_encode_eq` (`Uniform.lean:198`); it is needed for out-of-range outputs.
- *Graph-level relatives.* `threeColorable_gadgetGraph_iff` relates to `threeColorable_ofSimpleGraph_iff` (`ThreeColoring/Language.lean:116`), restated because `Graph.ofSimpleGraph` has no reader. `padColWord` equals `EncodingMachines.padTo (2B)` when `|w| ≤ 2B` (named in its docstring).
- *Unary rows.* `UnaryArith.lean` rows relate to the `sorry`ed `FormulaKit/Emit.lean:216-271` rows (not built, not used).
- *Tabulation.* The tabulation pattern specializes `EncodingMachines.polyTimeComputable_of_getD`.

**Must-reuse items, with where used:**
- `LevinReduction` (Hardness).
- `WitnessRelation` (Verifier).
- `zk_proof_of_witnessRelation_of_owp`, `zk_proof_of_mem_NP_of_owp` (corollaries).
- `polyTimeComputable_tabEmit`, `tabEmit_eq`, `polyTimeComputable_tabInput`, `cfgTab_eval`, `cfgTab_isFaninTwo`, `decide_emits_eq_of_computesInTime` (Verifier).
- `dagCktSatToSAT3`, `polyTimeComputable_dagCktSatToSAT3`, `TQBFHard.dagCktSatToSAT3_encode`, `eval_tseitinGates_values`, `toCNF_widthAtMost` (CircuitWitness, Hardness).
- `CVALPrefix`'s verdict machine for the wire values (A).
- `SATtoColorReduction` (Soundness).
- `encGraph_mem_L3COL_iff`, `R3COL_iff`, `encGraph_getD_nat`, `getD_encColoring*`.
- `CNF.decode_serialize`, `parse_repr`, `syntaxOK_spec`, `numVars_decode_le`.
- `ComposeMachines.polyTimeComputable_flatMap_range` (tabulation host), `BinArith` rows, `polyTimeComputable_transduce`, `EncodingMachines` unary rows, `PolyHierarchy.splitAtLastTrue_marker`, `FinTM.computesFunInTime_stripLast`/`_pairValid`.

**Not used:** `LevinReduction.trans`; the assembly builds the composite maps directly with exact padding.

**Private cross-file copies:** none. The unary helpers live once, publicly, in `UnaryArith.lean`.

## Scope requests (readers to add to frozen files; then delete `Bridge.lean` and re-point one-for-one)

| Proposed reader | Owner file |
|---|---|
| `toCNF_eq : C.toCNF = [(C.output, true)] :: tseitinGates n C.gates := rfl` | `Complexity/CircuitComplexity/DAGCircuitSat.lean` |
| `widthAtMost_iff`, `numVars_eq` | `Complexity/Formulas/CNF.lean` |
| `serializeLit_eq`, `serializeClause_eq`, `serialize_eq`, `decode_eq`, `fallback_eq`, `syntaxStep_eq`, `syntaxOK_eq` | `Complexity/Formulas/CNFEncoding.lean` |
| `satisfiesLiteral_pos/neg`, `satisfiesClause_eq`, `satisfiesSat3_eq`, `isSatisfiable_iff`, `is3Colorable_iff`, `reductionGraph_adj`, nine `edgeRelation_*` case readers | `Complexity/NPReductions/ThreeSATToColoring.lean` (course material) |
| `levinNPHard_iff` | `Cryptography/ZeroKnowledge/NP.lean` (J6) |

**Also missing, routed around (no bridge):**
- `Complexity.SAT3` (`mem_SAT3_iff`), `DAGCircuit.Satisfiable` (`satisfiable_iff`), `CktSatReduction.descTail`, `Graph.ofSimpleGraph` (`ofSimpleGraph_apply`).
- A public `PolyTimeComputable` row for `descTail`.

## Attribution

Only in-repo anchors from the brief are cited:
- [AB09] Def 6.9, Lemmas 6.10/6.11 p. 111, Remark 6.7, §2.3, §2.3.1;
- [PS10] §4.7, Theorem 124.1 step 2, Definition 191.11;
- the CS 294-268 course material as `ThreeSATToColoring.lean` cites it.

No quotation, page or number was invented. Garey–Johnson and Stockmeyer are not cited (Q-H12-2: not ingested). Glue declarations say "Glue".

## Questions for Seyoon

- **EF-H12-W1.** Accept `Bridge.lean` as a recorded Rule-10 exception until the owner PRs add the listed readers? **(A, recommended)** Yes; the scope requests are filed above. (B) Hold landing until the owner readers land, then re-point.
- **EF-H12-W2.** The sorried `polyTimeComputable_unary_*` rows in `FormulaKit/Emit.lean:216-271` (not used here). **(A, recommended)** Queue them for their owner (they duplicate the proved `EncodingMachines`/`UnaryArith` rows). (B) Leave them.
- **EF-H12-W3.** Promote the generic `polyTimeComputable_foldl_accept` (finite-automaton acceptance) to the host registry? **(A, recommended)** Yes, as a registered host row (it instantiates `polyTimeComputable_transduce`). (B) Keep it local.

## Evidence manifest

`evidence/SHA256SUMS` lists every evidence file:
- `build/`: C1.
- `logs/`: preflight, cache, packages, bootstrap, root build, pool, C13.
- `axioms/`, `seals/`, `checks/`, `probes/`.
- `subagents/`, `tools/`: the scripts used, including `lean_slot.sh`, `pool.py`, `payload.sh`, `c7_frozen.py` and the gate-04 seal tools as run.

The top-level `SHA256SUMS` covers the whole payload.
