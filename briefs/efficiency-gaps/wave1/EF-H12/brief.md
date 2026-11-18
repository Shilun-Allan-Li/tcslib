# EF-H12 · `LevinNPHard L3COL R3COL`: the string-level Levin reduction to 3-colouring

**Unit** `ef-h12-levin-3col` · **Route** Claude fill (lead, up to 3 sub-agents on disjoint files) ·
**Base** REC `cf6a2266e9556ca8ad61e56f7232266ccc6d4e62` · **Size** 2,000–3,800 new Lean lines (±40%) ·
**Rulings** Q8 ("Prove it now"), Q11 A (file-disjoint from Stage 2), rule 15. **Arora–Barak and course
material is read-only**: every `TCSlib/Complexity/**` file is imported, never edited.

Read `../COMMON.md` first; it is part of this brief.

## Scope

`LevinNPHard L3COL R3COL` (`ZeroKnowledge/NP.lean:654`) is the one hypothesis left on ZK for NP (audit R18,
class MH): "every language with a witness relation Levin-reduces to `(3COL, R_3COL)`", where a
`LevinReduction` (`NP.lean:134`) has a polynomial-time instance map `f`, a polynomial-time witness map `w`
on `⟨x, y⟩`, `x ∈ L ↔ f x ∈ L'`, `R x y → R' (f x) (w x y)`, and exact length regularity
`|f x| = p(|x|)` with `p ≥ id`. This job **proves it**, in new crypto-side files, and adds unconditional
one-line corollaries of the ZK-for-NP theorems. `NP.lean` (J6) is not edited.

## What TCSlib already has (maintainer, static, read-only reuse)

- **Cook–Levin, direct route** (`Complexity/CookLevin/Hardness.lean`, 8,783 lines; [AB09, Theorem 2.10,
  Lemmas 2.11, 2.14]): the public API is `NPHard.polyTimeReducible`, `SAT_NPHard`, `SAT_NPComplete`,
  `SAT3_NPHard`, `SAT3_NPComplete` — Karp reductions only, **no witness map**; the tableau, its emitter and
  the completeness assignment are among its **540 `private` declarations**. Not reusable for witnesses
  without an Arora–Barak-side change.
- **Cook–Levin through circuits** ([AB09, Lemma 6.10, Lemma 6.11, p. 111: "The Cook–Levin Theorem follows
  immediately from the next two lemmas"]), public and polynomial-time at the string level:
  - `BoolCircuit.dagCktSatLang_NPHard` (`CircuitComplexity/CircuitSatNPHard.lean:93`): `x ↦
    UTab.tabEmit M (1^{m(x)} 0 1^{T(x)} 0 x)` (`UniformTableauEmitterMain.lean:420`,
    `polyTimeComputable_tabEmit` `:435`, `tabEmit_eq` `:443`; `polyTimeComputable_tabInput`
    `UniformTableau.lean:74`), the description of `cfgTab M m x T` (`UniformTableauSpec.lean:88`) with
    `cfgTab_eval` (`:99`) and `cfgTab_isFaninTwo` (`:117`). **Its certificate is the circuit's input**, so
    the witness map of this step is the certificate itself.
  - `BoolCircuit.dagCktSatToSAT3` (`DAGCircuitSatLang.lean:219`), `polyTimeComputable_dagCktSatToSAT3`
    (`CircuitSatReduction.lean:133`), `mem_dagCktSatLang_iff_mem_SAT3` (`DAGCircuitSatLang.lean:241`): the
    Tseitin map, whose satisfying assignment is the circuit's wire values (`DAGCircuit.values`
    `DAGCircuit.lean:480`, `eval_tseitinGates_values` `DAGCircuitSat.lean:312`,
    `values_getD_eq_of_eval_tseitinGates` `:322`, `toCNF` `:267`, `toCNF_widthAtMost` `:272`).
- **3SAT → 3COL, graph level** (`Complexity/NPReductions/ThreeSATToColoring.lean`, CS 294 course material):
  `SATtoColor.SATtoColorReduction (f : Sat3 V) : IsSatisfiable f ↔ Is3Colorable (ReductionGraph f)`
  (`:401`), over `SimpleGraph (OutputVertex V)` with clause gadgets indexed by `Clause V` (duplicate clauses
  share a gadget) and exactly three literals per clause. The explicit colouring `sat3Coloring` (`:175`) and
  `clauseGadgetColor` (`:163`) are **private**; the completeness lemma gives only `Nonempty (G.Coloring (Fin 3))`.
- **No SAT → 3SAT witness map is needed** on the circuit route (`dagCktSatToSAT3` emits a 3-CNF directly).
  `NPReductions/SATTo3SAT.lean` exists (course material) and is not used.
- **The 3COL side** (`ZeroKnowledge/ThreeColoring/Language.lean`, J6, read-only): `L3COL` (`:126`),
  `R3COL` (`:130`), `mem_L3COL_iff`, `encGraph_mem_L3COL_iff` (`:150`), `Graph.ofSimpleGraph` (`:111`),
  `threeColorable_ofSimpleGraph_iff` (`:116`), `ProperColoring`; `encGraph` (adjacency matrix, `n²` bits) and
  `encColoring` (`ZeroKnowledge/Encoding.lean:126`, `:258`).

## Route (Q-H12-1 A)

`(L, R)` → `(CKT-SAT, R_CKT)` → `(3SAT, R_3SAT)` → `(3COL, R_3COL)`, then pad:
1. **Verifier** (file `Verifier.lean`): from `WitnessRelation L R` (bound `q`, decider `T`), a fixed-length,
   self-delimiting certificate `certOf x y` of length `m(|x|)` and the verifier language
   `{⟨x, u⟩ | |u| = m(|x|) ∧ R x (decodeCert u)} ∈ P`; the instance map
   `f₁ x := UTab.tabEmit M (front-end x)` for its decider `M`, as in `dagCktSatLang_NPHard`'s proof (a
   specialization: disclose), with `x ∈ L ↔ f₁ x ∈ dagCktSatLang` and the witness map `w₁ x y := certOf x y`.
2. **Circuit witness** (`CircuitWitness.lean`): `f₂ := dagCktSatToSAT3`; `w₂ ⟨desc, u⟩ :=` the encoded wire
   values `C.values u` (an assignment word read with `getD`), polynomial-time from the description and the
   input (a new evaluator on the registered loops, or the `CircuitEval` machinery if a public all-wire
   output exists — check `CircuitEval*.lean` first), and the witness lemma from `eval_tseitinGates_values`
   and the output clause of `toCNF`. `R_3SAT φ a :≡ (CNF.decode φ).WidthAtMost 3 ∧ (CNF.decode φ).eval
   (fun v => a.getD v false)` (define it publicly here; `SAT.lean`'s `satAssignment` is private), with
   `mem_SAT3_iff_exists_R_3SAT`.
3. **Colouring graph** (`ColoringGraph.lean`): `f₃ φ := encGraph (Graph.ofSimpleGraph G_φ)` for an explicit
   `Fin N`-indexed gadget graph `G_φ` of `CNF.decode φ` (clauses widened to three literals by repetition; an
   empty clause sent to a fixed non-3-colourable gadget, e.g. `K₄`), polynomial-time as a string map;
   `mem_iff` **through `SATtoColorReduction`** along an explicit graph isomorphism between `G_φ` and
   `ReductionGraph` of the widened, de-duplicated clause list (`SimpleGraph.Iso` and colouring transport),
   not by a second soundness proof.
4. **Colouring witness** (`ColoringWitness.lean`): `w₃ ⟨φ, a⟩ := encColoring c_a` for an explicit colouring
   `c_a` of `G_φ` from the assignment, polynomial-time, and `ProperColoring` of it when `a` satisfies `φ`.
   Because `sat3Coloring` is private and the file is read-only, this re-derives the completeness colouring:
   **a disclosed duplication** (Q-H12-3 A).
5. **Assembly and padding** (`Hardness.lean`): the composite instance map padded with isolated vertices to
   exactly `B(|x|)` vertices for a polynomial `B` bounding every stage's size (so `|f x| = B(|x|)²` for
   **every** `x`, and `B(n)² ≥ n`), the composite witness map, and the `LevinReduction`.

## Targets (proposed; the worker may refine with disclosure)

Namespace `TCSlib.Cryptography` (sub-namespace `LevinHardness` for helpers), in
`ZeroKnowledge/LevinHardness/*.lean`:
- `theorem levinNPHard_L3COL : LevinNPHard L3COL R3COL` — the headline.
- `theorem exists_levinReduction_L3COL {L : Language Bool} {R} (hR : WitnessRelation L R) :
    ∃ f w p, LevinReduction L L3COL R R3COL f w p` (the same, unfolded; keep only one of the two if the
  other is a restatement — `levinNPHard_L3COL` is the one consumers need).
- One-line unconditional corollaries (new names; the `NP.lean` originals stay):
  `zk_proof_of_witnessRelation_of_owp_unconditional`, `zk_proof_of_mem_NP_of_owp_unconditional`, each
  `… levinNPHard_L3COL …`, with the conclusions of `zk_proof_of_witnessRelation_of_owp` (`NP.lean`) and
  `zk_proof_of_mem_NP_of_owp` (`:742`) without the `LevinNPHard` hypothesis.
- Intermediate steps as public lemmas with readers: `certOf`, `decodeCert`, `R_CKT`, `R_3SAT`, the
  `Fin N` gadget graph and the colouring `c_a`, each instance and witness map with its
  `polyTimeComputable_*`, its membership lemma and its witness lemma. Intermediate steps need not be
  `LevinReduction`s (length regularity is only imposed on the composite).

## Sources

Not ingested: AB09 chapters 2 and 6 (only chapters 7 and 13 are under `blueprint/src/references/`), and no
3-colouring source. Until Q-H12-2 is answered, cite only anchors **established in audited TCSlib files**:
- [AB09] Arora, Barak, *Computational Complexity: A Modern Approach*, CUP 2009: **Definition 2.7** (Karp
  reductions; `NP.lean`), **Theorem 2.10** p. 45 (Cook–Levin), Lemma 2.11 pp. 45–49, Lemma 2.14 p. 49
  (`CookLevin/Hardness.lean`); **§6.1.2, Lemma 6.10 and Lemma 6.11, p. 111**, Remark 6.7, Definition 6.9
  (`CircuitComplexity/{CircuitSatNPHard,DAGCircuitSatLang}.lean`). The Levin-reduction remark is cited in
  `NP.lean` as "[AB09, §2.3]"; gate 03e (finding 6) suggested §2.3.6 ("More thoughts on the Cook–Levin
  theorem") **unverified**: keep "[AB09, §2.3]" until verified, and never quote it.
- [PS10] §4.7, Theorem 124.1, step 2 ("Cook's reduction can be applied to the witness"), Claim-124.b/c,
  Definition 191.11 — as `NP.lean` cites them (`pass-shelat-2010-ch4`, appendix ingested).
- 3SAT → 3COL: the course material as `ThreeSATToColoring.lean` cites it; candidate published sources for
  the maintainer to pin at ingestion (Q-H12-2): Garey–Johnson, *Computers and Intractability*, 1979,
  Appendix A1.1, problem [GT4] (graph `K`-colourability, NP-complete for `K = 3`); Stockmeyer, *Planar
  3-colorability is NP-complete*, SIGACT News 5(3), 1973. Do not cite either until ingested.

## Must reuse

Everything named under *What TCSlib already has*, plus: `LevinReduction`, `LevinReduction.trans`,
`.polyTimeReducible`, `.refl`; `WitnessRelation`, `exists_witnessRelation_of_mem_NP`
(`InteractiveProofs.lean:318`); `zk_proof_of_witnessRelation_of_owp`, `zk_proof_of_mem_NP_of_owp`;
`Complexity.mem_P_iff`, `mem_P_of_test`, `test_of_mem_P`, `polyTimeComputable_polyUnary`,
`decide_emits_eq_of_computesInTime` (`CircuitComplexity/PSubsetPPolyTableauCorrect.lean:375`),
`encode_mem_dagCktSatLang_iff` (`DAGCircuitSatLang.lean:199`), `mem_dagCktSat_iff`; `Complexity.SAT3`,
`CNF.decode`, `CNF.serialize`, `decode_serialize` (`Complexity/Formulas/CNFEncoding.lean:287`);
`BinArith` loops (`forLoop`, `getW`, `eqW`, `chunkW`), `polyTimeComputable_iterate`.

## Duplication sweep (maintainer, static)

- `LevinNPHard L3COL R3COL` is proved nowhere and no Levin reduction other than `LevinReduction.refl`/`trans`
  exists (grep `LevinReduction` over `TCSlib/`: `NP.lean`, `NPLemmas.lean` and its consumers only); no
  `levinNPHard`/`LevinHardness` name exists on any of the 280 remote heads.
- **Known, accepted overlap** (disclose each in § *Overlap and reuse*): (a) step 1 re-instantiates the
  core of `dagCktSatLang_NPHard`'s proof (`CircuitSatNPHard.lean:93–127`, about 30 lines) for a specific verifier (a specialization, since that
  theorem is existential); (b) step 4 re-derives the completeness colouring of `SATtoColorCompleteness`
  because `sat3Coloring` is private (Q-H12-3); (c) the witness relation `R_3SAT` duplicates the private
  `satAssignment` convention of `ClassNP/SAT.lean` (`u.getD v false`), stated publicly. Nothing else of
  `CookLevin/Hardness.lean`, `CircuitComplexity/*` or `NPReductions/*` may be re-proved.
- No string-level 3COL graph emitter exists (`encGraph` is a function of a typed `Graph n`); no all-wire
  circuit evaluator with a `PolyTimeComputable` theorem was found (`CVAL`, `CVALPrefix` are output
  decisions): check `CircuitEvalRun.lean`/`CircuitEvalSpec.lean` before writing one.

## Files (create or change only these)

| File | Kind |
|---|---|
| `TCSlib/Cryptography/ZeroKnowledge/LevinHardness/Verifier.lean` | new |
| `TCSlib/Cryptography/ZeroKnowledge/LevinHardness/CircuitWitness.lean` | new |
| `TCSlib/Cryptography/ZeroKnowledge/LevinHardness/ColoringGraph.lean` | new |
| `TCSlib/Cryptography/ZeroKnowledge/LevinHardness/ColoringWitness.lean` | new |
| `TCSlib/Cryptography/ZeroKnowledge/LevinHardness/Hardness.lean` | new |
| `TCSlib/Cryptography/ZeroKnowledge/LevinHardness.lean` | new facade |
| `TCSlib/Cryptography/ZeroKnowledge.lean` | facade: one import and its `## Contents` entry |

(Split or merge the five files as the work requires, each under 1,000 lines, inside
`ZeroKnowledge/LevinHardness/`; report the final list.)

**Disjointness check (maintainer, mechanical).**
- **Stage 2**: no path is an owner file of `scope.tsv`/`s2a-items.tsv`; J6 owns `ZeroKnowledge/NP.lean`,
  `NPLemmas.lean`, `Encoding.lean`, `ThreeColoring/*` and others, all **imported read-only** here; J6's rows on
  the declarations used are proof-level or reader additions (`S2-SL-481..502`, `S2-BO-190..193`,
  `S2-RD-53`, `S2-RP-053`), and the one statement-level row, `S2-BO-191` (`outV_pullback_cheat`,
  meaning-preserving), is not used. Not changed on `cleanup/stage2-s2a`.
- **#376/#377**: no overlap.
- **Arora–Barak and Ladner**: every new path is under `TCSlib/Cryptography/`, which no
  `complexity/arora-barak-ch3-4` or `codex/ab34-*` diff touches (their 252 paths are under
  `TCSlib/Complexity/`, `TCSlib/BooleanAnalysis/` and `TCSlib.lean`). Those branches **do** change files this
  job imports (`CircuitComplexity/{CircuitEvalMachine,CircuitEvalRun,CircuitSatReductionMachine,
  CircuitSatReductionMachineTapes}.lean`, `ClassNP/SAT.lean`, `CookLevin/Hardness.lean`): replay risk at
  landing only; import, never edit.

## Checks and evidence (in addition to COMMON C1–C13)

- **H12-P1**: for a toy witness relation (e.g. `R x y :≡ y = x`), `#eval` the composite instance and witness
  maps on `|x| ≤ 2` and check `R3COL (f x) (w x y)` by kernel `decide` on the decoded graph and colouring
  where it reduces (otherwise `#eval` evidence).
- **H12-P2**: `|f x| = B(|x|)²` on every `x` of length ≤ 3, including `x ∉ L`.
- **H12-P3**: `#print axioms levinNPHard_L3COL` and of both unconditional corollaries: standard only (R18
  becomes class **M**).
- `REPORT.md` gives the polynomials `m`, `T`, `B`, and `p = B²` explicitly, and the three overlap
  disclosures (a)–(c).

## Size

Verifier and step 1 300–500; circuit witness (evaluator, `R_3SAT`) 400–900; colouring graph (gadgets,
emitter, isomorphism to `ReductionGraph`) 700–1,300; colouring witness 350–650; assembly and padding
250–450.

## Questions for Seyoon

**Q-H12-1. Route.**
- **A (recommended).** Through circuits: [AB09, Lemmas 6.10, 6.11] (public string-level maps), then
  3SAT → 3COL. Cook–Levin is still [AB09, Theorem 2.10] (p. 111 derives it from the two lemmas).
- **B.** The direct §2.3 tableau: needs the Arora–Barak owner to publish the witness side of
  `CookLevin/Hardness.lean` (now private), an Arora–Barak-side change outside this job.

**Q-H12-2. Sources for AB09 ch. 2/6 and 3-colouring.**
- **A (recommended).** The maintainer ingests AB09 §2.2–§2.3 (Definition 2.7, Theorem 2.10 and the
  Levin-reduction remark), §6.1.2 (Lemmas 6.10–6.11, Remark 6.7) and one published 3-colouring source
  ([GJ79, App. A1.1, GT4] or [Sto73]) before the delivery review; the worker uses the in-repo anchors
  meanwhile and the gate checks the final citations.
- **B.** No ingestion: in-repo anchors and the course material only, disclosed.

**Q-H12-3. The explicit 3-colouring (witness map).**
- **A (recommended).** Re-derive it in the new files, disclosed (the course file stays read-only, as ruled
  in Q8).
- **B.** Lift read-only for `NPReductions/ThreeSATToColoring.lean` only: a two-declaration owner PR that
  makes `sat3Coloring` public and adds its properness lemma, which this job then cites (no duplication).
