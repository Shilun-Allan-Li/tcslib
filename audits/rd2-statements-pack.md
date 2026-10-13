# External audit pack — RD-2: B4a restated over the H6 kit (statement gate)

Campaign: Arora–Barak chapters 3–4 (`AroraBarakChapters3-4Plan.md`, cluster B4, plan row at
`:843`), under the host rule of design `machine-library-design.md` §14. **RD-2** (backlog
`backlog.md:698–707`; design §16b item 2, `machine-library-design.md:3786–3823`) restates
Claim 4.4(2) of [AB09] in place: the proved existential `Complexity.exists_adjacency_codec_cnf`
(`TCSlib/Complexity/ClassPSPACE/TQBF.lean:1744–1811`) becomes public definitions of the
configuration codec and its three CNFs, with closed-form variable indexing built on a new
machine-to-formula kit (registry row H6, `machine-library-design.md:3065`), and theorems in
place of its `∀ n s, ∃ …`. It changes an audited public statement, so it takes a full
statement gate before the re-fill (RD-2a, semantic) and the uniformity fill (RD-2b).

**This gate audits proposed files that are not landed.** Theorems are sorried, except the
statement-phase proofs listed in brief item 9; definitions have real bodies. Every file
elaborates read-only against the campaign tip with 0 errors (attestation 1). If the gate
closes, the files land by a PR the user merges, unchanged except for the corrections the
findings require.

All `file:line` references are to the campaign tip unless they name a proposed file, which is
cited by its bundle path below. **Provenance (maintainer):** a maintainer sub-agent drafted the
files against the read-only checkout `wt-g3` of campaign commit
`d63c7159c30b87c8e77b7aa5a9ca6adfc942f21d`, with the olean snapshot `oleans-f7`. The bundle is
built at a later campaign commit. Its only Lean changes are `SpaceComplexity/Hierarchy.lean`
(PR #82) and the new `Build/Contract.lean` with its facade import (PR #83), none of them cited
here, so the Lean references hold. The maintainer re-pointed the references into the design
document, the backlog and the plan, which changed in between, to the bundle's commit.

## The audit object

| Bundle path | Lands as | Content |
|---|---|---|
| `audits/evidence/rd2-gate/FormulaKitGate.lean.txt` (232 lines) | new `TCSlib/Complexity/FormulaKit/Gate.lean` | H6 kit I: block variables, truth-table templates and gates, exactly-one, cost and serialization ledgers |
| `audits/evidence/rd2-gate/FormulaKitEmit.lean.txt` (293 lines) | new `TCSlib/Complexity/FormulaKit/Emit.lean` | H6 kit II: fragments, ordered uniform emission, fixed templates with polynomial-time wires, unary index arithmetic, offsets |
| `audits/evidence/rd2-gate/FormulaKit.lean.txt` (37 lines) | new facade `TCSlib/Complexity/FormulaKit.lean` | `## Contents` |
| `audits/evidence/rd2-gate/QBF.lean.txt` (296 lines) and `QBF.patch` | `TCSlib/Complexity/Formulas/QBF.lean` (existing, 176 lines) | **additions to an existing file**: prefix truth over any leaf and auxiliary variables after the prefix (all proved); module docstring |
| `audits/evidence/rd2-gate/TQBF.lean.txt` (3305 lines) and `TQBF.patch` | `TCSlib/Complexity/ClassPSPACE/TQBF.lean` (existing, 2639 lines) | the new public `Complexity.ConfigCodec` surface, inserted in two blocks; docstring rewrites; nothing else changed |
| `audits/evidence/rd2-gate/ClassPSPACE.lean.txt` and `ClassPSPACE.patch` | `TCSlib/Complexity/ClassPSPACE.lean` | facade docstring |

Also proposed, outside these files: `import TCSlib.Complexity.FormulaKit` in `TCSlib.lean`
(export of the new topic, `policy.md` §1). The patches are `diff -u` against the tip. The
`TQBF.lean` patch is the readable form of the restatement: its removed lines are all
docstring text (attestation 3).

**Placement of the restated surface.** The user decided that B4a is restated **in place**
(§16b item 2), so the codec stays in `TQBF.lean`, in two blocks:
- **the definitions** (`TQBF.lean.txt:133–439`, namespace `Complexity.ConfigCodec`) go
  *before* the B4a fill appendix, so that at RD-2a the surviving private lemmas can refer to
  the public definitions that replace their private twins (the merge rows of the migration
  list);
- **the theorems** (`TQBF.lean.txt:2142–2459`) go after the old statement, which stays,
  proved, until RD-2a deletes it with its retired privates. No proved statement regresses to
  `sorry` during the window (design note §6.2 step 1).

A separate module `ClassPSPACE/ConfigCodec.lean` would layer better (`policy.md` §1,
*Layering*: a consumer of the codec would not import B4 membership's private block,
`TQBF.lean:1820–2532`). It was not taken because the decision is "in place". Brief item 8
asks for a ruling.

## What the gate covers and why (Finding A)

**Finding A** (design §16b item 2, `machine-library-design.md:3788–3792`; the docstring of
`TQBF_PSPACEHard`, `TQBF.lean:2613–2614`, "The packaged existential supplies no algorithm"):
B4a's formulas number their variables and order their clauses through choices over index
types that depend on `n` and `s`. No machine or program can be proved to emit a formula whose
literal indices are values of such a choice. The `TQBF` hardness reduction must emit `ψ`, so
it cannot be built over B4a as stated. In the tip:

| # | Where | What | The choice |
|---|---|---|---|
| A1 | `codecWord`, `TQBF.lean:302–307` | bit `i` of the padded code is `a ((Fintype.equivFin α).symm ⟨i, _⟩)`, `α = CodecBit M n s` | `Fintype.equivFin α := (truncEquivFin α).out` (Mathlib `Data/Fintype/EquivFin.lean:76–78`) |
| A2 | `configurationCodec`, `:332–337` | the code is `codecWord (C*(s+n+1)) …` | inherits A1 |
| A3 | `configurationValidity` `:586–589`, `configurationAcceptance` `:628–630`, `codecPairWire` `:976–979` | variables numbered `(Fintype.equivFin (CodecBit M n s) b).val` | inherits A1 |
| A4 | `codecOneHot`, `:376–381`, used by `codecValidity` `:480–488` over `Fin (n + 2)`, `Option M.State`, `Fin (2s + 1)` | clause order `Finset.univ.toList` | `Finset.toList` is `Multiset.toList = s.out` (Mathlib `Data/Finset/Dedup.lean:158–160`, `Data/Multiset/Basic.lean:29–30`) |
| A5 | `CodecGateIndex` `:1527–1529`, `codecTransitionCNF` `:1531–1535` | gate order `Finset.univ.toList` over positions × cases × coordinates | as A4, over a type depending on `n, s` |
| A6 | `codecLocalCheck` `:932–951`, `codecGate_cnf`/`codecGateCNF` `:1498–1517` | each gate is a `Classical.choose` of `exists_cnf_boolFun`, taken **after** wiring | the chosen clause list depends on the position and the coordinate, not only on a finite kind |
| A7 | the statement, `:1744–1747` | `∃ C, 0 < C ∧ ∀ n s, ∃ code φv φa φacc, …` | nothing to unfold; the module docstring says so (`:52–55`, "The package is existence, not an algorithm") |

Choices over types fixed by the machine are harmless and stay: an emitter for the fixed machine
stores them as a finite table, as Cook–Levin's field code does (`CookLevin/Hardness.lean:270`,
`clFieldCode`; `:241–243`, `clTemplate`). The landing form keeps two, both documented:
`ConfigCodec.stateIndex` (through `Fintype.equivFin M.State`) and `ConfigCodec.caseList`
(through `Finset.univ.toList` over `Case M`).

**Consumers of the old statement** (grep of the tip, `.lake` excluded): **no Lean proof**.
The open `TQBF_PSPACEHard` names it in its docstring (`TQBF.lean:2586`); the module
docstring (`:71`) and `Build/CfgRecord.lean:95` (the `Cfg.InWindow` docstring) mention it;
the blueprint, `docs/`, `dataset/`, `scripts/` and `tests/` do not. The live records that name
it are the plan (`:712`, `:843`), the design document and the backlog; audit records are
historical.

**In scope:** the statements, definitions and sketches of the five proposed Lean files and
the facade docstring; the migration list for RD-2a; the restated sketch of
`TQBF_PSPACEHard`. **Out of scope:** tactic proofs (kernel-checked); the RD-2a/RD-2b fills
themselves; B4 hardness's guarded matrix and its pointwise lemma, which are its own design
(brief item 4).

## The user's decisions (2026-10-12, binding; design §16b item 2, `:3811–3817`)

1. B4a is **restated in place** over closed-form indexing designed with the H6 kit.
2. `exists_adjacency_codec_cnf` is **retired**: no proof uses it.
3. The uniformity theorems are part of RD-2, as the fill **RD-2b**.
4. The `ψ` matrix is a **guarded CNF** (option T2 of the design note §7.3), so the private
   Tseitin lemmas of the colleague-owned `CircuitComplexity/DAGCircuitSat.lean` are not
   needed.
5. The `ψ` emitter is a **machine**, on H6 and the `PolyTimeComputable` closure algebra.
6. The transition gates are **truth-table templates**, as in Cook–Levin.

Audit rounds verify these decisions; they do not dispose of them (`workflow.md` §1).

## What the files state (verify)

### `FormulaKit/Gate.lean` (namespace `Complexity.FormulaKit`; imports `Formulas/CNFEncoding` only)

- `blockVar base width t i = base + t·width + i`.
- `template ℓ p`: for `r = 0, …, 2^ℓ − 1` in order, the clause excluding the row `bitsOf ℓ r`
  (bit `i` is `r.testBit i`), kept iff `p` is false there. `gate ℓ p wire` is
  `(template ℓ p).relabel wire`; `readBit v j` reads `v` at `j < ℓ`, `false` above.
- `template_eval`: the template evaluates to `p` of the first `ℓ` values. `gate_eval`
  (proved from it): a gate computes `p` on `a ∘ wire`. Bounds: `template_numVars_le` (`≤ ℓ`),
  `template_length_le` (`≤ 2^ℓ`), `template_widthAtMost` (`ℓ`).
- `exactlyOne vs`: one positive clause over the list, then for each `v` and each listed
  `w ≠ v` the clause `¬v ∨ ¬w`, in list order. `exactlyOne_eval`: true iff some listed `j`
  has `a v = decide (v = j)` for every listed `v`.
- `cost φ = Σ_C (|C| + 1)`, generic over the variable type; `cost_relabel`, `cost_append`
  (proved), `cost_flatMap_le`; `serialize_length_le` (variables below `N` ⇒ at most
  `cost φ · (N + 3) + 1` bits); `gate_cost_le` (`≤ 2^ℓ (ℓ + 1)`); `exactlyOne_cost_le`
  (`≤ m + 1 + 3m²`); `numVars_le_of_forall_lt`.

### `FormulaKit/Emit.lean` (same namespace; imports Gate and `ClassNP/PolyTimeBlockLoop`, `PolyTimePairing`, `Transducer`)

- `fragment φ` = the serialization without the formula terminator;
  `serialize_eq_fragment` (`rfl`), `fragment_append`, `fragment_flatMap` (proved);
  `polyTimeComputable_fragment_iff_serialize`.
- `polyTimeComputable_flatMap_range count chunk`: if `x ↦ 1^(count x)` and
  `z ↦ chunk (pairFstD z) |pairSndD z|` are polynomial-time, so is
  `x ↦ (range (count x)).flatMap (chunk x)` (over `Complexity.polyTimeComputable_emitIter`,
  `ClassNP/PolyTimeBlockLoop.lean:315`). `polyTimeComputable_serialize_flatMap` (proved from
  it).
- `polyTimeComputable_fragment_relabel φ wire`: a fixed `φ` relabeled by wires that are
  polynomial-time in unary below `φ.numVars` has a polynomial-time fragment.
  `polyTimeComputable_fragment_gate` (proved from it); `polyTimeComputable_fragment_gate_select`:
  a gate whose predicate `pred (kind z)` is chosen from a finite type of kinds by a
  polynomial-time key.
- Unary index arithmetic: `polyTimeComputable_unary_add` (proved), `…_sub`, `…_mul`,
  `…_pow` (proved from `mul`), `…_le` (one-bit verdict), `…_div`, `…_mod`, with variable
  operands.
- `polyTimeComputable_serialize_relabel_add F o`: shifting every variable by a
  polynomial-time offset preserves polynomial-time serialization.

### `Formulas/QBF.lean`, additions (namespace `Complexity.QBF`; `QBF.lean.txt:180–296`; all proved)

- `PrefixTruth P qs σ i`: the recursion of `truthAux` (`QBF.lean:94–97`) with the leaf
  `P σ` in place of `m.eval σ = true`. `truthAux_iff_prefixTruth`, `prefixTruth_congr`,
  `prefixTruth_append`.
- `truthAux_exSuffix_iff m j σ i (hm : m.numVars ≤ i + j)`: `j` existential quantifiers
  from variable `i` hold iff some `τ` agreeing with `σ` below `i` satisfies `m`.
- `truth_exSuffix_of_pointwise qs T G P (hT : T.numVars ≤ |qs| + G) (hpt)`:
  `truth ⟨qs ++ replicate G .ex, T⟩ ↔ PrefixTruth P qs (fun _ => false) 0`, where
  `hpt : ∀ σ, (∃ τ, (∀ v < |qs|, τ v = σ v) ∧ T.eval τ = true) ↔ P σ` — correctness of the
  auxiliary encoding **for every prefix assignment σ**.

### `ClassPSPACE/TQBF.lean`, the new `Complexity.ConfigCodec` surface

Definitions (`TQBF.lean.txt:133–439`): the layout `stateCount = card + 1`, `stateIndex`
(halt `0`, else `equivFin q + 1`), `stateOffset n = 2n + 2`, `workOffset`, `summaryOffset`,
`width M n s = 2n + 4 + Q + 3k(2s + 1)`; the field indices `inputVar i = i`,
`headVar n j = n + j`, `stateVar`, `workVar M n s i j b = workOffset + 3((2s+1)i + j) + b`,
`summaryVar` (`false`: output `[true]`; `true`: dead); `workFlags` (holds `false`, holds
`true`, head here, at exact integer position `j − s`); `code` (input bits, one-hot input head,
one-hot state, work flags tape by tape and cell by cell, the two summary flags); `validity`
(exactly-one head, state and per-tape head markers; no cell with both symbol flags; not both
summary flags); `acceptance` (two unit clauses: halt marker, accept flag); `inputEquality`
(two clauses per input bit across the blocks); `Case`, `caseAction`, `caseList`; `Port k`
(`3k + 7` ports, deriving `Fintype`, `DecidableEq`), `portCount`, `portIndex`, `portOf`;
`Expect` (copy, constant, recomputed summary), `GateKind = Case × Bool × Expect`;
`readSymbol`, `readSummary`, `summaryWord`, `guard`, `expectBit`, `kindPred` (guard ⇒ new bit
is expected bit); `headOf s h i = h / (2s+1)^i % (2s+1)`; `moveInput` (`moveInputPos` on
`ℕ`); `expectOf n s p h q v` (the kind of target bit `v`); `portWire`; `transitionGate`
(the template of the kind `(q, 0 < p ≤ n, expectOf …)`, wired by `portWire ∘ portOf`);
`transition` (`p < n + 2`, `h < (2s+1)^k`, `q ∈ caseList`, `v < width`, nested in that
order); `adjacency = inputEquality ++ transition`.

Theorems (`TQBF.lean.txt:2142–2459`): layout and ports — `width_eq` (proved), `width_le`,
`stateVar_none` (proved), `card_port`, `portIndex_lt`, `portOf_portIndex` (proved); the
closed-form indexing contract `code_length` and `code_getD_inputVar/headVar/stateVar/
workVar/summaryVar`; the old clauses (table below); uniformity —
`polyTimeComputable_serialize_validity/adjacency/acceptance (n s o)` and
`polyTimeComputable_code_initCfg (s)`.

### The old statement's clauses, one by one

| Old clause (`TQBF.lean`) | New theorem (`TQBF.lean.txt`) | Change |
|---|---|---|
| `(code x c).length = C·(s+n+1)` (`:1748–1749`) | `code_length` (`:2216`), `width_le` (`:2170`) | exact closed-form width, bounded by `(card + 6k + 5)(s+n+1)`; no padding |
| input separation, windowed (`:1750–1752`) | `code_input_eq` (`:2272`) | window hypotheses dropped |
| codes equal ↔ `coreSum` equal (`:1753–1755`) | `code_eq_iff` (`:2288`) | none |
| `φv` ↔ codec image, `|w| = C(s+n+1)` (`:1756–1759`) | `validity_eval_iff` (`:2302`) | `|w| = width` |
| `φa` ↔ quotient step (`:1760–1763`) | `adjacency_eval_iff` (`:2322`) | none |
| `φa` false across inputs (`:1764–1767`) | `adjacency_eval_of_ne` (`:2335`) | window hypotheses dropped |
| `φacc` ↔ halted ∧ accept (`:1768–1771`) | `acceptance_eval_iff` (`:2347`) | length and window hypotheses dropped |
| `φv.numVars ≤ ℓ` (`:1772`) | `validity_numVars_le` (`:2356`) | `ℓ = width` |
| `φacc.numVars ≤ ℓ` (`:1773`) | `acceptance_numVars_le` (`:2362`) | `ℓ = width` |
| `φa.numVars ≤ 2ℓ` (`:1774`) | `adjacency_numVars_le` (`:2371`) | `ℓ = width` |
| three serialized lengths `≤ C(s+n+2)^C` (`:1775–1777`) | `exists_serialize_length_le` (`:2383`) | `∃ K, ∀ n s`, separate from the width coefficient |
| (absent) | `code_getD_*` (`:2224–2264`) | **new**: the indexing contract |
| (absent; "private, named fill obligations" of the summit, `:2613–2626`) | the four uniformity theorems (`:2407–2459`) | **new** |

The repaired properties of the P4.3 rounds are kept: no full-output injectivity (round-1
finding 1); validity guards midpoints (finding 3); halted vertices self-adjacent, live ones
not necessarily (round-2 finding 3); the input carried in the code (finding 7); serialized
sizes at base `s + n + 2` (finding 8, round-2 finding 1); per-gate, polynomial universality
(round-2 finding 4).

**Evidence that retiring the existential loses nothing used.** `rd2Evidence_oldShape`
(`audits/evidence/rd2-gate/TQBFEvidence.tail.lean.txt`, elaborated appended to the `TQBF`
harness; not landing) proves from the eleven theorems the old statement with its first
clause replaced by "a width `ℓ ≤ C(s+n+1)` and exact length `ℓ`". The exact padded length is the only clause
not recovered.

### The restated `TQBF_PSPACEHard` sketch (`TQBF.lean.txt:3227–3293`)

Same statement. The sketch now runs over `ConfigCodec` with `W := width M n s` levels; the
prefix is level-blocked (`blockVar 0 W`: target block `0`, level `r` with midpoint `3r + 1`
and the universal pair in `3r + 2`, `3r + 3`); the matrix is a **guarded CNF** whose
auxiliary variables (one guard per level, disequality witnesses for the selectors) come after
the prefix and feed `QBF.truth_exSuffix_of_pointwise`; truth by the codec theorems and the
quotient dictionary; the emitter is a machine over the kit and the uniformity theorems.
Fill obligations and the host (H6) are named; two needs are recorded as **not supplied by
RD-2**: the guard-literal transducer (a leaf row) and the bounded-reachability kit of design
§14 (not yet built).

## The migration at RD-2a (`audits/logs/rd2-statements-migration.log`)

The table lists all 120 declarations of the B4a block (119 private and the old statement,
tip lines 114–1811), with line ranges including docstrings (MEASURED). The categories are
computed mechanically. MERGE, MOVE and RETIRE are given. REWRITE is given for the nine
numbered objects and propagated to every declaration whose text names a REWRITE, MOVE or
RETIRE declaration. Every remaining declaration is KEEP, or KEEP-R if it names a MERGE row.
The propagation found no conflict.

| Fate at RD-2a | Declarations | Lines | Meaning |
|---|---|---|---|
| KEEP | 39 | 510 | byte-identical (the finite rows, `codecBitsValid*`, `codecRow_realize`, `codecObserve*`, `codec_absorb`, `codecInputRead_wire`, …) |
| KEEP-R | 15 | 193 | byte-identical up to the rename map below (`codecGuard*`, `codecExpected*`, `codecGate`, `codecGateWire`, `codecAction_apply`, …) |
| MERGE | 10 | 48 | private twin deleted, uses renamed: `CodecCase`, `codecAction`, `codecSummaryWord`, `codecReadSymbol`, `codecReadSummary`, `CodecPort`, `codecCnfCost` and its three lemmas |
| MOVE | 7 | 146 | generic, deleted here, role taken by the kit: `codecOneHot(_eval/_cost)`, `codecCnf_numVars`, `codecCnf_serialize`, `codecLocalCheck`, `codecPort_card` |
| REWRITE | 39 | 482 | same role over the closed form: `codecWord*`, `configurationCodec*`, `codecValidity*`, `configuration{Validity,Acceptance,InputEquality,Adjacency}*`, the size ledgers, `codecPairWire*`, `codecTransitionCNF(_eval/_step_iff/_cost)` |
| RETIRE | 10 | 180 | the padding (5), `codecGate_cnf`, `codecGateCNF(_spec)`, `CodecGateIndex`, `exists_adjacency_codec_cnf` |

Rename map (KEEP-R): `CodecCase ↦ ConfigCodec.Case`, `codecAction ↦ ConfigCodec.caseAction`,
`codecSummaryWord ↦ ConfigCodec.summaryWord`, `codecReadSymbol ↦ ConfigCodec.readSymbol`,
`codecReadSummary ↦ ConfigCodec.readSummary`, `CodecPort M ↦ ConfigCodec.Port M.k`,
`codecCnfCost(_relabel/_append/_flatMap_le) ↦ FormulaKit.cost(_relabel/_append/_flatMap_le)`.
The public and private bodies are identical (`Port` is indexed by `k` where `CodecPort` is
indexed by `M`, with the same constructors), and `cost` is generic over the variable type, as
`codecCnfCost` is, so the rename is textual.

**Survival is 703 lines (KEEP + KEEP-R), not the design note's "≈ 820"** (design note §1.4,
an estimate of ±30 lines per row). The note counted `codecValidity_cost_raw` and
`codecTransitionCNF_step_iff` as verbatim, but their statements name rewritten objects
(`codecValidity`, `codecTransitionCNF`). It also counted the merged private twins as
surviving, although §4.2 of the same note makes them public. This pack treats the
`step_iff` proof body after its first line as reusable inside a REWRITE row.

Other edits:

| When | File | Edit |
|---|---|---|
| statement PR | `TQBF.lean` | imports `FormulaKit.Gate`, `FormulaKit.Emit`; module docstring (design bullet, main lists, references); the two new blocks; a status line in the old statement's docstring; `TQBF_PSPACEHard`'s docstring |
| statement PR | `Formulas/QBF.lean` | additions and module docstring |
| statement PR | `ClassPSPACE.lean`, `TCSlib.lean` | facade docstring; the new facade's import |
| RD-2a | `TQBF.lean` | the migration above; the fill-appendix header (`TQBF.lean:114–130`, "numbered by a finite equivalence … zero padding") rewritten |
| RD-2a | `Build/CfgRecord.lean:93–96` | the `Cfg.InWindow` docstring names `Complexity.exists_adjacency_codec_cnf`; re-point it at `Complexity.ConfigCodec.code` (docstring only; a `Build` file, so the downstream rebuild is large) |
| with the PR | design §14 row H6, §16b item 2; backlog RD-2; plan `:843` | the maintainer's record edits |

## Changes from the draft (`audits/evidence/rd2/RD2Draft.lean.txt`)

The draft had 48 definitions and 47 theorems (11 proved). The landing form has the same 48
definitions and 61 theorems (20 proved, 41 sorried).

- **Homes and namespaces.** The draft's `Complexity.Draft.RD2.*` becomes `Complexity.FormulaKit`
  (two files and a facade), `Complexity.QBF` and `Complexity.ConfigCodec`. The draft's
  section header placed the prefix lemmas in "`FormulaKit/Tseitin.lean`", but the design
  note's table (§3.1) puts them in `Formulas/QBF.lean`; the landing form follows the table.
  `Gate.lean` imports only `Formulas/CNFEncoding` (the draft imported `TQBF` and
  `DAGCircuitSat`).
- **Removed (3).** `exists_toCNF_extension_iff` and `truth_tseitin_after_prefix` are gone by
  decision 4: they have no consumer and would import a colleague-owned file.
  `exists_adjacency_codec_cnf_of_closedForm` is gone by decision 2; it is kept as gate
  evidence (`rd2Evidence_oldShape`).
- **Added (17).** `cost_relabel`, `cost_append` and `cost_flatMap_le`, so that the private
  `codecCnfCost` family merges instead of surviving as a twin.
  `polyTimeComputable_fragment_iff_serialize`, because the uniformity theorems conclude on `serialize` while the emission theorem consumes
  `fragment`. `polyTimeComputable_fragment_relabel`, the public form of Cook–Levin's
  `clA5Template_native`, now the base of `polyTimeComputable_fragment_gate`.
  `polyTimeComputable_fragment_gate_select`, the snapshot-keyed form both consumers need.
  The unary index arithmetic (7): the design note's §2.2 lists Cook–Levin's unary closures as
  "generic", but the draft's kit had none, and the codec divides by `2s + 1`, which grows with
  the input. `stateVar_none`, `card_port`, `portIndex_lt` and `portOf_portIndex`, the port
  contract the adjacency sketch uses.
- **Strengthened.** The three CNF uniformity theorems take the input length as a
  polynomial-time parameter `n` (the draft fixed it to `x.length`), so that a per-level
  emitter can call them on `⟨x, 1^r⟩`; the draft's form is the instance `n := List.length`
  (evidence `rd2Evidence_validity_at_length`).
- **Proved now.** `truthAux_exSuffix_iff` (12 lines, with the file's private Q3), so the
  prefix lemma lands closed. Also `polyTimeComputable_serialize_flatMap`,
  `polyTimeComputable_fragment_gate`, `polyTimeComputable_unary_add`/`_pow` and the four
  port and layout facts.
- **Small.** `Port` and `Expect` derive `Fintype`, `DecidableEq`. The ConfigCodec
  definitions moved before the fill appendix. The `ConfigCodec` docstrings were rewritten with
  [AB09] tags, and `TQBF_PSPACEHard`'s sketch and the module docstring were rewritten. The
  old sketch's remark "continuation budget certain" is dropped.

## Known deviations (declared in the docstrings; verify they are benign, flag any other)

- Code width `O(s + n)`, not `O(s)` (the input is carried); sizes through serialized lengths at
  base `s + n + 2`; halted vertices self-adjacent, live ones not necessarily (deviations
  (i)–(iii) of the module docstring, unchanged from P4.3).
- **No padding**: the width is closed form and only *bounded* by `C·(s + n + 1)`.
- `code_input_eq`, `adjacency_eval_of_ne`, `acceptance_eval_iff` drop the window (and, for
  acceptance, the length) hypotheses of the old clauses: these are strengthenings.
- Templates are the explicit truth table in `List.range` order, not a choice from
  [AB09, Claim 2.13]'s universality (`exists_cnf_boolFun`).
- Two machine-constant choices: `stateIndex`, `caseList`.
- The auxiliary-variable lemma is stated for any CNF correct at every prefix assignment
  ([AB09, §4.2, p. 83]); the Tseitin circuit instance is not stated.

## Brief for the auditor

1. **The layout and the three CNFs, clause by clause.** For each row of the clause table,
   check that the new theorem is at least the old clause, and that the definitions mean what
   [AB09, Claim 4.4(2)] and the docstrings say. Check in particular:
   - the work-cell flags at exact integer positions (`workFlags`): a head outside the window
     marks no cell, so a step that leaves the window cannot be adjacent to any windowed `d`;
   - the input-symbol port of an end-marker position reads a variable that `guard` ignores;
     interior positions read source bit `p − 1` (`Cfg.inputSymbol`,
     `TuringMachine/Configuration.lean:158`);
   - `moveInput` against `moveInputPos` (`:115`); the head-flag expectation
     `headOf + move = j`; writes `some w` with `w : Option Bool`, blank included
     (`Action.apply`, `:199`);
   - the summary recomputation through `summaryWord ∘ readSummary` and the append table
     (`outSummary`, `SpaceComplexity/ConfigGraph.lean:117`; `outSummary_append_congr`, `:135`);
   - the halted case (`caseAction` at `none` is the silent identity; `step_of_halt`,
     `Deterministic.lean:163`);
   - coverage: `transition` ranges over every input position, head tuple (`headOf`, mixed
     radix), case and coordinate.

   Report any `(n, s, c, d)` on which a stated equivalence fails. Try at least `k = 0`,
   `s = 0`, `n = 0`, a halted `c`, and a step that leaves the window.
2. **Retiring the existential.** Does anything need the old statement's exact length
   `C·(s + n + 1)` or its packaged form? Check `rd2Evidence_oldShape` against
   `TQBF.lean:1744–1777`, and the consumer grep above. Should a packaged corollary be kept
   after all, and under which name?
3. **Uniformity strength for `TQBF_PSPACEHard`'s emitter.** Are the four theorems, with the
   kit, enough for a machine emitting the level-blocked guarded formula? In particular:
   - per-level calls at input `⟨x, 1^r⟩` with offset `(3r + 1)·W` — the reason `n` is a
     parameter;
   - the pairing with the prefix word in `Complexity.QBF.encode`
     (`Formulas/QBFEncoding.lean:69`);
   - whether `exists_serialize_length_le` is still needed once size follows from polynomial
     time.

   Name any lemma the emitter will need that neither RD-2 nor the closure algebra supplies.
   The pack names two: the guard-literal transducer and the bounded-reachability kit.
4. **The auxiliary-variable lemma for the guarded CNF.** `QBF.truth_exSuffix_of_pointwise`
   (`QBF.lean.txt:282`) is proved, with axioms `[propext, Quot.sound]`. Check that its
   hypothesis `hpt` is exactly "correct for every prefix assignment" (design §14 row H6),
   that the auxiliary values may depend on every universal variable (P4.3 round-1 answer 5),
   and that `hT` and the `0`-based variable convention fit the level-blocked prefix. Is the
   interface right for T2, whose pointwise lemma (the guards force the guarded clauses exactly
   when the selectors hold; the witnesses certify each failed selector) belongs to B4
   hardness? Should a guarded-clause primitive and its evaluation lemma enter the kit now?
5. **The kit's interface and its fit to Cook–Levin.** Map Cook–Levin's private kit
   (`CookLevin/Hardness.lean`):
   - `clPack` `:185` ↔ `blockVar`;
   - `clTemplate` `:241` ↔ `template` (explicit, not chosen);
   - `clGroup` `:462` ↔ `gate` of a kind;
   - `clFragment` `:123` ↔ `fragment`;
   - `clChunks_serialize` `:153` and `clEmitter_of_body` `:544` ↔
     `polyTimeComputable_serialize_flatMap`;
   - `clA5Template_native` `:6996` ↔ `polyTimeComputable_fragment_relabel`;
   - `clA5Add/Sub/Times/Div/Mod/Le_native` (`:7671`, `:7678`, `:6971`, `:7808`, `:7838`,
     `:6981`) ↔ the unary arithmetic.

   Is anything a consumer needs missing? The evidence `example`s check the codec side
   (`transitionGate` is literally `FormulaKit.gate` of a kind, by `rfl`; `GateKind` is
   `Fintype` and `DecidableEq`). Rule on the homes:
   - the kit as a new topic `Complexity/FormulaKit/`, rather than under `Formulas/` (which sits
     below `ClassNP`, so its facade would come to depend on the polynomial-time layer) or
     under `ClassNP/`;
   - the unary arithmetic in the kit, rather than in the `ClassNP` closure layer. It overlaps
     `Complexity.PolyHierarchy.UnaryPT` (`PolyHierarchy/Padding.lean:200–235`: `add`,
     `const`, `comp`; Hydroxyi's).

   Re-basing Cook–Levin on the kit is a later restyling row, not part of RD-2.
6. **The migration list.** Check `audits/logs/rd2-statements-migration.log` against
   `TQBF.lean:114–1811`:
   - every KEEP or KEEP-R row names only KEEP, KEEP-R or MERGE declarations;
   - every MERGE twin is identical to its public successor;
   - nothing that carries an A1–A6 choice survives;
   - the "≈ 820" discrepancy is explained.

   Is the two-block placement inside `TQBF.lean` right?
7. **The restated `TQBF_PSPACEHard` sketch** as a proof plan. Check:
   - the level layout and the depth `W` (at most `2^W` codes);
   - the guarded matrix, at the level of the sketch;
   - the truth induction's ingredients, including the window lemma for the decider's runs
     (`ConfigCount.lean:248`, `abs_pos_lt_card_visited`) and the cross-input rejection;
   - the emission plan;
   - the named obligations, and the host list against design §14.
8. **Placement and modularity** (`policy.md` §1): the two new files and the facade, their
   imports, namespaces and export; the additions to `QBF.lean`; and the in-place codec versus
   a separate `ClassPSPACE/ConfigCodec.lean`. File size is not a criterion here: `TQBF.lean`
   was already past `policy.md`'s 1000-line guideline at the tip (2639 lines, now 3305), and
   the user has ruled that size alone triggers no split.
9. **Statement-phase proofs** (`workflow.md` §2; declared part of the audited surface). The
   proofs: `gate_eval`, `cost_relabel`, `cost_append`, `serialize_eq_fragment`,
   `fragment_append`, `fragment_flatMap`, `polyTimeComputable_serialize_flatMap`,
   `polyTimeComputable_fragment_gate`, `polyTimeComputable_unary_add`, `…_pow`, the five
   `QBF.lean` theorems, `width_eq`, `stateVar_none`, `card_port`,
   `portIndex_lt`, `portOf_portIndex`. Four of them are corollaries of sorried kit
   statements: `gate_eval`, `…_serialize_flatMap`, `…_fragment_gate`, `…_pow`. Say whether
   any should wait for the fill.
10. **Documentation and policy** (`policy.md` §2–3): statement prose on every public
    declaration; `[AB09]` tags (Claim 4.4(2), pp. 80–81; Theorem 4.13, pp. 84–85; Claim 2.13,
    p. 46; Lemma 2.11, pp. 45–49; §4.2, p. 83); Cook–Levin's indexing cited as internal
    precedent; a literal proof sketch on every nontrivial sorried statement; the 100-column
    limit.
11. **Duplication** (template failure mode 5; table below). Is anything a copy that is not
    disclosed?
12. Report anything else the files or this pack misstate, in the standard table.

## Duplication introduced by the statement PR (disclosed)

| Public (new) | Twin | Lines | Resolution |
|---|---|---|---|
| `ConfigCodec.Case`, `caseAction`, `summaryWord`, `readSymbol`, `readSummary`, `Port` | private `CodecCase`, `codecAction`, `codecSummaryWord`, `codecReadSymbol`, `codecReadSummary`, `CodecPort` (`TQBF.lean:1226–1293`); identical bodies, `Port` indexed by `k` | ≈ 25 | MERGE at RD-2a |
| `FormulaKit.cost`, `cost_relabel`, `cost_append` (one-line proofs) | private `codecCnfCost` family (`TQBF.lean:642–654`) | ≈ 8 | MERGE at RD-2a |
| `ConfigCodec.card_port` proof (3 lines) | private `codecPort_card` (`TQBF.lean:1274–1278`) | 3 | MOVE at RD-2a |
| `FormulaKit.blockVar`, `fragment` | private `clPack`, `clFragment` (`Hardness.lean:185`, `:123`) | 4 | Cook–Levin re-basing row |
| `FormulaKit.excludeClause` | private `falsifyingClause` (`Formulas/CNF.lean:155–156`) | 2 | make the private public, or keep (CNF.lean sits below the kit) |
| `FormulaKit.polyTimeComputable_unary_add` proof (1 line) | private `clA5Add_native` (`Hardness.lean:7671`); `PolyHierarchy.UnaryPT.add` (`Padding.lean:223`, Hydroxyi) | 1 | re-basing row; the `UnaryPT` overlap goes to the maintainer's 12.2c dedup window |

All twins are maintainer-owned except `UnaryPT.add`. None is a copy of proved material beyond
one-line unfolding proofs.

## Repository-side attestations (verify or challenge)

Source facts:

- The old statement has no Lean proof consumer (grep above).
- `Formulas/QBF.lean`, `CookLevin/Hardness.lean`, `Formulas/CNF.lean`,
  `Formulas/CNFEncoding.lean`, `ClassNP/PolyTimeBlockLoop.lean`, `ClassNP/PolyTimePairing.lean`,
  `Build/CfgRecord.lean` and `ClassPSPACE/TQBF.lean` are byte-identical between the tip and the
  worktree the design note read. The design note's `file:line` references into these files
  stand. Its references into `machine-library-design.md` and `backlog.md` are to that
  worktree and are shifted at the tip (H6 is `:3065`, §16b item 2 is `:3786`, RD-2 is
  `backlog.md:698`).

Maintainer execution claims:

1. **Elaboration** (`audits/logs/rd2-statements-elaboration.log`). Every file was elaborated
   read-only (`lean <file>`, no `-o`, no `lake`) against the olean tree `oleans-f7` with the
   tip checkout, Lean `v4.25.0`. A proposed file that imports another proposed module was
   elaborated as a **harness**: the dependencies' bodies verbatim, under the union of their
   imports (asserted by the generator `audits/evidence/rd2-gate/tools/mkharness.py`; SHA-256
   sums in the log). Results:

   | File | Errors | `sorry` warnings | Other warnings |
   |---|---|---|---|
   | `FormulaKitGate.lean` (direct) | 0 | 10 | 0 |
   | `harness/FormulaKitEmit` (Gate + Emit) | 0 | 20 (10 + 10) | 0 |
   | `harness/FormulaKit` (Gate + Emit + facade) | 0 | 20 | 0 |
   | `QBF.lean` (direct, full file) | 0 | 0 | 0 |
   | `harness/TQBF` (Gate + Emit + full `TQBF.lean`) | 0 | 44 (20 kit + 21 new + the tip's 3) | 0 |
   | `ClassPSPACE.lean` (direct) | 0 | 0 | 0 |
   | `evidence/QBFEvidence` (`QBF.lean` + names and axioms) | 0 | 0 | 0 |
   | `evidence/TQBFEvidence` (`TQBF` harness + evidence tail) | 0 | 44 | 0 |

2. **Axioms** (from the evidence files, in the log). The `QBF.lean` additions depend on at
   most `[propext, Quot.sound]`. `cost_relabel`, `cost_append`, the fragment lemmas,
   `unary_add`, `width_eq`, `stateVar_none`, `card_port`, `portIndex_lt` and
   `portOf_portIndex` depend on at most the standard three. The corollaries of sorried
   statements show `sorryAx`. The old `exists_adjacency_codec_cnf` still shows exactly the
   standard three in the proposed file.
3. **Freeze** (`audits/logs/rd2-statements-freeze.log`). The comment-stripped text of all 172
   tip declarations of `TQBF.lean`, and of all 8 of `QBF.lean`, reappears verbatim and in
   order. The additions are 64 and 6 declarations. The comment-stripped tip lines are a
   subsequence of each proposed file, so the patches remove only comment text.
4. **Names** (`audits/logs/rd2-statements-names.log`). Every identifier cited in the new
   docstrings resolves by `#check`, or, for the private declarations of other modules, by
   grep. A full-name screen of `TCSlib/` found no existing `FormulaKit`, `ConfigCodec`,
   `PrefixTruth`, `exSuffix`, `blockVar`, `exactlyOne` or `polyTimeComputable_unary_*`.
5. **Lint** (`audits/logs/rd2-statements-lint.log`). `scripts/style_lint.py`, unmodified, was
   run in a mirror tree at the landing paths. The new files have 0 findings. `TQBF.lean`,
   `QBF.lean` and `ClassPSPACE.lean` have exactly the tip's findings: `TQBF.lean`'s size, two
   sketch-less private proofs, and the facade's missing options. Every new or changed line is
   within 100 columns; the six over-long lines are the tip's.
6. **No `lake`, no `.olean` written, no git command.** Python was run only as `python3 -I`.
7. **The maintainer's re-check.** The maintainer, with the same tool and snapshot, re-elaborated
   all eight rows of the table in item 1, with the same counts. Separate maintainer scripts
   checked that:
   - each harness holds its dependencies' bodies and its own, verbatim and in order;
   - each evidence file is its base followed by its tail, exactly;
   - the three patches, regenerated against the tip, reproduce;
   - the tip's comment-stripped code is a subsequence of each edited file, whose only added
     imports are `FormulaKit.Gate` and `FormulaKit.Emit` (in `TQBF.lean`).

   The maintainer's own declaration-freeze tool (`declfreeze.py` v2) agrees: no statement
   changed, no public removed, and no private added, removed or changed. Its two body-change
   flags, `TQBF_PSPACEHard` and `exists_adjacency_codec_cnf`, are the docstring rewrites
   disclosed above.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide as in `audits/TEMPLATE.md`. **Blocker**: a downstream phase (RD-2a, RD-2b or
B4 hardness) would build on a wrong statement. **Major**: fixable but materially misleading
as it stands, or undisclosed or unacknowledged debt. **Minor**: an edge case, naming or
attribution defect. **Note**: an observation; no change required. Findings go verbatim into
`audits/rd2-statements-findings.md`. The gate closes on a round with zero blockers and zero
majors; the files then land by a PR the user merges.
