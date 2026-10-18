# RD-2 design note: B4a restated in place over the H6 kit

Backlog RD-2 (`backlog.md:630–635`); design `machine-library-design.md` §16b item 2
(`:3641–3651`) and §14 row H6 (`:3056`). Worktree read: `wt-rd2` (tip `3462c1b4` plus the
2026-10-12 records). All `file:line` references are to that worktree unless marked otherwise.
Sizes are **estimates** unless marked MEASURED.

Deliverables in this directory:

- `RD2Draft.lean`: the sorried statement draft, namespace `Complexity.Draft.RD2`, 944 lines
  (MEASURED): 48 definitions with bodies and 47 theorems, of which 11 are proved (among them
  the Tseitin-after-prefix lemma and the old-shape corollary, from the sorried ones) and 36
  are `sorry` with a proof sketch. Elaboration with `tools/leanelab.sh` against `oleans-m1`: **0 errors, 36
  warnings, all of them `declaration uses 'sorry'`** (log `elab.out`). The repository style
  lint (`scripts/style_lint.py`, run on a copy) reports 0 findings.
- `RD2-design.md`: this note.

---

## 0. Summary

**Decision being designed** (user, 2026-10-12): `Complexity.exists_adjacency_codec_cnf`
(`ClassPSPACE/TQBF.lean:1744`) becomes public definitions of the configuration codec and its
three CNFs, with closed-form variable indexing, and theorems in place of its
`∀ n s, ∃ code φv φa φacc, …`.

**Proposal in one paragraph.** A new kit `Complexity.FormulaKit` (H6) provides fixed-arity
gate templates given by an explicit truth table, closed-form wiring, the exactly-one gadget,
the cost and serialization ledgers, and an *ordered uniform emission* theorem built on the
public `Complexity.polyTimeComputable_emitIter`. `Formulas/QBF.lean` gains a generalized
prefix semantics `QBF.PrefixTruth` and the **Tseitin-after-prefix** lemma
`truth_exSuffix_of_pointwise` (any encoding whose auxiliary variables are existentially
quantified after the prefix and which is correct pointwise), with its instance for the
existing circuit Tseitin `BoolCircuit.DAGCircuit.toCNF`. The codec becomes
`ConfigCodec.code` with the closed-form layout `input | input head | state | work cells |
summary` and the CNFs `ConfigCodec.validity`, `.adjacency`, `.acceptance`, every clause list
ordered by `List.range`, every gate a fixed template of a machine-constant *kind* wired in
closed form. The old statement's clauses become eleven theorems, plus four **uniformity**
theorems (the three CNFs at any polynomial-time offset, and the initial vertex's code, are
polynomial-time computable), which the packaged existential could never supply. About half
of the present 1,700-line proof survives verbatim.

---

## 1. The present construction

### 1.1 What the statement says

`exists_adjacency_codec_cnf` (`TQBF.lean:1744–1777`): for each machine `M` there is
`C > 0` such that for all `n s` there exist `code`, `φv`, `φa`, `φacc` with: code length
`C·(s+n+1)` for all inputs; input separation on windowed configurations; code equality iff
`NDTM.coreSum` equality at one input; `φv` characterizes the codec image among words of the
code length; `φa` is the step on the vertex quotient (same input) and rejects distinct
inputs; `φacc` is "halted with `accept` summary"; `numVars` bounds; serialized lengths at
most `C·(s+n+2)^C`. Proof at `:1778–1811`, assembled from 119 private declarations
(`audits/b4a-fill-agent-reports/REPORT.md`, "All 119 new explicit declarations are private")
in `:114–1743`.

### 1.2 Where the non-uniformity enters

"Non-uniform" here means: the formula's literal indices or clause order are values of a
choice that no proof can compute, over a type that grows with `n` and `s`, so no emitter's
output can be shown equal to the formula.

| # | Where | What | Why it is opaque |
|---|---|---|---|
| A1 | `codecWord`, `TQBF.lean:302–307` | bit `i` of the padded code is `a ((Fintype.equivFin α).symm ⟨i, _⟩)` with `α = CodecBit M n s` | `Fintype.equivFin α := (truncEquivFin α).out` (Mathlib `Data/Fintype/EquivFin.lean:76–78`): a choice of bijection, unspecified |
| A2 | `configurationCodec`, `:333–337` | the code is `codecWord (C*(s+n+1)) …` | inherits A1 |
| A3 | `configurationValidity`, `:587–589`; `configurationAcceptance`, `:629–630`; `codecPairWire`, `:977–979` | variables are numbered `(Fintype.equivFin (CodecBit M n s) b).val` | inherits A1 |
| A4 | `codecOneHot`, `:377–381` | clause order `Finset.univ.toList` over `Fin (n+2)`, `Option M.State`, `Fin (2s+1)` (used at `:482–485`) | `Finset.toList` (Mathlib `Data/Finset/Dedup.lean:159`) is `Multiset.toList = s.out` (`Data/Multiset/Basic.lean:29–30`): a choice of order |
| A5 | `codecTransitionCNF`, `:1532–1535` | gate order `Finset.univ.toList : List (CodecGateIndex M n s)`, the index type `:1528–1529` = positions × cases × coordinates | as A4, over a type depending on `n, s` |
| A6 | `codecGateCNF`, `:1515–1517` | each gate is `(codecGate_cnf M n s p q b).choose`, from `codecLocalCheck` (`:934–951`), which applies `exists_cnf_boolFun` **after** wiring | the chosen clause list depends on the position `p` and coordinate `b`, not only on a finite kind, and is a `Classical.choose` |
| A7 | the statement itself, `:1745–1747` | `∃ C, ∀ n s, ∃ code φv φa φacc` | no definition to unfold; the docstrings already say so (`:52–57`, "The package is existence, not an algorithm"; `:2613–2614`, "The packaged existential supplies no algorithm") |

Machine-constant choices are **harmless** and stay: they range over types fixed by `M`, so
an emitter for the fixed machine stores them as a finite table. In the present code:
`Fintype.equivFin (CodecPort M)` (`:1505`), the case type `CodecCase M` (`:1247–1248`), and
the truth-table construction of `exists_cnf_boolFun` (`Formulas/CNF.lean:177–179`, a
`Finset.univ` order over `Fin ℓ → Bool` with `ℓ` fixed). Cook–Levin relies on the same
principle (`clFieldCode`, `CookLevin/Hardness.lean:270–279`, a `Classical.choice` of an
embedding for `Option M.State`; `clTemplate`, `:241–243`, a `Classical.choose` per finite
kind). The draft keeps two such choices, both documented: `ConfigCodec.stateIndex` (through
`Fintype.equivFin M.State`) and `ConfigCodec.caseList` (through `Finset.univ.toList` over
`Case M`).

### 1.3 What the proof relies on

The proof factors through three layers (the fill appendix, `:114–130`):

1. **The finite row**: `CodecRow` (`:133–139`), `CodecBit` (`:142–148`), the marker
   encoding `codecRowBits` and its injectivity (`:174–237`), the row of a configuration
   through `ConfigCount.coreCode` (`:240–298`), validity of rows and the decoding of valid
   bit assignments (`:424–478`), and the realization of any row by a windowed
   configuration (`:500–547`). None of this mentions an index into `ℕ`.
2. **The local step semantics**: exact-integer observations `codecObserve` (`:1145–1224`),
   the halted identity action and ports (`:1247–1306`), the guard and the expected bit
   (`:1309–1496`), and the step-iff-gates theorem `codecTransitionCNF_step_iff`
   (`:1553–1582`), which uses only `codecTransitionCNF_eval`'s statement.
3. **Numbering, ordering and ledgers**: everything in §1.2, plus the cost and size
   ledgers (`:643–930`, `:1586–1695`) and the absorption of all constants into one `C`
   (`codec_absorb`, `:1099–1126`).

Layers 1 and 2 are where the mathematics is, and they do not depend on the numbering.

### 1.4 What survives a re-indexing (line counts of `:114–1811` by declaration range)

Counted by a script over the declaration ranges, each declaration with its docstring;
boundaries are approximate (about ±30 lines per row).

| Fate | Lines | Declarations |
|---|---|---|
| **Survives verbatim** | ≈ 820 | layer 1 and layer 2 above (`CodecRow` … `codecRowOf_eq_iff`, `codecBitsValid*`, `codec_posCode`, `codecRow_realize`, `codecAcceptance(_eval)`, `codecPairBits`, `codecInputEquality(_eval/_cost)`, `configurationCodec_step_congr`, `codec_posCode_eq_iff` … `codecExpected_step`, `codecTransitionCNF_step_iff`, `codecValidity_cost_raw`; also `codec_square_le_pow`, `codec_absorb` if one size constant is kept) |
| **Moves to the kit** (generic) | ≈ 170 | `codecCnfCost` and its four lemmas (`:643–665`), `codecOneHot(_eval/_cost)` (`:377–420`, `:671–693`, rewritten over a list), `codecCnf_numVars`, `codecCnf_serialize` (`:696–745`); `codecLocalCheck` (`:934–951`) is superseded by `FormulaKit.gate` |
| **Rewritten** (same role, closed form) | ≈ 500 | `codecWord*` and `configurationCodec*` (`:302–364`), `codecValidity(_eval)` (`:481–497`), `configurationValidity/Acceptance(_eval)` (`:587–640`), the size ledgers (`:748–930`, `:1625–1695`), positions and pair wiring (`:954–1011`), the numbered input equality (`:1041–1068`), the gate index and its enumeration (`:1528–1595`), the numbered adjacency (`:1597–1622`) |
| **Retired** | ≈ 185 | padding (`:550–584`), `codecGate_cnf`/`codecGateCNF(_spec)` (`:1499–1525`), the packaged theorem and its proof (`:1698–1811`) |

The bridge that makes layers 1–2 reusable: the public `ConfigCodec.code` reads, at the
closed-form index of each `CodecBit`, the bit `codecObserve` gives it, and on windowed
configurations `codecObserve = codecRowBits ∘ codecRowOf` already (`codecObserve_eq`,
`:1154–1166`). So one new private lemma "the code at `index b` is `codecRowBits (codecRowOf …)
b`, for windowed configurations" lets every surviving lemma be used unchanged.

---

## 2. Cook–Levin's explicit indexing (`CookLevin/Hardness.lean`)

### 2.1 How variables and gates are numbered

- **Variables.** Variables `0 … m-1` are the input and certificate bits, with
  `m = |x| + C·(|x|+1)^e` (`clTableauGroups`, `:486–497`); the input part is pinned by unit
  clauses `[[(j, x[j])]]`. Snapshot `t`'s bit `i` is `clPack m B t i = m + t·B + i`
  (`:185`), with block width `B = clWidth M code = code.width + 2 + 2k` (`:410–411`).
- **Block layout.** State bits (a fixed binary field code of `Option M.State`, `:262–279`),
  then two input-symbol bits, then two bits per work tape (`clBlockEncode` and the slices,
  `:295–313`).
- **Gates.** Every gate has the uniform arity `2B + 1`: a source block, a target block and
  one extra input variable (`clSourceBits`/`clTargetBits`/`clWindowBit`, `:414–424`). A
  gate is the fixed template of its kind, `clTemplate (2B+1) (clPredicate M code kind)`
  (`:241`, `:438–455`), relabeled by the closed-form `clWire m B source target p`
  (`:457–460`); this is `clGroup` (`:462–466`). Kinds form the finite type
  `CLTemplateKind k` (`:427–432`).
- **Order.** The six families in a fixed order, `clGroups` (`:100–110`): `n` pins, the
  initial row, `T` state rows, `T+1` input rows, `k(T+1)` work rows (time, then tape),
  `T` accept rows; `clLastRound` counts them (`:95–96`). Random access by offset
  arithmetic, `clA5GroupAt` (`:7888–7905`).
- **Emission.** Fragments and chunks (`clFragment`, `clChunk`, `:123–135`), the exact word
  identity `clChunks_serialize` (`:153`), the loop assembly `clEmitter_of_body` (`:544`,
  through `FinTM.exists_emitLoopTM`, `:587`), the template-with-native-wires lemma
  `clA5Template_native` (`:6996`), addresses `clA5Address_native` (`:7018`), the per-group
  lemma `clA5Group_native` (`:7027`), and the final identity `clA5OutputIdentity`
  (`:8212`).

### 2.2 Generic and specific

**Generic** (no snapshot or oblivious content): `clPack`; `clTemplate` with its spec and
relabel-eval (`:241–258`); `clFragment`/`clChunk` and their lemmas (`:123–180`);
`clEmitter_of_body`; `clA5Template_native` and `clA5Address_native`; the unary-arithmetic
and selection closures (`clA5Times/Le/Add/Sub/Div/Mod/Select_native`); the closure lemmas
`clA5_pt_const`, `clA5_pt_cond`, `clNative_append`, which repeat public lemmas
(`polyTimeComputable_const`, `polyTimeComputable_ite`, `PolyTimeComputable.append`,
`ClassNP/PolyTimePairing.lean:71, :269, :185`; the docstring at `Hardness.lean:623–625`
records the local repetition).

**Specific**: the snapshot code, `CLTemplateKind`/`clPredicate` (reconstruction from
`stepState`, `writtenOrKept`, `emitted`), `clInputGroup`/`clWorkGroup` (oblivious schedules
`inputPosAt`, `prevVisit`), and the preparation of the packed records by simulation
(`:607–6155`).

**What the codec cannot share.** Cook–Levin's gates read whole blocks because snapshots have
constant size; the codec's blocks have `Θ(s + n)` bits, so its gates must read `O(1)`
scattered bits at positions chosen by the guarded head tuple. The shared scheme is therefore
one level down: closed-form field offsets, `blockVar` for repeated blocks, constant-arity
templates per machine-constant kind with closed-form wires, `List.range`-ordered group
lists, and one emission theorem.

---

## 3. The H6 kit (`FormulaKit`)

### 3.1 Placement and layering

`Formulas/` sits below `ClassNP` (`ClassNP/SAT.lean` imports `Formulas/CNFEncoding.lean`), so
the emission half, which needs `PolyTimeComputable`, cannot live there. Proposal:

| File | Contents | Imports |
|---|---|---|
| `TCSlib/Complexity/FormulaKit/Gate.lean` | `blockVar`, `bitsOf`, `excludeClause`, `template` (+ eval, `numVars`, length, width), `gate` (+ eval, cost), `readBit`, `exactlyOne` (+ eval, cost), `cost`, `serialize_length_le`, `numVars_le_of_forall_lt` | `Formulas/CNFEncoding` |
| `TCSlib/Complexity/FormulaKit/Emit.lean` | `fragment` (+ 3 lemmas), `polyTimeComputable_flatMap_range`, `polyTimeComputable_serialize_flatMap`, `polyTimeComputable_fragment_gate`, `polyTimeComputable_serialize_relabel_add` | `Gate`, `ClassNP/PolyTimeBlockLoop`, `ClassNP/PolyTimePairing` |
| `TCSlib/Complexity/Formulas/QBF.lean` (additions) | `QBF.PrefixTruth`, `truthAux_iff_prefixTruth`, `prefixTruth_congr`, `prefixTruth_append`, `truthAux_exSuffix_iff`, `truth_exSuffix_of_pointwise` | unchanged (they need only `Formulas/CNF`) |
| `TCSlib/Complexity/FormulaKit/Tseitin.lean` (only if a consumer uses circuits, §7.3) | `exists_toCNF_extension_iff`, `truth_tseitin_after_prefix` | `CircuitComplexity/DAGCircuitSat`, `Formulas/QBF`, `Gate` |
| `TCSlib/Complexity/FormulaKit.lean` | facade with `## Contents`; exported from `TCSlib.lean` | |

`truthAux_exSuffix_iff` generalizes `truth_exPrefix_iff_satisfiable` (`Formulas/QBF.lean:166`)
to a start index and subsumes its private helpers Q1–Q3 (`:108`, `:119`, `:136`); putting it in
`QBF.lean` avoids a copy. Namespaces: `Complexity.FormulaKit`, `Complexity.QBF`, and
`BoolCircuit.DAGCircuit` for the circuit lemma (`BoolCircuit` is the registered root-level
model namespace). A name screen over `TCSlib/` found no existing `FormulaKit`, `ConfigCodec`,
`PrefixTruth`, `blockVar`, `exactlyOne`, `template`, `GroupFamily` or `exSuffix` (grep,
2026-10-12).

### 3.2 Signatures (as in the draft, §1–§3)

```lean
namespace Complexity.FormulaKit
def blockVar (base width t i : ℕ) : ℕ := base + t * width + i
def bitsOf (ℓ r : ℕ) : Fin ℓ → Bool := fun i => r.testBit i.val
def excludeClause (ℓ : ℕ) (v : Fin ℓ → Bool) : CNF.Clause ℕ := List.ofFn fun i => (i.val, !v i)
def template (ℓ : ℕ) (p : (Fin ℓ → Bool) → Bool) : CNF ℕ :=
  (List.range (2 ^ ℓ)).filterMap fun r =>
    if p (bitsOf ℓ r) then none else some (excludeClause ℓ (bitsOf ℓ r))
theorem template_eval (ℓ p a) : (template ℓ p).eval a = p (fun i => a i.val)
theorem template_numVars_le / template_length_le (≤ 2 ^ ℓ) / template_widthAtMost
def gate (ℓ p) (wire : ℕ → ℕ) : CNF ℕ := (template ℓ p).relabel wire
theorem gate_eval : (gate ℓ p wire).eval a = p (fun i => a (wire i.val))      -- proved
def exactlyOne (vs : List ℕ) : CNF ℕ
theorem exactlyOne_eval : (exactlyOne vs).eval a = true ↔ ∃ j ∈ vs, ∀ v ∈ vs, a v = decide (v = j)
def cost (φ : CNF ℕ) : ℕ := (φ.map fun C => C.length + 1).sum
theorem serialize_length_le (h : ∀ C ∈ φ, ∀ l ∈ C, l.1 < N) :
    (CNF.serialize φ).length ≤ cost φ * (N + 3) + 1
theorem numVars_le_of_forall_lt (h : ∀ C ∈ φ, ∀ l ∈ C, l.1 < N) : φ.numVars ≤ N
theorem gate_cost_le : cost (gate ℓ p wire) ≤ 2 ^ ℓ * (ℓ + 1)
theorem exactlyOne_cost_le : cost (exactlyOne vs) ≤ vs.length + 1 + 3 * vs.length ^ 2

def fragment (φ : CNF ℕ) : List Bool := φ.flatMap fun C => true :: CNF.serializeClause C
theorem serialize_eq_fragment : CNF.serialize φ = fragment φ ++ [false]          -- rfl
theorem fragment_append / fragment_flatMap                                        -- proved
theorem polyTimeComputable_flatMap_range (count : List Bool → ℕ) (chunk : List Bool → ℕ → List Bool)
    (hcount : PolyTimeComputable fun x => List.replicate (count x) true)
    (hchunk : PolyTimeComputable fun z => chunk (pairFstD z) (pairSndD z).length) :
    PolyTimeComputable fun x => (List.range (count x)).flatMap (chunk x)
theorem polyTimeComputable_serialize_flatMap (count) (G : List Bool → ℕ → CNF ℕ) (hcount)
    (hG : PolyTimeComputable fun z => fragment (G (pairFstD z) (pairSndD z).length)) :
    PolyTimeComputable fun x => CNF.serialize ((List.range (count x)).flatMap (G x))
theorem polyTimeComputable_fragment_gate (ℓ p) (wire : List Bool → ℕ → ℕ)
    (hw : ∀ j < ℓ, PolyTimeComputable fun z => List.replicate (wire z j) true) :
    PolyTimeComputable fun z => fragment (gate ℓ p (wire z))
theorem polyTimeComputable_serialize_relabel_add (F : List Bool → CNF ℕ) (o : List Bool → ℕ)
    (hF : PolyTimeComputable fun x => CNF.serialize (F x))
    (ho : PolyTimeComputable fun x => List.replicate (o x) true) :
    PolyTimeComputable fun x => CNF.serialize ((F x).relabel (o x + ·))
```

Design points:

- **Explicit templates.** `template` replaces `Classical.choose (exists_cnf_boolFun …)`
  (`clTemplate`, `codecLocalCheck`) by the truth table in the order `r = 0 … 2^ℓ - 1`. It is
  the same construction as the private `falsifyingCNF` (`Formulas/CNF.lean:177`), with the
  `Finset.univ` order replaced by `List.range`. The semantic lemma is all a consumer uses;
  the explicit list is what an emitter is compared against.
- **The emission theorem is the PolyTimeComputable-level host.** `polyTimeComputable_emitIter`
  (`ClassNP/PolyTimeBlockLoop.lean:315`) is already the public emitting loop, "built on
  `Turing.FinTM.exists_emitLoopTM`" (module docstring, `:46`; proof sketch, `:306`);
  `flatMap_range` adds the saturating index state and the polynomial count, which every formula emitter needs. This
  is H6's "ordered emission by `exists_emitLoopTM`" (`machine-library-design.md:3056`), with
  the round index passed as `pairEncode x 1ⁱ`.
- **Offsets by a transducer**, not by re-deriving each family at each offset:
  `serialize_relabel_add` shifts any polynomial-time serialization. The `ψ` emitter places
  each codec CNF at a block offset with it.
- **Cook–Levin keeps its precomputation.** `flatMap_range` recomputes per round; that is
  polynomial for Cook–Levin too (each group is polynomial-time from `(x, i)`, rerunning the
  reference simulation), but Cook–Levin's existing packed-record route is faster and proved.
  Re-basing Cook–Levin on the kit is a later restyling row, not part of RD-2.

### 3.3 What each consumer instantiates

| Kit item | Cook–Levin (`Hardness.lean`) | Codec (`ConfigCodec`) | `ψ` emitter (`TQBF_PSPACEHard`) |
|---|---|---|---|
| `blockVar` | `clPack m B t i` (`:185`), exactly | source block `0`, target block `width` | level blocks `blockVar 0 W t j` (§7.2) |
| `template`, `gate` | `clGroup` has the shape `gate (2B+1) (clPredicate M code κ) (clWire m B src tgt p)`, with `clTemplate` for `template`; kinds `CLTemplateKind k` | `transitionGate` = `gate (3k+7) (kindPred κ …) (portWire …)`, kinds `GateKind M` | — |
| `exactlyOne` | — (binary field codes) | the one-hot head, state and work-head tracks | — |
| `cost`, `serialize_length_le`, `numVars_le_of_forall_lt` | the output-length ledger | the size theorem and `numVars` bounds | the size of `ψ`, if a ledger is wanted |
| `fragment`, `serialize_flatMap` | `clFragment`, `clChunk`, `clEmitter_of_body` | the four uniformity theorems | the matrix emission |
| `fragment_gate` | `clA5Template_native`, `clA5Group_native` | adjacency's uniformity | — |
| `serialize_relabel_add` | — | — | the codec CNFs at block offsets |
| `truth_exSuffix_of_pointwise` | — | — | Tseitin after the prefix |

---

## 4. The restated public surface (`ConfigCodec`)

All in `namespace Complexity.ConfigCodec` (draft: `Complexity.Draft.RD2.ConfigCodec`),
`variable (M : FinTM Bool)`.

### 4.1 The closed-form layout

`k = M.k`, `Q = stateCount M = card M.State + 1`, window cells `j < 2s + 1` stand for
positions `j - s`.

| Field | Variable | Meaning |
|---|---|---|
| input content | `inputVar i = i`, `i < n` | input bit `i` |
| input head | `headVar n j = n + j`, `j < n + 2` | input head at `j` (`0`, `n + 1` are the end markers) |
| state | `stateVar M n q = 2n + 2 + stateIndex M q` | state is `q` (`stateIndex none = 0`) |
| work cells | `workVar M n s i j b = 2n + 2 + Q + 3((2s+1)i + j) + b` | tape `i`, cell `j`: `b = 0` holds `false`, `1` holds `true`, `2` head here |
| summary | `summaryVar M n s d = 2n + 2 + Q + 3k(2s+1) + [d]` | `d = false`: output `[true]`; `d = true`: output dead |
| width | `width M n s = 2n + 4 + Q + 3k(2s + 1)` | no padding |

This is the field order of the present `CodecBit` (`TQBF.lean:142–147`) and of the marker
encoding `codecRowBits` (`:174–183`); only the numbering becomes explicit. Head flags use
exact integer positions (`decide (c.workTapePos i = j - s)`), as `codecObserve` does
(`:1145–1151`), so the code is total and its reads hold for every configuration.

### 4.2 Definitions

```lean
def stateCount : ℕ := Fintype.card M.State + 1
noncomputable def stateIndex : Option M.State → ℕ                 -- machine-constant
def stateOffset (n) : ℕ := 2 * n + 2
def workOffset (n) : ℕ := stateOffset n + stateCount M
def summaryOffset (n s) : ℕ := workOffset M n + 3 * (M.k * (2 * s + 1))
def width (n s) : ℕ := summaryOffset M n s + 2
def inputVar (i) / headVar (n j) / stateVar (n q) / workVar (n s i j b) / summaryVar (n s dead)
def workFlags (s) (c) (i : Fin M.k) (j : ℕ) : List Bool            -- the three cell flags
noncomputable def code (n s : ℕ) (x : List Bool) (c : Cfg M.k Bool M.State x) : List Bool
def validity (n s : ℕ) : CNF ℕ                                    -- computable
def acceptance (n s : ℕ) : CNF ℕ := [[(stateOffset n, true)], [(summaryVar M n s false, true)]]
def inputEquality (n s : ℕ) : CNF ℕ
abbrev Case := Option M.State × Option Bool × (Fin M.k → Option Bool)
def caseAction (q : Case M) : Action M.k Bool M.State
noncomputable def caseList : List (Case M)                        -- machine-constant
inductive Port (k : ℕ) | state | inputHead | inputSymbol | workHead (i) | workSymbol (i t)
  | summary (t) | oldBit | newBit
def portCount (k) : ℕ := 3 * k + 7
def portIndex : Port k → ℕ ;  def portOf (k j : ℕ) : Port k       -- closed form, inverse
inductive Expect | copy | const (b : Bool) | summary (dead : Bool)
abbrev GateKind := Case M × Bool × Expect                          -- finite, machine-only
def guard (q) (interior : Bool) (a : Port M.k → Bool) : Bool
def expectBit (act) : Expect → (Port M.k → Bool) → Bool
def kindPred (κ : GateKind M) (a : Port M.k → Bool) : Bool
def headOf (s h i : ℕ) : ℕ := h / (2 * s + 1) ^ i % (2 * s + 1)  -- mixed radix head tuple
def moveInput (n p : ℕ) (m : SignType) : ℕ                         -- moveInputPos on ℕ
noncomputable def expectOf (n s p h : ℕ) (q : Case M) (v : ℕ) : Expect
noncomputable def portWire (n s p h : ℕ) (q : Case M) (v : ℕ) : Port M.k → ℕ
noncomputable def transitionGate (n s p h) (q) (v) : CNF ℕ :=
  FormulaKit.gate (portCount M.k)
    (fun a => kindPred M (q, decide (0 < p ∧ p ≤ n), expectOf M n s p h q v)
      (fun port => FormulaKit.readBit a (portIndex port)))
    (fun j => portWire M n s p h q v (portOf M.k j))
noncomputable def transition (n s : ℕ) : CNF ℕ :=
  (List.range (n + 2)).flatMap fun p => (List.range ((2 * s + 1) ^ M.k)).flatMap fun h =>
    (caseList M).flatMap fun q => (List.range (width M n s)).flatMap fun v =>
      transitionGate M n s p h q v
noncomputable def adjacency (n s : ℕ) : CNF ℕ := inputEquality M n s ++ transition M n s
```

`Port`, `readSymbol`, `readSummary`, `summaryWord`, `guard`, `expectBit` and `caseAction`
are the present `CodecPort`, `codecReadSymbol`, `codecReadSummary`, `codecSummaryWord`,
`codecGuard`, `codecExpected` and `codecAction` (`:1251–1416`), made public with three
changes: ports are indexed by `k` rather than `M`; the guard is a `Bool`; and the expected
bit is factored through a finite **kind** `Expect`, computed by `expectOf` from the
coordinate's field. That factoring is what removes A6: the old gate's Boolean function
depends on `(p, b)` only through the case, the interior flag of `p`, and `Expect`, so one
template per kind serves every position.

### 4.3 Theorems: the old clauses, one by one

| Old clause (`TQBF.lean:1748–1777`) | New theorem | Change |
|---|---|---|
| length `= C·(s+n+1)` for all `x, c` | `code_length : (code M n s x c).length = width M n s` | closed-form width, no padding; `width_eq`, `width_le : width ≤ (card + 6k + 5)(s+n+1)` |
| input separation (windowed) | `code_input_eq` | the window hypotheses are dropped (not needed) |
| code eq ↔ `coreSum` eq | `code_eq_iff` | none |
| `φv` ↔ codec image | `validity_eval_iff` (`w.length = width`) | none besides the width |
| `φa` ↔ step on the quotient | `adjacency_eval_iff` | none |
| `φa` rejects distinct inputs | `adjacency_eval_of_ne` | window hypotheses dropped |
| `φacc` ↔ halted ∧ accept | `acceptance_eval_iff` | length and window hypotheses dropped |
| `numVars` bounds (three) | `validity_numVars_le`, `acceptance_numVars_le`, `adjacency_numVars_le` | none |
| serialized lengths `≤ C·(s+n+2)^C` | `exists_serialize_length_le : ∃ K, ∀ n s, … ≤ K·(s+n+2)^K` (three) | the constant is separate from the width |
| (absent) | `code_getD_inputVar/headVar/stateVar/workVar/summaryVar` | **new**: the closed-form indexing contract |
| (absent; a private fill obligation of the summit, `:2614–2623`) | `polyTimeComputable_serialize_validity/adjacency/acceptance (s o …)` and `polyTimeComputable_code_initCfg (s …)` | **new**: uniformity |

The uniformity statements, verbatim from the draft:

```lean
theorem polyTimeComputable_serialize_validity (s o : List Bool → ℕ)
    (hs : PolyTimeComputable fun x => List.replicate (s x) true)
    (ho : PolyTimeComputable fun x => List.replicate (o x) true) :
    PolyTimeComputable fun x =>
      CNF.serialize ((validity M x.length (s x)).relabel (o x + ·))
-- likewise for adjacency (both blocks shift by `o x`) and acceptance
theorem polyTimeComputable_code_initCfg (s : List Bool → ℕ)
    (hs : PolyTimeComputable fun x => List.replicate (s x) true) :
    PolyTimeComputable fun x => code M x.length (s x) x (M.tm.initCfg x)
```

The repaired properties of the P4.3 gate rounds are all kept: no full-output injectivity
(round-1 finding 1, `TQBF.lean:32–34`); validity guards midpoints (finding 3); halted
vertices self-adjacent, live ones not necessarily (round-2 finding 3); the input carried in
the code (finding 7); serialized-length size bounds at base `s + n + 2` (finding 8, round-2
finding 1); polynomial, per-gate universality (round-2 finding 4).

### 4.4 The old existential, if kept

The draft proves, from the theorems above, `exists_adjacency_codec_cnf_of_closedForm`: the
old statement with its length clause replaced by "a width `ℓ ≤ C·(s+n+1)` and exact length
`ℓ`" (the proof is a 25-line term, elaborated; it is the "one-line corollary" in substance:
`⟨C, hC, fun n s => ⟨width M n s, code M n s, validity M n s, adjacency M n s, acceptance M n s,
…theorems…⟩⟩` with `C = max (card + 6k + 5) K`). Recovering the old statement byte for byte
would need padding to `C·(s+n+1)` and a shifted target block, about 100–150 lines
(estimate) for a statement with no consumer. Recommendation in §9, Q1.

---

## 5. Tseitin after the prefix

### 5.1 Existing material (surveyed)

| Where | What | Fit |
|---|---|---|
| `CircuitComplexity/DAGCircuitSat.lean` (Hydroxyi) | `DAGGate.tseitin` (`:134`), `eval_tseitin` (`:160`), `tseitinGates` (`:211`), `eval_tseitinGates` (`:216`), `DAGCircuit.toCNF` on `Std.Sat.CNF ℕ` with vertex `v` = variable `v` (`:267`), `toCNF_var_lt_size` (`:296`); privates `eval_tseitinGates_values` (`:312`) and `values_getD_eq_of_eval_tseitinGates` (`:322`); public `satisfiable_iff_toCNF_satisfiable` (`:354`) | **closed-form numbering already** (inputs `0…n-1`, gate `i` at `n+i`); fan-in `≤ 2`; only the existential closure is public, the per-assignment content is in the two privates |
| `CircuitComplexity/CircuitSatReduction*.lean` (Hydroxyi) | the proved polynomial-time Tseitin emitter: `polyTimeComputable_gateClauses` (`CircuitSatReduction.lean:89`), `gateClauses_encode … = CNF.serialize (tseitinGates n C.gates)` (`CircuitSatReductionSpec.lean:337`), decomposition `dagCktSatToSAT3_eq` (`CircuitSatReduction.lean:101`) | reusable if a consumer emits circuit descriptions |
| `CircuitComplexity/DAGFanin.lean` (Hydroxyi) | `DAGCircuit.binarize` (`:347`), `binarize_eval` (`:357`), `binarize_isFaninTwo` (`:362`) | turns wide gates into fan-in two |
| `CircuitComplexity/CircuitSat.lean` (Yichuan Wang) | `TreeCircuit.tseitin` (`:126`), wide fan-in | different carrier (`CNFFormula (CktVar n)`, `NPReductions/SATTo3SAT.lean:75`), variables indexed by subtrees: not closed form |
| Lean core `Std.Sat.AIG` (toolchain v4.25.0, `src/lean/Std/Sat/AIG/CNF.lean`) | `AIG.toCNF` with `toCNF_equisat` (`:674`, `Unsat ↔ Unsat` only) | atoms are renumbered after the gates (`inj`, `:557–560`), clause order follows a cached DFS, and the per-assignment facts (`go_sat`, `denote_as_go`) are private: examined for comparison, nothing taken |
| Mathlib, other packages | no Tseitin material (grep of `.lake/packages`) | — |

### 5.2 Statement

Two layers, so that the prefix argument is proved once for every encoding:

```lean
namespace Complexity.QBF
def PrefixTruth (P : (ℕ → Bool) → Prop) : List Quant → (ℕ → Bool) → ℕ → Prop  -- truthAux's recursion
theorem truthAux_iff_prefixTruth (m qs σ i) :
    truthAux m qs σ i ↔ PrefixTruth (fun τ => m.eval τ = true) qs σ i          -- proved
theorem prefixTruth_congr (h : ∀ τ, P τ ↔ P' τ) : PrefixTruth P qs σ i ↔ PrefixTruth P' qs σ i  -- proved
theorem prefixTruth_append : PrefixTruth P (qs ++ rs) σ i ↔
    PrefixTruth (fun τ => PrefixTruth P rs τ (i + qs.length)) qs σ i          -- proved
theorem truthAux_exSuffix_iff (m j σ i) (hm : m.numVars ≤ i + j) :
    truthAux m (List.replicate j .ex) σ i ↔ ∃ τ, (∀ v < i, τ v = σ v) ∧ m.eval τ = true
/-- Tseitin after the prefix, for any encoding. -/
theorem truth_exSuffix_of_pointwise (qs : List Quant) (T : CNF ℕ) (G : ℕ)
    (P : (ℕ → Bool) → Prop) (hT : T.numVars ≤ qs.length + G)
    (hpt : ∀ σ, (∃ τ, (∀ v < qs.length, τ v = σ v) ∧ T.eval τ = true) ↔ P σ) :
    truth ⟨qs ++ List.replicate G .ex, T⟩ ↔ PrefixTruth P qs (fun _ => false) 0   -- proved from the above
end Complexity.QBF

theorem BoolCircuit.DAGCircuit.exists_toCNF_extension_iff (C : DAGCircuit n)
    (hC : ∀ g ∈ C.gates, g.args.length ≤ 2) (σ : ℕ → Bool) :
    (∃ τ, (∀ v < n, τ v = σ v) ∧ C.toCNF.eval τ = true) ↔ C.eval (fun i => σ i) = true
theorem Complexity.QBF.truth_tseitin_after_prefix (qs) (C : DAGCircuit qs.length) (hC) :
    truth ⟨qs ++ List.replicate C.gates.length .ex, C.toCNF⟩ ↔
      PrefixTruth (fun σ => C.eval (fun i => σ i) = true) qs (fun _ => false) 0  -- proved from the above
```

"Correct for every prefix assignment" is exactly the hypothesis `hpt`: the gate variables
sit after the whole prefix, so their values may depend on every universal variable. In the
draft, `truth_exSuffix_of_pointwise` and `truth_tseitin_after_prefix` have real proofs (from
the sorried `truthAux_exSuffix_iff` and `exists_toCNF_extension_iff`); the remaining fills are
about 40 lines (the suffix lemma, after Q1/Q3) and about 30 lines (the pointwise lemma, if the
two privates of `DAGCircuitSat.lean` are made public), both estimates.

---

## 6. What changes, where

### 6.1 Consumers of the old statement (grep of the whole worktree, `.lake` excluded)

- **Lean proofs: none.** `exists_adjacency_codec_cnf` is used by no proof; its only consumer
  is the open, sorried `TQBF_PSPACEHard` (`TQBF.lean:2628–2629`), through its docstring.
- **Lean docstrings (live, edited by RD-2):** `TQBF.lean` module docstring (`:24–57` design
  bullet "Claim 4.4(2) … packaged quotient codec … The package is existence, not an
  algorithm"; `:61–75` main lists), the fill appendix header (`:114–130`), the theorem's
  docstring (`:1698–1743`), and `TQBF_PSPACEHard`'s sketch (`:2579–2627`: "over the packaged
  carrier", `ℓ := C·(s+n+1)`, and the fill-obligation list, of which the "three-CNF emitter
  family", the "initial-code computation" and the "Tseitin-after-prefix equivalence" become
  RD-2 and kit theorems). `Build/CfgRecord.lean:95` (the `Cfg.InWindow` docstring names the
  packaged codec).
- **Blueprint, `docs/`, `dataset/`, `proofmatch/`, `site_root/`, `webpage/`, `scripts/`,
  `tests/`: no occurrence.** There is no blueprint chapter for `ClassPSPACE`.
- **Live records (maintainer edits):** `machine-library-design.md:3056` (H6 row) and
  `:3641` (§16b item 2), `backlog.md:630–635` (RD-2), `AroraBarakChapters3-4Plan.md:832`
  (the B4 row).
- **Historical records (no edits):** the audits and briefs that name it (P4.3 gate rounds,
  `briefs/b4a-fill-codec.md`, the S128 and C1 briefs). `briefs/ch34-b4-mem.md:321` froze
  B4a's statement and privates for B4 membership; that brief stopped at its fills-6 partial
  and its successor MIG-22 waits for stage 2 (`backlog.md:555`), so nothing in flight holds
  the freeze. Any later brief that owns `TQBF.lean` must be sequenced after RD-2's re-fill.

### 6.2 How the existing proof is adapted

1. **Statement phase (PR, then the statement gate).** Add the public surface next to the old
   block: the definitions with bodies and the theorems sorried; the kit files with sorried
   statements; the `QBF.lean` additions; the docstring edits of §6.1. The old existential and
   its 119 privates stay untouched, so no proved statement regresses to `sorry` during the
   gate; the old statement is marked "retired at RD-2's re-fill".
2. **RD-2a, the semantic re-fill (PR, freeze screen).** One private bridge, the code at the
   closed-form index of `b` is `codecRowBits (codecRowOf …) b` on windowed configurations
   (through `codecObserve_eq`); then: `code_eq_iff`, `code_input_eq` from the surviving row
   lemmas; `validity_eval_iff` from `codecBitsValid_iff` and `codecRow_realize` through
   `exactlyOne_eval`; the gate bridge `kindPred (kind p h q v) (ports) = codecGate …` (a case
   split on the field computed by `expectOf`) plus coverage of the explicit enumeration, which
   re-proves `codecTransitionCNF_eval` for the new list, after which
   `codecTransitionCNF_step_iff` and `adjacency_eval_iff` follow unchanged; the ledgers
   re-normalized without padding. The retired declarations of §1.4 are deleted in the same PR,
   with the old theorem (or replaced by the corollary, Q1). The screen checks that the
   ≈ 820 surviving lines are byte-identical.
3. **RD-2b, uniformity (PR).** The four polynomial-time theorems over `FormulaKit/Emit`.
4. **Fill gate** over 2–3, with the replay and the axioms check.

---

## 7. The `ψᵢ` emitter: machine (H6) or program (`emit`)

### 7.1 Trade-offs I can substantiate

**Machine route** (functions built in the `PolyTimeComputable` closure algebra over the H6
kit, the Cook–Levin streaming-emitter style):

- Every prerequisite exists or is a promotion: `polyTimeComputable_const` (`PolyTimePairing.lean:71`),
  `PolyTimeComputable.pairEncode` (`:128`), `.append` (`:185`), `polyTimeComputable_polyUnary`
  (`:194`), `polyTimeComputable_ite` (`:269`), `polyTimeComputable_and` (`:298`),
  `polyTimeComputable_lenLe` (`:309`), `PolyTimeComputable.comp` (`PolyTime.lean:149`),
  `output_length_le` (`:91`), `polyTimeComputable_emitIter` (`PolyTimeBlockLoop.lean:315`), and
  Cook–Levin's template-with-native-wires argument (`Hardness.lean:6996–7041`, private, to be
  promoted as `fragment_gate`). For a circuit-based matrix, also the proved polynomial-time
  Tseitin emitter (§5.1).
- The design already classifies H6 as a machine-level host that "proceed[s] now"
  (`machine-library-design.md:3206–3207`), and Cook–Levin, a TM-intrinsic result, stays at
  machine level (§16 decision 3, `:3485–3487`); one emission kit then serves both.
- A Karp reduction needs only a time bound: no space contract, word size or footprint (the
  obstacles PROG-3 and PROG-4 are about space, `backlog.md:610–628`).
- The `ψ` emitter's indices are closed-form in `(n, s)` (§7.2). Cook–Levin's emitter needed a
  long preparation (`Hardness.lean:607–6155`: simulating the oblivious verifier, trajectory
  and last-visit tables) that has no counterpart here, so the Cook–Levin size is not a guide.
- Cost: proofs by closure composition are verbose; unary arithmetic on indices is no loss,
  since the serialization is unary anyway (`CNFEncoding.lean:99–100`).

**Program route** (a program of the vendored language with a future `emit`):

- Loops over levels, blocks and clauses are natural to write, and the program logic has
  frames.
- `emit` is not in the language yet: it is part of PROG-2 (`backlog.md:594–608`, design
  §15c `:3432–3433`), a statement phase plus a fidelity gate.
- A program yields `PolyTimeComputable` only through stage 2, the RAM-to-`FinTM` simulation
  (PROG-1(d)), estimated at 6,000–10,000 lines and not started (design `:3292–3294`); its
  statement must carry the emitted output (PROG-4, `backlog.md:618–628`).
- The correctness obligation "the emitted word is `CNF.serialize ψ`" is the same in either
  route; in the program route it is stated through `EndsIO`, which is itself new
  (design §15c, `:3418–3421`).

**Recommendation (mine): the machine route**, over the H6 kit and the closure algebra, now.
Revisit only if stage 2 lands before B4 hardness is briefed and the closure proofs turn out
heavier than estimated.

### 7.2 What the hardness proof consumes from RD-2 (consumer view)

With `W = width M n s` and `R = W` levels (at most `2^W` codes, so a shortest path fits):
block `t` occupies `blockVar 0 W t j`; block `0` is the existential target `b`; level `r`
uses `z_r = 3r + 1` (existential), `u_r = 3r + 2`, `v_r = 3r + 3` (universal). Because `u_r`
and `v_r` are adjacent, `adjacency.relabel (blockVar 0 W (3r+2) 0 + ·)` reads them as source
and target with one offset, and `polyTimeComputable_serialize_adjacency` applies directly;
validity at `z_r` and acceptance at `b` likewise. The prefix has `W(3R+1)` variables,
followed by the existential auxiliary variables. The start code is a constant, computed by
`polyTimeComputable_code_initCfg`.

### 7.3 The matrix encoding (for B4 hardness's design)

Both options use `truth_exSuffix_of_pointwise`:

- **T1, circuit plus the existing Tseitin.** Build the prenex matrix as a fan-in-two
  `DAGCircuit` (or wide, then `binarize`), use `truth_tseitin_after_prefix`, and emit a
  circuit description piped through `gateClauses`. Reuses the most proved material, but the
  circuit's gate numbering is a running sum, and its semantics goes through `runWith`
  (`DAGCircuit.lean:136–215`).
- **T2, a guarded CNF.** One existential guard `g_r` per level and existential disequality
  witnesses for the selectors; the codec CNFs enter as their clauses at block offsets with
  the guard literal prepended. Emission stays at the CNF level (one more transducer in the
  style of `serialize_relabel_add`); the pointwise lemma is specific to this shape.

My tentative lean is **T2**: fewer new components and no circuit bookkeeping. If T2 is
chosen, `exists_toCNF_extension_iff` and `truth_tseitin_after_prefix` have no named consumer
and should not be admitted yet (the two-customer rule of admission, design §4, as applied
at `:801`); the draft states them so that the gate can see the circuit instance.

---

## 8. Size estimate and gates

Estimates (lines of Lean), except where marked MEASURED. The statement layer is the draft
moved into place; the other rows are proofs.

| Item | Lines | Notes |
|---|---|---|
| Statement layer (kit, `QBF.lean` additions, `ConfigCodec`) | ≈ 940 | MEASURED in the draft (944 lines, ≈ 470 of them the `ConfigCodec` section with its layout table); 47 theorems, 11 of them already proved, 36 sorried; 48 definitions with bodies |
| Proofs, `FormulaKit/Gate.lean` | 250–350 | ≈ 170 moved from `TQBF.lean`'s privates (cost ledger, one-hot, serialization bound); the explicit truth table's lemmas ≈ 120 |
| Proofs, `FormulaKit/Emit.lean` | 250–500 | `flatMap_range` over `emitIter` 150–250; `fragment_gate` ≈ 80 (after `Hardness.lean:6996–7041`); the offset transducer 100–200 |
| Proofs, `Formulas/QBF.lean` additions | 40–80 | only `truthAux_exSuffix_iff` is open; it subsumes Q1–Q3 |
| Proofs, circuit Tseitin instance | 30–60 | only with T1 (Q3); ≈ 30 if the two privates are made public |
| RD-2a, semantic re-fill in `TQBF.lean` | 500–800 | bridges and rewritten ledgers; ≈ 820 lines survive verbatim and ≈ 185 are retired (counted, §1.4) |
| RD-2b, uniformity | 400–800 | validity, acceptance and the initial code ≈ 250; adjacency 300–500 |
| Docstrings (§6.1) | ≈ 100 | |
| **Total landed** | **≈ 2,500–3,600** | against ≈ 850 lines of the old block retired, moved or rewritten; net growth of the tree ≈ 1,700–2,800 |

Gates, each a PR the user merges:

1. **Statement gate (RD-2-S)**, a full gate: it changes an audited public statement (§16
   decision 2, "Each retired or changed statement needs a full statement gate",
   `machine-library-design.md:3479–3483`). The pack needs the draft, the old statement, this
   note, the P4.3 findings whose repairs §4.3 keeps (`audits/ch4-p43-findings.md`,
   `audits/ch4-p43-r2-findings.md`), and the standards (`audits/TEMPLATE.md`,
   `policy.md`, `workflow.md`).
2. **RD-2a re-fill** with the kit's `Gate` and the `QBF.lean` additions (different files, so
   in parallel), under the survival screen, a replay and the axioms check.
3. **RD-2b** with the kit's `Emit`.
4. **Fill gate** over 2–3, which also retires (or replaces) the old existential.

---

## 9. Open questions (each with a recommendation)

1. **Retire `exists_adjacency_codec_cnf` or keep a corollary?** It has no proof consumer and no
   blueprint entry. *Recommendation:* retire it at the re-fill; keep
   `exists_adjacency_codec_cnf_of_closedForm` only if a stable packaged form is wanted, under
   the old name, with the width clause `ℓ ≤ C·(s+n+1)`.
2. **Are the four uniformity theorems part of RD-2, or of B4 hardness?** *Recommendation:* part of
   RD-2 (as RD-2b). They are the reason for the restatement, and gating them with the
   definitions fixes the contract the emitter relies on.
3. **The `ψ` matrix encoding: T1 (circuit) or T2 (guarded CNF)?** Decided with B4 hardness's
   design. *Recommendation (tentative):* T2, admitting only the generic
   `truth_exSuffix_of_pointwise` now. If T1 is chosen, make the two privates of
   `DAGCircuitSat.lean` (`:312`, `:322`) public by a PR to that colleague-owned file rather than
   copying them; a copy would be disclosed duplication needing your approval (`policy.md` §1).
4. **The emitter: machine or program?** *Recommendation:* machine (§7.1).
5. **Transition gates: truth-table templates per kind, or explicit guarded clauses?** Explicit
   clauses ("guard literals ∨ (new = expected)", at most four clauses per gate instead of up to
   `2^(3k+7)`) give much smaller formulas, but need a new semantic proof per gate shape.
   *Recommendation:* templates. They keep the old proof's per-gate argument, share the kit with
   Cook–Levin, and the size stays polynomial for the fixed machine, with the same per-gate bound
   as today (`codecGate_cnf`, `TQBF.lean:1502`).
