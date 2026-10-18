/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.QBFEncoding
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.SpaceComplexity.Inclusions
import TCSlib.Complexity.TuringMachine.Build.CfgRecord
import TCSlib.Complexity.FormulaKit.Gate
import TCSlib.Complexity.FormulaKit.Emit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `PSPACE`-completeness and `TQBF`

[AB09, §4.2]: `PSPACE`-hardness and -completeness (Definition 4.9), the
adjacency-formula half of Claim 4.4(2), and the Stockmeyer-Meyer theorem that
`TQBF` is `PSPACE`-complete (Theorem 4.13). Phase P4.3 of
`AroraBarakChapters3-4Plan.md`.

## Design

* **Def 4.9 verbatim over the campaign's `≤ₚ`** (`Complexity.PolyTimeReducible`,
  chapter 2); the logspace-reduction variant ([AB09, Exercise 4.9]) waits for
  phase P4.4's `≤ₗ`.
* **Claim 4.4(2) at polynomial size, over the closed-form codec `Complexity.ConfigCodec`**
  (restated by RD-2, user decision of 2026-10-12, `machine-library-design.md` §16b item 2;
  the packaged existential `Complexity.exists_adjacency_codec_cnf` is retired at the RD-2a
  re-fill). For each machine and each `(n, s)`: a configuration bit-codec
  `ConfigCodec.code` of width `ConfigCodec.width M n s = 2n + 4 + Q + 3k(2s + 1)`, linear
  in `s + n`, every field at a closed-form index, **factoring through the input
  and the P4.2 vertex quotient** `Turing.NDTM.coreSum` — full configurations
  are *not* injectively codable at fixed length, the output tape being
  unbounded (round-1 blocker, finding 1) — together with **three** CNFs over
  the code bits, each an explicit clause list ordered by `List.range` and built from the
  truth-table gates of `Complexity.FormulaKit` (design §14 row H6): a validity predicate
  characterizing exactly the codec image (unguarded midpoint quantification admits paths
  through junk codes — round-1 finding 3), the adjacency test (true on same-input windowed
  pairs iff the step descends to the vertex quotient; false across distinct
  inputs), and the acceptance test (halted state with `accept` summary).
  Declared deviations from the book's Claim 4.4(2), each argued harmless to
  Theorem 4.13: (i) the codec length is `O(s + n)` rather than `O(s)` — the
  code carries the **input content** and a one-hot input-position track, so
  every check is *local* and the formulas are input-independent (Cook-Levin's
  marker discipline; round-1 finding 7); (ii) the CNF sizes are bounded
  through their **serialized lengths** — polynomial, not linear; a
  literal-occurrence count alone misses empty clauses (round-1 finding 8) —
  at base `s + n + 2`, which gives the description room the code width does
  not (round-2 finding 1);
  (iii) adjacency compares `coreSum (step c)` with `coreSum d`, so halted
  vertices are self-adjacent while live ones **need not** be (a stationary
  silent live loop is — round-2 finding 3); the ψ-recursion's base case
  supplies `a = b` separately (round-1 finding 6). **Uniformity** (new with RD-2; round-1
  major 2 recorded that the packaged existential supplied no algorithm): the three CNFs at
  any polynomial-time input length, radius and variable offset, and the initial vertex's
  code, are polynomial-time computable (`ConfigCodec.polyTimeComputable_serialize_validity`
  and its siblings). Two choices depend on the machine only — the state numbering
  `ConfigCodec.stateIndex` and the case list `ConfigCodec.caseList` — as Cook-Levin's field
  codes do. Sole consumer unchanged (`Complexity.TQBF_PSPACEHard`); D6-style promotion
  recorded for a second consumer (the phase-P4.4 `PATH` encoding remains the candidate).
* **The facade discipline**: `ClassPSPACE.lean` is this phase's own new
  facade; nothing frozen is touched.

## Main definitions

* `Complexity.PSPACEHard`, `Complexity.PSPACEComplete` — [AB09, Definition 4.9].
* `Complexity.ConfigCodec.code`, `Complexity.ConfigCodec.width` and the field indices
  `inputVar`, `headVar`, `stateVar`, `workVar`, `summaryVar` — the configuration codec of
  [AB09, Claim 4.4], in closed form.
* `Complexity.ConfigCodec.validity`, `Complexity.ConfigCodec.adjacency`,
  `Complexity.ConfigCodec.acceptance` — its three CNFs. [AB09, Claim 4.4(2)]
* `Complexity.TQBF` — the true quantified Boolean formulas, over
  `Complexity.QBF.decode`. [AB09, §4.2, before Theorem 4.13]

## Main results

* `Complexity.PSPACE_eq_P_of_pspaceComplete_mem_P` — a `PSPACE`-complete
  language in `P` collapses `PSPACE` to `P`. [AB09, §4.2, after Definition 4.9]
* `Complexity.ConfigCodec.code_eq_iff`, `Complexity.ConfigCodec.validity_eval_iff`,
  `Complexity.ConfigCodec.adjacency_eval_iff`, `Complexity.ConfigCodec.acceptance_eval_iff`
  and their siblings — Claim 4.4(2), clause by clause (sorried until the RD-2a re-fill).
* `Complexity.ConfigCodec.polyTimeComputable_serialize_validity` and its adjacency,
  acceptance and initial-code siblings — the uniform emitters (sorried until RD-2b).
* `Complexity.exists_adjacency_codec_cnf` — Claim 4.4(2), packaged quotient form; retired at
  the RD-2a re-fill (no proof uses it).
* `Complexity.TQBF_mem_PSPACE` — [AB09, Theorem 4.13, membership half].
* `Complexity.TQBF_PSPACEHard` — [AB09, Theorem 4.13, hardness half]; a fill
  summit (the `ψᵢ` emitter).
* `Complexity.TQBF_PSPACEComplete` — [AB09, Theorem 4.13].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Definition 4.9, Claim 4.4,
  Theorem 4.13; Claim 2.13, p. 46, for the gate templates.)
* [SM73] L. Stockmeyer, A. Meyer, *Word problems requiring exponential time*,
  STOC 1973. (Cited through [AB09]; no external text required.)
-/

namespace Complexity

open Std.Sat (CNF)
open Turing

/-- **`PSPACE`-hardness** [AB09, Definition 4.9]: every `PSPACE` language
Karp-reduces to `L'` in polynomial time. (The logspace variant is phase
P4.4's.) -/
def PSPACEHard (L' : Language Bool) : Prop :=
  ∀ L ∈ PSPACE, L ≤ₚ L'

/-- **`PSPACE`-completeness** [AB09, Definition 4.9]: `PSPACE`-hard and in
`PSPACE`. -/
def PSPACEComplete (L' : Language Bool) : Prop :=
  L' ∈ PSPACE ∧ PSPACEHard L'

/-- **A `PSPACE`-complete language in `P` collapses the class**
([AB09, §4.2, the paragraph after Definition 4.9]; proved, citing `P_subset_PSPACE`):
if some `PSPACE`-complete `L'` lies in `P`, then `PSPACE = P`.

**Proof sketch.** `⊇` is `Complexity.P_subset_PSPACE` (phase P4.1). `⊆`: a
`PSPACE` member reduces to `L'` (hardness), and `P` is closed downward under
`≤ₚ` (`Complexity.mem_P_of_polyTimeReducible`, chapter 2). -/
theorem PSPACE_eq_P_of_pspaceComplete_mem_P {L' : Language Bool}
    (h : PSPACEComplete L') (hP : L' ∈ P) : PSPACE = P := by
  exact Set.Subset.antisymm
    (fun L hL => mem_P_of_polyTimeReducible (h.2 L hL) hP) P_subset_PSPACE

/-! ### Claim 4.4(2): the closed-form configuration codec (definitions)

Restated by RD-2 (design §16b item 2): the codec and its three CNFs are public definitions
with closed-form variable indexing, built from the gates of `Complexity.FormulaKit`; the
theorems about them follow the fill appendix below. Layout of a code word of `width M n s`
bits, for input length `n` and window radius `s` (`k = M.k`, `Q = card M.State + 1`, window
cell `j < 2s + 1` stands for work position `j - s`):

| field | variables | meaning |
|---|---|---|
| input content | `i` for `i < n` | input bit `i` |
| input head | `n + j` for `j < n + 2` | the input head is at `j` (`0`, `n + 1`: end markers) |
| state | `2n + 2 + r` for `r < Q` | the state has index `r` (`0` is the halting state) |
| work cells | `2n + 2 + Q + 3((2s+1)i + j) + b` | tape `i`, cell `j`, flag `b < 3` (below) |
| summary | `2n + 2 + Q + 3k(2s+1) + d` | `d = 0`: output `[true]`; `d = 1`: output dead |

The flags of a work cell are `b = 0` "holds `false`", `b = 1` "holds `true`" and `b = 2` "the
head is here". This is the field order of the finite row `CodecRow` of the fill appendix;
only the numbering is new. Adjacency reads two blocks: the source code at `[0, width)` and
the target code at `[width, 2 · width)`. Two choices depend on the machine only and are fixed
once for it, as in Cook-Levin's field codes: the state numbering `stateIndex` and the case
list `caseList`. -/

namespace ConfigCodec

variable (M : FinTM Bool)

/-- The number of state markers: one per state of `M` and one for the halting state. -/
def stateCount : ℕ := Fintype.card M.State + 1

/-- **The machine-constant state numbering**: the halting state is `0`, and state `q` is one
more than its position in a fixed enumeration of the finite state type
(`Fintype.equivFin M.State`). The choice depends on the machine only, not on `n` or `s`, so an
emitter for the fixed machine stores it as a finite table. -/
noncomputable def stateIndex : Option M.State → ℕ
  | none => 0
  | some q => (Fintype.equivFin M.State q).val + 1

/-- The first state-marker variable, after the `n` input bits and the `n + 2` input-head
markers. -/
def stateOffset (n : ℕ) : ℕ := 2 * n + 2

/-- The first work-track variable, after the state markers. -/
def workOffset (n : ℕ) : ℕ := stateOffset n + stateCount M

/-- The first summary variable, after the `3 · k · (2s + 1)` work-track variables. -/
def summaryOffset (n s : ℕ) : ℕ := workOffset M n + 3 * (M.k * (2 * s + 1))

/-- **The code width** `2n + 4 + Q + 3k(2s + 1)`, linear in `s + n` for the fixed machine
([AB09, Claim 4.4(2)]; deviation (i) of the module docstring: the code carries the input, so
the width is `O(s + n)` rather than `O(s)`). Unlike the retired packaged statement, there is
no padding to `C · (s + n + 1)`. -/
def width (n s : ℕ) : ℕ := summaryOffset M n s + 2

/-- The variable of input bit `i`, namely `i`. -/
def inputVar (i : ℕ) : ℕ := i

/-- The variable of the input-head marker at position `j`, namely `n + j` (`j = 0` and
`j = n + 1` are the end markers). -/
def headVar (n j : ℕ) : ℕ := n + j

/-- The variable of the marker of state `q` (`none` is the halting state):
`stateOffset n + stateIndex M q`. -/
noncomputable def stateVar (n : ℕ) (q : Option M.State) : ℕ := stateOffset n + stateIndex M q

/-- The variable of flag `b` of window cell `j` of work tape `i`:
`workOffset M n + 3 · ((2s + 1) · i + j) + b`. -/
def workVar (n s i j b : ℕ) : ℕ := workOffset M n + 3 * ((2 * s + 1) * i + j) + b

/-- The variable of an output-summary flag: `summaryOffset M n s` for "the output is
`[true]`" (`dead = false`) and the next variable for "the output is dead" (`dead = true`). -/
def summaryVar (n s : ℕ) (dead : Bool) : ℕ := summaryOffset M n s + if dead then 1 else 0

/-- The three flags of window cell `j` (work position `j - s`) of work tape `i` of `c`:
the cell holds `false`; the cell holds `true`; the head of tape `i` is at the cell. Positions
are exact integers, so a head outside the window marks no cell. -/
def workFlags (s : ℕ) {x : List Bool} (c : Cfg M.k Bool M.State x) (i : Fin M.k) (j : ℕ) :
    List Bool :=
  [decide (c.workTapes i ((j : ℤ) - s) = some false),
    decide (c.workTapes i ((j : ℤ) - s) = some true),
    decide (c.workTapePos i = (j : ℤ) - s)]

/-- **The configuration codec** ([AB09, Claim 4.4(2)], with the marker discipline of the
Cook-Levin tableau row): the code of `c` at input length `n` and radius `s` is the
concatenation, in the order of the layout table, of the first `n` input bits, the one-hot
input-head track, the one-hot state track, the three flags of every window cell of every work
tape, and the two output-summary flags. The output tape enters only through
`Turing.outSummary` (a full-output code of fixed length cannot be injective; P4.3 round-1
finding 1). Total on all inputs and configurations; its theorems concern inputs of length `n`
and, where stated, configurations in the radius-`s` window. -/
noncomputable def code (n s : ℕ) (x : List Bool) (c : Cfg M.k Bool M.State x) : List Bool :=
  List.ofFn (fun i : Fin n => x.getD i false) ++
    List.ofFn (fun j : Fin (n + 2) => decide (c.inputPos.val = j.val)) ++
    List.ofFn (fun r : Fin (stateCount M) => decide (stateIndex M c.state = r.val)) ++
    (List.finRange M.k).flatMap (fun i => (List.range (2 * s + 1)).flatMap (workFlags M s c i)) ++
    [decide (outSummary c.output = .accept), decide (outSummary c.output = .dead)]

/-- **The validity CNF** ([AB09, Claim 4.4(2)]; P4.3 round-1 finding 3: the `ψ` recursion
guards its midpoints with it): exactly one input-head marker, exactly one state marker,
exactly one head marker on each work tape, never both symbol flags of a cell, and never both
summary flags. The input bits are unconstrained. Every clause list is ordered by
`List.range`, so the formula is a closed-form function of `(M, n, s)`. -/
def validity (n s : ℕ) : CNF ℕ :=
  FormulaKit.exactlyOne ((List.range (n + 2)).map (headVar n)) ++
    FormulaKit.exactlyOne ((List.range (stateCount M)).map (stateOffset n + ·)) ++
    (List.range M.k).flatMap (fun i =>
      FormulaKit.exactlyOne ((List.range (2 * s + 1)).map fun j => workVar M n s i j 2)) ++
    (List.range M.k).flatMap (fun i => (List.range (2 * s + 1)).map fun j =>
      [(workVar M n s i j 0, false), (workVar M n s i j 1, false)]) ++
    [[(summaryVar M n s false, false), (summaryVar M n s true, false)]]

/-- **The acceptance CNF** ([AB09, Claim 4.4(2)]): two unit clauses, the halting-state marker
(variable `stateOffset n`, which is `stateVar M n none`) and the accepting-summary flag. -/
def acceptance (n s : ℕ) : CNF ℕ :=
  [[(stateOffset n, true)], [(summaryVar M n s false, true)]]

/-- **Carried-input equality** between the source block and the target block: for each
input position `i < n`, two clauses stating that variables `i` and `width + i` are equal. -/
def inputEquality (n s : ℕ) : CNF ℕ :=
  (List.range n).flatMap fun i =>
    [[(i, false), (width M n s + i, true)], [(i, true), (width M n s + i, false)]]

/-- The finite transition **cases** of `M`: a state (the halting state included), a scanned
input symbol, and a scanned symbol on each work tape. A type depending on the machine only.
(The private `CodecCase` of the fill appendix, made public.) -/
abbrev Case := Option M.State × Option Bool × (Fin M.k → Option Bool)

/-- The action of a case: the machine's transition at that state and those scanned symbols,
or, at the halting state, the silent identity action. (The private `codecAction`, made
public.) -/
def caseAction (q : Case M) : Action M.k Bool M.State :=
  match q.1 with
  | none => ⟨0, fun _ => (none, 0), none, none⟩
  | some st => M.tm.tr st q.2.1 q.2.2

/-- **The machine-constant case list**: a fixed enumeration of the finite case type
(`Finset.univ.toList`). Its order depends on the machine only, so an emitter for the fixed
machine stores it as a finite table. -/
noncomputable def caseList : List (Case M) := (Finset.univ : Finset (Case M)).toList

/-- The `3k + 7` Boolean **ports** of one transition gate on a machine with `k` work tapes:
the state, input-head and work-head markers of the guard, the scanned input bit, the two
symbol flags of each scanned work cell, the two old summary flags, and the old and the new
value of the updated bit. (The private `CodecPort`, indexed by `k` and made public.) -/
inductive Port (k : ℕ)
  | state
  | inputHead
  | inputSymbol
  | workHead : Fin k → Port k
  | workSymbol : Fin k → Bool → Port k
  | summary : Bool → Port k
  | oldBit
  | newBit
  deriving Fintype, DecidableEq

/-- The number of ports of a gate on a machine with `k` work tapes, `3k + 7`. -/
def portCount (k : ℕ) : ℕ := 3 * k + 7

/-- **Closed-form port numbering**: `state`, `inputHead`, `inputSymbol` are `0, 1, 2`; the `k`
work heads follow; then two symbol flags per tape (`false` before `true`); then the two summary
flags; then the old and the new bit, `3k + 5` and `3k + 6`. -/
def portIndex {k : ℕ} : Port k → ℕ
  | .state => 0
  | .inputHead => 1
  | .inputSymbol => 2
  | .workHead i => 3 + i.val
  | .workSymbol i t => 3 + k + 2 * i.val + if t then 1 else 0
  | .summary t => 3 + 3 * k + if t then 1 else 0
  | .oldBit => 5 + 3 * k
  | .newBit => 6 + 3 * k

/-- The port with number `j` (inverse to `portIndex` below `portCount k`; numbers at or above
`portCount k` give `newBit`). -/
def portOf (k j : ℕ) : Port k :=
  if h₀ : j < 3 then (if j = 0 then .state else if j = 1 then .inputHead else .inputSymbol)
  else if h : j < 3 + k then .workHead ⟨j - 3, by omega⟩
  else if h' : j < 3 + 3 * k then .workSymbol ⟨(j - 3 - k) / 2, by omega⟩ ((j - 3 - k) % 2 = 1)
  else if j = 3 + 3 * k then .summary false
  else if j = 4 + 3 * k then .summary true
  else if j = 5 + 3 * k then .oldBit
  else .newBit

/-- What a gate asserts about its new bit: that it copies the old bit, that it is a constant,
or that it is one of the two summary flags recomputed from the old flags and the case's
output. -/
inductive Expect
  | copy
  | const (b : Bool)
  | summary (dead : Bool)
  deriving Fintype, DecidableEq

/-- A **gate kind**: a case, whether the guarded input position is interior, and an
expectation. A finite type depending on the machine only, so there is one gate template per
kind for the fixed machine. -/
abbrev GateKind := Case M × Bool × Expect

/-- Two symbol flags decode to blank, `false` or `true` (the excluded pattern `11` reads
`true`). (The private `codecReadSymbol`, made public.) -/
def readSymbol (f t : Bool) : Option Bool := if t then some true else if f then some false else none

/-- Two summary flags decode to an output summary (the excluded pattern `11` reads dead). (The
private `codecReadSummary`, made public.) -/
def readSummary (acc dead : Bool) : OutSummary :=
  if dead then .dead else if acc then .accept else .empty

/-- A canonical output word with each summary: `[]`, `[true]`, `[false]`. (The private
`codecSummaryWord`, made public.) -/
def summaryWord : OutSummary → List Bool
  | .empty => []
  | .accept => [true]
  | .dead => [false]

/-- **The guard of a gate** of case `q`: the selected state, input-head and work-head markers
are all set, the scanned input symbol is that of the case (an end-marker position, not
`interior`, scans blank), and each scanned work cell's flags decode to the case's symbol. -/
def guard (q : Case M) (interior : Bool) (a : Port M.k → Bool) : Bool :=
  a .state && a .inputHead && (List.finRange M.k).all (fun i => a (.workHead i)) &&
    decide ((if interior then some (a .inputSymbol) else none) = q.2.1) &&
    (List.finRange M.k).all fun i =>
      decide (readSymbol (a (.workSymbol i false)) (a (.workSymbol i true)) = q.2.2 i)

/-- The bit a gate expects as the new bit, under an action: the old bit (`copy`), a constant,
or a summary flag of the old summary followed by the action's output. -/
def expectBit (act : Action M.k Bool M.State) : Expect → (Port M.k → Bool) → Bool
  | .copy, a => a .oldBit
  | .const b, _ => b
  | .summary dead, a =>
    decide (outSummary (summaryWord (readSummary (a (.summary false)) (a (.summary true))) ++
      act.output.toList) = if dead then .dead else .accept)

/-- **The predicate of a gate kind** `(q, interior, e)`: if the guard holds, then the new bit
is the bit expected under the case's action. -/
def kindPred (κ : GateKind M) (a : Port M.k → Bool) : Bool :=
  !guard M κ.1 κ.2.1 a || (a .newBit == expectBit M (caseAction M κ.1) κ.2.2 a)

/-- The window cell of the head of work tape `i` in the head tuple coded by `h < (2s+1)^k`
(mixed radix `2s + 1`, tape `0` least significant). -/
def headOf (s h i : ℕ) : ℕ := h / (2 * s + 1) ^ i % (2 * s + 1)

/-- The input-head move of `Turing.moveInputPos`, on natural-number positions: add the move
in `ℤ`, truncate at `0`, and clamp at the right end marker `n + 1`. -/
def moveInput (n p : ℕ) (m : SignType) : ℕ :=
  let p' := ((p : ℤ) + (m.cast : ℤ)).toNat
  if p' < n + 2 then p' else n + 1

/-- **The expectation of target bit `v`** under input-head position `p`, head tuple `h` and
case `q`: input bits are copied; the input-head, state and work-head markers are recomputed
constants; a symbol flag at a written head cell is the written value, and is copied at every
other cell; the summary flags are recomputed. Closed form in `(n, s, p, h, v)` for the fixed
case. -/
noncomputable def expectOf (n s p h : ℕ) (q : Case M) (v : ℕ) : Expect :=
  let act := caseAction M q
  if v < n then .copy
  else if v < stateOffset n then .const (decide (moveInput n p act.inputTape = v - n))
  else if v < workOffset M n then .const (decide (stateIndex M act.state = v - stateOffset n))
  else if v < summaryOffset M n s then
    let u := v - workOffset M n
    let i := u / 3 / (2 * s + 1)
    let j := u / 3 % (2 * s + 1)
    if hi : i < M.k then
      if u % 3 < 2 then
        if headOf s h i = j then
          match (act.workTapes ⟨i, hi⟩).1 with
          | none => .copy
          | some w => .const (decide (w = some (decide (u % 3 = 1))))
        else .copy
      else .const (decide ((headOf s h i : ℤ) + ((act.workTapes ⟨i, hi⟩).2.cast : ℤ) = j))
    else .copy
  else .summary (decide (v = summaryOffset M n s + 1))

/-- **The wiring of a gate**, in closed form: the guard ports read the source block at the
markers selected by `(p, h, q)`; the old bit is source variable `v`; the new bit is target
variable `width + v`. The input-symbol port of an end-marker position reads a variable that
the guard ignores. -/
noncomputable def portWire (n s p h : ℕ) (q : Case M) (v : ℕ) : Port M.k → ℕ
  | .state => stateVar M n q.1
  | .inputHead => headVar n p
  | .inputSymbol => if 0 < p ∧ p ≤ n then inputVar (p - 1) else summaryVar M n s false
  | .workHead i => workVar M n s i (headOf s h i) 2
  | .workSymbol i t => workVar M n s i (headOf s h i) (if t then 1 else 0)
  | .summary t => summaryVar M n s t
  | .oldBit => v
  | .newBit => width M n s + v

/-- **One transition gate**: the fixed template (`Complexity.FormulaKit.gate`) of the kind
`(q, interior p, expectOf …)`, wired by `portWire`. -/
noncomputable def transitionGate (n s p h : ℕ) (q : Case M) (v : ℕ) : CNF ℕ :=
  FormulaKit.gate (portCount M.k)
    (fun a => kindPred M (q, decide (0 < p ∧ p ≤ n), expectOf M n s p h q v)
      (fun port => FormulaKit.readBit a (portIndex port)))
    (fun j => portWire M n s p h q v (portOf M.k j))

/-- **The transition conjunction**, enumerated in closed form: input-head positions
`p < n + 2`, head tuples `h < (2s + 1)^k`, the fixed case list, and target bits `v < width`,
in that nesting (P4.3 round-2 finding 4: `(n + 2)(2s + 1)^k` guarded positions, polynomial for
the fixed machine; Boolean universality is used per gate, never per row). -/
noncomputable def transition (n s : ℕ) : CNF ℕ :=
  (List.range (n + 2)).flatMap fun p =>
    (List.range ((2 * s + 1) ^ M.k)).flatMap fun h =>
      (caseList M).flatMap fun q =>
        (List.range (width M n s)).flatMap fun v => transitionGate M n s p h q v

/-- **The adjacency CNF** ([AB09, Claim 4.4(2)]): carried-input equality and the transition
conjunction, over the source block `[0, width)` and the target block `[width, 2 · width)`. -/
noncomputable def adjacency (n s : ℕ) : CNF ℕ := inputEquality M n s ++ transition M n s

end ConfigCodec

/-! ### Fill appendix: finite marker tracks for the quotient codec

The finite row below factors through `ConfigCount.coreCode`. Its Boolean coordinates
are the input contents, one-hot input head and state, three bits per work cell
(two mutually exclusive symbol bits and one head marker), and two summary bits.
Coordinates are numbered by a finite equivalence; the rest of the prescribed width
is zero padding. No output history other than `outSummary` is retained.

For adjacency, each joint head tuple and finite scanned-symbol/state case guards
one output-coordinate gate. Its `3k+7` ports include the guard markers, the scanned
input and work bits, the summary flags, and the old/new coordinate. Thus every use
of Boolean universality has machine-only arity. Exact integer successor markers
reject outward moves; the code itself is only compared on windowed configurations.
Normalizing the output history before a transition uses `NDTM.coreSum_stepWith`.
With `u=s+n+2`, the validity and acceptance ledgers have degree three, and adjacency
has degree `k+3`. A single constant absorbs all coefficients and the padded width.
-/

/-- The finite fields of a windowed configuration, together with its input. -/
private structure CodecRow (M : FinTM Bool) (n s : ℕ) where
  input : Fin n → Bool
  state : Option M.State
  inputHead : Fin (n + 2)
  symbols : Fin M.k → Fin (2 * s + 1) → Option Bool
  heads : Fin M.k → Fin (2 * s + 1)
  summary : OutSummary

/-- One coordinate for each bit in the marker discipline of Claim 4.4(2). -/
private inductive CodecBit (M : FinTM Bool) (n s : ℕ)
  | input : Fin n → CodecBit M n s
  | inputHead : Fin (n + 2) → CodecBit M n s
  | state : Option M.State → CodecBit M n s
  | work : Fin M.k → Fin (2 * s + 1) → Fin 3 → CodecBit M n s
  | summary : Bool → CodecBit M n s
  deriving Fintype, DecidableEq

/-- The unpadded track width, with three bits for every work cell. -/
private theorem codecBit_card (M : FinTM Bool) (n s : ℕ) :
    Fintype.card (CodecBit M n s) =
      n + (n + 2) + (Fintype.card M.State + 1) + M.k * (2 * s + 1) * 3 + 2 := by
  rw [← Fintype.card_congr (CodecBit.proxyTypeEquiv M n s)]
  simp
  ring

/-- A machine-dependent linear coefficient sufficient for all raw tracks. -/
private def codecCoefficient (M : FinTM Bool) : ℕ :=
  Fintype.card M.State + 6 * M.k + 5

/-- The raw tracks fit every requested width with coefficient at least this one. -/
private theorem codecBit_card_le (M : FinTM Bool) (n s C : ℕ)
    (hC : codecCoefficient M ≤ C) :
    Fintype.card (CodecBit M n s) ≤ C * (s + n + 1) := by
  rw [codecBit_card]
  unfold codecCoefficient at hC
  calc
    _ ≤ (Fintype.card M.State + 6 * M.k + 5) * (s + n + 1) := by nlinarith
    _ ≤ _ := Nat.mul_le_mul_right _ hC

/-- Marker encoding of a finite row. Blank symbols and the empty summary use `00`;
false/true symbols and accept/dead summaries use the two singleton patterns. -/
private def codecRowBits {M : FinTM Bool} {n s : ℕ} (r : CodecRow M n s) :
    CodecBit M n s → Bool
  | .input i => r.input i
  | .inputHead j => decide (r.inputHead = j)
  | .state q => decide (r.state = q)
  | .work i j b =>
      if b.val = 0 then decide (r.symbols i j = some false)
      else if b.val = 1 then decide (r.symbols i j = some true)
      else decide (r.heads i = j)
  | .summary b => decide (r.summary = if b then .dead else .accept)

/-- Two singleton flags distinguish all three values of an optional bit. -/
private theorem codec_symbol_ext (u v : Option Bool)
    (h0 : decide (u = some false) = decide (v = some false))
    (h1 : decide (u = some true) = decide (v = some true)) : u = v := by
  cases u with
  | none => cases v with
    | none => rfl
    | some b => cases b <;> simp_all
  | some a => cases v with
    | none => cases a <;> simp_all
    | some b => cases a <;> cases b <;> simp_all

/-- Marker equality recovers every field of a finite row.

**Proof sketch.** Read the true marker at the first row's state and head positions.
The two symbol flags distinguish blank, false and true; the two summary flags
similarly distinguish the three output summaries. Input bits are direct coordinates. -/
private theorem codecRowBits_injective {M : FinTM Bool} {n s : ℕ} :
    Function.Injective (@codecRowBits M n s) := by
  intro r t h
  have hi : r.input = t.input := funext fun j => congrFun h (.input j)
  have hs : r.state = t.state := by
    have := congrFun h (.state r.state)
    exact Eq.symm (of_decide_eq_true (show decide (t.state = r.state) = true from by
      simpa only [codecRowBits, decide_true] using this.symm))
  have hp : r.inputHead = t.inputHead := by
    have := congrFun h (.inputHead r.inputHead)
    exact Eq.symm (of_decide_eq_true (show decide (t.inputHead = r.inputHead) = true from by
      simpa only [codecRowBits, decide_true] using this.symm))
  have hw : r.symbols = t.symbols := by
    funext i j
    apply codec_symbol_ext
    · exact congrFun h (.work i j 0)
    · exact congrFun h (.work i j 1)
  have hh : r.heads = t.heads := by
    funext i
    have := congrFun h (.work i (r.heads i) 2)
    exact Eq.symm (of_decide_eq_true (show decide (t.heads i = r.heads i) = true from by
      simpa [codecRowBits] using this.symm))
  have ho : r.summary = t.summary := by
    have h0 := congrFun h (.summary false)
    have h1 := congrFun h (.summary true)
    cases hr : r.summary <;> cases ht : t.summary <;>
      simp_all [codecRowBits]
  cases r
  cases t
  cases hi
  cases hs
  cases hp
  cases hw
  cases hh
  cases ho
  rfl

/-- Restriction of a configuration to its finite core code, with input and summary. -/
private def codecRowOf (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) : CodecRow M n s :=
  let t := MultiTapeTM.ConfigCount.coreCode s c
  { input := fun i => x.getD i.val false
    state := t.1
    inputHead := ⟨t.2.1.val, by simpa [hx] using t.2.1.isLt⟩
    symbols := t.2.2.1
    heads := t.2.2.2
    summary := outSummary c.output }

/-- Translate the public window predicate into the hypotheses of `coreCode_inj`. -/
private theorem codec_core_window {k : ℕ} {S : Type} {x : List Bool} {s : ℕ}
    {c : Cfg k Bool S x} (hc : c.InWindow s) :
    ∀ i, |c.workTapePos i| ≤ s ∧ ∀ z, c.workTapes i z ≠ none → |z| ≤ s := by
  intro i
  refine ⟨hc.1 i, ?_⟩
  intro z hz
  by_contra hn
  exact hz (hc.2 i z (lt_of_not_ge hn))

/-- Equality of the finite rows recovers the input content. -/
private theorem codecRowOf_input_eq (M : FinTM Bool) (n s : ℕ)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (c : Cfg M.k Bool M.State x) (d : Cfg M.k Bool M.State y)
    (h : (codecRowOf M n s x hx c).input = (codecRowOf M n s y hy d).input) : x = y := by
  apply List.ext_getElem
  · omega
  · intro i hix hiy
    have he := congrFun h ⟨i, by omega⟩
    simpa [codecRowOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hix, hiy] using he

/-- The finite row identifies exactly the configuration-graph vertex at a fixed input.

**Proof sketch.** Forward, the four finite core fields agree, so `coreCode_inj`
recovers the core using the window bounds; the fifth field supplies the summary.
Backward, equality of cores and summaries directly makes all finite fields equal. -/
private theorem codecRowOf_eq_iff (M : FinTM Bool) (n s : ℕ)
    (x : List Bool) (hx : x.length = n) (c d : Cfg M.k Bool M.State x)
    (hc : c.InWindow s) (hd : d.InWindow s) :
    codecRowOf M n s x hx c = codecRowOf M n s x hx d ↔
      NDTM.coreSum c = NDTM.coreSum d := by
  constructor
  · intro h
    apply Prod.ext
    · apply MultiTapeTM.ConfigCount.coreCode_inj s (codec_core_window hc) (codec_core_window hd)
      apply Prod.ext (congrArg CodecRow.state h)
      apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun r => r.inputHead.val) h
      · exact Prod.ext (congrArg CodecRow.symbols h) (congrArg CodecRow.heads h)
    · exact congrArg CodecRow.summary h
  · intro h
    have hc := congrArg Prod.fst h
    have ho := congrArg Prod.snd h
    change MultiTapeTM.ConfigCount.core c = MultiTapeTM.ConfigCount.core d at hc
    change outSummary c.output = outSummary d.output at ho
    simp only [MultiTapeTM.ConfigCount.core, Prod.mk.injEq] at hc
    rcases hc with ⟨hs, hp, hw, hh⟩
    simp only [codecRowOf, MultiTapeTM.ConfigCount.coreCode, hs, hp, hw, hh, ho]

/-- Pad an arbitrary finite bit assignment to exactly `L` bits (truncate if necessary).
The application below always proves that truncation cannot occur. -/
private noncomputable def codecWord {α : Type} [Fintype α] (L : ℕ) (a : α → Bool) :
    List Bool :=
  List.ofFn fun i : Fin L =>
    if h : i.val < Fintype.card α then
      a ((Fintype.equivFin α).symm ⟨i.val, h⟩)
    else false

/-- The padded word has its prescribed length on all arguments. -/
private theorem codecWord_length {α : Type} [Fintype α] (L : ℕ) (a : α → Bool) :
    (codecWord L a).length = L := by simp [codecWord]

/-- Reading the coordinate of a finite bit assignment after sufficient padding. -/
private theorem codecWord_get {α : Type} [Fintype α] (L : ℕ) (a : α → Bool)
    (hL : Fintype.card α ≤ L) (i : α) :
    (codecWord L a).getD (Fintype.equivFin α i).val false = a i := by
  have hi := (Fintype.equivFin α i).isLt
  simp [codecWord, List.getD_eq_getElem?_getD, hi, lt_of_lt_of_le hi hL]

/-- Sufficiently padded words agree exactly when their underlying bits agree. -/
private theorem codecWord_eq_iff {α : Type} [Fintype α] (L : ℕ)
    (hL : Fintype.card α ≤ L) (a b : α → Bool) :
    codecWord L a = codecWord L b ↔ a = b := by
  constructor
  · intro h
    funext i
    have he := congrArg (fun w : List Bool => w.getD (Fintype.equivFin α i).val false) h
    simpa only [codecWord_get L a hL i, codecWord_get L b hL i] using he
  · rintro rfl
    rfl

/-- The total configuration codec. Wrong-length inputs receive the all-zero word. -/
private noncomputable def configurationCodec (M : FinTM Bool) (C n s : ℕ)
    (x : List Bool) (c : Cfg M.k Bool M.State x) : List Bool :=
  if hx : x.length = n then
    codecWord (C * (s + n + 1)) (codecRowBits (codecRowOf M n s x hx c))
  else List.replicate (C * (s + n + 1)) false

/-- Exact length holds even for wrong-length inputs and nonwindowed configurations. -/
private theorem configurationCodec_length (M : FinTM Bool) (C n s : ℕ)
    (x : List Bool) (c : Cfg M.k Bool M.State x) :
    (configurationCodec M C n s x c).length = C * (s + n + 1) := by
  unfold configurationCodec
  split <;> simp [codecWord_length]

/-- The codec separates inputs of the prescribed length. -/
private theorem configurationCodec_input_eq (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x y : List Bool)
    (hx : x.length = n) (hy : y.length = n)
    (c : Cfg M.k Bool M.State x) (d : Cfg M.k Bool M.State y)
    (h : configurationCodec M C n s x c = configurationCodec M C n s y d) : x = y := by
  simp only [configurationCodec, dif_pos hx, dif_pos hy] at h
  have hbits := (codecWord_eq_iff _ (codecBit_card_le M n s C hC) _ _).mp h
  exact codecRowOf_input_eq M n s x y hx hy c d (congrArg CodecRow.input (codecRowBits_injective hbits))

/-- The padded codec factors through, and separates, the windowed vertex quotient. -/
private theorem configurationCodec_eq_iff (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x : List Bool) (hx : x.length = n)
    (c d : Cfg M.k Bool M.State x) (hc : c.InWindow s) (hd : d.InWindow s) :
    configurationCodec M C n s x c = configurationCodec M C n s x d ↔
      NDTM.coreSum c = NDTM.coreSum d := by
  simp only [configurationCodec, dif_pos hx,
    codecWord_eq_iff _ (codecBit_card_le M n s C hC), codecRowBits_injective.eq_iff]
  exact codecRowOf_eq_iff M n s x hx c d hc hd

/-- A flattened family conjoins exactly its member formulas. -/
private theorem codecCnf_eval_flatMap {α β : Type} (xs : List β) (f : β → CNF α)
    (a : α → Bool) : CNF.eval a (xs.flatMap f) = true ↔ ∀ i ∈ xs, (f i).eval a = true := by
  simp [CNF.eval, List.all_flatMap, List.all_eq_true]

/-- A list of clauses conjoins their individual evaluations. -/
private theorem codecCnf_eval_map {α β : Type} (xs : List β) (f : β → CNF.Clause α)
    (a : α → Bool) : CNF.eval a (xs.map f) = true ↔ ∀ i ∈ xs, (f i).eval a = true := by
  simp [CNF.eval, List.all_eq_true]

/-- Exactly one positive marker, expressed by one positive clause and pairwise exclusions. -/
private noncomputable def codecOneHot (α : Type) [Fintype α] [DecidableEq α] : CNF α :=
  [(Finset.univ.toList.map fun i : α => (i, true))] ++
    Finset.univ.toList.flatMap fun i : α =>
      (Finset.univ.toList.filter fun j : α => decide (i ≠ j)).map fun j =>
        [(i, false), (j, false)]

/-- Pairwise exclusions give precisely a one-hot assignment.

**Proof sketch.** The positive clause selects a true coordinate. Its exclusion clause
with any other coordinate forces that other coordinate false. Conversely, an assignment
with a single true coordinate satisfies the positive clause and every exclusion. -/
private theorem codecOneHot_eval (α : Type) [Fintype α] [DecidableEq α] (a : α → Bool) :
    (codecOneHot α).eval a = true ↔ ∃ j : α, ∀ i : α, a i = decide (j = i) := by
  classical
  have he : (codecOneHot α).eval a = true ↔
      (∃ j : α, a j = true) ∧ ∀ i j : α, i ≠ j → (a i = false ∨ a j = false) := by
    simp [codecOneHot, CNF.eval, CNF.Clause.eval, List.all_flatMap,
      List.all_filter, Bool.or_eq_true]
    intro _ _
    constructor
    · intro h i j hij
      exact (h i j).resolve_left hij
    · intro h i j
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr (h i j hij)
  rw [he]
  constructor
  · rintro ⟨⟨j, hj⟩, hpair⟩
    refine ⟨j, fun i => ?_⟩
    by_cases hji : j = i
    · subst i
      simpa using hj
    · have hi := hpair j i hji
      simpa [hji, hj] using hi
  · rintro ⟨j, hj⟩
    refine ⟨⟨j, by simpa using hj j⟩, ?_⟩
    intro u v huv
    by_cases hju : j = u
    · right
      have hjv : j ≠ v := by simpa [hju] using huv
      simpa [hjv] using hj v
    · left
      simpa [hju] using hj u

/-- Valid marker assignments consist of one-hot heads and state, with the forbidden
`11` pattern excluded from each symbol and summary pair. -/
private def codecBitsValid (M : FinTM Bool) (n s : ℕ) (a : CodecBit M n s → Bool) : Prop :=
  (∃ j : Fin (n + 2), ∀ i, a (.inputHead i) = decide (j = i)) ∧
  (∃ q : Option M.State, ∀ p, a (.state p) = decide (q = p)) ∧
  (∀ i : Fin M.k, ∃ h : Fin (2 * s + 1),
    ∀ j, a (.work i j 2) = decide (h = j)) ∧
  (∀ i j, a (.work i j 0) = false ∨ a (.work i j 1) = false) ∧
  (a (.summary false) = false ∨ a (.summary true) = false)

/-- Every finite row produces a valid marker assignment. -/
private theorem codecRowBits_valid {M : FinTM Bool} {n s : ℕ} (r : CodecRow M n s) :
    codecBitsValid M n s (codecRowBits r) := by
  refine ⟨⟨r.inputHead, fun _ => rfl⟩, ⟨r.state, fun _ => rfl⟩,
    (fun i => ⟨r.heads i, fun _ => rfl⟩), ?_, ?_⟩
  · intro i j
    cases h : r.symbols i j with
    | none => simp [codecRowBits, h]
    | some b => cases b <;> simp [codecRowBits, h]
  · cases h : r.summary <;> simp [codecRowBits, h]

/-- Every valid marker assignment is the encoding of a finite row.

**Proof sketch.** Choose the unique head and state markers. Decode each two-bit symbol
pair as false, true or blank; its exclusion rules out `11`. Decode the summary in the
same way. Each coordinate of the constructed row then has the prescribed bit. -/
private theorem codecBitsValid_iff (M : FinTM Bool) (n s : ℕ)
    (a : CodecBit M n s → Bool) :
    codecBitsValid M n s a ↔ ∃ r : CodecRow M n s, codecRowBits r = a := by
  classical
  constructor
  · rintro ⟨⟨ip, hip⟩, ⟨q, hq⟩, hh, hw, ho⟩
    choose hp hhp using hh
    let r : CodecRow M n s :=
      { input := fun i => a (.input i)
        state := q
        inputHead := ip
        symbols := fun i j => if a (.work i j 0) then some false
          else if a (.work i j 1) then some true else none
        heads := hp
        summary := if a (.summary false) then .accept
          else if a (.summary true) then .dead else .empty }
    refine ⟨r, funext fun z => ?_⟩
    cases z with
    | input i => rfl
    | inputHead i => exact (hip i).symm
    | state p => exact (hq p).symm
    | work i j b =>
      have hij := hw i j
      fin_cases b <;>
        cases h0 : a (.work i j 0) <;> cases h1 : a (.work i j 1) <;>
        simp_all [codecRowBits, r]
    | summary b =>
      cases b <;> cases h0 : a (.summary false) <;>
        cases h1 : a (.summary true) <;> simp_all [codecRowBits, r]
  · rintro ⟨r, rfl⟩
    exact codecRowBits_valid r

/-- The validity CNF on unpadded tracks. Input contents are unrestricted. -/
private noncomputable def codecValidity (M : FinTM Bool) (n s : ℕ) : CNF (CodecBit M n s) :=
  (codecOneHot (Fin (n + 2))).relabel CodecBit.inputHead ++
  (codecOneHot (Option M.State)).relabel CodecBit.state ++
  (List.finRange M.k).flatMap (fun i =>
    (codecOneHot (Fin (2 * s + 1))).relabel (fun j => CodecBit.work i j 2)) ++
  (List.finRange M.k).flatMap (fun i => (List.finRange (2 * s + 1)).map fun j =>
    [(CodecBit.work i j 0, false), (CodecBit.work i j 1, false)]) ++
  [[(CodecBit.summary false, false), (CodecBit.summary true, false)]]

/-- The unpadded validity formula recognizes exactly the finite-row encodings. -/
private theorem codecValidity_eval (M : FinTM Bool) (n s : ℕ)
    (a : CodecBit M n s → Bool) :
    (codecValidity M n s).eval a = true ↔ ∃ r : CodecRow M n s, codecRowBits r = a := by
  rw [← codecBitsValid_iff]
  simp [codecValidity, codecBitsValid, CNF.eval_append, CNF.eval_relabel,
    codecOneHot_eval, codecCnf_eval_flatMap, codecCnf_eval_map, CNF.Clause.eval,
    Bool.or_eq_true]

/-- The finite position code decodes the designated cell of the window. -/
private theorem codec_posCode (s : ℕ) (j : Fin (2 * s + 1)) :
    MultiTapeTM.ConfigCount.posCode s ((j.val : ℤ) - s) = j := by
  apply Fin.ext
  dsimp [MultiTapeTM.ConfigCount.posCode]
  have hj := j.isLt
  omega

/-- Every finite row is realized by a genuine windowed configuration.

**Proof sketch.** Turn the input vector into a list and extend the finite work tracks
by blanks outside the window. Subtract the radius to recover work-head positions.
Use respectively `[]`, `[true]` and `[false]` for the three summaries. Reading the
finite core code of this configuration returns exactly the original row. -/
private theorem codecRow_realize (M : FinTM Bool) (n s : ℕ) (r : CodecRow M n s) :
    ∃ (x : List Bool) (hx : x.length = n) (c : Cfg M.k Bool M.State x),
      c.InWindow s ∧ codecRowOf M n s x hx c = r := by
  let x := List.ofFn r.input
  have hx : x.length = n := by simp [x]
  let c : Cfg M.k Bool M.State x :=
    { state := r.state
      inputPos := ⟨r.inputHead.val, by rw [hx]; exact r.inputHead.isLt⟩
      workTapes := fun i z => if |z| ≤ (s : ℤ) then
        r.symbols i (MultiTapeTM.ConfigCount.posCode s z) else none
      workTapePos := fun i => (r.heads i).val - (s : ℤ)
      output := match r.summary with
        | .empty => []
        | .accept => [true]
        | .dead => [false] }
  have hz (j : Fin (2 * s + 1)) : |(j.val : ℤ) - s| ≤ (s : ℤ) := by
    have hj := j.isLt
    rw [abs_le]
    omega
  refine ⟨x, hx, c, ⟨fun i => hz (r.heads i), ?_⟩, ?_⟩
  · intro i z h
    simp [c, not_le_of_gt h]
  · have hi : (fun i : Fin n => x.getD i.val false) = r.input := by
      funext i
      simp [x, List.getD_eq_getElem?_getD]
    have hw : (fun (i : Fin M.k) (j : Fin (2 * s + 1)) => c.workTapes i ((j.val : ℤ) - s)) = r.symbols := by
      funext i j
      simp [c, hz j, codec_posCode]
    have hh : (fun i => MultiTapeTM.ConfigCount.posCode s (c.workTapePos i)) = r.heads := by
      funext i
      exact codec_posCode s (r.heads i)
    have ho : outSummary c.output = r.summary := by
      cases h : r.summary <;> simp [c, h, outSummary]
    dsimp [codecRowOf, MultiTapeTM.ConfigCount.coreCode]
    rw [hi, hw, hh, ho]

/-- A padded word's unused suffix is zero. -/
private theorem codecWord_padding {α : Type} [Fintype α] (L : ℕ) (a : α → Bool)
    (j : ℕ) (hj : Fintype.card α ≤ j) : (codecWord L a).getD j false = false := by
  by_cases hL : j < L
  · simp [codecWord, List.getD_eq_getElem?_getD, hL, not_lt_of_ge hj]
  · simp [codecWord, List.getD_eq_getElem?_getD, hL]

/-- A word of length `L` with zero padding is recovered from its finite coordinates. -/
private theorem codecWord_reconstruct {α : Type} [Fintype α] (L : ℕ)
    (w : List Bool) (hw : w.length = L)
    (hpad : ∀ j, Fintype.card α ≤ j → j < L → w.getD j false = false) :
    codecWord L (fun i : α => w.getD (Fintype.equivFin α i).val false) = w := by
  apply List.ext_getElem
  · simpa [codecWord_length] using hw.symm
  · intro i hi hiw
    have hiL : i < L := by simpa only [codecWord_length] using hi
    by_cases hiα : i < Fintype.card α
    · simp [codecWord, hiα, List.getD_eq_getElem?_getD, hiw]
    · have he := hpad i (by omega) hiL
      simpa [codecWord, hiα, List.getD_eq_getElem?_getD, hiw] using he.symm

/-- The padding clauses fix every unused coordinate to false. -/
private def codecPadding (first L : ℕ) : CNF ℕ :=
  (List.range (L - first)).map fun i => [(first + i, false)]

/-- Evaluation of the padding clauses states exactly that the unused suffix is zero. -/
private theorem codecPadding_eval (first L : ℕ) (a : ℕ → Bool) :
    (codecPadding first L).eval a = true ↔ ∀ j, first ≤ j → j < L → a j = false := by
  simp only [codecPadding, CNF.eval, List.all_map, List.all_eq_true, List.mem_range,
    Function.comp_apply, CNF.Clause.eval_cons, CNF.Clause.eval_nil, Bool.or_false,
    beq_iff_eq]
  constructor
  · intro h j hj hjL
    simpa [Nat.add_sub_of_le hj] using h (j - first) (by omega)
  · intro h i hi
    exact h (first + i) (by omega) (by omega)

/-- Number the finite validity formula inside the prescribed width and add zero padding. -/
private noncomputable def configurationValidity (M : FinTM Bool) (C n s : ℕ) : CNF ℕ :=
  (codecValidity M n s).relabel (fun b => (Fintype.equivFin (CodecBit M n s) b).val) ++
    codecPadding (Fintype.card (CodecBit M n s)) (C * (s + n + 1))

/-- Validity recognizes exactly the padded codes of windowed configurations.

**Proof sketch.** The unpadded formula recovers a finite row and the padding clauses
recover the remaining zeros. Realize that row by the window extension lemma.
Conversely every configuration supplies a valid row and zero padding. -/
private theorem configurationValidity_eval (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (w : List Bool) (hw : w.length = C * (s + n + 1)) :
    (configurationValidity M C n s).eval (fun j => w.getD j false) = true ↔
      ∃ x : List Bool, x.length = n ∧ ∃ c : Cfg M.k Bool M.State x,
        c.InWindow s ∧ w = configurationCodec M C n s x c := by
  have hfit := codecBit_card_le M n s C hC
  simp only [configurationValidity, CNF.eval_append, Bool.and_eq_true, CNF.eval_relabel,
    codecValidity_eval, codecPadding_eval, Function.comp_def]
  constructor
  · rintro ⟨⟨r, hr⟩, hp⟩
    obtain ⟨x, hx, c, hc, he⟩ := codecRow_realize M n s r
    refine ⟨x, hx, c, hc, ?_⟩
    simp only [configurationCodec, dif_pos hx, he, hr]
    exact (codecWord_reconstruct _ w hw hp).symm
  · rintro ⟨x, hx, c, hc, rfl⟩
    simp only [configurationCodec, dif_pos hx]
    refine ⟨⟨codecRowOf M n s x hx c, ?_⟩, ?_⟩
    · funext b
      exact (codecWord_get _ _ hfit b).symm
    · intro j hj _
      exact codecWord_padding _ _ j hj

/-- Acceptance reads the halt marker and the accepting summary marker. -/
private def codecAcceptance (M : FinTM Bool) (n s : ℕ) : CNF (CodecBit M n s) :=
  [[(.state none, true)], [(.summary false, true)]]

/-- The acceptance formula has the required meaning on every finite row. -/
private theorem codecAcceptance_eval (M : FinTM Bool) (n s : ℕ) (r : CodecRow M n s) :
    (codecAcceptance M n s).eval (codecRowBits r) = true ↔
      r.state = none ∧ r.summary = .accept := by
  simp [codecAcceptance, CNF.eval, CNF.Clause.eval, codecRowBits]

/-- Number the two acceptance tests at their actual code positions. -/
private noncomputable def configurationAcceptance (M : FinTM Bool) (n s : ℕ) : CNF ℕ :=
  (codecAcceptance M n s).relabel (fun b => (Fintype.equivFin (CodecBit M n s) b).val)

/-- The numbered acceptance CNF recognizes halted configurations with accepting summary. -/
private theorem configurationAcceptance_eval (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x : List Bool) (hx : x.length = n)
    (c : Cfg M.k Bool M.State x) :
    (configurationAcceptance M n s).eval (fun j => (configurationCodec M C n s x c).getD j false)
      = true ↔ c.state = none ∧ outSummary c.output = .accept := by
  simp only [configurationAcceptance, CNF.eval_relabel, Function.comp_def,
    configurationCodec, dif_pos hx, codecWord_get _ _ (codecBit_card_le M n s C hC)]
  exact codecAcceptance_eval M n s (codecRowOf M n s x hx c)

/-- Clause count plus literal occurrences; empty clauses still cost one unit. -/
private def codecCnfCost {α : Type} (φ : CNF α) : ℕ :=
  (φ.map fun clause => clause.length + 1).sum

/-- Renumbering variables preserves the clause-and-literal cost. -/
private theorem codecCnfCost_relabel {α β : Type} (φ : CNF α) (f : α → β) :
    codecCnfCost (φ.relabel f) = codecCnfCost φ := by
  simp [codecCnfCost, CNF.relabel, CNF.Clause.relabel, List.map_map, Function.comp_def]

/-- Conjoining CNFs adds their clause-and-literal costs. -/
private theorem codecCnfCost_append {α : Type} (φ ψ : CNF α) :
    codecCnfCost (φ ++ ψ) = codecCnfCost φ + codecCnfCost ψ := by
  simp [codecCnfCost]

/-- A family of bounded-cost checks has at most its length times the common cost. -/
private theorem codecCnfCost_flatMap_le {α β : Type} (xs : List β) (f : β → CNF α)
    (B : ℕ) (h : ∀ x ∈ xs, codecCnfCost (f x) ≤ B) :
    codecCnfCost (xs.flatMap f) ≤ xs.length * B := by
  induction xs with
  | nil => simp [codecCnfCost]
  | cons x xs ih =>
    rw [List.flatMap_cons, codecCnfCost_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    exact (Nat.add_le_add (h x List.mem_cons_self)
      (ih fun y hy => h y (List.mem_cons_of_mem x hy))).trans_eq (Nat.add_comm _ _)

/-- The exactly-one constraint has a quadratic cost, including its positive clause.

**Proof sketch.** The positive clause costs the number of markers plus one.
There are at most the square of that many ordered exclusions, each costing three. -/
private theorem codecOneHot_cost (α : Type) [Fintype α] [DecidableEq α] :
    codecCnfCost (codecOneHot α) ≤
      Fintype.card α + 1 + 3 * (Fintype.card α) ^ 2 := by
  classical
  let xs := (Finset.univ : Finset α).toList
  have hx : xs.length = Fintype.card α := by simp [xs]
  have hpair (i : α) : codecCnfCost
      ((xs.filter fun j => decide (i ≠ j)).map fun j => [(i, false), (j, false)]) ≤
        Fintype.card α * 3 := by
    simp only [codecCnfCost, List.map_map, Function.comp_def, List.length_cons,
      List.length_nil, Nat.reduceAdd, List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]
    exact Nat.mul_le_mul_right 3 ((List.length_filter_le _ _).trans_eq hx)
  have h := codecCnfCost_flatMap_le xs
    (fun i => (xs.filter fun j => decide (i ≠ j)).map fun j => [(i, false), (j, false)])
    (Fintype.card α * 3) (fun i _ => hpair i)
  unfold codecOneHot
  rw [codecCnfCost_append]
  have hsingle : codecCnfCost [xs.map fun i => (i, true)] = Fintype.card α + 1 := by
    simp [codecCnfCost, hx]
  change codecCnfCost [xs.map fun i => (i, true)] + _ ≤ _
  rw [hsingle]
  rw [hx] at h
  nlinarith

/-- A variable bound for an explicitly bounded relabeling of a finite formula. -/
private theorem codecCnf_numVars {α : Type} (φ : CNF α) (wire : α → ℕ) (N : ℕ)
    (hw : ∀ c ∈ φ, ∀ l ∈ c, wire l.1 < N) : (CNF.relabel wire φ).numVars ≤ N := by
  apply List.max_le_of_forall_le
  intro j hj
  simp only [CNF.relabel, CNF.Clause.relabel, List.flatMap_map, List.map_map,
    Function.comp_def, List.mem_flatMap, List.mem_map] at hj
  obtain ⟨clause, hc, lit, hl, rfl⟩ := hj
  exact Nat.succ_le_of_lt (hw clause hc lit hl)

/-- The chapter-2 grammar bounds serialization by the cost times the index bound.

**Proof sketch.** A literal at index below `N` serializes to at most `N+2` bits.
Each clause contributes its prefix and terminator, and the formula has one final
terminator. Counting one extra unit per clause covers both separators, including
empty clauses. The bound deliberately allows `N+3` bits per cost unit. -/
private theorem codecCnf_serialize {α : Type} (φ : CNF α) (wire : α → ℕ) (N : ℕ)
    (hw : ∀ c ∈ φ, ∀ l ∈ c, wire l.1 < N) :
    (CNF.serialize (CNF.relabel wire φ)).length ≤ codecCnfCost φ * (N + 3) + 1 := by
  have hlit (l : Std.Sat.Literal α) (hl : wire l.1 < N) :
      (CNF.serializeLit (wire l.1, l.2)).length ≤ N + 2 := by
    simp only [CNF.serializeLit, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  have hclause (c : CNF.Clause α) (hc : ∀ l ∈ c, wire l.1 < N) :
      (CNF.serializeClause (c.relabel wire)).length + 1 ≤ (c.length + 1) * (N + 3) := by
    have ht : ((c.relabel wire).flatMap CNF.serializeLit).length ≤ c.length * (N + 2) := by
      induction c with
      | nil => simp [CNF.Clause.relabel]
      | cons l c ih =>
        simp only [CNF.Clause.relabel, List.map_cons, List.flatMap_cons,
          List.length_append, List.length_cons] at *
        calc
          _ ≤ (N + 2) + c.length * (N + 2) := Nat.add_le_add (hlit l (hc l List.mem_cons_self))
            (ih fun t ht => hc t (List.mem_cons_of_mem l ht))
          _ = _ := by ring
    simp only [CNF.serializeClause, List.length_append, List.length_cons, List.length_nil]
    nlinarith
  induction φ with
  | nil => simp [CNF.serialize, CNF.relabel, codecCnfCost]
  | cons c φ ih =>
    have hc := hclause c (hw c List.mem_cons_self)
    have ih := ih (fun d hd => hw d (List.mem_cons_of_mem c hd))
    have he : (CNF.serialize (CNF.relabel wire (c :: φ))).length =
        (CNF.serializeClause (c.relabel wire)).length + 1 +
          (CNF.serialize (CNF.relabel wire φ)).length := by
      simp [CNF.serialize, CNF.relabel]
      omega
    rw [he]
    simp only [codecCnfCost, List.map_cons, List.sum_cons] at *
    nlinarith

/-- Explicit polynomial coefficient for the unpadded validity clauses. -/
private def codecValidityCoefficient (M : FinTM Bool) : ℕ :=
  let q := Fintype.card M.State + 1
  3 * q ^ 2 + q + 9 + 21 * M.k

/-- Counting one-hot exclusions and trit ranges gives the raw validity cost.

**Proof sketch.** Apply the exactly-one ledger to the input head, state and each
work head. Each work cell adds one two-literal exclusion, as does the summary.
There are `k(2s+1)` work cells, and no constraint on the input-content bits. -/
private theorem codecValidity_cost_raw (M : FinTM Bool) (n s : ℕ) :
    codecCnfCost (codecValidity M n s) ≤
      ((n + 2) + 1 + 3 * (n + 2) ^ 2) +
      ((Fintype.card M.State + 1) + 1 + 3 * (Fintype.card M.State + 1) ^ 2) +
      M.k * ((2 * s + 1) + 1 + 3 * (2 * s + 1) ^ 2) +
      M.k * (3 * (2 * s + 1)) + 3 := by
  classical
  have hinput := codecOneHot_cost (Fin (n + 2))
  have hstate := codecOneHot_cost (Option M.State)
  have hhead := codecCnfCost_flatMap_le (List.finRange M.k)
    (fun i => (codecOneHot (Fin (2 * s + 1))).relabel
      (fun j => CodecBit.work (M := M) (n := n) i j 2))
    ((2 * s + 1) + 1 + 3 * (2 * s + 1) ^ 2) (by
      intro i _
      simpa [codecCnfCost_relabel] using codecOneHot_cost (Fin (2 * s + 1)))
  have hcell := codecCnfCost_flatMap_le (List.finRange M.k)
    (fun i => (List.finRange (2 * s + 1)).map fun j =>
      [(CodecBit.work (M := M) (n := n) i j 0, false), (CodecBit.work i j 1, false)])
    (3 * (2 * s + 1)) (by
      intro i _
      simp [codecCnfCost, List.map_map, Function.comp_def]
      omega)
  simp only [Fintype.card_option, Fintype.card_fin, List.length_finRange] at hinput hstate hhead hcell
  simp only [codecValidity, codecCnfCost_append, codecCnfCost_relabel]
  have hsummary : codecCnfCost
      [[(CodecBit.summary (M := M) (n := n) (s := s) false, false),
        (CodecBit.summary true, false)]] = 3 := rfl
  rw [hsummary]
  omega

/-- The raw validity cost is bounded quadratically in `s+n+2`.

**Proof sketch.** Bound the input track by the common base and each work track by
twice that base. The state count is a machine constant; collect the quadratic terms. -/
private theorem codecValidity_cost (M : FinTM Bool) (n s : ℕ) :
    codecCnfCost (codecValidity M n s) ≤ codecValidityCoefficient M * (s + n + 2) ^ 2 := by
  let u := s + n + 2
  let q := Fintype.card M.State + 1
  have hu : 2 ≤ u := by omega
  have hu1 : 1 ≤ u ^ 2 := by nlinarith
  have hin : n + 2 ≤ u := by omega
  have hwork : 2 * s + 1 ≤ 2 * u := by omega
  have hi : (n + 2) + 1 + 3 * (n + 2) ^ 2 ≤ 5 * u ^ 2 := by
    have := Nat.pow_le_pow_left hin 2
    nlinarith
  have hw : (2 * s + 1) + 1 + 3 * (2 * s + 1) ^ 2 ≤ 15 * u ^ 2 := by
    have := Nat.pow_le_pow_left hwork 2
    nlinarith
  have hq : q + 1 + 3 * q ^ 2 ≤ (q + 1 + 3 * q ^ 2) * u ^ 2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (q + 1 + 3 * q ^ 2) hu1
  have hc : 3 * (2 * s + 1) ≤ 6 * u ^ 2 := by nlinarith
  have ht := codecValidity_cost_raw M n s
  have hh := Nat.mul_le_mul_left M.k hw
  have hs := Nat.mul_le_mul_left M.k hc
  change codecCnfCost (codecValidity M n s) ≤ (3 * q ^ 2 + q + 9 + 21 * M.k) * u ^ 2
  change codecCnfCost (codecValidity M n s) ≤
    _ + (q + 1 + 3 * q ^ 2) + _ + _ + 3 at ht
  nlinarith

/-- The padding contributes at most two cost units per code position. -/
private theorem codecPadding_cost (first L : ℕ) : codecCnfCost (codecPadding first L) ≤ 2 * L := by
  simp [codecPadding, codecCnfCost, List.map_map, Function.comp_def]
  omega

/-- All validity literals lie strictly inside the prescribed code width. -/
private theorem configurationValidity_literals (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    ∀ cl ∈ configurationValidity M C n s, ∀ l ∈ cl, l.1 < C * (s + n + 1) := by
  have hfit := codecBit_card_le M n s C hC
  intro cl hcl l hl
  simp only [configurationValidity, List.mem_append] at hcl
  rcases hcl with hcl | hcl
  · simp only [CNF.relabel, List.mem_map] at hcl
    obtain ⟨c, _, rfl⟩ := hcl
    simp only [CNF.Clause.relabel, List.mem_map] at hl
    obtain ⟨b, _, rfl⟩ := hl
    exact (Fintype.equivFin (CodecBit M n s) b.1).isLt.trans_le hfit
  · simp only [codecPadding, List.mem_map, List.mem_range] at hcl
    obtain ⟨j, hj, rfl⟩ := hcl
    simp only [List.mem_singleton] at hl
    subst l
    dsimp
    omega

/-- The validity CNF's variable count is inside the code width. -/
private theorem configurationValidity_numVars (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (configurationValidity M C n s).numVars ≤ C * (s + n + 1) := by
  simpa using codecCnf_numVars (configurationValidity M C n s) id _
    (configurationValidity_literals M C n s hC)

/-- A preliminary serialized-size ledger, before choosing the common theorem constant. -/
private theorem configurationValidity_size_raw (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (CNF.serialize (configurationValidity M C n s)).length ≤
      (codecValidityCoefficient M * (s + n + 2) ^ 2 + 2 * (C * (s + n + 1))) *
        (C * (s + n + 1) + 3) + 1 := by
  have h := codecCnf_serialize (configurationValidity M C n s) id _
    (configurationValidity_literals M C n s hC)
  simp only [CNF.relabel_id] at h
  have hw : codecCnfCost (configurationValidity M C n s) ≤
      codecValidityCoefficient M * (s + n + 2) ^ 2 + 2 * (C * (s + n + 1)) := by
    simpa only [configurationValidity, codecCnfCost_append, codecCnfCost_relabel] using
      Nat.add_le_add (codecValidity_cost M n s)
        (codecPadding_cost (Fintype.card (CodecBit M n s)) (C * (s + n + 1)))
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hw) 1)

/-- The acceptance CNF has two unit clauses and all its indices are inside the code. -/
private theorem configurationAcceptance_bounds (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (configurationAcceptance M n s).numVars ≤ C * (s + n + 1) ∧
    (CNF.serialize (configurationAcceptance M n s)).length ≤ 4 * (C * (s + n + 1) + 3) + 1 := by
  have hfit := codecBit_card_le M n s C hC
  have hb : ∀ cl ∈ codecAcceptance M n s, ∀ l ∈ cl,
      (Fintype.equivFin (CodecBit M n s) l.1).val < C * (s + n + 1) :=
    fun _ _ l _ => (Fintype.equivFin (CodecBit M n s) l.1).isLt.trans_le hfit
  refine ⟨codecCnf_numVars (codecAcceptance M n s) _ _ hb, ?_⟩
  have h := codecCnf_serialize (codecAcceptance M n s)
    (fun b => (Fintype.equivFin (CodecBit M n s) b).val) (C * (s + n + 1)) hb
  simpa only [codecAcceptance, codecCnfCost, List.map_cons, List.map_nil, List.length_cons,
    List.length_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd] using h

/-- Normalize the validity serialization ledger to one cubic polynomial.

**Proof sketch.** Write `u=t+1≥2`. The cost is at most `(A+2)Cu²`, and every
serialized index costs at most `3Cu`. The extra final bit is covered by one
more copy of `C²u³`. -/
private theorem codec_size_normalize (A C t : ℕ) (hC : 1 ≤ C) (ht : 1 ≤ t) :
    (A * (t + 1) ^ 2 + 2 * (C * t)) * (C * t + 3) + 1 ≤
      (3 * A + 7) * C ^ 2 * (t + 1) ^ 3 := by
  have hu : t ≤ (t + 1) ^ 2 := by nlinarith
  have hA : A ≤ A * C := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left A hC
  have hcost : A * (t + 1) ^ 2 + 2 * (C * t) ≤ (A + 2) * C * (t + 1) ^ 2 := by
    have h1 := Nat.mul_le_mul_right ((t + 1) ^ 2) hA
    have h2 := Nat.mul_le_mul_left (2 * C) hu
    nlinarith
  have hindex : C * t + 3 ≤ 3 * C * (t + 1) := by nlinarith
  have hfinal : 1 ≤ C ^ 2 * (t + 1) ^ 3 := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by positivity))
  calc
    _ ≤ ((A + 2) * C * (t + 1) ^ 2) * (3 * C * (t + 1)) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul hcost hindex) 1
    _ ≤ ((A + 2) * C * (t + 1) ^ 2) * (3 * C * (t + 1)) + C ^ 2 * (t + 1) ^ 3 :=
      Nat.add_le_add_left hfinal _
    _ = _ := by ring

/-- Validity has a polynomial serialized-size bound uniform in the width coefficient. -/
private theorem configurationValidity_size (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (CNF.serialize (configurationValidity M C n s)).length ≤
      (3 * codecValidityCoefficient M + 7) * C ^ 2 * (s + n + 2) ^ 3 := by
  have hpos : 1 ≤ C := by unfold codecCoefficient at hC; omega
  have h := codec_size_normalize (codecValidityCoefficient M) C (s + n + 1) hpos (by omega)
  simpa only [show s + n + 1 + 1 = s + n + 2 by omega] using
    (configurationValidity_size_raw M C n s hC).trans h

/-- Acceptance also fits a cubic ledger, uniformly over all sufficient code widths. -/
private theorem configurationAcceptance_size (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (CNF.serialize (configurationAcceptance M n s)).length ≤
      13 * C ^ 2 * (s + n + 2) ^ 3 := by
  have hpos : 1 ≤ C := by unfold codecCoefficient at hC; omega
  have hi : C * (s + n + 1) + 3 ≤ 3 * C * (s + n + 2) := by nlinarith
  have hm : C * (s + n + 2) ≤ C ^ 2 * (s + n + 2) ^ 3 :=
    Nat.mul_le_mul (Nat.le_pow (by decide)) (Nat.le_pow (by decide))
  have hp : 1 ≤ C ^ 2 * (s + n + 2) ^ 3 := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by positivity))
  calc
    _ ≤ 4 * (C * (s + n + 1) + 3) + 1 := (configurationAcceptance_bounds M C n s hC).2
    _ ≤ 4 * (3 * C * (s + n + 2)) + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left 4 hi) 1
    _ = 12 * (C * (s + n + 2)) + 1 := by ring
    _ ≤ 12 * (C ^ 2 * (s + n + 2) ^ 3) + C ^ 2 * (s + n + 2) ^ 3 :=
      Nat.add_le_add (Nat.mul_le_mul_left 12 hm) hp
    _ = _ := by ring

/-- A fixed-arity Boolean check becomes a CNF of bounded cost after arbitrary wiring.
This applies the chapter-2 universality theorem to a single gate, never to a row. -/
private theorem codecLocalCheck {α : Type} [Inhabited α] (arity : ℕ)
    (wire : Fin arity → α) (f : (Fin arity → Bool) → Bool) :
    ∃ φ : CNF α, codecCnfCost φ ≤ 2 ^ arity * (arity + 1) ∧
      ∀ a : α → Bool, φ.eval a = f (fun i => a (wire i)) := by
  classical
  obtain ⟨ψ, _, hlen, hwidth, heval⟩ := exists_cnf_boolFun arity f
  let wiring (j : ℕ) : α := if h : j < arity then wire ⟨j, h⟩ else default
  refine ⟨ψ.relabel wiring, ?_, ?_⟩
  · rw [codecCnfCost_relabel]
    have h := codecCnfCost_flatMap_le ψ (fun c => [c]) (arity + 1) (by
      intro c hc
      simpa [codecCnfCost] using Nat.add_le_add_right (hwidth c hc) 1)
    simpa using h.trans (Nat.mul_le_mul_right (arity + 1) hlen)
  · intro a
    rw [CNF.eval_relabel, heval]
    congr 1
    funext i
    simp [wiring, i.isLt]

/-- Positions jointly guarded by one local transition check. -/
private abbrev CodecPositions (M : FinTM Bool) (n s : ℕ) :=
  Fin (n + 2) × (Fin M.k → Fin (2 * s + 1))

/-- The joint head-position enumeration has polynomial size for a fixed machine.

**Proof sketch.** There are `n+2` input positions and `2s+1` independent positions
for each work head. Bound these factors by `u` and `2u`, with `u=s+n+2`. -/
private theorem codecPositions_card_le (M : FinTM Bool) (n s : ℕ) :
    Fintype.card (CodecPositions M n s) ≤
      2 ^ M.k * (s + n + 2) ^ (M.k + 1) := by
  simp only [CodecPositions, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  calc
    (n + 2) * (2 * s + 1) ^ M.k ≤
        (s + n + 2) * (2 * (s + n + 2)) ^ M.k :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
    _ = _ := by rw [mul_pow, pow_succ]; ring

/-- Source and target bit tracks for a pair of finite rows. -/
private def codecPairBits {M : FinTM Bool} {n s : ℕ}
    (r t : CodecRow M n s) (p : Bool × CodecBit M n s) : Bool :=
  if p.1 then codecRowBits t p.2 else codecRowBits r p.2

/-- Place the target coordinates after one full padded source block. -/
private noncomputable def codecPairWire (M : FinTM Bool) (C n s : ℕ)
    (p : Bool × CodecBit M n s) : ℕ :=
  (if p.1 then C * (s + n + 1) else 0) + (Fintype.equivFin (CodecBit M n s) p.2).val

/-- Every pair coordinate lies inside the concatenation of the two code blocks. -/
private theorem codecPairWire_lt (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (p : Bool × CodecBit M n s) :
    codecPairWire M C n s p < 2 * (C * (s + n + 1)) := by
  have h := (Fintype.equivFin (CodecBit M n s) p.2).isLt.trans_le
    (codecBit_card_le M n s C hC)
  unfold codecPairWire
  cases p.1 <;> simp only [Bool.false_eq_true, if_false, if_true, zero_add] <;> omega

/-- Numbered pair coordinates read exactly the source or target finite-row bit. -/
private theorem configurationCodec_pair_get (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (c : Cfg M.k Bool M.State x) (d : Cfg M.k Bool M.State y)
    (p : Bool × CodecBit M n s) :
    (configurationCodec M C n s x c ++ configurationCodec M C n s y d).getD
        (codecPairWire M C n s p) false =
      codecPairBits (codecRowOf M n s x hx c) (codecRowOf M n s y hy d) p := by
  have hfit := codecBit_card_le M n s C hC
  have hi := (Fintype.equivFin (CodecBit M n s) p.2).isLt.trans_le hfit
  rcases p with ⟨side, bit⟩
  cases side
  · simp only [codecPairWire, Bool.false_eq_true, if_false, zero_add, codecPairBits]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simpa only [configurationCodec_length] using hi),
      ← List.getD_eq_getElem?_getD]
    simp only [configurationCodec, dif_pos hx, codecWord_get _ _ hfit]
  · simp only [codecPairWire, if_true, codecPairBits]
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [configurationCodec_length]; omega),
      configurationCodec_length, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
    simp only [configurationCodec, dif_pos hy, codecWord_get _ _ hfit]

/-- Two clauses per input bit require equality of the carried input contents. -/
private def codecInputEquality (M : FinTM Bool) (n s : ℕ) : CNF (Bool × CodecBit M n s) :=
  (List.finRange n).flatMap fun i =>
    [[((false, .input i), false), ((true, .input i), true)],
      [((false, .input i), true), ((true, .input i), false)]]

/-- The input-equality conjunct compares exactly the input-content fields. -/
private theorem codecInputEquality_eval (M : FinTM Bool) (n s : ℕ) (r t : CodecRow M n s) :
    (codecInputEquality M n s).eval (codecPairBits r t) = true ↔ r.input = t.input := by
  have hbit (i : Fin n) : CNF.eval (codecPairBits r t)
      [[((false, CodecBit.input i), false), ((true, CodecBit.input i), true)],
        [((false, CodecBit.input i), true), ((true, CodecBit.input i), false)]] = true ↔
        r.input i = t.input i := by
    cases hr : r.input i <;> cases ht : t.input i <;>
      simp [CNF.eval, CNF.Clause.eval, codecPairBits, codecRowBits, hr, ht]
  simp only [codecInputEquality, codecCnf_eval_flatMap, List.mem_finRange, forall_const, hbit]
  exact funext_iff.symm

/-- Input equality costs six units per input position: two clauses of width two. -/
private theorem codecInputEquality_cost (M : FinTM Bool) (n s : ℕ) :
    codecCnfCost (codecInputEquality M n s) ≤ 6 * n := by
  have h := codecCnfCost_flatMap_le (List.finRange n)
    (fun i => [[((false, CodecBit.input (M := M) (s := s) i), false),
        ((true, .input i), true)], [((false, .input i), true), ((true, .input i), false)]])
    6 (fun _ _ => by simp [codecCnfCost])
  simpa only [List.length_finRange, Nat.mul_comm] using h

/-- Number the cross-input rejection conjunct in the two padded code blocks. -/
private noncomputable def configurationInputEquality (M : FinTM Bool) (C n s : ℕ) : CNF ℕ :=
  (codecInputEquality M n s).relabel (codecPairWire M C n s)

/-- Distinct carried inputs fail the equality conjunct, independently of transition checks. -/
private theorem configurationInputEquality_reject (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : x ≠ y) (c : Cfg M.k Bool M.State x) (d : Cfg M.k Bool M.State y) :
    (configurationInputEquality M C n s).eval
      (fun v => (configurationCodec M C n s x c ++ configurationCodec M C n s y d).getD v false)
      = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [configurationInputEquality, CNF.eval_relabel, Function.comp_def,
    configurationCodec_pair_get M C n s hC x y hx hy c d, codecInputEquality_eval] at h
  exact hxy (codecRowOf_input_eq M n s x y hx hy c d h)

/-- The cross-input equality conjunct has bounded indices and polynomial serialization. -/
private theorem configurationInputEquality_bounds (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (configurationInputEquality M C n s).numVars ≤ 2 * (C * (s + n + 1)) ∧
    (CNF.serialize (configurationInputEquality M C n s)).length ≤
      6 * n * (2 * (C * (s + n + 1)) + 3) + 1 := by
  have hb : ∀ cl ∈ codecInputEquality M n s, ∀ l ∈ cl,
      codecPairWire M C n s l.1 < 2 * (C * (s + n + 1)) :=
    fun _ _ l _ => codecPairWire_lt M C n s hC l.1
  refine ⟨codecCnf_numVars (codecInputEquality M n s) _ _ hb, ?_⟩
  exact (codecCnf_serialize (codecInputEquality M n s) _ _ hb).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (codecInputEquality_cost M n s)) 1)

/-- Equal windowed codes have equal successor vertices, through the public quotient bridge.
This is the deterministic instance of `NDTM.coreSum_stepWith`, not a second step proof. -/
private theorem configurationCodec_step_congr (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x : List Bool) (hx : x.length = n)
    (c d : Cfg M.k Bool M.State x) (hc : c.InWindow s) (hd : d.InWindow s)
    (h : configurationCodec M C n s x c = configurationCodec M C n s x d) :
    NDTM.coreSum (M.tm.step c) = NDTM.coreSum (M.tm.step d) := by
  have hv := (configurationCodec_eq_iff M C n s hC x hx c d hc hd).mp h
  exact NDTM.coreSum_stepWith M.tm.toNDTM false hv

/-- Beyond four, the exponential pays for a quadratic coefficient. -/
private theorem codec_square_le_pow (C : ℕ) (hC : 4 ≤ C) : C ^ 2 ≤ 2 ^ C := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hC
  induction t with
  | zero => norm_num
  | succ t ih =>
    have hi := ih (by omega)
    calc
      (4 + (t + 1)) ^ 2 ≤ 2 * (4 + t) ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ (4 + t) := Nat.mul_le_mul_left 2 hi
      _ = 2 ^ (4 + (t + 1)) := by
        rw [show 4 + (t + 1) = (4 + t) + 1 by omega, pow_succ]
        ring

/-- One constant can simultaneously dominate the width and the polynomial ledgers.

**Proof sketch.** Choose `C` at least four, the requested width coefficient, the
polynomial exponent, and `B·2^d`. Then `B·C·2^d ≤ C² ≤ 2^C`, so
`B·C ≤ 2^(C-d) ≤ u^(C-d)` for every `u≥2`. Multiply by `C·u^d`. -/
private theorem codec_absorb (B d K : ℕ) :
    ∃ C : ℕ, 0 < C ∧ K ≤ C ∧ ∀ u : ℕ, 2 ≤ u →
      B * C ^ 2 * u ^ d ≤ C * u ^ C := by
  let C := max 4 (max K (max d (B * 2 ^ d)))
  have h4 : 4 ≤ C := le_max_left _ _
  have hK : K ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hd : d ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hB : B * 2 ^ d ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, by omega, hK, fun u hu => ?_⟩
  have hpow : B * C ≤ 2 ^ (C - d) := by
    have hbig : (B * C) * 2 ^ d ≤ 2 ^ C := by
      calc
        _ = (B * 2 ^ d) * C := by ring
        _ ≤ C * C := Nat.mul_le_mul_right C hB
        _ ≤ 2 ^ C := by simpa [pow_two] using codec_square_le_pow C h4
    have hsplit : 2 ^ C = 2 ^ (C - d) * 2 ^ d := by
      rw [← pow_add, Nat.sub_add_cancel hd]
    rw [hsplit] at hbig
    have hp : 0 < 2 ^ d := by positivity
    nlinarith
  calc
    B * C ^ 2 * u ^ d = C * ((B * C) * u ^ d) := by ring
    _ ≤ C * (2 ^ (C - d) * u ^ d) :=
      Nat.mul_le_mul_left C (Nat.mul_le_mul_right _ hpow)
    _ ≤ C * (u ^ (C - d) * u ^ d) :=
      Nat.mul_le_mul_left C (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hu _))
    _ = C * u ^ C := by rw [← pow_add, Nat.sub_add_cancel hd]


/-- Exact window markers recover integer positions without clamping. -/
private theorem codec_posCode_eq_iff (s : ℕ) (z : ℤ) (hz : |z| ≤ s)
    (j : Fin (2 * s + 1)) :
    MultiTapeTM.ConfigCount.posCode s z = j ↔ z = (j.val : ℤ) - s := by
  constructor
  · intro h
    apply MultiTapeTM.ConfigCount.posCode_injOn s hz
    · have hj := j.isLt
      rw [abs_le]
      omega
    · simpa only [codec_posCode] using h
  · rintro rfl
    exact codec_posCode s j

/-- Observe the row coordinates using exact integer head markers. An exterior head
has no true marker; this prevents clamping from admitting an overflowing step. -/
private def codecObserve (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) : CodecBit M n s → Bool
  | .work i j b =>
      if b.val = 0 then decide (c.workTapes i ((j.val : ℤ) - s) = some false)
      else if b.val = 1 then decide (c.workTapes i ((j.val : ℤ) - s) = some true)
      else decide (c.workTapePos i = (j.val : ℤ) - s)
  | b => codecRowBits (codecRowOf M n s x hx c) b

/-- On windowed configurations, exact observations agree with the padded codec's row. -/
private theorem codecObserve_eq (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) (hc : c.InWindow s) :
    codecObserve M n s x hx c = codecRowBits (codecRowOf M n s x hx c) := by
  funext b
  cases b with
  | work i j b =>
    simp only [codecObserve, codecRowBits, codecRowOf, MultiTapeTM.ConfigCount.coreCode]
    by_cases h0 : b.val = 0
    · simp only [h0, if_true]
    · by_cases h1 : b.val = 1
      · simp only [h1, if_true]
      · simp only [h0, h1, if_false, codec_posCode_eq_iff s _ (hc.1 i)]
  | _ => rfl

/-- Exact observations depend only on the public configuration-graph vertex. -/
private theorem codecObserve_congr (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c d : Cfg M.k Bool M.State x)
    (h : NDTM.coreSum c = NDTM.coreSum d) :
    codecObserve M n s x hx c = codecObserve M n s x hx d := by
  have hcore := congrArg Prod.fst h
  have hout := congrArg Prod.snd h
  change outSummary c.output = outSummary d.output at hout
  simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core, Prod.mk.injEq] at hcore
  rcases hcore with ⟨hst, hip, hwt, hwp⟩
  funext b
  cases b <;> simp only [codecObserve, codecRowBits, codecRowOf,
    MultiTapeTM.ConfigCount.coreCode, hst, hip, hwt, hwp, hout]

/-- Applying a transition cannot write outside a window containing its old heads. -/
private theorem codec_step_blank (M : FinTM Bool) (s : ℕ) (x : List Bool)
    (c : Cfg M.k Bool M.State x) (hc : c.InWindow s) :
    ∀ i z, (s : ℤ) < |z| → (M.tm.step c).workTapes i z = none := by
  intro i z hz
  cases hs : c.state with
  | none => simpa only [MultiTapeTM.step, hs] using hc.2 i z hz
  | some q =>
    have hzhead : z ≠ c.workTapePos i := by
      intro he
      rw [he] at hz
      exact (not_lt_of_ge (hc.1 i)) hz
    simp only [MultiTapeTM.step, hs, Action.apply]
    cases hw : ((M.tm.tr q c.inputSymbol c.workTapeSymbols).workTapes i).1 <;>
      simp [Function.update, hzhead, hc.2 i z hz]

/-- Equality of exact successor observations with a valid target is adjacency.

**Proof sketch.** The target's true head markers force each successor head into
the window. All exterior cells stay blank because writes occur at old heads.
The public finite-core injection then identifies the vertices. Conversely,
vertex equality preserves every observation. -/
private theorem codecObserve_step_iff (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c d : Cfg M.k Bool M.State x)
    (hc : c.InWindow s) (hd : d.InWindow s) :
    codecObserve M n s x hx (M.tm.step c) = codecRowBits (codecRowOf M n s x hx d) ↔
      NDTM.coreSum (M.tm.step c) = NDTM.coreSum d := by
  constructor
  · intro h
    have hwin : (M.tm.step c).InWindow s := by
      refine ⟨fun i => ?_, codec_step_blank M s x c hc⟩
      let j := (codecRowOf M n s x hx d).heads i
      have he := congrFun h (.work i j 2)
      have heq : (M.tm.step c).workTapePos i = (j.val : ℤ) - s := by
        apply of_decide_eq_true
        simpa [codecObserve, codecRowBits, j] using he
      rw [heq, abs_le]
      have hj := j.isLt
      omega
    rw [codecObserve_eq M n s x hx _ hwin] at h
    exact (codecRowOf_eq_iff M n s x hx _ d hwin hd).mp (codecRowBits_injective h)
  · intro h
    exact (codecObserve_congr M n s x hx _ d h).trans (codecObserve_eq M n s x hx d hd)

/-- A canonical representative of each of the three output summaries. -/
private def codecSummaryWord : OutSummary → List Bool
  | .empty => []
  | .accept => [true]
  | .dead => [false]

/-- The chosen representative has the prescribed output summary. -/
private theorem codecSummaryWord_summary (o : OutSummary) :
    outSummary (codecSummaryWord o) = o := by cases o <;> rfl

/-- Output histories may be normalized before taking a step, through the public
`coreSum_stepWith` bridge; the exact observed successor bits are unchanged. -/
private theorem codecObserve_step_normalize (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) :
    codecObserve M n s x hx (M.tm.step c) = codecObserve M n s x hx
      (M.tm.step { c with output := codecSummaryWord (outSummary c.output) }) := by
  apply codecObserve_congr
  apply NDTM.coreSum_stepWith M.tm.toNDTM false
  exact Prod.ext rfl (codecSummaryWord_summary (outSummary c.output)).symm

/-- The finite transition-table cases: control, scanned input, and scanned work symbols. -/
private abbrev CodecCase (M : FinTM Bool) :=
  Option M.State × Option Bool × (Fin M.k → Option Bool)

/-- Include a silent identity action for the halted case. -/
private def codecAction (M : FinTM Bool) (q : CodecCase M) : Action M.k Bool M.State :=
  match q.1 with
  | none => ⟨0, fun _ => (none, 0), none, none⟩
  | some st => M.tm.tr st q.2.1 q.2.2

/-- The case action computes the native step, including halted self-edges. -/
private theorem codecAction_apply (M : FinTM Bool) (x : List Bool)
    (c : Cfg M.k Bool M.State x) :
    (codecAction M (c.state, c.inputSymbol, c.workTapeSymbols)).apply c = M.tm.step c := by
  cases hs : c.state with
  | none =>
    apply Cfg.ext <;> simp [codecAction, hs, Action.apply, MultiTapeTM.step]
  | some q => simp only [codecAction, MultiTapeTM.step, hs]

/-- The constant number of Boolean ports read by a single guarded update gate. -/
private inductive CodecPort (M : FinTM Bool)
  | state | inputHead | inputSymbol
  | workHead : Fin M.k → CodecPort M
  | workSymbol : Fin M.k → Bool → CodecPort M
  | summary : Bool → CodecPort M
  | oldBit | newBit
  deriving Fintype, DecidableEq

/-- Gate arity is independent of the input length and window radius. -/
private theorem codecPort_card (M : FinTM Bool) : Fintype.card (CodecPort M) = 3 * M.k + 7 := by
  rw [← Fintype.card_congr (CodecPort.proxyTypeEquiv M)]
  simp
  ring

/-- A two-flag decoder for optional work symbols, with an arbitrary value on `11`. -/
private def codecReadSymbol (f t : Bool) : Option Bool :=
  if t then some true else if f then some false else none

/-- The symbol decoder recovers every legal two-flag encoding. -/
private theorem codecReadSymbol_flags (v : Option Bool) :
    codecReadSymbol (decide (v = some false)) (decide (v = some true)) = v := by
  cases v with
  | none => rfl
  | some b => cases b <;> rfl

/-- Decode the two summary flags; `11` is irrelevant on encoded configurations. -/
private def codecReadSummary (acc dead : Bool) : OutSummary :=
  if dead then .dead else if acc then .accept else .empty

/-- Summary decoding recovers the three canonical flag patterns. -/
private theorem codecReadSummary_flags (o : OutSummary) :
    codecReadSummary (decide (o = .accept)) (decide (o = .dead)) = o := by
  cases o <;> rfl

/-- Wire one input-symbol port; boundary cases ignore the arbitrary fallback wire. -/
private def codecInputWire (M : FinTM Bool) (n s : ℕ) (p : Fin (n + 2)) : CodecBit M n s :=
  if h : 0 < p.val ∧ p.val ≤ n then .input ⟨p.val - 1, by omega⟩ else .summary false

/-- The physical input boundaries read blank; interior positions read the wired bit. -/
private def codecInputRead {n : ℕ} (p : Fin (n + 2)) (b : Bool) : Option Bool :=
  if 0 < p.val ∧ p.val ≤ n then some b else none

/-- Wire the guard, scanned symbols, summary, and one old/new bit pair. -/
private def codecGateWire (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (q : CodecCase M) (b : CodecBit M n s) : CodecPort M → Bool × CodecBit M n s
  | .state => (false, .state q.1)
  | .inputHead => (false, .inputHead p.1)
  | .inputSymbol => (false, codecInputWire M n s p.1)
  | .workHead i => (false, .work i (p.2 i) 2)
  | .workSymbol i t => (false, .work i (p.2 i) (if t then 1 else 0))
  | .summary t => (false, .summary t)
  | .oldBit => (false, b)
  | .newBit => (true, b)

/-- A joint position/table guard. All quantification is over the machine's fixed tapes. -/
private def codecGuard (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (q : CodecCase M) (a : CodecPort M → Bool) : Prop :=
  a .state = true ∧ a .inputHead = true ∧ (∀ i, a (.workHead i) = true) ∧
    codecInputRead p.1 (a .inputSymbol) = q.2.1 ∧
    ∀ i, codecReadSymbol (a (.workSymbol i false)) (a (.workSymbol i true)) = q.2.2 i

/-- Under the input-position guard, the input-symbol port reads the actual input.

**Proof sketch.** An interior marker selects its predecessor-indexed input bit.
Either boundary instead gives blank, exactly as in the native input reader. -/
private theorem codecInputRead_wire (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) (p : Fin (n + 2))
    (hp : (codecRowOf M n s x hx c).inputHead = p) :
    codecInputRead p (codecRowBits (codecRowOf M n s x hx c) (codecInputWire M n s p)) =
      c.inputSymbol := by
  have hv : c.inputPos.val = p.val := congrArg Fin.val hp
  by_cases hi : 0 < p.val ∧ p.val ≤ n
  · have h0 : c.inputPos ≠ 0 := by
      intro h
      have hz : c.inputPos.val = 0 := Fin.val_eq_zero_iff.mpr h
      omega
    have hn : c.inputPos.val ≠ x.length + 1 := by omega
    have hlt : c.inputPos.val - 1 < x.length := by omega
    simp only [codecInputRead, if_pos hi, codecInputWire, dif_pos hi, codecRowBits,
      codecRowOf, Cfg.inputSymbol, dif_neg h0, dif_neg hn]
    simp [List.getD_eq_getElem?_getD, ← hv, hlt]
  · have hboundary : c.inputPos = 0 ∨ c.inputPos.val = x.length + 1 := by
      have hp := p.isLt
      by_cases hz : c.inputPos.val = 0
      · exact Or.inl (Fin.ext hz)
      · exact Or.inr (by omega)
    rcases hboundary with h0 | hn
    · simp only [codecInputRead, if_neg hi, Cfg.inputSymbol, dif_pos h0]
    · simp only [codecInputRead, if_neg hi, Cfg.inputSymbol, dif_pos hn]
      split <;> rfl

/-- On encoded rows, the gate guard tests exactly the selected positions and reads. -/
private theorem codecGuard_rows (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (q : CodecCase M) (b : CodecBit M n s) (r t : CodecRow M n s) :
    codecGuard M n s p q (codecPairBits r t ∘ codecGateWire M n s p q b) ↔
      r.state = q.1 ∧ r.inputHead = p.1 ∧ (∀ i, r.heads i = p.2 i) ∧
      codecInputRead p.1 (codecRowBits r (codecInputWire M n s p.1)) = q.2.1 ∧
      ∀ i, r.symbols i (p.2 i) = q.2.2 i := by
  simp [codecGuard, codecGateWire, codecPairBits, codecRowBits,
    codecReadSymbol_flags]

/-- Native meaning of a true guard on a windowed configuration.

**Proof sketch.** The one-hot markers identify all head positions. Decode the
work-symbol flags at those positions, and use the carried input bit except at
the two blank boundaries. These are exactly the machine's scanned symbols. -/
private theorem codecGuard_spec (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) (hc : c.InWindow s)
    (t : CodecRow M n s) (p : CodecPositions M n s) (q : CodecCase M) (b : CodecBit M n s) :
    codecGuard M n s p q
      (codecPairBits (codecRowOf M n s x hx c) t ∘ codecGateWire M n s p q b) ↔
      c.state = q.1 ∧ (codecRowOf M n s x hx c).inputHead = p.1 ∧
      (∀ i, c.workTapePos i = ((p.2 i).val : ℤ) - s) ∧
      c.inputSymbol = q.2.1 ∧ c.workTapeSymbols = q.2.2 := by
  rw [codecGuard_rows]
  have hh (i : Fin M.k) : (codecRowOf M n s x hx c).heads i = p.2 i ↔
      c.workTapePos i = ((p.2 i).val : ℤ) - s :=
    codec_posCode_eq_iff s _ (hc.1 i) _
  constructor
  · rintro ⟨hst, hip, hwp, hin, hws⟩
    have hp := fun i => (hh i).mp (hwp i)
    refine ⟨hst, hip, hp, ?_, ?_⟩
    · rwa [codecInputRead_wire M n s x hx c _ hip] at hin
    · funext i
      simpa only [codecRowOf, MultiTapeTM.ConfigCount.coreCode,
        Cfg.workTapeSymbols, hp i] using hws i
  · rintro ⟨hst, hip, hwp, hin, hws⟩
    refine ⟨hst, hip, fun i => (hh i).mpr (hwp i), ?_, ?_⟩
    · simpa only [codecInputRead_wire M n s x hx c _ hip] using hin
    · intro i
      simpa only [codecRowOf, MultiTapeTM.ConfigCount.coreCode,
        Cfg.workTapeSymbols, hwp i] using congrFun hws i

/-- One output bit of the selected action: copy unmarked cells, write at old
heads, shift markers, rewrite the state, and update the output summary. -/
private def codecExpected (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (act : Action M.k Bool M.State) (a : CodecPort M → Bool) : CodecBit M n s → Bool
  | .input _ => a .oldBit
  | .inputHead j => decide (moveInputPos p.1 act.inputTape = j)
  | .state st => decide (act.state = st)
  | .work i j b =>
      if b.val = 0 ∨ b.val = 1 then
        if p.2 i = j then
          match (act.workTapes i).1 with
          | none => a .oldBit
          | some v => decide (v = some (decide (b.val = 1)))
        else a .oldBit
      else decide (((p.2 i).val : ℤ) - s + ((act.workTapes i).2 : ℤ) = (j.val : ℤ) - s)
  | .summary dead => decide
      (outSummary (codecSummaryWord (codecReadSummary (a (.summary false)) (a (.summary true))) ++
        act.output.toList) = if dead then .dead else .accept)

/-- The guarded single-bit predicate compiled by per-gate Boolean universality. -/
private noncomputable def codecGate (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (q : CodecCase M) (b : CodecBit M n s) (a : CodecPort M → Bool) : Bool := by
  classical
  exact decide (codecGuard M n s p q a → a .newBit = codecExpected M n s p (codecAction M q) a b)

/-- Each expected bit is the exact bit of the action applied to the canonical
output representative; only the guard's positions and a constant number of bits enter.

**Proof sketch.** Input content is unchanged, state and input-head markers follow
the action, and the two work-symbol flags copy except at a written head cell.
The integer head equation retains an exterior move rather than clamping it.
The summary ports supply the canonical output word for the append table. -/
private theorem codecExpected_apply (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) (t : CodecRow M n s)
    (p : CodecPositions M n s) (q : CodecCase M) (act : Action M.k Bool M.State)
    (hp : (codecRowOf M n s x hx c).inputHead = p.1)
    (hh : ∀ i, c.workTapePos i = ((p.2 i).val : ℤ) - s) (b : CodecBit M n s) :
    codecExpected M n s p act
      (codecPairBits (codecRowOf M n s x hx c) t ∘ codecGateWire M n s p q b) b =
    codecObserve M n s x hx
      (act.apply { c with output := codecSummaryWord (outSummary c.output) }) b := by
  cases b with
  | input i => rfl
  | inputHead j =>
    subst n
    have hpos : c.inputPos = p.1 := hp
    change decide (moveInputPos p.1 act.inputTape = j) =
      decide (moveInputPos c.inputPos act.inputTape = j)
    rw [hpos]
  | state st => rfl
  | summary d =>
    simp [codecExpected, codecObserve, codecGateWire, codecPairBits, codecRowBits,
      codecRowOf, Action.apply, codecReadSummary_flags]
  | work i j b =>
    have hcell : ((j.val : ℤ) - s = c.workTapePos i) ↔ p.2 i = j := by
      rw [hh i]
      constructor
      · intro h
        apply Fin.ext
        omega
      · rintro h
        rw [h]
    fin_cases b <;>
      simp only [codecExpected, codecObserve, Function.comp_apply, codecGateWire,
        codecPairBits, Bool.false_eq_true, if_false, codecRowBits, codecRowOf,
        MultiTapeTM.ConfigCount.coreCode, Action.apply]
    · rcases Option.eq_none_or_eq_some ((act.workTapes i).1) with hw | ⟨v, hw⟩ <;>
        by_cases hj : p.2 i = j <;>
        simp [hw, hj, Function.update, hcell]
    · rcases Option.eq_none_or_eq_some ((act.workTapes i).1) with hw | ⟨v, hw⟩ <;>
        by_cases hj : p.2 i = j <;>
        simp [hw, hj, Function.update, hcell]
    · simp [hh i]

/-- A true transition guard makes its expected bit the actual successor bit.
Output normalization is justified by `NDTM.coreSum_stepWith`. -/
private theorem codecExpected_step (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c : Cfg M.k Bool M.State x) (hc : c.InWindow s)
    (t : CodecRow M n s) (p : CodecPositions M n s) (q : CodecCase M) (b : CodecBit M n s)
    (h : codecGuard M n s p q
      (codecPairBits (codecRowOf M n s x hx c) t ∘ codecGateWire M n s p q b)) :
    codecExpected M n s p (codecAction M q)
      (codecPairBits (codecRowOf M n s x hx c) t ∘ codecGateWire M n s p q b) b =
      codecObserve M n s x hx (M.tm.step c) b := by
  obtain ⟨hst, hip, hwp, hin, hws⟩ := (codecGuard_spec M n s x hx c hc t p q b).mp h
  have he : (c.state, c.inputSymbol, c.workTapeSymbols) = q :=
    Prod.ext hst (Prod.ext hin hws)
  have ha : (codecAction M q).apply { c with output := codecSummaryWord (outSummary c.output) } =
      M.tm.step { c with output := codecSummaryWord (outSummary c.output) } := by
    rw [← he]
    exact codecAction_apply M x { c with output := codecSummaryWord (outSummary c.output) }
  calc
    _ = codecObserve M n s x hx
        ((codecAction M q).apply { c with output := codecSummaryWord (outSummary c.output) }) b :=
      codecExpected_apply M n s x hx c t p q _ hip hwp b
    _ = codecObserve M n s x hx
        (M.tm.step { c with output := codecSummaryWord (outSummary c.output) }) b := by rw [ha]
    _ = _ := congrFun (codecObserve_step_normalize M n s x hx c).symm b

/-- Compile one finite-port gate, retaining a machine-only cost bound. -/
private theorem codecGate_cnf (M : FinTM Bool) (n s : ℕ) (p : CodecPositions M n s)
    (q : CodecCase M) (b : CodecBit M n s) :
    ∃ φ : CNF (Bool × CodecBit M n s),
      codecCnfCost φ ≤ 2 ^ (3 * M.k + 7) * (3 * M.k + 8) ∧
      ∀ a, φ.eval a = codecGate M n s p q b (a ∘ codecGateWire M n s p q b) := by
  letI : Inhabited (Bool × CodecBit M n s) := ⟨(false, .summary false)⟩
  let e := Fintype.equivFin (CodecPort M)
  obtain ⟨φ, hcost, heval⟩ := codecLocalCheck (Fintype.card (CodecPort M))
    (fun i => codecGateWire M n s p q b (e.symm i))
    (fun a => codecGate M n s p q b (fun port => a (e port)))
  refine ⟨φ, ?_, ?_⟩
  · simpa only [codecPort_card, Nat.add_assoc] using hcost
  · intro a
    simpa only [e.symm_apply_apply, Function.comp_def] using heval a

/-- Choose the per-gate CNF from the proved constant-arity universality bound. -/
private noncomputable def codecGateCNF (M : FinTM Bool) (n s : ℕ)
    (p : CodecPositions M n s) (q : CodecCase M) (b : CodecBit M n s) :
    CNF (Bool × CodecBit M n s) := (codecGate_cnf M n s p q b).choose

/-- The chosen gate formula has exactly its local semantics and machine-only cost. -/
private theorem codecGateCNF_spec (M : FinTM Bool) (n s : ℕ)
    (p : CodecPositions M n s) (q : CodecCase M) (b : CodecBit M n s) :
    codecCnfCost (codecGateCNF M n s p q b) ≤ 2 ^ (3 * M.k + 7) * (3 * M.k + 8) ∧
    ∀ a, (codecGateCNF M n s p q b).eval a =
      codecGate M n s p q b (a ∘ codecGateWire M n s p q b) :=
  (codecGate_cnf M n s p q b).choose_spec

/-- Enumerate the guarded positions, finite table cases, and updated coordinates. -/
private abbrev CodecGateIndex (M : FinTM Bool) (n s : ℕ) :=
  CodecPositions M n s × CodecCase M × CodecBit M n s

/-- Conjoin one constant-arity gate for each guarded coordinate update. -/
private noncomputable def codecTransitionCNF (M : FinTM Bool) (n s : ℕ) :
    CNF (Bool × CodecBit M n s) :=
  (Finset.univ.toList : List (CodecGateIndex M n s)).flatMap fun ix =>
    codecGateCNF M n s ix.1 ix.2.1 ix.2.2

/-- The transition conjunction enforces exactly all of its local update gates. -/
private theorem codecTransitionCNF_eval (M : FinTM Bool) (n s : ℕ)
    (a : Bool × CodecBit M n s → Bool) :
    (codecTransitionCNF M n s).eval a = true ↔
      ∀ p q b, codecGate M n s p q b (a ∘ codecGateWire M n s p q b) = true := by
  have hg := fun p q b => (codecGateCNF_spec M n s p q b).2 a
  simp only [codecTransitionCNF, codecCnf_eval_flatMap, Finset.mem_toList,
    Finset.mem_univ, forall_const, CodecGateIndex, Prod.forall, hg]

/-- The local conjunction is equivalent to adjacency on windowed same-input pairs.

**Proof sketch.** For soundness, choose the actual head tuple and scanned-symbol
case. Its guard is true, so every target bit equals the exact successor bit;
the exact-marker lemma identifies the successor vertex. For completeness,
every true guard reads the same native transition, whose bits match the target.
This includes the silent halted identity action and exterior-head rejection. -/
private theorem codecTransitionCNF_step_iff (M : FinTM Bool) (n s : ℕ) (x : List Bool)
    (hx : x.length = n) (c d : Cfg M.k Bool M.State x)
    (hc : c.InWindow s) (hd : d.InWindow s) :
    (codecTransitionCNF M n s).eval
      (codecPairBits (codecRowOf M n s x hx c) (codecRowOf M n s x hx d)) = true ↔
      NDTM.coreSum (M.tm.step c) = NDTM.coreSum d := by
  rw [codecTransitionCNF_eval, ← codecObserve_step_iff M n s x hx c d hc hd]
  constructor
  · intro h
    let p : CodecPositions M n s :=
      ((codecRowOf M n s x hx c).inputHead, (codecRowOf M n s x hx c).heads)
    let q : CodecCase M := (c.state, c.inputSymbol, c.workTapeSymbols)
    funext b
    have hg : codecGuard M n s p q
        (codecPairBits (codecRowOf M n s x hx c) (codecRowOf M n s x hx d) ∘
          codecGateWire M n s p q b) := by
      apply (codecGuard_spec M n s x hx c hc _ p q b).mpr
      refine ⟨rfl, rfl, ?_, rfl, rfl⟩
      intro i
      exact (codec_posCode_eq_iff s _ (hc.1 i) _).mp rfl
    have hb := h p q b
    simp only [codecGate, decide_eq_true_eq] at hb
    have he := hb hg
    change codecRowBits (codecRowOf M n s x hx d) b = _ at he
    exact (codecExpected_step M n s x hx c hc _ p q b hg).symm.trans he.symm
  · intro h p q b
    simp only [codecGate, decide_eq_true_eq]
    intro hg
    change codecRowBits (codecRowOf M n s x hx d) b = _
    rw [codecExpected_step M n s x hx c hc _ p q b hg, h]

/-- Counting local gates multiplies positions, fixed machine cases, coordinates,
and the constant per-gate cost; no row truth table appears. -/
private theorem codecTransitionCNF_cost (M : FinTM Bool) (n s : ℕ) :
    codecCnfCost (codecTransitionCNF M n s) ≤
      Fintype.card (CodecPositions M n s) * Fintype.card (CodecCase M) *
      Fintype.card (CodecBit M n s) * (2 ^ (3 * M.k + 7) * (3 * M.k + 8)) := by
  have h := codecCnfCost_flatMap_le (Finset.univ.toList : List (CodecGateIndex M n s))
    (fun ix => codecGateCNF M n s ix.1 ix.2.1 ix.2.2)
    (2 ^ (3 * M.k + 7) * (3 * M.k + 8)) (fun ix _ => (codecGateCNF_spec M n s _ _ _).1)
  simpa only [codecTransitionCNF, Finset.length_toList, Finset.card_univ,
    CodecGateIndex, Fintype.card_prod, Nat.mul_assoc] using h

/-- The numbered adjacency formula includes the separate carried-input equality conjunct. -/
private noncomputable def configurationAdjacency (M : FinTM Bool) (C n s : ℕ) : CNF ℕ :=
  (codecInputEquality M n s ++ codecTransitionCNF M n s).relabel (codecPairWire M C n s)

/-- The numbered adjacency formula has the required quotient-step interpretation. -/
private theorem configurationAdjacency_eval (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x : List Bool) (hx : x.length = n)
    (c d : Cfg M.k Bool M.State x) (hc : c.InWindow s) (hd : d.InWindow s) :
    (configurationAdjacency M C n s).eval
      (fun v => (configurationCodec M C n s x c ++ configurationCodec M C n s x d).getD v false)
      = true ↔ NDTM.coreSum (M.tm.step c) = NDTM.coreSum d := by
  simp only [configurationAdjacency, CNF.eval_relabel, Function.comp_def,
    configurationCodec_pair_get M C n s hC x x hx hx c d, CNF.eval_append,
    Bool.and_eq_true, codecInputEquality_eval, codecTransitionCNF_step_iff M n s x hx c d hc hd]
  exact and_iff_right rfl

/-- Different carried inputs fail the adjacency formula's equality conjunct. -/
private theorem configurationAdjacency_reject (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : x ≠ y) (c : Cfg M.k Bool M.State x) (d : Cfg M.k Bool M.State y) :
    (configurationAdjacency M C n s).eval
      (fun v => (configurationCodec M C n s x c ++ configurationCodec M C n s y d).getD v false)
      = false := by
  rw [configurationAdjacency, CNF.relabel_append, CNF.eval_append]
  change ((configurationInputEquality M C n s).eval _ && _) = false
  rw [configurationInputEquality_reject M C n s hC x y hx hy hxy c d]
  rfl

/-- Machine-only coefficient for the joint transition enumeration. -/
private def codecTransitionCoefficient (M : FinTM Bool) : ℕ :=
  2 ^ M.k * Fintype.card (CodecCase M) * (2 ^ (3 * M.k + 7) * (3 * M.k + 8))

/-- The transition gates have polynomial cost, of degree `k+2` before serialization. -/
private theorem codecTransitionCNF_cost_poly (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    codecCnfCost (codecTransitionCNF M n s) ≤
      codecTransitionCoefficient M * C * (s + n + 2) ^ (M.k + 2) := by
  have hp := codecPositions_card_le M n s
  have hb : Fintype.card (CodecBit M n s) ≤ C * (s + n + 2) :=
    (codecBit_card_le M n s C hC).trans (Nat.mul_le_mul_left _ (by omega))
  calc
    _ ≤ Fintype.card (CodecPositions M n s) * Fintype.card (CodecCase M) *
        Fintype.card (CodecBit M n s) * (2 ^ (3 * M.k + 7) * (3 * M.k + 8)) :=
      codecTransitionCNF_cost M n s
    _ ≤ (2 ^ M.k * (s + n + 2) ^ (M.k + 1)) * Fintype.card (CodecCase M) *
        (C * (s + n + 2)) * (2 ^ (3 * M.k + 7) * (3 * M.k + 8)) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_right _ hp) hb)
    _ = _ := by unfold codecTransitionCoefficient; rw [pow_succ]; ring

/-- Input equality and transition gates share the degree-`k+2` cost ledger. -/
private theorem codecAdjacency_cost (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    codecCnfCost (codecInputEquality M n s ++ codecTransitionCNF M n s) ≤
      (6 + codecTransitionCoefficient M) * C * (s + n + 2) ^ (M.k + 2) := by
  have hpos : 1 ≤ C := by unfold codecCoefficient at hC; omega
  have hn : n ≤ C * (s + n + 2) ^ (M.k + 2) := by
    calc
      n ≤ s + n + 2 := by omega
      _ ≤ (s + n + 2) ^ (M.k + 2) := Nat.le_pow (by omega)
      _ ≤ C * (s + n + 2) ^ (M.k + 2) := Nat.le_mul_of_pos_left _ (by omega)
  rw [codecCnfCost_append]
  calc
    _ ≤ 6 * n + codecTransitionCoefficient M * C * (s + n + 2) ^ (M.k + 2) :=
      Nat.add_le_add (codecInputEquality_cost M n s) (codecTransitionCNF_cost_poly M C n s hC)
    _ ≤ 6 * (C * (s + n + 2) ^ (M.k + 2)) +
        codecTransitionCoefficient M * C * (s + n + 2) ^ (M.k + 2) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 6 hn) _
    _ = _ := by ring

/-- Adjacency uses only the two code blocks and has a polynomial serialized length.

**Proof sketch.** Every variable is wired into one of the two padded blocks.
The cost ledger counts both literal occurrences and clause delimiters, including
empty clauses. The public serialization grammar adds one factor bounded by
`5 C (s+n+2)`, hence degree `k+3`; the final terminator is included explicitly. -/
private theorem configurationAdjacency_bounds (M : FinTM Bool) (C n s : ℕ)
    (hC : codecCoefficient M ≤ C) :
    (configurationAdjacency M C n s).numVars ≤ 2 * (C * (s + n + 1)) ∧
    (CNF.serialize (configurationAdjacency M C n s)).length ≤
      (5 * (6 + codecTransitionCoefficient M) + 1) * C ^ 2 * (s + n + 2) ^ (M.k + 3) := by
  have hb : ∀ cl ∈ codecInputEquality M n s ++ codecTransitionCNF M n s,
      ∀ l ∈ cl, codecPairWire M C n s l.1 < 2 * (C * (s + n + 1)) :=
    fun _ _ l _ => codecPairWire_lt M C n s hC l.1
  refine ⟨codecCnf_numVars _ _ _ hb, ?_⟩
  have hpos : 1 ≤ C := by unfold codecCoefficient at hC; omega
  have hindex : 2 * (C * (s + n + 1)) + 3 ≤ 5 * C * (s + n + 2) := by nlinarith
  have hterm : 1 ≤ C ^ 2 * (s + n + 2) ^ (M.k + 3) := by
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (by positivity))
  calc
    _ ≤ codecCnfCost (codecInputEquality M n s ++ codecTransitionCNF M n s) *
        (2 * (C * (s + n + 1)) + 3) + 1 := codecCnf_serialize _ _ _ hb
    _ ≤ ((6 + codecTransitionCoefficient M) * C * (s + n + 2) ^ (M.k + 2)) *
        (5 * C * (s + n + 2)) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul (codecAdjacency_cost M C n s hC) hindex) 1
    _ = 5 * (6 + codecTransitionCoefficient M) * C ^ 2 *
        (s + n + 2) ^ (M.k + 3) + 1 := by rw [pow_succ]; ring
    _ ≤ 5 * (6 + codecTransitionCoefficient M) * C ^ 2 *
        (s + n + 2) ^ (M.k + 3) + C ^ 2 * (s + n + 2) ^ (M.k + 3) :=
      Nat.add_le_add_left hterm _
    _ = _ := by ring


/-- **Claim 4.4(2), packaged quotient form** (proved — phase
P4.3 round 2; **retired at the RD-2a re-fill**, design §16b item 2: superseded by the
`Complexity.ConfigCodec` theorems below, and used by no proof; see the module docstring's
declared deviations): for every
machine there is a constant `C` such that for all `(n, s)` there are a
configuration bit-codec — fixed length `C · (s + n + 1)`, **factoring through the input and the
vertex quotient** `Turing.NDTM.coreSum` on windowed configurations (an iff:
equal codes exactly when equal vertices, at one input) — and three CNFs: `φv` characterizing exactly the codec image
among the length-matching strings, `φa` deciding adjacency (the step, read on
the vertex quotient) on same-input windowed pairs and rejecting cross-input
pairs, and `φacc` deciding acceptance (halted state, `accept` summary); all
three with `numVars` inside the code width and serialized lengths bounded by
`C · (s + n + 2) ^ C` — base `s + n + 2`, not the code width's `s + n + 1`:
at `n = s = 0` the code width equals `C` while one literal reading the
second block already serializes to `C + 6` (round-2 blocker, finding 1).

**Proof sketch.** The codec is the marker discipline of the Cook-Levin
tableau row (`TCSlib.Complexity.CookLevin` precedents), now carrying the
input: an input-content track of `n` bits, a one-hot input-position track of
length `n + 2`, a one-hot state block (halt included), per work tape a window
track of `2s + 1` cells — three-valued symbol plus a head-marker bit — and a
two-bit summary block; total length linear in `s + n` with the machine's
constants in `C`, padded to the exact `C · (s + n + 1)`. Injectivity to
`(x, coreSum)` mirrors `Turing.MultiTapeTM.ConfigCount.coreCode_inj` on the
window tracks plus the content track; the output enters only through the
summary block (full-output injectivity is impossible and not claimed —
round-1 finding 1). `φv` conjoins per-track well-formedness (one-hot blocks,
trit ranges, canonical padding); `φacc` reads the halt pattern and the
summary block; `φa` conjoins content-track equality, locality of unmarked
window cells, the marked-cell and neighbor updates by the transition table —
the scanned input bit read from the content track under the position
marker — the one-hot shifts by at most one, the state rewrite, and the
summary update (`Turing.outSummary`'s append table): the one-hot blocks' uniqueness
constraints are pairwise-exclusion clauses — quadratic in the block length,
polynomial overall — and the transition checks are enumerated over the
input-position and work-head tuples jointly with the finitely many
state/scanned-symbol cases (the head markers couple the tracks:
`(n + 2) · (2s + 1)^k` guarded cases for the fixed machine), each case a
constant-size CNF by the chapter-2 universality
(`Complexity.exists_cnf_boolFun`, applied per **gate**, never per row — a
whole-row truth table is exponential); the honest count is polynomial, not
linear (round-2 finding 4), bounding clause count, `numVars`, and the
serialized lengths (the chapter-2 grammar's serialization-length equation —
clause count enters it explicitly, round-1 finding 8). Fill obligations,
named: the codec definition with exact-length padding; the two injectivity
lemmas; the validity characterization in both directions; the per-position
check enumeration; the three serialized-size ledgers; the
step-iff-adjacency equivalence through `Turing.NDTM.coreSum_stepWith`. -/
theorem exists_adjacency_codec_cnf (M : Turing.FinTM Bool) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n s : ℕ),
      ∃ (code : (x : List Bool) → Cfg M.k Bool M.State x → List Bool)
        (φv φa φacc : CNF ℕ),
        (∀ (x : List Bool) (c : Cfg M.k Bool M.State x),
          (code x c).length = C * (s + n + 1)) ∧
        (∀ (x x' : List Bool), x.length = n → x'.length = n →
          ∀ (c : Cfg M.k Bool M.State x) (c' : Cfg M.k Bool M.State x'),
            c.InWindow s → c'.InWindow s → code x c = code x' c' → x = x') ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c d : Cfg M.k Bool M.State x, c.InWindow s → d.InWindow s →
            (code x c = code x d ↔ NDTM.coreSum c = NDTM.coreSum d)) ∧
        (∀ w : List Bool, w.length = C * (s + n + 1) →
          (φv.eval (fun v => w.getD v false) = true ↔
            ∃ (x : List Bool), x.length = n ∧
              ∃ c : Cfg M.k Bool M.State x, c.InWindow s ∧ w = code x c)) ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c d : Cfg M.k Bool M.State x, c.InWindow s → d.InWindow s →
            (φa.eval (fun v => (code x c ++ code x d).getD v false) = true ↔
              NDTM.coreSum (M.tm.step c) = NDTM.coreSum d)) ∧
        (∀ (x x' : List Bool), x.length = n → x'.length = n → x ≠ x' →
          ∀ (c : Cfg M.k Bool M.State x) (c' : Cfg M.k Bool M.State x'),
            c.InWindow s → c'.InWindow s →
            φa.eval (fun v => (code x c ++ code x' c').getD v false) = false) ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c : Cfg M.k Bool M.State x, c.InWindow s →
            (φacc.eval (fun v => (code x c).getD v false) = true ↔
              (c.state = none ∧ outSummary c.output = OutSummary.accept))) ∧
        φv.numVars ≤ C * (s + n + 1) ∧
        φacc.numVars ≤ C * (s + n + 1) ∧
        φa.numVars ≤ 2 * (C * (s + n + 1)) ∧
        (CNF.serialize φv).length ≤ C * (s + n + 2) ^ C ∧
        (CNF.serialize φa).length ≤ C * (s + n + 2) ^ C ∧
        (CNF.serialize φacc).length ≤ C * (s + n + 2) ^ C := by
  let B := (3 * codecValidityCoefficient M + 7) +
    (5 * (6 + codecTransitionCoefficient M) + 1) + 13
  obtain ⟨C, hC, hwidth, hsize⟩ := codec_absorb B (M.k + 3) (codecCoefficient M)
  refine ⟨C, hC, fun n s => ?_⟩
  have hp : (s + n + 2) ^ 3 ≤ (s + n + 2) ^ (M.k + 3) := by
    rw [pow_add]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hledger (a e : ℕ) (ha : a ≤ B)
      (he : (s + n + 2) ^ e ≤ (s + n + 2) ^ (M.k + 3)) :
      a * C ^ 2 * (s + n + 2) ^ e ≤ C * (s + n + 2) ^ C :=
    (Nat.mul_le_mul (Nat.mul_le_mul_right _ ha) he).trans (hsize _ (by omega))
  refine ⟨configurationCodec M C n s, configurationValidity M C n s,
    configurationAdjacency M C n s, configurationAcceptance M n s,
    configurationCodec_length M C n s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy c d _ _ he
    exact configurationCodec_input_eq M C n s hwidth x y hx hy c d he
  · intro x hx c d hc hd
    exact configurationCodec_eq_iff M C n s hwidth x hx c d hc hd
  · exact configurationValidity_eval M C n s hwidth
  · intro x hx c d hc hd
    exact configurationAdjacency_eval M C n s hwidth x hx c d hc hd
  · intro x y hx hy hxy c d _ _
    exact configurationAdjacency_reject M C n s hwidth x y hx hy hxy c d
  · intro x hx c _
    exact configurationAcceptance_eval M C n s hwidth x hx c
  · exact configurationValidity_numVars M C n s hwidth
  · exact (configurationAcceptance_bounds M C n s hwidth).1
  · exact (configurationAdjacency_bounds M C n s hwidth).1
  · exact (configurationValidity_size M C n s hwidth).trans
      (hledger _ 3 (by dsimp [B]; omega) hp)
  · exact (configurationAdjacency_bounds M C n s hwidth).2.trans
      (hledger _ (M.k + 3) (by dsimp [B]; omega) (Nat.le_refl _))
  · exact (configurationAcceptance_size M C n s hwidth).trans
      (hledger 13 3 (by dsimp [B]; omega) hp)

/-! ### Claim 4.4(2), restated: the theorems of the closed-form codec

The eleven clauses of the retired packaged statement, one theorem each (`code_length`,
`code_input_eq`, `code_eq_iff`, `validity_eval_iff`, `adjacency_eval_iff`,
`adjacency_eval_of_ne`, `acceptance_eval_iff`, the three `numVars` bounds and
`exists_serialize_length_le`); the closed-form indexing contract (`code_getD_*`); and the
uniformity theorems, which the packaged existential could not supply. The semantic theorems are
re-filled at RD-2a from the fill appendix above, the uniformity theorems at RD-2b over
`TCSlib.Complexity.FormulaKit.Emit`. -/

namespace ConfigCodec

variable (M : FinTM Bool)

/-! #### Layout -/

/-- The width in closed form, `2n + 4 + Q + 3k(2s + 1)` with `Q = stateCount M`. (Proved by
unfolding.) -/
theorem width_eq (n s : ℕ) :
    width M n s = 2 * n + 4 + stateCount M + 3 * (M.k * (2 * s + 1)) := by
  simp only [width, summaryOffset, workOffset, stateOffset]
  omega

/-- The width is linear in `s + n + 1`, with the machine coefficient `card + 6k + 5` of the
retired padded codec (`codecCoefficient`).

**Proof sketch.** `width_eq`, then compare coefficients: `2n + 5 + card + 6ks + 3k` is at most
`(card + 6k + 5)(s + n + 1)` term by term. -/
theorem width_le (n s : ℕ) :
    width M n s ≤ (Fintype.card M.State + 6 * M.k + 5) * (s + n + 1) := by
  sorry

/-- The halting-state marker is the first state variable, `stateOffset n`. (Proved by
unfolding.) -/
theorem stateVar_none (n : ℕ) : stateVar M n none = stateOffset n := by
  simp [stateVar, stateIndex]

/-- There are `portCount k = 3k + 7` ports. (Proved by counting the constructors through the
derived `Fintype` instance, as the private `codecPort_card` does.) -/
theorem card_port (k : ℕ) : Fintype.card (Port k) = portCount k := by
  rw [← Fintype.card_congr (Port.proxyTypeEquiv k)]
  simp [portCount]
  ring

/-- Every port number is below `portCount k`. (Proved by cases.) -/
theorem portIndex_lt {k : ℕ} (p : Port k) : portIndex p < portCount k := by
  cases p with
  | workHead i => have := i.isLt; simp only [portIndex, portCount]; omega
  | workSymbol i t => have := i.isLt; cases t <;> simp [portIndex, portCount] <;> omega
  | summary t => cases t <;> simp [portIndex, portCount] <;> omega
  | _ => simp [portIndex, portCount] <;> omega

/-- `portOf` inverts `portIndex`: the port with the number of `p` is `p`. (Proved by cases:
the `if` chain of `portOf` selects the branch of `p`'s number range, and `omega` recovers the
tape index and the flag.) -/
theorem portOf_portIndex {k : ℕ} (p : Port k) : portOf k (portIndex p) = p := by
  cases p with
  | workHead i =>
    have hi := i.isLt
    simp only [portIndex, portOf]
    split_ifs <;> first | (exfalso; omega) | (congr 1; ext; simp)
  | workSymbol i t =>
    have hi := i.isLt
    cases t <;> simp only [portIndex, portOf, Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;>
      first | (exfalso; omega) | (congr 1 <;> first | (ext; simp; omega) | (simp; omega))
  | summary t =>
    cases t <;> simp only [portIndex, portOf, Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;>
      first | rfl | (exfalso; omega)
  | _ => simp only [portIndex, portOf]; split_ifs <;> first | rfl | (exfalso; omega)

/-- **Every code word has exactly the width**, for every input and configuration.

**Proof sketch.** The five segments have lengths `n`, `n + 2`, `stateCount M`,
`k · (2s + 1) · 3` (three flags per cell) and `2`; `width_eq`. -/
theorem code_length (n s : ℕ) (x : List Bool) (c : Cfg M.k Bool M.State x) :
    (code M n s x c).length = width M n s := by
  sorry

/-- The input variable `i < n` of a code word reads input bit `i` (`false` past the end of
`x`).

**Proof sketch.** Index into the first segment (`List.getD_append`, `List.getElem_ofFn`). -/
theorem code_getD_inputVar (n s : ℕ) (x : List Bool) (c : Cfg M.k Bool M.State x) (i : ℕ)
    (hi : i < n) : (code M n s x c).getD (inputVar i) false = x.getD i false := by
  sorry

/-- The head variable `j < n + 2` reads "the input head is at `j`".

**Proof sketch.** Index into the second segment after the first `n` bits. -/
theorem code_getD_headVar (n s : ℕ) (x : List Bool) (c : Cfg M.k Bool M.State x) (j : ℕ)
    (hj : j < n + 2) :
    (code M n s x c).getD (headVar n j) false = decide (c.inputPos.val = j) := by
  sorry

/-- The state variable of `q` reads "the state is `q`".

**Proof sketch.** Index into the third segment; `stateIndex` is injective (it is `0` at the
halting state and one more than an equivalence elsewhere) and below `stateCount M`. -/
theorem code_getD_stateVar (n s : ℕ) (x : List Bool) (c : Cfg M.k Bool M.State x)
    (q : Option M.State) :
    (code M n s x c).getD (stateVar M n q) false = decide (c.state = q) := by
  sorry

/-- The work variable `(i, j, b)` with `j < 2s + 1` and `b < 3` reads flag `b` of window cell
`j` of tape `i`.

**Proof sketch.** Index into the fourth segment: the flattening over tapes, then cells, then
the three flags, puts that flag at offset `3((2s + 1)i + j) + b`. -/
theorem code_getD_workVar (n s : ℕ) (x : List Bool) (c : Cfg M.k Bool M.State x)
    (i : Fin M.k) (j b : ℕ) (hj : j < 2 * s + 1) (hb : b < 3) :
    (code M n s x c).getD (workVar M n s i j b) false = (workFlags M s c i j).getD b false := by
  sorry

/-- The summary variables read "the output is `[true]`" (`dead = false`) and "the output is
dead" (`dead = true`).

**Proof sketch.** Index into the last segment. -/
theorem code_getD_summaryVar (n s : ℕ) (x : List Bool) (c : Cfg M.k Bool M.State x)
    (dead : Bool) :
    (code M n s x c).getD (summaryVar M n s dead) false =
      decide (outSummary c.output = if dead then .dead else .accept) := by
  sorry

/-! #### Claim 4.4(2), clause by clause -/

/-- **The codec separates inputs** of length `n` (clause 2 of the retired statement; its
window hypotheses are not needed, since the input track is read directly): if two inputs of
length `n` have configurations with equal codes, the inputs are equal.

**Proof sketch.** `code_getD_inputVar` at every `i < n`, and `List.ext_getElem`. -/
theorem code_input_eq (n s : ℕ) (x x' : List Bool) (hx : x.length = n) (hx' : x'.length = n)
    (c : Cfg M.k Bool M.State x) (c' : Cfg M.k Bool M.State x')
    (h : code M n s x c = code M n s x' c') : x = x' := by
  sorry

/-- **The codec is the vertex quotient on windowed configurations** ([AB09, Claim 4.4(2)];
clause 3 of the retired statement): at one input of length `n`, two configurations in the
radius-`s` window have equal codes iff they are the same configuration-graph vertex
`Turing.NDTM.coreSum`.

**Proof sketch.** The private `codecObserve_eq` identifies the exact-integer head flags with
the window code `Turing.MultiTapeTM.ConfigCount.coreCode` on windowed configurations, and the
code at the closed-form index of each coordinate `b` of the private `CodecBit` is the private
`codecRowBits (codecRowOf …) b` (one new private bridge, from the `code_getD_*` reads). The
surviving private `codecRowBits_injective` and `codecRowOf_eq_iff` (through the public
`Turing.MultiTapeTM.ConfigCount.coreCode_inj`) close both directions. -/
theorem code_eq_iff (n s : ℕ) (x : List Bool) (hx : x.length = n)
    (c d : Cfg M.k Bool M.State x) (hc : c.InWindow s) (hd : d.InWindow s) :
    code M n s x c = code M n s x d ↔ NDTM.coreSum c = NDTM.coreSum d := by
  sorry

/-- **Validity characterizes the codec image** ([AB09, Claim 4.4(2)]; clause 4 of the retired
statement, at the closed-form width): a word of the code width satisfies the validity CNF iff
it is the code of a configuration in the radius-`s` window on some input of length `n`.

**Proof sketch.** Through the bridge of `code_eq_iff`, the exactly-one gadgets
(`Complexity.FormulaKit.exactlyOne_eval`) and the pair exclusions state the private
`codecBitsValid`; the surviving `codecBitsValid_iff` decodes a finite row and
`codecRow_realize` realizes it by a windowed configuration whose code is the word (both have
the width, and they agree at every closed-form index). There is no padding clause. -/
theorem validity_eval_iff (n s : ℕ) (w : List Bool) (hw : w.length = width M n s) :
    (validity M n s).eval (fun v => w.getD v false) = true ↔
      ∃ x : List Bool, x.length = n ∧ ∃ c : Cfg M.k Bool M.State x,
        c.InWindow s ∧ w = code M n s x c := by
  sorry

/-- **Adjacency is the step on the vertex quotient** ([AB09, Claim 4.4(2)]; clause 5 of the
retired statement): for configurations `c, d` in the radius-`s` window on one input of length
`n`, the adjacency CNF holds on the concatenated codes iff the successor of `c` and `d` are
the same vertex. Halted vertices are self-adjacent; a live vertex need not be (P4.3 round-2
finding 3).

**Proof sketch.** Bridge each gate to the private semantics: `Complexity.FormulaKit.gate_eval`
and `portOf_portIndex` give `kindPred` of the wired ports, which is the private `codecGate` at
`(p, h, q, v)` (a case split on the coordinate field computed by `expectOf`). The closed-form
enumeration covers every input position, head tuple (`headOf`, mixed radix), case
(`caseList` is complete) and coordinate, so `transition` holds iff every private gate holds
(the re-proved `codecTransitionCNF_eval`), and the surviving step lemma
(`codecTransitionCNF_step_iff`, restated over the gate conjunction) concludes; the input
equality conjunct holds on same-input pairs. -/
theorem adjacency_eval_iff (n s : ℕ) (x : List Bool) (hx : x.length = n)
    (c d : Cfg M.k Bool M.State x) (hc : c.InWindow s) (hd : d.InWindow s) :
    (adjacency M n s).eval (fun v => (code M n s x c ++ code M n s x d).getD v false) = true ↔
      NDTM.coreSum (M.tm.step c) = NDTM.coreSum d := by
  sorry

/-- **Adjacency rejects pairs across distinct inputs** (clause 6 of the retired statement;
its window hypotheses are not needed): for distinct inputs of length `n`, the adjacency CNF
is false on the concatenated codes of any of their configurations.

**Proof sketch.** Some `i < n` has `x[i] ≠ x'[i]`; by `code_length` and `code_getD_inputVar`
variables `i` and `width + i` read the two bits, and one of the two equality clauses of `i`
fails. -/
theorem adjacency_eval_of_ne (n s : ℕ) (x x' : List Bool) (hx : x.length = n)
    (hx' : x'.length = n) (hne : x ≠ x') (c : Cfg M.k Bool M.State x)
    (c' : Cfg M.k Bool M.State x') :
    (adjacency M n s).eval (fun v => (code M n s x c ++ code M n s x' c').getD v false) =
      false := by
  sorry

/-- **Acceptance reads halting with accepting summary** ([AB09, Claim 4.4(2)]; clause 7 of the
retired statement; its length and window hypotheses are not needed): the acceptance CNF holds
on the code of `c` iff `c` is halted with output summary `accept`.

**Proof sketch.** `stateVar_none`, `code_getD_stateVar` and `code_getD_summaryVar`. -/
theorem acceptance_eval_iff (n s : ℕ) (x : List Bool) (c : Cfg M.k Bool M.State x) :
    (acceptance M n s).eval (fun v => (code M n s x c).getD v false) = true ↔
      c.state = none ∧ outSummary c.output = .accept := by
  sorry

/-- Validity mentions only code variables (a `numVars` clause of the retired statement).

**Proof sketch.** `Complexity.FormulaKit.numVars_le_of_forall_lt`: every listed variable is a
head, state, work or summary variable below `width`. -/
theorem validity_numVars_le (n s : ℕ) : (validity M n s).numVars ≤ width M n s := by
  sorry

/-- Acceptance mentions only code variables (a `numVars` clause of the retired statement).

**Proof sketch.** Its two variables are below `width`. -/
theorem acceptance_numVars_le (n s : ℕ) : (acceptance M n s).numVars ≤ width M n s := by
  sorry

/-- Adjacency mentions only the variables of the two blocks (a `numVars` clause of the retired
statement).

**Proof sketch.** Input equality uses `i` and `width + i`; every gate's template mentions only
ports below `portCount` (`Complexity.FormulaKit.template_numVars_le`), and every port wire is
below `2 · width`. -/
theorem adjacency_numVars_le (n s : ℕ) : (adjacency M n s).numVars ≤ 2 * width M n s := by
  sorry

/-- **Polynomial serialized size** (the size clauses of the retired statement; P4.3 round-1
finding 8 and round-2 finding 1: serialized lengths, at base `s + n + 2`): one machine constant
`K` bounds the serializations of all three CNFs by `K · (s + n + 2)^K`.

**Proof sketch.** `Complexity.FormulaKit.serialize_length_le` with the index bound `width`
(or `2 · width`), and the cost ledgers `Complexity.FormulaKit.exactlyOne_cost_le`,
`Complexity.FormulaKit.gate_cost_le` and `Complexity.FormulaKit.cost_flatMap_le`: validity
and acceptance have degree `3`, adjacency `k + 3` (`(n + 2)(2s + 1)^k · |caseList| · width`
gates); the surviving private `codec_absorb` makes one constant. -/
theorem exists_serialize_length_le :
    ∃ K : ℕ, ∀ n s : ℕ,
      (CNF.serialize (validity M n s)).length ≤ K * (s + n + 2) ^ K ∧
      (CNF.serialize (adjacency M n s)).length ≤ K * (s + n + 2) ^ K ∧
      (CNF.serialize (acceptance M n s)).length ≤ K * (s + n + 2) ^ K := by
  sorry

/-! #### Uniformity: what the packaged existential could not supply

Each CNF is emitted in polynomial time at any input length `n x`, radius `s x` and variable
offset `o x` given in unary by polynomial-time functions of the reduction's input `x`, and the
initial vertex's code is computed in polynomial time. These are the fill obligations "the
three-CNF emitter family" and "the initial-code computation" of `Complexity.TQBF_PSPACEHard`,
now theorems of the codec (RD-2b). The input length is a parameter, not `x.length`, so that a
per-level emitter can call them on the pair of the instance and a level index. -/

/-- **Validity is emitted in polynomial time** at any polynomial-time input length, radius and
offset: the serialization of `validity M (n x) (s x)` with every variable `v` renamed
`o x + v` is polynomial-time computable.

**Proof sketch.** Present validity as ordered groups (the exactly-one gadgets, the cell
exclusions, the summary exclusion), each with a polynomial-time fragment from `(x, i)` by
unary index arithmetic; `Complexity.FormulaKit.polyTimeComputable_serialize_flatMap` emits it
and `Complexity.FormulaKit.polyTimeComputable_serialize_relabel_add` shifts it. -/
theorem polyTimeComputable_serialize_validity (n s o : List Bool → ℕ)
    (hn : PolyTimeComputable fun x => List.replicate (n x) true)
    (hs : PolyTimeComputable fun x => List.replicate (s x) true)
    (ho : PolyTimeComputable fun x => List.replicate (o x) true) :
    PolyTimeComputable fun x =>
      CNF.serialize ((validity M (n x) (s x)).relabel (o x + ·)) := by
  sorry

/-- **Adjacency is emitted in polynomial time** at any polynomial-time input length, radius and
offset (both blocks shift together: the source at `o x`, the target at `o x + width`).

**Proof sketch.** Input equality is `n x` groups of two clauses. The transition groups are
indexed by `(p, h, q, v)` in mixed radix; a group is the fixed template of the kind
`(q, interior p, expectOf …)`, selected among the machine's finitely many kinds
(`Complexity.FormulaKit.polyTimeComputable_fragment_gate_select`), with wires `portWire …`
computed by unary arithmetic; `Complexity.FormulaKit.polyTimeComputable_serialize_flatMap`
emits them and `Complexity.FormulaKit.polyTimeComputable_serialize_relabel_add` shifts them. -/
theorem polyTimeComputable_serialize_adjacency (n s o : List Bool → ℕ)
    (hn : PolyTimeComputable fun x => List.replicate (n x) true)
    (hs : PolyTimeComputable fun x => List.replicate (s x) true)
    (ho : PolyTimeComputable fun x => List.replicate (o x) true) :
    PolyTimeComputable fun x =>
      CNF.serialize ((adjacency M (n x) (s x)).relabel (o x + ·)) := by
  sorry

/-- **Acceptance is emitted in polynomial time** at any polynomial-time input length, radius
and offset.

**Proof sketch.** Two unit clauses whose unary indices `o x + stateOffset (n x)` and
`o x + summaryOffset M (n x) (s x)` are polynomial-time; finite concatenation. -/
theorem polyTimeComputable_serialize_acceptance (n s o : List Bool → ℕ)
    (hn : PolyTimeComputable fun x => List.replicate (n x) true)
    (hs : PolyTimeComputable fun x => List.replicate (s x) true)
    (ho : PolyTimeComputable fun x => List.replicate (o x) true) :
    PolyTimeComputable fun x =>
      CNF.serialize ((acceptance M (n x) (s x)).relabel (o x + ·)) := by
  sorry

/-- **The initial vertex's code is computed in polynomial time** at any polynomial-time radius:
the code of `M`'s initial configuration on `x`, at input length `|x|` and radius `s x`.

**Proof sketch.** `Turing.Cfg.init` has input head `1`, the start state, blank work tapes with
every head at position `0` and the empty output, so the code is five concatenated segments
(`PolyTimeComputable.append`): a copy of `x`; the head track `0 1 0^n`; the constant state
track of the start state; per tape the pattern of `2s + 1` blank cells with the head flag at
cell `s`; and the summary `00`. Each is a copy of the input or a unary pattern of polynomial
length in `|x|` and `s x`. -/
theorem polyTimeComputable_code_initCfg (s : List Bool → ℕ)
    (hs : PolyTimeComputable fun x => List.replicate (s x) true) :
    PolyTimeComputable fun x => code M x.length (s x) x (M.tm.initCfg x) := by
  sorry

end ConfigCodec

/-- **The language `TQBF`** [AB09, §4.2]: binary strings whose decoded
quantified formula is true. The decoding fallback is the true closed formula,
so non-well-formed strings are members — the `SAT`-polarity convention of
`Complexity.QBF.decode`. -/
def TQBF : Language Bool :=
  {x | (QBF.decode x).truth}

/-! ### Fill appendix: membership validation and the assignment walk -/

/-- The aligned-pair stage remembers either no bit or the first bit of a pair;
after the separator, control is the public six-state CNF grammar automaton. -/
private abbrev b4mSyntaxState := Option Bool ⊕ Fin 6

/-- Consume one native input bit. A mismatched `10` pair enters the grammar's
permanent error state; only an aligned `01` starts the matrix grammar. -/
private def b4mSyntaxStep : b4mSyntaxState → Bool → b4mSyntaxState
  | .inl none, b => .inl (some b)
  | .inl (some false), false => .inl none
  | .inl (some false), true => .inr 0
  | .inl (some true), true => .inl none
  | .inl (some true), false => .inr 5
  | .inr q, b => .inr (CNF.syntaxStep q b)

/-- Syntax acceptance is read only after the fold has consumed the entire input. -/
private def b4mValid (x : List Bool) : Bool :=
  decide (x.foldl b4mSyntaxStep (.inl none) = .inr 4)

/-- Once the separator has been read, the product automaton is exactly the
promoted matrix automaton. -/
private theorem b4mSyntax_matrix (x : List Bool) (q : Fin 6) :
    x.foldl b4mSyntaxStep (.inr q) = .inr (x.foldl CNF.syntaxStep q) := by
  induction x generalizing q with
  | nil => rfl
  | cons b x ih => exact ih (CNF.syntaxStep q b)

/-- The native syntax fold accepts exactly successful pair decoding followed
by successful matrix parsing.

**Proof sketch.** Follow the pair decoder's aligned two-bit recursion. Equal
pairs reset the pair stage; `01` enters the public matrix grammar. An incomplete
pair never accepts, and `10` enters the grammar's rejecting residual. The matrix
case cites the promoted grammar theorem, including its exact-consumption check. -/
private theorem b4mValid_spec (x : List Bool) :
    b4mValid x = match pairDecode x with
      | none => false
      | some (_, m) => (CNF.parse m).isSome := by
  induction x using pairDecode.induct with
  | case1 xs ih =>
      change b4mValid xs = _
      rw [ih]
      cases hp : pairDecode xs <;> simp [pairDecode, hp]
  | case2 xs ih =>
      change b4mValid xs = _
      rw [ih]
      cases hp : pairDecode xs <;> simp [pairDecode, hp]
  | case3 xs =>
      simp only [b4mValid, List.foldl_cons, b4mSyntaxStep, b4mSyntax_matrix,
        Sum.inr.injEq, pairDecode]
      exact CNF.syntaxOK_spec xs
  | case4 xs h00 h11 h01 =>
      rcases xs with _ | ⟨b, _ | ⟨c, r⟩⟩
      · rfl
      · cases b <;> rfl
      · cases b <;> cases c
        · exact False.elim (h00 r rfl)
        · exact False.elim (h01 r rfl)
        · have herr : r.foldl CNF.syntaxStep 5 ≠ 4 := by
            intro hc
            exact (CNF.syntaxSuffix_run 5 r).mpr hc
          simpa [b4mValid, b4mSyntaxStep, b4mSyntax_matrix, pairDecode] using herr
        · exact False.elim (h11 r rfl)

/-- The empty matrix is true under every prefix, including unused quantifiers.
Proof sketch: existential quantifiers choose `false`, and universal quantifiers
apply the induction hypothesis to each update of the current assignment. -/
private theorem b4mTruth_empty (qs : List QBF.Quant) (σ : ℕ → Bool) (i : ℕ) :
    QBF.truthAux [] qs σ i := by
  induction qs generalizing σ i with
  | nil => rfl
  | cons q qs ih =>
      cases q with
      | ex => exact ⟨false, ih _ _⟩
      | all => exact fun b => ih (Function.update σ i b) (i + 1)

/-- A failed full syntax pass takes precisely one of the two true fallbacks.
This conclusion is available only after validation has consumed the whole input. -/
private theorem b4mReject_mem {x : List Bool} (h : b4mValid x = false) : x ∈ TQBF := by
  change (QBF.decode x).truth
  cases hp : pairDecode x with
  | none =>
      simpa [QBF.decode, hp, QBF.truth, CNF.fallback] using
        b4mTruth_empty [] (fun _ => false) 0
  | some p =>
      obtain ⟨qs, m⟩ := p
      have hm : CNF.parse m = none := by
        cases he : CNF.parse m with
        | none => rfl
        | some φ => simp [b4mValid_spec, hp, he] at h
      simpa [QBF.decode, hp, QBF.truth, CNF.decode, hm, CNF.fallback] using
        b4mTruth_empty (qs.map QBF.quantOfBit) (fun _ => false) 0

/-- Accepted strings reconstruct the exact prefix and matrix that the evaluator
will reread. No private parser machinery is used. -/
private theorem b4mValid_repr {x : List Bool} (h : b4mValid x = true) :
    ∃ (qs : List Bool) (m : CNF ℕ), x = pairEncode qs (CNF.serialize m) := by
  rw [b4mValid_spec] at h
  cases hp : pairDecode x with
  | none => simp [hp] at h
  | some p =>
      obtain ⟨qs, y⟩ := p
      cases hm : CNF.parse y with
      | none => simp [hp, hm] at h
      | some m =>
          exact ⟨qs, m, (eq_pairEncode_of_pairDecode x qs y hp).trans
            (congrArg (pairEncode qs) (CNF.parse_repr hm))⟩

/-- The completed input-fold machine's rejection has the decoder's true
semantics. The only machine fact used is the public full-input fold contract. -/
private theorem b4mValidation_reject {k : ℕ} {x : List Bool}
    (d : Cfg k Bool (ScanPhase b4mSyntaxState) x)
    (hs : d.state = some (.fwd (.inl none))) (hi : d.inputPos = 1)
    (hr : ((inputFoldTM k b4mSyntaxStep (.inl none)).runFrom d
      (2 * x.length + 2)).state ≠ some (.done (.inr 4))) : x ∈ TQBF := by
  apply b4mReject_mem
  rw [(inputFoldTM_run_ofCfg b4mSyntaxStep (.inl none) d hs hi).1] at hr
  simpa [b4mValid] using hr

/-- Validation visits only the existing origin of each work head, independently
of input length and of whether syntax succeeds. -/
private theorem b4mValidation_space {k : ℕ} {x : List Bool}
    (d : Cfg k Bool (ScanPhase b4mSyntaxState) x)
    (hs : d.state = some (.fwd (.inl none))) (hi : d.inputPos = 1) :
    (inputFoldTM k b4mSyntaxStep (.inl none)).spaceUsed d (2 * x.length + 2) ≤ k := by
  have hheads := (inputFoldTM_run_ofCfg b4mSyntaxStep (.inl none) d hs hi).2.2
  calc
    _ ≤ ∑ j : Fin k, 1 := Finset.sum_le_sum (fun j _ => by
      have h := MultiTapeTM.spaceUsedByTape_le_card_Icc
        (inputFoldTM k b4mSyntaxStep (.inl none)) d (2 * x.length + 2) j
        (d.workTapePos j) (d.workTapePos j)
        (fun u hu => by simp [hheads j u hu])
      simpa using h)
    _ = k := by simp

/-- The carry is stopped (`inl none`), is carrying a subtree verdict
(`inl (some v)`), or has read the quantifier and awaits its branch bit
(`inr (v, q)`). This is finite control over binary work tapes. -/
private abbrev b4mCarryState := Option Bool ⊕ (Bool × Bool)

/-- Backward odometer transition for the two-cell record `(branch, quantifier)`.
A neutral first branch requests the second branch; a decisive or second branch
resets the record and propagates the verdict toward the root. -/
private def b4mBack : b4mCarryState → Bool → b4mCarryState × Bool
  | .inl none, b => (.inl none, b)
  | .inl (some v), q => (.inr (v, q), q)
  | .inr (v, q), b =>
      if b = false ∧ v ≠ q then (.inl none, true) else (.inl (some v), false)

/-- Pure specification of a backward pass. The logical record list runs from
the innermost variable toward the root. `none` means that another leaf is
needed; `some v` at the end means root overflow with verdict `v`. -/
private def b4mCarryRecords : Option Bool → List (Bool × Bool) →
    Option Bool × List (Bool × Bool)
  | none, rs => (none, rs)
  | some v, [] => (some v, [])
  | some v, (b, q) :: rs =>
      if b = false ∧ v ≠ q then (none, (true, q) :: rs)
      else
        let r := b4mCarryRecords (some v) rs
        (r.1, (false, q) :: r.2)

/-- The physical record word, root first. Each record occupies exactly two
Boolean cells: branch bit, then quantifier bit (`true` for existential). -/
private def b4mRecordWord (rs : List (Bool × Bool)) : List Bool :=
  (rs.flatMap (fun r => [r.2, r.1])).reverse

/-- The backward transducer implements the record carry exactly.

**Proof sketch.** Induct on the innermost-first record list. The first two reads
are the quantifier and branch bits. In the stopped case neither cell changes.
Otherwise the eight Boolean cases are precisely the neutral-first-branch rule;
the induction hypothesis handles the remaining, more outward records. -/
private theorem b4mBack_run (rs : List (Bool × Bool)) (v : Option Bool) :
    mealyRun b4mBack (.inl v) (rs.flatMap (fun r => [r.2, r.1])) =
      (.inl (b4mCarryRecords v rs).1,
        (b4mCarryRecords v rs).2.flatMap (fun r => [r.2, r.1])) := by
  induction rs generalizing v with
  | nil => cases v <;> rfl
  | cons r rs ih =>
      obtain ⟨b, q⟩ := r
      cases v with
      | none => simp [mealyRun, b4mBack, b4mCarryRecords, ih]
      | some v =>
          cases b <;> cases q <;> cases v <;>
            simp [mealyRun, b4mBack, b4mCarryRecords, ih]

/-- The odometer leaves every quantifier in its original position. Thus the
record count and the space occupied by the assignment bank are invariant. -/
private theorem b4mCarryRecords_quants (rs : List (Bool × Bool)) (v : Option Bool) :
    (b4mCarryRecords v rs).2.map Prod.snd = rs.map Prod.snd := by
  induction rs generalizing v with
  | nil => cases v <;> rfl
  | cons r rs ih =>
      obtain ⟨b, q⟩ := r
      cases v with
      | none => rfl
      | some v =>
          simp only [b4mCarryRecords]
          split_ifs
          · rfl
          · exact congrArg (q :: ·) (ih (some v))

/-- The physical assignment word uses exactly two cells per quantified variable. -/
private theorem b4mRecordWord_length (rs : List (Bool × Bool)) :
    (b4mRecordWord rs).length = 2 * rs.length := by
  simp only [b4mRecordWord, List.length_reverse]
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih]; omega

/-- A full catalog scan performs the short-circuit odometer pass and restores
the word's original orientation.

**Proof sketch.** Induct from the root end of the record list to check the
read-only forward pass, two cells at a time. The backward pass is the preceding
record-transducer theorem; reversing its output gives the physical word again.
No generic scan-trace or Mealy append/length lemma is re-proved. -/
private theorem b4mScan_result (rs : List (Bool × Bool)) (v : Option Bool) :
    scanResult scanKeep b4mBack (.inl v) (b4mRecordWord rs) =
      (.inl (b4mCarryRecords v rs).1, b4mRecordWord (b4mCarryRecords v rs).2) := by
  have hf : mealyRun scanKeep (.inl v : b4mCarryState) (b4mRecordWord rs) =
      (.inl v, b4mRecordWord rs) := by
    induction rs using List.reverseRecOn with
    | nil => rfl
    | append_singleton rs r ih =>
        simpa [b4mRecordWord, List.flatMap_append, List.reverse_append,
          mealyRun, scanKeep] using
          congrArg (fun p : b4mCarryState × List Bool => (p.1, r.1 :: r.2 :: p.2)) ih
  unfold scanResult
  rw [hf]
  simp only [b4mRecordWord, List.reverse_reverse, b4mBack_run]

/-- The machine odometer has an envelope of `2m + 1` on its record tape and
zero on every other tape. Its public scan contract takes exactly `4m + 2`
steps, restores all heads and leaves the input position and output unchanged.

**Proof sketch.** Instantiate the public scan contract on the two-cell record
word. Its record-head interval is from one cell before the word to its right
delimiter. Convert this interval to an absolute displacement; the other heads
are fixed by that same contract. No scan trace is reproved. -/
private theorem b4mOdometer_envelope {k : ℕ} {x : List Bool} (i : Fin k)
    (rs : List (Bool × Bool)) (v : Option Bool)
    (d : Cfg k Bool (ScanPhase b4mCarryState) x)
    (hs : d.state = some (.fwd (.inl v)))
    (hw : ∀ p : ℤ, -1 ≤ p → p ≤ ((b4mRecordWord rs).length : ℤ) →
      d.workTapes i (d.workTapePos i + p) = FinTM.bufferTape (b4mRecordWord rs) p) :
    ∀ u ≤ 4 * rs.length + 2, ∀ j,
      |((scanTM k i scanKeep b4mBack (.inl v)).runFrom d u).workTapePos j -
        d.workTapePos j| ≤ if j = i then ((2 * rs.length + 1 : ℕ) : ℤ) else 0 := by
  intro u hu j
  have hu' : u ≤ 2 * (b4mRecordWord rs).length + 2 := by
    rw [b4mRecordWord_length]
    omega
  have h := (scanTM_run_ofCfg i scanKeep b4mBack (.inl v)
    (b4mRecordWord rs) d hs hw).2.2 j u hu'
  by_cases hj : j = i
  · rw [if_pos hj] at h ⊢
    have hb := Finset.mem_Icc.mp h
    rw [b4mRecordWord_length] at hb
    exact abs_le.mpr ⟨by omega, by omega⟩
  · rw [if_neg hj] at h ⊢
    simp [h]

/-- The carry preserves the number of records, by its stronger quantifier-word
invariant. -/
private theorem b4mCarryRecords_length (rs : List (Bool × Bool)) (v : Option Bool) :
    (b4mCarryRecords v rs).2.length = rs.length := by
  have h := congrArg List.length (b4mCarryRecords_quants rs v)
  simpa using h

/-- The branch bits, innermost first, as a little-endian counter. This is a
termination measure in the proof; the machine does not store a second copy. -/
private def b4mRank (rs : List (Bool × Bool)) : ℕ :=
  Nat.ofDigits 2 (rs.map (fun r => r.1.toNat))

/-- Every branch word has rank strictly below the number of complete assignments. -/
private theorem b4mRank_lt (rs : List (Bool × Bool)) : b4mRank rs < 2 ^ rs.length := by
  apply (Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2) ?_).trans_le
  · simp
  · intro n hn
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hn
    cases r.1 <;> decide

/-- Every nonterminal carry strictly advances the assignment rank.

**Proof sketch.** At a neutral first branch, the lowest remaining zero changes
to one. Otherwise the current bit resets to zero and the outward suffix must
advance. Its increase is multiplied by two, which exceeds the possible loss
of the current bit. Short-circuiting can skip assignments but cannot revisit one. -/
private theorem b4mRank_progress (rs : List (Bool × Bool)) (v : Bool)
    (h : (b4mCarryRecords (some v) rs).1 = none) :
    b4mRank rs < b4mRank (b4mCarryRecords (some v) rs).2 := by
  induction rs with
  | nil => simp [b4mCarryRecords] at h
  | cons r rs ih =>
      obtain ⟨b, q⟩ := r
      by_cases hn : b = false ∧ v ≠ q
      · rcases hn with ⟨rfl, hn⟩
        simp [b4mCarryRecords, hn, b4mRank, Nat.ofDigits_cons]
      · have ht : (b4mCarryRecords (some v) rs).1 = none := by
          simpa only [b4mCarryRecords, if_neg hn] using h
        have hg := ih ht
        have hb : b.toNat ≤ 1 := by cases b <;> decide
        rw [b4mCarryRecords, if_neg hn]
        change b.toNat + 2 * b4mRank rs <
          0 + 2 * b4mRank (b4mCarryRecords (some v) rs).2
        omega

/-- The pure leaf-and-carry loop. `leaf` is the matrix verdict for the current
assignment; a successful result is root overflow, and exhaustion returns `none`.
This function describes rounds, not their Turing-machine implementation. -/
private def b4mWalk (leaf : List (Bool × Bool) → Bool) :
    ℕ → List (Bool × Bool) → Option Bool
  | 0, _ => none
  | fuel + 1, rs =>
      let r := b4mCarryRecords (some (leaf rs)) rs
      match r.1 with
      | some v => some v
      | none => b4mWalk leaf fuel r.2

/-- No more than the remaining number of assignments is needed, for any leaf
verdict function. The empty prefix still takes one leaf evaluation.

**Proof sketch.** Induct on the available round budget. A terminal carry returns
immediately. A nonterminal carry preserves length and strictly increases rank,
so it decreases the number of remaining assignments by at least one. Rank is
strictly below `2^m`, ruling out exhaustion at zero. -/
private theorem b4mWalk_terminates (leaf : List (Bool × Bool) → Bool)
    (fuel : ℕ) (rs : List (Bool × Bool)) (hf : 2 ^ rs.length - b4mRank rs ≤ fuel) :
    (b4mWalk leaf fuel rs).isSome = true := by
  induction fuel generalizing rs with
  | zero =>
      have h := b4mRank_lt rs
      omega
  | succ fuel ih =>
      cases he : (b4mCarryRecords (some (leaf rs)) rs).1 with
      | some v => simp [b4mWalk, he]
      | none =>
          simp only [b4mWalk, he]
          apply ih
          have hp := b4mRank_progress rs (leaf rs) he
          have hl := b4mCarryRecords_length rs (some (leaf rs))
          rw [hl]
          omega

/-- The short-circuit AND/OR value of a Boolean tree. `false` node kinds are
AND; `true` node kinds are OR. The first child returns immediately when its
value equals the node kind; otherwise the second child's value is returned.
The leaf is arbitrary and the base assignment supplies unmentioned coordinates. -/
private def b4mValue (leaf : (ℕ → Bool) → Bool) :
    List Bool → (ℕ → Bool) → ℕ → Bool
  | [], σ, _ => leaf σ
  | q :: qs, σ, i =>
      let v := b4mValue leaf qs (Function.update σ i false) (i + 1)
      if v = q then v else b4mValue leaf qs (Function.update σ i true) (i + 1)

/-- The carry rule closes exactly the node whose branch has just
returned. For a second branch, the first branch's neutral verdict is the
invariant that makes an accumulator unnecessary.

**Proof sketch.** Split the quantifier, branch, and verdict bits. Existential
quantification is disjunction of its two Boolean instances; universal
quantification is conjunction. A decisive first instance fixes the result,
and a neutral first instance leaves the second instance's value unchanged. -/
private theorem b4mValue_close (leaf : (ℕ → Bool) → Bool) (qs : List Bool)
    (σ : ℕ → Bool) (i : ℕ) (q b v : Bool)
    (hv : b4mValue leaf qs (Function.update σ i b) (i + 1) = v)
    (hfirst : b = true →
      b4mValue leaf qs (Function.update σ i false) (i + 1) = !q)
    (hclose : ¬(b = false ∧ v ≠ q)) :
    b4mValue leaf (q :: qs) σ i = v := by
  cases q <;> cases b <;> cases v <;>
    simp_all [b4mValue]

/-- A carry that reaches the root keeps its input verdict and resets every
branch below that root. Those reset branches are ready for the next outer branch. -/
private theorem b4mCarryRecords_done (rs : List (Bool × Bool)) (v u : Bool)
    (h : (b4mCarryRecords (some v) rs).1 = some u) :
    u = v ∧ ∀ r ∈ (b4mCarryRecords (some v) rs).2, r.1 = false := by
  induction rs with
  | nil => simp [b4mCarryRecords] at h ⊢; exact h.symm
  | cons r rs ih =>
      obtain ⟨b, q⟩ := r
      by_cases hn : b = false ∧ v ≠ q
      · simp [b4mCarryRecords, hn] at h
      · have ht : (b4mCarryRecords (some v) rs).1 = some u := by
          simpa only [b4mCarryRecords, if_neg hn] using h
        obtain ⟨hu, hr⟩ := ih ht
        refine ⟨hu, ?_⟩
        simpa [b4mCarryRecords, hn] using hr

/-- Appending one outer record first carries through the inner records, then
through that outer record; the rewritten records concatenate in the same order. -/
private theorem b4mCarryRecords_outer (rs : List (Bool × Bool)) (r : Bool × Bool)
    (v : Option Bool) :
    b4mCarryRecords v (rs ++ [r]) =
      let s := b4mCarryRecords v rs
      let t := b4mCarryRecords s.1 [r]
      (t.1, s.2 ++ t.2) := by
  induction rs generalizing v with
  | nil => cases v <;> simp [b4mCarryRecords]
  | cons p rs ih =>
      obtain ⟨b, q⟩ := p
      cases v with
      | none => rfl
      | some v =>
          by_cases hn : b = false ∧ v ≠ q
          · simp [b4mCarryRecords, hn]
          · simp only [List.cons_append, b4mCarryRecords, if_neg hn]
            rw [ih]

/-- The assignment read from a root-first record list by successive coordinate
updates. Unmentioned coordinates retain the base assignment. -/
private def b4mAssigned : List (Bool × Bool) → (ℕ → Bool) → ℕ → (ℕ → Bool)
  | [], σ, _ => σ
  | (b, _) :: rs, σ, i => b4mAssigned rs (Function.update σ i b) (i + 1)

/-- Assignment lookup beyond the quantifier prefix reads the base value; with
the all-false base, this is the required free-variable convention. -/
private theorem b4mAssigned_free (rs : List (Bool × Bool)) (σ : ℕ → Bool)
    (i j : ℕ) (hj : i + rs.length ≤ j) : b4mAssigned rs σ i j = σ j := by
  induction rs generalizing σ i with
  | nil => rfl
  | cons r rs ih =>
      obtain ⟨b, q⟩ := r
      change b4mAssigned rs (Function.update σ i b) (i + 1) j = σ j
      rw [ih _ _ (by simp only [List.length_cons] at hj; omega)]
      exact Function.update_of_ne (by simp only [List.length_cons] at hj; omega) _ _

/-- The depth-first invariant on a root-first record list. A `true` branch bit
certifies that the first subtree was neutral for its quantifier; the invariant
continues down the branch currently selected at each variable. -/
private def b4mLegal (leaf : (ℕ → Bool) → Bool) :
    List (Bool × Bool) → (ℕ → Bool) → ℕ → Prop
  | [], _, _ => True
  | (b, q) :: rs, σ, i =>
      (b = true →
        b4mValue leaf (rs.map Prod.snd) (Function.update σ i false) (i + 1) = !q) ∧
      b4mLegal leaf rs (Function.update σ i b) (i + 1)

/-- All-first-branch records satisfy the invariant under every outer assignment.
This applies both to initialization and to a reset suffix after a carry. -/
private theorem b4mLegal_reset (leaf : (ℕ → Bool) → Bool) (rs : List (Bool × Bool))
    (σ : ℕ → Bool) (i : ℕ) (hb : ∀ r ∈ rs, r.1 = false) :
    b4mLegal leaf rs σ i := by
  induction rs generalizing σ i with
  | nil => trivial
  | cons r rs ih =>
      obtain ⟨b, q⟩ := r
      have h0 : b = false := hb (b, q) List.mem_cons_self
      subst b
      exact ⟨by simp, ih _ _ (fun r hr => hb r (List.mem_cons_of_mem _ hr))⟩

/-- The same carry viewed on a root-first list, for the AND/OR induction;
tape execution continues to use `b4mCarryRecords`. -/
private def b4mAdvance (v : Option Bool) (rs : List (Bool × Bool)) :
    Option Bool × List (Bool × Bool) :=
  let r := b4mCarryRecords v rs.reverse
  (r.1, r.2.reverse)

/-- Changing the proof-side orientation does not change the quantifier word. -/
private theorem b4mAdvance_quants (rs : List (Bool × Bool)) (v : Option Bool) :
    (b4mAdvance v rs).2.map Prod.snd = rs.map Prod.snd := by
  have h := congrArg List.reverse (b4mCarryRecords_quants rs.reverse v)
  simpa [b4mAdvance, List.map_reverse] using h

/-- In root-first orientation the inner suffix runs first; only its overflow
can change the outer record. This is the recursive form used by the semantic proof. -/
private theorem b4mAdvance_cons (rs : List (Bool × Bool)) (b q : Bool)
    (v : Option Bool) :
    b4mAdvance v ((b, q) :: rs) =
      let s := b4mAdvance v rs
      match s.1 with
      | none => (none, (b, q) :: s.2)
      | some w => if b = false ∧ w ≠ q then (none, (true, q) :: s.2)
          else (some w, (false, q) :: s.2) := by
  unfold b4mAdvance
  rw [List.reverse_cons, b4mCarryRecords_outer]
  cases he : (b4mCarryRecords v rs.reverse).1 with
  | none => simp [he, b4mCarryRecords]
  | some w =>
      by_cases hc : b = false ∧ w ≠ q <;> simp [he, b4mCarryRecords, hc]

/-- One leaf evaluation and carry either preserves the depth-first invariant
or returns the full AND/OR value.

**Proof sketch.** Induct on the root-first record list, against the short-circuit value. A nonterminal inner suffix preserves the outer record and its neutral
first-branch fact. A terminal suffix supplies its exact value. If the
outer record requests its second branch, that value establishes the new neutral
fact and the reset inner records satisfy the invariant under the changed outer
assignment. Otherwise the node-closing lemma returns the outer value. -/
private theorem b4mAdvance_correct (leaf : (ℕ → Bool) → Bool) (rs : List (Bool × Bool))
    (σ : ℕ → Bool) (i : ℕ) (hlegal : b4mLegal leaf rs σ i) :
    let r := b4mAdvance (some (leaf (b4mAssigned rs σ i))) rs
    match r.1 with
    | none => b4mLegal leaf r.2 σ i
    | some u => b4mValue leaf (rs.map Prod.snd) σ i = u := by
  induction rs generalizing σ i with
  | nil => rfl
  | cons r rs ih =>
      obtain ⟨b, q⟩ := r
      let v := leaf (b4mAssigned rs (Function.update σ i b) (i + 1))
      have hs := ih (Function.update σ i b) (i + 1) hlegal.2
      change (match (b4mAdvance (some v) rs).1 with
        | none => b4mLegal leaf (b4mAdvance (some v) rs).2
            (Function.update σ i b) (i + 1)
        | some u => b4mValue leaf (rs.map Prod.snd)
            (Function.update σ i b) (i + 1) = u) at hs
      have hqs := b4mAdvance_quants rs (some v)
      change (match (b4mAdvance (some v) ((b, q) :: rs)).1 with
        | none => b4mLegal leaf (b4mAdvance (some v) ((b, q) :: rs)).2 σ i
        | some u => b4mValue leaf (q ::
            rs.map Prod.snd) σ i = u)
      simp only [b4mAdvance_cons]
      cases he : (b4mAdvance (some v) rs).1 with
      | none =>
          simp only [he] at hs ⊢
          refine ⟨?_, hs⟩
          intro hb
          rw [hqs]
          exact hlegal.1 hb
      | some w =>
          simp only [he] at hs ⊢
          have hd := b4mCarryRecords_done rs.reverse v w he
          have hreset : ∀ p ∈ (b4mAdvance (some v) rs).2, p.1 = false := by
            simpa [b4mAdvance] using hd.2
          by_cases hc : b = false ∧ w ≠ q
          · simp only [if_pos hc]
            obtain ⟨hb, hw⟩ := hc
            subst b
            refine ⟨?_, b4mLegal_reset leaf _ _ _ hreset⟩
            intro _
            rw [hqs]
            exact hs.trans (by cases q <;> cases w <;> simp_all)
          · simp only [if_neg hc]
            exact b4mValue_close leaf _ σ i q b w hs hlegal.1 hc

/-- Apply the arbitrary leaf to the complete current assignment. Unmentioned
coordinates read from the all-false base. -/
private def b4mLeaf (leaf : (ℕ → Bool) → Bool) (rs : List (Bool × Bool)) : Bool :=
  leaf (b4mAssigned rs.reverse (fun _ => false) 0)

/-- Every returned verdict of the leaf-and-carry walk equals the AND/OR value, provided
the current records satisfy the neutral-first-branch invariant.

**Proof sketch.** Induct on the round budget. The one-round theorem either
returns the AND/OR value immediately or supplies the next invariant.
In the latter case the quantifier word is unchanged, so the induction hypothesis
proves the same tree value at the next assignment. -/
private theorem b4mWalk_correct (leaf : (ℕ → Bool) → Bool) (fuel : ℕ) (rs : List (Bool × Bool))
    (v : Bool) (hlegal : b4mLegal leaf rs.reverse (fun _ => false) 0)
    (h : b4mWalk (b4mLeaf leaf) fuel rs = some v) :
    b4mValue leaf (rs.reverse.map Prod.snd)
      (fun _ => false) 0 = v := by
  induction fuel generalizing rs with
  | zero => simp [b4mWalk] at h
  | succ fuel ih =>
      have hc := b4mAdvance_correct leaf rs.reverse (fun _ => false) 0 hlegal
      simp only [b4mAdvance, List.reverse_reverse] at hc
      change (match (b4mCarryRecords (some (b4mLeaf leaf rs)) rs).1 with
        | none => b4mLegal leaf (b4mCarryRecords (some (b4mLeaf leaf rs)) rs).2.reverse
            (fun _ => false) 0
        | some u => b4mValue leaf (rs.reverse.map Prod.snd)
            (fun _ => false) 0 = u) at hc
      cases he : (b4mCarryRecords (some (b4mLeaf leaf rs)) rs).1 with
      | some w =>
          simp only [b4mWalk, he, Option.some.injEq] at h
          subst w
          simpa only [he] using hc
      | none =>
          simp only [he] at hc
          simp only [b4mWalk, he] at h
          have hh := ih _ hc h
          have hqs : (b4mCarryRecords (some (b4mLeaf leaf rs)) rs).2.reverse.map
              Prod.snd = rs.reverse.map Prod.snd := by
            simpa only [List.map_reverse] using
              congrArg List.reverse (b4mCarryRecords_quants rs (some (b4mLeaf leaf rs)))
          simpa only [hqs] using hh

/-- **Promotion candidate (host H1, AND/OR evaluator;
`machine-library-design.md` §14).** For any Boolean leaf function and root-first
list of AND/OR node kinds, the initialized depth-first walk returns the tree
value within `2^m` leaf rounds, including one round for an empty tree. This is
the pure semantic contract; its machine realization is a separate obligation.

**Proof sketch.** Every initial branch bit is false, so the invariant holds
without any previously evaluated subtree. The rank bound supplies a returned
verdict within the full assignment budget, and the loop correctness theorem
identifies it with the AND/OR value at the all-false base. -/
private theorem b4mWalk_value (leaf : (ℕ → Bool) → Bool) (qs : List Bool) :
    ∃ v, b4mWalk (b4mLeaf leaf) (2 ^ qs.length)
        (qs.map (fun q => (false, q))).reverse = some v ∧
      (b4mValue leaf qs (fun _ => false) 0 = v) := by
  let rs := (qs.map (fun q => (false, q))).reverse
  have hn := b4mWalk_terminates (b4mLeaf leaf) (2 ^ qs.length) rs (by
    simp only [rs, List.length_reverse, List.length_map]
    exact Nat.sub_le _ _)
  have hl : b4mLegal leaf rs.reverse (fun _ => false) 0 := by
    apply b4mLegal_reset
    intro r hr
    simp only [rs, List.reverse_reverse, List.mem_map] at hr
    obtain ⟨q, _, rfl⟩ := hr
    rfl
  cases hw : b4mWalk (b4mLeaf leaf) (2 ^ qs.length) rs with
  | none => simp [hw] at hn
  | some v =>
      refine ⟨v, rfl, ?_⟩
      simpa [rs, List.map_map] using b4mWalk_correct leaf (2 ^ qs.length) rs v hl hw

/-- **Promotion candidate (host H1, AND/OR evaluator;
`machine-library-design.md` §14).** A framed leaf module for the Boolean
assignment walker. Tape zero contains the root-first two-cell record word;
the other `k` tapes are scratch and enter blank. From `entry` at `home x`,
the module reaches the exit carrying the leaf's verdict within `time x m`
steps. Before that exit it is silent and every work head stays within
`radius x m` of its entry position. At exit all work tapes and work heads
are restored and the native input head is again at `home x`.

This is a hypothesis on a machine, not an asserted construction of one.
The bounds may depend on the input and number of records, but not on the
assignment. Restoring all tapes preserves the record word and blanks every
scratch tape, so successive calls can reuse the same banks. -/
private def b4mLeafFramed {k : ℕ} {S : Type} (M : MultiTapeTM (k + 1) Bool S)
    (entry : S) (exit : Bool → S) (leaf : List Bool → (ℕ → Bool) → Bool)
    (home : List Bool → ℕ) (time radius : List Bool → ℕ → ℕ) : Prop :=
  ∀ (x : List Bool) (rs : List (Bool × Bool)) (d : Cfg (k + 1) Bool S x),
    d.state = some entry → d.inputPos.val = home x →
    (∀ p : ℤ, -1 ≤ p → p ≤ ((b4mRecordWord rs).length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + p) = FinTM.bufferTape (b4mRecordWord rs) p) →
    (∀ j : Fin k, ∀ p, d.workTapes j.succ p = none) →
    ∃ t ≤ time x rs.length,
      (∀ u < t, ∀ v, (M.runFrom d u).state ≠ some (exit v)) ∧
      (∀ u ≤ t, ∀ j, |(M.runFrom d u).workTapePos j - d.workTapePos j| ≤
        (radius x rs.length : ℤ)) ∧
      (∀ u ≤ t, (M.runFrom d u).output = d.output) ∧
      (M.runFrom d t).state = some (exit (b4mLeaf (leaf x) rs)) ∧
      (M.runFrom d t).inputPos.val = home x ∧
      (M.runFrom d t).workTapes = d.workTapes ∧
      (M.runFrom d t).workTapePos = d.workTapePos

/-- The hypothesis-carrying leaf parameter. Its finite state space and
decidable equality are supplied by the caller; no CNF-specific data appears. -/
private structure b4mLeafModule (k : ℕ) (S : Type) [Fintype S] [DecidableEq S]
    (leaf : List Bool → (ℕ → Bool) → Bool) where
  machine : MultiTapeTM (k + 1) Bool S
  entry : S
  exit : Bool → S
  exit_injective : Function.Injective exit
  home : List Bool → ℕ
  home_bound : ∀ x, home x ≤ x.length + 1
  time : List Bool → ℕ → ℕ
  radius : List Bool → ℕ → ℕ
  framed : b4mLeafFramed machine entry exit leaf home time radius

/-- The CNF instance of the generic AND/OR value is the QBF interpretation.
The all-false base is supplied by the caller, so free-variable behavior is
unchanged.

**Proof sketch.** Induct on the node kinds. For an AND node, a false first
child decides the conjunction; for an OR node, a true first child decides the
disjunction. In the neutral cases both definitions return the second child.
The empty node list is the supplied matrix evaluation. -/
private theorem b4mValue_truth (m : CNF ℕ) (qs : List Bool) (σ : ℕ → Bool) (i : ℕ) :
    b4mValue m.eval qs σ i = true ↔ QBF.truthAux m (qs.map QBF.quantOfBit) σ i := by
  induction qs generalizing σ i with
  | nil => rfl
  | cons q qs ih =>
      have h0 := ih (Function.update σ i false) (i + 1)
      have h1 := ih (Function.update σ i true) (i + 1)
      cases q <;>
        cases hv : b4mValue m.eval qs (Function.update σ i false) (i + 1) <;>
        simp_all [b4mValue, QBF.quantOfBit, QBF.truthAux, Bool.forall_bool, Bool.exists_bool]

/-- The CNF leaf instance of the generic walker computes `truthAux`; its
algorithm and termination proof are inherited from the leaf-parametric host. -/
private theorem b4mWalk_truth (m : CNF ℕ) (qs : List Bool) :
    ∃ v, b4mWalk (b4mLeaf m.eval) (2 ^ qs.length)
        (qs.map (fun q => (false, q))).reverse = some v ∧
      (QBF.truthAux m (qs.map QBF.quantOfBit) (fun _ => false) 0 ↔ v = true) := by
  obtain ⟨v, hv, hvalue⟩ := b4mWalk_value m.eval qs
  refine ⟨v, hv, ?_⟩
  rw [← b4mValue_truth, hvalue]

/-- An all-true fuel word as long as a paired input has value strictly greater
than the walk's full assignment budget. Thus its final leaf fits the counter
loop's strict early-exit condition.

**Proof sketch.** Split the fuel after the first `m` bits and the next two bits.
The middle `11` alone contributes `3 * 2^m`; all other contributions are
nonnegative. The pair length is `2m + 2 + |matrix|`, so this split always fits.
This uses the public digit-append identity, without copying the private exact
all-true-value calculation in `Inclusions`. -/
private theorem b4mFuel_sufficient (qs ys : List Bool) :
    2 ^ qs.length < Nat.ofDigits 2
      ((List.replicate (pairEncode qs ys).length true).map Bool.toNat) := by
  have hr : List.replicate (pairEncode qs ys).length true =
      (List.replicate qs.length true ++ [true, true]) ++
        List.replicate (qs.length + ys.length) true := by
    change List.replicate (pairEncode qs ys).length true =
      (List.replicate qs.length true ++ List.replicate 2 true) ++
        List.replicate (qs.length + ys.length) true
    rw [← List.replicate_add, ← List.replicate_add, length_pairEncode]
    congr 1
    omega
  rw [hr, List.map_append, List.map_append, Nat.ofDigits_append, Nat.ofDigits_append]
  simp only [List.map_replicate, List.length_replicate, List.length_append,
    List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    Bool.toNat_true, Nat.ofDigits_cons, Nat.ofDigits_nil]
  have hpos : 0 < 2 ^ qs.length := pow_pos (by decide) _
  omega

/-- **`TQBF ∈ PSPACE`** ([AB09, Theorem 4.13, membership half]; spec, fill
pending): truth of a quantified formula is decidable in polynomial space.

**Proof sketch.** Validate the **entire** encoding before any matrix
verdict: trailing garbage makes the total decoder select the true fallback,
so a scanned prefix that "looks unsatisfiable" must not short-circuit
(round-1 answer 5). Then the recursive evaluator `A` of [AB09]: peel the
first quantifier, evaluate both restrictions, combine by the quantifier —
realized iteratively with a partial-assignment word of one trit per prefix
variable (the book's footnote: the linear-space global-array variant) walked
depth-first by the loop combinator, with no per-level formula copies; the
base case evaluates the CNF matrix under the assembled assignment by one
scan per clause, re-reading prefix bits and matrix bytes from the input. Space: the assignment
word (linear), the matrix cursor (linear), the recursion is depth-first on
the word in place — `O(n)` cells, inside `SPACE (n + 1) ⊆ PSPACE`. Fill
obligations, named: the depth-first assignment walker (a §12 loop/catalog
consumer), the CNF evaluator machine (one-pass per clause over the decoded
matrix), the parser reuse (`Complexity.QBF.decode` realized by the chapter-2
parser machinery), and the `DecidesInSpace` packaging.

**Fill appendix (B4 membership; partial, with Addendum 1).** The private block
above supplies full-input validation and the pure assignment walker. Refinement
(i): the validator composes the aligned-pair stage with the promoted public CNF
grammar facts and `inputFoldTM`, replacing inaccessible private parser machinery.
Refinement (ii): the remaining machine evaluator must compose the public
counter-loop/catalog index-lookup idiom, following `exists_inputSeekTM`; that
lookup and the streaming CNF instance are not yet constructed. Refinement (iii):
the §12.8 machine route supersedes the old wide-ARM planning references.

Records occupy two Boolean cells `(branch, node kind)`, physically root first;
the kind is `false` for AND/universal and `true` for OR/existential. The backward
scan sees kind before branch. A neutral first branch sets the branch bit and
stops; a decisive first branch or completed second branch resets it and carries
outward. All-first-branch initialization and this invariant yield the generic
AND/OR value in at most `2^m` rounds, with no formula copies. The leaf-specific
connection to `QBF.truthAux` is a separate lemma, and the framed leaf-module
parameter states timing, head-envelope, scratch-restoration and native-input
return obligations without mentioning CNF.

This partial does not yet realize that generic loop as a machine, instantiate
the leaf-module contract with the streaming CNF evaluator, initialize its banks,
or assemble the phases and complete the combined `DecidesInSpace` ledger. The
target remains admitted; the new private lemmas introduce no admissions. -/
theorem TQBF_mem_PSPACE : TQBF ∈ PSPACE := by
  sorry

/-- **`TQBF` is `PSPACE`-hard** ([AB09, Theorem 4.13, hardness half]; spec,
fill pending — **the phase-P4.3 fill summit**, the `ψᵢ` emitter; route restated by RD-2,
`machine-library-design.md` §16b item 2).

**Proof sketch.** Let `L ∈ PSPACE`, decided by `M` in space `c₀ · (n^c + 1)`.
On input `x` (length `n`, window radius `s := c₀·(n^c + 1)`), the reduction
emits a quantified formula asserting "some accepting vertex is reachable
from the initial vertex within `2^W` steps" over the closed-form codec
`Complexity.ConfigCodec` of Claim 4.4(2): vertices are the
`W := ConfigCodec.width M n s`-bit codes of input-carrying windowed quotient
configurations, with `Valid := ConfigCodec.validity M n s`,
`Next := ConfigCodec.adjacency M n s` (a source block followed by a target block) and
`Accept := ConfigCodec.acceptance M n s`. The midpoint recursion is
`ψ₀(a, b) := Valid a ∧ Valid b ∧ (a = b ∨ Next (a, b))` — the base includes
length-zero paths — `Next` self-loops are guaranteed only at halted
vertices, and a live vertex may or may not be self-adjacent (round-1
finding 6; round-2 finding 3) — and
`ψᵢ₊₁(a, b) := ∃ z (Valid z ∧ ∀ u v, ((u,v) = (a,z) ∨ (u,v) = (z,b)) → ψᵢ(u,v))`
([AB09]'s succinct `∀`-trick keeping one copy of `ψᵢ`, with the midpoint
**guarded by `Valid`** — unguarded quantification admits paths through junk
codes, round-1 finding 3), unfolded to depth `W` (at most `2^W` codes, so a
shortest path fits), against the initial code
`ConfigCodec.code M n s x (M.tm.initCfg x)` and an existentially quantified `Accept`
target (no unique accepting configuration is needed).

*Layout and matrix.* The prefix is level-blocked by `Complexity.FormulaKit.blockVar 0 W`:
block `0` is the target (existential); level `r < W` has its midpoint in block `3r + 1`
(existential) and the pair `u, v` in the adjacent blocks `3r + 2`, `3r + 3` (universal), so
that one offset places `Next` on the pair. The matrix is a **guarded CNF** (user decision,
design §16b item 2): one existential guard variable per level and existential disequality
witnesses for the selectors, all quantified **after** the whole prefix, with the codec CNFs
entering as their clauses at block offsets, each with its level's guard literal prepended.
Its pointwise lemma — for **every** assignment of the prefix variables, some extension to the
auxiliary variables satisfies the matrix iff the prenex matrix holds there — is the hypothesis
of `Complexity.QBF.truth_exSuffix_of_pointwise`, which turns the closed formula into the
prenex semantics `Complexity.QBF.PrefixTruth` (auxiliary values may depend on every universal
variable: round-1 answer 5).

*Truth.* By induction on `i`, under `Complexity.QBF.PrefixTruth`, `ψᵢ(a, b)` holds at valid
codes iff `b`'s vertex is reachable from `a`'s within `2^i` steps:
`ConfigCodec.validity_eval_iff`, `ConfigCodec.adjacency_eval_iff`,
`ConfigCodec.adjacency_eval_of_ne` (paths never change input), `ConfigCodec.code_eq_iff` and
`ConfigCodec.acceptance_eval_iff`, with the quotient dictionary
(`Turing.NDTM.reflTransGen_cfgStep_iff` through `Turing.MultiTapeTM.toNDTM`), path lifting
via `Turing.NDTM.coreSum_stepWith`, and the space bound keeping every genuine run inside the
window (`Turing.MultiTapeTM.abs_pos_lt_card_visited`). The midpoint and shortest-path facts
are the bounded-reachability kit of design §14 (not yet built).

*Emission* (a machine, user decision, design §16b item 2). The emitter is built in the
`Complexity.PolyTimeComputable` closure algebra over the H6 kit: the level groups by
`Complexity.FormulaKit.polyTimeComputable_serialize_flatMap` over `r < W`; the codec CNFs at
their block offsets by `ConfigCodec.polyTimeComputable_serialize_validity`,
`ConfigCodec.polyTimeComputable_serialize_adjacency` and
`ConfigCodec.polyTimeComputable_serialize_acceptance`, called at input length
`(pairFstD z).length` with the level-dependent offset; fragments by
`Complexity.FormulaKit.polyTimeComputable_fragment_iff_serialize`; the initial code by
`ConfigCodec.polyTimeComputable_code_initCfg`; the output word is `Complexity.QBF.encode` of
the formula, assembled by `PolyTimeComputable.pairEncode`. Size is polynomial because the
emitter is polynomial-time (`PolyTimeComputable.output_length_le`).

Fill obligations, named: the guarded matrix (the guards and the disequality witnesses) and its
pointwise lemma for every prefix assignment; the guard-literal transducer (a leaf row in the
style of `Complexity.FormulaKit.polyTimeComputable_serialize_relabel_add`, not a host); the
truth-preservation induction `ψᵢ ↔ reachability within 2^i`, both directions of the guarded
recursion, over the bounded-reachability kit; the window lemma for the decider's runs; the
emitter's assembly and the final identity through `Complexity.QBF.decode_encode`. Host: H6,
`Complexity.FormulaKit` (registered, design §14). -/
theorem TQBF_PSPACEHard : PSPACEHard TQBF := by
  sorry

/-- **The Stockmeyer-Meyer theorem**: `TQBF` is `PSPACE`-complete.
[AB09, Theorem 4.13]

**Proof sketch.** `Complexity.TQBF_mem_PSPACE` with
`Complexity.TQBF_PSPACEHard`. -/
theorem TQBF_PSPACEComplete : PSPACEComplete TQBF := by
  sorry

end Complexity
