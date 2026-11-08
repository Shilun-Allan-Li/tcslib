/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.StraightLine

/-!
# Circuits as straight-line programs: dual rail

The circuit-to-program half of [AB09, Ex 6.2], and the exercise's two-sided statement: a
function on `n` bits has a short Boolean straight-line program ([AB09, Note 6.4]) iff it
has a small fan-in-two circuit ([AB09, Def 6.1]), with explicit constants.

A program may negate only inputs, so a `¬` gate on an inner vertex cannot be copied line
for line.  We simulate the circuit **dual rail**: every vertex carries an operand for its
value and one for its complement.  An `∧`/`∨` gate of fan-in two costs two lines (the gate,
and its De Morgan dual on the complements), a `¬` gate swaps the two operands for free, a
fan-in-one gate is the identity, and a constant gate (fan-in `0`) costs the two lines
`x₁ ∨ ¬x₁`, `x₁ ∧ ¬x₁`.  A final line copies the output's operand into `y_T`.

## Main definitions

* `BoolCircuit.StraightLine.emitOp`, `BoolCircuit.StraightLine.gateEmit`,
  `BoolCircuit.StraightLine.dualRail` — the simulation (internal glue lives in the
  `BoolCircuit.StraightLine` namespace).
* `BoolCircuit.DAGCircuit.toStraightLine` — the dual-rail program of a circuit.

## Main results

* `BoolCircuit.DAGCircuit.toStraightLine_eval`, `toStraightLine_length_le` — a circuit with
  `G` gates of fan-in at most two and `n ≥ 1` inputs becomes a program of at most `2G + 1`
  lines.
* `BoolCircuit.exists_dagCircuit_of_straightLine`,
  `BoolCircuit.exists_straightLine_of_dagCircuit` — [AB09, Ex 6.2] with explicit constants.
* `BoolCircuit.not_exists_straightLine_true` — the `n = 0` edge case: the constant `1` on
  zero inputs has a one-vertex circuit but no program.

## Divergences from [AB09, Ex 6.2]

* **Not "S lines iff size S".**  For Boolean straight-line programs [AB09, Note 6.4]
  asserts exactly that `f` has an `S`-line program iff it has an `S`-sized circuit
  (the note's "up to polynomial factors" refers to general programming languages, not to
  this claim).
  - *Program to circuit*: the literal claim is false, because [AB09, Def 6.1]'s size
    counts the `n` input vertices and a negated literal costs a `¬` gate: `x₁ ∧ x₂` is a
    `1`-line program but needs a circuit of size `3`
    (`exists_straightLine_and_not_dagCircuit`).  We prove size `≤ 2n + max T 1` for `T`
    lines.
  - *Circuit to program*: we prove `≤ 2(S - n) + 1 ≤ 2S - 1` lines for size `S`, the cost
    of the dual-rail simulation.
  - So the corrected statement — both directions within a factor `2` and an additive
    `2n` — is proved.  Exactly `S` lines for circuit to program is proved for `n ≤ 2`
    by an exhaustive table check (`exists_straightLine_length_le_size_of_le_two`,
    `StraightLineSmall.lean`); for `n ≥ 3` it is not decided here.
* **`n ≥ 1` for circuit-to-program.**  The DAG model allows constant gates (fan-in `0`), so
  with `n = 0` a circuit computes the constant `1`, while the book's grammar admits only the
  empty program on zero inputs (`StraightLineProgram.eval_of_zero`).  The
  circuit-to-program direction is stated for `n ≥ 1`, and the failure at `n = 0` is proved
  (`not_exists_straightLine_true`).  This loses nothing against the book: under the
  literal [AB09, Def 6.1] (`∧`/`∨` of fan-in exactly `2`, no constants) a circuit has an
  output vertex, which is an input or a gate reading earlier vertices, so there are no
  circuits on `0` inputs at all.
* **Fan-in.**  The circuit-to-program direction needs only fan-in at most two, not
  well-formedness; `¬` gates of any fan-in `≤ 2` are read as `¬∧`, as `DAGGate.eval` does.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1, Note 6.4, Exercise 6.2.)
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

open StraightLine

variable {n : ℕ}

/-! ## From circuits to programs: dual rail -/

namespace StraightLine

/-- A *rail pair*: an operand for a vertex's value and an operand for its complement. -/
abbrev Rail (n : ℕ) := SLOperand n × SLOperand n

/-- The rail pair of vertex `a`. -/
def railAt (rs : List (Rail n)) (a : ℕ) : Rail n := rs.getD a (.line 0, .line 0)

/-- The lines simulating an `o`-gate (`o = ∧` or `∨`) of fan-in at most two, the new lines
starting at line `ℓ`, and the rail pair of its output.  Fan-in `0` is the constant `o` of
nothing, built from `x_{i₀} ∨ ¬x_{i₀}` and `x_{i₀} ∧ ¬x_{i₀}`; fan-in `1` is the identity
and costs no line; fan-in `2` costs one line `p ∘ q` and one dual line `¬p ∘' ¬q`.
Longer argument lists are not used. -/
def emitOp (i0 : Fin n) (o : SLOp) (ℓ : ℕ) : List (Rail n) → List (SLStmt n) × Rail n
  | [] => ([⟨o.dual, .input i0, .negInput i0⟩, ⟨o, .input i0, .negInput i0⟩],
      (.line ℓ, .line (ℓ + 1)))
  | [p] => ([], p)
  | p :: q :: _ => ([⟨o, p.1, q.1⟩, ⟨o.dual, p.2, q.2⟩], (.line ℓ, .line (ℓ + 1)))

/-- The lines simulating gate `g` whose inputs have rail pairs `rails`; a `¬` gate computes
the `∧` of its inputs with the rails swapped, costing no extra line. -/
def gateEmit (i0 : Fin n) (ℓ : ℕ) (g : DAGGate) (rails : List (Rail n)) :
    List (SLStmt n) × Rail n :=
  match g.kind with
  | .and => emitOp i0 .and ℓ rails
  | .or => emitOp i0 .or ℓ rails
  | .not => ((emitOp i0 .and ℓ rails).1, ((emitOp i0 .and ℓ rails).2.2,
      (emitOp i0 .and ℓ rails).2.1))

/-- Simulate one more gate: append its lines and its rail pair. -/
private def dualStep (i0 : Fin n) (s : List (SLStmt n) × List (Rail n)) (g : DAGGate) :
    List (SLStmt n) × List (Rail n) :=
  let r := gateEmit i0 s.1.length g (g.args.map (railAt s.2))
  (s.1 ++ r.1, s.2 ++ [r.2])

/-- Simulate a gate list: the lines, and the rail pair of every vertex (input `k` has the
rails `x_k`, `¬x_k`). -/
def dualRail (i0 : Fin n) (gs : List DAGGate) : List (SLStmt n) × List (Rail n) :=
  gs.foldl (dualStep i0) ([], List.ofFn fun k => (.input k, .negInput k))

/-- The invariant of the dual-rail simulation after the gates `old`. -/
structure DualInv (n : ℕ) (old : List DAGGate) (s : List (SLStmt n) × List (Rail n)) :
    Prop where
  /-- There is one rail pair per vertex. -/
  rails_length : s.2.length = n + old.length
  /-- The lines read only inputs and earlier lines. -/
  valid : LinesValid s.1
  /-- Every rail reads only existing lines. -/
  before : ∀ v < n + old.length,
    (railAt s.2 v).1.Before s.1.length ∧ (railAt s.2 v).2.Before s.1.length
  /-- The rails of vertex `v` compute its value and its complement. -/
  value : ∀ (x : Fin n → Bool), ∀ v < n + old.length,
    (railAt s.2 v).1.eval x (runLines s.1 x) = vertexValue old x v ∧
      (railAt s.2 v).2.eval x (runLines s.1 x) = !vertexValue old x v
  /-- At most two lines per gate. -/
  length_le : s.1.length ≤ 2 * old.length

/-- Before any gate, the input rails `x_k`, `¬x_k` satisfy the dual-rail invariant. -/
private theorem dualInv_nil : DualInv n [] (([] : List (SLStmt n)),
    List.ofFn fun k : Fin n => ((.input k, .negInput k) : Rail n)) := by
  have hr : ∀ v (hv : v < n),
      railAt (List.ofFn fun k : Fin n => ((.input k, .negInput k) : Rail n)) v =
      (.input ⟨v, by omega⟩, .negInput ⟨v, by omega⟩) := by
    intro v hv
    simp [railAt, List.getD_eq_getElem?_getD, hv]
  refine ⟨by simp, LinesValid.nil, fun v hv => ?_, fun x v hv => ?_, by simp⟩
  · rw [hr v (by simpa using hv)]; exact ⟨trivial, trivial⟩
  · have hv' : v < n := by simpa using hv
    rw [hr v hv']
    have := vertexValue_input ([] : List DAGGate) x ⟨v, hv'⟩
    simp only [SLOperand.eval] at this ⊢
    simp [this]

/-- The two-line gadget evaluates line by line. -/
private theorem runLines_two (ss : List (SLStmt n)) (s t : SLStmt n) (x : Fin n → Bool) :
    runLines (ss ++ [s, t]) x = runLines ss x ++
      [s.eval x (runLines ss x), t.eval x (runLines ss x ++ [s.eval x (runLines ss x)])] := by
  have : ss ++ [s, t] = (ss ++ [s]) ++ [t] := by simp
  rw [this, runLines_snoc, runLines_snoc]; simp

/-- What `emitOp` guarantees for an `o`-gate on at most two arguments `args` whose rails
read only existing lines: the new lines are valid, there are at most two of them, the new
rails read only existing lines, and if each argument's rails compute `vals.getD a` and its
complement, the new rails compute the gate's value and its complement.

**Proof sketch.** Case on the number of arguments.  Fan-in `0`: the lines
`x ∘' ¬x` and `x ∘ ¬x` are the constants `o []` and its complement.  Fan-in `1`: the gate
is the identity, reuse the argument's rails.  Fan-in `2`: the line `p ∘ q` computes the
gate, and by De Morgan the line `¬p ∘' ¬q` computes its complement; appended lines do
not change operands reading earlier lines. -/
private theorem emitOp_spec (i0 : Fin n) (o : SLOp) {ss : List (SLStmt n)} (hss : LinesValid ss)
    (rs : List (Rail n)) (args : List ℕ) (hlen : args.length ≤ 2)
    (hb : ∀ a ∈ args, (railAt rs a).1.Before ss.length ∧ (railAt rs a).2.Before ss.length) :
    let r := emitOp i0 o ss.length (args.map (railAt rs))
    LinesValid (ss ++ r.1) ∧ r.1.length ≤ 2 ∧
      r.2.1.Before (ss ++ r.1).length ∧ r.2.2.Before (ss ++ r.1).length ∧
      ∀ (x : Fin n → Bool) (vals : List Bool),
        (∀ a ∈ args, (railAt rs a).1.eval x (runLines ss x) = vals.getD a false ∧
          (railAt rs a).2.eval x (runLines ss x) = !vals.getD a false) →
        r.2.1.eval x (runLines (ss ++ r.1) x) = (⟨o.kind, args⟩ : DAGGate).eval vals ∧
          r.2.2.eval x (runLines (ss ++ r.1) x) = !(⟨o.kind, args⟩ : DAGGate).eval vals := by
  have hsnoc2 : ∀ s t : SLStmt n, s.Before ss.length → t.Before (ss.length + 1) →
      LinesValid (ss ++ [s, t]) := fun s t hs ht => by
    have : ss ++ [s, t] = (ss ++ [s]) ++ [t] := by simp
    rw [this]; exact (hss.snoc hs).snoc (by simpa using ht)
  have hget : ∀ (Y : List Bool) (u v : Bool),
      (Y ++ [u, v]).getD Y.length false = u ∧ (Y ++ [u, v]).getD (Y.length + 1) false = v :=
    fun Y u v => ⟨by simp, by simp⟩
  match args, hlen, hb with
  | [], _, _ =>
    refine ⟨hsnoc2 _ _ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩, by simp [emitOp],
      by simp [emitOp, SLOperand.Before], by simp [emitOp, SLOperand.Before], ?_⟩
    intro x vals _
    simp only [List.map_nil, emitOp, runLines_two, SLOperand.eval]
    have h := hget (runLines ss x)
    simp only [length_runLines] at h
    rw [(h _ _).1, (h _ _).2]
    cases o <;> cases x i0 <;> simp [SLStmt.eval, SLOp.apply, SLOp.dual, SLOp.kind,
      DAGGate.eval, SLOperand.eval]
  | [a], _, hb =>
    have ha := hb a (by simp)
    refine ⟨by simpa [emitOp] using hss, by simp [emitOp], by simpa [emitOp] using ha.1,
      by simpa [emitOp] using ha.2, ?_⟩
    intro x vals hv
    obtain ⟨h1, h2⟩ := hv a (by simp)
    simp only [emitOp, List.map_cons, List.map_nil, List.append_nil]
    rw [h1, h2]
    cases o <;> simp [SLOp.kind, DAGGate.eval]
  | [a, b], _, hb =>
    have ha := hb a (by simp)
    have hb' := hb b (by simp)
    refine ⟨hsnoc2 _ _ ⟨ha.1, hb'.1⟩ ⟨ha.2.mono (by omega), hb'.2.mono (by omega)⟩,
      by simp [emitOp], by simp [emitOp, SLOperand.Before], by simp [emitOp, SLOperand.Before],
      ?_⟩
    intro x vals hv
    obtain ⟨ha1, ha2⟩ := hv a (by simp)
    obtain ⟨hb1, hb2⟩ := hv b (by simp)
    simp only [emitOp, List.map_cons, List.map_nil, runLines_two, SLOperand.eval]
    have h := hget (runLines ss x)
    simp only [length_runLines] at h
    rw [(h _ _).1, (h _ _).2]
    simp only [SLStmt.eval]
    rw [SLOperand.eval_append x (by simpa using ha.2),
      SLOperand.eval_append x (by simpa using hb'.2),
      ha1, ha2, hb1, hb2]
    cases o <;> simp [SLOp.apply, SLOp.dual, SLOp.kind, DAGGate.eval]
  | _ :: _ :: _ :: _, h, _ => simp at h

/-- What `gateEmit` guarantees: emitting a gate of fan-in at most two after valid lines
appends at most two valid lines, whose output rails refer to earlier lines and, whenever
the argument rails carry each argument value and its negation, evaluate to the gate's
value and its negation. This is `emitOp_spec` for the gate's own operation, the rails
swapped for a `¬` gate.

**Proof sketch.** Case on the gate kind. For `∧` and `∨` the claim is exactly the
emission lemma for that operation. A `¬` gate is emitted as the (unary) `∧` of its
argument with the positive and negative rails exchanged, so all structural facts carry
over from the `∧` case with the two rails swapped, and its positive rail evaluates to
the negation of the argument, i.e. to the `¬` gate's value. -/
private theorem gateEmit_spec (i0 : Fin n) {ss : List (SLStmt n)} (hss : LinesValid ss)
    (rs : List (Rail n)) (g : DAGGate) (hlen : g.args.length ≤ 2)
    (hb : ∀ a ∈ g.args, (railAt rs a).1.Before ss.length ∧ (railAt rs a).2.Before ss.length) :
    let r := gateEmit i0 ss.length g (g.args.map (railAt rs))
    LinesValid (ss ++ r.1) ∧ r.1.length ≤ 2 ∧
      r.2.1.Before (ss ++ r.1).length ∧ r.2.2.Before (ss ++ r.1).length ∧
      ∀ (x : Fin n → Bool) (vals : List Bool),
        (∀ a ∈ g.args, (railAt rs a).1.eval x (runLines ss x) = vals.getD a false ∧
          (railAt rs a).2.eval x (runLines ss x) = !vals.getD a false) →
        r.2.1.eval x (runLines (ss ++ r.1) x) = g.eval vals ∧
          r.2.2.eval x (runLines (ss ++ r.1) x) = !g.eval vals := by
  obtain ⟨k, args⟩ := g
  cases k with
  | and => exact emitOp_spec i0 .and hss rs args hlen hb
  | or => exact emitOp_spec i0 .or hss rs args hlen hb
  | not =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := emitOp_spec i0 .and hss rs args hlen hb
    refine ⟨h1, h2, h4, h3, fun x vals hv => ?_⟩
    obtain ⟨e1, e2⟩ := h5 x vals hv
    refine ⟨e2, ?_⟩
    simp only [gateEmit] at e1 ⊢
    rw [e1]
    simp [DAGGate.eval, SLOp.kind]

/-- Appending lines only appends line values. -/
theorem runLines_append (ss ext : List (SLStmt n)) (x : Fin n → Bool) :
    ∃ e, runLines (ss ++ ext) x = runLines ss x ++ e := by
  induction ext using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton ext s ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e ++ [s.eval x (runLines (ss ++ ext) x)], ?_⟩
    rw [← List.append_assoc, runLines_snoc, he, List.append_assoc]

/-- An operand reading only existing lines keeps its value when lines are appended. -/
theorem _root_.BoolCircuit.SLOperand.eval_runLines_append (x : Fin n → Bool) {o : SLOperand n}
    {ss : List (SLStmt n)} (h : o.Before ss.length) (ext : List (SLStmt n)) :
    o.eval x (runLines (ss ++ ext) x) = o.eval x (runLines ss x) := by
  obtain ⟨e, he⟩ := runLines_append ss ext x
  rw [he, SLOperand.eval_append x (by simpa using h)]

/-- One simulated gate preserves the dual-rail invariant.

**Proof sketch.** Old vertices keep their rails, and their rails keep their values since
appended lines do not change earlier lines.  The new vertex's rails compute the gate's
value and complement by `gateEmit_spec`, the arguments' rails being correct by the
invariant; the gate adds at most two lines. -/
private theorem dualInv_step (i0 : Fin n) {old : List DAGGate} {g : DAGGate}
    {s : List (SLStmt n) × List (Rail n)} (hinv : DualInv n old s)
    (hg : ∀ a ∈ g.args, a < n + old.length) (hlen : g.args.length ≤ 2) :
    DualInv n (old ++ [g]) (dualStep i0 s g) := by
  obtain ⟨ss, rs⟩ := s
  obtain ⟨hrl, hval, hbef, hvalue, hle⟩ := hinv
  simp only at hrl hval hbef hvalue hle
  obtain ⟨h1, h2, h3, h4, h5⟩ := gateEmit_spec i0 hval rs g hlen fun a ha => hbef a (hg a ha)
  set r := gateEmit i0 ss.length g (g.args.map (railAt rs)) with hr
  have hstep : dualStep i0 (ss, rs) g = (ss ++ r.1, rs ++ [r.2]) := rfl
  rw [hstep]
  have hrail_old : ∀ v < n + old.length, railAt (rs ++ [r.2]) v = railAt rs v := fun v hv =>
    List.getD_append _ _ _ _ (by omega)
  have hrail_new : railAt (rs ++ [r.2]) (n + old.length) = r.2 := by
    simp [railAt, hrl]
  have hlen' : n + (old ++ [g]).length = n + old.length + 1 := by simp; omega
  refine ⟨by simp [hrl]; omega, h1, fun v hv => ?_, fun x v hv => ?_, ?_⟩
  · rw [hlen'] at hv
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
    · rw [hrail_old v hv]
      exact ⟨(hbef v hv).1.mono (by simp), (hbef v hv).2.mono (by simp)⟩
    · rw [hrail_new]; exact ⟨h3, h4⟩
  · rw [hlen'] at hv
    rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
    · rw [hrail_old v hv, vertexValue_append _ _ _ hv,
        SLOperand.eval_runLines_append x (hbef v hv).1,
        SLOperand.eval_runLines_append x (hbef v hv).2]
      exact hvalue x v hv
    · rw [hrail_new, vertexValue_last]
      exact h5 x _ fun a ha => hvalue x a (hg a ha)
  · simp only [List.length_append, List.length_singleton]
    omega

/-- The dual-rail simulation of an acyclic gate list of fan-in at most two satisfies the
invariant: every vertex's rails compute its value and its complement, with at most two
lines per gate. -/
theorem dualRail_inv (i0 : Fin n) :
    ∀ (gs : List DAGGate), GatesAcyclic n gs → (∀ g ∈ gs, g.args.length ≤ 2) →
      DualInv n gs (dualRail i0 gs) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ _; exact dualInv_nil
  | append_singleton gs g ih =>
    intro hac hlen
    have hac' : GatesAcyclic n gs := fun i hi a ha => by
      have := hac i (by simp; omega) a (by rwa [List.getElem_append_left hi])
      exact this
    have := ih hac' fun g' hg' => hlen g' (by simp [hg'])
    rw [dualRail, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hg : ∀ a ∈ g.args, a < n + gs.length := by
      intro a ha
      have := hac gs.length (by simp) a (by simpa using ha)
      simpa using this
    exact dualInv_step i0 this hg (hlen g (by simp))

end StraightLine

namespace DAGCircuit

variable (C : DAGCircuit n)

/-- The dual-rail program of a circuit with fan-in at most two and at least one input
(`i0`): the dual-rail lines of all gates, then one line `y_T = z ∧ z` copying the output's
rail.  [AB09, Ex 6.2] -/
def toStraightLine (hC : ∀ g ∈ C.gates, g.args.length ≤ 2) (i0 : Fin n) :
    StraightLineProgram n where
  stmts := (dualRail i0 C.gates).1 ++
    [⟨.and, (railAt (dualRail i0 C.gates).2 C.output).1,
      (railAt (dualRail i0 C.gates).2 C.output).1⟩]
  valid := by
    have h := dualRail_inv i0 C.gates C.args_lt hC
    exact h.valid.snoc ⟨(h.before _ C.output_lt).1, (h.before _ C.output_lt).1⟩

variable (hC : ∀ g ∈ C.gates, g.args.length ≤ 2) (i0 : Fin n)

/-- The dual-rail program computes the circuit's function.  [AB09, Ex 6.2] -/
theorem toStraightLine_eval (x : Fin n → Bool) : (C.toStraightLine hC i0).eval x = C.eval x := by
  have h := (dualRail_inv i0 C.gates C.args_lt hC).value x _ C.output_lt
  simp only [StraightLineProgram.eval, StraightLineProgram.values, StraightLineProgram.length,
    toStraightLine, runLines_snoc, List.length_append, List.length_singleton,
    Nat.add_sub_cancel]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [length_runLines, Nat.sub_self, List.getD_cons_zero, SLStmt.eval, SLOp.apply,
    Bool.and_self, h.1]
  rfl

/-- The dual-rail program of a circuit with `G` gates has at most `2G + 1` lines.
[AB09, Ex 6.2] -/
theorem toStraightLine_length_le : (C.toStraightLine hC i0).length ≤ 2 * C.gates.length + 1 := by
  have h := dualRail_inv i0 C.gates C.args_lt hC
  have := h.length_le
  simp [toStraightLine, StraightLineProgram.length]
  omega

end DAGCircuit

/-! ## [AB09, Ex 6.2]: programs and circuits -/

/-- **[AB09, Ex 6.2], program to circuit.**  If `f` is computed by a straight-line program
of at most `S` lines, it is computed by a fan-in-two circuit of size at most
`2n + max S 1`.  Deviation: [AB09] claims size `S`; a program negates inputs for free while
a circuit pays one `¬` gate per negated input, and circuit size counts the `n` inputs.

**Proof sketch.** Use `StraightLineProgram.toCircuit`: `n` negation gates, then one fan-in-two
gate per line reading the vertices of its operands. -/
theorem exists_dagCircuit_of_straightLine {f : (Fin n → Bool) → Bool} {S : ℕ}
    (h : ∃ P : StraightLineProgram n, P.length ≤ S ∧ ∀ x, P.eval x = f x) :
    ∃ C : DAGCircuit n, C.IsFaninTwo ∧ C.size ≤ 2 * n + max S 1 ∧ ∀ x, C.eval x = f x := by
  obtain ⟨P, hS, hf⟩ := h
  refine ⟨P.toCircuit, P.toCircuit_isFaninTwo, ?_, fun x => (P.toCircuit_eval x).trans (hf x)⟩
  rw [P.toCircuit_size]; omega

/-- **[AB09, Ex 6.2], circuit to program.**  If `f` on `n ≥ 1` inputs is computed by a
fan-in-two circuit of size at most `S`, it is computed by a straight-line program of at
most `2(S - n) + 1` lines (so at most `2S - 1`).  Deviation: [AB09] claims `S` lines; our
factor `2` is the cost of the dual-rail simulation of `¬` gates on non-inputs.  The literal
claim is false in the other direction (`exists_straightLine_and_not_dagCircuit`); with
`exists_dagCircuit_of_straightLine` this gives the corrected statement, both directions
within a factor `2` and an additive `2n`.  Exactly `S` lines is proved for `n ≤ 2`
(`exists_straightLine_length_le_size_of_le_two`); for `n ≥ 3` it is not decided here.  `n ≥ 1` is
needed because no program on zero inputs computes the constant `1`
(`not_exists_straightLine_true`); the book's literal model has no circuits on `0` inputs.

**Proof sketch.** Use `DAGCircuit.toStraightLine`: carry for every vertex an operand for its
value and one for its complement; `∧`/`∨` gates cost two lines (the gate and its De Morgan
dual), `¬` gates swap the two operands for free, constants cost two lines built from
`x₁ ∨ ¬x₁` and `x₁ ∧ ¬x₁`; a final line copies the output.  A circuit of size `S` has
`S - n` gates. -/
theorem exists_straightLine_of_dagCircuit (hn : 0 < n) {f : (Fin n → Bool) → Bool} {S : ℕ}
    (h : ∃ C : DAGCircuit n, C.IsFaninTwo ∧ C.size ≤ S ∧ ∀ x, C.eval x = f x) :
    ∃ P : StraightLineProgram n, P.length ≤ 2 * (S - n) + 1 ∧ ∀ x, P.eval x = f x := by
  obtain ⟨C, hC, hS, hf⟩ := h
  refine ⟨C.toStraightLine hC.2 ⟨0, hn⟩, ?_,
    fun x => (C.toStraightLine_eval hC.2 ⟨0, hn⟩ x).trans (hf x)⟩
  have := C.toStraightLine_length_le hC.2 ⟨0, hn⟩
  simp only [DAGCircuit.size] at hS
  omega

/-- The `n = 0` edge case of [AB09, Ex 6.2]: the constant `1` on zero inputs is computed by
a one-vertex circuit (an `∧` gate of fan-in `0`) but by no straight-line program, so the
circuit-to-program direction needs `n ≥ 1`. -/
theorem not_exists_straightLine_true :
    (∃ C : DAGCircuit 0, C.IsFaninTwo ∧ C.size = 1 ∧ ∀ x, C.eval x = true) ∧
      ¬ ∃ P : StraightLineProgram 0, ∀ x, P.eval x = true := by
  refine ⟨⟨constCircuit 0 true, constCircuit_isFaninTwo 0 true, rfl,
    fun x => constCircuit_eval true x⟩, ?_⟩
  rintro ⟨P, hP⟩
  have := hP Fin.elim0
  rw [P.eval_of_zero] at this
  exact Bool.false_ne_true this

end BoolCircuit
