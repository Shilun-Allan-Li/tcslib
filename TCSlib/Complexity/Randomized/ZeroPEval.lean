/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Data.ZMod.Basic
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Complexity.Randomized.AlgCircuit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Evaluating an encoded algebraic circuit modulo `k`: one gate

The gate step of the evaluator behind the class half of [AB09, §7.2.3, p.130]: from the code
of an algebraic circuit (`Randomized.AlgCircuit.encodeGates`), a point and a modulus `k`, read
one gate, check that it reads earlier nodes only, and append its value modulo `k` (so every
value has at most `log k` bits). The loop and its running time are in
`TCSlib.Complexity.Randomized.ZeroPRun`.

## Main definitions

* `Randomized.PIT.gateVal`, `Randomized.PIT.evalVals` — node values modulo `k`, in `ℕ`.
* `Randomized.PIT.absStep` — one gate on (remaining code, values so far).
* `Randomized.PIT.wStep` — the same through word functions (`uHead`, `uRest`, tag bits).
* `Randomized.PIT.gStep`, `Randomized.PIT.encState` — the step on loop-state words.

## Main results

* `Randomized.PIT.natCast_evalVals` — the values mod `k` are the circuit's values in `ZMod k`.
* `Randomized.PIT.iterate_absStep_encodeGates`, `Randomized.PIT.exists_of_iterate_absStep` —
  the steps run exactly the codes of node lists whose nodes read earlier nodes.
* `Randomized.PIT.absStep_eq_wStep`, `Randomized.PIT.gStep_encState` — the word step simulates
  the gate step.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

namespace PIT

open Complexity Turing BinArith AlgCircuit
open Complexity.LogProg (bitsVal bitsVal_bits)

variable {n : ℕ}

/-! ### Values modulo `k` -/

/-- The value modulo `k` of node `g`, from the earlier values `vs` and the point `a`. -/
def gateVal (k : ℕ) (a : ℕ → ℕ) (vs : List ℕ) : AlgGate n → ℕ
  | .var i => a i % k
  | .one => 1 % k
  | .add j l => (vs.getD j 0 + vs.getD l 0) % k
  | .sub j l => (vs.getD j 0 + (k - vs.getD l 0)) % k
  | .mul j l => (vs.getD j 0 * vs.getD l 0) % k

/-- The node values modulo `k` of the node list `gs`, after the values `vs`. -/
def evalVals (k : ℕ) (a : ℕ → ℕ) (gs : List (AlgGate n)) (vs : List ℕ) : List ℕ :=
  gs.foldl (fun vs g => vs ++ [gateVal k a vs g]) vs

/-- Reading a cast list is casting the read entry. -/
theorem getD_map_natCast {k : ℕ} (vs : List ℕ) (j : ℕ) :
    (vs.map (Nat.cast : ℕ → ZMod k)).getD j 0 = ((vs.getD j 0 : ℕ) : ZMod k) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vs[j]? <;> simp

/-- An entry of a list of residues mod `k` is at most `k`. -/
theorem getD_le {k : ℕ} {vs : List ℕ} (h : ∀ v ∈ vs, v < k) (j : ℕ) : vs.getD j 0 ≤ k := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : vs[j]? with
  | none => simp
  | some v => simpa using (h v (List.mem_of_getElem? hj)).le

/-- A node value is a residue. -/
theorem gateVal_lt {k : ℕ} (hk : 0 < k) (a : ℕ → ℕ) (vs : List ℕ) (g : AlgGate n) :
    gateVal k a vs g < k := by
  cases g <;> exact Nat.mod_lt _ hk

/-- The node value mod `k` is the node's value in `ZMod k`. -/
theorem natCast_gateVal {k : ℕ} (a : ℕ → ℕ) {vs : List ℕ} (hvs : ∀ v ∈ vs, v < k)
    (g : AlgGate n) :
    ((gateVal k a vs g : ℕ) : ZMod k) = g.eval (fun i => (a i : ZMod k)) (vs.map Nat.cast) := by
  cases g with
  | var i => simp [gateVal, AlgGate.eval]
  | one => simp [gateVal, AlgGate.eval]
  | add j l => simp only [gateVal, AlgGate.eval, getD_map_natCast, ZMod.natCast_mod, Nat.cast_add]
  | sub j l =>
    simp only [gateVal, AlgGate.eval, getD_map_natCast, ZMod.natCast_mod, Nat.cast_add,
      Nat.cast_sub (getD_le hvs l), ZMod.natCast_self]
    ring
  | mul j l => simp only [gateVal, AlgGate.eval, getD_map_natCast, ZMod.natCast_mod, Nat.cast_mul]

/-- Values mod `k` after residues `vs`, cast to `ZMod k`, follow the circuit's evaluation. -/
theorem map_evalVals {k : ℕ} (hk : 0 < k) (a : ℕ → ℕ) (gs : List (AlgGate n)) :
    ∀ vs : List ℕ, (∀ v ∈ vs, v < k) →
      (evalVals k a gs vs).map Nat.cast =
        gs.foldl (fun us g => us ++ [g.eval (fun i => (a i : ZMod k)) us]) (vs.map Nat.cast) ∧
      ∀ v ∈ evalVals k a gs vs, v < k := by
  induction gs with
  | nil => intro vs h; exact ⟨rfl, h⟩
  | cons g gs ih =>
    intro vs h
    have h' : ∀ v ∈ vs ++ [gateVal k a vs g], v < k := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h v hv
      · rw [List.mem_singleton.mp hv]; exact gateVal_lt hk a vs g
    obtain ⟨h1, h2⟩ := ih _ h'
    refine ⟨?_, h2⟩
    change (evalVals k a gs (vs ++ [gateVal k a vs g])).map Nat.cast = _
    rw [h1, List.map_append, List.map_singleton, natCast_gateVal a h g]
    rfl

/-- **Values mod `k` are values in `ZMod k`**: the residues of the nodes, cast to `ZMod k`,
are the node values of the circuit run over `ZMod k`. -/
theorem natCast_evalVals {k : ℕ} (hk : 0 < k) (a : ℕ → ℕ) (gs : List (AlgGate n)) :
    (evalVals k a gs []).map Nat.cast = run (fun i => (a i : ZMod k)) gs :=
  (map_evalVals hk a gs [] (by simp)).1

/-- The residues are below `k`. -/
theorem lt_of_mem_evalVals {k : ℕ} (hk : 0 < k) (a : ℕ → ℕ) (gs : List (AlgGate n))
    {v : ℕ} (hv : v ∈ evalVals k a gs []) : v < k :=
  (map_evalVals hk a gs [] (by simp)).2 v hv

/-- The number of values. -/
theorem length_evalVals (k : ℕ) (a : ℕ → ℕ) (gs : List (AlgGate n)) (vs : List ℕ) :
    (evalVals k a gs vs).length = vs.length + gs.length := by
  induction gs generalizing vs with
  | nil => simp [evalVals]
  | cons g gs ih =>
    change (evalVals k a gs (vs ++ [gateVal k a vs g])).length = _
    rw [ih]; simp; omega

/-! ### One gate of the evaluation -/

/-- One gate: on `(1 ++ code(g) ++ rest, vs)` with `g` reading earlier nodes only, append `g`'s
value mod `k`; `([0], vs)` (end of list) and `([], vs)` (rejected) are fixed; everything else
is rejected. -/
def absStep (n k : ℕ) (a : ℕ → ℕ) : List Bool × List ℕ → List Bool × List ℕ
  | (true :: l, vs) => match AlgGate.parse n l with
    | some (g, l') => if g.refsBelow vs.length then (l', vs ++ [gateVal k a vs g]) else ([], vs)
    | none => ([], vs)
  | ([], vs) => ([], vs)
  | ([false], vs) => ([false], vs)
  | (false :: _ :: _, vs) => ([], vs)

/-- A parsed node is the prefix it was read from.

**Proof sketch.** Unary numbers parse back to their codes (`decodeNat_eq`,
`eq_encodeNat_of_hasFalse`); a gate is a tag followed by one or two such numbers
(`AlgGate.parseBin`), so in each case of `AlgGate.parse` the consumed prefix is the gate's
code. -/
theorem parse_eq_some {l l' : List Bool} {g : AlgGate n} (h : AlgGate.parse n l = some (g, l')) :
    l = g.encode ++ l' := by
  have hdec : ∀ {w r : List Bool} {j : ℕ}, BoolCircuit.decodeNat w = some (j, r) →
      w = BoolCircuit.encodeNat j ++ r := by
    intro w r j hw
    rw [decodeNat_eq] at hw
    split at hw
    · cases hw
      exact eq_encodeNat_of_hasFalse (by assumption)
    · cases hw
  have hbin : ∀ {mk : ℕ → ℕ → AlgGate n} {w : List Bool},
      AlgGate.parseBin mk w = some (g, l') →
      ∃ j k, g = mk j k ∧ w = BoolCircuit.encodeNat j ++ BoolCircuit.encodeNat k ++ l' := by
    intro mk w hw
    unfold AlgGate.parseBin at hw
    split at hw
    · cases hw
    · rename_i j l₁ h₁
      split at hw
      · cases hw
      · rename_i k l₂ h₂
        cases hw
        exact ⟨j, k, rfl, by rw [hdec h₁, hdec h₂, List.append_assoc]⟩
  unfold AlgGate.parse at h
  split at h
  · split at h
    · cases h
    · rename_i i l₀ hd
      split_ifs at h with hi
      cases h
      simp [AlgGate.encode, hdec hd]
  · cases h
    simp [AlgGate.encode]
  · obtain ⟨j, k, rfl, rfl⟩ := hbin h
    simp [AlgGate.encode]
  · obtain ⟨j, k, rfl, rfl⟩ := hbin h
    simp [AlgGate.encode]
  · obtain ⟨j, k, rfl, rfl⟩ := hbin h
    simp [AlgGate.encode]
  · cases h

/-- **The loop runs a node list**: from `(code(gs), vs)`, if every node reads earlier nodes,
`|gs|` gates end in `([0], vs ++ values)`. -/
theorem iterate_absStep_encodeGates (k : ℕ) (a : ℕ → ℕ) :
    ∀ (gs : List (AlgGate n)) (vs : List ℕ),
      (∀ i (h : i < gs.length), gs[i].refsBelow (vs.length + i) = true) →
      (absStep n k a)^[gs.length] (encodeGates gs, vs) = ([false], evalVals k a gs vs)
  | [], vs, _ => rfl
  | g :: gs, vs, h => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have h0 : g.refsBelow vs.length = true := by simpa using h 0 (by simp)
    have hstep : absStep n k a (encodeGates (g :: gs), vs) =
        (encodeGates gs, vs ++ [gateVal k a vs g]) := by
      simp [encodeGates, absStep, AlgGate.parse_encode, h0]
    rw [hstep]
    refine iterate_absStep_encodeGates k a gs _ (fun i hi => ?_)
    have := h (i + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- **Only node lists run to the end**: if the loop reaches `([0], vs')` from `(w, vs)`, then
`w` is the code of a node list reading earlier nodes only, and `vs'` its values.

**Proof sketch.** Induction on the number of gates: a rejected state is fixed at `[]`, so it
never reaches `[0]`; an accepted gate was parsed off the front of `w` (`parse_eq_some`). -/
theorem exists_of_iterate_absStep (k : ℕ) (a : ℕ → ℕ) :
    ∀ (T : ℕ) (w : List Bool) (vs vs' : List ℕ),
      (absStep n k a)^[T] (w, vs) = ([false], vs') →
      ∃ gs : List (AlgGate n), w = encodeGates gs ∧
        (∀ i (h : i < gs.length), gs[i].refsBelow (vs.length + i) = true) ∧
        vs' = evalVals k a gs vs := by
  have hnil : ∀ T (vs : List ℕ), (absStep n k a)^[T] ([], vs) = ([], vs) :=
    fun T vs => Function.iterate_fixed rfl T
  intro T
  induction T with
  | zero =>
    intro w vs vs' h
    simp only [Function.iterate_zero, id, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, by simp, rfl⟩
  | succ T ih =>
    intro w vs vs' h
    rw [Function.iterate_succ_apply] at h
    match w, h with
    | [], h => rw [show absStep n k a ([], vs) = ([], vs) from rfl, hnil] at h; simp at h
    | [false], h =>
      rw [show absStep n k a ([false], vs) = ([false], vs) from rfl,
        Function.iterate_fixed rfl] at h
      simp only [Prod.mk.injEq, true_and] at h
      exact ⟨[], rfl, by simp, h.symm⟩
    | false :: _ :: _, h =>
      rw [show absStep n k a (false :: _ :: _, vs) = ([], vs) from rfl, hnil] at h; simp at h
    | true :: l, h =>
      cases hp : AlgGate.parse n l with
      | none =>
        rw [show absStep n k a (true :: l, vs) = ([], vs) by simp [absStep, hp], hnil] at h
        simp at h
      | some p =>
        obtain ⟨g, l'⟩ := p
        by_cases hr : g.refsBelow vs.length = true
        · rw [show absStep n k a (true :: l, vs) = (l', vs ++ [gateVal k a vs g]) by
            simp [absStep, hp, hr]] at h
          obtain ⟨gs, hgs, href, hvs⟩ := ih _ _ _ h
          refine ⟨g :: gs, by rw [parse_eq_some hp, hgs]; rfl, fun i hi => ?_, hvs⟩
          cases i with
          | zero => simpa using hr
          | succ i =>
            have := href i (by simp at hi; omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
        · rw [show absStep n k a (true :: l, vs) = ([], vs) by simp [absStep, hp, hr], hnil] at h
          simp at h

/-! ### The gate step on words -/

/-- The `i`-th letter of `w` (`0` past the end). -/
def tagBit (i : ℕ) (w : List Bool) : Bool := (w.drop i).headD false

/-- The indices of the gate at the front of `w`: everything after its 4-bit header. -/
def bodyW (w : List Bool) : List Bool := w.drop 4

/-- The first index (unary). -/
def arg1W (w : List Bool) : List Bool := uHead (bodyW w)

/-- The word after the first index. -/
def midW (w : List Bool) : List Bool := uRest (bodyW w)

/-- The second index (unary). -/
def arg2W (w : List Bool) : List Bool := uHead (midW w)

/-- The word after the second index. -/
def rest2W (w : List Bool) : List Bool := uRest (midW w)

/-- Tag `000`: a variable. -/
def isVarW (w : List Bool) : Bool := !tagBit 1 w && !tagBit 2 w && !tagBit 3 w

/-- Tag `001`: the constant `1`. -/
def isOneW (w : List Bool) : Bool := !tagBit 1 w && !tagBit 2 w && tagBit 3 w

/-- Tag `010`: `+`. -/
def isAddW (w : List Bool) : Bool := !tagBit 1 w && tagBit 2 w && !tagBit 3 w

/-- Tag `011`: `−`. -/
def isSubW (w : List Bool) : Bool := !tagBit 1 w && tagBit 2 w && tagBit 3 w

/-- Tag `100`: `×`. -/
def isMulW (w : List Bool) : Bool := tagBit 1 w && !tagBit 2 w && !tagBit 3 w

/-- The loop has stopped: `w = []` (rejected) or `w = [0]` (end of list). -/
def isDone (w : List Bool) : Bool := isNilB w || (isNilB (w.drop 1) && !(w.headD false))

/-- The gate at the front of `w` is well formed for `n` inputs and `i` earlier nodes. -/
def okW (n i : ℕ) (w : List Bool) : Bool :=
  w.headD false && ((isVarW w && hasFalse (bodyW w) && decide ((arg1W w).length < n)) ||
    isOneW w || ((isAddW w || isSubW w || isMulW w) && hasFalse (bodyW w) &&
      hasFalse (midW w) && decide ((arg1W w).length < i) && decide ((arg2W w).length < i)))

/-- The code after the gate at the front of `w`. -/
def restW (w : List Bool) : List Bool :=
  if isVarW w then midW w else if isOneW w then bodyW w else rest2W w

/-- The value mod `k` of the gate at the front of `w`. -/
def valN (k : ℕ) (a : ℕ → ℕ) (vs : List ℕ) (w : List Bool) : ℕ :=
  if isVarW w then a (arg1W w).length % k
  else if isOneW w then 1 % k
  else if isAddW w then (vs.getD (arg1W w).length 0 + vs.getD (arg2W w).length 0) % k
  else if isSubW w then (vs.getD (arg1W w).length 0 + (k - vs.getD (arg2W w).length 0)) % k
  else (vs.getD (arg1W w).length 0 * vs.getD (arg2W w).length 0) % k

/-- `absStep` through the word functions above. -/
def wStep (n k : ℕ) (a : ℕ → ℕ) (s : List Bool × List ℕ) : List Bool × List ℕ :=
  if isDone s.1 then s
  else if okW n s.2.length s.1 then (restW s.1, s.2 ++ [valN k a s.2 s.1]) else ([], s.2)

/-- The gate step through word functions is the gate step.

**Proof sketch.** Case analysis on the first four letters of `w` and on whether the index
fields end (`decodeNat_eq`): the header selects the node kind exactly as `AlgGate.parse` does,
and the unary fields are read by `uHead`/`uRest`. -/
theorem absStep_eq_wStep (k : ℕ) (a : ℕ → ℕ) (w : List Bool) (vs : List ℕ) :
    absStep n k a (w, vs) = wStep n k a (w, vs) := by
  match w with
  | [] => rfl
  | [false] => rfl
  | false :: b :: l =>
    simp [absStep, wStep, isDone, isNilB, okW]
  | [true] => simp [absStep, wStep, isDone, isNilB, okW, AlgGate.parse, isVarW, isOneW, isAddW,
      isSubW, isMulW, tagBit, bodyW]
  | [true, t] => cases t <;> simp [absStep, wStep, isDone, isNilB, okW, AlgGate.parse, isVarW,
      isOneW, isAddW, isSubW, isMulW, tagBit, bodyW]
  | [true, t, t'] => cases t <;> cases t' <;> simp [absStep, wStep, isDone, isNilB, okW,
      AlgGate.parse, isVarW, isOneW, isAddW, isSubW, isMulW, tagBit, bodyW]
  | true :: t₀ :: t₁ :: t₂ :: body =>
    have h1 := decodeNat_eq body
    have h2 := decodeNat_eq (uRest body)
    cases t₀ <;> cases t₁ <;> cases t₂ <;>
      cases hb : hasFalse body <;> cases hm : hasFalse (uRest body) <;>
      simp only [hb, hm, if_true, if_false, Bool.false_eq_true] at h1 h2 <;>
      by_cases hn : (uHead body).length < n <;>
      simp [absStep, wStep, isDone, isNilB, okW, AlgGate.parse, AlgGate.parseBin, isVarW,
        isOneW, isAddW, isSubW, isMulW, tagBit, bodyW, midW, arg1W, arg2W, restW, rest2W, valN,
        h1, h2, hb, hm, AlgGate.refsBelow, gateVal, hn]

/-- The gate step through word functions, as a function. -/
theorem wStep_eq_absStep (k : ℕ) (a : ℕ → ℕ) : wStep n k a = absStep n k a := by
  funext s
  obtain ⟨w, vs⟩ := s
  exact (absStep_eq_wStep k a w vs).symm

/-! ### The loop on words

A loop state is `⟨ctx, ⟨w, ⟨1^i, values⟩⟩⟩`: the context `ctx = ⟨1^n, ⟨R, P⟩⟩` (number of
inputs, modulus `k = R + 1`, list `P` of point coordinates minus one), the remaining code `w`,
the number `i` of nodes read, and their values as an encoded list of binary numbers. -/

/-- The context slot. -/
def sCtx (D : List Bool) : List Bool := pairFstD D

/-- The remaining code. -/
def sW (D : List Bool) : List Bool := pairFstD (pairSndD D)

/-- The number of nodes read, in unary. -/
def sI (D : List Bool) : List Bool := pairFstD (pairSndD (pairSndD D))

/-- The list of node values. -/
def sL (D : List Bool) : List Bool := pairSndD (pairSndD (pairSndD D))

/-- The number of inputs, in unary. -/
def sN (D : List Bool) : List Bool := pairFstD (sCtx D)

/-- The modulus minus one. -/
def sRaw (D : List Bool) : List Bool := pairFstD (pairSndD (sCtx D))

/-- The point coordinates minus one, as an encoded list. -/
def sPts (D : List Bool) : List Bool := pairSndD (pairSndD (sCtx D))

/-- The modulus `k = R + 1`. -/
def sK (D : List Bool) : List Bool := BinArith.add (pairEncode (sRaw D) [true])

/-- The value of the node with index `|J|`. -/
def xW (J D : List Bool) : List Bool := getW (pairEncode J (sL D))

/-- The value of the gate at the front of the code, before reduction mod `k`. -/
def rawValW (D : List Bool) : List Bool :=
  if isVarW (sW D) then BinArith.add (pairEncode (getW (pairEncode (arg1W (sW D)) (sPts D))) [true])
  else if isOneW (sW D) then [true]
  else if isAddW (sW D) then BinArith.add (pairEncode (xW (arg1W (sW D)) D) (xW (arg2W (sW D)) D))
  else if isSubW (sW D) then BinArith.add (pairEncode (xW (arg1W (sW D)) D)
    (BinArith.sub (pairEncode (sK D) (xW (arg2W (sW D)) D))))
  else BinArith.mul (pairEncode (xW (arg1W (sW D)) D) (xW (arg2W (sW D)) D))

/-- The value of the gate at the front of the code, mod `k`. -/
def valW (D : List Bool) : List Bool := BinArith.mod (pairEncode (rawValW D) (sK D))

/-- **One gate on words**: a stopped state is fixed; a well-formed gate is consumed and its
value appended; otherwise the code is replaced by `[]` (rejected). -/
def gStep (D : List Bool) : List Bool :=
  if isDone (sW D) then D
  else if okW (sN D).length (sI D).length (sW D) then
    pairEncode (sCtx D) (pairEncode (restW (sW D))
      (pairEncode (true :: sI D) (sL D ++ pairEncode (valW D) [])))
  else pairEncode (sCtx D) (pairEncode [] (pairEncode (sI D) (sL D)))

/-- The context `⟨1^n, ⟨R, P⟩⟩`. -/
def ctxOf (n : ℕ) (R : List Bool) (P : List (List Bool)) : List Bool :=
  pairEncode (List.replicate n true) (pairEncode R (encWords P))

/-- The `i`-th point coordinate: one plus the value of the `i`-th entry of `P`. -/
def ptVal (P : List (List Bool)) (i : ℕ) : ℕ := bitsVal (P.getD i []) + 1

/-- The loop state with context `ctx`, remaining code `w` and node values `vs`. -/
def encState (ctx w : List Bool) (vs : List ℕ) : List Bool :=
  pairEncode ctx (pairEncode w (pairEncode (List.replicate vs.length true)
    (encWords (vs.map Nat.bits))))

/-- The word step on an encoded state is the gate step. -/
theorem gStep_encState (R : List Bool) (P : List (List Bool)) (w : List Bool) (vs : List ℕ) :
    gStep (encState (ctxOf n R P) w vs) =
      encState (ctxOf n R P) (wStep n (bitsVal R + 1) (ptVal P) (w, vs)).1
        (wStep n (bitsVal R + 1) (ptVal P) (w, vs)).2 := by
  have hval : valW (encState (ctxOf n R P) w vs) =
      Nat.bits (valN (bitsVal R + 1) (ptVal P) vs w) := by
    simp only [valW, rawValW, sK, xW, sRaw, sPts, sL, sW, sCtx, encState, ctxOf,
      pairFstD_pairEncode, pairSndD_pairEncode, getW_pairEncode_bits, valN]
    simp only [getW_pairEncode]
    split_ifs <;> simp [BinArith.add, BinArith.sub, BinArith.mul, BinArith.mod, bitsVal_bits,
      ptVal, bitsVal]
  unfold gStep
  rw [hval]
  simp only [wStep, sW, sCtx, sI, sL, sN, encState, ctxOf, pairFstD_pairEncode,
    pairSndD_pairEncode, List.length_replicate]
  split_ifs
  · rfl
  · simp [encWords_append_singleton, List.replicate_succ]
  · rfl

/-- The word loop follows the gate loop. -/
theorem iterate_gStep (R : List Bool) (P : List (List Bool)) :
    ∀ (T : ℕ) (w : List Bool) (vs : List ℕ),
      gStep^[T] (encState (ctxOf n R P) w vs) =
        encState (ctxOf n R P) ((absStep n (bitsVal R + 1) (ptVal P))^[T] (w, vs)).1
          ((absStep n (bitsVal R + 1) (ptVal P))^[T] (w, vs)).2 := by
  intro T
  induction T with
  | zero => intro w vs; rfl
  | succ T ih =>
    intro w vs
    rw [Function.iterate_succ_apply, gStep_encState, wStep_eq_absStep, ih,
      Function.iterate_succ_apply]

end PIT

end Randomized
