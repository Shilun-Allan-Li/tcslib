/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.CircuitEvalSpec

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Correctness of the circuit-value algorithm

The streaming circuit-value algorithm of
`TCSlib.Complexity.CircuitComplexity.CircuitEvalSpec` accepts exactly the descriptions of
fan-in-two circuits that output `1`: each phase of the abstract run is characterized by
an equivalence (`absRun_u`, `absRun_o`, `absRun_a`, `absRun_g`) between "the run from
this phase accepts the remaining bits" and "the remaining bits are the code of the
expected piece of a circuit description, satisfying the fan-in-two conditions, and the
run accepts what follows". Composing them gives `verdict_pairEncode`.

## Main definitions

* `BoolCircuit.CircuitEval.GatesOK` — the fan-in-two and acyclicity conditions on a gate
  list, in the form the streaming run checks them.

## Main results

* `BoolCircuit.CircuitEval.absRun_g` — the run from the gate-list phase accepts iff the
  rest is the code of a gate list and an output vertex of a fan-in-two circuit with
  output `1`.
* `BoolCircuit.CircuitEval.verdict_pairEncode` — the verdict on `pairEncode code x` is
  `true` iff `code` is the description of a fan-in-two circuit `C` on `n` inputs, with
  `n ≤ |x|` (`n = |x|` if `exact`), and `C` outputs `1` on the first `n` bits of `x`.

## Length

This file exceeds the 600-line target (about 650 lines): its four phase lemmas are
mutually dependent inductions over one streaming run, each needing both directions of
an equivalence, and are kept together with the theorem that composes them.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.1, Definition 6.1; p. 111.)
-/

namespace BoolCircuit

namespace CircuitEval

/-- The fan-in-two conditions on a gate list whose first gate sees `len` vertices:
each gate has at most two pairwise distinct arguments, all below the number of vertices
before it, and a `¬` gate has exactly one. -/
def GatesOK : List DAGGate → ℕ → Prop
  | [], _ => True
  | g :: gs, len =>
    (g.args.length ≤ 2 ∧ g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧
      ∀ a ∈ g.args, a < len) ∧ GatesOK gs (len + 1)

/-- The accumulator fold computes the gate's value.

**Proof sketch.** Folding `acc && v` from `b` gives `b && all`, folding `acc || v` gives `b || any`
(induction on the argument list); compare with the three cases of `DAGGate.eval`. -/
theorem accFin_foldl (k : GateKind) (args : List ℕ) (vals : List Bool) :
    accFin k (args.foldl (fun acc a => accComb k acc (vals.getD a false)) (accInit k)) =
      DAGGate.eval ⟨k, args⟩ vals := by
  have hand : ∀ (f : ℕ → Bool) (l : List ℕ) (b : Bool),
      l.foldl (fun acc a => acc && f a) b = (b && l.all f) := by
    intro f l
    induction l with
    | nil => simp
    | cons a l ih => intro b; rw [List.foldl_cons, ih]; simp [Bool.and_assoc]
  have hor : ∀ (f : ℕ → Bool) (l : List ℕ) (b : Bool),
      l.foldl (fun acc a => acc || f a) b = (b || l.any f) := by
    intro f l
    induction l with
    | nil => simp
    | cons a l ih => intro b; rw [List.foldl_cons, ih]; simp [Bool.or_assoc]
  cases k
  · simp only [accFin, accComb, accInit, DAGGate.eval]
    rw [hand]; simp
  · simp only [accFin, accComb, accInit, DAGGate.eval]
    rw [hor]; simp
  · simp only [accFin, accComb, accInit, DAGGate.eval]
    rw [hand]; simp

/-- Walking a unary argument: from phase `u` at head `j`, the run accepts iff the
remaining bits are `1ʳ0` followed by `rest`, the cell `j + r` holds a value and is not
yet marked, and the run accepts `rest` after folding that value in and marking the
cell.

**Proof sketch.** Induct on the bits, generalizing `j`. At the end of the description, or at a
`1` over a blank cell, the run rejects and no decomposition exists. At a `0` it reads cell
`j` (so `r = 0`), rejecting on a blank or a marked cell. A `1` over a value cell moves the
head to `j + 1`, shifting `r` by one. -/
theorem absRun_u (k : GateKind) (c : Fin 3) (acc : Bool) (vals : List Bool) (ms : List ℕ) :
    ∀ (l : List Bool) (j : ℕ), absRun ⟨.u k c acc, vals, ms, j⟩ l = true ↔
      ∃ r rest, l = List.replicate r true ++ false :: rest ∧ j + r < vals.length ∧
        j + r ∉ ms ∧
        absRun ⟨.a k (c + 1) (accComb k acc (vals.getD (j + r) false)), vals,
          (j + r) :: ms, 0⟩ rest = true := by
  intro l
  induction l with
  | nil =>
    intro j
    constructor
    · intro h
      simp [absRun, absStep, absOf, lact, LA.rej] at h
    · rintro ⟨r, rest, h, -⟩
      cases r <;> simp at h
  | cons b l ih =>
    intro j
    cases b with
    | false =>
      constructor
      · intro h
        rcases hv : vals[j]? with _ | v
        · simp [absRun, absStep, absOf, lact, LA.rej, hv] at h
        · by_cases hm : j ∈ ms
          · simp [absRun, absStep, absOf, lact, LA.rej, hv, markCell, hm] at h
          · have hj : j < vals.length := by
              by_contra hc; simp [List.getElem?_eq_none (by omega : vals.length ≤ j)] at hv
            have hg : vals.getD j false = v := by simp [List.getD_eq_getElem?_getD, hv]
            refine ⟨0, l, rfl, by simpa using hj, by simpa using hm, ?_⟩
            simpa [absRun, absStep, absOf, lact, hv, markCell, hm, hg] using h
      · rintro ⟨r, rest, hl, hj, hm, h⟩
        cases r with
        | succ r => simp [List.replicate_succ] at hl
        | zero =>
          simp only [List.replicate_zero, List.nil_append, List.cons.injEq, true_and] at hl
          subst hl
          simp only [Nat.add_zero] at hj hm h
          have hv : vals[j]? = some vals[j] := List.getElem?_eq_getElem hj
          have hg : vals.getD j false = vals[j] := by
            simp [List.getD_eq_getElem?_getD, hv]
          rw [hg] at h
          simpa [absRun, absStep, absOf, lact, hv, markCell, hm] using h
    | true =>
      rcases hv : vals[j]? with _ | v
      · constructor
        · intro h
          simp [absRun, absStep, absOf, lact, LA.rej, hv] at h
        · rintro ⟨r, rest, hl, hj, -⟩
          have : vals.length ≤ j := by simpa using hv
          omega
      · have hstep : absRun ⟨.u k c acc, vals, ms, j⟩ (true :: l) =
            absRun ⟨.u k c acc, vals, ms, j + 1⟩ l := by
          simp [absRun, absStep, absOf, lact, hv]
        rw [hstep, ih (j + 1)]
        constructor
        · rintro ⟨r, rest, hl, hj, hm, h⟩
          refine ⟨r + 1, rest, by simp [hl, List.replicate_succ], by omega,
            by rwa [show j + (r + 1) = j + 1 + r by omega], ?_⟩
          rwa [show j + (r + 1) = j + 1 + r by omega]
        · rintro ⟨r, rest, hl, hj, hm, h⟩
          cases r with
          | zero => simp at hl
          | succ r =>
            simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at hl
            refine ⟨r, rest, hl, by omega, by rwa [show j + 1 + r = j + (r + 1) by omega], ?_⟩
            rwa [show j + 1 + r = j + (r + 1) by omega]

/-- Walking the output vertex: the run accepts iff the remaining bits are exactly `1ʳ0`
with `j + r` a vertex whose value is `1`.

**Proof sketch.** Induct on the bits, generalizing `j`, as for `absRun_u`; after the `0` the
phase `fin v` accepts iff the description ends there, with verdict `v`. -/
theorem absRun_o (vals : List Bool) (ms : List ℕ) :
    ∀ (l : List Bool) (j : ℕ), absRun ⟨.o, vals, ms, j⟩ l = true ↔
      ∃ r, l = List.replicate r true ++ [false] ∧ j + r < vals.length ∧
        vals.getD (j + r) false = true := by
  intro l
  induction l with
  | nil =>
    intro j
    constructor
    · intro h
      simp [absRun, absStep, absOf, lact, LA.rej] at h
    · rintro ⟨r, h, -⟩
      cases r <;> simp at h
  | cons b l ih =>
    intro j
    cases b with
    | false =>
      constructor
      · intro h
        rcases hv : vals[j]? with _ | v
        · simp [absRun, absStep, absOf, lact, LA.rej, hv] at h
        · have hj : j < vals.length := by
            by_contra hc; simp [List.getElem?_eq_none (by omega : vals.length ≤ j)] at hv
          have hg : vals.getD j false = v := by simp [List.getD_eq_getElem?_getD, hv]
          rcases l with _ | ⟨b, l⟩
          · refine ⟨0, rfl, by simpa using hj, ?_⟩
            simpa [absRun, absStep, absOf, lact, hv, hg, LA.go] using h
          · simp [absRun, absStep, absOf, lact, hv, LA.go, LA.rej] at h
      · rintro ⟨r, hl, hj, h⟩
        cases r with
        | succ r => simp [List.replicate_succ] at hl
        | zero =>
          simp only [List.replicate_zero, List.nil_append, List.cons.injEq, true_and] at hl
          subst hl
          simp only [Nat.add_zero] at hj h
          have hv : vals[j]? = some vals[j] := List.getElem?_eq_getElem hj
          have hg : vals.getD j false = vals[j] := by
            simp [List.getD_eq_getElem?_getD, hv]
          rw [hg] at h
          simpa [absRun, absStep, absOf, lact, hv, LA.go] using h
    | true =>
      rcases hv : vals[j]? with _ | v
      · constructor
        · intro h
          simp [absRun, absStep, absOf, lact, LA.rej, hv] at h
        · rintro ⟨r, hl, hj, -⟩
          have : vals.length ≤ j := by simpa using hv
          omega
      · have hstep : absRun ⟨.o, vals, ms, j⟩ (true :: l) =
            absRun ⟨.o, vals, ms, j + 1⟩ l := by
          simp [absRun, absStep, absOf, lact, hv]
        rw [hstep, ih (j + 1)]
        constructor
        · rintro ⟨r, hl, hj, h⟩
          refine ⟨r + 1, by simp [hl, List.replicate_succ], by omega, ?_⟩
          rwa [show j + (r + 1) = j + 1 + r by omega]
        · rintro ⟨r, hl, hj, h⟩
          cases r with
          | zero => simp at hl
          | succ r =>
            simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at hl
            refine ⟨r, hl, by omega, ?_⟩
            rwa [show j + 1 + r = j + (r + 1) by omega]

/-- Reading an argument list after the arguments `pre` (marked, folded into `acc`):
the run accepts iff the remaining bits are the code of an argument list `args` followed
by `rest`, all of `pre ++ args` is a fan-in-two argument list of distinct vertices, and
the run accepts `rest` after appending the gate value.

**Proof sketch.** Induct on the number `m = 2 - |pre|` of arguments still allowed. A `0` ends
the list: after the `¬`-arity check (`c` counts `pre`) the run appends `accFin k acc`,
the gate's value by `accFin_foldl`. A `1` starts an argument: it is rejected when two
arguments were read already (`m = 0`); otherwise `absRun_u` walks it, checking that it is
a vertex and unmarked (the marks are `pre`, which gives distinctness), and the induction
hypothesis applies to `pre ++ [a]`. -/
theorem absRun_a (k : GateKind) (vals : List Bool) :
    ∀ (m : ℕ) (pre : List ℕ) (c : Fin 3) (ms : List ℕ) (l : List Bool),
      pre.length + m = 2 → c.val = pre.length → pre.Nodup →
      (∀ a ∈ pre, a < vals.length) →
      (∀ a, a ∈ ms ↔ a ∈ pre) →
      (absRun ⟨.a k c (pre.foldl (fun acc a => accComb k acc (vals.getD a false))
          (accInit k)), vals, ms, 0⟩ l = true ↔
        ∃ args rest, l = encodeList encodeNat args ++ rest ∧ (pre ++ args).length ≤ 2 ∧
          (pre ++ args).Nodup ∧ (∀ a ∈ args, a < vals.length) ∧
          (k = .not → (pre ++ args).length = 1) ∧
          absRun ⟨.g, vals ++ [DAGGate.eval ⟨k, pre ++ args⟩ vals], [], 0⟩
            rest = true) := by
  -- the end of the argument list, shared by every stage
  have hend : ∀ (pre : List ℕ) (c : Fin 3) (ms : List ℕ) (rest : List Bool),
      pre.length ≤ 2 → c.val = pre.length → pre.Nodup →
      (absRun ⟨.a k c (pre.foldl (fun acc a => accComb k acc (vals.getD a false))
          (accInit k)), vals, ms, 0⟩ (false :: rest) = true ↔
        ∃ args rest', false :: rest = encodeList encodeNat args ++ rest' ∧
          (pre ++ args).length ≤ 2 ∧ (pre ++ args).Nodup ∧
          (∀ a ∈ args, a < vals.length) ∧
          (k = .not → (pre ++ args).length = 1) ∧
          absRun ⟨.g, vals ++ [DAGGate.eval ⟨k, pre ++ args⟩ vals], [], 0⟩
            rest' = true) := by
    intro pre c ms rest hle hc hnd
    have hstep : absRun ⟨.a k c (pre.foldl (fun acc a => accComb k acc (vals.getD a false))
        (accInit k)), vals, ms, 0⟩ (false :: rest) =
        if k = .not ∧ c ≠ 1 then false
        else absRun ⟨.g, vals ++ [DAGGate.eval ⟨k, pre⟩ vals], [], 0⟩ rest := by
      rw [← accFin_foldl]
      by_cases h : k = .not ∧ c ≠ 1
      · simp [absRun, absStep, absOf, lact, LA.rej, h]
      · simp only [h, if_false]
        simp only [absRun, absStep, lact, h, if_false, LA.go, absOf]
    have hc1 : (c ≠ 1) ↔ pre.length ≠ 1 := by
      constructor
      · intro h h'; exact h (Fin.ext (by rw [hc, h']; rfl))
      · intro h h'; exact h (by rw [← hc, h']; rfl)
    rw [hstep]
    constructor
    · intro h
      by_cases hk : k = .not ∧ c ≠ 1
      · simp [hk] at h
      · simp only [hk, if_false] at h
        refine ⟨[], rest, by simp [encodeList], by simpa using hle, by simpa using hnd,
          by simp, ?_, by simpa using h⟩
        intro hkn
        by_contra hne
        exact hk ⟨hkn, hc1.mpr (by simpa using hne)⟩
    · rintro ⟨args, rest', hl, -, -, -, hk, h⟩
      cases args with
      | cons a args => simp [encodeList] at hl
      | nil =>
        simp only [encodeList, List.singleton_append, List.cons.injEq, true_and] at hl
        subst hl
        simp only [List.append_nil] at hk h
        have hk' : ¬(k = .not ∧ c ≠ 1) := fun ⟨h1, h2⟩ => hc1.mp h2 (hk h1)
        simpa [hk'] using h
  intro m
  induction m with
  | zero =>
    intro pre c ms l hlen hc hnd hlt hms
    rcases l with _ | ⟨b, l⟩
    · constructor
      · intro h
        simp [absRun, absStep, absOf, lact, LA.rej] at h
      · rintro ⟨args, rest, h, -⟩
        cases args <;> simp [encodeList] at h
    · cases b with
      | false => exact hend pre c ms l (by omega) hc hnd
      | true =>
        have hc2 : c = 2 := Fin.ext (by rw [hc]; simp; omega)
        constructor
        · intro h
          simp [absRun, absStep, absOf, lact, LA.rej, hc2] at h
        · rintro ⟨args, rest, hl, hle, -⟩
          cases args with
          | nil => simp [encodeList] at hl
          | cons a args => simp at hle; omega
  | succ m ih =>
    intro pre c ms l hlen hc hnd hlt hms
    rcases l with _ | ⟨b, l⟩
    · constructor
      · intro h
        simp [absRun, absStep, absOf, lact, LA.rej] at h
      · rintro ⟨args, rest, h, -⟩
        cases args <;> simp [encodeList] at h
    · cases b with
      | false => exact hend pre c ms l (by omega) hc hnd
      | true =>
        have hc2 : c ≠ 2 := fun h => by rw [h] at hc; simp at hc; omega
        have hstep : absRun ⟨.a k c (pre.foldl (fun acc a => accComb k acc (vals.getD a false))
            (accInit k)), vals, ms, 0⟩ (true :: l) =
            absRun ⟨.u k c (pre.foldl (fun acc a => accComb k acc (vals.getD a false))
              (accInit k)), vals, ms, 0⟩ l := by
          simp [absRun, absStep, absOf, lact, hc2, LA.go]
        rw [hstep, absRun_u]
        have hc' : (c + 1).val = (pre ++ [0]).length := by
          simp [Fin.val_add, hc]; omega
        constructor
        · rintro ⟨r, rest, hl, hr, hrm, h⟩
          simp only [Nat.zero_add] at hr hrm h
          have hfold : (pre ++ [r]).foldl (fun acc a => accComb k acc (vals.getD a false))
              (accInit k) = accComb k (pre.foldl (fun acc a => accComb k acc
                (vals.getD a false)) (accInit k)) (vals.getD r false) := by
            simp [List.foldl_append]
          rw [← hfold] at h
          have hrpre : r ∉ pre := fun h' => hrm ((hms r).mpr h')
          have := (ih (pre ++ [r]) (c + 1) (r :: ms) rest (by simp; omega)
            (by simpa using hc') (List.nodup_append.mpr ⟨hnd, by simp, fun a ha b hb => by
              simp at hb; subst hb; exact fun h => hrpre (h ▸ ha)⟩)
            (by intro a ha; simp at ha; rcases ha with ha | rfl; exact hlt a ha; exact hr)
            (by intro a; simp [hms a, or_comm])).mp h
          obtain ⟨args, rest', hl', hle, hnd', hargs, hk, h'⟩ := this
          refine ⟨r :: args, rest', ?_, by simpa using hle, by simpa using hnd',
            ?_, by simpa using hk, by simpa using h'⟩
          · rw [hl, hl']; simp [encodeList, encodeNat]
          · intro a ha; simp at ha; rcases ha with rfl | ha; exact hr; exact hargs a ha
        · rintro ⟨args, rest, hl, hle, hnd', hargs, hk, h⟩
          cases args with
          | nil => simp [encodeList] at hl
          | cons r args =>
            simp only [encodeList, encodeNat, List.cons_append, List.cons.injEq, true_and,
              List.append_assoc] at hl
            have hr : r < vals.length := hargs r (by simp)
            have hrpre : r ∉ pre := by
              intro h'; exact (List.nodup_append.mp hnd').2.2 r h' r (by simp) rfl
            have hfold : (pre ++ [r]).foldl (fun acc a => accComb k acc (vals.getD a false))
                (accInit k) = accComb k (pre.foldl (fun acc a => accComb k acc
                  (vals.getD a false)) (accInit k)) (vals.getD r false) := by
              simp [List.foldl_append]
            refine ⟨r, encodeList encodeNat args ++ rest, hl, by simpa using hr,
              fun h' => hrpre ((hms r).mp (by simpa using h')), ?_⟩
            simp only [Nat.zero_add]
            rw [← hfold]
            refine (ih (pre ++ [r]) (c + 1) (r :: ms) _ (by simp; omega)
              (by simpa using hc')
              (List.nodup_append.mpr ⟨hnd, by simp, fun a ha b hb => by
                simp at hb; subst hb; exact fun h => hrpre (h ▸ ha)⟩)
              (by intro a ha; simp at ha; rcases ha with ha | rfl; exact hlt a ha; exact hr)
              (by intro a; simp [hms a, or_comm])).mpr
              ⟨args, rest, rfl, by simpa using hle, by simpa using hnd',
                fun a ha => hargs a (by simp [ha]), by simpa using hk, by simpa using h⟩

/-- The gate list: from phase `g` with the value list `vals`, the run accepts iff the
remaining bits are the code of a gate list `gs` followed by the code of an output
vertex `o`, the gates satisfy the fan-in-two conditions, and vertex `o` exists and has
value `1` after running the gates.

**Proof sketch.** Strong induction on the number of remaining bits. A `0` ends the gate list
and `absRun_o` reads the output vertex. A `1` starts a gate: two label bits (`11` is
rejected; the others are `GateKind.encode (kindOf b₁ b₂)`), then the argument list by
`absRun_a` with no previous arguments, after which the run continues in the gate-list
phase, with the gate's value appended, on a strictly shorter suffix. -/
theorem absRun_g : ∀ (l : List Bool) (vals : List Bool),
    absRun ⟨.g, vals, [], 0⟩ l = true ↔
      ∃ gs o, l = encodeList DAGGate.encode gs ++ encodeNat o ∧ GatesOK gs vals.length ∧
        o < vals.length + gs.length ∧ (runWith DAGGate.eval gs vals).getD o false = true := by
  have hkind : ∀ b₁ b₂ : Bool, (b₁ && b₂) = false →
      (kindOf b₁ b₂).encode = [b₁, b₂] := by
    decide
  have hkind' : ∀ k : GateKind, ∃ b₁ b₂ : Bool, k.encode = [b₁, b₂] ∧
      (b₁ && b₂) = false ∧
      kindOf b₁ b₂ = k := by
    intro k; cases k
    · exact ⟨false, false, rfl, rfl, rfl⟩
    · exact ⟨false, true, rfl, rfl, rfl⟩
    · exact ⟨true, false, rfl, rfl, rfl⟩
  suffices H : ∀ (N : ℕ) (l : List Bool), l.length ≤ N → ∀ vals : List Bool,
      (absRun ⟨.g, vals, [], 0⟩ l = true ↔
        ∃ gs o, l = encodeList DAGGate.encode gs ++ encodeNat o ∧ GatesOK gs vals.length ∧
          o < vals.length + gs.length ∧
          (runWith DAGGate.eval gs vals).getD o false = true) by
    intro l vals; exact H l.length l le_rfl vals
  intro N
  induction N with
  | zero =>
    intro l hl vals
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    constructor
    · intro h; simp [absRun, absStep, absOf, lact, LA.rej] at h
    · rintro ⟨gs, o, h, -⟩; cases gs <;> simp [encodeList] at h
  | succ N ih =>
    intro l hl vals
    rcases l with _ | ⟨b, l⟩
    · constructor
      · intro h; simp [absRun, absStep, absOf, lact, LA.rej] at h
      · rintro ⟨gs, o, h, -⟩; cases gs <;> simp [encodeList] at h
    cases b with
    | false =>
      have hstep : absRun ⟨.g, vals, [], 0⟩ (false :: l) = absRun ⟨.o, vals, [], 0⟩ l := by
        simp [absRun, absStep, absOf, lact, LA.go]
      rw [hstep, absRun_o]
      constructor
      · rintro ⟨r, hl', hr, hv⟩
        refine ⟨[], r, ?_, trivial, by simpa using hr, by simpa using hv⟩
        simp [hl', encodeList, encodeNat]
      · rintro ⟨gs, o, h, -, ho, hv⟩
        cases gs with
        | cons g gs => simp [encodeList] at h
        | nil =>
          simp only [encodeList, encodeNat, List.singleton_append, List.cons.injEq,
            true_and] at h
          exact ⟨o, h, by simpa using ho, by simpa using hv⟩
    | true =>
      rcases l with _ | ⟨b₁, l⟩
      · constructor
        · intro h; simp [absRun, absStep, absOf, lact, LA.rej, LA.go] at h
        · rintro ⟨gs, o, h, -⟩
          cases gs with
          | nil => simp [encodeList] at h
          | cons g gs =>
            obtain ⟨b₁, b₂, he, -⟩ := hkind' g.kind
            simp [encodeList, DAGGate.encode, he] at h
      rcases l with _ | ⟨b₂, l⟩
      · constructor
        · intro h; simp [absRun, absStep, absOf, lact, LA.rej, LA.go] at h
        · rintro ⟨gs, o, h, -⟩
          cases gs with
          | nil => simp [encodeList] at h
          | cons g gs =>
            obtain ⟨c₁, c₂, he, -⟩ := hkind' g.kind
            simp [encodeList, DAGGate.encode, he] at h
      by_cases hb : (b₁ && b₂) = true
      · constructor
        · intro h; simp [absRun, absStep, absOf, lact, LA.rej, LA.go, hb] at h
        · rintro ⟨gs, o, h, -⟩
          cases gs with
          | nil => simp [encodeList] at h
          | cons g gs =>
            obtain ⟨c₁, c₂, he, hc, -⟩ := hkind' g.kind
            simp only [encodeList, DAGGate.encode, he, List.cons_append, List.cons.injEq,
              true_and, List.append_assoc, List.nil_append] at h
            rw [h.1, h.2.1] at hb
            simp [hb] at hc
      · have hb' : (b₁ && b₂) = false := by simpa using hb
        have hstep : absRun ⟨.g, vals, [], 0⟩ (true :: b₁ :: b₂ :: l) =
            absRun ⟨.a (kindOf b₁ b₂) 0 (([] : List ℕ).foldl
              (fun acc a => accComb (kindOf b₁ b₂) acc (vals.getD a false))
              (accInit (kindOf b₁ b₂))), vals, [], 0⟩ l := by
          simp [absRun, absStep, absOf, lact, LA.go, hb']
        rw [hstep, absRun_a (kindOf b₁ b₂) vals 2 [] 0 [] l rfl rfl List.nodup_nil
          (by simp) (by simp)]
        constructor
        · rintro ⟨args, rest, hl', hle, hnd, hargs, hk, h⟩
          have hlen : rest.length ≤ N := by
            have : (true :: b₁ :: b₂ :: l).length ≤ N + 1 := hl
            have h2 : l.length = (encodeList encodeNat args).length + rest.length := by
              rw [hl', List.length_append]
            simp at this; omega
          obtain ⟨gs, o, hrest, hok, ho, hv⟩ := (ih rest hlen _).mp h
          refine ⟨⟨kindOf b₁ b₂, args⟩ :: gs, o, ?_, ?_, ?_, ?_⟩
          · simp [hl', hrest, encodeList, DAGGate.encode, hkind b₁ b₂ hb']
          · refine ⟨⟨by simpa using hle, by simpa using hnd, by simpa using hk, hargs⟩, ?_⟩
            simpa using hok
          · simp at ho ⊢; omega
          · simpa [runWith_cons] using hv
        · rintro ⟨gs, o, h, hok, ho, hv⟩
          cases gs with
          | nil => simp [encodeList] at h
          | cons g gs =>
            obtain ⟨c₁, c₂, he, hc, hkc⟩ := hkind' g.kind
            simp only [encodeList, DAGGate.encode, he, List.cons_append, List.cons.injEq,
              true_and, List.append_assoc, List.nil_append] at h
            obtain ⟨rfl, rfl, hl'⟩ := h
            obtain ⟨⟨hle, hnd, hk, hargs⟩, hok⟩ := hok
            have hg : g = ⟨kindOf b₁ b₂, g.args⟩ := by rw [hkc]
            refine ⟨g.args, encodeList DAGGate.encode gs ++ encodeNat o, hl', by simpa using hle,
              by simpa using hnd, hargs, by simpa [hkc] using hk, ?_⟩
            have hlen : (encodeList DAGGate.encode gs ++ encodeNat o).length ≤ N := by
              have : (true :: b₁ :: b₂ :: l).length ≤ N + 1 := hl
              have h2 : l.length = (encodeList encodeNat g.args).length +
                  (encodeList DAGGate.encode gs ++ encodeNat o).length := by
                rw [hl', List.length_append]
              simp at this; omega
            refine (ih _ hlen _).mpr ⟨gs, o, rfl, by simpa using hok, ?_, ?_⟩
            · simp at ho ⊢; omega
            · rw [hg] at hv; simpa [runWith_cons] using hv

/-- The gate-list conditions in the circuit's indexing: gate `i` sees `len + i`
vertices.

**Proof sketch.** Induction on the gate list: gate `0` sees `len` vertices, and gate `i + 1`
of the list is gate `i` of the tail, which sees `(len + 1) + i`. -/
theorem gatesOK_iff (gs : List DAGGate) (len : ℕ) :
    GatesOK gs len ↔ (∀ g ∈ gs, g.args.length ≤ 2 ∧ g.args.Nodup ∧
      (g.kind = .not → g.args.length = 1)) ∧
      ∀ (i : ℕ) (h : i < gs.length), ∀ a ∈ (gs[i]).args, a < len + i := by
  induction gs generalizing len with
  | nil => simp [GatesOK]
  | cons g gs ih =>
    simp only [GatesOK, ih, List.mem_cons, forall_eq_or_imp, List.length_cons]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
      refine ⟨⟨⟨h1, h2, h3⟩, h5⟩, ?_⟩
      intro i hi a ha
      cases i with
      | zero => simpa using h4 a ha
      | succ i =>
        have := h6 i (by omega) a (by simpa using ha)
        omega
    · rintro ⟨⟨⟨h1, h2, h3⟩, h5⟩, h6⟩
      refine ⟨⟨h1, h2, h3, fun a ha => by simpa using h6 0 (by omega) a (by simpa using ha)⟩,
        h5, ?_⟩
      intro i hi a ha
      have := h6 (i + 1) (by omega) a (by simpa using ha)
      omega

/-- The leading unary number of `1ⁿ0 ++ rest` is `n`. -/
theorem leadOnes_replicate (n : ℕ) (rest : List Bool) :
    leadOnes (List.replicate n true ++ false :: rest) = n := by
  induction n with
  | zero => simp [leadOnes]
  | succ n ih =>
    simp only [leadOnes, List.replicate_succ, List.cons_append] at ih ⊢
    simp

/-- A string containing a `0` starts with its leading unary number, terminated. -/
theorem eq_replicate_leadOnes (code : List Bool) (h : false ∈ code) :
    code = List.replicate (leadOnes code) true ++ false :: code.drop (leadOnes code + 1) := by
  induction code with
  | nil => simp at h
  | cons b code ih =>
    cases b with
    | false => simp [leadOnes]
    | true =>
      have h' : false ∈ code := by simpa using h
      have hl : leadOnes (true :: code) = leadOnes code + 1 := by
        simp [leadOnes]
      rw [hl]
      conv_lhs => rw [ih h']
      simp [List.replicate_succ]

/-- The main pass skips the leading unary number. -/
theorem absRun_skipN (n : ℕ) (vals : List Bool) (ms : List ℕ) (j : ℕ) (rest : List Bool) :
    absRun ⟨.skipN, vals, ms, j⟩ (List.replicate n true ++ false :: rest) =
      absRun ⟨.g, vals, ms, j⟩ rest := by
  induction n with
  | zero => simp [absRun, absStep, absOf, lact, LA.go]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, ← ih]
    simp [absRun, absStep, absOf, lact, LA.go]

/-- The first `n` bits of `x` as an input assignment, read back as a list. -/
theorem ofFn_getD_eq_take (x : List Bool) (n : ℕ) (h : n ≤ x.length) :
    List.ofFn (fun i : Fin n => x.getD i false) = x.take n := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simp at h1; omega : i < x.length)]

/-- **Correctness of the algorithm.** The verdict on `pairEncode code x` is `true` iff
`code` describes a fan-in-two circuit `C` on `n ≤ |x|` inputs (`n = |x|` when `exact`)
that outputs `1` on the first `n` bits of `x`.

**Proof sketch.** A description starts with `1ⁿ0`, so the setup reads `n` and the main
pass skips it (`leadOnes`). The rest is decomposed by `absRun_g`: it is the code of a
gate list and an output vertex satisfying the fan-in-two conditions (`GatesOK`, which
`gatesOK_iff` turns into the circuit's acyclicity and well-formedness), with the
output's value `1` after running the gates on the first `n` input bits; these are
exactly a fan-in-two `DAGCircuit n`, its description and its output. -/
theorem verdict_pairEncode (exact : Bool) (code x : List Bool) :
    verdict exact (Turing.pairEncode code x) = true ↔
      ∃ (n : ℕ) (C : DAGCircuit n), C.IsFaninTwo ∧ C.encode = code ∧ n ≤ x.length ∧
        (exact = true → n = x.length) ∧ C.eval (fun i => x.getD i false) = true := by
  simp only [verdict, Turing.pairDecode_pairEncode]
  constructor
  · intro h
    by_cases hc : false ∈ code ∧ leadOnes code ≤ x.length ∧
        (exact = false ∨ leadOnes code = x.length)
    · rw [if_pos hc] at h
      obtain ⟨hf, hn, hex⟩ := hc
      set n := leadOnes code with hndef
      have hcode := eq_replicate_leadOnes code hf
      rw [← hndef] at hcode
      rw [hcode, absRun_skipN, absRun_g] at h
      obtain ⟨gs, o, hrest, hok, ho, hv⟩ := h
      have hlen : (x.take n).length = n := by simp; omega
      rw [hlen] at hok ho
      have hok' := (gatesOK_iff gs n).mp hok
      let C : DAGCircuit n := ⟨gs, o, hok'.2, ho⟩
      refine ⟨n, C, ⟨fun g hg => ⟨(hok'.1 g hg).2.1, (hok'.1 g hg).2.2⟩,
        fun g hg => (hok'.1 g hg).1⟩, ?_, hn, ?_, ?_⟩
      · simp only [DAGCircuit.encode, C]
        rw [hcode, hrest]
        simp [encodeNat]
      · intro he; rcases hex with h' | h'
        · simp [he] at h'
        · exact h'
      · simp only [DAGCircuit.eval, DAGCircuit.values, C]
        rw [ofFn_getD_eq_take x n hn]
        exact hv
    · rw [if_neg hc] at h
      exact absurd h (by simp)
  · rintro ⟨n, C, hfan, henc, hn, hex, hv⟩
    have hlead : leadOnes code = n := by
      rw [← henc]; simp [DAGCircuit.encode, encodeNat, leadOnes_replicate]
    have hf : false ∈ code := by rw [← henc]; simp [DAGCircuit.encode, encodeNat]
    have hc : false ∈ code ∧ leadOnes code ≤ x.length ∧
        (exact = false ∨ leadOnes code = x.length) := by
      refine ⟨hf, by omega, ?_⟩
      cases exact
      · exact Or.inl rfl
      · exact Or.inr (by rw [hlead]; exact hex rfl)
    rw [if_pos hc, hlead, ← henc]
    simp only [DAGCircuit.encode, encodeNat, List.append_assoc, List.singleton_append]
    rw [absRun_skipN, absRun_g]
    have hlen : (x.take n).length = n := by simp; omega
    refine ⟨C.gates, C.output, rfl, ?_, ?_, ?_⟩
    · rw [hlen, gatesOK_iff]
      exact ⟨fun g hg => ⟨hfan.2 g hg, (hfan.1 g hg).1, (hfan.1 g hg).2⟩, C.args_lt⟩
    · rw [hlen]; exact C.output_lt
    · rw [← ofFn_getD_eq_take x n hn]; exact hv

end CircuitEval

end BoolCircuit
