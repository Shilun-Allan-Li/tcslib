/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.TMToPartrec
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.CodeParser
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Mathlib bridge: the effective scheme

The Mathlib-facing layer behind `Turing.exists_effectiveMachineCode`: it proves
the suffix scanner and prefix operation primitive recursive and converts that
fact into an actual finite binary machine. This module **quarantines the
`Mathlib.Computability.TMToPartrec` import** — Mathlib's recursion-theory and
TM2 development — behind this single module. The canonizer is obtained by the
arbitrary-time compiler route: primitive recursiveness of `Turing.codeCanonical`,
Mathlib's verified compilation of partial recursive functions to its TM2 stack
machines, a private in-model simulation of the compiled stack machine by the
four-work-tape controller `bridgeTM`, and the alphabet-reduction theorem to land
in a binary machine; **no polynomial time bound is claimed**. This module was
split out mechanically from `TCSlib.Complexity.TuringMachine.Encoding` at the
epoch-3→4 merge; its content is the epoch-3 fill, batch A. Its architectural
placement is **pending human review — `AroraBarakChapter1Plan.md` §5, open
design question 1**.

## Main results

* `Turing.exists_effectiveMachineCode` — a concrete effective representation
  scheme exists.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

private lemma codePrimUnary : Primrec codeReadUnary := by
  have h := Primrec.list_rec (α := List Bool) (β := Bool) Primrec.id (Primrec.const (none : Option (ℕ × List Bool)))
    (Primrec.to₂ (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.to₂ (Primrec.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd))))
      (Primrec.option_some.comp (Primrec.pair (Primrec.const 0) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))))
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    dsimp only [id, List.recOn] at ih ⊢
    cases b <;> simp [codeReadUnary, ih]

private lemma codePrimBit : Primrec₂ Nat.bit := by
  apply (Primrec.cond Primrec.fst
    (Primrec.succ.comp (Primrec.nat_double.comp Primrec.snd))
    (Primrec.nat_double.comp Primrec.snd)).of_eq
  intro p
  rcases p with ⟨b, n⟩
  cases b <;> simp [Nat.bit]

private lemma codePrimBitsNat : Primrec codeBitsNat :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (codePrimBit.comp₂ (Primrec.fst.comp₂ Primrec₂.right) (Primrec.snd.comp₂ Primrec₂.right))

/-- **Proof sketch.** A list recursion stores the aligned-parser results for both the current suffix and its tail. Adding one input bit can therefore inspect the next bit and reuse the result two positions ahead. This realizes the two-bit recursion using primitive recursive list operations. -/
private lemma codePrimPair : Primrec pairDecode := by
  let step : Bool × List Bool × (Option (List Bool × List Bool) × Option (List Bool × List Bool)) →
      Option (List Bool × List Bool) × Option (List Bool × List Bool) := fun p =>
    ((p.2.1.head?).bind fun b =>
      bif p.1 == b then p.2.2.2.map (fun q => (p.1 :: q.1, q.2))
      else bif p.1 then none else some ([], p.2.1.tail), p.2.2.1)
  have hstep : Primrec step := by
    apply Primrec.pair
    · apply Primrec.option_bind (Primrec.list_head?.comp (Primrec.fst.comp Primrec.snd))
      change Primrec _
      apply Primrec.cond (Primrec.beq.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      · apply Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        exact (Primrec.pair
          (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)).to₂
      · exact Primrec.cond (Primrec.fst.comp Primrec.fst) (Primrec.const none)
          (Primrec.option_some.comp (Primrec.pair (Primrec.const [])
            (Primrec.list_tail.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))))
    · exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_rec (α := List Bool) (β := Bool) Primrec.id
    (Primrec.const (none, none)) (hstep.comp Primrec.snd).to₂
  have he (xs : List Bool) :
      List.recOn xs (none, none) (fun b xs ih => step (b, xs, ih)) =
        (pairDecode xs, pairDecode xs.tail) := by
    induction xs with
    | nil => rfl
    | cons b xs ih =>
      dsimp only [List.recOn] at ih ⊢
      rw [ih]
      cases xs with
      | nil => cases b <;> rfl
      | cons a xs => cases b <;> cases a <;> rfl
  exact (Primrec.fst.comp h).of_eq fun xs => congrArg Prod.fst (he xs)

/-- **Proof sketch.** Use well-founded primitive recursion with the natural number itself as measure and its half as the sole recursive dependency. The zero case emits no bits; otherwise prepend the parity bit to the recursively computed bits of the half. -/
private lemma codePrimBits : Primrec Nat.bits := by
  let deps : ℕ → List ℕ := fun n => if n = 0 then [] else [n.div2]
  let step : ℕ → List (List Bool) → Option (List Bool) := fun n vals =>
    if n = 0 then some [] else vals.head?.map (fun xs => n.bodd :: xs)
  have hd : Primrec deps := Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const []) (Primrec.list_cons.comp Primrec.nat_div2 (Primrec.const []))
  have hs : Primrec₂ step := Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.const (some [])) (Primrec.option_map (Primrec.list_head?.comp Primrec.snd)
      (Primrec.to₂ (Primrec.list_cons.comp (Primrec.nat_bodd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)))
  apply Primrec.nat_omega_rec' Nat.bits (m := id) (l := deps) (g := step) Primrec.id hd hs
  · intro n a ha
    by_cases hn : n = 0
    · simp [deps, hn] at ha
    · simp only [deps, hn, ↓reduceIte, List.mem_singleton] at ha
      subst a
      exact Nat.binaryRec_decreasing hn
  · intro n
    by_cases hn : n = 0
    · simp [step, deps, hn]
    · have hb : n.div2 = 0 → n.bodd = true := by
        intro h
        have he := Nat.bit_bodd_div2 n
        rw [h] at he
        cases hh : n.bodd
        · simp [hh] at he
          exact (hn he.symm).elim
        · rfl
      simp only [deps, step, hn, ↓reduceIte, List.map_cons, List.map_nil, List.head?_cons, Option.map_some]
      congr 1
      exact (Nat.bits_append_bit n.div2 n.bodd hb).symm.trans (congrArg Nat.bits (Nat.bit_bodd_div2 n))

private lemma codePrimSkipPair (valid : Bool → Bool → Bool) : Primrec (codeSkipPair valid) := by
  have hi : Primrec₂ (fun p : Bool × List Bool => fun q : Bool × List Bool =>
      if valid p.1 q.1 then some q.2 else none) :=
    Primrec.ite (Primrec.eq.comp ((Primrec.dom_bool₂ valid).comp
      (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)) (Primrec.const true))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)
  have ho := Primrec.list_casesOn Primrec.snd (Primrec.const none) hi
  exact Primrec.list_casesOn Primrec.id (Primrec.const none) (ho.comp Primrec.snd).to₂

private lemma codePrimSkipFin : Primrec₂ codeSkipFin := by
  unfold codeSkipFin
  apply Primrec.option_bind (codePrimUnary.comp Primrec.snd)
  change Primrec _
  exact Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)

private lemma codePrimSkipState : Primrec₂ codeSkipState := by
  have h : Primrec₂ (fun p : ℕ × List Bool => fun q : Bool × List Bool =>
      if q.1 then codeSkipFin p.1 q.2 else some q.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true))
      (codePrimSkipFin.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_casesOn Primrec.snd (Primrec.const none) h

private lemma codePrimSkipAction : Primrec₂ codeSkipAction := by
  unfold codeSkipAction
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  exact codePrimSkipState.comp (Primrec.succ.comp
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))) Primrec.snd

private lemma codeSkipRepeat_iter (r : List Bool → Option (List Bool)) (n : ℕ) (xs : List Bool) :
    codeSkipRepeat r n xs = (fun o => o.bind r)^[n] (some xs) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [codeSkipRepeat, Function.iterate_succ_apply]
    cases h : r xs with
    | none =>
      simp only [Option.bind_none, Option.bind_some, h]
      clear ih xs h
      induction n with
      | zero => rfl
      | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih
    | some ys => simpa only [Option.bind_some, Option.bind_some, h] using ih ys

private lemma codePrimRepeat {A : Type} [Primcodable A]
    (r : A → List Bool → Option (List Bool)) (hr : Primrec₂ r)
    (count : A → ℕ) (hn : Primrec count) :
    Primrec₂ (fun a xs => codeSkipRepeat (r a) (count a) xs) := by
  have h := Primrec.nat_iterate (hn.comp Primrec.fst) (Primrec.option_some.comp Primrec.snd)
    (Primrec.option_bind Primrec.snd
      (hr.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂).to₂
  exact h.of_eq fun p => (codeSkipRepeat_iter (r p.1) (count p.1) p.2).symm

private lemma codePrimAll : Primrec (fun xs : List Bool => xs.all id) := by
  have h := Primrec.list_foldr (α := List Bool) (β := Bool) Primrec.id (Primrec.const true)
    ((Primrec.dom_bool₂ Bool.and).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun xs => by
    dsimp only [id]
    induction xs with
    | nil => rfl
    | cons b xs ih => simpa only [List.foldr_cons, List.all_cons, id_eq] using congrArg (fun z => b && z) ih

/-- **Proof sketch.** Compose primitive recursive readers, comparisons, and fixed-count iterations in the exact order of the erased parser. The canonical-count check and minimum-length check surround the state and record scans. The final branch accepts precisely an all-true suffix. -/
private lemma codePrimScan : Primrec codeScan := by
  unfold codeScan
  apply Primrec.option_bind codePrimPair
  change Primrec _
  apply Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
    (codePrimBits.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd)))).not)
    (Primrec.const none)
  apply Primrec.ite (Primrec.nat_lt.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_mul.comp (Primrec.const 81) (Primrec.succ.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd)))))
    (Primrec.const none)
  apply Primrec.option_bind (codePrimSkipFin.comp
    (Primrec.succ.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd))
  change Primrec _
  have hr := codePrimRepeat _ (codePrimRepeat _ (codePrimRepeat _ codePrimSkipAction (fun _ => 3) (Primrec.const 3))
    (fun _ => 3) (Primrec.const 3)) (fun n => n + 1) Primrec.succ
  apply Primrec.option_bind (hr.comp
    (codePrimBitsNat.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  change Primrec _
  exact Primrec.ite (Primrec.eq.comp (codePrimAll.comp Primrec.snd) (Primrec.const true))
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)

private lemma codePrimDrop : Primrec₂ (fun xs : List Bool => fun n => xs.drop n) := by
  have h := Primrec.nat_iterate (α := List Bool × ℕ) (β := List Bool) Primrec.snd Primrec.fst (Primrec.list_tail.comp Primrec.snd).to₂
  apply h.of_eq
  intro p
  rcases p with ⟨xs, n⟩
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    cases xs <;> simp

private lemma codePrimPrefix : Primrec₂ (fun xs : List Bool => fun n => xs.take (xs.length - n)) := by
  have h := Primrec.list_reverse.comp (codePrimDrop.comp (Primrec.list_reverse.comp Primrec.fst) Primrec.snd)
  exact h.of_eq fun p => by simp only [List.reverse_drop, List.reverse_reverse, List.length_reverse]

private lemma codePrimCanonical : Primrec codeCanonical :=
  Primrec.option_casesOn codePrimScan (Primrec.const codeFallback.serialize)
    (codePrimPrefix.comp Primrec.fst (Primrec.list_length.comp Primrec.snd))


private abbrev BridgeAlphabet := Bool ⊕ PartrecToTM2.Γ'

private def bridgeIndex : PartrecToTM2.K' → Fin 4
  | .main => 0
  | .rev => 1
  | .aux => 2
  | .stack => 3

private def bridgeStack (xs : List PartrecToTM2.Γ') (z : ℤ) : Option BridgeAlphabet :=
  if 0 ≤ z + xs.length then (xs[(z + xs.length).toNat]?).map Sum.inr else none

private lemma bridgeStack_read (xs : List PartrecToTM2.Γ') :
    bridgeStack xs (-(xs.length : ℤ)) = xs.head?.map Sum.inr := by
  simp only [bridgeStack, neg_add_cancel, le_refl, if_pos, Int.toNat_zero]
  cases xs <;> rfl

private lemma bridgeStack_nil : bridgeStack [] = fun _ => none := by
  funext z
  simp [bridgeStack]

private lemma bridgeStack_push (xs : List PartrecToTM2.Γ') (a : PartrecToTM2.Γ') :
    Function.update (bridgeStack xs) (-(xs.length : ℤ) - 1) (some (.inr a)) =
      bridgeStack (a :: xs) := by
  funext z
  by_cases hz : z = -(xs.length : ℤ) - 1
  · subst z
    simp [bridgeStack]
  · rw [Function.update_of_ne hz]
    by_cases h : 0 ≤ z + xs.length
    · have h' : 0 ≤ z + (a :: xs).length := by simp; omega
      have hi : (z + (a :: xs).length).toNat = (z + xs.length).toNat + 1 := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
      simp only [bridgeStack, if_pos h, if_pos h', hi, List.getElem?_cons_succ]
    · have h' : ¬0 ≤ z + (a :: xs).length := by simp; omega
      simp only [bridgeStack, if_neg h, if_neg h']

private lemma bridgeStack_pop (xs : List PartrecToTM2.Γ') (a : PartrecToTM2.Γ') :
    Function.update (bridgeStack (a :: xs)) (-((a :: xs).length : ℤ)) none =
      bridgeStack xs := by
  rw [← bridgeStack_push]
  have hi : -((a :: xs).length : ℤ) = -(xs.length : ℤ) - 1 := by simp; omega
  rw [hi, Function.update_idem]
  have hr : bridgeStack xs (-(xs.length : ℤ) - 1) = none := by
    have h : ¬0 ≤ -(xs.length : ℤ) - 1 + xs.length := by omega
    simp only [bridgeStack, if_neg h]
  rw [← hr, Function.update_eq_self]

private def bridgeKey : Fin 4 → PartrecToTM2.K' :=
  Fin.cases .main (Fin.cases .rev (Fin.cases .aux (fun _ => .stack)))

private lemma bridgeKey_index (k : PartrecToTM2.K') : bridgeKey (bridgeIndex k) = k := by
  cases k <;> rfl

private lemma bridgeIndex_key (i : Fin 4) : bridgeIndex (bridgeKey i) = i := by
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

private inductive BridgeState (Q : Type)
  | scan | startCons | startBit | back
  | pushInput (b : Bool)
  | exec (q : Q) (v : Option PartrecToTM2.Γ')
  | push (q : Q) (v : Option PartrecToTM2.Γ')
  | emit (carry : Option Bool)
  deriving Fintype, DecidableEq

private noncomputable def bridgeSupp (c : ToPartrec.Code) :=
  TM2.stmts PartrecToTM2.tr (PartrecToTM2.codeSupp c .halt)

private abbrev BridgeQ (c : ToPartrec.Code) := {q // q ∈ bridgeSupp c}

private def bridgeBit : Bool → PartrecToTM2.Γ'
  | false => .bit0
  | true => .bit1

private noncomputable def bridgeExec (c : ToPartrec.Code)
    (q : Option PartrecToTM2.Stmt') (v : Option PartrecToTM2.Γ') :
    Option (BridgeState (BridgeQ c)) := by
  classical
  exact if h : q ∈ bridgeSupp c then some (.exec ⟨q, h⟩ v) else none

private def bridgeIdle {Q : Type} (q : Option Q) : Action 4 BridgeAlphabet Q :=
  ⟨.zero, fun _ => (none, .zero), none, q⟩

private def bridgeOne {Q : Type} (k : Fin 4) (wr : Option (Option BridgeAlphabet))
    (d : SignType) (q : Option Q) : Action 4 BridgeAlphabet Q :=
  ⟨.zero, fun i => if i = k then (wr, d) else (none, .zero), none, q⟩

/-- A four-work-tape controller for Mathlib's proved partial-recursive compiler.
Each source stack occupies the negative cells ending at -1; its head points to the
stack top, and an empty stack has a blank head at zero. Source statements range
over the finite support of the selected program. Input bits live in the left
summand of the finite alphabet and stack symbols in the right summand. -/
private noncomputable def bridgeTM (c : ToPartrec.Code) : FinTM BridgeAlphabet := by
  classical
  exact {
    k := 4
    State := BridgeState (BridgeQ c)
    tm := {
      q₀ := .scan
      tr := fun q inp work =>
        match q with
        | .scan =>
          if inp.isSome then ⟨.pos, fun _ => (none, .zero), none, some .scan⟩
          else bridgeOne 0 none .neg (some .startCons)
        | .startCons => bridgeOne 0 (some (some (.inr .cons))) .neg (some .startBit)
        | .startBit => ⟨.neg, fun i => if i = 0 then
            (some (some (.inr .bit1)), .zero) else (none, .zero), none, some .back⟩
        | .back => match inp with
          | some (.inl b) => bridgeOne 0 none .neg (some (.pushInput b))
          | _ => bridgeIdle (bridgeExec c (some (PartrecToTM2.tr (PartrecToTM2.trNormal c .halt))) none)
        | .pushInput b => ⟨.neg, fun i => if i = 0 then
            (some (some (.inr (bridgeBit b))), .zero) else (none, .zero), none, some .back⟩
        | .exec q v =>
          match q.val with
          | none => bridgeIdle (some (.emit none))
          | some stmt => match stmt with
            | .push k _ _ => bridgeOne (bridgeIndex k) none .neg (some (.push q v))
            | .peek k f tail => bridgeIdle (bridgeExec c (some tail) (f v ((work (bridgeIndex k)).bind Sum.getRight?)))
            | .pop k f tail =>
              let w := work (bridgeIndex k)
              bridgeOne (bridgeIndex k) (some none) (if w.isSome then .pos else .zero)
                (bridgeExec c (some tail) (f v (w.bind Sum.getRight?)))
            | .load f tail => bridgeIdle (bridgeExec c (some tail) (f v))
            | .branch f yes no => bridgeIdle (bridgeExec c (some (if f v then yes else no)) v)
            | .goto f => bridgeIdle (bridgeExec c (some (PartrecToTM2.tr (f v))) v)
            | .halt => bridgeIdle (bridgeExec c none v)
        | .push q v =>
          match q.val with
          | some (.push k f tail) =>
            bridgeOne (bridgeIndex k) (some (some (.inr (f v)))) .zero (bridgeExec c (some tail) v)
          | _ => bridgeIdle none
        | .emit carry =>
          match work 0 with
          | some (.inr .bit0) =>
            { bridgeOne 0 (some none) .pos (some (.emit (some false))) with output := carry.map Sum.inl }
          | some (.inr .bit1) =>
            { bridgeOne 0 (some none) .pos (some (.emit (some true))) with output := carry.map Sum.inl }
          | _ => bridgeIdle none } }

private def bridgeCfg (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) :
    Cfg 4 BridgeAlphabet (BridgeState (BridgeQ c)) x :=
  ⟨q, p, fun i => bridgeStack (st (bridgeKey i)),
    fun i => -((st (bridgeKey i)).length : ℤ), out⟩

private lemma bridgeCfg_read (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') :
    (bridgeCfg c q p st out).workTapeSymbols (bridgeIndex k) =
      (st k).head?.map Sum.inr := by
  simp only [Cfg.workTapeSymbols, bridgeCfg, bridgeKey_index, bridgeStack_read]

private def bridgeReach {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) (a b : Cfg k A Q x) : Prop := ∃ t, M.runFrom a t = b

private lemma bridgeReach_refl {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) (a : Cfg k A Q x) : bridgeReach M a a := ⟨0, rfl⟩

private lemma bridgeReach_step {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) (a : Cfg k A Q x) : bridgeReach M a (M.step a) := ⟨1, rfl⟩

private lemma bridgeReach_trans {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) {a b d : Cfg k A Q x}
    (h : bridgeReach M a b) (h' : bridgeReach M b d) : bridgeReach M a d := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, ht⟩ := h'
  exact ⟨s + t, by rw [MultiTapeTM.runFrom_add, hs, ht]⟩

private lemma bridgeCfg_idle (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) :
    (bridgeIdle q').apply (bridgeCfg c q p st out) = bridgeCfg c q' p st out := by
  apply Cfg.ext <;> simp [bridgeIdle, bridgeCfg]

/-- **Proof sketch.** On the selected tape, erasing the current top cell and moving right gives the representation of the tail stack. Other tapes and the input head stay fixed; configuration extensionality combines these field equations. -/
private lemma bridgeCfg_pop (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') (xs : List PartrecToTM2.Γ')
    (hs : st k = a :: xs) :
    (bridgeOne (bridgeIndex k) (some none) .pos q').apply (bridgeCfg c q p st out) =
      bridgeCfg c q' p (Function.update st k xs) out := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero p
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, hs]
      rw [bridgeKey_index, Function.update_self]
      exact bridgeStack_pop xs a
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply_workTapes, bridgeOne, bridgeCfg, hi, hk]
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, hs, SignType.pos_eq_one, SignType.coe_one, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      rw [bridgeKey_index, Function.update_self]
      omega
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply, bridgeOne, bridgeCfg, hi, hk]
  · simp [Action.apply, bridgeOne, bridgeCfg]

/-- **Proof sketch.** Move the selected work head one cell left, then write the pushed symbol. The stack representation lemma identifies the resulting tape with the extended stack. All other tapes and the input/output components are unchanged. -/
private lemma bridgeCfg_push (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q qm q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') :
    (bridgeOne (bridgeIndex k) (some (some (.inr a))) .zero q').apply
      ((bridgeOne (bridgeIndex k) none .neg qm).apply (bridgeCfg c q p st out)) =
      bridgeCfg c q' p (Function.update st k (a :: st k)) out := by
  apply Cfg.ext
  · rfl
  · simp [Action.apply, bridgeOne, bridgeCfg]
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one]
      rw [bridgeKey_index, Function.update_self]
      exact bridgeStack_push (st k) a
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply_workTapes, bridgeOne, bridgeCfg, hi, hk]
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one,
        SignType.zero_eq_zero, SignType.coe_zero, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [bridgeKey_index, Function.update_self]
      simp
      omega
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply, bridgeOne, bridgeCfg, hi, hk]
  · simp [Action.apply, bridgeOne, bridgeCfg]

/-- **Proof sketch.** For an empty stack the tape is blank, so the machine erases a blank and stays. For a nonempty stack, apply the pop configuration lemma. These two cases match the stack machine pop semantics. -/
private lemma bridgeCfg_pop_any (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') :
    (bridgeOne (bridgeIndex k) (some none)
      (if (st k).head?.isSome then .pos else .zero) q').apply (bridgeCfg c q p st out) =
      bridgeCfg c q' p (Function.update st k (st k).tail) out := by
  cases hs : st k with
  | nil =>
    have hu : Function.update st k [] = st := by rw [← hs, Function.update_eq_self]
    simp only [List.head?_nil, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.tail_nil, hu]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext i
      by_cases hi : i = bridgeIndex k
      · subst i
        simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, hs,
          bridgeStack_nil]
        funext z
        simp
      · simp [Action.apply, bridgeOne, bridgeCfg, hi]
    · funext i
      by_cases hi : i = bridgeIndex k <;> simp [Action.apply, bridgeOne, bridgeCfg, hi]
    · simp [Action.apply, bridgeOne, bridgeCfg]
  | cons a xs =>
    simp only [List.head?_cons, Option.isSome_some, ↓reduceIte, List.tail_cons]
    exact bridgeCfg_pop c q q' p st out k a xs hs

private lemma bridgeExec_mem (c : ToPartrec.Code) (q : Option PartrecToTM2.Stmt')
    (v : Option PartrecToTM2.Γ') (h : q ∈ bridgeSupp c) :
    bridgeExec c q v = some (.exec ⟨q, h⟩ v) := by
  classical
  simp [bridgeExec, h]

private lemma bridge_step (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q : BridgeState (BridgeQ c)) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) :
    (bridgeTM c).tm.step (bridgeCfg c (some q) p st out) =
      ((bridgeTM c).tm.tr q (bridgeCfg c (some q) p st out).inputSymbol
        (bridgeCfg c (some q) p st out).workTapeSymbols).apply
          (bridgeCfg c (some q) p st out) := rfl

private lemma bridge_sub (c : ToPartrec.Code) (q tail : PartrecToTM2.Stmt')
    (hq : some q ∈ bridgeSupp c) (h : tail ∈ TM2.stmts₁ q) :
    some tail ∈ bridgeSupp c := TM2.stmts_trans h hq

private lemma bridge_none (c : ToPartrec.Code) : none ∈ bridgeSupp c := by
  classical
  simp [bridgeSupp, TM2.stmts]

/-- **Proof sketch.** Induct on the stack-machine statement. Push uses two native transitions; pop, peek, and register load use one before continuing recursively. Branch executes its chosen substatement. Goto and halt update the control label directly. The finite support lemma ensures every recursive substatement remains an available native state. -/
private lemma bridge_statement (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (out : List BridgeAlphabet) (q : PartrecToTM2.Stmt') :
    ∀ (v : Option PartrecToTM2.Γ') (st : PartrecToTM2.K' → List PartrecToTM2.Γ')
      (_hq : some q ∈ bridgeSupp c),
    bridgeReach (bridgeTM c).tm (bridgeCfg c (bridgeExec c (some q) v) p st out)
      (bridgeCfg c (bridgeExec c ((TM2.stepAux q v st).l.map PartrecToTM2.tr)
        (TM2.stepAux q v st).var) p (TM2.stepAux q v st).stk out) := by
  classical
  induction q with
  | push k f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) v)
      p (Function.update st k (f v :: st k)) out) ?_ (ih v _ ht)
    refine ⟨2, ?_⟩
    rw [bridgeExec_mem c _ v hq, show 2 = 1 + 1 from rfl,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    change (bridgeTM c).tm.step
      ((bridgeOne (bridgeIndex k) none .neg (some (.push ⟨some (.push k f tail), hq⟩ v))).apply
        (bridgeCfg c (some (.exec ⟨some (.push k f tail), hq⟩ v)) p st out)) = _
    unfold MultiTapeTM.step
    dsimp only [Action.apply, bridgeTM]
    exact bridgeCfg_push c _ _ _ p st out k (f v)
  | peek k f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) (f v (st k).head?))
      p st out) ?_ (ih _ _ ht)
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    rw [bridgeCfg_read]
    have hh : ((st k).head?.map (Sum.inr (α := Bool))).bind Sum.getRight? = (st k).head? := by
      cases (st k).head? <;> rfl
    rw [hh]
    exact bridgeCfg_idle c _ _ p st out
  | pop k f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) (f v (st k).head?))
      p (Function.update st k (st k).tail) out) ?_ (ih _ _ ht)
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    rw [bridgeCfg_read]
    have hh : ((st k).head?.map (Sum.inr (α := Bool))).bind Sum.getRight? = (st k).head? := by
      cases (st k).head? <;> rfl
    rw [hh]
    simp only [Option.isSome_map]
    exact bridgeCfg_pop_any c _ _ p st out k
  | load f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) (f v)) p st out)
      ?_ (ih _ _ ht)
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    exact bridgeCfg_idle c _ _ p st out
  | branch f yes no ihy ihn =>
    intro v st hq
    cases hv : f v with
    | false =>
      have ht := bridge_sub c _ no hq (by exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self))
      apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some no) v) p st out)
        ?_ (by simpa [TM2.stepAux, hv] using ihn v st ht)
      refine ⟨1, ?_⟩
      rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
        MultiTapeTM.runFrom_zero, bridge_step]
      simp only [bridgeTM, hv, Bool.false_eq_true, ↓reduceIte]
      exact bridgeCfg_idle c _ _ p st out
    | true =>
      have ht := bridge_sub c _ yes hq (by exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self))
      apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some yes) v) p st out)
        ?_ (by simpa [TM2.stepAux, hv] using ihy v st ht)
      refine ⟨1, ?_⟩
      rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
        MultiTapeTM.runFrom_zero, bridge_step]
      simp only [bridgeTM, hv, ↓reduceIte]
      exact bridgeCfg_idle c _ _ p st out
  | goto f =>
    intro v st hq
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM, TM2.stepAux, Option.map_some]
    exact bridgeCfg_idle c _ _ p st out
  | halt =>
    intro v st hq
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM, TM2.stepAux, Option.map_none]
    exact bridgeCfg_idle c _ _ p st out

private lemma bridge_label (c : ToPartrec.Code) (l : Option PartrecToTM2.Λ')
    (h : l ∈ Finset.insertNone (PartrecToTM2.codeSupp c .halt)) :
    l.map PartrecToTM2.tr ∈ bridgeSupp c := by
  classical
  cases l with
  | none => exact bridge_none c
  | some l =>
    have hl := Finset.some_mem_insertNone.mp h
    apply Finset.some_mem_insertNone.mpr
    exact Finset.mem_biUnion.mpr ⟨l, hl, TM2.stmts₁_self⟩

/-- **Proof sketch.** Induct on finite reachability of the compiled stack machine. Its support theorem preserves membership in the finite label set. For each source step, the statement simulation supplies a finite native execution, and transitivity concatenates these executions. -/
private lemma bridge_simulate (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (out : List BridgeAlphabet)
    (a b : PartrecToTM2.Cfg') (h : TM2.Reaches PartrecToTM2.tr a b)
    (ha : a.l ∈ Finset.insertNone (PartrecToTM2.codeSupp c .halt)) :
    b.l ∈ Finset.insertNone (PartrecToTM2.codeSupp c .halt) ∧
    bridgeReach (bridgeTM c).tm
      (bridgeCfg c (bridgeExec c (a.l.map PartrecToTM2.tr) a.var) p a.stk out)
      (bridgeCfg c (bridgeExec c (b.l.map PartrecToTM2.tr) b.var) p b.stk out) := by
  classical
  letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal c .halt⟩
  have support := PartrecToTM2.tr_supports c PartrecToTM2.Cont'.halt
  induction h with
  | refl => exact ⟨ha, bridgeReach_refl _ _⟩
  | @tail b d h hd ih =>
    refine ⟨TM2.step_supports _ support hd ih.1, bridgeReach_trans _ ih.2 ?_⟩
    rcases b with ⟨l, v, st⟩
    cases l with
    | none => simp [TM2.step] at hd
    | some l =>
      simp only [TM2.step, Option.mem_def, Option.some.injEq] at hd
      subst d
      exact bridge_statement c p out (PartrecToTM2.tr l) v st (bridge_label c _ ih.1)

private def bridgeNumber (xs : List Bool) : ℕ := xs.foldr Nat.bit 1

private def bridgeWord (xs : List Bool) : List PartrecToTM2.Γ' :=
  xs.map bridgeBit ++ [.bit1, .cons]

private lemma bridgeNumber_pos (xs : List Bool) : 0 < bridgeNumber xs := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    cases b <;> simp only [bridgeNumber, List.foldr_cons, Nat.bit_val] at * <;> omega

/-- **Proof sketch.** Encode a bit string as its low-to-high bits followed by a high true sentinel. Induction on the string matches each binary numeral constructor with the corresponding stack symbol; positivity rules out the zero numeral case. Append the compiled list terminator. -/
private lemma bridgeWord_number (xs : List Bool) :
    PartrecToTM2.trList [bridgeNumber xs] = bridgeWord xs := by
  suffices h : PartrecToTM2.trNat (bridgeNumber xs) = xs.map bridgeBit ++ [.bit1] by
    simpa [PartrecToTM2.trList, bridgeWord, List.append_assoc] using
      congrArg (fun zs => zs ++ [PartrecToTM2.Γ'.cons]) h
  induction xs with
  | nil => simp [bridgeNumber, PartrecToTM2.trNat, PartrecToTM2.trNum,
      PartrecToTM2.trPosNum]
  | cons b xs ih =>
    have hp := bridgeNumber_pos xs
    cases hn : (bridgeNumber xs : Num) with
    | zero =>
      have hz := congrArg (fun n : Num => (n : ℕ)) hn
      simp only [Num.to_of_nat, Num.cast_zero] at hz
      change bridgeNumber xs = 0 at hz
      omega
    | pos n =>
      have hword : PartrecToTM2.trPosNum n = xs.map bridgeBit ++ [.bit1] := by
        simpa only [PartrecToTM2.trNat, hn, PartrecToTM2.trNum] using ih
      change PartrecToTM2.trNum (Num.ofNat' (Nat.bit b (bridgeNumber xs))) = _
      rw [Num.ofNat'_bit, Num.ofNat'_eq, hn]
      cases b <;> simp [Num.bit0, Num.bit1, PartrecToTM2.trNum,
        PartrecToTM2.trPosNum, hword, bridgeBit]

private lemma bridgeCfg_push_input (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q qm q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') (d : SignType) :
    ({ bridgeOne (bridgeIndex k) (some (some (.inr a))) .zero q' with inputTape := d }).apply
      ((bridgeOne (bridgeIndex k) none .neg qm).apply (bridgeCfg c q p st out)) =
      bridgeCfg c q' (moveInputPos p d) (Function.update st k (a :: st k)) out := by
  have h := bridgeCfg_push c q qm q' p st out k a
  apply Cfg.ext
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.state h
  · simp [Action.apply, bridgeOne, bridgeCfg]
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapes h
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapePos h
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.output h

private def bridgeStore (xs : List PartrecToTM2.Γ') : PartrecToTM2.K' → List PartrecToTM2.Γ' :=
  PartrecToTM2.K'.elim xs [] [] []

private lemma bridgeStore_push (xs : List PartrecToTM2.Γ') (b : PartrecToTM2.Γ') :
    Function.update (bridgeStore xs) .main (b :: bridgeStore xs .main) = bridgeStore (b :: xs) := by
  funext k
  cases k <;> simp [bridgeStore, PartrecToTM2.K'.elim]

/-- **Proof sketch.** Induct on the input head position while scanning backward. Each bit is pushed onto the main stack in two steps, extending the already loaded suffix. At the left endmarker the complete word is present and execution enters the compiled program. -/
private lemma bridge_back (c : ToPartrec.Code) (x : List Bool) :
    ∀ j (hj : j ≤ x.length),
    bridgeReach (bridgeTM c).tm
      (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨j, by simp; omega⟩
        (bridgeStore (bridgeWord (x.drop j))) [])
      (bridgeCfg c (bridgeExec c (some (PartrecToTM2.tr (PartrecToTM2.trNormal c .halt))) none)
        0 (bridgeStore (bridgeWord x)) []) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨1, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
    have hi : (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨0, by simp⟩
      (bridgeStore (bridgeWord (x.drop 0))) []).inputSymbol = none := by
      simp [bridgeCfg, Cfg.inputSymbol]
    rw [hi]
    simp only [bridgeTM, List.drop_zero]
    rw [bridgeCfg_idle]
    congr 1
  | succ j ih =>
    intro hj
    apply bridgeReach_trans _ (b := bridgeCfg (x := x.map Sum.inl) c (some .back)
      ⟨j, by simp; omega⟩ (bridgeStore (bridgeWord (x.drop j))) []) ?_ (ih (by omega))
    refine ⟨2, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
    have hi : (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨j + 1, by simp; omega⟩
      (bridgeStore (bridgeWord (x.drop (j + 1)))) []).inputSymbol = some (Sum.inl x[j]) := by
      exact (inputSymbolInner (cfg := bridgeCfg (x := x.map Sum.inl) c (some .back)
        ⟨j + 1, by simp; omega⟩ (bridgeStore (bridgeWord (x.drop (j + 1)))) []) j
        (by simp [bridgeCfg]; omega) (by simp; omega)).trans
        (congrArg some (List.getElem_map (Sum.inl : Bool → BridgeAlphabet)))
    rw [hi]
    simp only [bridgeTM]
    change ({ bridgeOne (bridgeIndex .main) (some (some (.inr (bridgeBit x[j]))))
      .zero (some (BridgeState.back : BridgeState (BridgeQ c))) with inputTape := .neg }).apply
        ((bridgeOne (bridgeIndex .main) none .neg (some (BridgeState.pushInput (Q := BridgeQ c) x[j]))).apply
          (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨j + 1, by simp; omega⟩
            (bridgeStore (bridgeWord (x.drop (j + 1)))) [])) = _
    rw [bridgeCfg_push_input]
    simp only [bridgeStore_push]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    have hw : bridgeBit x[j] :: bridgeWord (x.drop (j + 1)) = bridgeWord (x.drop j) := by
      rw [List.drop_eq_getElem_cons (by omega : j < x.length)]
      rfl
    rw [hw]
    apply Cfg.ext
    · rfl
    · apply Fin.ext; simp
    · rfl
    · rfl
    · rfl

private lemma bridgeStore_nil : bridgeStore [] = fun _ => [] := by
  funext k
  cases k <;> rfl

private lemma bridgeStore_at (xs : List PartrecToTM2.Γ') (i : Fin 4) :
    bridgeStore xs (bridgeKey i) = if i = 0 then xs else [] := by
  by_cases hi : i = 0
  · subst i; rfl
  · have hk : bridgeKey i ≠ .main := by
      intro h
      apply hi
      rw [← bridgeIndex_key i, h]
      rfl
    cases h : bridgeKey i <;> simp [bridgeStore, PartrecToTM2.K'.elim, hi, hk, h] at *

/-- **Proof sketch.** Induct on the number of input symbols passed. Before the right endmarker every symbol is nonblank, so the controller moves right without changing any work tape or output. -/
private lemma bridge_scan (c : ToPartrec.Code) (x : List Bool) : ∀ j (hj : j ≤ x.length),
    (bridgeTM c).tm.runFrom ((bridgeTM c).tm.initCfg (x.map Sum.inl)) j =
      bridgeCfg c (some .scan) ⟨j + 1, by simp; omega⟩ (bridgeStore []) [] := by
  intro j
  induction j with
  | zero =>
    intro _
    apply Cfg.ext <;> simp [MultiTapeTM.runFrom, bridgeTM, bridgeCfg, bridgeStore_nil,
      bridgeStack_nil, MultiTapeTM.initCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), bridge_step]
    have hi : (bridgeCfg (x := x.map Sum.inl) c (some .scan) ⟨j + 1, by simp; omega⟩
      (bridgeStore []) []).inputSymbol = some (Sum.inl x[j]) := by
      exact (inputSymbolInner (cfg := bridgeCfg (x := x.map Sum.inl) c (some .scan)
        ⟨j + 1, by simp; omega⟩ (bridgeStore []) []) j
        (by simp [bridgeCfg]; omega) (by simp; omega)).trans
        (congrArg some (List.getElem_map (Sum.inl : Bool → BridgeAlphabet)))
    rw [hi]
    simp only [bridgeTM, Option.isSome_some, ↓reduceIte]
    apply Cfg.ext
    · rfl
    · change moveInputPos ⟨j + 1, _⟩ .pos = _
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
      rfl
    · rfl
    · funext i; simp [Action.apply, bridgeCfg]
    · rfl

/-- **Proof sketch.** At the right endmarker, three transitions create the list terminator and high true sentinel on the main tape, then move the input head left. Extensionality verifies the empty stacks on the other tapes and the exact two-cell main stack. -/
private lemma bridge_seed (c : ToPartrec.Code) (x : List Bool) :
    (bridgeTM c).tm.runFrom
      (bridgeCfg (x := x.map Sum.inl) c (some .scan) ⟨x.length + 1, by simp⟩ (bridgeStore []) []) 3 =
      bridgeCfg c (some .back) ⟨x.length, by simp⟩ (bridgeStore [.bit1, .cons]) [] := by
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
  have hi : (bridgeCfg (x := x.map Sum.inl) c (some .scan) ⟨x.length + 1, by simp⟩
    (bridgeStore []) []).inputSymbol = none := by
    simp [bridgeCfg, Cfg.inputSymbol, Fin.ext_iff]
  rw [hi]
  simp only [bridgeTM, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  unfold MultiTapeTM.step
  dsimp only [Action.apply, bridgeOne, bridgeTM]
  apply Cfg.ext
  · rfl
  · simp only [Action.apply, bridgeCfg, bridgeOne, SignType.zero_eq_zero,
      moveInputPos_zero]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    apply Fin.ext
    simp
  · funext i
    by_cases hi : i = 0
    · subst i
      simp only [bridgeCfg, bridgeStore_at, ↓reduceIte, List.length_nil, Nat.cast_zero,
        neg_zero, SignType.zero_eq_zero, SignType.coe_zero, SignType.neg_eq_neg_one,
        SignType.coe_neg_one, zero_add]
      change Function.update (Function.update (bridgeStack []) (-1) (some (.inr .cons)))
        (-2) (some (.inr .bit1)) = bridgeStack [.bit1, .cons]
      rw [show (-1 : ℤ) = -(([] : List PartrecToTM2.Γ').length : ℤ) - 1 from rfl,
        bridgeStack_push, show (-2 : ℤ) = -(([PartrecToTM2.Γ'.cons]).length : ℤ) - 1 from rfl,
        bridgeStack_push]
    · simp [bridgeCfg, bridgeStore_at, hi]
  · funext i
    by_cases hi : i = 0 <;> simp [bridgeCfg, bridgeStore_at, hi]
  · rfl

private lemma bridge_start (c : ToPartrec.Code) (x : List Bool) :
    bridgeReach (bridgeTM c).tm ((bridgeTM c).tm.initCfg (x.map Sum.inl))
      (bridgeCfg c (bridgeExec c (some (PartrecToTM2.tr (PartrecToTM2.trNormal c .halt))) none)
        0 (bridgeStore (bridgeWord x)) []) := by
  apply bridgeReach_trans _ ⟨x.length, bridge_scan c x _ (le_refl _)⟩
  apply bridgeReach_trans _ ⟨3, bridge_seed c x⟩
  simpa only [List.drop_length, bridgeWord, List.map_nil, List.nil_append] using
    bridge_back c x x.length (le_refl _)

private lemma bridgeCfg_pop_emit (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') (xs : List PartrecToTM2.Γ')
    (hs : st k = a :: xs) (e : Option BridgeAlphabet) :
    ({ bridgeOne (bridgeIndex k) (some none) .pos q' with output := e }).apply
      (bridgeCfg c q p st out) =
      bridgeCfg c q' p (Function.update st k xs) (out ++ e.toList) := by
  have h := bridgeCfg_pop c q q' p st out k a xs hs
  apply Cfg.ext
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.state h
  · exact moveInputPos_zero p
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapes h
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapePos h
  · rfl

private lemma bridge_emit_step (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (st : PartrecToTM2.K' → List PartrecToTM2.Γ')
    (out : List BridgeAlphabet) (carry : Option Bool) (b : Bool)
    (xs : List PartrecToTM2.Γ') (hs : st .main = bridgeBit b :: xs) :
    (bridgeTM c).tm.step (bridgeCfg c (some (.emit carry)) p st out) =
      bridgeCfg c (some (.emit (some b))) p (Function.update st .main xs)
        (out ++ carry.toList.map Sum.inl) := by
  rw [bridge_step]
  have hr := bridgeCfg_read c (some (.emit carry)) p st out .main
  rw [hs] at hr
  change (bridgeCfg c (some (.emit carry)) p st out).workTapeSymbols 0 = some (.inr (bridgeBit b)) at hr
  cases b <;> simp only [bridgeTM, hr, bridgeBit]
  all_goals
    simpa only [Option.toList_map] using bridgeCfg_pop_emit c (some (.emit carry)) _ p st out
      .main _ xs hs (carry.map Sum.inl)

/-- **Proof sketch.** Induct on the output bit string. The controller keeps one pending bit and emits the previous bit while advancing, so the last pending high sentinel is discarded at the list terminator. The empty-string case still consumes the sentinel and terminator without emitting a bit. -/
private lemma bridge_emit (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (xs : List Bool) :
    ∀ (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) (carry : Option Bool),
    st .main = bridgeWord xs →
    bridgeReach (bridgeTM c).tm (bridgeCfg c (some (.emit carry)) p st out)
      (bridgeCfg c none p (Function.update st .main [.cons])
        (out ++ carry.toList.map Sum.inl ++ xs.map Sum.inl)) := by
  induction xs with
  | nil =>
    intro st out carry hs
    refine ⟨2, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_emit_step c p st out carry true [.cons] hs, bridge_step]
    have hr := bridgeCfg_read c (some (.emit (some true))) p (Function.update st .main [.cons])
      (out ++ carry.toList.map Sum.inl) .main
    simp only [Function.update_self, List.head?_cons, Option.map_some] at hr
    change (bridgeCfg c (some (.emit (some true))) p (Function.update st .main [.cons])
      (out ++ carry.toList.map Sum.inl)).workTapeSymbols 0 = some (.inr .cons) at hr
    simp only [bridgeTM, hr, List.map_nil, List.append_nil]
    exact bridgeCfg_idle c _ none p (Function.update st .main [.cons]) _
  | cons b xs ih =>
    intro st out carry hs
    have hs' : st .main = bridgeBit b :: bridgeWord xs := hs
    apply bridgeReach_trans _ (b := bridgeCfg c (some (.emit (some b))) p
      (Function.update st .main (bridgeWord xs)) (out ++ carry.toList.map Sum.inl))
    · exact ⟨1, by simpa only [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero] using
        bridge_emit_step c p st out carry b (bridgeWord xs) hs'⟩
    · have h := ih (Function.update st .main (bridgeWord xs))
        (out ++ carry.toList.map Sum.inl) (some b) (Function.update_self _ _ _)
      simp only [Function.update_idem, Option.toList_some, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] at h
      simpa only [List.map_cons, List.append_assoc] using h

/-- **Proof sketch.** The proved partial-recursive compiler gives a terminating stack-machine execution with the specified result. Load the sentinel-coded input, simulate that finite execution, then emit its result with the sentinel removed. The resulting halted native configuration has exactly the requested output. -/
private lemma bridge_compiles (c : ToPartrec.Code) (f : List Bool → List Bool)
    (hc : ∀ x, c.eval [bridgeNumber x] = Part.some [bridgeNumber (f x)]) (x : List Bool) :
    ∃ t, (bridgeTM c).ComputesInTime (x.map Sum.inl) ((f x).map Sum.inl) t := by
  classical
  have he := PartrecToTM2.tr_eval c [bridgeNumber x]
  rw [hc x] at he
  have hm : PartrecToTM2.halt [bridgeNumber (f x)] ∈
      Turing.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init c [bridgeNumber x]) := by
    rw [he]
    simp
  have hr := (Turing.mem_eval.mp hm).1
  have ha : (PartrecToTM2.init c [bridgeNumber x]).l ∈
      Finset.insertNone (PartrecToTM2.codeSupp c .halt) := by
    apply Finset.some_mem_insertNone.mpr
    exact PartrecToTM2.codeSupp_self _ _ (PartrecToTM2.trStmts₁_self _)
  have hs := (bridge_simulate c (x := x.map Sum.inl) 0 [] _ _ hr ha).2
  simp only [PartrecToTM2.init, PartrecToTM2.halt, Option.map_some, Option.map_none,
    bridgeWord_number, bridgeExec_mem c none none (bridge_none c)] at hs
  have hstart := bridge_start c x
  have hem : bridgeReach (bridgeTM c).tm
      (bridgeCfg c (some (.exec ⟨none, bridge_none c⟩ none)) (x := x.map Sum.inl) 0
        (bridgeStore (bridgeWord (f x))) [])
      (bridgeCfg c (some (.emit none)) 0 (bridgeStore (bridgeWord (f x))) []) := by
    refine ⟨1, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
    exact bridgeCfg_idle c _ _ _ _ _
  have hf := bridge_emit c (x := x.map Sum.inl) 0 (f x)
    (bridgeStore (bridgeWord (f x))) [] none rfl
  have hall := bridgeReach_trans _ hstart (bridgeReach_trans _ hs (bridgeReach_trans _ hem hf))
  obtain ⟨t, ht⟩ := hall
  refine ⟨t, (FinTM.computesInTime_iff _ _ _ _).mpr ?_⟩
  change ((bridgeTM c).tm.runFrom ((bridgeTM c).tm.initCfg _) t).state = none ∧ _
  rw [ht]
  exact ⟨rfl, rfl⟩

private lemma bridge_binary (c : ToPartrec.Code) (f : List Bool → List Bool)
    (hc : ∀ x, c.eval [bridgeNumber x] = Part.some [bridgeNumber (f x)]) :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ), M.ComputesFunInTime f T := by
  classical
  choose t ht using bridge_compiles c f hc
  let T : ℕ → ℕ := fun n =>
    (Finset.univ : Finset (List.Vector Bool n)).sup fun x => t x.val
  have hT : (bridgeTM c).ComputesFunInTimeVia ⟨Sum.inl, Sum.inl_injective⟩ f T := by
    intro x
    exact (ht x).mono (Finset.le_sup (f := fun y : List.Vector Bool x.length => t y.val)
      (Finset.mem_univ (α := List.Vector Bool x.length) ⟨x, rfl⟩))
  obtain ⟨a, M, _, hM⟩ := FinTM.alphabet_reduction ⟨Sum.inl, Sum.inl_injective⟩ (bridgeTM c) f T hT
  exact ⟨M, _, hM⟩


private lemma bridgeNumber_bits (xs : List Bool) : (bridgeNumber xs).bits = xs ++ [true] := by
  induction xs with
  | nil => exact Nat.one_bits
  | cons b xs ih =>
    change (Nat.bit b (bridgeNumber xs)).bits = (b :: xs) ++ [true]
    rw [Nat.bits_append_bit _ _ (fun h => (Nat.ne_of_gt (bridgeNumber_pos xs) h).elim), ih]
    rfl

private def bridgeUnnumber (n : ℕ) : List Bool := n.bits.reverse.tail.reverse

private lemma bridgeUnnumber_number (xs : List Bool) : bridgeUnnumber (bridgeNumber xs) = xs := by
  simp [bridgeUnnumber, bridgeNumber_bits]

private lemma bridgePrimNumber : Primrec bridgeNumber :=
  Primrec.list_foldr Primrec.id (Primrec.const 1)
    (codePrimBit.comp₂ (Primrec.fst.comp₂ Primrec₂.right) (Primrec.snd.comp₂ Primrec₂.right))

private lemma bridgePrimUnnumber : Primrec bridgeUnnumber :=
  Primrec.list_reverse.comp (Primrec.list_tail.comp (Primrec.list_reverse.comp codePrimBits))

/-- A primitive recursive string operation has an actual finite binary machine.
The sentinel number code preserves trailing false bits and the empty word. -/
private lemma codePrim_machine (f : List Bool → List Bool) (hf : Primrec f) :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ), M.ComputesFunInTime f T := by
  have hn := bridgePrimNumber.comp (hf.comp (bridgePrimUnnumber.comp
    (Primrec.vector_head (n := 0))))
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.of_prim hn)
  apply bridge_binary c f
  intro x
  have hx := hc (List.Vector.ofFn (fun _ : Fin 1 => bridgeNumber x))
  simpa [List.Vector.ofFn, bridgeUnnumber_number] using hx

/-- The verified suffix scanner computes exactly the fixed serialization of decode. -/
private lemma codeCanonical_machine :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ),
      M.ComputesFunInTime (fun xs => (codeDecode xs).serialize) T := by
  have he : codeCanonical = fun xs => (codeDecode xs).serialize := funext codeCanonical_eq
  rw [← he]
  exact codePrim_machine codeCanonical codePrimCanonical

/-- A concrete effective representation scheme exists.

**Proof sketch.** Take `encode := CodeTM.serialize` — which records the state count,
the initial state, and the table (finding 5) — and let `decode` run the aligned-pair
parser of `pairEncode_injective` on the doubled-bit region to recover `numStates`,
then parse the unary initial state and the `9 · (numStates + 1)` fixed-format records;
any malformation (including trailing non-`true` junk) yields a canonical trivial
machine, making `decode` total. The parser **short-circuits on the first incomplete
record** (equivalently, rejects up front any state count whose minimum table length
exceeds the remaining input), so a short malformed string declaring a huge binary
state count is rejected in time polynomial in the string, not by enumerating its
missing records (round-2 audit, finding 8). A complete serialization determines its own length,
and the parser ignores a trailing all-`true` suffix, giving `decode_encode_pad`.
**[Original, superseded proposed sketch for the canonizer — the delivered proof
takes a different route; see the implementation note below (epoch-3 audit,
finding 1).]** The `canonizer` is a machine implementing exactly this parse
followed by re-serialization (on valid codes, the identity up to padding removal;
on invalid ones, the trivial machine's serialization), with a polynomial
`canonizerTime`; its construction uses the composition combinators of
`TCSlib.Complexity.TuringMachine.Composition`. **[End of superseded paragraph:
no polynomial `canonizerTime` is proved, and no combinator construction was
built.]**

**Epoch 3 implementation note.** The parser and erased suffix scanner implement
the grammar above, including the up-front minimum-length guard. For the canonizer,
this implementation takes the brief's arbitrary-time route: it proves the scanner
and prefix operation primitive recursive, uses Mathlib's proved partial-recursive
to stack-machine compiler, and supplies a private simulation by an actual finite
four-work-tape machine. A sentinel number encoding preserves empty strings and
trailing false bits. The proved alphabet-reduction theorem then gives a binary
machine. A finite maximum of the individual halting times at each input length
supplies the bound; no polynomial claim is made for this implementation. This
replaces the suggested composition-based implementation, not the fixed
serialization or its effectivity contract. No universal-machine admission is used. -/
theorem exists_effectiveMachineCode : Nonempty EffectiveMachineCode := by
  obtain ⟨M, T, h⟩ := codeCanonical_machine
  exact ⟨{
    encode := CodeTM.serialize
    decode := codeDecode
    decode_encode_pad := codeDecode_serialize_pad
    canonizer := M
    canonizerTime := T
    canonizer_computes := h }⟩

end Turing
