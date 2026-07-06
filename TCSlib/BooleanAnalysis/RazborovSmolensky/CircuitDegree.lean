/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.ACpGates
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup

open Finset
open scoped BigOperators

universe u v

namespace ACP

open FeedForward

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- Cast a Boolean input to the prime field. -/
def boolInput {n : ℕ} (x : Fin n → Fin 2) : Fin n → ZMod p :=
  fun i => ((x i : Nat) : ZMod p)

/-- The field value represented by a Boolean. -/
def boolVal (b : Fin 2) : ZMod p :=
  ((b : Nat) : ZMod p)

lemma boolVal_mem (b : Fin 2) :
    boolVal (p := p) b ∈ ({0, 1} : Set (ZMod p)) := by
  fin_cases b <;> simp [boolVal]

lemma bitify_boolVal (b : Fin 2) :
    bitify (p := p) (boolVal (p := p) b) = b := by
  fin_cases b <;> simp [bitify, boolVal]

/-- One-step unfolding of `FeedForward.evalNode` at a successor layer. -/
lemma evalNode_succ_eq {α : Type u} {inp out : Type v}
    (F : FeedForward α inp out) (d : Fin F.depth)
    (u : F.nodes d.succ) (x : inp → α) :
    F.evalNode (d := d.succ) u x =
      (F.gates d u).op.func
        (fun i => F.evalNode (d := d.castSucc) ((F.gates d u).inputs i) x) := by
  rfl

/-- Degree target after `d` layers. -/
def circuitDegreeBound (p ℓ d : ℕ) : ℕ :=
  ((p - 1) * ℓ) ^ d

/-- Number of non-input gates in the first `d` layers. -/
noncomputable def gateCountBefore {out : Type} {n : ℕ}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)] :
    (d : ℕ) → d ≤ F.depth → ℕ
  | 0, _ => 0
  | d + 1, hd =>
      gateCountBefore F d (Nat.le_trans (Nat.le_succ d) hd) +
        Fintype.card (F.nodes ⟨d + 1, Nat.lt_succ_of_le hd⟩)

@[simp] lemma gateCountBefore_zero {out : Type} {n : ℕ}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)] (hd : 0 ≤ F.depth) :
    gateCountBefore F 0 hd = 0 := by
  simp [gateCountBefore]

@[simp] lemma gateCountBefore_succ {out : Type} {n d : ℕ}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)] (hd : d + 1 ≤ F.depth) :
    gateCountBefore F (d + 1) hd =
      gateCountBefore F d (Nat.le_trans (Nat.le_succ d) hd) +
        Fintype.card (F.nodes ⟨d + 1, Nat.lt_succ_of_le hd⟩) := by
  simp [gateCountBefore]

/-- Cardinality of a product filtered only on the left coordinate. -/
lemma prod_left_filter_card {α β : Type*} [Fintype α]
    [Fintype β]
    (P : α → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun z : α × β => P z.1)).card =
      (Finset.univ.filter P).card * Fintype.card β := by
  classical
  let e : {z : α × β // P z.1} ≃ {a : α // P a} × β :=
    { toFun := fun z => (⟨z.1.1, z.2⟩, z.1.2)
      invFun := fun z => ⟨(z.1.1, z.2), z.1.2⟩
      left_inv := by
        intro z
        cases z with
        | mk z hz => cases z; rfl
      right_inv := by
        intro z
        cases z with
        | mk a b => cases a; rfl }
  calc
    (Finset.univ.filter (fun z : α × β => P z.1)).card
        = Fintype.card {z : α × β // P z.1} := by
            symm
            exact Fintype.card_subtype (fun z : α × β => P z.1)
    _ = Fintype.card ({a : α // P a} × β) := Fintype.card_congr e
    _ = Fintype.card {a : α // P a} * Fintype.card β := by
          rw [Fintype.card_prod]
    _ = (Finset.univ.filter P).card * Fintype.card β := by
          rw [Fintype.card_subtype P]

/-- Fiberwise product counting. -/
lemma prod_filter_fiber_mul_le {α β : Type*} [Fintype α]
    [Fintype β]
    (P : α → Prop) (Q : α → β → Prop)
    [DecidablePred P] [∀ a b, Decidable (Q a b)]
    (C B : ℕ)
    (hQ : ∀ a, P a → (Finset.univ.filter (fun b : β => Q a b)).card * C ≤ B) :
    (Finset.univ.filter (fun z : α × β => P z.1 ∧ Q z.1 z.2)).card * C ≤
      (Finset.univ.filter P).card * B := by
  classical
  let e : {z : α × β // P z.1 ∧ Q z.1 z.2} ≃
      Sigma (fun a : {a : α // P a} => {b : β // Q a.1 b}) :=
    { toFun := fun z => ⟨⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩⟩
      invFun := fun z => ⟨(z.1.1, z.2.1), z.1.2, z.2.2⟩
      left_inv := by
        intro z
        cases z with
        | mk z hz => cases z; rfl
      right_inv := by
        intro z
        cases z with
        | mk a b => cases a; cases b; rfl }
  have hcard :
      (Finset.univ.filter (fun z : α × β => P z.1 ∧ Q z.1 z.2)).card =
        ∑ a : {a : α // P a}, (Finset.univ.filter (fun b : β => Q a.1 b)).card := by
    calc
      (Finset.univ.filter (fun z : α × β => P z.1 ∧ Q z.1 z.2)).card
          = Fintype.card {z : α × β // P z.1 ∧ Q z.1 z.2} := by
              symm
              exact Fintype.card_subtype
                (fun z : α × β => P z.1 ∧ Q z.1 z.2)
      _ = Fintype.card (Sigma (fun a : {a : α // P a} => {b : β // Q a.1 b})) :=
            Fintype.card_congr e
      _ = ∑ a : {a : α // P a}, Fintype.card {b : β // Q a.1 b} := by
            rw [Fintype.card_sigma]
      _ = ∑ a : {a : α // P a}, (Finset.univ.filter (fun b : β => Q a.1 b)).card := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [Fintype.card_subtype (fun b : β => Q a.1 b)]
  calc
    (Finset.univ.filter (fun z : α × β => P z.1 ∧ Q z.1 z.2)).card * C
        = (∑ a : {a : α // P a}, (Finset.univ.filter (fun b : β => Q a.1 b)).card) * C := by
            rw [hcard]
    _ = ∑ a : {a : α // P a},
          (Finset.univ.filter (fun b : β => Q a.1 b)).card * C := by
            rw [Finset.sum_mul]
    _ ≤ ∑ a : {a : α // P a}, B := by
          refine Finset.sum_le_sum ?_
          intro a ha
          exact hQ a.1 a.2
    _ = Fintype.card {a : α // P a} * B := by
          simp
    _ = (Finset.univ.filter P).card * B := by
          rw [Fintype.card_subtype P]

/-- Split a dependent function into one coordinate and all remaining coordinates. -/
noncomputable def piEquivAt {ι : Type*} [DecidableEq ι]
    {β : ι → Type*} (i : ι) :
    ((j : ι) → β j) ≃ β i × ((j : {j : ι // j ≠ i}) → β j.1) where
  toFun f := (f i, fun j => f j.1)
  invFun x := fun j =>
    if h : j = i then by
      subst h
      exact x.1
    else
      x.2 ⟨j, h⟩
  left_inv := by
    intro f
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  right_inv := by
    intro x
    ext j
    · simp
    · simp [j.2]

/-- Count functions whose `i`-th coordinate is bad. -/
lemma pi_coordinate_bad_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (i : ι) (Bad : β i → Prop) [DecidablePred Bad] (C : ℕ)
    (hBad : (Finset.univ.filter Bad).card * C ≤ Fintype.card (β i)) :
    (Finset.univ.filter (fun f : (j : ι) → β j => Bad (f i))).card * C ≤
      Fintype.card ((j : ι) → β j) := by
  classical
  let Rest := (j : {j : ι // j ≠ i}) → β j.1
  let E : ((j : ι) → β j) ≃ β i × Rest := piEquivAt (β := β) i
  have hsubcard :
      (Finset.univ.filter (fun f : (j : ι) → β j => Bad (f i))).card =
        (Finset.univ.filter Bad).card * Fintype.card Rest := by
    let e : {f : ((j : ι) → β j) // Bad (f i)} ≃ {b : β i // Bad b} × Rest :=
      { toFun := fun f => (⟨f.1 i, f.2⟩, fun j => f.1 j.1)
        invFun := fun x =>
          ⟨E.symm (x.1.1, x.2), by
            have hfst := congrArg Prod.fst (E.right_inv (x.1.1, x.2))
            change Bad ((E (E.symm (x.1.1, x.2))).1)
            exact hfst.symm ▸ x.1.2⟩
        left_inv := by
          intro f
          apply Subtype.ext
          exact E.left_inv f.1
        right_inv := by
          intro x
          cases x with
          | mk b r =>
            apply Prod.ext
            · apply Subtype.ext
              change (E (E.symm (b.1, r))).1 = b.1
              exact congrArg Prod.fst (E.right_inv (b.1, r))
            · change (E (E.symm (b.1, r))).2 = r
              exact congrArg Prod.snd (E.right_inv (b.1, r)) }
    calc
      (Finset.univ.filter (fun f : (j : ι) → β j => Bad (f i))).card
          = Fintype.card {f : ((j : ι) → β j) // Bad (f i)} := by
              symm
              exact Fintype.card_subtype
                (fun f : ((j : ι) → β j) => Bad (f i))
      _ = Fintype.card ({b : β i // Bad b} × Rest) := Fintype.card_congr e
      _ = Fintype.card {b : β i // Bad b} * Fintype.card Rest := by
            rw [Fintype.card_prod]
      _ = (Finset.univ.filter Bad).card * Fintype.card Rest := by
            rw [Fintype.card_subtype Bad]
  have htotal :
      Fintype.card ((j : ι) → β j) = Fintype.card (β i) * Fintype.card Rest := by
    calc
      Fintype.card ((j : ι) → β j)
          = Fintype.card (β i × Rest) := Fintype.card_congr E
      _ = Fintype.card (β i) * Fintype.card Rest := by
            rw [Fintype.card_prod]
  calc
    (Finset.univ.filter (fun f : (j : ι) → β j => Bad (f i))).card * C
        = ((Finset.univ.filter Bad).card * Fintype.card Rest) * C := by
            rw [hsubcard]
    _ = ((Finset.univ.filter Bad).card * C) * Fintype.card Rest := by
          ring
    _ ≤ Fintype.card (β i) * Fintype.card Rest := by
          exact Nat.mul_le_mul_right (Fintype.card Rest) hBad
    _ = Fintype.card ((j : ι) → β j) := htotal.symm

/-- Union bound over all coordinates of a dependent product. -/
lemma pi_exists_bad_card_mul_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ι → Type*} [∀ i, Fintype (β i)]
    (Bad : ∀ i, β i → Prop) [∀ i b, Decidable (Bad i b)] (C : ℕ)
    (hBad : ∀ i, (Finset.univ.filter (fun b : β i => Bad i b)).card * C ≤
      Fintype.card (β i)) :
    (Finset.univ.filter (fun f : (i : ι) → β i => ∃ i, Bad i (f i))).card * C ≤
      Fintype.card ι * Fintype.card ((i : ι) → β i) := by
  classical
  let Target : Finset ((i : ι) → β i) :=
    Finset.univ.filter (fun f : (i : ι) → β i => ∃ i, Bad i (f i))
  let Coord (i : ι) : Finset ((i : ι) → β i) :=
    Finset.univ.filter (fun f : (j : ι) → β j => Bad i (f i))
  have hcover : Target ⊆ Finset.univ.biUnion Coord := by
    intro f hf
    rcases (Finset.mem_filter.mp hf).2 with ⟨i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, by simp, by simpa [Coord] using hi⟩
  have hcard : Target.card ≤ ∑ i : ι, (Coord i).card := by
    exact le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
  calc
    (Finset.univ.filter (fun f : (i : ι) → β i => ∃ i, Bad i (f i))).card * C
        = Target.card * C := rfl
    _ ≤ (∑ i : ι, (Coord i).card) * C := Nat.mul_le_mul_right C hcard
    _ = ∑ i : ι, (Coord i).card * C := by
          rw [Finset.sum_mul]
    _ ≤ ∑ i : ι, Fintype.card ((i : ι) → β i) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact pi_coordinate_bad_mul_le (i := i) (Bad := Bad i) C (hBad i)
    _ = Fintype.card ι * Fintype.card ((i : ι) → β i) := by
          simp


/-- Filtering a mapped list has the same length as filtering the source by the
pulled-back predicate.  This is useful for turning a finite seed distribution
into a list while preserving multiplicities. -/
lemma list_filter_map_length {α β : Type*} (l : List α) (f : α → β)
    (P : β → Prop) [DecidablePred P] :
    ((l.map f).filter P).length = (l.filter (fun a => P (f a))).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : P (f a) <;> simp [h, ih]

/-- The list obtained from a finset preserves the cardinality of filtered
subsets. -/
lemma finset_toList_filter_length_eq_card {α : Type*} (s : Finset α)
    (q : α → Prop) [DecidablePred q] :
    (s.toList.filter q).length = (s.filter q).card := by
  classical
  have htf : (s.toList.filter q).toFinset = s.filter q := by
    ext a
    simp
  calc
    (s.toList.filter q).length = ((s.toList.filter q).toFinset).card := by
      symm
      exact List.toFinset_card_of_nodup ((Finset.nodup_toList s).filter q)
    _ = (s.filter q).card := by
      rw [htf]

/-- A gate approximator family whose seed type depends only on the gate, not on
its incoming polynomials. -/
structure GatePolyFamily (p : ℕ) [Fact (Nat.Prime p)] (n ℓ : ℕ)
    (op : GateOp (Fin 2)) where
  Seed : Type
  [seedFintype : Fintype Seed]
  [seedDecEq : DecidableEq Seed]
  card_pos : 0 < Fintype.card Seed
  poly : (op.ι → MvPolynomial (Fin n) (ZMod p)) → Seed →
    MvPolynomial (Fin n) (ZMod p)
  degree : ∀ (polys : op.ι → MvPolynomial (Fin n) (ZMod p)) s,
    (poly polys s).totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree
  bad : ∀ (polys : op.ι → MvPolynomial (Fin n) (ZMod p))
      (x : Fin n → Fin 2),
    let y : Fin n → ZMod p := boolInput (p := p) x
    let inputs := fun i => (polys i).eval y
    (∀ i, inputs i ∈ ({0, 1} : Set (ZMod p))) →
      (Finset.univ.filter (fun s : Seed =>
        (poly polys s).eval y ≠
          (((op.func (fun i => bitify (p := p) (inputs i)) : Fin 2) : Nat) : ZMod p))).card *
          2 ^ ℓ ≤ Fintype.card Seed

attribute [instance] GatePolyFamily.seedFintype GatePolyFamily.seedDecEq

lemma exists_gate_poly_family (n ℓ : ℕ)
    (op : GateOp (Fin 2)) (hop : op ∈ ACp_GateOps p) :
    ∃ _ : GatePolyFamily p n ℓ op, True := by
  classical
  by_cases hℓ : ℓ = 0
  · subst ℓ
    refine ⟨{
      Seed := PUnit
      card_pos := by simp
      poly := fun _ _ => (0 : MvPolynomial (Fin n) (ZMod p))
      degree := by intro polys s; simp
      bad := ?_ }, trivial⟩
    intro polys x
    dsimp [boolInput]
    intro hbits
    simpa using
      (Finset.card_le_univ (Finset.univ.filter (fun s : PUnit =>
        ((0 : MvPolynomial (Fin n) (ZMod p)).eval (boolInput (p := p) x)) ≠
          (((op.func (fun i => bitify (p := p)
            ((polys i).eval (boolInput (p := p) x))) : Fin 2) : Nat) : ZMod p))))
  · have hℓ1 : 1 ≤ ℓ := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hℓ)
    have hmul : 1 ≤ (p - 1) * ℓ := by
      have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
      have hp' : 0 < p - 1 := by omega
      exact Nat.succ_le_of_lt (Nat.mul_pos hp' (Nat.pos_of_ne_zero hℓ))
    rcases ACp_GateOps_cases (p := p) hop with hId | hNot | hAnd | hMod
    · subst hId
      refine ⟨{
        Seed := PUnit
        card_pos := by simp
        poly := fun polys _ => polys PUnit.unit
        degree := ?_
        bad := ?_ }, trivial⟩
      · intro polys s
        have hsup : (⨆ i, (polys i).totalDegree) = (polys PUnit.unit).totalDegree := by
          simp
        rw [hsup]
        simpa [one_mul, mul_assoc] using
          (Nat.mul_le_mul_right (polys PUnit.unit).totalDegree hmul)
      · intro polys x
        dsimp [boolInput]
        intro hbits
        have hcorrect :
            (polys PUnit.unit).eval (boolInput (p := p) x) =
              (((bitify (p := p)
                ((polys PUnit.unit).eval (boolInput (p := p) x)) : Fin 2) : Nat) : ZMod p) := by
          simpa using (cast_bitify_eq (p := p) (hbits PUnit.unit)).symm
        have hfilter :
            (Finset.univ.filter (fun s : PUnit =>
              (polys PUnit.unit).eval (boolInput (p := p) x) ≠
                (((bitify (p := p)
                  ((polys PUnit.unit).eval (boolInput (p := p) x)) : Fin 2) : Nat) : ZMod p))) = ∅ := by
          ext s
          constructor
          · intro hs
            exact False.elim ((Finset.mem_filter.mp hs).2 hcorrect)
          · intro hs
            cases hs
        rw [hfilter]
        simp
    · subst hNot
      refine ⟨{
        Seed := PUnit
        card_pos := by simp
        poly := fun polys _ => 1 - polys 0
        degree := ?_
        bad := ?_ }, trivial⟩
      · intro polys s
        have hdeg0 : (1 - polys 0).totalDegree ≤ (polys 0).totalDegree := by
          simpa using
            (MvPolynomial.totalDegree_sub (1 : MvPolynomial (Fin n) (ZMod p)) (polys 0))
        have hsup : (polys 0).totalDegree ≤ ⨆ i, (polys i).totalDegree := by
          exact le_ciSup (Set.finite_range (polys · |>.totalDegree) |> Set.Finite.bddAbove) 0
        calc
          (1 - polys 0).totalDegree ≤ (polys 0).totalDegree := hdeg0
          _ ≤ 1 * (⨆ i, (polys i).totalDegree) := by
                rw [one_mul]
                exact hsup
          _ ≤ ((p - 1) * ℓ) * (⨆ i, (polys i).totalDegree) := by
            simpa [one_mul] using Nat.mul_le_mul_right (⨆ i, (polys i).totalDegree) hmul
          _ = (p - 1) * ℓ * (⨆ i, (polys i).totalDegree) := by
            simp [mul_assoc]
      · intro polys x
        dsimp [boolInput]
        intro hbits
        have hcorrect :
            (1 - polys 0).eval (boolInput (p := p) x) =
              ((((1 - bitify (p := p)
                ((polys 0).eval (boolInput (p := p) x)) : Fin 2) : Fin 2) : Nat) : ZMod p) := by
          have h0 := hbits 0
          simp at h0
          rcases h0 with h0 | h1
          · simp [h0, bitify]
          · simp [h1, bitify]
        have hfilter :
            (Finset.univ.filter (fun s : PUnit =>
              (1 - polys 0).eval (boolInput (p := p) x) ≠
                ((((1 - bitify (p := p)
                  ((polys 0).eval (boolInput (p := p) x)) : Fin 2) : Fin 2) : Nat) : ZMod p))) = ∅ := by
          ext s
          constructor
          · intro hs
            exact False.elim ((Finset.mem_filter.mp hs).2 hcorrect)
          · intro hs
            cases hs
        rw [hfilter]
        simp
    · rcases hAnd with ⟨width, rfl⟩
      refine ⟨{
        Seed := Fin ℓ → Finset (Fin width)
        card_pos := by simp
        poly := fun polys S => approxAnd p polys S
        degree := by intro polys S; exact approxAnd_totalDegree (p := p) n width ℓ polys S
        bad := ?_ }, trivial⟩
      intro polys x
      dsimp [boolInput]
      intro hbits
      let y : Fin n → ZMod p := boolInput (p := p) x
      have htarget :
          (∏ i, (1 - (1 - MvPolynomial.eval y (polys i)) ^ (p - 1)) : ZMod p) =
            (((∏ i, bitify (p := p) (MvPolynomial.eval y (polys i)) : Fin 2) : Nat) : ZMod p) := by
        exact exactAnd_on_bits (p := p)
          (fun i ↦ MvPolynomial.eval y (polys i))
          (by intro i; simpa [y, boolInput] using hbits i)
      have hbad := approxAnd_pointwise_bad_count (p := p) n width ℓ polys y
      have hfilter :
          (Finset.univ.filter (fun s : Fin ℓ → Finset (Fin width) =>
            (approxAnd p polys s).eval y ≠
              (((∏ i, bitify (p := p) (MvPolynomial.eval y (polys i)) : Fin 2) : Nat) : ZMod p))) =
          (Finset.univ.filter (fun s : Fin ℓ → Finset (Fin width) =>
            (approxAnd p polys s).eval y ≠
              ∏ i, (1 - (1 - MvPolynomial.eval y (polys i)) ^ (p - 1)))) := by
        ext s
        simp [← htarget]
      rw [hfilter]
      calc
        (Finset.univ.filter (fun s : Fin ℓ → Finset (Fin width) =>
          (approxAnd p polys s).eval y ≠
            ∏ i, (1 - (1 - MvPolynomial.eval y (polys i)) ^ (p - 1)))).card * 2 ^ ℓ
            ≤ 2 ^ (width * ℓ) := by
              simpa [y] using hbad
        _ = Fintype.card (Fin ℓ → Finset (Fin width)) :=
            (approxSeed_card width ℓ).symm
    · rcases hMod with ⟨width, rfl⟩
      refine ⟨{
        Seed := PUnit
        card_pos := by simp
        poly := fun polys _ => exactMod p polys
        degree := ?_
        bad := ?_ }, trivial⟩
      · intro polys s
        refine le_trans (exactMod_totalDegree (p := p) n width polys) ?_
        have hsupmul : (⨆ i, (polys i).totalDegree) ≤ ℓ * (⨆ i, (polys i).totalDegree) := by
          simpa [one_mul] using Nat.mul_le_mul_right (⨆ i, (polys i).totalDegree) hℓ1
        have hmul' :
            (p - 1) * (⨆ i, (polys i).totalDegree) ≤
              (p - 1) * (ℓ * (⨆ i, (polys i).totalDegree)) := by
          exact Nat.mul_le_mul_left (p - 1) hsupmul
        simpa [mul_assoc] using hmul'
      · intro polys x
        dsimp [boolInput]
        intro hbits
        have hcorrect :
            (exactMod p polys).eval (boolInput (p := p) x) =
              (((modGateOp p width).func
                (fun i ↦ bitify (p := p)
                  ((polys i).eval (boolInput (p := p) x))) : Fin 2) : Nat) := by
          simpa [exactMod, boolInput] using exactMod_on_bits (p := p)
            (fun i ↦ MvPolynomial.eval (boolInput (p := p) x) (polys i)) hbits
        have hfilter :
            (Finset.univ.filter (fun s : PUnit =>
              (exactMod p polys).eval (boolInput (p := p) x) ≠
                ((((modGateOp p width).func
                  (fun i ↦ bitify (p := p)
                    ((polys i).eval (boolInput (p := p) x))) : Fin 2) : Nat) : ZMod p))) = ∅ := by
          ext s
          constructor
          · intro hs
            exact False.elim ((Finset.mem_filter.mp hs).2 hcorrect)
          · intro hs
            cases hs
        rw [hfilter]
        simp

noncomputable def gatePolyFamily (n ℓ : ℕ)
    (op : GateOp (Fin 2)) (hop : op ∈ ACp_GateOps p) :
    GatePolyFamily p n ℓ op :=
  Classical.choose (exists_gate_poly_family (p := p) n ℓ op hop)

/-- A simultaneous polynomial distribution for one layer of a circuit. -/
structure LayerPolyFamily (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ} {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)] [∀ i, DecidableEq (F.nodes i)]
    (ℓ : ℕ) (d : ℕ) (hd : d ≤ F.depth) where
  Seed : Type
  [seedFintype : Fintype Seed]
  [seedDecEq : DecidableEq Seed]
  card_pos : 0 < Fintype.card Seed
  poly : Seed → F.nodes ⟨d, Nat.lt_succ_of_le hd⟩ →
    MvPolynomial (Fin n) (ZMod p)
  degree : ∀ s u, (poly s u).totalDegree ≤ circuitDegreeBound p ℓ d
  bad : ∀ x : Fin n → Fin 2,
    (Finset.univ.filter (fun s : Seed =>
      ∃ u : F.nodes ⟨d, Nat.lt_succ_of_le hd⟩,
        (poly s u).eval (boolInput (p := p) x) ≠
          (((F.evalNode (d := ⟨d, Nat.lt_succ_of_le hd⟩) u x : Fin 2) : Nat) : ZMod p))).card *
      2 ^ ℓ ≤ gateCountBefore F d hd * Fintype.card Seed

attribute [instance] LayerPolyFamily.seedFintype LayerPolyFamily.seedDecEq

noncomputable def inputLayerFamily {n : ℕ} {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)] [∀ i, DecidableEq (F.nodes i)]
    (ℓ : ℕ) (hd : 0 ≤ F.depth) : LayerPolyFamily p F ℓ 0 hd := by
  classical
  refine {
    Seed := PUnit
    card_pos := by simp
    poly := fun _ u => MvPolynomial.X (F.nodes_zero ▸ u)
    degree := ?_
    bad := ?_ }
  · intro s u
    simp [circuitDegreeBound]
  · intro x
    have hfilter :
        (Finset.univ.filter (fun s : PUnit =>
          ∃ u : F.nodes ⟨0, Nat.lt_succ_of_le hd⟩,
            (MvPolynomial.X (F.nodes_zero ▸ u)).eval (boolInput (p := p) x) ≠
              (((F.evalNode (d := ⟨0, Nat.lt_succ_of_le hd⟩) u x : Fin 2) : Nat) : ZMod p))) = ∅ := by
      ext s
      constructor
      · intro hs
        rcases (Finset.mem_filter.mp hs).2 with ⟨u, hu⟩
        have hcorrect :
            (MvPolynomial.X (F.nodes_zero ▸ u)).eval (boolInput (p := p) x) =
              (((F.evalNode (d := ⟨0, Nat.lt_succ_of_le hd⟩) u x : Fin 2) : Nat) : ZMod p) := by
          simp [FeedForward.evalNode, boolInput]
        exact False.elim (hu hcorrect)
      · intro hs
        cases hs
    rw [hfilter]
    simp [gateCountBefore]

noncomputable def stepLayerFamily {n : ℕ} {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)] [∀ i, DecidableEq (F.nodes i)]
    (hUses : F.onlyUsesGates (ACp_GateOps p))
    (ℓ d : ℕ) (hdlt : d < F.depth)
    (A : LayerPolyFamily p F ℓ d (Nat.le_of_lt hdlt)) :
    LayerPolyFamily p F ℓ (d + 1) (Nat.succ_le_of_lt hdlt) := by
  classical
  let dF : Fin F.depth := ⟨d, hdlt⟩
  let curr : Fin (F.depth + 1) := dF.succ
  let Fam : (u : F.nodes curr) → GatePolyFamily p n ℓ ((F.gates dF u).op) :=
    fun u => gatePolyFamily (p := p) n ℓ ((F.gates dF u).op) (hUses dF u)
  let Tail := (u : F.nodes curr) → (Fam u).Seed
  letI : Fintype A.Seed := A.seedFintype
  letI : DecidableEq A.Seed := A.seedDecEq
  letI (u : F.nodes curr) : Fintype ((Fam u).Seed) := (Fam u).seedFintype
  letI (u : F.nodes curr) : DecidableEq ((Fam u).Seed) := (Fam u).seedDecEq
  refine {
    Seed := A.Seed × Tail
    card_pos := ?_
    poly := ?_
    degree := ?_
    bad := ?_ }
  · have hA : Nonempty A.Seed := Fintype.card_pos_iff.mp A.card_pos
    have hFam : ∀ u : F.nodes curr, Nonempty ((Fam u).Seed) :=
      fun u => Fintype.card_pos_iff.mp (Fam u).card_pos
    rcases hA with ⟨a⟩
    exact Fintype.card_pos_iff.mpr ⟨(a, fun u => Classical.choice (hFam u))⟩
  · intro st u
    exact (Fam u).poly (fun i => A.poly st.1 ((F.gates dF u).inputs i)) (st.2 u)
  · intro st u
    have hgate := (Fam u).degree
      (fun i => A.poly st.1 ((F.gates dF u).inputs i)) (st.2 u)
    have hsup :
        (⨆ i, (A.poly st.1 ((F.gates dF u).inputs i)).totalDegree) ≤
          circuitDegreeBound p ℓ d := by
      exact ciSup_le' (fun i => A.degree st.1 ((F.gates dF u).inputs i))
    calc
      ((Fam u).poly (fun i => A.poly st.1 ((F.gates dF u).inputs i)) (st.2 u)).totalDegree
          ≤ (p - 1) * ℓ * ⨆ i, (A.poly st.1 ((F.gates dF u).inputs i)).totalDegree := hgate
      _ ≤ (p - 1) * ℓ * circuitDegreeBound p ℓ d := by
            exact Nat.mul_le_mul_left ((p - 1) * ℓ) hsup
      _ = circuitDegreeBound p ℓ (d + 1) := by
            simp [circuitDegreeBound, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]
  · intro x
    let y : Fin n → ZMod p := boolInput (p := p) x
    let PrevBad : A.Seed → Prop := fun r =>
      ∃ v : F.nodes dF.castSucc,
        (A.poly r v).eval y ≠
          (((F.evalNode (d := dF.castSucc) v x : Fin 2) : Nat) : ZMod p)
    let GateBad : A.Seed → Tail → Prop := fun r t =>
      ∃ u : F.nodes curr,
        ((Fam u).poly (fun i => A.poly r ((F.gates dF u).inputs i)) (t u)).eval y ≠
          ((((F.gates dF u).op.func
              (fun i => bitify (p := p)
                ((A.poly r ((F.gates dF u).inputs i)).eval y)) : Fin 2) : Nat) : ZMod p)
    let StepBad : A.Seed × Tail → Prop := fun st =>
      ∃ u : F.nodes curr,
        ((Fam u).poly (fun i => A.poly st.1 ((F.gates dF u).inputs i)) (st.2 u)).eval y ≠
          (((F.evalNode (d := curr) u x : Fin 2) : Nat) : ZMod p)
    let Sstep : Finset (A.Seed × Tail) := Finset.univ.filter StepBad
    let Sprev : Finset (A.Seed × Tail) := Finset.univ.filter (fun st => PrevBad st.1)
    let Sgate : Finset (A.Seed × Tail) :=
      Finset.univ.filter (fun st => ¬ PrevBad st.1 ∧ GateBad st.1 st.2)
    have hsub : Sstep ⊆ Sprev ∪ Sgate := by
      intro st hst
      rcases (Finset.mem_filter.mp hst).2 with ⟨u, hu⟩
      by_cases hp : PrevBad st.1
      · exact Finset.mem_union_left _ (by simp [Sprev, hp])
      · have hcorr : ∀ v : F.nodes dF.castSucc,
            (A.poly st.1 v).eval y =
              (((F.evalNode (d := dF.castSucc) v x : Fin 2) : Nat) : ZMod p) := by
          intro v
          by_contra hv
          exact hp ⟨v, hv⟩
        have hargs :
            (fun i => bitify (p := p)
              ((A.poly st.1 ((F.gates dF u).inputs i)).eval y)) =
            (fun i => F.evalNode (d := dF.castSucc) ((F.gates dF u).inputs i) x) := by
          funext i
          rw [hcorr ((F.gates dF u).inputs i)]
          exact bitify_boolVal (p := p)
            (F.evalNode (d := dF.castSucc) ((F.gates dF u).inputs i) x)
        have htarget :
            ((((F.gates dF u).op.func
              (fun i => bitify (p := p)
                ((A.poly st.1 ((F.gates dF u).inputs i)).eval y)) : Fin 2) : Nat) : ZMod p) =
              (((F.evalNode (d := curr) u x : Fin 2) : Nat) : ZMod p) := by
          rw [hargs]
          rw [evalNode_succ_eq (F := F) dF u x]
        have hgbad : GateBad st.1 st.2 := by
          refine ⟨u, ?_⟩
          intro hgood
          apply hu
          exact hgood.trans htarget
        exact Finset.mem_union_right _ (by simp [Sgate, hp, hgbad])
    have hcard_union : Sstep.card ≤ Sprev.card + Sgate.card := by
      exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le Sprev Sgate)
    have hprev : Sprev.card * 2 ^ ℓ ≤
        gateCountBefore F d (Nat.le_of_lt hdlt) * Fintype.card (A.Seed × Tail) := by
      have hprevCard : Sprev.card =
          (Finset.univ.filter PrevBad).card * Fintype.card Tail := by
        simpa [Sprev] using prod_left_filter_card (P := PrevBad) (β := Tail)
      have hA_bad := A.bad x
      calc
        Sprev.card * 2 ^ ℓ
            = ((Finset.univ.filter PrevBad).card * Fintype.card Tail) * 2 ^ ℓ := by
                rw [hprevCard]
        _ = ((Finset.univ.filter PrevBad).card * 2 ^ ℓ) * Fintype.card Tail := by
              ring
        _ ≤ (gateCountBefore F d (Nat.le_of_lt hdlt) * Fintype.card A.Seed) * Fintype.card Tail := by
              exact Nat.mul_le_mul_right (Fintype.card Tail) hA_bad
        _ = gateCountBefore F d (Nat.le_of_lt hdlt) * Fintype.card (A.Seed × Tail) := by
              simp [Fintype.card_prod, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have htail_bad : ∀ r : A.Seed, ¬ PrevBad r →
        (Finset.univ.filter (GateBad r)).card * 2 ^ ℓ ≤
          Fintype.card (F.nodes curr) * Fintype.card Tail := by
      intro r hgood
      have hcorr : ∀ v : F.nodes dF.castSucc,
          (A.poly r v).eval y =
            (((F.evalNode (d := dF.castSucc) v x : Fin 2) : Nat) : ZMod p) := by
        intro v
        by_contra hv
        exact hgood ⟨v, hv⟩
      let BadAt : (u : F.nodes curr) → (Fam u).Seed → Prop := fun u s =>
        ((Fam u).poly (fun i => A.poly r ((F.gates dF u).inputs i)) s).eval y ≠
          ((((F.gates dF u).op.func
              (fun i => bitify (p := p)
                ((A.poly r ((F.gates dF u).inputs i)).eval y)) : Fin 2) : Nat) : ZMod p)
      have hpi :
          (Finset.univ.filter (fun t : (u : F.nodes curr) → (Fam u).Seed =>
            ∃ u : F.nodes curr, BadAt u (t u))).card * 2 ^ ℓ ≤
            Fintype.card (F.nodes curr) *
              Fintype.card ((u : F.nodes curr) → (Fam u).Seed) := by
        refine pi_exists_bad_card_mul_le
          (ι := F.nodes curr)
          (β := fun u : F.nodes curr => (Fam u).Seed)
          (Bad := BadAt) (C := 2 ^ ℓ) ?_
        intro u
        have hbits : ∀ i,
            (A.poly r ((F.gates dF u).inputs i)).eval y ∈ ({0, 1} : Set (ZMod p)) := by
          intro i
          rw [hcorr ((F.gates dF u).inputs i)]
          exact boolVal_mem (p := p)
            (F.evalNode (d := dF.castSucc) ((F.gates dF u).inputs i) x)
        simpa [BadAt, y] using
          (Fam u).bad (fun i => A.poly r ((F.gates dF u).inputs i)) x hbits
      simpa [Tail, GateBad, BadAt] using hpi
    have hgate : Sgate.card * 2 ^ ℓ ≤
        Fintype.card (F.nodes curr) * Fintype.card (A.Seed × Tail) := by
      have hfiber := prod_filter_fiber_mul_le
        (P := fun r : A.Seed => ¬ PrevBad r)
        (Q := fun r (t : Tail) => GateBad r t)
        (C := 2 ^ ℓ)
        (B := Fintype.card (F.nodes curr) * Fintype.card Tail)
        (by intro r hr; exact htail_bad r hr)
      calc
        Sgate.card * 2 ^ ℓ
            ≤ (Finset.univ.filter (fun r : A.Seed => ¬ PrevBad r)).card *
                (Fintype.card (F.nodes curr) * Fintype.card Tail) := by
              simpa [Sgate] using hfiber
        _ ≤ Fintype.card A.Seed *
                (Fintype.card (F.nodes curr) * Fintype.card Tail) := by
              exact Nat.mul_le_mul_right _ (Finset.card_le_univ _)
        _ = Fintype.card (F.nodes curr) * Fintype.card (A.Seed × Tail) := by
              rw [Fintype.card_prod]
              ring_nf
    calc
      (Finset.univ.filter StepBad).card * 2 ^ ℓ
          = Sstep.card * 2 ^ ℓ := rfl
      _ ≤ (Sprev.card + Sgate.card) * 2 ^ ℓ := Nat.mul_le_mul_right _ hcard_union
      _ = Sprev.card * 2 ^ ℓ + Sgate.card * 2 ^ ℓ := by
            rw [Nat.add_mul]
      _ ≤ gateCountBefore F d (Nat.le_of_lt hdlt) * Fintype.card (A.Seed × Tail) +
            Fintype.card (F.nodes curr) * Fintype.card (A.Seed × Tail) := by
            exact Nat.add_le_add hprev hgate
      _ = gateCountBefore F (d + 1) (Nat.succ_le_of_lt hdlt) *
            Fintype.card (A.Seed × Tail) := by
            simp [gateCountBefore, curr, dF, Fintype.card_prod]
            ring_nf

noncomputable def buildLayerFamily {n : ℕ} {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)] [∀ i, DecidableEq (F.nodes i)]
    (hUses : F.onlyUsesGates (ACp_GateOps p))
    (ℓ : ℕ) : (d : ℕ) → (hd : d ≤ F.depth) → LayerPolyFamily p F ℓ d hd
  | 0, hd => inputLayerFamily (p := p) F ℓ hd
  | d + 1, hd =>
      let hdlt : d < F.depth := Nat.lt_of_succ_le hd
      stepLayerFamily (p := p) F hUses ℓ d hdlt
        (buildLayerFamily F hUses ℓ d (Nat.le_of_lt hdlt))

/-- Simultaneous pointwise polynomial distribution for all output nodes. -/
theorem exists_poly_distribution_for_circuit_outputs {n : ℕ} {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)]
    [Fintype out]
    (hUses : F.onlyUsesGates (ACp_GateOps p)) (ℓ : ℕ) :
    ∃ (Seed : Type) (_ : Fintype Seed) (_ : DecidableEq Seed)
      (P : Seed → out → MvPolynomial (Fin n) (ZMod p)),
      0 < Fintype.card Seed ∧
      (∀ s o, (P s o).totalDegree ≤ circuitDegreeBound p ℓ F.depth) ∧
      ∀ x : Fin n → Fin 2,
        (Finset.univ.filter (fun s : Seed =>
          ∃ o : out,
            (P s o).eval (boolInput (p := p) x) ≠
              (((F.eval x o : Fin 2) : Nat) : ZMod p))).card * 2 ^ ℓ ≤
          gateCountBefore F F.depth (Nat.le_refl F.depth) * Fintype.card Seed := by
  classical
  letI : ∀ i, DecidableEq (F.nodes i) := fun i => Classical.decEq _
  let A := buildLayerFamily (p := p) F hUses ℓ F.depth (Nat.le_refl F.depth)
  letI : Fintype A.Seed := A.seedFintype
  letI : DecidableEq A.Seed := A.seedDecEq
  refine ⟨A.Seed, inferInstance, inferInstance,
    (fun s o => A.poly s (F.nodes_last.symm.rec o)), A.card_pos, ?_, ?_⟩
  · intro s o
    exact A.degree s (F.nodes_last.symm.rec o)
  · intro x
    have hsub :
        (Finset.univ.filter (fun s : A.Seed =>
          ∃ o : out,
            (A.poly s (F.nodes_last.symm.rec o)).eval (boolInput (p := p) x) ≠
              (((F.eval x o : Fin 2) : Nat) : ZMod p))) ⊆
        (Finset.univ.filter (fun s : A.Seed =>
          ∃ u : F.nodes ⟨F.depth, Nat.lt_succ_self F.depth⟩,
            (A.poly s u).eval (boolInput (p := p) x) ≠
              (((F.evalNode (d := ⟨F.depth, Nat.lt_succ_self F.depth⟩) u x : Fin 2) : Nat) : ZMod p))) := by
      intro s hs
      rcases (Finset.mem_filter.mp hs).2 with ⟨o, ho⟩
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      refine ⟨F.nodes_last.symm.rec o, ?_⟩
      simpa [FeedForward.eval] using ho
    exact le_trans
      (Nat.mul_le_mul_right (2 ^ ℓ) (Finset.card_le_card hsub))
      (A.bad x)

/-- Pointwise distribution for a single-output circuit. -/
theorem exists_poly_distribution_for_circuit_one {n : ℕ} {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACp_GateOps p)) (ℓ : ℕ) :
    ∃ (Seed : Type) (_ : Fintype Seed) (_ : DecidableEq Seed)
      (P : Seed → MvPolynomial (Fin n) (ZMod p)),
      0 < Fintype.card Seed ∧
      (∀ s, (P s).totalDegree ≤ circuitDegreeBound p ℓ F.depth) ∧
      ∀ x : Fin n → Fin 2,
        (Finset.univ.filter (fun s : Seed =>
          (P s).eval (boolInput (p := p) x) ≠
            (((F.eval₁ x : Fin 2) : Nat) : ZMod p))).card * 2 ^ ℓ ≤
          gateCountBefore F F.depth (Nat.le_refl F.depth) * Fintype.card Seed := by
  classical
  letI : ∀ i, DecidableEq (F.nodes i) := fun i => Classical.decEq _
  let A := buildLayerFamily (p := p) F hUses ℓ F.depth (Nat.le_refl F.depth)
  letI : Fintype A.Seed := A.seedFintype
  letI : DecidableEq A.Seed := A.seedDecEq
  let outNode : F.nodes ⟨F.depth, Nat.lt_succ_self F.depth⟩ := F.nodes_last.symm.rec default
  refine ⟨A.Seed, inferInstance, inferInstance,
    (fun s => A.poly s outNode), A.card_pos, ?_, ?_⟩
  · intro s
    exact A.degree s outNode
  · intro x
    have hsub :
        (Finset.univ.filter (fun s : A.Seed =>
          (A.poly s outNode).eval (boolInput (p := p) x) ≠
            (((F.eval₁ x : Fin 2) : Nat) : ZMod p))) ⊆
        (Finset.univ.filter (fun s : A.Seed =>
          ∃ u : F.nodes ⟨F.depth, Nat.lt_succ_self F.depth⟩,
            (A.poly s u).eval (boolInput (p := p) x) ≠
              (((F.evalNode (d := ⟨F.depth, Nat.lt_succ_self F.depth⟩) u x : Fin 2) : Nat) : ZMod p))) := by
      intro s hs
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      refine ⟨outNode, ?_⟩
      simpa [FeedForward.eval₁, FeedForward.eval, outNode] using (Finset.mem_filter.mp hs).2
    exact le_trans
      (Nat.mul_le_mul_right (2 ^ ℓ) (Finset.card_le_card hsub))
      (A.bad x)

/-- Same single-output theorem, presented as a list of polynomials with
multiplicity, one entry per global random seed. -/
theorem exists_poly_list_for_circuit_one {n : ℕ} {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACp_GateOps p)) (ℓ : ℕ) :
    ∃ Ps : List (MvPolynomial (Fin n) (ZMod p)),
      0 < Ps.length ∧
      (∀ P ∈ Ps, P.totalDegree ≤ circuitDegreeBound p ℓ F.depth) ∧
      ∀ x : Fin n → Fin 2,
        (Ps.filter (fun P =>
          P.eval (boolInput (p := p) x) ≠
            (((F.eval₁ x : Fin 2) : Nat) : ZMod p))).length * 2 ^ ℓ ≤
          gateCountBefore F F.depth (Nat.le_refl F.depth) * Ps.length := by
  classical
  rcases exists_poly_distribution_for_circuit_one (p := p) F hUses ℓ with
    ⟨Seed, instF, instD, P, hpos, hdeg, hbad⟩
  letI : Fintype Seed := instF
  letI : DecidableEq Seed := instD
  refine ⟨(Finset.univ : Finset Seed).toList.map P, ?_, ?_, ?_⟩
  · simpa using hpos
  · intro Q hQ
    rcases List.mem_map.mp hQ with ⟨s, hs, rfl⟩
    exact hdeg s
  · intro x
    let badQ : Seed → Prop := fun s =>
      (P s).eval (boolInput (p := p) x) ≠
        (((F.eval₁ x : Fin 2) : Nat) : ZMod p)
    have hlen : ((Finset.univ : Finset Seed).toList.map P).length = Fintype.card Seed := by
      simp
    have hfilter :
        (((Finset.univ : Finset Seed).toList.map P).filter (fun Q =>
          Q.eval (boolInput (p := p) x) ≠
            (((F.eval₁ x : Fin 2) : Nat) : ZMod p))).length =
          (Finset.univ.filter badQ).card := by
      rw [list_filter_map_length]
      simpa [badQ] using
        (finset_toList_filter_length_eq_card (s := (Finset.univ : Finset Seed)) (q := badQ))
    have hbad' :
        (Finset.univ.filter badQ).card * 2 ^ ℓ ≤
          gateCountBefore F F.depth (Nat.le_refl F.depth) * Fintype.card Seed := by
      simpa [badQ] using hbad x
    calc
      (((Finset.univ : Finset Seed).toList.map P).filter (fun Q =>
          Q.eval (boolInput (p := p) x) ≠
            (((F.eval₁ x : Fin 2) : Nat) : ZMod p))).length * 2 ^ ℓ
          = (Finset.univ.filter badQ).card * 2 ^ ℓ := by
              rw [hfilter]
      _ ≤ gateCountBefore F F.depth (Nat.le_refl F.depth) * Fintype.card Seed := hbad'
      _ = gateCountBefore F F.depth (Nat.le_refl F.depth) *
            (((Finset.univ : Finset Seed).toList.map P).length) := by
              rw [← hlen]

end ACP
