import Mathlib.Tactic.Common
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Inv
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Ring
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Fintype.Powerset

namespace CommunicationComplexity.Functions.Disjointness
end CommunicationComplexity.Functions.Disjointness

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.Deterministic
inductive Protocol (X Y α : Type*) where
  | output (val : α) : Protocol X Y α
  | alice (f : X → Bool) (P : Bool → Protocol X Y α) : Protocol X Y α
  | bob (f : Y → Bool) (P : Bool → Protocol X Y α) : Protocol X Y α
end CommunicationComplexity.Deterministic

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def run (p : Protocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | .output val => val
  | .alice f P => (P (f x)).run x y
  | .bob f P => (P (f y)).run x y
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def complexity : Protocol X Y α → ℕ
  | .output _ => 0
  | .alice _ P => 1 + max (P false).complexity (P true).complexity
  | .bob _ P => 1 + max (P false).complexity (P true).complexity
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def Computes (p : Protocol X Y α) (f : X → Y → α) : Prop :=
  p.run = f
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def swap : Protocol X Y α → Protocol Y X α
  | .output val => .output val
  | .alice f P => .bob f (fun b => (P b).swap)
  | .bob f P => .alice f (fun b => (P b).swap)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
@[simp]
theorem swap_run (p : Protocol X Y α) (x : X) (y : Y) :
    p.swap.run y x = p.run x y := by
  induction p <;> simp [swap, run, *]
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
@[simp]
theorem swap_complexity (p : Protocol X Y α) :
    p.swap.complexity = p.complexity := by
  induction p <;> simp [swap, complexity, *]
end CommunicationComplexity.Deterministic.Protocol

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity
inductive Deterministic.FiniteMessage.Protocol (X Y α : Type*) where
  | output (val : α) : Protocol X Y α
  | alice {β : Type} [Fintype β] [Nonempty β]
      (f : X → β) (P : β → Protocol X Y α) :
      Protocol X Y α
  | bob {β : Type} [Fintype β] [Nonempty β]
      (f : Y → β) (P : β → Protocol X Y α) :
      Protocol X Y α
end CommunicationComplexity

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
def run (p : Protocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | Deterministic.FiniteMessage.Protocol.output val => val
  | Deterministic.FiniteMessage.Protocol.alice f P => (P (f x)).run x y
  | Deterministic.FiniteMessage.Protocol.bob f P => (P (f y)).run x y
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
def complexity : Protocol X Y α → ℕ
  | Deterministic.FiniteMessage.Protocol.output _ => 0
  | Deterministic.FiniteMessage.Protocol.alice (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)
  | Deterministic.FiniteMessage.Protocol.bob (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
private def completeTreeAlice (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → Deterministic.Protocol X Y α) : Deterministic.Protocol X Y α :=
  match d with
  | 0 => Q Fin.elim0
  | d + 1 => Deterministic.Protocol.alice (query 0) (fun b =>
      completeTreeAlice d (query ∘ Fin.succ) (fun bits => Q (Fin.cons b bits)))
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
private theorem completeTreeAlice_run (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → Deterministic.Protocol X Y α) (x : X) (y : Y) :
    (completeTreeAlice d query Q).run x y = (Q (fun i => query i x)).run x y := by
  induction d with
  | zero =>
    simp only [completeTreeAlice]
    congr; ext i; exact i.elim0
  | succ d ih =>
    simp only [completeTreeAlice, Deterministic.Protocol.run]
    rw [ih]
    -- Goal: (Q (Fin.cons (query 0 x) ...)).run x y = (Q (fun i => query i x)).run x y
    -- Suffices to show the arguments to Q are equal
    have :
        Fin.cons (query 0 x) (fun i => (query ∘ Fin.succ) i x) =
        fun i => query i x := by
      simpa [Function.comp] using (Fin.cons_self_tail (fun i => query i x))
    rw [this]
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
private theorem completeTreeAlice_complexity (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → Deterministic.Protocol X Y α) :
    (completeTreeAlice d query Q).complexity =
      d + Finset.univ.sup (fun bits => (Q bits).complexity) := by
  induction d with
  | zero =>
    simp only [completeTreeAlice, Nat.zero_add]
    have : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      simpa using (univ_eq_singleton_of_card_one Fin.elim0 (by simp))
    rw [this, Finset.sup_singleton]
  | succ d ih =>
    -- Unfold to 1 + max (rec false).complexity (rec true).complexity
    simp only [completeTreeAlice, Deterministic.Protocol.complexity]
    rw [ih, ih, Nat.succ_add, Nat.add_max_add_left]
    have hsplit : Finset.univ.sup (fun bits : Fin (d + 1) → Bool => (Q bits).complexity) =
        max (Finset.univ.sup (fun bits : Fin d → Bool => (Q (Fin.cons false bits)).complexity))
            (Finset.univ.sup (fun bits : Fin d → Bool => (Q (Fin.cons true bits)).complexity)) := by
      have hdec : (Finset.univ : Finset (Fin (d + 1) → Bool)) =
          (Finset.univ.image (Fin.cons false)) ∪ (Finset.univ.image (Fin.cons true)) := by
        ext bits
        simp only [Finset.mem_univ, Finset.mem_union,
          Finset.mem_image, true_and, true_iff]
        by_cases h : bits 0 = true
        · right; exact ⟨Fin.tail bits, by
            ext i; simp only [Fin.cons]
            refine Fin.cases ?_ ?_ i <;> simp [Fin.tail, h]⟩
        · left; exact ⟨Fin.tail bits, by
            ext i; refine Fin.cases ?_ ?_ i <;>
              simp [Fin.cons, Fin.tail, Bool.eq_false_iff.mpr h]⟩
      rw [hdec, Finset.sup_union, Finset.sup_image, Finset.sup_image]; rfl
    linarith [hsplit]
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
private theorem encode_alice {X Y α β : Type*} [Fintype β] [Nonempty β] (f : X → β)
    (Q : β → Deterministic.Protocol X Y α) :
    ∃ R : Deterministic.Protocol X Y α,
      (∀ x y, R.run x y = (Q (f x)).run x y) ∧
      R.complexity = Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun b => (Q b).complexity) := by
  have hcard : 0 < Fintype.card β := Fintype.card_pos
  let b₀ : β := (Fintype.equivFin β).symm ⟨0, hcard⟩
  let d := Nat.clog 2 (Fintype.card β)
  -- Binary encoding: β → (Fin d → Bool) via Fintype.equivFin then testBit
  let encode : β → (Fin d → Bool) := fun b =>
    fun i => (Fintype.equivFin β b).val.testBit i.val
  have hencode_inj : Function.Injective encode := by
    intro a b hab
    apply (Fintype.equivFin β).injective; apply Fin.ext
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < d
    · exact congr_fun hab ⟨i, hi⟩
    · have hd : Fintype.card β ≤ 2 ^ d := Nat.le_pow_clog (by norm_num) _
      have hle := hd.trans
        (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi))
      rw [Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le (Fintype.equivFin β a).isLt hle),
          Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le (Fintype.equivFin β b).isLt hle)]
  -- Upgrade ∃ to ∃! using injectivity, for use with Fintype.choose
  have hencode_unique : ∀ bits, (∃ b, encode b = bits) → ∃! b, encode b = bits := by
    intro bits ⟨b, hb⟩; exact ⟨b, hb, fun c hc => hencode_inj (hc.trans hb.symm)⟩
  -- Build a complete binary tree of alice queries
  let query : Fin d → X → Bool := fun i x => encode (f x) i
  -- For each bit pattern, use Fintype.choose to find the unique β value (if any)
  let leafQ : (Fin d → Bool) → Deterministic.Protocol X Y α :=
    fun bits => if h : ∃ b, encode b = bits then
      Q (Fintype.choose (fun b => encode b = bits) (hencode_unique bits h))
    else Q b₀
  refine ⟨completeTreeAlice d query leafQ, ?_, ?_⟩
  · -- run correctness
    intro x y
    rw [completeTreeAlice_run]
    have hquery : (fun i => query i x) = encode (f x) := rfl
    rw [hquery]
    have hexists : ∃ b, encode b = encode (f x) := ⟨f x, rfl⟩
    simp only [leafQ, hexists, dite_true]
    -- Fintype.choose picks the unique b with encode b = encode (f x); by injectivity it's f x
    have hch := Fintype.choose_spec (fun b => encode b = encode (f x)) (hencode_unique _ hexists)
    rw [hencode_inj hch]
  · -- complexity
    rw [completeTreeAlice_complexity]
    congr 1
    apply le_antisymm
    · apply Finset.sup_le; intro bits _
      by_cases h : ∃ b, encode b = bits
      · simp only [leafQ, h, dite_true]
        exact Finset.le_sup (f := fun b => (Q b).complexity) (Finset.mem_univ _)
      · simp only [leafQ, h, dite_false]
        exact Finset.le_sup (f := fun b => (Q b).complexity) (Finset.mem_univ _)
    · apply Finset.sup_le; intro b _
      have hleafQ : leafQ (encode b) = Q b := by
        have hexb : ∃ b', encode b' = encode b := ⟨b, rfl⟩
        simp only [leafQ, hexb, dite_true]
        congr 1
        have hch := Fintype.choose_spec (fun b' => encode b' = encode b) (hencode_unique _ hexb)
        exact hencode_inj hch
      calc (Q b).complexity
          = (leafQ (encode b)).complexity := by rw [hleafQ]
        _ ≤ Finset.univ.sup (fun bits => (leafQ bits).complexity) :=
            Finset.le_sup (f := fun bits => (leafQ bits).complexity) (Finset.mem_univ _)
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
private theorem toProtocol_exists
    (p : Protocol X Y α) :
    ∃ (P : Deterministic.Protocol X Y α),
      P.run = p.run ∧ P.complexity = p.complexity := by
  induction p with
  | output val => exact ⟨Deterministic.Protocol.output val, rfl, rfl⟩
  | @alice β _ _ f P ih =>
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ := encode_alice f Q
    exact ⟨R,
      funext₂ fun x y => by rw [hR_run, hQ_run, Deterministic.FiniteMessage.Protocol.run],
      by rw [hR_comp]; simp [Deterministic.FiniteMessage.Protocol.complexity, hQ_comp]⟩
  | @bob β _ _ f P ih =>
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ := encode_alice f (fun b => (Q b).swap)
    exact ⟨R.swap,
      funext₂ fun x y => by
        simp [Deterministic.FiniteMessage.Protocol.run,
          Deterministic.Protocol.swap_run, hR_run, hQ_run],
      by simp [Deterministic.FiniteMessage.Protocol.complexity,
          Deterministic.Protocol.swap_complexity, hR_comp,
          Deterministic.Protocol.swap_complexity, hQ_comp]⟩
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
noncomputable def toProtocol (p : Protocol X Y α) : Deterministic.Protocol X Y α :=
  (toProtocol_exists p).choose
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
@[simp]
theorem toProtocol_run (p : Protocol X Y α) :
    (toProtocol p).run = p.run :=
  (toProtocol_exists p).choose_spec.1
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
@[simp]
theorem toProtocol_complexity (p : Protocol X Y α) :
    (toProtocol p).complexity = p.complexity :=
  (toProtocol_exists p).choose_spec.2
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
def ofProtocol : Deterministic.Protocol X Y α → Protocol X Y α
  | Deterministic.Protocol.output val => Deterministic.FiniteMessage.Protocol.output val
  | Deterministic.Protocol.alice f P =>
      Deterministic.FiniteMessage.Protocol.alice f (fun b => ofProtocol (P b))
  | Deterministic.Protocol.bob f P =>
      Deterministic.FiniteMessage.Protocol.bob f (fun b => ofProtocol (P b))
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
theorem ofProtocol_run (p : Deterministic.Protocol X Y α) (x : X) (y : Y) :
    (ofProtocol p).run x y = p.run x y := by
  induction p <;> simp [ofProtocol, run, Deterministic.Protocol.run, *]
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
theorem ofProtocol_complexity (p : Deterministic.Protocol X Y α) :
    (ofProtocol p).complexity = p.complexity := by
  induction p <;> simp only [ofProtocol, complexity,
    Deterministic.Protocol.complexity, Fintype.univ_bool,
    Finset.sup_insert, Finset.sup_singleton,
    show Nat.clog 2 (Fintype.card Bool) = 1 from by native_decide,
    Nat.max_comm, *]
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
theorem ofProtocol_equiv (p : Deterministic.Protocol X Y α) :
    ∃ (P : Protocol X Y α), P.run = p.run ∧ P.complexity = p.complexity :=
  ⟨ofProtocol p, funext₂ (ofProtocol_run p), ofProtocol_complexity p⟩
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.Internal
@[simp]
theorem enat_iInf_le_coe_iff {ι : Sort*} {f : ι → ENat} {n : ℕ} :
    iInf f ≤ ↑n ↔ ∃ i, f i ≤ ↑n := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    apply not_lt.mpr h
    have : ∀ i, (↑(n + 1) : ENat) ≤ f i := fun i => by
      match f i, hne i with
      | none, _ => exact le_top
      | some m, hi =>
        exact WithTop.coe_le_coe.mpr
          (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp hi))
    exact lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n))
      (le_iInf this)
  · rintro ⟨i, hi⟩
    exact (iInf_le f i).trans hi
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Deterministic
noncomputable def communicationComplexity
    {X Y α : Type*} (f : X → Y → α) : ENat :=
  ⨅ (p : Protocol X Y α) (_ : p.Computes f),
    (p.complexity : ENat)
end CommunicationComplexity.Deterministic

namespace CommunicationComplexity.Deterministic
theorem communicationComplexity_le_iff
    {X Y α : Type*} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : Protocol X Y α,
        p.Computes f ∧ p.complexity ≤ n := by
  simp only [communicationComplexity,
    Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]
end CommunicationComplexity.Deterministic

namespace CommunicationComplexity.Deterministic
theorem communicationComplexity_le_iff_finiteMessage
    {X Y α : Type*} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : FiniteMessage.Protocol X Y α,
        p.run = f ∧ p.complexity ≤ n := by
  rw [communicationComplexity_le_iff]
  constructor
  · rintro ⟨p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.ofProtocol_equiv p
    exact ⟨P, hP_run.trans hp, hP_comp ▸ hc⟩
  · rintro ⟨p, hp, hc⟩
    exact ⟨p.toProtocol,
      (FiniteMessage.Protocol.toProtocol_run p).trans hp,
      FiniteMessage.Protocol.toProtocol_complexity p ▸ hc⟩
end CommunicationComplexity.Deterministic

namespace CommunicationComplexity.Deterministic
theorem le_communicationComplexity_iff
    {X Y α : Type*} (f : X → Y → α) (n : ℕ) :
    (n : ENat) ≤ communicationComplexity f ↔
      ∀ p : Protocol X Y α,
        p.Computes f → n ≤ p.complexity := by
  simp only [communicationComplexity,
    le_iInf_iff, Nat.cast_le]
end CommunicationComplexity.Deterministic

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.Rectangle
variable {X Y α : Type*}
def IsRectangle (S : Set (X × Y)) : Prop :=
  ∃ A : Set X, ∃ B : Set Y, S = A ×ˢ B
end CommunicationComplexity.Rectangle

namespace CommunicationComplexity.Rectangle
variable {X Y α : Type*}
theorem IsRectangle_iff (R : Set (X × Y)) :
    IsRectangle R ↔ ∀ x x' y y', (x, y) ∈ R → (x', y') ∈ R → (x', y) ∈ R ∧ (x, y') ∈ R := by
  constructor
  · rintro ⟨A, B, rfl⟩ x x' y y' ⟨hx, hy⟩ ⟨hx', hy'⟩
    exact ⟨⟨hx', hy⟩, ⟨hx, hy'⟩⟩
  · intro h
    refine ⟨Prod.fst '' R, Prod.snd '' R, ?_⟩
    ext ⟨x, y⟩
    simp only [Set.mem_prod, Set.mem_image, Prod.exists]
    constructor
    · intro hxy
      exact ⟨⟨x, y, hxy, rfl⟩, ⟨x, y, hxy, rfl⟩⟩
    · rintro ⟨⟨x', y', hx'y', rfl⟩, ⟨x'', y'', hx''y'', rfl⟩⟩
      exact (h _ _ _ _ hx'y' hx''y'').2
end CommunicationComplexity.Rectangle

namespace CommunicationComplexity.Rectangle
variable {X Y α : Type*}
def IsMonochromatic (S : Set (X × Y)) (g : X → Y → α) : Prop :=
  ∀ x x' y y', (x, y) ∈ S → (x', y') ∈ S → g x y = g x' y'
end CommunicationComplexity.Rectangle

namespace CommunicationComplexity.Rectangle
variable {X Y α : Type*}
def IsFoolingSet (S : Set (X × Y)) (g : X → Y → α) : Prop :=
  ∀ R : Set (X × Y), IsRectangle R → IsMonochromatic R g →
    (S ∩ R).Subsingleton
end CommunicationComplexity.Rectangle

namespace CommunicationComplexity.Rectangle
variable {X Y α : Type*}
def IsMonoPartition
    (Part : Set (Set (X × Y))) (g : X → Y → α) : Prop :=
  (∀ R ∈ Part, IsRectangle R) ∧
  (∀ R ∈ Part, IsMonochromatic R g) ∧
  ⋃₀ Part = Set.univ ∧
  (∀ R S, R ∈ Part → S ∈ Part → R ≠ S → Disjoint R S)
end CommunicationComplexity.Rectangle

namespace CommunicationComplexity.Rectangle
variable {X Y α : Type*}
variable {Part : Set (Set (X × Y))} {g : X → Y → α}
theorem monoPartition_point_mem (h : IsMonoPartition Part g)
    (p : X × Y) : ∃ R ∈ Part, p ∈ R := by
  have := h.2.2.1 ▸ Set.mem_univ p
  exact Set.mem_sUnion.mp this
end CommunicationComplexity.Rectangle

namespace CommunicationComplexity.Rectangle
variable {X Y α : Type*}
variable {Part : Set (Set (X × Y))} {g : X → Y → α}
theorem monoPartition_values_eq (h : IsMonoPartition Part g)
    {R : Set (X × Y)} (hR : R ∈ Part)
    {x x' : X} {y y' : Y}
    (hxy : (x, y) ∈ R) (hx'y' : (x', y') ∈ R) :
    g x y = g x' y' :=
  h.2.1 R hR x x' y y' hxy hx'y'
end CommunicationComplexity.Rectangle

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
private def leafRectanglesAux (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    Set (Set (X × Y)) :=
  match p with
  | output _  => {A ×ˢ B}
  | alice f P => leafRectanglesAux (P false) (A ∩ {x | f x = false}) B ∪
                 leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B
  | bob   f P => leafRectanglesAux (P false) A (B ∩ {y | f y = false}) ∪
                 leafRectanglesAux (P true)  A (B ∩ {y | f y = true})
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def leafRectangles (p : Protocol X Y α) : Set (Set (X × Y)) :=
  leafRectanglesAux p Set.univ Set.univ
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
private lemma aux_isRectangle (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) : Rectangle.IsRectangle R := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR
    exact ⟨A, B, hR⟩
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;> exact ih _ _ _ h
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;> exact ih _ _ _ h
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
lemma leafRectangles_isRectangle (p : Protocol X Y α)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : Rectangle.IsRectangle R :=
  aux_isRectangle p Set.univ Set.univ R hR
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
private lemma aux_subset (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) : R ⊆ A ×ˢ B := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR
    subst hR; exact le_refl _
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;>
      exact (ih _ _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx.1, hy⟩)
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;>
      exact (ih _ _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx, hy.1⟩)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
private lemma aux_cover (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    A ×ˢ B ⊆ ⋃₀ leafRectanglesAux p A B := by
  induction p generalizing A B with
  | output _ =>
    intro xy hxy
    exact Set.mem_sUnion.mpr ⟨_, Set.mem_singleton _, hxy⟩
  | alice f P ih =>
    intro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [leafRectanglesAux, Set.sUnion_union]
    cases hf : f x with
    | false => exact Set.mem_union_left  _ (ih false _ _ ⟨⟨hx, hf⟩, hy⟩)
    | true  => exact Set.mem_union_right _ (ih true  _ _ ⟨⟨hx, hf⟩, hy⟩)
  | bob f P ih =>
    intro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [leafRectanglesAux, Set.sUnion_union]
    cases hf : f y with
    | false => exact Set.mem_union_left  _ (ih false _ _ ⟨hx, ⟨hy, hf⟩⟩)
    | true  => exact Set.mem_union_right _ (ih true  _ _ ⟨hx, ⟨hy, hf⟩⟩)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
private lemma aux_disjoint (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R S : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) (hS : S ∈ leafRectanglesAux p A B)
    (hne : R ≠ S) : Disjoint R S := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR hS
    exact absurd (hR.trans hS.symm) hne
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih false _ _ hR hS
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P false) _ _ R hR hxyR).1.2
      have h2 := (aux_subset (P true)  _ _ S hS hxyS).1.2
      simp_all
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P true)  _ _ R hR hxyR).1.2
      have h2 := (aux_subset (P false) _ _ S hS hxyS).1.2
      simp_all
    · exact ih true _ _ hR hS
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih false _ _ hR hS
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P false) _ _ R hR hxyR).2.2
      have h2 := (aux_subset (P true)  _ _ S hS hxyS).2.2
      simp_all
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P true)  _ _ R hR hxyR).2.2
      have h2 := (aux_subset (P false) _ _ S hS hxyS).2.2
      simp_all
    · exact ih true _ _ hR hS
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
lemma leafRectangles_cover (p : Protocol X Y α) :
    ⋃₀ leafRectangles p = Set.univ :=
  Set.eq_univ_of_univ_subset (by simpa using aux_cover p Set.univ Set.univ)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
lemma leafRectangles_disjoint (p : Protocol X Y α)
    (R S : Set (X × Y)) (hR : R ∈ leafRectangles p) (hS : S ∈ leafRectangles p)
    (hne : R ≠ S) : Disjoint R S :=
  aux_disjoint p Set.univ Set.univ R S hR hS hne
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
private lemma aux_mono (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B)
    (x x' : X) (y y' : Y) (hxy : (x, y) ∈ R) (hxy' : (x', y') ∈ R) :
    p.run x y = p.run x' y' := by
  induction p generalizing A B with
  | output v => rfl
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with hR | hR
    · have hfx  : f x  = false := (aux_subset (P false) _ _ R hR hxy).1.2
      have hfx' : f x' = false := (aux_subset (P false) _ _ R hR hxy').1.2
      simp only [run, hfx, hfx']
      exact ih false _ _ hR
    · have hfx  : f x  = true := (aux_subset (P true) _ _ R hR hxy).1.2
      have hfx' : f x' = true := (aux_subset (P true) _ _ R hR hxy').1.2
      simp only [run, hfx, hfx']
      exact ih true _ _ hR
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with hR | hR
    · have hfy  : f y  = false := (aux_subset (P false) _ _ R hR hxy).2.2
      have hfy' : f y' = false := (aux_subset (P false) _ _ R hR hxy').2.2
      simp only [run, hfy, hfy']
      exact ih false _ _ hR
    · have hfy  : f y  = true := (aux_subset (P true) _ _ R hR hxy).2.2
      have hfy' : f y' = true := (aux_subset (P true) _ _ R hR hxy').2.2
      simp only [run, hfy, hfy']
      exact ih true _ _ hR
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
lemma leafRectangles_mono (p : Protocol X Y α)
    (g : X → Y → α) (h_comp : Computes p g)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : Rectangle.IsMonochromatic R g := by
  intro x x' y y' hxy hxy'
  have := aux_mono p Set.univ Set.univ R hR x x' y y' hxy hxy'
  simp only [Computes, funext_iff] at h_comp
  rw [← h_comp x y, ← h_comp x' y']; exact this
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
private lemma aux_card (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    Set.ncard (leafRectanglesAux p A B) ≤ 2 ^ p.complexity := by
  induction p generalizing A B with
  | output _ =>
    simp [leafRectanglesAux, complexity]
  | alice f P ih =>
    simp only [leafRectanglesAux, complexity]
    calc Set.ncard (leafRectanglesAux (P false) (A ∩ {x | f x = false}) B ∪
                    leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B)
        ≤ Set.ncard (leafRectanglesAux (P false) (A ∩ {x | f x = false}) B) +
          Set.ncard (leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B) :=
            Set.ncard_union_le _ _
      _ ≤ 2 ^ (P false).complexity + 2 ^ (P true).complexity := by
            exact Nat.add_le_add (ih false _ _) (ih true _ _)
      _ ≤ 2 ^ max (P false).complexity (P true).complexity +
          2 ^ max (P false).complexity (P true).complexity :=
            Nat.add_le_add
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
      _ = 2 ^ (1 + max (P false).complexity (P true).complexity) := by ring
  | bob f P ih =>
    simp only [leafRectanglesAux, complexity]
    calc Set.ncard (leafRectanglesAux (P false) A (B ∩ {y | f y = false}) ∪
                    leafRectanglesAux (P true)  A (B ∩ {y | f y = true}))
        ≤ Set.ncard (leafRectanglesAux (P false) A (B ∩ {y | f y = false})) +
          Set.ncard (leafRectanglesAux (P true)  A (B ∩ {y | f y = true})) :=
            Set.ncard_union_le _ _
      _ ≤ 2 ^ (P false).complexity + 2 ^ (P true).complexity :=
            Nat.add_le_add (ih false _ _) (ih true _ _)
      _ ≤ 2 ^ max (P false).complexity (P true).complexity +
          2 ^ max (P false).complexity (P true).complexity :=
            Nat.add_le_add
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
      _ = 2 ^ (1 + max (P false).complexity (P true).complexity) := by ring
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
lemma leafRectangles_card (p : Protocol X Y α) :
    Set.ncard (leafRectangles p) ≤ 2 ^ p.complexity :=
  aux_card p Set.univ Set.univ
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
theorem leafRectangles_isMonoPartition
    (p : Protocol X Y α) (g : X → Y → α)
    (h_comp : Computes p g) :
    Rectangle.IsMonoPartition (leafRectangles p) g :=
  ⟨fun R hR => leafRectangles_isRectangle p R hR,
   fun R hR => leafRectangles_mono p g h_comp R hR,
   leafRectangles_cover p,
   fun R S hR hS hne =>
     leafRectangles_disjoint p R S hR hS hne⟩
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic
variable {X Y α : Type*}
theorem mono_partition_of_communicationComplexity_le
    (g : X → Y → α) (n : ℕ)
    (h : communicationComplexity g ≤ n) :
    ∃ Part : Set (Set (X × Y)),
      Rectangle.IsMonoPartition Part g ∧
      Set.ncard Part ≤ 2 ^ n := by
  obtain ⟨p, hp, hc⟩ := (communicationComplexity_le_iff g n).mp h
  exact ⟨Protocol.leafRectangles p,
    Protocol.leafRectangles_isMonoPartition p g hp,
    (Protocol.leafRectangles_card p).trans
      (Nat.pow_le_pow_right (by omega) hc)⟩
end CommunicationComplexity.Deterministic

namespace CommunicationComplexity.Deterministic
variable {X Y α : Type*}
theorem le_communicationComplexity_of_forall_lt_ncard
    (g : X → Y → α) (n : ℕ)
    (h : ∀ Part : Set (Set (X × Y)),
      Rectangle.IsMonoPartition Part g →
      2 ^ n < Set.ncard Part) :
    (n + 1 : ℕ) ≤ communicationComplexity g := by
  rw [le_communicationComplexity_iff]
  intro p hp
  have hle : communicationComplexity g ≤
      p.complexity :=
    (communicationComplexity_le_iff g p.complexity).mpr ⟨p, hp, le_refl _⟩
  obtain ⟨Part, hPart, hCard⟩ :=
    mono_partition_of_communicationComplexity_le g p.complexity hle
  have hsuff := h Part hPart
  by_contra hlt; push_neg at hlt
  have : 2 ^ p.complexity ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega
end CommunicationComplexity.Deterministic

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.Deterministic
theorem communicationComplexity_le_clog_card_X_alpha
    {X Y α : Type} [Finite X] [Finite α] [Nonempty X] [Nonempty α]
    (f : X → Y → α) :
    communicationComplexity f ≤
      Nat.clog 2 (Nat.card X) + Nat.clog 2 (Nat.card α) := by
  haveI := Fintype.ofFinite X; haveI := Fintype.ofFinite α
  rw [← Nat.cast_add, communicationComplexity_le_iff_finiteMessage]
  refine ⟨FiniteMessage.Protocol.alice id (fun x =>
    FiniteMessage.Protocol.bob (f x) (fun a =>
      FiniteMessage.Protocol.output a)), ?_, ?_⟩
  · ext x y; unfold FiniteMessage.Protocol.run; rfl
  · simp [FiniteMessage.Protocol.complexity, Nat.card_eq_fintype_card, Finset.sup_const]
end CommunicationComplexity.Deterministic

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open CommunicationComplexity.Functions.Disjointness
open Rectangle

open CommunicationComplexity.Functions.Disjointness
open scoped symmDiff

namespace CommunicationComplexity.Functions.Disjointness
noncomputable def disjointness (n : ℕ) (X Y : Set (Fin n)) : Bool :=
  by
    classical
    exact decide (Disjoint X Y)
end CommunicationComplexity.Functions.Disjointness

namespace CommunicationComplexity.Functions.Disjointness
def foolingSet (n : ℕ) : Set (Set (Fin n) × Set (Fin n)) :=
  {p | p.2 = p.1ᶜ}
end CommunicationComplexity.Functions.Disjointness

namespace CommunicationComplexity.Functions.Disjointness
theorem foolingSet_isFoolingSet (n : ℕ) :
    IsFoolingSet (foolingSet n) (disjointness n) := by
  intro R hR hmono p hp q hq
  rcases p with ⟨X, Y⟩
  rcases q with ⟨X', Y'⟩
  simp only [foolingSet, Set.mem_inter_iff, Set.mem_setOf_eq] at hp hq
  rcases hp with ⟨rfl, hpR⟩
  rcases hq with ⟨rfl, hqR⟩
  by_cases hXX' : X = X'
  · subst hXX'
    rfl
  · have hcross := (IsRectangle_iff R).mp hR X X' Xᶜ X'ᶜ hpR hqR
    obtain ⟨i, hi⟩ : (X ∆ X').Nonempty := Set.symmDiff_nonempty.mpr hXX'
    rw [Set.mem_symmDiff] at hi
    rcases hi with hi | hi
    · have hval := hmono X X Xᶜ X'ᶜ hpR hcross.2
      have htrue : disjointness n X Xᶜ = true := by
        simpa [disjointness] using (disjoint_compl_right : Disjoint X Xᶜ)
      have hne : disjointness n X X'ᶜ ≠ true := by
        unfold disjointness
        simp only [ne_eq, decide_eq_true_eq]
        intro hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj hi.1 hi.2
      rw [htrue] at hval
      exact (hne hval.symm).elim
    · have hval := hmono X' X' X'ᶜ Xᶜ hqR hcross.1
      have htrue : disjointness n X' X'ᶜ = true := by
        simpa [disjointness] using (disjoint_compl_right : Disjoint X' X'ᶜ)
      have hne : disjointness n X' Xᶜ ≠ true := by
        unfold disjointness
        simp only [ne_eq, decide_eq_true_eq]
        intro hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj hi.1 hi.2
      rw [htrue] at hval
      exact (hne hval.symm).elim
end CommunicationComplexity.Functions.Disjointness

namespace CommunicationComplexity.Functions.Disjointness
theorem communicationComplexity_le (n : ℕ) :
    Deterministic.communicationComplexity (disjointness n) ≤ n + 1 := by
  calc Deterministic.communicationComplexity (disjointness n)
      ≤ Nat.clog 2 (Nat.card (Set (Fin n))) + Nat.clog 2 (Nat.card Bool) :=
        Deterministic.communicationComplexity_le_clog_card_X_alpha (disjointness n)
    _ = n + 1 := by
        have hbool : Nat.clog 2 2 = 1 := by native_decide
        simp only [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin,
          Fintype.card_bool, Nat.one_lt_ofNat, Nat.clog_pow]
        rw [hbool]
        norm_num
end CommunicationComplexity.Functions.Disjointness

namespace CommunicationComplexity.Functions.Disjointness
theorem le_communicationComplexity (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℕ) ≤ Deterministic.communicationComplexity (disjointness n) := by
  apply Deterministic.le_communicationComplexity_of_forall_lt_ncard
  intro Part hPart
  choose rect hrect_mem hrect_in using fun X : Set (Fin n) =>
    monoPartition_point_mem hPart (X, Xᶜ)
  have hrect_inj : Function.Injective rect := by
    intro X X' hXX
    have hsub :=
      foolingSet_isFoolingSet n (rect X) (hPart.1 _ (hrect_mem X)) (hPart.2.1 _ (hrect_mem X))
    have hp : (X, Xᶜ) ∈ foolingSet n ∩ rect X := by
      simp [foolingSet, hrect_in X]
    have hq : (X', X'ᶜ) ∈ foolingSet n ∩ rect X := by
      simp [foolingSet, hXX ▸ hrect_in X']
    exact congrArg Prod.fst (hsub hp hq)
  have himage_card :
      Set.ncard (Set.range rect) = 2 ^ n := by
    simpa [Fintype.card_set, Fintype.card_fin] using
      Set.ncard_range_of_injective hrect_inj
  let i0 : Fin n := ⟨0, hn⟩
  let x0 : Set (Fin n) := {i0}
  let y0 : Set (Fin n) := {i0}
  obtain ⟨R0, hR0_mem, hR0_in⟩ := monoPartition_point_mem hPart (x0, y0)
  have hR0_not_diag : R0 ∉ Set.range rect := by
    rintro ⟨X, rfl⟩
    have hval := monoPartition_values_eq hPart (hrect_mem X) (hrect_in X) hR0_in
    have htrue : disjointness n X Xᶜ = true := by
      simpa [disjointness] using (disjoint_compl_right : Disjoint X Xᶜ)
    have hne : disjointness n x0 y0 ≠ true := by
      unfold disjointness
      simp only [ne_eq, decide_eq_true_eq]
      intro hdisj
      rw [Set.disjoint_left] at hdisj
      have hnot : i0 ∉ y0 := hdisj (by simp [x0])
      exact hnot (by simp [y0])
    rw [htrue] at hval
    exact (hne hval.symm).elim
  have hinsert : insert R0 (Set.range rect) ⊆ Part :=
    Set.insert_subset hR0_mem (fun R ⟨X, hX⟩ => hX ▸ hrect_mem X)
  calc 2 ^ n
      = Set.ncard (Set.range rect) := himage_card.symm
    _ < Set.ncard (insert R0 (Set.range rect)) := by
        rw [Set.ncard_insert_of_notMem hR0_not_diag, himage_card]
        omega
    _ ≤ Set.ncard Part :=
        Set.ncard_le_ncard hinsert (Set.toFinite Part)
end CommunicationComplexity.Functions.Disjointness

namespace CommunicationComplexity.Functions.Disjointness
theorem communicationComplexity_eq (n : ℕ) (hn : 1 ≤ n) :
    Deterministic.communicationComplexity (disjointness n) = n + 1 := by
  apply le_antisymm (communicationComplexity_le n)
  exact le_communicationComplexity n hn
end CommunicationComplexity.Functions.Disjointness
