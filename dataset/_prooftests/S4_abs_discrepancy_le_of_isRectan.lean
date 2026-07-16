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
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.ConditionalProbability
import Mathlib.Data.Fintype.Prod
import Mathlib.Probability.UniformOn
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Mul

namespace ProbabilityTheory
end ProbabilityTheory
namespace CommunicationComplexity
end CommunicationComplexity

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

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
@[simp]
theorem swap_swap (p : Protocol X Y α) :
    p.swap.swap = p := by
  induction p <;> simp [swap, *]
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def comap {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) : Protocol X' Y' α :=
  match p with
  | .output val => .output val
  | .alice f P => .alice (f ∘ fX) (fun b => (P b).comap fX fY)
  | .bob f P => .bob (f ∘ fY) (fun b => (P b).comap fX fY)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
@[simp]
theorem comap_run {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y)
    (x' : X') (y' : Y') :
    (p.comap fX fY).run x' y' = p.run (fX x') (fY y') := by
  induction p <;> simp [comap, run, *]
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
@[simp]
theorem comap_complexity {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    (p.comap fX fY).complexity = p.complexity := by
  induction p <;> simp [comap, complexity, *]
end CommunicationComplexity.Deterministic.Protocol

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
inductive IsSubprotocol : Protocol X Y α → Protocol X Y α → Prop where
| refl : ∀ p, IsSubprotocol p p
| alice_false : ∀ f P s, IsSubprotocol s (P false) → IsSubprotocol s (Protocol.alice f P)
| alice_true  : ∀ f P s, IsSubprotocol s (P true)  → IsSubprotocol s (Protocol.alice f P)
| bob_false   : ∀ f P s, IsSubprotocol s (P false) → IsSubprotocol s (Protocol.bob f P)
| bob_true    : ∀ f P s, IsSubprotocol s (P true)  → IsSubprotocol s (Protocol.bob f P)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
inductive SubprotocolPath : Protocol X Y α → Protocol X Y α → Type _ where
| refl : ∀ p, SubprotocolPath p p
| alice_false : ∀ f P s, SubprotocolPath s (P false) → SubprotocolPath s (Protocol.alice f P)
| alice_true  : ∀ f P s, SubprotocolPath s (P true)  → SubprotocolPath s (Protocol.alice f P)
| bob_false   : ∀ f P s, SubprotocolPath s (P false) → SubprotocolPath s (Protocol.bob f P)
| bob_true    : ∀ f P s, SubprotocolPath s (P true)  → SubprotocolPath s (Protocol.bob f P)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
theorem path_exists_of_isSubprotocol {s p : Protocol X Y α}
    (hsp : IsSubprotocol s p) : Nonempty (SubprotocolPath s p) := by
  induction hsp with
  | refl p => exact ⟨SubprotocolPath.refl p⟩
  | alice_false f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.alice_false f P s t⟩
  | alice_true f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.alice_true f P s t⟩
  | bob_false f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.bob_false f P s t⟩
  | bob_true f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.bob_true f P s t⟩
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
noncomputable def choosePath {s p : Protocol X Y α}
    (hsp : IsSubprotocol s p) : SubprotocolPath s p :=
  Classical.choice (path_exists_of_isSubprotocol hsp)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def reachXPath {s p : Protocol X Y α} (hsp : SubprotocolPath s p) : Set X :=
  match hsp with
  | SubprotocolPath.refl _ => Set.univ
  | SubprotocolPath.alice_false f P s hs => reachXPath hs ∩ {x | f x = false}
  | SubprotocolPath.alice_true f P s hs => reachXPath hs ∩ {x | f x = true}
  | SubprotocolPath.bob_false _ _ _ hs => reachXPath hs
  | SubprotocolPath.bob_true _ _ _ hs => reachXPath hs
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def reachYPath {s p : Protocol X Y α} (hsp : SubprotocolPath s p) : Set Y :=
  match hsp with
  | SubprotocolPath.refl _ => Set.univ
  | SubprotocolPath.alice_false _ _ _ hs => reachYPath hs
  | SubprotocolPath.alice_true _ _ _ hs => reachYPath hs
  | SubprotocolPath.bob_false f P s hs => reachYPath hs ∩ {y | f y = false}
  | SubprotocolPath.bob_true f P s hs => reachYPath hs ∩ {y | f y = true}
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def reachX {s p : Protocol X Y α} (hsp : IsSubprotocol s p) : Set X :=
  reachXPath (choosePath hsp)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def reachY {s p : Protocol X Y α} (hsp : IsSubprotocol s p) : Set Y :=
  reachYPath (choosePath hsp)
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
noncomputable def testSubprotocol {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (qIn qOut : Protocol X Y α) : Protocol X Y α :=
  Protocol.alice (fun x => by
    classical
    exact decide (x ∈ reachX hsp)) (fun bx =>
    Protocol.bob (fun y => by
      classical
      exact decide (y ∈ reachY hsp)) (fun bY =>
        if bx && bY then qIn else qOut))
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
@[simp] lemma testSubprotocol_complexity
    {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (qIn qOut : Protocol X Y α) :
    (testSubprotocol hsp qIn qOut).complexity =
      2 + max qIn.complexity qOut.complexity := by
  simp [testSubprotocol, complexity, Nat.max_comm]
  omega
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
def comap {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    Protocol X' Y' α :=
  match p with
  | .output a => .output a
  | Protocol.alice f P =>
      Protocol.alice (f ∘ fX) (fun b => (P b).comap fX fY)
  | Protocol.bob f P =>
      Protocol.bob (f ∘ fY) (fun b => (P b).comap fX fY)
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
@[simp]
theorem comap_run {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y)
    (x' : X') (y' : Y') :
    (p.comap fX fY).run x' y' = p.run (fX x') (fY y') := by
  induction p <;> simp [comap, run, *]
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
@[simp]
theorem comap_complexity {X' Y' : Type*} (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    (p.comap fX fY).complexity = p.complexity := by
  induction p <;> simp [comap, complexity, *]
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

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.Rectangle
variable {X Y α : Type*}
def IsRectangle (S : Set (X × Y)) : Prop :=
  ∃ A : Set X, ∃ B : Set Y, S = A ×ˢ B
end CommunicationComplexity.Rectangle

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def swapInputSet (R : Set (X × Y)) : Set (Y × X) :=
  {yx | (yx.2, yx.1) ∈ R}
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
@[simp]
theorem mem_swapInputSet (R : Set (X × Y)) (yx : Y × X) :
    yx ∈ swapInputSet R ↔ (yx.2, yx.1) ∈ R :=
  Iff.rfl
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
@[simp]
theorem swapInputSet_swapInputSet (R : Set (X × Y)) :
    swapInputSet (swapInputSet R) = R := by
  ext xy
  rfl
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
def preimageInputSet {X' Y' : Type*} (fX : X' → X) (fY : Y' → Y) (R : Set (X × Y)) :
    Set (X' × Y') :=
  {xy | (fX xy.1, fY xy.2) ∈ R}
end CommunicationComplexity.Deterministic.Protocol

namespace CommunicationComplexity.Deterministic.Protocol
variable {X Y α : Type*}
@[simp]
theorem mem_preimageInputSet {X' Y' : Type*} (fX : X' → X) (fY : Y' → Y) (R : Set (X × Y))
    (xy : X' × Y') :
    xy ∈ preimageInputSet fX fY R ↔ (fX xy.1, fY xy.2) ∈ R :=
  Iff.rfl
end CommunicationComplexity.Deterministic.Protocol

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity
abbrev BoolInput (n : Nat) := Fin n → Bool
end CommunicationComplexity

namespace CommunicationComplexity
def zeroInput (n : Nat) : BoolInput n := fun _ => false
end CommunicationComplexity

namespace CommunicationComplexity
lemma exists_true_of_ne_zeroInput {n : ℕ} {x : BoolInput n} (hx : x ≠ zeroInput n) :
    ∃ i, x i = true := by
  by_contra hx'
  apply hx
  funext i
  by_cases hxi : x i = true
  · exact False.elim <| hx' ⟨i, hxi⟩
  · cases h : x i <;> simp [zeroInput, h] at *
end CommunicationComplexity

namespace CommunicationComplexity
def boolSign (b : Bool) : ℝ :=
  if b then -1 else 1
end CommunicationComplexity

namespace CommunicationComplexity
@[simp] lemma boolSign_xor (a b : Bool) :
    boolSign (Bool.xor a b) = boolSign a * boolSign b := by
  cases a <;> cases b <;> norm_num [boolSign]
end CommunicationComplexity

namespace CommunicationComplexity
lemma boolSign_sum {α : Type*} (s : Finset α) (f : α → Bool) :
    boolSign (Finset.sum s f) = Finset.prod s (fun i => boolSign (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [boolSign]
  | insert a s ha hs =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      change boolSign (Bool.xor (f a) (Finset.sum s f)) = _
      rw [boolSign_xor]
      simpa [mul_assoc] using congrArg (fun t => boolSign (f a) * t) hs
end CommunicationComplexity

namespace CommunicationComplexity
def flipAt {n : ℕ} (i : Fin n) (x : BoolInput n) : BoolInput n :=
  Function.update x i (!(x i))
end CommunicationComplexity

namespace CommunicationComplexity
@[simp] lemma flipAt_apply_same {n : ℕ} (i : Fin n) (x : BoolInput n) :
    flipAt i x i = !(x i) := by
  simp [flipAt]
end CommunicationComplexity

namespace CommunicationComplexity
@[simp] lemma flipAt_apply_ne {n : ℕ} {i j : Fin n} (hij : j ≠ i) (x : BoolInput n) :
    flipAt i x j = x j := by
  simp [flipAt, hij]
end CommunicationComplexity

namespace CommunicationComplexity
@[simp] lemma flipAt_flipAt {n : ℕ} (i : Fin n) (x : BoolInput n) :
    flipAt i (flipAt i x) = x := by
  ext j
  by_cases hij : j = i
  · subst hij
    simp [flipAt]
  · simp [flipAt, hij]
end CommunicationComplexity

namespace CommunicationComplexity
lemma flipAt_bijective {n : ℕ} (i : Fin n) :
    Function.Bijective (flipAt i : BoolInput n → BoolInput n) := by
  refine Function.bijective_iff_has_inverse.mpr ?_
  exact ⟨flipAt i, flipAt_flipAt i, flipAt_flipAt i⟩
end CommunicationComplexity

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open MeasureTheory

open scoped ProbabilityTheory

namespace CommunicationComplexity
class FiniteMeasureSpace (Ω : Type*) [MeasurableSpace Ω] where
  fintype :
    Fintype Ω
  discrete :
    DiscreteMeasurableSpace Ω
end CommunicationComplexity

namespace CommunicationComplexity
attribute [instance] FiniteMeasureSpace.discrete
end CommunicationComplexity

namespace CommunicationComplexity
def FiniteMeasureSpace.of
    (Ω : Type*) [MeasurableSpace Ω] [Fintype Ω] [DiscreteMeasurableSpace Ω] :
    FiniteMeasureSpace Ω :=
{ fintype := inferInstance
  discrete := inferInstance }
end CommunicationComplexity

namespace CommunicationComplexity
class FiniteProbabilitySpace (Ω : Type*) where
  toMeasureSpace : MeasureSpace Ω
  finite :
    @FiniteMeasureSpace Ω toMeasureSpace.toMeasurableSpace
  prob :
    @IsProbabilityMeasure Ω
      toMeasureSpace.toMeasurableSpace toMeasureSpace.volume
end CommunicationComplexity

namespace CommunicationComplexity
attribute [instance] FiniteProbabilitySpace.toMeasureSpace
end CommunicationComplexity

namespace CommunicationComplexity
attribute [instance] FiniteProbabilitySpace.finite
end CommunicationComplexity

namespace CommunicationComplexity
attribute [instance] FiniteProbabilitySpace.prob
end CommunicationComplexity

namespace CommunicationComplexity
def FiniteProbabilitySpace.of
    (Ω : Type*)
    [m : MeasureSpace Ω]
    [Fintype Ω]
    [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] :
    FiniteProbabilitySpace Ω :=
{ toMeasureSpace := m
  finite := FiniteMeasureSpace.of Ω
  prob := inferInstance }
end CommunicationComplexity

namespace CommunicationComplexity
noncomputable def FiniteProbabilitySpace.ofMeasure
    (Ω : Type*) [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    FiniteProbabilitySpace Ω :=
{ toMeasureSpace :=
    { toMeasurableSpace := inferInstance
      volume := μ }
  finite := inferInstance
  prob := inferInstance }
end CommunicationComplexity

namespace CommunicationComplexity
open Classical in
theorem FiniteMeasureSpace.measureReal_eq_sum_singletons
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) :
    μ.real S =
      ∑ ω : Ω, if ω ∈ S then μ.real ({ω} : Set Ω) else 0 := by
  let T : Finset Ω := Finset.univ.filter fun ω : Ω => ω ∈ S
  have hST : (↑T : Set Ω) = S := by
    ext ω
    simp [T]
  rw [← hST]
  rw [← MeasureTheory.sum_measureReal_singleton (μ := μ) T]
  simp [T, Finset.sum_filter]
end CommunicationComplexity

namespace CommunicationComplexity
open Classical in
theorem FiniteMeasureSpace.measureReal_preimage_eq_sum_fibers
    {Ω α : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    [Fintype α] (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → α) (P : α → Prop) :
    μ.real {ω | P (Z ω)} =
      ∑ z : α, if P z then μ.real (Z ⁻¹' {z}) else 0 := by
  rw [FiniteMeasureSpace.measureReal_eq_sum_singletons μ {ω | P (Z ω)}]
  symm
  calc
    (∑ z : α, if P z then μ.real (Z ⁻¹' {z}) else 0)
        = ∑ z : α, if P z then
            ∑ ω : Ω, if Z ω = z then μ.real ({ω} : Set Ω) else 0
          else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : P z
        · simp [hz, FiniteMeasureSpace.measureReal_eq_sum_singletons μ
            (Z ⁻¹' {z} : Set Ω)]
        · simp [hz]
    _ = ∑ z : α, ∑ ω : Ω,
          if P z ∧ Z ω = z then μ.real ({ω} : Set Ω) else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : P z <;> simp [hz]
    _ = ∑ ω : Ω, ∑ z : α,
          if P z ∧ Z ω = z then μ.real ({ω} : Set Ω) else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ ω : Ω, if P (Z ω) then μ.real ({ω} : Set Ω) else 0 := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hP : P (Z ω)
        · rw [Finset.sum_eq_single (Z ω)]
          · simp [hP]
          · intro z _ hz_ne
            simp [hz_ne.symm]
          · intro hnot
            simp at hnot
        · rw [Finset.sum_eq_zero]
          · simp [hP]
          · intro z _
            by_cases hz : P z ∧ Z ω = z
            · exact (hP (by rw [hz.2]; exact hz.1)).elim
            · simp [hz]
end CommunicationComplexity

namespace CommunicationComplexity
open Classical in
theorem FiniteMeasureSpace.absolutelyContinuous_iff_forall_singletons
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω] {μ ν : Measure Ω} :
    μ ≪ ν ↔ ∀ ω, ν ({ω} : Set Ω) = 0 → μ ({ω} : Set Ω) = 0 := by
  constructor
  · intro h ω hν
    exact h hν
  · intro h S hνS
    let T : Finset Ω := Finset.univ.filter fun ω : Ω => ω ∈ S
    have hST : (↑T : Set Ω) = S := by
      ext ω
      simp [T]
    rw [← hST]
    rw [← MeasureTheory.sum_measure_singleton (μ := μ) (s := T)]
    apply Finset.sum_eq_zero
    intro ω hω
    exact h ω (measure_mono_null (μ := ν) (by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      simpa [T] using hω) hνS)
end CommunicationComplexity

namespace CommunicationComplexity
theorem FiniteMeasureSpace.sq_integral_le_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) :
    (∫ ω, f ω ∂μ)^2 ≤ ∫ ω, (f ω)^2 ∂μ :=
  ConvexOn.map_integral_le
    (by simpa using (show ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) from
      Even.convexOn_pow (𝕜 := ℝ) (by decide : Even 2)))
    (by simpa using
      (show ContinuousOn (fun x : ℝ => x ^ 2) Set.univ from
        (continuous_pow 2).continuousOn))
    isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    Integrable.of_finite
    Integrable.of_finite
end CommunicationComplexity

namespace CommunicationComplexity
open Classical in
theorem FiniteMeasureSpace.integral_comp_eq_sum_measureReal_fibers
    {Ω α : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [Fintype α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → α) (f : α → ℝ) :
    ∫ ω, f (Z ω) ∂μ = ∑ z : α, μ.real (Z ⁻¹' {z}) * f z := by
  have hmap :
      ∫ ω, f (Z ω) ∂μ = ∫ z, f z ∂Measure.map Z μ := by
    exact (integral_map Measurable.of_discrete.aemeasurable
      Measurable.of_discrete.aestronglyMeasurable).symm
  rw [hmap]
  rw [MeasureTheory.integral_fintype f Integrable.of_finite]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_measureReal_apply Measurable.of_discrete MeasurableSet.of_discrete]
end CommunicationComplexity

namespace CommunicationComplexity
open Classical in
theorem FiniteMeasureSpace.measureReal_eq_sum_cond_fiber_real
    {Ω α : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    [MeasurableSpace α] [DiscreteMeasurableSpace α] [Fintype α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → α) (S : Set Ω) :
    μ.real S =
      ∑ z : α, μ.real (Z ⁻¹' {z}) * (μ[|(Z ⁻¹' {z})]).real S := by
  have htotal := ProbabilityTheory.sum_meas_smul_cond_fiber (X := Z) Measurable.of_discrete μ
  have hS : (∑ z, μ (Z ⁻¹' {z}) • μ[|(Z ⁻¹' {z})]) S = μ S := by
    rw [htotal]
  rw [Measure.real, ← hS]
  simp only [Measure.real, Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro z _
    rw [ENNReal.toReal_mul]
  · intro z _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
end CommunicationComplexity

namespace CommunicationComplexity
instance finiteMeasureSpaceBool : FiniteMeasureSpace Bool :=
  FiniteMeasureSpace.of Bool
end CommunicationComplexity

namespace CommunicationComplexity
noncomputable instance finiteMeasureSpaceProd
    (Ω₁ Ω₂ : Type*) [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [FiniteMeasureSpace Ω₁] [FiniteMeasureSpace Ω₂] :
    FiniteMeasureSpace (Ω₁ × Ω₂) :=
  FiniteMeasureSpace.of (Ω₁ × Ω₂)
end CommunicationComplexity

namespace CommunicationComplexity
open Classical in
noncomputable instance finiteMeasureSpacePi
    {ι : Type*} [Fintype ι] (Ω : ι → Type*) [∀ i, MeasurableSpace (Ω i)]
    [∀ i, FiniteMeasureSpace (Ω i)] :
    FiniteMeasureSpace ((i : ι) → Ω i) :=
  FiniteMeasureSpace.of ((i : ι) → Ω i)
end CommunicationComplexity

namespace CommunicationComplexity
noncomputable instance instProd (Ω₁ Ω₂ : Type*)
    [FiniteProbabilitySpace Ω₁] [FiniteProbabilitySpace Ω₂] :
    FiniteProbabilitySpace (Ω₁ × Ω₂) :=
  FiniteProbabilitySpace.of (Ω₁ × Ω₂)
end CommunicationComplexity

namespace CommunicationComplexity
open Classical in
noncomputable instance instPi
    {ι : Type*} [Fintype ι] (Ω : ι → Type*)
    [∀ i, FiniteProbabilitySpace (Ω i)] :
    FiniteProbabilitySpace ((i : ι) → Ω i) :=
  FiniteProbabilitySpace.of ((i : ι) → Ω i)
end CommunicationComplexity

namespace CommunicationComplexity
open Classical in
theorem uniformOn_univ_measureReal_eq_card_filter
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] (S : Set Ω) :
    ((ProbabilityTheory.uniformOn Set.univ : Measure Ω) S).toReal =
      ((Finset.univ.filter fun ω : Ω => ω ∈ S).card : ℝ) / Fintype.card Ω := by
  rw [ProbabilityTheory.uniformOn_univ, ENNReal.toReal_div,
    Measure.count_apply MeasurableSet.of_discrete,
    Set.encard_eq_coe_toFinset_card]
  simp [ENat.toENNReal_coe, ENNReal.toReal_natCast]
end CommunicationComplexity

namespace CommunicationComplexity
open Classical in
theorem uniformOn_univ_measureReal_eq_card_subtype
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] (S : Set Ω) [Fintype {ω : Ω // ω ∈ S}] :
    ((ProbabilityTheory.uniformOn Set.univ : Measure Ω) S).toReal =
      (Fintype.card {ω : Ω // ω ∈ S} : ℝ) / Fintype.card Ω := by
  rw [uniformOn_univ_measureReal_eq_card_filter]
  congr 1
  exact_mod_cast (by simp [Fintype.card_subtype])
end CommunicationComplexity

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem nonempty
    {Ω : Type*} [FiniteProbabilitySpace Ω] : Nonempty Ω :=
  (nonempty_of_measure_ne_zero (s := Set.univ) (μ := (volume : Measure Ω))
    (by simp)).to_type
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
instance (priority := 100) instNonempty
    (Ω : Type*) [FiniteProbabilitySpace Ω] : Nonempty Ω :=
  FiniteProbabilitySpace.nonempty (Ω := Ω)
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
def toPMF (Ω : Type*) [FiniteProbabilitySpace Ω] : PMF Ω :=
  (volume : Measure Ω).toPMF
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
open Classical in
theorem measure_eq {Ω : Type*} [FiniteProbabilitySpace Ω] (S : Set Ω) :
    volume S = ∑ ω : S, toPMF Ω ω := by
  have hμ : (toPMF Ω).toMeasure = (volume : Measure Ω) := by
    simp only [toPMF, Measure.toPMF_toMeasure]
  rw [← hμ]
  rw [PMF.toMeasure_apply (p := toPMF Ω) (s := S) MeasurableSet.of_discrete]
  rw [← tsum_subtype S (toPMF Ω), tsum_fintype]
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem hasSum_measure_singletons
    {Ω α : Type*} [FiniteProbabilitySpace Ω] [Finite α]
    (e : Ω ≃ α) :
    HasSum (fun a : α => volume ({e.symm a} : Set Ω)) 1 := by
  have huniv : (Set.univ : Set Ω) = ⋃ a : α, {e.symm a} := by
    ext x
    simp
  rw [show 1 = volume (Set.univ : Set Ω) from measure_univ.symm]
  rw [huniv]
  rw [measure_iUnion
    (fun a b hab => Set.disjoint_singleton.mpr (e.symm.injective.ne hab))
    (fun _ => MeasurableSet.of_discrete)]
  exact ENNReal.summable.hasSum
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem pmf_prod {Ω₁ Ω₂ : Type*}
    [FiniteProbabilitySpace Ω₁] [FiniteProbabilitySpace Ω₂] :
    ∀ x y, toPMF (Ω₁ × Ω₂) (x, y) = (toPMF Ω₁ x) * (toPMF Ω₂ y) := by
  intro x y
  -- toPMF Ω (x,y) = volume {(x,y)} = volume ({x} ×ˢ {y}) = volume {x} * volume {y}
  simp only [toPMF, Measure.toPMF_apply]
  rw [show ({(x, y)} : Set (Ω₁ × Ω₂)) = {x} ×ˢ {y} from by ext; simp [Prod.ext_iff]]
  rw [show (volume : Measure (Ω₁ × Ω₂)) = volume.prod volume from rfl]
  rw [Measure.prod_prod]
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem measureReal_prod
    {Ω₁ Ω₂ : Type*} [FiniteProbabilitySpace Ω₁] [FiniteProbabilitySpace Ω₂]
    (A : Set Ω₁) (B : Set Ω₂) :
    volume.real (A ×ˢ B : Set (Ω₁ × Ω₂)) =
      volume.real A * volume.real B := by
  rw [Measure.real, Measure.real, Measure.real]
  rw [show (volume : Measure (Ω₁ × Ω₂)) = volume.prod volume from rfl]
  rw [Measure.prod_prod, ENNReal.toReal_mul]
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem measureReal_iUnion_fintype
    {Ω ι : Type*} [FiniteProbabilitySpace Ω] [Fintype ι]
    (A : ι → Set Ω) (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    volume.real (⋃ i, A i) = ∑ i, volume.real (A i) := by
  rw [Measure.real]
  rw [measure_iUnion hdisj (fun _ => MeasurableSet.of_discrete),
    tsum_fintype, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp [Measure.real]
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem measureReal_preimage_finset
    {Ξ Ω : Type*} [FiniteProbabilitySpace Ξ]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (φ : Ξ → Ω) (T : Finset Ω) :
    volume.real (φ ⁻¹' (↑T : Set Ω) : Set Ξ) =
      ∑ a ∈ T, volume.real (φ ⁻¹' ({a} : Set Ω) : Set Ξ) := by
  rw [Measure.real]
  rw [show (φ ⁻¹' (↑T : Set Ω) : Set Ξ) = ⋃ a ∈ T, φ ⁻¹' ({a} : Set Ω) from by
    ext ξ
    simp]
  rw [measure_biUnion_finset
    (fun a _ b _ h => Disjoint.preimage _ (Set.disjoint_singleton.mpr h))
    (fun _ _ => MeasurableSet.of_discrete)]
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp [Measure.real]
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem measureReal_finset
    {Ω : Type*} [FiniteProbabilitySpace Ω] (T : Finset Ω) :
    volume.real (↑T : Set Ω) = ∑ a ∈ T, volume.real ({a} : Set Ω) := by
  exact measureReal_preimage_finset id T
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem integral_eq_pmf_sum {Ω : Type*} [FiniteProbabilitySpace Ω]
    (f : Ω → ℝ) :
    ∫ ω, f ω = ∑ ω : Ω, (toPMF Ω ω).toReal * f ω := by
  rw [MeasureTheory.integral_fintype f (Integrable.of_finite)]; congr 1
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem sq_integral_le_integral_sq
    {Ω : Type*} [FiniteProbabilitySpace Ω] (f : Ω → ℝ) :
    (∫ ω, f ω)^2 ≤ ∫ ω, (f ω)^2 :=
  FiniteMeasureSpace.sq_integral_le_integral_sq volume f
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem integral_comp_eval
    {ι Ω : Type*} [Fintype ι] [FiniteProbabilitySpace Ω]
    (i : ι) (f : Ω → ℝ) :
    ∫ ωs : (j : ι) → Ω, f (ωs i) = ∫ ω, f ω := by
  let ν : Measure ((j : ι) → Ω) := Measure.pi fun _ : ι => (volume : Measure Ω)
  have hmap := measurePreserving_eval (μ := fun (_ : ι) => (volume : Measure Ω)) i
  have h1 :
      ∫ ωs : (j : ι) → Ω, f (ωs i) ∂ν =
        ∫ ω, f ω ∂(Measure.map (Function.eval i) ν) :=
    (integral_map (measurable_pi_apply i).aemeasurable
      Measurable.of_discrete.aestronglyMeasurable).symm
  simpa [ν, hmap.map_eq] using h1
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem measureReal_pi_univ
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, FiniteProbabilitySpace (Ω i)]
    (s : ∀ i, Set (Ω i)) :
    volume.real (Set.pi Set.univ s : Set ((i : ι) → Ω i)) =
      ∏ i, volume.real (s i) := by
  rw [Measure.real]
  change (Measure.pi (fun i => (volume : Measure (Ω i))) (Set.pi Set.univ s)).toReal = _
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  simp [Measure.real]
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem measureReal_eq_integral_indicator_one
    {Ω : Type*} [FiniteProbabilitySpace Ω] (S : Set Ω) :
    volume.real S = ∫ ω, Set.indicator S (1 : Ω → ℝ) ω := by
  rw [MeasureTheory.integral_indicator_one MeasurableSet.of_discrete]
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
open Classical in
theorem measureReal_eq_integral_indicator
    {Ω : Type*} [FiniteProbabilitySpace Ω] (S : Set Ω) :
    volume.real S = ∫ ω, if ω ∈ S then (1 : ℝ) else 0 := by
  have hfun : Set.indicator S (1 : Ω → ℝ) = fun ω => if ω ∈ S then (1 : ℝ) else 0 := by
    funext ω
    by_cases hω : ω ∈ S <;> simp [hω]
  rw [measureReal_eq_integral_indicator_one, hfun]
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem pmf_toReal_sum_eq_one {Ω : Type*} [FiniteProbabilitySpace Ω] :
    ∑ ω : Ω, (toPMF Ω ω).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun _ _ => (PMF.apply_lt_top _ _).ne)]
  conv_lhs => rw [show ∑ ω : Ω, toPMF Ω ω = ∑' ω : Ω, toPMF Ω ω from
    (tsum_fintype _).symm]
  rw [PMF.tsum_coe]; simp
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem pmf_toReal_nonneg {Ω : Type*} [FiniteProbabilitySpace Ω] (ω : Ω) :
    0 ≤ (toPMF Ω ω).toReal := ENNReal.toReal_nonneg
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem exists_pmf_toReal_pos {Ω : Type*} [FiniteProbabilitySpace Ω] :
    ∃ ω : Ω, 0 < (toPMF Ω ω).toReal := by
  by_contra h; push_neg at h
  have : ∑ ω : Ω, (toPMF Ω ω).toReal = 0 :=
    Finset.sum_eq_zero (fun ω _ => le_antisymm (h ω) ENNReal.toReal_nonneg)
  linarith [pmf_toReal_sum_eq_one (Ω := Ω)]
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem integral_le_of_le {Ω : Type*} [FiniteProbabilitySpace Ω]
    {f : Ω → ℝ} {c : ℝ} (hf : ∀ ω, f ω ≤ c) :
    ∫ ω, f ω ≤ c := by
  rw [integral_eq_pmf_sum]
  calc ∑ ω, (toPMF Ω ω).toReal * f ω
      ≤ ∑ ω, (toPMF Ω ω).toReal * c :=
        Finset.sum_le_sum (fun ω _ =>
          mul_le_mul_of_nonneg_left (hf ω) (pmf_toReal_nonneg (Ω := Ω) ω))
    _ = c := by rw [← Finset.sum_mul, pmf_toReal_sum_eq_one (Ω := Ω), one_mul]
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem measureReal_ge_le_integral_div
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    {f : Ω → ℝ} {ε : ℝ} (hf_nonneg : ∀ ω, 0 ≤ f ω) (hε : 0 < ε) :
    volume.real {ω : Ω | ε ≤ f ω} ≤ (∫ ω, f ω) / ε := by
  have hmarkov :
      ε * volume.real {ω : Ω | ε ≤ f ω} ≤ ∫ ω, f ω :=
    mul_meas_ge_le_integral_of_nonneg
      (μ := (volume : Measure Ω)) (f := f)
      (ae_of_all _ hf_nonneg) Integrable.of_finite ε
  rw [le_div_iff₀ hε]
  simpa [Measure.real, mul_comm] using hmarkov
end CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity.FiniteProbabilitySpace
theorem lt_integral_of_lt {Ω : Type*} [FiniteProbabilitySpace Ω]
    {f : Ω → ℝ} {c : ℝ} (hf : ∀ ω, c < f ω) :
    c < ∫ ω, f ω := by
  rw [integral_eq_pmf_sum]
  obtain ⟨ω₀, hω₀⟩ := exists_pmf_toReal_pos (Ω := Ω)
  calc c = ∑ ω, (toPMF Ω ω).toReal * c := by
        rw [← Finset.sum_mul, pmf_toReal_sum_eq_one (Ω := Ω), one_mul]
    _ < ∑ ω, (toPMF Ω ω).toReal * f ω :=
        Finset.sum_lt_sum
          (fun ω _ => mul_le_mul_of_nonneg_left (hf ω).le (pmf_toReal_nonneg (Ω := Ω) ω))
          ⟨ω₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hf ω₀) hω₀⟩
end CommunicationComplexity.FiniteProbabilitySpace

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity
abbrev CoinTape (n : ℕ) := Fin n → Bool
end CommunicationComplexity

open CommunicationComplexity
open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open CommunicationComplexity
open MeasureTheory ProbabilityTheory

namespace CommunicationComplexity.PublicCoin
abbrev Protocol (Ω : Type*) (X Y α : Type*) :=
  Deterministic.Protocol (Ω × X) (Ω × Y) α
end CommunicationComplexity.PublicCoin

namespace CommunicationComplexity.PublicCoin.Protocol
variable {Ω : Type*} {X Y α : Type*}
def rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.run (ω, x) (ω, y)
end CommunicationComplexity.PublicCoin.Protocol

namespace CommunicationComplexity.PublicCoin.Protocol
variable {Ω : Type*} {X Y α : Type*}
@[simp]
theorem rrun_eq (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) :
    p.rrun x y ω = p.run (ω, x) (ω, y) := rfl
end CommunicationComplexity.PublicCoin.Protocol

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open CommunicationComplexity
open MeasureTheory

namespace CommunicationComplexity.PublicCoin
abbrev FiniteMessage.Protocol (Ω : Type*) (X Y α : Type*) :=
  Deterministic.FiniteMessage.Protocol (Ω × X) (Ω × Y) α
end CommunicationComplexity.PublicCoin

namespace CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
variable {Ω : Type*} {X Y α : Type*}
def rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.run (ω, x) (ω, y)
end CommunicationComplexity.PublicCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
variable {Ω : Type*} {X Y α : Type*}
@[simp]
theorem rrun_eq (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) :
    p.rrun x y ω = p.run (ω, x) (ω, y) := rfl
end CommunicationComplexity.PublicCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
variable {Ω : Type*} {X Y α : Type*}
noncomputable abbrev toProtocol (p : Protocol Ω X Y α) :
    PublicCoin.Protocol Ω X Y α :=
  Deterministic.FiniteMessage.Protocol.toProtocol p
end CommunicationComplexity.PublicCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
variable {Ω : Type*} {X Y α : Type*}
@[simp]
theorem toProtocol_rrun (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    (p.toProtocol).rrun x y ω = p.rrun x y ω := by
  simp [PublicCoin.Protocol.rrun, rrun,
    Deterministic.FiniteMessage.Protocol.toProtocol_run]
end CommunicationComplexity.PublicCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
variable {Ω : Type*} {X Y α : Type*}
@[simp]
theorem toProtocol_complexity (p : Protocol Ω X Y α) :
    (p.toProtocol).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.toProtocol_complexity p
end CommunicationComplexity.PublicCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
variable {Ω : Type*} {X Y α : Type*}
abbrev ofProtocol (p : PublicCoin.Protocol Ω X Y α) :
    Protocol Ω X Y α :=
  Deterministic.FiniteMessage.Protocol.ofProtocol p
end CommunicationComplexity.PublicCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
variable {Ω : Type*} {X Y α : Type*}
@[simp]
theorem ofProtocol_rrun
    (p : PublicCoin.Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    (ofProtocol p).rrun x y ω = p.rrun x y ω := by
  simp [rrun, PublicCoin.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.ofProtocol_run]
end CommunicationComplexity.PublicCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
variable {Ω : Type*} {X Y α : Type*}
@[simp]
theorem ofProtocol_complexity
    (p : PublicCoin.Protocol Ω X Y α) :
    (ofProtocol p).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p
end CommunicationComplexity.PublicCoin.FiniteMessage.Protocol

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open CommunicationComplexity
open MeasureTheory ProbabilityTheory

namespace CommunicationComplexity.PrivateCoin
abbrev Protocol (Ω_X Ω_Y : Type*) (X Y α : Type*) :=
  Deterministic.Protocol (Ω_X × X) (Ω_Y × Y) α
end CommunicationComplexity.PrivateCoin

namespace CommunicationComplexity.PrivateCoin.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
def output (a : α) : Protocol Ω_X Ω_Y X Y α :=
  Deterministic.Protocol.output a
end CommunicationComplexity.PrivateCoin.Protocol

namespace CommunicationComplexity.PrivateCoin.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
def alice (f : X → Ω_X → Bool)
    (P : Bool → Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.Protocol.alice (fun ⟨ω, x⟩ => f x ω) P
end CommunicationComplexity.PrivateCoin.Protocol

namespace CommunicationComplexity.PrivateCoin.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
def bob (f : Y → Ω_Y → Bool)
    (P : Bool → Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.Protocol.bob (fun ⟨ω, y⟩ => f y ω) P
end CommunicationComplexity.PrivateCoin.Protocol

namespace CommunicationComplexity.PrivateCoin.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
def rrun (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) : α :=
  p.run (ω_x, x) (ω_y, y)
end CommunicationComplexity.PrivateCoin.Protocol

namespace CommunicationComplexity.PrivateCoin.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
@[simp]
theorem rrun_eq (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) :
    p.rrun x y ω_x ω_y = p.run (ω_x, x) (ω_y, y) := rfl
end CommunicationComplexity.PrivateCoin.Protocol

namespace CommunicationComplexity.PrivateCoin.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
def ApproxSatisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω_X × Ω_Y |
      ¬Q x y (p.rrun x y ω.1 ω.2)}).toReal ≤ ε
end CommunicationComplexity.PrivateCoin.Protocol

namespace CommunicationComplexity.PrivateCoin.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
noncomputable def ApproxComputes
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω_X × Ω_Y |
      p.rrun x y ω.1 ω.2 ≠ f x y}).toReal ≤ ε
end CommunicationComplexity.PrivateCoin.Protocol

namespace CommunicationComplexity.PrivateCoin.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
theorem ApproxComputes_eq_ApproxSatisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) :
    p.ApproxComputes f ε =
      p.ApproxSatisfies (fun x y a => a = f x y) ε := by
  simp only [ApproxComputes, ApproxSatisfies, ne_eq]
end CommunicationComplexity.PrivateCoin.Protocol

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open CommunicationComplexity
open MeasureTheory

namespace CommunicationComplexity.PrivateCoin
abbrev FiniteMessage.Protocol (Ω_X Ω_Y : Type*) (X Y α : Type*) :=
  Deterministic.FiniteMessage.Protocol (Ω_X × X) (Ω_Y × Y) α
end CommunicationComplexity.PrivateCoin

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
def output (a : α) : Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.output a
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
def alice {β : Type} [Fintype β] [Nonempty β]
    (f : X → Ω_X → β) (P : β → Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.alice (fun ⟨ω, x⟩ => f x ω) P
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
def bob {β : Type} [Fintype β] [Nonempty β]
    (f : Y → Ω_Y → β) (P : β → Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.bob (fun ⟨ω, y⟩ => f y ω) P
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
def rrun (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) : α :=
  p.run (ω_x, x) (ω_y, y)
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
@[simp]
theorem rrun_eq (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) :
    p.rrun x y ω_x ω_y = p.run (ω_x, x) (ω_y, y) := rfl
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
def ApproxSatisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    volume.real {ω : Ω_X × Ω_Y |
      ¬Q x y (p.rrun x y ω.1 ω.2)} ≤ ε
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
noncomputable def ApproxComputes
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    volume.real {ω : Ω_X × Ω_Y |
      p.rrun x y ω.1 ω.2 ≠ f x y} ≤ ε
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
theorem ApproxComputes_eq_ApproxSatisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) :
    p.ApproxComputes f ε =
      p.ApproxSatisfies (fun x y a => a = f x y) ε := by
  simp only [ApproxComputes, ApproxSatisfies, ne_eq]
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
noncomputable abbrev toProtocol (p : Protocol Ω_X Ω_Y X Y α) :
    PrivateCoin.Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.toProtocol p
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
@[simp]
theorem toProtocol_rrun (p : Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (p.toProtocol).rrun x y ω_x ω_y = p.rrun x y ω_x ω_y := by
  simp [PrivateCoin.Protocol.rrun, rrun,
    Deterministic.FiniteMessage.Protocol.toProtocol_run]
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
@[simp]
theorem toProtocol_complexity (p : Protocol Ω_X Ω_Y X Y α) :
    (p.toProtocol).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.toProtocol_complexity p
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
abbrev ofProtocol (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α) :
    Protocol Ω_X Ω_Y X Y α :=
  Deterministic.FiniteMessage.Protocol.ofProtocol p
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
@[simp]
theorem ofProtocol_rrun
    (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (ofProtocol p).rrun x y ω_x ω_y = p.rrun x y ω_x ω_y := by
  simp [rrun, PrivateCoin.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.ofProtocol_run]
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
@[simp]
theorem ofProtocol_complexity
    (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α) :
    (ofProtocol p).complexity = p.complexity :=
  Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol
variable {Ω_X Ω_Y : Type*} {X Y α : Type*}
theorem ofProtocol_equiv
    (p : PrivateCoin.Protocol Ω_X Ω_Y X Y α) :
    ∃ (P : Protocol Ω_X Ω_Y X Y α),
      (∀ x y ω_x ω_y,
        P.rrun x y ω_x ω_y = p.rrun x y ω_x ω_y) ∧
      P.complexity = p.complexity :=
  ⟨ofProtocol p,
   fun x y ω_x ω_y => ofProtocol_rrun p x y ω_x ω_y,
   ofProtocol_complexity p⟩
end CommunicationComplexity.PrivateCoin.FiniteMessage.Protocol

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open MeasureTheory

open scoped ENNReal

namespace CommunicationComplexity.Internal
def cdf {m : ℕ} (p : PMF (Fin m)) (n : ℕ) : ℝ≥0∞ :=
  ∑ j : Fin m, if j < n then p j else 0
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
@[simp] lemma cdf_zero {m : ℕ} (p : PMF (Fin m)) :
    cdf p 0 = 0 := by
  simp [cdf]
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
lemma cdf_succ {m : ℕ} (p : PMF (Fin m)) (n : Fin m) :
    cdf p (n + 1) = cdf p n + p n := by
  simp only [cdf]
  -- Split: ∑ (if j < n+1 ...) = ∑ (if j < n ...) + ∑ (if j = n ...)
  have key : ∀ j : Fin m,
      (if (j : ℕ) < (n : ℕ) + 1 then (p j : ℝ≥0∞) else 0) =
      (if (j : ℕ) < (n : ℕ) then p j else 0) +
      (if j = n then p n else 0) := by
    intro j
    split_ifs with h1 h2 <;> simp_all <;> omega
  simp_rw [key, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
lemma cdf_one {m : ℕ} (p : PMF (Fin m)) :
    cdf p m = 1 := by
  simp only [cdf, Fin.is_lt, ↓reduceIte]
  have hsum := PMF.tsum_coe p
  simp only [tsum_fintype] at hsum
  exact hsum
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
lemma cdf_mono {m : ℕ} (p : PMF (Fin m)) :
    Monotone (cdf p) := by
  intro i j hij
  unfold cdf
  apply Finset.sum_le_sum
  intro k _
  split_ifs with h1 h2
  · exact le_refl _
  · exact absurd (lt_of_lt_of_le h1 hij) h2
  · exact zero_le _
  · exact le_refl _
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
noncomputable def invCdf {m : ℕ} [NeZero m] (p : PMF (Fin m)) (x : ℝ≥0∞) : Fin m :=
  (Finset.univ.filter (fun (i : Fin m) => cdf p i ≤ x)).max' (by
    unfold Finset.Nonempty
    refine ⟨(⟨0, Nat.pos_of_neZero m⟩ : Fin m), ?_⟩
    simp
  )
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
theorem invCdf_eq_iff {m : ℕ} [NeZero m] (p : PMF (Fin m)) (x : ℝ≥0∞) (hx : x < 1) (i : Fin m) :
    invCdf p x = i ↔ cdf p i ≤ x ∧ x < cdf p (i + 1) := by
  constructor
  · intro h
    unfold invCdf at h
    rw [Finset.max'_eq_iff] at h
    constructor
    · have h := h.1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    · have h := h.2
      by_cases hi : i + 1 < m
      · specialize h ⟨i + 1, hi⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
        by_contra hcontra
        rw [not_lt] at hcontra
        specialize h hcontra
        rw [← Fin.val_fin_le] at h
        simp at h
      · have hi : i + 1 = m := by omega
        rw [hi, cdf_one]
        trivial
  · rintro ⟨hlo, hhi⟩
    unfold invCdf
    rw [Finset.max'_eq_iff]
    constructor
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlo
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hlt := lt_of_le_of_lt hb hhi
      have hmono := Monotone.reflect_lt (cdf_mono p) hlt
      omega
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
noncomputable def uniformApprox {m : ℕ} [NeZero m]
    (p : PMF (Fin m)) (n : ℕ) [NeZero n] :
    Fin n → Fin m :=
  fun i => invCdf p ((i : ℝ≥0∞) / n)
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
private lemma card_nat_in_Ico (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    ((Finset.univ.filter (fun j : Fin n =>
      a ≤ (j : ℝ) ∧ (j : ℝ) < b)).card : ℝ) ≤ b - a + 1 := by
  by_cases hS : (Finset.univ.filter (fun j : Fin n =>
      a ≤ (j : ℝ) ∧ (j : ℝ) < b)).card = 0
  · simp [hS]; linarith
  set S := Finset.univ.filter (fun j : Fin n => a ≤ (j : ℝ) ∧ (j : ℝ) < b)
  have hne : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hS)
  set jlo := (S.min' hne : ℕ)
  set jhi := (S.max' hne : ℕ)
  have hlo_mem := Finset.min'_mem S hne
  have hhi_mem := Finset.max'_mem S hne
  have hlo_ge : a ≤ jlo := ((Finset.mem_filter.mp hlo_mem).2).1
  have hhi_lt : (jhi : ℝ) < b := ((Finset.mem_filter.mp hhi_mem).2).2
  have hle : jlo ≤ jhi := (Finset.min'_le S _ hhi_mem)
  -- S maps injectively (via Fin.val) into Finset.Icc jlo jhi in ℕ
  have hcard_le : S.card ≤ jhi - jlo + 1 := by
    calc S.card
        = (Finset.image Fin.val S).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (Finset.Icc jlo jhi).card := by
          apply Finset.card_le_card
          intro k hk
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
          exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hj, Finset.le_max' _ _ hj⟩
      _ = jhi - jlo + 1 := by simp; omega
  calc (S.card : ℝ) ≤ (jhi - jlo + 1 : ℕ) := by exact_mod_cast hcard_le
    _ = (jhi : ℝ) - (jlo : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hle]; simp
    _ ≤ b - a + 1 := by linarith
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
theorem uniformApprox_approx {m : ℕ} [NeZero m] (p : PMF (Fin m)) (n : ℕ) [NeZero n] (i : Fin m) :
    ((Finset.univ.filter (fun j : Fin n => uniformApprox p n j = i)).card : ℝ) / n
      ≤ (p i).toReal + 1 / n := by
  -- Characterize the preimage: invCdf p (j/n) = i iff cdf p i ≤ j/n < cdf p (i+1)
  -- Convert ENNReal div conditions to ℝ mul conditions: cdf.toReal*n ≤ j < cdf(i+1).toReal*n
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hcdf_le : cdf p i ≤ cdf p (i + 1) := cdf_mono p (Nat.le_succ _)
  have hcdf_le1 : cdf p (i + 1) ≤ 1 := by
    calc cdf p (i + 1) ≤ cdf p m := cdf_mono p (by omega)
      _ = 1 := cdf_one p
  have hcdf_fin : cdf p i ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hcdf_le.trans hcdf_le1)
  have hcdf1_fin : cdf p (i + 1) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hcdf_le1
  have hset : Finset.univ.filter (fun j : Fin n => uniformApprox p n j = i) ⊆
      Finset.univ.filter (fun j : Fin n =>
        (cdf p i).toReal * n ≤ (j : ℝ) ∧ (j : ℝ) < (cdf p (i + 1)).toReal * n) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, uniformApprox] at hj ⊢
    have hlt : (j : ℝ≥0∞) / n < 1 := by
      rw [ENNReal.div_lt_iff (by simp [NeZero.ne n]) (by simp)]
      simp [show (j : ℕ) < n from j.isLt]
    obtain ⟨hlo, hhi⟩ := (invCdf_eq_iff p _ hlt i).mp hj
    have hjn_toReal : ((j : ℝ≥0∞) / n).toReal = (j : ℝ) / n := by
      rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    constructor
    · -- cdf p i ≤ j/n (ENNReal) → cdf.toReal * n ≤ j (ℝ)
      rw [← le_div_iff₀ hn_pos]
      rw [← hjn_toReal]
      exact ENNReal.toReal_mono (ne_top_of_lt hlt) hlo
    · -- j/n < cdf p (i+1) (ENNReal) → j < cdf(i+1).toReal * n (ℝ)
      rw [← div_lt_iff₀ hn_pos, ← hjn_toReal]
      exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hlt) hcdf1_fin).mpr hhi
  have hcard := Finset.card_le_card hset
  -- Apply the ℝ counting lemma
  have hab_real : (cdf p i).toReal ≤ (cdf p (i + 1)).toReal :=
    (ENNReal.toReal_le_toReal hcdf_fin hcdf1_fin).mpr hcdf_le
  have hint := card_nat_in_Ico n ((cdf p i).toReal * n) ((cdf p (i + 1)).toReal * n)
    (mul_le_mul_of_nonneg_right hab_real (Nat.cast_nonneg _))
  -- cdf p (i+1).toReal - cdf p i.toReal = (p i).toReal
  have hdiff : (cdf p (↑i + 1)).toReal - (cdf p i).toReal = (p i).toReal := by
    rw [cdf_succ, ENNReal.toReal_add hcdf_fin (PMF.apply_lt_top p _).ne, add_sub_cancel_left]
  calc ((Finset.univ.filter _).card : ℝ) / n
      ≤ ((Finset.univ.filter _).card : ℝ) / n :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard) hn_pos.le
    _ ≤ ((cdf p (i + 1)).toReal * n - (cdf p i).toReal * n + 1) / n :=
        div_le_div_of_nonneg_right hint hn_pos.le
    _ = (p i).toReal + 1 / n := by rw [← hdiff]; field_simp
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
theorem single_coin_approx
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (φ : CoinTape n → Ω),
      ∀ (S : Set Ω),
        volume.real (φ ⁻¹' S : Set (CoinTape n)) ≤
        volume.real S + δ := by
  classical
  set k := Fintype.card Ω with hk_def
  have hk_pos : 0 < k := Fintype.card_pos
  haveI : NeZero k := ⟨by omega⟩
  -- Choose n with k / 2^n ≤ δ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (k : ℝ) / 2 ^ n ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (div_pos hδ (Nat.cast_pos.mpr hk_pos)) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, le_of_lt ?_⟩
    have : (1 / 2 : ℝ) ^ n * k < δ := by rwa [lt_div_iff₀ (by positivity)] at hn
    linarith [show (k : ℝ) / 2 ^ n = (1 / 2) ^ n * k from by
      rw [one_div, inv_pow, inv_mul_eq_div]]
  use n
  set N := Fintype.card (CoinTape n)
  have hN_pos : 0 < N := Fintype.card_pos
  haveI : NeZero N := ⟨by omega⟩
  have hN_eq : N = 2 ^ n := by simp [N, Fintype.card_fin]
  -- PMF on Fin k from the measure on Ω
  set e := Fintype.equivFin Ω
  have hpmf : HasSum (fun i : Fin k => volume ({e.symm i} : Set Ω)) 1 :=
    FiniteProbabilitySpace.hasSum_measure_singletons e
  set q : PMF (Fin k) := ⟨fun i => volume ({e.symm i} : Set Ω), hpmf⟩
  -- φ: CoinTape n ≃ Fin N → uniformApprox → Fin k → e.symm → Ω
  set eC : CoinTape n ≃ Fin N := Fintype.equivFin _
  refine ⟨fun c => e.symm (uniformApprox q N (eC c)), fun S => ?_⟩
  set φ := fun c => e.symm (uniformApprox q N (eC c))
  set g := fun c : CoinTape n => uniformApprox q N (eC c)
  set S_idx := Finset.univ.filter (fun i : Fin k => e.symm i ∈ S)
  -- Per-element bound (bijected via eC)
  have helem : ∀ i : Fin k,
      ((Finset.univ.filter (fun c : CoinTape n => g c = i)).card : ℝ) / N ≤
      (q i).toReal + 1 / N := by
    intro i
    rw [show (Finset.univ.filter (fun c : CoinTape n => g c = i)).card =
      (Finset.univ.filter (fun j : Fin N => uniformApprox q N j = i)).card from
      Finset.card_equiv eC (fun c => by simp [g])]
    exact uniformApprox_approx q N i
  -- Fiber decomposition: {c | φ c ∈ S} partitions by g(c) value
  have hfiber : (Finset.univ.filter (fun c : CoinTape n => φ c ∈ S)).card =
      ∑ i ∈ S_idx, (Finset.univ.filter (fun c : CoinTape n => g c = i)).card := by
    have : ∀ c : CoinTape n, φ c ∈ S ↔ g c ∈ S_idx := by
      intro c; simp [φ, g, S_idx]
    rw [show Finset.univ.filter (fun c => φ c ∈ S) =
      Finset.univ.filter (fun c => g c ∈ S_idx) from Finset.filter_congr (fun c _ => this c)]
    exact (Finset.sum_card_fiberwise_eq_card_filter _ _ _).symm
  -- CoinTape volume = counting / N
  have hvol_pre : volume.real (φ ⁻¹' S : Set (CoinTape n)) =
      ((Finset.univ.filter (fun c : CoinTape n => φ c ∈ S)).card : ℝ) / N := by
    simpa [N, Set.mem_preimage] using
      uniformOn_univ_measureReal_eq_card_filter
        (Ω := CoinTape n) (φ ⁻¹' S : Set (CoinTape n))
  -- Volume of S as sum of q
  have hvol_S : volume.real S = ∑ i ∈ S_idx, (q i).toReal := by
    have hpre : e ⁻¹' (↑S_idx : Set (Fin k)) = S := by
      ext x
      change (e x ∈ S_idx) ↔ x ∈ S
      simp [S_idx]
    rw [← hpre]
    rw [FiniteProbabilitySpace.measureReal_preimage_finset
      (Ξ := Ω) (Ω := Fin k) e S_idx]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hs : e ⁻¹' ({i} : Set (Fin k)) = ({e.symm i} : Set Ω) := by
      ext x
      constructor
      · intro hx
        simpa using congrArg e.symm hx
      · intro hx
        subst x
        exact e.apply_symm_apply i
    rw [hs]
    rfl
  -- Combine
  rw [hvol_pre, hfiber]; push_cast
  have hN_pos_real : (0 : ℝ) < N := by positivity
  -- (∑ f_i) / N ≤ vol(S) + δ, using per-element bound
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos_real
  calc (∑ x ∈ S_idx, ((Finset.univ.filter (fun c => g c = x)).card : ℝ)) / N
      = ∑ x ∈ S_idx, ((Finset.univ.filter (fun c => g c = x)).card : ℝ) / N := by
        simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
    _ ≤ ∑ i ∈ S_idx, ((q i).toReal + 1 / N) :=
        Finset.sum_le_sum (fun i _ => helem i)
    _ = (∑ i ∈ S_idx, (q i).toReal) + S_idx.card / N := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ volume.real S + k / N := by
        rw [hvol_S]
        have hcard : (S_idx.card : ℝ) ≤ k := by
          have h := S_idx.card_le_univ; simp only [Fintype.card_fin] at h; exact_mod_cast h
        linarith [div_le_div_of_nonneg_right hcard hN_pos_real.le]
    _ ≤ volume.real S + δ := by
        have : (k : ℝ) / N ≤ δ := by rw [hN_eq]; push_cast; exact hn
        linarith
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
private lemma weighted_sum_approx {α : Type*} [Fintype α]
    (p q : α → ℝ) (g : α → ℝ)
    (hg_nn : ∀ a, 0 ≤ g a) (hg_le1 : ∀ a, g a ≤ 1)
    (hδ : ℝ)
    (happrox : ∀ T : Finset α, ∑ a ∈ T, p a ≤ ∑ a ∈ T, q a + hδ) :
    ∑ a, p a * g a ≤ ∑ a, q a * g a + hδ := by
  -- Split into A⁺ = {a | q a < p a} and complement
  set Apos := Finset.univ.filter (fun a => q a < p a)
  suffices h : ∑ a, (p a - q a) * g a ≤ hδ by
    have : ∑ a, p a * g a - ∑ a, q a * g a = ∑ a, (p a - q a) * g a := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext a; ring
    linarith
  rw [(Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => q a < p a) _).symm]
  -- Complement: (p-q)*g ≤ 0
  have h_neg : ∑ a ∈ Finset.univ.filter (fun a => ¬(q a < p a)),
      (p a - q a) * g a ≤ 0 := Finset.sum_nonpos (fun a ha =>
    mul_nonpos_of_nonpos_of_nonneg (by linarith [(Finset.mem_filter.mp ha).2]) (hg_nn a))
  -- A⁺: (p-q)*g ≤ (p-q) since g ≤ 1
  have h_pos : ∑ a ∈ Apos, (p a - q a) * g a ≤ ∑ a ∈ Apos, (p a - q a) :=
    Finset.sum_le_sum (fun a ha =>
      mul_le_of_le_one_right (by linarith [(Finset.mem_filter.mp ha).2]) (hg_le1 a))
  -- ∑_{A⁺} (p-q) ≤ δ (from happrox applied to A⁺)
  have h_approx : ∑ a ∈ Apos, (p a - q a) ≤ hδ := by
    have := happrox Apos
    have hsub : ∑ a ∈ Apos, (p a - q a) = ∑ a ∈ Apos, p a - ∑ a ∈ Apos, q a := by
      rw [← Finset.sum_sub_distrib]
    linarith [hsub]
  linarith
end CommunicationComplexity.Internal

namespace CommunicationComplexity.Internal
private theorem product_coin_approx
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (nX nY : ℕ) (φ_X : CoinTape nX → Ω_X)
      (φ_Y : CoinTape nY → Ω_Y),
      ∀ (S : Set (Ω_X × Ω_Y)),
        volume.real (Prod.map φ_X φ_Y ⁻¹' S :
          Set (CoinTape nX × CoinTape nY)) ≤
        volume.real S + δ := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  obtain ⟨nX, φ_X, hX⟩ := single_coin_approx (Ω := Ω_X) (δ / 2) hδ2
  obtain ⟨nY, φ_Y, hY⟩ := single_coin_approx (Ω := Ω_Y) (δ / 2) hδ2
  refine ⟨nX, nY, φ_X, φ_Y, fun S => ?_⟩
  -- Slice: S_a = {b | (a,b) ∈ S}
  set S_a : Ω_X → Set Ω_Y := fun a => Prod.mk a ⁻¹' S
  -- Decompose preimage as union of rectangles
  have hunion : (Prod.map φ_X φ_Y ⁻¹' S : Set (CoinTape nX × CoinTape nY)) =
      ⋃ a : Ω_X, (φ_X ⁻¹' {a}) ×ˢ (φ_Y ⁻¹' S_a a) := by
    ext ⟨cx, cy⟩; simp [S_a, Set.mem_preimage, Set.mem_iUnion]
  have hdisj : Pairwise (fun a b : Ω_X => Disjoint
      ((φ_X ⁻¹' {a}) ×ˢ (φ_Y ⁻¹' S_a a)) ((φ_X ⁻¹' {b}) ×ˢ (φ_Y ⁻¹' S_a b))) := by
    intro a b hab; rw [Set.disjoint_left]
    rintro ⟨cx, cy⟩ h1 h2
    have hcx : φ_X cx = a := by
      simpa only [Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff] using h1.1
    have hcx' : φ_X cx = b := by
      simpa only [Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff] using h2.1
    exact hab (hcx.symm.trans hcx')
  -- LHS = ∑_a vol(φ_X⁻¹({a})) * vol(φ_Y⁻¹(S_a))
  have hLHS : volume.real (Prod.map φ_X φ_Y ⁻¹' S :
      Set (CoinTape nX × CoinTape nY)) =
      ∑ a : Ω_X, volume.real (φ_X ⁻¹' {a} : Set (CoinTape nX)) *
        volume.real (φ_Y ⁻¹' S_a a : Set (CoinTape nY)) := by
    rw [hunion, FiniteProbabilitySpace.measureReal_iUnion_fintype _ hdisj]
    refine Finset.sum_congr rfl ?_
    intro a ha
    simpa using FiniteProbabilitySpace.measureReal_prod
      (φ_X ⁻¹' ({a} : Set Ω_X)) (φ_Y ⁻¹' S_a a)
  -- RHS = ∑_a vol({a}) * vol(S_a)
  have hRHS : volume.real S = ∑ a : Ω_X, volume.real ({a} : Set Ω_X) *
      volume.real (S_a a) := by
    have hS : S = ⋃ a : Ω_X, ({a} : Set Ω_X) ×ˢ S_a a := by
      ext ⟨x, y⟩; simp [S_a]
    have hdisj' : Pairwise (fun a b : Ω_X => Disjoint
        (({a} : Set Ω_X) ×ˢ S_a a) (({b} : Set Ω_X) ×ˢ S_a b)) := by
      intro a b hab; rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      have hx : x = a := by
        simpa only [Set.mem_prod, Set.mem_singleton_iff] using h1.1
      have hx' : x = b := by
        simpa only [Set.mem_prod, Set.mem_singleton_iff] using h2.1
      exact hab (hx.symm.trans hx')
    rw [hS, FiniteProbabilitySpace.measureReal_iUnion_fintype _ hdisj']
    refine Finset.sum_congr rfl ?_
    intro a ha
    simpa using FiniteProbabilitySpace.measureReal_prod ({a} : Set Ω_X) (S_a a)
  -- Step 1: bound using hY on each slice
  set pX := fun a => volume.real (φ_X ⁻¹' {a} : Set (CoinTape nX))
  set qX := fun a => volume.real ({a} : Set Ω_X)
  rw [hLHS]
  have hstep1 : ∑ a : Ω_X, pX a * volume.real (φ_Y ⁻¹' S_a a : Set (CoinTape nY)) ≤
      ∑ a : Ω_X, pX a * (volume.real (S_a a) + δ / 2) :=
    Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hY _)
      (by simp [pX, Measure.real]))
  -- ∑ pX * (g + δ/2) = ∑ pX * g + δ/2 (since ∑ pX = 1)
  have hpX_sum : ∑ a : Ω_X, pX a = 1 := by
    calc ∑ a : Ω_X, pX a
        = volume.real (φ_X ⁻¹' (Set.univ : Set Ω_X) : Set (CoinTape nX)) := by
            symm
            simpa [pX] using
              (FiniteProbabilitySpace.measureReal_preimage_finset
                (Ξ := CoinTape nX) (Ω := Ω_X) φ_X Finset.univ)
      _ = 1 := by simp
  have hexpand : ∑ a, pX a * (volume.real (S_a a) + δ / 2) =
      (∑ a, pX a * volume.real (S_a a)) + δ / 2 := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hpX_sum, one_mul]
  -- Step 2: bound ∑ pX * g ≤ ∑ qX * g + δ/2 using weighted_sum_approx
  set gval := fun a : Ω_X => volume.real (S_a a)
  have hstep2 : ∑ a, pX a * gval a ≤ ∑ a, qX a * gval a + δ / 2 := by
    apply weighted_sum_approx pX qX gval
      (fun _ => MeasureTheory.measureReal_nonneg)
      (fun a => by
        calc gval a = volume.real (S_a a) := rfl
          _ ≤ volume.real (Set.univ : Set Ω_Y) := by
              rw [Measure.real, Measure.real]
              exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
          _ = 1 := by simp)
      (δ / 2)
      (fun T => by
        have := hX (↑T : Set Ω_X)
        simp only [pX, qX]
        -- Convert both finite-set measures into sums over singleton fibers.
        rw [FiniteProbabilitySpace.measureReal_preimage_finset
          (Ξ := CoinTape nX) (Ω := Ω_X) φ_X T] at this
        rw [FiniteProbabilitySpace.measureReal_finset (Ω := Ω_X) T] at this
        linarith)
  calc ∑ a, pX a * volume.real (φ_Y ⁻¹' S_a a : Set (CoinTape nY))
      ≤ (∑ a, pX a * gval a) + δ / 2 := by linarith [hstep1, hexpand]
    _ ≤ (∑ a, qX a * gval a) + δ / 2 + δ / 2 := by linarith [hstep2]
    _ = (∑ a, qX a * gval a) + δ := by ring
    _ = volume.real S + δ := by rw [hRHS]
end CommunicationComplexity.Internal

namespace CommunicationComplexity.PrivateCoin
noncomputable def FiniteMessage.Protocol.toCoinTape
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    Σ (nX : ℕ) (nY : ℕ),
      FiniteMessage.Protocol (CoinTape nX) (CoinTape nY) X Y α :=
  let data := Internal.product_coin_approx (Ω_X := Ω_X) (Ω_Y := Ω_Y) δ hδ
  let nX := data.choose
  let nY := data.choose_spec.choose
  let φ_X := data.choose_spec.choose_spec.choose
  let φ_Y := data.choose_spec.choose_spec.choose_spec.choose
  ⟨nX, nY, p.comap (Prod.map φ_X id) (Prod.map φ_Y id)⟩
end CommunicationComplexity.PrivateCoin

namespace CommunicationComplexity.PrivateCoin
@[simp]
theorem FiniteMessage.Protocol.toCoinTape_complexity
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    (p.toCoinTape δ hδ).2.2.complexity = p.complexity := by
  simp [FiniteMessage.Protocol.toCoinTape]
end CommunicationComplexity.PrivateCoin

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open MeasureTheory

namespace CommunicationComplexity.PublicCoin
noncomputable def FiniteMessage.Protocol.toCoinTape
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    Σ (n : ℕ), FiniteMessage.Protocol (CoinTape n) X Y α :=
  let data := Internal.single_coin_approx (Ω := Ω) δ hδ
  let n := data.choose
  let φ := data.choose_spec.choose
  ⟨n, p.comap (Prod.map φ id) (Prod.map φ id)⟩
end CommunicationComplexity.PublicCoin

namespace CommunicationComplexity.PublicCoin
@[simp]
theorem FiniteMessage.Protocol.toCoinTape_complexity
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    (p.toCoinTape δ hδ).2.complexity = p.complexity := by
  simp [FiniteMessage.Protocol.toCoinTape]
end CommunicationComplexity.PublicCoin

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open CommunicationComplexity
open MeasureTheory ProbabilityTheory

namespace CommunicationComplexity
abbrev PublicCoin.Protocol.toDeterministic
    {Ω X Y α : Type*}
    (p : PublicCoin.Protocol Ω X Y α) (ω : Ω) :
    Deterministic.Protocol X Y α :=
  p.comap (Prod.mk ω) (Prod.mk ω)
end CommunicationComplexity

namespace CommunicationComplexity
@[simp]
theorem PublicCoin.Protocol.toDeterministic_run
    {Ω X Y α : Type*}
    (p : PublicCoin.Protocol Ω X Y α) (ω : Ω)
    (x : X) (y : Y) :
    (p.toDeterministic ω).run x y = p.rrun x y ω := by
  simp [toDeterministic, PublicCoin.Protocol.rrun]
end CommunicationComplexity

namespace CommunicationComplexity
@[simp]
theorem PublicCoin.Protocol.toDeterministic_complexity
    {Ω X Y α : Type*}
    (p : PublicCoin.Protocol Ω X Y α) (ω : Ω) :
    (p.toDeterministic ω).complexity = p.complexity := by
  simp [toDeterministic]
end CommunicationComplexity

namespace CommunicationComplexity
abbrev Deterministic.FiniteMessage.Protocol.toPrivateCoin
    {X Y α Ω_X Ω_Y : Type*}
    (p : Deterministic.FiniteMessage.Protocol X Y α) :
    PrivateCoin.FiniteMessage.Protocol Ω_X Ω_Y X Y α :=
  p.comap Prod.snd Prod.snd
end CommunicationComplexity

namespace CommunicationComplexity
@[simp]
theorem Deterministic.FiniteMessage.Protocol.toPrivateCoin_rrun
    {X Y α Ω_X Ω_Y : Type*}
    (p : Deterministic.FiniteMessage.Protocol X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    PrivateCoin.FiniteMessage.Protocol.rrun
      (p.toPrivateCoin (Ω_X := Ω_X) (Ω_Y := Ω_Y)) x y ω_x ω_y =
      p.run x y := by
  simp [toPrivateCoin, PrivateCoin.FiniteMessage.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.comap_run]
end CommunicationComplexity

namespace CommunicationComplexity
@[simp]
theorem Deterministic.FiniteMessage.Protocol.toPrivateCoin_complexity
    {X Y α Ω_X Ω_Y : Type*}
    (p : Deterministic.FiniteMessage.Protocol X Y α) :
    (p.toPrivateCoin (Ω_X := Ω_X) (Ω_Y := Ω_Y)).complexity =
      p.complexity := by
  simp [toPrivateCoin]
end CommunicationComplexity

namespace CommunicationComplexity
abbrev PublicCoin.FiniteMessage.Protocol.toDeterministic
    {Ω X Y α : Type*}
    (p : PublicCoin.FiniteMessage.Protocol Ω X Y α) (ω : Ω) :
    Deterministic.FiniteMessage.Protocol X Y α :=
  p.comap (Prod.mk ω) (Prod.mk ω)
end CommunicationComplexity

namespace CommunicationComplexity
@[simp]
theorem PublicCoin.FiniteMessage.Protocol.toDeterministic_run
    {Ω X Y α : Type*}
    (p : PublicCoin.FiniteMessage.Protocol Ω X Y α) (ω : Ω)
    (x : X) (y : Y) :
    (p.toDeterministic ω).run x y = p.rrun x y ω := by
  simp [toDeterministic, rrun,
    Deterministic.FiniteMessage.Protocol.comap_run]
end CommunicationComplexity

namespace CommunicationComplexity
@[simp]
theorem PublicCoin.FiniteMessage.Protocol.toDeterministic_complexity
    {Ω X Y α : Type*}
    (p : PublicCoin.FiniteMessage.Protocol Ω X Y α) (ω : Ω) :
    (p.toDeterministic ω).complexity = p.complexity := by
  simp [toDeterministic]
end CommunicationComplexity

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open CommunicationComplexity
open MeasureTheory

open CommunicationComplexity
open scoped BigOperators

namespace CommunicationComplexity
variable {X Y : Type*}
noncomputable def discrepancy
    [μ : FiniteProbabilitySpace (X × Y)]
    (g : X → Y → Bool)
    (S : Set (X × Y)) : ℝ := by
  classical
  exact ∫ xy : X × Y,
    (if xy ∈ S then (1 : ℝ) else 0) * boolSign (g xy.1 xy.2)
end CommunicationComplexity

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open CommunicationComplexity
open MeasureTheory

open CommunicationComplexity
open ProbabilityTheory

open CommunicationComplexity
open scoped BigOperators

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
def innerProduct (n : ℕ) (x y : BoolInput n) : Bool :=
  ∑ i, (x i && y i)
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
@[simp] lemma innerProduct_zero_right (x : BoolInput n) :
    innerProduct n x (zeroInput n) = false := by
  unfold innerProduct zeroInput
  refine Finset.sum_eq_zero ?_
  intro i hi
  cases hxi : x i <;> decide
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
private lemma pmf_toReal_eq_two_pow_inv (x : BoolInput n) :
    (FiniteProbabilitySpace.toPMF (BoolInput n) x).toReal = (1 : ℝ) / 2 ^ n := by
  classical
  change (volume (Set.singleton x : Set (BoolInput n))).toReal = (1 : ℝ) / 2 ^ n
  change
    (((ProbabilityTheory.uniformOn Set.univ : Measure (BoolInput n))
        (Set.singleton x)).toReal = (1 : ℝ) / 2 ^ n)
  rw [ProbabilityTheory.uniformOn_univ, ENNReal.toReal_div]
  have hcount : (Measure.count (Set.singleton x)).toReal = 1 := by
    unfold Set.singleton
    simp
  have hcard :
      (↑(Fintype.card (BoolInput n)) : ENNReal).toReal = 2 ^ n := by
    simp [BoolInput, Fintype.card_pi, Fintype.card_fin, Fintype.card_bool]
  rw [hcount]
  rw [hcard]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
private lemma integral_eq_average_sum (f : BoolInput n → ℝ) :
    ∫ x, f x = ((1 : ℝ) / 2 ^ n) * ∑ x, f x := by
  rw [FiniteProbabilitySpace.integral_eq_pmf_sum]
  simp_rw [pmf_toReal_eq_two_pow_inv]
  rw [Finset.mul_sum]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
lemma innerProduct_flipAt_eq_xor (x y : BoolInput n) (i : Fin n) (hyi : y i = true) :
    innerProduct n (flipAt i x) y = Bool.xor (innerProduct n x y) true := by
  unfold innerProduct
  rw [← Finset.add_sum_erase (a := i) (h := Finset.mem_univ _)]
  rw [← Finset.add_sum_erase (a := i) (h := Finset.mem_univ _)]
  unfold flipAt
  simp only [Function.update_self]
  nth_rw 1 [Finset.sum_congr (g := fun j => x j && y j) rfl]
  · rw [hyi]
    simp only [Bool.and_true, Bool.bne_true]
    rw [(show (∀ x y, (!x) + y = !(x + y)) by decide)]
  · intro x_1 hx
    simp at hx
    simp [hx]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
private lemma sum_boolSign_innerProduct_eq_zero_of_exists_true
    (z : BoolInput n) {i : Fin n} (hzi : z i = true) :
    ∑ x : BoolInput n, boolSign (innerProduct n x z) = 0 := by
  let S : ℝ := ∑ x : BoolInput n, boolSign (innerProduct n x z)
  have hperm :
      S = ∑ x : BoolInput n, boolSign (innerProduct n (flipAt i x) z) := by
    unfold S
    symm
    exact Fintype.sum_bijective (flipAt i) (flipAt_bijective i)
      (fun x => boolSign (innerProduct n (flipAt i x) z))
      (fun x => boolSign (innerProduct n x z))
      (fun x => rfl)
  have hneg :
      (∑ x : BoolInput n, boolSign (innerProduct n (flipAt i x) z)) = -S := by
    unfold S
    have hpoint :
        ∀ x : BoolInput n,
          boolSign (innerProduct n (flipAt i x) z) = -boolSign (innerProduct n x z) := by
      intro x
      rw [innerProduct_flipAt_eq_xor x z i hzi, boolSign_xor]
      norm_num [boolSign]
    rw [show (∑ x : BoolInput n, boolSign (innerProduct n (flipAt i x) z)) =
      ∑ x : BoolInput n, -boolSign (innerProduct n x z) by
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact hpoint x]
    simp
  have hEq : S = -S := hperm.trans hneg
  linarith
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
private lemma sum_boolSign_innerProduct_eq_zeroInput_indicator
    (z : BoolInput n) :
    ∑ x : BoolInput n, boolSign (innerProduct n x z) =
      if z = zeroInput n then 2 ^ n else 0 := by
  by_cases hz : z = zeroInput n
  · subst hz
    simp [innerProduct_zero_right, boolSign]
  · obtain ⟨i, hzi⟩ := exists_true_of_ne_zeroInput hz
    simp [hz, sum_boolSign_innerProduct_eq_zero_of_exists_true z hzi]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
def xorInput (y z : BoolInput n) : BoolInput n :=
  fun i => Bool.xor (y i) (z i)
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
@[simp] private lemma xorInput_apply (y z : BoolInput n) (i : Fin n) :
    xorInput y z i = Bool.xor (y i) (z i) := rfl
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
@[simp] private lemma xorInput_eq_zeroInput_iff (y z : BoolInput n) :
    xorInput y z = zeroInput n ↔ y = z := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    cases hy : y i <;> cases hz : z i <;> simp [xorInput, zeroInput, hy, hz] at hi ⊢
  · intro h
    subst h
    funext i
    simp [xorInput, zeroInput]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
private lemma boolSign_innerProduct_mul_eq_xorInput
    (x y z : BoolInput n) :
    boolSign (innerProduct n x y) * boolSign (innerProduct n x z) =
      boolSign (innerProduct n x (xorInput y z)) := by
  rw [innerProduct, innerProduct, innerProduct, boolSign_sum, boolSign_sum, boolSign_sum]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i hi
  cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
    simp [xorInput, boolSign, hy, hz]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
private lemma sum_boolSign_innerProduct_mul_eq_indicator
    (y z : BoolInput n) :
    ∑ x : BoolInput n, boolSign (innerProduct n x y) * boolSign (innerProduct n x z) =
      if y = z then 2 ^ n else 0 := by
  simp_rw [boolSign_innerProduct_mul_eq_xorInput]
  rw [sum_boolSign_innerProduct_eq_zeroInput_indicator]
  simp [xorInput_eq_zeroInput_iff]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
private lemma indicatorOne_sq
    (B : Set (BoolInput n)) (y : BoolInput n) :
    (Set.indicator B (1 : BoolInput n → ℝ) y)^2 =
      Set.indicator B (1 : BoolInput n → ℝ) y := by
  by_cases hy : y ∈ B <;> simp [hy, pow_two]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
private lemma indicatorOne_le_one
    (B : Set (BoolInput n)) (y : BoolInput n) :
    Set.indicator B (1 : BoolInput n → ℝ) y ≤ 1 := by
  by_cases hy : y ∈ B <;> simp [hy]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
open Classical in
private lemma sum_sq_eq_sum_prod
    {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    ∑ x : α, (∑ y : β, f x y)^2 =
      ∑ yz : β × β, ∑ x : α, f x yz.1 * f x yz.2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro _ _
  simp only [pow_two, Fintype.sum_mul_sum]
  rw [eq_comm]
  apply Fintype.sum_prod_type
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
private lemma sum_mul_mul
    {α : Type*} [Fintype α] (a b : ℝ) (f g : α → ℝ) :
    ∑ x : α, (a * f x) * (b * g x) = a * b * ∑ x : α, f x * g x := by
  conv =>
    enter [1, 2, x]
    equals (a * b) * (f x * g x) => ring
  rw [Finset.mul_sum]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
private lemma sum_mul_ite_eq_diag
    {α : Type*} [Fintype α] [DecidableEq α] (h : α → α → ℝ) (c : ℝ) :
    ∑ yz : α × α, h yz.1 yz.2 * (if yz.1 = yz.2 then c else 0) =
      ∑ y : α, h y y * c := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro y hy
  simp
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
private lemma sum_sq_mul_of_orthogonal
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (φ : α → β → ℝ) (c : ℝ) (b : β → ℝ)
    (horth : ∀ y z, ∑ x : α, φ x y * φ x z = if y = z then c else 0) :
    ∑ x : α, (∑ y : β, b y * φ x y)^2 =
      ∑ y : β, (b y)^2 * c := by
  rw [sum_sq_eq_sum_prod]
  simp_rw [sum_mul_mul, horth]
  rw [sum_mul_ite_eq_diag (fun y z => b y * b z)]
  refine Finset.sum_congr rfl ?_
  ring_nf
  simp
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
open Classical in
private lemma sum_sq_mul_boolSign_innerProduct
    (b : BoolInput n → ℝ) :
    ∑ x : BoolInput n,
      (∑ y : BoolInput n, b y * boolSign (innerProduct n x y))^2 =
      ∑ y : BoolInput n, (b y)^2 * (2 ^ n : ℝ) := by
  refine sum_sq_mul_of_orthogonal
    (fun x y => boolSign (innerProduct n x y))
    (2 ^ n) b ?_
  intro y z
  simpa [mul_assoc] using sum_boolSign_innerProduct_mul_eq_indicator (n := n) y z
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
open Classical in
private lemma sum_sq_indicator_mul_boolSign_innerProduct_le
    (B : Set (BoolInput n)) :
    ∑ x : BoolInput n,
      (∑ y : BoolInput n, Set.indicator B 1 y * boolSign (innerProduct n x y))^2 ≤
      (2 ^ n : ℝ)^2 := by
  rw [sum_sq_mul_boolSign_innerProduct (n := n) (b := Set.indicator B 1)]
  have hdiag_bound :
      ∑ y : BoolInput n, (Set.indicator B 1 y)^2 * (2 ^ n : ℝ) ≤
        ∑ y : BoolInput n, 1 * (2 ^ n : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro y hy
    rw [indicatorOne_sq B y]
    gcongr
    exact indicatorOne_le_one B y
  calc
    ∑ y : BoolInput n, (Set.indicator B 1 y)^2 * (2 ^ n : ℝ)
      ≤ ∑ y : BoolInput n, 1 * (2 ^ n : ℝ) := hdiag_bound
    _ = (2 ^ n : ℝ)^2 := by
      simp [BoolInput, Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, pow_two]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
open Classical in
private lemma integral_sq_indicator_mul_boolSign_innerProduct_le
    (B : Set (BoolInput n)) :
    ∫ x : BoolInput n,
      (∫ y : BoolInput n,
        (if y ∈ B then (1 : ℝ) else 0) * boolSign (innerProduct n x y))^2 ≤
      (1 : ℝ) / 2 ^ n := by
  simp_rw [integral_eq_average_sum]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  simp only [one_div, inv_pow, inv_pos, Nat.ofNat_pos, pow_pos,
    mul_le_iff_le_one_right]
  rw [inv_mul_le_one₀ (by positivity)]
  apply sum_sq_indicator_mul_boolSign_innerProduct_le
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
open Classical in
private lemma discrepancy_prod_eq_integral
    (A B : Set (BoolInput n)) :
    discrepancy (innerProduct n) (A ×ˢ B : Set (BoolInput n × BoolInput n)) =
      ∫ x : BoolInput n,
        (if x ∈ A then (1 : ℝ) else 0) *
          ∫ y : BoolInput n,
            (if y ∈ B then (1 : ℝ) else 0) * boolSign (innerProduct n x y) := by
  rw [discrepancy]
  simp_rw [Set.mem_prod]
  rw [show (volume : Measure (BoolInput n × BoolInput n)) =
    (volume : Measure (BoolInput n)).prod (volume : Measure (BoolInput n)) from rfl]
  rw [MeasureTheory.integral_prod _ (Integrable.of_finite)]
  refine integral_congr_ae ?_
  filter_upwards with x
  by_cases hx : x ∈ A <;> simp [hx]
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
open Classical in
private lemma sq_discrepancy_prod_le
    (A B : Set (BoolInput n)) :
    (discrepancy (innerProduct n) (A ×ˢ B : Set (BoolInput n × BoolInput n)))^2 ≤
      (1 : ℝ) / 2 ^ n := by
  rw [discrepancy_prod_eq_integral]
  apply le_trans (FiniteProbabilitySpace.sq_integral_le_integral_sq _)
  refine le_trans ?_ (integral_sq_indicator_mul_boolSign_innerProduct_le B)
  apply MeasureTheory.integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro x
  simp only
  by_cases hx : x ∈ A
  · simp [hx]
  · simp only [hx, ↓reduceIte, zero_mul, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, ite_mul, one_mul, zero_mul]
    apply sq_nonneg
end CommunicationComplexity.Functions.InnerProduct
end

noncomputable section
namespace CommunicationComplexity.Functions.InnerProduct
variable {n : ℕ}
open Classical in
theorem abs_discrepancy_le_of_isRectangle
    (R : Set (BoolInput n × BoolInput n)) (hR : Rectangle.IsRectangle R) :
    |discrepancy (innerProduct n) R| ≤ Real.sqrt ((1 : ℝ) / 2 ^ n) := by
  rcases hR with ⟨A, B, rfl⟩
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa [sq_abs, Real.sq_sqrt (show 0 ≤ (1 : ℝ) / 2 ^ n by positivity)] using
    sq_discrepancy_prod_le (n := n) A B
end CommunicationComplexity.Functions.InnerProduct
end
