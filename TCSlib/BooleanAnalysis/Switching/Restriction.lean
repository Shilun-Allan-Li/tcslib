import TCSlib.BooleanAnalysis.Switching.Circuit
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star

/-!
# Switching Lemma — Basic Definitions

Basic definitions for the switching lemma: restrictions, their effect on
literals/terms/DNFs, and small auxiliary lemmas used throughout the proof.
-/

open Classical

namespace SwitchingLemma2

variable {n : ℕ}

/-! ## Restrictions -/

abbrev Restriction (n : ℕ) := Fin n → Option Bool

namespace Restriction

def freeVars {n : ℕ} (ρ : Restriction n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (ρ i).isNone)

def numFree {n : ℕ} (ρ : Restriction n) : ℕ := ρ.freeVars.card

def extend {n : ℕ} (ρ : Restriction n) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => (ρ i).getD (x i)

/-- Fix a list of (variable, value) pairs in a restriction. -/
def fixVars {n : ℕ} : Restriction n → List (Fin n × Bool) → Restriction n
  | ρ, [] => ρ
  | ρ, (v, b) :: rest => fixVars (Function.update ρ v (some b)) rest

/-- Un-fix a list of variables (set to `none`), restoring them to free. -/
def unfixVars {n : ℕ} : Restriction n → List (Fin n × Bool) → Restriction n
  | ρ, [] => ρ
  | ρ, (v, _) :: rest => unfixVars (Function.update ρ v none) rest

end Restriction

private instance (n : ℕ) : Fintype (Restriction n) :=
  inferInstanceAs (Fintype (Fin n → Option Bool))

def IsRestriction (s : ℕ) {n : ℕ} (ρ : Restriction n) : Prop :=
  ρ.numFree = s

/-! ## Effect of restrictions on literals and terms -/

def Literal.killedBy {n : ℕ} (l : Literal n) (ρ : Restriction n) : Prop :=
  ρ l.var = some l.neg

def Literal.fixedBy {n : ℕ} (l : Literal n) (ρ : Restriction n) : Prop :=
  ρ l.var = some (!l.neg)

def Term.killedBy {n : ℕ} (t : Term n) (ρ : Restriction n) : Prop :=
  ∃ l ∈ t, Literal.killedBy l ρ

def Term.fixedBy {n : ℕ} (t : Term n) (ρ : Restriction n) : Prop :=
  ∀ l ∈ t, Literal.fixedBy l ρ

def isAlive {n : ℕ} (t : Term n) (ρ : Restriction n) : Prop :=
  ¬Term.killedBy t ρ ∧ ¬Term.fixedBy t ρ

/-! ## Applying a restriction to a Boolean function -/

def restrictFn {n : ℕ} (f : (Fin n → Bool) → Bool) (ρ : Restriction n) :
    (Fin n → Bool) → Bool :=
  fun x => f (ρ.extend x)

def IsBadRestriction {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) (ρ : Restriction n) :
    Prop :=
  dtDepth (restrictFn f ρ) > d

def numSRestrictions (n s : ℕ) : ℕ := n.choose s * 2 ^ (n - s)

/-! ## Consistency lemmas -/

lemma Literal.killedBy_eval_false {n : ℕ} (l : Literal n) (ρ : Restriction n)
    (h : Literal.killedBy l ρ) (x : Fin n → Bool) :
    l.eval (ρ.extend x) = false := by
  unfold Literal.killedBy at h
  simp [Literal.eval, Restriction.extend, h]

lemma Literal.fixedBy_eval_true {n : ℕ} (l : Literal n) (ρ : Restriction n)
    (h : Literal.fixedBy l ρ) (x : Fin n → Bool) :
    l.eval (ρ.extend x) = true := by
  unfold Literal.fixedBy at h
  simp [Literal.eval, Restriction.extend, h]

/-! ## Auxiliary lemmas -/

private lemma dtDepth_le_of_tree {n : ℕ} {f : (Fin n → Bool) → Bool}
    (T : DecisionTree n) (d : ℕ) (hd : T.depth ≤ d)
    (heval : ∀ x, T.eval x = f x) : dtDepth f ≤ d := by
  unfold dtDepth
  exact Nat.find_min' _ ⟨T, hd, heval⟩

lemma list_any_eq_false {α : Type*} {l : List α} {p : α → Bool}
    (h : ∀ x ∈ l, p x = false) : l.any p = false := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.any_cons, h hd (by simp), ih (fun x hx => h x (by simp [hx])),
               Bool.false_or]

lemma list_all_eq_false_of_mem {α : Type*} {l : List α} {p : α → Bool}
    {a : α} (ha : a ∈ l) (hp : p a = false) : l.all p = false := by
  induction l with
  | nil => simp at ha
  | cons hd tl ih =>
    rw [List.all_cons]
    by_cases heq : a = hd
    · subst heq; simp [hp]
    · have hmem : a ∈ tl := by
        rcases List.mem_cons.mp ha with rfl | h
        · exact absurd rfl heq
        · exact h
      simp [ih hmem]

/-! ## Key structural lemmas -/

lemma fixedTerm_implies_dtDepth_zero {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (h : ∃ t ∈ f, Term.fixedBy t ρ) :
    dtDepth (restrictFn f.eval ρ) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply dtDepth_le_of_tree (.leaf true) 0 (le_refl 0)
  intro x
  obtain ⟨t, ht_mem, ht_fixed⟩ := h
  simp only [DecisionTree.eval, restrictFn, DNF.eval]
  symm
  rw [List.any_eq_true]
  refine ⟨t, ht_mem, ?_⟩
  show t.eval (ρ.extend x) = true
  rw [Term.eval, List.all_eq_true]
  exact fun l hl => Literal.fixedBy_eval_true l ρ (ht_fixed l hl) x

lemma killedAll_implies_dtDepth_zero {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (h : ∀ t ∈ f, Term.killedBy t ρ) :
    dtDepth (restrictFn f.eval ρ) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply dtDepth_le_of_tree (.leaf false) 0 (le_refl 0)
  intro x
  simp only [DecisionTree.eval, restrictFn, DNF.eval]
  symm
  apply list_any_eq_false
  intro t ht
  show t.eval (ρ.extend x) = false
  obtain ⟨l, hl_mem, hl_killed⟩ := h t ht
  simp only [Term.eval]
  exact list_all_eq_false_of_mem hl_mem (Literal.killedBy_eval_false l ρ hl_killed x)

/-- Killing is monotone w.r.t. non-free agreement: if `t` is killed by `ρ`
    and `σ` agrees with `ρ` on all non-free variables, then `t` is killed
    by `σ`. (Killing literals use non-free variables by definition.) -/
lemma killedBy_of_nonfree_agree {n : ℕ} (t : Term n) (ρ σ : Restriction n)
    (hk : Term.killedBy t ρ) (hagree : ∀ v, ρ v ≠ none → σ v = ρ v) :
    Term.killedBy t σ := by
  obtain ⟨l, hl_mem, hl_killed⟩ := hk
  exact ⟨l, hl_mem, by rwa [Literal.killedBy, hagree _ (by simp [Literal.killedBy] at hl_killed; rw [hl_killed]; simp)]⟩

/-- If `t` is the first element of `f` satisfying `¬killedBy · ρ`, and
    `σ` agrees with `ρ` on non-free variables, and `t` is not killed by `σ`,
    then `t` is also the first element satisfying `¬killedBy · σ`. -/
lemma first_clause_preserved {n : ℕ} (f : DNF n) (ρ σ : Restriction n)
    (t : Term n)
    (hfirst : f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t)
    (hagree : ∀ v, ρ v ≠ none → σ v = ρ v)
    (ht_alive : ¬Term.killedBy t σ) :
    f.find? (fun t => decide (¬Term.killedBy t σ)) = some t := by
  rw [List.find?_eq_some_iff_append] at hfirst ⊢
  obtain ⟨hpt, prefix_, suffix_, hf_eq, hprefix⟩ := hfirst
  refine ⟨by simp [ht_alive], prefix_, suffix_, hf_eq, fun t' ht'_mem => ?_⟩
  have ht'_killed_ρ : Term.killedBy t' ρ := by
    have := hprefix t' ht'_mem; simp at this; exact this
  have ht'_killed_σ := killedBy_of_nonfree_agree t' ρ σ ht'_killed_ρ hagree
  simp [ht'_killed_σ]

/-- A term's length is at most the DNF width. -/
lemma term_length_le_width {n : ℕ} (f : DNF n) (t : Term n) (ht : t ∈ f) :
    t.length ≤ f.width := by
  unfold DNF.width Term.width
  induction f with
  | nil => simp at ht
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp ht with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- `zipIdx.find?` projecting to the first component agrees with `find?`. -/
lemma zipIdx_find_to_find {α : Type*} (l : List α) (p : α → Bool)
    (x : α) (idx : ℕ) (start : ℕ := 0)
    (h : (l.zipIdx start).find? (fun ⟨a, _⟩ => p a) = some ⟨x, idx⟩) :
    l.find? p = some x := by
  induction l generalizing idx start with
  | nil => simp [List.zipIdx] at h
  | cons hd tl ih =>
    simp only [List.zipIdx_cons, List.find?_cons] at h ⊢
    by_cases hp : p hd
    · simp [hp] at h ⊢; exact h.1
    · simp [hp] at h ⊢; exact ih _ _ h

/-- If `(l, idx) ∈ t.zipIdx`, then `t.drop idx` starts with `l`. -/
lemma zipIdx_drop_spec {α : Type*} (t : List α) (l : α) (idx : ℕ)
    (h : (l, idx) ∈ t.zipIdx) : ∃ rest, t.drop idx = l :: rest := by
  obtain ⟨_, hidx, heq⟩ := List.mem_zipIdx h
  simp at hidx heq
  have hlt : idx < t.length := by omega
  rw [heq]
  exact ⟨List.drop (idx + 1) t, List.drop_eq_getElem_cons hlt⟩

/-- If `(l, idx)` comes from `t.zipIdx` filtered by a predicate, and `t` has
    length ≤ w, then `idx < w`. -/
lemma zipIdx_filter_idx_lt {α : Type*} (t : List α) (p : α × ℕ → Bool)
    (l : α) (idx : ℕ) (w : ℕ) (hw : t.length ≤ w)
    (h : (l, idx) ∈ (t.zipIdx).filter p) : idx < w := by
  have hmem := (List.mem_filter.mp h).1
  obtain ⟨_, hidx, _⟩ := List.mem_zipIdx hmem
  simp at hidx; omega

end SwitchingLemma2
