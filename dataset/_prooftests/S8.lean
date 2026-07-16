import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic
import Mathlib
import Mathlib.Tactic.Cases

namespace SwitchingLemma2
end SwitchingLemma2
namespace SwitchingLemmaCNF
end SwitchingLemmaCNF
namespace BernoulliCost
end BernoulliCost
namespace BoolCircuit
end BoolCircuit
namespace SwitchingBernoulli
end SwitchingBernoulli

set_option maxHeartbeats 800000

namespace BoolCircuit
structure Lit (n : Nat) where
  idx : Fin n
  sign : Bool
deriving DecidableEq, Repr, Hashable
end BoolCircuit

namespace BoolCircuit
@[simp]
def Lit.eval (l : Lit n) (x : Fin n → Bool) : Bool :=
  if l.sign then x l.idx else !x l.idx
end BoolCircuit

structure Literal (n : ℕ) where
  var : Fin n
  neg : Bool
  deriving DecidableEq

def Literal.eval {n : ℕ} (l : Literal n) (x : Fin n → Bool) : Bool :=
  if l.neg then !x l.var else x l.var

abbrev Term (n : ℕ) := List (Literal n)

def Term.width {n : ℕ} (t : Term n) : ℕ := t.length

def Term.eval {n : ℕ} (t : Term n) (x : Fin n → Bool) : Bool :=
  t.all (fun l => l.eval x)

abbrev DNF (n : ℕ) := List (Term n)

def DNF.width {n : ℕ} (d : DNF n) : ℕ := (d.map Term.width).foldr max 0

def DNF.eval {n : ℕ} (d : DNF n) (x : Fin n → Bool) : Bool :=
  d.any (fun t => t.eval x)

abbrev CNF (n : ℕ) := List (Term n)

def CNF.width {n : ℕ} (c : CNF n) : ℕ := (c.map Term.width).foldr max 0

def CNF.evalClause {n : ℕ} (t : Term n) (x : Fin n → Bool) : Bool :=
  t.any (fun l => l.eval x)

def CNF.eval {n : ℕ} (c : CNF n) (x : Fin n → Bool) : Bool :=
  c.all (fun t => CNF.evalClause t x)

inductive DecisionTree (n : ℕ) where
  | leaf   (val : Bool)                            : DecisionTree n
  | branch (var : Fin n) (lo hi : DecisionTree n) : DecisionTree n

def DecisionTree.eval {n : ℕ} : DecisionTree n → (Fin n → Bool) → Bool
  | .leaf b,          _  => b
  | .branch i lo hi,  x  => if x i then hi.eval x else lo.eval x

def DecisionTree.depth {n : ℕ} : DecisionTree n → ℕ
  | .leaf _          => 0
  | .branch _ lo hi  => 1 + max lo.depth hi.depth

def DecisionTree.deepPath {n : ℕ} : DecisionTree n → List (Fin n × Bool)
  | .leaf _ => []
  | .branch v lo hi =>
    if hi.depth ≥ lo.depth then
      (v, true) :: hi.deepPath
    else
      (v, false) :: lo.deepPath

lemma DecisionTree.length_deepPath {n : ℕ} (T : DecisionTree n) :
    T.deepPath.length = T.depth := by
  induction T with
  | leaf _ => rfl
  | branch v lo hi ih_lo ih_hi =>
    simp only [deepPath]
    split
    · rename_i h
      simp only [List.length_cons, ih_hi, depth]
      omega
    · rename_i h
      simp only [List.length_cons, ih_lo, depth]
      omega

def buildFullDTree {n : ℕ} (f : (Fin n → Bool) → Bool)
    (k : ℕ) (acc : Fin n → Bool) : DecisionTree n :=
  if h : k < n then
    .branch ⟨k, h⟩
      (buildFullDTree f (k + 1) (Function.update acc ⟨k, h⟩ false))
      (buildFullDTree f (k + 1) (Function.update acc ⟨k, h⟩ true))
  else
    .leaf (f acc)
termination_by n - k

lemma buildFullDTree_depth {n : ℕ} (f : (Fin n → Bool) → Bool)
    (k : ℕ) (_ : k ≤ n) (acc : Fin n → Bool) :
    (buildFullDTree f k acc).depth ≤ n - k := by
  unfold buildFullDTree
  split
  · rename_i h
    simp only [DecisionTree.depth]
    have h1 := buildFullDTree_depth f (k + 1) (by omega)
      (Function.update acc ⟨k, h⟩ false)
    have h2 := buildFullDTree_depth f (k + 1) (by omega)
      (Function.update acc ⟨k, h⟩ true)
    have h3 := max_le h1 h2
    omega
  · simp [DecisionTree.depth]
termination_by n - k

lemma buildFullDTree_eval {n : ℕ} (f : (Fin n → Bool) → Bool)
    (k : ℕ) (hk : k ≤ n) (acc x : Fin n → Bool)
    (hinv : ∀ i : Fin n, i.val < k → acc i = x i) :
    (buildFullDTree f k acc).eval x = f x := by
  unfold buildFullDTree
  split
  · rename_i h
    simp only [DecisionTree.eval]
    cases hxv : x ⟨k, h⟩ with
    | false =>
      rw [if_neg (by decide : ¬(false = true))]
      apply buildFullDTree_eval f (k + 1) (by omega)
      intro i hi
      by_cases heq : i = ⟨k, h⟩
      · subst heq; simp [Function.update, hxv]
      · simp only [Function.update, heq]
        exact hinv i (by have : i.val ≠ k := fun hv => heq (Fin.ext hv); omega)
    | true =>
      rw [if_pos rfl]
      apply buildFullDTree_eval f (k + 1) (by omega)
      intro i hi
      by_cases heq : i = ⟨k, h⟩
      · subst heq; simp [Function.update, hxv]
      · simp only [Function.update, heq]
        exact hinv i (by have : i.val ≠ k := fun hv => heq (Fin.ext hv); omega)
  · simp only [DecisionTree.eval]
    have : acc = x := funext fun i => hinv i (by omega)
    rw [this]
termination_by n - k

noncomputable def dtDepth {n : ℕ} (f : (Fin n → Bool) → Bool) : ℕ := by
  classical
  exact Nat.find (p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x)
    ⟨n, buildFullDTree f 0 (fun _ => false),
     buildFullDTree_depth f 0 (Nat.zero_le n) _,
     fun x => buildFullDTree_eval f 0 (Nat.zero_le n) _ x (fun _ hi => by omega)⟩

open Classical

namespace SwitchingLemma2
variable {n : ℕ}
abbrev Restriction (n : ℕ) := Fin n → Option Bool
end SwitchingLemma2

namespace SwitchingLemma2.Restriction
variable {n : ℕ}
def freeVars {n : ℕ} (ρ : Restriction n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (ρ i).isNone)
end SwitchingLemma2.Restriction

namespace SwitchingLemma2.Restriction
variable {n : ℕ}
def numFree {n : ℕ} (ρ : Restriction n) : ℕ := ρ.freeVars.card
end SwitchingLemma2.Restriction

namespace SwitchingLemma2.Restriction
variable {n : ℕ}
def extend {n : ℕ} (ρ : Restriction n) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => (ρ i).getD (x i)
end SwitchingLemma2.Restriction

namespace SwitchingLemma2
variable {n : ℕ}
private instance (n : ℕ) : Fintype (Restriction n) :=
  inferInstanceAs (Fintype (Fin n → Option Bool))
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
def IsRestriction (s : ℕ) {n : ℕ} (ρ : Restriction n) : Prop :=
  ρ.numFree = s
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
def Literal.killedBy {n : ℕ} (l : Literal n) (ρ : Restriction n) : Prop :=
  ρ l.var = some l.neg
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
def Literal.fixedBy {n : ℕ} (l : Literal n) (ρ : Restriction n) : Prop :=
  ρ l.var = some (!l.neg)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
def Term.killedBy {n : ℕ} (t : Term n) (ρ : Restriction n) : Prop :=
  ∃ l ∈ t, Literal.killedBy l ρ
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
def Term.fixedBy {n : ℕ} (t : Term n) (ρ : Restriction n) : Prop :=
  ∀ l ∈ t, Literal.fixedBy l ρ
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
def restrictFn {n : ℕ} (f : (Fin n → Bool) → Bool) (ρ : Restriction n) :
    (Fin n → Bool) → Bool :=
  fun x => f (ρ.extend x)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
def IsBadRestriction {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ) (ρ : Restriction n) :
    Prop :=
  dtDepth (restrictFn f ρ) > d
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
def numSRestrictions (n s : ℕ) : ℕ := n.choose s * 2 ^ (n - s)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma Literal.killedBy_eval_false {n : ℕ} (l : Literal n) (ρ : Restriction n)
    (h : Literal.killedBy l ρ) (x : Fin n → Bool) :
    l.eval (ρ.extend x) = false := by
  unfold Literal.killedBy at h
  simp [Literal.eval, Restriction.extend, h]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma Literal.fixedBy_eval_true {n : ℕ} (l : Literal n) (ρ : Restriction n)
    (h : Literal.fixedBy l ρ) (x : Fin n → Bool) :
    l.eval (ρ.extend x) = true := by
  unfold Literal.fixedBy at h
  simp [Literal.eval, Restriction.extend, h]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma dtDepth_le_of_tree {n : ℕ} {f : (Fin n → Bool) → Bool}
    (T : DecisionTree n) (d : ℕ) (hd : T.depth ≤ d)
    (heval : ∀ x, T.eval x = f x) : dtDepth f ≤ d := by
  unfold dtDepth
  exact Nat.find_min' _ ⟨T, hd, heval⟩
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma list_any_eq_false {α : Type*} {l : List α} {p : α → Bool}
    (h : ∀ x ∈ l, p x = false) : l.any p = false := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.any_cons, h hd (by simp), ih (fun x hx => h x (by simp [hx])),
               Bool.false_or]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
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
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
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
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
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
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma killedBy_of_nonfree_agree {n : ℕ} (t : Term n) (ρ σ : Restriction n)
    (hk : Term.killedBy t ρ) (hagree : ∀ v, ρ v ≠ none → σ v = ρ v) :
    Term.killedBy t σ := by
  obtain ⟨l, hl_mem, hl_killed⟩ := hk
  exact ⟨l, hl_mem, by rwa [Literal.killedBy, hagree _ (by simp [Literal.killedBy] at hl_killed; rw [hl_killed]; simp)]⟩
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
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
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
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
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma zipIdx_drop_spec {α : Type*} (t : List α) (l : α) (idx : ℕ)
    (h : (l, idx) ∈ t.zipIdx) : ∃ rest, t.drop idx = l :: rest := by
  obtain ⟨_, hidx, heq⟩ := List.mem_zipIdx h
  simp at hidx heq
  have hlt : idx < t.length := by omega
  rw [heq]
  exact ⟨List.drop (idx + 1) t, List.drop_eq_getElem_cons hlt⟩
end SwitchingLemma2

open Classical SwitchingLemma2

noncomputable section
namespace SwitchingLemma2
variable {n : ℕ}
def bernoulliRestrWeight (p : ℝ) (ρ : Restriction n) : ℝ :=
  p ^ ρ.freeVars.card * ((1 - p) / 2) ^ (n - ρ.freeVars.card)
end SwitchingLemma2
end

noncomputable section
namespace SwitchingLemma2
variable {n : ℕ}
def bernoulliRestrProb (p : ℝ) (event : Restriction n → Prop)
    [DecidablePred event] : ℝ :=
  ∑ ρ : Restriction n,
    bernoulliRestrWeight p ρ * (if event ρ then 1 else 0)
end SwitchingLemma2
end

noncomputable section
namespace SwitchingLemma2
variable {n : ℕ}
lemma bernoulliRestrWeight_nonneg' (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Restriction n) : 0 ≤ bernoulliRestrWeight p ρ := by
  unfold bernoulliRestrWeight
  apply mul_nonneg
  · exact pow_nonneg hp _
  · exact pow_nonneg (div_nonneg (sub_nonneg.mpr hp1) (by norm_num)) _
end SwitchingLemma2
end

noncomputable section
namespace SwitchingLemma2
variable {n : ℕ}
lemma bernoulliRestrWeight_sum_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ ρ : Restriction n, bernoulliRestrWeight p ρ = 1 := by
  -- We can rewrite the sum as a product of sums over each variable.
  have h_prod_sum : ∑ ρ : Fin n → Option Bool, p ^ (Finset.univ.filter (fun i => ρ i = none)).card * ((1 - p) / 2) ^ (n - (Finset.univ.filter (fun i => ρ i = none)).card) = ∏ i : Fin n, (∑ ρ_i : Option Bool, (if ρ_i = none then p else (1 - p) / 2)) := by
    rw [ Finset.prod_sum ];
    refine' Finset.sum_bij ( fun ρ _ => fun i _ => ρ i ) _ _ _ _ <;> simp +decide;
    · simp +decide [ funext_iff ];
    · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), funext fun i => rfl ⟩;
    · intro a; rw [ Finset.prod_ite ] ; simp +decide [ Finset.filter_not, Finset.card_sdiff ] ;
      exact Or.inl ( by rw [ div_pow ] );
  convert h_prod_sum using 1;
  · unfold bernoulliRestrWeight; congr; ext; simp +decide [ Restriction.freeVars ] ;
  · norm_num [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
    have h1 : p + 2 * ((1 - p) / 2) = 1 := by ring
    rw [h1, one_pow]
end SwitchingLemma2
end

noncomputable section
namespace SwitchingLemma2
variable {n : ℕ}
lemma bernoulliRestrProb_le_one' (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (event : Restriction n → Prop) [DecidablePred event] :
    bernoulliRestrProb p event ≤ 1 := by
  unfold bernoulliRestrProb
  calc ∑ ρ : Restriction n, bernoulliRestrWeight p ρ * (if event ρ then 1 else 0)
      ≤ ∑ ρ : Restriction n, bernoulliRestrWeight p ρ := by
        apply Finset.sum_le_sum
        intro ρ _
        have h1 : (if event ρ then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
        calc bernoulliRestrWeight p ρ * (if event ρ then 1 else 0)
            ≤ bernoulliRestrWeight p ρ * 1 :=
              mul_le_mul_of_nonneg_left h1 (bernoulliRestrWeight_nonneg' p hp hp1 ρ)
          _ = bernoulliRestrWeight p ρ := by ring
    _ = 1 := bernoulliRestrWeight_sum_one p hp hp1
end SwitchingLemma2
end

open Classical

namespace SwitchingLemma2
variable {n : ℕ}
lemma numFree_update_lt {n : ℕ} (ρ : Restriction n) (v : Fin n) (b : Bool)
    (hv : v ∈ ρ.freeVars) :
    Restriction.numFree (Function.update ρ v (some b)) < ρ.numFree := by
  simp only [Restriction.numFree]
  apply Finset.card_lt_card
  rw [ssubset_iff_subset_ne]
  constructor
  · intro i hi
    simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simp only [Function.update] at hi
    split at hi
    · simp at hi
    · exact hi
  · intro heq
    have hv_not : v ∉ Restriction.freeVars (Function.update ρ v (some b)) := by
      simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [Function.update]
    rw [← heq] at hv
    exact hv_not hv
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
noncomputable def termSubTree {n : ℕ} :
    List (Literal n) → Restriction n →
    (Restriction n → DecisionTree n) → DecisionTree n
  | [], ρ, cont => cont ρ
  | l :: rest, ρ, cont =>
    if l.var ∈ ρ.freeVars then
      .branch l.var
        (termSubTree rest (Function.update ρ l.var (some false)) cont)
        (termSubTree rest (Function.update ρ l.var (some true)) cont)
    else
      termSubTree rest ρ cont
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
noncomputable def canonicalDTree {n : ℕ} (f : DNF n) (ρ : Restriction n) :
    DecisionTree n :=
  canonicalDTree.go f (ρ.numFree + 1) ρ
where
  go (f : DNF n) : ℕ → Restriction n → DecisionTree n
    | 0, _ => .leaf false
    | fuel + 1, ρ =>
      if _h1 : ∀ t ∈ f, Term.killedBy t ρ then .leaf false
      else if _h2 : ∃ t ∈ f, Term.fixedBy t ρ then .leaf true
      else
        match f.find? (fun t => decide (¬Term.killedBy t ρ)) with
        | none => .leaf false
        | some t =>
          termSubTree t ρ (fun ρ' =>
            if decide (Term.fixedBy t ρ') then .leaf true
            else go f fuel ρ')
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma extend_update_self {n : ℕ} (ρ : Restriction n) (v : Fin n)
    (x : Fin n → Bool) (b : Bool) (hv : v ∈ ρ.freeVars) (hxv : x v = b) :
    Restriction.extend (Function.update ρ v (some b)) x = ρ.extend x := by
  funext i
  simp only [Restriction.extend]
  by_cases h : i = v
  · subst h
    have hfree : ρ i = none := by
      simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
                  Option.isNone_iff_eq_none] at hv
      exact hv
    simp [Function.update, hfree, hxv]
  · simp [Function.update, h]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma termSubTree_eval {n : ℕ} (lits : List (Literal n))
    (ρ : Restriction n) (cont : Restriction n → DecisionTree n) (x : Fin n → Bool) :
    (termSubTree lits ρ cont).eval x =
    (cont (lits.foldl (fun ρ' l =>
      if l.var ∈ ρ'.freeVars then Function.update ρ' l.var (some (x l.var)) else ρ') ρ)).eval x := by
  induction lits generalizing ρ with
  | nil => simp [termSubTree]
  | cons l rest ih =>
    simp only [termSubTree]
    split
    · rename_i hfree
      simp only [DecisionTree.eval]
      cases hxv : x l.var <;> simp [hxv, ih] <;>
        congr 1 <;> simp [hfree]
    · rename_i hnfree
      rw [ih]; congr 1; simp [List.foldl, hnfree]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma termSubTree_extend_eq {n : ℕ} (lits : List (Literal n))
    (ρ : Restriction n) (x : Fin n → Bool) :
    (lits.foldl (fun (ρ' : Restriction n) l =>
      if l.var ∈ ρ'.freeVars then Function.update ρ' l.var (some (x l.var))
      else ρ') ρ).extend x = ρ.extend x := by
  induction lits generalizing ρ with
  | nil => rfl
  | cons l rest ih =>
    simp only [List.foldl]
    split
    · rename_i hfree
      rw [ih]; exact extend_update_self ρ l.var x (x l.var) hfree rfl
    · exact ih ρ
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma termSubTree_foldl_preserves_nonnone {n : ℕ}
    (lits : List (Literal n)) (ρ : Restriction n) (x : Fin n → Bool)
    (v : Fin n) (hv : ρ v ≠ none) :
    (lits.foldl (fun (ρ' : Restriction n) (lit : Literal n) =>
      if lit.var ∈ Restriction.freeVars ρ' then Function.update ρ' lit.var (some (x lit.var))
      else ρ') ρ) v ≠ none := by
  induction lits generalizing ρ with
  | nil => exact hv
  | cons hd tl ih =>
    simp only [List.foldl_cons]; apply ih
    split
    · simp only [Function.update_apply]; split <;> simp_all
    · exact hv
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma termSubTree_foldl_sets_member {n : ℕ}
    (lits : List (Literal n)) (ρ : Restriction n) (x : Fin n → Bool)
    (l : Literal n) (hl : l ∈ lits) (hfree : l.var ∈ ρ.freeVars) :
    (lits.foldl (fun (ρ' : Restriction n) (lit : Literal n) =>
      if lit.var ∈ Restriction.freeVars ρ' then Function.update ρ' lit.var (some (x lit.var))
      else ρ') ρ) l.var ≠ none := by
  induction lits generalizing ρ with
  | nil => simp at hl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hl with rfl | hl_tl
    · apply termSubTree_foldl_preserves_nonnone
      simp only [hfree, ↓reduceIte]
      simp [Function.update]
    · -- l ∈ tl, need to show foldl over (hd :: tl) doesn't set l.var to none
      split
      · -- hd.var ∈ ρ.freeVars
        by_cases heq : l.var = hd.var
        · -- l.var = hd.var: update sets it to some, preserved by foldl
          apply termSubTree_foldl_preserves_nonnone
          rw [Function.update_apply, if_pos heq]
          exact Option.some_ne_none _
        · -- l.var ≠ hd.var: l.var still free after update
          apply ih _ hl_tl
          rw [Restriction.freeVars, Finset.mem_filter] at hfree ⊢
          simp only [Finset.mem_univ, true_and,
            Option.isNone_iff_eq_none] at hfree ⊢
          rw [Function.update_apply, if_neg heq]
          exact hfree
      · -- hd.var ∉ ρ.freeVars: ρ unchanged, use ih directly
        exact ih _ hl_tl hfree
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma termSubTree_foldl_numFree_lt {n : ℕ}
    (lits : List (Literal n)) (ρ : Restriction n) (x : Fin n → Bool)
    (l : Literal n) (hl : l ∈ lits) (hfree : l.var ∈ ρ.freeVars) :
    (lits.foldl (fun (ρ' : Restriction n) (lit : Literal n) =>
      if lit.var ∈ Restriction.freeVars ρ' then Function.update ρ' lit.var (some (x lit.var))
      else ρ') ρ).numFree < ρ.numFree := by
  set ρ' := lits.foldl _ ρ
  have hsub : ρ'.freeVars ⊆ ρ.freeVars := by
    intro v hv
    simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
      Option.isNone_iff_eq_none] at hv ⊢
    by_contra h; push_neg at h
    exact absurd hv (termSubTree_foldl_preserves_nonnone lits ρ x v h)
  have hne : l.var ∉ ρ'.freeVars := by
    simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
      Option.isNone_iff_eq_none]
    exact termSubTree_foldl_sets_member lits ρ x l hl hfree
  exact Finset.card_lt_card (hsub.ssubset_of_ne (fun heq => hne (heq ▸ hfree)))
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma canonicalDTree_go_correct {n : ℕ} (f : DNF n) (fuel : ℕ) (ρ : Restriction n)
    (hfuel : ρ.numFree < fuel) :
    ∀ x, (canonicalDTree.go f fuel ρ).eval x = restrictFn f.eval ρ x := by
  intro x
  induction fuel generalizing ρ with
  | zero => omega
  | succ k ih =>
    simp only [canonicalDTree.go]
    split
    · rename_i h1
      simp only [DecisionTree.eval, restrictFn, DNF.eval]; symm
      apply list_any_eq_false; intro t ht
      show t.eval (ρ.extend x) = false
      obtain ⟨l, hl_mem, hl_killed⟩ := h1 t ht
      simp only [Term.eval]
      exact list_all_eq_false_of_mem hl_mem (Literal.killedBy_eval_false l ρ hl_killed x)
    · split
      · rename_i _ h2
        simp only [DecisionTree.eval, restrictFn, DNF.eval]
        obtain ⟨t, ht_mem, ht_fixed⟩ := h2; symm; rw [List.any_eq_true]
        refine ⟨t, ht_mem, ?_⟩; show t.eval (ρ.extend x) = true
        rw [Term.eval, List.all_eq_true]
        exact fun l hl => Literal.fixedBy_eval_true l ρ (ht_fixed l hl) x
      · rename_i h1 h2; split
        · rename_i hfind; exfalso; apply h1; intro t ht
          by_contra htk; rw [List.find?_eq_none] at hfind
          exact (hfind t ht) (by simp [htk])
        · rename_i t hfind
          set ρ' := t.foldl (fun (ρ' : Restriction n) l =>
            if l.var ∈ ρ'.freeVars then Function.update ρ' l.var (some (x l.var))
            else ρ') ρ
          rw [termSubTree_eval]
          have hext : ρ'.extend x = ρ.extend x := termSubTree_extend_eq t ρ x
          split
          · rename_i ht_fixed
            simp only [DecisionTree.eval, restrictFn, DNF.eval]
            have ht_fixed' : Term.fixedBy t ρ' := of_decide_eq_true ht_fixed
            symm; rw [List.any_eq_true]
            refine ⟨t, List.mem_of_find?_eq_some hfind, ?_⟩
            show t.eval (ρ.extend x) = true
            rw [← hext, Term.eval, List.all_eq_true]
            exact fun l hl => Literal.fixedBy_eval_true l ρ' (ht_fixed' l hl) x
          · rename_i ht_not_fixed
            have hres : restrictFn f.eval ρ' x = restrictFn f.eval ρ x := by
              simp only [restrictFn]; rw [hext]
            have hρ'_lt : ρ'.numFree < k := by
              have hle : ρ.numFree ≤ k := Nat.lt_succ_iff.mp hfuel
              have ht_nk : ¬Term.killedBy t ρ := by
                have := List.find?_some hfind; simp at this; exact this
              have ht_nf : ¬Term.fixedBy t ρ :=
                fun hf => h2 ⟨t, List.mem_of_find?_eq_some hfind, hf⟩
              have ⟨l, hl_mem, hl_free⟩ : ∃ l ∈ t, l.var ∈ ρ.freeVars := by
                by_contra hall; push_neg at hall; apply ht_nf; intro l hl
                have : l.var ∉ ρ.freeVars := hall l hl
                simp [Restriction.freeVars, Finset.mem_filter, Option.isNone_iff_eq_none] at this
                cases hv : ρ l.var with
                | none => exact absurd hv this
                | some b =>
                  by_cases hbl : b = l.neg
                  · exact absurd ⟨l, hl, by rw [Literal.killedBy, hv, hbl]⟩ ht_nk
                  · show ρ l.var = some (!l.neg); rw [hv]; congr 1
                    cases b <;> cases hn : l.neg <;> simp_all
              exact lt_of_lt_of_le
                (termSubTree_foldl_numFree_lt t ρ x l hl_mem hl_free) hle
            change (canonicalDTree.go f k ρ').eval x = _
            rw [ih ρ' hρ'_lt, hres]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma canonicalDTree_correct {n : ℕ} (f : DNF n) (ρ : Restriction n) :
    ∀ x, (canonicalDTree f ρ).eval x = restrictFn f.eval ρ x :=
  canonicalDTree_go_correct f _ ρ (Nat.lt_succ_of_le (le_refl _))
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma numFree_update_le {n : ℕ} (ρ : Restriction n) (v : Fin n) (b : Bool) :
    Restriction.numFree (Function.update ρ v (some b)) ≤ ρ.numFree := by
  simp only [Restriction.numFree]
  apply Finset.card_le_card
  intro i hi
  simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
             Option.isNone_iff_eq_none] at hi ⊢
  rw [Function.update_apply] at hi
  split at hi
  · simp at hi
  · exact hi
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma termSubTree_cont_congr {n : ℕ} :
    ∀ (lits : List (Literal n)) (ρ : Restriction n)
      (cont₁ cont₂ : Restriction n → DecisionTree n)
      (_ : ∀ ρ', ρ'.numFree ≤ ρ.numFree → cont₁ ρ' = cont₂ ρ'),
      termSubTree lits ρ cont₁ = termSubTree lits ρ cont₂
  | [], ρ, cont₁, cont₂, hcont => by
      show cont₁ ρ = cont₂ ρ
      exact hcont ρ (le_refl _)
  | l :: rest, ρ, cont₁, cont₂, hcont => by
      by_cases hfree : l.var ∈ ρ.freeVars
      · simp only [termSubTree, hfree, ↓reduceIte]
        congr 1
        · apply termSubTree_cont_congr rest _ cont₁ cont₂
          intro ρ' hρ'
          exact hcont ρ' (le_trans hρ'
            (numFree_update_le ρ l.var false))
        · apply termSubTree_cont_congr rest _ cont₁ cont₂
          intro ρ' hρ'
          exact hcont ρ' (le_trans hρ'
            (numFree_update_le ρ l.var true))
      · simp only [termSubTree, hfree, ↓reduceIte]
        exact termSubTree_cont_congr rest ρ cont₁ cont₂ hcont
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma termSubTree_cont_congr_strict {n : ℕ} :
    ∀ (lits : List (Literal n)) (ρ : Restriction n)
      (_ : ∃ l ∈ lits, l.var ∈ ρ.freeVars)
      (cont₁ cont₂ : Restriction n → DecisionTree n)
      (_ : ∀ ρ', ρ'.numFree < ρ.numFree → cont₁ ρ' = cont₂ ρ'),
      termSubTree lits ρ cont₁ = termSubTree lits ρ cont₂
  | [], _, hex, _, _, _ => by
      obtain ⟨_, hl, _⟩ := hex
      exact absurd hl (List.not_mem_nil)
  | l :: rest, ρ, hex, cont₁, cont₂, hcont => by
      by_cases hfree : l.var ∈ ρ.freeVars
      · -- Free case: descend into both branches via non-strict congr.
        -- Updating at l.var strictly decreases numFree.
        simp only [termSubTree, hfree, ↓reduceIte]
        have hupd_lt_false : Restriction.numFree (Function.update ρ l.var (some false)) <
            ρ.numFree := numFree_update_lt ρ l.var false hfree
        have hupd_lt_true : Restriction.numFree (Function.update ρ l.var (some true)) <
            ρ.numFree := numFree_update_lt ρ l.var true hfree
        congr 1
        · apply termSubTree_cont_congr rest _ cont₁ cont₂
          intro ρ' hρ'
          exact hcont ρ' (Nat.lt_of_le_of_lt hρ' hupd_lt_false)
        · apply termSubTree_cont_congr rest _ cont₁ cont₂
          intro ρ' hρ'
          exact hcont ρ' (Nat.lt_of_le_of_lt hρ' hupd_lt_true)
      · -- Non-free case: skip; apply IH on rest with smaller hex.
        simp only [termSubTree, hfree, ↓reduceIte]
        have hex' : ∃ l' ∈ rest, l'.var ∈ ρ.freeVars := by
          obtain ⟨l', hl'_mem, hl'_free⟩ := hex
          rcases List.mem_cons.mp hl'_mem with rfl | hl'_tl
          · exact absurd hl'_free hfree
          · exact ⟨l', hl'_tl, hl'_free⟩
        exact termSubTree_cont_congr_strict rest ρ hex' cont₁ cont₂ hcont
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma canonicalDTree_go_fuel_invariant {n : ℕ} (f : DNF n) :
    ∀ (k : ℕ) (ρ : Restriction n) (fuel₁ fuel₂ : ℕ)
      (_ : ρ.numFree = k) (_ : ρ.numFree < fuel₁) (_ : ρ.numFree < fuel₂),
      canonicalDTree.go f fuel₁ ρ = canonicalDTree.go f fuel₂ ρ := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro ρ fuel₁ fuel₂ hk h₁ h₂
    -- Both fuels are positive.
    obtain ⟨f₁, rfl⟩ : ∃ f₁, fuel₁ = f₁ + 1 := ⟨fuel₁ - 1, by omega⟩
    obtain ⟨f₂, rfl⟩ : ∃ f₂, fuel₂ = f₂ + 1 := ⟨fuel₂ - 1, by omega⟩
    -- Unfold both `go`s.
    simp only [canonicalDTree.go]
    split_ifs with hkilled hfixed
    · rfl
    · rfl
    · -- Alive branch.
      split
      · rfl
      · rename_i t hfind
        -- t has a free literal in ρ (since it's not killed and not fixed).
        have ht_nk : ¬ Term.killedBy t ρ := by
          have := List.find?_some hfind; simp at this; exact this
        have ht_mem : t ∈ f := List.mem_of_find?_eq_some hfind
        have ht_nf : ¬ Term.fixedBy t ρ := fun hf => hfixed ⟨t, ht_mem, hf⟩
        have hex : ∃ l ∈ t, l.var ∈ ρ.freeVars := by
          by_contra hall
          push_neg at hall
          apply ht_nf
          intro l hl
          have hlnf : l.var ∉ ρ.freeVars := hall l hl
          simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ,
                     true_and, Option.isNone_iff_eq_none] at hlnf
          cases hv : ρ l.var with
          | none => exact absurd hv hlnf
          | some b =>
            show ρ l.var = some (!l.neg)
            by_cases hbl : b = l.neg
            · exact absurd ⟨l, hl, by rw [Literal.killedBy, hv, hbl]⟩ ht_nk
            · rw [hv]; congr 1
              cases b <;> cases hn : l.neg <;> simp_all
        -- Apply `termSubTree_cont_congr_strict` directly, avoiding `congr`.
        exact termSubTree_cont_congr_strict t ρ hex _ _ (by
          intro ρ' hρ'
          by_cases hfix : decide (Term.fixedBy t ρ')
          · simp only [hfix, ↓reduceIte]
          · simp only [hfix]
            have hρ'_lt_k : ρ'.numFree < k := hk ▸ hρ'
            exact ih ρ'.numFree hρ'_lt_k ρ' f₁ f₂ rfl
              (by omega) (by omega))
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma cont_eq_canonicalDTree {n : ℕ} (f : DNF n) (ρ_orig : Restriction n)
    (t : Term n) (ht_mem : t ∈ f) (ρ' : Restriction n)
    (hfuel : ρ_orig.numFree ≥ ρ'.numFree + 1) :
    (if decide (Term.fixedBy t ρ') then DecisionTree.leaf true
     else canonicalDTree.go f ρ_orig.numFree ρ') =
    canonicalDTree f ρ' := by
  split_ifs <;> simp_all +decide [ SwitchingLemma2.canonicalDTree ];
  · rw [ SwitchingLemma2.canonicalDTree.go ];
    split_ifs;
    · have := ‹∀ t ∈ f, Term.killedBy t ρ'› t ht_mem;
      obtain ⟨ l, hl₁, hl₂ ⟩ := this;
      exact absurd ( ‹Term.fixedBy t ρ'› l hl₁ ) ( by unfold Literal.fixedBy; unfold Literal.killedBy at hl₂; aesop );
    · rfl;
    · exact False.elim <| ‹¬∃ t ∈ f, Term.fixedBy t ρ'› ⟨ t, ht_mem, by assumption ⟩;
  · apply SwitchingLemma2.canonicalDTree_go_fuel_invariant;
    exacts [ rfl, hfuel, Nat.lt_succ_self _ ]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma termSubTree_cons_free {n : ℕ}
    (l : Literal n) (rest : List (Literal n)) (ρ : Restriction n)
    (cont : Restriction n → DecisionTree n)
    (hfree : l.var ∈ ρ.freeVars) :
    termSubTree (l :: rest) ρ cont = .branch l.var
      (termSubTree rest (Function.update ρ l.var (some false)) cont)
      (termSubTree rest (Function.update ρ l.var (some true)) cont) := by
  simp [termSubTree, hfree]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma termSubTree_cons_nonfree {n : ℕ}
    (l : Literal n) (rest : List (Literal n)) (ρ : Restriction n)
    (cont : Restriction n → DecisionTree n)
    (hnfree : l.var ∉ ρ.freeVars) :
    termSubTree (l :: rest) ρ cont = termSubTree rest ρ cont := by
  simp [termSubTree, hnfree]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma termSubTree_deepPath_head_free {n : ℕ}
    (l : Literal n) (rest : List (Literal n)) (ρ : Restriction n)
    (cont : Restriction n → DecisionTree n)
    (hfree : l.var ∈ ρ.freeVars) :
    ∃ b, (termSubTree (l :: rest) ρ cont).deepPath =
      (l.var, b) :: (termSubTree rest (Function.update ρ l.var (some b)) cont).deepPath := by
  rw [termSubTree_cons_free l rest ρ cont hfree]
  -- .branch l.var lo hi where:
  --   lo = termSubTree rest (update false) cont
  --   hi = termSubTree rest (update true) cont
  -- deepPath picks the deeper side (ties → true).
  simp only [DecisionTree.deepPath]
  split
  · -- hi.depth ≥ lo.depth: take true branch
    exact ⟨true, rfl⟩
  · -- hi.depth < lo.depth: take false branch
    exact ⟨false, rfl⟩
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma filter_free_update_eq {n : ℕ}
    (rest : List (Literal n)) (ρ : Restriction n) (v : Fin n) (b : Bool)
    (hdist : ∀ l ∈ rest, l.var ≠ v) :
    rest.filter (fun l => decide (l.var ∈ Restriction.freeVars (Function.update ρ v (some b)))) =
    rest.filter (fun l => decide (l.var ∈ ρ.freeVars)) := by
  -- Since the variables in `rest` are pairwise distinct and `v` is not in `rest`, the freeness of `l.var` under `Function.update ρ v (some b)` is the same as under `ρ`.
  have h_free_eq : ∀ l ∈ rest, (l.var ∈ Restriction.freeVars (Function.update ρ v (some b))) = (l.var ∈ ρ.freeVars) := by
    unfold Restriction.freeVars; aesop;
  exact List.filter_congr fun x hx => by specialize h_free_eq x hx; aesop;
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma termSubTree_deepPath_var_match {n : ℕ} :
    ∀ (lits : List (Literal n)) (ρ : Restriction n)
      (cont : Restriction n → DecisionTree n)
      (_hdistinct : lits.Pairwise (fun l₁ l₂ => l₁.var ≠ l₂.var))
      (k : ℕ)
      (hk : k < (lits.filter (fun l => decide (l.var ∈ ρ.freeVars))).length)
      (hk_path : k < (termSubTree lits ρ cont).deepPath.length),
      ((termSubTree lits ρ cont).deepPath[k]'hk_path).1 =
        ((lits.filter (fun l => decide (l.var ∈ ρ.freeVars)))[k]'hk).var := by
  intro lits ρ cont hdistinct k hk hk_path; induction' lits with l rest ih generalizing ρ cont k <;> simp +decide [ List.filter_cons ] ;
  · contradiction;
  · by_cases hfree : l.var ∈ ρ.freeVars <;> simp +decide [ hfree ] at hk hk_path ⊢;
    · obtain ⟨b, hb⟩ : ∃ b, (termSubTree (l :: rest) ρ cont).deepPath = (l.var, b) :: (termSubTree rest (Function.update ρ l.var (some b)) cont).deepPath :=
        termSubTree_deepPath_head_free l rest ρ cont hfree
      rcases k with ( _ | k ) <;> simp +decide [ hb ] at hk_path ⊢;
      convert ih ( Function.update ρ l.var ( some b ) ) cont _ k _ hk_path using 1;
      any_goals rw [ filter_free_update_eq ];
      any_goals linarith;
      any_goals rw [ List.pairwise_cons ] at hdistinct; tauto;
      congr! 2;
      refine' List.filter_congr fun x hx => _;
      by_cases h : x.var = l.var <;> simp_all +decide [ Restriction.freeVars ];
      exact hdistinct.1 x hx h.symm;
    · have heq := termSubTree_cons_nonfree l rest ρ cont hfree
      simp only [heq] at hk_path ⊢
      exact ih ρ cont (List.pairwise_cons.mp hdistinct).2 k hk hk_path
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma canonicalDTree_alive_eq_termSubTree {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (fuel : ℕ)
    (h1 : ¬ ∀ t ∈ f, Term.killedBy t ρ)
    (h2 : ¬ ∃ t ∈ f, Term.fixedBy t ρ)
    (t : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t) :
    canonicalDTree.go f (fuel + 1) ρ =
      termSubTree t ρ (fun ρ' =>
        if decide (Term.fixedBy t ρ') then .leaf true
        else canonicalDTree.go f fuel ρ') := by
  simp only [canonicalDTree.go]
  rw [dif_neg h1, dif_neg h2]
  rw [hfind]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma canonicalDTree_alive_eq_termSubTree' {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (h1 : ¬ ∀ t ∈ f, Term.killedBy t ρ)
    (h2 : ¬ ∃ t ∈ f, Term.fixedBy t ρ)
    (t : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t) :
    canonicalDTree f ρ =
      termSubTree t ρ (fun ρ' =>
        if decide (Term.fixedBy t ρ') then .leaf true
        else canonicalDTree.go f ρ.numFree ρ') := by
  show canonicalDTree.go f (ρ.numFree + 1) ρ = _
  exact canonicalDTree_alive_eq_termSubTree f ρ ρ.numFree h1 h2 t hfind
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma depth_ge_dtDepth {n : ℕ} {f : (Fin n → Bool) → Bool}
    (T : DecisionTree n) (heval : ∀ x, T.eval x = f x) :
    T.depth ≥ dtDepth f := by
  unfold dtDepth
  exact Nat.find_min' _ ⟨T, le_refl _, heval⟩
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma canonicalDTree_depth_ge {n : ℕ} (f : DNF n) (ρ : Restriction n) :
    (canonicalDTree f ρ).depth ≥ dtDepth (restrictFn f.eval ρ) :=
  depth_ge_dtDepth _ (canonicalDTree_correct f ρ)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma dtDepth_restrictFn_le_numFree {n : ℕ} (f : (Fin n → Bool) → Bool)
    (ρ : Restriction n) :
    dtDepth (restrictFn f ρ) ≤ ρ.numFree := by
  suffices h : ∀ k (ρ : Restriction n), ρ.numFree ≤ k →
      ∃ T : DecisionTree n, T.depth ≤ k ∧ ∀ x, T.eval x = restrictFn f ρ x by
    obtain ⟨T, hT, hev⟩ := h ρ.numFree ρ le_rfl
    exact (depth_ge_dtDepth T hev).trans hT
  intro k
  induction k with
  | zero =>
    intro ρ hρ
    have hempty : ρ.freeVars = ∅ := by
      apply Finset.card_eq_zero.mp
      show ρ.numFree = 0
      omega
    refine ⟨.leaf (f (ρ.extend (fun _ => false))), le_rfl, fun x => ?_⟩
    simp only [DecisionTree.eval, restrictFn]
    congr 1
    funext i
    have hi : ρ i ≠ none := by
      intro hn
      have hmem : i ∈ ρ.freeVars := by
        simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
                   Option.isNone_iff_eq_none]
        exact hn
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    simp only [Restriction.extend]
    cases hv : ρ i with
    | none => exact absurd hv hi
    | some b => rfl
  | succ k ih =>
    intro ρ hρ
    by_cases hne : ρ.freeVars.Nonempty
    · obtain ⟨v, hv⟩ := hne
      have h0 : Restriction.numFree (Function.update ρ v (some false)) < ρ.numFree :=
        numFree_update_lt ρ v false hv
      have h1 : Restriction.numFree (Function.update ρ v (some true)) < ρ.numFree :=
        numFree_update_lt ρ v true hv
      obtain ⟨T0, hd0, hev0⟩ := ih (Function.update ρ v (some false)) (by omega)
      obtain ⟨T1, hd1, hev1⟩ := ih (Function.update ρ v (some true)) (by omega)
      refine ⟨.branch v T0 T1, ?_, fun x => ?_⟩
      · simp only [DecisionTree.depth]; omega
      · simp only [DecisionTree.eval]
        cases hxv : x v with
        | false =>
          simp only [Bool.false_eq_true, if_false]
          rw [hev0]
          simp only [restrictFn]
          rw [extend_update_self ρ v x false hv hxv]
        | true =>
          simp only [if_true]
          rw [hev1]
          simp only [restrictFn]
          rw [extend_update_self ρ v x true hv hxv]
    · have hempty : ρ.freeVars = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hρ0 : ρ.numFree ≤ k := by
        have hz : ρ.numFree = 0 := by
          simp [Restriction.numFree, hempty]
        omega
      obtain ⟨T, hT, hev⟩ := ih ρ hρ0
      exact ⟨T, hT.trans (Nat.le_succ _), hev⟩
end SwitchingLemma2

open Classical

namespace SwitchingLemma2
variable {n : ℕ}
noncomputable def processClauseLits {n : ℕ} :
    List (Literal n × ℕ) → List (Fin n × Bool) → Restriction n → Restriction n →
    List (Fin n × Bool) × Restriction n × Restriction n × List (ℕ × Bool)
  | [], path, ρ₀, σ => (path, ρ₀, σ, [])
  | _, [], ρ₀, σ => ([], ρ₀, σ, [])
  | (l, idx) :: restLits, (_, dir) :: restPath, ρ₀, σ =>
    let r := processClauseLits restLits restPath
      (Function.update ρ₀ l.var (some dir))
      (Function.update σ l.var (some (!l.neg)))
    (r.1, r.2.1, r.2.2.1, (idx, dir) :: r.2.2.2)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
noncomputable def razborovEncode {n : ℕ} (f : DNF n) (w d : ℕ)
    (ρ : Restriction n) : Restriction n × List (ℕ × Bool) :=
  let path := (canonicalDTree f ρ).deepPath.take d
  razborovEncode.go f w (path.length + 1) path ρ ρ []
where
  /-- Main encoding loop: find the first non-killed clause, process ALL of its
      free literals against the path, emit a termination marker, and repeat. -/
  go (f : DNF n) (w : ℕ) :
      ℕ → List (Fin n × Bool) → Restriction n → Restriction n →
      List (ℕ × Bool) → Restriction n × List (ℕ × Bool)
    | _, [], _, σ, acc => (σ, acc)
    | 0, _, _, σ, acc => (σ, acc)
    | fuel + 1, step :: rest, ρ₀, σ, acc =>
      let path := step :: rest
      match f.find? (fun t => decide (¬Term.killedBy t ρ₀)) with
      | none => (σ, acc)
      | some t =>
        let freeLitsIdx := (t.zipIdx).filter (fun ⟨l, _⟩ => decide (l.var ∈ ρ₀.freeVars))
        match freeLitsIdx with
        | [] => (σ, acc)
        | fl :: fls =>
          let r := processClauseLits (fl :: fls) path ρ₀ σ
          go f w fuel r.1 r.2.1 r.2.2.1 (acc ++ r.2.2.2 ++ [(w, false)])
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
noncomputable def razborovDecode {n : ℕ} (f : DNF n) (w : ℕ)
    (γ : Restriction n) (aux : List (ℕ × Bool)) : Restriction n :=
  (razborovDecode.go f w (aux.length + 1) γ γ aux).1
where
  /-- Process aux entries for one clause until termination marker. -/
  processEntries (t : Term n) (w : ℕ) :
      Restriction n → Restriction n → List (ℕ × Bool) →
      Restriction n × Restriction n × List (ℕ × Bool)
    | σ, ρ₀, [] => (σ, ρ₀, [])
    | σ, ρ₀, (idx, dir) :: rest =>
      if idx ≥ w then
        (σ, ρ₀, rest)
      else
        match t.drop idx with
        | [] => (σ, ρ₀, rest)
        | l :: _ =>
          processEntries t w
            (Function.update σ l.var none)
            (Function.update ρ₀ l.var (some dir))
            rest
  /-- Main decoding loop: find the clause, process its aux block, repeat. -/
  go (f : DNF n) (w : ℕ) :
      ℕ → Restriction n → Restriction n → List (ℕ × Bool) →
      Restriction n × Restriction n
    | _, σ, ρ₀, [] => (σ, ρ₀)
    | 0, σ, ρ₀, _ => (σ, ρ₀)
    | fuel + 1, σ, ρ₀, entry :: restAux =>
      let aux := entry :: restAux
      match f.find? (fun t => decide (¬Term.killedBy t ρ₀)) with
      | none => (σ, ρ₀)
      | some t =>
        let (σ', ρ₀', aux') := processEntries t w σ ρ₀ aux
        go f w fuel σ' ρ₀' aux'
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_path_le {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits lits path ρ₀ σ).1.length ≤ path.length := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      exact le_trans (ih _ _ _) (Nat.le_succ _)
end SwitchingLemma2

open Classical

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_bound {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits lits path ρ₀ σ).2.2.2.length +
    2 * (processClauseLits lits path ρ₀ σ).1.length ≤ 2 * path.length := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits, List.length_cons]
      have := ih ps (Function.update ρ₀ hd.1.var (some p.2))
                    (Function.update σ hd.1.var (some (!hd.1.neg)))
      omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_tight {n : ℕ}
    (fl : Literal n × ℕ) (fls : List (Literal n × ℕ))
    (step : Fin n × Bool) (rest : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.2.2.length + 1 +
    2 * (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).1.length ≤
    2 * (step :: rest).length := by
  simp only [processClauseLits, List.length_cons]
  have := processClauseLits_bound fls rest
    (Function.update ρ₀ fl.1.var (some step.2))
    (Function.update σ fl.1.var (some (!fl.1.neg)))
  omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma encode_go_aux_length_bound {n : ℕ} (f : DNF n) (w : ℕ)
    (fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (acc : List (ℕ × Bool)) :
    (razborovEncode.go f w fuel path ρ₀ σ acc).2.length ≤
    acc.length + 2 * path.length := by
  induction fuel generalizing path ρ₀ σ acc with
  | zero =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons _ _ => simp [razborovEncode.go]
  | succ fuel ih =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons step rest =>
      simp only [razborovEncode.go]
      split
      · simp;
      · split
        · simp;
        · next fl fls _ =>
          apply le_trans (ih _ _ _ _)
          simp only [List.length_append, List.length_cons,
                     List.length_nil]
          have := processClauseLits_tight fl fls step rest ρ₀ σ
          have : (step :: rest).length = rest.length + 1 := List.length_cons
          omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma razborovEncode_aux_length_le {n : ℕ} (f : DNF n) (w d : ℕ) (ρ : Restriction n)
    (_hbad : IsBadRestriction f.eval d ρ) :
    (razborovEncode f w d ρ).2.length ≤ 2 * d := by
  show (razborovEncode.go f w _ _ ρ ρ []).2.length ≤ 2 * d
  calc (razborovEncode.go f w _ _ ρ ρ []).2.length
      ≤ 0 + 2 * ((canonicalDTree f ρ).deepPath.take d).length :=
        encode_go_aux_length_bound f w _ _ ρ ρ []
    _ ≤ 2 * d := by
        have := List.length_take_le d (canonicalDTree f ρ).deepPath
        omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_sigma_stable {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n) (hv : ∀ p ∈ lits, p.1.var ≠ v) :
    (processClauseLits lits path ρ₀ σ).2.2.1 v = σ v := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      have hne : hd.1.var ≠ v := hv hd (List.mem_cons_self)
      rw [ih _ _ _ (fun p hp => hv p (List.mem_cons_of_mem _ hp))]
      simp only [Function.update_apply, hne.symm, ite_false]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_rho_stable {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n) (hv : ∀ p ∈ lits, p.1.var ≠ v) :
    (processClauseLits lits path ρ₀ σ).2.1 v = ρ₀ v := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      have hne : hd.1.var ≠ v := hv hd (List.mem_cons_self)
      rw [ih _ _ _ (fun p hp => hv p (List.mem_cons_of_mem _ hp))]
      simp only [Function.update_apply, hne.symm, ite_false]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_rho_ne_none {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n) (hv : ρ₀ v ≠ none) :
    (processClauseLits lits path ρ₀ σ).2.1 v ≠ none := by
  induction lits generalizing path ρ₀ σ with
  | nil => simpa [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simpa [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      apply ih
      simp only [Function.update_apply]
      split
      · simp
      · exact hv
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma encode_go_fst_nonfree {n : ℕ} (f : DNF n) (w : ℕ)
    (fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (acc : List (ℕ × Bool)) (v : Fin n) (hv : ρ₀ v ≠ none) :
    (razborovEncode.go f w fuel path ρ₀ σ acc).1 v = σ v := by
  induction fuel generalizing path ρ₀ σ acc with
  | zero =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons _ _ => simp [razborovEncode.go]
  | succ fuel ih =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons step rest =>
      simp only [razborovEncode.go]
      split
      · rfl
      · next t _ =>
        generalize hfli :
          List.filter (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
            (List.zipIdx t) = fli
        match fli with
        | [] => simp
        | fl :: fls =>
          have hfree : ∀ p ∈ (fl :: fls), ρ₀ p.1.var = none := by
            intro p hp
            have hm : p ∈ List.filter
                (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
                (List.zipIdx t) := hfli ▸ hp
            simp [List.mem_filter, Restriction.freeVars, Finset.mem_filter,
                  Option.isNone_iff_eq_none] at hm
            exact hm.2
          have hne : ∀ p ∈ (fl :: fls), p.1.var ≠ v :=
            fun p hp heq => hv (heq ▸ hfree p hp)
          rw [ih _ _ _ _ (processClauseLits_rho_ne_none _ _ _ _ _ hv)]
          exact processClauseLits_sigma_stable _ _ _ _ _ hne
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma encode_go_acc {n : ℕ} (f : DNF n) (w : ℕ)
    (fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (acc : List (ℕ × Bool)) :
    razborovEncode.go f w fuel path ρ₀ σ acc =
    let r := razborovEncode.go f w fuel path ρ₀ σ []
    (r.1, acc ++ r.2) := by
  induction fuel generalizing path ρ₀ σ acc with
  | zero =>
    cases path <;> simp [razborovEncode.go]
  | succ fuel ih =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons step rest =>
      simp only [razborovEncode.go]
      split
      · simp
      · split
        · simp
        · rw [ih, ih (acc := _ ++ _)]
          simp [List.append_assoc]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma encode_go_fst_acc {n : ℕ} (f : DNF n) (w fuel : ℕ)
    (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n) (acc : List (ℕ × Bool)) :
    (razborovEncode.go f w fuel path ρ₀ σ acc).1 =
    (razborovEncode.go f w fuel path ρ₀ σ []).1 := by
  have := encode_go_acc f w fuel path ρ₀ σ acc; rw [this]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processEntries_preserves_none {n : ℕ}
    (t : Term n) (w : ℕ) (σ ρ₀ : Restriction n) (aux : List (ℕ × Bool))
    (v : Fin n) (hv : σ v = none) :
    (razborovDecode.processEntries t w σ ρ₀ aux).1 v = none := by
  induction aux generalizing σ ρ₀ with
  | nil => simp [razborovDecode.processEntries, hv]
  | cons entry rest ih =>
    simp only [razborovDecode.processEntries]
    split
    · exact hv
    · split
      · exact hv
      · apply ih
        simp only [Function.update_apply]
        split
        · rfl
        · exact hv
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma decode_go_preserves_none {n : ℕ} (f : DNF n) (w : ℕ)
    (fuel : ℕ) (σ ρ₀ : Restriction n) (aux : List (ℕ × Bool))
    (v : Fin n) (hv : σ v = none) :
    (razborovDecode.go f w fuel σ ρ₀ aux).1 v = none := by
  induction fuel generalizing σ ρ₀ aux with
  | zero =>
    cases aux <;> simp [razborovDecode.go, hv]
  | succ fuel ih =>
    cases aux with
    | nil => simp [razborovDecode.go, hv]
    | cons entry restAux =>
      simp only [razborovDecode.go]
      split
      · exact hv
      · next t _ =>
        apply ih
        exact processEntries_preserves_none t w σ ρ₀ _ v hv
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_sigma_indep {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ₁ σ₂ : Restriction n) :
    (processClauseLits lits path ρ₀ σ₁).1 = (processClauseLits lits path ρ₀ σ₂).1 ∧
    (processClauseLits lits path ρ₀ σ₁).2.1 = (processClauseLits lits path ρ₀ σ₂).2.1 ∧
    (processClauseLits lits path ρ₀ σ₁).2.2.2 = (processClauseLits lits path ρ₀ σ₂).2.2.2 := by
  induction lits generalizing path ρ₀ σ₁ σ₂ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      obtain ⟨h1, h2, h3⟩ := ih ps _ _ _
      exact ⟨h1, h2, congrArg _ h3⟩
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma encode_go_snd_sigma_indep {n : ℕ} (f : DNF n) (w fuel : ℕ)
    (path : List (Fin n × Bool)) (ρ₀ σ₁ σ₂ : Restriction n) :
    (razborovEncode.go f w fuel path ρ₀ σ₁ []).2 =
    (razborovEncode.go f w fuel path ρ₀ σ₂ []).2 := by
  induction fuel generalizing path ρ₀ σ₁ σ₂ with
  | zero => cases path <;> simp [razborovEncode.go]
  | succ fuel ih =>
    cases path with
    | nil => simp [razborovEncode.go]
    | cons step rest =>
      simp only [razborovEncode.go]
      split
      · rfl
      · split
        · rfl
        · next fl fls _ =>
          have hindep := processClauseLits_sigma_indep (fl :: fls) (step :: rest) ρ₀ σ₁ σ₂
          obtain ⟨hpath, hrho, haux_eq⟩ := hindep
          have hacc₁ := encode_go_acc f w fuel
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₁).1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₁).2.1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₁).2.2.1
            ((processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₁).2.2.2 ++ [(w, false)])
          have hacc₂ := encode_go_acc f w fuel
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.2.1
            ((processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.2.2 ++ [(w, false)])
          simp only [hacc₁, hacc₂, List.nil_append]
          rw [haux_eq, hpath, hrho]
          exact congrArg _ (ih _ _ _ _)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_aux_entries_from_lits {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (e : ℕ × Bool) (he : e ∈ (processClauseLits lits path ρ₀ σ).2.2.2) :
    ∃ li ∈ lits, e.1 = li.2 := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits] at he
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits] at he
    | cons p ps =>
      simp only [processClauseLits, List.mem_cons] at he
      rcases he with ⟨rfl, rfl⟩ | he
      · exact ⟨hd, .head _, rfl⟩
      · obtain ⟨li, hli, hidx⟩ := ih _ _ _ he
        exact ⟨li, List.mem_cons_of_mem _ hli, hidx⟩
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_aux_ne_nonfree {n : ℕ}
    (t : Term n) (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hne_var : ∀ p ∈ lits, p.1.var ≠ v) :
    ∀ e ∈ (processClauseLits lits path ρ₀ σ).2.2.2,
    ∀ (l : Literal n) (rest : List (Literal n)),
    t.drop e.1 = l :: rest → l.var ≠ v := by
  intro e he l rest hdrop
  obtain ⟨li, hli, hidx⟩ := processClauseLits_aux_entries_from_lits lits path ρ₀ σ e he
  have hli_zip := hmem li hli
  obtain ⟨rest', hdrop'⟩ := zipIdx_drop_spec t li.1 li.2 hli_zip
  rw [hidx] at hdrop; rw [hdrop'] at hdrop
  have : l = li.1 := (List.cons.inj hdrop |>.1).symm
  rw [this]
  exact hne_var li hli
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_aux_vars_free {n : ℕ}
    (t : Term n) (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (e : ℕ × Bool)
    (he : e ∈ (processClauseLits lits path ρ₀ σ).2.2.2)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hfree : ∀ p ∈ lits, ρ₀ p.1.var = none) :
    ∀ (l : Literal n) (rest : List (Literal n)),
      t.drop e.1 = l :: rest → ρ₀ l.var = none := by
  obtain ⟨li, hli, hidx⟩ := processClauseLits_aux_entries_from_lits lits path ρ₀ σ e he
  obtain ⟨rest', hdrop'⟩ := zipIdx_drop_spec t li.1 li.2 (hmem li hli)
  intro l rest hdrop
  rw [hidx] at hdrop; rw [hdrop'] at hdrop
  have : l = li.1 := (List.cons.inj hdrop |>.1).symm
  rw [this]; exact hfree li hli
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma foldl_sigma_stable {n : ℕ} (t : Term n)
    (entries : List (ℕ × Bool)) (σ : Restriction n) (v : Fin n)
    (hne : ∀ e ∈ entries, ∀ (l : Literal n) (rest : List (Literal n)),
      t.drop e.1 = l :: rest → l.var ≠ v) :
    entries.foldl (fun σ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ v
    = σ v := by
  induction entries generalizing σ with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    have hne_e := hne e (List.mem_cons_self)
    have hne_es : ∀ e' ∈ es, _ := fun e' he' => hne e' (List.mem_cons_of_mem _ he')
    match h : t.drop e.1 with
    | [] => exact ih _ hne_es
    | l :: _ =>
      rw [ih _ hne_es]
      simp only [Function.update_apply, (hne_e l _ h).symm, ite_false]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma foldl_rho_stable {n : ℕ} (t : Term n)
    (entries : List (ℕ × Bool)) (ρ₀ : Restriction n) (v : Fin n)
    (hne : ∀ e ∈ entries, ∀ (l : Literal n) (rest : List (Literal n)),
      t.drop e.1 = l :: rest → l.var ≠ v) :
    entries.foldl (fun ρ₀ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀ v
    = ρ₀ v := by
  induction entries generalizing ρ₀ with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    have hne_e := hne e (List.mem_cons_self)
    have hne_es : ∀ e' ∈ es, _ := fun e' he' => hne e' (List.mem_cons_of_mem _ he')
    match h : t.drop e.1 with
    | [] => exact ih _ hne_es
    | l :: _ =>
      rw [ih _ hne_es]
      simp only [Function.update_apply, (hne_e l _ h).symm, ite_false]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma foldl_sigma_preserves_none {n : ℕ} (t : Term n)
    (entries : List (ℕ × Bool)) (σ : Restriction n) (v : Fin n) (hv : σ v = none) :
    entries.foldl (fun σ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ v = none := by
  induction entries generalizing σ with
  | nil => simpa
  | cons e es ih =>
    simp only [List.foldl_cons]
    apply ih
    match h : t.drop e.1 with
    | [] => simp [hv]
    | l :: _ =>
      simp only [Function.update_apply]
      split
      · exact rfl
      · exact hv
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_foldl_sigma_none {n : ℕ} (t : Term n)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ σ_dec : Restriction n) (v : Fin n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hfree : ρ₀ v = none)
    (hset : (processClauseLits lits path ρ₀ σ).2.1 v ≠ none) :
    (processClauseLits lits path ρ₀ σ).2.2.2.foldl (fun σ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ_dec v
    = none := by
  induction lits generalizing path ρ₀ σ σ_dec with
  | nil => simp [processClauseLits] at hset; exact absurd hfree hset
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits] at hset; exact absurd hfree hset
    | cons p ps =>
      simp only [processClauseLits, List.foldl_cons]
      obtain ⟨drop_rest, hdrop⟩ := zipIdx_drop_spec t hd.1 hd.2
        (hmem hd (.head _))
      simp only [hdrop]
      by_cases heq : hd.1.var = v
      · subst heq; exact foldl_sigma_preserves_none t _ _ _
          (by rw [Function.update_apply, if_pos rfl])
      · exact ih ps _ _ (Function.update σ_dec hd.1.var none)
          (fun p hp => hmem p (.tail _ hp))
          (by rwa [Function.update_apply, if_neg (Ne.symm heq)])
          (by simp only [processClauseLits] at hset; exact hset)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_foldl_rho_eq {n : ℕ} (t : Term n)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ ρ₀_dec : Restriction n) (v : Fin n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hinit : ρ₀ v = ρ₀_dec v) :
    (processClauseLits lits path ρ₀ σ).2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec v
    = (processClauseLits lits path ρ₀ σ).2.1 v := by
  induction lits generalizing path ρ₀ σ ρ₀_dec with
  | nil => simp [processClauseLits, hinit]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits, hinit]
    | cons p ps =>
      simp only [processClauseLits, List.foldl_cons]
      obtain ⟨drop_rest, hdrop⟩ := zipIdx_drop_spec t hd.1 hd.2 (hmem hd (.head _))
      simp only [hdrop]
      exact ih ps _ _ _
        (fun q hq => hmem q (.tail _ hq))
        (by simp only [Function.update_apply]; split <;> simp_all)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_foldl_rho_eq_of_set {n : ℕ} (t : Term n)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ ρ₀_dec : Restriction n) (v : Fin n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hfree : ρ₀ v = none)
    (hset : (processClauseLits lits path ρ₀ σ).2.1 v ≠ none) :
    (processClauseLits lits path ρ₀ σ).2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec v
    = (processClauseLits lits path ρ₀ σ).2.1 v := by
  induction lits generalizing path ρ₀ σ ρ₀_dec with
  | nil => simp [processClauseLits] at hset; exact absurd hfree hset
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits] at hset; exact absurd hfree hset
    | cons p ps =>
      simp only [processClauseLits, List.foldl_cons]
      obtain ⟨drop_rest, hdrop⟩ := zipIdx_drop_spec t hd.1 hd.2 (hmem hd (.head _))
      simp only [hdrop]
      by_cases heq : hd.1.var = v
      · exact processClauseLits_foldl_rho_eq t tl ps _ _ _ v
          (fun q hq => hmem q (.tail _ hq))
          (by simp only [Function.update_apply, if_pos heq.symm])
      · exact ih ps _ _ _
          (fun q hq => hmem q (.tail _ hq))
          (by rwa [Function.update_apply, if_neg (Ne.symm heq)])
          (by simp only [processClauseLits] at hset; exact hset)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_no_target_of_rho_none {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hfree : ρ₀ v = none)
    (hnone : (processClauseLits lits path ρ₀ σ).2.1 v = none)
    (hlen : lits.length ≤ path.length) :
    ∀ p ∈ lits, p.1.var ≠ v := by
  induction lits generalizing path ρ₀ σ with
  | nil => intro p hp; simp at hp
  | cons hd tl ih =>
    cases path with
    | nil => simp at hlen
    | cons step rest =>
      simp only [processClauseLits] at hnone
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp_tl
      · intro hpv
        have hne : (Function.update ρ₀ p.1.var (some step.2)) v ≠ none := by
          rw [Function.update_apply, if_pos hpv.symm]; exact Option.some_ne_none _
        exact absurd hnone (processClauseLits_rho_ne_none tl rest _ _ _ hne)
      · by_cases heq : hd.1.var = v
        · have hne : (Function.update ρ₀ hd.1.var (some step.2)) v ≠ none := by
            rw [Function.update_apply, if_pos heq.symm]; exact Option.some_ne_none _
          exact absurd hnone (processClauseLits_rho_ne_none tl rest _ _ _ hne)
        · exact ih rest _ _ (by rwa [Function.update_apply, if_neg (Ne.symm heq)]) hnone
            (by simp [List.length_cons] at hlen ⊢; omega) p hp_tl
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_sigma_at_v {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ₁ σ₂ : Restriction n) (v : Fin n) (hv : σ₁ v = σ₂ v) :
    (processClauseLits lits path ρ₀ σ₁).2.2.1 v =
    (processClauseLits lits path ρ₀ σ₂).2.2.1 v := by
  induction lits generalizing path ρ₀ σ₁ σ₂ with
  | nil => simp [processClauseLits, hv]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits, hv]
    | cons p ps =>
      simp only [processClauseLits]
      apply ih
      simp only [Function.update_apply]
      split_ifs <;> [rfl; exact hv]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_sigma_none_of_rho_none {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hfree : ρ₀ v = none)
    (h : (processClauseLits lits path ρ₀ σ).2.1 v = none) :
    (processClauseLits lits path ρ₀ σ).2.2.1 v = σ v := by
  induction' lits with hd tl ih generalizing path ρ₀ σ;
  · cases path <;> aesop;
  · rcases path with ( _ | ⟨ x, path ⟩ ) <;> simp +decide [ processClauseLits ] at h ⊢;
    by_cases hvar : hd.1.var = v;
    · exact absurd h ( by exact SwitchingLemma2.processClauseLits_rho_ne_none _ _ _ _ _ ( by aesop ) );
    · convert ih path ( Function.update ρ₀ hd.1.var ( some x.2 ) ) ( Function.update σ hd.1.var ( some !hd.1.neg ) ) _ h using 1;
      · rw [ Function.update_apply ] ; aesop;
      · rw [ Function.update_apply ] ; aesop
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma encode_go_fst_sigma_indep_at_free {n : ℕ} (f : DNF n) (w fuel : ℕ)
    (path : List (Fin n × Bool)) (ρ₀ σ₁ σ₂ : Restriction n) (v : Fin n)
    (hfree : ρ₀ v = none) (h₁ : σ₁ v = none) (h₂ : σ₂ v = none) :
    (razborovEncode.go f w fuel path ρ₀ σ₁ []).1 v =
    (razborovEncode.go f w fuel path ρ₀ σ₂ []).1 v := by
  induction fuel generalizing path ρ₀ σ₁ σ₂ with
  | zero => cases path <;> simp [razborovEncode.go, h₁, h₂]
  | succ fuel ih =>
    cases path with
    | nil => simp [razborovEncode.go, h₁, h₂]
    | cons step rest =>
      simp only [razborovEncode.go]
      split
      · simp [h₁, h₂]
      · split
        · simp [h₁, h₂]
        · next fl fls _ =>
          obtain ⟨hpath, hrho, _⟩ :=
            processClauseLits_sigma_indep (fl :: fls) (step :: rest) ρ₀ σ₁ σ₂
          conv_lhs => rw [encode_go_fst_acc]
          conv_rhs => rw [encode_go_fst_acc]
          rw [hpath, hrho]
          by_cases hv : (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.1 v = none
          · have hσ₁_eq : (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₁).2.2.1 v = none :=
              (processClauseLits_sigma_none_of_rho_none _ _ _ _ _ hfree
                (hrho ▸ hv)) ▸ h₁ ▸ rfl
            have hσ₂_eq : (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.2.1 v = none :=
              (processClauseLits_sigma_none_of_rho_none _ _ _ _ _ hfree hv) ▸ h₂ ▸ rfl
            exact ih _ _ _ _ hv hσ₁_eq hσ₂_eq
          · rw [encode_go_fst_nonfree f w fuel _ _ _ [] v hv,
                encode_go_fst_nonfree f w fuel _ _ _ [] v hv]
            exact processClauseLits_sigma_at_v _ _ _ _ _ v (by rw [h₁, h₂])
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processEntries_of_processClauseLits {n : ℕ}
    (t : Term n) (w : ℕ) (hw : t.length ≤ w)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀_enc σ_enc σ_dec ρ₀_dec : Restriction n)
    (rest : List (ℕ × Bool))
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx) :
    let pcl := processClauseLits lits path ρ₀_enc σ_enc
    razborovDecode.processEntries t w σ_dec ρ₀_dec (pcl.2.2.2 ++ [(w, false)] ++ rest) =
    ( pcl.2.2.2.foldl (fun σ (e : ℕ × Bool) =>
        match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ_dec,
      pcl.2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
        match t.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec,
      rest ) := by
  induction lits generalizing path ρ₀_enc σ_enc σ_dec ρ₀_dec with
  | nil =>
    simp only [processClauseLits, List.nil_append, List.foldl_nil]
    simp [razborovDecode.processEntries]
  | cons hd tl ih =>
    cases path with
    | nil =>
      simp only [processClauseLits, List.nil_append, List.foldl_nil]
      simp [razborovDecode.processEntries]
    | cons p ps =>
      simp only [processClauseLits]
      have hmem_hd : hd ∈ t.zipIdx :=
        hmem hd (.head _)
      have hidx_lt : hd.2 < w := by
        obtain ⟨_, hidx, _⟩ := List.mem_zipIdx hmem_hd
        simp at hidx; omega
      obtain ⟨drop_rest, hdrop⟩ := zipIdx_drop_spec t hd.1 hd.2 hmem_hd
      simp only [List.cons_append, razborovDecode.processEntries,
                 show ¬(hd.2 ≥ w) from by omega, ↓reduceIte, hdrop]
      -- Unfold one step of the foldl on the RHS
      simp only [List.foldl_cons, hdrop]
      exact ih ps _ _ _ _ (fun q hq => hmem q (.tail _ hq))
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_sigma_ne_neg {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (l : Literal n)
    (hnd : ∀ m ∈ lits, m.1.var = l.var → m.1 = l)
    (hσ : σ l.var ≠ some l.neg) :
    (processClauseLits lits path ρ₀ σ).2.2.1 l.var ≠ some l.neg := by
  induction lits generalizing path ρ₀ σ with
  | nil => simpa [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simpa [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits]
      apply ih ps _ _ (fun m hm => hnd m (List.mem_cons_of_mem _ hm))
      by_cases heq : hd.1.var = l.var
      · have hd_eq : hd.1 = l := hnd hd List.mem_cons_self heq
        rw [Function.update_apply, if_pos heq.symm, hd_eq]
        intro h
        injection h with h'
        cases hb : l.neg <;> (rw [hb] at h'; simp at h')
      · rw [Function.update_apply, if_neg (Ne.symm heq)]
        exact hσ
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_path_nil_of_rho_none_and_mem {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (l : Literal n) (idx : ℕ)
    (hl : (l, idx) ∈ lits)
    (hnd : ∀ m ∈ lits, m.1.var = l.var → m.1 = l)
    (hfree : ρ₀ l.var = none)
    (h : (processClauseLits lits path ρ₀ σ).2.1 l.var = none) :
    (processClauseLits lits path ρ₀ σ).1 = [] := by
  induction lits generalizing path ρ₀ σ with
  | nil => exact absurd hl (List.not_mem_nil)
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits] at h ⊢
      -- Reduce: in either case of membership, apply IH with updated ρ₀
      rcases List.mem_cons.mp hl with hl_eq | hl_tl
      · -- hl : (l, idx) = hd, so hd.1 = l and hd.1.var = l.var
        -- After update, ρ₀ at l.var = some p.2 ≠ none, so PCL rho at l.var ≠ none
        have hd_var : hd.1.var = l.var := by rw [← hl_eq]
        exfalso
        apply processClauseLits_rho_ne_none tl ps _ _ l.var _ h
        rw [Function.update_apply, if_pos hd_var.symm]
        exact Option.some_ne_none _
      · -- hl : (l, idx) ∈ tl. Apply IH.
        by_cases heq : hd.1.var = l.var
        · -- hd.1.var = l.var, so after update ρ₀ l.var = some p.2 ≠ none. Contradicts h.
          exfalso
          apply processClauseLits_rho_ne_none tl ps _ _ l.var _ h
          rw [Function.update_apply, if_pos heq.symm]
          exact Option.some_ne_none _
        · exact ih ps _ _ hl_tl
            (fun m hm => hnd m (List.mem_cons_of_mem _ hm))
            (by rw [Function.update_apply, if_neg (Ne.symm heq)]; exact hfree)
            h
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
set_option maxHeartbeats 800000 in
lemma encode_go_not_kills_first_clause {n : ℕ} (f : DNF n) (w : ℕ)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (enc_fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (t : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) = some t)
    (l : Literal n) (hl : l ∈ t) (hfree : ρ₀ l.var = none) :
    (razborovEncode.go f w enc_fuel path ρ₀ σ []).1 l.var ≠ some l.neg := by
  induction' enc_fuel with enc_fuel ih generalizing path ρ₀ σ <;> simp_all +decide ;
  · cases path <;> simp_all +decide [ SwitchingLemma2.razborovEncode.go ];
  · rcases path with ( _ | ⟨ step, rest ⟩ );
    · rw [ razborovEncode.go ] ; aesop;
    · obtain ⟨fl, fls, hfl⟩ : ∃ fl fls, (t.zipIdx).filter (fun ⟨l, _⟩ => decide (l.var ∈ ρ₀.freeVars)) = fl :: fls := by
        obtain ⟨k, hk⟩ : ∃ k, l = t.get k ∧ k.val < t.length := by
          have := List.mem_iff_get.mp hl; aesop;
        have h_mem : (l, k.val) ∈ (t.zipIdx).filter (fun ⟨l, _⟩ => decide (l.var ∈ ρ₀.freeVars)) := by
          simp +decide [ hk, Restriction.freeVars ];
          grind;
        exact List.exists_cons_of_ne_nil ( by rintro h; simp +decide [ h ] at h_mem );
      -- By definition of `processClauseLits`, we know that `pcl.2.1 l.var = none` or `pcl.2.1 l.var ≠ none`.
      by_cases hpcl : (SwitchingLemma2.processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.1 l.var = none;
      · have hpcl_path : (SwitchingLemma2.processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).1 = [] := by
          apply SwitchingLemma2.processClauseLits_path_nil_of_rho_none_and_mem;
          rotate_left;
          rotate_left;
          exact hfree;
          exact hpcl;
          exact ( List.idxOf l t );
          · replace hfl := congr_arg List.toFinset hfl; rw [ Finset.ext_iff ] at hfl; specialize hfl ( l, List.idxOf l t ) ; simp_all +decide [ List.mem_iff_get ] ;
            contrapose! hfl; simp_all +decide [ Fin.exists_iff ] ;
            refine Or.inl ⟨ ⟨ ?_, ?_ ⟩, ?_, ?_ ⟩;
            · grind;
            · unfold Restriction.freeVars; aesop;
            · exact fun h => hfl ⟨ 0, Nat.zero_lt_succ _ ⟩ ( by aesop );
            · exact fun i => fun hi => hfl ⟨ i + 1, by linarith [ Fin.is_lt i ] ⟩ ( by simpa [ Fin.add_def, Nat.mod_eq_of_lt ] using hi );
          · grind +splitImp;
        rw [ SwitchingLemma2.razborovEncode.go ];
        rw [ show List.find? ( fun t => decide ¬Term.killedBy t ρ₀ ) f = some t from by simpa using hfind ];
        simp +decide [ hpcl_path, hfl ];
        rw [ SwitchingLemma2.razborovEncode.go ];
        simp only []
        have hnd_lits : ∀ m ∈ (fl :: fls), m.1.var = l.var → m.1 = l := by
          intro m hm hmv
          have hm' := hfl ▸ hm
          have hmz := (List.mem_filter.mp hm').1
          obtain ⟨_, hi, heq⟩ := List.mem_zipIdx hmz
          simp at hi heq
          have hmt : m.1 ∈ t := heq ▸ List.getElem_mem (by omega)
          exact hnd t (List.mem_of_find?_eq_some hfind) m.1 hmt l hl hmv
        exact processClauseLits_sigma_ne_neg _ _ _ _ _ hnd_lits (by rw [hE _ hfree]; simp)
      · have hnd_lits : ∀ m ∈ (fl :: fls), m.1.var = l.var → m.1 = l := by
          intro m hm hmv
          have hm' := hfl ▸ hm
          have hmz := (List.mem_filter.mp hm').1
          obtain ⟨_, hi, heq⟩ := List.mem_zipIdx hmz
          simp at hi heq
          have hmt : m.1 ∈ t := heq ▸ List.getElem_mem (by omega)
          exact hnd t (List.mem_of_find?_eq_some hfind) m.1 hmt l hl hmv
        have hkey : (razborovEncode.go f w enc_fuel
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.1
            (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.2.1
            ((processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.2.2 ++ [(w, false)])).1 l.var
            = (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ).2.2.1 l.var := by
          rw [encode_go_fst_acc]
          exact encode_go_fst_nonfree f w enc_fuel _ _ _ [] l.var (by push_neg at hpcl; exact hpcl)
        rw [ SwitchingLemma2.razborovEncode.go ];
        rw [ show List.find? ( fun t => decide ¬Term.killedBy t ρ₀ ) f = some t from by simpa using hfind ] ; simp +decide [ hfl ] ;
        rw [hkey]
        exact processClauseLits_sigma_ne_neg _ _ _ _ _ hnd_lits (by rw [hE _ hfree]; simp)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_rho_ne_none_of_mem {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (p : Literal n × ℕ) (hp : p ∈ lits) (hpv : p.1.var = v)
    (hlen : lits.length ≤ path.length) :
    (processClauseLits lits path ρ₀ σ).2.1 v ≠ none := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp at hp
  | cons hd tl ih =>
    cases path with
    | nil => simp at hlen
    | cons step rest =>
      simp only [processClauseLits]
      rcases List.mem_cons.mp hp with rfl | hp_tl
      · -- p = hd, so hd.1.var = v, Function.update sets ρ₀ at v to some
        apply processClauseLits_rho_ne_none
        rw [Function.update_apply, if_pos hpv.symm]
        exact Option.some_ne_none _
      · exact ih rest _ _ hp_tl (by simp [List.length_cons] at hlen ⊢; omega)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma roundtrip_base {n : ℕ} (f : DNF n) (w : ℕ)
    (ρ₀ σ σ_dec ρ₀_dec : Restriction n) (dec_fuel : ℕ)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (hA : ∀ v, ρ₀ v = none → σ_dec v = σ v)
    (hC : ∀ v, ρ₀ v ≠ none → σ_dec v = σ v) :
    (razborovDecode.go f w dec_fuel σ_dec ρ₀_dec []).1 = σ := by
  cases dec_fuel with
  | zero => simp [razborovDecode.go]; funext v; by_cases h : ρ₀ v = none <;> simp_all
  | succ _ => simp [razborovDecode.go]; funext v; by_cases h : ρ₀ v = none <;> simp_all
end SwitchingLemma2

open Classical

namespace SwitchingLemma2
variable {n : ℕ}
lemma pcl_none_implies_rho_free {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hv' : (processClauseLits lits path ρ₀ σ).2.1 v = none) :
    ρ₀ v = none := by
  by_contra h; push_neg at h
  exact absurd hv' (processClauseLits_rho_ne_none lits path ρ₀ σ v h)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma find_clause_preserved_in_encode {n : ℕ}
    (f : DNF n) (w : ℕ)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (enc_fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ ρ₀_dec : Restriction n)
    (t_clause : Term n)
    (hfind_enc : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) = some t_clause)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (hB : ∀ v, ρ₀ v = none →
      ρ₀_dec v = (razborovEncode.go f w enc_fuel path ρ₀ σ []).1 v)
    (hD : ∀ v, ρ₀ v ≠ none → ρ₀_dec v = ρ₀ v) :
    f.find? (fun t => decide (¬Term.killedBy t ρ₀_dec)) = some t_clause := by
  apply first_clause_preserved f ρ₀ ρ₀_dec t_clause hfind_enc hD
  intro ⟨l, hl_mem, hl_killed⟩
  simp only [Literal.killedBy] at hl_killed
  by_cases hfv : ρ₀ l.var = none
  · rw [hB l.var hfv] at hl_killed
    exact encode_go_not_kills_first_clause f w hnd enc_fuel
      path ρ₀ σ hE t_clause hfind_enc l hl_mem hfv hl_killed
  · rw [hD l.var hfv] at hl_killed
    have hkill : Term.killedBy t_clause ρ₀ := ⟨l, hl_mem, hl_killed⟩
    have hnkill := List.find?_some hfind_enc
    simp at hnkill
    exact absurd hkill hnkill
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma mem_filter_freeVars_zipIdx {n : ℕ} (ρ₀ : Restriction n)
    (t_clause : List (Literal n)) (p : Literal n × ℕ)
    (hp : p ∈ List.filter
      (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
      (List.zipIdx t_clause)) :
    p ∈ t_clause.zipIdx ∧ ρ₀ p.1.var = none := by
  refine ⟨(List.mem_filter.mp hp).1, ?_⟩
  have hfree := (List.mem_filter.mp hp).2
  simp [Restriction.freeVars, Finset.mem_filter, Option.isNone_iff_eq_none] at hfree
  exact hfree
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma processClauseLits_aux_ne_of_pcl_none {n : ℕ}
    (t : Term n) (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hnone : (processClauseLits lits path ρ₀ σ).2.1 v = none) :
    ∀ e ∈ (processClauseLits lits path ρ₀ σ).2.2.2,
    ∀ (l : Literal n) (rest : List (Literal n)),
    t.drop e.1 = l :: rest → l.var ≠ v := by
  revert hnone;
  induction' lits with lits ih generalizing path ρ₀ σ;
  · intro _ e he _ _ _; simp [processClauseLits] at he
  · rcases path with ( _ | ⟨ step, path ⟩ ) <;> simp_all +decide [ processClauseLits ];
    intro hnone
    apply And.intro;
    · intro l rest hdrop hvar
      have hvar_eq : lits.1.var = v := by
        have hzip : (lits.1, lits.2) ∈ List.zipIdx t := hmem.left
        have hzip : ∃ rest, t.drop lits.2 = lits.1 :: rest := by
          exact zipIdx_drop_spec t lits.1 lits.2 hzip;
        grind +splitImp;
      exact absurd hnone ( by erw [ hvar_eq ] ; exact fun h => by have := processClauseLits_rho_ne_none ih path ( Function.update ρ₀ v ( some step.2 ) ) ( Function.update σ v ( some !lits.1.neg ) ) v; aesop )
    · grind +splitIndPred
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma encode_go_fst_eq_rec {n : ℕ} (f : DNF n) (w fuel : ℕ)
    (step : Fin n × Bool) (rest : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (t_clause : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) = some t_clause)
    (fl : Literal n × ℕ) (fls : List (Literal n × ℕ))
    (hfli_eq : List.filter (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
      (List.zipIdx t_clause) = fl :: fls) :
    let pcl := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ
    (razborovEncode.go f w (fuel + 1) (step :: rest) ρ₀ σ []).1 =
    (razborovEncode.go f w fuel pcl.1 pcl.2.1 pcl.2.2.1 []).1 := by
  cases' h : List.find? ( fun t => !Term.killedBy t ρ₀ ) f with t <;> simp_all +decide [ SwitchingLemma2.razborovEncode.go ];
  rw [ SwitchingLemma2.encode_go_fst_acc ]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma roundtrip_inv_hC' {n : ℕ}
    (t_clause : Term n)
    (lits : List (Literal n × ℕ))
    (path : List (Fin n × Bool))
    (ρ₀ σ σ_dec : Restriction n)
    (hfree_lits : ∀ p ∈ lits, ρ₀ p.1.var = none)
    (hmem_zip : ∀ p ∈ lits, p ∈ t_clause.zipIdx)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (hC : ∀ v, ρ₀ v ≠ none → σ_dec v = σ v)
    (v : Fin n)
    (hv : (processClauseLits lits path ρ₀ σ).2.1 v ≠ none) :
    (processClauseLits lits path ρ₀ σ).2.2.2.foldl
      (fun σ' (e : ℕ × Bool) =>
        match t_clause.drop e.1 with | [] => σ' | l :: _ => Function.update σ' l.var none)
      σ_dec v = σ v := by
  by_cases hv' : ρ₀ v = none <;> simp_all +decide ;
  · exact?;
  · convert foldl_sigma_stable t_clause ( processClauseLits lits path ρ₀ σ |> Prod.snd |> Prod.snd |> Prod.snd ) σ_dec v _ using 1;
    · rw [ hC v hv' ];
    · apply_rules [ SwitchingLemma2.processClauseLits_aux_ne_nonfree ];
      · exact fun p hp => hmem_zip _ _ hp;
      · grind +ring
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma roundtrip_inv_hD' {n : ℕ}
    (t_clause : Term n)
    (lits : List (Literal n × ℕ))
    (path : List (Fin n × Bool))
    (ρ₀ σ ρ₀_dec : Restriction n)
    (hfree_lits : ∀ p ∈ lits, ρ₀ p.1.var = none)
    (hmem_zip : ∀ p ∈ lits, p ∈ t_clause.zipIdx)
    (hD : ∀ v, ρ₀ v ≠ none → ρ₀_dec v = ρ₀ v)
    (v : Fin n)
    (hv : (processClauseLits lits path ρ₀ σ).2.1 v ≠ none) :
    (processClauseLits lits path ρ₀ σ).2.2.2.foldl
      (fun ρ₀' (e : ℕ × Bool) =>
        match t_clause.drop e.1 with | [] => ρ₀' | l :: _ => Function.update ρ₀' l.var (some e.2))
      ρ₀_dec v = (processClauseLits lits path ρ₀ σ).2.1 v := by
  by_cases hfree : ρ₀ v = none;
  · convert SwitchingLemma2.processClauseLits_foldl_rho_eq_of_set t_clause lits path ρ₀ σ ρ₀_dec v hmem_zip hfree hv using 1;
  · have hnone : ∀ p ∈ lits, p.1.var ≠ v := by
      grind +ring;
    convert foldl_rho_stable t_clause ( processClauseLits lits path ρ₀ σ |>.2.2.2 ) ρ₀_dec v _ using 1;
    · rw [ hD v hfree, processClauseLits_rho_stable lits path ρ₀ σ v hnone ];
    · exact?
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma go_roundtrip_gen {n : ℕ} (f : DNF n) (w : ℕ) (hw : f.width ≤ w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (enc_fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (σ_dec ρ₀_dec : Restriction n) (dec_fuel : ℕ)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (hA : ∀ v, ρ₀ v = none → σ_dec v = (razborovEncode.go f w enc_fuel path ρ₀ σ []).1 v)
    (hB : ∀ v, ρ₀ v = none → ρ₀_dec v = (razborovEncode.go f w enc_fuel path ρ₀ σ []).1 v)
    (hC : ∀ v, ρ₀ v ≠ none → σ_dec v = σ v)
    (hD : ∀ v, ρ₀ v ≠ none → ρ₀_dec v = ρ₀ v)
    (hfuel : dec_fuel ≥ (razborovEncode.go f w enc_fuel path ρ₀ σ []).2.length + 1) :
    (razborovDecode.go f w dec_fuel σ_dec ρ₀_dec
      (razborovEncode.go f w enc_fuel path ρ₀ σ []).2).1 = σ := by
  set enc := razborovEncode.go f w enc_fuel path ρ₀ σ [] with henc_def
  have base : enc = (σ, []) →
      (razborovDecode.go f w dec_fuel σ_dec ρ₀_dec enc.2).1 = σ := by
    intro heq
    rw [show enc.2 = [] from by rw [heq]]
    exact roundtrip_base f w ρ₀ σ σ_dec ρ₀_dec dec_fuel hE
      (fun v hv => by rw [hA v hv, show enc.1 v = σ v from by rw [heq]]) hC
  induction enc_fuel generalizing path ρ₀ σ σ_dec ρ₀_dec dec_fuel with
  | zero =>
    cases path <;> (simp only [razborovEncode.go] at henc_def; exact base henc_def)
  | succ fuel ih =>
    cases path with
    | nil => simp only [razborovEncode.go] at henc_def; exact base henc_def
    | cons step rest =>
      simp only [razborovEncode.go] at henc_def
      revert henc_def; split
      · intro henc_def; exact base henc_def
      · rename_i t_clause hfind_enc
        intro henc_def
        generalize hfli_eq :
          List.filter (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
            (List.zipIdx t_clause) = fli
        revert henc_def; rw [hfli_eq]; intro henc_def
        match fli with
        | [] => exact base henc_def
        | fl :: fls =>
          simp only [List.nil_append] at henc_def
          set pcl := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ with hpcl_def
          set rec_enc := razborovEncode.go f w fuel pcl.1 pcl.2.1 pcl.2.2.1 [] with hrec_def
          have henc_acc := encode_go_acc f w fuel pcl.1 pcl.2.1 pcl.2.2.1
            (pcl.2.2.2 ++ [(w, false)])
          have henc_eq : enc = (rec_enc.1, (pcl.2.2.2 ++ [(w, false)]) ++ rec_enc.2) :=
            henc_def.trans henc_acc
          have haux : enc.2 = pcl.2.2.2 ++ [(w, false)] ++ rec_enc.2 := by
            have := congrArg Prod.snd henc_eq; simpa [List.append_assoc] using this
          have hfli_spec : ∀ p ∈ (fl :: fls),
              p ∈ t_clause.zipIdx ∧ ρ₀ p.1.var = none := by
            intro p hp; rw [← hfli_eq] at hp
            exact mem_filter_freeVars_zipIdx ρ₀ t_clause p hp
          have hmem_zip : ∀ p ∈ (fl :: fls), p ∈ t_clause.zipIdx :=
            fun p hp => (hfli_spec p hp).1
          have hfree_lits : ∀ p ∈ (fl :: fls), ρ₀ p.1.var = none :=
            fun p hp => (hfli_spec p hp).2
          have htw : t_clause.length ≤ w :=
            le_trans (term_length_le_width f t_clause (List.mem_of_find?_eq_some hfind_enc)) hw
          have hfind_dec : f.find? (fun t => decide (¬Term.killedBy t ρ₀_dec)) =
              some t_clause :=
            find_clause_preserved_in_encode f w hnd (fuel + 1) (step :: rest)
              ρ₀ σ ρ₀_dec t_clause hfind_enc hE hB hD
          have hpe := processEntries_of_processClauseLits t_clause w htw
            (fl :: fls) (step :: rest) ρ₀ σ σ_dec ρ₀_dec rec_enc.2 hmem_zip
          rw [haux]
          have hpcl_aux_ne : pcl.2.2.2 ≠ [] := by
            simp only [hpcl_def, processClauseLits]; exact List.cons_ne_nil _ _
          obtain ⟨hd_aux, tl_aux, hpcl_cons⟩ := List.exists_cons_of_ne_nil hpcl_aux_ne
          obtain ⟨df, rfl⟩ : ∃ k, dec_fuel = k + 1 := ⟨dec_fuel - 1, by omega⟩
          rw [hpcl_cons]
          simp only [List.cons_append, razborovDecode.go, hfind_dec]
          have hreassoc : hd_aux :: (tl_aux ++ [(w, false)] ++ rec_enc.2) =
              pcl.2.2.2 ++ [(w, false)] ++ rec_enc.2 := by
            simp only [hpcl_cons, List.cons_append, List.append_assoc]
          rw [hreassoc, hpe]
          -- Define the foldl'd restrictions (without set, to avoid opacity issues)
          have hsigma_indep : rec_enc.2 =
              (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).2 :=
            encode_go_snd_sigma_indep f w fuel pcl.1 pcl.2.1 pcl.2.2.1 σ
          rw [hsigma_indep]
          -- Key: enc.1 = rec_enc.1
          have henc1_eq : enc.1 = rec_enc.1 := by
            have := congrArg Prod.fst henc_eq; simp at this; exact this
          -- Helper: σ_indep for rec_enc
          have hrec_sigma_indep : ∀ v, pcl.2.1 v = none →
              rec_enc.1 v = (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).1 v := by
            intro v hv
            exact encode_go_fst_sigma_indep_at_free f w fuel pcl.1 pcl.2.1
              pcl.2.2.1 σ v hv
              (by rw [processClauseLits_sigma_none_of_rho_none _ _ _ _ v
                       (pcl_none_implies_rho_free _ _ ρ₀ σ v hv) hv,
                       hE v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv)])
              (hE v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv))
          -- Now apply ih
          -- The goal has tuple projections that need simplification
          -- Goal: (go f w df (foldl_σ, foldl_ρ, enc'.2).1 (foldl_σ, foldl_ρ, enc'.2).2.1 enc'.2).1 = σ
          -- which is: (go f w df foldl_σ foldl_ρ enc'.2).1 = σ
          apply ih pcl.1 pcl.2.1 σ
            (pcl.2.2.2.foldl (fun σ (e : ℕ × Bool) =>
              match t_clause.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ_dec)
            (pcl.2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
              match t_clause.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec)
            df
          -- (1) hE': pcl.2.1 v = none → σ v = none
          · exact fun v hv => hE v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv)
          -- (2) hC': pcl.2.1 v ≠ none → σ_fold v = σ v
          · exact fun v hv => roundtrip_inv_hC' t_clause _ _ ρ₀ σ σ_dec hfree_lits hmem_zip hE hC v hv
          -- (3) hD': pcl.2.1 v ≠ none → ρ₀_fold v = pcl.2.1 v
          · exact fun v hv => roundtrip_inv_hD' t_clause _ _ ρ₀ σ ρ₀_dec hfree_lits hmem_zip hD v hv
          -- (4) hA': pcl.2.1 v = none → σ_fold v = (go f w fuel pcl.1 pcl.2.1 σ []).1 v
          · intro v hv
            have h1 : pcl.2.2.2.foldl (fun σ (e : ℕ × Bool) =>
              match t_clause.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ_dec v
              = σ_dec v :=
              foldl_sigma_stable t_clause _ _ _
                (processClauseLits_aux_ne_of_pcl_none t_clause _ _ _ _ v hmem_zip hv)
            rw [h1, hA v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv), henc1_eq]
            exact hrec_sigma_indep v hv
          -- (5) hB': pcl.2.1 v = none → ρ₀_fold v = (go f w fuel pcl.1 pcl.2.1 σ []).1 v
          · intro v hv
            have h1 : pcl.2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
              match t_clause.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec v
              = ρ₀_dec v :=
              foldl_rho_stable t_clause _ _ _
                (processClauseLits_aux_ne_of_pcl_none t_clause _ _ _ _ v hmem_zip hv)
            rw [h1, hB v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv), henc1_eq]
            exact hrec_sigma_indep v hv
          -- (6) fuel bound
          · rw [← hsigma_indep]
            have : enc.2.length = pcl.2.2.2.length + 1 + rec_enc.2.length := by
              simp only [haux, List.length_append, List.length_cons, List.length_nil]
            have : pcl.2.2.2.length ≥ 1 := by rw [hpcl_cons]; simp
            omega
          -- (7) rfl
          · rfl
          -- (8) base case
          · intro heq
            have h_enc2_nil : (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).2 = [] :=
              congrArg Prod.snd heq
            rw [h_enc2_nil]
            apply roundtrip_base f w pcl.2.1 σ _ _ df
            · exact fun v hv => hE v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv)
            · intro v hv
              have h1 := foldl_sigma_stable t_clause pcl.2.2.2 σ_dec v
                (processClauseLits_aux_ne_of_pcl_none t_clause _ _ _ _ v hmem_zip hv)
              have h2 := hA v (pcl_none_implies_rho_free _ _ ρ₀ σ v hv)
              have h5 : (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).1 v = σ v :=
                congrFun (congrArg Prod.fst heq) v
              calc _ = σ_dec v := h1
                _ = enc.1 v := h2
                _ = rec_enc.1 v := congrFun henc1_eq v
                _ = (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).1 v := hrec_sigma_indep v hv
                _ = σ v := h5
            · exact fun v hv => roundtrip_inv_hC' t_clause _ _ ρ₀ σ σ_dec hfree_lits hmem_zip hE hC v hv
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma go_roundtrip {n : ℕ} (f : DNF n) (w : ℕ) (hw : f.width ≤ w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (enc_fuel : ℕ) (path : List (Fin n × Bool)) (ρ : Restriction n) :
    let enc := razborovEncode.go f w enc_fuel path ρ ρ []
    (razborovDecode.go f w (enc.2.length + 1) enc.1 enc.1 enc.2).1 = ρ := by
  exact go_roundtrip_gen f w hw hnd enc_fuel path ρ ρ
    (razborovEncode.go f w enc_fuel path ρ ρ []).1
    (razborovEncode.go f w enc_fuel path ρ ρ []).1
    ((razborovEncode.go f w enc_fuel path ρ ρ []).2.length + 1)
    (fun v hv => hv)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun v hv => encode_go_fst_nonfree f w enc_fuel path ρ ρ [] v hv)
    (fun v hv => encode_go_fst_nonfree f w enc_fuel path ρ ρ [] v hv)
    (le_refl _)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma razborovDecode_encode {n : ℕ} (f : DNF n) (w d : ℕ) (ρ : Restriction n)
    (_hbad : IsBadRestriction f.eval d ρ) (hw : f.width ≤ w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) :
    razborovDecode f w (razborovEncode f w d ρ).1 (razborovEncode f w d ρ).2 = ρ := by
  unfold razborovDecode razborovEncode
  exact go_roundtrip f w hw hnd _ _ ρ
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
theorem razborovEncode_injective {n : ℕ} (f : DNF n) (w d : ℕ)
    (ρ₁ ρ₂ : Restriction n)
    (hbad₁ : IsBadRestriction f.eval d ρ₁) (hbad₂ : IsBadRestriction f.eval d ρ₂)
    (hw : f.width ≤ w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (henc : razborovEncode f w d ρ₁ = razborovEncode f w d ρ₂) :
    ρ₁ = ρ₂ := by
  rw [← razborovDecode_encode f w d ρ₁ hbad₁ hw hnd,
      ← razborovDecode_encode f w d ρ₂ hbad₂ hw hnd, henc]
end SwitchingLemma2

open Classical

namespace SwitchingLemma2
variable {n : ℕ}
private def parseAux (w : ℕ) (hw_pos : 0 < w) :
    List (ℕ × Bool) → List (Fin w × Bool × Bool)
  | [] => []
  | (idx, dir) :: rest =>
    if h : idx < w then
      match rest with
      | [] => [(⟨idx, h⟩, dir, false)]
      | (idx', dir') :: rest' =>
        if idx' ≥ w then
          (⟨idx, h⟩, dir, true) :: parseAux w hw_pos rest'
        else
          (⟨idx, h⟩, dir, false) :: parseAux w hw_pos ((idx', dir') :: rest')
    else
      parseAux w hw_pos rest
termination_by l => l.length
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private def triplesToAux (w : ℕ) :
    List (Fin w × Bool × Bool) → List (ℕ × Bool)
  | [] => []
  | (pos, dir, true) :: rest =>
    (pos.val, dir) :: (w, false) :: triplesToAux w rest
  | (pos, dir, false) :: rest =>
    (pos.val, dir) :: triplesToAux w rest
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma parseAux_cons_marker (w : ℕ) (hw_pos : 0 < w)
    (idx : ℕ) (h : idx < w) (dir : Bool) (rest : List (ℕ × Bool)) :
    parseAux w hw_pos ((idx, dir) :: (w, false) :: rest) =
      (⟨idx, h⟩, dir, true) :: parseAux w hw_pos rest := by
  rw [parseAux]
  simp only [h, ↓reduceDIte, ge_iff_le, le_refl, ↓reduceIte]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma parseAux_cons_nonmarker (w : ℕ) (hw_pos : 0 < w)
    (idx : ℕ) (h : idx < w) (dir : Bool)
    (idx' : ℕ) (h' : idx' < w) (dir' : Bool) (rest : List (ℕ × Bool)) :
    parseAux w hw_pos ((idx, dir) :: (idx', dir') :: rest) =
      (⟨idx, h⟩, dir, false) :: parseAux w hw_pos ((idx', dir') :: rest) := by
  rw [parseAux]
  have hnge : ¬ idx' ≥ w := not_le.mpr h'
  simp only [h, ↓reduceDIte, ge_iff_le, hnge, ↓reduceIte]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma parseAux_singleton (w : ℕ) (hw_pos : 0 < w)
    (idx : ℕ) (h : idx < w) (dir : Bool) :
    parseAux w hw_pos [(idx, dir)] = [(⟨idx, h⟩, dir, false)] := by
  rw [parseAux]
  simp only [h, ↓reduceDIte]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma parseAux_nil (w : ℕ) (hw_pos : 0 < w) :
    parseAux w hw_pos [] = [] := by
  rw [parseAux]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma parseAux_triplesToAux (w : ℕ) (hw_pos : 0 < w) :
    ∀ (ts : List (Fin w × Bool × Bool)),
      parseAux w hw_pos (triplesToAux w ts) = ts := by
  intro ts
  induction ts with
  | nil => rw [triplesToAux, parseAux_nil]
  | cons hd rest ih =>
    obtain ⟨pos, dir, mark⟩ := hd
    have hlt : pos.val < w := pos.isLt
    have hfin : (⟨pos.val, hlt⟩ : Fin w) = pos := Fin.ext rfl
    cases mark with
    | true =>
      show parseAux w hw_pos ((pos.val, dir) :: (w, false) :: triplesToAux w rest) =
        (pos, dir, true) :: rest
      rw [parseAux_cons_marker w hw_pos pos.val hlt dir (triplesToAux w rest), ih, hfin]
    | false =>
      show parseAux w hw_pos ((pos.val, dir) :: triplesToAux w rest) =
        (pos, dir, false) :: rest
      cases rest with
      | nil =>
        show parseAux w hw_pos [(pos.val, dir)] = [(pos, dir, false)]
        rw [parseAux_singleton w hw_pos pos.val hlt dir, hfin]
      | cons hd2 rest2 =>
        obtain ⟨pos2, dir2, mark2⟩ := hd2
        have hpos2 : pos2.val < w := pos2.isLt
        cases mark2 with
        | true =>
          show parseAux w hw_pos ((pos.val, dir) ::
              (pos2.val, dir2) :: (w, false) :: triplesToAux w rest2) =
            (pos, dir, false) :: (pos2, dir2, true) :: rest2
          rw [parseAux_cons_nonmarker w hw_pos pos.val hlt dir pos2.val hpos2 dir2
                ((w, false) :: triplesToAux w rest2)]
          have hih : parseAux w hw_pos ((pos2.val, dir2) :: (w, false) :: triplesToAux w rest2)
              = (pos2, dir2, true) :: rest2 := by
            have hexp : triplesToAux w ((pos2, dir2, true) :: rest2) =
                (pos2.val, dir2) :: (w, false) :: triplesToAux w rest2 := rfl
            rw [← hexp]; exact ih
          rw [hih, hfin]
        | false =>
          show parseAux w hw_pos ((pos.val, dir) ::
              (pos2.val, dir2) :: triplesToAux w rest2) =
            (pos, dir, false) :: (pos2, dir2, false) :: rest2
          rw [parseAux_cons_nonmarker w hw_pos pos.val hlt dir pos2.val hpos2 dir2
                (triplesToAux w rest2)]
          have hih : parseAux w hw_pos ((pos2.val, dir2) :: triplesToAux w rest2)
              = (pos2, dir2, false) :: rest2 := by
            have hexp : triplesToAux w ((pos2, dir2, false) :: rest2) =
                (pos2.val, dir2) :: triplesToAux w rest2 := rfl
            rw [← hexp]; exact ih
          rw [hih, hfin]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma triplesToAux_append (w : ℕ)
    (ts₁ ts₂ : List (Fin w × Bool × Bool)) :
    triplesToAux w (ts₁ ++ ts₂) = triplesToAux w ts₁ ++ triplesToAux w ts₂ := by
  induction ts₁ with
  | nil => simp [triplesToAux]
  | cons hd rest ih =>
    obtain ⟨pos, dir, mark⟩ := hd
    cases mark with
    | true =>
      show triplesToAux w ((pos, dir, true) :: (rest ++ ts₂)) =
        triplesToAux w ((pos, dir, true) :: rest) ++ triplesToAux w ts₂
      simp [triplesToAux, ih]
    | false =>
      show triplesToAux w ((pos, dir, false) :: (rest ++ ts₂)) =
        triplesToAux w ((pos, dir, false) :: rest) ++ triplesToAux w ts₂
      simp [triplesToAux, ih]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_len_add {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits lits path ρ₀ σ).2.2.2.length +
    (processClauseLits lits path ρ₀ σ).1.length ≤ path.length := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits, List.length_cons]
      have := ih ps (Function.update ρ₀ hd.1.var (some p.2))
                    (Function.update σ hd.1.var (some (!hd.1.neg)))
      omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private def markLast {w : ℕ} :
    List (Fin w × Bool) → List (Fin w × Bool × Bool)
  | [] => []
  | hd :: [] => [(hd.1, hd.2, true)]
  | hd :: (hd2 :: rest) => (hd.1, hd.2, false) :: markLast (hd2 :: rest)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma triplesToAux_markLast (w : ℕ)
    (block : List (Fin w × Bool)) (hne : block ≠ []) :
    triplesToAux w (markLast block) =
      block.map (fun p => (p.1.val, p.2)) ++ [(w, false)] := by
  induction block with
  | nil => exact absurd rfl hne
  | cons hd rest ih =>
    obtain ⟨p, d⟩ := hd
    cases rest with
    | nil =>
      simp [markLast, triplesToAux]
    | cons hd2 rest2 =>
      have hML : markLast ((p, d) :: hd2 :: rest2) =
          (p, d, false) :: markLast (hd2 :: rest2) := by
        show markLast (((p, d) : Fin w × Bool) :: hd2 :: rest2) =
          (((p, d) : Fin w × Bool).1, ((p, d) : Fin w × Bool).2, false) ::
            markLast (hd2 :: rest2)
        rfl
      rw [hML]
      rw [show triplesToAux w ((p, d, false) :: markLast (hd2 :: rest2)) =
            (p.val, d) :: triplesToAux w (markLast (hd2 :: rest2)) from rfl]
      rw [ih (List.cons_ne_nil _ _)]
      simp
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma markLast_ne_nil {w : ℕ} (block : List (Fin w × Bool))
    (hne : block ≠ []) : markLast block ≠ [] := by
  match block, hne with
  | [hd], _ => simp [markLast]
  | hd :: hd2 :: rest, _ => simp [markLast]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma markLast_length {w : ℕ} :
    ∀ (block : List (Fin w × Bool)), (markLast block).length = block.length
  | [] => rfl
  | [_] => rfl
  | hd :: hd2 :: rest => by
      show ((hd.1, hd.2, false) :: markLast (hd2 :: rest)).length =
        (hd :: hd2 :: rest).length
      have ih := markLast_length (hd2 :: rest)
      simp [ih]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma markLast_getLast_true {w : ℕ} :
    ∀ (block : List (Fin w × Bool)) (hne : markLast block ≠ []),
      ((markLast block).getLast hne).2.2 = true
  | [], hne => by simp [markLast] at hne
  | [hd], _ => by
      show (((hd.1, hd.2, true) : Fin w × Bool × Bool)).2.2 = true
      rfl
  | hd :: hd2 :: rest, hne => by
      have hne' : markLast (hd2 :: rest) ≠ [] :=
        markLast_ne_nil _ (List.cons_ne_nil _ _)
      have ih := markLast_getLast_true (hd2 :: rest) hne'
      show (((hd.1, hd.2, false) :: markLast (hd2 :: rest)).getLast hne).2.2 = true
      rw [List.getLast_cons hne']
      exact ih
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private def toFinBlock (w : ℕ) :
    ∀ (l : List (ℕ × Bool)) (_ : ∀ e ∈ l, e.1 < w), List (Fin w × Bool)
  | [], _ => []
  | (idx, dir) :: rest, h =>
    (⟨idx, h (idx, dir) (List.mem_cons_self)⟩, dir) ::
      toFinBlock w rest (fun e he => h e (List.mem_cons_of_mem _ he))
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma toFinBlock_length (w : ℕ) (l : List (ℕ × Bool))
    (h : ∀ e ∈ l, e.1 < w) :
    (toFinBlock w l h).length = l.length := by
  induction l with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨idx, dir⟩ := hd
    simp [toFinBlock, ih]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma toFinBlock_map (w : ℕ) (l : List (ℕ × Bool))
    (h : ∀ e ∈ l, e.1 < w) :
    (toFinBlock w l h).map (fun p => (p.1.val, p.2)) = l := by
  induction l with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨idx, dir⟩ := hd
    simp [toFinBlock, ih]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma toFinBlock_ne_nil (w : ℕ) (l : List (ℕ × Bool))
    (h : ∀ e ∈ l, e.1 < w) (hne : l ≠ []) :
    toFinBlock w l h ≠ [] := by
  cases l with
  | nil => exact absurd rfl hne
  | cons hd rest =>
    obtain ⟨idx, dir⟩ := hd
    simp [toFinBlock]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_aux_idx_lt {n : ℕ} (t : Term n)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx) :
    ∀ e ∈ (processClauseLits lits path ρ₀ σ).2.2.2, e.1 < t.length := by
  intro e he
  obtain ⟨li, hli, hidx⟩ := processClauseLits_aux_entries_from_lits lits path ρ₀ σ e he
  obtain ⟨_, hlt_len, _⟩ := List.mem_zipIdx (hmem li hli)
  rw [hidx]; omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma encode_go_wellformed {n : ℕ} (f : DNF n) (w : ℕ)
    (hw : f.width ≤ w) (_hw_pos : 0 < w)
    (fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n) :
    ∃ ts : List (Fin w × Bool × Bool),
      (razborovEncode.go f w fuel path ρ₀ σ []).2 = triplesToAux w ts ∧
      ts.length ≤ path.length ∧
      (∀ (hne : ts ≠ []), (ts.getLast hne).2.2 = true) := by
  induction fuel generalizing path ρ₀ σ with
  | zero =>
    refine ⟨[], ?_, by simp, by intro hne; exact absurd rfl hne⟩
    cases path <;> simp [razborovEncode.go, triplesToAux]
  | succ fuel ih =>
    cases path with
    | nil =>
      refine ⟨[], ?_, by simp, by intro hne; exact absurd rfl hne⟩
      simp [razborovEncode.go, triplesToAux]
    | cons step rest =>
      simp only [razborovEncode.go]
      -- Case split on find?
      cases hfind : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) with
      | none =>
        refine ⟨[], ?_, by simp, by intro hne; exact absurd rfl hne⟩
        simp [triplesToAux]
      | some t_clause =>
        simp only []
        -- Filter free literals
        set fli := (t_clause.zipIdx).filter
          (fun ⟨l, _⟩ => decide (l.var ∈ ρ₀.freeVars)) with hfli_def
        cases hflicase : fli with
        | nil =>
          refine ⟨[], ?_, by simp, by intro hne; exact absurd rfl hne⟩
          simp [triplesToAux]
        | cons fl fls =>
          simp only []
          set pcl := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ with hpcl_def
          -- Extract the "new block" of aux data from pcl
          have ht_mem : t_clause ∈ f := List.mem_of_find?_eq_some hfind
          have ht_len : t_clause.length ≤ w :=
            le_trans (term_length_le_width f t_clause ht_mem) hw
          have hfli_mem_zip : ∀ p ∈ fl :: fls, p ∈ t_clause.zipIdx := by
            intro p hp
            rw [← hflicase] at hp
            rw [hfli_def] at hp
            exact (List.mem_filter.mp hp).1
          have hpcl_idx_lt : ∀ e ∈ pcl.2.2.2, e.1 < w := by
            intro e he
            exact lt_of_lt_of_le
              (processClauseLits_aux_idx_lt t_clause (fl :: fls) (step :: rest)
                ρ₀ σ hfli_mem_zip e he) ht_len
          -- The new block is nonempty
          have hpcl_ne : pcl.2.2.2 ≠ [] := by
            simp only [hpcl_def, processClauseLits]
            exact List.cons_ne_nil _ _
          -- Convert to Fin w × Bool list
          set block := toFinBlock w pcl.2.2.2 hpcl_idx_lt with hblock_def
          have hblock_ne : block ≠ [] := toFinBlock_ne_nil w _ _ hpcl_ne
          -- Apply the accumulator lemma and IH
          simp only [List.nil_append]
          rw [encode_go_acc f w fuel pcl.1 pcl.2.1 pcl.2.2.1 (pcl.2.2.2 ++ [(w, false)])]
          obtain ⟨ts_rec, hts_eq, hts_len, hts_last⟩ :=
            ih pcl.1 pcl.2.1 pcl.2.2.1
          refine ⟨markLast block ++ ts_rec, ?_, ?_, ?_⟩
          · -- Show the combined aux list matches triplesToAux
            simp only
            rw [triplesToAux_append, triplesToAux_markLast w block hblock_ne,
                hblock_def, toFinBlock_map, hts_eq]
          · -- Length bound
            rw [List.length_append]
            have hml_len : (markLast block).length = pcl.2.2.2.length := by
              rw [markLast_length]
              exact toFinBlock_length w pcl.2.2.2 hpcl_idx_lt
            have hpcl_len : pcl.2.2.2.length + pcl.1.length ≤ (step :: rest).length :=
              processClauseLits_len_add (fl :: fls) (step :: rest) ρ₀ σ
            omega
          · intro _
            -- The last of markLast block ++ ts_rec is either ts_rec's last
            -- or markLast block's last (if ts_rec = []).
            by_cases hts_rec_ne : ts_rec = []
            · subst hts_rec_ne
              simp only [List.append_nil]
              exact markLast_getLast_true block (markLast_ne_nil block hblock_ne)
            · rw [List.getLast_append_of_ne_nil _ hts_rec_ne]
              exact hts_last hts_rec_ne
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma exists_aux_injection {n : ℕ} (f : DNF n) (w d : ℕ)
    (hw : f.width ≤ w) (hw_pos : 0 < w) (γ : Restriction n) :
    ∃ g : List (ℕ × Bool) → (Fin d → Fin w × Bool × Bool),
      Set.InjOn g
        (((Finset.univ.filter fun ρ : Restriction n =>
          IsBadRestriction f.eval d ρ ∧
          (razborovEncode f w d ρ).1 = γ).image
          (fun ρ => (razborovEncode f w d ρ).2) : Finset _) :
            Set (List (ℕ × Bool))) := by
  -- Strategy: parse aux into triples (pos : Fin w, dir : Bool, hasMarker : Bool)
  -- where `hasMarker = true` means the `(idx, dir)` entry is immediately
  -- followed by a `(w, false)` termination marker.  Pad to length d with a
  -- default triple to get a function `Fin d → Fin w × Bool × Bool`.
  -- For injectivity we use the round-trip `triplesToAux ∘ parseAux = id` on
  -- the encoder image; this is proved as a separate invariant of the encoder
  -- combined with `parseAux_triplesToAux`.
  classical
  refine ⟨fun aux =>
    fun i => ((parseAux w hw_pos aux)[i.val]?).getD (⟨0, hw_pos⟩, false, false),
    ?_⟩
  intro aux₁ haux₁ aux₂ haux₂ hg_eq
  -- Unified encoder well-formedness: every aux in the image is of the form
  -- `triplesToAux w ts` for some `ts` of length ≤ d whose last element (if any)
  -- has `hasMarker = true`.
  have hwf : ∀ aux : List (ℕ × Bool),
      aux ∈ ((Finset.univ.filter fun ρ : Restriction n =>
          IsBadRestriction f.eval d ρ ∧
          (razborovEncode f w d ρ).1 = γ).image
          (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
      ∃ ts : List (Fin w × Bool × Bool),
        aux = triplesToAux w ts ∧ ts.length ≤ d ∧
        (∀ (hne : ts ≠ []), (ts.getLast hne).2.2 = true) := by
    intro aux haux
    rw [Finset.mem_image] at haux
    obtain ⟨ρ, _, hρ_eq⟩ := haux
    rw [← hρ_eq]
    unfold razborovEncode
    obtain ⟨ts, hts_eq, hts_len, hts_last⟩ :=
      encode_go_wellformed f w hw hw_pos
        (((canonicalDTree f ρ).deepPath.take d).length + 1)
        ((canonicalDTree f ρ).deepPath.take d) ρ ρ
    refine ⟨ts, hts_eq, ?_, hts_last⟩
    have : ((canonicalDTree f ρ).deepPath.take d).length ≤ d :=
      List.length_take_le d _
    omega
  -- Derive the three local facts from hwf.
  have hround : ∀ aux : List (ℕ × Bool),
      aux ∈ ((Finset.univ.filter fun ρ : Restriction n =>
          IsBadRestriction f.eval d ρ ∧
          (razborovEncode f w d ρ).1 = γ).image
          (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
      triplesToAux w (parseAux w hw_pos aux) = aux := by
    intro aux haux
    obtain ⟨ts, hts_eq, _, _⟩ := hwf aux haux
    rw [hts_eq, parseAux_triplesToAux]
  have hlen : ∀ aux : List (ℕ × Bool),
      aux ∈ ((Finset.univ.filter fun ρ : Restriction n =>
          IsBadRestriction f.eval d ρ ∧
          (razborovEncode f w d ρ).1 = γ).image
          (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
      (parseAux w hw_pos aux).length ≤ d := by
    intro aux haux
    obtain ⟨ts, hts_eq, hts_len, _⟩ := hwf aux haux
    rw [hts_eq, parseAux_triplesToAux]
    exact hts_len
  have hlast : ∀ aux : List (ℕ × Bool),
      aux ∈ ((Finset.univ.filter fun ρ : Restriction n =>
          IsBadRestriction f.eval d ρ ∧
          (razborovEncode f w d ρ).1 = γ).image
          (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
      ∀ (hlen_pos : 0 < (parseAux w hw_pos aux).length),
        ((parseAux w hw_pos aux)[(parseAux w hw_pos aux).length - 1]'
          (Nat.sub_lt hlen_pos (by norm_num))).2.2 = true := by
    intro aux haux hlen_pos
    obtain ⟨ts, hts_eq, _, hts_last⟩ := hwf aux haux
    have hparse : parseAux w hw_pos aux = ts := by
      rw [hts_eq, parseAux_triplesToAux]
    -- Translate the goal to ts
    have hts_ne : ts ≠ [] := by
      intro h
      rw [hparse, h] at hlen_pos
      exact absurd hlen_pos (by simp)
    have hlast_val := hts_last hts_ne
    -- `ts.getLast hts_ne = ts[ts.length - 1]`
    have hgetLast_eq :
        ts.getLast hts_ne = ts[ts.length - 1]'(Nat.sub_lt
          (List.length_pos_iff.mpr hts_ne) (by norm_num)) := by
      rw [List.getLast_eq_getElem]
    rw [hgetLast_eq] at hlast_val
    -- And the parseAux version = ts version
    conv_lhs =>
      rw [show (parseAux w hw_pos aux)[(parseAux w hw_pos aux).length - 1]'
              (Nat.sub_lt hlen_pos (by norm_num)) =
            ts[ts.length - 1]'(Nat.sub_lt (List.length_pos_iff.mpr hts_ne) (by norm_num))
          from by (congr 1; rw [hparse])]
    exact hlast_val
  have hparse_eq : parseAux w hw_pos aux₁ = parseAux w hw_pos aux₂ := by
    have h1 := hlen aux₁ haux₁
    have h2 := hlen aux₂ haux₂
    have hpt : ∀ i : Fin d,
        (parseAux w hw_pos aux₁)[i.val]?.getD (⟨0, hw_pos⟩, false, false) =
        (parseAux w hw_pos aux₂)[i.val]?.getD (⟨0, hw_pos⟩, false, false) := by
      intro i
      have := congrFun hg_eq i
      simpa using this
    -- Step 1: lengths are equal.
    have hlen_eq : (parseAux w hw_pos aux₁).length = (parseAux w hw_pos aux₂).length := by
      by_contra hne
      -- Symmetric helper handling the case L1.length < L2.length.
      have key : ∀ (a b : List (ℕ × Bool)),
          a ∈ ((Finset.univ.filter fun ρ : Restriction n =>
              IsBadRestriction f.eval d ρ ∧
              (razborovEncode f w d ρ).1 = γ).image
              (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
          b ∈ ((Finset.univ.filter fun ρ : Restriction n =>
              IsBadRestriction f.eval d ρ ∧
              (razborovEncode f w d ρ).1 = γ).image
              (fun ρ => (razborovEncode f w d ρ).2) : Finset _) →
          (parseAux w hw_pos a).length ≤ d → (parseAux w hw_pos b).length ≤ d →
          (parseAux w hw_pos a).length < (parseAux w hw_pos b).length →
          (∀ i : Fin d,
            (parseAux w hw_pos a)[i.val]?.getD (⟨0, hw_pos⟩, false, false) =
            (parseAux w hw_pos b)[i.val]?.getD (⟨0, hw_pos⟩, false, false)) →
          False := by
        intro a b ha hb ha_d hb_d hlt hpt_ab
        set La := parseAux w hw_pos a
        set Lb := parseAux w hw_pos b
        have hb_pos : 0 < Lb.length := lt_of_le_of_lt (Nat.zero_le _) hlt
        set j := Lb.length - 1 with hj_def
        have hjlt : j < Lb.length := Nat.sub_lt hb_pos (by norm_num)
        have hjd : j < d := lt_of_lt_of_le hjlt hb_d
        have hjLa : La.length ≤ j := by omega
        have hja : La[j]? = none := List.getElem?_eq_none hjLa
        have hjb : Lb[j]? = some (Lb[j]) := List.getElem?_eq_getElem hjlt
        have hval := hpt_ab ⟨j, hjd⟩
        rw [hja, hjb] at hval
        simp only [Option.getD_none, Option.getD_some] at hval
        have hmark : (Lb[j]).2.2 = true := hlast b hb hb_pos
        rw [← hval] at hmark
        simp at hmark
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact key aux₁ aux₂ haux₁ haux₂ h1 h2 hlt hpt
      · exact key aux₂ aux₁ haux₂ haux₁ h2 h1 hgt (fun i => (hpt i).symm)
    -- Step 2: equal lengths + pointwise equality gives list equality.
    apply List.ext_getElem hlen_eq
    intro i hi1 hi2
    have hid : i < d := lt_of_lt_of_le hi1 h1
    have hval := hpt ⟨i, hid⟩
    rw [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2] at hval
    simpa using hval
  -- Now apply triplesToAux to both sides.
  have := congrArg (triplesToAux w) hparse_eq
  rw [hround aux₁ haux₁, hround aux₂ haux₂] at this
  exact this
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma aux_image_card_bound {n : ℕ} (f : DNF n) (w d : ℕ)
    (hw : f.width ≤ w) (γ : Restriction n) :
    (((Finset.univ.filter fun ρ : Restriction n =>
        IsBadRestriction f.eval d ρ ∧
        (razborovEncode f w d ρ).1 = γ).image
        (fun ρ => (razborovEncode f w d ρ).2)).card) ≤ (4 * w) ^ d := by
  by_cases hw0 : w = 0
  · -- Edge case w = 0: `f.width ≤ 0` forces every term in `f` to be empty,
    -- and empty terms are trivially `fixedBy` any restriction, so
    -- `dtDepth (restrictFn f.eval ρ) = 0` and there are no bad restrictions.
    subst hw0
    have hall_empty : ∀ t ∈ f, t = [] := by
      intro t ht
      have ht_len : t.length ≤ 0 := le_trans (term_length_le_width f t ht) hw
      exact List.length_eq_zero_iff.mp (Nat.le_zero.mp ht_len)
    have hno_bad : ∀ ρ : Restriction n, ¬ IsBadRestriction f.eval d ρ := by
      intro ρ hbad
      unfold IsBadRestriction at hbad
      -- If f has any term, that term is empty hence fixedBy ρ → dtDepth 0
      -- If f is empty, restrictFn is constant false → dtDepth 0
      by_cases hf : f = []
      · have hdtd : dtDepth (restrictFn f.eval ρ) = 0 := by
          apply killedAll_implies_dtDepth_zero
          intro t ht
          rw [hf] at ht; exact absurd ht (List.not_mem_nil)
        omega
      · obtain ⟨t, ht_mem⟩ := List.exists_mem_of_ne_nil f hf
        have ht_empty : t = [] := hall_empty t ht_mem
        have hdtd : dtDepth (restrictFn f.eval ρ) = 0 := by
          apply fixedTerm_implies_dtDepth_zero
          exact ⟨t, ht_mem, by rw [ht_empty]; intro l hl; exact absurd hl (List.not_mem_nil)⟩
        omega
    have hfilter_empty : (Finset.univ.filter fun ρ : Restriction n =>
        IsBadRestriction f.eval d ρ ∧ (razborovEncode f 0 d ρ).1 = γ) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      exact hno_bad ρ hρ.2.1
    rw [hfilter_empty, Finset.image_empty, Finset.card_empty]
    exact Nat.zero_le _
  · have hw_pos : 0 < w := Nat.pos_of_ne_zero hw0
    obtain ⟨g, hginj⟩ := exists_aux_injection f w d hw hw_pos γ
    set S := ((Finset.univ.filter fun ρ : Restriction n =>
        IsBadRestriction f.eval d ρ ∧
        (razborovEncode f w d ρ).1 = γ).image
        (fun ρ => (razborovEncode f w d ρ).2)) with hS_def
    have hcard_eq : Fintype.card (Fin d → Fin w × Bool × Bool) = (4 * w) ^ d := by
      simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
                 Fintype.card_bool]
      ring
    calc S.card
        = (S.image g).card := (Finset.card_image_of_injOn hginj).symm
      _ ≤ (Finset.univ : Finset (Fin d → Fin w × Bool × Bool)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card (Fin d → Fin w × Bool × Bool) := Finset.card_univ
      _ = (4 * w) ^ d := hcard_eq
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma fiber_bound {n : ℕ} (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (_hd : d ≤ s)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (γ : Restriction n) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ ∧
        (razborovEncode f w d ρ).1 = γ).card ≤ (4 * w) ^ d := by
  -- Step 1: drop the `IsRestriction` hypothesis (monotone in the filter).
  set S := (Finset.univ.filter fun ρ : Restriction n =>
      IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ ∧
      (razborovEncode f w d ρ).1 = γ)
  set T := (Finset.univ.filter fun ρ : Restriction n =>
      IsBadRestriction f.eval d ρ ∧ (razborovEncode f w d ρ).1 = γ)
  have hST : S ⊆ T := by
    intro ρ hρ
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    exact ⟨hρ.2.1, hρ.2.2⟩
  refine le_trans (Finset.card_le_card hST) ?_
  -- Step 2: the map `ρ ↦ (razborovEncode f w d ρ).2` is injective on T.
  have hinj : Set.InjOn (fun ρ : Restriction n => (razborovEncode f w d ρ).2)
      (T : Set (Restriction n)) := by
    intro ρ₁ hρ₁ ρ₂ hρ₂ heq
    simp only [T, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hρ₁ hρ₂
    obtain ⟨hbad₁, hγ₁⟩ := hρ₁
    obtain ⟨hbad₂, hγ₂⟩ := hρ₂
    have henc : razborovEncode f w d ρ₁ = razborovEncode f w d ρ₂ := by
      apply Prod.ext
      · rw [hγ₁, hγ₂]
      · exact heq
    exact razborovEncode_injective f w d ρ₁ ρ₂ hbad₁ hbad₂ hw hnd henc
  rw [← Finset.card_image_of_injOn hinj]
  exact aux_image_card_bound f w d hw γ
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma card_filter_numFree_eq (n k : ℕ) :
    (Finset.univ.filter fun ρ : Restriction n => ρ.numFree = k).card =
    n.choose k * 2 ^ (n - k) := by
  -- Partition restrictions by their set of free variables.
  classical
  rw [show (Finset.univ.filter fun ρ : Restriction n => ρ.numFree = k) =
      (Finset.univ.filter fun ρ : Restriction n => ρ.freeVars.card = k) from rfl]
  -- Use bijection: ρ ↔ (ρ.freeVars, g) where g encodes the non-free values.
  -- The cardinality is computed via a fiberwise sum over subsets of size k.
  have hcard : ∀ S : Finset (Fin n),
      (Finset.univ.filter fun ρ : Restriction n => ρ.freeVars = S).card = 2 ^ (n - S.card) := by
    intro S
    -- Bijection with functions (Fin n \ S) → Bool.
    let φ : (Fin n → Bool) → Restriction n :=
      fun g i => if i ∈ S then none else some (g i)
    have hφinj : ∀ g₁ g₂ : Fin n → Bool, (∀ i ∈ S, g₁ i = false) →
        (∀ i ∈ S, g₂ i = false) → φ g₁ = φ g₂ → g₁ = g₂ := by
      intro g₁ g₂ hg₁ hg₂ heq
      funext i
      by_cases hi : i ∈ S
      · rw [hg₁ i hi, hg₂ i hi]
      · have := congrFun heq i
        simp only [φ, hi, if_false] at this
        exact Option.some.inj this
    have himg : (Finset.univ.filter fun ρ : Restriction n => ρ.freeVars = S) =
        ((Finset.univ.filter fun g : Fin n → Bool => ∀ i ∈ S, g i = false).image φ) := by
      ext ρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hρ
        refine ⟨fun i => (ρ i).getD false, ?_, ?_⟩
        · intro i hi
          have : ρ i = none := by
            have : i ∈ ρ.freeVars := by rw [hρ]; exact hi
            simp [Restriction.freeVars] at this
            exact this
          simp [this]
        · funext i
          simp only [φ]
          by_cases hi : i ∈ S
          · simp only [hi, if_true]
            have : i ∈ ρ.freeVars := by rw [hρ]; exact hi
            simp [Restriction.freeVars] at this
            exact this.symm
          · simp only [hi, if_false]
            have hnf : i ∉ ρ.freeVars := by rw [hρ]; exact hi
            simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ,
                       true_and, Option.isNone_iff_eq_none] at hnf
            cases h : ρ i with
            | none => exact absurd h hnf
            | some b => simp
      · rintro ⟨g, hg, rfl⟩
        ext i
        simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and, φ]
        constructor
        · intro hi
          by_cases h : i ∈ S
          · exact h
          · simp [h] at hi
        · intro hi
          simp [hi]
    rw [himg, Finset.card_image_of_injOn]
    · -- cardinality of {g : Fin n → Bool | ∀ i ∈ S, g i = false}
      -- equals 2 ^ (n - S.card) since g is free on (Fin n \ S).
      -- Use bijection with (Fin n \ S) → Bool... or just direct counting.
      classical
      let ψ : ((↥Sᶜ : Type) → Bool) → (Fin n → Bool) :=
        fun h i => if hi : i ∈ S then false else h ⟨i, by
          simp only [Finset.mem_compl]; exact hi⟩
      have hψ_range : Set.range ψ =
          {g : Fin n → Bool | ∀ i ∈ S, g i = false} := by
        ext g
        simp only [Set.mem_range, Set.mem_setOf_eq]
        constructor
        · rintro ⟨h, rfl⟩ i hi
          simp [ψ, hi]
        · intro hg
          refine ⟨fun j => g j.val, ?_⟩
          funext i
          simp only [ψ]
          by_cases hi : i ∈ S
          · simp [hi, hg i hi]
          · simp [hi]
      have hψ_inj : Function.Injective ψ := by
        intro h₁ h₂ heq
        funext ⟨i, hi⟩
        have := congrFun heq i
        simp only [Finset.mem_compl] at hi
        simp only [ψ, hi, dite_false] at this
        exact this
      have hcard_ψ : Fintype.card ((↥Sᶜ : Type) → Bool) = 2 ^ (n - S.card) := by
        simp [Fintype.card_coe]
      have himg_ψ : (Finset.univ.image ψ :
          Finset (Fin n → Bool)) = (Finset.univ.filter fun g => ∀ i ∈ S, g i = false) := by
        ext g
        simp only [Finset.mem_image, Finset.mem_univ, true_and,
                   Finset.mem_filter]
        rw [← Set.mem_range (f := ψ), hψ_range]
        simp
      rw [← himg_ψ, Finset.card_image_of_injective _ hψ_inj]
      rw [Finset.card_univ]
      exact hcard_ψ
    · intro g₁ hg₁ g₂ hg₂ heq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg₁ hg₂
      exact hφinj g₁ g₂ hg₁ hg₂ heq
  -- Now sum over S with |S| = k using powersetCard directly.
  have hpart : (Finset.univ.filter fun ρ : Restriction n => ρ.freeVars.card = k) =
      ((Finset.univ : Finset (Fin n)).powersetCard k).biUnion
        (fun S => Finset.univ.filter fun ρ : Restriction n => ρ.freeVars = S) := by
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
               Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · intro hρ; exact ⟨ρ.freeVars, hρ, rfl⟩
    · rintro ⟨S, hS, hρ⟩; rw [hρ]; exact hS
  rw [hpart, Finset.card_biUnion]
  · -- Each fiber has size 2^(n - S.card), and |S| = k in powersetCard.
    have hsum_eq : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (Finset.univ.filter fun ρ : Restriction n => ρ.freeVars = S).card =
          2 ^ (n - k) := by
      intro S hS
      rw [hcard S]
      rw [Finset.mem_powersetCard] at hS
      rw [hS.2]
    rw [Finset.sum_congr rfl hsum_eq]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard]
    simp
  · -- Disjoint: different S give different ρ
    intro S₁ _ S₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left]
    intro ρ hρ₁ hρ₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ₁ hρ₂
    exact hne (hρ₁.symm.trans hρ₂)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma numFree_update_free {n : ℕ} (ρ : Restriction n) (v : Fin n) (b : Bool)
    (hv : ρ v = none) :
    Restriction.numFree (Function.update ρ v (some b)) + 1 = ρ.numFree := by
  classical
  have hv_mem : v ∈ ρ.freeVars := by
    simp [Restriction.freeVars, hv]
  have hsub : Restriction.freeVars (Function.update ρ v (some b)) = ρ.freeVars.erase v := by
    ext i
    simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_erase]
    by_cases hi : i = v
    · subst hi; simp [Function.update, hv]
    · simp [hi]
  have hcard : Restriction.numFree (Function.update ρ v (some b)) =
      (ρ.freeVars.erase v).card := by
    unfold Restriction.numFree; rw [hsub]
  rw [hcard, Finset.card_erase_of_mem hv_mem]
  unfold Restriction.numFree
  have hpos : 0 < ρ.freeVars.card := Finset.card_pos.mpr ⟨v, hv_mem⟩
  omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_freeVars_agree {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (hagree : ∀ v, ρ₀ v = none ↔ σ v = none) :
    ∀ v, (processClauseLits lits path ρ₀ σ).2.1 v = none ↔
         (processClauseLits lits path ρ₀ σ).2.2.1 v = none := by
  induction lits generalizing path ρ₀ σ with
  | nil => intro v; simp [processClauseLits]; exact hagree v
  | cons hd tl ih =>
    cases path with
    | nil => intro v; simp [processClauseLits]; exact hagree v
    | cons p ps =>
      simp only [processClauseLits]
      apply ih
      intro v
      by_cases heq : v = hd.1.var
      · subst heq; simp [Function.update]
      · simp [Function.update_of_ne heq]; exact hagree v
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_numFree_σ {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (hagree : ∀ v, ρ₀ v = none ↔ σ v = none)
    (hfree : ∀ p ∈ lits, ρ₀ p.1.var = none)
    (hdistinct : lits.Pairwise (fun p q => p.1.var ≠ q.1.var)) :
    (processClauseLits lits path ρ₀ σ).2.2.1.numFree + min lits.length path.length =
      σ.numFree := by
  classical
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits, List.length_cons]
      have hhd : ρ₀ hd.1.var = none := hfree hd (by simp)
      have hhdσ : σ hd.1.var = none := (hagree _).mp hhd
      have hagree' : ∀ v,
          (Function.update ρ₀ hd.1.var (some p.2)) v = none ↔
          (Function.update σ hd.1.var (some (!hd.1.neg))) v = none := by
        intro v
        by_cases heq : v = hd.1.var
        · subst heq; simp [Function.update]
        · simp [Function.update_of_ne heq]; exact hagree v
      have hfree' : ∀ q ∈ tl,
          (Function.update ρ₀ hd.1.var (some p.2)) q.1.var = none := by
        intro q hq
        have hneq : q.1.var ≠ hd.1.var := by
          have := List.rel_of_pairwise_cons hdistinct hq
          exact fun h => this h.symm
        rw [Function.update_of_ne hneq]
        exact hfree q (by simp [hq])
      have hdistinct' : tl.Pairwise (fun p q => p.1.var ≠ q.1.var) :=
        List.Pairwise.of_cons hdistinct
      have hih := ih ps (Function.update ρ₀ hd.1.var (some p.2))
                    (Function.update σ hd.1.var (some (!hd.1.neg)))
                    hagree' hfree' hdistinct'
      have hupd :
          Restriction.numFree (Function.update σ hd.1.var (some (!hd.1.neg))) + 1 =
            σ.numFree := numFree_update_free σ hd.1.var (!hd.1.neg) hhdσ
      omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma canonicalDTree_deepPath_length_ge {n : ℕ} (f : DNF n)
    (ρ : Restriction n) (d : ℕ) (hbad : IsBadRestriction f.eval d ρ) :
    d < (canonicalDTree f ρ).deepPath.length := by
  rw [DecisionTree.length_deepPath]
  have h1 : dtDepth (restrictFn f.eval ρ) > d := hbad
  have h2 : (canonicalDTree f ρ).depth ≥ dtDepth (restrictFn f.eval ρ) :=
    canonicalDTree_depth_ge f ρ
  omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma razborovEncode_path_length {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (d : ℕ) (hbad : IsBadRestriction f.eval d ρ) :
    ((canonicalDTree f ρ).deepPath.take d).length = d := by
  have hge : d ≤ (canonicalDTree f ρ).deepPath.length :=
    Nat.le_of_lt (canonicalDTree_deepPath_length_ge f ρ d hbad)
  rw [List.length_take]
  omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_path_length_eq {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits lits path ρ₀ σ).1.length + min lits.length path.length =
      path.length := by
  induction lits generalizing path ρ₀ σ with
  | nil => simp [processClauseLits]
  | cons hd tl ih =>
    cases path with
    | nil => simp [processClauseLits]
    | cons p ps =>
      simp only [processClauseLits, List.length_cons]
      have hih := ih ps (Function.update ρ₀ hd.1.var (some p.2))
                       (Function.update σ hd.1.var (some (!hd.1.neg)))
      omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma canonicalDTree_depth_zero_of_killed {n : ℕ} (f : DNF n)
    (ρ : Restriction n) (h : ∀ t ∈ f, Term.killedBy t ρ) :
    (canonicalDTree f ρ).depth = 0 := by
  unfold canonicalDTree
  -- `canonicalDTree.go f (ρ.numFree + 1) ρ` hits the `fuel + 1` branch,
  -- and the first `if` is satisfied by hypothesis, so returns `.leaf false`.
  set fuel := ρ.numFree
  show (canonicalDTree.go f (fuel + 1) ρ).depth = 0
  simp only [canonicalDTree.go]
  rw [dif_pos h]
  rfl
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma canonicalDTree_depth_zero_of_fixed {n : ℕ} (f : DNF n)
    (ρ : Restriction n) (h : ∃ t ∈ f, Term.fixedBy t ρ) :
    (canonicalDTree f ρ).depth = 0 := by
  unfold canonicalDTree
  set fuel := ρ.numFree
  show (canonicalDTree.go f (fuel + 1) ρ).depth = 0
  simp only [canonicalDTree.go]
  by_cases hkill : ∀ t ∈ f, Term.killedBy t ρ
  · rw [dif_pos hkill]; rfl
  · rw [dif_neg hkill, dif_pos h]; rfl
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private def IsCanonicalPath {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (path : List (Fin n × Bool)) : Prop :=
  path = (canonicalDTree f ρ).deepPath.take path.length
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma zipIdx_filter_length {n : ℕ} (t : Term n)
    (p : Literal n → Bool) :
    (t.zipIdx.filter (fun x => p x.1)).length = (t.filter p).length := by
  induction' t using List.reverseRecOn with t ih;
  · rfl;
  · grind
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma zipIdx_filter_getElem_fst {n : ℕ} (t : Term n)
    (p : Literal n → Bool) (k : ℕ)
    (hk1 : k < (t.zipIdx.filter (fun x => p x.1)).length)
    (hk2 : k < (t.filter p).length) :
    ((t.zipIdx.filter (fun x => p x.1))[k]'hk1).1 = (t.filter p)[k]'hk2 := by
  -- By definition of `List.zipIdx`, the first component of the k-th element in the filtered list is the k-th element of the original list.
  have h_zipIdx : ∀ (t : Term n) (p : Literal n → Bool), List.map (fun x => x.1) (List.filter (fun x => p x.1) (List.zipIdx t)) = List.filter p t := by
    intros t p;
    induction' t using List.reverseRecOn with t ih;
    · rfl;
    · grind;
  grind
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma canonicalDTree_deepPath_match_freeLits {n : ℕ} (f : DNF n)
    (ρ : Restriction n) (t : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t)
    (hnd : ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : t.Nodup)
    (k : ℕ)
    (flis : List (Literal n × ℕ))
    (hflis : flis = (t.zipIdx).filter (fun p => decide (p.1.var ∈ ρ.freeVars)))
    (hk_flis : k < flis.length)
    (hk_path : k < (canonicalDTree f ρ).deepPath.length) :
    ((canonicalDTree f ρ).deepPath[k]'hk_path).1 = (flis[k]'hk_flis).1.var := by
  have halive : ¬ (∀ t ∈ f, Term.killedBy t ρ) ∧ ¬ (∃ t ∈ f, Term.fixedBy t ρ) := by
    constructor <;> contrapose! hk_path <;> simp_all +decide [ Term.killedBy, Term.fixedBy ] ;
    · grind;
    · have h_depth_zero : (canonicalDTree f ρ).depth = 0 := by
        apply SwitchingLemma2.canonicalDTree_depth_zero_of_fixed f ρ hk_path
      generalize_proofs at *; (
      have h_depth_zero : ∀ (T : DecisionTree n), T.depth = 0 → T.deepPath.length = 0 := by
        intros T hT_depth_zero
        have hT_leaf : T = .leaf true ∨ T = .leaf false := by
          cases T <;> simp_all +decide [ DecisionTree.depth ]
        generalize_proofs at *; (
        rcases hT_leaf with ( rfl | rfl ) <;> rfl)
      generalize_proofs at *; (
      exact le_trans ( h_depth_zero _ ‹_› |> le_of_eq ) ( Nat.zero_le _ )));
  -- Apply the lemma termSubTree_deepPath_var_match with the pairwise distinctness of t.
  have h_pairwise : t.Pairwise (fun l₁ l₂ => l₁.var ≠ l₂.var) := by
    refine' List.Pairwise.imp_of_mem _ hnodup;
    exact fun { a b } ha hb hab h => hab <| hnd a ha b hb h;
  have := canonicalDTree_alive_eq_termSubTree' f ρ halive.1 halive.2 t hfind;
  have := termSubTree_deepPath_var_match t ρ (fun ρ' => if decide (Term.fixedBy t ρ') = true then DecisionTree.leaf true else SwitchingLemma2.canonicalDTree.go f ρ.numFree ρ') h_pairwise k ?_ ?_ <;> simp_all +decide ;
  any_goals rw [ ← zipIdx_filter_length ] ; simp +decide [ hk_flis ];
  rw [ ← zipIdx_filter_getElem_fst ]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_fst_eq_drop {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) :
    (processClauseLits lits path ρ₀ σ).1 = path.drop (min lits.length path.length) := by
  induction' lits with hd tl hl generalizing path ρ₀ σ;
  · cases path <;> aesop;
  · cases path <;> simp_all +decide [ processClauseLits ]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_numFree_ρ_eq {n : ℕ}
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (hfree : ∀ p ∈ lits, ρ₀ p.1.var = none)
    (hdistinct : lits.Pairwise (fun p q => p.1.var ≠ q.1.var)) :
    (processClauseLits lits path ρ₀ σ).2.1.numFree + min lits.length path.length = ρ₀.numFree := by
  induction' lits with hd tl hl generalizing path ρ₀ σ;
  · cases path <;> aesop;
  · rcases path with ( _ | ⟨ p, ps ⟩ ) <;> simp_all +decide;
    · rfl;
    · convert congr_arg ( · + 1 ) ( hl ps ( Function.update ρ₀ hd.1.var ( some p.2 ) ) ( Function.update σ hd.1.var ( some ( !hd.1.neg ) ) ) ( fun a b hab => ?_ ) ) using 1;
      · rw [ numFree_update_free ] ; aesop;
      · rw [Function.update_of_ne (Ne.symm (hdistinct.1 a b hab))]; exact hfree.2 a b hab
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_termSubTree_drop {n : ℕ} :
    ∀ (t : Term n) (ρ₀ σ : Restriction n)
      (cont : Restriction n → DecisionTree n)
      (_hdistinct : t.Pairwise (fun l₁ l₂ => l₁.var ≠ l₂.var))
      (path : List (Fin n × Bool))
      (lits : List (Literal n × ℕ))
      (hlits_len : lits.length = (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars))).length)
      (_hlits_match : ∀ k (hk : k < lits.length),
        (lits[k]'hk).1 = (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars)))[k]'(by omega))
      (_hpath_take : path = (termSubTree t ρ₀ cont).deepPath.take path.length)
      (_hfreeLen_le : lits.length ≤ path.length)
      (_hdp_len : path.length ≤ (termSubTree t ρ₀ cont).deepPath.length),
    (termSubTree t ρ₀ cont).deepPath.drop lits.length =
      (cont (processClauseLits lits path ρ₀ σ).2.1).deepPath := by
  intros t ρ₀ σ cont hdistinct path lits hlits_len hlits_match hpath hlits_le_path hpath_le_depth;
  induction' t with l rest ih generalizing ρ₀ σ cont path lits;
  · cases lits with
    | nil => simp [termSubTree, processClauseLits]
    | cons => simp at hlits_len;
  · by_cases hfree : l.var ∈ ρ₀.freeVars;
    · obtain ⟨b, hb⟩ : ∃ b : Bool, (termSubTree (l :: rest) ρ₀ cont).deepPath = (l.var, b) :: (termSubTree rest (Function.update ρ₀ l.var (some b)) cont).deepPath :=
        termSubTree_deepPath_head_free l rest ρ₀ cont hfree
      obtain ⟨lits_hd, lits_tl, hlits⟩ : ∃ lits_hd lits_tl, lits = lits_hd :: lits_tl ∧ lits_hd.1 = l := by
        rcases lits <;> simp +decide [ List.filter_cons ] at *;
        · grind;
        · simpa [ hfree ] using hlits_match 0 (by omega);
      obtain ⟨path_hd, path_tl, hpath⟩ : ∃ path_hd path_tl, path = (l.var, b) :: path_tl ∧ path_hd = (l.var, b) := by
        rcases path with ( _ | ⟨ x, _ | ⟨ y, path ⟩ ⟩ ) <;> simp +decide [ hb ] at hlits_le_path hpath_le_depth ⊢;
        · grind;
        · grind;
        · grind;
      specialize ih ( Function.update ρ₀ l.var ( some b ) ) ( Function.update σ l.var ( some ( !l.neg ) ) ) cont ( by
        exact List.pairwise_cons.mp hdistinct |>.2 ) path_tl lits_tl ( by
        simp +decide [ hlits, hfree ] at hlits_len ⊢;
        convert hlits_len using 2;
        apply filter_free_update_eq;
        exact fun x hx => by have := List.pairwise_cons.mp hdistinct; exact fun h => this.1 x hx <| by simp +decide [ h ] ; ) ( by
        all_goals generalize_proofs at *;
        intro k hk;
        convert hlits_match ( k + 1 ) ( by
          grind ) using 1
        generalize_proofs at *;
        · simp +decide [ hlits ];
        · all_goals generalize_proofs at *;
          simp +decide [ hfree ];
          congr! 1;
          refine' List.filter_congr fun x hx => _;
          by_cases h : x.var = l.var <;> simp +decide [ h ];
          · exact absurd ( List.pairwise_cons.mp hdistinct |>.1 x hx ) ( by simp +decide [ h ] );
          · simp +decide [ Restriction.freeVars, Function.update_apply, h ] ) ( by
        grind +ring ) ( by
        grind ) ( by
        grind );
      rw [ hlits.1, hb ];
      rw [ hpath.1 ];
      rw [ processClauseLits ];
      simp +decide [ hlits.2 ] at * ; tauto;
    · simp +decide [ termSubTree_cons_nonfree _ _ _ _ hfree ] at *;
      grind
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
set_option maxHeartbeats 1600000 in
private lemma canonicalPath_preserve_processClauseLits {n : ℕ} (f : DNF n)
    (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n)
    (hcanon : IsCanonicalPath f ρ₀ path)
    (_hmatch : ∀ (k : ℕ) (hk : k < min lits.length path.length),
      (lits[k]'(by omega)).1.var = (path[k]'(by omega)).1)
    -- Extra context for the proof:
    (t : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) = some t)
    (hnd_t : ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup_t : t.Nodup)
    (hdepth : path.length ≤ (canonicalDTree f ρ₀).depth)
    (hlits_eq : lits = (t.zipIdx).filter (fun p => decide (p.1.var ∈ ρ₀.freeVars))) :
    IsCanonicalPath f (processClauseLits lits path ρ₀ σ).2.1
        (processClauseLits lits path ρ₀ σ).1 ∧
    (processClauseLits lits path ρ₀ σ).1.length ≤
      (canonicalDTree f (processClauseLits lits path ρ₀ σ).2.1).depth := by
  have hrem := processClauseLits_fst_eq_drop lits path ρ₀ σ
  by_cases hge : lits.length ≥ path.length
  · -- All path entries consumed; remaining path is []
    have : min lits.length path.length = path.length := Nat.min_eq_right (by omega)
    rw [hrem, this, List.drop_length]
    exact ⟨by simp [IsCanonicalPath], Nat.zero_le _⟩
  · -- All lits consumed; remaining path = path.drop lits.length
    push_neg at hge
    have hmin : min lits.length path.length = lits.length := Nat.min_eq_left (by omega)
    rw [hrem, hmin]
    -- Establish alive conditions
    have hpath_pos : 0 < path.length := by omega
    have hdepth_pos : 0 < (canonicalDTree f ρ₀).depth := by omega
    have h_not_all_killed : ¬ ∀ t ∈ f, Term.killedBy t ρ₀ := by
      intro hall
      have := canonicalDTree_depth_zero_of_killed f ρ₀ hall
      omega
    have h_not_fixed : ¬ ∃ t ∈ f, Term.fixedBy t ρ₀ := by
      intro ⟨t', ht', hfix'⟩
      have := canonicalDTree_depth_zero_of_fixed f ρ₀ ⟨t', ht', hfix'⟩
      omega
    -- Rewrite canonicalDTree as termSubTree
    have hdt := canonicalDTree_alive_eq_termSubTree' f ρ₀ h_not_all_killed h_not_fixed t hfind
    -- Get pairwise distinct vars for t
    have ht_pairwise : t.Pairwise (fun l₁ l₂ => l₁.var ≠ l₂.var) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij heq
      have := hnd_t t[i] (List.getElem_mem _) t[j] (List.getElem_mem _) heq
      exact absurd ((List.Nodup.getElem_inj_iff hnodup_t).mp this) (by omega)
    set cont := (fun ρ' => if decide (Term.fixedBy t ρ') then DecisionTree.leaf true
      else canonicalDTree.go f ρ₀.numFree ρ') with hcont_def
    set ρ' := (processClauseLits lits path ρ₀ σ).2.1 with hρ'_def
    have ht_mem : t ∈ f := List.mem_of_find?_eq_some hfind
    -- lits.length = |free lits of t|
    have hfree_len : (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars))).length = lits.length := by
      rw [hlits_eq, ← zipIdx_filter_length]
    -- lits match the free literals of t
    have hlits_match : ∀ k (hk : k < lits.length),
        (lits[k]'hk).1 = (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars)))[k]'(by omega) := by
      intro k hk
      have hk1 : k < (t.zipIdx.filter (fun x => decide (x.1.var ∈ ρ₀.freeVars))).length := by
        rw [← hlits_eq]; exact hk
      have hk2 : k < (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars))).length := by omega
      have := zipIdx_filter_getElem_fst t (fun l => decide (l.var ∈ ρ₀.freeVars)) k hk1 hk2
      simp only [hlits_eq] at this ⊢; exact this
    -- path = termSubTree deepPath take
    have hpath_take : path = (termSubTree t ρ₀ cont).deepPath.take path.length := by
      conv_lhs => rw [hcanon]; rw [hdt]
    -- path.length ≤ deepPath.length
    have hdp_len : path.length ≤ (termSubTree t ρ₀ cont).deepPath.length := by
      rw [← hdt]; rw [DecisionTree.length_deepPath]; exact hdepth
    -- deepPath.drop lits.length = (cont ρ').deepPath
    have hdp_drop : (canonicalDTree f ρ₀).deepPath.drop lits.length = (cont ρ').deepPath := by
      rw [hdt]
      exact processClauseLits_termSubTree_drop t ρ₀ σ cont ht_pairwise path lits
        hfree_len.symm hlits_match hpath_take (by omega) hdp_len
    -- numFree bound for ρ'
    -- All literal variables are free in ρ₀
    have hlits_free : ∀ p ∈ lits, ρ₀ p.1.var = none := by
      intro p hp
      rw [hlits_eq] at hp
      have := List.mem_filter.mp hp
      simp [Restriction.freeVars, Finset.mem_filter] at this
      exact this.2
    -- Literal variables are pairwise distinct
    have hlits_distinct : lits.Pairwise (fun p q => p.1.var ≠ q.1.var) := by
      rw [hlits_eq]
      have : t.Pairwise (fun l₁ l₂ : Literal n => l₁.var ≠ l₂.var) := by
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij heq_var
        have heq := hnd_t t[i] (List.getElem_mem _) t[j] (List.getElem_mem _) heq_var
        exact absurd ((List.Nodup.getElem_inj_iff hnodup_t).mp heq) (by omega)
      exact List.Pairwise.filter _ (by
        rw [List.pairwise_iff_getElem] at this ⊢
        intro i j hi hj hij
        rw [List.length_zipIdx] at hi hj
        rw [List.getElem_zipIdx, List.getElem_zipIdx]; simp
        exact this i j hi hj hij)
    have hfuel_ok : ρ₀.numFree ≥ ρ'.numFree + 1 := by
      have := processClauseLits_numFree_ρ_eq lits path ρ₀ σ hlits_free hlits_distinct
      rw [hmin] at this
      -- We need lits.length ≥ 1 to conclude.
      -- If lits is empty, the else branch gives trivial result
      by_cases hlits_empty : lits.length = 0
      · -- lits.length = 0 is impossible: all free lits of t = 0 means t is fixedBy ρ₀,
        -- contradicting h_not_fixed.
        exfalso; apply h_not_fixed
        have hfree_empty : (t.filter (fun l => decide (l.var ∈ ρ₀.freeVars))).length = 0 := by omega
        have ht_nk : ¬Term.killedBy t ρ₀ := by
          have := List.find?_some hfind; simp at this; exact this
        exact ⟨t, ht_mem, fun l hl => by
          have hv_not_free : l.var ∉ ρ₀.freeVars := by
            intro hfv
            have hmem : l ∈ t.filter (fun l => decide (l.var ∈ ρ₀.freeVars)) :=
              List.mem_filter.mpr ⟨hl, by simp [hfv]⟩
            exact absurd (List.length_pos_of_mem hmem) (by omega)
          simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
                     Option.isNone_iff_eq_none] at hv_not_free
          cases hv : ρ₀ l.var with
          | none => exact absurd hv hv_not_free
          | some b =>
            unfold Literal.fixedBy; rw [hv]
            congr 1
            by_contra hneq
            exact ht_nk ⟨l, hl, by
              unfold Literal.killedBy; rw [hv]; congr 1
              revert hneq; cases b <;> cases l.neg <;> simp⟩⟩
      · rw [← hρ'_def] at this; omega
    -- cont ρ' = canonicalDTree f ρ'
    have hcont_canon := cont_eq_canonicalDTree f ρ₀ t ht_mem ρ' hfuel_ok
    have hcont_dp : (cont ρ').deepPath = (canonicalDTree f ρ').deepPath :=
      congr_arg DecisionTree.deepPath hcont_canon
    -- path.drop lits.length = (deepPath.drop lits.length).take (path.length - lits.length)
    have hpath_drop_eq : List.drop lits.length path =
        ((canonicalDTree f ρ₀).deepPath.drop lits.length).take (path.length - lits.length) := by
      conv_lhs => rw [hcanon]
      exact List.drop_take
    -- Combine
    rw [hpath_drop_eq, hdp_drop, hcont_dp]
    refine ⟨?_, ?_⟩
    · -- IsCanonicalPath: take of deepPath is a take of deepPath
      simp [IsCanonicalPath, List.length_take]
    · -- depth bound: take length ≤ depth
      simp [List.length_take, DecisionTree.length_deepPath]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma processClauseLits_freeLits_pairwise_var {n : ℕ}
    (t : Term n) (ρ₀ : Restriction n) (ht_nodup : t.Nodup)
    (hnd : ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) :
    ((t.zipIdx).filter
        (fun p => decide (p.1.var ∈ ρ₀.freeVars))).Pairwise
      (fun p q : Literal n × ℕ => p.1.var ≠ q.1.var) := by
  -- First, the zipIdx is pairwise distinct in both components.
  have hzip_pairwise : t.zipIdx.Pairwise
      (fun p q : Literal n × ℕ => p.1 = q.1 → p.2 ≠ q.2) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_zipIdx] at hi hj
    rw [List.getElem_zipIdx, List.getElem_zipIdx]
    intro _; simp; omega
  -- Distinct literals in `t` have distinct variables under hnd.
  have ht_var_pairwise : t.Pairwise (fun l₁ l₂ : Literal n => l₁.var ≠ l₂.var) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij heq_var
    have hi_mem : t[i] ∈ t := List.getElem_mem _
    have hj_mem : t[j] ∈ t := List.getElem_mem _
    have heq : t[i] = t[j] := hnd t[i] hi_mem t[j] hj_mem heq_var
    -- But t is Nodup, so i = j, contradicting i < j.
    rw [List.nodup_iff_getElem?_ne_getElem?] at ht_nodup
    have := ht_nodup i j hij hj
    apply this
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, heq]
  -- Transport pairwise distinct vars from t to t.zipIdx.
  have hzip_var_pairwise : t.zipIdx.Pairwise
      (fun p q : Literal n × ℕ => p.1.var ≠ q.1.var) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_zipIdx] at hi hj
    rw [List.getElem_zipIdx, List.getElem_zipIdx]
    simp only
    rw [List.pairwise_iff_getElem] at ht_var_pairwise
    exact ht_var_pairwise i j hi hj hij
  -- The filter preserves pairwise-ness.
  exact List.Pairwise.filter _ hzip_var_pairwise
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma razborovEncode_go_numFree_invariant {n : ℕ}
    (f : DNF n) (w : ℕ)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup)
    (fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (hagree : ∀ v, ρ₀ v = none ↔ σ v = none)
    (hcanon : IsCanonicalPath f ρ₀ path)
    (hdepth : path.length ≤ (canonicalDTree f ρ₀).depth)
    (hfuel : path.length < fuel) :
    (razborovEncode.go f w fuel path ρ₀ σ []).1.numFree + path.length = σ.numFree := by
  induction fuel generalizing path ρ₀ σ with
  | zero => exact absurd hfuel (Nat.not_lt_zero _)
  | succ fuel ih =>
    cases path with
    | nil =>
      simp [razborovEncode.go]
    | cons step rest =>
      -- path.length = rest.length + 1 > 0, so (canonicalDTree f ρ₀).depth ≥ 1
      have hpath_pos : 0 < (step :: rest).length := Nat.succ_pos _
      have hdepth_pos : 0 < (canonicalDTree f ρ₀).depth :=
        Nat.lt_of_lt_of_le hpath_pos hdepth
      simp only [razborovEncode.go]
      -- Case split on find?
      cases hfind : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) with
      | none =>
        -- All clauses killed by ρ₀ → dtDepth = 0, contradicting hdepth_pos.
        exfalso
        have hall : ∀ t ∈ f, Term.killedBy t ρ₀ := by
          intro t ht
          have hne := (List.find?_eq_none.mp hfind) t ht
          simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not,
                     not_not] at hne
          exact hne
        have hdtd := canonicalDTree_depth_zero_of_killed f ρ₀ hall
        omega
      | some t_clause =>
        simp only []
        have ht_mem : t_clause ∈ f := List.mem_of_find?_eq_some hfind
        -- Build freeLitsIdx
        set fli := (t_clause.zipIdx).filter
          (fun p => decide (p.1.var ∈ ρ₀.freeVars)) with hfli_def
        cases hflicase : fli with
        | nil =>
          -- No free literal in t_clause under ρ₀. Then every literal of
          -- t_clause has ρ₀ fixed. Since ¬killedBy, t_clause is fixedBy ρ₀.
          -- So dtDepth(f|ρ₀) = 0, contradicting hdepth_pos.
          exfalso
          -- Extract ¬killedBy from find?.
          have hnk : ¬ Term.killedBy t_clause ρ₀ := by
            have := List.find?_eq_some_iff_append.mp hfind
            obtain ⟨h1, _⟩ := this
            simp only [decide_not, Bool.not_eq_true',
                       decide_eq_false_iff_not] at h1
            exact h1
          have hall_ne_none : ∀ l ∈ t_clause, ρ₀ l.var ≠ none := by
            intro l hl hnone
            -- Get an index of l in t_clause via getElem?.
            rw [List.mem_iff_getElem] at hl
            obtain ⟨k, hk_lt, hk_eq⟩ := hl
            -- (l, k) ∈ t_clause.zipIdx via mk_mem_zipIdx_iff_getElem?.
            have hmem_zip : (l, k) ∈ t_clause.zipIdx := by
              rw [List.mk_mem_zipIdx_iff_getElem?]
              rw [List.getElem?_eq_getElem hk_lt]
              exact Option.some_inj.mpr hk_eq
            have hmem_fli : (l, k) ∈ fli := by
              rw [hfli_def, List.mem_filter]
              refine ⟨hmem_zip, ?_⟩
              simp only [decide_eq_true_eq, Restriction.freeVars, Finset.mem_filter,
                         Finset.mem_univ, true_and]
              exact Option.isNone_iff_eq_none.mpr hnone
            rw [hflicase] at hmem_fli
            exact List.not_mem_nil hmem_fli
          -- For every literal, ρ₀ l.var = some (!l.neg) (since not none and not some l.neg).
          have hfixed : Term.fixedBy t_clause ρ₀ := by
            intro l hl
            show ρ₀ l.var = some (!l.neg)
            have hnn := hall_ne_none l hl
            -- ¬ killedBy means: not (∃ l ∈ t_clause, ρ₀ l.var = some l.neg).
            have hlk : ¬ Literal.killedBy l ρ₀ := by
              intro hk
              exact hnk ⟨l, hl, hk⟩
            unfold Literal.killedBy at hlk
            -- ρ₀ l.var ≠ none and ≠ some l.neg → = some (!l.neg)
            cases h : ρ₀ l.var with
            | none => exact absurd h hnn
            | some b =>
              cases hb : b
              · rcases Bool.eq_false_or_eq_true l.neg with hneg | hneg
                · rw [hneg]; rfl
                · rw [hneg] at hlk
                  rw [h, hb] at hlk
                  exact absurd rfl hlk
              · rcases Bool.eq_false_or_eq_true l.neg with hneg | hneg
                · rw [hneg] at hlk
                  rw [h, hb] at hlk
                  exact absurd rfl hlk
                · rw [hneg]; rfl
          have hdtd : (canonicalDTree f ρ₀).depth = 0 :=
            canonicalDTree_depth_zero_of_fixed f ρ₀ ⟨t_clause, ht_mem, hfixed⟩
          omega
        | cons fl fls =>
          simp only []
          set pcl := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ with hpcl_def
          -- Apply accumulator lemma to strip the acc argument.
          simp only [List.nil_append]
          rw [encode_go_acc f w fuel pcl.1 pcl.2.1 pcl.2.2.1 (pcl.2.2.2 ++ [(w, false)])]
          -- Key facts about pcl:
          have hfree_pcl : ∀ p ∈ (fl :: fls), ρ₀ p.1.var = none := by
            intro p hp
            have hp_fli : p ∈ fli := by rw [hflicase]; exact hp
            rw [hfli_def] at hp_fli
            have h2 := (List.mem_filter.mp hp_fli).2
            simp only [decide_eq_true_eq, Restriction.freeVars, Finset.mem_filter,
                       Finset.mem_univ, true_and] at h2
            exact Option.isNone_iff_eq_none.mp h2
          have hdistinct_pcl : (fl :: fls).Pairwise
              (fun p q : Literal n × ℕ => p.1.var ≠ q.1.var) := by
            have := processClauseLits_freeLits_pairwise_var t_clause ρ₀
              (hnodup t_clause ht_mem) (hnd t_clause ht_mem)
            rw [← hfli_def, hflicase] at this
            exact this
          -- σ.numFree after pcl:
          have hσ_pcl : pcl.2.2.1.numFree + min (fl :: fls).length (step :: rest).length =
              σ.numFree :=
            processClauseLits_numFree_σ (fl :: fls) (step :: rest) ρ₀ σ
              hagree hfree_pcl hdistinct_pcl
          -- ρ₀' agreement with σ' after pcl:
          have hagree_pcl : ∀ v, pcl.2.1 v = none ↔ pcl.2.2.1 v = none :=
            processClauseLits_freeVars_agree (fl :: fls) (step :: rest) ρ₀ σ hagree
          -- Canonical-path preservation (gives both canon and depth bound).
          -- The `hmatch` hypothesis (that each free literal's variable matches
          -- the canonical path's head variable) is a structural fact about
          -- `canonicalDTree`'s descent through `termSubTree` on the first alive
          -- clause.
          have hmatch_pcl : ∀ (k : ℕ)
              (hk : k < min (fl :: fls).length (step :: rest).length),
              ((fl :: fls)[k]'(by omega)).1.var =
              ((step :: rest)[k]'(by omega)).1 := by
            intro k hk
            have hk_path : k < (step :: rest).length := by
              simp only [lt_min_iff] at hk; exact hk.2
            have hk_flis : k < (fl :: fls).length := by
              simp only [lt_min_iff] at hk; exact hk.1
            have hk_lt_path_len : k < (canonicalDTree f ρ₀).deepPath.length := by
              rw [DecisionTree.length_deepPath]
              have hdpath := hdepth
              omega
            -- From hcanon : (step :: rest) = deepPath.take (step::rest).length,
            -- so for index k, (step::rest)[k] = deepPath[k].
            have hpath_get :
                ((step :: rest)[k]'hk_path).1 =
                ((canonicalDTree f ρ₀).deepPath[k]'hk_lt_path_len).1 := by
              have heq : (step :: rest) =
                  (canonicalDTree f ρ₀).deepPath.take (step :: rest).length := hcanon
              have hk_take : k < ((canonicalDTree f ρ₀).deepPath.take
                  (step :: rest).length).length := by
                rw [List.length_take]; omega
              have h1 : ((step :: rest)[k]'hk_path) =
                  ((canonicalDTree f ρ₀).deepPath.take (step :: rest).length)[k]'hk_take := by
                congr 1
              rw [h1, List.getElem_take]
            -- Apply the structural fact.
            have hflis_eq : (fl :: fls) =
                (t_clause.zipIdx).filter (fun p => decide (p.1.var ∈ ρ₀.freeVars)) := by
              rw [← hflicase, hfli_def]
            have hmatch :=
              canonicalDTree_deepPath_match_freeLits f ρ₀ t_clause hfind
                (hnd t_clause ht_mem) (hnodup t_clause ht_mem) k
                (fl :: fls) hflis_eq hk_flis hk_lt_path_len
            -- Combine: (fl :: fls)[k].1.var = deepPath[k].1 = (step::rest)[k].1
            exact hmatch.symm.trans hpath_get.symm
          have hpres_pcl :=
            canonicalPath_preserve_processClauseLits f (fl :: fls) (step :: rest)
              ρ₀ σ hcanon hmatch_pcl
              t_clause hfind (hnd t_clause ht_mem) (hnodup t_clause ht_mem)
              hdepth (by rw [← hflicase, hfli_def])
          have hcanon_pcl : IsCanonicalPath f pcl.2.1 pcl.1 := hpres_pcl.1
          have hdepth_pcl : pcl.1.length ≤
              (canonicalDTree f pcl.2.1).depth := hpres_pcl.2
          -- Length decomposition:
          have hlen_add : pcl.2.2.2.length + pcl.1.length ≤ (step :: rest).length :=
            processClauseLits_len_add (fl :: fls) (step :: rest) ρ₀ σ
          -- Fuel suffices for recursion:
          have hfuel_pcl : pcl.1.length < fuel := by
            have hstrict : pcl.1.length ≤ rest.length := by
              simp only [hpcl_def, processClauseLits]
              exact processClauseLits_path_le _ _ _ _
            have hlen_eq : (step :: rest).length = rest.length + 1 := rfl
            have hf : (step :: rest).length < fuel + 1 := hfuel
            omega
          -- Apply IH to the recursive call
          have hih := ih pcl.1 pcl.2.1 pcl.2.2.1 hagree_pcl hcanon_pcl hdepth_pcl hfuel_pcl
          -- Combine: we need
          --   (go f w fuel pcl.1 pcl.2.1 pcl.2.2.1 []).1.numFree + (step :: rest).length
          --     = σ.numFree
          -- from hih: (...).1.numFree + pcl.1.length = pcl.2.2.1.numFree
          -- and hσ_pcl: pcl.2.2.1.numFree + min ... = σ.numFree
          -- Need: pcl.1.length + min ((fl::fls).length) ((step::rest).length)
          --        = (step :: rest).length
          -- This is the tight version of processClauseLits_len_add; we assert
          -- it via hlen_add and the observation that when lits ≠ [] and
          -- path ≠ [], at least min(|lits|, |path|) steps are consumed, and
          -- in fact exactly min steps, with pcl.1.length = |path| - min.
          have htight : pcl.1.length + min (fl :: fls).length (step :: rest).length =
              (step :: rest).length :=
            processClauseLits_path_length_eq (fl :: fls) (step :: rest) ρ₀ σ
          show (razborovEncode.go f w fuel pcl.1 pcl.2.1 pcl.2.2.1 []).1.numFree +
              (step :: rest).length = σ.numFree
          omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma razborovEncode_fst_numFree_eq {n : ℕ} (f : DNF n) (w d : ℕ)
    (ρ : Restriction n) (s : ℕ) (hρ : IsRestriction s ρ)
    (hbad : IsBadRestriction f.eval d ρ) (hd : d ≤ s)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    IsRestriction (s - d) (razborovEncode f w d ρ).1 := by
  classical
  unfold IsRestriction at hρ ⊢
  -- Unfold razborovEncode.
  show (razborovEncode.go f w _ _ ρ ρ []).1.numFree = s - d
  set path := (canonicalDTree f ρ).deepPath.take d with hpath_def
  have hpath_len : path.length = d := razborovEncode_path_length f ρ d hbad
  -- Invariants for the go-lemma with ρ₀ = σ = ρ.
  have hagree : ∀ v, ρ v = none ↔ ρ v = none := fun _ => Iff.rfl
  -- `path` is defined as `(canonicalDTree f ρ).deepPath.take d`, so it is
  -- by construction a prefix of `deepPath` — i.e., `IsCanonicalPath`.
  have hcanon : IsCanonicalPath f ρ path := by
    show path = (canonicalDTree f ρ).deepPath.take path.length
    rw [hpath_len, hpath_def]
  -- Depth bound via `canonicalDTree_depth_ge` and `hbad`.
  have hdepth : path.length ≤ (canonicalDTree f ρ).depth := by
    rw [hpath_len]
    have h1 : dtDepth (restrictFn f.eval ρ) > d := hbad
    have h2 : (canonicalDTree f ρ).depth ≥ dtDepth (restrictFn f.eval ρ) :=
      canonicalDTree_depth_ge f ρ
    omega
  have hfuel : path.length < path.length + 1 := Nat.lt_succ_self _
  have hinv :=
    razborovEncode_go_numFree_invariant f w hnd hnodup (path.length + 1)
      path ρ ρ hagree hcanon hdepth hfuel
  -- hinv : (go ...).1.numFree + path.length = ρ.numFree
  rw [hpath_len] at hinv ⊢
  rw [hρ] at hinv
  -- hinv : (go ...).1.numFree + d = s
  omega
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma bad_count_bound {n : ℕ} (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hd : d ≤ s)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ).card ≤
    n.choose (s - d) * 2 ^ (n - (s - d)) * (4 * w) ^ d := by
  classical
  set S := (Finset.univ.filter fun ρ : Restriction n =>
      IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ) with hS_def
  -- Partition S by the γ := (razborovEncode f w d ρ).1 image.
  have hfgamma : ∀ ρ ∈ S, (razborovEncode f w d ρ).1 ∈
      (Finset.univ.filter (fun γ : Restriction n => γ.numFree = s - d)) := by
    intro ρ hρ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    obtain ⟨hsρ, hbadρ⟩ := hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact razborovEncode_fst_numFree_eq f w d ρ s hsρ hbadρ hd hnd hnodup
  rw [Finset.card_eq_sum_card_fiberwise hfgamma]
  -- Bound each fiber by (4 * w) ^ d using fiber_bound.
  have hfiber_le : ∀ γ ∈ (Finset.univ.filter
      (fun γ : Restriction n => γ.numFree = s - d)),
      (S.filter fun ρ => (razborovEncode f w d ρ).1 = γ).card ≤ (4 * w) ^ d := by
    intro γ _
    have hfib := fiber_bound f w s d hw hd hnd γ
    refine le_trans ?_ hfib
    apply Finset.card_le_card
    intro ρ hρ
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hρ.1.1, hρ.1.2, hρ.2⟩
  calc ∑ γ ∈ (Finset.univ.filter (fun γ : Restriction n => γ.numFree = s - d)),
          (S.filter fun ρ => (razborovEncode f w d ρ).1 = γ).card
      ≤ ∑ _γ ∈ (Finset.univ.filter (fun γ : Restriction n => γ.numFree = s - d)),
          (4 * w) ^ d := Finset.sum_le_sum hfiber_le
    _ = (Finset.univ.filter (fun γ : Restriction n => γ.numFree = s - d)).card *
          (4 * w) ^ d := by rw [Finset.sum_const]; ring
    _ = n.choose (s - d) * 2 ^ (n - (s - d)) * (4 * w) ^ d := by
        rw [card_filter_numFree_eq n (s - d)]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma bad_filter_empty_of_d_ge_s {n : ℕ} (f : DNF n) (d s : ℕ) (hds : s ≤ d) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ) = ∅ := by
  simp +zetaDelta at *
  exact fun ρ hρ => not_lt.mpr (le_trans (dtDepth_restrictFn_le_numFree _ _)
    (by linarith [hρ.symm]))
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma choose_mul_pow_bound {n s d : ℕ} (hs : 5 * s ≤ n) (hd : d ≤ s) :
    n.choose (s - d) * (4 * n) ^ d ≤ n.choose s * (5 * s) ^ d := by
  induction d with
  | zero => norm_num
  | succ d hd_ih =>
    have h_simp : (Nat.choose n (s - d - 1)) * (4 * n) ≤ (Nat.choose n (s - d)) * (5 * s) := by
      set m := s - d - 1 with hm_def
      have hm_succ : s - d = m + 1 := by omega
      rw [hm_succ]
      have h_eq := Nat.choose_succ_right_eq n m
      have h_mn : m ≤ n := by omega
      have h_pos : 0 < Nat.choose n m := Nat.choose_pos h_mn
      have h_sub_add : (n - m) + m = n := Nat.sub_add_cancel h_mn
      suffices h : 4 * n * (m + 1) ≤ (n - m) * (5 * s) by nlinarith [h_eq]
      have hms : m + 1 + d = s := by omega
      zify [h_mn] at h_sub_add hs ⊢
      nlinarith [hms]
    have := hd_ih ( Nat.le_of_succ_le hd )
    rw [ Nat.sub_sub ] at *
    rw [ pow_succ', pow_succ' ]
    nlinarith [ pow_pos ( show 0 < 4 * n by linarith ) d ]
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
theorem switching_lemma {n : ℕ} (hn : 0 < n) (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hs : 5 * s ≤ n)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ).card * n ^ d ≤
    numSRestrictions n s * (10 * s * w) ^ d := by
  by_cases hds : d ≤ s
  · refine le_trans (Nat.mul_le_mul_right _ (bad_count_bound f w s d hw hds hnd hnodup)) ?_
    convert Nat.mul_le_mul_right _ (choose_mul_pow_bound hs hds) |> le_trans <| ?_ using 1; ring
    rotate_left
    exact 2 ^ (n - s) * (2 * w) ^ d
    · unfold numSRestrictions; ring_nf
      norm_num [mul_assoc, mul_left_comm, ← mul_pow]
      ring_nf; norm_num [mul_assoc, mul_comm, mul_left_comm]
    · rw [show n - (s - d) = n - s + d by omega]; ring
  · rw [bad_filter_empty_of_d_ge_s f d s (by linarith)]; norm_num
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private def toDNF {n : ℕ} : DecisionTree n → DNF n
  | .leaf true  => [[]   ]
  | .leaf false => []
  | .branch v lo hi =>
    ((toDNF lo).map fun t => ⟨v, true⟩ :: t) ++
    ((toDNF hi).map fun t => ⟨v, false⟩ :: t)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private def toCNF {n : ℕ} : DecisionTree n → CNF n
  | .leaf true  => []
  | .leaf false => [[]   ]
  | .branch v lo hi =>
    ((toCNF lo).map fun c => ⟨v, false⟩ :: c) ++
    ((toCNF hi).map fun c => ⟨v, true⟩ :: c)
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
private lemma dtDepth_witness {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∃ T : DecisionTree n, T.depth ≤ dtDepth f ∧ ∀ x, T.eval x = f x := by
  classical
  let p := fun d => ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x
  have hexists : ∃ d, p d := ⟨n, buildFullDTree f 0 (fun _ => false),
    buildFullDTree_depth f 0 (Nat.zero_le n) _,
    fun x => buildFullDTree_eval f 0 (Nat.zero_le n) _ x (fun _ hi => by omega)⟩
  have hspec := Nat.find_spec hexists
  show p (dtDepth f)
  unfold dtDepth
  convert hspec using 1
end SwitchingLemma2

namespace SwitchingLemma2
variable {n : ℕ}
lemma dtDepth_le_implies_small_dnf_cnf {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ)
    (h : dtDepth f ≤ d) :
    (∃ φ : DNF n, φ.width ≤ d ∧ ∀ x, φ.eval x = f x) ∧
    (∃ ψ : CNF n, ψ.width ≤ d ∧ ∀ x, ψ.eval x = f x) := by
  obtain ⟨T, hTd, hTeval⟩ := dtDepth_witness f
  have hTd' : T.depth ≤ d := le_trans hTd h
  constructor
  · use SwitchingLemma2.toDNF T, by
      have h_width_le_depth : ∀ T : DecisionTree n, (toDNF T).width ≤ T.depth := by
        intro T;
        have h_width_induction : ∀ T : DecisionTree n, ∀ t ∈ toDNF T, t.length ≤ T.depth := by
          intro T
          induction' T with v lo hi hlo hhi;
          · cases v <;> simp +decide [ toDNF ];
          · intro t ht; unfold toDNF at ht; simp_all +decide [ DecisionTree.depth ] ;
            grind;
        have h_width_induction : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ T.depth) → List.foldr max 0 l ≤ T.depth := by
          intros l hl; induction l <;> aesop;
        exact h_width_induction fun x hx => by aesop;
      exact le_trans ( h_width_le_depth T ) hTd', by
      intro x;
      convert hTeval x using 1;
      clear hTd hTeval hTd' h;
      induction' T with v lo hi ihlo ihhi;
      · cases v <;> simp +decide [ toDNF ];
        · rfl;
        · rfl;
      · unfold DNF.eval at *; simp_all +decide [ DecisionTree.eval ] ;
        unfold toDNF; simp +decide [ *, List.any_append ] ;
        split_ifs <;> simp_all +decide [ Term.eval ];
        · simp_all +decide [ Literal.eval ];
          simp_all +decide [ List.any_eq, List.all_eq ];
        · simp_all +decide [ List.any_eq, Literal.eval ]
  · use toCNF T;
    refine' ⟨ le_trans _ hTd', fun x => _ ⟩;
    · have h_clause_length : ∀ T : DecisionTree n, ∀ c ∈ toCNF T, c.length ≤ T.depth := by
        intro T c hc
        induction' T with v lo hi ih_lo ih_hi generalizing c;
        · cases v <;> cases hc ; trivial;
          contradiction;
        · have h_clauses : ∀ c ∈ toCNF (DecisionTree.branch lo hi ih_lo), ∃ c' ∈ toCNF hi ∪ toCNF ih_lo, c = ⟨lo, false⟩ :: c' ∨ c = ⟨lo, true⟩ :: c' := by
            intro c hc; rw [ show toCNF ( DecisionTree.branch lo hi ih_lo ) = ( toCNF hi |> List.map fun c' => ⟨ lo, false ⟩ :: c' ) ++ ( toCNF ih_lo |> List.map fun c' => ⟨ lo, true ⟩ :: c' ) from rfl ] at hc; aesop;
          obtain ⟨ c', hc', rfl | rfl ⟩ := h_clauses c hc <;> simp +arith +decide [ *, DecisionTree.depth ];
          · grind;
          · grind;
      have h_foldr_le : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ T.depth) → List.foldr Max.max 0 l ≤ T.depth := by
        intros l hl; induction l <;> aesop;
      exact h_foldr_le fun x hx => by aesop;
    · rw [ ← hTeval, eq_comm ];
      have h_equiv : ∀ T : DecisionTree n, ∀ x : Fin n → Bool, T.eval x = (toCNF T).eval x := by
        intros T x; induction' T with v lo hi ih_lo ih_hi generalizing x; simp +decide [ *, CNF.eval ] ;
        · cases v <;> simp +decide [ DecisionTree.eval ];
          · exact ⟨ [ ], by tauto, by tauto ⟩;
          · exact fun t ht => by cases ht;
        · simp +decide [ *, DecisionTree.eval, CNF.eval ];
          rw [ show toCNF ( DecisionTree.branch lo hi ih_lo ) = ( toCNF hi |> List.map fun c => ⟨ lo, false ⟩ :: c ) ++ ( toCNF ih_lo |> List.map fun c => ⟨ lo, true ⟩ :: c ) by rfl ];
          split_ifs <;> simp_all +decide [ CNF.evalClause ];
          · simp +decide [ *, Literal.eval ];
            grind +splitIndPred;
          · simp +decide [ *, Literal.eval ];
            grind;
      exact h_equiv T x
end SwitchingLemma2

open Classical

def Literal.flipNeg {n : ℕ} (l : Literal n) : Literal n :=
  ⟨l.var, !l.neg⟩

@[simp]
lemma Literal.flipNeg_eval {n : ℕ} (l : Literal n) (x : Fin n → Bool) :
    l.flipNeg.eval x = !(l.eval x) := by
  simp only [Literal.flipNeg, Literal.eval]
  cases l.neg <;> simp

@[simp]
lemma Literal.flipNeg_var {n : ℕ} (l : Literal n) :
    l.flipNeg.var = l.var := rfl

lemma Literal.flipNeg_injective {n : ℕ} : Function.Injective (Literal.flipNeg (n := n)) := by
  intro l₁ l₂ h
  cases l₁; cases l₂
  simp [Literal.flipNeg] at h
  exact Literal.mk.injEq .. ▸ h

def cnfToDualDNF {n : ℕ} (ψ : CNF n) : DNF n :=
  ψ.map (fun clause => clause.map Literal.flipNeg)

def DecisionTree.negateLeaves {n : ℕ} : DecisionTree n → DecisionTree n
  | .leaf b => .leaf (!b)
  | .branch v lo hi => .branch v (negateLeaves lo) (negateLeaves hi)

@[simp]
lemma DecisionTree.negateLeaves_eval {n : ℕ} (T : DecisionTree n) (x : Fin n → Bool) :
    T.negateLeaves.eval x = !(T.eval x) := by
  induction T with
  | leaf b => simp [negateLeaves, DecisionTree.eval]
  | branch v lo hi ih_lo ih_hi =>
    simp only [negateLeaves, DecisionTree.eval]
    split <;> simp_all

@[simp]
lemma DecisionTree.negateLeaves_depth {n : ℕ} (T : DecisionTree n) :
    T.negateLeaves.depth = T.depth := by
  induction T with
  | leaf _ => simp [negateLeaves, DecisionTree.depth]
  | branch v lo hi ih_lo ih_hi =>
    simp [negateLeaves, DecisionTree.depth, ih_lo, ih_hi]

open SwitchingLemmaCNF
open SwitchingLemma2

namespace SwitchingLemmaCNF
variable {n : ℕ}
lemma cnfToDualDNF_nodup {n : ℕ} (ψ : CNF n)
    (h : ∀ c ∈ ψ, c.Nodup) :
    ∀ t ∈ cnfToDualDNF ψ, t.Nodup := by
  intro t ht
  simp only [cnfToDualDNF, List.mem_map] at ht
  obtain ⟨c, hc_mem, rfl⟩ := ht
  exact (h c hc_mem).map Literal.flipNeg_injective
end SwitchingLemmaCNF

open SwitchingLemma2

noncomputable section
namespace BernoulliCost
variable {n : ℕ}
def fixedSizeRestrs (n k : ℕ) : Finset (Restriction n) :=
  Finset.univ.filter (fun ρ : Restriction n => ρ.freeVars.card = k)
end BernoulliCost
end

noncomputable section
namespace BernoulliCost
variable {n : ℕ}
def fixedSizeRestrProb (event : Restriction n → Prop) [DecidablePred event]
    (k : ℕ) : ℝ :=
  ↑((fixedSizeRestrs n k).filter (fun ρ => event ρ)).card / ↑(fixedSizeRestrs n k).card
end BernoulliCost
end

noncomputable section
namespace BernoulliCost
variable {n : ℕ}
def binomialPMF (nn : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  ↑(nn.choose k) * p ^ k * (1 - p) ^ (nn - k)
end BernoulliCost
end

noncomputable section
namespace BernoulliCost
variable {n : ℕ}
lemma fixedSizeRestrProb_le_one (event : Restriction n → Prop)
    [DecidablePred event] (k : ℕ) :
    fixedSizeRestrProb event k ≤ 1 := by
  unfold fixedSizeRestrProb
  rcases Nat.eq_zero_or_pos (fixedSizeRestrs n k).card with h | h
  · simp [h]
  · rw [div_le_one (Nat.cast_pos.mpr h)]
    exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
end BernoulliCost
end

noncomputable section
namespace BernoulliCost
variable {n : ℕ}
lemma binomialPMF_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ binomialPMF n p k := by
  unfold binomialPMF
  apply mul_nonneg
  apply mul_nonneg
  · exact Nat.cast_nonneg _
  · exact pow_nonneg hp _
  · exact pow_nonneg (sub_nonneg.mpr hp1) _
end BernoulliCost
end

noncomputable section
namespace BernoulliCost
variable {n : ℕ}
lemma binomialPMF_sum_one (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ k ∈ Finset.range (n + 1), binomialPMF n p k = 1 := by
  unfold binomialPMF;
  have := add_pow p ( 1 - p ) n;
  simpa [ mul_assoc, mul_comm, mul_left_comm ] using this.symm
end BernoulliCost
end

noncomputable section
namespace BernoulliCost
variable {n : ℕ}
set_option maxHeartbeats 800000 in
lemma bernoulli_decompose (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (event : Restriction n → Prop) [DecidablePred event] :
    bernoulliRestrProb p event =
    ∑ k ∈ Finset.range (n + 1),
      binomialPMF n p k * fixedSizeRestrProb event k := by
  have h_card_fixedSizeRestrs : ∀ k ≤ n, (fixedSizeRestrs n k).card = Nat.choose n k * 2 ^ (n - k) := by
    intro k hk;
    -- The set of restrictions with exactly k free variables is in bijection with the set of subsets of size k from the set of n variables.
    have h_bij : (fixedSizeRestrs n k).card = (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card * 2 ^ (n - k) := by
      have h_bij : ∀ s : Finset (Fin n), s.card = k → (Finset.filter (fun ρ : Restriction n => ρ.freeVars = s) (Finset.univ : Finset (Restriction n))).card = 2 ^ (n - k) := by
        intro s hs_card
        have h_restrictions : (Finset.univ.filter (fun ρ : Restriction n => ρ.freeVars = s)).card = (Finset.univ.filter (fun ρ : Fin n → Option Bool => ∀ i, ρ i = if i ∈ s then none else some (ρ i).get!)).card := by
          refine' Finset.card_bij ( fun ρ _ => ρ ) _ _ _ <;> simp +decide [ Restriction.freeVars ];
          · intro ρ hρ i; by_cases hi : i ∈ s <;> simp_all +decide [ Finset.ext_iff ] ;
            cases h : ρ i <;> specialize hρ i <;> aesop;
          · grind;
        -- Each restriction with free variables exactly $s$ corresponds to a function from the complement of $s$ to $\{0, 1\}$.
        have h_restrictions_bij : (Finset.univ.filter (fun ρ : Fin n → Option Bool => ∀ i, ρ i = if i ∈ s then none else some (ρ i).get!)).card = (Finset.univ.filter (fun ρ : Fin n → Bool => ∀ i ∈ s, ρ i = false)).card := by
          refine' Finset.card_bij ( fun ρ _ => fun i => if i ∈ s then false else ( ρ i ).get! ) _ _ _ <;> simp +decide [ funext_iff ];
          · tauto;
          · grind;
          · intro b hb; use fun i => if i ∈ s then none else some ( b i ) ; aesop;
        have h_complement_card : (Finset.univ.filter (fun ρ : Fin n → Bool => ∀ i ∈ s, ρ i = false)).card = (Finset.univ.filter (fun ρ : {i : Fin n // i ∉ s} → Bool => True)).card := by
          refine' Finset.card_bij ( fun ρ hρ => fun i => ρ i ) _ _ _ <;> simp +decide [ Finset.mem_filter ];
          · intro a₁ ha₁ a₂ ha₂ h; ext i; by_cases hi : i ∈ s <;> simp_all +decide [ funext_iff ] ;
          · intro b; use fun i => if hi : i ∈ s then false else b ⟨ i, hi ⟩ ; aesop;
        simp_all +decide [ Finset.card_univ ];
      have h_bij : (fixedSizeRestrs n k).card = ∑ s ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)), (Finset.filter (fun ρ : Restriction n => ρ.freeVars = s) (Finset.univ : Finset (Restriction n))).card := by
        rw [ ← Finset.card_biUnion ];
        · congr with ρ ; simp +decide [ fixedSizeRestrs ];
        · exact fun s hs t ht hst => Finset.disjoint_left.mpr fun x hx hx' => hst <| by aesop;
      rw [ h_bij, Finset.sum_congr rfl fun s hs => ‹∀ s : Finset ( Fin n ), s.card = k → Finset.card { ρ : Restriction n | ρ.freeVars = s } = 2 ^ ( n - k ) › s <| Finset.mem_powersetCard.mp hs |>.2, Finset.sum_const, smul_eq_mul, mul_comm ];
    rw [ h_bij, Finset.card_powersetCard, Finset.card_fin ];
  have h_decomp : bernoulliRestrProb p event = ∑ k ∈ Finset.range (n + 1), ∑ ρ ∈ fixedSizeRestrs n k, (bernoulliRestrWeight p ρ * if event ρ then 1 else 0) := by
    rw [ Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x hx => ⟨ x.freeVars.card, x ⟩ ) _ _ _ _ <;> simp +decide [ fixedSizeRestrs ];
    · exact fun ρ => by
        have h1 : ρ.freeVars.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
        have h2 : (Finset.univ : Finset (Fin n)).card = n := by
          rw [Finset.card_univ, Fintype.card_fin]
        omega
    · exact fun b hb₁ hb₂ => ⟨ b.2, by aesop ⟩;
  have h_decomp : ∀ k ≤ n, ∑ ρ ∈ fixedSizeRestrs n k, (bernoulliRestrWeight p ρ * if event ρ then 1 else 0) = (binomialPMF n p k) * ((fixedSizeRestrs n k).filter (fun ρ => event ρ)).card / (fixedSizeRestrs n k).card := by
    intro k hk
    have h_decomp : ∀ ρ ∈ fixedSizeRestrs n k, bernoulliRestrWeight p ρ = p ^ k * ((1 - p) / 2) ^ (n - k) := by
      unfold fixedSizeRestrs at *; aesop;
    rw [ Finset.sum_congr rfl fun x hx => by rw [ h_decomp x hx ] ]
    simp_rw [ show ∀ x : Restriction n, p ^ k * ((1 - p) / 2) ^ (n - k) * (if event x then 1 else 0) =
        if event x then p ^ k * ((1 - p) / 2) ^ (n - k) else 0 from fun x => by split_ifs <;> ring ]
    rw [ Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
         h_card_fixedSizeRestrs k hk ]
    have hdenom : (↑(Nat.choose n k * 2 ^ (n - k)) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (Nat.choose_pos hk) (pow_pos (by norm_num : (0:ℕ) < 2) (n - k))).ne'
    rw [ eq_div_iff hdenom ]
    simp only [ binomialPMF ]
    push_cast
    rw [ div_pow ]
    have h2pow_ne : (2 : ℝ) ^ (n - k) ≠ 0 := by positivity
    field_simp [ h2pow_ne ]
  convert ‹bernoulliRestrProb p event = ∑ k ∈ Finset.range ( n + 1 ), ∑ ρ ∈ fixedSizeRestrs n k, bernoulliRestrWeight p ρ * if event ρ then 1 else 0› using 2;
  rw [ h_decomp _ ( Finset.mem_range_succ_iff.mp ‹_› ), fixedSizeRestrProb ] ; ring
end BernoulliCost
end

noncomputable section
namespace BernoulliCost
variable {n : ℕ}
lemma chernoff_binomial_upper_tail (nn : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∑ k ∈ (Finset.range (nn + 1)).filter (fun k : ℕ => (↑k : ℝ) > 2 * ↑nn * p),
      binomialPMF nn p k ≤ Real.exp (-(↑nn * p / 3)) := by
  by_cases h_cases : p ≤ 0.5;
  · -- Using the Chernoff bound, we have:
    have h_chernoff : (∑ k ∈ Finset.range (nn + 1), (nn.choose k) * p^k * (1 - p)^(nn - k) * Real.exp ((k - 2 * nn * p) * Real.log 2)) ≤ Real.exp (nn * p * (Real.exp (Real.log 2) - 1) - 2 * nn * p * Real.log 2) := by
      have h_chernoff : (∑ k ∈ Finset.range (nn + 1), (nn.choose k) * p^k * (1 - p)^(nn - k) * Real.exp (k * Real.log 2)) ≤ Real.exp (nn * p * (Real.exp (Real.log 2) - 1)) := by
        have h_chernoff : (∑ k ∈ Finset.range (nn + 1), (nn.choose k) * p^k * (1 - p)^(nn - k) * Real.exp (k * Real.log 2)) = (p * Real.exp (Real.log 2) + (1 - p)) ^ nn := by
          rw [ add_pow ];
          exact Finset.sum_congr rfl fun x hx => by rw [ mul_pow, ← Real.exp_nat_mul ] ; ring;
        rw [ h_chernoff, ← Real.rpow_natCast, Real.rpow_def_of_pos ( by nlinarith [ Real.add_one_le_exp ( Real.log 2 ), Real.log_pos one_lt_two ] ) ] ; ring_nf ; norm_num;
        exact le_trans ( mul_le_mul_of_nonneg_right ( Real.log_le_sub_one_of_pos ( by nlinarith [ Real.add_one_le_exp ( Real.log 2 ), Real.log_pos one_lt_two ] ) ) ( Nat.cast_nonneg _ ) ) ( by nlinarith [ Real.add_one_le_exp ( Real.log 2 ), Real.log_pos one_lt_two ] );
      convert mul_le_mul_of_nonneg_right h_chernoff ( Real.exp_nonneg ( -2 * nn * p * Real.log 2 ) ) using 1 <;> norm_num [ sub_mul, Real.exp_add, Real.exp_sub ] ; ring;
      · rw [ Finset.sum_mul _ _ _ ] ; congr ; ext ; rw [ ← Real.exp_neg ] ; ring;
      · rw [ div_eq_mul_inv, Real.exp_neg ];
    -- Simplify the exponent in the Chernoff bound.
    have h_exp_simplified : Real.exp (nn * p * (Real.exp (Real.log 2) - 1) - 2 * nn * p * Real.log 2) ≤ Real.exp (-nn * p / 3) := by
      norm_num [ Real.exp_log ] at *;
      have := Real.log_two_gt_d9 ; norm_num at this ; nlinarith [ mul_nonneg ( Nat.cast_nonneg nn ) hp.le ];
    -- Apply the Chernoff bound to the sum.
    have h_sum_bound : (∑ k ∈ Finset.range (nn + 1), (if k > 2 * nn * p then (nn.choose k) * p^k * (1 - p)^(nn - k) else 0)) ≤ Real.exp (-nn * p / 3) := by
      refine le_trans ?_ ( h_chernoff.trans h_exp_simplified );
      gcongr;
      split_ifs;
      · exact le_mul_of_one_le_right ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp.le _ ) ) ( pow_nonneg ( sub_nonneg.mpr hp1 ) _ ) ) ( Real.one_le_exp ( mul_nonneg ( sub_nonneg.mpr <| le_of_lt ‹_› ) ( Real.log_nonneg one_le_two ) ) );
      · exact mul_nonneg ( mul_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( pow_nonneg hp.le _ ) ) ( pow_nonneg ( sub_nonneg.mpr hp1 ) _ ) ) ( Real.exp_nonneg _ );
    convert h_sum_bound using 1 <;> norm_num [ Finset.sum_ite, binomialPMF ] ; ring;
  · rcases eq_or_ne nn 0 <;> simp_all +decide [ binomialPMF ];
    · norm_num [ Finset.sum_filter ];
    · have hempty : (Finset.range (nn + 1)).filter (fun k : ℕ => (↑k : ℝ) > 2 * ↑nn * p) = ∅ := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.not_mem_empty, iff_false, not_and]
        intro hk
        push_neg
        have hk_le : (k : ℝ) ≤ ↑nn := by exact_mod_cast Nat.lt_succ_iff.mp hk
        have hnn_pos : (0 : ℝ) < ↑nn := by
          have : 0 < nn := by omega
          exact_mod_cast this
        have hp_gt : (0.5 : ℝ) < p := by linarith
        nlinarith
      rw [hempty, Finset.sum_empty]; exact Real.exp_nonneg _
end BernoulliCost
end

noncomputable section
namespace BernoulliCost
variable {n : ℕ}
theorem bernoulli_restriction_cost
    (n_pos : 0 < n) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (w s : ℕ) (hw : 0 < w) (_hs : 0 < s)
    (event : Restriction n → Prop) [DecidablePred event]
    (h_fixed : ∀ k : ℕ, k ≤ n →
      fixedSizeRestrProb event k ≤ (5 * ↑k * ↑w / ↑n) ^ s) :
    bernoulliRestrProb p event ≤
      (10 * p * ↑w) ^ s + Real.exp (-(↑n * p / 3)) := by
  -- Apply h_bound to each term in the split sum.
  have h_split : bernoulliRestrProb p event ≤ (∑ k ∈ Finset.range (n + 1), if (k : ℝ) ≤ 2 * (n : ℝ) * p then binomialPMF n p k * ((10 * p * w) ^ s) else 0) + (∑ k ∈ Finset.range (n + 1), if (k : ℝ) > 2 * (n : ℝ) * p then binomialPMF n p k else 0) := by
    rw [ ← Finset.sum_add_distrib, bernoulli_decompose p hp.le hp1 event ];
    gcongr;
    split_ifs <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
    · linarith;
    · refine' mul_le_mul_of_nonneg_left _ ( binomialPMF_nonneg p hp.le hp1 _ );
      refine le_trans ( h_fixed _ (by omega) ) ?_;
      exact pow_le_pow_left₀ ( by positivity ) ( by rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ w ) ] ) _;
    · exact mul_le_of_le_one_right ( binomialPMF_nonneg p hp.le hp1 _ ) ( fixedSizeRestrProb_le_one _ _ );
  refine le_trans h_split ?_;
  refine' add_le_add _ _;
  · -- Factor out $(10 * p * w) ^ s$ from the sum.
    suffices h_factor : (∑ k ∈ Finset.range (n + 1), if (k : ℝ) ≤ 2 * (n : ℝ) * p then binomialPMF n p k else 0) ≤ 1 by
      convert mul_le_mul_of_nonneg_right h_factor ( pow_nonneg ( show 0 ≤ 10 * p * w by positivity ) s ) using 1 <;> norm_num [ Finset.sum_ite ] ; ring;
      simp +decide only [mul_comm, mul_assoc, Finset.mul_sum _ _ _];
    refine' le_trans ( Finset.sum_le_sum fun _ _ => _ ) ( binomialPMF_sum_one p hp.le hp1 |> le_of_eq );
    split_ifs <;> norm_num [ binomialPMF_nonneg p hp.le hp1 ];
  · convert chernoff_binomial_upper_tail n p hp hp1 using 1;
    rw [ Finset.sum_filter ]
end BernoulliCost
end

open SwitchingLemma2 BernoulliCost

open Classical in
attribute [local instance] Classical.propDecidable

noncomputable section
namespace SwitchingBernoulli
variable {n : ℕ}
lemma fixedSizeRestrs_card (k : ℕ) (hk : k ≤ n) :
    (fixedSizeRestrs n k).card = numSRestrictions n k := by
  have h_card : (Finset.univ.filter fun ρ : Fin n → Option Bool => (Finset.univ.filter fun i => ρ i = none).card = k).card = (Nat.choose n k) * 2^(n-k) := by
    -- Let's count the number of restrictions with exactly k free variables by considering the number of ways to choose k positions out of n to be free.
    have h_count : (Finset.univ.filter (fun ρ : Fin n → Option Bool => (Finset.univ.filter (fun i => ρ i = none)).card = k)).card = Finset.sum (Finset.powersetCard k (Finset.univ : Finset (Fin n))) (fun s => 2 ^ (n - s.card)) := by
      have h_count : Finset.univ.filter (fun ρ : Fin n → Option Bool => (Finset.univ.filter (fun i => ρ i = none)).card = k) = Finset.biUnion (Finset.powersetCard k (Finset.univ : Finset (Fin n))) (fun s => Finset.image (fun f : { i : Fin n // i ∉ s } → Bool => fun i => if h : i ∈ s then none else some (f ⟨i, h⟩)) (Finset.univ : Finset ({ i : Fin n // i ∉ s } → Bool))) := by
        ext ρ; simp [Finset.mem_biUnion, Finset.mem_image];
        constructor <;> intro h;
        · refine' ⟨ Finset.univ.filter fun i => ρ i = none, _, _ ⟩ <;> simp_all +decide [ funext_iff ];
          use fun ⟨i, hi⟩ => if h : ρ i = none then Bool.true else (ρ i).get (by
          cases h' : ρ i <;> aesop)
          generalize_proofs at *;
          grind;
        · obtain ⟨ a, ha, b, rfl ⟩ := h; simp +decide [ Finset.filter_congr, ha ] ;
      rw [ h_count, Finset.card_biUnion ];
      · refine' Finset.sum_congr rfl fun s hs => _;
        rw [ Finset.card_image_of_injective ];
        · simp +decide [ Finset.card_univ ];
        · intro f g hfg; ext i; replace hfg := congr_fun hfg i; aesop;
      · intros s hs t ht hst; simp_all +decide [ Finset.disjoint_left ] ;
        intro a x hx; contrapose! hst; ext i; replace hx := congr_fun hx i; by_cases hi : i ∈ s <;> by_cases hj : i ∈ t <;> simp_all +decide ;
    rw [ h_count, Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ Finset.card_univ ];
  convert h_card using 1;
  convert Finset.card_image_of_injective _ ( show Function.Injective ( fun ρ : Restriction n => fun i => ρ i ) from fun a b h => by funext i; exact congr_fun h i ) using 2;
  ext; simp [fixedSizeRestrs];
  convert Iff.rfl;
  ext; simp [Restriction.freeVars]
end SwitchingBernoulli
end

noncomputable section
namespace SwitchingBernoulli
variable {n : ℕ}
lemma fixedSizeRestrs_filter_bad_eq (f : (Fin n → Bool) → Bool) (d k : ℕ) :
    ((fixedSizeRestrs n k).filter (fun ρ => dtDepth (restrictFn f ρ) > d)).card =
    (Finset.univ.filter (fun ρ : Restriction n =>
      IsRestriction k ρ ∧ IsBadRestriction f d ρ)).card := by
  congr 1 with ρ ; simp +decide [ IsRestriction, IsBadRestriction ] ;
  simp +decide [ fixedSizeRestrs, Restriction.numFree ]
end SwitchingBernoulli
end

noncomputable section
namespace SwitchingBernoulli
variable {n : ℕ}
lemma switching_fixedSize_bound_small (f : DNF n) (w k d : ℕ)
    (hn : 0 < n) (hw : f.width ≤ w)
    (hk : 5 * k ≤ n)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    fixedSizeRestrProb (fun ρ => dtDepth (restrictFn f.eval ρ) > d) k ≤
    (10 * ↑k * ↑w / ↑n) ^ d := by
  convert SwitchingLemma2.switching_lemma hn f w k d hw hk hnd hnodup using 1;
  rw [ fixedSizeRestrProb ];
  rw [ div_pow, div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ fixedSizeRestrs_card ];
  · rw [ mul_comm, fixedSizeRestrs_filter_bad_eq, fixedSizeRestrs_card ];
    · grind +qlia;
    · linarith;
  · refine' ⟨ fun i => if i.val < k then none else some Bool.true, _ ⟩ ; simp +decide [ fixedSizeRestrs ];
    rw [ show ( Restriction.freeVars fun i : Fin n => if ( i : ℕ ) < k then none else some true ) = Finset.univ.filter ( fun i : Fin n => ( i : ℕ ) < k ) from ?_ ];
    · rw [ Finset.card_eq_of_bijective ];
      use fun i hi => ⟨ i, by linarith ⟩;
      · grind +splitIndPred;
      · grind +qlia;
      · grind +extAll;
    · ext i; simp [Restriction.freeVars];
  · positivity
end SwitchingBernoulli
end

noncomputable section
namespace SwitchingBernoulli
variable {n : ℕ}
lemma switching_fixedSize_bound (f : DNF n) (w k d : ℕ)
    (hn : 0 < n) (hw : f.width ≤ w) (hw_pos : 0 < w)
    (_hk : k ≤ n)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    fixedSizeRestrProb (fun ρ => dtDepth (restrictFn f.eval ρ) > d) k ≤
    (10 * ↑k * ↑w / ↑n) ^ d := by
  -- We split into two cases: $5k \le n$ and $5k > n$.
  by_cases h_case : 5 * k ≤ n;
  · exact switching_fixedSize_bound_small f w k d hn hw h_case hnd hnodup;
  · exact le_trans ( fixedSizeRestrProb_le_one _ _ ) ( one_le_pow₀ ( by rw [ le_div_iff₀ ] <;> norm_cast ; nlinarith ) )
end SwitchingBernoulli
end

noncomputable section
namespace SwitchingBernoulli
variable {n : ℕ}
lemma switching_fixedSize_bound_rescaled (f : DNF n) (w k d : ℕ)
    (hn : 0 < n) (hw : f.width ≤ w) (hw_pos : 0 < w)
    (hk : k ≤ n)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    fixedSizeRestrProb (fun ρ => dtDepth (restrictFn f.eval ρ) > d) k ≤
    (5 * ↑k * ↑(2 * w) / ↑n) ^ d := by
  have h := switching_fixedSize_bound f w k d hn hw hw_pos hk hnd hnodup
  convert h using 2
  push_cast
  ring
end SwitchingBernoulli
end

noncomputable section
namespace SwitchingBernoulli
variable {n : ℕ}
theorem switching_bernoulli_dtDepth_dnf (f : DNF n) (w : ℕ)
    (hw : f.width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1)
    (t : ℕ) :
    bernoulliRestrProb p
      (fun ρ => dtDepth (restrictFn f.eval ρ) > t) ≤
    (1 / 2 : ℝ) ^ t + Real.exp (-(↑n * p / 3)) := by
  by_cases ht : t = 0;
  · convert bernoulliRestrProb_le_one' p hp_pos.le hp1 _ |> le_trans <| ?_ using 1 ; norm_num [ ht ];
    positivity;
  · have := bernoulli_restriction_cost hn p hp_pos hp1 ( 2 * w ) t ( by positivity ) ( by positivity ) ( fun ρ => dtDepth ( restrictFn f.eval ρ ) > t ) ?_;
    · refine le_trans this ?_;
      exact add_le_add ( pow_le_pow_left₀ ( by positivity ) ( by rw [ le_div_iff₀ ( by positivity ) ] at hp_le; push_cast at *; nlinarith [ show ( w : ℝ ) ≥ 1 by norm_cast ] ) _ ) le_rfl;
    · intro k hk;
      convert switching_fixedSize_bound_rescaled f w k t hn hw hw_pos hk hnd hnodup using 1
end SwitchingBernoulli
end

open BoolCircuit SwitchingLemma2 SwitchingBernoulli

open Classical in
attribute [local instance] Classical.propDecidable

noncomputable section
namespace LMN
variable {n : ℕ}
lemma bernoulliRestrProb_mono (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Restriction n → Prop) [DecidablePred A] [DecidablePred B]
    (h : ∀ ρ, A ρ → B ρ) :
    bernoulliRestrProb p A ≤ bernoulliRestrProb p B := by
  unfold bernoulliRestrProb
  apply Finset.sum_le_sum
  intro ρ _
  by_cases ha : A ρ
  · simp [ha, h ρ ha]
  · simp [ha]; split_ifs <;> simp [bernoulliRestrWeight_nonneg' p hp hp1 ρ]
end LMN
end

noncomputable section
namespace LMN
variable {n : ℕ}
theorem switching_bernoulli_gate_to_cnf (g : DNF n) (w l : ℕ)
    (hw : g.width ≤ w) (hw_pos : 0 < w)
    (hnd : ∀ t ∈ g, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ g, t.Nodup)
    (hn : 0 < n)
    (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1) :
    bernoulliRestrProb p
      (fun ρ => ¬ ∃ ψ : CNF n, ψ.width ≤ l ∧ ∀ x, ψ.eval x = restrictFn g.eval ρ x) ≤
    (1 / 2 : ℝ) ^ l + Real.exp (-(↑n * p / 3)) := by
  -- The event "no width-l CNF exists" implies "dtDepth > l"
  apply le_trans _ (switching_bernoulli_dtDepth_dnf g w hw hw_pos hnd hnodup hn p hp_pos hp_le hp1 l)
  apply bernoulliRestrProb_mono p hp_pos.le hp1
  intro ρ h_no_cnf
  -- If dtDepth(g|_ρ) ≤ l, then by dtDepth_le_implies_small_dnf_cnf,
  -- there exists a width-≤-l CNF. Contradiction.
  by_contra h_not_gt
  push_neg at h_not_gt
  exact h_no_cnf (dtDepth_le_implies_small_dnf_cnf _ l h_not_gt).2
end LMN
end
