import TCSlib.BooleanAnalysis.Circuit
import Mathlib

/-!
# Håstad's Switching Lemma — Razborov's Decision-Tree Path Encoding

An implementation of Håstad's Switching Lemma (1987) via Razborov's proof.

## Encoding strategy

The encoding maps a bad restriction ρ to (γ, aux):

1. Build the canonical decision tree for f|ρ (queries first free variable
   of first alive clause at each node).
2. Extract the deepest root-to-leaf path (length = tree depth ≥ dtDepth > d).
3. Take the first d steps of this path.
4. For each step, identify the clause and literal position by simulating
   the canonical DT's branching. Fix each variable to its **satisfying**
   direction (not the path direction) to build γ. Record literal positions
   within clauses as auxiliary data.

The simulation maintains two restrictions: ρ₀ follows the path directions
(to match canonical DT branching), while σ (= γ) follows satisfying
directions.

## Main result

`switching_lemma`: If `f` is a non-contradictory DNF of width ≤ `w` and `ρ` is a
uniformly random `s`-restriction with `5s ≤ n`, then:

  `#{bad s-restrictions} · nᵈ ≤ numSRestrictions n s · (10 · s · w)ᵈ`

## References

* J. Håstad, *Computational Limitations of Small-Depth Circuits*, MIT Press, 1987.
* A. Razborov, simplified proof of the switching lemma.
* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014.
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

private lemma list_any_eq_false {α : Type*} {l : List α} {p : α → Bool}
    (h : ∀ x ∈ l, p x = false) : l.any p = false := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.any_cons, h hd (by simp), ih (fun x hx => h x (by simp [hx])),
               Bool.false_or]

private lemma list_all_eq_false_of_mem {α : Type*} {l : List α} {p : α → Bool}
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

/-! ## Canonical decision tree -/

private lemma numFree_update_lt {n : ℕ} (ρ : Restriction n) (v : Fin n) (b : Bool)
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

private lemma exists_free_of_not_killed_not_fixed {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (h1 : ¬∀ t ∈ f, Term.killedBy t ρ) (h2 : ¬∃ t ∈ f, Term.fixedBy t ρ) :
    ∃ v : Fin n, v ∈ ρ.freeVars := by
  by_contra hall
  push_neg at hall
  apply h1; intro t ht
  by_contra ht_nk
  apply h2; refine ⟨t, ht, fun l hl => ?_⟩
  have hass : l.var ∉ ρ.freeVars := hall l.var
  simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and] at hass
  simp only [Option.isNone_iff_eq_none] at hass
  cases hv : ρ l.var with
  | none => exact absurd hv hass
  | some b =>
    show ρ l.var = some (!l.neg)
    by_cases hbl : b = l.neg
    · exfalso; exact ht_nk ⟨l, hl, by simp only [Literal.killedBy]; rw [hv, hbl]⟩
    · rw [hv]; congr 1
      cases b <;> cases hln : l.neg
      · exfalso; rw [hln] at hbl; exact hbl rfl
      · rfl
      · rfl
      · exfalso; rw [hln] at hbl; exact hbl rfl

noncomputable def selectBranchVar {n : ℕ} (f : DNF n) (ρ : Restriction n) :
    Option (Fin n) :=
  match f.find? (fun t => decide (¬Term.killedBy t ρ)) with
  | none => none
  | some t =>
    match t.find? (fun l => decide (l.var ∈ ρ.freeVars)) with
    | none => none
    | some l => some l.var

private lemma selectBranchVar_spec {n : ℕ} (f : DNF n) (ρ : Restriction n)
    (h1 : ¬∀ t ∈ f, Term.killedBy t ρ) (h2 : ¬∃ t ∈ f, Term.fixedBy t ρ) :
    ∃ v, selectBranchVar f ρ = some v ∧ v ∈ ρ.freeVars := by
  unfold selectBranchVar
  have h1' : f.find? (fun t => decide (¬Term.killedBy t ρ)) ≠ none := by
    intro habs; rw [List.find?_eq_none] at habs
    push_neg at h1; obtain ⟨t, htm, htnk⟩ := h1
    exact (habs t htm) (by simp [htnk])
  obtain ⟨t, ht_eq⟩ : ∃ t, f.find? (fun t => decide (¬Term.killedBy t ρ)) = some t := by
    cases hf : f.find? (fun t => decide (¬Term.killedBy t ρ)) with
    | none => exact absurd hf h1'
    | some t => exact ⟨t, rfl⟩
  simp only [ht_eq]
  have ht_nk : ¬Term.killedBy t ρ := by
    have := List.find?_some ht_eq; simp at this; exact this
  have ht_mem : t ∈ f := List.mem_of_find?_eq_some ht_eq
  have ht_nf : ¬Term.fixedBy t ρ := fun hf => h2 ⟨t, ht_mem, hf⟩
  have h3 : t.find? (fun l => decide (l.var ∈ ρ.freeVars)) ≠ none := by
    intro hall
    rw [List.find?_eq_none] at hall
    apply ht_nf; intro l hl
    have : l.var ∉ ρ.freeVars := by have := hall l hl; simp at this; exact this
    simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
               Option.isNone_iff_eq_none] at this
    cases hv : ρ l.var with
    | none => exact absurd hv this
    | some b =>
      by_cases hbl : b = l.neg
      · exfalso; exact ht_nk ⟨l, hl, by simp only [Literal.killedBy]; rw [hv, hbl]⟩
      · show ρ l.var = some (!l.neg); rw [hv]; congr 1
        cases b <;> simp_all
  obtain ⟨l, hl_eq⟩ : ∃ l, t.find? (fun l => decide (l.var ∈ ρ.freeVars)) = some l := by
    cases hf : t.find? (fun l => decide (l.var ∈ ρ.freeVars)) with
    | none => exact absurd hf h3
    | some l => exact ⟨l, rfl⟩
  simp only [hl_eq]
  exact ⟨l.var, rfl, by have := List.find?_some hl_eq; simp at this; exact this⟩

/-- Build a complete sub-tree for a term, querying all its free variables
    in order. At each leaf, call the continuation with the updated restriction.

    This matches the paper: "Form the complete, depth-d₁ decision tree over
    those variables, considering the variables in order." Variables already
    fixed under ρ are skipped (they contribute no branching). -/
private noncomputable def termSubTree {n : ℕ} :
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

/-- The canonical decision tree for f|ρ, following Razborov's construction.

    At each stage: find the first term not killed by the current restriction.
    Build a **complete** sub-tree over all of that term's free variables
    (querying them in list order). The unique leaf where the term is fixed
    (all literals satisfied) becomes a 1-leaf. Every other leaf (the term is
    killed) continues recursively to the next clause.

    This ensures each path through a clause's sub-tree queries **all** of
    that clause's free variables before moving on — the key structural
    property needed for the encoding round-trip. -/
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
          -- Build complete sub-tree for t, querying all its free variables.
          -- At leaves: if t is now fixed → 1-leaf; otherwise → continue.
          termSubTree t ρ (fun ρ' =>
            if decide (Term.fixedBy t ρ') then .leaf true
            else go f fuel ρ')

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

/-- `termSubTree` preserves the semantics: evaluating the sub-tree on input `x`
    is the same as assigning each free variable in `lits` according to `x` and
    then evaluating the continuation. -/
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
    · -- l.var free: branch
      rename_i hfree
      simp only [DecisionTree.eval]
      cases hxv : x l.var <;> simp [hxv, ih] <;>
        congr 1 <;> simp [List.foldl, hfree, hxv]
    · -- l.var not free: skip
      rename_i hnfree
      rw [ih]; congr 1; simp [List.foldl, hnfree]

/-- After `termSubTree` assigns all free variables from `x`, the resulting
    restriction extends the same as the original: `ρ'.extend x = ρ.extend x`. -/
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

/-- The foldl in `termSubTree_eval` preserves non-none: once `ρ v ≠ none`,
    no step can set it to `none` (each step either sets to `some` or is identity). -/
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

/-- The foldl in `termSubTree_eval` strictly decreases `numFree` when at least
    one literal in the list has a free variable. -/
private lemma termSubTree_foldl_numFree_lt {n : ℕ}
    (lits : List (Literal n)) (ρ : Restriction n) (x : Fin n → Bool)
    (l : Literal n) (hl : l ∈ lits) (hfree : l.var ∈ ρ.freeVars) :
    (lits.foldl (fun (ρ' : Restriction n) (lit : Literal n) =>
      if lit.var ∈ Restriction.freeVars ρ' then Function.update ρ' lit.var (some (x lit.var))
      else ρ') ρ).numFree < ρ.numFree := by
  -- Opaque iff: membership in freeVars iff the restriction is none at v
  have fv_iff : ∀ (R : Restriction n) (w : Fin n), w ∈ R.freeVars ↔ R w = none := by
    intro R w
    unfold Restriction.freeVars
    simp [Option.isNone_iff_eq_none]
  -- Key: for any restriction R with l.var free, after the foldl, l.var is fixed
  have key : ∀ (lits' : List (Literal n)) (R : Restriction n),
      l ∈ lits' → R l.var = none →
      (lits'.foldl (fun ρ' lit =>
        if lit.var ∈ Restriction.freeVars ρ' then
          Function.update ρ' lit.var (some (x lit.var))
        else ρ') R) l.var ≠ none := by
    intro lits'
    induction lits' with
    | nil => intro R hl' _; cases hl'
    | cons hd tl ih =>
      intro R hl' hfree'
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hl' with rfl | htl
      · -- hd = l: fixes hd.var, preserved by tail
        apply termSubTree_foldl_preserves_nonnone
        rw [if_pos ((fv_iff R l.var).mpr hfree')]
        simp [Function.update_apply]
      · -- l ∈ tl: either hd.var is free in R (updated) or not
        by_cases hd_free : hd.var ∈ R.freeVars
        · rw [if_pos hd_free]
          by_cases heq : l.var = hd.var
          · -- l.var = hd.var: directly fixed
            apply termSubTree_foldl_preserves_nonnone
            rw [heq]; simp [Function.update_apply]
          · -- l.var ≠ hd.var: still free in updated R
            apply ih _ htl
            rw [Function.update_apply, if_neg heq]; exact hfree'
        · rw [if_neg hd_free]
          exact ih _ htl hfree'
  have hne_at_l : (lits.foldl (fun (ρ' : Restriction n) (lit : Literal n) =>
      if lit.var ∈ Restriction.freeVars ρ' then Function.update ρ' lit.var (some (x lit.var))
      else ρ') ρ) l.var ≠ none := key lits ρ hl ((fv_iff ρ l.var).mp hfree)
  -- subset
  have hsub : (lits.foldl (fun (ρ' : Restriction n) (lit : Literal n) =>
      if lit.var ∈ Restriction.freeVars ρ' then Function.update ρ' lit.var (some (x lit.var))
      else ρ') ρ).freeVars ⊆ ρ.freeVars := by
    intro v hv
    rw [fv_iff] at hv ⊢
    by_contra h
    exact (termSubTree_foldl_preserves_nonnone lits ρ x v h) hv
  have hne_mem : l.var ∉ (lits.foldl (fun (ρ' : Restriction n) (lit : Literal n) =>
      if lit.var ∈ Restriction.freeVars ρ' then Function.update ρ' lit.var (some (x lit.var))
      else ρ') ρ).freeVars := by
    rw [fv_iff]; exact hne_at_l
  exact Finset.card_lt_card (hsub.ssubset_of_ne (fun heq => hne_mem (heq ▸ hfree)))

private lemma canonicalDTree_go_correct {n : ℕ} (f : DNF n) (fuel : ℕ) (ρ : Restriction n)
    (hfuel : ρ.numFree < fuel) :
    ∀ x, (canonicalDTree.go f fuel ρ).eval x = restrictFn f.eval ρ x := by
  intro x
  induction fuel generalizing ρ with
  | zero => omega
  | succ k ih =>
    simp only [canonicalDTree.go]
    split
    · -- all killed
      rename_i h1
      simp only [DecisionTree.eval, restrictFn, DNF.eval]; symm
      apply list_any_eq_false; intro t ht
      show t.eval (ρ.extend x) = false
      obtain ⟨l, hl_mem, hl_killed⟩ := h1 t ht
      simp only [Term.eval]
      exact list_all_eq_false_of_mem hl_mem (Literal.killedBy_eval_false l ρ hl_killed x)
    · split
      · -- some fixed
        rename_i _ h2
        simp only [DecisionTree.eval, restrictFn, DNF.eval]
        obtain ⟨t, ht_mem, ht_fixed⟩ := h2; symm; rw [List.any_eq_true]
        refine ⟨t, ht_mem, ?_⟩; show t.eval (ρ.extend x) = true
        rw [Term.eval, List.all_eq_true]
        exact fun l hl => Literal.fixedBy_eval_true l ρ (ht_fixed l hl) x
      · -- alive
        rename_i h1 h2; split
        · rename_i hfind; exfalso; apply h1; intro t ht
          by_contra htk; rw [List.find?_eq_none] at hfind
          exact (hfind t ht) (by simp [htk])
        · rename_i t hfind
          rw [termSubTree_eval]
          -- Let ρ' be the foldl result, via a have (not set), to keep goal normal
          have hext : (t.foldl (fun (ρ' : Restriction n) l =>
              if l.var ∈ ρ'.freeVars then Function.update ρ' l.var (some (x l.var))
              else ρ') ρ).extend x = ρ.extend x := termSubTree_extend_eq t ρ x
          show (if decide (Term.fixedBy t (t.foldl _ ρ)) then DecisionTree.leaf true
            else canonicalDTree.go f k (t.foldl _ ρ)).eval x = restrictFn f.eval ρ x
          split
          · -- t fixed under the foldl
            rename_i ht_fixed
            simp only [DecisionTree.eval, restrictFn, DNF.eval]
            have ht_fixed' := of_decide_eq_true ht_fixed; symm; rw [List.any_eq_true]
            refine ⟨t, List.mem_of_find?_eq_some hfind, ?_⟩
            show t.eval (ρ.extend x) = true
            rw [← hext, Term.eval, List.all_eq_true]
            exact fun l hl => Literal.fixedBy_eval_true l _ (ht_fixed' l hl) x
          · -- t not fixed: recurse
            rename_i ht_not_fixed
            have hres : restrictFn f.eval (t.foldl (fun (ρ' : Restriction n) l =>
                if l.var ∈ ρ'.freeVars then Function.update ρ' l.var (some (x l.var))
                else ρ') ρ) x = restrictFn f.eval ρ x := by
              simp only [restrictFn]; rw [hext]
            have hρ'_lt : (t.foldl (fun (ρ' : Restriction n) l =>
                if l.var ∈ ρ'.freeVars then Function.update ρ' l.var (some (x l.var))
                else ρ') ρ).numFree < k := by
              have hle : ρ.numFree ≤ k := Nat.lt_succ_iff.mp hfuel
              have ht_nk : ¬Term.killedBy t ρ := by
                have := List.find?_some hfind; simp at this; exact this
              have ht_nf : ¬Term.fixedBy t ρ :=
                fun hf => h2 ⟨t, List.mem_of_find?_eq_some hfind, hf⟩
              have ⟨l, hl_mem, hl_free⟩ : ∃ l ∈ t, l.var ∈ ρ.freeVars := by
                by_contra hall; push_neg at hall; apply ht_nf; intro l hl
                have hnf : ¬(l.var ∈ ρ.freeVars) := hall l hl
                have hne : ρ l.var ≠ none := by
                  intro hn
                  apply hnf
                  simp [Restriction.freeVars, Option.isNone_iff_eq_none, hn]
                have hnk_l : ρ l.var ≠ some l.neg := fun hk => ht_nk ⟨l, hl, hk⟩
                show ρ l.var = some (!l.neg)
                cases hv : ρ l.var with
                | none => exact absurd hv hne
                | some b =>
                  have hbne : b ≠ l.neg := by
                    intro heq
                    exact hnk_l (by rw [hv, heq])
                  cases b <;> cases hln : l.neg <;> simp_all
              exact lt_of_lt_of_le
                (termSubTree_foldl_numFree_lt t ρ x l hl_mem hl_free) hle
            rw [ih _ hρ'_lt, hres]

lemma canonicalDTree_correct {n : ℕ} (f : DNF n) (ρ : Restriction n) :
    ∀ x, (canonicalDTree f ρ).eval x = restrictFn f.eval ρ x :=
  canonicalDTree_go_correct f _ ρ (Nat.lt_succ_of_le (le_refl _))

/-! ## Depth bounds -/

lemma depth_ge_dtDepth {n : ℕ} {f : (Fin n → Bool) → Bool}
    (T : DecisionTree n) (heval : ∀ x, T.eval x = f x) :
    T.depth ≥ dtDepth f := by
  unfold dtDepth
  exact Nat.find_min' _ ⟨T, le_refl _, heval⟩

lemma canonicalDTree_depth_ge {n : ℕ} (f : DNF n) (ρ : Restriction n) :
    (canonicalDTree f ρ).depth ≥ dtDepth (restrictFn f.eval ρ) :=
  depth_ge_dtDepth _ (canonicalDTree_correct f ρ)

/-! ## dtDepth upper bound -/

private lemma dtDepth_restrictFn_le_numFree {n : ℕ} (f : (Fin n → Bool) → Bool)
    (ρ : Restriction n) :
    dtDepth (restrictFn f ρ) ≤ ρ.numFree := by
  -- Build a decision tree querying each free variable of ρ; its depth is ρ.numFree.
  suffices h : ∀ (k : ℕ) (ρ : Restriction n), ρ.numFree = k →
      ∃ T : DecisionTree n, T.depth ≤ k ∧ ∀ x, T.eval x = restrictFn f ρ x by
    obtain ⟨T, hT_d, hT_e⟩ := h ρ.numFree ρ rfl
    exact le_trans (depth_ge_dtDepth T hT_e) hT_d
  intro k
  induction k with
  | zero =>
    intro ρ hρ
    -- No free variables: ρ.extend x is constant in x
    refine ⟨.leaf (f (fun i => (ρ i).getD false)), by simp [DecisionTree.depth], ?_⟩
    intro x
    simp only [DecisionTree.eval, restrictFn]
    congr 1
    funext i
    simp only [Restriction.extend]
    have hemp : ρ.freeVars = ∅ := Finset.card_eq_zero.mp hρ
    have hne : ρ i ≠ none := by
      intro hn
      have : i ∈ ρ.freeVars := by
        simp [Restriction.freeVars, Option.isNone_iff_eq_none, hn]
      rw [hemp] at this
      exact absurd this (Finset.notMem_empty i)
    cases h : ρ i with
    | none => exact absurd h hne
    | some _ => rfl
  | succ k ih =>
    intro ρ hρ
    have hne : ρ.freeVars.Nonempty := Finset.card_pos.mpr (by omega)
    obtain ⟨v, hv⟩ := hne
    have hv_none : ρ v = none := by
      simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
        Option.isNone_iff_eq_none] at hv
      exact hv
    -- Updating v preserves all other free variables; numFree decreases by 1
    have hupd_numFree : ∀ b : Bool, (Function.update ρ v (some b)).numFree = k := by
      intro b
      have herase : (Function.update ρ v (some b)).freeVars = ρ.freeVars.erase v := by
        ext i
        simp only [Restriction.freeVars, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, Option.isNone_iff_eq_none, Function.update_apply]
        by_cases hi : i = v
        · subst hi; simp
        · simp [hi]
      show (Function.update ρ v (some b)).freeVars.card = k
      rw [herase, Finset.card_erase_of_mem hv]
      show ρ.freeVars.card - 1 = k
      omega
    obtain ⟨Tf, hTf_d, hTf_e⟩ := ih (Function.update ρ v (some false)) (hupd_numFree false)
    obtain ⟨Tt, hTt_d, hTt_e⟩ := ih (Function.update ρ v (some true)) (hupd_numFree true)
    refine ⟨.branch v Tf Tt, ?_, ?_⟩
    · simp only [DecisionTree.depth]; omega
    · intro x
      -- Key: (Function.update ρ v (some b)).extend x = ρ.extend x when x v = b
      have hext : ∀ (b : Bool), x v = b →
          (Function.update ρ v (some b)).extend x = ρ.extend x := by
        intro b hxv
        funext i
        simp only [Restriction.extend, Function.update_apply]
        by_cases hi : i = v
        · subst hi; simp [hv_none, hxv]
        · simp [hi]
      simp only [DecisionTree.eval]
      cases hxv : x v with
      | false =>
        rw [if_neg (by simp [hxv])]
        rw [hTf_e x]
        simp only [restrictFn]
        rw [hext false hxv]
      | true =>
        rw [if_pos (by simp [hxv])]
        rw [hTt_e x]
        simp only [restrictFn]
        rw [hext true hxv]

/-! ========================================================================
    RAZBOROV ENCODING — Canonical Decision Tree Path
    ========================================================================

Following Razborov's proof: the encoding extracts the deepest path from
the canonical decision tree for f|ρ, takes the first d steps, and fixes
the corresponding variables to their satisfying directions.

**Path extraction**: Build the canonical DT for f|ρ (which queries the
first free variable of the first alive clause at each node). Extract
the deepest root-to-leaf path using `DecisionTree.deepPath`. Since ρ
is bad (dtDepth(f|ρ) > d), the canonical DT has depth > d, so the
deepest path has length > d and we can take d steps.

**Encoding**: For each of the d path steps, simulate the canonical DT
to identify the clause and literal position. The simulation tracks two
restrictions:
- `ρ₀` (path restriction): follows the actual path directions, so that
  `selectBranchVar` at each step gives the same clause/literal as the
  canonical DT.
- `σ` (output restriction γ): fixes each variable to the **satisfying**
  direction for its literal (not the path direction). This is the key
  difference between π (path values) and γ (satisfying values).

Each aux entry is `(literal_position_in_clause, path_direction)` from
alphabet `{0,...,w-1} × Bool`, interleaved with termination markers
`(w, false)` that signal clause boundaries. We use an alphabet of size
`w + 1` (positions `{0,...,w-1}` plus the termination character `w`).
The aux has d data entries plus one termination marker per clause
traversed (at most d markers, since each clause contributes ≥ 1 step). -/

/-- Find the free literals in a term under restriction ρ. -/
noncomputable def Term.freeLiterals {n : ℕ} (t : Term n) (ρ : Restriction n) :
    List (Literal n) :=
  t.filter (fun l => decide (l.var ∈ ρ.freeVars))

/-- Process one clause's free literals against the canonical DT path.
    For each free literal (in clause order), consume one path entry:
    - Fix the literal's variable to its satisfying direction in σ (building γ)
    - Track the path direction in ρ₀ (simulating canonical DT branching)
    - Record `(literal_position_in_clause, path_direction)` in aux

    Returns `(remaining_path, updated_ρ₀, updated_σ, clause_aux_data)`.

    This matches the paper: for each clause Tᵢ, we fix ALL dᵢ free variables
    to their satisfying values at once, recording positions and path directions. -/
private noncomputable def processClauseLits {n : ℕ} :
    List (Literal n × ℕ) → List (Fin n × Bool) → Restriction n → Restriction n →
    List (Fin n × Bool) × Restriction n × Restriction n × List (ℕ × Bool)
  | [], path, ρ₀, σ => (path, ρ₀, σ, [])
  | _, [], ρ₀, σ => ([], ρ₀, σ, [])
  | (l, idx) :: restLits, (_, dir) :: restPath, ρ₀, σ =>
    let r := processClauseLits restLits restPath
      (Function.update ρ₀ l.var (some dir))
      (Function.update σ l.var (some (!l.neg)))
    (r.1, r.2.1, r.2.2.1, (idx, dir) :: r.2.2.2)

private lemma processClauseLits_path_le {n : ℕ}
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

/-- The Razborov encoding: follow the deepest path in the canonical decision
    tree for f|ρ, processing **one clause at a time**.

    The canonical DT's `termSubTree` queries ALL free variables of a clause
    before moving to the next. The encoder mirrors this structure: for each
    clause, it identifies all free literals, consumes path entries for each
    one, fixes them to satisfying directions in σ, and records positions and
    path directions in aux. A termination marker `(w, false)` is emitted
    after each clause block.

    Returns `(γ, aux)` where:
    - `γ` extends `ρ` by fixing d variables to their satisfying directions
    - `aux` has clause blocks `[(idx₁, dir₁), ..., (idx_k, dir_k), (w, false)]`
      separated by termination markers `(w, false)` -/
noncomputable def razborovEncode {n : ℕ} (f : DNF n) (w d : ℕ)
    (ρ : Restriction n) : Restriction n × List (ℕ × Bool) :=
  let path := (canonicalDTree f ρ).deepPath.take d
  razborovEncode.go f w (path.length + 1) path ρ ρ []
where
  /-- Main encoding loop: find the first non-killed clause, process ALL of its
      free literals against the path (matching `termSubTree`'s traversal),
      emit a termination marker, and repeat for the next clause. -/
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
        -- Get ALL free literals of this clause with their positions
        let freeLitsIdx := (t.zipIdx).filter (fun ⟨l, _⟩ => decide (l.var ∈ ρ₀.freeVars))
        match freeLitsIdx with
        | [] => (σ, acc)
        | fl :: fls =>
          -- Process the entire clause: consume one path entry per free literal
          let r := processClauseLits (fl :: fls) path ρ₀ σ
          go f w fuel r.1 r.2.1 r.2.2.1 (acc ++ r.2.2.2 ++ [(w, false)])

/-- Decode: given `(γ, aux)` from the Razborov encoding, recover the original
    restriction ρ.

    The decoder maintains two restrictions:
    - `σ`: starts at `γ`, progressively un-fixes path variables to `none`
    - `ρ₀`: starts at `γ`, re-fixes path variables to their recorded path
      directions (mirroring the encoder's ρ₀ state for clause identification)

    For each clause block in aux:
    1. Find the first non-killed clause under `ρ₀` (same clause the encoder
       found, since killing is preserved and the clause is still fixed)
    2. Process data entries `(idx, dir)` until the termination marker
       `(w, false)`: look up literal at position `idx` in the clause,
       un-fix it in `σ`, fix it to `dir` in `ρ₀`
    3. After the termination marker, find the next clause and repeat

    Correctness relies on the encoder processing ALL free literals of each
    clause before moving on (matching `termSubTree`), which ensures:
    (1) killed-by-ρ ⇒ killed-by-γ (killing uses non-free variables)
    (2) each clause is fixed under the decoder's ρ₀ when first encountered
    (3) after processing a clause's block, it becomes killed under ρ₀
        (since the path directions collectively kill it), so the decoder
        correctly advances to the next clause -/
noncomputable def razborovDecode {n : ℕ} (f : DNF n) (w : ℕ)
    (γ : Restriction n) (aux : List (ℕ × Bool)) : Restriction n :=
  (razborovDecode.go f w (aux.length + 1) γ γ aux).1
where
  /-- Process aux entries for one clause until termination marker or end.
      The clause `t` is identified once by the caller and used for all
      entries in this block.
      Returns `(updated_σ, updated_ρ₀, remaining_aux)`. -/
  processEntries (t : Term n) (w : ℕ) :
      Restriction n → Restriction n → List (ℕ × Bool) →
      Restriction n × Restriction n × List (ℕ × Bool)
    | σ, ρ₀, [] => (σ, ρ₀, [])
    | σ, ρ₀, (idx, dir) :: rest =>
      if idx ≥ w then
        -- Termination marker: this clause block is done
        (σ, ρ₀, rest)
      else
        match t.drop idx with
        | [] => (σ, ρ₀, rest)
        | l :: _ =>
          -- Un-fix in output σ; track path direction in ρ₀
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
        -- Process all entries for this clause (until termination marker)
        let (σ', ρ₀', aux') := processEntries t w σ ρ₀ aux
        go f w fuel σ' ρ₀' aux'

/-! ### Encoding properties -/

/-- Killing is monotone w.r.t. non-free agreement: if `t` is killed by `ρ`
    and `σ` agrees with `ρ` on all non-free variables, then `t` is killed
    by `σ`. (Killing literals use non-free variables by definition.) -/
private lemma killedBy_of_nonfree_agree {n : ℕ} (t : Term n) (ρ σ : Restriction n)
    (hk : Term.killedBy t ρ) (hagree : ∀ v, ρ v ≠ none → σ v = ρ v) :
    Term.killedBy t σ := by
  obtain ⟨l, hl_mem, hl_killed⟩ := hk
  exact ⟨l, hl_mem, by rwa [Literal.killedBy, hagree _ (by simp [Literal.killedBy] at hl_killed; rw [hl_killed]; simp)]⟩

/-- `zipIdx.find?` projecting to the first component agrees with `find?`. -/
private lemma zipIdx_find_to_find {α : Type*} (l : List α) (p : α → Bool)
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

/-- If `t` is the first element of `f` satisfying `¬killedBy · ρ`, and
    `σ` agrees with `ρ` on non-free variables, and `t` is not killed by `σ`,
    then `t` is also the first element satisfying `¬killedBy · σ`. -/
private lemma first_clause_preserved {n : ℕ} (f : DNF n) (ρ σ : Restriction n)
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

/-- `processClauseLits` produces at most `2 * path.length` combined output:
    the data entries plus twice the remaining path length. This is the key
    bound for the encoding: each consumed path entry contributes 1 data entry,
    and the remaining path entries each contribute 2 (for future data + marker). -/
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

/-- Tight bound: for non-empty inputs, the data entries plus termination marker
    plus twice the remaining path is at most `2 * path.length`. This absorbs the
    `+1` for the termination marker because one path entry was consumed. -/
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

/-- Bound on `razborovEncode.go` output length: the aux data has length
    at most `acc.length + 2 * path.length`. Each clause contributes its
    data entries plus one termination marker, and the tight bound ensures
    the marker is absorbed by the consumed path entries. -/
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
      -- Case split on f.find?
      split
      · -- find? = none: returns (σ, acc)
        simp;
      · -- find? = some t: case split on freeLitsIdx
        split
        · -- freeLitsIdx = []: returns (σ, acc)
          simp;
        · -- freeLitsIdx = fl :: fls: recursive case
          -- By IH on fuel with the updated accumulator:
          next fl fls _ =>
          apply le_trans (ih _ _ _ _)
          -- Goal: (acc ++ clauseAux ++ [(w, false)]).length + 2 * path'.length
          --       ≤ acc.length + 2 * (step :: rest).length
          simp only [List.length_append, List.length_cons,
                     List.length_nil, Nat.add_zero]
          -- Apply the tight processClauseLits bound
          have := processClauseLits_tight fl fls step rest ρ₀ σ
          have : (step :: rest).length = rest.length + 1 := List.length_cons
          omega

lemma razborovEncode_aux_length_le {n : ℕ} (f : DNF n) (w d : ℕ) (ρ : Restriction n)
    (hbad : IsBadRestriction f.eval d ρ) :
    (razborovEncode f w d ρ).2.length ≤ 2 * d := by
  show (razborovEncode.go f w _ _ ρ ρ []).2.length ≤ 2 * d
  calc (razborovEncode.go f w _ _ ρ ρ []).2.length
      ≤ 0 + 2 * ((canonicalDTree f ρ).deepPath.take d).length :=
        encode_go_aux_length_bound f w _ _ ρ ρ []
    _ ≤ 2 * d := by
        have := List.length_take_le d (canonicalDTree f ρ).deepPath
        omega

/-! ### Round-trip helper lemmas -/

/-- `processClauseLits` preserves σ at variables not in the literal list. -/
private lemma processClauseLits_sigma_stable {n : ℕ}
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
      simp only [Function.update_apply, ne_eq, hne.symm, not_false_eq_true, ite_false]

/-- `processClauseLits` preserves ρ₀ at variables not in the literal list. -/
private lemma processClauseLits_rho_stable {n : ℕ}
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
      simp only [Function.update_apply, ne_eq, hne.symm, not_false_eq_true, ite_false]

/-- `processClauseLits` never makes ρ₀ become `none` at a non-free variable:
    it only sets variables to `some dir`, never to `none`. -/
private lemma processClauseLits_rho_ne_none {n : ℕ}
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
      · simp  -- v = hd.1.var: updated to some, ≠ none
      · exact hv  -- v ≠ hd.1.var: unchanged

/-- The encoder's γ preserves σ at variables that are non-free under ρ₀.
    The encoder only modifies variables found free by the filter on `ρ₀.freeVars`,
    so non-free variables are untouched in both σ and ρ₀. -/
private lemma encode_go_fst_nonfree {n : ℕ} (f : DNF n) (w : ℕ)
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
      · rfl  -- find? = none
      · -- find? = some t: need to handle the freeLitsIdx match
        -- Use `next` to name the matched term from find?
        next t _ =>
        -- Capture the filter → list equality so we can extract freeness
        generalize hfli :
          List.filter (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
            (List.zipIdx t) = fli
        match fli with
        | [] => simp
        | fl :: fls =>
          -- hfli : filter(...) = fl :: fls, so all members have free vars
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
          -- By IH (ρ₀ preserved non-none) then σ stable at v
          rw [ih _ _ _ _ (processClauseLits_rho_ne_none _ _ _ _ _ hv)]
          exact processClauseLits_sigma_stable _ _ _ _ _ hne

/-- The encoder's `go` with accumulator: `.1` is independent of `acc`, and
    `.2` prepends `acc` to the clean output. -/
private lemma encode_go_acc {n : ℕ} (f : DNF n) (w : ℕ)
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
      · simp  -- find? = none
      · split
        · simp  -- freeLitsIdx = []
        · -- fl :: fls
          rw [ih, ih (acc := _ ++ _)]
          simp [List.append_assoc]

/-- `processEntries` preserves `none`: if `σ v = none`, the σ-output at `v` is `none`.
    This is because `processEntries` only applies `Function.update σ l.var none`,
    which either preserves `none` (if `l.var ≠ v`) or sets to `none` (if `l.var = v`). -/
private lemma processEntries_preserves_none {n : ℕ}
    (t : Term n) (w : ℕ) (σ ρ₀ : Restriction n) (aux : List (ℕ × Bool))
    (v : Fin n) (hv : σ v = none) :
    (razborovDecode.processEntries t w σ ρ₀ aux).1 v = none := by
  induction aux generalizing σ ρ₀ with
  | nil => simp [razborovDecode.processEntries, hv]
  | cons entry rest ih =>
    simp only [razborovDecode.processEntries]
    split
    · exact hv  -- idx ≥ w: termination marker, returns σ
    · split
      · exact hv  -- t.drop idx = []: returns σ
      · -- t.drop idx = l :: _: update σ at l.var to none, then recurse
        apply ih
        simp only [Function.update_apply]
        split
        · rfl  -- v = l.var: updated to none
        · exact hv  -- v ≠ l.var: unchanged

private lemma decode_go_preserves_none {n : ℕ} (f : DNF n) (w : ℕ)
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
      · exact hv  -- find? = none
      · -- find? = some t: processEntries then recursive go
        next t _ =>
        apply ih
        exact processEntries_preserves_none t w σ ρ₀ _ v hv

/-- If `(l, idx) ∈ t.zipIdx`, then `t.drop idx` starts with `l`. -/
private lemma zipIdx_drop_spec {α : Type*} (t : List α) (l : α) (idx : ℕ)
    (h : (l, idx) ∈ t.zipIdx) : ∃ rest, t.drop idx = l :: rest := by
  obtain ⟨_, hidx, heq⟩ := List.mem_zipIdx h
  simp at hidx heq
  have hlt : idx < t.length := by omega
  rw [heq]
  exact ⟨List.drop (idx + 1) t, List.drop_eq_getElem_cons hlt⟩

/-- If `(l, idx)` comes from `t.zipIdx` filtered by a predicate, and `t` has
    length ≤ w, then `idx < w`. -/
private lemma zipIdx_filter_idx_lt {α : Type*} (t : List α) (p : α × ℕ → Bool)
    (l : α) (idx : ℕ) (w : ℕ) (hw : t.length ≤ w)
    (h : (l, idx) ∈ (t.zipIdx).filter p) : idx < w := by
  have hmem := (List.mem_filter.mp h).1
  obtain ⟨_, hidx, _⟩ := List.mem_zipIdx hmem
  simp at hidx; omega

/-- Characterization of `processEntries` on data from `processClauseLits`
    followed by a termination marker. The decoder processes each `(idx, dir)`
    entry produced by `processClauseLits`, doing `Function.update σ l.var none`
    and `Function.update ρ₀ l.var (some dir)` for the literal `l` at position
    `idx` in clause `t`. After all data entries, it hits the termination marker
    `(w, false)` and returns `rest` as the remaining aux.

    The RHS is a fold over `pcl.2.2.2` (the aux block) that mirrors the decoder's
    updates. Each entry `(idx, dir)` looks up `t.drop idx` to find the literal. -/
private lemma processEntries_of_processClauseLits {n : ℕ}
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
    -- pcl.2.2.2 = [], PE hits termination marker (w, false) immediately
    simp only [processClauseLits, List.nil_append, List.foldl_nil]
    simp [razborovDecode.processEntries, show w ≥ w from le_refl w]
  | cons hd tl ih =>
    cases path with
    | nil =>
      -- path empty: pcl.2.2.2 = [], same as nil case
      simp only [processClauseLits, List.nil_append, List.foldl_nil]
      simp [razborovDecode.processEntries, show w ≥ w from le_refl w]
    | cons p ps =>
      -- hd = (l, idx), p = (_, dir)
      -- pcl.2.2.2 = (idx, dir) :: inner.2.2.2
      simp only [processClauseLits]
      -- Need: idx < w (not a termination marker) and t.drop idx = l :: _
      have hmem_hd : hd ∈ t.zipIdx := hmem hd (List.mem_cons_self)
      have ⟨drop_rest, hdrop⟩ := zipIdx_drop_spec t hd.1 hd.2 hmem_hd
      have hidx : ¬(hd.2 ≥ w) := by
        push_neg
        exact zipIdx_filter_idx_lt t (fun _ => true) hd.1 hd.2 w hw
          (by simp [List.mem_filter]; exact hmem_hd)
      -- Unfold PE for the first entry
      simp only [List.cons_append, razborovDecode.processEntries, hidx, ↓reduceIte, hdrop]
      -- Now the goal reduces to the IH application
      simp only [List.foldl_cons, hdrop]
      exact ih ps _ _ _ _
        (fun p hp => hmem p (List.mem_cons_of_mem _ hp))

/-- The encoder's γ does not kill the first non-killed clause: for any literal
    `l` in `t` with `l.var` free under `ρ₀`, `γ(l.var) ≠ some(l.neg)`. This uses
    the no-duplicate-variable hypothesis `hnd` to ensure the satisfying direction
    stored in γ matches `l`'s own polarity. -/
private lemma encode_go_not_kills_first_clause {n : ℕ} (f : DNF n) (w : ℕ)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (enc_fuel : ℕ) (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (t : Term n)
    (hfind : f.find? (fun t => decide (¬Term.killedBy t ρ₀)) = some t)
    (l : Literal n) (hl : l ∈ t) (hfree : ρ₀ l.var = none) :
    (razborovEncode.go f w enc_fuel path ρ₀ σ []).1 l.var ≠ some l.neg := by
  sorry

/-- A term's length is at most the DNF width. -/
private lemma term_length_le_width {n : ℕ} (f : DNF n) (t : Term n) (ht : t ∈ f) :
    t.length ≤ f.width := by
  unfold DNF.width Term.width
  induction f with
  | nil => simp at ht
  | cons hd tl ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp ht with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- The σ-fold over `processClauseLits` aux preserves `v` when `v` is not
    the variable of any literal encountered by `t.drop`. -/
private lemma foldl_sigma_stable {n : ℕ} (t : Term n)
    (entries : List (ℕ × Bool)) (σ : Restriction n) (v : Fin n)
    (hne : ∀ e ∈ entries, ∀ (l : Literal n) (rest : List (Literal n)),
      t.drop e.1 = l :: rest → l.var ≠ v) :
    entries.foldl (fun σ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ v = σ v := by
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
      simp only [Function.update_apply, ne_eq, (hne_e l _ h).symm, not_false_eq_true, ite_false]

/-- The ρ₀-fold over `processClauseLits` aux preserves `v` when `v` is not
    the variable of any literal encountered. -/
private lemma foldl_rho_stable {n : ℕ} (t : Term n)
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
      simp only [Function.update_apply, ne_eq, (hne_e l _ h).symm, not_false_eq_true, ite_false]

/-- Base-case helper: when the encoder returns `(σ, [])`, the decoder returns
    `σ_dec` and `σ_dec = σ` by the invariant conditions. -/
private lemma roundtrip_base {n : ℕ} (f : DNF n) (w : ℕ)
    (ρ₀ σ σ_dec ρ₀_dec : Restriction n) (dec_fuel : ℕ)
    (hE : ∀ v, ρ₀ v = none → σ v = none)
    (hA : ∀ v, ρ₀ v = none → σ_dec v = σ v)
    (hC : ∀ v, ρ₀ v ≠ none → σ_dec v = σ v) :
    (razborovDecode.go f w dec_fuel σ_dec ρ₀_dec []).1 = σ := by
  cases dec_fuel with
  | zero => simp [razborovDecode.go]; funext v; by_cases h : ρ₀ v = none <;> simp_all
  | succ _ => simp [razborovDecode.go]; funext v; by_cases h : ρ₀ v = none <;> simp_all

/-- The entries in `processClauseLits`'s aux output correspond to literals from
    the input list: for each `(idx, dir) ∈ pcl.2.2.2`, the literal at `t.drop idx`
    has a variable that was free under `ρ₀` (came from the filter).
    More precisely: `t.drop idx = l :: _` where `(l, idx) ∈ lits`. -/
private lemma processClauseLits_aux_entries_from_lits {n : ℕ}
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

/-- Derived: for non-free `v`, no entry in `pcl.2.2.2` targets `v`. -/
private lemma processClauseLits_aux_ne_nonfree {n : ℕ}
    (t : Term n) (lits : List (Literal n × ℕ)) (path : List (Fin n × Bool))
    (ρ₀ σ : Restriction n) (v : Fin n)
    (hmem : ∀ p ∈ lits, p ∈ t.zipIdx)
    (hne_var : ∀ p ∈ lits, p.1.var ≠ v) :
    ∀ e ∈ (processClauseLits lits path ρ₀ σ).2.2.2,
    ∀ (l : Literal n) (rest : List (Literal n)),
    t.drop e.1 = l :: rest → l.var ≠ v := by
  intro e he l rest hdrop
  obtain ⟨li, hli, hidx⟩ := processClauseLits_aux_entries_from_lits lits path ρ₀ σ e he
  -- e.1 = li.2, and (li.1, li.2) ∈ t.zipIdx, so t.drop li.2 = li.1 :: _
  have hli_zip := hmem li hli
  obtain ⟨rest', hdrop'⟩ := zipIdx_drop_spec t li.1 li.2 hli_zip
  -- t.drop e.1 = t.drop li.2 = li.1 :: rest'
  rw [hidx] at hdrop; rw [hdrop'] at hdrop
  -- l = li.1
  have : l = li.1 := (List.cons.inj hdrop |>.1).symm
  rw [this]
  exact hne_var li hli

/-- All entries in `pcl.2.2.2` reference literal variables that are free under `ρ₀`,
    provided the literal list comes from `t.zipIdx`. Combined with any condition
    implying `v` is not such a variable, this gives the "no-target" fact for foldl. -/
private lemma processClauseLits_aux_vars_free {n : ℕ}
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

/-- The σ-foldl preserves `none`: once `σ v = none`, no step can change it
    (every step does `Function.update _ _ none`). -/
private lemma foldl_sigma_preserves_none {n : ℕ} (t : Term n)
    (entries : List (ℕ × Bool)) (σ : Restriction n) (v : Fin n) (hv : σ v = none) :
    entries.foldl (fun σ (e : ℕ × Bool) =>
      match t.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ v = none := by
  induction entries generalizing σ with
  | nil => simpa
  | cons e es ih =>
    simp only [List.foldl_cons]
    apply ih
    match h : t.drop e.1 with
    | [] => simp [h, hv]
    | l :: _ =>
      simp only [Function.update_apply]
      split
      · exact rfl
      · exact hv

/-- If `pcl.2.1 v ≠ none` but `ρ₀ v = none`, the σ-foldl produces `none` at `v`.
    Some entry in `pcl.2.2.2` targets `v` (since PCL set ρ₀ at v to `some`),
    and the foldl sets σ to `none` there. -/
private lemma processClauseLits_foldl_sigma_none {n : ℕ} (t : Term n)
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
      · -- hd targets v: σ set to none, preserved by foldl_sigma_preserves_none
        subst heq; exact foldl_sigma_preserves_none t _ _ _
          (by rw [Function.update_apply, if_pos rfl])
      · -- hd doesn't target v: no-op, apply IH
        exact ih ps _ _ (Function.update σ_dec hd.1.var none)
          (fun p hp => hmem p (.tail _ hp))
          (by rwa [Function.update_apply, if_neg (Ne.symm heq)])
          (by simp only [processClauseLits] at hset; exact hset)

/-- The ρ₀-foldl over `pcl.2.2.2` starting from `ρ₀_dec` always agrees with
    `pcl.2.1` at `v`, provided it agrees initially (`ρ₀ v = ρ₀_dec v`) or
    some entry targets `v`. Unconditional version: proved by induction showing
    foldl and PCL apply the same `Function.update` at each step. -/
private lemma processClauseLits_foldl_rho_eq {n : ℕ} (t : Term n)
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
      -- Both foldl and PCL update at hd.1.var with the same value, then recurse.
      -- After the update: ρ₀_dec'(v) = Function.update ρ₀_dec hd.1.var (some p.2) v
      --                   ρ₀'(v) = Function.update ρ₀ hd.1.var (some p.2) v
      -- By hinit (ρ₀ v = ρ₀_dec v), these agree: ρ₀'(v) = ρ₀_dec'(v).
      exact ih ps _ _ _
        (fun q hq => hmem q (.tail _ hq))
        (by simp only [Function.update_apply]; split <;> simp_all)

/-- Variant of `processClauseLits_foldl_rho_eq` when initial values may differ but
    `v` is free under `ρ₀` and gets set by PCL (pcl.2.1 v ≠ none). The first entry
    targeting `v` overwrites both ρ₀ and ρ₀_dec to the same value, after which the
    `hinit` version applies for the rest. -/
private lemma processClauseLits_foldl_rho_eq_of_set {n : ℕ} (t : Term n)
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
      · -- hd targets v: both set to same value, then hinit version applies
        exact processClauseLits_foldl_rho_eq t tl ps _ _ _ v
          (fun q hq => hmem q (.tail _ hq))
          (by simp only [Function.update_apply, if_pos heq.symm])
      · -- hd doesn't target v: no-op, apply IH
        exact ih ps _ _ _
          (fun q hq => hmem q (.tail _ hq))
          (by rwa [Function.update_apply, if_neg (Ne.symm heq)])
          (by simp only [processClauseLits] at hset; exact hset)

/-- `processClauseLits` outputs `.1` (remaining path), `.2.1` (updated ρ₀), and
    `.2.2.2` (aux entries) are all independent of the `σ` argument. Only `.2.2.1`
    (updated σ) depends on σ. -/
private lemma processClauseLits_sigma_indep {n : ℕ}
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

/-- The `.2` component of `razborovEncode.go` is independent of the `σ` argument. -/
private lemma encode_go_snd_sigma_indep {n : ℕ} (f : DNF n) (w fuel : ℕ)
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
        · -- fl :: fls case
          next fl fls _ =>
          -- pcl₁ and pcl₂ agree on .1, .2.1, .2.2.2 by σ-independence
          have hindep := processClauseLits_sigma_indep (fl :: fls) (step :: rest) ρ₀ σ₁ σ₂
          obtain ⟨hpath, hrho, haux_eq⟩ := hindep
          -- Use encode_go_acc to factor: (go ... acc).2 = acc ++ (go ... []).2
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

/-- Contrapositive of rho_stable: if `pcl.2.1 v = none` and `ρ₀ v = none`,
    then no literal in `lits` has `var = v` (assuming path is long enough). -/
private lemma processClauseLits_no_target_of_rho_none {n : ℕ}
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
      -- After one step: ρ₀' = Function.update ρ₀ hd.1.var (some step.2)
      -- If hd.1.var = v, then ρ₀' v = some step.2 ≠ none.
      -- processClauseLits_rho_ne_none on ρ₀' gives pcl.2.1 v ≠ none.
      -- But hnone says pcl.2.1 v = none. Contradiction.
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp_tl
      · -- p = hd
        intro hpv
        have hne : (Function.update ρ₀ p.1.var (some step.2)) v ≠ none := by
          rw [Function.update_apply, if_pos hpv.symm]; exact Option.some_ne_none _
        exact absurd hnone (processClauseLits_rho_ne_none tl rest _ _ _ hne)
      · -- p ∈ tl: check if hd.1.var = v
        by_cases heq : hd.1.var = v
        · -- hd targets v too: ρ₀' v ≠ none → pcl.2.1 v ≠ none, contradicts hnone
          have hne : (Function.update ρ₀ hd.1.var (some step.2)) v ≠ none := by
            rw [Function.update_apply, if_pos heq.symm]; exact Option.some_ne_none _
          exact absurd hnone (processClauseLits_rho_ne_none tl rest _ _ _ hne)
        · -- hd doesn't target v: ρ₀' v = ρ₀ v = none, apply IH
          exact ih rest _ _ (by rwa [Function.update_apply, if_neg (Ne.symm heq)]) hnone
            (by simp [List.length_cons] at hlen ⊢; omega) p hp_tl

/-- The encoder's `.1` is independent of the accumulator. -/
private lemma encode_go_fst_acc {n : ℕ} (f : DNF n) (w fuel : ℕ)
    (path : List (Fin n × Bool)) (ρ₀ σ : Restriction n) (acc : List (ℕ × Bool)) :
    (razborovEncode.go f w fuel path ρ₀ σ acc).1 =
    (razborovEncode.go f w fuel path ρ₀ σ []).1 := by
  have := encode_go_acc f w fuel path ρ₀ σ acc; rw [this]

/-- `processClauseLits` output `.2.2.1` (updated σ) at variable `v` is independent of
    the initial σ when `v` appears in the literal list (both get `some (!l.neg)`),
    and equals `σ v` when `v` doesn't appear. -/
private lemma processClauseLits_sigma_at_v {n : ℕ}
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

/-- The encoder's `.1` (γ) at a free variable `v` (where `ρ₀ v = none`) is
    independent of the initial σ, provided both σ values agree at `v` (both `none`). -/
private lemma encode_go_fst_sigma_indep_at_free {n : ℕ} (f : DNF n) (w fuel : ℕ)
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
      · simp [h₁, h₂]  -- find? = none
      · split
        · simp [h₁, h₂]  -- freeLitsIdx = []
        · -- fl :: fls case
          next fl fls _ =>
          obtain ⟨hpath, hrho, _⟩ :=
            processClauseLits_sigma_indep (fl :: fls) (step :: rest) ρ₀ σ₁ σ₂
          -- Strip accumulator from both sides
          conv_lhs => rw [encode_go_fst_acc]
          conv_rhs => rw [encode_go_fst_acc]
          rw [hpath, hrho]
          -- Case split: did processClauseLits set v?
          by_cases hv : (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.1 v = none
          · -- v still free after pcl: no literal targeted v
            -- pcl₂.2.1 v = none and ρ₀ v = none: if any p.1.var = v,
            -- pcl would set ρ₀ at v via Function.update, giving pcl.2.1 v ≠ none
            have hne_v : ∀ p ∈ (fl :: fls), p.1.var ≠ v := by
              intro p hp hpv
              -- p.1.var = v and ρ₀ v = none. After processClauseLits processes p,
              -- ρ₀ gets Function.update at v to some dir, so pcl.2.1 v ≠ none.
              -- But hv says pcl₂.2.1 v = none. Contradiction.
              have : ρ₀ p.1.var ≠ none → (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.1 p.1.var ≠ none :=
                processClauseLits_rho_ne_none _ _ _ _ _
              rw [hpv] at this
              -- this : ρ₀ v ≠ none → pcl₂.2.1 v ≠ none. But ρ₀ v = none (hfree).
              -- We need: pcl₂.2.1 v ≠ none (to contradict hv).
              -- processClauseLits_rho_ne_none gives the wrong direction here.
              -- Instead use: if processClauseLits processes hd with hd.1.var = v,
              -- then it does Function.update ρ₀ v (some dir). Then rho_ne_none
              -- on the updated ρ₀ (which has v ≠ none) gives the result.
              -- Simplify: just unfold one step of processClauseLits.
              sorry
            exact ih _ _
              (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₁).2.2.1
              (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.2.1
              hv
              (by rw [processClauseLits_sigma_stable _ _ _ _ _ hne_v]; exact h₁)
              (by rw [processClauseLits_sigma_stable _ _ _ _ _ hne_v]; exact h₂)
          · -- v was set by pcl: use encode_go_fst_nonfree on both sides
            rw [encode_go_fst_nonfree f w fuel _ _ _ [] v hv,
                encode_go_fst_nonfree f w fuel _ _ _ [] v hv]
            exact processClauseLits_sigma_at_v _ _ _ _ _ v (by rw [h₁, h₂])

/-- Generalized round-trip: the decoder, starting from `(σ_dec, ρ₀_dec)` satisfying
    the compatibility invariant with encoder state `(ρ₀, σ)`, recovers `σ`.
    Requires that each term in `f` has at most one literal per variable. -/
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
  -- Abbreviate the encoder output
  set enc := razborovEncode.go f w enc_fuel path ρ₀ σ [] with henc_def
  -- In base cases, the encoder returns (σ, []) so γ = σ and aux = [].
  -- hA then gives σ_dec v = σ v for free vars (since γ = σ).
  -- Combined with hC: σ_dec = σ. Decoder on [] returns σ_dec = σ.
  -- Factor this into roundtrip_base.
  have base : enc = (σ, []) →
      (razborovDecode.go f w dec_fuel σ_dec ρ₀_dec enc.2).1 = σ := by
    intro heq
    rw [show enc.2 = [] from by rw [heq]]
    have hA' : ∀ v, ρ₀ v = none → σ_dec v = σ v := by
      intro v hv; rw [hA v hv, show enc.1 v = σ v from by rw [heq]]
    exact roundtrip_base f w ρ₀ σ σ_dec ρ₀_dec dec_fuel hE hA' hC
  induction enc_fuel generalizing path ρ₀ σ σ_dec ρ₀_dec dec_fuel with
  | zero =>
    cases path <;> (simp only [razborovEncode.go] at henc_def; exact base henc_def)
  | succ fuel ih =>
    cases path with
    | nil => simp only [razborovEncode.go] at henc_def; exact base henc_def
    | cons step rest =>
      simp only [razborovEncode.go] at henc_def
      -- Split on find?
      revert henc_def; split
      · intro henc_def; exact base henc_def  -- find? = none
      · -- find? = some t_clause
        rename_i t_clause hfind_enc
        intro henc_def
        -- Split on freeLitsIdx
        generalize hfli_eq :
          List.filter (fun (x : Literal n × ℕ) => decide (x.1.var ∈ Restriction.freeVars ρ₀))
            (List.zipIdx t_clause) = fli
        revert henc_def; rw [hfli_eq]; intro henc_def
        match fli with
        | [] => exact base henc_def  -- freeLitsIdx = []
        | fl :: fls =>
          -- *** INDUCTIVE CASE ***
          -- Reduce the match in henc_def
          simp only [List.nil_append] at henc_def
          -- Set up names for the processClauseLits output
          set pcl := processClauseLits (fl :: fls) (step :: rest) ρ₀ σ with hpcl_def
          -- By encode_go_acc, the encoder output decomposes as:
          -- enc = (rec.1, (pcl.2.2.2 ++ [(w, false)]) ++ rec.2)
          -- where rec = razborovEncode.go f w fuel pcl.1 pcl.2.1 pcl.2.2.1 []
          set rec_enc := razborovEncode.go f w fuel pcl.1 pcl.2.1 pcl.2.2.1 [] with hrec_def
          have henc_acc := encode_go_acc f w fuel pcl.1 pcl.2.1 pcl.2.2.1
            (pcl.2.2.2 ++ [(w, false)])
          -- enc.1 = rec_enc.1 (γ is independent of acc)
          have henc_eq : enc = (rec_enc.1, (pcl.2.2.2 ++ [(w, false)]) ++ rec_enc.2) :=
            henc_def.trans henc_acc
          have hγ : enc.1 = rec_enc.1 := by rw [henc_eq]
          have haux : enc.2 = pcl.2.2.2 ++ [(w, false)] ++ rec_enc.2 := by
            have := congrArg Prod.snd henc_eq; simpa [List.append_assoc] using this
          -- All elements of fl :: fls are in t_clause.zipIdx (from filter)
          have hmem_zip : ∀ p ∈ (fl :: fls), p ∈ t_clause.zipIdx := by
            intro p hp; rw [← hfli_eq] at hp
            exact (List.mem_filter.mp hp).1
          -- t_clause.length ≤ w (from f.width ≤ w)
          have htw : t_clause.length ≤ w := by
            have ht_mem := List.mem_of_find?_eq_some hfind_enc
            exact le_trans (term_length_le_width f t_clause ht_mem) hw
          -- All elements of fl :: fls have free variables under ρ₀
          have hfree_lits : ∀ p ∈ (fl :: fls), ρ₀ p.1.var = none := by
            intro p hp; rw [← hfli_eq] at hp
            simp [List.mem_filter, Restriction.freeVars, Finset.mem_filter,
                  Option.isNone_iff_eq_none] at hp
            exact hp.2
          -- === Step 1: Decoder finds the same clause t_clause ===
          have hfind_dec : f.find? (fun t => decide (¬Term.killedBy t ρ₀_dec)) =
              some t_clause := by
            apply first_clause_preserved f ρ₀ ρ₀_dec t_clause hfind_enc hD
            -- t_clause not killed by ρ₀_dec
            intro ⟨l, hl_mem, hl_killed⟩
            simp only [Literal.killedBy] at hl_killed
            by_cases hfv : ρ₀ l.var = none
            · -- l.var free under ρ₀: ρ₀_dec = γ at l.var
              rw [hB l.var hfv] at hl_killed
              exact encode_go_not_kills_first_clause f w hnd (fuel + 1)
                (step :: rest) ρ₀ σ hE t_clause hfind_enc l hl_mem hfv
                (hγ ▸ hl_killed)
            · -- l.var non-free: ρ₀_dec = ρ₀ at l.var
              have := hD l.var hfv
              rw [this] at hl_killed
              have hkill : Term.killedBy t_clause ρ₀ := ⟨l, hl_mem, hl_killed⟩
              have hnkill := List.find?_some hfind_enc
              simp at hnkill; exact absurd hkill hnkill
          -- === Step 2: processEntries processes one clause block ===
          -- Apply processEntries_of_processClauseLits
          have hpe := processEntries_of_processClauseLits t_clause w htw
            (fl :: fls) (step :: rest) ρ₀ σ σ_dec ρ₀_dec rec_enc.2 hmem_zip
          -- Rewrite the decoder unfolding
          rw [haux]
          -- === Step 3: Unfold decoder, apply PE, apply IH ===
          -- pcl.2.2.2 is non-empty (from fl :: fls and step :: rest)
          have hpcl_aux_ne : pcl.2.2.2 ≠ [] := by
            simp only [hpcl_def, processClauseLits]; exact List.cons_ne_nil _ _
          -- Write pcl.2.2.2 = hd_aux :: tl_aux for the decoder pattern match
          obtain ⟨hd_aux, tl_aux, hpcl_cons⟩ : ∃ h t, pcl.2.2.2 = h :: t :=
            List.exists_cons_of_ne_nil hpcl_aux_ne
          -- dec_fuel ≥ 1 (from hfuel and non-empty aux)
          obtain ⟨df, rfl⟩ : ∃ k, dec_fuel = k + 1 := ⟨dec_fuel - 1, by omega⟩
          -- Unfold razborovDecode.go one step using hpcl_cons
          rw [hpcl_cons]
          simp only [List.cons_append, razborovDecode.go, hfind_dec]
          -- The processEntries call: rewrite using hpe
          -- After simp, the goal has hd_aux :: (tl_aux ++ ...) form
          -- Restore pcl.2.2.2 for hpe
          have hreassoc : hd_aux :: (tl_aux ++ [(w, false)] ++ rec_enc.2) =
              pcl.2.2.2 ++ [(w, false)] ++ rec_enc.2 := by
            simp only [hpcl_cons, List.cons_append, List.append_assoc]
          rw [hreassoc, hpe]
          -- After rw [hpe], the goal has explicit foldl terms and rec_enc.2.
          -- Name the foldl components
          set σ_fold := pcl.2.2.2.foldl (fun σ (e : ℕ × Bool) =>
            match t_clause.drop e.1 with | [] => σ | l :: _ => Function.update σ l.var none) σ_dec
            with σ_fold_def
          set ρ₀_fold := pcl.2.2.2.foldl (fun ρ₀ (e : ℕ × Bool) =>
            match t_clause.drop e.1 with | [] => ρ₀ | l :: _ => Function.update ρ₀ l.var (some e.2)) ρ₀_dec
            with ρ₀_fold_def
          -- Use σ-independence to replace rec_enc.2 with (encode ... σ []).2
          have hsigma_indep : rec_enc.2 =
              (razborovEncode.go f w fuel pcl.1 pcl.2.1 σ []).2 :=
            encode_go_snd_sigma_indep f w fuel pcl.1 pcl.2.1 pcl.2.2.1 σ
          rw [hsigma_indep]
          refine ih pcl.1 pcl.2.1 σ _ _ df ?hE' ?hC' ?hD' ?hA' ?hB' ?hfuel' ?henc' ?hbase'
          case hE' => -- ∀ v, pcl.2.1 v = none → σ v = none
            intro v hv'; exact hE v (by
              by_contra h; push_neg at h
              exact absurd hv' (processClauseLits_rho_ne_none
                (fl :: fls) (step :: rest) ρ₀ σ v h))
          case hC' => -- ∀ v, pcl.2.1 v ≠ none → σ_fold v = σ v
            intro v hv'
            simp only [σ_fold_def]
            by_cases hv : ρ₀ v = none
            · rw [processClauseLits_foldl_sigma_none t_clause _ _ ρ₀ σ _ _ hmem_zip hv
                (by simp only [hpcl_def] at hv'; exact hv')]
              exact (hE v hv).symm
            · exact (foldl_sigma_stable t_clause _ _ _
                (processClauseLits_aux_ne_nonfree t_clause _ _ ρ₀ σ v hmem_zip
                  (fun p hp heq => hv (heq ▸ hfree_lits p hp)))).trans (hC v hv)
          case hD' => -- ∀ v, pcl.2.1 v ≠ none → ρ₀_fold v = pcl.2.1 v
            intro v hv'
            simp only [ρ₀_fold_def]
            by_cases hv : ρ₀ v = none
            · exact processClauseLits_foldl_rho_eq_of_set t_clause _ _ ρ₀ σ _ v
                hmem_zip hv (by simp only [hpcl_def] at hv'; exact hv')
            · have hne := processClauseLits_aux_ne_nonfree t_clause (fl :: fls) (step :: rest) ρ₀ σ v hmem_zip
                (fun p hp heq => hv (heq ▸ hfree_lits p hp))
              rw [foldl_rho_stable t_clause _ _ _ hne, hD v hv]
              exact (processClauseLits_rho_stable _ _ _ _ _
                (fun p hp => by intro heq; exact hv (heq ▸ hfree_lits p hp))).symm
          case hA' => sorry
          case hB' => sorry
          case hfuel' => sorry
          case henc' => rfl
          case hbase' => sorry

/-- Go-level round-trip: decoding the encoding of ρ (with σ = ρ₀ = ρ and
    empty accumulator) recovers ρ. Instantiates `go_roundtrip_gen` with
    `ρ₀ = σ = σ_dec = ρ₀_dec = ρ`. -/
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

/-- The round-trip: decoding the encoding of ρ recovers ρ. -/
lemma razborovDecode_encode {n : ℕ} (f : DNF n) (w d : ℕ) (ρ : Restriction n)
    (hbad : IsBadRestriction f.eval d ρ) (hw : f.width ≤ w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂) :
    razborovDecode f w (razborovEncode f w d ρ).1 (razborovEncode f w d ρ).2 = ρ := by
  unfold razborovDecode razborovEncode
  exact go_roundtrip f w hw hnd _ _ ρ

/-- **Injectivity**: the encoding is injective on bad restrictions. -/
theorem razborovEncode_injective {n : ℕ} (f : DNF n) (w d : ℕ)
    (ρ₁ ρ₂ : Restriction n)
    (hbad₁ : IsBadRestriction f.eval d ρ₁) (hbad₂ : IsBadRestriction f.eval d ρ₂)
    (hw : f.width ≤ w)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (henc : razborovEncode f w d ρ₁ = razborovEncode f w d ρ₂) :
    ρ₁ = ρ₂ := by
  rw [← razborovDecode_encode f w d ρ₁ hbad₁ hw hnd,
      ← razborovDecode_encode f w d ρ₂ hbad₂ hw hnd, henc]

/-! ### Counting bounds -/

/-- Each aux data entry is `(position, direction)` with position in `{0,...,w-1}`
    and direction in Bool. Termination markers `(w, false)` separate clauses but
    their positions are determined by `γ` (which clauses are fixed), so they carry
    no additional information. The d free choices give at most `(2w)^d` fibers. -/
private lemma fiber_bound {n : ℕ} (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hd : d ≤ s) (γ : Restriction n) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ ∧
        (razborovEncode f w d ρ).1 = γ).card ≤ (2 * w) ^ d := by
  sorry

/-- **Razborov counting bound**: the number of bad s-restrictions is at most
    `C(n, s−d) · 2^{n−(s−d)} · (2w)^d`. -/
private lemma bad_count_bound {n : ℕ} (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hd : d ≤ s) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ).card ≤
    n.choose (s - d) * 2 ^ (n - (s - d)) * (2 * w) ^ d := by
  sorry

/-! ## Combinatorial inequalities -/

private lemma bad_filter_empty_of_d_ge_s {n : ℕ} (f : DNF n) (d s : ℕ) (hds : s ≤ d) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ) = ∅ := by
  simp +zetaDelta at *
  exact fun ρ hρ => not_lt.mpr (le_trans (dtDepth_restrictFn_le_numFree _ _)
    (by linarith [hρ.symm]))

/-
The key binomial coefficient inequality:
    `C(n, s-d) * (2n)^d ≤ C(n, s) * (5s)^d` when `5s ≤ n` and `d ≤ s`.
-/
private lemma choose_mul_pow_bound {n s d : ℕ} (hs : 5 * s ≤ n) (hd : d ≤ s) :
    n.choose (s - d) * (2 * n) ^ d ≤ n.choose s * (5 * s) ^ d := by
  induction d with
  | zero => norm_num
  | succ d hd_ih =>
    have h_simp : (Nat.choose n (s - d - 1)) * (2 * n) ≤ (Nat.choose n (s - d)) * (5 * s) := by
      set m := s - d - 1 with hm_def
      have hm_succ : s - d = m + 1 := by omega
      rw [hm_succ]
      have h_eq := Nat.choose_succ_right_eq n m
      have h_mn : m ≤ n := by omega
      have h_pos : 0 < Nat.choose n m := Nat.choose_pos h_mn
      have h_sub_add : (n - m) + m = n := Nat.sub_add_cancel h_mn
      suffices h : 2 * n * (m + 1) ≤ (n - m) * (5 * s) by nlinarith [h_eq]
      have hms : m + 1 + d = s := by omega
      zify [h_mn] at h_sub_add hs ⊢
      nlinarith [hms]
    have := hd_ih ( Nat.le_of_succ_le hd );
    rw [ Nat.sub_sub ] at *;
    rw [ pow_succ', pow_succ' ];
    nlinarith [ pow_pos ( show 0 < 2 * n by linarith ) d ]

/-! ## Main theorem -/

theorem switching_lemma {n : ℕ} (hn : 0 < n) (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hs : 5 * s ≤ n) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧ IsBadRestriction f.eval d ρ).card * n ^ d ≤
    numSRestrictions n s * (10 * s * w) ^ d := by
  by_cases hds : d ≤ s
  · refine le_trans (Nat.mul_le_mul_right _ (bad_count_bound f w s d hw hds)) ?_
    convert Nat.mul_le_mul_right _ (choose_mul_pow_bound hs hds) |> le_trans <| ?_ using 1; ring
    rotate_left
    exact 2 ^ (n - s) * (2 * w) ^ d
    · unfold numSRestrictions; ring_nf
      norm_num [mul_assoc, mul_left_comm, ← mul_pow]
      ring_nf; norm_num [mul_assoc, mul_comm, mul_left_comm]
    · rw [show n - (s - d) = n - s + d by omega]; ring
  · rw [bad_filter_empty_of_d_ge_s f d s (by linarith)]; norm_num

/-! ## Decision tree to DNF/CNF conversion -/

private def toDNF {n : ℕ} : DecisionTree n → DNF n
  | .leaf true  => [[]]
  | .leaf false => []
  | .branch v lo hi =>
    ((toDNF lo).map fun t => ⟨v, true⟩ :: t) ++
    ((toDNF hi).map fun t => ⟨v, false⟩ :: t)

private def toCNF {n : ℕ} : DecisionTree n → CNF n
  | .leaf true  => []
  | .leaf false => [[]]
  | .branch v lo hi =>
    ((toCNF lo).map fun c => ⟨v, false⟩ :: c) ++
    ((toCNF hi).map fun c => ⟨v, true⟩ :: c)

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

/-
`DTdepth(f) ≤ d` implies `f` has both a width-`d` DNF and a width-`d` CNF.
-/
lemma dtDepth_le_implies_small_dnf_cnf {n : ℕ} (f : (Fin n → Bool) → Bool) (d : ℕ)
    (h : dtDepth f ≤ d) :
    (∃ φ : DNF n, φ.width ≤ d ∧ ∀ x, φ.eval x = f x) ∧
    (∃ ψ : CNF n, ψ.width ≤ d ∧ ∀ x, ψ.eval x = f x) := by
  obtain ⟨T, hTd, hTeval⟩ := dtDepth_witness f
  have hTd' : T.depth ≤ d := le_trans hTd h
  constructor
  ·
    -- By definition of `toDNF`, we know that `toDNF T` is a DNF formula equivalent to `T` and has width at most `d`.
    use SwitchingLemma2.toDNF T, by
      -- By definition of `toDNF`, the width of the resulting DNF formula is at most the depth of the decision tree `T`.
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
        split_ifs <;> simp_all +decide [ Function.comp, Term.eval ];
        · simp_all +decide [ Function.comp, Literal.eval ];
          simp_all +decide [ Function.comp, List.any_eq, List.all_eq ];
        · simp_all +decide [ Function.comp, List.any_eq, Literal.eval ]
  ·
    -- Let's choose the CNF formula ψ to be toCNF T.
    use toCNF T;
    refine' ⟨ le_trans _ hTd', fun x => _ ⟩;
    · -- By induction on the depth of the decision tree, we can show that the length of each clause in the CNF is at most the depth of the tree.
      have h_clause_length : ∀ T : DecisionTree n, ∀ c ∈ toCNF T, c.length ≤ T.depth := by
        intro T c hc
        induction' T with v lo hi ih_lo ih_hi generalizing c;
        · cases v <;> cases hc ; trivial;
          contradiction;
        · -- By definition of `toCNF`, the clauses in `toCNF (DecisionTree.branch lo hi ih_lo)` are either of the form `⟨lo, false⟩ :: c` where `c` is a clause from `toCNF hi`, or `⟨lo, true⟩ :: c` where `c` is a clause from `toCNF ih_lo`.
          have h_clauses : ∀ c ∈ toCNF (DecisionTree.branch lo hi ih_lo), ∃ c' ∈ toCNF hi ∪ toCNF ih_lo, c = ⟨lo, false⟩ :: c' ∨ c = ⟨lo, true⟩ :: c' := by
            intro c hc; rw [ show toCNF ( DecisionTree.branch lo hi ih_lo ) = ( toCNF hi |> List.map fun c' => ⟨ lo, false ⟩ :: c' ) ++ ( toCNF ih_lo |> List.map fun c' => ⟨ lo, true ⟩ :: c' ) from rfl ] at hc; aesop;
          obtain ⟨ c', hc', rfl | rfl ⟩ := h_clauses c hc <;> simp +arith +decide [ *, DecisionTree.depth ];
          · grind;
          · grind;
      have h_foldr_le : ∀ {l : List ℕ}, (∀ x ∈ l, x ≤ T.depth) → List.foldr Max.max 0 l ≤ T.depth := by
        intros l hl; induction l <;> aesop;
      exact h_foldr_le fun x hx => by aesop;
    · rw [ ← hTeval, eq_comm ];
      -- By definition of `toCNF`, we know that `toCNF T` is equivalent to `T`.
      have h_equiv : ∀ T : DecisionTree n, ∀ x : Fin n → Bool, T.eval x = (toCNF T).eval x := by
        intros T x; induction' T with v lo hi ih_lo ih_hi generalizing x; simp +decide [ *, CNF.eval ] ;
        · cases v <;> simp +decide [ DecisionTree.eval ];
          · exact ⟨ [ ], by tauto, by tauto ⟩;
          · exact fun t ht => by cases ht;
        · simp +decide [ *, DecisionTree.eval, CNF.eval ];
          rw [ show toCNF ( DecisionTree.branch lo hi ih_lo ) = ( toCNF hi |> List.map fun c => ⟨ lo, false ⟩ :: c ) ++ ( toCNF ih_lo |> List.map fun c => ⟨ lo, true ⟩ :: c ) by rfl ];
          split_ifs <;> simp_all +decide [ CNF.evalClause ];
          · simp +decide [ *, Function.comp, Literal.eval ];
            grind +splitIndPred;
          · simp +decide [ *, Function.comp, Literal.eval ];
            grind;
      exact h_equiv T x

theorem switching_corollary {n : ℕ} (hn : 0 < n) (f : DNF n) (w s : ℕ)
    (hw : f.width ≤ w) (hs : 5 * s ≤ n) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧
        ¬ ∃ ψ : CNF n, ψ.width ≤ w ∧
          ∀ x, ψ.eval x = restrictFn f.eval ρ x).card * n ^ w ≤
    numSRestrictions n s * (10 * s * w) ^ w := by
  apply le_trans _ (switching_lemma hn f w s w hw hs)
  apply Nat.mul_le_mul_right
  apply Finset.card_le_card
  intro ρ hρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
  refine ⟨hρ.1, ?_⟩
  show dtDepth (restrictFn f.eval ρ) > w
  by_contra hgood; push_neg at hgood
  exact hρ.2 (dtDepth_le_implies_small_dnf_cnf _ w hgood).2

end SwitchingLemma2
