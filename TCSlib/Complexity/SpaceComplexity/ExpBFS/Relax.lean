/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Run

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The relaxation round of the search machine

Run lemmas for the first parts of one search of `Complexity.LogProg.ExpBFS.A` over the codes
`u < K`, its marks kept at the memory cells `Bs + u`: the specifications (the decider answers
`ini`, `stp`, the growth predicates `Mono`, `Out`, the reachable codes `Cl`), the initial
marking (`ini_run`) and one relaxation round (`inner_run` for a fixed source `U`, `outer_run`
over all sources). The rounds, the count and the whole search are in
`TCSlib.Complexity.SpaceComplexity.ExpBFS.Search`.

Infrastructure for [AB09, §4.1.1, proof of Theorem 4.2]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ExpBFS.ini`, `Complexity.LogProg.ExpBFS.stp` — the decider answers.
* `Complexity.LogProg.ExpBFS.Mono`, `Complexity.LogProg.ExpBFS.Out` — the memory grows, and
  only in the region.
* `Complexity.LogProg.ExpBFS.Cl` — the codes reachable below `K`.

## Main results

* `Complexity.LogProg.ExpBFS.ini_run` — the initial marking.
* `Complexity.LogProg.ExpBFS.inner_run`, `Complexity.LogProg.ExpBFS.outer_run` — one
  relaxation round.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Theorem 4.2.)
-/

namespace Complexity.LogProg

namespace ExpBFS

open Turing

variable {K₀ : ℕ} {orc : Fin 4 → List Bool → Bool} {x : List Bool} {B P : ℕ}

/-! ## Specifications -/

/-- The radius of a search: `s` for the first, `s1` for the second. -/
def rr (S : St) (φ : Bool) : ℕ := if φ then S.s1 else S.s

/-- The radius register of a search holds its radius. -/
lemma toV_rad (S : St) (φ : Bool) : S.toV (rad (toPh φ)) = rr S φ := by cases φ <;> rfl

/-- The initial-code decider's answer at `u` (radius `r`). -/
def ini (orc : Fin 4 → List Bool → Bool) (x : List Bool) (r u : ℕ) : Bool :=
  orc 1 (pairEncode x (pairEncode (Nat.bits u) (Nat.bits r)))

/-- The step-pair decider's answer at `(u, v)` (radius `r`). -/
def stp (orc : Fin 4 → List Bool → Bool) (x : List Bool) (r u v : ℕ) : Bool :=
  orc 2 (pairEncode x (pairEncode (Nat.bits u) (pairEncode (Nat.bits v) (Nat.bits r))))

/-- The memory cell of code `v` in the region at base `b`. -/
abbrev cell (b v : ℕ) : ℤ := ((b + v : ℕ) : ℤ)

/-- The memory only grows. -/
def Mono (M M' : ℤ → Bool) : Prop := ∀ z, M z = true → M' z = true

/-- The memory changes only in the region `[b, b + K)`. -/
def Out (b K : ℕ) (M M' : ℤ → Bool) : Prop := ∀ z, (∀ v, v < K → z ≠ cell b v) → M' z = M z

/-- The memory grows from itself. -/
lemma Mono.refl (M : ℤ → Bool) : Mono M M := fun _ h => h

/-- Growth of the memory composes. -/
lemma Mono.trans {M M' M'' : ℤ → Bool} (h : Mono M M') (h' : Mono M' M'') : Mono M M'' :=
  fun z hz => h' z (h z hz)

/-- An unchanged memory changes only in the region. -/
lemma Out.refl (b K : ℕ) (M : ℤ → Bool) : Out b K M M := fun _ _ => rfl

/-- Changes only in the region compose. -/
lemma Out.trans {b K : ℕ} {M M' M'' : ℤ → Bool} (h : Out b K M M') (h' : Out b K M' M'') :
    Out b K M M'' := fun z hz => (h' z hz).trans (h z hz)

/-- Setting a bit grows the memory. -/
lemma mono_update (M : ℤ → Bool) (z : ℤ) : Mono M (Function.update M z true) := by
  intro z' hz
  by_cases h : z' = z
  · subst h; simp
  · rw [Function.update_of_ne h]; exact hz

/-- Setting a bit of the region changes the memory only in the region. -/
lemma out_update (M : ℤ → Bool) {b K v : ℕ} (hv : v < K) :
    Out b K M (Function.update M (cell b v) true) := fun _ hz =>
  Function.update_of_ne (hz v hv) _ _

/-- Distinct codes have distinct cells. -/
lemma cell_inj {b v v' : ℕ} (h : cell b v = cell b v') : v = v' := by
  simp only [cell] at h; omega

/-- Prefixing a run to a run statement with one witness. -/
lemma ex1_pre {α : Type} {a b : MConf 17 (Lb K₀)} {f : α → MConf 17 (Lb K₀)} {Q : α → Prop}
    (h1 : MReach (A K₀) orc x (G x B P) a b)
    (h2 : ∃ y, MReach (A K₀) orc x (G x B P) b (f y) ∧ Q y) :
    ∃ y, MReach (A K₀) orc x (G x B P) a (f y) ∧ Q y := by
  obtain ⟨y, hr, hq⟩ := h2; exact ⟨y, h1.trans hr, hq⟩

/-- Prefixing a run to a run statement with two witnesses. -/
lemma ex2_pre {α β : Type} {a b : MConf 17 (Lb K₀)} {f : α → β → MConf 17 (Lb K₀)}
    {Q : α → β → Prop} (h1 : MReach (A K₀) orc x (G x B P) a b)
    (h2 : ∃ y z, MReach (A K₀) orc x (G x B P) b (f y z) ∧ Q y z) :
    ∃ y z, MReach (A K₀) orc x (G x B P) a (f y z) ∧ Q y z := by
  obtain ⟨y, z, hr, hq⟩ := h2; exact ⟨y, z, h1.trans hr, hq⟩

/-- **The codes reachable below `K`**: reachable from an initial code `u < K` through step
pairs with targets below `K`. -/
def Cl (orc : Fin 4 → List Bool → Bool) (x : List Bool) (r K v : ℕ) : Prop :=
  ∃ u, u < K ∧ ini orc x r u = true ∧
    Relation.ReflTransGen (fun a b => stp orc x r a b = true ∧ b < K) u v

/-- Reachable codes lie below `K`. -/
lemma Cl.lt {r K v : ℕ} (h : Cl orc x r K v) : v < K := by
  obtain ⟨u, hu, -, hpath⟩ := h
  cases hpath.cases_tail with
  | inl e => exact e ▸ hu
  | inr h => obtain ⟨_, -, -, hb⟩ := h; exact hb

/-- Reachable codes are closed under step pairs below `K`. -/
lemma Cl.step {r K u v : ℕ} (h : Cl orc x r K u) (hs : stp orc x r u v = true) (hv : v < K) :
    Cl orc x r K v := by
  obtain ⟨u₀, hu₀, hi, hpath⟩ := h
  exact ⟨u₀, hu₀, hi, hpath.tail ⟨hs, hv⟩⟩

/-! ## The initial marking -/

/-- The bounds of a search: registers at most `B`, the region and the counters fit. -/
def SBd (B P : ℕ) (S : St) : Prop :=
  S.Bd B ∧ S.Bs + S.K ≤ B ∧ S.Bs + S.K ≤ P ∧ S.K + 1 ≤ B

/-- **The initial marking**: from `iU` with `U = u₀`, the machine marks the initial codes
`u₀ ≤ v < K` and reaches `rl0` with `U = K`.

**Proof sketch.** Induction on `K - U`: test `U = K`, ask the initial-code decider, mark by an
access (`ac_run`), increment `U`. -/
theorem ini_run (φ : Bool) : ∀ (j : ℕ) (S : St) (M : ℤ → Bool), S.K - S.U = j → S.U ≤ S.K →
    S.T = 0 → S.T2 = 0 → S.Z = 0 → SBd B P S →
    ∃ M', MReach (A K₀) orc x (G x B P) (cf (.iU φ) S M 0) (cf (.rl0 φ) { S with U := S.K } M' 0) ∧
      Mono M M' ∧ Out S.Bs S.K M M' ∧
      (∀ v, S.U ≤ v → v < S.K → ini orc x (rr S φ) v = true → M' (cell S.Bs v) = true) ∧
      (∀ v, v < S.K → M' (cell S.Bs v) = true → M (cell S.Bs v) = true ∨
        ini orc x (rr S φ) v = true) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro S M hj hUK hT hT2 hZ hS
  obtain ⟨hbd, hB1, hP1, hK1⟩ := hS
  by_cases hU : S.U = S.K
  · refine ⟨M, ?_, Mono.refl M, Out.refl _ _ M, fun v h1 h2 => by omega, fun v _ h => Or.inl h⟩
    refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs [hU, ↓reduceIte]
    refine reach_cf (MReach.refl _) ?_ rfl
    ext <;> simp [hU]
  · have hlt : S.U < S.K := by omega
    -- the next round, from `U + 1`, with memory `M1`
    have next : ∀ M1 : ℤ → Bool, Mono M M1 → Out S.Bs S.K M M1 →
        (ini orc x (rr S φ) S.U = true → M1 (cell S.Bs S.U) = true) →
        (∀ v, v < S.K → M1 (cell S.Bs v) = true → M (cell S.Bs v) = true ∨
          ini orc x (rr S φ) v = true) →
        ∃ M', MReach (A K₀) orc x (G x B P) (cf (.iN φ) S M1 0)
          (cf (.rl0 φ) { S with U := S.K } M' 0) ∧ Mono M M' ∧ Out S.Bs S.K M M' ∧
          (∀ v, S.U ≤ v → v < S.K → ini orc x (rr S φ) v = true → M' (cell S.Bs v) = true) ∧
          (∀ v, v < S.K → M' (cell S.Bs v) = true → M (cell S.Bs v) = true ∨
            ini orc x (rr S φ) v = true) := by
      intro M1 hm1 ho1 hu1 hc1
      have hbd1 : St.Bd B { S with U := S.U + 1 } := by simp only [St.Bd] at hbd ⊢; omega
      obtain ⟨M', hr, hm, ho, hmark, hclean⟩ := ih (S.K - (S.U + 1)) (by omega)
        { S with U := S.U + 1 } M1 rfl (by simp only; omega) hT hT2 hZ
        ⟨hbd1, hB1, hP1, hK1⟩
      refine ⟨M', ?_, hm1.trans hm, ho1.trans ho, fun v h1 h2 h3 => ?_, fun v h1 h2 => ?_⟩
      · refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
        simp only [astep]; regs
        exact reach_cf hr (by ext <;> simp) rfl
      · rcases Nat.eq_or_lt_of_le h1 with e | e
        · subst e; exact hm _ (hu1 h3)
        · exact hmark v (by simp only; omega) h2 h3
      · rcases hclean v h1 h2 with h | h
        · exact hc1 v h1 h
        · exact Or.inr h
    refine ex1_pre (b := ?b1) ?p1 ?q1
    case p1 =>
      refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
      simp only [astep]; regs; rw [if_neg hU]
      refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
      simp only [astep, vword_whole₂]; regs
      rw [toV_rad]
      exact MReach.refl _
    by_cases hi : orc 1 (pairEncode x (pairEncode (Nat.bits S.U) (Nat.bits (rr S φ)))) = true
    · simp only [hi, ↓reduceIte]
      have hac := ac_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.ini φ) S M hbd hT
        hT2 hZ (by simp [Site.idx]; omega) (by simp [Site.idx]; omega)
      simp only [Site.set, Site.idx, St.toV_U, acExit] at hac
      obtain ⟨M', hr, rest⟩ := next (Function.update M (cell S.Bs S.U) true)
        (mono_update M _) (out_update M hlt) (fun _ => by simp)
        (fun v hv h => by
          by_cases e : v = S.U
          · subst e; exact Or.inr hi
          · left; rwa [Function.update_of_ne (fun h' => e (cell_inj h'))] at h)
      exact ⟨M', hac.trans hr, rest⟩
    · rw [Bool.not_eq_true] at hi
      simp only [hi, Bool.false_eq_true, ↓reduceIte]
      have hni : ini orc x (rr S φ) S.U = false := hi
      obtain ⟨M', hr, rest⟩ := next M (Mono.refl M) (Out.refl _ _ M)
        (by simp [hni]) (fun v _ h => Or.inl h)
      exact ⟨M', hr, rest⟩

/-! ## A relaxation round -/

/-- **The inner loop of a round**: for the marked source `U = u`, from `rlV` with `V = v₀`, the
machine marks the unmarked targets `v₀ ≤ v < K` of step pairs `(u, v)`, raising the change
flag if it marks one, and reaches `rlNU` with `V` cleared.

**Proof sketch.** Induction on `K - V`: test `V = K`; read the mark of `V` (`ac_run`); if
unmarked ask the step decider, and on a step pair mark `V` and raise the flag. -/
theorem inner_run (φ : Bool) (u : ℕ) : ∀ (j : ℕ) (S : St) (M : ℤ → Bool), S.K - S.V = j →
    S.V ≤ S.K → S.U = u → u < S.K → S.T = 0 → S.T2 = 0 → S.Z = 0 → S.ch ≤ 1 → SBd B P S →
    ∃ M' ch', MReach (A K₀) orc x (G x B P) (cf (.rlV φ) S M 0)
        (cf (.rlNU φ) { S with V := 0, ch := ch' } M' 0) ∧
      Mono M M' ∧ Out S.Bs S.K M M' ∧ ch' ≤ 1 ∧
      (∀ v, v < S.K → M' (cell S.Bs v) = true → M (cell S.Bs v) = true ∨
        stp orc x (rr S φ) u v = true) ∧
      (∀ v, S.V ≤ v → v < S.K → stp orc x (rr S φ) u v = true → M' (cell S.Bs v) = true) ∧
      (M' = M → ch' = S.ch) ∧ (M' ≠ M → ch' = 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro S M hj hVK hUu hu hT hT2 hZ hch hS
  obtain ⟨hbd, hB1, hP1, hK1⟩ := hS
  by_cases hV : S.V = S.K
  · refine ⟨M, S.ch, ?_, Mono.refl M, Out.refl _ _ M, hch, fun v _ h => Or.inl h,
      fun v h1 h2 => by omega, fun _ => rfl, fun h => absurd rfl h⟩
    refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs [hV, ↓reduceIte]
    refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs
    refine reach_cf (MReach.refl _) ?_ rfl
    ext <;> simp
  · have hlt : S.V < S.K := by omega
    -- continuing from `V + 1` with memory `M1` and flag `c1`
    have next : ∀ (M1 : ℤ → Bool) (c1 : ℕ), c1 ≤ 1 → Mono M M1 → Out S.Bs S.K M M1 →
        (∀ v, v < S.K → M1 (cell S.Bs v) = true → M (cell S.Bs v) = true ∨
          stp orc x (rr S φ) u v = true) →
        (stp orc x (rr S φ) u S.V = true → M1 (cell S.Bs S.V) = true) →
        (M1 = M → c1 = S.ch) → (M1 ≠ M → c1 = 1) →
        ∃ M' ch', MReach (A K₀) orc x (G x B P) (cf (.rlNV φ) { S with ch := c1 } M1 0)
            (cf (.rlNU φ) { S with V := 0, ch := ch' } M' 0) ∧
          Mono M M' ∧ Out S.Bs S.K M M' ∧ ch' ≤ 1 ∧
          (∀ v, v < S.K → M' (cell S.Bs v) = true → M (cell S.Bs v) = true ∨
            stp orc x (rr S φ) u v = true) ∧
          (∀ v, S.V ≤ v → v < S.K → stp orc x (rr S φ) u v = true →
            M' (cell S.Bs v) = true) ∧
          (M' = M → ch' = S.ch) ∧ (M' ≠ M → ch' = 1) := by
      intro M1 c1 hc1 hm1 ho1 hcl1 hmk1 he1 hn1
      have hbd1 : St.Bd B { S with V := S.V + 1, ch := c1 } := by
        simp only [St.Bd] at hbd ⊢; omega
      obtain ⟨M', ch', hr, hm, ho, hch', hcl, hmk, he, hn⟩ := ih (S.K - (S.V + 1)) (by omega)
        { S with V := S.V + 1, ch := c1 } M1 rfl (by simp only; omega) hUu hu hT hT2 hZ hc1
        ⟨hbd1, hB1, hP1, hK1⟩
      have hrr : rr { S with V := S.V + 1, ch := c1 } φ = rr S φ := by cases φ <;> rfl
      rw [hrr] at hcl hmk
      refine ⟨M', ch', ?_, hm1.trans hm, ho1.trans ho, hch', fun v hv h => ?_, fun v h1 h2 h3 => ?_,
        fun e => ?_, fun e => ?_⟩
      · have hbd2 : St.Bd B { S with ch := c1 } := by simp only [St.Bd] at hbd ⊢; omega
        refine step_of rfl hbd2 ⟨le_rfl, by omega⟩ ?_
        simp only [astep]; regs
        exact reach_cf hr (by ext <;> simp) rfl
      · rcases hcl v hv h with h' | h'
        · exact hcl1 v hv h'
        · exact Or.inr h'
      · rcases Nat.eq_or_lt_of_le h1 with e | e
        · subst e; exact hm _ (hmk1 h3)
        · exact hmk v (by simp only; omega) h2 h3
      · have e1 : M1 = M := by
          funext z
          have a1 := hm1 z
          have a2 := hm z
          rw [e] at a2
          cases h1 : M z <;> cases h2 : M1 z <;> simp_all
        rw [he (e.trans e1.symm), he1 e1]
      · by_cases e1 : M' = M1
        · rw [he e1]; exact hn1 (fun h => e (e1.trans h))
        · exact hn e1
    refine ex2_pre (b := ?b2) ?p2 ?q2
    case p2 =>
      refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
      simp only [astep]; regs; rw [if_neg hV]
      exact MReach.refl _
    have hac := ac_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.rV φ) S M hbd hT
      hT2 hZ (by simp [Site.idx]; omega) (by simp [Site.idx]; omega)
    simp only [Site.set, Site.idx, St.toV_V, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
      acExit] at hac
    refine ex2_pre hac ?_
    by_cases hb : M (cell S.Bs S.V) = true
    · simp only [hb, ↓reduceIte]
      obtain ⟨M', ch', hr, rest⟩ := next M S.ch hch (Mono.refl M) (Out.refl _ _ M)
        (fun v _ h => Or.inl h) (fun _ => hb) (fun _ => rfl) (fun h => absurd rfl h)
      exact ⟨M', ch', cont (by ext <;> rfl) hr, rest⟩
    · rw [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      refine ex2_pre (b := ?b3) ?p3 ?q3
      case p3 =>
        refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
        simp only [astep, vword_whole₃]; regs
        simp only [toV_rad, hUu]
        exact MReach.refl _
      by_cases hs : orc 2 (pairEncode x (pairEncode (Nat.bits u) (pairEncode (Nat.bits S.V)
          (Nat.bits (rr S φ))))) = true
      · simp only [hs, ↓reduceIte]
        have hac2 := ac_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.sV φ) S M hbd
          hT hT2 hZ (by simp [Site.idx]; omega) (by simp [Site.idx]; omega)
        simp only [Site.set, Site.idx, St.toV_V, acExit] at hac2
        refine ex2_pre hac2 ?_
        have hbd0 : St.Bd B { S with ch := 0 } := by simp only [St.Bd] at hbd ⊢; omega
        refine ex2_pre (b := ?b4) ?p4 ?q4
        case p4 =>
          refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
          simp only [astep]; regs
          refine step_of rfl hbd0 ⟨le_rfl, by omega⟩ ?_
          simp only [astep]; regs
          exact MReach.refl _
        have hne : Function.update M (cell S.Bs S.V) true ≠ M := by
          intro e
          have := congrFun e (cell S.Bs S.V)
          rw [Function.update_self, hb] at this
          cases this
        obtain ⟨M', ch', hr, rest⟩ := next (Function.update M (cell S.Bs S.V) true) 1 le_rfl
          (mono_update M _) (out_update M hlt)
          (fun v hv h => by
            by_cases e : v = S.V
            · subst e; exact Or.inr hs
            · left; rwa [Function.update_of_ne (fun h' => e (cell_inj h'))] at h)
          (fun _ => by simp) (fun e => absurd e hne) (fun _ => rfl)
        exact ⟨M', ch', cont (by ext <;> simp) hr, rest⟩
      · rw [Bool.not_eq_true] at hs
        simp only [hs, Bool.false_eq_true, ↓reduceIte]
        have hns : stp orc x (rr S φ) u S.V = false := hs
        obtain ⟨M', ch', hr, rest⟩ := next M S.ch hch (Mono.refl M) (Out.refl _ _ M)
          (fun v _ h => Or.inl h) (fun h => by rw [hns] at h; cases h) (fun _ => rfl)
          (fun h => absurd rfl h)
        exact ⟨M', ch', cont (by ext <;> rfl) hr, rest⟩

/-- Memory that grows from `M` to `M'` and back is unchanged. -/
lemma mono_antisymm {M M' : ℤ → Bool} (h : Mono M M') (h' : Mono M' M) : M' = M := by
  funext z
  have a := h z
  have b := h' z
  cases h1 : M z <;> cases h2 : M' z <;> simp_all

/-- **The outer loop of a round**: from `rlU` with `U = u₀` and `V` clear, the machine runs
the inner loop for every marked source `u₀ ≤ U < K` and reaches `rlE` with `U = K`. Every new
mark is a step target of an earlier mark (so a set closed under step pairs and containing the
old marks contains the new ones); if nothing was marked, the marks were closed under step
pairs from the sources `u₀ ≤ u < K`; the change flag is raised iff something was marked.

**Proof sketch.** Induction on `K - U`: read the mark of `U` (`ac_run`); if marked run
`inner_run`; increment `U`. -/
theorem outer_run (φ : Bool) : ∀ (j : ℕ) (S : St) (M : ℤ → Bool), S.K - S.U = j → S.U ≤ S.K →
    S.V = 0 → S.T = 0 → S.T2 = 0 → S.Z = 0 → S.ch ≤ 1 → SBd B P S →
    ∃ M' ch', MReach (A K₀) orc x (G x B P) (cf (.rlU φ) S M 0)
        (cf (.rlE φ) { S with U := S.K, ch := ch' } M' 0) ∧
      Mono M M' ∧ Out S.Bs S.K M M' ∧ ch' ≤ 1 ∧
      (∀ Q : ℕ → Prop, (∀ a b, Q a → a < S.K → b < S.K →
          stp orc x (rr S φ) a b = true → Q b) →
        (∀ v, v < S.K → M (cell S.Bs v) = true → Q v) →
        ∀ v, v < S.K → M' (cell S.Bs v) = true → Q v) ∧
      (M' = M → ∀ a b, S.U ≤ a → a < S.K → b < S.K → M (cell S.Bs a) = true →
        stp orc x (rr S φ) a b = true → M (cell S.Bs b) = true) ∧
      (M' = M → ch' = S.ch) ∧ (M' ≠ M → ch' = 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro S M hj hUK hV hT hT2 hZ hch hS
  obtain ⟨hbd, hB1, hP1, hK1⟩ := hS
  by_cases hU : S.U = S.K
  · refine ⟨M, S.ch, ?_, Mono.refl M, Out.refl _ _ M, hch, fun Q _ h => h,
      fun _ a b h1 h2 => by omega, fun _ => rfl, fun h => absurd rfl h⟩
    refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
    simp only [astep]; regs [hU, ↓reduceIte]
    refine reach_cf (MReach.refl _) ?_ rfl
    ext <;> simp [hU]
  · have hlt : S.U < S.K := by omega
    -- continuing from `U + 1` with memory `M1` and flag `c1`
    have next : ∀ (M1 : ℤ → Bool) (c1 : ℕ), c1 ≤ 1 → Mono M M1 → Out S.Bs S.K M M1 →
        (∀ Q : ℕ → Prop, (∀ a b, Q a → a < S.K → b < S.K →
            stp orc x (rr S φ) a b = true → Q b) →
          (∀ v, v < S.K → M (cell S.Bs v) = true → Q v) →
          ∀ v, v < S.K → M1 (cell S.Bs v) = true → Q v) →
        (M1 = M → ∀ b, b < S.K → M (cell S.Bs S.U) = true →
          stp orc x (rr S φ) S.U b = true → M (cell S.Bs b) = true) →
        (M1 = M → c1 = S.ch) → (M1 ≠ M → c1 = 1) →
        ∃ M' ch', MReach (A K₀) orc x (G x B P) (cf (.rlNU φ) { S with ch := c1 } M1 0)
            (cf (.rlE φ) { S with U := S.K, ch := ch' } M' 0) ∧
          Mono M M' ∧ Out S.Bs S.K M M' ∧ ch' ≤ 1 ∧
          (∀ Q : ℕ → Prop, (∀ a b, Q a → a < S.K → b < S.K →
              stp orc x (rr S φ) a b = true → Q b) →
            (∀ v, v < S.K → M (cell S.Bs v) = true → Q v) →
            ∀ v, v < S.K → M' (cell S.Bs v) = true → Q v) ∧
          (M' = M → ∀ a b, S.U ≤ a → a < S.K → b < S.K → M (cell S.Bs a) = true →
            stp orc x (rr S φ) a b = true → M (cell S.Bs b) = true) ∧
          (M' = M → ch' = S.ch) ∧ (M' ≠ M → ch' = 1) := by
      intro M1 c1 hc1 hm1 ho1 hq1 hcl1 he1 hn1
      have hbd1 : St.Bd B { S with U := S.U + 1, ch := c1 } := by
        simp only [St.Bd] at hbd ⊢; omega
      obtain ⟨M', ch', hr, hm, ho, hch', hq, hcl, he, hn⟩ := ih (S.K - (S.U + 1)) (by omega)
        { S with U := S.U + 1, ch := c1 } M1 rfl (by simp only; omega) hV hT hT2 hZ hc1
        ⟨hbd1, hB1, hP1, hK1⟩
      have hrr : rr { S with U := S.U + 1, ch := c1 } φ = rr S φ := by cases φ <;> rfl
      rw [hrr] at hq hcl
      have hbd2 : St.Bd B { S with ch := c1 } := by simp only [St.Bd] at hbd ⊢; omega
      refine ⟨M', ch', ?_, hm1.trans hm, ho1.trans ho, hch', fun Q hQ hM => hq Q hQ (hq1 Q hQ hM),
        fun e => ?_, fun e => ?_, fun e => ?_⟩
      · refine step_of rfl hbd2 ⟨le_rfl, by omega⟩ ?_
        simp only [astep]; regs
        exact reach_cf hr (by ext <;> simp) rfl
      · have e1 : M1 = M := mono_antisymm hm1 (e ▸ hm)
        intro a b ha hab hb hMa hs
        rcases Nat.eq_or_lt_of_le ha with e2 | e2
        · subst e2; exact hcl1 e1 b hb hMa hs
        · have := hcl (e ▸ e1.symm ▸ rfl) a b (by simp only; omega) hab hb (e1 ▸ hMa) hs
          rwa [e1] at this
      · have e1 : M1 = M := mono_antisymm hm1 (e ▸ hm)
        rw [he (e.trans e1.symm), he1 e1]
      · by_cases e1 : M' = M1
        · rw [he e1]; exact hn1 (fun h => e (e1.trans h))
        · exact hn e1
    refine ex2_pre (b := ?b5) ?p5 ?q5
    case p5 =>
      refine step_of rfl hbd ⟨le_rfl, by omega⟩ ?_
      simp only [astep]; regs; rw [if_neg hU]
      exact MReach.refl _
    have hac := ac_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.rU φ) S M hbd hT
      hT2 hZ (by simp [Site.idx]; omega) (by simp [Site.idx]; omega)
    simp only [Site.set, Site.idx, St.toV_U, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
      acExit] at hac
    refine ex2_pre hac ?_
    by_cases hb : M (cell S.Bs S.U) = true
    · simp only [hb, ↓reduceIte]
      obtain ⟨M1, c1, hr1, hm1, ho1, hc1, hcl1, hmk1, he1, hn1⟩ :=
        inner_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) φ S.U (S.K - S.V) S M rfl
          (by omega) rfl hlt hT hT2 hZ hch ⟨hbd, hB1, hP1, hK1⟩
      obtain ⟨M', ch', hr, rest⟩ := next M1 c1 hc1 hm1 ho1
        (fun Q hQ hM v hv h => by
          rcases hcl1 v hv h with h' | h'
          · exact hM v hv h'
          · exact hQ _ _ (hM _ hlt hb) hlt hv h')
        (fun e b hbK _ hs => by
          have := hmk1 b (by omega) hbK hs
          rwa [e] at this)
        (fun e => he1 e) (fun e => hn1 e)
      refine ⟨M', ch', hr1.trans ?_, rest⟩
      exact cont (by ext <;> simp [hV]) hr
    · rw [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨M', ch', hr, rest⟩ := next M S.ch hch (Mono.refl M) (Out.refl _ _ M)
        (fun Q _ h => h) (fun _ b _ h => by rw [hb] at h; cases h) (fun _ => rfl)
        (fun h => absurd rfl h)
      exact ⟨M', ch', cont (by ext <;> rfl) hr, rest⟩

end ExpBFS

end Complexity.LogProg
