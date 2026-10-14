/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.ExpBFS.Machine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Routines of the search machine

Run lemmas for the straight-line parts of the breadth-first search memory machine
`Complexity.LogProg.ExpBFS.A`: single steps (`step_of`, `mright_of`, …), the loop sites
(instances of the generic loops of `TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops`,
transferred to the memory machine by `Complexity.LogProg.MReach.of_areach`), a memory access
(`ac_run`: walk the head out to `Bs + idx`, read or set the bit, walk back), the setup
(`setup_run`) and the width computation (`wk_run`).

Infrastructure for [AB09, §4.1.1, proof of Theorem 4.2]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ExpBFS.G` — the guard: registers at most `B`, the memory head in
  `[0, P]`.

## Main results

* `Complexity.LogProg.ExpBFS.preS_A` — the machine meets the syntactic preconditions.
* `Complexity.LogProg.ExpBFS.ac_run` — a memory access.
* `Complexity.LogProg.ExpBFS.setup_run`, `Complexity.LogProg.ExpBFS.wk_run`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Theorem 4.2.)
-/

namespace Complexity.LogProg

namespace ExpBFS

open Turing

variable {K₀ : ℕ}

/-- The deterministic part of the search machine. -/
abbrev Ad (K₀ : ℕ) : ARM 17 4 (Lb K₀) := (A K₀).detPart false

/-- A configuration of the search machine with a named register file. -/
abbrev cf (l : Lb K₀) (st : St) (M : ℤ → Bool) (p : ℤ) : MConf 17 (Lb K₀) :=
  ((some l, st.toV, none), (M, p))

/-- The radius registers are not `U`. -/
lemma rad_ne_U (p : Ph3) : rU ≠ rad p := by cases p <;> decide

/-- The radius registers are neither `U` nor `V`. -/
lemma rad_ne_V (p : Ph3) : rV ≠ rad p := by cases p <;> decide

/-- **The search machine meets the syntactic preconditions** everywhere: its equality tests
compare distinct registers and its calls have distinct arguments. -/
lemma preS_A (x : List Bool) (a : AConf 17 (Lb K₀)) : PreS (Ad K₀) x a := by
  rcases a with ⟨_ | l, v, res⟩
  · trivial
  · cases l with
    | iC φ => simp [PreS, MARM.detPart, A, rad_ne_U]
    | rlS φ => cases φ <;> simp [PreS, MARM.detPart, A, rad, toPh] <;> decide
    | d1 i => simp [PreS, MARM.detPart, A]
    | fz i => simp [PreS, MARM.detPart, A]
    | nz i => by_cases h : i.val = 0 <;> simp [PreS, MARM.detPart, A, h]
    | cp k j => fin_cases j <;> simp [PreS, MARM.detPart, A, cpI]
    | mv j => fin_cases j <;> simp [PreS, MARM.detPart, A, mvI]
    | sh p j => fin_cases j <;> simp [PreS, MARM.detPart, A, shI]
    | ac st ph =>
      rcases ph with j | _ | ⟨b, j⟩
      · fin_cases j <;> simp [PreS, MARM.detPart, A, acI]
      · by_cases h : st.set <;> simp [PreS, MARM.detPart, A, acI, h]
      · fin_cases j <;> simp [PreS, MARM.detPart, A, acI]
    | _ => simp [PreS, MARM.detPart, A] <;> decide

variable {orc : Fin 4 → List Bool → Bool} {x : List Bool} {B P : ℕ}

/-- **The guard** of the search machine's runs: the syntactic preconditions, every register
at most `B`, the memory head in `[0, P]`. -/
def G (x : List Bool) (B P : ℕ) (c : MConf 17 (Lb K₀)) : Prop :=
  GuardLe (Ad K₀) x B c.1 ∧ 0 ≤ c.2.2 ∧ c.2.2 ≤ P

/-- A bounded register file with the memory head in range meets the guard. -/
lemma g_of {st : St} {M : ℤ → Bool} {p : ℤ} (hbd : st.Bd B) (hp : 0 ≤ p ∧ p ≤ P)
    (l : Lb K₀) : G x B P (cf l st M p) := ⟨⟨preS_A x _, hbd.toV⟩, hp⟩

/-- One register step from a bounded register file. -/
lemma step_of {st : St} {M : ℤ → Bool} {p : ℤ} {l : Lb K₀} {i : Ins 17 4 (Lb K₀)}
    {c : MConf 17 (Lb K₀)} (hA : A K₀ l = .det i) (hbd : st.Bd B) (hp : 0 ≤ p ∧ p ≤ P)
    (h : MReach (A K₀) orc x (G x B P) (astep (fun _ => i) orc x (some l, st.toV, none), (M, p))
      c) :
    MReach (A K₀) orc x (G x B P) (cf l st M p) c := by
  refine MReach.step (g_of hbd hp l) ?_
  have e : mstep (A K₀) orc x (cf l st M p) =
      (astep (fun _ => i) orc x (some l, st.toV, none), (M, p)) := by
    simp only [mstep, hA]
  rw [e]; exact h

/-- One halting register step from a bounded register file. -/
lemma stepH_of {st : St} {M : ℤ → Bool} {p : ℤ} {l : Lb K₀} {i : Ins 17 4 (Lb K₀)} {r : Bool}
    (hA : A K₀ l = .det i) (hbd : st.Bd B) (hp : 0 ≤ p ∧ p ≤ P)
    (h : MHalt (A K₀) orc x (G x B P) (astep (fun _ => i) orc x (some l, st.toV, none), (M, p))
      r) :
    MHalt (A K₀) orc x (G x B P) (cf l st M p) r := by
  refine MHalt.step (g_of hbd hp l) ?_
  have e : mstep (A K₀) orc x (cf l st M p) =
      (astep (fun _ => i) orc x (some l, st.toV, none), (M, p)) := by
    simp only [mstep, hA]
  rw [e]; exact h

/-- A memory head move to the right. -/
lemma mright_of {st : St} {M : ℤ → Bool} {p : ℤ} {l l' : Lb K₀} {c : MConf 17 (Lb K₀)}
    (hA : A K₀ l = .mright l') (hbd : st.Bd B) (hp : 0 ≤ p ∧ p ≤ P)
    (h : MReach (A K₀) orc x (G x B P) (cf l' st M (p + 1)) c) :
    MReach (A K₀) orc x (G x B P) (cf l st M p) c := by
  refine MReach.step (g_of hbd hp l) ?_
  have e : mstep (A K₀) orc x (cf l st M p) = cf l' st M (p + 1) := by simp only [cf, mstep, hA]
  rw [e]; exact h

/-- A memory head move to the left. -/
lemma mleft_of {st : St} {M : ℤ → Bool} {p : ℤ} {l l' : Lb K₀} {c : MConf 17 (Lb K₀)}
    (hA : A K₀ l = .mleft l') (hbd : st.Bd B) (hp : 0 ≤ p ∧ p ≤ P)
    (h : MReach (A K₀) orc x (G x B P) (cf l' st M (p - 1)) c) :
    MReach (A K₀) orc x (G x B P) (cf l st M p) c := by
  refine MReach.step (g_of hbd hp l) ?_
  have e : mstep (A K₀) orc x (cf l st M p) = cf l' st M (p - 1) := by simp only [cf, mstep, hA]
  rw [e]; exact h

/-- Setting the memory bit under the head. -/
lemma mset_of {st : St} {M : ℤ → Bool} {p : ℤ} {l l' : Lb K₀} {c : MConf 17 (Lb K₀)}
    (hA : A K₀ l = .mset l') (hbd : st.Bd B) (hp : 0 ≤ p ∧ p ≤ P)
    (h : MReach (A K₀) orc x (G x B P) (cf l' st (Function.update M p true) p) c) :
    MReach (A K₀) orc x (G x B P) (cf l st M p) c := by
  refine MReach.step (g_of hbd hp l) ?_
  have e : mstep (A K₀) orc x (cf l st M p) = cf l' st (Function.update M p true) p := by
    simp only [cf, mstep, hA]
  rw [e]; exact h

/-- Branching on the memory bit under the head. -/
lemma mread_of {st : St} {M : ℤ → Bool} {p : ℤ} {l l₁ l₀ : Lb K₀} {c : MConf 17 (Lb K₀)}
    (hA : A K₀ l = .mread l₁ l₀) (hbd : st.Bd B) (hp : 0 ≤ p ∧ p ≤ P)
    (h : MReach (A K₀) orc x (G x B P) (cf (if M p then l₁ else l₀) st M p) c) :
    MReach (A K₀) orc x (G x B P) (cf l st M p) c := by
  refine MReach.step (g_of hbd hp l) ?_
  have e : mstep (A K₀) orc x (cf l st M p) = cf (if M p then l₁ else l₀) st M p := by
    simp only [cf, mstep, hA]
  rw [e]; exact h

/-- Continue a run from an equal register file. -/
lemma cont {st st' : St} {M : ℤ → Bool} {p : ℤ} {l : Lb K₀} {c : MConf 17 (Lb K₀)}
    (e : st = st') (h : MReach (A K₀) orc x (G x B P) (cf l st' M p) c) :
    MReach (A K₀) orc x (G x B P) (cf l st M p) c := e ▸ h

/-- Transfer a run of the deterministic part through `GuardLe` to the search machine. -/
lemma of_areach {a a' : AConf 17 (Lb K₀)} {M : ℤ → Bool} {p : ℤ} (hp : 0 ≤ p ∧ p ≤ P)
    (h : AReach (Ad K₀) orc x (GuardLe (Ad K₀) x B) a a') (hlive : a'.1 ≠ none) :
    MReach (A K₀) orc x (G x B P) (a, (M, p)) (a', (M, p)) :=
  (MReach.of_areach (M, p) h hlive).mono fun c ⟨h1, h2⟩ => ⟨h1, by rw [h2]; exact hp⟩

/-- A clear step. -/
lemma clr_step {st : St} {M : ℤ → Bool} {p : ℤ} {l l' : Lb K₀} {r : Fin 17}
    {c : MConf 17 (Lb K₀)} (hA : A K₀ l = .det (.clr r l')) (hbd : st.Bd B) (hp : 0 ≤ p ∧ p ≤ P)
    (h : MReach (A K₀) orc x (G x B P) ((some l', Function.update st.toV r 0, none), (M, p)) c) :
    MReach (A K₀) orc x (G x B P) (cf l st M p) c :=
  step_of hA hbd hp h

/-- An increment step. -/
lemma inc_step {st : St} {M : ℤ → Bool} {p : ℤ} {l l' : Lb K₀} {r : Fin 17}
    {c : MConf 17 (Lb K₀)} (hA : A K₀ l = .det (.inc r l')) (hbd : st.Bd B) (hp : 0 ≤ p ∧ p ≤ P)
    (h : MReach (A K₀) orc x (G x B P)
      ((some l', Function.update st.toV r (st.toV r + 1), none), (M, p)) c) :
    MReach (A K₀) orc x (G x B P) (cf l st M p) c :=
  step_of hA hbd hp h

/-! ## Loop sites -/

/-- Copy sites have distinct registers, all different from `Z`. -/
lemma cp_ne (k : CpS K₀) : cpSrc k ≠ cpDst k ∧ cpSrc k ≠ rZ ∧ cpDst k ≠ rZ := by
  rcases k with p | p | ⟨p, i⟩ | p | p | p | st | st | _
  · cases p <;> simp only [cpSrc, cpDst, rad] <;> decide
  all_goals first
    | (simp only [cpSrc, cpDst]; decide)
    | (cases st <;> simp only [cpSrc, cpDst, Site.idx] <;> decide)

/-- **A copy site** adds the source to the target. -/
theorem cp_run (k : CpS K₀) (st : St) (M : ℤ → Bool) (p : ℤ) (hp : 0 ≤ p ∧ p ≤ P)
    (hbd : st.Bd B) (hZ : st.Z = 0) (hb : st.toV (cpDst k) + st.toV (cpSrc k) ≤ B) :
    MReach (A K₀) orc x (G x B P) (cf (.cp k 0) st M p)
      ((some (cpExit k), Function.update st.toV (cpDst k)
        (st.toV (cpDst k) + st.toV (cpSrc k)), none), (M, p)) :=
  of_areach hp (copy_run (A := Ad K₀) (oracle := orc) (x := x) (B := B) (l := .cp k 0)
    (l1 := .cp k 1) (l2 := .cp k 2) (l3 := .cp k 3) (l4 := .cp k 4) (l5 := .cp k 5)
    (l6 := .cp k 6) (lx := cpExit k) (cp_ne k).1 (cp_ne k).2.1 (cp_ne k).2.2 rfl rfl rfl rfl
    rfl rfl rfl _ hZ hbd.toV hb) (by simp)

/-- **The shift site** of phase `p` multiplies `K` by `2 ^ C` and clears `C`. -/
theorem sh_run (q : Ph3) (st : St) (M : ℤ → Bool) (p : ℤ) (hp : 0 ≤ p ∧ p ≤ P)
    (hbd : st.Bd B) (hZ : st.Z = 0) (hb : st.K * 2 ^ st.C ≤ B) :
    MReach (A K₀) orc x (G x B P) (cf (.sh q 0) st M p)
      (cf (.cp (.KB1 q) 0) { st with C := 0, K := st.K * 2 ^ st.C } M p) := by
  have h := shl_run (A := Ad K₀) (oracle := orc) (x := x) (B := B) (c := rC) (r := rK) (z := rZ)
    (l := .sh q 0) (l1 := .sh q 1) (l2 := .sh q 2) (l3 := .sh q 3) (l4 := .sh q 4)
    (l5 := .sh q 5) (l6 := .sh q 6) (l7 := .sh q 7) (l8 := .sh q 8) (lx := .cp (.KB1 q) 0)
    (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl rfl rfl rfl rfl _ st.toV rfl hZ
    hbd.toV hb
  regs at h
  exact of_areach hp h (by simp)

/-- **The move site** `c1 := c1 + c`, `c := 0`. -/
theorem mv_run (st : St) (M : ℤ → Bool) (p : ℤ) (hp : 0 ≤ p ∧ p ≤ P) (hbd : st.Bd B)
    (hb : st.c1 + st.c ≤ B) :
    MReach (A K₀) orc x (G x B P) (cf (.mv 0) st M p)
      (cf (.cp .s1 0) { st with c := 0, c1 := st.c1 + st.c } M p) := by
  have h := move_run (A := Ad K₀) (oracle := orc) (x := x) (B := B) (r := rc) (t := rc1)
    (l := .mv 0) (l1 := .mv 1) (l2 := .mv 2) (lx := .cp .s1 0) (by decide) rfl rfl rfl _
    st.toV rfl hbd.toV hb
  regs at h
  exact of_areach hp h (by simp)

/-- Rewriting the end configuration of a run along equal register files and head positions. -/
lemma reach_cf {a : MConf 17 (Lb K₀)} {l : Lb K₀} {st st' : St} {M : ℤ → Bool} {p p' : ℤ}
    (h : MReach (A K₀) orc x (G x B P) a (cf l st M p)) (e1 : st = st') (e2 : p = p') :
    MReach (A K₀) orc x (G x B P) a (cf l st' M p') := e1 ▸ e2 ▸ h

/-! ## Memory accesses -/

/-- The index register of an access site is `U` or `V`. -/
lemma idx_cases (st : Site) : st.idx = rU ∨ st.idx = rV := by
  cases st <;> simp [Site.idx]

/-- **The outward walk**: from `wo 0` with `T = k`, the head moves `k` cells right while `T`
counts down to `0` and `T2` counts up by `k`.

**Proof sketch.** Induction on `k`; one round is `jz`, `dec T`, `inc T2`, `mright`. -/
theorem wo_run (st : Site) : ∀ (k : ℕ) (S : St) (M : ℤ → Bool) (p : ℤ), S.T = k → S.Bd B →
    S.T2 + k ≤ B → 0 ≤ p → p + k ≤ P →
    MReach (A K₀) orc x (G x B P) (cf (.ac st (.wo 0)) S M p)
      (cf (.ac st .op) { S with T := 0, T2 := S.T2 + k } M (p + k)) := by
  intro k
  induction k with
  | zero =>
    intro S M p hT hbd hb hp0 hpP
    refine step_of rfl hbd ⟨hp0, by omega⟩ ?_
    simp only [astep, St.toV_T, hT, ↓reduceIte]
    exact reach_cf (MReach.refl _) (by ext <;> simp [hT]) (by simp)
  | succ k ih =>
    intro S M p hT hbd hb hp0 hpP
    refine step_of rfl hbd ⟨hp0, by omega⟩ ?_
    simp only [astep, St.toV_T, hT, Nat.add_one_ne_zero, ↓reduceIte]
    refine step_of rfl hbd ⟨hp0, by omega⟩ ?_
    simp only [astep]; regs [hT, Nat.add_sub_cancel]
    have hbd1 : St.Bd B { S with T := k } := by simp only [St.Bd] at hbd ⊢; omega
    refine step_of rfl hbd1 ⟨hp0, by omega⟩ ?_
    simp only [astep]; regs
    have hbd2 : St.Bd B { S with T := k, T2 := S.T2 + 1 } := by
      simp only [St.Bd] at hbd ⊢; omega
    refine mright_of rfl hbd2 ⟨hp0, by omega⟩ ?_
    refine reach_cf (ih _ M (p + 1) rfl hbd2 (by simp only; omega) (by omega)
      (by push_cast at hpP ⊢; omega)) (by ext <;> simp; omega) (by push_cast; ring)

/-- **The return walk**: from `wb b 0` with `T2 = k`, the head moves `k` cells left while `T2`
counts down to `0`, and the access exits with the bit `b`.

**Proof sketch.** Induction on `k`; one round is `jz`, `dec T2`, `mleft`. -/
theorem wb_run (st : Site) (b : Bool) : ∀ (k : ℕ) (S : St) (M : ℤ → Bool) (p : ℤ), S.T2 = k →
    S.Bd B → 0 ≤ p - k → p ≤ P →
    MReach (A K₀) orc x (G x B P) (cf (.ac st (.wb b 0)) S M p)
      (cf (acExit st b) { S with T2 := 0 } M (p - k)) := by
  intro k
  induction k with
  | zero =>
    intro S M p hT hbd hp0 hpP
    refine step_of rfl hbd ⟨by omega, hpP⟩ ?_
    simp only [astep, St.toV_T2, hT, ↓reduceIte]
    exact reach_cf (MReach.refl _) (by ext <;> simp [hT]) (by simp)
  | succ k ih =>
    intro S M p hT hbd hp0 hpP
    refine step_of rfl hbd ⟨by omega, hpP⟩ ?_
    simp only [astep, St.toV_T2, hT, Nat.add_one_ne_zero, ↓reduceIte]
    refine step_of rfl hbd ⟨by omega, hpP⟩ ?_
    simp only [astep]; regs [hT, Nat.add_sub_cancel]
    have hbd1 : St.Bd B { S with T2 := k } := by simp only [St.Bd] at hbd ⊢; omega
    refine mleft_of rfl hbd1 ⟨by omega, hpP⟩ ?_
    refine reach_cf (ih _ M (p - 1) rfl hbd1 (by push_cast at hp0 ⊢; omega) (by omega))
      (by ext <;> simp) (by push_cast; ring)

/-- **A memory access** at site `st`, from the start of its two copies with `T`, `T2`, `Z`
clear and the memory head at `0`: the access ends at the site's exit for the bit read at
`Bs + idx` (or `true` after setting it), with the same register file and the head back at `0`;
a setting site sets the bit at `Bs + idx`.

**Proof sketch.** Copy `Bs` and the index into `T` (`cp_run`), walk out (`wo_run`), read or
set (`mread_of`, `mset_of`), walk back (`wb_run`). -/
theorem ac_run (st : Site) (S : St) (M : ℤ → Bool) (hbd : S.Bd B) (hT : S.T = 0)
    (hT2 : S.T2 = 0) (hZ : S.Z = 0) (hB : S.Bs + S.toV st.idx ≤ B)
    (hP : S.Bs + S.toV st.idx ≤ P) :
    MReach (A K₀) orc x (G x B P) (cf (.cp (.aB st) 0) S M 0)
      (cf (acExit st (st.set || M ((S.Bs + S.toV st.idx : ℕ) : ℤ))) S
        (if st.set then Function.update M ((S.Bs + S.toV st.idx : ℕ) : ℤ) true else M) 0) := by
  set u := S.toV st.idx with hu
  have h1 := cp_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.aB st) S M 0
    ⟨le_rfl, by omega⟩
    hbd hZ (by simp only [cpDst, cpSrc]; regs; omega)
  simp only [cpDst, cpSrc, cpExit] at h1
  regs at h1
  simp only [hT, zero_add] at h1
  have hbd1 : St.Bd B { S with T := S.Bs } := by simp only [St.Bd] at hbd ⊢; omega
  have hidx1 : ({ S with T := S.Bs } : St).toV st.idx = u := by
    rcases idx_cases st with h | h <;> simp [hu, h]
  have h2 := cp_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.aI st)
    { S with T := S.Bs } M 0
    ⟨le_rfl, by omega⟩ hbd1 (by simpa using hZ) (by
      simp only [cpDst, cpSrc]; rw [hidx1]; simp only [St.toV_T]; omega)
  simp only [cpDst, cpSrc, cpExit] at h2
  rw [hidx1] at h2
  regs at h2
  have hbd2 : St.Bd B { S with T := S.Bs + u } := by simp only [St.Bd] at hbd ⊢; omega
  have h3 := wo_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) st (S.Bs + u)
    { S with T := S.Bs + u } M 0 rfl hbd2 (by simp only; omega) le_rfl (by push_cast; omega)
  simp only [zero_add] at h3
  set S3 : St := { S with T := 0, T2 := S.Bs + u } with hS3
  have hS3' : ({ ({ S with T := S.Bs + u } : St) with T := 0, T2 := S.T2 + (S.Bs + u) } : St)
      = S3 := by ext <;> simp [hS3, hT2]
  rw [hS3'] at h3
  have hbd3 : S3.Bd B := by simp only [hS3, St.Bd] at hbd ⊢; omega
  have hend : ({ S3 with T2 := 0 } : St) = S := by ext <;> simp [hS3, hT, hT2]
  refine ((h1.trans h2).trans h3).trans ?_
  by_cases hs : st.set
  · refine mset_of (l' := .ac st (.wb true 0)) (by simp [A, acI, hs]) hbd3
      ⟨by omega, by push_cast; omega⟩ ?_
    have h4 := wb_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) st true (S.Bs + u) S3
      (Function.update M ((S.Bs + u : ℕ) : ℤ) true) ((S.Bs + u : ℕ) : ℤ) rfl hbd3 (by simp)
      (by push_cast; omega)
    simp only [hs, Bool.true_or, ↓reduceIte]
    exact reach_cf h4 hend (by simp)
  · refine mread_of (l₁ := .ac st (.wb true 0)) (l₀ := .ac st (.wb false 0))
      (by simp [A, acI, hs]) hbd3 ⟨by omega, by push_cast; omega⟩ ?_
    have h4 := wb_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) st
      (M ((S.Bs + u : ℕ) : ℤ)) (S.Bs + u) S3 M ((S.Bs + u : ℕ) : ℤ) rfl hbd3 (by simp)
      (by push_cast; omega)
    simp only [hs, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
    have e : (if M ((S.Bs + u : ℕ) : ℤ) = true then Lb.ac st (.wb true 0)
        else Lb.ac st (.wb false 0)) = Lb.ac (K₀ := K₀) st (.wb (M ((S.Bs + u : ℕ) : ℤ)) 0) := by
      cases M ((S.Bs + u : ℕ) : ℤ) <;> rfl
    rw [e]
    exact reach_cf h4 hend (by simp)

/-! ## The setup -/

/-- The number of halvings that take `k` to `0`. -/
def hv (k : ℕ) : ℕ := if k = 0 then 0 else Nat.log 2 k + 1

/-- One halving less. -/
lemma hv_div (k : ℕ) (hk : k ≠ 0) : hv k = hv (k / 2) + 1 := by
  unfold hv
  rcases Nat.lt_or_ge k 2 with h | h
  · obtain rfl : k = 1 := by omega
    simp
  · have h2 : k / 2 ≠ 0 := by omega
    rw [if_neg hk, if_neg h2, Nat.log_of_one_lt_of_le (by decide) h]

/-- The value of `Lg` after the setup: `1 +` the number of halvings of `|x|`. -/
def lgv (n : ℕ) : ℕ := 1 + hv n

/-- `Lg` bounds the logarithm of the input length. -/
lemma logSpace_le_lgv (n : ℕ) : logSpace n ≤ lgv n := by
  unfold lgv hv logSpace
  split_ifs with h
  · subst h; simp
  · omega

/-- `Lg` exceeds the logarithm of the input length by at most one. -/
lemma lgv_le (n : ℕ) : lgv n ≤ logSpace n + 1 := by
  unfold lgv hv logSpace
  split_ifs <;> omega

/-- `Lg` is at most `|x| + 1`. -/
lemma lgv_le_succ (n : ℕ) : lgv n ≤ n + 1 := by
  unfold lgv hv
  split_ifs with h
  · omega
  · have := Nat.log_lt_self 2 h
    omega

/-- **The logarithm loop**: from `lg0` with `N = k`, the machine halves `N` to `0`, adding the
number of halvings to `Lg`, and reaches the first width computation.

**Proof sketch.** Strong induction on `k` (`hv_div`). -/
theorem lg_run : ∀ (k : ℕ) (S : St) (M : ℤ → Bool), S.N = k → S.Bd B → S.Lg + hv k ≤ B →
    MReach (A K₀) orc x (G x B P) (cf .lg0 S M 0)
      (cf (.cp (.radX .fst) 0) { S with N := 0, Lg := S.Lg + hv k } M 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S M hN hbd hb
  by_cases hk : k = 0
  · subst hk
    refine step_of rfl hbd ⟨le_rfl, Nat.cast_nonneg _⟩ ?_
    simp only [astep]; regs [hN, ↓reduceIte]
    exact reach_cf (MReach.refl _) (by ext <;> simp [hN, hv]) rfl
  · refine step_of rfl hbd ⟨le_rfl, Nat.cast_nonneg _⟩ ?_
    simp only [astep]; regs [hN, hk, ↓reduceIte]
    refine step_of rfl hbd ⟨le_rfl, Nat.cast_nonneg _⟩ ?_
    simp only [astep]; regs [hN]
    have hdiv := hv_div k hk
    have hbd1 : St.Bd B { S with N := k / 2 } := by
      simp only [St.Bd] at hbd ⊢; refine ⟨by omega, ?_⟩; omega
    refine step_of rfl hbd1 ⟨le_rfl, Nat.cast_nonneg _⟩ ?_
    simp only [astep]; regs
    have hbd2 : St.Bd B { S with N := k / 2, Lg := S.Lg + 1 } := by
      simp only [St.Bd] at hbd ⊢; omega
    exact reach_cf (ih (k / 2) (by omega) _ M rfl hbd2 (by simp only; omega))
      (by ext <;> simp; omega) rfl

/-- **The setup**: from `scan` with all registers clear, the machine counts the input length
into `N`, sets `Lg := 1` and runs the logarithm loop, reaching the first width computation with
`Lg = lgv |x|` and every other register clear.

**Proof sketch.** `inputLength_loop` (asking decider `0`) on the deterministic part,
transferred by `of_areach`; one increment; `lg_run`. -/
theorem setup_run (hq : ∀ k ≤ x.length, orc 0 (pairEncode x (Nat.bits k)) = decide (k < x.length))
    (M : ℤ → Bool) (hB : x.length + 2 ≤ B) :
    MReach (A K₀) orc x (G x B P) (cf .scan St.zero M 0)
      (cf (.cp (.radX .fst) 0) { St.zero with Lg := lgv x.length } M 0) := by
  have hbd0 : St.zero.Bd B := by simp only [St.Bd, St.zero]; omega
  have h := inputLength_loop (Ad K₀) orc x rN 0 .scan .incN .lgI rfl rfl hq B (by omega)
    St.zero.toV hbd0.toV (by simp [St.zero])
  regs at h
  refine (of_areach (P := P) (M := M) ⟨le_rfl, Nat.cast_nonneg _⟩ h (by simp)).trans ?_
  have hbd1 : St.Bd B { St.zero with N := x.length } := by simp only [St.Bd, St.zero]; omega
  refine step_of rfl hbd1 ⟨le_rfl, Nat.cast_nonneg _⟩ ?_
  simp only [astep]; regs
  have hbd2 : St.Bd B { St.zero with N := x.length, Lg := 1 } := by
    simp only [St.Bd, St.zero]; omega
  have hhv : hv x.length ≤ x.length := by
    unfold hv; split_ifs with h0
    · omega
    · have := Nat.log_lt_self 2 h0; omega
  exact reach_cf (lg_run x.length _ M rfl (by simpa [St.zero] using hbd2)
    (by simp [St.zero]; omega)) (by ext <;> simp [St.zero, lgv]) rfl

/-! ## The width computation -/

/-- **The multiplication chain**: from the `i`-th copy of `X` into `w`, with `w = i · X`, the
machine reaches `wkC` with `w = K₀ · X`.

**Proof sketch.** Induction on `K₀ - i`, each step a copy site. -/
theorem mw_run (q : Ph3) : ∀ (j i : ℕ) (hi : i < K₀) (S : St) (M : ℤ → Bool), K₀ - i = j →
    S.w = i * S.X → S.Z = 0 → S.Bd B → K₀ * S.X ≤ B →
    MReach (A K₀) orc x (G x B P) (cf (.cp (.mw q ⟨i, hi⟩) 0) S M 0)
      (cf (.wkC q) { S with w := K₀ * S.X } M 0) := by
  intro j
  induction j with
  | zero => intro i hi; omega
  | succ j ih =>
    intro i hi S M hj hw hZ hbd hb
    have hle : (i + 1) * S.X ≤ K₀ * S.X := Nat.mul_le_mul_right _ (by omega)
    have hwX : S.w + S.X ≤ B := by rw [hw, ← Nat.succ_mul]; exact hle.trans hb
    have h := cp_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.mw q ⟨i, hi⟩) S M 0
      ⟨le_rfl, Nat.cast_nonneg _⟩ hbd hZ (by simp only [cpDst, cpSrc]; regs; exact hwX)
    simp only [cpDst, cpSrc, cpExit] at h
    regs at h
    have hbd1 : St.Bd B { S with w := S.w + S.X } := by
      simp only [St.Bd] at hbd ⊢; omega
    by_cases hlt : i + 1 < K₀
    · rw [dif_pos hlt] at h
      refine h.trans (reach_cf (ih (i + 1) hlt _ M (by omega) (by simp only; rw [hw]; ring) hZ
        hbd1 (by simpa using hb)) (by ext <;> simp) rfl)
    · rw [dif_neg hlt] at h
      have hK : K₀ = i + 1 := by omega
      exact reach_cf h (by ext <;> simp [hw, hK]; ring) rfl

/-- The register file after a width computation of phase `q` at radius `r`. -/
def wkSt (q : Ph3) (S : St) (r : ℕ) : St :=
  { S with
    w := K₀ * (r + S.Lg + 1)
    K := 2 ^ (K₀ * (r + S.Lg + 1))
    Bs := (if q = .snd then 1 else 2) * 2 ^ (K₀ * (r + S.Lg + 1)) }

/-- **The width computation**: from its first copy, with `X`, `w`, `K`, `Bs`, `C`, `Z`
clear, the machine computes `w = K₀ (r + Lg + 1)` for the phase's radius `r`, `K = 2 ^ w` and
the base `Bs` (`K` for the second search, else `2K`), and reaches the phase's exit.

**Proof sketch.** Copies (`cp_run`) and the multiplication chain (`mw_run`) compute `w`, the
shift site (`sh_run`) computes `K`, copies compute `Bs`. -/
theorem wk_run (q : Ph3) (S : St) (M : ℤ → Bool) (hX : S.X = 0) (hw : S.w = 0) (hK : S.K = 0)
    (hBs : S.Bs = 0) (hC : S.C = 0) (hZ : S.Z = 0) (hK0 : 0 < K₀) (hbd : S.Bd B)
    (hB : 3 * 2 ^ (K₀ * (S.toV (rad q) + S.Lg + 1)) ≤ B) :
    MReach (A K₀) orc x (G x B P) (cf (.cp (.radX q) 0) S M 0)
      (cf (wkExit q) (wkSt (K₀ := K₀) q S (S.toV (rad q))) M 0) := by
  set r := S.toV (rad q) with hr
  set w := K₀ * (r + S.Lg + 1) with hwd
  have hw2 : w < 2 ^ w := Nat.lt_two_pow_self
  have hX1 : r + S.Lg + 1 ≤ w := by
    calc r + S.Lg + 1 = 1 * (r + S.Lg + 1) := (one_mul _).symm
      _ ≤ w := Nat.mul_le_mul_right _ hK0
  have hp : (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ P := ⟨le_rfl, Nat.cast_nonneg _⟩
  -- `X := r`
  have h1 := cp_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.radX q) S M 0 hp hbd hZ
    (by simp only [cpDst, cpSrc]; rw [← hr]; regs; omega)
  simp only [cpDst, cpSrc, cpExit] at h1
  rw [← hr] at h1
  regs [hX, zero_add] at h1
  -- `X := r + Lg`
  have hbd1 : St.Bd B { S with X := r } := by simp only [St.Bd] at hbd ⊢; omega
  have h2 := cp_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.lgX q)
    { S with X := r } M 0 hp
    hbd1 hZ (by simp only [cpDst, cpSrc]; regs; omega)
  simp only [cpDst, cpSrc, cpExit] at h2
  regs at h2
  refine (h1.trans h2).trans ?_
  -- `X := r + Lg + 1`
  have hbd2 : St.Bd B { S with X := r + S.Lg } := by simp only [St.Bd] at hbd ⊢; omega
  refine step_of rfl hbd2 hp ?_
  simp only [astep, dif_pos hK0]; regs
  -- `w := K₀ · X`
  have hbd3 : St.Bd B { S with X := r + S.Lg + 1 } := by simp only [St.Bd] at hbd ⊢; omega
  have h3 := mw_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) q K₀ 0 hK0
    { S with X := r + S.Lg + 1 }
    M (by omega) (by simp [hw]) hZ hbd3 (by simp only; omega)
  refine h3.trans ?_
  -- `X := 0`, `K := 1`
  have hbd4 : St.Bd B { S with X := r + S.Lg + 1, w := w } := by
    simp only [St.Bd] at hbd ⊢; omega
  refine step_of rfl hbd4 hp ?_
  simp only [astep]; regs
  refine cont (st' := { S with w := w }) (by ext <;> simp [hX, hwd]) ?_
  have hbd5 : St.Bd B { S with w := w } := by simp only [St.Bd] at hbd ⊢; omega
  refine step_of rfl hbd5 hp ?_
  simp only [astep]; regs
  refine cont (st' := { S with w := w, K := 1 }) (by ext <;> simp [hK]) ?_
  -- `C := w`
  have hbd6 : St.Bd B { S with w := w, K := 1 } := by simp only [St.Bd] at hbd ⊢; omega
  have h4 := cp_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.wC q)
    { S with w := w, K := 1 } M 0 hp hbd6 hZ (by simp only [cpDst, cpSrc]; regs; omega)
  simp only [cpDst, cpSrc, cpExit] at h4
  regs at h4
  refine (reach_cf h4 (st' := { S with w := w, K := 1, C := w }) (by ext <;> simp [hC])
    rfl).trans ?_
  -- `K := 2 ^ w`
  have hbd7 : St.Bd B { S with w := w, K := 1, C := w } := by simp only [St.Bd] at hbd ⊢; omega
  have h5 := sh_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) q
    { S with w := w, K := 1, C := w } M 0 hp hbd7 hZ (by simp only; omega)
  refine (reach_cf h5 (st' := { S with w := w, K := 2 ^ w }) (by ext <;> simp [hC])
    rfl).trans ?_
  -- `Bs := K` (and once more)
  have hbd8 : St.Bd B { S with w := w, K := 2 ^ w } := by simp only [St.Bd] at hbd ⊢; omega
  have h6 := cp_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.KB1 q)
    { S with w := w, K := 2 ^ w } M 0 hp hbd8 hZ (by simp only [cpDst, cpSrc]; regs; omega)
  simp only [cpDst, cpSrc, cpExit] at h6
  regs at h6
  refine (reach_cf h6 (st' := { S with w := w, K := 2 ^ w, Bs := 2 ^ w })
    (by ext <;> simp [hBs]) rfl).trans ?_
  by_cases hq : q = .snd
  · rw [if_pos hq]
    exact reach_cf (MReach.refl _) (by ext <;> simp [wkSt, hq, hwd, hr]) rfl
  · rw [if_neg hq]
    have hbd9 : St.Bd B { S with w := w, K := 2 ^ w, Bs := 2 ^ w } := by
      simp only [St.Bd] at hbd ⊢; omega
    have h7 := cp_run (orc := orc) (x := x) (B := B) (P := P) (K₀ := K₀) (.KB2 q)
      { S with w := w, K := 2 ^ w, Bs := 2 ^ w } M 0 hp hbd9 hZ
      (by simp only [cpDst, cpSrc]; regs; omega)
    simp only [cpDst, cpSrc, cpExit] at h7
    regs at h7
    exact reach_cf h7 (by ext <;> simp [wkSt, hq, hwd, hr]; ring) rfl

/-! ## The clear chains -/

/-- **The clear chain after the first search**: `U`, `V`, `w`, `K`, `Bs` are cleared. -/
theorem d1_run (S : St) (M : ℤ → Bool) (hbd : S.Bd B) :
    MReach (A K₀) orc x (G x B P) (cf (.d1 0) S M 0)
      (cf (.mv 0) { S with U := 0, V := 0, w := 0, K := 0, Bs := 0 } M 0) := by
  have hp : (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ P := ⟨le_rfl, Nat.cast_nonneg _⟩
  refine clr_step (r := rU) (l' := .d1 1) rfl hbd hp ?_; regs
  refine clr_step (r := rV) (l' := .d1 2) rfl (by simp only [St.Bd] at hbd ⊢; omega) hp ?_; regs
  refine clr_step (r := rw) (l' := .d1 3) rfl (by simp only [St.Bd] at hbd ⊢; omega) hp ?_; regs
  refine clr_step (r := rK) (l' := .d1 4) rfl (by simp only [St.Bd] at hbd ⊢; omega) hp ?_; regs
  refine clr_step (r := rBs) (l' := .mv 0) rfl (by simp only [St.Bd] at hbd ⊢; omega) hp ?_; regs
  exact MReach.refl _

/-- **The clear chain before the final scan**: `U`, `V`, `w`, `K`, `Bs` are cleared. -/
theorem fz_run (S : St) (M : ℤ → Bool) (hbd : S.Bd B) :
    MReach (A K₀) orc x (G x B P) (cf (.fz 0) S M 0)
      (cf (.cp (.radX .fin) 0) { S with U := 0, V := 0, w := 0, K := 0, Bs := 0 } M 0) := by
  have hp : (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ P := ⟨le_rfl, Nat.cast_nonneg _⟩
  refine clr_step (r := rU) (l' := .fz 1) rfl hbd hp ?_; regs
  refine clr_step (r := rV) (l' := .fz 2) rfl (by simp only [St.Bd] at hbd ⊢; omega) hp ?_; regs
  refine clr_step (r := rw) (l' := .fz 3) rfl (by simp only [St.Bd] at hbd ⊢; omega) hp ?_; regs
  refine clr_step (r := rK) (l' := .fz 4) rfl (by simp only [St.Bd] at hbd ⊢; omega) hp ?_; regs
  refine clr_step (r := rBs) (l' := .cp (.radX .fin) 0) rfl
    (by simp only [St.Bd] at hbd ⊢; omega) hp ?_; regs
  exact MReach.refl _

/-- **The chain to the next iteration**: `s` is incremented and `U`, `V`, `w`, `K`, `Bs`, `c`,
`c1`, `s1` are cleared. -/
theorem nz_run (S : St) (M : ℤ → Bool) (hbd : S.Bd B) (hs : S.s + 1 ≤ B) :
    MReach (A K₀) orc x (G x B P) (cf (.nz 0) S M 0)
      (cf (.cp (.radX .fst) 0)
        { S with s := S.s + 1, U := 0, V := 0, w := 0, K := 0, Bs := 0, c := 0, c1 := 0,
                 s1 := 0 } M 0) := by
  have hp : (0 : ℤ) ≤ 0 ∧ (0 : ℤ) ≤ P := ⟨le_rfl, Nat.cast_nonneg _⟩
  refine inc_step (r := rs) (l' := .nz 1) rfl hbd hp ?_; regs
  have hbd1 : St.Bd B { S with s := S.s + 1 } := by simp only [St.Bd] at hbd ⊢; omega
  refine clr_step (r := rU) (l' := .nz 2) rfl hbd1 hp ?_; regs
  refine clr_step (r := rV) (l' := .nz 3) rfl (by simp only [St.Bd] at hbd1 ⊢; omega) hp ?_; regs
  refine clr_step (r := rw) (l' := .nz 4) rfl (by simp only [St.Bd] at hbd1 ⊢; omega) hp ?_; regs
  refine clr_step (r := rK) (l' := .nz 5) rfl (by simp only [St.Bd] at hbd1 ⊢; omega) hp ?_; regs
  refine clr_step (r := rBs) (l' := .nz 6) rfl (by simp only [St.Bd] at hbd1 ⊢; omega) hp ?_
  regs
  refine clr_step (r := rc) (l' := .nz 7) rfl (by simp only [St.Bd] at hbd1 ⊢; omega) hp ?_; regs
  refine clr_step (r := rc1) (l' := .nz 8) rfl (by simp only [St.Bd] at hbd1 ⊢; omega) hp ?_
  regs
  refine clr_step (r := rs1) (l' := .cp (.radX .fst) 0) rfl
    (by simp only [St.Bd] at hbd1 ⊢; omega) hp ?_; regs
  exact MReach.refl _

end ExpBFS

end Complexity.LogProg
