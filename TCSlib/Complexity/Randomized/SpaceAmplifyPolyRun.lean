/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SpaceAmplifyPolyMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The repetition machine simulates its runs

The probabilistic semantics of the main loop of `Randomized.PolyAmp.ampA` [AB09, §7.7,
p. 139]. A run moves the code of `N`'s configuration along `K` coins: each coin picks the least
or the greatest step partner of the current code, which are the codes of the two successors,
so the probability that the run ends accepting is `Randomized.PolyAmp.accP` of the start after
`K` coins (`Randomized.PolyAmp.ps_steps`). The runs are independent, and the loop over them has
the semantics `Randomized.PolyAmp.runVal`: the probability that the decision rule holds of the
number of accepting runs among independent blocks of `K` coins (`Randomized.PolyAmp.ps_runs`).

## Main definitions

* `Randomized.PolyAmp.mk` — the register file of the main loop.
* `Randomized.PolyAmp.decRule`, `Randomized.PolyAmp.runVal` — the decision and its
  probability.

## Main results

* `Randomized.PolyAmp.ps_steps` — one run, coin by coin.
* `Randomized.PolyAmp.ps_runs` — the loop over the runs.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.PolyAmp

open Complexity Complexity.LogProg Complexity.Codec Turing

variable {cS F : ℕ} {N : FinNDTM Bool} {os : Bool} {x : List Bool} {B : ℕ}

/-- The register file of the main loop: input length `n`, `ℓ`, radius `S`, `K`, `K + 1` runs;
`i` runs left, `cnt` accepting runs, current code `c`, candidate `d`, `j` coins left. -/
def mk (n ℓ S K i cnt c d j : ℕ) : Reg := ⟨n, ℓ, S, 0, K, K + 1, i, cnt, c, d, j, 0, 0, 0, 0⟩

/-- A copy site: `dst := dst + src` (scratch clear), then the exit. -/
lemma ps_cp (k : CpS) {σ σ' : Reg} {p : ℚ} (hσ : σ.Le B) (hz : σ.z = 0)
    (hb : σ.v (cpDst k) + σ.v (cpSrc k) ≤ B)
    (he : σ'.v = Function.update σ.v (cpDst k) (σ.v (cpDst k) + σ.v (cpSrc k)))
    (hK : PS N os x B (cpEx k : Lab cS F) σ' p) : PS N os x B (.cp0 k : Lab cS F) σ p := by
  have hr := copy_run (A := (ampA cS F os).detPart false) (oracle := ampOr N) (x := x) (B := B)
    (l := .cp0 k) (l1 := .cp1 k) (l2 := .cp2 k) (l3 := .cp3 k) (l4 := .cp4 k) (l5 := .cp5 k)
    (l6 := .cp6 k) (lx := cpEx k) (src := cpSrc k) (dst := cpDst k) (z := 11)
    (by cases k <;> decide) (by cases k <;> decide) (by cases k <;> decide)
    rfl rfl rfl rfl rfl rfl rfl σ.v hz (Reg.le_v hσ) hb
  exact PSem.of_reach (AReach.mono hr fun _ h => h.2) (he ▸ hK)

/-! ### The oracle on the main loop -/

/-- The initial-code decider. -/
theorem ampOr_init (S c : ℕ) :
    ampOr N 1 (pairEncode x (pairEncode (Nat.bits c) (Nat.bits S))) =
      decide (c = cfgCode S (N.tm.initCfg x)) := by
  rw [ampOr, indicator_eq_decide]
  exact decide_eq_decide.mpr (mem_initLang_iff S c)

/-- The step decider at a reachable code. -/
theorem ampOr_step {S : ℕ} {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ S)
    {C : Cfg N.k Bool N.State x} (hC : Reach C) (c' : ℕ) :
    ampOr N 2 (pairEncode x (pairEncode (Nat.bits (cfgCode S C))
      (pairEncode (Nat.bits c') (Nat.bits S)))) =
      decide (c' = cfgCode S (N.tm.stepWith true C) ∨ c' = cfgCode S (N.tm.stepWith false C)) := by
  rw [ampOr, indicator_eq_decide]
  refine decide_eq_decide.mpr ((mem_stepLang_iff hN hs hC c').trans ?_)
  constructor
  · rintro ⟨b, rfl⟩; cases b <;> simp
  · rintro (h | h) <;> exact ⟨_, h⟩

/-- The accepting-code decider at a reachable code. -/
theorem ampOr_accept {S : ℕ} {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ S)
    {C : Cfg N.k Bool N.State x} (hC : Reach C) :
    ampOr N 3 (pairEncode x (pairEncode (Nat.bits (cfgCode S C)) (Nat.bits S))) =
      decide (Accepting C) := by
  rw [ampOr, indicator_eq_decide]
  exact decide_eq_decide.mpr (mem_acceptLang_iff hN hs hC)

/-! ### One run -/

section Run

variable {n ℓ S K : ℕ}

/-- The fields of `mk` are bounded when the run counters and codes are. -/
lemma mk_le {i cnt c d j : ℕ} (hB : n + ℓ + S + 2 * K + 2 ≤ B) (hi : i ≤ K + 1)
    (hc : cnt ≤ K + 1) (hcc : c ≤ K) (hd : d ≤ K) (hj : j ≤ K) :
    (mk n ℓ S K i cnt c d j).Le B := by
  simp only [Reg.Le, mk]; omega

/-- **A coin of the run**: from the code of a reachable configuration `C` with `j` coins
left, the run ends accepting with probability `accP C j`; the continuations `A1` (accepting)
and `A0` are weighted accordingly.

**Proof sketch.** Induction on `j`. With no coin left the acceptance check asks the accepting
code decider (`ampOr_accept`). Otherwise the coin selects the upward search, which stops at
the least step partner, or the downward search from `K`, which stops at the greatest
(`searchUp_run`, `searchDown_run`, `ampOr_step`); these are the codes of the two successors
(below `K` by `cfgCode_lt_codeBound`), so averaging the induction hypotheses at the two
successors gives `accP_succ`. -/
theorem ps_steps {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ S)
    (hK : codeBound N x.length S ≤ K) (hB : n + ℓ + S + 2 * K + 2 ≤ B) {i cnt : ℕ}
    (hi : i ≤ K + 1) (hcnt : cnt + 1 ≤ K + 1) {A1 A0 : ℚ}
    (h1 : ∀ c d, c ≤ K → d ≤ K → PS N os x B (.rT : Lab cS F) (mk n ℓ S K i (cnt + 1) c d 0) A1)
    (h0 : ∀ c d, c ≤ K → d ≤ K → PS N os x B (.rT : Lab cS F) (mk n ℓ S K i cnt c d 0) A0) :
    ∀ (j : ℕ) (C : Cfg N.k Bool N.State x) (d : ℕ), j ≤ K → Reach C → d ≤ K →
      PS N os x B (.sT : Lab cS F) (mk n ℓ S K i cnt (cfgCode S C) d j)
        (accP C j * A1 + (1 - accP C j) * A0) := by
  have hlt : ∀ C : Cfg N.k Bool N.State x, cfgCode S C < K :=
    fun C => (cfgCode_lt_codeBound S C).trans_le hK
  have hle : ∀ {i' cnt' c d j}, i' ≤ K + 1 → cnt' ≤ K + 1 → c ≤ K → d ≤ K → j ≤ K →
      RegLe 15 (Lab cS F) B (none, (mk n ℓ S K i' cnt' c d j).v, none) :=
    fun a b c d e => Reg.le_v (mk_le hB a b c d e)
  intro j
  induction j with
  | zero =>
    intro C d _ hC hd
    refine PSem.jz_pos (A := ampA cS F os) rfl (hle hi (by omega) (hlt C).le hd (by omega)) rfl ?_
    refine PSem.call (A := ampA cS F os) rfl (hle hi (by omega) (hlt C).le hd (by omega)) ?_
    rw [vword_whole₂]
    simp only [Reg.v_8, Reg.v_2, mk]
    simp only [ampOr_accept hN hs hC, accP_zero]
    by_cases hacc : Accepting C
    · simp only [hacc, decide_true, ↓reduceIte]
      refine PSem.inc (A := ampA cS F os) rfl (hle hi (by omega) (hlt C).le hd (by omega)) ?_
      simp only [Reg.v_7, Reg.u_7]
      exact (h1 _ _ (hlt C).le hd).congr (by ring)
    · simp only [hacc, decide_false, ↓reduceIte, Bool.false_eq_true]
      exact (h0 _ _ (hlt C).le hd).congr (by ring)
  | succ j ih =>
    intro C d hj hC hd
    obtain ⟨ct, hct_def⟩ : ∃ y, y = cfgCode S (N.tm.stepWith true C) := ⟨_, rfl⟩
    obtain ⟨cf, hcf_def⟩ : ∃ y, y = cfgCode S (N.tm.stepWith false C) := ⟨_, rfl⟩
    have hct : ct < K := hct_def ▸ hlt (N.tm.stepWith true C)
    have hcf : cf < K := hcf_def ▸ hlt (N.tm.stepWith false C)
    have hCK := (hlt C).le
    set σ := mk n ℓ S K i cnt (cfgCode S C) d j with hσ
    have hσB : σ.Le B := mk_le hB hi (by omega) hCK hd (by omega)
    -- after the move, the run continues from the chosen successor
    have hmv : ∀ C' : Cfg N.k Bool N.State x, Reach C' →
        PS N os x B (.mv : Lab cS F) (mk n ℓ S K i cnt (cfgCode S C) (cfgCode S C') j)
          (accP C' j * A1 + (1 - accP C' j) * A0) := by
      intro C' hC'
      have hC'K := (hlt C').le
      refine PSem.clr (A := ampA cS F os) rfl (Reg.le_v (mk_le hB hi (by omega) hCK hC'K
        (by omega))) ?_
      simp only [Reg.u_8]
      refine ps_cp .cc (σ' := mk n ℓ S K i cnt (cfgCode S C') (cfgCode S C') j)
        (by simp only [Reg.Le, mk]; omega) rfl (by simp [cpDst, cpSrc, mk]; omega)
        (by simp [cpDst, cpSrc, mk]) ?_
      exact ih C' _ (by omega) hC' hC'K
    have hcall : ∀ (l₁ l₀ : Lab cS F) (c' : ℕ),
        astep ((ampA cS F os).detPart false) (ampOr N) x
            (some (.uT : Lab cS F), Function.update σ.v 9 c', none) =
          (some (if c' = ct ∨ c' = cf then .mv else .uI), Function.update σ.v 9 c', none) ∧
        astep ((ampA cS F os).detPart false) (ampOr N) x
            (some (.dT : Lab cS F), Function.update σ.v 9 c', none) =
          (some (if c' = ct ∨ c' = cf then .mv else .dD), Function.update σ.v 9 c', none) := by
      intro _ _ c'
      have h := ampOr_step hN hs hC c'
      rw [← hct_def, ← hcf_def] at h
      constructor <;>
      · simp [astep, NARM.detPart, ampA, vword_whole₃, Function.update_apply, hσ, mk, h]
    have hpre : ∀ (l : Lab cS F), (l = .uT ∨ l = .dT) → ∀ w : Fin 15 → ℕ,
        PreS ((ampA cS F os).detPart false) x (some l, w, none) := by
      rintro l (rfl | rfl) w <;> simp [PreS, NARM.detPart, ampA]
    -- the upward search stops at the least successor code
    have hup : PS N os x B (.up : Lab cS F) σ
        (accP (if ct ≤ cf then N.tm.stepWith true C else N.tm.stepWith false C) j * A1 +
          (1 - accP (if ct ≤ cf then N.tm.stepWith true C else N.tm.stepWith false C) j) * A0) := by
      refine PSem.clr (A := ampA cS F os) rfl (Reg.le_v hσB) ?_
      have hr := searchUp_run (x := x) ((ampA cS F os).detPart false) (ampOr N) 9
        (fun c' => c' = ct ∨ c' = cf) .uT .uI .mv B σ.v (Reg.le_v hσB)
        (fun c' => (hcall .mv .uI c').1) (hpre .uT (Or.inl rfl)) rfl (min ct cf)
        (by rcases le_total ct cf with h | h <;> simp [h]) (by omega) 0 (Nat.zero_le _)
        (fun c' _ h => by omega)
      refine PSem.of_reach (AReach.mono hr fun _ h => h.2) ?_
      have e : Function.update σ.v 9 (min ct cf) =
          (mk n ℓ S K i cnt (cfgCode S C) (cfgCode S (if ct ≤ cf then N.tm.stepWith true C
            else N.tm.stepWith false C)) j).v := by
        rw [Reg.u_9]
        split_ifs with h
        · rw [min_eq_left h]; simp [hσ, mk, hct_def]
        · rw [min_eq_right (le_of_not_ge h)]; simp [hσ, mk, hcf_def]
      rw [e]
      exact hmv _ (by split_ifs <;> exact hC.step _)
    -- the downward search from `K` stops at the greatest successor code
    have hdn : PS N os x B (.dn : Lab cS F) σ
        (accP (if ct ≤ cf then N.tm.stepWith false C else N.tm.stepWith true C) j * A1 +
          (1 - accP (if ct ≤ cf then N.tm.stepWith false C else N.tm.stepWith true C) j) * A0) := by
      refine PSem.clr (A := ampA cS F os) rfl (Reg.le_v hσB) ?_
      simp only [Reg.u_9]
      refine ps_cp .kc (σ' := mk n ℓ S K i cnt (cfgCode S C) K j)
        (by simp only [Reg.Le, hσ, mk]; omega) rfl (by simp [cpDst, cpSrc, hσ, mk]; omega)
        (by simp [cpDst, cpSrc, hσ, mk]) ?_
      have hr := searchDown_run (x := x) ((ampA cS F os).detPart false) (ampOr N) 9
        (fun c' => c' = ct ∨ c' = cf) .dD .dT .mv B σ.v (Reg.le_v hσB)
        (fun c' => (hcall .mv .dD c').2) (hpre .dT (Or.inr rfl)) rfl (max ct cf)
        (by rcases le_total ct cf with h | h <;> simp [h]) K (by omega) (by omega)
        (fun c' h1 h2 => by omega)
      have e0 : Function.update σ.v 9 K = (mk n ℓ S K i cnt (cfgCode S C) K j).v := by
        rw [Reg.u_9]; simp [hσ, mk]
      rw [e0] at hr
      refine PSem.of_reach (AReach.mono hr fun _ h => h.2) ?_
      have e : Function.update σ.v 9 (max ct cf) =
          (mk n ℓ S K i cnt (cfgCode S C) (cfgCode S (if ct ≤ cf then N.tm.stepWith false C
            else N.tm.stepWith true C)) j).v := by
        rw [Reg.u_9]
        split_ifs with h
        · rw [max_eq_right h]; simp [hσ, mk, hcf_def]
        · rw [max_eq_left (le_of_not_ge h)]; simp [hσ, mk, hct_def]
      rw [e]
      exact hmv _ (by split_ifs <;> exact hC.step _)
    have hG1 := Reg.le_v (mk_le (n := n) (ℓ := ℓ) (S := S) (K := K) (i := i) (cnt := cnt)
      (c := cfgCode S C) (d := d) (j := j + 1) hB hi (by omega) hCK hd hj)
    refine PSem.jz_neg (A := ampA cS F os) rfl (fun r => hG1 r) (by simp [mk]) ?_
    refine PSem.dec (A := ampA cS F os) rfl (fun r => hG1 r) ?_
    have e : Function.update (mk n ℓ S K i cnt (cfgCode S C) d (j + 1)).v 10
        ((mk n ℓ S K i cnt (cfgCode S C) d (j + 1)).v 10 - 1) = σ.v := by
      rw [Reg.u_10]; rfl
    rw [e]
    refine (PSem.choose (A := ampA cS F os) rfl (Reg.le_v hσB) hup hdn).congr ?_
    rw [accP_succ]
    split_ifs <;> ring

end Run

/-! ### The runs -/

/-- The acceptance bit of a block of coins: the run of `N` on it ends accepting. -/
def accBit (N : FinNDTM Bool) (x : List Bool) (l : List Bool) : Bool :=
  decide (Accepting (N.tm.runWith l (N.tm.initCfg x)))

/-- The decision on the number `m` of accepting runs out of `K + 1`: some run accepted
(one-sided), or a strict majority (two-sided). -/
def decRule (os : Bool) (K m : ℕ) : Bool := if os then decide (1 ≤ m) else decide (K + 1 < 2 * m)

/-- The probability that the decision holds of `cnt` plus the number of accepting blocks among
`i` independent blocks of `K` coins. -/
noncomputable def runVal (N : FinNDTM Bool) (x : List Bool) (os : Bool) (K i cnt : ℕ) : ℚ :=
  randProb (i * K) fun w => decRule os K (cnt + blockCount K i (accBit N x) w) = true

/-- With no block left the decision is on `cnt`. -/
theorem runVal_zero (K cnt : ℕ) :
    runVal N x os K 0 cnt = if decRule os K cnt then 1 else 0 := by
  unfold runVal
  rw [zero_mul, ← randProb_const 0 (decRule os K cnt = true)]
  refine randProb_congr fun r => ?_
  simp [blockCount]

/-- One more block: the first block accepts with probability `accP` of the start.

**Proof sketch.** Split the coins into the first block and the rest (`blockCount_succ`): the
event is the disjoint union of "the first block accepts and the rest decides from `cnt + 1`"
and "the first block rejects and the rest decides from `cnt`"; each part factors
(`randProb_split`). -/
theorem runVal_succ (K i cnt : ℕ) :
    runVal N x os K (i + 1) cnt =
      accP (N.tm.initCfg x) K * runVal N x os K i (cnt + 1) +
        (1 - accP (N.tm.initCfg x) K) * runVal N x os K i cnt := by
  have hp : accP (N.tm.initCfg x) K = randProb K (fun l => accBit N x l = true) :=
    randProb_congr fun r => by simp [accBit]
  unfold runVal
  rw [hp, show (i + 1) * K = K + i * K by ring]
  have hev : randProb (K + i * K)
      (fun l => decRule os K (cnt + blockCount K (i + 1) (accBit N x) l) = true) =
      randProb (K + i * K) (fun l =>
        ((fun l' => accBit N x l' = true) (l.take K) ∧
          (fun w => decRule os K (cnt + 1 + blockCount K i (accBit N x) w) = true) (l.drop K)) ∨
        ((fun l' => accBit N x l' = false) (l.take K) ∧
          (fun w => decRule os K (cnt + blockCount K i (accBit N x) w) = true) (l.drop K))) :=
    randProb_congr fun r => by
      rw [blockCount_succ]
      rcases hb : accBit N x ((List.ofFn r).take K) <;> simp [hb, Nat.add_assoc]
  rw [hev, randProb_or_disjoint _ _ (fun r => by
      rintro ⟨⟨h1, -⟩, h2, -⟩
      rw [h1] at h2
      exact absurd h2 (by simp)),
    randProb_split K (i * K) (fun l' => accBit N x l' = true)
      (fun w => decRule os K (cnt + 1 + blockCount K i (accBit N x) w) = true),
    randProb_split K (i * K) (fun l' => accBit N x l' = false)
      (fun w => decRule os K (cnt + blockCount K i (accBit N x) w) = true), randProb_bool_false]

section Loop

variable {n ℓ S K : ℕ}

/-- **The decision**: from `fin` with `cnt` accepting runs, the machine answers `decRule`.

**Proof sketch.** One-sided: a zero test of the count. Two-sided: an add-twice loop puts `2 cnt`
into register `14` (`psem_addTwice`), and the comparison loop `Complexity.Codec.le_loop`
tests `2 cnt ≤ K + 1`. -/
theorem ps_fin (hB : n + ℓ + S + 2 * K + 2 ≤ B) {cnt c d : ℕ} (hcnt : cnt ≤ K + 1)
    (hc : c ≤ K) (hd : d ≤ K) :
    PS N os x B (.fin : Lab cS F) (mk n ℓ S K 0 cnt c d 0)
      (if decRule os K cnt then 1 else 0) := by
  have hσ := mk_le (n := n) (ℓ := ℓ) (S := S) (K := K) (B := B) hB (Nat.zero_le _) hcnt hc hd
    (Nat.zero_le _) (i := 0) (j := 0)
  cases os with
  | true =>
    by_cases h0 : cnt = 0
    · subst h0
      refine PSem.jz_pos (A := ampA cS F true) rfl (Reg.le_v hσ) rfl ?_
      exact (PSem.rej (A := ampA cS F true) rfl (Reg.le_v hσ)).congr (by simp [decRule])
    · refine PSem.jz_neg (A := ampA cS F true) rfl (Reg.le_v hσ) (by simpa [mk] using h0) ?_
      exact (PSem.acc (A := ampA cS F true) rfl (Reg.le_v hσ)).congr
        (by simp [decRule]; omega)
  | false =>
    refine psem_addTwice (ampA cS F false) (ampOr N) x B 12 7 14 (by decide) (by decide)
      (by decide) .fin .ad1 .ad2 .ad3 .fC rfl rfl rfl rfl _ _ (Reg.le_v hσ) (by simp [mk])
      (by simp [mk]; omega) ?_
    simp only [Reg.v_14, Reg.v_7, Reg.v_12, Reg.u_14, Reg.u_12, mk]
    set σ : Reg := ⟨n, ℓ, S, 0, K, K + 1, 0, cnt, c, d, 0, 0, 0, 0, 2 * cnt⟩ with hσ'
    have hσB : σ.Le B := by simp only [Reg.Le, hσ']; omega
    have e1 : ({ ({ (mk n ℓ S K 0 cnt c d 0) with w := 0 + 2 * (cnt - 0) } : Reg) with t := cnt } :
        Reg) = { σ with t := cnt } := by simp [hσ', mk]
    simp only [mk] at e1
    rw [e1]
    refine PSem.clr (A := ampA cS F false) rfl (Reg.le_v (by simp only [Reg.Le, hσ']; omega)) ?_
    simp only [Reg.u_12]
    have e2 : ({ ({ σ with t := cnt } : Reg) with t := 0 } : Reg) = σ := rfl
    rw [e2]
    have hr := Codec.le_loop ((ampA cS F false).detPart false) (ampOr N) x 12 14 5 (by decide)
      (by decide) .lt1 .lt2 .ltb .rej .acc rfl rfl rfl B σ.v (Reg.le_v hσB) (by simp [hσ'])
      (by simp [hσ'])
    refine PSem.of_reach (AReach.mono hr fun _ h => h.2) ?_
    have hv : ∀ r, Function.update σ.v 12 (min (σ.v 14) (σ.v 5)) r ≤ B :=
      register_update_le σ.v 12 B _ (Reg.le_v hσB) (by simp [hσ']; omega)
    by_cases hle : 2 * cnt ≤ K + 1
    · rw [if_pos (by simpa [hσ'] using hle)]
      exact (PSem.rej (A := ampA cS F false) rfl hv).congr (by simp [decRule]; omega)
    · rw [if_neg (by simpa [hσ'] using hle)]
      exact (PSem.acc (A := ampA cS F false) rfl hv).congr (by simp [decRule]; omega)

/-- **The loop over the runs**: from `rT` with `i` runs left and `cnt` accepting runs, the
answer is `true` with probability `runVal i cnt`.

**Proof sketch.** Induction on `i`. With no run left, `ps_fin`. Otherwise the run searches the
initial code (`searchUp_run`, `ampOr_init`), copies `K` into the coin counter, and runs
(`ps_steps` from the start, with the induction hypothesis as continuations); `runVal_succ`
recombines. -/
theorem ps_runs {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ S)
    (hK : codeBound N x.length S ≤ K) (hB : n + ℓ + S + 2 * K + 2 ≤ B) :
    ∀ (i cnt c d : ℕ), cnt + i ≤ K + 1 → c ≤ K → d ≤ K →
      PS N os x B (.rT : Lab cS F) (mk n ℓ S K i cnt c d 0) (runVal N x os K i cnt) := by
  intro i
  induction i with
  | zero =>
    intro cnt c d hcnt hc hd
    have hσ := mk_le (n := n) (ℓ := ℓ) (S := S) (K := K) (B := B) hB (Nat.zero_le _)
      (by omega) hc hd (Nat.zero_le _) (i := 0) (cnt := cnt) (j := 0)
    refine PSem.jz_pos (A := ampA cS F os) rfl (Reg.le_v hσ) rfl ?_
    rw [runVal_zero]
    exact ps_fin hB (by omega) hc hd
  | succ i ih =>
    intro cnt c d hcnt hc hd
    have hσ := mk_le (n := n) (ℓ := ℓ) (S := S) (K := K) (B := B) hB (by omega)
      (by omega) hc hd (Nat.zero_le _) (i := i + 1) (cnt := cnt) (j := 0)
    refine PSem.jz_neg (A := ampA cS F os) rfl (Reg.le_v hσ) (by simp [mk]) ?_
    refine PSem.dec (A := ampA cS F os) rfl (Reg.le_v hσ) ?_
    have e : Function.update (mk n ℓ S K (i + 1) cnt c d 0).v 6
        ((mk n ℓ S K (i + 1) cnt c d 0).v 6 - 1) = (mk n ℓ S K i cnt c d 0).v := by
      rw [Reg.u_6]; rfl
    rw [e]
    have hσi := mk_le (n := n) (ℓ := ℓ) (S := S) (K := K) (B := B) hB (by omega)
      (by omega) hc hd (Nat.zero_le _) (i := i) (cnt := cnt) (j := 0)
    refine PSem.clr (A := ampA cS F os) rfl (Reg.le_v hσi) ?_
    -- the initial-code search
    obtain ⟨c₀, hc₀_def⟩ : ∃ y, y = cfgCode S (N.tm.initCfg x) := ⟨_, rfl⟩
    have hc₀ : c₀ < K := hc₀_def ▸ (cfgCode_lt_codeBound S _).trans_le hK
    have hr := searchUp_run (x := x) ((ampA cS F os).detPart false) (ampOr N) 8 (fun c' => c' = c₀)
      .iT .iI (.cp0 .kj) B (mk n ℓ S K i cnt c d 0).v (Reg.le_v hσi)
      (fun c' => by
        have h := ampOr_init (N := N) (x := x) S c'
        rw [← hc₀_def] at h
        simp [astep, NARM.detPart, ampA, vword_whole₂, Function.update_apply, mk, h])
      (fun w => by simp [PreS, NARM.detPart, ampA]) rfl c₀ rfl (by omega) 0 (Nat.zero_le _)
      (fun c' _ h => by omega)
    refine PSem.of_reach (AReach.mono hr fun _ h => h.2) ?_
    rw [Reg.u_8]
    refine ps_cp .kj (σ' := mk n ℓ S K i cnt c₀ d K) (by simp only [Reg.Le, mk]; omega) rfl
      (by simp [cpDst, cpSrc, mk]; omega) (by simp [cpDst, cpSrc, mk]) ?_
    have hrun := ps_steps (cS := cS) (F := F) (os := os) hN hs hK hB (i := i) (cnt := cnt)
      (by omega) (by omega)
      (fun c' d' hc' hd' => ih (cnt + 1) c' d' (by omega) hc' hd')
      (fun c' d' hc' hd' => ih cnt c' d' (by omega) hc' hd') K (N.tm.initCfg x) d le_rfl
      reach_init hd
    rw [runVal_succ, hc₀_def]
    exact hrun

end Loop

end Randomized.PolyAmp
