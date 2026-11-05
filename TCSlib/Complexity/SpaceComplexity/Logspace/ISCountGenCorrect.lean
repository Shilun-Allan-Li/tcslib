/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenLoop
import TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenRadius
import TCSlib.Complexity.SpaceComplexity.Machines.NARMProof

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic space is closed under complement

The window-growing inductive-counting machine `Complexity.LogProg.ISGen.igA`
[AB09, §4.3.2, proof of Theorem 4.20, and Corollary 4.21], run with the deciders of the code
languages of a nondeterministic decider `N` of `L` in space `sp = c · S`
(`Complexity.LogProg.SavitchARM.decs`, all in `L`), decides `Lᶜ`: from the start it accepts
iff `x ∉ L` (`gen_start`), every radius it visits is at most `sp |x| + 1`, so its registers
have `O(S |x|)` binary digits (`S ≥ logSpace`), and
`Complexity.LogProg.narm_decides_space` gives `Lᶜ ∈ NSPACE S`
(`Complexity.compl_mem_NSPACE`).

Unlike [AB09, Corollary 4.21] (and Exercise 4.11's configuration-graph route), the radius is
not computed from a space-constructibility witness: the machine grows it until the count of
reachable codes stops growing (`TCSlib.Complexity.SpaceComplexity.ExpBFS.Radius`), so only the
book's standing convention `S ≥ log` is used.

## Main definitions

* none (the correctness of the machine `Complexity.LogProg.ISGen.igA` of
  `TCSlib.Complexity.SpaceComplexity.Logspace.ISCountGenMachine`, and the complement
  closures it gives).

## Main results

* `Complexity.LogProg.ISGen.loop_run` — the radius loop decides non-membership.
* `Complexity.LogProg.ISGen.gen_start` — the semantics from the start.
* `Complexity.compl_mem_NSPACE` — `L ∈ NSPACE S → Lᶜ ∈ NSPACE S` for `S ≥ logSpace`.
  [AB09, Corollary 4.21]
* `Complexity.compl_mem_NL` — `L ∈ NL → Lᶜ ∈ NL`, the case `S = logSpace`.
  [AB09, Theorem 4.20]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.2, Theorem 4.20, Corollary 4.21.)
-/

namespace Complexity.LogProg

namespace ISGen

open Turing Codec ExpBFS ISCount
open SavitchARM (orcN decs rel_orcN initO_orcN accO_orcN)

variable {N : FinNDTM Bool} {x : List Bool}

/-- The code bound at radius `s` dominates the codes: `codeK N ≤ E` and `lg = size |x| + 1`
give `2 ^ (codeK N · (s + logSpace |x| + 1)) ≤ gKv E lg s`. -/
lemma code_le_gKv {E : ℕ} (hE : codeK N ≤ E) (s : ℕ) :
    2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ gKv E (lgv x.length) s := by
  apply Nat.pow_le_pow_right (by norm_num)
  have hl := logSpace_le_size_succ x.length
  have h1 : s + logSpace x.length + 1 ≤ 2 * lgv x.length + 2 * s := by
    simp only [lgv] at hl ⊢; omega
  calc codeK N * (s + logSpace x.length + 1) ≤ E * (2 * lgv x.length + 2 * s) :=
        Nat.mul_le_mul hE h1
    _ = gev E (lgv x.length) s := by simp only [gev]; ring

/-- The code bound grows with the radius. -/
lemma gKv_mono (E lg : ℕ) {s s' : ℕ} (h : s ≤ s') : gKv E lg s ≤ gKv E lg s' :=
  Nat.pow_le_pow_right (by norm_num) (by simp only [gev]; nlinarith)

/-- A radius is below its code bound. -/
lemma lt_gKv {E : ℕ} (hE : 1 ≤ E) (lg s : ℕ) : s < gKv E lg s := by
  have h1 : s ≤ gev E lg s := by simp only [gev]; nlinarith
  exact lt_of_le_of_lt h1 Nat.lt_two_pow_self

/-- **The radius loop decides non-membership**: let `N` decide `L` in space `sp`,
`codeK N ≤ E`, and `B` exceed the code bound at the radius `sp |x| + 1`. At `rd false E` with
radius `s ≤ sp |x| + 1`, `lg = size |x| + 1`, `e = 0`, clear scratch registers and the
previous count `n` either `0` (at `s = 0`) or the number of reachable codes at radius
`s - 1`, every branch terminates and some branch accepts iff `x ∉ L`.

**Proof sketch.** Strong induction on `sp |x| + 1 - s`. One iteration (`iter_run`) computes
the number `R s` of reachable codes (`card_ball_eq_rset`) and rejects on an accepting one
(`noAcc_balls_iff`); then `cmp_run`. If `R s` equals the previous count, `s ≥ 1` (as
`R 0 ≥ 1`) and membership is an accepting reachable code (`mem_iff_exists_acc_of_card_eq`).
Otherwise `s - 1 < sp |x|` (`card_rset_succ_of_le`), so the next radius is in range and the
induction hypothesis applies with the correct previous count; an accepting reachable code
would give membership anyway (`mem_of_exists_acc`). -/
theorem loop_run {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp) {E B : ℕ}
    (hE : codeK N ≤ E) (hE1 : 1 ≤ E)
    (hB : gKv E (lgv x.length) (sp x.length + 1) + 1 ≤ B) :
    ∀ d s, sp x.length + 1 - s = d → s ≤ sp x.length + 1 → ∀ σ : St, σ.s = s →
      σ.lg = lgv x.length → σ.e = 0 → σ.Clear → σ.Bd B →
      ((s = 0 ∧ σ.n = 0) ∨ (1 ≤ s ∧ σ.n = (rset N x (s - 1)).card)) →
      IG (E := E) (orcN N) x B (.rd false (Fin.last E)) σ (x ∉ L) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro s hd hs σ hσs hσlg hσe hz hσ hprv
  have hR : RelO (orcN N) x s = StepRel N x s := rel_orcN N x s
  have hI : InitO (orcN N) x s = InitM N x s := funext fun u => propext (initO_orcN N x s u)
  have hA : AccO (orcN N) x s = AccM N x s := funext fun u => propext (accO_orcN N x s u)
  have hcode := code_le_gKv (x := x) hE s
  have hKs : gKv E (lgv x.length) s + 1 ≤ B :=
    le_trans (Nat.succ_le_succ (gKv_mono E _ hs)) hB
  have hsB : s + 1 ≤ B := by
    have := lt_gKv hE1 (lgv x.length) s
    omega
  have hR1 := one_le_card_rset (N := N) (x := x) s
  -- one iteration, then the comparison
  have hit := iter_run (E := E) (orc := orcN N) (x := x) (B := B)
    ((rset N x s).card = σ.n ∨ ((rset N x s).card ≠ σ.n ∧ x ∉ L)) σ hσ hσe hz
    (by rw [hσlg, hσs]; exact hKs)
    (by rw [hσlg, hσs, hR, hI]; exact card_ball_zero_code hcode)
    (fun k' T' v' c' hk' hT' hv' hc' => ?_)
  · rw [hσlg, hσs, hR, hI, hA] at hit
    refine hit.congr ?_
    rw [noAcc_balls_iff hcode]
    constructor
    · rintro ⟨hno, h | ⟨-, h⟩⟩
      · -- the counts agree: decided at radius `s`
        have hs1 : 1 ≤ s := by
          rcases hprv with ⟨rfl, h0⟩ | ⟨h1, -⟩
          · omega
          · exact h1
        have heq : (rset N x (s - 1)).card = (rset N x s).card := by
          rcases hprv with ⟨h00, h0⟩ | ⟨-, hp⟩
          · omega
          · rw [← hp, h]
        rw [mem_iff_exists_acc_of_card_eq hN hs1 heq]
        rintro ⟨t, ht, hacc⟩
        exact hno t ht hacc
      · exact h
    · intro hx
      refine ⟨fun t ht hacc => hx (mem_of_exists_acc hN ⟨t, ht, hacc⟩), ?_⟩
      by_cases h : (rset N x s).card = σ.n
      · exact Or.inl h
      · exact Or.inr ⟨h, hx⟩
  · -- the comparison, with the count of reachable codes
    have hcp : (ball (gKv E σ.lg σ.s) (RelO (orcN N) x σ.s) (InitO (orcN N) x σ.s)
        (gKv E σ.lg σ.s)).card = (rset N x s).card := by
      rw [hσlg, hσs, hR, hI]; exact card_ball_eq_rset hcode
    have hKle : gKv E σ.lg σ.s + 1 ≤ B := by rw [hσlg, hσs]; exact hKs
    have hRK : (rset N x s).card ≤ gKv E σ.lg σ.s := by
      rw [← hcp]
      calc _ ≤ (Finset.range (gKv E σ.lg σ.s)).card :=
            Finset.card_le_card fun t ht => Finset.mem_range.mpr (mem_ball.mp ht).lt
        _ = _ := Finset.card_range _
    rw [hcp]
    refine cmp_run (E := E) (orc := orcN N) (x := x) (B := B) (x ∉ L) _ ?_
      (by simpa [hσs] using hsB) fun hne => ?_
    · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hσ
      refine ⟨h0, h1, hk', h3, Nat.zero_le _, ?_, hT', ?_, ?_, ?_,
        hv', hc', h12, h13, h14, h15, h16⟩ <;> dsimp only <;> omega
    · -- the counts differ: the next radius, with the correct previous count
      dsimp only at hne ⊢
      have hlt : s + 1 ≤ sp x.length + 1 := by
        rcases hprv with ⟨rfl, -⟩ | ⟨h1, hp⟩
        · omega
        · by_contra hcon
          have hle : sp x.length ≤ s - 1 := by omega
          have := card_rset_succ_of_le (x := x) hN hle
          rw [Nat.sub_add_cancel h1] at this
          exact hne (by rw [hp, this])
      refine ih (sp x.length + 1 - (s + 1)) (by omega) (s + 1) rfl hlt _
        (by simp [hσs]) (by simp [hσlg]) rfl hz ?_ (Or.inr ⟨by omega, by simp⟩)
      obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hσ
      refine ⟨?_, h1, hk', ?_, Nat.zero_le _, ?_, hT', ?_, ?_,
        ?_, hv', hc', h12, h13, h14, h15, h16⟩ <;> dsimp only <;> omega

/-- **The semantics from the start**: from the zero register file every branch terminates,
with registers at most `B`, and some branch accepts iff `x ∉ L`.

**Proof sketch.** The setup (`start_run`) enters the radius loop at radius `0` with previous
count `0`; `loop_run`. -/
theorem gen_start {L : Language Bool} {sp : ℕ → ℕ} (hN : N.DecidesInSpace L sp) {E B : ℕ}
    (hE : codeK N ≤ E) (hE1 : 1 ≤ E)
    (hB : gKv E (lgv x.length) (sp x.length + 1) + 1 ≤ B) :
    IG (E := E) (orcN N) x B .scan St.zero (x ∉ L) := by
  have hq : ∀ m ≤ x.length, orcN N 0 (pairEncode x (Nat.bits m)) = decide (m < x.length) := by
    intro m _
    simp only [orcN, decs, Matrix.cons_val_zero, inputLenLang, indicator_indexLang_pairEncode]
    exact decide_eq_decide.mpr Iff.rfl
  have hlg : 2 ^ lgv x.length ≤ gKv E (lgv x.length) (sp x.length + 1) := by
    apply Nat.pow_le_pow_right (by norm_num)
    simp only [gev]; nlinarith
  have hl : lgv x.length < 2 ^ lgv x.length := Nat.lt_two_pow_self
  refine start_run hq _ (by omega) ?_
  exact loop_run hN hE hE1 hB _ 0 rfl (Nat.zero_le _) _ rfl rfl rfl
    (by simp [St.Clear, St.zero]) (by simp only [St.Bd, St.zero]; omega)
    (Or.inl ⟨rfl, rfl⟩)

end ISGen

end Complexity.LogProg

namespace Complexity

open Turing LogProg LogProg.ISCount LogProg.ISGen LogProg.SavitchARM

/-- A number `m ≤ 2 ^ e + 1` has a binary expansion of at most `e + 2` digits after one
increment. -/
private lemma bits_succ_le {m e : ℕ} (h : m ≤ 2 ^ e + 1) : (Nat.bits (m + 1)).length ≤ e + 2 := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  have : 2 ^ e + 2 < 2 ^ (e + 2) := by
    rw [pow_add]; have := Nat.one_le_two_pow (n := e); omega
  omega

/-- The binary length is at most the logarithmic width. -/
private lemma size_le_logSpace (n : ℕ) : Nat.size n ≤ logSpace n := by
  rw [Nat.size_le]
  exact Nat.lt_pow_succ_log_self (by norm_num) n

/-- **Nondeterministic space is closed under complement** [AB09, Corollary 4.21, proved by
the inductive counting of Theorem 4.20 on the configuration graph]: for every bound
`S ≥ logSpace`, `L ∈ NSPACE S` implies `Lᶜ ∈ NSPACE S`. No space-constructibility is
needed: the counting machine finds the window radius itself.

**Proof sketch.** Let `N` decide `L` in space `c · S` and `E = codeK N + 1`. The
window-growing counting machine `igA E` with the input-length and code-language deciders
(all in `L`) accepts from the start iff `x ∉ L`, every branch terminating with registers at
most `B = 2 ^ e + 1`, `e = 2E (size |x| + 1) + 2E (c S |x| + 1)` (`gen_start`). So registers
have at most `W = e + 2 ≤ (6E + 2Ec + 2) · S |x|` digits, a virtual input has length
`v ≤ 36 · 2 ^ (logSpace |x| + W)`, and a logspace decider uses `O(logSpace v) = O(S |x|)`
cells (`logSpace_le_of_le_mul_two_pow`). `narm_decides_space` concludes. -/
theorem compl_mem_NSPACE {S : ℕ → ℕ} (hS : ∀ n, logSpace n ≤ S n) {L : Language Bool}
    (hL : L ∈ NSPACE S) : Lᶜ ∈ NSPACE S := by
  classical
  obtain ⟨c, N, hN⟩ := hL
  set E := Codec.codeK N + 1 with hE
  have hE1 : 1 ≤ E := by omega
  have hc : ∀ j, ∃ (c : ℕ) (M : FinTM Bool),
      M.DecidesInSpace (decs N j) fun n => c * logSpace n := by
    intro j
    fin_cases j
    · exact inputLenLang_mem
    · exact Codec.initLang_mem
    · exact Codec.acceptLang_mem
    · exact Codec.stepLang_mem
  choose cs Ms hMs using hc
  set cS := ∑ j, cs j with hcS
  have hcj : ∀ j, cs j ≤ cS := fun j =>
    Finset.single_le_sum (f := cs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hS1 : ∀ n, 1 ≤ S n := fun n => le_trans (by simp [logSpace]) (hS n)
  -- the register width
  set W : ℕ → ℕ := fun n => gev E (lgv n) (c * S n + 1) + 2 with hW
  set CW := 6 * E + 2 * E * c + 2 with hCW
  have hWle : ∀ n, W n ≤ CW * S n := by
    intro n
    have h1 := hS1 n
    have hlg : lgv n ≤ 2 * S n := by
      have := size_le_logSpace n; have := hS n; simp only [lgv]; omega
    simp only [hW, hCW, gev]
    have e1 : 2 * E * lgv n ≤ 2 * E * (2 * S n) := Nat.mul_le_mul_left _ hlg
    have e2 : 2 * E * (c * S n + 1) ≤ 2 * E * (c * S n + S n) :=
      Nat.mul_le_mul_left _ (by omega)
    have e3 : (6 * E + 2 * E * c + 2) * S n =
        2 * E * (2 * S n) + 2 * E * (c * S n + S n) + 2 * S n := by ring
    rw [e3]; omega
  refine narm_decides_space (igA E) .scan (decs N) (fun j v => cs j * logSpace v)
    (fun j => ⟨Ms j, hMs j⟩) S W (CW + cS * (37 * (1 + CW))) hS1
    (fun n => (hWle n).trans (Nat.mul_le_mul_right _ (by omega))) (fun j n v hv => ?_)
    (fun x => ?_)
  · -- the deciders' space on the virtual inputs
    beta_reduce at hv ⊢
    have h1 := hS1 n
    have hn : n + 1 ≤ 2 ^ logSpace n := Nat.lt_pow_succ_log_self (by norm_num) n
    have hw1 : W n + 1 ≤ 2 ^ W n := Nat.lt_two_pow_self
    have hv' : v ≤ 36 * 2 ^ (logSpace n + W n) := by
      rw [pow_add]
      have := Nat.mul_le_mul hn hw1
      have e : 2 * n + 2 + 17 * (2 * W n + 2) ≤ 36 * ((n + 1) * (W n + 1)) := by nlinarith
      calc v ≤ 36 * ((n + 1) * (W n + 1)) := hv.trans e
        _ ≤ 36 * (2 ^ logSpace n * 2 ^ W n) := Nat.mul_le_mul_left _ this
    have hlog := logSpace_le_of_le_mul_two_pow hv' (by simp only [logSpace]; omega)
    have hlS : logSpace n + W n ≤ (1 + CW) * S n := by
      have := hS n; have := hWle n; nlinarith
    calc cs j * logSpace v ≤ cS * ((36 + 1) * ((1 + CW) * S n)) :=
          Nat.mul_le_mul (hcj j) (hlog.trans (Nat.mul_le_mul_left _ hlS))
      _ ≤ (CW + cS * (37 * (1 + CW))) * S n := by
          have : cS * ((36 + 1) * ((1 + CW) * S n)) = cS * (37 * (1 + CW)) * S n := by ring
          rw [this]; exact Nat.mul_le_mul_right _ (by omega)
  · -- the machine's semantics from the start
    set B := gKv E (lgv x.length) (c * S x.length + 1) + 1 with hB
    obtain ⟨Nn, hNn, hiff⟩ :=
      (gen_start (x := x) (sp := fun n => c * S n) hN (Nat.le_succ _) hE1 le_rfl).decides
    rw [ISCount.St.toV_zero] at hNn hiff
    refine ⟨Nn, hNn.mono fun a ha => ⟨igA_npreS x a, fun r => bits_succ_le (ha r)⟩, ?_⟩
    exact hiff

/-- **Nondeterministic logspace is closed under complement** [AB09, §4.3.2, Theorem 4.20 in
the form `L ∈ NL → Lᶜ ∈ NL`, proved by inductive counting on the configuration graph]:
`L ∈ NL` implies `Lᶜ ∈ NL`.

**Proof sketch.** `NL = NSPACE logSpace`; `compl_mem_NSPACE` with `S = logSpace`. -/
theorem compl_mem_NL {L : Language Bool} (hL : L ∈ NL) : Lᶜ ∈ NL :=
  compl_mem_NSPACE (fun _ => le_rfl) hL

end Complexity
