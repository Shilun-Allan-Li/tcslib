/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Sim

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The return phase of a subroutine call

The first half of `TCSlib.Complexity.SpaceComplexity.Machines.Call`: compiled configurations
built from their blocks, and the return phase of a call — rewinding the input head and
moving every argument register head back to cell `0`.

## Main definitions

* `Complexity.LogProg.mkCfg` — a compiled configuration from its register and decider
  blocks.

## Main results

* `Complexity.LogProg.ret2_run` — the input rewind of the return.
* `Complexity.LogProg.retR_run` — restoring one argument register head.
* `Complexity.LogProg.regs_run` — restoring all argument register heads.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, proof of Lemma 4.17.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- A compiled configuration from its register block and decider block. -/
def mkCfg (st : Option (CSt Λ SD m)) (ip : Fin (x.length + 2)) (rt : Fin m → ℤ → Option Bool)
    (rp : Fin m → ℤ) (dt : Fin kD → ℤ → Option Bool) (dp : Fin kD → ℤ) (out : List Bool) :
    Cfg (m + kD) Bool (CSt Λ SD m) x :=
  ⟨st, ip, Fin.append rt dt, Fin.append rp dp, out⟩

/-- The configuration built by `mkCfg st …` is in state `st`. -/
@[simp] lemma mkCfg_state (st : Option (CSt Λ SD m)) (ip : Fin (x.length + 2)) rt rp
    (dt : Fin kD → ℤ → Option Bool) dp out :
    (mkCfg st ip rt rp dt dp out).state = st := rfl

/-- An action moving only the input head and register heads. -/
lemma apply_moves (st : Option (CSt Λ SD m)) (ip : Fin (x.length + 2))
    (rt : Fin m → ℤ → Option Bool) (rp : Fin m → ℤ) (dt : Fin kD → ℤ → Option Bool)
    (dp : Fin kD → ℤ) (out : List Bool) (mvI : SignType) (f : Fin m → SignType)
    (st' : CSt Λ SD m) :
    (⟨mvI, Fin.append (fun r => (none, f r)) dIdle, none, some st'⟩ :
        Action (m + kD) Bool (CSt Λ SD m)).apply (mkCfg st ip rt rp dt dp out) =
      mkCfg (some st') (moveInputPos ip mvI) rt (fun r => rp r + f r) dt dp out := by
  refine Cfg.ext rfl rfl ?_ ?_ (by simp [mkCfg])
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [mkCfg, dIdle]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [mkCfg, dIdle]

/-- An action moving one register head. -/
lemma apply_regMove (st : Option (CSt Λ SD m)) (ip : Fin (x.length + 2))
    (rt : Fin m → ℤ → Option Bool) (rp : Fin m → ℤ) (dt : Fin kD → ℤ → Option Bool)
    (dp : Fin kD → ℤ) (out : List Bool) (r : Fin m) (mv : SignType) (st' : CSt Λ SD m) :
    (⟨0, Fin.append (regMove r mv) dIdle, none, some st'⟩ :
        Action (m + kD) Bool (CSt Λ SD m)).apply (mkCfg st ip rt rp dt dp out) =
      mkCfg (some st') ip rt (Function.update rp r (rp r + mv)) dt dp out := by
  have := apply_moves st ip rt rp dt dp out 0 (fun r' => if r' = r then mv else 0) st'
  simp only [moveInputPos_zero] at this
  convert this using 2
  funext r'
  by_cases h : r' = r
  · subst h; simp
  · simp [h]

/-- An action moving only the input head. -/
lemma apply_inputOnly (st : Option (CSt Λ SD m)) (ip : Fin (x.length + 2))
    (rt : Fin m → ℤ → Option Bool) (rp : Fin m → ℤ) (dt : Fin kD → ℤ → Option Bool)
    (dp : Fin kD → ℤ) (out : List Bool) (mvI : SignType) (st' : CSt Λ SD m) :
    (⟨mvI, fun _ => (none, 0), none, some st'⟩ : Action (m + kD) Bool (CSt Λ SD m)).apply
        (mkCfg st ip rt rp dt dp out) =
      mkCfg (some st') (moveInputPos ip mvI) rt rp dt dp out := by
  refine Cfg.ext rfl rfl ?_ ?_ (by simp [mkCfg])
  · funext i z
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [mkCfg]
  · funext i
    refine Fin.addCases (fun r => ?_) (fun j => ?_) i <;> simp [mkCfg]

/-- The seam of a program configuration as a `mkCfg`. -/
lemma seam_eq_mkCfg (c : Cfg m Bool Λ x) :
    seam (kD := kD) (SD := SD) c = mkCfg (c.state.map .prog) c.inputPos c.workTapes
      c.workTapePos (fun _ _ => none) (fun _ => 0) c.output := rfl

/-! ## The return phase -/

section Return

variable (P : RProg m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)

/-- The input scan of the return: from position `j ≤ |x|` the head walks left to the left
blank and steps onto the first cell.

**Proof sketch.** Induction on `j`. At a position `j > 0` the input symbol is a letter of the
input, so the head moves left and the state stays `ret2`; at position `0` the left blank sends
the head to position `1` and the machine enters the next return state. No work head moves. -/
lemma ret2_run (l : Λ) (cs : CallSpec m d Λ) (hcall : P.call l = some cs)
    (s : Fin (m + 1)) (dir b : Bool) (rt : Fin m → ℤ → Option Bool) (rp : Fin m → ℤ)
    (dt : Fin kD → ℤ → Option Bool) (dp : Fin kD → ℤ) (out : List Bool) :
    ∀ (j : ℕ) (ip : Fin (x.length + 2)), ip.val = j → j ≤ x.length →
      (∀ t ≤ j + 1, ((compileTM P l₀ D q0).runFrom
          (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out) t).workTapePos =
        Fin.append rp dp) ∧
      (compileTM P l₀ D q0).runFrom (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out)
          (j + 1) = mkCfg (some (nextRet cs l s dir b 0)) 1 rt rp dt dp out := by
  intro j
  induction j with
  | zero =>
    intro ip hip _
    have hz : ip = 0 := Fin.ext hip
    have hstep : (compileTM P l₀ D q0).step (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out) =
        mkCfg (some (nextRet cs l s dir b 0)) 1 rt rp dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      have hsym : (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out :
          Cfg (m + kD) Bool (CSt Λ SD m) x).inputSymbol = none := by
        simp [Cfg.inputSymbol, mkCfg, hz]
      simp only [compileTM, ctr, hsym, hcall]
      rw [apply_inputOnly]
      congr 1
      rw [hz]; exact Fin.ext (by simp [moveInputPos])
    refine ⟨fun t ht => ?_, by simpa using hstep⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      rfl
    · obtain rfl : t = 1 := by omega
      simp only [MultiTapeTM.runFrom, Function.iterate_one] at hstep ⊢
      rw [hstep]; rfl
  | succ j ih =>
    intro ip hip hj
    have hsym : (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out :
        Cfg (m + kD) Bool (CSt Λ SD m) x).inputSymbol = some x[j] :=
      inputSymbolInner j (by simp [mkCfg, hip]; omega) (by omega)
    have hstep : (compileTM P l₀ D q0).step (mkCfg (some (.ret2 l s dir b)) ip rt rp dt dp out) =
        mkCfg (some (.ret2 l s dir b)) (moveInputPos ip (-1)) rt rp dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      simp only [compileTM, ctr, hsym]
      rw [apply_inputOnly]
    have hval : (moveInputPos ip (-1)).val = j := by
      rw [show (-1 : SignType) = .neg from rfl, FinTM.moveInputPos_neg_val]; omega
    obtain ⟨ihb, ihr⟩ := ih (moveInputPos ip (-1)) hval (by omega)
    refine ⟨fun t ht => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; rfl
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        exact ihb t' (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact ihr

/-- The left scan of an argument register in the return: from position `p ∈ [-1, |w|)` the
head walks left to the left blank `-1` and steps onto cell `0`.

**Proof sketch.** Induction on `n = p + 1`. While the head of register `rr` reads a letter of
`w` it moves left; at the left blank `-1` it moves right onto cell `0` and the machine enters
the next return state. Only that head moves, and it stays in `[-1, max p 0]`. -/
lemma retR_scan (l : Λ) (cs : CallSpec m d Λ) (hcall : P.call l = some cs)
    (s : Fin (m + 1)) (dir b : Bool) (a : Fin m) (w : List Bool) (rr : Fin m)
    (hrr : cs.args.getD a a = rr)
    (rt : Fin m → ℤ → Option Bool) (hrt : rt rr = FinTM.bufferTape w)
    (dt : Fin kD → ℤ → Option Bool) (dp : Fin kD → ℤ) (out : List Bool)
    (ip : Fin (x.length + 2)) :
    ∀ (n : ℕ) (rp : Fin m → ℤ), rp (rr) + 1 = n → (n : ℤ) ≤ w.length →
      (∀ t ≤ n + 1, ∀ r, (((compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) t).workTapePos
            (Fin.castAdd kD r) = rp r ∨
          (r = rr ∧ -1 ≤ ((compileTM P l₀ D q0).runFrom
            (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) t).workTapePos
              (Fin.castAdd kD r) ∧ ((compileTM P l₀ D q0).runFrom
            (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) t).workTapePos
              (Fin.castAdd kD r) ≤ max (rp r) 0)) ∧
        ((compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) t).workTapePos
            ∘ Fin.natAdd m = dp) ∧
      (compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) (n + 1) =
        mkCfg (some (nextRet cs l s dir b (a.val + 1))) ip rt
          (Function.update rp (rr) 0) dt dp out := by
  intro n
  induction n with
  | zero =>
    intro rp hp _
    have hpos : rp (rr) = -1 := by omega
    have hrd : (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out :
        Cfg (m + kD) Bool (CSt Λ SD m) x).workTapeSymbols (Fin.castAdd kD (rr)) =
          none := by
      simp [Cfg.workTapeSymbols, mkCfg, hrt, hpos]
    have hstep : (compileTM P l₀ D q0).step
        (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) =
        mkCfg (some (nextRet cs l s dir b (a.val + 1))) ip rt
          (Function.update rp (rr) 0) dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      simp only [compileTM, ctr, hcall, hrr, hrd, ↓reduceIte]
      rw [apply_regMove]
      congr 1
      rw [hpos]; simp
    refine ⟨fun t ht r => ?_, ?_⟩
    · rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        exact ⟨Or.inl (by simp [mkCfg]), by funext i; simp [mkCfg]⟩
      · obtain rfl : t = 1 := by omega
        simp only [MultiTapeTM.runFrom, Function.iterate_one, hstep]
        refine ⟨?_, by funext i; simp [mkCfg]⟩
        by_cases hr : r = rr
        · subst hr; right; simp [mkCfg, hpos]
        · left; simp [mkCfg, hr]
    · simpa using hstep
  | succ n ih =>
    intro rp hp hn
    have hpos : rp (rr) = n := by omega
    have hrd : (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out :
        Cfg (m + kD) Bool (CSt Λ SD m) x).workTapeSymbols (Fin.castAdd kD (rr)) =
          some w[n] := by
      simp [Cfg.workTapeSymbols, mkCfg, hrt, hpos, FinTM.bufferTape,
        List.getElem?_eq_getElem (show n < w.length by omega)]
    set rp' := Function.update rp (rr) (n - 1 : ℤ) with hrp'
    have hstep : (compileTM P l₀ D q0).step
        (mkCfg (some (.retR l s dir b a true)) ip rt rp dt dp out) =
        mkCfg (some (.retR l s dir b a true)) ip rt rp' dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      simp only [compileTM, ctr, hcall, hrr, hrd, ↓reduceIte]
      rw [apply_regMove]
      congr 1
      rw [hrp', hpos, sub_eq_add_neg]; simp
    obtain ⟨ihb, ihr⟩ := ih rp' (by simp [hrp']) (by omega)
    refine ⟨fun t ht r => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact ⟨Or.inl (by simp [mkCfg]), by funext i; simp [mkCfg]⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        obtain ⟨h1, h2⟩ := ihb t' (by omega) r
        refine ⟨?_, h2⟩
        by_cases hr : r = rr
        · subst hr
          right
          rcases h1 with h1 | h1
          · rw [h1]; simp [hrp', hpos]
          · refine ⟨rfl, h1.2.1, h1.2.2.trans ?_⟩
            simp only [hrp', Function.update_self, hpos]
            omega
        · left
          rcases h1 with h1 | h1
          · rw [h1]; simp [hrp', hr]
          · exact absurd h1.1 hr
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, ihr]
      congr 1
      funext r
      by_cases hr : r = rr
      · subst hr; simp
      · simp [hrp', hr]

/-- The side test of the return phase for argument register number `a`. -/
def leftSide (s : Fin (m + 1)) (dir : Bool) (a : Fin m) : Bool :=
  decide (s.val < a.val + 1) || (decide (s.val = a.val + 1) && !dir)

/-- Restoring one argument register head: from any position in `[-1, |w|]` (a blank end
being identified by the side test) the head returns to cell `0`.

**Proof sketch.** If the head is on a letter, or on a blank identified as the left end by the
side test, the scan `retR_scan` applies (after at most one step right from `-1`). If it is on
the right blank `|w|`, one step moves it left onto the last letter and `retR_scan` applies from
there. In both cases only the head of `rr` moves, within `[-1, |w|]`. -/
lemma retR_run (l : Λ) (cs : CallSpec m d Λ) (hcall : P.call l = some cs)
    (s : Fin (m + 1)) (dir b : Bool) (a : Fin m) (w : List Bool) (rr : Fin m)
    (hrr : cs.args.getD a a = rr) (rt : Fin m → ℤ → Option Bool)
    (hrt : rt rr = FinTM.bufferTape w) (dt : Fin kD → ℤ → Option Bool) (dp : Fin kD → ℤ)
    (out : List Bool) (ip : Fin (x.length + 2)) (rp : Fin m → ℤ)
    (hp : -1 ≤ rp rr ∧ rp rr ≤ w.length) (hl : rp rr = -1 → leftSide s dir a = true)
    (hrgt : rp rr = w.length → leftSide s dir a = false) :
    ∃ T, (∀ t ≤ T, ∀ r, (((compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) t).workTapePos
            (Fin.castAdd kD r) = rp r ∨
          (r = rr ∧ -1 ≤ ((compileTM P l₀ D q0).runFrom
            (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) t).workTapePos
              (Fin.castAdd kD r) ∧ ((compileTM P l₀ D q0).runFrom
            (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) t).workTapePos
              (Fin.castAdd kD r) ≤ max (rp r) 0)) ∧
        ((compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) t).workTapePos
            ∘ Fin.natAdd m = dp) ∧
      (compileTM P l₀ D q0).runFrom
          (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) T =
        mkCfg (some (nextRet cs l s dir b (a.val + 1))) ip rt
          (Function.update rp rr 0) dt dp out := by
  have hread : (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out :
      Cfg (m + kD) Bool (CSt Λ SD m) x).workTapeSymbols (Fin.castAdd kD rr) =
        FinTM.bufferTape w (rp rr) := by
    simp [Cfg.workTapeSymbols, mkCfg, hrt]
  by_cases hm1 : rp rr = -1
  · -- on the left blank: one step right
    have hrd : FinTM.bufferTape w (rp rr) = none := by rw [hm1]; simp
    have hstep : (compileTM P l₀ D q0).step
        (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) =
        mkCfg (some (nextRet cs l s dir b (a.val + 1))) ip rt
          (Function.update rp rr 0) dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      have hls := hl hm1
      simp only [leftSide] at hls
      simp only [compileTM, ctr, hcall, hrr, hread, hrd, Bool.false_eq_true, ↓reduceIte, hls]
      rw [apply_regMove]
      congr 1
      rw [hm1]; simp
    refine ⟨1, fun t ht r => ?_, by simpa using hstep⟩
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact ⟨Or.inl (by simp [mkCfg]), by funext i; simp [mkCfg]⟩
    · obtain rfl : t = 1 := by omega
      simp only [MultiTapeTM.runFrom, Function.iterate_one, hstep]
      refine ⟨?_, by funext i; simp [mkCfg]⟩
      by_cases hr : r = rr
      · subst hr; right; simp [mkCfg, hm1]
      · left; simp [mkCfg, hr]
  · -- otherwise: one step left, then the left scan
    have hn : ∃ n : ℕ, rp rr = n := ⟨(rp rr).toNat, by omega⟩
    obtain ⟨n, hn⟩ := hn
    have hside : FinTM.bufferTape w (rp rr) = none → leftSide s dir a = false := by
      intro hnone
      apply hrgt
      by_contra hne
      have hlt : n < w.length := by omega
      rw [hn] at hnone
      simp [FinTM.bufferTape, List.getElem?_eq_getElem hlt] at hnone
    set rp' := Function.update rp rr (rp rr - 1) with hrp'
    have hstep : (compileTM P l₀ D q0).step
        (mkCfg (some (.retR l s dir b a false)) ip rt rp dt dp out) =
        mkCfg (some (.retR l s dir b a true)) ip rt rp' dt dp out := by
      unfold MultiTapeTM.step
      simp only [mkCfg_state]
      simp only [compileTM, ctr, hcall, hrr, hread, Bool.false_eq_true, ↓reduceIte]
      cases hb : FinTM.bufferTape w (rp rr) with
      | none =>
        have hls := hside hb
        simp only [leftSide] at hls
        simp only [hls, ↓reduceIte, Bool.false_eq_true]
        rw [apply_regMove]
        congr 1
      | some _ =>
        simp only
        rw [apply_regMove]
        congr 1
    obtain ⟨hb, hr⟩ := retR_scan P l₀ D q0 l cs hcall s dir b a w rr hrr rt hrt dt dp out ip n rp'
      (by simp [hrp', hn]) (by omega)
    refine ⟨n + 1 + 1, fun t ht r => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with h | h
      · subst h; exact ⟨Or.inl (by simp [mkCfg]), by funext i; simp [mkCfg]⟩
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
        obtain ⟨h1, h2⟩ := hb t' (by omega) r
        refine ⟨?_, h2⟩
        by_cases hrr' : r = rr
        · subst hrr'
          right
          rcases h1 with h1 | h1
          · rw [h1]; simp only [hrp', Function.update_self]
            exact ⟨trivial, by omega, by omega⟩
          · refine ⟨rfl, h1.2.1, h1.2.2.trans ?_⟩
            simp only [hrp', Function.update_self]
            omega
        · left
          rcases h1 with h1 | h1
          · rw [h1]; simp [hrp', hrr']
          · exact absurd h1.1 hrr'
    · rw [MultiTapeTM.runFrom_succ_eq_step, hstep, hr]
      congr 1
      simp [hrp']

/-- The register positions after restoring the first `a` argument registers. -/
def retPos (cs : CallSpec m d Λ) (rp0 : Fin m → ℤ) (a : ℕ) (r : Fin m) : ℤ :=
  if r ∈ cs.args ∧ cs.args.idxOf r < a then 0 else rp0 r

/-- Register positions within the call's range: non-arguments untouched, argument `r` in
`[-1, |W r|]`. -/
def RegBox (cs : CallSpec m d Λ) (c0pos : Fin m → ℤ) (W : Fin m → List Bool)
    (p : Fin m → ℤ) : Prop :=
  ∀ r, (r ∉ cs.args → p r = c0pos r) ∧ (r ∈ cs.args → -1 ≤ p r ∧ p r ≤ (W r).length)

/-- Restoring all argument registers, one after the other.

**Proof sketch.** Induction on the number `k` of argument registers still to restore. Each
register is restored by `retR_run`, whose side test is supplied by `hside`; the restored head is
at `0`, so the positions remain in the register box. When all are restored the machine returns
to the program state `yes` or `no` according to the answer `b`. -/
lemma regs_run (l : Λ) (cs : CallSpec m d Λ) (hcall : P.call l = some cs) (hnd : cs.args.Nodup)
    (s : Fin (m + 1)) (dir b : Bool) (W : Fin m → List Bool) (rt : Fin m → ℤ → Option Bool)
    (hrt : ∀ r ∈ cs.args, rt r = FinTM.bufferTape (W r)) (dt : Fin kD → ℤ → Option Bool)
    (dp : Fin kD → ℤ) (out : List Bool) (ip : Fin (x.length + 2)) (c0pos rp0 : Fin m → ℤ)
    (hbox : RegBox cs c0pos W rp0)
    (hside : ∀ (a : ℕ) (ha : a < cs.args.length) (hm : a < m),
      (rp0 cs.args[a] = -1 → leftSide s dir ⟨a, hm⟩ = true) ∧
      (rp0 cs.args[a] = (W cs.args[a]).length → leftSide s dir ⟨a, hm⟩ = false)) :
    ∀ k a, a + k = cs.args.length →
      ∃ T, (∀ t ≤ T, RegBox cs c0pos W (fun r => ((compileTM P l₀ D q0).runFrom
          (mkCfg (some (nextRet cs l s dir b a)) ip rt (retPos cs rp0 a) dt dp out) t).workTapePos
            (Fin.castAdd kD r)) ∧
          ((compileTM P l₀ D q0).runFrom
          (mkCfg (some (nextRet cs l s dir b a)) ip rt (retPos cs rp0 a) dt dp out) t).workTapePos
            ∘ Fin.natAdd m = dp) ∧
        (compileTM P l₀ D q0).runFrom
          (mkCfg (some (nextRet cs l s dir b a)) ip rt (retPos cs rp0 a) dt dp out) T =
          mkCfg (some (.prog (if b then cs.yes else cs.no))) ip rt
            (retPos cs rp0 cs.args.length) dt dp out := by
  have hlen : cs.args.length ≤ m := by simpa using hnd.length_le_card
  -- the positions at every stage stay in the box
  have hret : ∀ a, RegBox cs c0pos W (retPos cs rp0 a) := by
    intro a r
    refine ⟨fun hr => by simp [retPos, hr, (hbox r).1 hr], fun hr => ?_⟩
    unfold retPos
    split_ifs
    · exact ⟨by omega, by omega⟩
    · exact (hbox r).2 hr
  intro k
  induction k with
  | zero =>
    intro a ha
    have hna : ¬ (a < cs.args.length ∧ a < m) := by omega
    refine ⟨0, fun t ht => ?_, ?_⟩
    · obtain rfl : t = 0 := by omega
      exact ⟨fun r => by simpa [mkCfg] using hret a r, by funext i; simp [mkCfg]⟩
    · simp only [MultiTapeTM.runFrom_zero, nextRet, hna, ↓reduceDIte]
      rw [show a = cs.args.length by omega]
  | succ k ih =>
    intro a ha
    have hal : a < cs.args.length := by omega
    have ham : a < m := by omega
    have hnr : nextRet (SD := SD) cs l s dir b a = .retR l s dir b ⟨a, ham⟩ false := by
      simp [nextRet, hal, ham]
    set rr := cs.args[a] with hrrdef
    have hrr : cs.args.getD (⟨a, ham⟩ : Fin m).val ⟨a, ham⟩ = rr := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hal, hrrdef]
    have hmem : rr ∈ cs.args := List.getElem_mem hal
    have hidx : cs.args.idxOf rr = a := List.idxOf_getElem hnd a hal
    have hp0 : retPos cs rp0 a rr = rp0 rr := by simp [retPos, hidx]
    obtain ⟨hs1, hs2⟩ := hside a hal ham
    obtain ⟨T₁, hb₁, hr₁⟩ := retR_run P l₀ D q0 l cs hcall s dir b ⟨a, ham⟩ (W rr) rr hrr rt
      (hrt rr hmem) dt dp out ip (retPos cs rp0 a)
      (by rw [hp0]; exact (hbox rr).2 hmem) (by rw [hp0]; exact hs1) (by rw [hp0]; exact hs2)
    have hupd : Function.update (retPos cs rp0 a) rr 0 = retPos cs rp0 (a + 1) := by
      funext r
      by_cases hr : r = rr
      · subst hr; simp [retPos, hidx, hmem]
      · rw [Function.update_of_ne hr]
        unfold retPos
        by_cases hm : r ∈ cs.args
        · have hne : cs.args.idxOf r ≠ a := by
            intro h; apply hr; rw [hrrdef]
            have := List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
            rw [← this]; congr 1
          simp only [hm, true_and]
          split_ifs <;> first | rfl | omega
        · simp [hm]
    rw [hupd] at hr₁
    obtain ⟨T₂, hb₂, hr₂⟩ := ih (a + 1) (by omega)
    refine ⟨T₁ + T₂, fun t ht => ?_, ?_⟩
    · rw [hnr]
      rcases Nat.lt_or_ge t T₁ with h | h
      · have h1 := fun r => (hb₁ t h.le r).1
        have h2 := (hb₁ t h.le rr).2
        refine ⟨fun r => ⟨fun hr => ?_, fun hr => ?_⟩, by simpa using h2⟩
        · beta_reduce
          rcases h1 r with h1 | h1
          · rw [h1]; exact ((hret a) r).1 hr
          · exact absurd (h1.1 ▸ hmem) hr
        · beta_reduce
          rcases h1 r with h1 | h1
          · rw [h1]; exact ((hret a) r).2 hr
          · refine ⟨h1.2.1, h1.2.2.trans ?_⟩
            have := ((hret a) r).2 hr
            omega
      · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
        rw [MultiTapeTM.runFrom_add, hr₁]
        exact hb₂ t' (by omega)
    · rw [hnr, MultiTapeTM.runFrom_add, hr₁, hr₂]

end Return

end Complexity.LogProg
