/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance
import TCSlib.Complexity.TuringMachine.Build.ZoneStep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to two work tapes

[HS66], as used in [AB09, §1.7] for the efficient universal machine: `k` work tapes are simulated
by two work tapes with a slowdown of `O(T log T)`. Run for run, every binary machine has a
binary two-work-tape equivalent that reproduces each halting run of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and whose completed outputs are outputs of the source.

## Deviations from [AB09] and [HS66]

* The slowdown is stated per run, with an existential constant, and padded with `+ 1` in both
  factors so that it covers the empty run (`t = 0`).
* The statement includes the converse (every completed output of the simulator is an output of
  the source), which the universal machine's correctness needs.
* The statement holds for every number of work tapes, zero and one included.

## Main definitions

No new definitions: the reduction is an existential contract.

## Main results

* `Turing.FinTM.two_work_tapes_run` — two work tapes suffice, with logarithmic overhead, run by
  run and with the converse [HS66].
* `Turing.FinTM.two_work_tapes_binary` — the same at the level of computed functions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.7, the proof of Theorem 1.9.)
* [HS66] F. C. Hennie, R. E. Stearns, *Two-tape simulation of multitape Turing machines*,
  J. ACM 13(4), 1966, 533–546.
-/

namespace Turing.FinTM

/-! ### The frame and the zero-tape case -/

/-- **Zero work tapes** [HS66; AB09, §1.7]: a binary machine `M` without work tapes has a binary
equivalent with two work tapes that reproduces each halting run of `t` steps within
`1 · (t + 1)(log₂(t + 1) + 1)` steps, and whose completed outputs are outputs of `M`.

**Proof sketch.** Run `M` on the two-tape host through the forwarding embedding
`Turing.embedEmitTM` along the empty selection `Fin M.k ↪ Fin 2`, restarted at `M`'s initial
state. The host's initial configuration is the embedding of `M`'s into the blank frame with
heads at `0` and empty prefix (`Turing.embedEmitCfg_eq`, field by field from the `Cfg.init`
equations; the selected bank is empty). By `Turing.embedEmitTM_runFrom` the host's run is the
embedding of `M`'s run, so the two have the same state and the same output at every time
(`Turing.embedEmitCfg_state`, `Turing.embedEmitCfg_output`). Hence they halt together with the
same output, and `t ≤ (t + 1)(log₂(t + 1) + 1)` pads the time. -/
private theorem tt_zero_tapes (M : FinTM Bool) (hk : M.k = 0) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  obtain ⟨σ⟩ : Nonempty (Fin M.k ↪ Fin 2) := ⟨Fin.castLEEmb (by omega)⟩
  -- the host: R1 of `M.tm`, restarted at `M`'s initial state
  obtain ⟨N, hq, hr⟩ : ∃ N : MultiTapeTM 2 Bool M.State,
      (∀ x, N.initCfg x = Cfg.init M.tm.q₀ x) ∧
        ∀ (x : List Bool) (c : Cfg 2 Bool M.State x) (t : ℕ),
          N.runFrom c t = (embedEmitTM σ M.tm).runFrom c t :=
    ⟨_, fun x => MultiTapeTM.initCfg_with_q₀ (embedEmitTM σ M.tm) M.tm.q₀ x,
      fun _ c t => MultiTapeTM.runFrom_with_q₀ (embedEmitTM σ M.tm) M.tm.q₀ c t⟩
  -- the host's initial configuration is the embedding of `M`'s into the blank frame
  have hinit : ∀ x : List Bool,
      embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (M.tm.initCfg x) =
        Cfg.init M.tm.q₀ x := by
    intro x
    rw [MultiTapeTM.initCfg_eq]
    refine embedEmitCfg_eq σ _ _ [] _ _ ?_ ?_ ?_ ?_ ?_
    · simp only [Cfg.init_state]
    · simp only [Cfg.init_inputPos]
    · simp only [Cfg.init_output, List.append_nil]
    · intro i
      exact absurd i.isLt (by omega)
    · intro j _
      exact ⟨funext fun p => by simp only [Cfg.init_workTapes],
        by simp only [Cfg.init_workTapePos]⟩
  -- the host's run is the embedding of `M`'s
  have hrun : ∀ (x : List Bool) (t : ℕ), N.runFrom (N.initCfg x) t =
      embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (M.tm.runFrom (M.tm.initCfg x) t) := by
    intro x t
    rw [hq, ← hinit x, hr, embedEmitTM_runFrom]
  refine ⟨{ k := 2, State := M.State, tm := N }, 1, rfl, fun x o t h => ?_, fun x o h => ?_⟩
  · obtain ⟨hs, ho⟩ := (computesInTime_iff M x o t).1 h
    have hb : t ≤ 1 * ((t + 1) * (Nat.log 2 (t + 1) + 1)) :=
      calc t ≤ t + 1 := Nat.le_succ t
        _ = (t + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ (t + 1) * (Nat.log 2 (t + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = 1 * ((t + 1) * (Nat.log 2 (t + 1) + 1)) := (Nat.one_mul _).symm
    refine ComputesInTime.mono ?_ hb
    rw [computesInTime_iff]
    show (N.runFrom (N.initCfg x) t).state = none ∧ (N.runFrom (N.initCfg x) t).output = o
    refine ⟨?_, ?_⟩
    · rw [hrun, embedEmitCfg_state, hs]
    · rw [hrun, embedEmitCfg_output, ho, List.nil_append]
  · obtain ⟨t, ht⟩ := h
    obtain ⟨hs, ho⟩ := (computesInTime_iff _ x o t).1 ht
    have hs' : (N.runFrom (N.initCfg x) t).state = none := hs
    have ho' : (N.runFrom (N.initCfg x) t).output = o := ho
    rw [hrun, embedEmitCfg_state] at hs'
    rw [hrun, embedEmitCfg_output, List.nil_append] at ho'
    exact ⟨t, (computesInTime_iff M x o t).2 ⟨hs', ho'⟩⟩

/-- **The frame of the two-work-tape reduction** [HS66; AB09, §1.7, with Claim 1.5 for the
alphabet]: let `HS` be a machine over the zone alphabet `Turing.ZoneSym M.k` with two work tapes
that reproduces each halting run of `M` of `t` steps on the encoded input `x.map Sum.inl`, with
the encoded output, within `c₁ · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of
which on an encoded input is the encoding of an output of `M`. Then `M` has a binary equivalent
with two work tapes, with the same overhead up to a constant, and whose completed outputs are
outputs of `M`.

**Proof sketch.** Reduce `HS` to the binary alphabet by `Turing.FinTM.alphabet_reduction_run`
along `Sum.inl : Bool ↪ ZoneSym M.k`, which keeps the two work tapes and multiplies the time by a
constant `c₂`; the constant of the result is `c₂ · c₁`. Forward, `M`'s run gives `HS`'s within
`c₁ · (t + 1)(log₂(t + 1) + 1)` steps, and the reduction's forward direction gives the binary
machine's. Conversely, a completed output `w` of the binary machine comes from a completed output
`o'` of `HS` on the encoded input such that every binary word encoding to `o'` is `w`; the
converse property of `HS` writes `o'` as the encoding of an output `v` of `M`, so `v = w`. -/
private theorem tt_frame (M : FinTM Bool) (HS : FinTM (ZoneSym M.k)) (hHS : HS.k = 2) (c₁ : ℕ)
    (hfwd : ∀ (x o : List Bool) (t : ℕ), M.ComputesInTime x o t →
      HS.ComputesInTime (x.map Sum.inl) (o.map Sum.inl)
        (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1))))
    (hconv : ∀ (x : List Bool) (o' : List (ZoneSym M.k)) (t' : ℕ),
      HS.ComputesInTime (x.map Sum.inl) o' t' →
        ∃ (t : ℕ) (v : List Bool), M.ComputesInTime x v t ∧ o' = v.map Sum.inl) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  obtain ⟨c₂, M', hk, hf, hc⟩ :=
    alphabet_reduction_run (Function.Embedding.inl : Bool ↪ ZoneSym M.k) HS
  have hinl : ⇑(Function.Embedding.inl : Bool ↪ ZoneSym M.k) = Sum.inl :=
    funext fun b => Function.Embedding.inl_apply b
  rw [hinl] at hf hc
  refine ⟨M', c₂ * c₁, hk.trans hHS, fun x o t h => ?_, fun x o h => ?_⟩
  · rw [Nat.mul_assoc]
    exact hf x o _ (hfwd x o t h)
  · obtain ⟨t', o', ht', hv⟩ := hc x o h
    obtain ⟨t, v, hM, rfl⟩ := hconv x o' t' ht'
    obtain rfl := hv v rfl
    exact ⟨t, hM⟩

/-- **The route of the two-work-tape reduction** [HS66; AB09, §1.7]: if every binary machine
with at least one work tape has a two-work-tape zone machine with the forward property and the
image converse of `tt_frame`, then every binary machine has a binary equivalent with two work
tapes, with overhead `O((t + 1) log(t + 1))` per run of `t` steps, whose completed outputs are
outputs of the source.

**Proof sketch.** Without work tapes, `tt_zero_tapes`; otherwise the hypothesis gives the zone
machine, and `tt_frame` finishes. -/
private theorem tt_route
    (hHS : ∀ M : FinTM Bool, 1 ≤ M.k →
      ∃ (HS : FinTM (ZoneSym M.k)) (_ : HS.k = 2) (c₁ : ℕ),
        (∀ (x o : List Bool) (t : ℕ), M.ComputesInTime x o t →
          HS.ComputesInTime (x.map Sum.inl) (o.map Sum.inl)
            (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
        ∀ (x : List Bool) (o' : List (ZoneSym M.k)) (t' : ℕ),
          HS.ComputesInTime (x.map Sum.inl) o' t' →
            ∃ (t : ℕ) (v : List Bool), M.ComputesInTime x v t ∧ o' = v.map Sum.inl)
    (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  by_cases hk : M.k = 0
  · exact tt_zero_tapes M hk
  · obtain ⟨HS, hHSk, c₁, hf, hc⟩ := hHS M (by omega)
    exact tt_frame M HS hHSk c₁ hf hc

/-! ### The target -/

/-- **Two work tapes suffice, run by run** [HS66]: every binary machine `M` has a binary
equivalent `M'` with two work tapes that reproduces each halting run of `M` of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of `M'` is an output of `M` on
the same input.

**Proof sketch.** (The Hennie–Stearns simulation.) The first work tape of `M'` holds all `k` of
`M`'s work tapes as tracks, folded around a fixed origin cell into zones of doubling sizes
`2^i`, so that every simulated head stays at the origin and a tape movement shifts contents
between neighbouring zones. Each zone is kept half full. A shift that empties or fills a zone `i`
rebalances zones `0, …, i` using the second work tape as scratch, in `O(2^i)` steps, and a zone `i`
is rebalanced at most once every `2^(i-1)` simulated steps. Summing over the `log₂ t + 1` zones a
run of `t` steps reaches gives `O(t log t)` steps in all. The converse holds because `M'` writes
an output symbol exactly when `M` does, in the same order, and halts only when `M` halts. With
no work tapes, `M` is run directly beside two idle tapes. -/
theorem two_work_tapes_run (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  refine tt_route (fun M hk => ?_) M
  sorry

/-- **Two work tapes suffice** for computing a function: if a binary machine computes `f` within
time `T`, then a binary machine with two work tapes computes `f` within
`c · (T n + 1)(log₂(T n + 1) + 1)` for some constant `c` [HS66].

**Proof sketch.** Apply `Turing.FinTM.two_work_tapes_run` to `M` and use its forward direction at
each input `x`, with the run of `T |x|` steps that computes `f x`. -/
theorem two_work_tapes_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      M'.ComputesFunInTime f fun n => c * ((T n + 1) * (Nat.log 2 (T n + 1) + 1)) := by
  obtain ⟨M', c, hk, h, -⟩ := two_work_tapes_run M
  exact ⟨M', c, hk, (computesFunInTime_iff _ _ _).2 fun x =>
    h x (f x) _ ((computesFunInTime_iff _ _ _).1 hM x)⟩

end Turing.FinTM
