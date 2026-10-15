/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Checks

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Acceptance as a chain of codes

The bridge between a space-bounded nondeterministic decider and the code languages: for a
window radius `s` at least the space bound on `x`, `x` is accepted exactly when there is a
chain of codes `c₀, …, c_t` — the initial code, configuration-graph edges between
consecutive codes, an accepting last code — of length at most the vertex count
`Turing.FinNDTM.configBound |x| s`, every code below `2 ^ (codeK N · (s + logSpace |x| + 1))`.
This is the form in which configuration-graph algorithms (Savitch's midpoint recursion, the
`PATH` reduction, inductive counting) consume a nondeterministic decider [AB09, §4.1.1,
§4.2, §4.3]: they search for such chains over register-held codes, calling the logspace
deciders of the code languages.

The window of a space-bounded branch and the step "an accepting branch of any length gives
membership" are those of `TCSlib.Complexity.SpaceComplexity.ConfigGraph`
(`Turing.NDTM.runWith_take_inWindow`, `Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin`),
over the window predicate `Turing.Cfg.InWindow`. Within the codec, the path-to-membership
argument exists once (`mem_of_codePath`); `mem_iff_codeChain` and the Savitch machine
(`Complexity.LogProg.SavitchARM.mem_iff_reach`) both use it.

## Main definitions

* `Complexity.Codec.StepRel` — the code-level step relation of a decider.

## Main results

* `Complexity.Codec.configBound_mono` — a helper.
* `Complexity.Codec.mem_of_codePath` — a `StepRel`-path of any length from an initial to an
  accepting code gives membership.
* `Complexity.Codec.mem_iff_codeChain` — the bridge lemma. [AB09, §4.1.1, Claim 4.4(1) in
  code form]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4.)
-/

namespace Complexity.Codec

open Turing LogProg

variable {N : FinNDTM Bool} {x : List Bool}

/-! ## The bridge -/

/-- The vertex count is monotone in the window radius. -/
lemma configBound_mono (N : FinNDTM Bool) (n : ℕ) {s s' : ℕ} (h : s ≤ s') :
    N.configBound n s ≤ N.configBound n s' := by
  unfold FinNDTM.configBound
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul
  · apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
  · exact Nat.pow_le_pow_left (by omega) _

/-- **The code-level step relation** of `N` on `x` at radius `s`: `⟨x, ⟨bits a, ⟨bits b,
bits s⟩⟩⟩` is a step pair (a member of `Complexity.Codec.stepLang N`). -/
def StepRel (N : FinNDTM Bool) (x : List Bool) (s : ℕ) (a b : ℕ) : Prop :=
  pairEncode x (pairEncode (Nat.bits a) (pairEncode (Nat.bits b) (Nat.bits s))) ∈ stepLang N

/-- **A code path from an initial to an accepting code makes the input a member**: if `N`
decides `L` (in any space bound), `u` is the initial code and `v` an accepting code at
radius `s`, and `v` is reachable from `u` along step pairs (`Relation.ReflTransGen` of
`StepRel N x s`, of any length), then `x ∈ L`. This is the direction `⇐` of
`Complexity.Codec.mem_iff_codeChain`, without its length and size bounds. [AB09, §4.1.1:
a path from the initial to an accepting configuration in the configuration graph is an
accepting branch]

**Proof sketch.** By induction along the path, some choice word reaches a configuration with
the vertex of the current code: codes determine vertices on window-bounded configurations
(`coreSum_eq_of_cfgWord_eq`) and steps respect vertices (`Turing.NDTM.coreSum_stepWith`).
At the accepting code the vertex is halted with output `[true]`, so the word accepts, and an
accepting branch of any length gives membership
(`Turing.FinNDTM.DecidesInSpace.mem_of_acceptsWithin`). -/
theorem mem_of_codePath {L : Language Bool} {sp : ℕ → ℕ} (h : N.DecidesInSpace L sp)
    (x : List Bool) (s u v : ℕ)
    (hinit : pairEncode x (pairEncode (Nat.bits u) (Nat.bits s)) ∈ initLang N)
    (hpath : Relation.ReflTransGen (StepRel N x s) u v)
    (hacc : pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ acceptLang N) : x ∈ L := by
  rw [mem_initLang] at hinit
  have chain : ∀ c, Relation.ReflTransGen (StepRel N x s) u c → ∃ w : List Bool,
      ∃ D : Cfg N.k Bool N.State x, Cfg.InWindow s D ∧ cfgCode s D = c ∧
        NDTM.coreSum (N.tm.runWith w (N.tm.initCfg x)) = NDTM.coreSum D := by
    intro c hc
    induction hc with
    | refl =>
      exact ⟨[], N.tm.initCfg x, Cfg.inWindow_init _ x s, hinit, rfl⟩
    | tail _ hst ih =>
      obtain ⟨w, D, hD, hcD, hcore⟩ := ih
      obtain ⟨C, hC, hcC, C', ⟨b, hb⟩, hC', hcC'⟩ := (mem_stepLang N x _ _ s).mp hst
      have hDC : NDTM.coreSum D = NDTM.coreSum C :=
        coreSum_eq_of_cfgWord_eq hD hC (by rw [← bits_cfgCode, ← bits_cfgCode, hcD, hcC])
      refine ⟨w ++ [b], C', hC', hcC', ?_⟩
      rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil, ← hb]
      exact NDTM.coreSum_stepWith N.tm b (hcore.trans hDC)
  obtain ⟨w, D, hD, hcD, hcore⟩ := chain v hpath
  obtain ⟨C, hC, hcC, hst, hout⟩ := (mem_acceptLang N x _ s).mp hacc
  have hDC : NDTM.coreSum D = NDTM.coreSum C :=
    coreSum_eq_of_cfgWord_eq hD hC (by rw [← bits_cfgCode, ← bits_cfgCode, hcD, hcC])
  have hfin := hcore.trans hDC
  apply h.mem_of_acceptsWithin (t := w.length)
  refine ⟨w, rfl, ?_, ?_⟩
  · have := congrArg (fun z => z.1.1) hfin
    simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core] at this
    rw [this, hst]
  · have := congrArg Prod.snd hfin
    simp only [NDTM.coreSum] at this
    rw [hout] at this
    exact (outSummary_eq_accept_iff _).mp this

/-- **Acceptance as a chain of codes** (the bridge lemma): let `N` decide `L` in space `sp`,
and let `s ≥ sp |x|`. Then `x ∈ L` iff there are `t ≤ configBound |x| s` and codes
`c 0, …, c t` such that `c 0` is the initial code, each `(c i, c (i + 1))` is a step pair,
`c t` is an accepting code (all at radius `s`, as memberships in the code languages), and
every code is below `2 ^ (codeK N · (s + logSpace |x| + 1))`. [AB09, §4.1.1: the machine
accepts iff the configuration graph has a path from the initial to an accepting
configuration; Claim 4.4(1) bounds its length by the vertex count]

**Proof sketch.** (⇒) Take an accepting branch of length the vertex count at the space bound
(`DecidesInSpace.mem_iff_acceptsWithin_configBound`, `configBound_mono`); its prefixes stay in
the window `[-s, s]` (`Turing.NDTM.runWith_take_inWindow`: compare with a branch of the
halting budget — padding the accepting word, or truncating it where every branch has halted);
the codes of
the prefix configurations form the chain, consecutive prefixes differing by one step, the
last halted with output `[true]`; codes are short (`cfgCode_lt`). (⇐) The chain is a
`StepRel`-path from the initial to the accepting code, which gives membership
(`mem_of_codePath`). -/
theorem mem_iff_codeChain {L : Language Bool} {sp : ℕ → ℕ} (h : N.DecidesInSpace L sp)
    (x : List Bool) (s : ℕ) (hs : sp x.length ≤ s) :
    x ∈ L ↔ ∃ (t : ℕ) (c : ℕ → ℕ), t ≤ N.configBound x.length s ∧
      pairEncode x (pairEncode (Nat.bits (c 0)) (Nat.bits s)) ∈ initLang N ∧
      (∀ i < t, pairEncode x (pairEncode (Nat.bits (c i))
        (pairEncode (Nat.bits (c (i + 1))) (Nat.bits s))) ∈ stepLang N) ∧
      pairEncode x (pairEncode (Nat.bits (c t)) (Nat.bits s)) ∈ acceptLang N ∧
      ∀ i ≤ t, c i < 2 ^ (codeK N * (s + logSpace x.length + 1)) := by
  constructor
  · intro hx
    obtain ⟨w, hw, hhalt, hout⟩ := (h.mem_iff_acceptsWithin_configBound x).mp hx
    set tb := N.configBound x.length (sp x.length)
    obtain ⟨T, hHalt, hSpace, -⟩ := h x
    -- every prefix configuration is in the window
    have hwin : ∀ j, Cfg.InWindow s (N.tm.runWith (w.take j) (N.tm.initCfg x)) := by
      by_cases hT : tb ≤ T
      · intro j
        set w' := w ++ List.replicate (T - tb) false
        have hw' : w'.length = T := by simp [w', hw]; omega
        have hsp := (hSpace w' hw').trans hs
        by_cases hj : j ≤ tb
        · have e : w'.take j = w.take j := by
            simp only [w']; rw [List.take_append_of_le_length (by omega)]
          rw [← e]; exact NDTM.runWith_take_inWindow N.tm w' hsp j
        · have e1 : w.take j = w := List.take_of_length_le (by omega)
          have e2 : w'.take tb = w := by
            simp only [w']; rw [List.take_append_of_le_length (by omega),
              List.take_of_length_le (by omega)]
          rw [e1, ← e2]; exact NDTM.runWith_take_inWindow N.tm w' hsp tb
      · intro j
        have hlen : (w.take T).length = T := List.length_take_of_le (by omega)
        have hsp := (hSpace (w.take T) hlen).trans hs
        by_cases hj : j ≤ T
        · have e : (w.take T).take j = w.take j := by rw [List.take_take, Nat.min_eq_left hj]
          rw [← e]; exact NDTM.runWith_take_inWindow N.tm (w.take T) hsp j
        · have frozen : N.tm.runWith (w.take j) (N.tm.initCfg x) =
              N.tm.runWith (w.take T) (N.tm.initCfg x) := by
            have : w.take j = w.take T ++ (w.take j).drop T := by
              conv_lhs => rw [← List.take_append_drop T (w.take j)]
              rw [List.take_take, Nat.min_eq_left (by omega : T ≤ j)]
            rw [this, NDTM.runWith_append, NDTM.runWith_of_halt _ (hHalt _ hlen)]
          rw [frozen, show w.take T = (w.take T).take T by simp]
          exact NDTM.runWith_take_inWindow N.tm (w.take T) hsp T
    refine ⟨tb, fun i => cfgCode s (N.tm.runWith (w.take i) (N.tm.initCfg x)),
      configBound_mono N _ hs, ?_, fun i hi => ?_, ?_, fun i _ => cfgCode_lt s _⟩
    · rw [mem_initLang]; simp
    · rw [mem_stepLang]
      refine ⟨_, hwin i, rfl, _, ⟨w[i]'(by omega), ?_⟩, hwin (i + 1), rfl⟩
      rw [List.take_succ, NDTM.runWith_append, List.getElem?_eq_getElem (by omega)]
      rfl
    · rw [mem_acceptLang]
      refine ⟨_, hwin tb, rfl, ?_, ?_⟩
      · rw [← hw, List.take_length]; exact hhalt
      · rw [← hw, List.take_length]; exact hout
  · rintro ⟨t, c, -, hinit, hstep, hacc, -⟩
    have hpath : ∀ j ≤ t, Relation.ReflTransGen (StepRel N x s) (c 0) (c j) := by
      intro j
      induction j with
      | zero => intro _; exact Relation.ReflTransGen.refl
      | succ j ih => intro hj; exact (ih (by omega)).tail (hstep j (by omega))
    exact mem_of_codePath h x s (c 0) (c t) hinit (hpath t le_rfl) hacc

end Complexity.Codec
