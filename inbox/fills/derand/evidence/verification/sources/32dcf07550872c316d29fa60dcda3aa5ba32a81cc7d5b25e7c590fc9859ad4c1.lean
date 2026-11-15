/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Step

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The four code languages

The languages a configuration-graph algorithm calls on codes of configurations of a fixed
machine `N` on its real input `x`, at window radius `s` [AB09, §4.1.1]. Each takes the input
`x`, one or two codes and the radius, laid out as the virtual input of a `whole`-mode call
of an abstract register machine whose registers hold the codes and the radius
(`Complexity.LogProg.vword`): `⟨x, ⟨bits c, bits s⟩⟩` or `⟨x, ⟨bits c, ⟨bits c', bits s⟩⟩⟩`.

* `Complexity.Codec.validLang N` — `c` is the code of a window-bounded configuration;
* `Complexity.Codec.initLang N` — `c` is the code of the initial configuration;
* `Complexity.Codec.acceptLang N` — `c` is the code of a halted window-bounded
  configuration with output `[true]` (acceptance as in `Turing.FinNDTM.AcceptsWithin`);
* `Complexity.Codec.stepLang N` — `c`, `c'` are codes of window-bounded configurations
  with an edge `Turing.NDTM.CfgStep` between them.

Besides the membership characterizations, this file reduces membership to the finite
checks on code words that the logspace deciders perform (`ValidChk`, `InitChk`,
`AcceptChk`, `StepChk`).

Configuration-graph infrastructure; not a result of [AB09].

## Main definitions

* `Complexity.Codec.validLang`, `initLang`, `acceptLang`, `stepLang`.
* `Complexity.Codec.InitChk`, `AcceptChk`, `StepChk` — the word-level checks.

## Main results

* `Complexity.Codec.mem_validLang`, `mem_initLang`, `mem_acceptLang`, `mem_stepLang` —
  membership through the codec.
* `Complexity.Codec.initChk_iff`, `acceptChk_iff`, `stepChk_iff` — the checks recognize
  the code words of the respective configurations.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.Codec

open Turing LogProg

variable (N : FinNDTM Bool)

/-! ## The languages -/

/-- **Valid codes**: `⟨x, ⟨bits c, bits s⟩⟩` such that `c` is the code at radius `s` of a
window-bounded configuration of `N` on `x`. -/
def validLang : Language Bool :=
  {y | ∃ (x : List Bool) (c s : ℕ), y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
    ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c}

/-- **Initial codes**: `⟨x, ⟨bits c, bits s⟩⟩` such that `c` is the code at radius `s` of the
initial configuration of `N` on `x`. -/
def initLang : Language Bool :=
  {y | ∃ (x : List Bool) (c s : ℕ), y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
    cfgCode s (N.tm.initCfg x) = c}

/-- **Accepting codes**: `⟨x, ⟨bits c, bits s⟩⟩` such that `c` is the code at radius `s` of a
window-bounded configuration of `N` on `x` that is halted with output exactly `[true]`. -/
def acceptLang : Language Bool :=
  {y | ∃ (x : List Bool) (c s : ℕ), y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
    ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧ C.state = none ∧
      C.output = [true]}

/-- **Step pairs**: `⟨x, ⟨bits c, ⟨bits c', bits s⟩⟩⟩` such that `c` and `c'` are the codes at
radius `s` of window-bounded configurations of `N` on `x` joined by a configuration-graph
edge (one step under some choice bit). -/
def stepLang : Language Bool :=
  {y | ∃ (x : List Bool) (c c' s : ℕ),
    y = pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits c') (Nat.bits s))) ∧
    ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
      ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧ cfgCode s C' = c'}

/-- The pairing is injective in both components. -/
lemma pairEncode_inj {a b a' b' : List Bool} (h : pairEncode a b = pairEncode a' b') :
    a = a' ∧ b = b' := by
  have := pairEncode_injective (show (fun p : List Bool × List Bool => pairEncode p.1 p.2) (a, b) =
    (fun p : List Bool × List Bool => pairEncode p.1 p.2) (a', b') from h)
  simpa using this

/-- **Membership in the valid-code language.** -/
theorem mem_validLang (x : List Bool) (c s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ validLang N ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c := by
  constructor
  · rintro ⟨x', c', s', h, hC⟩
    obtain ⟨rfl, h2⟩ := pairEncode_inj h
    obtain ⟨h3, h4⟩ := pairEncode_inj h2
    rw [bits_injective h3, bits_injective h4]
    exact hC
  · intro h; exact ⟨x, c, s, rfl, h⟩

/-- **Membership in the initial-code language.** -/
theorem mem_initLang (x : List Bool) (c s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ initLang N ↔
      cfgCode s (N.tm.initCfg x) = c := by
  constructor
  · rintro ⟨x', c', s', h, hC⟩
    obtain ⟨rfl, h2⟩ := pairEncode_inj h
    obtain ⟨h3, h4⟩ := pairEncode_inj h2
    rw [bits_injective h3, bits_injective h4]
    exact hC
  · intro h; exact ⟨x, c, s, rfl, h⟩

/-- **Membership in the accepting-code language.** -/
theorem mem_acceptLang (x : List Bool) (c s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ acceptLang N ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧ C.state = none ∧
        C.output = [true] := by
  constructor
  · rintro ⟨x', c', s', h, hC⟩
    obtain ⟨rfl, h2⟩ := pairEncode_inj h
    obtain ⟨h3, h4⟩ := pairEncode_inj h2
    rw [bits_injective h3, bits_injective h4]
    exact hC
  · intro h; exact ⟨x, c, s, rfl, h⟩

/-- **Membership in the step language.** -/
theorem mem_stepLang (x : List Bool) (c c' s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits c') (Nat.bits s))) ∈
        stepLang N ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
        ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧
          cfgCode s C' = c' := by
  constructor
  · rintro ⟨x', c₁, c₂, s', h, hC⟩
    obtain ⟨rfl, h2⟩ := pairEncode_inj h
    obtain ⟨h3, h4⟩ := pairEncode_inj h2
    obtain ⟨h5, h6⟩ := pairEncode_inj h4
    rw [bits_injective h3, bits_injective h5, bits_injective h6]
    exact hC
  · intro h; exact ⟨x, c, c', s, rfl, h⟩

end Complexity.Codec
