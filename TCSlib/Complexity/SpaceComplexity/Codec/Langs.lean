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
# The code languages

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
  with an edge `Turing.NDTM.CfgStep` between them;
* `Complexity.Codec.edgeLang N` — `c` is the code of a window-bounded configuration with a
  work head on the window's boundary.

The finite checks on code words that the logspace deciders perform (`ValidChk`, `InitChk`,
`AcceptChk`, `StepChk`), and the reduction of membership to them, are in
`SpaceComplexity/Codec/Checks`.

Configuration-graph infrastructure; not a result of [AB09].

## Main definitions

* `Complexity.Codec.validLang`, `initLang`, `acceptLang`, `stepLang`, `edgeLang`.

## Main results

* `Complexity.Codec.mem_validLang_iff`, `mem_initLang_iff`, `mem_acceptLang_iff`,
  `mem_stepLang_iff`, `mem_edgeLang_iff` — the defining equations of the languages.
* `Complexity.Codec.mem_codeLang_iff` — membership in a language of encoded triples.
* `Complexity.Codec.mem_validLang`, `mem_initLang`, `mem_acceptLang`, `mem_stepLang`,
  `mem_edgeLang` —
  membership through the codec.

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

/-- **Edge codes**: `⟨x, ⟨bits c, bits s⟩⟩` such that `c` is the code at radius `s` of a
window-bounded configuration of `N` on `x` with some work head on the window's boundary, at
position `-s` or `s`. A configuration-graph search at radius `s` that reaches no edge code has
seen every reachable configuration. -/
def edgeLang : Language Bool :=
  {y | ∃ (x : List Bool) (c s : ℕ), y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
    ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
      ∃ i, |C.workTapePos i| = (s : ℤ)}

/-- A word is in the valid-code language exactly when it encodes an input `x`, a code `c` and a
radius `s` such that `c` is the radius-`s` code of a configuration on `x` that stays in the window
of radius `s`. -/
lemma mem_validLang_iff (y : List Bool) :
    y ∈ validLang N ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c := Iff.rfl

/-- A word is in the initial-code language exactly when it encodes an input `x`, a code `c` and a
radius `s` such that `c` is the radius-`s` code of the initial configuration of `N` on `x`. -/
lemma mem_initLang_iff (y : List Bool) :
    y ∈ initLang N ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
      cfgCode s (N.tm.initCfg x) = c := Iff.rfl

/-- A word is in the accepting-code language exactly when it encodes an input `x`, a code `c` and
a radius `s` such that `c` is the radius-`s` code of a configuration on `x` that stays in the
window of radius `s`, is halted and has output exactly `[true]`. -/
lemma mem_acceptLang_iff (y : List Bool) :
    y ∈ acceptLang N ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧ C.state = none ∧
        C.output = [true] := Iff.rfl

/-- A word is in the step language exactly when it encodes an input `x`, two codes `c`, `c'` and a
radius `s` such that `c` and `c'` are the radius-`s` codes of configurations `C`, `C'` on `x` that
stay in the window of radius `s`, with a configuration-graph edge from `C` to `C'`. -/
lemma mem_stepLang_iff (y : List Bool) :
    y ∈ stepLang N ↔ ∃ (x : List Bool) (c c' s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits c') (Nat.bits s))) ∧
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
        ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧
          cfgCode s C' = c' := Iff.rfl

/-- A word is in the edge-code language exactly when it encodes an input `x`, a code `c` and a
radius `s` such that `c` is the radius-`s` code of a configuration on `x` that stays in the
window of radius `s` and has some work head at `-s` or `+s`. -/
lemma mem_edgeLang_iff (y : List Bool) :
    y ∈ edgeLang N ↔ ∃ (x : List Bool) (c s : ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∧
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
        ∃ i, |C.workTapePos i| = (s : ℤ) := Iff.rfl

/-- The pairing is injective in both components. -/
lemma pairEncode_inj {a b a' b' : List Bool} (h : pairEncode a b = pairEncode a' b') :
    a = a' ∧ b = b' := by
  have := pairEncode_injective (show (fun p : List Bool × List Bool => pairEncode p.1 p.2) (a, b) =
    (fun p : List Bool × List Bool => pairEncode p.1 p.2) (a', b') from h)
  simpa using this

/-- **Membership in a language of encoded triples.** Let `L` be a language whose members are
exactly the encodings `⟨x, ⟨bits c, enc t⟩⟩` with `P x c t`, for an injective encoding `enc` of
the tail. Then for every word `w`, `⟨x, ⟨w, enc t⟩⟩ ∈ L` exactly when `w` is the binary word of
some `c` with `P x c t`. The code languages are of this shape: with tail `bits s` for
`validLang`, `initLang`, `acceptLang` and `edgeLang`, and with tail `⟨w', bits s⟩` for
`stepLang`.

Configuration-graph infrastructure ([AB09, §4.1.1]); not a result of [AB09].

**Proof sketch.** A member `⟨x', ⟨bits c, enc t'⟩⟩` equal to `⟨x, ⟨w, enc t⟩⟩` has `x' = x` and
`bits c = w` by injectivity of the pairing, in both layers, and `t' = t` by injectivity of `enc`.
Conversely `⟨x, ⟨bits c, enc t⟩⟩` is a member when `P x c t` holds. -/
theorem mem_codeLang_iff {τ : Type} {enc : τ → List Bool} (henc : Function.Injective enc)
    {L : Language Bool} {P : List Bool → ℕ → τ → Prop}
    (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c : ℕ) (t : τ),
      y = pairEncode x (pairEncode (Nat.bits c) (enc t)) ∧ P x c t)
    (x w : List Bool) (t : τ) :
    pairEncode x (pairEncode w (enc t)) ∈ L ↔ ∃ c, Nat.bits c = w ∧ P x c t := by
  rw [hL]
  constructor
  · rintro ⟨x', c, t', h, hP⟩
    obtain ⟨rfl, h2⟩ := pairEncode_inj h
    obtain ⟨hw, ht⟩ := pairEncode_inj h2
    obtain rfl := henc ht
    exact ⟨c, hw.symm, hP⟩
  · rintro ⟨c, rfl, hP⟩
    exact ⟨x, c, t, rfl, hP⟩

/-- **Membership in the valid-code language.** The encoding of `x`, `bits c` and `bits s` is in
the language exactly when `c` is the radius-`s` code of a configuration on `x` inside the window
of radius `s`. -/
theorem mem_validLang (x : List Bool) (c s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ validLang N ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c := by
  rw [mem_codeLang_iff bits_injective (mem_validLang_iff N)]
  simp only [bits_injective.eq_iff, exists_eq_left]

/-- **Membership in the initial-code language.** The encoding of `x`, `bits c` and `bits s` is in
the language exactly when `c` is the radius-`s` code of `N`'s initial configuration on `x`. -/
theorem mem_initLang (x : List Bool) (c s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ initLang N ↔
      cfgCode s (N.tm.initCfg x) = c := by
  rw [mem_codeLang_iff bits_injective (mem_initLang_iff N)]
  simp only [bits_injective.eq_iff, exists_eq_left]

/-- **Membership in the accepting-code language.** The encoding of `x`, `bits c` and `bits s` is
in the language exactly when `c` is the radius-`s` code of a halted configuration on `x` inside
the window of radius `s` whose output is `[true]`. -/
theorem mem_acceptLang (x : List Bool) (c s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ acceptLang N ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧ C.state = none ∧
        C.output = [true] := by
  rw [mem_codeLang_iff bits_injective (mem_acceptLang_iff N)]
  simp only [bits_injective.eq_iff, exists_eq_left]

/-- **Membership in the step language.** The encoding of `x`, `bits c`, `bits c'` and `bits s` is
in the language exactly when `c` and `c'` are the radius-`s` codes of configurations on `x` inside
the window of radius `s`, the second reached from the first by one step of `N`. -/
theorem mem_stepLang (x : List Bool) (c c' s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits c') (Nat.bits s))) ∈
        stepLang N ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
        ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow s C' ∧
          cfgCode s C' = c' := by
  -- the tail `⟨bits c', bits s⟩` is the injective image of the pair `(c', s)`
  have henc : Function.Injective fun t : ℕ × ℕ => pairEncode (Nat.bits t.1) (Nat.bits t.2) :=
    fun t t' h => by
      obtain ⟨h1, h2⟩ := pairEncode_inj h
      exact Prod.ext (bits_injective h1) (bits_injective h2)
  have hL : ∀ y, y ∈ stepLang N ↔ ∃ (x : List Bool) (c : ℕ) (t : ℕ × ℕ),
      y = pairEncode x (pairEncode (Nat.bits c) (pairEncode (Nat.bits t.1) (Nat.bits t.2))) ∧
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow t.2 C ∧ cfgCode t.2 C = c ∧
        ∃ C' : Cfg N.k Bool N.State x, N.tm.CfgStep C C' ∧ Cfg.InWindow t.2 C' ∧
          cfgCode t.2 C' = t.1 := fun y => by
    rw [mem_stepLang_iff]
    simp only [Prod.exists]
  rw [mem_codeLang_iff henc hL x (Nat.bits c) (c', s)]
  simp only [bits_injective.eq_iff, exists_eq_left]

/-- **Membership in the edge-code language.** The encoding of `x`, `bits c` and `bits s` is in
the language exactly when `c` is the radius-`s` code of a configuration on `x` inside the window
of radius `s` with some work head at `-s` or `+s`. -/
theorem mem_edgeLang (x : List Bool) (c s : ℕ) :
    pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ edgeLang N ↔
      ∃ C : Cfg N.k Bool N.State x, Cfg.InWindow s C ∧ cfgCode s C = c ∧
        ∃ i, |C.workTapePos i| = (s : ℤ) := by
  rw [mem_codeLang_iff bits_injective (mem_edgeLang_iff N)]
  simp only [bits_injective.eq_iff, exists_eq_left]

end Complexity.Codec
