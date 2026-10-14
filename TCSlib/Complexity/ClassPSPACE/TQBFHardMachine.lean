/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassPSPACE.TQBFHardSemantics
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Acceptance as a short path of blocks

[AB09, Claim 4.4 and the proof of Theorem 4.13]: a space-bounded machine accepts `x` iff its
configuration graph has a path from the initial to an accepting configuration of length at
most the number of configurations. This file restates the bridge lemma of the configuration
codec (`Complexity.Codec.mem_iff_codeChain`, `Complexity.Codec.mem_of_codePath`) in the
form the `TQBF` reduction quantifies over: **blocks** of `w ≥ codeLen` bits whose first
`codeLen` bits are a code word, a one-step relation `blockStep` that is reflexive (so that
paths of length at most `2^w` are paths of length exactly `2^w`), and the midpoint recursion
`Complexity.TQBFHard.Mid` of `TQBFHardSemantics`.

Infrastructure for `Complexity.TQBF_PSPACEHard`; not itself a book result.

## Main definitions

* `Complexity.TQBFHard.codeLen` — the length of a code word.
* `Complexity.TQBFHard.blockInit`, `blockAcc`, `blockStep` — the three code-language tests on
  the code-word prefixes of blocks.

## Main results

* `Complexity.TQBFHard.mem_iff_mid` — membership is "some initial block reaches some
  accepting block in the midpoint recursion of depth `w`". [AB09, Claim 4.4(1), proof of
  Theorem 4.13]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4; §4.2, Theorem 4.13.)
-/

namespace Complexity

namespace TQBFHard

open Turing Codec LogProg

variable (N : FinNDTM Bool)

/-- The length `W(2s + 1) + wP n + 1` of a code word at input length `n` and radius `s`
(`Complexity.Codec.length_cfgWord`). -/
def codeLen (n s : ℕ) : ℕ := W N * (2 * s + 1) + wP n + 1

/-- The initial-code test on the first `L` bits of a block. -/
def blockInit (x : List Bool) (s L : ℕ) (β : List Bool) : Prop :=
  pairEncode x (pairEncode (β.take L) (Nat.bits s)) ∈ initLang N

/-- The accepting-code test on the first `L` bits of a block. -/
def blockAcc (x : List Bool) (s L : ℕ) (β : List Bool) : Prop :=
  pairEncode x (pairEncode (β.take L) (Nat.bits s)) ∈ acceptLang N

/-- **The one-step relation on blocks**: equal blocks, or blocks whose first `L` bits are a
step pair of the code (`Complexity.Codec.stepLang`). Reflexive by its first disjunct. -/
def blockStep (x : List Bool) (s L : ℕ) (β β' : List Bool) : Prop :=
  β = β' ∨ pairEncode x (pairEncode (β.take L) (pairEncode (β'.take L) (Nat.bits s))) ∈
    stepLang N

/-- With a reflexive one-step relation, a path can be lengthened. (Proved, by induction on
the excess, padding at the end.) -/
theorem steps_mono {w : ℕ} {E : List Bool → List Bool → Prop} (hE : ∀ B, E B B)
    {k k' : ℕ} (hk : k ≤ k') {A B : List Bool} (hB : B.length = w) (h : Steps w E k A B) :
    Steps w E k' A B := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + d := ⟨k' - k, by omega⟩
  clear hk
  induction d with
  | zero => simpa using h
  | succ d ih => exact ⟨B, hB, ih, hE B⟩

/-- A block path is a path of code-word prefixes along step pairs. (Proved, by induction on
the path length.) -/
theorem steps_reflTransGen (x : List Bool) (s L w : ℕ) :
    ∀ (k : ℕ) (A B : List Bool), Steps w (blockStep N x s L) k A B →
      Relation.ReflTransGen (fun γ γ' : List Bool =>
        pairEncode x (pairEncode γ (pairEncode γ' (Nat.bits s))) ∈ stepLang N)
        (A.take L) (B.take L) := by
  intro k
  induction k with
  | zero => rintro A B rfl; exact Relation.ReflTransGen.refl
  | succ k ih =>
    rintro A B ⟨z, -, h1, h2 | h2⟩
    · subst h2; exact ih A z h1
    · exact (ih A z h1).tail h2

/-- A path of words along step pairs from the word of a code `u` reaches only words of codes,
along the code-level step relation `Complexity.Codec.StepRel`. (Proved, by induction along
the path.) -/
theorem reflTransGen_stepRel (x : List Bool) (s u : ℕ) {γ : List Bool}
    (h : Relation.ReflTransGen (fun γ γ' : List Bool =>
      pairEncode x (pairEncode γ (pairEncode γ' (Nat.bits s))) ∈ stepLang N) (Nat.bits u) γ) :
    ∀ c, γ = Nat.bits c → Relation.ReflTransGen (StepRel N x s) u c := by
  induction h with
  | refl =>
    intro c hc
    rw [bits_injective hc]
  | tail _ hst ih =>
    intro c hc
    subst hc
    obtain ⟨x', c₁, c₂, s', heq, -⟩ := id hst
    obtain ⟨rfl, h2⟩ := pairEncode_inj heq
    obtain ⟨h3, h4⟩ := pairEncode_inj h2
    obtain ⟨h5, h6⟩ := pairEncode_inj h4
    have hc₂ := bits_injective h5
    have hs := bits_injective h6
    subst hc₂ hs
    refine (ih c₁ h3).tail ?_
    show pairEncode x (pairEncode (Nat.bits c₁) (pairEncode (Nat.bits c) (Nat.bits s))) ∈
      stepLang N
    rw [← h3]
    exact hst

/-- **Acceptance as a block path** ([AB09, Claim 4.4(1)] in the form of the proof of
Theorem 4.13): let `N` decide `L` in space `sp`, `s ≥ sp |x|`, blocks of width
`w ≥ codeLen |x| s`, and `configBound |x| s ≤ 2^w`. Then `x ∈ L` iff there are blocks `A`,
`B` of width `w`, `A` initial and `B` accepting (on their code-word prefixes), with
`Mid w (blockStep …) w A B`.

**Proof sketch.** `Complexity.TQBFHard.mid_iff_steps` turns `Mid` into a path of exactly `2^w`
steps. (⇒) The chain of codes of `Complexity.Codec.mem_iff_codeChain`, each padded to width
`w` (code words have length `codeLen`, `Complexity.Codec.length_cfgWord`), is a block path of
length `t ≤ configBound ≤ 2^w`, lengthened by reflexive steps (`steps_mono`). (⇐) The block
path is a path of code-word prefixes (`steps_reflTransGen`) from the initial code's word, and
every word along it is a code's word (`reflTransGen_stepRel`), ending at an accepting code;
conclude with `Complexity.Codec.mem_of_codePath`. -/
theorem mem_iff_mid {L : Language Bool} {sp : ℕ → ℕ} (h : N.DecidesInSpace L sp)
    (x : List Bool) (s w : ℕ) (hs : sp x.length ≤ s) (hw : codeLen N x.length s ≤ w)
    (hR : N.configBound x.length s ≤ 2 ^ w) :
    x ∈ L ↔ ∃ A B : List Bool, A.length = w ∧ B.length = w ∧
      blockInit N x s (codeLen N x.length s) A ∧ blockAcc N x s (codeLen N x.length s) B ∧
      Mid w (blockStep N x s (codeLen N x.length s)) w A B := by
  set Lc := codeLen N x.length s with hLc
  have hrefl : ∀ B : List Bool, blockStep N x s Lc B B := fun B => Or.inl rfl
  constructor
  · intro hx
    obtain ⟨t, c, ht, hinit, hstep, hacc, -⟩ := (mem_iff_codeChain h x s hs).mp hx
    -- every code of the chain has a code word of length `Lc`
    have hlen : ∀ i ≤ t, (Nat.bits (c i)).length = Lc := by
      intro i hi
      rcases i with _ | i
      · rw [mem_initLang] at hinit
        rw [← hinit, bits_cfgCode, length_cfgWord, hLc, codeLen]
      · obtain ⟨-, -, -, C', -, -, hC'⟩ := (mem_stepLang N x _ _ s).mp (hstep i (by omega))
        rw [← hC', bits_cfgCode, length_cfgWord, hLc, codeLen]
    let β : ℕ → List Bool := fun i => Nat.bits (c i) ++ List.replicate (w - Lc) false
    have hβlen : ∀ i ≤ t, (β i).length = w := by
      intro i hi
      simp only [β, List.length_append, List.length_replicate, hlen i hi]
      omega
    have hβtake : ∀ i ≤ t, (β i).take Lc = Nat.bits (c i) := by
      intro i hi
      simp only [β]
      rw [List.take_append_of_le_length (by rw [hlen i hi]), List.take_of_length_le
        (by rw [hlen i hi])]
    have hpath : ∀ k ≤ t, Steps w (blockStep N x s Lc) k (β 0) (β k) := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        refine ⟨β k, hβlen k (by omega), ih (by omega), Or.inr ?_⟩
        rw [hβtake k (by omega), hβtake (k + 1) hk]
        exact hstep k (by omega)
    refine ⟨β 0, β t, hβlen 0 (by omega), hβlen t le_rfl, ?_, ?_, ?_⟩
    · simp only [blockInit]
      rw [hβtake 0 (by omega)]
      exact hinit
    · simp only [blockAcc]
      rw [hβtake t le_rfl]
      exact hacc
    · rw [mid_iff_steps _ _ _ _ _ (hβlen 0 (by omega)) (hβlen t le_rfl)]
      exact steps_mono hrefl (ht.trans hR) (hβlen t le_rfl) (hpath t le_rfl)
  · rintro ⟨A, B, hA, hB, hinit, hacc, hmid⟩
    rw [mid_iff_steps _ _ _ _ _ hA hB] at hmid
    have hwords := steps_reflTransGen N x s Lc w _ A B hmid
    obtain ⟨x₁, u, s₁, h₁, hu⟩ := hinit
    obtain ⟨rfl, h₁'⟩ := pairEncode_inj h₁
    obtain ⟨hAu, hs₁⟩ := pairEncode_inj h₁'
    obtain rfl := bits_injective hs₁
    obtain ⟨x₂, v, s₂, h₂, hv⟩ := hacc
    obtain ⟨hx₂, h₂'⟩ := pairEncode_inj h₂
    obtain ⟨hBv, hs₂⟩ := pairEncode_inj h₂'
    obtain rfl := bits_injective hs₂
    subst hx₂
    rw [hAu] at hwords
    have hpath := reflTransGen_stepRel N x s u hwords v hBv
    refine mem_of_codePath h x s u v ((mem_initLang N x u s).mpr hu) hpath ?_
    exact (mem_acceptLang N x v s).mpr hv

end TQBFHard

end Complexity
