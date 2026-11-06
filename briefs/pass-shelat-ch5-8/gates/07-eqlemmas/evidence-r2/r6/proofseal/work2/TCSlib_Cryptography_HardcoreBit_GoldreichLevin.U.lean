/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.HardcoreBit.InnerProduct
import TCSlib.Cryptography.HardcoreBit.PairwiseIndependence

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Goldreich–Levin: the general case (prediction at least `1/2 + ε`)

[Gar26, Theorem 2.3, real case]: if `A` predicts `⟨x, r⟩` from `f(x) ‖ r` with
probability at least `1/2 + ε`, the inverter of [Gar26, Figure 2.5] inverts
`g(x, r) = f(x) ‖ r`. It samples `k` strings `s_ℓ` and guesses `k` bits `b_ℓ` (meant to
be `⟨x, s_ℓ⟩`); for each bit `i` and each nonempty `L ⊆ [k]` it forms the trial
`B_L ⊕ A(f(x) ‖ S_L ⊕ eᵢ)` with `S_L = ⊕_{j ∈ L} s_j`, `B_L = ⊕_{j ∈ L} b_j`, and
takes the majority over `L`. All guesses are right with probability `2^{-k}`, and then
the trials are pairwise independent, so Chebyshev applies.

Deviations from the source.
* The source ranges over all `L ⊆ [log T]`, including `L = ∅`, where `S_∅ = 0` is not
  uniform and the trial `A(f(x) ‖ eᵢ)` has no guaranteed success probability. Only the
  `2^k - 1` nonempty subsets are used.
* `k` (the source's `log T`) is an explicit natural number with the hypothesis
  `2 n ≤ ε² (2^k - 1)`, the role of `T = 2n / ε²`; the bound is `ε / (4 · 2^k)` in place
  of `(1/T) · (ε/2) · (1/2) = ε³/(8n)`. With `2^k ≤ 4n/ε²`, which a minimal `k` satisfies
  up to the rounding of `2n/ε² + 1` to a power of two, this is at least `ε³/(16 n)`
  (`invProb_guessInverter_cubic`).
* Each call to `A` uses fresh coins; independence across calls is part of the analysis.

## Main definitions

* `NESubset k`: the nonempty subsets of `Fin k`.
* `guessRecover A k`, `guessInverter A k`: the inverter of [Gar26, Figure 2.5].
* `idealRecover f A x`: the same procedure run with the correct guesses.

## Main results

* `guessRecover_correct_guess`: with correct guesses, `B_L = ⟨x, S_L⟩`.
* `uprob_idealRecover_ne_le`: for a good `x`, each majority is wrong with probability at
  most `1 / (ε² (2^k - 1))`.
* `invProb_guessInverter`: [Gar26, Theorem 2.3, real case].

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5.1, Theorem 2.3 (real case) and Figure 2.5.
-/

namespace TCSlib.Cryptography.HardcoreBit

open Finset TCSlib.Cryptography

variable {n : ℕ} {β ρ : Type*} [Fintype ρ]

/-- The nonempty subsets `L` of `[k] = Fin k`, which index the trials of
[Gar26, Figure 2.5] (the source also uses `L = ∅`; see the module docstring). -/
abbrev NESubset (k : ℕ) : Type := {L : Finset (Fin k) // L.Nonempty}

/-- The coins of the inverter of [Gar26, Figure 2.5]: `k` strings `s_ℓ`, `k` guessed bits
`b_ℓ`, and a fresh coin string of `A` for each bit `i` and each nonempty `L`. -/
abbrev GuessCoins (n k : ℕ) (ρ : Type*) : Type _ :=
  (Fin k → Fin n → Bool) × (Fin k → Bool) × (Fin n → NESubset k → ρ)

/-- The recovery procedure of [Gar26, Figure 2.5]: bit `i` is the majority over nonempty
`L ⊆ [k]` of `B_L ⊕ A(y ‖ S_L ⊕ eᵢ)`, with `S_L = ⊕_{j ∈ L} s_j` and
`B_L = ⊕_{j ∈ L} b_j`. In total it makes `n (2^k - 1)` calls to `A`, samples `k` strings
of `n` bits, `k` bits and `n (2^k - 1)` coin strings, and computes the `2^k - 1` subset
XORs of strings and of bits, `n (2^k - 1)` further string and bit XORs, and `n`
majorities of `2^k - 1` bits. -/
def guessRecover (A : β × (Fin n → Bool) → ρ → Bool) (k : ℕ) (y : β)
    (c : GuessCoins n k ρ) : Fin n → Bool :=
  fun i => majority fun L : NESubset k =>
    subsetSum L.1 c.2.1 + A (y, subsetSum L.1 c.1 + Pi.single i true) (c.2.2 i L)

/-- The inverter of [Gar26, Figure 2.5]: on `f(x) ‖ r` it outputs
`guessRecover A k (f(x)) ‖ r`. -/
def guessInverter (A : β × (Fin n → Bool) → ρ → Bool) (k : ℕ) :
    β × (Fin n → Bool) → GuessCoins n k ρ → (Fin n → Bool) × (Fin n → Bool) :=
  glInverter (guessRecover A k)

/-- The defining equation of `guessInverter`:
`guessInverter A k = glInverter (guessRecover A k)`. -/
theorem guessInverter_eq (A : β × (Fin n → Bool) → ρ → Bool) (k : ℕ) :
    guessInverter A k = glInverter (guessRecover A k) := rfl

/-- The recovery procedure of [Gar26, Figure 2.5] for a known `x`, run with the correct
guesses `b_ℓ = ⟨x, s_ℓ⟩`: bit `i` is the majority over `L` of
`⟨x, S_L⟩ ⊕ A(f(x) ‖ S_L ⊕ eᵢ)`. An analysis device, not an algorithm. -/
def idealRecover (f : (Fin n → Bool) → β) (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ}
    (x : Fin n → Bool) (s : Fin k → Fin n → Bool) (cs : Fin n → NESubset k → ρ) :
    Fin n → Bool :=
  fun i => majority fun L : NESubset k =>
    ip x (subsetSum L.1 s) + A (f x, subsetSum L.1 s + Pi.single i true) (cs i L)

omit [Fintype ρ] in
/-- With the correct guesses `b_ℓ = ⟨x, s_ℓ⟩`, the guessed bits `B_L` equal `⟨x, S_L⟩`,
so the recovery procedure is `idealRecover`. [Gar26, §2.5.1, real case], the
computation `B(x, S_L) = B_L` under the event `F`. -/
theorem guessRecover_correct_guess (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} (x : Fin n → Bool)
    (s : Fin k → Fin n → Bool) (cs : Fin n → NESubset k → ρ) :
    guessRecover A k (f x) (s, fun ℓ => ip x (s ℓ), cs) = idealRecover f A x s cs := by
  funext i
  simp only [guessRecover, idealRecover, subsetSum, ip_sum]

/-- For a good `x` (`secProb f A x ≥ 1/2 + ε/2`), each trial of the ideal procedure,
`⟨x, a⟩ ⊕ A(f(x) ‖ a ⊕ eᵢ)` for uniform `a` and coins, is right with probability at
least `1/2 + ε/2`. [Gar26, §2.5.1, real case].

**Proof sketch.** The trial equals `xᵢ` exactly when `A` is right on the query
`a ⊕ eᵢ`, since `⟨x, a ⊕ eᵢ⟩ = ⟨x, a⟩ ⊕ xᵢ`; and `a ⊕ eᵢ` is uniform. -/
theorem idealTrial_correct (f : (Fin n → Bool) → β) (A : β × (Fin n → Bool) → ρ → Bool)
    (x : Fin n → Bool) (i : Fin n) :
    uprob (fun z : (Fin n → Bool) × ρ =>
      ip x z.1 + A (f x, z.1 + Pi.single i true) z.2 = x i) = secProb f A x := by
  have hev : (fun z : (Fin n → Bool) × ρ =>
      ip x z.1 + A (f x, z.1 + Pi.single i true) z.2 = x i) =
      fun z => A (f x, z.1 + Pi.single i true) z.2 = ip x (z.1 + Pi.single i true) := by
    funext z
    rw [ip_add, ip_single]
    apply propext
    cases A (f x, z.1 + Pi.single i true) z.2 <;> cases ip x z.1 <;> cases x i <;> decide
  rw [hev]
  exact ((pushesUniform_xor (Pi.single i true)).prodMap
    (pushesUniform_id (Ω := ρ))).uprob_eq
    (fun z : (Fin n → Bool) × ρ => A (f x, z.1) z.2 = ip x z.1)

/-- For a good `x` (`secProb f A x ≥ 1/2 + ε/2`, `ε > 0`) and `k ≥ 1`, each majority of
the ideal procedure is wrong with probability at most `1 / (ε² (2^k - 1))`.
[Gar26, §2.5.1, real case], the bound `Pr[x'ᵢ ≠ xᵢ] ≤ 1/(4 (ε/2)² T)`.

**Proof sketch.** The trial for `L` is a function of `(S_L, cs i L)`. The subset sums over
nonempty `L` are pairwise uniform, and so are the coin strings `cs i L`; so the pairs are
pairwise uniform and the trials pairwise independent, each right with probability at
least `1/2 + ε/2`. Chebyshev over the `2^k - 1` trials with `δ = ε/2` gives the bound. -/
theorem uprob_idealRecover_ne_le [Nonempty ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} (hk : 0 < k) (x : Fin n → Bool)
    (i : Fin n) {ε : ℝ} (hε : 0 < ε) (hx : 1 / 2 + ε / 2 ≤ secProb f A x) :
    uprob (fun ω : (Fin k → Fin n → Bool) × (Fin n → NESubset k → ρ) =>
      idealRecover f A x ω.1 ω.2 i ≠ x i) ≤ 1 / (ε ^ 2 * ((2 : ℝ) ^ k - 1)) := by
  have hpu : PairwiseUniform (fun (L : NESubset k)
      (ω : (Fin k → Fin n → Bool) × (Fin n → NESubset k → ρ)) =>
      (subsetSum L.1 ω.1, ω.2 i L)) :=
    (pairwiseUniform_subsetSum (κ := Fin k) (G := Fin n → Bool)).prod
      ((pairwiseUniform_eval (ι := NESubset k) (γ := ρ)).comp_right (pushesUniform_eval i))
  let H : NESubset k → (Fin n → Bool) × ρ → Bool := fun _ z =>
    decide (ip x z.1 + A (f x, z.1 + Pi.single i true) z.2 = x i)
  have hY := hpu.pairwiseIndep H
  have hp : ∀ L : NESubset k, 1 / 2 + ε / 2 ≤
      uprob (fun ω : (Fin k → Fin n → Bool) × (Fin n → NESubset k → ρ) =>
        H L (subsetSum L.1 ω.1, ω.2 i L) = true) := by
    intro L
    rw [(hpu.marginal L).uprob_eq (fun z => H L z = true)]
    simpa only [H, decide_eq_true_eq, idealTrial_correct] using hx
  have hcard : Fintype.card (NESubset k) = 2 ^ k - 1 := by
    rw [card_nonempty_finset, Fintype.card_fin]
  have hm : 0 < Fintype.card (NESubset k) := by
    rw [hcard]
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hb := uprob_majority_fails_le hY (half_pos hε) hm hp
  have hcardR : (Fintype.card (NESubset k) : ℝ) = (2 : ℝ) ^ k - 1 := by
    rw [hcard, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hconst : 4 * (ε / 2) ^ 2 * (Fintype.card (NESubset k) : ℝ) =
      ε ^ 2 * ((2 : ℝ) ^ k - 1) := by
    rw [hcardR]; ring
  rw [hconst] at hb
  refine le_trans (uprob_mono fun ω hω => ?_) hb
  have := two_mul_card_le_of_majority_ne _ _ hω
  simpa only [H, decide_eq_true_eq] using this

/-- A uniform tuple of `k` bits equals a fixed one with probability `2^{-k}`: all `k`
guesses are right with probability `1 / 2^k`. [Gar26, §2.5.1, real case], `Pr[F]`. -/
theorem uprob_guess_eq {k : ℕ} (b₀ : Fin k → Bool) :
    uprob (fun b : Fin k → Bool => b = b₀) = 1 / 2 ^ k := by
  classical
  rw [uprob_eq_card_filter, filter_eq' univ b₀]
  simp

/-- For a good `x`, the guessing procedure recovers `x` with probability at least `2^{-k}`
times the probability that the ideal procedure does. [Gar26, §2.5.1, real case], the
factor `Pr[F]` in the final bound.

**Proof sketch.** Restrict to the event that all guesses are right, `b = (⟨x, s_ℓ⟩)_ℓ`,
where the procedure is the ideal one. The guesses are independent of `s` and of the coins,
so for each `s` this event and ideal success multiply, giving `2^{-k}` times the ideal
success probability. -/
theorem uprob_guessRecover_ge (f : (Fin n → Bool) → β) (A : β × (Fin n → Bool) → ρ → Bool)
    {k : ℕ} (x : Fin n → Bool) :
    1 / 2 ^ k * uprob (fun ω : (Fin k → Fin n → Bool) × (Fin n → NESubset k → ρ) =>
        idealRecover f A x ω.1 ω.2 = x) ≤
      uprob (fun c : GuessCoins n k ρ => guessRecover A k (f x) c = x) := by
  have hmono : uprob (fun c : GuessCoins n k ρ =>
      c.2.1 = (fun ℓ => ip x (c.1 ℓ)) ∧ idealRecover f A x c.1 c.2.2 = x) ≤
      uprob (fun c : GuessCoins n k ρ => guessRecover A k (f x) c = x) := by
    refine uprob_mono fun c hc => ?_
    obtain ⟨s, b, cs⟩ := c
    obtain ⟨hb, hc⟩ := hc
    simp only at hb hc ⊢
    rw [hb, guessRecover_correct_guess]
    exact hc
  refine le_trans (le_of_eq ?_) hmono
  rw [uprob_prod (fun c : GuessCoins n k ρ =>
      c.2.1 = (fun ℓ => ip x (c.1 ℓ)) ∧ idealRecover f A x c.1 c.2.2 = x),
    uprob_prod (fun ω : (Fin k → Fin n → Bool) × (Fin n → NESubset k → ρ) =>
      idealRecover f A x ω.1 ω.2 = x), ← uexp_const_mul]
  congr 1
  funext s
  have h := uprob_prod_and (fun b : Fin k → Bool => b = fun ℓ => ip x (s ℓ))
    (fun cs : Fin n → NESubset k → ρ => idealRecover f A x s cs = x)
  simp only at h ⊢
  rw [h, uprob_guess_eq]

/-- The general case of Goldreich–Levin: if `A` predicts `B(x, r) = ⟨x, r⟩` from
`g(x, r) = f(x) ‖ r` with probability at least `1/2 + ε`, `ε > 0`, and the number `k` of
guessed bits satisfies `2 n ≤ ε² (2^k - 1)`, then `guessInverter A k` inverts `g` with
probability at least `ε / (4 · 2^k)`. [Gar26, Theorem 2.3, real case]; the source's
`log T` with `T = 2n/ε²` is the explicit `k`, the trials range over the `2^k - 1`
nonempty subsets, and the source's bound `ε³/(8n) = (1/T)(ε/2)(1/2)` becomes
`2^{-k} (ε/2)(1/2)`.

**Proof sketch.** The good set `G = {x | Pr_r[E] ≥ 1/2 + ε/2}` has probability at least
`ε/2`. For `x ∈ G`, each of the `n` ideal majorities is wrong with probability at most
`1/(ε² (2^k - 1)) ≤ 1/(2n)`, so the ideal procedure recovers `x` with probability at
least `1/2`; the guesses are all right with probability `2^{-k}`, independently. -/
theorem invProb_guessInverter [Nonempty ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hk : 2 * (n : ℝ) ≤ ε ^ 2 * ((2 : ℝ) ^ k - 1))
    (h : 1 / 2 + ε ≤ predProb (glPad f) glBit A) :
    ε / (4 * 2 ^ k) ≤ invProb (glPad f) (guessInverter A k) := by
  have hG := half_le_uprob_good f A (by norm_num) hε.le h
  have key := le_invProb_of_good f (guessRecover A k) hG
    (by positivity : (0 : ℝ) ≤ 1 / 2 ^ k * (1 / 2)) fun x hx => by
      refine le_trans ?_ (uprob_guessRecover_ge f A x)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine le_trans ?_ (one_sub_sum_le_uprob_eq
        (fun ω : (Fin k → Fin n → Bool) × (Fin n → NESubset k → ρ) =>
          idealRecover f A x ω.1 ω.2) x)
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; norm_num
      have hm : (0 : ℝ) < (2 : ℝ) ^ k - 1 := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith [sq_nonneg ε]
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; norm_num at hm
        · exact h0
      have hsum : ∑ i : Fin n, uprob (fun ω : (Fin k → Fin n → Bool) ×
          (Fin n → NESubset k → ρ) => idealRecover f A x ω.1 ω.2 i ≠ x i) ≤
          ∑ _i : Fin n, 1 / (ε ^ 2 * ((2 : ℝ) ^ k - 1)) :=
        sum_le_sum fun i _ => uprob_idealRecover_ne_le f A hk0 x i hε hx
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      have : (n : ℝ) * (1 / (ε ^ 2 * ((2 : ℝ) ^ k - 1))) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        linarith
      linarith
  unfold guessInverter
  refine le_trans (le_of_eq ?_) key
  field_simp
  ring

/-- The general case in the source's cubic form: under the hypotheses of
`invProb_guessInverter` and `ε² 2^k ≤ 4 n` (so `k` is within one of the source's
`log(2n/ε²)`), the inversion probability is at least `ε³/(16 n)`. [Gar26, Theorem 2.3,
real case], whose bound is `ε³/(8n)` with the unrounded `T = 2n/ε²`; the factor 2 is the
cost of rounding to a power of two and of dropping `L = ∅`. -/
theorem invProb_guessInverter_cubic [Nonempty ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hk : 2 * (n : ℝ) ≤ ε ^ 2 * ((2 : ℝ) ^ k - 1)) (hk' : ε ^ 2 * (2 : ℝ) ^ k ≤ 4 * n)
    (h : 1 / 2 + ε ≤ predProb (glPad f) glBit A) :
    ε ^ 3 / (16 * n) ≤ invProb (glPad f) (guessInverter A k) := by
  refine le_trans ?_ (invProb_guessInverter f A hε hk h)
  have hn : (0 : ℝ) < n := by
    by_contra hn
    push_neg at hn
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith [sq_nonneg ε, mul_pos hε hε]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hε hε]

end TCSlib.Cryptography.HardcoreBit


/- ===== gate 07 statement sweep: seal-candidate collector (appended to the statement-only copy) =====
Walks every constant declared in this file (the current module of the statement-only copy, in which
every theorem/lemma/example value is `sorry`): the TYPE of every constant (theorems, definitions,
instances, structures and their fields/constructors/recursors, auxiliaries), and the VALUE of every
definition/instance/abbreviation/opaque (theorem values are `sorry`, so proofs contribute nothing).
Every TCSlib constant declared in another module that occurs there is classified:
* `def` (a plain, non-instance, non-reducible, non-projection, non-auxiliary, non-private
  definition): a seal candidate. Its value and its type are walked further (`deep` tier).
* instance / `@[reducible]` (incl. `abbrev`) / private / auxiliary (matcher, `_unary`, …):
  transparent or unnameable, so not sealed; recorded, and their values and types are walked.
* any other constant (theorem, structure, inductive, constructor, projection, axiom, …): its TYPE is
  walked (using a constant can make the elaborator reduce its type), it is not sealed.
`direct` = occurs in this file's types/values; `deep` = reached only through a foreign constant.
Output: SWEEP_OUT.cands.tsv, SWEEP_OUT.uses.tsv, SWEEP_OUT.transparent.tsv -/
namespace SweepCollect
open Lean
def numSuffix (s pre : String) : Bool :=
  s.startsWith pre && (s.drop pre.length).length > 0 && (s.drop pre.length).all Char.isDigit
def isAuxComp (s : String) : Bool :=
  s.startsWith "_" || numSuffix s "match_" || numSuffix s "proof_" || numSuffix s "eq_" ||
    s == "eq_def" || s == "eq_unfold"
def isAuxName : Name → Bool
  | .str p s => isAuxComp s || isAuxName p
  | .num _ _ => true
  | .anonymous => false
end SweepCollect

open Lean Meta in
run_cmd do
  let env ← getEnv
  let outBase : String := "/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/final6/proofseal/work2/TCSlib_Cryptography_HardcoreBit_GoldreichLevin.coll"
  let modNames := env.header.moduleNames
  let isTCS (j : ModuleIdx) : Bool := (modNames[j.toNat]!).getRoot == `TCSlib
  let kindOf (n : Name) : String :=
    match env.find? n with
    | some (.defnInfo _) =>
      if isPrivateName n then "private"
      else if SweepCollect.isAuxName n || isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then "aux"
      else if env.isProjectionFn n then "proj"
      else if isInstanceCore env n then "instance"
      else if getReducibilityStatusCore env n == .reducible then "reducible"
      else if getReducibilityStatusCore env n == .irreducible then "irreducible"
      else "def"
    | some (.thmInfo _) => "thm"
    | some (.axiomInfo _) => "axiom"
    | some (.opaqueInfo _) => "opaque"
    | some (.inductInfo _) => "inductive"
    | some (.ctorInfo _) => "ctor"
    | some (.recInfo _) => "rec"
    | some (.quotInfo _) => "quot"
    | none => "none"
  -- local constants of this file
  let locals := env.constants.map₂.toList.filter fun (n, _) => !(n.components.contains `SweepCollect)
  -- candidate ↦ (tier, via set, owners)
  let mut cands : Std.HashMap Name (String × NameSet × NameSet) := {}
  let mut transp : Std.HashMap Name (String × NameSet) := {}
  let mut uses : Array String := #[]
  for (ln, ci) in locals do
    -- owner: strip auxiliary components / private prefix
    let owner := (privateToUserName? ln).getD ln
    let roots : Array (Name × String) :=
      (ci.type.getUsedConstantsAsSet.toArray.map (·, "T")) ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | _ => #[])
    -- worklist: (constant, region T/V, via (anonymous = direct))
    let mut work : Array (Name × String × Name) := roots.map fun (n, r) => (n, r, Name.anonymous)
    let mut seen : Std.HashSet (Name × String) := {}
    let mut found : Array String := #[]
    while !work.isEmpty do
      let (u, r, via) := work.back!
      work := work.pop
      if seen.contains (u, r) then continue
      seen := seen.insert (u, r)
      let some j := env.getModuleIdxFor? u | continue   -- local or unknown: locals are walked as roots
      unless isTCS j do continue
      let some cu := env.find? u | continue
      let k := kindOf u
      let via' := if via.isAnonymous then u else via
      if k == "def" then
        let tier := if via.isAnonymous then "direct" else "deep"
        let (t0, vs, os) := cands.getD u (tier, {}, {})
        let t1 := if t0 == "direct" || tier == "direct" then "direct" else "deep"
        cands := cands.insert u (t1, if via.isAnonymous then vs else vs.insert via, os.insert owner)
        if via.isAnonymous then found := found.push s!"{u}@{r}"
      else if k == "instance" || k == "reducible" || k == "private" || k == "aux" || k == "proj" then
        let (m0, os) := transp.getD u (k, {})
        transp := transp.insert u (m0, os.insert owner)
      -- walk further: the type always; the value of definitions (sealed or transparent)
      for v in cu.type.getUsedConstantsAsSet.toArray do
        unless seen.contains (v, r) do work := work.push (v, r, via')
      if let .defnInfo dv := cu then
        for v in dv.value.getUsedConstantsAsSet.toArray do
          unless seen.contains (v, r) do work := work.push (v, r, via')
    if !found.isEmpty then
      uses := uses.push s!"{owner}\t{ln}\t{" ".intercalate found.toList}"
  let mut cl : Array String := #[]
  for (n, (t, vs, os)) in cands.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    let vsT := ", ".intercalate ((vs.toArray.qsort Name.lt).toList.take 3 |>.map toString)
    cl := cl.push s!"{n}\t{modNames[j.toNat]!}\t{t}\t{vsT}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".cands.tsv") ("\n".intercalate cl.toList ++ "\n")
  IO.FS.writeFile (outBase ++ ".uses.tsv") ("\n".intercalate uses.toList ++ "\n")
  let mut tl : Array String := #[]
  for (n, (k, os)) in transp.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    tl := tl.push s!"{n}\t{k}\t{modNames[j.toNat]!}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".transparent.tsv") ("\n".intercalate tl.toList ++ "\n")
  -- own-file dependency graph (for the minimiser's cascade/masking rule): for every local constant,
  -- its declaration line and the declaration lines of the local constants its type/value mentions
  let lineOf (n : Name) : Lean.Elab.Command.CommandElabM Int := do
    let mut cur := n
    for _ in [0:8] do
      if let some r ← Lean.findDeclarationRanges? cur then return (r.range.pos.line : Int)
      if let some u := privateToUserName? cur then
        if let some r ← Lean.findDeclarationRanges? u then return (r.range.pos.line : Int)
      match cur with
      | .str p _ => cur := p
      | .num p _ => cur := p
      | .anonymous => return -1
    return -1
  let localSet : NameSet := locals.foldl (fun s (n, _) => s.insert n) {}
  let mut dl : Array String := #[]
  for (ln, ci) in locals do
    -- theorem values included: top-level theorem values are `sorry` here, but the auxiliary
    -- theorems `D.proof_N` abstracted from a definition's body carry that body's proofs
    let refs := ci.type.getUsedConstantsAsSet.toArray ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray
       | _ => #[])
    let mut ls : Array Int := #[]
    for v in refs do
      if localSet.contains v && v != ln then
        let l ← lineOf v
        unless ls.contains l do ls := ls.push l
    let l0 ← lineOf ln
    dl := dl.push s!"{l0}\t{ln}\t{" ".intercalate (ls.toList.map toString)}"
  IO.FS.writeFile (outBase ++ ".deps.tsv") ("\n".intercalate dl.toList ++ "\n")
