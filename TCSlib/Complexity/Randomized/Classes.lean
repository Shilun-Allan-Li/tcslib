/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The randomized complexity classes BPP, RP, coRP, ZPP

Verifier-style definitions of Arora–Barak's randomized complexity classes,
following the certificate view of [AB09, Def 7.4]: a language is in a
randomized class when some efficient two-input predicate `M(x, r)`, run on the
input `x` and a uniformly random string `r` of polynomially-bounded length,
decides membership with the class's acceptance-probability profile.

## Main definitions

* `Randomized.randProb` — the probability of an event over a uniform random
  string of a given length, as a rational counting ratio.
* `Randomized.polyLen` — the canonical polynomial length schedule
  `n ↦ a·(n+1)^k` for random strings.
* `Randomized.VerifierModel` — an abstract *efficiency notion* standing in for
  "polynomial-time Turing machine" (see **Deviations** below).
* `Randomized.InBPP` — [AB09, Def 7.4] (equivalently Def 7.1 via the
  certificate view).
* `Randomized.InRP`, `Randomized.InCoRP` — [AB09, Def 7.6] and the remark
  following it.
* `Randomized.InZPP` — [AB09, Def 7.7], in the zero-error "abort"
  formulation (see **Deviations**).
* `Randomized.raceVerifier`, `Randomized.majorityVerifier` — the two verifier
  constructions used by Theorems 7.8 and 7.10.

## Main results (sorry-stubbed)

* `Randomized.inZPP_iff_inRP_and_inCoRP` — `ZPP = RP ∩ coRP` [AB09, Thm 7.8].
* `Randomized.InBPP.compl` — `BPP = coBPP` (used by [AB09, Thm 7.18]).
* `Randomized.bpp_error_reduction` — error reduction [AB09, Thm 7.10].
* `Randomized.inBPPWeak_iff_inBPP` — `BPP_{n^{-c}} = BPP` [AB09, Lem 7.9].

## Deviations from the source

* **Machine model.** [AB09] defines these classes with polynomial-time Turing
  machines.  Per the repository's agreed scope, we use the certificate view of
  [AB09, Def 7.4] — predicates over inputs and random strings — and replace
  "`M` is a polynomial-time TM" by membership in an abstract
  `VerifierModel` `E`, a predicate on verifiers.  Every class and theorem is
  parametrized by `E`.  The closure properties that [AB09]'s proofs use
  (building the race, majority, complement, and projection verifiers out of
  given ones) are stated as explicit named hypotheses (`ClosedUnder…`), all of
  which hold for the intended instantiation "computable in polynomial time".
  Intended instantiation targets, once a uniform-computability layer is
  available: the `P`/`PolyTime` development of the `complexity/arora-barak-ch1`
  branch, or Mathlib's `Turing.TM2ComputableInPolyTime`.
* **Length schedules.** [AB09, Def 7.4] draws `r ∈ {0,1}^{p(|x|)}` for a
  polynomial `p`.  We fix the canonical schedule `polyLen a k : n ↦ a·(n+1)^k`
  (existentially quantified over `a, k : ℕ`) rather than an arbitrary
  `p : ℕ → ℕ` with a polynomial bound: an arbitrary bounded `p` need not be
  computable and could smuggle undecidable information through the schedule
  itself.  Every polynomial is dominated by some `polyLen a k`, and a verifier
  can ignore padding bits, so the class is unchanged.
* **Probability.** `Pr_{r ∈ {0,1}^m}` is the counting ratio
  `#{r : accepted}/2^m` valued in `ℚ`; random strings of length `m` are
  `Fin m → Bool`, passed to verifiers as lists via `List.ofFn`.
* **ZPP.** [AB09, Def 7.7] defines `ZPP` by expected running time of a
  zero-error machine.  Expected time is not expressible for abstract
  predicates, so we use the standard equivalent "Las Vegas" formulation: a
  verifier with values in `Option Bool` that is never wrong and outputs `none`
  ("don't know") with probability at most `1/2`.  [AB09, §7.4.2] sketches the
  equivalence of expected-time and worst-case formulations (truncation via
  Markov's inequality).
* **The weak threshold of Lemma 7.9.** The book's success threshold
  `1/2 + |x|^{-c}` exceeds `1` for `|x| ≤ 1`, making the literal class
  `BPP_{n^{-c}}` empty; we require advantage `min (1/6) ((|x|+1)^{-c})`
  instead, which for `c ≥ 1` agrees with the book's (up to the `n+1` shift) for
  `|x| ≥ 5` and makes `BPP ⊆ BPP_{n^{-c}}` hold as the book intends.
* The constant `2/3` follows [AB09, Defs 7.1/7.6]; `1/2` in `InZPP` is the
  conventional choice (any constant in `(0,1)` gives the same class, by the
  same repetition argument as [AB09, §7.4.1]).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset

/-- The probability, over a uniformly random string `r ∈ {0,1}^m`, that the
event `A` holds of `r` (as a list): the counting ratio `#{r : A r}/2^m`.
[AB09, Def 7.4: "`Pr_{r ∈_R {0,1}^{p(|x|)}}`"] -/
def randProb (m : ℕ) (A : List Bool → Prop) [DecidablePred A] : ℚ :=
  ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ) / 2 ^ m

/-- Two events that agree on every random string have the same
probability. -/
theorem randProb_congr {m : ℕ} {A B : List Bool → Prop} [DecidablePred A]
    [DecidablePred B]
    (h : ∀ r : Fin m → Bool, A (List.ofFn r) ↔ B (List.ofFn r)) :
    randProb m A = randProb m B := by
  unfold randProb
  rw [Finset.filter_congr fun r _ => h r]

/-- The canonical polynomial length schedule `n ↦ a·(n+1)^k` for random
strings — a concrete, computable stand-in for [AB09, Def 7.4]'s "polynomial
`p`" (see the module docstring's **Deviations**: an arbitrary polynomially
*bounded* `ℕ → ℕ` need not be computable and would let the schedule itself
decide undecidable languages). -/
def polyLen (a k : ℕ) : ℕ → ℕ := fun n => a * (n + 1) ^ k

/-- An abstract *efficiency notion* for verifiers, standing in for
"polynomial-time Turing machine" in [AB09, Def 7.4] (see the module
docstring's **Deviations**).  `Eff M` reads "`M` is an efficient verifier";
verifiers are `Option Bool`-valued so that zero-error ("don't know") verifiers
and ordinary Boolean verifiers share one notion.  `EffTwoWitness N` is the
corresponding notion for predicates of an input and two witness strings, the
verifier format of `Σ₂`-statements (used by [AB09, Thm 7.18]).  Intended
instantiations: a polynomial-time TM layer (the `complexity/arora-barak-ch1`
branch's `PolyTime`, or Mathlib's `Turing.TM2ComputableInPolyTime`). -/
structure VerifierModel where
  /-- "`M` is an efficient (poly-time) verifier." -/
  Eff : (List Bool → List Bool → Option Bool) → Prop
  /-- "`N` is an efficient (poly-time) two-witness predicate." -/
  EffTwoWitness : (List Bool → List Bool → List Bool → Bool) → Prop

/-- A Boolean verifier, viewed as an `Option Bool`-valued one. -/
def boolVerifier (M : List Bool → List Bool → Bool) :
    List Bool → List Bool → Option Bool :=
  fun x r => some (M x r)

variable (E : VerifierModel)

/-- `L ∈ BPP`: some efficient verifier `M` with polynomially-long randomness
decides `L` with two-sided error at most `1/3` — for every input `x`,
`Pr_{r ∈ {0,1}^{p(|x|)}}[M(x,r) = L(x)] ≥ 2/3`, where `p = polyLen a k`.
[AB09, Def 7.4] (the certificate form of [AB09, Def 7.1]). -/
def InBPP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false)

/-- `L ∈ RP`: one-sided error — inputs in `L` are accepted with probability
at least `2/3`, inputs outside `L` are *never* accepted.  [AB09, Def 7.6] -/
def InRP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) = false)

/-- `L ∈ coRP` iff its complement is in `RP`: one-sided error in the other
direction.  [AB09, §7.3: "`coRP = {L | L̄ ∈ RP}`"] -/
def InCoRP (L : Language Bool) : Prop :=
  InRP E Lᶜ

/-- `L ∈ ZPP`: some efficient zero-error verifier decides `L` — it may output
`none` ("don't know") with probability at most `1/2`, but whenever it outputs
an answer, the answer is correct.  [AB09, Def 7.7], in the equivalent
Las Vegas formulation (see the module docstring's **Deviations**). -/
def InZPP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Option Bool) (a k : ℕ),
    E.Eff M ∧
    ∀ x : List Bool,
      (x ∈ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some false) ∧
      (x ∉ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some true) ∧
      randProb (polyLen a k x.length) (fun r => M x r = none) ≤ 1/2

section Constructions

/-- The *race* of an `RP` verifier for `L` and an `RP` verifier for `Lᶜ` on
split randomness: on `r = r₁ ++ r₂`, answer `some true` if `M₁` accepts `r₁`,
else `some false` if `M₂` accepts `r₂`, else `none`.  The construction behind
`RP ∩ coRP ⊆ ZPP` in [AB09, Thm 7.8]. -/
def raceVerifier (M₁ M₂ : List Bool → List Bool → Bool) (p₁ : ℕ → ℕ) :
    List Bool → List Bool → Option Bool := fun x r =>
  if M₁ x (r.take (p₁ x.length)) then some true
  else if M₂ x (r.drop (p₁ x.length)) then some false
  else none

/-- The `k`-fold repetition of a verifier with majority vote, on randomness
split into `k` blocks of length `p(|x|)`: the construction behind error
reduction [AB09, Thm 7.10]. -/
def majorityVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → Bool := fun x r =>
  let n := x.length
  let votes := (List.range (k n)).countP fun i =>
    M x ((r.drop (i * p n)).take (p n))
  k n < 2 * votes

/-- `E` can race two of its Boolean verifiers on a polynomial split point
(closure of polynomial time under running two machines on split
randomness). -/
def ClosedUnderRace : Prop :=
  ∀ M₁ M₂ a k, E.Eff (boolVerifier M₁) → E.Eff (boolVerifier M₂) →
    E.Eff (raceVerifier M₁ M₂ (polyLen a k))

/-- `E` can turn a zero-error verifier into the Boolean verifier answering
"did it output `some b`?" (closure of polynomial time under postprocessing
the output). -/
def ClosedUnderAnswerIs : Prop :=
  ∀ M b, E.Eff M →
    E.Eff (boolVerifier fun x r => M x r = some b)

/-- The `k`-fold repetition of a verifier accepting if *any* repetition
accepts, on randomness split into `k` blocks of length `p(|x|)`: the
one-sided amplifier (an `OR`, not a majority — a strict majority cannot
amplify success probability exactly `1/2`, whereas for one-sided error the
`OR` drives the failure probability to `(1/2)^k` without hurting
soundness).  Used by [AB09, Thm 7.8]'s `ZPP ⊆ RP` direction. -/
def anyVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → Bool := fun x r =>
  (List.range (k x.length)).any fun i =>
    M x ((r.drop (i * p x.length)).take (p x.length))

/-- `E` can repeat a Boolean verifier a polynomial number of times, on blocks
of polynomial length, and take the majority (closure of polynomial time under
polynomial repetition). -/
def ClosedUnderMajority : Prop :=
  ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.Eff (boolVerifier (majorityVerifier M (polyLen a k) (polyLen a' k')))

/-- `E` can repeat a Boolean verifier a polynomial number of times, on blocks
of polynomial length, and accept if any repetition accepts (closure of
polynomial time under polynomial repetition with an `OR`). -/
def ClosedUnderAny : Prop :=
  ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.Eff (boolVerifier (anyVerifier M (polyLen a k) (polyLen a' k')))

/-- `E` can negate a Boolean verifier's answer (closure of polynomial time
under complementation of the output). -/
def ClosedUnderNot : Prop :=
  ∀ M, E.Eff (boolVerifier M) →
    E.Eff (boolVerifier fun x r => !(M x r))

end Constructions

/-- `BPP` is closed under complementation (`BPP = coBPP`): swap the two
acceptance clauses and negate the verifier's answer.  Used by
[AB09, Thm 7.18]'s proof ("it is enough to prove `BPP ⊆ Σ₂ᵖ` because `BPP`
is closed under complementation").

**Proof sketch.** If `M` decides `L` with two-sided error `1/3`, then
`¬M` decides `Lᶜ` with the same error: the `x ∈ Lᶜ` clause for `¬M` is the
`x ∉ L` clause for `M` and vice versa, since
`¬M x r = true ↔ M x r = false`. -/
theorem InBPP.compl (hNot : ClosedUnderNot E) {L : Language Bool}
    (hL : InBPP E L) : InBPP E Lᶜ := by
  obtain ⟨M, a, k, hM, hacc⟩ := hL
  refine ⟨fun x r => !(M x r), a, k, hNot M hM, fun x => ?_⟩
  constructor
  · intro hx
    calc (2/3 : ℚ)
        ≤ randProb (polyLen a k x.length) fun r => M x r = false :=
          (hacc x).2 hx
      _ = randProb (polyLen a k x.length) fun r => (!(M x r)) = true :=
          randProb_congr fun r => by simp
  · intro hx
    calc (2/3 : ℚ)
        ≤ randProb (polyLen a k x.length) fun r => M x r = true :=
          (hacc x).1 (Set.not_notMem.mp hx)
      _ = randProb (polyLen a k x.length) fun r => (!(M x r)) = false :=
          randProb_congr fun r => by simp

/-- **`ZPP = RP ∩ coRP`** ([AB09, Thm 7.8]).  Stated relative to the
efficiency notion `E`, under the closure properties the two directions use.

**Proof sketch.** (⊆) A zero-error verifier yields an `RP` verifier by
answering `true` exactly on output `some true` (`hAns`): inputs outside `L`
are never accepted (zero error), and inputs in `L` are accepted whenever the
verifier does not abort, hence with probability at least `1/2`.  Amplify
`1/2` to `2/3` with a 2-fold `OR` (`anyVerifier`, `hAny`): soundness is
preserved (an `OR` of never-accepting runs never accepts) and the failure
probability drops to `(1/2)² = 1/4`, so success is `≥ 3/4 ≥ 2/3`.  (A strict
*majority* cannot amplify success probability exactly `1/2`, which is why
the one-sided `OR` closure is the right tool here.)  Symmetrically with
`some false` for `Lᶜ`, giving `coRP`.  (⊇) Race an `RP` verifier `M₁` for
`L` against an `RP` verifier `M₂` for `Lᶜ` on split randomness
(`raceVerifier`): a definite answer is never wrong, since `M₁` accepting
certifies `x ∈ L` and `M₂` accepting certifies `x ∉ L`; and whichever of the
two is the "live" verifier for `x` accepts with probability ≥ `2/3`, so the
race aborts with probability at most `1/3 ≤ 1/2`. -/
theorem inZPP_iff_inRP_and_inCoRP (hRace : ClosedUnderRace E)
    (hAns : ClosedUnderAnswerIs E) (hAny : ClosedUnderAny E)
    (L : Language Bool) :
    InZPP E L ↔ InRP E L ∧ InCoRP E L := by
  sorry

/-- The advantage demanded of a weak `BPP` verifier on inputs of length `n`:
`min (1/6) ((n+1)^{-c})`.  For `c ≥ 1` and `n ≥ 5` this is the book's
`n^{-c}` up to the `n+1` shift (for `c = 0` both the book's `n^{-c}` and
`(n+1)^{-c}` are the constant `1`, and the cap takes over); the cap `1/6`
keeps the threshold `1/2 + weakAdv c n ≤ 2/3` attainable at small lengths,
where the book's literal `1/2 + n^{-c}` exceeds `1` (see the module
docstring's **Deviations**). -/
def weakAdv (c n : ℕ) : ℚ :=
  min (1/6) (((n : ℚ) + 1)⁻¹ ^ c)

/-- `L ∈ BPP_{n^{-c}}`: like `InBPP`, but with success probability only
`1/2 + weakAdv c |x|`, i.e. an inverse-polynomial advantage over guessing.
[AB09, Lem 7.9], with the small-length repair described in the module
docstring. -/
def InBPPWeak (c : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 1/2 + weakAdv c x.length ≤
        randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 1/2 + weakAdv c x.length ≤
        randProb (polyLen a k x.length) fun r => M x r = false)

/-- `L ∈ BPP` with error at most `2^{-((|x|+1)^d + 1)}` — the amplified form
produced by error reduction.  The exponent `(|x|+1)^d + 1 ≥ |x|^d`
strengthens [AB09, Thm 7.10]'s `2^{-|x|^d}` uniformly in `|x|`, and the
`+ 1` keeps the success threshold at least `3/4 > 2/3` at *every* length
and every `d` (including `d = 0` and the empty input), so
`InBPPStrong E d L → InBPP E L` follows directly using the same witnesses
(via the arithmetic inequality `2/3 ≤ 1 − (1/2)^{(n+1)^d + 1}`), with no closure
assumption on `E`.  (With the bare exponent `(|x|+1)^d`, a fair coin would
satisfy the definition at `d = 0` for every language, and at `|x| = 0` for
every `d` — a finite exception that cannot be patched for an abstract
model.) -/
def InBPPStrong (d : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤
        randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤
        randProb (polyLen a k x.length) fun r => M x r = false)

/-- **Error reduction** ([AB09, Thm 7.10]).  A language decidable with an
inverse-polynomial advantage is decidable with success probability
`1 − 2^{-((|x|+1)^d + 1)}`, for every constant `d` — relative to `E`,
assuming `E` is closed under polynomial majority repetition.

**Proof sketch.** Run the weak verifier `k(n) = 26·(n+1)^{2c+d}` times on
independent blocks of randomness and take the majority
(`majorityVerifier`).  The votes are i.i.d. Bernoulli with success
probability `p ≥ 1/2 + ε` where `ε = weakAdv c n ≥ (n+1)^{-c}/6`, so by
Hoeffding's inequality (`Randomized.majority_error_le` in
`Randomized.ErrorReduction`, transported from the product measure to the
counting probability `randProb`) the majority errs with probability at most
`e^{−2ε²k} ≤ e^{−26(n+1)^d/18} ≤ 2^{-((n+1)^d + 1)}`. -/
theorem bpp_error_reduction (hMaj : ClosedUnderMajority E) {c : ℕ}
    {L : Language Bool} (hL : InBPPWeak E c L) (d : ℕ) :
    InBPPStrong E d L := by
  sorry

/-- **`BPP_{n^{-c}} = BPP`** ([AB09, Lem 7.9]): the success threshold `2/3`
in the definition of `BPP` can be weakened to an inverse-polynomial advantage
over `1/2` without changing the class.

**Proof sketch.** `BPP ⊆ BPP_{n^{-c}}` since `weakAdv c n ≤ 1/6` makes the
weak threshold at most `2/3` at every length.  Conversely, from advantage
`ε = weakAdv c n ≥ (n+1)^{-c}/6`, run the weak verifier
`k(n) = 324·(n+1)^{2c}` times and take the majority: by Hoeffding
(`majority_error_le`), the majority errs with probability at most
`e^{−2ε²k} ≤ e^{-9/2} ≤ 1/3`. -/
theorem inBPPWeak_iff_inBPP (hMaj : ClosedUnderMajority E) (c : ℕ)
    (L : Language Bool) :
    InBPPWeak E c L ↔ InBPP E L := by
  sorry

end Randomized
