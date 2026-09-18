/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# EXP and NEXP

[AB09, Claim 2.4 and §2.6.2]: the exponential-time classes. `EXP` is
`⋃ c, DTIME (2^(n^c))` verbatim from Claim 2.4. `NEXP` is defined here in the
certificate form of [AB09, Exercise 2.27] — exponential-length certificates with
a polynomial-time verifier language — mirroring `Complexity.NP`; its equivalence
with the `NTIME` form of §2.6.2 is a phase-2 obligation, once nondeterministic
machines exist.

## Design and deviations from [AB09]

* `NEXP`'s verifier is a language `V ∈ P`: "polynomial time" is measured in the
  length of the padded string `x ++ u`, which is exponential in `|x|` — this is
  the standard certificate rendering and exactly Exercise 2.27's intent.
* The chain `P ⊆ NP ⊆ EXP ⊆ NEXP` [AB09, Claim 2.4 and §2.6.2] is stated as the
  three individual inclusions below (`P ⊆ NP` lives in `ClassNP/NP.lean`).

## Main definitions

* `Complexity.EXP` — [AB09, Claim 2.4].
* `Complexity.ExpBound`, `Complexity.NEXP` — [AB09, §2.6.2, in the form of
  Exercise 2.27].

## Main results

* `Complexity.P_subset_EXP` — [AB09, Claim 2.4].
* `Complexity.NP_subset_EXP` — certificate enumeration [AB09, Claim 2.4].
* `Complexity.EXP_subset_NEXP` — [AB09, §2.6.2].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 2.4, p. 41; §2.6.2, pp. 56-57;
  Exercise 2.27.)
-/

namespace Complexity

/-- **The class EXP** [AB09, Claim 2.4]: languages decidable in time `2^(n^c)`
for some constant `c` (up to `DTIME`'s constant-factor slack). -/
def EXP : Set (Language Bool) :=
  ⋃ c : ℕ, DTIME fun n => 2 ^ n ^ c

/-- The bound `p : ℕ → ℕ` is *exponentially bounded*: `p n ≤ C · 2^((n+1)^c)` for
some constants — the certificate-length regime of `NEXP`. -/
def ExpBound (p : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ n, p n ≤ C * 2 ^ (n + 1) ^ c

/-- **The class NEXP**, in the certificate form of [AB09, Exercise 2.27]:
exponential-length certificates with a verifier language decidable in time
polynomial in the padded string `x ++ u`. The `NTIME` form of [AB09, §2.6.2] and
its equivalence with this one are phase-2 obligations. -/
def NEXP : Set (Language Bool) :=
  {L | ∃ (p : ℕ → ℕ) (V : Language Bool), ExpBound p ∧ V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔ ∃ u : List Bool, u.length = p x.length ∧ x ++ u ∈ V}

/-- **`P ⊆ EXP`** [AB09, Claim 2.4].

**Proof sketch.** `n^c + 1 ≤ 2 · 2^(n^c)` for every `n` (as `n^c < 2^(n^c)`), so
each `DTIME (n^c + 1)` sits inside `DTIME (2 · 2^(n^c)) ⊆ EXP` by
`Complexity.DTIME.mono` and the constant-absorbing `Complexity.DTIME`
definition. -/
theorem P_subset_EXP : P ⊆ EXP := by
  sorry

/-- **`NP ⊆ EXP`** [AB09, Claim 2.4]: brute-force certificate enumeration.

**Proof sketch.** Let `L ∈ NP` with certificate length `p` (bounded by the
monotone majorant `C (n+1)^c`) and verifier `V ∈ P` decided by machine `MV`.
The deciding machine, on input `x` of length `n`: maintain a candidate
certificate `u` on a work tape as a binary counter of width `p n` (initialized to
all-`false`; width computed by the polynomial-counting machinery of
`Complexity.counterTM`); in each round, copy `x ++ u` to a buffer and run `MV` on
it via the guarded composition `Turing.FinTM.exists_comp_partial` and the branch
combinator `Turing.FinTM.exists_cond`; accept if `MV` accepts, else increment `u`
(`Complexity.counterInc`) and repeat, rejecting after the `2^(p n)`-th round.
There are at most `2^(p n) ≤ 2^(C (n+1)^c)` rounds, each costing polynomially
many steps in `n + p n`, so the total is `2^(n^{c'})`-bounded for a suitable
`c'`: `L ∈ EXP`. The construction is a bounded-search sibling of the epoch-1
combinator assemblies; its cost ledger is the fill's main obligation. -/
theorem NP_subset_EXP : NP ⊆ EXP := by
  sorry

/-- **`EXP ⊆ NEXP`** [AB09, §2.6.2].

**Proof sketch.** Given `L ∈ EXP` decided in time `2^(n^c)`, take the certificate
length `p n = 2^((n+1)^c)` (an `ExpBound`, strictly monotone in `n`) and the
verifier `V = {x ++ u : x ∈ L, |u| = p |x|}`. `V ∈ P`: on a string `y`, recover
the unique `n` with `n + p n = |y|` by scanning `n ≤ |y|` (strict monotonicity of
`n + p n`; each evaluation of `p` is a binary power computable in time polynomial
in `|y|`), split off `x`, and run `L`'s `2^(n^c)`-time decider — polynomial in
`|y| ≥ p n = 2^((n+1)^c)`. Certificates carry no information; padding buys the
verifier its time. -/
theorem EXP_subset_NEXP : EXP ⊆ NEXP := by
  sorry

end Complexity
