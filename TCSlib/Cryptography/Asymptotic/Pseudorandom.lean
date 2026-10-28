/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Ensembles
import TCSlib.Cryptography.Pseudorandom.Generators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pseudorandom ensembles and pseudorandom generators

The definitions of [PS10, §3.2.1 and §3.3.1]: a *pseudorandom ensemble* is one that is
computationally indistinguishable from the uniform ensemble `{U_{ℓ(n)}}`
[PS10, Definition 74.1], and a *pseudorandom generator* is an efficiently computable,
length-expanding function whose output on a uniform seed is a pseudorandom ensemble
[PS10, Definition 77.1].

`Ensemble.Pseudorandom` itself is the frozen definition of
`TCSlib.Cryptography.Asymptotic.Ensembles` (`Indist X (uniform ℓ)`); this file records that it
is literally "the PRG advantage `prgAdv` of [Gar26] is negligible for every non-uniform PPT"
(`Ensemble.pseudorandom_iff_prgAdv`), that the uniform ensemble is pseudorandom
(non-vacuity), and introduces the generator structure `PRG` with its efficiency clause
`PRG.Easy`, its output ensemble `PRG.ensemble` and the security predicate `PRG.Secure`.

Foundation decisions (`PassShelatChapter2-4Plan.md`): D5 (typed domains at each parameter),
D6 (ensembles are families of samplers), D9 (every length is a syntactic polynomial
`Complexity.PolyExpr`; the stretch `ℓ` of a generator is one).

**Deviation:** `PRG` is *length-regular*: `|G(x)|` depends only on `|x|` and is the syntactic
polynomial `stretch`, so that `G` is a typed family `G n : {0,1}^n → {0,1}^{ℓ(n)}` (the
concrete layer's convention [Gar26, Definition 3.5]); the text's `G : {0,1}* → {0,1}*` with
`|G(x)| > |x|` admits irregular lengths, which no construction of the book uses.

**Deviation:** `PRG.Easy`: a deterministic polynomial-time evaluator on the seed string
instead of a PPT computing `G` with probability one (equivalent by `Complexity.NUPPT.Computes`
and `ofPolyTimeUniform`, as for `FunFamily.Easy`); the seed is not prefixed by `1^n` since
its length is the parameter.

## Main definitions

* `TCSlib.Cryptography.PRG` — a length-regular generator with explicit stretch
  [PS10, Definition 77.1 (2)].
* `TCSlib.Cryptography.PRG.Easy` — the efficiency clause [PS10, Definition 77.1 (1)].
* `TCSlib.Cryptography.PRG.ensemble` — the output ensemble `{x ← U_n : G(x)}`.
* `TCSlib.Cryptography.PRG.Secure` — `G` is a pseudorandom generator
  [PS10, Definition 77.1 (1)+(3)].

## Main results

* `TCSlib.Cryptography.Ensemble.pseudorandom_iff_prgAdv` — [PS10, Definition 74.1] is
  "`prgAdv` negligible for every `D`" (the concrete quantity of [Gar26, Definition 3.5]).
* `TCSlib.Cryptography.Ensemble.uniform_pseudorandom` — the uniform ensemble is pseudorandom
  (non-vacuity of Definition 74.1).
* `TCSlib.Cryptography.PRG.secure_iff` — unfolding of `PRG.Secure` to the `prgAdv` form.
* `TCSlib.Cryptography.PRG.Easy.samplable` — the output ensemble of an efficiently
  computable generator is efficiently samplable (D6), so that `Ensemble.Indist.copies`
  applies to it.
* `TCSlib.Cryptography.PRG.stretch_pos` — the output length is positive (the hypothesis of
  [PS10, Theorem 75.4] holds for every generator).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.2.1: Definition 74.1; §3.3.1: Definition 77.1.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3 (Definition 3.5, the concrete `prgAdv`).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Pseudorandom ensembles [PS10, Definition 74.1] -/

/-- **Pseudorandomness is a negligible PRG advantage**: the frozen
`Ensemble.Pseudorandom X := Indist X (uniform ℓ)` [PS10, Definition 74.1] says exactly that
for every non-uniform PPT `D` the concrete PRG advantage
`prgAdv (X_n) D = |Pr[t ← X_n : D(1^n, t) = 1] − Pr[t ← U_{ℓ(n)} : D(1^n, t) = 1]|`
[Gar26, Definition 3.5] is a negligible function of `n`. Definitional: the uniform ensemble
samples by the identity. -/
theorem Ensemble.pseudorandom_iff_prgAdv {ℓ : PolyExpr} (X : Ensemble ℓ) :
    X.Pseudorandom ↔
      ∀ D : NUPPT, Negligible fun n => prgAdv (X.X n) (D.distinguisher n (ℓ.eval n)) :=
  Iff.rfl

/-- **The uniform ensemble is pseudorandom** (non-vacuity of [PS10, Definition 74.1]):
`{U_{ℓ(n)}} ≈ {U_{ℓ(n)}}` by reflexivity of `≈`. -/
theorem Ensemble.uniform_pseudorandom (ℓ : PolyExpr) : (Ensemble.uniform ℓ).Pseudorandom :=
  Ensemble.Indist.refl _

/-- Pseudorandomness is preserved by `≈`: if `{X_n} ≈ {Y_n}` and `{Y_n}` is pseudorandom then
so is `{X_n}` (transitivity of `≈`, [PS10, §3.1.1]). -/
theorem Ensemble.Indist.pseudorandom {ℓ : PolyExpr} {X Y : Ensemble ℓ} (h : X.Indist Y)
    (hY : Y.Pseudorandom) : X.Pseudorandom :=
  h.trans hY

/-! ### Pseudorandom generators [PS10, Definition 77.1] -/

/-- A **(length-regular) generator** with explicit stretch: at every seed length `n`, a
function `G n : {0,1}^n → {0,1}^{ℓ(n)}` with `ℓ(n) > n` — the expansion clause
[PS10, Definition 77.1 (2)] with the output length a syntactic polynomial `stretch` (D9).
The efficiency and pseudorandomness clauses are `PRG.Easy` and `PRG.Secure`.

**Deviation:** `PRG` is *length-regular*: `|G(x)|` depends only on `|x|` and is the syntactic
polynomial `stretch`, so that `G` is a typed family `G n : {0,1}^n → {0,1}^{ℓ(n)}` (the
concrete layer's convention [Gar26, Definition 3.5]); the text's `G : {0,1}* → {0,1}*` with
`|G(x)| > |x|` admits irregular lengths, which no construction of the book uses. -/
structure PRG where
  /-- The output length `ℓ(n)` at seed length `n`. -/
  stretch : PolyExpr
  /-- The generator at seed length `n`. -/
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  /-- Expansion: `|G(x)| > |x|` [PS10, Definition 77.1 (2)]. -/
  expands : ∀ n, n < stretch.eval n

namespace PRG

/-- **Efficiency** [PS10, Definition 77.1 (1)]: a polynomial-time string function computes
`G n s` from the seed string `s` (of length `n`).

**Deviation:** `PRG.Easy`: a deterministic polynomial-time evaluator on the seed string
instead of a PPT computing `G` with probability one (equivalent by `Complexity.NUPPT.Computes`
and `ofPolyTimeUniform`, as for `FunFamily.Easy`); the seed is not prefixed by `1^n` since
its length is the parameter. -/
def Easy (P : PRG) : Prop :=
  ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
    ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)

/-- The **output ensemble** `{x ← U_n : G(x)}_n` of a generator [PS10, Definition 77.1 (3)]:
seeds are the uniform `n`-bit strings and the sampler is `G n`. -/
def ensemble (P : PRG) : Ensemble P.stretch where
  σ n := Fin n → Bool
  X := P.G

/-- `G` is a **pseudorandom generator** [PS10, Definition 77.1]: efficiently computable
(clause (1)) and its output ensemble is pseudorandom (clause (3)); expansion (clause (2)) is
the field `PRG.expands` of the structure. -/
def Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom

/-- Unfolding of the output ensemble: the sampler at `n` is `G n`. -/
@[simp] theorem ensemble_X (P : PRG) (n : ℕ) : P.ensemble.X n = P.G n := rfl

/-- Unfolding of the output ensemble: the seed type at `n` is `{0,1}^n`. -/
theorem ensemble_σ (P : PRG) (n : ℕ) : P.ensemble.σ n = (Fin n → Bool) := rfl

/-- The output length of a generator is positive at every seed length (from the expansion
clause); this is the hypothesis `0 < ℓ(n)` of [PS10, Theorem 75.4] for output ensembles of
generators. -/
theorem stretch_pos (P : PRG) (n : ℕ) : 0 < P.stretch.eval n :=
  lt_of_le_of_lt (Nat.zero_le n) (P.expands n)

/-- **Security unfolded**: `G` is a secure PRG iff it is easy to compute and for every
non-uniform PPT `D` the PRG advantage `prgAdv (G n) (D(1^n, ·))` [Gar26, Definition 3.5] is
negligible — the form in which the concrete reductions of the Garg layer are consumed. -/
theorem secure_iff (P : PRG) :
    P.Secure ↔ P.Easy ∧
      ∀ D : NUPPT, Negligible fun n => prgAdv (P.G n) (D.distinguisher n (P.stretch.eval n)) :=
  Iff.rfl

/-- **An efficiently computable generator has an efficiently samplable output ensemble**
(D6): the sampler draws `n` uniform bits `r` (`s := var`) and returns `F r` where `F` is the
polynomial-time evaluator; the law of the padded output is exactly that of `G n` on a
uniform seed. This is what makes `Ensemble.Indist.copies` applicable to PRG outputs
[PS10, §3.3.5, the multi-copy argument of Lemma 80.5]. -/
theorem Easy.samplable {P : PRG} (h : P.Easy) : P.ensemble.Samplable := by
  obtain ⟨F, hF, hG⟩ := h
  refine ⟨.var, F ∘ pairSndD, hF.comp polyTimeComputable_pairSndD, fun n => ?_⟩
  have e : (fun r : Fin (PolyExpr.var.eval n) → Bool =>
      padFin (P.stretch.eval n) ((F ∘ pairSndD) (NUPPT.advInput n (List.ofFn r)))) =
      P.ensemble.X n := by
    funext r
    simp [NUPPT.advInput, hG, padFin_ofFn]
  rw [e]
  exact StatClose.refl _

end PRG

end TCSlib.Cryptography
