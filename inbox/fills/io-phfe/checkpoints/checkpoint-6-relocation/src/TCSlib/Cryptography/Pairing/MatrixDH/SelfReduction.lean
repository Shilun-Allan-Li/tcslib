/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.MatrixDH.Defs
import TCSlib.Cryptography.Pairing.MatrixDH.ColumnLaws
import TCSlib.Cryptography.Pairing.MatrixDH.Hardness
import TCSlib.Cryptography.Asymptotic.Realization
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Cryptography.Pairing.MatrixDH.Widths

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A column-hybrid reduction from uniform-matrix MDDH to DLIN

A canonical DLIN challenge implicitly contains the matrix `A₀` with rows `(a,0)`, `(0,b)`,
`(1,1)` and a response column `c`. A known left randomizer `L` produces `[LA₀]` and `[Lc]`
using products and powers only. On the real branch, full column rank of `A₀` gives a uniform
base matrix and a real response column. On the random branch, invertibility of `(A₀|c)`
gives a uniform base matrix and an independent uniform response column.

A hybrid index and the other response columns' masks are fixed in advice by averaging.
There is one realising machine, with the hybrid index inside its advice; the inequality
has a polynomial factor `d(κ)` rather than an unbounded family of machine advantages.
This is a column-hybrid implementation of the implication stated in [Wee20, §2.1], with
an explicit polynomial loss rather than the tight reduction cited there.

## Main definitions

* `BilinearGen.MddhAdvice`: one hybrid index and scalar matrices over the fixed schedule.
* `BilinearGen.mddhAdviceEnc`, `BilinearGen.mddhAdviceLen`: explicit advice encoding and bound.
* `BilinearGen.mddhPreChallenge`, `BilinearGen.mddhPre`: deterministic typed and string
  preprocessing of a canonical DLIN challenge.
* `BilinearGen.dlinToMddh`: one activation of the MDDH distinguisher, with its own coins.
* `BilinearGen.mddhSlack`: the explicit `4d(κ)/p(κ)` statistical correction.
* `BilinearGen.MDDHRealizable`: existence of a machine realising each fixed-advice reduction.

## Main results

* `BilinearGen.mddhAdvice_finite`, `BilinearGen.mddhAdvice_nonempty`: advice is finite and
  inhabited at every security parameter, including zero response columns.
* `BilinearGen.mddhAdviceEnc_injective`, `BilinearGen.length_mddhAdviceEnc_le`: bounded advice.
* `BilinearGen.mddhAdv_le`: one advice family works for every realiser at every parameter.
* `BilinearGen.mddhAdv_negligible`, `BilinearGen.mddh_subexpHard`: asymptotic consequences
  through the shared negligible and subexponential APIs.

The reduction never samples. Every scalar in its arithmetic is already in the advice.
The schedule only transports advice into the drawn field through the public order equality;
the algorithms do not compute the schedule. The advice encoding includes unary `κ` and
binary dimension headers, so one uniform preprocessing target can read its parameter and
dimensions directly from its input.

The width bound is reused from `BB1Machine.order_le_two_pow`; none of that module's draws
or coin decoders is used here.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §2.1, p. 4 (the MDDH
  implication, attributed there to Escala et al.; the reduction here has polynomial loss).
* [JLS26] A. Jain, H. Lin, and A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, Journal of the ACM 73(1), Article 1, 2026, §1.1, p. 3 (canonical DLIN).
-/

namespace TCSlib.Cryptography.Pairing

open Complexity Turing TCSlib.Cryptography.Games

namespace BilinearGen

variable (G : BilinearGen)

/-- Advice fixes a hybrid-column index, a left randomizer, coefficient masks for the other
real columns, and uniform scalars for the other random columns. This is reduction glue for
[Wee20, §2.1, p. 4]. The extra index value is a sentinel, ensuring inhabitation when `d=0`. -/
abbrev MddhAdvice (p : ℕ → ℕ) (d ℓ : PolyExpr) (κ : ℕ) : Type :=
  Fin (d.eval κ + 1) ×
    Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod (p κ)) ×
    Matrix (Fin 2) (Fin (d.eval κ)) (ZMod (p κ)) ×
    Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod (p κ))

/-- Advice is exactly the hybrid index and its three known scalar matrices. -/
theorem mddhAdvice_eq (p : ℕ → ℕ) (d ℓ : PolyExpr) (κ : ℕ) :
    MddhAdvice p d ℓ κ =
      (Fin (d.eval κ + 1) ×
        Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod (p κ)) ×
        Matrix (Fin 2) (Fin (d.eval κ)) (ZMod (p κ)) ×
        Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod (p κ))) := rfl

/-- Zero matrices and the first index give advice even when the response has no columns.
This is technical inhabitation glue, not a sampling algorithm. -/
def mddhAdviceDefault (p : ℕ → ℕ) (d ℓ : PolyExpr) (κ : ℕ) : MddhAdvice p d ℓ κ :=
  ⟨0, 0, 0, 0⟩

/-- The default advice consists of the first index and three zero matrices. -/
theorem mddhAdviceDefault_eq (p : ℕ → ℕ) (d ℓ : PolyExpr) (κ : ℕ) :
    mddhAdviceDefault p d ℓ κ = ⟨0, 0, 0, 0⟩ := rfl

/-- Advice is nonempty at every parameter, including `d(κ)=0`. Technical glue. -/
theorem mddhAdvice_nonempty (p : ℕ → ℕ) (d ℓ : PolyExpr) (κ : ℕ) :
    Nonempty (MddhAdvice p d ℓ κ) := ⟨mddhAdviceDefault p d ℓ κ⟩

/-- A fixed prime order schedule makes every advice type finite. Technical glue; no
additional nonzero-schedule assumption is imposed. -/
theorem mddhAdvice_finite (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr) (κ : ℕ) :
    Finite (MddhAdvice p d ℓ κ) :=
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  inferInstance

/-- The advice word stores unary `κ`, shortest binary dimension headers, a one-hot hybrid
index, and fixed-width modular matrices. Scalars are advice, never drawn by the reduction. -/
def mddhAdviceEnc (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) (κ : ℕ) (ω : MddhAdvice p d ℓ κ) : List Bool :=
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  pairEncode (List.replicate κ true)
    (pairEncode (Candidates.natToList (Nat.size (d.eval κ)) (d.eval κ))
      (pairEncode (Candidates.natToList (Nat.size (ℓ.eval κ)) (ℓ.eval κ))
        ((List.ofFn fun i : Fin (d.eval κ + 1) => decide (i = ω.1)) ++
          Encoding.Modular.encodeMatrix (G.wG.eval κ) ω.2.1 ++
          Encoding.Modular.encodeMatrix (G.wG.eval κ) ω.2.2.1 ++
          Encoding.Modular.encodeMatrix (G.wG.eval κ) ω.2.2.2)))

/-- The advice encoding exposes the security parameter, numeric dimensions and scalar blocks. -/
theorem mddhAdviceEnc_eq (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) (κ : ℕ) (ω : MddhAdvice p d ℓ κ) :
    G.mddhAdviceEnc p hp d ℓ κ ω =
      letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
      pairEncode (List.replicate κ true)
        (pairEncode (Candidates.natToList (Nat.size (d.eval κ)) (d.eval κ))
          (pairEncode (Candidates.natToList (Nat.size (ℓ.eval κ)) (ℓ.eval κ))
            ((List.ofFn fun i : Fin (d.eval κ + 1) => decide (i = ω.1)) ++
              Encoding.Modular.encodeMatrix (G.wG.eval κ) ω.2.1 ++
              Encoding.Modular.encodeMatrix (G.wG.eval κ) ω.2.2.1 ++
              Encoding.Modular.encodeMatrix (G.wG.eval κ) ω.2.2.2))) := rfl

/-- A polynomial bounds the parameter, dimension and one-hot headers and scalar blocks.
This is reduction-encoding glue. Binary lengths are bounded by their values plus one. -/
def mddhAdviceLen (d ℓ : PolyExpr) : PolyExpr :=
  ((((PolyExpr.var.mul (PolyExpr.const 2)).add ((PolyExpr.const 2).mul d)).add ((PolyExpr.const
    2).mul ℓ)).add
    (PolyExpr.const 10)).add ((d.add (PolyExpr.const 1)).add
      ((((ℓ.mul (PolyExpr.const 3)).add ((PolyExpr.const 2).mul d)).add (ℓ.mul d)).mul G.wG))

/-- The advice-length expression has one term for each serialized block. -/
theorem mddhAdviceLen_eq (d ℓ : PolyExpr) :
    G.mddhAdviceLen d ℓ =
      ((((PolyExpr.var.mul (PolyExpr.const 2)).add ((PolyExpr.const 2).mul d)).add ((PolyExpr.const
        2).mul ℓ)).add
        (PolyExpr.const 10)).add ((d.add (PolyExpr.const 1)).add
          ((((ℓ.mul (PolyExpr.const 3)).add ((PolyExpr.const 2).mul d)).add (ℓ.mul d)).mul G.wG)) :=
            rfl

/-- Every advice family has the same polynomial length bound. Technical glue.

**Proof sketch.** Use `length_pairEncode`, `Candidates.length_natToList`, the unary and
one-hot lengths, and `Encoding.Modular.encodeMatrix_length`. Bound each binary dimension
length by its value plus one and use the polynomial evaluation readers. -/
theorem length_mddhAdviceEnc_le (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr)
    (κ : ℕ) (ω : MddhAdvice p d ℓ κ) :
    (G.mddhAdviceEnc p hp d ℓ κ ω).length ≤ (G.mddhAdviceLen d ℓ).eval κ := by
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  have hd := Turing.length_bits_le_self (d.eval κ)
  have hℓ := Turing.length_bits_le_self (ℓ.eval κ)
  rw [Nat.size_eq_bits_len] at hd hℓ
  rw [G.mddhAdviceEnc_eq p hp d ℓ κ ω, G.mddhAdviceLen_eq d ℓ]
  simp only [length_pairEncode, List.length_replicate, Candidates.length_natToList,
    List.length_append, List.length_ofFn, Encoding.Modular.encodeMatrix_length,
    PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_var, PolyExpr.eval_const,
    Nat.add_mul]
  omega

/-- The advice word is injective on its index and scalar matrices. Technical glue.

**Proof sketch.** Split the fixed-width blocks. The one-hot word recovers the hybrid index.
Use `BB1Machine.order_le_two_pow` and the fixed order equality for a generated instance;
then apply `Encoding.Modular.encodeMatrix_injective` to each scalar block. -/
theorem mddhAdviceEnc_injective (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr) (κ : ℕ) :
    Function.Injective (G.mddhAdviceEnc p hp d ℓ κ) := by
  letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
  intro ω₁ ω₂ h
  -- Separate the fixed public metadata and then the fixed-length scalar blocks.
  simp only [G.mddhAdviceEnc_eq p hp d ℓ κ] at h
  rcases Prod.mk.inj (pairEncode_injective h) with ⟨_, h₁⟩
  rcases Prod.mk.inj (pairEncode_injective h₁) with ⟨_, h₂⟩
  rcases Prod.mk.inj (pairEncode_injective h₂) with ⟨_, hBody⟩
  simp only [List.append_assoc] at hBody
  have hIndexLen :=
    (List.length_ofFn (f := fun i : Fin (d.eval κ + 1) => decide (i = ω₁.1))).trans
      (List.length_ofFn (f := fun i : Fin (d.eval κ + 1) => decide (i = ω₂.1))).symm
  rcases List.append_inj hBody hIndexLen with ⟨hIndexWord, hBlocks⟩
  have hLLen :=
    (Encoding.Modular.encodeMatrix_length (G.wG.eval κ) ω₁.2.1).trans
      (Encoding.Modular.encodeMatrix_length (G.wG.eval κ) ω₂.2.1).symm
  rcases List.append_inj hBlocks hLLen with ⟨hLWord, hTail⟩
  have hSLen :=
    (Encoding.Modular.encodeMatrix_length (G.wG.eval κ) ω₁.2.2.1).trans
      (Encoding.Modular.encodeMatrix_length (G.wG.eval κ) ω₂.2.2.1).symm
  rcases List.append_inj hTail hSLen with ⟨hSWord, hUWord⟩
  -- The one-hot bit at the first advice index identifies that index.
  have hIndex : ω₁.1 = ω₂.1 :=
    of_decide_eq_true
      ((congrFun (List.ofFn_injective hIndexWord) ω₁.1).symm.trans
        (decide_eq_true (Eq.refl ω₁.1)))
  -- A generated instance supplies the existing no-truncation bound for each scalar word.
  have hWidth := orderSchedule_le_two_pow G p hp κ
  have hL : ω₁.2.1 = ω₂.2.1 :=
    Encoding.Modular.encodeMatrix_injective
      (q := p κ) (rows := ℓ.eval κ) (columns := 3) (G.wG.eval κ) hWidth hLWord
  have hS : ω₁.2.2.1 = ω₂.2.2.1 :=
    Encoding.Modular.encodeMatrix_injective
      (q := p κ) (rows := 2) (columns := d.eval κ) (G.wG.eval κ) hWidth hSWord
  have hU : ω₁.2.2.2 = ω₂.2.2.2 :=
    Encoding.Modular.encodeMatrix_injective
      (q := p κ) (rows := ℓ.eval κ) (columns := d.eval κ) (G.wG.eval κ) hWidth hUWord
  exact Prod.ext hIndex (Prod.ext hL (Prod.ext hS hU))

/-- The L1 typed preprocessor embeds the canonical DLIN column into a matrix hybrid. Its
role is to provide one challenge column and compute all other columns from fixed advice.
The per-column statistical correction is at most `4/p`; the hybrid contributes `d(κ)`.
All group entries are formed by products and known scalar powers [Wee20, §2.1, p. 4]. -/
def mddhPreChallenge (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) (κ : ℕ) (ω : MddhAdvice p d ℓ κ) (c : G.DLINChallenge κ) :
    G.MDDHChallenge d ℓ κ :=
  let castScalar := ZMod.ringEquivCongr (order_eq_of_publicParams G p hp κ c.pp).symm
  let L := fun i j => castScalar (ω.2.1 i j)
  let S := fun i j => castScalar (ω.2.2.1 i j)
  let U := fun i j => castScalar (ω.2.2.2 i j)
  let M := fun (i : Fin (ℓ.eval κ)) (j : Fin 2) =>
    if j = 0 then c.baseA ^ (L i 0).val * c.pp.generator ^ (L i 2).val
    else c.baseB ^ (L i 1).val * c.pp.generator ^ (L i 2).val
  let v := fun i =>
    c.responseA ^ (L i 0).val * c.responseB ^ (L i 1).val * c.responseSum ^ (L i 2).val
  ⟨c.pp, M, fun i j =>
    if j.val = ω.1.val then v i
    else if j.val < ω.1.val then M i 0 ^ (S 0 j).val * M i 1 ^ (S 1 j).val
    else c.pp.generator ^ (U i j).val⟩

/-- The typed preprocessor is precisely the displayed group-arithmetic embedding. 

**Proof sketch.** The explicit preprocessing formula reduces by reflexivity. -/
theorem mddhPreChallenge_eq (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) (κ : ℕ) (ω : MddhAdvice p d ℓ κ) (c : G.DLINChallenge κ) :
    G.mddhPreChallenge p hp d ℓ κ ω c =
      let castScalar := ZMod.ringEquivCongr (order_eq_of_publicParams G p hp κ c.pp).symm
      let L := fun i j => castScalar (ω.2.1 i j)
      let S := fun i j => castScalar (ω.2.2.1 i j)
      let U := fun i j => castScalar (ω.2.2.2 i j)
      let M := fun (i : Fin (ℓ.eval κ)) (j : Fin 2) =>
        if j = 0 then c.baseA ^ (L i 0).val * c.pp.generator ^ (L i 2).val
        else c.baseB ^ (L i 1).val * c.pp.generator ^ (L i 2).val
      let v := fun i =>
        c.responseA ^ (L i 0).val * c.responseB ^ (L i 1).val * c.responseSum ^ (L i 2).val
      ⟨c.pp, M, fun i j =>
        if j.val = ω.1.val then v i
        else if j.val < ω.1.val then M i 0 ^ (S 0 j).val * M i 1 ^ (S 1 j).val
        else c.pp.generator ^ (U i j).val⟩ := rfl

/-- The L1 string preprocessor serializes its typed matrix hybrid. Its input is a canonical
DLIN challenge and fixed advice; its output is the MDDH distinguisher's public input.
It contributes the same per-column correction as `mddhPreChallenge` and never samples. -/
def mddhPre (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) (κ : ℕ) (ω : MddhAdvice p d ℓ κ) (c : G.DLINChallenge κ) : List Bool :=
  G.mddhEnc d ℓ κ (G.mddhPreChallenge p hp d ℓ κ ω c)

/-- The string preprocessor is the encoding of its typed matrix hybrid. -/
theorem mddhPre_eq (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) (κ : ℕ) (ω : MddhAdvice p d ℓ κ) (c : G.DLINChallenge κ) :
    G.mddhPre p hp d ℓ κ ω c =
      G.mddhEnc d ℓ κ (G.mddhPreChallenge p hp d ℓ κ ω c) := rfl

/-- The L1 DLIN reduction activates `D` once on the preprocessed matrix hybrid, using the
input coins truncated to `D.coinLen κ`. It never samples. Its comparison has a hybrid
factor `d(κ)` and total statistical correction `4d(κ)/p(κ)` [Wee20, §2.1, p. 4]. -/
def dlinToMddh (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) (D : NUPPT) (ω : ∀ κ, MddhAdvice p d ℓ κ)
    (κ : ℕ) (c : G.DLINChallenge κ) (r : List Bool) : List Bool :=
  D.runAtL κ (G.mddhPre p hp d ℓ κ (ω κ) c) (r.take (D.coinLen κ))

/-- The reduction runs the MDDH distinguisher on its deterministic preprocessed input. -/
theorem dlinToMddh_eq (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) (D : NUPPT) (ω : ∀ κ, MddhAdvice p d ℓ κ)
    (κ : ℕ) (c : G.DLINChallenge κ) (r : List Bool) :
    G.dlinToMddh p hp d ℓ D ω κ c r =
      D.runAtL κ (G.mddhPre p hp d ℓ κ (ω κ) c) (r.take (D.coinLen κ)) := rfl

/-- The full column-hybrid correction is `4d(κ)/p(κ)`. On a real DLIN challenge the base
matrix has rank below two with probability `p⁻²`. On a random challenge the augmented
matrix is singular with probability `3/p-3/p²+1/p³`. Their sum is at most `4/p` per column.
This is an explicit loss for the column-hybrid route to [Wee20, §2.1, p. 4]. -/
noncomputable def mddhSlack (p : ℕ → ℕ) (d : PolyExpr) (κ : ℕ) : ℝ :=
  (d.eval κ : ℝ) * (4 / (p κ : ℝ))

/-- The correction is the response-column count times the per-column `4/p` bound. -/
theorem mddhSlack_eq (p : ℕ → ℕ) (d : PolyExpr) (κ : ℕ) :
    mddhSlack p d κ = (d.eval κ : ℝ) * (4 / (p κ : ℝ)) := rfl

/-- For every MDDH distinguisher, one advice family makes the column-hybrid bound hold for
EVERY machine realising the reduction, simultaneously at all parameters
[Wee20, §2.1, p. 4, polynomial-loss implementation of its cited implication].
The shared realisation predicate constrains only encoded challenges and coin strings of
the stated layout length, which suffices for this bound.

**Proof sketch.** For a nonzero column count, select an adjacent response-column hybrid by
the shared hybrid-gap lemma. Fix the left randomizer and other columns' masks by averaging.
For the real challenge, condition on rank two of `A₀`; for the random challenge, condition
on `det(A₀|c)=ab(t-r-s)` being nonzero. Left multiplication by the corresponding full-rank
matrix is a uniform linear map, giving the required adjacent laws. Bound their exceptional
probabilities by `p⁻²` and `3/p-3/p²+1/p³`. Transfer the typed reduction's verdict through
`RealizesOn.distinguisherL_eq`. Multiply by the column count. For zero columns the advantage
is zero, and the sentinel advice supplies the required inhabited value. -/
theorem mddhAdv_le (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) (D : NUPPT) :
    ∃ ω : ∀ κ, MddhAdvice p d ℓ κ, ∀ B : NUPPT,
      B.RealizesOn G.dlinEnc D.coins (G.dlinToMddh p hp d ℓ D ω) →
      ∀ κ, G.mddhAdv d ℓ D κ ≤
        (d.eval κ : ℝ) * G.dlinAdv B κ + mddhSlack p d κ := by
  -- The column index is fixed by the hybrid lemma; only its three scalar tapes are averaged.
  let Tape (κ : ℕ) : Type :=
    Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod (p κ)) ×
      Matrix (Fin 2) (Fin (d.eval κ)) (ZMod (p κ)) ×
      Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod (p κ))
  let avgTape (κ : ℕ) (f : Tape κ → ℝ) : ℝ :=
    letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
    ProbComp.expect (ProbComp.sample (Tape κ)) f
  -- These are the actual column hybrids, sharing the real base and the original D coins.
  let hybrid (κ i : ℕ) : ProbComp Bool :=
    (publicParamsGen G κ).bind fun pp =>
    (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order))).bind fun M =>
    (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order))).bind fun S =>
    (ProbComp.sample
      (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order))).bind fun U =>
    (ProbComp.sample (D.Coins κ)).bind fun r =>
      .pure (D.distinguisherL κ (G.mddhEnc d ℓ κ
        ⟨pp, pp.group.expMat pp.generator M,
          pp.group.expMat pp.generator
            (fun a b => if b.val < i then (M * S) a b else U a b)⟩) r)
  -- The reduction experiment uses the published preprocessor and never constructs a machine.
  let redGame (κ : ℕ) (w : MddhAdvice p d ℓ κ) (real : Bool) : ProbComp Bool :=
    (G.dlinSample real κ).bind fun c =>
    (ProbComp.sample (D.Coins κ)).bind fun r =>
      .pure (D.distinguisherL κ (G.mddhPre p hp d ℓ κ w c) r)
  let redGap (κ : ℕ) (w : MddhAdvice p d ℓ κ) : ℝ :=
    advantage (redGame κ w false) (redGame κ w true)
  have hEnds : ∀ κ,
      accept (hybrid κ 0) = accept (G.mddhGame d ℓ D false κ) ∧
        accept (hybrid κ (d.eval κ)) = accept (G.mddhGame d ℓ D true κ) := by
    intro κ
    constructor
    · dsimp only [hybrid]
      simp only [accept_eq, G.mddhGame_eq d ℓ D false κ, G.mddhSample_eq d ℓ false κ,
        ProbComp.prob_bind, ProbComp.expect_bind, ProbComp.expect_pure,
        Bool.false_eq_true, if_false, Nat.not_lt_zero]
    · dsimp only [hybrid]
      simp only [accept_eq, G.mddhGame_eq d ℓ D true κ, G.mddhSample_eq d ℓ true κ,
        ProbComp.prob_bind, ProbComp.expect_bind, ProbComp.expect_pure,
        ↓reduceIte, if_true, Fin.is_lt]
  have hEndpointGap (κ : ℕ) :
      G.mddhAdv d ℓ D κ = advantage (hybrid κ 0) (hybrid κ (d.eval κ)) := ?_
  swap
  · rw [G.mddhAdv_eq d ℓ D κ, advantage_eq, advantage_eq, (hEnds κ).1, (hEnds κ).2]
  -- Known scalar DLIN draws give exactly the group-arithmetic preprocessor's planted column.
  have hPreScalar : ∀ (κ : ℕ) (w : MddhAdvice p d ℓ κ) (pp : PublicParams G κ)
      (ab rs : Fin 2 → ZMod pp.group.order) (t : ZMod pp.group.order) (real : Bool),
      let castScalar := ZMod.ringEquivCongr (order_eq_of_publicParams G p hp κ pp).symm
      let L : Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod pp.group.order) :=
        fun i j => castScalar (w.2.1 i j)
      let S : Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order) :=
        fun i j => castScalar (w.2.2.1 i j)
      let U : Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order) :=
        fun i j => castScalar (w.2.2.2 i j)
      let A0 : Matrix (Fin 3) (Fin 2) (ZMod pp.group.order) :=
        ![![ab 0, 0], ![0, ab 1], ![1, 1]]
      let v0 : Fin 3 → ZMod pp.group.order :=
        ![ab 0 * rs 0, ab 1 * rs 1, if real then rs 0 + rs 1 else t]
      G.mddhPreChallenge p hp d ℓ κ w
          (G.dlinChallenge κ pp (pp.generator ^ (ab 0).val) (pp.generator ^ (ab 1).val)
            (pp.generator ^ (ab 0 * rs 0).val) (pp.generator ^ (ab 1 * rs 1).val)
            (pp.generator ^ (if real then rs 0 + rs 1 else t).val)) =
        ⟨pp, pp.group.expMat pp.generator (L * A0),
          pp.group.expMat pp.generator (fun i j =>
            if j.val = w.1.val then Matrix.mulVec L v0 i
            else if j.val < w.1.val then ((L * A0) * S) i j else U i j)⟩ := by
    intro κ w pp ab rs t real castScalar L S U A0 v0
    letI : Fact (1 < pp.group.order) := ⟨pp.group.order_prime.one_lt⟩
    let M : Matrix (Fin (ℓ.eval κ)) (Fin 2) pp.group.G := fun i j =>
      if j = 0 then
        (pp.generator ^ (ab 0).val) ^ (L i 0).val * pp.generator ^ (L i 2).val
      else (pp.generator ^ (ab 1).val) ^ (L i 1).val * pp.generator ^ (L i 2).val
    let v : Fin (ℓ.eval κ) → pp.group.G := fun i =>
      (pp.generator ^ (ab 0 * rs 0).val) ^ (L i 0).val *
        (pp.generator ^ (ab 1 * rs 1).val) ^ (L i 1).val *
        (pp.generator ^ (if real then rs 0 + rs 1 else t).val) ^ (L i 2).val
    -- Reuse the proved scalar-left action for the entire implicit base matrix.
    have hBase : M = pp.group.expMat pp.generator (L * A0) := ?_
    swap
    · rw [← pp.group.expMat_mul_left pp.generator L A0]
      funext i j
      fin_cases j <;>
        norm_num only [Fin.mk_zero, Fin.mk_one, M, matMulGroup_apply, groupDot_eq,
          Fin.prod_univ_three,
          pp.group.expMat_apply, A0, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ZMod.val_zero,
          ZMod.val_one pp.group.order, pow_zero, pow_one, one_pow, mul_one, one_mul,
          ↓reduceIte]
      all_goals rfl
    -- The planted column is the already-proved exponent dot product on three coordinates.
    have hPlant : v = pp.group.expVec pp.generator (Matrix.mulVec L v0) := ?_
    swap
    · funext i
      have hDot := pp.group.groupDot_expVec pp.generator v0 (L i)
      simp only [groupDot_eq, Fin.prod_univ_three, pp.group.expVec_apply, v0,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hDot
      rw [pp.group.expVec_apply]
      refine (show v i = pp.generator ^ (dotProduct (L i) v0).val from ?_)
      rw [dotProduct_comm]
      exact hDot
    -- Reuse the proved scalar-right action for each ordinary real response column.
    have hReal (i : Fin (ℓ.eval κ)) (j : Fin (d.eval κ)) :
        M i 0 ^ (S 0 j).val * M i 1 ^ (S 1 j).val =
          pp.group.expMat pp.generator ((L * A0) * S) i j := ?_
    swap
    · have hTransport := congrFun
        (congrFun (pp.group.expMat_mul pp.generator (L * A0) S) i) j
      simpa only [hBase, groupMatMul_apply, groupDot_eq, Fin.prod_univ_two] using hTransport
    have hResponse :
        (fun (i : Fin (ℓ.eval κ)) (j : Fin (d.eval κ)) =>
          if j.val = w.1.val then v i
          else if j.val < w.1.val then M i 0 ^ (S 0 j).val * M i 1 ^ (S 1 j).val
          else pp.generator ^ (U i j).val) =
          pp.group.expMat pp.generator (fun i j =>
            if j.val = w.1.val then Matrix.mulVec L v0 i
            else if j.val < w.1.val then ((L * A0) * S) i j else U i j) := ?_
    swap
    · funext i j
      rw [pp.group.expMat_apply]
      by_cases hSelected : j.val = w.1.val
      · simpa only [if_pos hSelected, pp.group.expVec_apply] using congrFun hPlant i
      · simp only [if_neg hSelected]
        by_cases hPrior : j.val < w.1.val
        · simpa only [if_pos hPrior, pp.group.expMat_apply] using hReal i j
        · simp only [if_neg hPrior]
    -- Read the public constructor and actual preprocessor, then assemble their data fields.
    rw [G.dlinChallenge_eq, G.mddhPreChallenge_eq p hp d ℓ κ w]
    exact congrArg₂
      (fun (N : Matrix (Fin (ℓ.eval κ)) (Fin 2) pp.group.G)
        (R : Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) pp.group.G) =>
        (⟨pp, N, R⟩ : G.MDDHChallenge d ℓ κ)) hBase hResponse
  -- Share the same observer, independent tape blocks and exact scalar draws for both laws.
  let SType (κ : ℕ) (pp : PublicParams G κ) : Type :=
    Matrix (Fin 2) (Fin (d.eval κ)) (ZMod pp.group.order)
  let UType (κ : ℕ) (pp : PublicParams G κ) : Type :=
    Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order)
  let A0 (κ : ℕ) (pp : PublicParams G κ) (ab : Fin 2 → ZMod pp.group.order) :
      Matrix (Fin 3) (Fin 2) (ZMod pp.group.order) :=
    ![![ab 0, 0], ![0, ab 1], ![1, 1]]
  let obs (κ : ℕ) (j : Fin (d.eval κ)) (pp : PublicParams G κ)
      (S : SType κ pp) (U : UType κ pp)
      (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order))
      (v : Fin (ℓ.eval κ) → ZMod pp.group.order) : ℝ :=
    ProbComp.prob (ProbComp.sample (D.Coins κ)) fun r =>
      D.distinguisherL κ (G.mddhEnc d ℓ κ
        ⟨pp, pp.group.expMat pp.generator M,
          pp.group.expMat pp.generator (fun a b =>
            if b.val = j.val then v a
            else if b.val < j.val then (M * S) a b else U a b)⟩) r = true
  let idealCore (κ : ℕ) (j : Fin (d.eval κ)) (real : Bool)
      (pp : PublicParams G κ) (S : SType κ pp) (U : UType κ pp) : ℝ :=
    ProbComp.expect
      (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)))
      fun M => if real then
        ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order))
          fun rs => obs κ j pp S U M (Matrix.mulVec M rs)
      else ProbComp.expect (ProbComp.sample (Fin (ℓ.eval κ) → ZMod pp.group.order))
        (obs κ j pp S U M)
  let plantedCore (κ : ℕ) (j : Fin (d.eval κ)) (real : Bool)
      (pp : PublicParams G κ) (S : SType κ pp) (U : UType κ pp) : ℝ :=
    ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)) fun ab =>
      ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)) fun rs =>
        ProbComp.expect (ProbComp.sample (ZMod pp.group.order)) fun t =>
          ProbComp.expect
            (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod pp.group.order)))
            fun L => obs κ j pp S U (L * A0 κ pp ab)
              (Matrix.mulVec L
                ![ab 0 * rs 0, ab 1 * rs 1, if real then rs 0 + rs 1 else t])
  let ideal (κ : ℕ) (j : Fin (d.eval κ)) (real : Bool) (pp : PublicParams G κ) : ℝ :=
    ProbComp.expect (ProbComp.sample (SType κ pp)) fun S =>
      ProbComp.expect (ProbComp.sample (UType κ pp)) (idealCore κ j real pp S)
  let planted (κ : ℕ) (j : Fin (d.eval κ)) (real : Bool) (pp : PublicParams G κ) : ℝ :=
    ProbComp.expect (ProbComp.sample (SType κ pp)) fun S =>
      ProbComp.expect (ProbComp.sample (UType κ pp)) (plantedCore κ j real pp S)
  let coreLoss (κ : ℕ) (real : Bool) : ℝ :=
    if real then 1 / (p κ : ℝ) ^ 2 else 1 - (1 - 1 / (p κ : ℝ)) ^ 3
  -- Commute the fixed-order advice sample through pp and transport each scalar coordinate
  -- by the order equality. hPreScalar reads the actual reduction for either real bit.
  have hReductionTransport : ∀ (κ : ℕ) (j : Fin (d.eval κ)) (real : Bool),
      avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) real)) =
        ProbComp.expect (publicParamsGen G κ) (planted κ j real) := by
    intro κ j real
    letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
    let Target (pp : PublicParams G κ) : Type :=
      Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod pp.group.order) ×
        SType κ pp × UType κ pp
    let castMatrix (pp : PublicParams G κ) (m n : ℕ) :
        Matrix (Fin m) (Fin n) (ZMod (p κ)) ≃
          Matrix (Fin m) (Fin n) (ZMod pp.group.order) :=
      Equiv.arrowCongr (Equiv.refl (Fin m))
        (Equiv.arrowCongr (Equiv.refl (Fin n))
          (ZMod.ringEquivCongr (order_eq_of_publicParams G p hp κ pp).symm).toEquiv)
    let tapeEquiv (pp : PublicParams G κ) : Tape κ ≃ Target pp :=
      Equiv.prodCongr (castMatrix pp (ℓ.eval κ) 3)
        (Equiv.prodCongr (castMatrix pp 2 (d.eval κ))
          (castMatrix pp (ℓ.eval κ) (d.eval κ)))
    let kernel (pp : PublicParams G κ) (τ : Target pp) : ℝ :=
      ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)) fun ab =>
        ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)) fun rs =>
          ProbComp.expect (ProbComp.sample (ZMod pp.group.order)) fun t =>
            obs κ j pp τ.2.1 τ.2.2 (τ.1 * A0 κ pp ab)
              (Matrix.mulVec τ.1
                ![ab 0 * rs 0, ab 1 * rs 1, if real then rs 0 + rs 1 else t])
    -- Read the actual game and its preprocessor; the only casts are the public-order ones.
    have hRead :
        avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) real)) =
          avgTape κ (fun τ : Tape κ => ProbComp.expect (publicParamsGen G κ)
            (fun pp => kernel pp (tapeEquiv pp τ))) := ?_
    swap
    · dsimp only [avgTape, redGame, kernel, tapeEquiv, castMatrix]
      simp only [accept_eq, G.dlinSample_eq, ProbComp.prob_bind,
        ProbComp.expect_bind, ProbComp.expect_pure, ProbComp.prob_pure,
        G.mddhPre_eq, hPreScalar, obs, ProbComp.prob_eq_expect]
      all_goals rfl
    -- The advice law is independent of pp, so Fubini precedes the pointwise equivalence.
    rw [hRead]
    dsimp only [avgTape]
    rw [← ProbComp.expect_expect_sample (publicParamsGen G κ) (Tape κ)
      (fun pp τ => kernel pp (tapeEquiv pp τ))]
    apply congrArg (ProbComp.expect (publicParamsGen G κ))
    funext pp
    rw [ProbComp.expect_sample_equiv (tapeEquiv pp) (kernel pp)]
    -- Split the uniform product, retaining each entire matrix and every unused coordinate.
    dsimp only [Target]
    rw [← Bridge.expect_sample_pair
      (α := Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod pp.group.order))
      (β := SType κ pp × UType κ pp) (kernel pp)]
    simp only [ProbComp.expect_bind, ProbComp.expect_pure,
      ← Bridge.expect_sample_pair (α := SType κ pp) (β := UType κ pp)]
    dsimp only [planted]
    rw [ProbComp.expect_sample_comm]
    apply congrArg (ProbComp.expect (ProbComp.sample (SType κ pp)))
    funext S
    rw [ProbComp.expect_sample_comm]
    apply congrArg (ProbComp.expect (ProbComp.sample (UType κ pp)))
    funext U
    -- Move L inside ab, rs and t using the same published independent-sample law.
    dsimp only [kernel, plantedCore]
    rw [ProbComp.expect_sample_comm]
    apply congrArg
      (ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)))
    funext ab
    rw [ProbComp.expect_sample_comm]
    apply congrArg
      (ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order)))
    funext rs
    exact ProbComp.expect_sample_comm (fun L t =>
      obs κ j pp S U (L * A0 κ pp ab)
        (Matrix.mulVec L
          ![ab 0 * rs 0, ab 1 * rs 1, if real then rs 0 + rs 1 else t]))
  -- Transpose the relevant matrix to whole columns and use the published coordinate
  -- resampling law: S's selected column when real, U's selected column otherwise.
  have hHybridResample : ∀ (κ : ℕ) (j : Fin (d.eval κ)) (real : Bool),
      accept (hybrid κ (j.val + (if real then 1 else 0))) =
        ProbComp.expect (publicParamsGen G κ) (ideal κ j real) := by
    intro κ j real
    -- Isolate just the actual-game/conditional-matrix read from uniform resampling.
    have hHybridRead : accept (hybrid κ (j.val + (if real then 1 else 0))) =
        ProbComp.expect (publicParamsGen G κ) (fun pp =>
          ProbComp.expect
            (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order)))
            (fun M => ProbComp.expect (ProbComp.sample (SType κ pp)) (fun S =>
              ProbComp.expect (ProbComp.sample (UType κ pp)) (fun U =>
                obs κ j pp S U M (if real then Matrix.mulVec M (fun a => S a j)
                  else fun a => U a j))))) := by
      dsimp only [hybrid]
      simp only [accept_eq, ProbComp.prob_bind, ProbComp.expect_bind,
        ProbComp.expect_pure, ProbComp.prob_pure]
      apply congrArg (ProbComp.expect (publicParamsGen G κ)); funext pp
      apply congrArg (ProbComp.expect
        (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2) (ZMod pp.group.order))))
      funext M
      apply congrArg (ProbComp.expect (ProbComp.sample (SType κ pp))); funext S
      apply congrArg (ProbComp.expect (ProbComp.sample (UType κ pp))); funext U
      dsimp only [obs]
      rw [ProbComp.prob_eq_expect]
      apply congrArg (ProbComp.expect (ProbComp.sample (D.Coins κ))); funext r
      apply congrArg (fun R :
          Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (ZMod pp.group.order) =>
        if D.distinguisherL κ (G.mddhEnc d ℓ κ
          ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator R⟩) r = true
        then (1 : ℝ) else 0)
      funext a b
      cases real with
      | false =>
        simp only [Bool.false_eq_true, if_false, Nat.add_zero]
        by_cases h : b.val = j.val
        · have hb : b = j := Fin.ext h
          subst b
          simp only [↓reduceIte, Nat.lt_irrefl]
        · simp only [if_neg h]
      | true =>
        simp only [↓reduceIte]
        by_cases h : b.val = j.val
        · have hb : b = j := Fin.ext h
          subst b
          simp only [Nat.lt_succ_self, if_true, if_pos rfl]
          exact Matrix.mul_apply'
        · have hCompare : b.val < j.val + 1 ↔ b.val < j.val := ?_
          swap
          · omega
          simp only [if_neg h, hCompare]
    rw [hHybridRead]
    apply congrArg (ProbComp.expect (publicParamsGen G κ)); funext pp
    let K : Type := ZMod pp.group.order
    let cols (m : ℕ) : Matrix (Fin m) (Fin (d.eval κ)) K ≃
        (Fin (d.eval κ) → Fin m → K) :=
      Equiv.piComm (fun (_ : Fin m) (_ : Fin (d.eval κ)) => K)
    -- The observer cannot see either mask's selected column.
    have hIgnore (S S' : SType κ pp) (U U' : UType κ pp)
        (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) K) (v : Fin (ℓ.eval κ) → K)
        (hS : ∀ a b, b.val ≠ j.val → S a b = S' a b)
        (hU : ∀ a b, b.val ≠ j.val → U a b = U' a b) :
        obs κ j pp S U M v = obs κ j pp S' U' M v := ?_
    swap
    · dsimp only [obs]
      apply congrArg (fun R : Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) K =>
        ProbComp.prob (ProbComp.sample (D.Coins κ)) (fun r =>
          D.distinguisherL κ (G.mddhEnc d ℓ κ
            ⟨pp, pp.group.expMat pp.generator M, pp.group.expMat pp.generator R⟩) r = true))
      funext a b
      split_ifs with hSel hPrior
      · rfl
      · rw [Matrix.mul_apply, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hS i b hSel]
      · exact hU a b hSel
    have hRealColumn (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) K) (U : UType κ pp) :
        ProbComp.expect (ProbComp.sample (SType κ pp))
            (fun S => obs κ j pp S U M (Matrix.mulVec M (fun a => S a j))) =
          ProbComp.expect (ProbComp.sample (SType κ pp)) (fun S =>
            ProbComp.expect (ProbComp.sample (Fin 2 → K))
              (fun rs => obs κ j pp S U M (Matrix.mulVec M rs))) := ?_
    swap
    · let F (rs : Fin 2 → K) (T : Fin (d.eval κ) → Fin 2 → K) : ℝ :=
        obs κ j pp ((cols 2).symm T) U M (Matrix.mulVec M rs)
      have hF : ∀ r r' T, F r (Function.update T j r') = F r T :=
        fun r r' T => hIgnore _ _ U U M (Matrix.mulVec M r)
          (fun a b hb => show Function.update T j r' b a = T b a from
            congrFun (Function.update_of_ne ((Fin.ne_iff_vne b j).mpr hb) r' T) a)
          (fun _ _ _ => rfl)
      have h := ProbComp.expect_sample_coord j F hF
      rw [ProbComp.expect_sample_comm F] at h
      exact (ProbComp.expect_sample_equiv (cols 2).symm
        (fun S : SType κ pp => obs κ j pp S U M
          (Matrix.mulVec M (fun a => S a j)))).symm.trans
        (h.trans (ProbComp.expect_sample_equiv (cols 2).symm
          (fun S : SType κ pp => ProbComp.expect (ProbComp.sample (Fin 2 → K))
            (fun rs => obs κ j pp S U M (Matrix.mulVec M rs)))))
    have hRandomColumn (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) K) (S : SType κ pp) :
        ProbComp.expect (ProbComp.sample (UType κ pp))
            (fun U => obs κ j pp S U M (fun a => U a j)) =
          ProbComp.expect (ProbComp.sample (UType κ pp)) (fun U =>
            ProbComp.expect (ProbComp.sample (Fin (ℓ.eval κ) → K))
              (fun v => obs κ j pp S U M v)) := ?_
    swap
    · let F (v : Fin (ℓ.eval κ) → K)
          (T : Fin (d.eval κ) → Fin (ℓ.eval κ) → K) : ℝ :=
        obs κ j pp S ((cols (ℓ.eval κ)).symm T) M v
      have hF : ∀ r r' T, F r (Function.update T j r') = F r T :=
        fun r r' T => hIgnore S S _ _ M r (fun _ _ _ => rfl)
          (fun a b hb => show Function.update T j r' b a = T b a from
            congrFun (Function.update_of_ne ((Fin.ne_iff_vne b j).mpr hb) r' T) a)
      have h := ProbComp.expect_sample_coord j F hF
      rw [ProbComp.expect_sample_comm F] at h
      exact (ProbComp.expect_sample_equiv (cols (ℓ.eval κ)).symm
        (fun U : UType κ pp => obs κ j pp S U M (fun a => U a j))).symm.trans
        (h.trans (ProbComp.expect_sample_equiv (cols (ℓ.eval κ)).symm
          (fun U : UType κ pp =>
            ProbComp.expect (ProbComp.sample (Fin (ℓ.eval κ) → K))
              (fun v => obs κ j pp S U M v))))
    have hResample (M : Matrix (Fin (ℓ.eval κ)) (Fin 2) K) :
        ProbComp.expect (ProbComp.sample (SType κ pp)) (fun S =>
          ProbComp.expect (ProbComp.sample (UType κ pp)) (fun U =>
            obs κ j pp S U M (if real then Matrix.mulVec M (fun a => S a j)
              else fun a => U a j))) =
          ProbComp.expect (ProbComp.sample (SType κ pp)) (fun S =>
            ProbComp.expect (ProbComp.sample (UType κ pp)) (fun U =>
              if real then ProbComp.expect (ProbComp.sample (Fin 2 → K))
                (fun rs => obs κ j pp S U M (Matrix.mulVec M rs))
              else ProbComp.expect (ProbComp.sample (Fin (ℓ.eval κ) → K))
                (fun v => obs κ j pp S U M v))) := ?_
    swap
    · cases real with
      | false =>
        simp only [Bool.false_eq_true, if_false]
        apply congrArg (ProbComp.expect (ProbComp.sample (SType κ pp))); funext S
        exact hRandomColumn M S
      | true =>
        simp only [↓reduceIte]
        rw [ProbComp.expect_sample_comm]
        conv_rhs => rw [ProbComp.expect_sample_comm]
        apply congrArg (ProbComp.expect (ProbComp.sample (UType κ pp))); funext U
        exact hRealColumn M U
    simp_rw [hResample]
    dsimp only [ideal, idealCore]
    rw [ProbComp.expect_sample_comm]
    apply congrArg (ProbComp.expect (ProbComp.sample (SType κ pp))); funext S
    rw [ProbComp.expect_sample_comm]
  -- Both canonical column laws consume this same bounded observer.
  have hCorePoint : ∀ (κ : ℕ) (j : Fin (d.eval κ)) (real : Bool)
      (pp : PublicParams G κ) (S : SType κ pp) (U : UType κ pp),
      |idealCore κ j real pp S U - plantedCore κ j real pp S U| ≤ coreLoss κ real := ?_
  swap
  · intro κ j real pp S U
    letI : Fact pp.group.order.Prime := ⟨pp.group.order_prime⟩
    letI : NeZero pp.group.order := ⟨pp.group.order_prime.ne_zero⟩
    have h0 : ∀ M v, 0 ≤ obs κ j pp S U M v :=
      fun M v => ProbComp.prob_nonneg (ProbComp.sample (D.Coins κ)) _
    have h1 : ∀ M v, obs κ j pp S U M v ≤ 1 :=
      fun M v => ProbComp.prob_le_one (ProbComp.sample (D.Coins κ)) _
    have hCard : Fintype.card (ZMod pp.group.order) = p κ :=
      (ZMod.card pp.group.order).trans (order_eq_of_publicParams G p hp κ pp)
    cases real with
    | false =>
      have h := dlin_random_column_gap_le (K := ZMod pp.group.order)
        (ℓ.eval κ) (obs κ j pp S U) h0 h1
      change |plantedCore κ j false pp S U - idealCore κ j false pp S U| ≤
        1 - (1 - 1 / (Fintype.card (ZMod pp.group.order) : ℝ)) ^ 3 at h
      rw [hCard] at h
      rw [abs_sub_comm]
      exact h
    | true =>
      -- Read the existing canonical real-vector identity, allowing arbitrary rs words.
      have hVector (ab rs : Fin 2 → ZMod pp.group.order) :
          Matrix.mulVec (A0 κ pp ab) rs =
            ![ab 0 * rs 0, ab 1 * rs 1, rs 0 + rs 1] := ?_
      swap
      · have hv := dlinMatrix_mulVec (ab 0) (ab 1) (rs 0) (rs 1)
        rw [dlinMatrix_eq] at hv
        have hrs : ![rs 0, rs 1] = rs :=
          funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
        exact (congrArg (Matrix.mulVec (A0 κ pp ab)) hrs).symm.trans hv
      -- The original t draw is independent and unused in this branch only.
      have hPlantedReal : plantedCore κ j true pp S U =
          ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order))
            (fun ab => ProbComp.expect (ProbComp.sample (Fin 2 → ZMod pp.group.order))
              (fun rs => ProbComp.expect
                (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 3) (ZMod pp.group.order)))
                (fun L => obs κ j pp S U (L * A0 κ pp ab)
                  (Matrix.mulVec L (Matrix.mulVec (A0 κ pp ab) rs))))) := ?_
      swap
      · dsimp only [plantedCore]
        simp only [↓reduceIte, ← hVector, ProbComp.expect_const]
      have h := dlin_real_column_gap_le (K := ZMod pp.group.order)
        (ℓ.eval κ) (obs κ j pp S U) h0 h1
      rw [hCard] at h
      rw [hPlantedReal, abs_sub_comm]
      exact h
  -- Average one common pointwise comparison over both untouched tape blocks and pp.
  have hClose : ∀ (κ : ℕ) (j : Fin (d.eval κ)) (real : Bool),
      |accept (hybrid κ (j.val + (if real then 1 else 0))) -
        avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) real))| ≤
          coreLoss κ real := ?_
  swap
  · intro κ j real
    rw [hHybridResample κ j real, hReductionTransport κ j real]
    apply ProbComp.abs_expect_sub_le (publicParamsGen G κ)
      (f := ideal κ j real) (g := planted κ j real)
    intro pp
    apply ProbComp.abs_expect_sub_le (ProbComp.sample (SType κ pp))
      (f := fun S => ProbComp.expect (ProbComp.sample (UType κ pp))
        (idealCore κ j real pp S))
      (g := fun S => ProbComp.expect (ProbComp.sample (UType κ pp))
        (plantedCore κ j real pp S))
    intro S
    exact ProbComp.abs_expect_sub_le (ProbComp.sample (UType κ pp))
      (f := idealCore κ j real pp S) (g := plantedCore κ j real pp S)
      (fun U => hCorePoint κ j real pp S U)
  have hRealClose : ∀ (κ : ℕ) (j : Fin (d.eval κ)),
      |accept (hybrid κ (j.val + 1)) -
        avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) true))| ≤
          1 / (p κ : ℝ) ^ 2 := fun κ j => hClose κ j true
  have hRandomClose : ∀ (κ : ℕ) (j : Fin (d.eval κ)),
      |accept (hybrid κ j.val) -
        avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) false))| ≤
          1 - (1 - 1 / (p κ : ℝ)) ^ 3 := fun κ j => hClose κ j false
  have hLossBudget : ∀ κ,
      1 / (p κ : ℝ) ^ 2 + (1 - (1 - 1 / (p κ : ℝ)) ^ 3) ≤
        4 / (p κ : ℝ) := by
    intro κ
    have hp1 : (1 : ℝ) ≤ (p κ : ℝ) :=
      Nat.one_le_cast.mpr ((Nat.le_add_right 1 1).trans
        (orderSchedule_prime G p hp κ).two_le)
    have hp0 : (0 : ℝ) < (p κ : ℝ) := lt_of_lt_of_le zero_lt_one hp1
    have hx0 : 0 ≤ 1 / (p κ : ℝ) := one_div_nonneg.mpr hp0.le
    have hx1 : 1 / (p κ : ℝ) ≤ 1 := (div_le_one hp0).mpr hp1
    have h3 : (1 / (p κ : ℝ)) ^ 3 ≤ (1 / (p κ : ℝ)) ^ 2 :=
      pow_le_pow_of_le_one hx0 hx1 (Nat.le_succ 2)
    simp only [div_eq_mul_inv, one_mul, ← inv_pow] at hx0 h3 ⊢
    nlinarith only [hx0, h3, sq_nonneg ((p κ : ℝ)⁻¹)]
  have hMeanComparison (κ : ℕ) (j : Fin (d.eval κ)) :
      advantage (hybrid κ j.val) (hybrid κ (j.val + 1)) ≤
        avgTape κ (fun τ : Tape κ => redGap κ (j.castSucc, τ)) + 4 / (p κ : ℝ) := ?_
  swap
  · letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
    let a0 := accept (hybrid κ j.val)
    let a1 := accept (hybrid κ (j.val + 1))
    let r0 := avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) false))
    let r1 := avgTape κ (fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) true))
    have hAvgGap : |r0 - r1| ≤
        avgTape κ (fun τ : Tape κ => redGap κ (j.castSucc, τ)) :=
      ProbComp.abs_expect_sub_le_expect (ProbComp.sample (Tape κ))
        (f := fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) false))
        (g := fun τ : Tape κ => accept (redGame κ (j.castSucc, τ) true))
        (h := fun τ : Tape κ => redGap κ (j.castSucc, τ))
        (fun τ => (advantage_eq (redGame κ (j.castSucc, τ) false)
          (redGame κ (j.castSucc, τ) true)).symm.le)
    have hC0 : |a0 - r0| ≤ 1 - (1 - 1 / (p κ : ℝ)) ^ 3 := hRandomClose κ j
    have hC1 : |a1 - r1| ≤ 1 / (p κ : ℝ) ^ 2 := hRealClose κ j
    rw [abs_sub_comm] at hC1
    have hTriangle0 := abs_sub_le a0 r0 a1
    have hTriangle1 := abs_sub_le r0 r1 a1
    rw [advantage_eq]
    change |a0 - a1| ≤
      avgTape κ (fun τ : Tape κ => redGap κ (j.castSucc, τ)) + 4 / (p κ : ℝ)
    linarith only [hTriangle0, hTriangle1, hC0, hC1, hAvgGap, hLossBudget κ]
  -- Select finite advice at each parameter before any realiser is introduced.
  have hPointwise : ∀ κ, ∃ w : MddhAdvice p d ℓ κ,
      G.mddhAdv d ℓ D κ ≤ (d.eval κ : ℝ) * redGap κ w + mddhSlack p d κ := ?_
  swap
  · intro κ
    letI : NeZero (p κ) := orderSchedule_neZero G p hp κ
    by_cases hd : d.eval κ = 0
    · refine ⟨mddhAdviceDefault p d ℓ κ, ?_⟩
      have hZero : G.mddhAdv d ℓ D κ = 0 := ?_
      swap
      · rw [hEndpointGap κ, hd, advantage_eq, sub_self, abs_zero]
      simpa only [hZero, mddhSlack_eq, hd, Nat.cast_zero, zero_mul, zero_add] using
        (le_refl (0 : ℝ))
    · have hdpos : 0 < d.eval κ := Nat.pos_of_ne_zero hd
      have hdR : 0 < (d.eval κ : ℝ) := Nat.cast_pos.mpr hdpos
      obtain ⟨j, hj, hgap⟩ := exists_advantage_hybrid_gap (hybrid κ) hdpos
      let i : Fin (d.eval κ) := ⟨j, hj⟩
      let f : Tape κ → ℝ := fun τ => redGap κ (i.castSucc, τ)
      obtain ⟨τ, hτ⟩ :=
        TCSlib.Cryptography.Authentication.LamportReduction.exists_expect_sample_le f
      refine ⟨(i.castSucc, τ), ?_⟩
      rw [← hEndpointGap κ] at hgap
      have hScaled : G.mddhAdv d ℓ D κ ≤
          (d.eval κ : ℝ) * advantage (hybrid κ i.val) (hybrid κ (i.val + 1)) := ?_
      swap
      · simpa only [mul_comm] using (div_le_iff₀ hdR).mp hgap
      have hPicked : avgTape κ f ≤ redGap κ (i.castSucc, τ) := hτ
      calc
        G.mddhAdv d ℓ D κ ≤
            (d.eval κ : ℝ) * advantage (hybrid κ i.val) (hybrid κ (i.val + 1)) := hScaled
        _ ≤ (d.eval κ : ℝ) * (avgTape κ f + 4 / (p κ : ℝ)) :=
          mul_le_mul_of_nonneg_left (hMeanComparison κ i) (Nat.cast_nonneg _)
        _ ≤ (d.eval κ : ℝ) * (redGap κ (i.castSucc, τ) + 4 / (p κ : ℝ)) :=
          mul_le_mul_of_nonneg_left (add_le_add_right hPicked (4 / (p κ : ℝ)))
            (Nat.cast_nonneg _)
        _ = (d.eval κ : ℝ) * redGap κ (i.castSucc, τ) + mddhSlack p d κ := ?_
      rw [mddhSlack_eq, mul_add]
  let ω : ∀ κ, MddhAdvice p d ℓ κ := fun κ => Classical.choose (hPointwise κ)
  have hω : ∀ κ,
      G.mddhAdv d ℓ D κ ≤ (d.eval κ : ℝ) * redGap κ (ω κ) + mddhSlack p d κ :=
    fun κ => Classical.choose_spec (hPointwise κ)
  refine ⟨ω, ?_⟩
  intro B hB κ
  -- This local coin identity reads the existing length-limited reduction; no machine is built.
  have hCoinUnwrap : ∀ (c : G.DLINChallenge κ) (ρ : B.Coins κ),
      decide (G.dlinToMddh p hp d ℓ D ω κ c (List.ofFn ρ) = [true]) =
        D.distinguisherL κ (G.mddhPre p hp d ℓ κ (ω κ) c)
          (NUPPT.coinsCongr (A := B) (B := D) hB.coins_eq κ ρ) := by
    intro c ρ
    have hLength : (List.ofFn ρ).length = D.coinLen κ :=
      (B.length_ofFn_coins κ ρ).trans
        ((congrArg (fun q : PolyExpr => q.eval κ) hB.coins_eq).trans
          (D.coinLen_eq κ).symm)
    rw [G.dlinToMddh_eq p hp d ℓ D ω κ c (List.ofFn ρ),
      D.distinguisherL_eq κ (G.mddhPre p hp d ℓ κ (ω κ) c)
        (NUPPT.coinsCongr (A := B) (B := D) hB.coins_eq κ ρ),
      NUPPT.runAt_coinsCongr (A := B) (B := D) hB.coins_eq κ
        (G.mddhPre p hp d ℓ κ (ω κ) c) ρ,
      List.take_of_length_le hLength.le]
  have hCoinVerdict (c : G.DLINChallenge κ) (ρ : B.Coins κ) :
      B.distinguisherL κ (G.dlinEnc κ c) ρ =
        D.distinguisherL κ (G.mddhPre p hp d ℓ κ (ω κ) c)
          (NUPPT.coinsCongr (A := B) (B := D) hB.coins_eq κ ρ) :=
    (hB.distinguisherL_eq κ c ρ).trans (hCoinUnwrap c ρ)
  have hAccept (real : Bool) :
      accept (G.dlinGame B real κ) = accept (redGame κ (ω κ) real) := ?_
  swap
  · rw [accept_eq (G.dlinGame B real κ), G.dlinGame_eq B real κ, ProbComp.prob_bind]
    dsimp only [redGame]
    rw [accept_eq, ProbComp.prob_bind]
    apply congrArg (ProbComp.expect (G.dlinSample real κ))
    funext c
    simp only [ProbComp.prob_bind, ProbComp.prob_pure]
    rw [← ProbComp.expect_sample_equiv (NUPPT.coinsCongr (A := B) (B := D) hB.coins_eq κ)
      (fun ρ : D.Coins κ =>
        if D.distinguisherL κ (G.mddhPre p hp d ℓ κ (ω κ) c) ρ = true
        then (1 : ℝ) else 0)]
    apply congrArg (ProbComp.expect (ProbComp.sample (B.Coins κ)))
    funext ρ
    rw [hCoinVerdict c ρ]
  have hGap : redGap κ (ω κ) = G.dlinAdv B κ := ?_
  swap
  · dsimp only [redGap]
    rw [G.dlinAdv_eq B κ, advantage_eq, advantage_eq, hAccept false, hAccept true]
  calc
    G.mddhAdv d ℓ D κ ≤ (d.eval κ : ℝ) * redGap κ (ω κ) + mddhSlack p d κ := hω κ
    _ = (d.eval κ : ℝ) * G.dlinAdv B κ + mddhSlack p d κ :=
      congrArg (fun x : ℝ => (d.eval κ : ℝ) * x + mddhSlack p d κ) hGap

/-- Realisability asks for one DLIN machine per fixed-advice reduction of a machine MDDH
adversary. This is the later machine-construction obligation, not an honest-algorithm
notion. The shared predicate constrains encoded challenges and layout-length coins only. -/
def MDDHRealizable (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) : Prop :=
  ∀ (D : NUPPT) (ω : ∀ κ, MddhAdvice p d ℓ κ), ∃ B : NUPPT,
    B.RealizesOn G.dlinEnc D.coins (G.dlinToMddh p hp d ℓ D ω)

/-- Matrix reduction realisability is exactly existence of a realiser for every machine and
advice family. -/
theorem mddhRealizable_iff (p : ℕ → ℕ) (hp : ∀ κ r, (G.inst κ r).order = p κ)
    (d ℓ : PolyExpr) :
    G.MDDHRealizable p hp d ℓ ↔
      ∀ (D : NUPPT) (ω : ∀ κ, MddhAdvice p d ℓ κ), ∃ B : NUPPT,
        B.RealizesOn G.dlinEnc D.coins (G.dlinToMddh p hp d ℓ D ω) := Iff.rfl

/-- The polynomial-over-order correction is subexponentially small at every exponent below
one when the prime schedule is at least `2^κ`. This uses the shared subexponential notion.

**Proof sketch.** Bound the correction by `4d(κ)2⁻κ`, use the polynomial growth bound for
`d`, and apply `subexpSmall_two_pow_neg`, `SubexpSmall.mul_pow`, `.const_mul` and `.mono`. -/
theorem mddhSlack_subexpSmall (p : ℕ → ℕ) (d : PolyExpr)
    (hpb : ∀ κ, 2 ^ κ ≤ p κ) {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) :
    SubexpSmall c (mddhSlack p d) :=
  Eq.mpr (congrArg (SubexpSmall c) (funext (mddhSlack_eq p d)))
    (mddhCorrection_subexpSmall p d hpb hc₀ hc₁)

/-- DLIN hardness implies uniform-matrix MDDH negligibility once the fixed-advice reduction
functions have machine realisers [Wee20, §2.1, p. 4].

**Proof sketch.** Choose the single advice family and its realiser. Apply
`EnsembleLemmas.negligible_polyExpr_mul` to the realiser's DLIN advantage. The explicit
correction is negligible by `mddhSlack_subexpSmall` and `SubexpSmall.negligible`; finish by
`Negligible.add` and `.mono`. -/
theorem mddhAdv_negligible (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr)
    (hpb : ∀ κ, 2 ^ κ ≤ p κ) (hR : G.MDDHRealizable p hp d ℓ)
    (h : G.DLINAssumption) (D : NUPPT) : Negligible (G.mddhAdv d ℓ D) :=
  G.mddh_negligible_of_adv_le d ℓ _ ((mddhSlack_subexpSmall p d hpb
    (half_pos zero_lt_one) (half_lt_self zero_lt_one)).negligible (half_pos zero_lt_one))
    (fun E => let ⟨ω, hω⟩ := G.mddhAdv_le p hp d ℓ E
      let ⟨B, hB⟩ := ((G.mddhRealizable_iff p hp d ℓ).mp hR) E ω
      ⟨B, hω B hB⟩) h D

/-- Subexponential DLIN implies subexponential MDDH for every fixed polynomial dimension
pair, under reduction realisability [Wee20, §2.1, p. 4; JLS26, §1.1, p. 3].

**Proof sketch.** Take a smaller positive exponent than the shared DLIN exponent and one.
The fixed polynomial hybrid factor is absorbed by `.mul_pow`, `.const_mul` and `.mono`.
Combine with `mddhSlack_subexpSmall` through `.add`; the exponent is independent of `D`. -/
theorem mddh_subexpHard (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr)
    (hpb : ∀ κ, 2 ^ κ ≤ p κ) (hR : G.MDDHRealizable p hp d ℓ)
    (h : G.SubexpDLIN) : SubexpHard (G.mddhAdv d ℓ) :=
  G.mddh_subexpHard_of_adv_le d ℓ _ (fun c hc₀ hc₁ =>
    mddhSlack_subexpSmall p d hpb (c := c) hc₀ hc₁)
    (fun D => let ⟨ω, hω⟩ := G.mddhAdv_le p hp d ℓ D
      let ⟨B, hB⟩ := ((G.mddhRealizable_iff p hp d ℓ).mp hR) D ω
      ⟨B, hω B hB⟩) h
end BilinearGen

end TCSlib.Cryptography.Pairing
