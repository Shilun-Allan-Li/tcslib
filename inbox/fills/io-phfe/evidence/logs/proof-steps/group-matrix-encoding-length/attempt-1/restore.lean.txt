/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Linear

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform-matrix decisional Diffie–Hellman experiments

The matrix assumption uses a uniform matrix with two columns. Its real response is its
product with an independent uniform coefficient matrix; its random response is a fully
uniform matrix. Public parameters are generated sequentially before all field-dependent
draws. The source group is symmetric and the matrix width is fixed at two.

## Main definitions

* `BilinearGroup.groupMatrixEnc`: row-major fixed-width encoding of source-group matrices.
* `BilinearGen.MDDHChallenge`, `BilinearGen.mddhEnc`: typed public matrix challenges and
  their public encoding.
* `BilinearGen.mddhSample`, `BilinearGen.mddhGame`, `BilinearGen.mddhAdv`: exact challenge
  law, experiment and two-experiment advantage.

## Main results

* `BilinearGen.mddhEnc_injective`, `BilinearGen.length_mddhEnc`: faithful public encoding
  and its fixed length.
* `BilinearGen.mddhAdv_smallRows_le`: when there are at most two rows, security is
  statistical, with an explicit rank-deficiency bound.

The coefficient-column and row dimensions are polynomial expressions and may evaluate to
zero. In particular, no nonempty-row or positive-column condition is required for the game.
Uniform sampling is only used to specify the exact laws; no coin sampler is constructed.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, §2.1, p. 4, Assumption 1.
-/

namespace TCSlib.Cryptography.Pairing

open Complexity Turing TCSlib.Cryptography.Games

namespace BilinearGroup

variable {wG wT rows cols : ℕ} (B : BilinearGroup wG wT)

/-- Encode a source-group matrix row by row using the group's fixed-width point encoding.
This is serialization glue for the implicit matrices of [Wee20, §2.1, p. 4]. -/
def groupMatrixEnc (M : Matrix (Fin rows) (Fin cols) B.G) : List Bool :=
  (List.ofFn fun i => (List.ofFn fun j => List.ofFn (B.encG (M i j))).flatten).flatten

/-- The group-matrix word concatenates the encoded entries, with rows and columns increasing. -/
theorem groupMatrixEnc_eq (M : Matrix (Fin rows) (Fin cols) B.G) :
    B.groupMatrixEnc M =
      (List.ofFn fun i => (List.ofFn fun j => List.ofFn (B.encG (M i j))).flatten).flatten := rfl

/-- A source-group matrix has one fixed-width block per entry. Serialization glue.

**Proof sketch.** Apply `List.length_flatten` and `List.length_ofFn` to both concatenations;
every point block has length `wG`. -/
theorem length_groupMatrixEnc (M : Matrix (Fin rows) (Fin cols) B.G) :
    (B.groupMatrixEnc M).length = rows * cols * wG := sorry

/-- Group-matrix serialization is injective, including empty dimensions. Serialization glue.

**Proof sketch.** Split equal concatenations into fixed-width rows and then point blocks,
using their known lengths. Apply `List.ofFn_injective` and `B.encG_injective` entrywise. -/
theorem groupMatrixEnc_injective :
    Function.Injective (B.groupMatrixEnc (rows := rows) (cols := cols)) := sorry

end BilinearGroup

namespace BilinearGen

variable (G : BilinearGen)

/-- An MDDH challenge contains shared public parameters, the two-column base matrix and its
response matrix [Wee20, §2.1, p. 4, Assumption 1]. Private scalar witnesses are not stored. -/
structure MDDHChallenge (d ℓ : PolyExpr) (κ : ℕ) where
  /-- The common public description and source-group generator. -/
  pp : PublicParams G κ
  /-- The implicit base matrix with exactly two columns. -/
  matrix : Matrix (Fin (ℓ.eval κ)) (Fin 2) (G.group κ pp.description.val).G
  /-- The implicit response with `d(κ)` columns. -/
  response : Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ)) (G.group κ pp.description.val).G

/-- Serialize the public parameters followed by the base and response matrices
[Wee20, §2.1, p. 4, Assumption 1]. The encoding contains no group-generator coin strings. -/
def mddhEnc (d ℓ : PolyExpr) (κ : ℕ) (c : G.MDDHChallenge d ℓ κ) : List Bool :=
  pairEncode c.pp.encode
    (pairEncode ((G.group κ c.pp.description.val).groupMatrixEnc c.matrix)
      ((G.group κ c.pp.description.val).groupMatrixEnc c.response))

/-- A public matrix challenge serializes as its parameters, base matrix and response matrix. -/
theorem mddhEnc_eq (d ℓ : PolyExpr) (κ : ℕ) (c : G.MDDHChallenge d ℓ κ) :
    G.mddhEnc d ℓ κ c =
      pairEncode c.pp.encode
        (pairEncode ((G.group κ c.pp.description.val).groupMatrixEnc c.matrix)
          ((G.group κ c.pp.description.val).groupMatrixEnc c.response)) := rfl

/-- Matrix-challenge encoding is injective on reachable public challenges. Serialization glue.

**Proof sketch.** Use `pairEncode_injective` to separate public parameters and matrix words.
Read the shared public encoding and apply `encG_injective` to its generator; description
reachability witnesses are propositions. Then use `groupMatrixEnc_injective` twice. -/
theorem mddhEnc_injective (d ℓ : PolyExpr) (κ : ℕ) :
    Function.Injective (G.mddhEnc d ℓ κ) := sorry

/-- The matrix-challenge word has a fixed polynomial length. Serialization glue.

**Proof sketch.** Use the shared public encoding reader, `length_pairEncode`,
`length_groupMatrixEnc`, and `length_desc` from the description's reachability witness. -/
theorem length_mddhEnc (d ℓ : PolyExpr) (κ : ℕ) (c : G.MDDHChallenge d ℓ κ) :
    (G.mddhEnc d ℓ κ c).length =
      4 * G.descLen.eval κ + (2 + 4 * ℓ.eval κ + ℓ.eval κ * d.eval κ) * G.wG.eval κ + 8 :=
  sorry

/-- Sample a uniform two-column matrix `M`, an independent coefficient matrix `S`, and a
uniform response matrix `U`, after generating the public group parameters. Return `[M]`
with `[MS]` in the real branch and `[U]` in the random branch
[Wee20, §2.1, p. 4, Assumption 1, with k=2]. -/
noncomputable def mddhSample (d ℓ : PolyExpr) (real : Bool) (κ : ℕ) :
    ProbComp (G.MDDHChallenge d ℓ κ) :=
  (publicParamsGen G κ).bind fun pp =>
  (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2)
    (ZMod (G.group κ pp.description.val).order))).bind fun M =>
  (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ))
    (ZMod (G.group κ pp.description.val).order))).bind fun S =>
  (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ))
    (ZMod (G.group κ pp.description.val).order))).bind fun U =>
    .pure ⟨pp, (G.group κ pp.description.val).expMat pp.generator M,
      (G.group κ pp.description.val).expMat pp.generator (if real then M * S else U)⟩

/-- The MDDH sampling law is the displayed sequence of dependent public and uniform scalar
matrix draws. -/
theorem mddhSample_eq (d ℓ : PolyExpr) (real : Bool) (κ : ℕ) :
    G.mddhSample d ℓ real κ =
      (publicParamsGen G κ).bind fun pp =>
      (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin 2)
        (ZMod (G.group κ pp.description.val).order))).bind fun M =>
      (ProbComp.sample (Matrix (Fin 2) (Fin (d.eval κ))
        (ZMod (G.group κ pp.description.val).order))).bind fun S =>
      (ProbComp.sample (Matrix (Fin (ℓ.eval κ)) (Fin (d.eval κ))
        (ZMod (G.group κ pp.description.val).order))).bind fun U =>
        .pure ⟨pp, (G.group κ pp.description.val).expMat pp.generator M,
          (G.group κ pp.description.val).expMat pp.generator (if real then M * S else U)⟩ := rfl

/-- Run a non-uniform PPT distinguisher on the encoded MDDH challenge with independent
machine coins [Wee20, §2.1, p. 4, Assumption 1]. -/
noncomputable def mddhGame (d ℓ : PolyExpr) (D : NUPPT) (real : Bool) (κ : ℕ) :
    ProbComp Bool :=
  (G.mddhSample d ℓ real κ).bind fun c =>
  (ProbComp.sample (D.Coins κ)).bind fun r =>
    .pure (D.distinguisherL κ (G.mddhEnc d ℓ κ c) r)

/-- The MDDH game draws a challenge and independent distinguisher coins. -/
theorem mddhGame_eq (d ℓ : PolyExpr) (D : NUPPT) (real : Bool) (κ : ℕ) :
    G.mddhGame d ℓ D real κ =
      (G.mddhSample d ℓ real κ).bind fun c =>
      (ProbComp.sample (D.Coins κ)).bind fun r =>
        .pure (D.distinguisherL κ (G.mddhEnc d ℓ κ c) r) := rfl

/-- The uniform-matrix MDDH advantage is the absolute difference of acceptance probabilities
[Wee20, §2.1, p. 4, Assumption 1]. -/
noncomputable def mddhAdv (d ℓ : PolyExpr) (D : NUPPT) (κ : ℕ) : ℝ :=
  advantage (G.mddhGame d ℓ D false κ) (G.mddhGame d ℓ D true κ)

/-- MDDH uses the library's two-experiment advantage. -/
theorem mddhAdv_eq (d ℓ : PolyExpr) (D : NUPPT) (κ : ℕ) :
    G.mddhAdv d ℓ D κ =
      advantage (G.mddhGame d ℓ D false κ) (G.mddhGame d ℓ D true κ) := rfl

/-- With at most two rows the matrix assumption is statistical, with the explicit
rank-deficiency bound averaged over the public group draw
[Wee20, §2.1, p. 4, paragraph after Assumption 1].

**Proof sketch.** Condition on the uniform base matrix having full row rank. Then its map
from two scalar coordinates onto the row space is surjective and sends uniform independent
coefficient columns to uniform response columns. The failure probability for zero, one,
or two rows is at most `2/p`; bound the distinguisher's gap by that event probability. -/
theorem mddhAdv_smallRows_le (d ℓ : PolyExpr) (D : NUPPT)
    (hℓ : ∀ κ, ℓ.eval κ ≤ 2) (κ : ℕ) :
    G.mddhAdv d ℓ D κ ≤
      ProbComp.expect (ProbComp.sample (G.gen.Coins κ))
        (fun r => 2 / ((G.inst κ r).order : ℝ)) := sorry

end BilinearGen

end TCSlib.Cryptography.Pairing
