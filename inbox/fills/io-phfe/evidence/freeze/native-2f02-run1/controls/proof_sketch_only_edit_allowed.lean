/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Raw
import TCSlib.Cryptography.Encoding.ModularDecode
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial classes for partially hiding functional encryption

A coefficient tensor represents public-input polynomials of degree at most d by
padding the public input with 1. Its tuple coordinates use the published explicit
base-(l+1) equivalence. The two private-input classes are [GJLS21, §9, pp.57–58]
and [Wee20, §3, p.6], restricted to these polynomial vectors.

All wire words are interpreted modulo the supplied positive modulus. The modular
parser is reused at the word modulus 2^w, where every width-w chunk is canonical;
its representatives are then cast into the supplied modulus. No word is rejected
merely because its integer representative is at least the supplied modulus.

## Main definitions

* `PolyTensor`, `polyTensorEval`: padded coefficient tensors and their evaluation.
* `decodeResidues`, `decodeTensor`, `encodeTensor`: canonical wire interpretation.
* `phfeClass`, `quadClass`: the two classes, with positive modulus as class parameter.
* `BidegreeAtMost`: monomial-wise bounds on public and private degrees.

## Main results

* `decodeResidues_parse`, `decodeResidues_apply`: total modular interpretation.
* `decodeTensor_encodeTensorBits`: tensor round trip under width coverage.
* `phfeClass_eval_eq_quad`: the embedding by duplicating the private input.
* `pad_one`: every polynomial of public degree at most d and private degree at most
  two is represented after padding the private input with 1.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, ePrint 2020/764, §9, printed pp.57–58.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, ePrint 2020/1420, §3, p.6.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open Complexity Turing
open TCSlib.Cryptography.NumberTheory (listToNat)

/-- A degree-d polynomial vector is represented by coefficients on padded tuples.
[GJLS21, §9, pp.57–58; Wee20, §3, p.6]. The representation uses ordered tuples
rather than monomials, with the padded constant accounting for smaller degrees. -/
abbrev PolyTensor (p : ℕ+) (l n d : ℕ) : Type :=
  Fin n → (Fin d → Fin (l + 1)) → ZMod (p : ℕ)

/-- A coefficient tensor has one residue for each output and padded monomial tuple. -/
theorem polyTensor_eq (p : ℕ+) (l n d : ℕ) :
    PolyTensor p l n d = (Fin n → (Fin d → Fin (l + 1)) → ZMod (p : ℕ)) := rfl

/-- The padded public input appends the constant 1, so tuples of fixed length d
can represent every smaller public degree. [GJLS21, §9, pp.57–58]. -/
def xhat {p : ℕ+} {l : ℕ} (x : Fin l → ZMod (p : ℕ)) :
    Fin (l + 1) → ZMod (p : ℕ) := Fin.snoc x 1

/-- Public-input padding is exactly `Fin.snoc x 1`. -/
theorem xhat_eq {p : ℕ+} {l : ℕ} (x : Fin l → ZMod (p : ℕ)) :
    xhat x = Fin.snoc x 1 := rfl

/-- Padding preserves each public-input coordinate. -/
theorem xhat_castSucc {p : ℕ+} {l : ℕ} (x : Fin l → ZMod (p : ℕ)) (i : Fin l) :
    xhat x i.castSucc = x i := Fin.snoc_castSucc (α := fun _ => ZMod (p : ℕ)) 1 x i

/-- The final padded public-input coordinate equals 1. -/
theorem xhat_last {p : ℕ+} {l : ℕ} (x : Fin l → ZMod (p : ℕ)) :
    xhat x (Fin.last l) = 1 := Fin.snoc_last (α := fun _ => ZMod (p : ℕ)) 1 x

/-- Tensor evaluation sums each coefficient times its padded public monomial.
[GJLS21, §9, pp.57–58; Wee20, §3, p.6]. -/
def polyTensorEval {p : ℕ+} {l n d : ℕ} (C : PolyTensor p l n d)
    (x : Fin l → ZMod (p : ℕ)) : Fin n → ZMod (p : ℕ) :=
  fun j => ∑ tau : Fin d → Fin (l + 1), C j tau * ∏ i : Fin d, xhat x (tau i)

/-- Tensor evaluation is the displayed sum over padded tuples. -/
theorem polyTensorEval_eq {p : ℕ+} {l n d : ℕ} (C : PolyTensor p l n d)
    (x : Fin l → ZMod (p : ℕ)) (j : Fin n) :
    polyTensorEval C x j =
      ∑ tau : Fin d → Fin (l + 1), C j tau * ∏ i : Fin d, xhat x (tau i) := rfl

/-- Padded monomial tuples have the explicit base-(l+1) coordinate ordering
provided by `finFunctionFinEquiv`; no arbitrary finite-type enumeration is chosen. -/
def tupleCoord (l d : ℕ) : (Fin d → Fin (l + 1)) ≃ Fin ((l + 1) ^ d) :=
  finFunctionFinEquiv

/-- Tuple coordinates use the published finite-function equivalence. -/
theorem tupleCoord_eq (l d : ℕ) : tupleCoord l d = finFunctionFinEquiv := rfl

/-- Parse a fixed-length residue word at its word modulus and cast each resulting
integer into the supplied positive modulus. The explicit zero fallback is
unreachable by `decodeResidues_parse`. This is total modular decoding glue. -/
def decodeResidues (p : ℕ+) (count width : ℕ)
    (word : Fin (count * width) → Bool) : Fin count → ZMod (p : ℕ) :=
  fun i => ((((Encoding.Modular.decodeVector (q := 2 ^ width) (length := count)
    width (List.ofFn word)).getD 0) i).val : ZMod (p : ℕ))

/-- Residue decoding is the word-modulus parser followed by representative casting,
with the displayed explicit fallback. -/
theorem decodeResidues_eq (p : ℕ+) (count width : ℕ)
    (word : Fin (count * width) → Bool) :
    decodeResidues p count width word = fun i =>
      ((((Encoding.Modular.decodeVector (q := 2 ^ width) (length := count)
        width (List.ofFn word)).getD 0) i).val : ZMod (p : ℕ)) := rfl

/-- Every fixed-length word passes the word-modulus parser: each width-bit block
is less than 2^width. In particular the decoding fallback is never used.

**Proof sketch.** Zhe vector length is `List.length_ofFn`; a taken block has at
most width bits. Apply the existing integer bound `listToNat_lt_two_pow`, then
monotonicity of powers, and use the published parser equation to open its guard. -/
theorem decodeResidues_parse (count width : ℕ) (word : Fin (count * width) → Bool) :
    Encoding.Modular.decodeVector (q := 2 ^ width) (length := count) width
        (List.ofFn word) =
      some (fun i : Fin count =>
        (listToNat (((List.ofFn word).drop (i.val * width)).take width) : ZMod (2 ^ width))) :=
  (Encoding.Modular.decodeVector_eq width (List.ofFn word)).trans
    (if_pos ⟨List.length_ofFn, fun i =>
      lt_of_lt_of_le (Candidates.listToNat_lt_two_pow _)
        (Nat.pow_le_pow_right (Nat.succ_pos 1) (List.length_take_le _ _))⟩)

/-- Each decoded residue is the integer represented by its block, reduced modulo
p. This reader explicitly rules out rejection of representatives at least p. -/
theorem decodeResidues_apply (p : ℕ+) (count width : ℕ)
    (word : Fin (count * width) → Bool) (i : Fin count) :
    decodeResidues p count width word i =
      (listToNat (((List.ofFn word).drop (i.val * width)).take width) : ZMod (p : ℕ)) :=
  (congrArg
      (fun o : Option (Fin count → ZMod (2 ^ width)) =>
        (((o.getD 0) i).val : ZMod (p : ℕ)))
      (decodeResidues_parse count width word)).trans
    (congrArg (fun a : ℕ => (a : ZMod (p : ℕ)))
      (ZMod.val_cast_of_lt (lt_of_lt_of_le (Candidates.listToNat_lt_two_pow _)
        (Nat.pow_le_pow_right (Nat.succ_pos 1) (List.length_take_le _ _)))))

/-- Equal modulus values give the same decoded residues after the natural cast.
This is the reader used when replacing a drawn order by a fixed prime schedule.

**Proof sketch.** Positive naturals with the same value are equal. Substitute
that equality and use the residue representative casting identity coordinatewise. -/
theorem decodeResidues_modulus (p q : ℕ+) (hpq : (p : ℕ) = (q : ℕ)) (count width : ℕ)
    (word : Fin (count * width) → Bool) :
    (fun i => ((decodeResidues p count width word i).val : ZMod (q : ℕ))) =
      decodeResidues q count width word := sorry

/-- Total decoding inverts a canonical vector encoding when its residues fit.

**Proof sketch.** Reinterpret the same integer representatives at the word
modulus, use the published modular-vector round trip, then cast each representative
back into p. The width hypothesis prevents any truncation of an original residue. -/
theorem decodeResidues_encodeVector (p : ℕ+) (count width : ℕ)
    (hwidth : (p : ℕ) ≤ 2 ^ width) (v : Fin count → ZMod (p : ℕ))
    (word : Fin (count * width) → Bool)
    (hword : List.ofFn word = Encoding.Modular.encodeVector width v) :
    decodeResidues p count width word = v := sorry

/-- Encode a coefficient tensor as a row-major modular matrix using the explicit
padded-tuple ordering. This reuses the published modular matrix encoder. -/
def encodeTensor {p : ℕ+} {l n d : ℕ} (width : ℕ) (C : PolyTensor p l n d) : List Bool :=
  Encoding.Modular.encodeMatrix width (fun j k => C j ((tupleCoord l d).symm k))

/-- Tensor encoding is the displayed row-major matrix encoding. -/
theorem encodeTensor_eq {p : ℕ+} {l n d : ℕ} (width : ℕ) (C : PolyTensor p l n d) :
    encodeTensor width C =
      Encoding.Modular.encodeMatrix width (fun j k => C j ((tupleCoord l d).symm k)) := rfl

/-- A tensor encoding has exactly n(l+1)^d residue blocks of the supplied width. -/
theorem encodeTensor_length {p : ℕ+} {l n d : ℕ} (width : ℕ) (C : PolyTensor p l n d) :
    (encodeTensor width C).length = n * (l + 1) ^ d * width :=
  Encoding.Modular.encodeMatrix_length width (fun j k => C j ((tupleCoord l d).symm k))

/-- View the tensor's canonical encoding as a fixed-width bit vector. -/
def encodeTensorBits {p : ℕ+} {l n d : ℕ} (width : ℕ) (C : PolyTensor p l n d) :
    Fin (n * (l + 1) ^ d * width) → Bool :=
  fun i => (encodeTensor width C).getD i.val false

/-- Tensor bit encoding reads the corresponding position of the canonical word. -/
theorem encodeTensorBits_eq {p : ℕ+} {l n d : ℕ} (width : ℕ) (C : PolyTensor p l n d) :
    encodeTensorBits width C = fun i => (encodeTensor width C).getD i.val false := rfl

/-- Writing the fixed-width tensor bits gives exactly its canonical word.

**Proof sketch.** The encoder's length is already known. Apply the list reading
round trip at that length; no padding or truncation occurs at any finite index. -/
theorem ofFn_encodeTensorBits {p : ℕ+} {l n d : ℕ} (width : ℕ)
    (C : PolyTensor p l n d) : List.ofFn (encodeTensorBits width C) = encodeTensor width C :=
  sorry

/-- Decode a coefficient tensor by total modular vector decoding and the explicit
row/tuple finite-product coordinates. This is wire-representation glue. -/
def decodeTensor (p : ℕ+) (l n d width : ℕ)
    (word : Fin (n * (l + 1) ^ d * width) → Bool) : PolyTensor p l n d :=
  fun j tau => decodeResidues p (n * (l + 1) ^ d) width word
    (finProdFinEquiv (j, tupleCoord l d tau))

/-- Tensor decoding reads the residue at the output/tuple product coordinate. -/
theorem decodeTensor_eq (p : ℕ+) (l n d width : ℕ)
    (word : Fin (n * (l + 1) ^ d * width) → Bool) :
    decodeTensor p l n d width word = fun j tau =>
      decodeResidues p (n * (l + 1) ^ d) width word
        (finProdFinEquiv (j, tupleCoord l d tau)) := rfl

/-- Tensor decoding inverts its canonical encoding under width coverage.

**Proof sketch.** Use the row-major modular matrix round trip, the total modular
interpretation, and the explicit tuple equivalence's inverse laws coordinatewise. -/
theorem decodeTensor_encodeTensorBits {p : ℕ+} {l n d : ℕ} (width : ℕ)
    (hwidth : (p : ℕ) ≤ 2 ^ width) (C : PolyTensor p l n d) :
    decodeTensor p l n d width (encodeTensorBits width C) = C := sorry

/-- Fixed-width coefficient descriptions are injective when every residue fits.

**Proof sketch.** Apply the tensor decoder to equal descriptions and use its
round trip. This delegates the actual modular encoding argument to the published API. -/
theorem encodeTensorBits_injective {p : ℕ+} {l n d : ℕ} (width : ℕ)
    (hwidth : (p : ℕ) ≤ 2 ^ width) :
    Function.Injective (encodeTensorBits (p := p) (l := l) (n := n) (d := d) width) := sorry

/-- The private tensor is the Kronecker product z1 ⊗ z2 in row-major pair order.
[Wee20, §3, p.6]. -/
def privateTensor {p : ℕ+} {n1 n2 : ℕ} (z1 : Fin n1 → ZMod (p : ℕ))
    (z2 : Fin n2 → ZMod (p : ℕ)) : Fin (n1 * n2) → ZMod (p : ℕ) :=
  fun i => Matrix.kroneckerMap (fun a b => a * b)
    (fun (_ : Fin 1) j => z1 j) (fun (_ : Fin 1) j => z2 j)
    (0, 0) (finProdFinEquiv.symm i)

/-- The private tensor is the displayed flattened Kronecker product. -/
theorem privateTensor_eq {p : ℕ+} {n1 n2 : ℕ} (z1 : Fin n1 → ZMod (p : ℕ))
    (z2 : Fin n2 → ZMod (p : ℕ)) :
    privateTensor z1 z2 = fun i => Matrix.kroneckerMap (fun a b => a * b)
      (fun (_ : Fin 1) j => z1 j) (fun (_ : Fin 1) j => z2 j)
      (0, 0) (finProdFinEquiv.symm i) := rfl

/-- The quadratic class evaluates the private tensor against the polynomial vector.
[Wee20, §3, p.6]. Polynomial vectors are the fixed-degree subclass used here. -/
def quadEval {p : ℕ+} {l n1 n2 d : ℕ} (C : PolyTensor p l (n1 * n2) d)
    (x : Fin l → ZMod (p : ℕ)) (z1 : Fin n1 → ZMod (p : ℕ))
    (z2 : Fin n2 → ZMod (p : ℕ)) : ZMod (p : ℕ) :=
  dotProduct (privateTensor z1 z2) (polyTensorEval C x)

/-- Quadratic evaluation is the displayed dot product. -/
theorem quadEval_eq {p : ℕ+} {l n1 n2 d : ℕ} (C : PolyTensor p l (n1 * n2) d)
    (x : Fin l → ZMod (p : ℕ)) (z1 : Fin n1 → ZMod (p : ℕ))
    (z2 : Fin n2 → ZMod (p : ℕ)) :
    quadEval C x z1 z2 = dotProduct (privateTensor z1 z2) (polyTensorEval C x) := rfl

/-- The PHFE class is the quadratic class restricted to the diagonal private input.
[GJLS21, §9, pp.57–58; Wee20, §3, p.6]. -/
def phfeEval {p : ℕ+} {l n d : ℕ} (C : PolyTensor p l (n * n) d)
    (x : Fin l → ZMod (p : ℕ)) (y : Fin n → ZMod (p : ℕ)) : ZMod (p : ℕ) :=
  quadEval C x y y

/-- PHFE evaluation is quadratic evaluation at the duplicated private input. -/
theorem phfeEval_eq {p : ℕ+} {l n d : ℕ} (C : PolyTensor p l (n * n) d)
    (x : Fin l → ZMod (p : ℕ)) (y : Fin n → ZMod (p : ℕ)) :
    phfeEval C x y = quadEval C x y y := rfl

/-- PHFE evaluation has exactly the sum-of-quadratic-terms form required in §9.
[GJLS21, §9, pp.57–58].

**Proof sketch.** Reindex the flattened private tensor by finProdFinEquiv, then
commute scalar factors in each term. Reuse finite-product sum reindexing. -/
theorem phfeEval_sum {p : ℕ+} {l n d : ℕ} (C : PolyTensor p l (n * n) d)
    (x : Fin l → ZMod (p : ℕ)) (y : Fin n → ZMod (p : ℕ)) :
    phfeEval C x y = ∑ j : Fin n, ∑ k : Fin n,
      polyTensorEval C x (finProdFinEquiv (j, k)) * y j * y k := sorry

/-- The tensor-description width is n(l+1)^d residue blocks of width w. -/
def tensorFnLen (l n w : PolyExpr) (d : ℕ) : PolyExpr :=
  .mul (.mul n (.pow (.add l (PolyExpr.const 1)) d)) w

/-- The tensor-description width is the displayed polynomial expression. -/
theorem tensorFnLen_eq (l n w : PolyExpr) (d : ℕ) :
    tensorFnLen l n w d = .mul (.mul n (.pow (.add l (PolyExpr.const 1)) d)) w := rfl

/-- The coefficient-description polynomial evaluates to its numeric block width. -/
theorem tensorFnLen_eval (l n w : PolyExpr) (d kappa : ℕ) :
    (tensorFnLen l n w d).eval kappa =
      n.eval kappa * (l.eval kappa + 1) ^ d * w.eval kappa := rfl

/-- Encode a scalar allowed value as a singleton modular vector at the binary
width of the supplied modulus. This preserves the scalar simulator input. -/
def encodeScalar (p : ℕ+) (a : ZMod (p : ℕ)) : List Bool :=
  Encoding.Modular.encodeVector (Nat.size (p : ℕ)) (fun _ : Fin 1 => a)

/-- Scalar encoding is the published modular singleton-vector encoding. -/
theorem encodeScalar_eq (p : ℕ+) (a : ZMod (p : ℕ)) :
    encodeScalar p a =
      Encoding.Modular.encodeVector (Nat.size (p : ℕ)) (fun _ : Fin 1 => a) := rfl

/-- Scalar-value encoding is injective because Nat.size p covers every residue. -/
theorem encodeScalar_injective (p : ℕ+) : Function.Injective (encodeScalar p) :=
  fun _ _ h => congrFun
    ((Encoding.Modular.encodeVector_injective (Nat.size (p : ℕ))
      (Nat.le_of_lt (Nat.lt_size_self (p : ℕ)))) h) 0

/-- The PHFE wire class uses the positive modulus as parameter and returns scalar
values for later embedding into the target group. [GJLS21, §9, pp.57–58]. -/
def phfeClass (l n w : PolyExpr) (d : ℕ) : FnClass where
  pubLen := .mul l w
  privLen := .mul n w
  fnLen := tensorFnLen l (.mul n n) w d
  Prm := fun _ => ℕ+
  Out := fun _ p => ZMod (p : ℕ)
  encValue := fun _ p => encodeScalar p
  encValue_injective := fun _ p => encodeScalar_injective p
  eval := fun kappa p f x y =>
    phfeEval (decodeTensor p (l.eval kappa) (n.eval kappa * n.eval kappa) d (w.eval kappa) f)
      (decodeResidues p (l.eval kappa) (w.eval kappa) x)
      (decodeResidues p (n.eval kappa) (w.eval kappa) y)

/-- The PHFE class has the displayed polynomial wire widths. -/
theorem phfeClass_pubLen (l n w : PolyExpr) (d : ℕ) :
    (phfeClass l n w d).pubLen = .mul l w := rfl

/-- The PHFE private input contains n residue blocks. -/
theorem phfeClass_privLen (l n w : PolyExpr) (d : ℕ) :
    (phfeClass l n w d).privLen = .mul n w := rfl

/-- The PHFE function description has one tensor coefficient for each private pair. -/
theorem phfeClass_fnLen (l n w : PolyExpr) (d : ℕ) :
    (phfeClass l n w d).fnLen = tensorFnLen l (.mul n n) w d := rfl

/-- The PHFE class parameter is any positive modulus. -/
theorem phfeClass_Prm (l n w : PolyExpr) (d kappa : ℕ) :
    (phfeClass l n w d).Prm kappa = ℕ+ := rfl

/-- The PHFE class returns residues at the supplied modulus. -/
theorem phfeClass_Out (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+) :
    (phfeClass l n w d).Out kappa p = ZMod (p : ℕ) := rfl

/-- PHFE scalar simulator values use the lossless modulus-dependent scalar encoding. -/
theorem phfeClass_encValue (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (a : ZMod (p : ℕ)) :
    (phfeClass l n w d).encValue kappa p a = encodeScalar p a := rfl

/-- The PHFE wire evaluation is the displayed tensor evaluation of decoded words. -/
theorem phfeClass_eval (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (f : Fin ((tensorFnLen l (.mul n n) w d).eval kappa) → Bool)
    (x : Fin (l.eval kappa * w.eval kappa) → Bool)
    (y : Fin (n.eval kappa * w.eval kappa) → Bool) :
    (phfeClass l n w d).eval kappa p f x y =
      phfeEval (decodeTensor p (l.eval kappa) (n.eval kappa * n.eval kappa) d (w.eval kappa) f)
        (decodeResidues p (l.eval kappa) (w.eval kappa) x)
        (decodeResidues p (n.eval kappa) (w.eval kappa) y) := rfl

/-- The PHFE class parameter is transported explicitly to its positive modulus.
This codec avoids unfolding the class bundle in foreign scheme constructions. -/
def phfeClassParamEquiv (l n w : PolyExpr) (d kappa : ℕ) :
    (phfeClass l n w d).Prm kappa ≃ ℕ+ := Equiv.refl _

/-- The PHFE parameter codec is internally the identity equivalence. -/
theorem phfeClassParamEquiv_eq (l n w : PolyExpr) (d kappa : ℕ) :
    phfeClassParamEquiv l n w d kappa = Equiv.refl ℕ+ := rfl

/-- Encoding then decoding a PHFE parameter recovers the supplied modulus. -/
theorem phfeClassParamEquiv_apply_symm (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+) :
    phfeClassParamEquiv l n w d kappa ((phfeClassParamEquiv l n w d kappa).symm p) = p :=
  (phfeClassParamEquiv l n w d kappa).apply_symm_apply p

/-- The PHFE value codec preserves the scalar at its explicitly encoded modulus. -/
def phfeClassValueEquiv (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+) :
    (phfeClass l n w d).Out kappa ((phfeClassParamEquiv l n w d kappa).symm p) ≃
      ZMod (p : ℕ) := Equiv.refl _

/-- The PHFE scalar-value codec is internally the identity equivalence. -/
theorem phfeClassValueEquiv_eq (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+) :
    phfeClassValueEquiv l n w d kappa p = Equiv.refl (ZMod (p : ℕ)) := rfl

/-- Encoding then decoding a PHFE scalar preserves the scalar value. -/
theorem phfeClassValueEquiv_apply_symm (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (a : ZMod (p : ℕ)) :
    phfeClassValueEquiv l n w d kappa p
      ((phfeClassValueEquiv l n w d kappa p).symm a) = a :=
  (phfeClassValueEquiv l n w d kappa p).apply_symm_apply a

/-- Encoding a packaged PHFE scalar gives the canonical residue encoding. -/
theorem phfeClass_encValue_codec (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (a : ZMod (p : ℕ)) :
    (phfeClass l n w d).encValue kappa ((phfeClassParamEquiv l n w d kappa).symm p)
      ((phfeClassValueEquiv l n w d kappa p).symm a) = encodeScalar p a := rfl

/-- Canonical encoded inputs realize the intended typed PHFE evaluation whenever
every residue fits in the public word width. [GJLS21, §9, pp.57–58].

**Proof sketch.** Read phfeClass_eval, apply the tensor encoding round trip and
the two total vector-decoding round trips, then identify the typed evaluation.
The width assumption is needed for representation completeness, not for totality. -/
theorem phfeClass_eval_encoded (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (hwidth : (p : ℕ) ≤ 2 ^ w.eval kappa)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa * n.eval kappa) d)
    (x : Fin (l.eval kappa) → ZMod (p : ℕ))
    (y : Fin (n.eval kappa) → ZMod (p : ℕ))
    (xword : Fin (l.eval kappa * w.eval kappa) → Bool)
    (yword : Fin (n.eval kappa * w.eval kappa) → Bool)
    (hx : List.ofFn xword = Encoding.Modular.encodeVector (w.eval kappa) x)
    (hy : List.ofFn yword = Encoding.Modular.encodeVector (w.eval kappa) y) :
    (phfeClass l n w d).eval kappa p (encodeTensorBits (w.eval kappa) C) xword yword =
      phfeEval C x y := sorry

/-- The quadratic wire class permits two independently sized private vectors.
[Wee20, §3, p.6]. Scalar outputs remain unembedded at the function-class layer. -/
def quadClass (l n1 n2 w : PolyExpr) (d : ℕ) : FnClass where
  pubLen := .mul l w
  privLen := .mul (.add n1 n2) w
  fnLen := tensorFnLen l (.mul n1 n2) w d
  Prm := fun _ => ℕ+
  Out := fun _ p => ZMod (p : ℕ)
  encValue := fun _ p => encodeScalar p
  encValue_injective := fun _ p => encodeScalar_injective p
  eval := fun kappa p f x z =>
    let privateValues := decodeResidues p (n1.eval kappa + n2.eval kappa) (w.eval kappa) z
    quadEval (decodeTensor p (l.eval kappa) (n1.eval kappa * n2.eval kappa) d (w.eval kappa) f)
      (decodeResidues p (l.eval kappa) (w.eval kappa) x)
      (fun i => privateValues (Fin.castAdd (n2.eval kappa) i))
      (fun j => privateValues (Fin.natAdd (n1.eval kappa) j))

/-- The quadratic public-input width is l residue blocks. -/
theorem quadClass_pubLen (l n1 n2 w : PolyExpr) (d : ℕ) :
    (quadClass l n1 n2 w d).pubLen = .mul l w := rfl

/-- The quadratic private-input width is n1+n2 residue blocks. -/
theorem quadClass_privLen (l n1 n2 w : PolyExpr) (d : ℕ) :
    (quadClass l n1 n2 w d).privLen = .mul (.add n1 n2) w := rfl

/-- The quadratic function description has one coefficient tensor for each private pair. -/
theorem quadClass_fnLen (l n1 n2 w : PolyExpr) (d : ℕ) :
    (quadClass l n1 n2 w d).fnLen = tensorFnLen l (.mul n1 n2) w d := rfl

/-- The quadratic class parameter is any positive modulus. -/
theorem quadClass_Prm (l n1 n2 w : PolyExpr) (d kappa : ℕ) :
    (quadClass l n1 n2 w d).Prm kappa = ℕ+ := rfl

/-- The quadratic class returns residues at the supplied modulus. -/
theorem quadClass_Out (l n1 n2 w : PolyExpr) (d kappa : ℕ) (p : ℕ+) :
    (quadClass l n1 n2 w d).Out kappa p = ZMod (p : ℕ) := rfl

/-- Quadratic scalar simulator values use the lossless modulus-dependent encoding. -/
theorem quadClass_encValue (l n1 n2 w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (a : ZMod (p : ℕ)) :
    (quadClass l n1 n2 w d).encValue kappa p a = encodeScalar p a := rfl

/-- The quadratic wire evaluation uses the two blocks of the decoded private vector. -/
theorem quadClass_eval (l n1 n2 w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (f : Fin ((tensorFnLen l (.mul n1 n2) w d).eval kappa) → Bool)
    (x : Fin (l.eval kappa * w.eval kappa) → Bool)
    (z : Fin ((n1.eval kappa + n2.eval kappa) * w.eval kappa) → Bool) :
    (quadClass l n1 n2 w d).eval kappa p f x z =
      quadEval (decodeTensor p (l.eval kappa) (n1.eval kappa * n2.eval kappa) d (w.eval kappa) f)
        (decodeResidues p (l.eval kappa) (w.eval kappa) x)
        (fun i => decodeResidues p (n1.eval kappa + n2.eval kappa) (w.eval kappa) z
          (Fin.castAdd (n2.eval kappa) i))
        (fun j => decodeResidues p (n1.eval kappa + n2.eval kappa) (w.eval kappa) z
          (Fin.natAdd (n1.eval kappa) j)) := rfl

/-- The quadratic class parameter is explicitly transported to its positive modulus. -/
def quadClassParamEquiv (l n1 n2 w : PolyExpr) (d kappa : ℕ) :
    (quadClass l n1 n2 w d).Prm kappa ≃ ℕ+ := Equiv.refl _

/-- The quadratic parameter codec is internally the identity equivalence. -/
theorem quadClassParamEquiv_eq (l n1 n2 w : PolyExpr) (d kappa : ℕ) :
    quadClassParamEquiv l n1 n2 w d kappa = Equiv.refl ℕ+ := rfl

/-- Encoding then decoding a quadratic parameter recovers the supplied modulus. -/
theorem quadClassParamEquiv_apply_symm (l n1 n2 w : PolyExpr) (d kappa : ℕ) (p : ℕ+) :
    quadClassParamEquiv l n1 n2 w d kappa
      ((quadClassParamEquiv l n1 n2 w d kappa).symm p) = p :=
  (quadClassParamEquiv l n1 n2 w d kappa).apply_symm_apply p

/-- The quadratic value codec preserves the scalar at its explicitly encoded modulus. -/
def quadClassValueEquiv (l n1 n2 w : PolyExpr) (d kappa : ℕ) (p : ℕ+) :
    (quadClass l n1 n2 w d).Out kappa ((quadClassParamEquiv l n1 n2 w d kappa).symm p) ≃
      ZMod (p : ℕ) := Equiv.refl _

/-- The quadratic scalar-value codec is internally the identity equivalence. -/
theorem quadClassValueEquiv_eq (l n1 n2 w : PolyExpr) (d kappa : ℕ) (p : ℕ+) :
    quadClassValueEquiv l n1 n2 w d kappa p = Equiv.refl (ZMod (p : ℕ)) := rfl

/-- Encoding then decoding a quadratic scalar preserves the scalar value. -/
theorem quadClassValueEquiv_apply_symm (l n1 n2 w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (a : ZMod (p : ℕ)) :
    quadClassValueEquiv l n1 n2 w d kappa p
      ((quadClassValueEquiv l n1 n2 w d kappa p).symm a) = a :=
  (quadClassValueEquiv l n1 n2 w d kappa p).apply_symm_apply a

/-- Encoding a packaged quadratic scalar gives the canonical residue encoding. -/
theorem quadClass_encValue_codec (l n1 n2 w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (a : ZMod (p : ℕ)) :
    (quadClass l n1 n2 w d).encValue kappa ((quadClassParamEquiv l n1 n2 w d kappa).symm p)
      ((quadClassValueEquiv l n1 n2 w d kappa p).symm a) = encodeScalar p a := rfl

/-- Duplicate private residue words in block order, without decoding them. This is
the wire form of y↦(y,y) used to embed [GJLS21, §9] into [Wee20, §3]. -/
def duplicatePrivateBits (n width : ℕ) (y : Fin (n * width) → Bool) :
    Fin ((n + n) * width) → Bool :=
  fun i => let jb := finProdFinEquiv.symm i
    y (finProdFinEquiv (Sum.elim id id (finSumFinEquiv.symm jb.1), jb.2))

/-- Private-word duplication repeats the residue row selected by the finite-sum
coordinate while preserving its within-residue bit coordinate. -/
theorem duplicatePrivateBits_eq (n width : ℕ) (y : Fin (n * width) → Bool) :
    duplicatePrivateBits n width y = fun i =>
      let jb := finProdFinEquiv.symm i
      y (finProdFinEquiv (Sum.elim id id (finSumFinEquiv.symm jb.1), jb.2)) := rfl

/-- The PHFE class embeds into the quadratic class by the identity on coefficient
words and duplication of the private word. [GJLS21, §9; Wee20, §3, p.6].

**Proof sketch.** The duplicated word decodes to two copies of the same residue
vector, by the total block-decoding reader and the published finite-sum/product
coordinate equations. The typed evaluations then agree by phfeEval_eq. -/
theorem phfeClass_eval_eq_quad (l n w : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (f : Fin ((tensorFnLen l (.mul n n) w d).eval kappa) → Bool)
    (x : Fin (l.eval kappa * w.eval kappa) → Bool)
    (y : Fin (n.eval kappa * w.eval kappa) → Bool) :
    (phfeClass l n w d).eval kappa p f x y =
      (quadClass l n n w d).eval kappa p f x
        (duplicatePrivateBits (n.eval kappa) (w.eval kappa) y) := sorry

/-- A multivariate polynomial has separate public/private degree bounds when
every nonzero monomial satisfies the corresponding sums of variable exponents.
This is representation glue for the class inclusion discussed in [GJLS21, §9, p.58]. -/
def BidegreeAtMost {p : ℕ+} {l n : ℕ} (d e : ℕ)
    (P : MvPolynomial (Fin l ⊕ Fin n) (ZMod (p : ℕ))) : Prop :=
  ∀ s : (Fin l ⊕ Fin n) →₀ ℕ, MvPolynomial.coeff s P ≠ 0 →
    (∑ i : Fin l, s (Sum.inl i)) ≤ d ∧ (∑ j : Fin n, s (Sum.inr j)) ≤ e

/-- Separate degree bounds mean exactly the displayed monomial exponent bounds. -/
theorem bidegreeAtMost_iff {p : ℕ+} {l n : ℕ} (d e : ℕ)
    (P : MvPolynomial (Fin l ⊕ Fin n) (ZMod (p : ℕ))) :
    BidegreeAtMost d e P ↔
      ∀ s : (Fin l ⊕ Fin n) →₀ ℕ, MvPolynomial.coeff s P ≠ 0 →
        (∑ i : Fin l, s (Sum.inl i)) ≤ d ∧ (∑ j : Fin n, s (Sum.inr j)) ≤ e := Iff.rfl

/-- Every public-degree-d, private-degree-two polynomial is represented by the
PHFE class after appending 1 to the private input. [GJLS21, §9, p.58]. This spells
out the constant/linear-term padding bridge for the tuple representation.

**Proof sketch.** Expand the polynomial as the finite sum of its monomials. For
each monomial, list its public variables with multiplicity, pad to d slots with
the public constant, list its private variables with multiplicity, and pad to
two slots with the private constant. Assign its coefficient to one such ordered
tuple pair. Reindex the finite coefficient sum; padding contributes only 1. -/
theorem pad_one {p : ℕ+} {l n d : ℕ}
    (P : MvPolynomial (Fin l ⊕ Fin n) (ZMod (p : ℕ)))
    (hdeg : BidegreeAtMost d 2 P) :
    ∃ C : PolyTensor p l ((n + 1) * (n + 1)) d,
      ∀ (x : Fin l → ZMod (p : ℕ)) (y : Fin n → ZMod (p : ℕ)),
        MvPolynomial.eval (Sum.elim x y) P = phfeEval C x (Fin.snoc y 1) := sorry

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
