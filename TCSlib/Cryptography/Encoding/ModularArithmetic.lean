/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.BinaryArith
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Complexity.ClassP.BinaryArith.Div
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Encoded arithmetic modulo a general modulus

## Main definitions

* `addMod`: on `⟨⟨c, q⟩, ⟨a, b⟩⟩`, the `|c|`-bit numeral of `(a + b) mod q`, with the modulus
  `q` read as an MSB numeral of any length.
* `vecAddStep`, `vecAddModWords`: coordinatewise modular addition of two fixed-width encoded
  vectors, one coordinate per round of the public counted loop.
* `subsetSumStep`, `subsetSumModWords`: the sum modulo `q` of the rows of a row-major encoded
  matrix selected by a bit string, one row per round of the same loop.
* `modContext`: the canonical context `⟨0^w, natToList (w + 1) q⟩`, with the readers
  `addMod_modContext`, `vecAddModWords_modContext`, `subsetSumModWords_modContext` and
  `subsetSumModWords_modContext_vector`.

## Main results

* `addMod_pairEncode`, `addMod_natToList`: the scalar map computes `(a + b) mod q`, and adds
  residues of `ZMod q` on their canonical numerals.
* `vecAddModWords_encodeVector`: `Encoding.Modular.encodeVector w u` and `encodeVector w v` go
  to `encodeVector w (u + v)` for `u v : Fin len → ZMod q`, `q ≤ 2^w`.
* `subsetSumModWords_encodeMatrix`: `encodeMatrix w A` and the bits `r` go to
  `encodeVector w (Aᵀ *ᵥ r)`; `subsetSumModWords_encodeVector` is the one-column case, the
  numeral of `∑ i, b i * r i`.
* `polyTimeComputable_addMod`, `polyTimeComputable_vecAddModWords`,
  `polyTimeComputable_subsetSumModWords`: all three maps are polynomial-time on every input.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009, Section 7.2 (the arithmetic machines' model).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010, Section 2.1
  (machine representations).
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definition 4.2.3 and Section 5.2.1 (the modular vectors and subset sums being represented).

**Representation.** Glue: these are repository adaptations, not textbook results. The
modulus is not a function of the input length: it is read from the input, so a reduction
supplies it as advice. The context word `⟨c, q⟩` carries the residue width `|c|` (only the
length of `c` is read) and the modulus `q` as an MSB numeral of any length (`q = 2^|c|` needs
`|c| + 1` bits). Residues are the canonical `|c|`-bit numerals of `Encoding.Modular`.
The scalar map is `Complexity.BinArith.add` followed by `BinArith.mod`, through the MSB↔LE
adapters `toLE` and `fromLEPoly .var` of `Encoding.BinaryArith`; the vector maps run it in
the registered counted loop `Complexity.BinArith.forLoop`. No new traversal or padding host
is introduced. The dyadic layers `Encoding.DyadicArithmetic` and `DyadicLinearAlgebra` are the
precedent for the layout; they reduce modulo `2^W` and do not cover a general modulus.
All maps are total: malformed pairs are read through the total projections, and a modulus
`0` leaves the sum unreduced. Faithfulness needs `q ≤ 2^|c|` and the canonical encodings.
-/

namespace TCSlib.Cryptography.Encoding.ModularArithmetic

open Complexity Turing
open TCSlib.Cryptography.NumberTheory (listToNat)
open TCSlib.Cryptography.Encoding.BinaryArith

/-! ## Scalar addition modulo `q` -/

/-- **Modular addition of two numerals.** On `⟨⟨c, q⟩, ⟨a, b⟩⟩` it writes the `|c|`-bit
numeral of `(a + b) mod q`, reading `a`, `b` and `q` as MSB numerals of any length. Glue
([AB09, §7.2]: the binary adder and the remainder machine, composed). -/
def addMod (z : List Bool) : List Bool :=
  fromLEPoly .var
    (pairEncode (pairFstD (pairFstD z))
      (BinArith.mod
        (pairEncode
          (BinArith.add
            (pairEncode (toLE (pairFstD (pairSndD z))) (toLE (pairSndD (pairSndD z)))))
          (toLE (pairSndD (pairFstD z))))))

/-- `addMod z` is `fromLEPoly .var ⟨c, mod ⟨add ⟨toLE a, toLE b⟩, toLE q⟩⟩` for the total
projections `c`, `q`, `a`, `b` of `z`. -/
theorem addMod_eq (z : List Bool) :
    addMod z =
      fromLEPoly .var
        (pairEncode (pairFstD (pairFstD z))
          (BinArith.mod
            (pairEncode
              (BinArith.add
                (pairEncode (toLE (pairFstD (pairSndD z))) (toLE (pairSndD (pairSndD z)))))
              (toLE (pairSndD (pairFstD z)))))) := rfl

/-- On an encoded input, `addMod ⟨⟨c, q⟩, ⟨a, b⟩⟩ = natToList |c| ((a + b) mod q)`, for MSB
numerals `a`, `b`, `q` of any lengths.

**Proof sketch.** Read `addMod_eq` and the pair equations; `toLE_eq_natBits` turns each
operand into the canonical little-endian numeral, `BinArith.add_pairEncode` and
`BinArith.mod_pairEncode` compute, and `fromLEPoly_pairEncode` writes the result. -/
theorem addMod_pairEncode (c qw a b : List Bool) :
    addMod (pairEncode (pairEncode c qw) (pairEncode a b)) =
      Candidates.natToList c.length ((listToNat a + listToNat b) % listToNat qw) := by
  rw [addMod_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, toLE_eq_natBits,
    BinArith.add_pairEncode, BinArith.mod_pairEncode, fromLEPoly_pairEncode,
    LogProg.bitsVal_bits, PolyExpr.eval_var]

/-- The output of `addMod z` has exactly the width `|pairFstD (pairFstD z)|` on every input.

**Proof sketch.** `fromLEPoly_length` with the template `pairFstD (pairFstD z)`. -/
theorem addMod_length (z : List Bool) :
    (addMod z).length = (pairFstD (pairFstD z)).length := by
  rw [addMod_eq, fromLEPoly_length, pairFstD_pairEncode, PolyExpr.eval_var]

/-- **Residue addition.** If `q ≤ 2^|c|` and `q`'s numeral `qw` has value `q`, then `addMod`
sends the canonical `|c|`-bit numerals of `x y : ZMod q` to the numeral of `x + y`.

**Proof sketch.** `addMod_pairEncode`; both numerals read back as `x.val`, `y.val` since they
are below `q ≤ 2^|c|` (`Candidates.listToNat_natToList`); then `ZMod.val_add`. -/
theorem addMod_natToList {q : ℕ} [NeZero q] (c qw : List Bool) (hq : q ≤ 2 ^ c.length)
    (hqw : listToNat qw = q) (x y : ZMod q) :
    addMod (pairEncode (pairEncode c qw)
        (pairEncode (Candidates.natToList c.length x.val)
          (Candidates.natToList c.length y.val))) =
      Candidates.natToList c.length (x + y).val := by
  rw [addMod_pairEncode, Candidates.listToNat_natToList (lt_of_lt_of_le (ZMod.val_lt x) hq),
    Candidates.listToNat_natToList (lt_of_lt_of_le (ZMod.val_lt y) hq), hqw, ZMod.val_add]

/-- **Modular addition is polynomial-time** on every input.

**Proof sketch.** Compose the total projections, `polyTimeComputable_toLE`,
`BinArith.polyTimeComputable_add`, `BinArith.polyTimeComputable_mod`, pairing and
`polyTimeComputable_fromLEPoly .var`; `addMod_eq` identifies the composite. -/
theorem polyTimeComputable_addMod : PolyTimeComputable addMod := by
  have ha := polyTimeComputable_toLE.comp BinArith.polyTimeComputable_slot2
  have hb := polyTimeComputable_toLE.comp BinArith.polyTimeComputable_slot3
  have hq := polyTimeComputable_toLE.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
  have hc := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hcomposed := (polyTimeComputable_fromLEPoly .var).comp
    (hc.pairEncode (BinArith.polyTimeComputable_mod.comp
      ((BinArith.polyTimeComputable_add.comp (ha.pairEncode hb)).pairEncode hq)))
  refine Eq.mp (congrArg PolyTimeComputable ?_) hcomposed
  funext z
  simp only [addMod_eq, Function.comp_apply]

/-! ## Coordinatewise vector addition modulo `q` -/

/-- **One coordinate of vector addition.** On the state `⟨ctx, ⟨x, ⟨y, out⟩⟩⟩` with
`ctx = ⟨c, q⟩`, cut one `|c|`-bit block from each operand and append their sum modulo `q` to
`out`. Glue: the leaf step of `vecAddModWords`. -/
def vecAddStep (z : List Bool) : List Bool :=
  let ctx := pairFstD z
  let w := (pairFstD ctx).length
  let xs := pairFstD (pairSndD z)
  let ys := pairFstD (pairSndD (pairSndD z))
  let out := pairSndD (pairSndD (pairSndD z))
  pairEncode ctx (pairEncode (xs.drop w) (pairEncode (ys.drop w)
    (out ++ addMod (pairEncode ctx (pairEncode (xs.take w) (ys.take w))))))

/-- `vecAddStep ⟨ctx, ⟨x, ⟨y, out⟩⟩⟩ = ⟨ctx, ⟨x.drop w, ⟨y.drop w,
out ++ addMod ⟨ctx, ⟨x.take w, y.take w⟩⟩⟩⟩⟩` with `w = |pairFstD ctx|`. -/
theorem vecAddStep_eq (z : List Bool) :
    vecAddStep z =
      let ctx := pairFstD z
      let w := (pairFstD ctx).length
      let xs := pairFstD (pairSndD z)
      let ys := pairFstD (pairSndD (pairSndD z))
      let out := pairSndD (pairSndD (pairSndD z))
      pairEncode ctx (pairEncode (xs.drop w) (pairEncode (ys.drop w)
        (out ++ addMod (pairEncode ctx (pairEncode (xs.take w) (ys.take w)))))) := rfl

/-- The step keeps its context: `pairFstD (vecAddStep z) = pairFstD z`.

**Proof sketch.** `vecAddStep_eq` and `pairFstD_pairEncode`. -/
theorem vecAddStep_fst (z : List Bool) : pairFstD (vecAddStep z) = pairFstD z := by
  rw [vecAddStep_eq, pairFstD_pairEncode]

/-- One step grows the state by at most `8 (|ctx| + 1)` bits.

**Proof sketch.** The operands only shrink and the output grows by exactly `|c| ≤ |ctx|`
(`addMod_length`); the pairing lengths of the input bound the re-encoded state. -/
theorem vecAddStep_length_le (z : List Bool) :
    (vecAddStep z).length ≤ z.length + 8 * ((pairFstD z).length + 1) := by
  have houter := length_pair_components_le z
  have hmiddle := length_pair_components_le (pairSndD z)
  have hinner := length_pair_components_le (pairSndD (pairSndD z))
  have hwidth := length_pairFstD_le (pairFstD z)
  simp only [vecAddStep_eq, length_pairEncode, List.length_drop, List.length_append,
    addMod_length, pairFstD_pairEncode]
  omega

/-- The vector-addition step is polynomial-time.

**Proof sketch.** Compose the projections, the cuts `polyTimeComputable_pairTakePoly .var` and
`pairDropPoly .var` on `⟨c, x⟩` and `⟨c, y⟩`, `polyTimeComputable_addMod`, append and pairing. -/
theorem polyTimeComputable_vecAddStep : PolyTimeComputable vecAddStep := by
  have hctx := polyTimeComputable_pairFstD
  have hc := polyTimeComputable_pairFstD.comp hctx
  have hx := BinArith.polyTimeComputable_slot2
  have hy := polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3
  have hout := BinArith.polyTimeComputable_slot4
  have hxTake := (polyTimeComputable_pairTakePoly .var).comp (hc.pairEncode hx)
  have hyTake := (polyTimeComputable_pairTakePoly .var).comp (hc.pairEncode hy)
  have hxDrop := (polyTimeComputable_pairDropPoly .var).comp (hc.pairEncode hx)
  have hyDrop := (polyTimeComputable_pairDropPoly .var).comp (hc.pairEncode hy)
  have hsum := polyTimeComputable_addMod.comp (hctx.pairEncode (hxTake.pairEncode hyTake))
  have hcomposed := hctx.pairEncode (hxDrop.pairEncode (hyDrop.pairEncode (hout.append hsum)))
  refine Eq.mp (congrArg PolyTimeComputable ?_) hcomposed
  funext z
  simp only [vecAddStep_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var]

/-- **Vector addition modulo `q`.** With context `ctx = ⟨c, q⟩`, run `vecAddStep` once per
letter of `n` from `⟨ctx, ⟨x, ⟨y, []⟩⟩⟩` and return the accumulated output: the
concatenated `|c|`-bit numerals of the coordinatewise sums modulo `q` of the first `|n|`
blocks of `x` and `y`. Glue: the general-modulus analogue of the dyadic loops. -/
def vecAddModWords (ctx n x y : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (pairSndD
    (BinArith.forLoop vecAddStep
      (pairEncode n (pairEncode ctx (pairEncode x (pairEncode y []))))))))

/-- `vecAddModWords ctx n x y` is the output slot of `forLoop vecAddStep ⟨n, ⟨ctx, ⟨x, ⟨y,
[]⟩⟩⟩⟩`. -/
theorem vecAddModWords_eq (ctx n x y : List Bool) :
    vecAddModWords ctx n x y =
      pairSndD (pairSndD (pairSndD (pairSndD
        (BinArith.forLoop vecAddStep
          (pairEncode n (pairEncode ctx (pairEncode x (pairEncode y [])))))))) := rfl

/-- The output has exactly `|n| · |pairFstD ctx|` bits, on every input.

**Proof sketch.** Every round appends `|c|` bits (`addMod_length`) and keeps the context
(`vecAddStep_fst`); induct over the rounds and read `forLoop_pairEncode`. -/
theorem vecAddModWords_length (ctx n x y : List Bool) :
    (vecAddModWords ctx n x y).length = n.length * (pairFstD ctx).length := by
  let init := pairEncode ctx (pairEncode x (pairEncode y []))
  have h (k : ℕ) :
      pairFstD (vecAddStep^[k] init) = ctx ∧
        (pairSndD (pairSndD (pairSndD (vecAddStep^[k] init)))).length =
          k * (pairFstD ctx).length := by
    induction k with
    | zero =>
      simp only [Function.iterate_zero_apply, init, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_nil, Nat.zero_mul, and_self]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨(vecAddStep_fst _).trans ih.1, ?_⟩
      simp only [vecAddStep_eq, pairSndD_pairEncode, pairFstD_pairEncode, List.length_append,
        addMod_length, ih.1, ih.2, Nat.succ_mul]
  rw [vecAddModWords_eq, BinArith.forLoop_pairEncode, pairSndD_pairEncode]
  exact (h n.length).2

/-- **Vector addition is polynomial-time**, in the packed form
`⟨ctx, ⟨n, ⟨x, y⟩⟩⟩ ↦ vecAddModWords ctx n x y`.

**Proof sketch.** `BinArith.polyTimeComputable_forLoop` with the envelope
`forLoop_bound_of_ctx 8` of `vecAddStep_fst` and `vecAddStep_length_le`; compose with the
initial pairing and the final projections. -/
theorem polyTimeComputable_vecAddModWords :
    PolyTimeComputable (fun z => vecAddModWords (pairFstD z) (pairFstD (pairSndD z))
      (pairFstD (pairSndD (pairSndD z))) (pairSndD (pairSndD (pairSndD z)))) := by
  have hloop := BinArith.polyTimeComputable_forLoop polyTimeComputable_vecAddStep 9 2
    (BinArith.forLoop_bound_of_ctx 8 vecAddStep_fst vecAddStep_length_le)
  have hctx := polyTimeComputable_pairFstD
  have hn := BinArith.polyTimeComputable_slot2
  have hx := polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3
  have hy := BinArith.polyTimeComputable_slot4
  have hinit := hctx.pairEncode (hx.pairEncode (hy.pairEncode (polyTimeComputable_const [])))
  have hcomposed := (BinArith.polyTimeComputable_slot4.comp polyTimeComputable_pairSndD).comp
    (hloop.comp (hn.pairEncode hinit))
  refine Eq.mp (congrArg PolyTimeComputable ?_) hcomposed
  funext z
  simp only [vecAddModWords_eq, Function.comp_apply]

/-- **Correspondence with `ZMod` addition** [Pei16, Definition 4.2.3, representation]: for
`q ≤ 2^|c|`, a numeral `qw` of `q` and a counter `n` of length `len`,
`vecAddModWords ⟨c, qw⟩ n (encodeVector |c| u) (encodeVector |c| v) = encodeVector |c| (u + v)`
for all `u v : Fin len → ZMod q`.

**Proof sketch.** Induct over the coordinates with an arbitrary output prefix: each round
cuts the leading numerals of both operands (`Modular.encodeVector_eq`, `List.ofFn_succ`,
`List.drop_left'`, `List.take_left'`) and appends the numeral of their sum
(`addMod_natToList`). At the end both operands are empty and the output is
`encodeVector |c| (u + v)`. -/
theorem vecAddModWords_encodeVector {q len : ℕ} [NeZero q] (c qw : List Bool)
    (hq : q ≤ 2 ^ c.length) (hqw : listToNat qw = q) (n : List Bool) (hn : n.length = len)
    (u v : Fin len → ZMod q) :
    vecAddModWords (pairEncode c qw) n (Modular.encodeVector c.length u)
      (Modular.encodeVector c.length v) = Modular.encodeVector c.length (u + v) := by
  subst hn
  let ctx := pairEncode c qw
  let w := c.length
  have hlen (x : ZMod q) : (Candidates.natToList w x.val).length = c.length :=
    Candidates.length_natToList w x.val
  have hsplit {k : ℕ} (v : Fin (k + 1) → ZMod q) : Modular.encodeVector w v =
      Candidates.natToList w (v 0).val ++ Modular.encodeVector w (fun i : Fin k => v i.succ) := by
    rw [Modular.encodeVector_eq, List.ofFn_succ, List.flatten_cons, Modular.encodeVector_eq]
  have walk (k : ℕ) (x y : Fin k → ZMod q) (out : List Bool) :
      vecAddStep^[k] (pairEncode ctx (pairEncode (Modular.encodeVector w x)
          (pairEncode (Modular.encodeVector w y) out))) =
        pairEncode ctx (pairEncode [] (pairEncode [] (out ++ Modular.encodeVector w (x + y)))) := by
    induction k generalizing out with
    | zero =>
      simp only [Function.iterate_zero_apply, Modular.encodeVector_eq, List.ofFn_zero,
        List.flatten_nil, List.append_nil]
    | succ k ih =>
      have hres : Modular.encodeVector w (x + y) =
          Candidates.natToList w (x 0 + y 0).val ++
            Modular.encodeVector w ((fun i : Fin k => x i.succ) + fun i => y i.succ) :=
        hsplit (x + y)
      rw [Function.iterate_succ_apply, vecAddStep_eq]
      simp only [ctx, pairFstD_pairEncode, pairSndD_pairEncode, hsplit x, hsplit y,
        List.drop_left' (hlen _), List.take_left' (hlen _)]
      rw [addMod_natToList c qw hq hqw, ih, hres, List.append_assoc]
  rw [vecAddModWords_eq, BinArith.forLoop_pairEncode, pairSndD_pairEncode]
  change pairSndD (pairSndD (pairSndD (vecAddStep^[n.length] (pairEncode ctx
    (pairEncode (Modular.encodeVector w u) (pairEncode (Modular.encodeVector w v) [])))))) = _
  rw [walk]
  simp only [pairSndD_pairEncode, List.nil_append, w]

/-! ## Subset sums of matrix rows modulo `q` -/

/-- **One row of a subset sum.** On the state `⟨⟨ctx, nT⟩, ⟨rows, ⟨bits, acc⟩⟩⟩` with
`ctx = ⟨c, q⟩`, cut one row of `|nT| · |c|` bits from `rows` and one bit from `bits`; if the
bit is `1`, add the row to `acc` modulo `q` with `vecAddModWords ctx nT`, otherwise keep
`acc`. Glue: the leaf step of `subsetSumModWords`. -/
def subsetSumStep (z : List Bool) : List Bool :=
  let ctx₂ := pairFstD z
  let ctx := pairFstD ctx₂
  let nT := pairSndD ctx₂
  let rowLen := nT.length * (pairFstD ctx).length
  let rows := pairFstD (pairSndD z)
  let bits := pairFstD (pairSndD (pairSndD z))
  let acc := pairSndD (pairSndD (pairSndD z))
  pairEncode ctx₂ (pairEncode (rows.drop rowLen) (pairEncode (bits.drop 1)
    (if bits.headD false then vecAddModWords ctx nT acc (rows.take rowLen) else acc)))

/-- `subsetSumStep ⟨⟨ctx, nT⟩, ⟨rows, ⟨bits, acc⟩⟩⟩` drops one row of `|nT| · |c|` bits and
one bit, and replaces `acc` by `vecAddModWords ctx nT acc row` when the bit is `1`. -/
theorem subsetSumStep_eq (z : List Bool) :
    subsetSumStep z =
      let ctx₂ := pairFstD z
      let ctx := pairFstD ctx₂
      let nT := pairSndD ctx₂
      let rowLen := nT.length * (pairFstD ctx).length
      let rows := pairFstD (pairSndD z)
      let bits := pairFstD (pairSndD (pairSndD z))
      let acc := pairSndD (pairSndD (pairSndD z))
      pairEncode ctx₂ (pairEncode (rows.drop rowLen) (pairEncode (bits.drop 1)
        (if bits.headD false then vecAddModWords ctx nT acc (rows.take rowLen) else acc))) :=
  rfl

/-- The step keeps its context: `pairFstD (subsetSumStep z) = pairFstD z`.

**Proof sketch.** `subsetSumStep_eq` and `pairFstD_pairEncode`. -/
theorem subsetSumStep_fst (z : List Bool) : pairFstD (subsetSumStep z) = pairFstD z := by
  rw [subsetSumStep_eq, pairFstD_pairEncode]

/-- One step grows the state by at most `6 + |ctx₂|²` bits, `ctx₂ = pairFstD z`.

**Proof sketch.** Rows and bits only shrink; the new accumulator is either the old one or a
vector sum of `|nT| · |c| ≤ |ctx₂|²` bits (`vecAddModWords_length`). The pairing lengths of
the input bound the re-encoded state. -/
theorem subsetSumStep_length_le (z : List Bool) :
    (subsetSumStep z).length ≤ z.length + (6 + (pairFstD z).length * (pairFstD z).length) := by
  have houter := length_pair_components_le z
  have hmiddle := length_pair_components_le (pairSndD z)
  have hinner := length_pair_components_le (pairSndD (pairSndD z))
  have hctx := length_pair_components_le (pairFstD z)
  have hc := length_pairFstD_le (pairFstD (pairFstD z))
  have hprod : (pairSndD (pairFstD z)).length * (pairFstD (pairFstD (pairFstD z))).length ≤
      (pairFstD z).length * (pairFstD z).length :=
    Nat.mul_le_mul (by omega) (by omega)
  have hacc : (if (pairFstD (pairSndD (pairSndD z))).headD false then
        vecAddModWords (pairFstD (pairFstD z)) (pairSndD (pairFstD z))
          (pairSndD (pairSndD (pairSndD z)))
          ((pairFstD (pairSndD z)).take ((pairSndD (pairFstD z)).length *
            (pairFstD (pairFstD (pairFstD z))).length))
      else pairSndD (pairSndD (pairSndD z))).length ≤
        (pairSndD (pairSndD (pairSndD z))).length +
          (pairFstD z).length * (pairFstD z).length := by
    split
    · rw [vecAddModWords_length]
      omega
    · omega
  rw [subsetSumStep_eq]
  simp only [length_pairEncode, List.length_drop]
  omega

/-- Iterating the subset-sum step `j` times adds at most `j (6 + |ctx₂|²)` bits.

**Proof sketch.** The context is invariant (`subsetSumStep_fst`), so every round obeys the
same bound `subsetSumStep_length_le`; induct on `j`. -/
theorem subsetSumStep_iterate_length_le (d : List Bool) (j : ℕ) :
    (subsetSumStep^[j] d).length ≤
      d.length + j * (6 + (pairFstD d).length * (pairFstD d).length) := by
  have hq (j : ℕ) : pairFstD (subsetSumStep^[j] d) = pairFstD d := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', subsetSumStep_fst, ih]
  induction j with
  | zero => simp only [Function.iterate_zero_apply, Nat.zero_mul, Nat.add_zero, le_refl]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have h := subsetSumStep_length_le (subsetSumStep^[j] d)
    rw [hq j] at h
    rw [Nat.succ_mul]
    omega

/-- The subset-sum step is polynomial-time.

**Proof sketch.** The row length template is `BinArith.mulU ⟨nT, c⟩` (length `|nT| · |c|`);
compose the cuts `pairTakePoly .var`/`pairDropPoly .var`, `polyTimeComputable_tail`, the
branch `polyTimeComputable_ite` on `polyTimeComputable_headD`, and
`polyTimeComputable_vecAddModWords`. -/
theorem polyTimeComputable_subsetSumStep : PolyTimeComputable subsetSumStep := by
  have hctx₂ := polyTimeComputable_pairFstD
  have hctx := polyTimeComputable_pairFstD.comp hctx₂
  have hnT := polyTimeComputable_pairSndD.comp hctx₂
  have hc := polyTimeComputable_pairFstD.comp hctx
  have hrows := BinArith.polyTimeComputable_slot2
  have hbits := polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3
  have hacc := BinArith.polyTimeComputable_slot4
  have htemplate := (BinArith.polyTimeComputable_mulU.comp (hnT.pairEncode hc)).pairEncode hrows
  have hrow : PolyTimeComputable (fun z => (pairFstD (pairSndD z)).take
      ((pairSndD (pairFstD z)).length * (pairFstD (pairFstD (pairFstD z))).length)) := by
    refine Eq.mp (congrArg PolyTimeComputable ?_)
      ((polyTimeComputable_pairTakePoly .var).comp htemplate)
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
      PolyExpr.eval_var, BinArith.length_mulU]
  have hrest : PolyTimeComputable (fun z => (pairFstD (pairSndD z)).drop
      ((pairSndD (pairFstD z)).length * (pairFstD (pairFstD (pairFstD z))).length)) := by
    refine Eq.mp (congrArg PolyTimeComputable ?_)
      ((polyTimeComputable_pairDropPoly .var).comp htemplate)
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
      PolyExpr.eval_var, BinArith.length_mulU]
  have htail : PolyTimeComputable (fun z => (pairFstD (pairSndD (pairSndD z))).drop 1) :=
    polyTimeComputable_tail.comp hbits
  have htest : PolyTimeComputable
      (fun z => [(pairFstD (pairSndD (pairSndD z))).headD false]) :=
    polyTimeComputable_headD.comp hbits
  have hsum : PolyTimeComputable (fun z => vecAddModWords (pairFstD (pairFstD z))
      (pairSndD (pairFstD z)) (pairSndD (pairSndD (pairSndD z)))
      ((pairFstD (pairSndD z)).take
        ((pairSndD (pairFstD z)).length * (pairFstD (pairFstD (pairFstD z))).length))) := by
    refine Eq.mp (congrArg PolyTimeComputable ?_) (polyTimeComputable_vecAddModWords.comp
      (hctx.pairEncode (hnT.pairEncode (hacc.pairEncode hrow))))
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hbranch := polyTimeComputable_ite htest hsum hacc
  have hcomposed := hctx₂.pairEncode (hrest.pairEncode (htail.pairEncode hbranch))
  exact hcomposed

/-- **Subset sum of matrix rows modulo `q`.** With context `ctx = ⟨c, q⟩`, run
`subsetSumStep` once per letter of `mT` from the accumulator `0^{|nT| · |c|}`: the result is
the encoded sum modulo `q` of the rows (of `|nT|` residues of `|c|` bits each) of `rows`
whose bit in `bits` is `1`. Glue: the general-modulus subset sum of [Pei16, §5.2.1]. -/
def subsetSumModWords (ctx nT mT rows bits : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (pairSndD (BinArith.forLoop subsetSumStep
    (pairEncode mT (pairEncode (pairEncode ctx nT) (pairEncode rows (pairEncode bits
      (List.replicate (nT.length * (pairFstD ctx).length) false)))))))))

/-- `subsetSumModWords ctx nT mT rows bits` is the accumulator slot of
`forLoop subsetSumStep ⟨mT, ⟨⟨ctx, nT⟩, ⟨rows, ⟨bits, 0^{|nT| · |c|}⟩⟩⟩⟩`. -/
theorem subsetSumModWords_eq (ctx nT mT rows bits : List Bool) :
    subsetSumModWords ctx nT mT rows bits =
      pairSndD (pairSndD (pairSndD (pairSndD (BinArith.forLoop subsetSumStep
        (pairEncode mT (pairEncode (pairEncode ctx nT) (pairEncode rows (pairEncode bits
          (List.replicate (nT.length * (pairFstD ctx).length) false))))))))) := rfl

/-- **Subset sums are polynomial-time**, in the packed form
`⟨ctx, ⟨nT, ⟨mT, ⟨rows, bits⟩⟩⟩⟩ ↦ subsetSumModWords ctx nT mT rows bits`.

**Proof sketch.** `BinArith.polyTimeComputable_forLoop` with a cubic envelope: by
`subsetSumStep_iterate_length_le`, `j ≤ |mT|` rounds add at most `j (6 + |ctx₂|²)` bits, and
`|mT|`, `|ctx₂|` and the state are all below `N = |⟨mT, state⟩|`, so the iterates have at
most `N + N (6 + N²) ≤ 7 (N + 1)³` bits. The zero accumulator is
`EnsembleLemmas.polyTimeComputable_zeros .var` of `BinArith.mulU ⟨nT, c⟩`. -/
theorem polyTimeComputable_subsetSumModWords :
    PolyTimeComputable (fun z => subsetSumModWords (pairFstD z) (pairFstD (pairSndD z))
      (pairFstD (pairSndD (pairSndD z))) (pairFstD (pairSndD (pairSndD (pairSndD z))))
      (pairSndD (pairSndD (pairSndD (pairSndD z))))) := by
  have hbound : ∀ c d j, j ≤ c.length →
      (subsetSumStep^[j] d).length ≤ 7 * ((pairEncode c d).length + 1) ^ 3 := by
    intro c d j hj
    have h := subsetSumStep_iterate_length_le d j
    have hq := length_pairFstD_le d
    have hN : c.length + d.length ≤ (pairEncode c d).length := by
      rw [length_pairEncode]
      omega
    have hF : (pairFstD d).length ≤ (pairEncode c d).length := by omega
    have hj' : j ≤ (pairEncode c d).length := by omega
    have hmul : j * (6 + (pairFstD d).length * (pairFstD d).length) ≤
        (pairEncode c d).length * (6 + (pairEncode c d).length * (pairEncode c d).length) :=
      Nat.mul_le_mul hj' (Nat.add_le_add_left (Nat.mul_le_mul hF hF) 6)
    have hd : d.length ≤ (pairEncode c d).length := by omega
    generalize (pairEncode c d).length = N at hmul hd
    nlinarith
  have hloop := BinArith.polyTimeComputable_forLoop polyTimeComputable_subsetSumStep 7 3 hbound
  have hctx := polyTimeComputable_pairFstD
  have hnT := BinArith.polyTimeComputable_slot2
  have hmT := polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3
  have hrows := polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot4
  have hbits := polyTimeComputable_pairSndD.comp BinArith.polyTimeComputable_slot4
  have hc := polyTimeComputable_pairFstD.comp hctx
  have hzero := EnsembleLemmas.polyTimeComputable_zeros .var
    (BinArith.polyTimeComputable_mulU.comp (hnT.pairEncode hc))
  have hinit := hmT.pairEncode ((hctx.pairEncode hnT).pairEncode
    (hrows.pairEncode (hbits.pairEncode hzero)))
  have hcomposed := (BinArith.polyTimeComputable_slot4.comp polyTimeComputable_pairSndD).comp
    (hloop.comp hinit)
  refine Eq.mp (congrArg PolyTimeComputable ?_) hcomposed
  funext z
  simp only [subsetSumModWords_eq, Function.comp_apply, PolyExpr.eval_var,
    BinArith.length_mulU]

/-- **Correspondence with the transposed matrix-vector product** [Pei16, §5.2.1,
representation]: for `q ≤ 2^|c|`, a numeral `qw` of `q`, counters `nT`, `mT` of lengths
`n`, `m`, a matrix `A : Matrix (Fin m) (Fin n) (ZMod q)` and bits `r : Fin m → Bool` followed
by any unread bits `extra`,
`subsetSumModWords ⟨c, qw⟩ nT mT (encodeMatrix |c| A) (ofFn r ++ extra) =
encodeVector |c| (Aᵀ *ᵥ (fun i => (r i).toNat))`, the sum of the rows `A i` with `r i = 1`.

**Proof sketch.** Induct over the rows with an arbitrary accumulator `acc`: one round cuts the
leading row `encodeVector |c| (A 0)` (`Modular.encodeMatrix_eq`, `List.ofFn_succ`,
`encodeVector_length`) and the bit `r 0`, and replaces `acc` by `acc + A 0` when `r 0 = 1`
(`vecAddModWords_encodeVector`). The invariant is `acc + Aᵀ *ᵥ r`; its step is
`Fin.sum_univ_succ` in each coordinate. The initial accumulator `0^{n|c|}` is
`encodeVector |c| 0` (`Candidates.natToList_length_listToNat`,
`Candidates.listToNat_replicate_false`). -/
theorem subsetSumModWords_encodeMatrix {q m n : ℕ} [NeZero q] (c qw : List Bool)
    (hq : q ≤ 2 ^ c.length) (hqw : listToNat qw = q) (nT mT : List Bool) (hn : nT.length = n)
    (hm : mT.length = m) (A : Matrix (Fin m) (Fin n) (ZMod q)) (r : Fin m → Bool)
    (extra : List Bool) :
    subsetSumModWords (pairEncode c qw) nT mT (Modular.encodeMatrix c.length A)
        (List.ofFn r ++ extra) =
      Modular.encodeVector c.length (A.transpose.mulVec fun i => ((r i).toNat : ZMod q)) := by
  subst hm
  let ctx := pairEncode c qw
  let ctx₂ := pairEncode ctx nT
  let w := c.length
  have hnum0 : Candidates.natToList w (0 : ZMod q).val = List.replicate w false := by
    simpa only [ZMod.val_zero, List.length_replicate, Candidates.listToNat_replicate_false] using
      Candidates.natToList_length_listToNat (List.replicate w false)
  have hzero : List.replicate (nT.length * w) false =
      Modular.encodeVector w (0 : Fin n → ZMod q) := by
    rw [Modular.encodeVector_eq]
    simp only [Pi.zero_apply, hnum0, List.ofFn_const, hn]
    rw [List.flatten_replicate_replicate]
  have hrowLen (v : Fin n → ZMod q) :
      (Modular.encodeVector w v).length = nT.length * (pairFstD ctx).length := by
    rw [Modular.encodeVector_length, hn, pairFstD_pairEncode]
  have walk (k : ℕ) (R : Matrix (Fin k) (Fin n) (ZMod q)) (s : Fin k → Bool)
      (acc : Fin n → ZMod q) :
      subsetSumStep^[k] (pairEncode ctx₂ (pairEncode (Modular.encodeMatrix w R)
          (pairEncode (List.ofFn s ++ extra) (Modular.encodeVector w acc)))) =
        pairEncode ctx₂ (pairEncode [] (pairEncode extra
          (Modular.encodeVector w
            (acc + R.transpose.mulVec fun i => ((s i).toNat : ZMod q))))) := by
    induction k generalizing acc with
    | zero =>
      have hsum : acc + R.transpose.mulVec (fun i => ((s i).toNat : ZMod q)) = acc := by
        funext j
        change acc j + ∑ i : Fin 0, R i j * ((s i).toNat : ZMod q) = acc j
        rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      rw [hsum, Function.iterate_zero_apply, Modular.encodeMatrix_eq, List.ofFn_zero,
        List.flatten_nil, List.ofFn_zero, List.nil_append]
    | succ k ih =>
      let tail : Matrix (Fin k) (Fin n) (ZMod q) := fun i j => R i.succ j
      have hsplit : Modular.encodeMatrix w R =
          Modular.encodeVector w (R 0) ++ Modular.encodeMatrix w tail := by
        rw [Modular.encodeMatrix_eq, List.ofFn_succ, List.flatten_cons, Modular.encodeMatrix_eq]
      have hbits : List.ofFn s ++ extra = s 0 :: (List.ofFn (fun i : Fin k => s i.succ) ++ extra) :=
        by rw [List.ofFn_succ, List.cons_append]
      have hnext : (if s 0 then acc + R 0 else acc) +
          tail.transpose.mulVec (fun i => ((s i.succ).toNat : ZMod q)) =
          acc + R.transpose.mulVec (fun i => ((s i).toNat : ZMod q)) := by
        funext j
        change (if s 0 then acc + R 0 else acc) j +
            ∑ i : Fin k, R i.succ j * ((s i.succ).toNat : ZMod q) =
          acc j + ∑ i : Fin (k + 1), R i j * ((s i).toNat : ZMod q)
        rw [Fin.sum_univ_succ]
        cases s 0
        · rw [if_neg Bool.false_ne_true, Bool.toNat_false, Nat.cast_zero, mul_zero, zero_add]
        · rw [if_pos rfl, Pi.add_apply, Bool.toNat_true, Nat.cast_one, mul_one, add_assoc]
      have hacc : (if (s 0 :: (List.ofFn (fun i : Fin k => s i.succ) ++ extra)).headD false then
            vecAddModWords ctx nT (Modular.encodeVector w acc)
              ((Modular.encodeVector w (R 0) ++ Modular.encodeMatrix w tail).take
                (nT.length * (pairFstD ctx).length))
          else Modular.encodeVector w acc) =
          Modular.encodeVector w (if s 0 then acc + R 0 else acc) := by
        rw [List.headD_cons, List.take_left' (hrowLen (R 0))]
        cases s 0
        · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
        · rw [if_pos rfl, if_pos rfl]
          exact vecAddModWords_encodeVector c qw hq hqw nT hn acc (R 0)
      rw [Function.iterate_succ_apply, subsetSumStep_eq]
      simp only [ctx₂, pairFstD_pairEncode, pairSndD_pairEncode]
      rw [hsplit, hbits, hacc, List.drop_left' (hrowLen (R 0))]
      rw [List.drop_one, List.tail_cons]
      rw [← hnext]
      exact ih tail (fun i => s i.succ) _
  rw [subsetSumModWords_eq, BinArith.forLoop_pairEncode, pairSndD_pairEncode]
  change pairSndD (pairSndD (pairSndD (subsetSumStep^[mT.length] (pairEncode ctx₂
    (pairEncode (Modular.encodeMatrix w A) (pairEncode (List.ofFn r ++ extra)
      (List.replicate (nT.length * (pairFstD ctx).length) false))))))) = _
  rw [pairFstD_pairEncode, hzero, walk]
  simp only [pairSndD_pairEncode, zero_add]
  rfl

/-- **The one-column case: a subset sum of residues** [Pei16, §5.2.1, representation]: with
the one-letter counter `[true]`, `subsetSumModWords ⟨c, qw⟩ [true] mT (encodeVector |c| b)
(ofFn r ++ extra)` is the `|c|`-bit numeral of `∑ i, b i * (r i).toNat` in `ZMod q`.

**Proof sketch.** `encodeVector |c| b` is the encoding of the `m × 1` matrix with column `b`
(`Modular.encodeMatrix_eq`, `encodeVector_eq` on one coordinate); apply
`subsetSumModWords_encodeMatrix` and read the single coordinate of the product. -/
theorem subsetSumModWords_encodeVector {q m : ℕ} [NeZero q] (c qw : List Bool)
    (hq : q ≤ 2 ^ c.length) (hqw : listToNat qw = q) (mT : List Bool) (hm : mT.length = m)
    (b : Fin m → ZMod q) (r : Fin m → Bool) (extra : List Bool) :
    subsetSumModWords (pairEncode c qw) [true] mT (Modular.encodeVector c.length b)
        (List.ofFn r ++ extra) =
      Candidates.natToList c.length (∑ i, b i * ((r i).toNat : ZMod q)).val := by
  let B : Matrix (Fin m) (Fin 1) (ZMod q) := fun i _ => b i
  have hsingle (x : Fin 1 → ZMod q) :
      Modular.encodeVector c.length x = Candidates.natToList c.length (x 0).val := by
    rw [Modular.encodeVector_eq, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
      List.flatten_nil, List.append_nil]
  have hmatrix : Modular.encodeVector c.length b = Modular.encodeMatrix c.length B := by
    rw [Modular.encodeMatrix_eq, Modular.encodeVector_eq]
    congr 1
    exact congrArg List.ofFn (funext fun i => (hsingle (B i)).symm)
  rw [hmatrix, subsetSumModWords_encodeMatrix c qw hq hqw [true] mT rfl hm B r extra, hsingle]
  rfl

/-! ## The canonical modulus context -/

/-- **The canonical context for width `w` and modulus `q`**: `⟨0^w, natToList (w + 1) q⟩`,
the width template `0^w` and the `(w + 1)`-bit numeral of `q` (one bit more than the residue
width, so that `q = 2^w` fits). Glue: the advice word a reduction hands the maps above. -/
def modContext (w q : ℕ) : List Bool :=
  pairEncode (List.replicate w false) (Candidates.natToList (w + 1) q)

/-- `modContext w q = ⟨0^w, natToList (w + 1) q⟩`. -/
theorem modContext_eq (w q : ℕ) :
    modContext w q = pairEncode (List.replicate w false) (Candidates.natToList (w + 1) q) :=
  rfl

/-- The context has `3w + 3` bits.

**Proof sketch.** `length_pairEncode`, `List.length_replicate`, `Candidates.length_natToList`. -/
theorem modContext_length (w q : ℕ) : (modContext w q).length = 3 * w + 3 := by
  rw [modContext_eq, length_pairEncode, List.length_replicate, Candidates.length_natToList]
  omega

/-- For `q ≤ 2^w` the modulus numeral of the context reads back as `q`.

**Proof sketch.** `q ≤ 2^w < 2^(w+1)`, then `Candidates.listToNat_natToList`. -/
theorem listToNat_modulusNumeral {w q : ℕ} (hq : q ≤ 2 ^ w) :
    listToNat (Candidates.natToList (w + 1) q) = q :=
  Candidates.listToNat_natToList
    (lt_of_le_of_lt hq (Nat.pow_lt_pow_right Nat.one_lt_two (Nat.lt_succ_self w)))

/-- **Residue addition in the canonical context**: for `q ≤ 2^w`,
`addMod ⟨modContext w q, ⟨natToList w x.val, natToList w y.val⟩⟩ = natToList w (x + y).val`.

**Proof sketch.** `addMod_natToList` at `c = 0^w` and `listToNat_modulusNumeral`. -/
theorem addMod_modContext {q : ℕ} [NeZero q] {w : ℕ} (hq : q ≤ 2 ^ w) (x y : ZMod q) :
    addMod (pairEncode (modContext w q)
        (pairEncode (Candidates.natToList w x.val) (Candidates.natToList w y.val))) =
      Candidates.natToList w (x + y).val := by
  have h := addMod_natToList (List.replicate w false) (Candidates.natToList (w + 1) q)
    (by rwa [List.length_replicate]) (listToNat_modulusNumeral hq) x y
  rwa [List.length_replicate] at h

/-- **Vector addition in the canonical context**: for `q ≤ 2^w` and a counter `n` of length
`len`, `vecAddModWords (modContext w q) n (encodeVector w u) (encodeVector w v) =
encodeVector w (u + v)`.

**Proof sketch.** `vecAddModWords_encodeVector` at `c = 0^w` and
`listToNat_modulusNumeral`. -/
theorem vecAddModWords_modContext {q len : ℕ} [NeZero q] {w : ℕ} (hq : q ≤ 2 ^ w)
    (n : List Bool) (hn : n.length = len) (u v : Fin len → ZMod q) :
    vecAddModWords (modContext w q) n (Modular.encodeVector w u) (Modular.encodeVector w v) =
      Modular.encodeVector w (u + v) := by
  have h := vecAddModWords_encodeVector (List.replicate w false)
    (Candidates.natToList (w + 1) q) (by rwa [List.length_replicate])
    (listToNat_modulusNumeral hq) n hn u v
  rwa [List.length_replicate] at h

/-- **Subset sums in the canonical context**: for `q ≤ 2^w` and counters of lengths `n`, `m`,
`subsetSumModWords (modContext w q) nT mT (encodeMatrix w A) (ofFn r ++ extra) =
encodeVector w (Aᵀ *ᵥ r)`.

**Proof sketch.** `subsetSumModWords_encodeMatrix` at `c = 0^w` and
`listToNat_modulusNumeral`. -/
theorem subsetSumModWords_modContext {q m n : ℕ} [NeZero q] {w : ℕ} (hq : q ≤ 2 ^ w)
    (nT mT : List Bool) (hn : nT.length = n) (hm : mT.length = m)
    (A : Matrix (Fin m) (Fin n) (ZMod q)) (r : Fin m → Bool) (extra : List Bool) :
    subsetSumModWords (modContext w q) nT mT (Modular.encodeMatrix w A) (List.ofFn r ++ extra) =
      Modular.encodeVector w (A.transpose.mulVec fun i => ((r i).toNat : ZMod q)) := by
  have h := subsetSumModWords_encodeMatrix (List.replicate w false)
    (Candidates.natToList (w + 1) q) (by rwa [List.length_replicate])
    (listToNat_modulusNumeral hq) nT mT hn hm A r extra
  rwa [List.length_replicate] at h

/-- **Residue subset sums in the canonical context**: for `q ≤ 2^w` and a counter of length
`m`, `subsetSumModWords (modContext w q) [true] mT (encodeVector w b) (ofFn r ++ extra)` is
the `w`-bit numeral of `∑ i, b i * (r i).toNat`.

**Proof sketch.** `subsetSumModWords_encodeVector` at `c = 0^w` and
`listToNat_modulusNumeral`. -/
theorem subsetSumModWords_modContext_vector {q m : ℕ} [NeZero q] {w : ℕ} (hq : q ≤ 2 ^ w)
    (mT : List Bool) (hm : mT.length = m) (b : Fin m → ZMod q) (r : Fin m → Bool)
    (extra : List Bool) :
    subsetSumModWords (modContext w q) [true] mT (Modular.encodeVector w b)
        (List.ofFn r ++ extra) =
      Candidates.natToList w (∑ i, b i * ((r i).toNat : ZMod q)).val := by
  have h := subsetSumModWords_encodeVector (List.replicate w false)
    (Candidates.natToList (w + 1) q) (by rwa [List.length_replicate])
    (listToNat_modulusNumeral hq) mT hm b r extra
  rwa [List.length_replicate] at h

end TCSlib.Cryptography.Encoding.ModularArithmetic
