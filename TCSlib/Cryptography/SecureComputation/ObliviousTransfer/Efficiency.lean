/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: Protocol 160.4 runs in polynomial time

Both parties of a protocol of the shape of [PS10, Protocol 160.4] (`OT.IsOT`) are efficient
strategies, and the messages of its honest executions are polynomially bounded: the
efficiency requirement `Functionality.PolyTime` of Definition 155.1 for `otFunctionality`.

Each next-message function branches on the number of messages received, which the raw machine
reads off the encoded history `⟨m₁, ⟨m₂, …⟩⟩` by emptiness tests of its iterated second
components (`polyTimeComputable_isNil`); the branches are compositions of `Gen`, the sampler and
the inverter (uniform machines, `NUPPT.polyTimeComputable_output`), the evaluator (`eval_poly`),
`H`, pairing and one XOR. The machines are `NUPPT.ofPolyTimeUniform` of these raw functions.

## Main definitions

* `OT.senderRaw`, `OT.receiverRaw`: the raw functions of the two parties' machines.

## Main results

* `OT.polyTimeComputable_senderRaw`, `OT.polyTimeComputable_receiverRaw`: they are
  polynomial-time.
* `OT.senderRaw_advInput`, `OT.receiverRaw_advInput`: they compute the next messages.
* `OT.length_runAtL_le`: the output-length bound of a machine on an untyped tape.
* `OT.polyTime_of_isOT`: [PS10, Protocol 160.4] runs in polynomial time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1 and Protocol 160.4 (book pp. 155, 160).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-! ### Reading the encoded history -/

/-- The first message of a history is the first projection of its encoding:
`hist.headD [] = fst (encodeMsgs hist)` (`Strategy.pairFstD_encodeMsgs`). -/
theorem headD_eq_pairFstD (hist : List (List Bool)) :
    hist.headD [] = pairFstD (Strategy.encodeMsgs hist) :=
  (Strategy.pairFstD_encodeMsgs hist).symm

/-- The second projection of the empty word is empty, `pairSndD [] = []`
(`BinArith.iterate_pairSndD_nil` at `1`). -/
theorem pairSndD_nil' : pairSndD ([] : List Bool) = [] :=
  BinArith.iterate_pairSndD_nil 1

/-- The second message of a history is read off its encoding:
`hist.getD 1 [] = fst (snd (encodeMsgs hist))`. -/
theorem getD_one_eq (hist : List (List Bool)) :
    hist.getD 1 [] = pairFstD (pairSndD (Strategy.encodeMsgs hist)) := by
  rcases hist with _ | ⟨m, _ | ⟨m', rest⟩⟩
  · rw [Strategy.encodeMsgs_nil, pairSndD_nil', pairFstD_nil]
    rfl
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, pairSndD_pairEncode, pairFstD_nil]
    rfl
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, pairSndD_pairEncode,
      pairFstD_pairEncode]
    rfl

/-- A uniform machine's activation is its output on the layout with empty advice:
`A.runAtL n y r = A.output (layout 1^n y [] r)` (`NUPPT.runAtL_eq_output_layout`). -/
theorem runAtL_eq_layout {A : NUPPT} (hA : A.Uniform) (n : ℕ) (y r : List Bool) :
    A.runAtL n y r = A.output (NUPPT.layout (List.replicate n true) y [] r) := by
  rw [NUPPT.runAtL_eq_output_layout, NUPPT.Uniform.advice_eq hA]

/-- The raw layout of a strategy activation: `⟨⟨advInput n a, []⟩, r⟩ = layout 1^n a [] r`. -/
theorem advInput_layout (n : ℕ) (a r : List Bool) :
    pairEncode (pairEncode (NUPPT.advInput n a) []) r =
      NUPPT.layout (List.replicate n true) a [] r := by
  rw [NUPPT.advInput_eq, NUPPT.layout_eq]

/-! ### Alice's machine -/

/-- `Gen`'s output on the raw layout `z`: `Gen(inParam z; inCoins z)` with empty argument,
`genRaw T z = Gen.output (layout (inParam z) [] [] (inCoins z))`. -/
def genRaw (z : List Bool) : List Bool :=
  T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z))

/-- The defining equation of `genRaw`: `genRaw T z = Gen.output (layout (inParam z) [] []
(inCoins z))`. -/
theorem genRaw_eq (z : List Bool) :
    genRaw T z = T.gen.output (NUPPT.layout (NUPPT.inParam z) [] [] (NUPPT.inCoins z)) := rfl

/-- `genRaw` is polynomial-time: `PolyTimeComputable (genRaw T)`. -/
theorem polyTimeComputable_genRaw : PolyTimeComputable (genRaw T) :=
  (T.gen.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam (polyTimeComputable_const [])
    (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)).congr
    fun z => (genRaw_eq T z).symm

/-- Alice's mask on the raw layout `z`, for the element `yj` and the bit word `bt`:
`zipWith xor (H ⟨i, Inv(⟨t, yj⟩; 1^{inv})⟩) bt` with `⟨i, t⟩ = genRaw T z`. -/
def maskRaw (z yj bt : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (pairFstD (genRaw T z))
    (T.inv.output (NUPPT.layout (NUPPT.inParam z) (pairEncode (pairSndD (genRaw T z)) yj) []
      (List.replicate (T.inv.coins.eval (NUPPT.inParam z).length) true))))) bt

/-- The defining equation of `maskRaw`: `maskRaw T H z yj bt =
zipWith xor (H ⟨i, Inv(inParam z, ⟨t, yj⟩; 1^{inv})⟩) bt` with `⟨i, t⟩ = genRaw T z`. -/
theorem maskRaw_eq (z yj bt : List Bool) :
    maskRaw T H z yj bt =
      List.zipWith xor (H (pairEncode (pairFstD (genRaw T z))
        (T.inv.output (NUPPT.layout (NUPPT.inParam z) (pairEncode (pairSndD (genRaw T z)) yj) []
          (List.replicate (T.inv.coins.eval (NUPPT.inParam z).length) true))))) bt := rfl

/-- The raw mask is polynomial-time in `z` for polynomial-time `yj` and `bt`:
`PolyTimeComputable (fun z => maskRaw T H z (Y z) (B z))` for polynomial-time `H`, `Y`, `B`.

**Proof sketch.** Pair the index (first projection of `genRaw`) with the inverter's output on
the layout of `1^n`, `⟨t, yj⟩` and the all-`true` tape (`polyTimeComputable_unaryPoly`), apply
`H`, pair with `bt` and XOR (`polyTimeComputable_pairXor`). -/
theorem polyTimeComputable_maskRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    {Y B : List Bool → List Bool} (hY : PolyTimeComputable Y) (hB : PolyTimeComputable B) :
    PolyTimeComputable fun z => maskRaw T H z (Y z) (B z) := by
  have hG := polyTimeComputable_genRaw T
  have hinv := T.inv.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam ((polyTimeComputable_pairSndD.comp' hG).pairEncode hY)
    (polyTimeComputable_const [])
    ((polyTimeComputable_unaryPoly T.inv.coins).comp' NUPPT.polyTimeComputable_inParam))
  have h := polyTimeComputable_pairXor.comp'
    ((hH.comp' ((polyTimeComputable_pairFstD.comp' hG).pairEncode hinv)).pairEncode hB)
  refine h.congr fun z => ?_
  rw [maskRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]

/-- **Alice's raw function** on `z = layout 1^{|x|} ⟨⟨x, y⟩, w⟩ [] r` with `w` the encoded
history: `fst (genRaw z)` if `w = []`; the two masks if `snd w = []`; else `[]`. -/
def senderRaw (z : List Bool) : List Bool :=
  if decide (pairSndD (NUPPT.inArg z) = []) then pairFstD (genRaw T z)
  else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then
    pairEncode
      (maskRaw T H z (pairFstD (pairFstD (pairSndD (NUPPT.inArg z))))
        [(pairSndD (pairFstD (NUPPT.inArg z))).headD false])
      (maskRaw T H z (pairSndD (pairFstD (pairSndD (NUPPT.inArg z))))
        [((pairSndD (pairFstD (NUPPT.inArg z))).drop 1).headD false])
  else []

/-- The defining equation of `senderRaw`: with `w = snd (inArg z)`, `fst (genRaw T z)` if
`w = []`, the two raw masks if `snd w = []`, else `[]`. -/
theorem senderRaw_eq (z : List Bool) :
    senderRaw T H z =
      if decide (pairSndD (NUPPT.inArg z) = []) then pairFstD (genRaw T z)
      else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then
        pairEncode
          (maskRaw T H z (pairFstD (pairFstD (pairSndD (NUPPT.inArg z))))
            [(pairSndD (pairFstD (NUPPT.inArg z))).headD false])
          (maskRaw T H z (pairSndD (pairFstD (pairSndD (NUPPT.inArg z))))
            [((pairSndD (pairFstD (NUPPT.inArg z))).drop 1).headD false])
      else [] := rfl

/-- **Alice's raw function is polynomial-time** (`polyTimeComputable_ite` on the two emptiness
tests `polyTimeComputable_isNil`, `polyTimeComputable_maskRaw`, `polyTimeComputable_headD`,
`polyTimeComputable_tail`): `PolyTimeComputable (senderRaw T H)` for polynomial-time `H`. -/
theorem polyTimeComputable_senderRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (senderRaw T H) := by
  have hw := polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg
  have hy := polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg)
  have hm := polyTimeComputable_pairFstD.comp' hw
  have h₁ := polyTimeComputable_maskRaw T hH (polyTimeComputable_pairFstD.comp' hm)
    (polyTimeComputable_headD.comp' hy)
  have h₂ := polyTimeComputable_maskRaw T hH (polyTimeComputable_pairSndD.comp' hm)
    (polyTimeComputable_headD.comp' (polyTimeComputable_tail.comp' hy))
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp' hw)
    (polyTimeComputable_pairFstD.comp' (polyTimeComputable_genRaw T))
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' (polyTimeComputable_pairSndD.comp' hw))
      (h₁.pairEncode h₂) (polyTimeComputable_const []))
  exact h.congr fun z => (senderRaw_eq T H z).symm

/-- `Gen`'s output on the layout of an activation at `1^{|x|}` is `Gen(1^{|x|}; r)`:
`genRaw T (layout 1^n a [] r) = Gen.runAtL n [] r`. -/
theorem genRaw_layout (n : ℕ) (a r : List Bool) :
    genRaw T (NUPPT.layout (List.replicate n true) a [] r) = T.gen.runAtL n [] r := by
  rw [genRaw_eq, NUPPT.inParam_layout, NUPPT.inCoins_layout, runAtL_eq_layout T.gen_uniform]

/-- The raw mask on the layout of an activation is Alice's mask:
`maskRaw T H (layout 1^n a [] r) yj [c] = mask T H n i t yj c` with `⟨i, t⟩ = Gen(1^n; r)`. -/
theorem maskRaw_layout (n : ℕ) (a r yj : List Bool) (c : Bool) :
    maskRaw T H (NUPPT.layout (List.replicate n true) a [] r) yj [c] =
      mask T H n (pairFstD (T.gen.runAtL n [] r)) (pairSndD (T.gen.runAtL n [] r)) yj c := by
  rw [maskRaw_eq, genRaw_layout, NUPPT.inParam_layout, List.length_replicate, mask_eq,
    runAtL_eq_layout T.inv_uniform]

/-- `y.getD 0 false` is the head bit: `y.getD 0 false = y.headD false`.
It is the public `TCSlib.Cryptography.headD_drop` at `i = 0`, reversed. -/
theorem getD_zero_eq (y : List Bool) : y.getD 0 false = y.headD false := by
  simpa only [List.drop_zero] using
    (TCSlib.Cryptography.headD_drop y 0 false).symm

/-- `y.getD 1 false` is the head bit of `y.drop 1`:
`y.getD 1 false = (y.drop 1).headD false`.
It is the public `TCSlib.Cryptography.headD_drop` at `i = 1`, reversed. -/
theorem getD_one_eq' (y : List Bool) : y.getD 1 false = (y.drop 1).headD false :=
  (TCSlib.Cryptography.headD_drop y 1 false).symm

/-- **Alice's raw function computes her next message**: on the raw input of the activation
`⟨⟨advInput |x| ⟨⟨x, y⟩, encodeMsgs hist⟩, []⟩, r⟩` it returns `senderNext T H x y r hist`:
`senderRaw T H ⟨⟨advInput |x| ⟨⟨x, y⟩, encodeMsgs hist⟩, []⟩, r⟩ =
senderNext T H x y r hist`.

**Proof sketch.** Cases on the history: `[]` (the encoding is empty), `[m]` (its second
projection is empty), and two or more messages (neither is empty); `genRaw_layout`,
`maskRaw_layout` and `getD_zero_eq`, `getD_one_eq'` identify the branches with
`senderNext_nil`, `senderNext_single`, `senderNext_eq`. -/
theorem senderRaw_advInput (x y r : List Bool) (hist : List (List Bool)) :
    senderRaw T H (pairEncode (pairEncode (NUPPT.advInput x.length
      (pairEncode (pairEncode x y) (Strategy.encodeMsgs hist))) []) r) =
      senderNext T H x y r hist := by
  rw [advInput_layout, senderRaw_eq, NUPPT.inArg_layout, genRaw_layout, pairSndD_pairEncode,
    pairFstD_pairEncode, pairSndD_pairEncode]
  rcases hist with _ | ⟨m, _ | ⟨m', rest⟩⟩
  · rw [Strategy.encodeMsgs_nil, if_pos (by simp), senderNext_nil]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, if_neg (by simp [pairEncode_ne_nil]),
      pairSndD_pairEncode, if_pos (by simp), pairFstD_pairEncode, senderNext_single,
      maskRaw_layout, maskRaw_layout, getD_zero_eq, getD_one_eq']
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, if_neg (by simp [pairEncode_ne_nil]),
      pairSndD_pairEncode, if_neg (by simp [pairEncode_ne_nil]), senderNext_eq,
      if_neg (by simp), if_neg (by simp)]

/-! ### Bob's machine -/

/-- Bob's sampled element on the raw layout `z`, at the index `i = fst w` of the encoded
history `w = snd (inArg z)`: the sampler on the first `coins_Sample(n)` coins. -/
def knownRaw (z : List Bool) : List Bool :=
  T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
    ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length)))

/-- The defining equation of `knownRaw`: `knownRaw T z = Sample(inParam z, fst w;
(inCoins z).take coins_Sample(n))` with `w = snd (inArg z)`. -/
theorem knownRaw_eq (z : List Bool) :
    knownRaw T z =
      T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
        ((NUPPT.inCoins z).take (T.sample.coins.eval (NUPPT.inParam z).length))) := rfl

/-- Bob's raw element on the raw layout `z`: the sampler on the coins after the first block,
`rawRaw T z = Sample(inParam z, fst w; (inCoins z).drop coins_Sample(n))` with
`w = snd (inArg z)`. -/
def rawRaw (z : List Bool) : List Bool :=
  T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
    ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length)))

/-- The defining equation of `rawRaw`: `rawRaw T z = Sample(inParam z, fst w;
(inCoins z).drop coins_Sample(n))` with `w = snd (inArg z)`. -/
theorem rawRaw_eq (z : List Bool) :
    rawRaw T z =
      T.sample.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (pairSndD (NUPPT.inArg z))) []
        ((NUPPT.inCoins z).drop (T.sample.coins.eval (NUPPT.inParam z).length))) := rfl

/-- Bob's output on the raw layout `z`: `H ⟨i, w⟩ ⊕ z_b` with `z_b` the second or first
projection of the second message, by the choice bit `b`:
`outRaw T H z = zipWith xor (H ⟨fst w, knownRaw T z⟩) z_b` with `w = snd (inArg z)`. -/
def outRaw (z : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
    (if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
      pairSndD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
    else pairFstD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z)))))

/-- The defining equation of `outRaw`: `outRaw T H z = zipWith xor (H ⟨fst w, knownRaw T z⟩) z_b`
with `z_b` the second or first projection of `fst (snd w)` by the choice bit. -/
theorem outRaw_eq (z : List Bool) :
    outRaw T H z =
      List.zipWith xor (H (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
        (if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
          pairSndD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))
        else pairFstD (pairFstD (pairSndD (pairSndD (NUPPT.inArg z))))) := rfl

/-- Bob's ordered pair on the raw layout `z`: `⟨w', eval ⟨i, w⟩⟩` if `b`, else
`⟨eval ⟨i, w⟩, w'⟩`, with `w = knownRaw T z`, `w' = rawRaw T z`, `i = fst (snd (inArg z))` and
`b = (snd (fst (inArg z))).headD false`. -/
def pairRaw (z : List Bool) : List Bool :=
  if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
    pairEncode (rawRaw T z)
      (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
  else
    pairEncode (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
      (rawRaw T z)

/-- The defining equation of `pairRaw`: `⟨rawRaw, eval ⟨fst w, knownRaw⟩⟩` if `b`, else
`⟨eval ⟨fst w, knownRaw⟩, rawRaw⟩`, i.e. `pairRaw T z = if b then ⟨rawRaw T z, eval ⟨fst w,
knownRaw T z⟩⟩ else ⟨eval ⟨fst w, knownRaw T z⟩, rawRaw T z⟩` with `w = snd (inArg z)`. -/
theorem pairRaw_eq (z : List Bool) :
    pairRaw T z =
      if (pairSndD (pairFstD (NUPPT.inArg z))).headD false then
        pairEncode (rawRaw T z)
          (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
      else
        pairEncode (T.eval (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (knownRaw T z)))
          (rawRaw T z) := rfl

/-- **Bob's raw function** on `z = layout 1^{|x|} ⟨⟨x, z_B⟩, w⟩ [] r`: `outRaw` if `w = []`, the
pair if `snd w = []`, `[]` if `snd (snd w) = []`, else `outRaw`. -/
def receiverRaw (z : List Bool) : List Bool :=
  if decide (pairSndD (NUPPT.inArg z) = []) then outRaw T H z
  else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then pairRaw T z
  else if decide (pairSndD (pairSndD (pairSndD (NUPPT.inArg z))) = []) then []
  else outRaw T H z

/-- The defining equation of `receiverRaw`: with `w = snd (inArg z)`, `outRaw` if `w = []`,
`pairRaw` if `snd w = []`, `[]` if `snd (snd w) = []`, else `outRaw`. -/
theorem receiverRaw_eq (z : List Bool) :
    receiverRaw T H z =
      if decide (pairSndD (NUPPT.inArg z) = []) then outRaw T H z
      else if decide (pairSndD (pairSndD (NUPPT.inArg z)) = []) then pairRaw T z
      else if decide (pairSndD (pairSndD (pairSndD (NUPPT.inArg z))) = []) then []
      else outRaw T H z := rfl

/-- **Bob's raw function is polynomial-time**: the sampler on the two coin blocks
(`polyTimeComputable_pairTakePoly`, `polyTimeComputable_pairDropPoly`), `eval_poly`, `H`, XOR,
pairing, and branches on the choice bit and three emptiness tests (`polyTimeComputable_ite`):
`PolyTimeComputable (receiverRaw T H)` for polynomial-time `H`.

**Proof sketch.** Build `knownRaw`, `rawRaw`, `outRaw`, `pairRaw` from the projections and the
machines' output functions, then nest three `polyTimeComputable_ite`. -/
theorem polyTimeComputable_receiverRaw {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (receiverRaw T H) := by
  have hU := NUPPT.polyTimeComputable_inParam
  have hw := polyTimeComputable_pairSndD.comp' NUPPT.polyTimeComputable_inArg
  have hi := polyTimeComputable_pairFstD.comp' hw
  have hb := polyTimeComputable_headD.comp' (polyTimeComputable_pairSndD.comp'
    (polyTimeComputable_pairFstD.comp' NUPPT.polyTimeComputable_inArg))
  have htake := (polyTimeComputable_pairTakePoly T.sample.coins).comp'
    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hdrop := (polyTimeComputable_pairDropPoly T.sample.coins).comp'
    (hU.pairEncode NUPPT.polyTimeComputable_inCoins)
  have hk : PolyTimeComputable (knownRaw T) :=
    (T.sample.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hi
      (polyTimeComputable_const []) htake)).congr fun z => by
        rw [knownRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  have hr : PolyTimeComputable (rawRaw T) :=
    (T.sample.polyTimeComputable_output.comp' (NUPPT.polyTimeComputable_layout hU hi
      (polyTimeComputable_const []) hdrop)).congr fun z => by
        rw [rawRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  have he := T.eval_poly.comp' (hi.pairEncode hk)
  have hm := polyTimeComputable_pairFstD.comp' (polyTimeComputable_pairSndD.comp' hw)
  have ho : PolyTimeComputable (outRaw T H) :=
    (polyTimeComputable_pairXor.comp' ((hH.comp' (hi.pairEncode hk)).pairEncode
      (polyTimeComputable_ite hb (polyTimeComputable_pairSndD.comp' hm)
        (polyTimeComputable_pairFstD.comp' hm)))).congr fun z => by
      rw [outRaw_eq, pairFstD_pairEncode, pairSndD_pairEncode]
  have hp : PolyTimeComputable (pairRaw T) :=
    (polyTimeComputable_ite hb (hr.pairEncode he) (he.pairEncode hr)).congr
      fun z => (pairRaw_eq T z).symm
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp' hw) ho
    (polyTimeComputable_ite (polyTimeComputable_isNil.comp' (polyTimeComputable_pairSndD.comp' hw))
      hp (polyTimeComputable_ite (polyTimeComputable_isNil.comp'
        (polyTimeComputable_pairSndD.comp' (polyTimeComputable_pairSndD.comp' hw)))
        (polyTimeComputable_const []) ho))
  exact h.congr fun z => (receiverRaw_eq T H z).symm

/-- On the layout of an activation, `knownRaw` is the sampler on the first coin block:
`knownRaw T (layout 1^n ⟨u, encodeMsgs hist⟩ [] r) =
Sample.runAtL n (hist.headD []) (r.take coins_Sample(n))`. -/
theorem knownRaw_layout (n : ℕ) (u r : List Bool) (hist : List (List Bool)) :
    knownRaw T
        (NUPPT.layout (List.replicate n true) (pairEncode u (Strategy.encodeMsgs hist)) [] r) =
      T.sample.runAtL n (hist.headD []) (r.take (T.sample.coins.eval n)) := by
  rw [knownRaw_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
    pairSndD_pairEncode, ← headD_eq_pairFstD, List.length_replicate,
    runAtL_eq_layout T.sample_uniform]

/-- On the layout of an activation, `rawRaw` is the sampler on the second coin block:
`rawRaw T (layout 1^n ⟨u, encodeMsgs hist⟩ [] r) =
Sample.runAtL n (hist.headD []) (r.drop coins_Sample(n))`. -/
theorem rawRaw_layout (n : ℕ) (u r : List Bool) (hist : List (List Bool)) :
    rawRaw T
        (NUPPT.layout (List.replicate n true) (pairEncode u (Strategy.encodeMsgs hist)) [] r) =
      T.sample.runAtL n (hist.headD []) (r.drop (T.sample.coins.eval n)) := by
  rw [rawRaw_eq, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
    pairSndD_pairEncode, ← headD_eq_pairFstD, List.length_replicate,
    runAtL_eq_layout T.sample_uniform]

/-- **Bob's raw function computes his next message**: on the raw input of the activation
`⟨⟨advInput |x| ⟨⟨x, z⟩, encodeMsgs hist⟩, []⟩, r⟩` it returns `receiverNext T H x z r hist`:
`receiverRaw T H ⟨⟨advInput |x| ⟨⟨x, z⟩, encodeMsgs hist⟩, []⟩, r⟩ =
receiverNext T H x z r hist`.

**Proof sketch.** `knownRaw_layout`, `rawRaw_layout`, `headD_eq_pairFstD` and `getD_one_eq`
identify `outRaw` with the last branch of `receiverNext` on every history and `pairRaw` with the
first. Then cases on the history: `[]`, `[i]`, two messages, and three or more, by the emptiness
of the iterated second projections of the encoding. -/
theorem receiverRaw_advInput (x z r : List Bool) (hist : List (List Bool)) :
    receiverRaw T H (pairEncode (pairEncode (NUPPT.advInput x.length
      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist))) []) r) =
      receiverNext T H x z r hist := by
  rw [advInput_layout, receiverRaw_eq]
  have hout : outRaw T H (NUPPT.layout (List.replicate x.length true)
      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r) =
      List.zipWith xor (H (pairEncode (hist.headD [])
        (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
        (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 [])) := by
    rw [outRaw_eq, knownRaw_layout, NUPPT.inArg_layout, pairSndD_pairEncode, pairFstD_pairEncode,
      pairSndD_pairEncode, ← headD_eq_pairFstD, getD_one_eq]
  have hpair : pairRaw T (NUPPT.layout (List.replicate x.length true)
      (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r) =
      receiverNext T H x z r [hist.headD []] := by
    rw [pairRaw_eq, knownRaw_layout, rawRaw_layout, NUPPT.inArg_layout, pairSndD_pairEncode,
      pairFstD_pairEncode, pairSndD_pairEncode, ← headD_eq_pairFstD, receiverNext_single]
  rw [hout, hpair, NUPPT.inArg_layout, pairSndD_pairEncode]
  rcases hist with _ | ⟨m, _ | ⟨m', _ | ⟨m'', rest⟩⟩⟩
  · rw [Strategy.encodeMsgs_nil, if_pos (by simp), receiverNext_eq,
      if_neg (show ¬([] : List (List Bool)).length = 1 by simp),
      if_neg (show ¬([] : List (List Bool)).length = 2 by simp)]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, if_neg (by simp [pairEncode_ne_nil]),
      pairSndD_pairEncode, if_pos (by simp), List.headD_cons]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode, if_pos (by simp),
      receiverNext_pair]
  · rw [Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
      if_neg (by simp [pairEncode_ne_nil]), pairSndD_pairEncode,
      if_neg (by simp [pairEncode_ne_nil]), receiverNext_eq,
      if_neg (show ¬(m :: m' :: m'' :: rest).length = 1 by simp),
      if_neg (show ¬(m :: m' :: m'' :: rest).length = 2 by simp)]

/-! ### Message lengths -/

/-- **The output-length bound on an untyped tape of the right length**: `|A(1^n, y; r)| ≤
runLenPoly A Y (n)` whenever `|y| ≤ Y(n)` and `|r| = coins_A(n)` (the list form of
`NUPPT.length_runAt_le_runLenPoly`, through `List.ofFn_get`). -/
theorem length_runAtL_le (A : NUPPT) {Y : PolyExpr} (n : ℕ) {y r : List Bool}
    (hy : y.length ≤ Y.eval n) (hr : r.length = A.coins.eval n) :
    (A.runAtL n y r).length ≤ (A.runLenPoly Y).eval n := by
  have hr' : r.length = A.coinLen n := hr.trans (A.coinLen_eq n).symm
  have h := A.length_runAt_le_runLenPoly n hy (fun j => r.get (Fin.cast hr'.symm j))
  rwa [NUPPT.runAt_eq, ← List.ofFn_congr hr' r.get, List.ofFn_get] at h

/-- A mask has at most one bit: `|zipWith xor w [a]| ≤ 1`. -/
theorem length_zipWith_singleton_le (w : List Bool) (a : Bool) :
    (List.zipWith xor w [a]).length ≤ 1 := by
  rw [List.length_zipWith, List.length_singleton]
  exact Nat.min_le_right _ _

/-- Alice's mask has at most one bit: `|mask T H n i t yj a| ≤ 1`. -/
theorem length_mask_le (n : ℕ) (i t yj : List Bool) (a : Bool) :
    (mask T H n i t yj a).length ≤ 1 := by
  rw [mask_eq]
  exact length_zipWith_singleton_le _ a

/-- **The messages of Protocol 160.4 are polynomially bounded**: for a protocol of its shape there
is a polynomial `B` with `|msg| ≤ B(n)` for every message of every honest execution on `1^n`.

**Proof sketch.** The transcript is `([y, []], [i, z, []])` (`transcriptWith_isOT`). The index
has `|i| ≤ Q₁(n)` (`Gen`'s `runLenPoly`); the two samples have `≤ Q₂(n)` (the sampler's
`runLenPoly` at `Q₁`, the coin blocks having `coins_Sample(n)` bits); the evaluation has
`≤ Q₃(n)` (the evaluator's polynomial bound at `2Q₁ + 2 + Q₂`); so `|y| ≤ 3(Q₂ + Q₃) + 2`.
The masks have one bit each, so `|z| ≤ 5`. Take `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5`. -/
theorem exists_messages_le {π : Protocol} (hπ : IsOT T H π) :
    ∃ B : PolyExpr, ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
      (y : Fin (otFunctionality.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)),
      ∀ msg ∈ (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).1 ++
          (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).2,
        msg.length ≤ B.eval n := by
  obtain ⟨-, -, hPc, hVc, -, -⟩ := (isOT_iff T H π).1 hπ
  obtain ⟨C, c, hC⟩ := T.eval_poly.output_length_le
  set Q₁ : PolyExpr := T.gen.runLenPoly (.const 0) with hQ₁
  set Q₂ : PolyExpr := T.sample.runLenPoly Q₁ with hQ₂
  set Q₃ : PolyExpr := (PolyExpr.normal C c).subst
    (.add (.add (.mul (.const 2) Q₁) (.const 2)) Q₂) with hQ₃
  refine ⟨.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2)) (.const 5)),
    fun n x y r msg hmsg => ?_⟩
  suffices key : ∀ (w a b : List Bool) (r : π.ExecCoins π.P w),
      ∀ msg ∈ (π.transcript w a b r).1 ++ (π.transcript w a b r).2,
        msg.length ≤ (PolyExpr.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2))
          (.const 5))).eval w.length by
    have h := key _ _ _ r msg hmsg
    rwa [List.length_replicate] at h
  intro w a b r msg hmsg
  rw [Protocol.transcript_eq_transcriptWith, transcriptWith_isOT T H hπ] at hmsg
  -- the coin lengths
  have hrA : (List.ofFn r.1).length = T.gen.coins.eval w.length := by
    rw [List.length_ofFn, Strategy.coinLen_eq, hPc]
  have hrB : (List.ofFn r.2).length =
      T.sample.coins.eval w.length + T.sample.coins.eval w.length := by
    rw [List.length_ofFn, Strategy.coinLen_eq, hVc, PolyExpr.eval_add]
  -- the index
  set i := pairFstD (T.gen.runAtL w.length [] (List.ofFn r.1)) with hi_def
  have hi : i.length ≤ Q₁.eval w.length :=
    (length_pairFstD_le _).trans (length_runAtL_le T.gen w.length (by simp) hrA)
  -- the two samples
  have hk : (T.sample.runAtL w.length i
      ((List.ofFn r.2).take (T.sample.coins.eval w.length))).length ≤ Q₂.eval w.length :=
    length_runAtL_le T.sample w.length hi (by rw [List.length_take, hrB]; omega)
  have hd : (T.sample.runAtL w.length i
      ((List.ofFn r.2).drop (T.sample.coins.eval w.length))).length ≤ Q₂.eval w.length :=
    length_runAtL_le T.sample w.length hi (by rw [List.length_drop, hrB]; omega)
  -- the evaluation
  have he : (T.eval (pairEncode i (T.sample.runAtL w.length i
      ((List.ofFn r.2).take (T.sample.coins.eval w.length))))).length ≤ Q₃.eval w.length := by
    refine (hC _).trans ?_
    rw [hQ₃, PolyExpr.eval_subst, PolyExpr.eval_normal]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp only [length_pairEncode, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  have hB : ∀ k, k ≤ Q₁.eval w.length + (3 * (Q₂.eval w.length + Q₃.eval w.length) + 2) + 5 →
      k ≤ (PolyExpr.add Q₁ (.add (.add (.mul (.const 3) (.add Q₂ Q₃)) (.const 2))
        (.const 5))).eval w.length := by
    intro k hk'
    simpa only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const] using hk'
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hmsg
  refine hB _ ?_
  rcases hmsg with h | h | h | h | h <;> subst h
  · -- Bob's pair
    rw [receiverNext_single]
    split_ifs <;> simp only [length_pairEncode] <;> omega
  · simp
  · omega
  · -- Alice's masks
    rw [senderNext_single, length_pairEncode]
    refine le_trans (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2
      (length_mask_le T H _ _ _ _ _)) 2) (length_mask_le T H _ _ _ _ _)) ?_
    omega
  · simp

/-- **Protocol 160.4 runs in polynomial time** [PS10, Definition 155.1, efficiency]: for a
protocol of its shape with a polynomial-time `H`, both parties are efficient strategies (the
machines `ofPolyTimeUniform` of `senderRaw` and `receiverRaw`) and the honest messages are
polynomially bounded (`exists_messages_le`): `IsOT T H π → otFunctionality.PolyTime π`. -/
theorem polyTime_of_isOT {H : List Bool → List Bool} (hH : PolyTimeComputable H) {π : Protocol}
    (hπ : IsOT T H π) : otFunctionality.PolyTime π := by
  obtain ⟨hP, hV, hPc, hVc, -, -⟩ := (isOT_iff T H π).1 hπ
  refine (Functionality.polyTime_iff _ _).2 ⟨?_, ?_, exists_messages_le T H hπ⟩
  · refine (Strategy.efficient_iff _).2 ⟨NUPPT.ofPolyTimeUniform (polyTimeComputable_senderRaw T hH)
      T.gen.coins, NUPPT.ofPolyTimeUniform_uniform _ _,
      hPc.trans (NUPPT.coins_ofPolyTimeUniform _ _).symm, fun x z r hist => ?_⟩
    rw [Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, senderRaw_advInput, hP]
  · refine (Strategy.efficient_iff _).2 ⟨NUPPT.ofPolyTimeUniform
      (polyTimeComputable_receiverRaw T hH) (.add T.sample.coins T.sample.coins),
      NUPPT.ofPolyTimeUniform_uniform _ _,
      hVc.trans (NUPPT.coins_ofPolyTimeUniform _ _).symm, fun x z r hist => ?_⟩
    rw [Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, receiverRaw_advInput, hV]

end TCSlib.Cryptography.SecureComputation.OT
