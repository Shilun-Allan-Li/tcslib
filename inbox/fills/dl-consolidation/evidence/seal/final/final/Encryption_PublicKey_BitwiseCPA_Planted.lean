/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Encryption.PublicKey.HybridMachine
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.RecordHandler
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Foundations.BitLists
/- DLC-SEAL Encryption_PublicKey_BitwiseCPA_Planted: whole-file closure seal of `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA/Planted.lean`. -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := []
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL Encryption_PublicKey_BitwiseCPA_Planted: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The planted bitwise ciphertext of the hybrid reduction

In the hybrid argument for the bitwise scheme under chosen-plaintext attack [PS10, p. 103, in
the game of Definition 171.5], the reduction holds a single-bit challenge ciphertext `c` and
answers the adversary's challenge `⟨m₀, m₁⟩` with the tuple whose block `j` is `c`, whose
blocks before `j` encrypt the bits of `m₁` and whose blocks after `j` encrypt the bits of `m₀`,
each with its own coin block. This file builds that answer, padded, as a polynomial-time string
function of the reduction's context and advice (`plantAns`), and the reduction's final bit
(`plantOut`), with their unfoldings.

## Main definitions

* `BitwiseSim.plantTuple`: the planted tuple, from the block encryptor `blockEncFun`.
* `BitwiseSim.plantAns`: the planted tuple padded with `padCt`.
* `BitwiseSim.plantOut`: the final bit, from the recorded bits `m₀_j`, `m₁_j`.

## Main results

* `BitwiseSim.plantTuple_spec`: the planted tuple on the hybrid layout.
* `BitwiseSim.plantOut_init`, `plantOut_recorded`: the final bit.
* `BitwiseSim.polyTimeComputable_plantAns`, `polyTimeComputable_plantOut`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 (the bitwise scheme and the hybrid argument) and §7.1.4, Definition 171.5.
-/

namespace TCSlib.Cryptography.Composability.BitwiseSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### List identities -/

/-- `List.ofFn` of a constant on a one-element type is a singleton:
`List.ofFn (fun _ : Fin p => b) = [b]` when `p = 1`. -/
theorem ofFn_const_of_eq_one {p : ℕ} (hp : p = 1) (b : Bool) :
    List.ofFn (fun _ : Fin p => b) = [b] := by
  subst hp
  rfl

/-- The first `j` bits of `List.ofFn m`, as a flattening of singletons (`p = 1`):
`(ofFn m).take j = (ofFn fun i : Fin j => ofFn fun _ : Fin p => m i).flatten`. -/
theorem take_ofFn_flatten {p n j : ℕ} (hp : p = 1) (m : Fin n → Bool) (hj : j ≤ n) :
    (List.ofFn m).take j =
      (List.ofFn fun i : Fin j => List.ofFn fun _ : Fin p => m (Fin.castLE hj i)).flatten := by
  rw [flatten_ofFn_singleton hp]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
    omega
  · intro t h₁ h₂
    simp only [List.getElem_take, List.getElem_ofFn]
    rfl

/-- The bits of `List.ofFn m` after the first `j + 1`, as a flattening of singletons (`p = 1`):
`(ofFn m).drop (j + 1) =
(ofFn fun i : Fin (n - j - 1) => ofFn fun _ : Fin p => m (j + 1 + i)).flatten`. -/
theorem drop_ofFn_flatten {p n j : ℕ} (hp : p = 1) (m : Fin n → Bool) (hj : j < n) :
    (List.ofFn m).drop (j + 1) =
      (List.ofFn fun i : Fin (n - j - 1) => List.ofFn fun _ : Fin p =>
        m ⟨j + 1 + i, by omega⟩).flatten := by
  rw [flatten_ofFn_singleton hp]
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_ofFn]
    omega
  · intro t h₁ h₂
    simp only [List.getElem_drop, List.getElem_ofFn]

/-! ### The planted tuple -/

/-- **The planted tuple** on `⟨⟨u, ⟨⟨pk, c⟩, ω⟩⟩, ⟨⟨u_j, ⟨u_b, Z⟩⟩, x⟩⟩` (unary parameter
`u = 1^n`, public key `pk`, single-bit ciphertext `c`, coins `ω`, `u_j = 1^j`,
`u_b = 1^{(j+1)·B(n)}`, challenge `x = m₀ ‖ m₁`): `T₁ ++ ⟨c, T₂⟩`, where `T₁` is the block
encryption (`blockEncFun`, one-bit blocks) of the first `j` bits of `m₁` with the coins `ω`,
and `T₂` that of the bits of `m₀` after the first `j + 1` with the coins of `ω` after the first
`(j + 1)·B(n)`. -/
def plantTuple (Enc : NUPPT) (w : List Bool) : List Bool :=
  blockEncFun Enc.output (.const 1) Enc.coins
      (blockState (pairFstD (pairFstD w)) (pairFstD (pairFstD (pairSndD (pairFstD w))))
        (((pairSndD (pairSndD w)).drop (pairFstD (pairFstD w)).length).take
          (pairFstD (pairFstD (pairSndD w))).length)
        (pairSndD (pairSndD (pairFstD w)))) ++
    pairEncode (pairSndD (pairFstD (pairSndD (pairFstD w))))
      (blockEncFun Enc.output (.const 1) Enc.coins
        (blockState (pairFstD (pairFstD w)) (pairFstD (pairFstD (pairSndD (pairFstD w))))
          (((pairSndD (pairSndD w)).take (pairFstD (pairFstD w)).length).drop
            ((pairFstD (pairFstD (pairSndD w))).length + 1))
          ((pairSndD (pairSndD (pairFstD w))).drop
            (pairFstD (pairSndD (pairFstD (pairSndD w)))).length)))

/-- The defining equation of `plantTuple`: on
`⟨⟨1^n, ⟨⟨pk, c⟩, ω⟩⟩, ⟨⟨1^j, ⟨1^{(j+1)B}, Z⟩⟩, m₀ ‖ m₁⟩⟩` it is `T₁ ++ ⟨c, T₂⟩`, with `T₁` the
one-bit block encryption of the first `j` bits of `m₁` on `ω` and `T₂` that of the bits of `m₀`
after the first `j + 1` on `ω.drop ((j+1)B)`. -/
theorem plantTuple_eq (Enc : NUPPT) (w : List Bool) :
    plantTuple Enc w =
      blockEncFun Enc.output (.const 1) Enc.coins
          (blockState (pairFstD (pairFstD w)) (pairFstD (pairFstD (pairSndD (pairFstD w))))
            (((pairSndD (pairSndD w)).drop (pairFstD (pairFstD w)).length).take
              (pairFstD (pairFstD (pairSndD w))).length)
            (pairSndD (pairSndD (pairFstD w)))) ++
        pairEncode (pairSndD (pairFstD (pairSndD (pairFstD w))))
          (blockEncFun Enc.output (.const 1) Enc.coins
            (blockState (pairFstD (pairFstD w)) (pairFstD (pairFstD (pairSndD (pairFstD w))))
              (((pairSndD (pairSndD w)).take (pairFstD (pairFstD w)).length).drop
                ((pairFstD (pairFstD (pairSndD w))).length + 1))
              ((pairSndD (pairSndD (pairFstD w))).drop
                (pairFstD (pairSndD (pairFstD (pairSndD w)))).length))) := rfl

/-- The planted tuple is polynomial-time.

**Proof sketch.** Pair projections for the slots; `polyTimeComputable_pairTakePoly` and
`polyTimeComputable_pairDropPoly` (`p := var`) cut the challenge and the coins at the unary
lengths; `blockEncFun_poly` encrypts; `append` and `pairEncode` assemble. -/
theorem polyTimeComputable_plantTuple (Enc : NUPPT) : PolyTimeComputable (plantTuple Enc) := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  have hu := hF.comp hF
  have hpk := hF.comp (hF.comp (hS.comp hF))
  have hc := hS.comp (hF.comp (hS.comp hF))
  have hω := hS.comp (hS.comp hF)
  have huj := hF.comp (hF.comp hS)
  have hub := hF.comp (hS.comp (hF.comp hS))
  have hx := hS.comp hS
  have hm₁ := (polyTimeComputable_pairDropPoly .var).comp (hu.pairEncode hx)
  have hm₀ := (polyTimeComputable_pairTakePoly .var).comp (hu.pairEncode hx)
  have hM₁ := (polyTimeComputable_pairTakePoly .var).comp (huj.pairEncode hm₁)
  have hM₂ := (polyTimeComputable_pairDropPoly .var).comp
    (((polyTimeComputable_const [true]).append huj).pairEncode hm₀)
  have hω₂ := (polyTimeComputable_pairDropPoly .var).comp (hub.pairEncode hω)
  have hE := blockEncFun_poly Enc.polyTimeComputable_output (.const 1) Enc.coins
  have hT₁ := hE.comp (hu.pairEncode (hpk.pairEncode (hM₁.pairEncode hω)))
  have hT₂ := hE.comp (hu.pairEncode (hpk.pairEncode (hM₂.pairEncode hω₂)))
  have h := hT₁.append (hc.pairEncode hT₂)
  refine h.congr fun w => ?_
  simp only [plantTuple_eq, blockState_eq, Function.comp_apply, pairFstD_pairEncode,
    pairSndD_pairEncode, PolyExpr.eval_var, List.cons_append, List.nil_append, List.length_cons]

/-- **The planted tuple on the hybrid layout.** With `u = 1^n`, coins `ω = coinBlocks v` (the
blocks `v_i` of `Enc`), `u_j = 1^j`, `u_b = 1^{(j+1)·B(n)}` (`j < n`) and challenge
`List.ofFn m₀ ++ List.ofFn m₁`, the planted tuple is the tuple
`⟨c_0, …, c_{n-1}⟩` with `c_i = Enc(1^n, ⟨pk, [m₁ i]⟩; v_i)` for `i < j`, `c_j = c`, and
`c_i = Enc(1^n, ⟨pk, [m₀ i]⟩; v_i)` for `i > j`.

**Proof sketch.** The cut challenge pieces are flattenings of singletons
(`take_ofFn_flatten`, `drop_ofFn_flatten`), so `blockEncFun_flatten` unfolds both block
encryptions with coin segments `coinBlock B i ω` and `coinBlock B i (ω.drop ((j+1)·B))`; these
are the blocks `v_i` and `v_{j+1+i}` (`coinBlock_ofFn_coinBlocks`, `coinBlock_drop`), and the
whole tuple splits at `j` (`encodeList_ofFn_split`). -/
theorem plantTuple_spec (Enc : NUPPT) (hEnc : Enc.Uniform) (n j : ℕ) (hj : j < n)
    (pk c Z : List Bool) (v : Fin n → Enc.Coins n) (m₀ m₁ : Fin n → Bool) :
    plantTuple Enc (pairEncode
        (seedIn n (pairEncode pk c) (List.ofFn (coinBlocks n (Enc.coinLen n) v)))
        (pairEncode (pairEncode (List.replicate j true)
            (pairEncode (List.replicate ((j + 1) * Enc.coinLen n) true) Z))
          (List.ofFn m₀ ++ List.ofFn m₁))) =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        if (i : ℕ) < j then Enc.runAt n (pairEncode pk [m₁ i]) (v i)
        else if (i : ℕ) = j then c
        else Enc.runAt n (pairEncode pk [m₀ i]) (v i)) := by
  have h1 : (PolyExpr.const 1).eval n = 1 := PolyExpr.eval_const 1 n
  have hlen : (List.ofFn m₀).length = n := List.length_ofFn
  simp only [plantTuple_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
  rw [List.drop_left' hlen, List.take_left' hlen, take_ofFn_flatten h1 m₁ hj.le,
    drop_ofFn_flatten h1 m₀ hj,
    blockEncFun_flatten Enc hEnc (.const 1) n (by rw [h1]; exact Nat.one_pos) pk j,
    blockEncFun_flatten Enc hEnc (.const 1) n (by rw [h1]; exact Nat.one_pos) pk (n - j - 1),
    encodeList_ofFn_split _ ⟨j, hj⟩]
  congr 1
  · refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
    have hi : (i : ℕ) < j := i.isLt
    rw [ofFn_const_of_eq_one h1, ← Fin.coe_castLE hj.le i, coinBlock_ofFn_coinBlocks,
      ← NUPPT.runAt_eq]
    simp only [Fin.coe_castLE, hi, if_true]
  · congr 1
    · simp
    · refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
      have hidx : coinBlock (Enc.coinLen n) (j + 1 + i)
          (List.ofFn (coinBlocks n (Enc.coinLen n) v)) =
          List.ofFn (v ⟨j + 1 + i, by have := i.isLt; omega⟩) :=
        coinBlock_ofFn_coinBlocks n (Enc.coinLen n) v ⟨j + 1 + i, by have := i.isLt; omega⟩
      rw [ofFn_const_of_eq_one h1, coinBlock_drop, hidx, ← NUPPT.runAt_eq]
      simp only [Fin.val_mk]
      rw [if_neg (by omega), if_neg (by omega)]

/-! ### The padded answer -/

/-- **The reduction's challenge answer**: the planted tuple padded to `L(n)` bits, with `n` read
from the unary parameter. -/
def plantAns (Enc : NUPPT) (L : PolyExpr) (w : List Bool) : List Bool :=
  padCt (L.eval (pairFstD (pairFstD w)).length) (plantTuple Enc w)

/-- The defining equation of `plantAns`: `plantAns Enc L w = padCt (L(n)) (plantTuple Enc w)`,
with `n` the length of the unary parameter `pairFstD (pairFstD w)`. -/
theorem plantAns_eq (Enc : NUPPT) (L : PolyExpr) (w : List Bool) :
    plantAns Enc L w = padCt (L.eval (pairFstD (pairFstD w)).length) (plantTuple Enc w) := rfl

/-- The padded answer is polynomial-time (`padCt_eq`: the padding is a cut of `1^{L(n)}`). -/
theorem polyTimeComputable_plantAns (Enc : NUPPT) (L : PolyExpr) :
    PolyTimeComputable (plantAns Enc L) := by
  have ht := polyTimeComputable_plantTuple Enc
  have h := ht.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
    ((ht.pairEncode (polyTimeComputable_const [])).pairEncode
      ((polyTimeComputable_unaryPoly L).comp
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD))))
  refine h.congr fun w => ?_
  simp [plantAns_eq, padCt_eq, Function.comp_apply, length_pairEncode]

/-! ### The final bit -/

/-- **The reduction's final bit** on `⟨ctx, ⟨⟨aux, t⟩, a⟩⟩` with `ctx = ⟨1^n, …⟩`,
`aux = ⟨1^j, …⟩` and `t = asked :: x`: with `b₀ = x_j`, `b₁ = x_{n+j}` (the bits `m₀_j`, `m₁_j`
of the recorded challenge), `[a]` if `(b₀, b₁) = (0, 1)`, `[¬a]` if `(b₀, b₁) = (1, 0)`, and `[0]`
if `b₀ = b₁` or no challenge was asked. -/
def plantOut (w : List Bool) : List Bool :=
  if (pairSndD (pairFstD (pairSndD w))).headD false then
    if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop
        (pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then
      if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop ((pairFstD (pairFstD w)) ++
          pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then [false]
      else [!(pairSndD (pairSndD w)).headD false]
    else
      if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop ((pairFstD (pairFstD w)) ++
          pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then
        [(pairSndD (pairSndD w)).headD false]
      else [false]
  else [false]

/-- The defining equation of `plantOut`: on `⟨ctx, ⟨⟨aux, t⟩, a⟩⟩` with `t = asked :: x`,
`b₀ = x_j` and `b₁ = x_{n+j}`, the output is `[a]` if `(b₀, b₁) = (0, 1)`, `[¬a]` if
`(b₀, b₁) = (1, 0)`, and `[0]` if `b₀ = b₁` or no challenge was asked. -/
theorem plantOut_eq (w : List Bool) :
    plantOut w =
      if (pairSndD (pairFstD (pairSndD w))).headD false then
        if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop
            (pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then
          if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop ((pairFstD (pairFstD w)) ++
              pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then [false]
          else [!(pairSndD (pairSndD w)).headD false]
        else
          if (((pairSndD (pairFstD (pairSndD w))).drop 1).drop ((pairFstD (pairFstD w)) ++
              pairFstD (pairFstD (pairFstD (pairSndD w)))).length).headD false then
            [(pairSndD (pairSndD w)).headD false]
          else [false]
      else [false] := rfl

/-- Without a recorded challenge the final bit is `[0]`:
`plantOut ⟨ctx, ⟨⟨aux, 0 :: y⟩, a⟩⟩ = [false]`. -/
theorem plantOut_init (ctx aux y a : List Bool) :
    plantOut (pairEncode ctx (pairEncode (pairEncode aux (false :: y)) a)) = [false] := by
  simp only [plantOut_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons,
    Bool.false_eq_true, if_false]

/-- With the challenge `l` recorded and the advice `⟨1^j, …⟩`, the final bit is
`(l_j ≠ l_{n+j}) ∧ (a ≠ l_j)`. -/
theorem plantOut_recorded (n j : ℕ) (z ω rest l a : List Bool) :
    plantOut (pairEncode (seedIn n z ω)
        (pairEncode (pairEncode (pairEncode (List.replicate j true) rest) (true :: l)) a)) =
      [(l.getD j false != l.getD (n + j) false) && (a.headD false != l.getD j false)] := by
  simp only [plantOut_eq, seedIn_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons,
    if_true, List.drop_succ_cons, List.drop_zero, List.length_append, List.length_replicate,
    headD_drop]
  cases l.getD j false <;> cases l.getD (n + j) false <;> cases a.headD false <;> rfl

/-- The final bit is polynomial-time. -/
theorem polyTimeComputable_plantOut : PolyTimeComputable plantOut := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  have ht : PolyTimeComputable fun w => pairSndD (pairFstD (pairSndD w)) := hS.comp (hF.comp hS)
  have hx : PolyTimeComputable fun w => (pairSndD (pairFstD (pairSndD w))).drop 1 :=
    polyTimeComputable_tail.comp ht
  have huj : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD (pairSndD w))) :=
    hF.comp (hF.comp (hF.comp hS))
  have hb₀ := polyTimeComputable_headD.comp
    ((polyTimeComputable_pairDropPoly .var).comp (huj.pairEncode hx))
  have hb₁ := polyTimeComputable_headD.comp
    ((polyTimeComputable_pairDropPoly .var).comp (((hF.comp hF).append huj).pairEncode hx))
  have ha : PolyTimeComputable fun w => [(pairSndD (pairSndD w)).headD false] :=
    polyTimeComputable_headD.comp (hS.comp hS)
  have h := polyTimeComputable_ite (polyTimeComputable_headD.comp ht)
    (polyTimeComputable_ite hb₀
      (polyTimeComputable_ite hb₁ (polyTimeComputable_const [false]) (polyTimeComputable_not ha))
      (polyTimeComputable_ite hb₁ ha (polyTimeComputable_const [false])))
    (polyTimeComputable_const [false])
  refine h.congr fun w => ?_
  simp only [plantOut_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var]

end TCSlib.Cryptography.Composability.BitwiseSim
