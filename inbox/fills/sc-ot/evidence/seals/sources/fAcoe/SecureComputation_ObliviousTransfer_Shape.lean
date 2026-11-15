/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.SecureComputation.Defs
import TCSlib.Cryptography.Asymptotic.Collections
/- DLC-SEAL SecureComputation_ObliviousTransfer_Shape: whole-file closure seal of `TCSlib/Cryptography/SecureComputation/ObliviousTransfer/Shape.lean`, variant A (PolyExpr.eval open), coe (projection coercions open). -/
/-- Strip leading lambdas (seal harness). -/
partial def dlcStripLam : Lean.Expr → Lean.Expr
  | .lam _ _ b _ => dlcStripLam b
  | e => e

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := [`Complexity.PolyExpr.eval]
  let coeOpen : Bool := true
  let coeClasses : List Lean.Name := [`CoeFun, `Coe, `CoeSort, `CoeOut, `CoeTail, `CoeHead,
    `CoeTC, `CoeHTCT, `CoeDep]
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  let mut coeExcl : Array Lean.Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    if coeOpen && Lean.Meta.isInstanceCore env n then
      let isCoeCls := match d.type.getForallBody.getAppFn.constName? with
        | some c => coeClasses.contains c
        | none => false
      if isCoeCls then
        let body := dlcStripLam d.value
        let args := body.getAppArgs
        let projArg := match args.back? with
          | some a => match (dlcStripLam a).getAppFn.constName? with
            | some p => (env.getProjectionFnInfo? p).isSome
            | none => false
          | none => false
        if projArg then
          coeExcl := coeExcl.push n
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
  Lean.logInfo m!"DLC-SEAL SecureComputation_ObliviousTransfer_Shape: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded} coe-excluded={coeExcl.size} {coeExcl.toList}"


set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: the shape of Protocol 160.4 and its five moves

The proofs of [PS10, Proposition 161.5] are carried out for every protocol of the shape of
Protocol 160.4, stated here by its next-message functions. This module cannot import
`SecureComputation/ObliviousTransfer.lean`, which imports it, so the shape restates the bodies of
`otSender` and `otReceiver` (with `otMask`, `otKnown` and `otRaw` expanded); the owned file proves
that `otProtocol` has this shape from its published field equations.

## Main definitions

* `OT.mask`, `OT.senderNext`, `OT.receiverNext`: Alice's mask and the two next-message
  functions of [PS10, Protocol 160.4].
* `OT.IsOT`: a protocol of the shape of Protocol 160.4.

## Main results

* `OT.senderNext_nil`, `OT.senderNext_single`, `OT.senderNext_pair`, `OT.receiverNext_single`,
  `OT.receiverNext_pair`: the messages on histories of length `0`, `1` and `2`.
* `OT.exec_five`: the five moves of a prover-first execution.
* `OT.transcriptWith_isOT`: the transcript of a protocol of the shape of Protocol 160.4.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Protocol 160.4 (book p. 160).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-- **Alice's mask** [PS10, Protocol 160.4]: `z_j = h(f_i⁻¹(y_j)) ⊕ a_j`, computed as
`zipWith xor (H ⟨i, Inv(1^n, ⟨t, y_j⟩; 1^{inv(n)})⟩) [a]` (the body of `otMask`). -/
def mask (n : ℕ) (i t yj : List Bool) (a : Bool) : List Bool :=
  List.zipWith xor (H (pairEncode i (T.inv.runAtL n (pairEncode t yj)
    (List.replicate (T.inv.coins.eval n) true)))) [a]

/-- The defining equation of `mask`: `mask T H n i t yj a =
zipWith xor (H ⟨i, Inv(1^n, ⟨t, yj⟩; 1^{inv(n)})⟩) [a]`. -/
theorem mask_eq (n : ℕ) (i t yj : List Bool) (a : Bool) :
    mask T H n i t yj a =
      List.zipWith xor (H (pairEncode i (T.inv.runAtL n (pairEncode t yj)
        (List.replicate (T.inv.coins.eval n) true)))) [a] := rfl

/-- **Alice's next message** [PS10, Protocol 160.4] (the body of `otSender`): on the empty
history `i = fst Gen(1^{|x|}; r)`; on one message `m`, `⟨mask (fst m) y₀, mask (snd m) y₁⟩` with
`⟨i, t⟩ = Gen(1^{|x|}; r)`; otherwise `[]`. -/
def senderNext (x y r : List Bool) (hist : List (List Bool)) : List Bool :=
  if hist.length = 0 then pairFstD (T.gen.runAtL x.length [] r)
  else if hist.length = 1 then
    pairEncode
      (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
        (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD (hist.headD [])) (y.getD 0 false))
      (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
        (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD (hist.headD [])) (y.getD 1 false))
  else []

/-- The defining equation of `senderNext`: `[]` ↦ `i`, `[m]` ↦ the two masks, else `[]`. -/
theorem senderNext_eq (x y r : List Bool) (hist : List (List Bool)) :
    senderNext T H x y r hist =
      if hist.length = 0 then pairFstD (T.gen.runAtL x.length [] r)
      else if hist.length = 1 then
        pairEncode
          (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
            (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD (hist.headD [])) (y.getD 0 false))
          (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
            (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD (hist.headD [])) (y.getD 1 false))
      else [] := rfl

/-- **Bob's next message** [PS10, Protocol 160.4] (the body of `otReceiver`): on one message
`i`, the pair of `f_i(w) = eval ⟨i, w⟩` (with `w` sampled from the first coin block) and the raw
sample `w'` (from the rest), ordered by the choice bit `b = z.headD false`; on two messages `[]`;
otherwise `H ⟨i, w⟩ ⊕ z_b`. -/
def receiverNext (x z r : List Bool) (hist : List (List Bool)) : List Bool :=
  if hist.length = 1 then
    if z.headD false then
      pairEncode (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
        (T.eval (pairEncode (hist.headD [])
          (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
    else
      pairEncode (T.eval (pairEncode (hist.headD [])
          (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
        (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
  else if hist.length = 2 then []
  else List.zipWith xor (H (pairEncode (hist.headD [])
      (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
    (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 []))

/-- The defining equation of `receiverNext`: `[i]` ↦ the ordered pair, two messages ↦ `[]`,
else `H ⟨i, w⟩ ⊕ z_b`. -/
theorem receiverNext_eq (x z r : List Bool) (hist : List (List Bool)) :
    receiverNext T H x z r hist =
      if hist.length = 1 then
        if z.headD false then
          pairEncode
            (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
            (T.eval (pairEncode (hist.headD [])
              (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
        else
          pairEncode (T.eval (pairEncode (hist.headD [])
              (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
            (T.sample.runAtL x.length (hist.headD []) (r.drop (T.sample.coins.eval x.length)))
      else if hist.length = 2 then []
      else List.zipWith xor (H (pairEncode (hist.headD [])
          (T.sample.runAtL x.length (hist.headD []) (r.take (T.sample.coins.eval x.length)))))
        (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 [])) := rfl

/-- **A protocol of the shape of Protocol 160.4** [PS10]: `P.next = senderNext T H`,
`V.next = receiverNext T H`, `P.coins = coins_Gen`, `V.coins = coins_Sample + coins_Sample`,
five messages, Alice first. -/
def IsOT (π : Protocol) : Prop :=
  π.P.next = senderNext T H ∧ π.V.next = receiverNext T H ∧ π.P.coins = T.gen.coins ∧
    π.V.coins = .add T.sample.coins T.sample.coins ∧ π.rounds = .const 5 ∧
      π.verifierFirst = false

/-- The defining property of `IsOT`: `IsOT T H π` iff the six field equations hold. -/
theorem isOT_iff (π : Protocol) :
    IsOT T H π ↔
      π.P.next = senderNext T H ∧ π.V.next = receiverNext T H ∧ π.P.coins = T.gen.coins ∧
        π.V.coins = .add T.sample.coins T.sample.coins ∧ π.rounds = .const 5 ∧
          π.verifierFirst = false := Iff.rfl

/-! ### Messages on short histories -/

/-- Alice's first message is the index: `senderNext T H x y r [] = fst Gen(1^{|x|}; r)`. -/
theorem senderNext_nil (x y r : List Bool) :
    senderNext T H x y r [] = pairFstD (T.gen.runAtL x.length [] r) := by
  rw [senderNext_eq, if_pos List.length_nil]

/-- Alice's second message is the pair of masks:
`senderNext T H x y r [m] = ⟨mask (fst m) y₀, mask (snd m) y₁⟩`. -/
theorem senderNext_single (x y r m : List Bool) :
    senderNext T H x y r [m] =
      pairEncode
        (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
          (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD m) (y.getD 0 false))
        (mask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
          (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD m) (y.getD 1 false)) := by
  rw [senderNext_eq, if_neg (by simp), if_pos List.length_singleton, List.headD_cons]

/-- Alice's third message is empty: `senderNext T H x y r [m, m'] = []`. -/
theorem senderNext_pair (x y r m m' : List Bool) : senderNext T H x y r [m, m'] = [] := by
  rw [senderNext_eq, if_neg (by simp), if_neg (by simp)]

/-- Bob's first message is the ordered pair `⟨f_i(w), w'⟩` (or `⟨w', f_i(w)⟩` when `b`). -/
theorem receiverNext_single (x z r i : List Bool) :
    receiverNext T H x z r [i] =
      if z.headD false then
        pairEncode (T.sample.runAtL x.length i (r.drop (T.sample.coins.eval x.length)))
          (T.eval (pairEncode i
            (T.sample.runAtL x.length i (r.take (T.sample.coins.eval x.length)))))
      else
        pairEncode
          (T.eval (pairEncode i
            (T.sample.runAtL x.length i (r.take (T.sample.coins.eval x.length)))))
          (T.sample.runAtL x.length i (r.drop (T.sample.coins.eval x.length))) := by
  rw [receiverNext_eq, if_pos List.length_singleton, List.headD_cons]

/-- Bob's second message is empty: `receiverNext T H x z r [m, m'] = []`. -/
theorem receiverNext_pair (x z r m m' : List Bool) : receiverNext T H x z r [m, m'] = [] := by
  rw [receiverNext_eq, if_neg (by simp), if_pos (by simp)]

/-! ### The five moves -/

/-- **The five moves of a prover-first execution** [PS10, §4.4]: with
`m₁ = P([])`, `m₂ = V([m₁])`, `m₃ = P([m₂])`, `m₄ = V([m₁, m₃])`, `m₅ = P([m₂, m₄])`,
`exec P V false x zP zV rP rV 5 = ([m₂, m₄], [m₁, m₃, m₅])`. -/
theorem exec_five (P V : Strategy) (x zP zV rP rV : List Bool) {m₁ m₂ m₃ m₄ m₅ : List Bool}
    (h₁ : P.next x zP rP [] = m₁) (h₂ : V.next x zV rV [m₁] = m₂)
    (h₃ : P.next x zP rP [m₂] = m₃) (h₄ : V.next x zV rV [m₁, m₃] = m₄)
    (h₅ : P.next x zP rP [m₂, m₄] = m₅) :
    exec P V false x zP zV rP rV 5 = ([m₂, m₄], [m₁, m₃, m₅]) := by
  simp only [exec_succ, exec_zero, moverIsV_false]
  simp [h₁, h₂, h₃, h₄, h₅]

/-- **The transcript of a protocol of the shape of Protocol 160.4**: with
`i = fst Gen(1^{|x|}; r₁)`, `y = receiverNext [i]` and `z = senderNext [y]`, the messages received
are `([y, []], [i, z, []])`. -/
theorem transcriptWith_isOT {π : Protocol} (hπ : IsOT T H π) (x y z : List Bool)
    (r : π.ExecCoins π.P x) :
    π.transcriptWith π.P x y z r =
      ([receiverNext T H x z (List.ofFn r.2)
          [pairFstD (T.gen.runAtL x.length [] (List.ofFn r.1))], []],
        [pairFstD (T.gen.runAtL x.length [] (List.ofFn r.1)),
          senderNext T H x y (List.ofFn r.1) [receiverNext T H x z (List.ofFn r.2)
            [pairFstD (T.gen.runAtL x.length [] (List.ofFn r.1))]], []]) := by
  obtain ⟨hP, hV, -, -, hr, hf⟩ := (isOT_iff T H π).1 hπ
  rw [Protocol.transcriptWith_eq, hr, hf, PolyExpr.eval_const]
  exact exec_five _ _ _ _ _ _ _ (by rw [hP, senderNext_nil]) (by rw [hV]) (by rw [hP])
    (by rw [hV, receiverNext_pair]) (by rw [hP, senderNext_pair])

end TCSlib.Cryptography.SecureComputation.OT
