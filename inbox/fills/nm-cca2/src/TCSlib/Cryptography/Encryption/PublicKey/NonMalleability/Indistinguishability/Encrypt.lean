/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The reduction from CCA2 security to non-malleability

Direction (⇐) of [PS10, Theorem 175.9]. Given a CCA2 adversary `A` with guess `g`, the
non-malleability adversary runs `A` on the public key and forwards all of `A`'s queries to its own
oracles (`NMCCA2.fwdHandler`). It then outputs two fresh encryptions under `pk`, with its own
coins: of `g^{m}` and of `(¬g)^{m}`, where `m = msgLen(n)`. The distinguisher `guessDist` reads `g`
back from the two decryptions: from the first message bit if the first decryption is valid,
and otherwise from the negated last bit of the second.

This file builds the handler (`encHandler S`), whose seed is two encryption tapes. It proves
the finalization's equation (`encHandler_finish`) and defines the distinguisher with its two
verdicts (`guessBit_valid`, `guessBit_refused`). It also shows that at `msgLen(n) = 0` the two
CCA2 oracles coincide (`indImpl_eq_of_msgLen_eq_zero`).

## Main definitions

* `NMCCA2.encHandler`: the handler of the reduction.
* `NMCCA2.encTape`, `NMCCA2.encCt`: the seed's two tapes and the two ciphertexts.
* `NMCCA2.guessBit`, `NMCCA2.guessDist`: the distinguisher.

## Main results

* `NMCCA2.simulate_encHandler_impl`, `NMCCA2.encHandler_finish`.
* `NMCCA2.guessDist_distinguisherL`, `NMCCA2.guessBit_valid`, `NMCCA2.guessBit_refused`.
* `NMCCA2.indImpl_eq_of_msgLen_eq_zero`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.9 (book p. 175).
-/

namespace TCSlib.Cryptography.Composability.NMCCA2

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open AdaptiveCPA (acDin acDout acDout_zero)

variable (S : FixedLengthPKScheme)

/-! ### The finalization -/

/-- The plaintext bit of ciphertext `β`: the adversary's guess `g` (its output's first bit) for
`β = true`, and `¬g` for `β = false`. -/
private def eBit (β : Bool) (w : List Bool) : Bool :=
  if β then (finA w).headD false else !(finA w).headD false

/-- The plaintext of ciphertext `β`: its bit repeated `msgLen(n)` times. -/
private def eMsg (β : Bool) (w : List Bool) : List Bool :=
  if eBit β w then List.replicate (S.msgLen.eval (finU w).length) true
  else List.replicate (S.msgLen.eval (finU w).length) false

/-- The coins of ciphertext `β`: the first (`β = true`) or the second `ρ(n)` bits of the seed. -/
private def eTape (β : Bool) (w : List Bool) : List Bool :=
  if β then (finW w).take (S.enc.coins.eval (finU w).length)
  else (finW w).drop (S.enc.coins.eval (finU w).length)

/-- Ciphertext `β`: `Enc` on `⟨1^n, ⟨pk, plaintext⟩⟩` with empty advice and its coins, padded to
`ctLen(n)` bits. -/
private def eCt (β : Bool) (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (finU w).length)
    (S.enc.output (pairEncode (pairEncode (pairEncode (finU w)
      (pairEncode (finZ w) (eMsg S β w))) []) (eTape S β w)))

/-- **The finalization's round:** output the two ciphertexts, `⟨[true], c₁ ‖ c₂⟩`. -/
private def eFin (w : List Bool) : List Bool := pairEncode [true] (eCt S true w ++ eCt S false w)

/-- The finalization round is polynomial-time. -/
private theorem polyTimeComputable_eFin : PolyTimeComputable (eFin S) := by
  obtain ⟨hU, hZ, hW, hA, -⟩ := polyTimeComputable_finFields
  have hg : PolyTimeComputable fun w => [(finA w).headD false] := polyTimeComputable_headD.comp hA
  have hBit : ∀ β, PolyTimeComputable fun w => [eBit β w] := by
    intro β
    cases β
    · exact (polyTimeComputable_not hg).congr fun w => rfl
    · exact hg.congr fun w => rfl
  have hMsg : ∀ β, PolyTimeComputable (eMsg S β) := fun β =>
    polyTimeComputable_ite (hBit β) ((polyTimeComputable_unaryPoly S.msgLen).comp hU)
      (EnsembleLemmas.polyTimeComputable_zeros S.msgLen hU)
  have hTape : ∀ β, PolyTimeComputable (eTape S β) := by
    intro β
    cases β
    · exact ((polyTimeComputable_pairDropPoly S.enc.coins).comp (hU.pairEncode hW)).congr
        fun w => by simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
    · exact ((polyTimeComputable_pairTakePoly S.enc.coins).comp (hU.pairEncode hW)).congr
        fun w => by simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hCt : ∀ β, PolyTimeComputable (eCt S β) := fun β =>
    EnsembleLemmas.polyTimeComputable_padL S.ctLen hU (S.enc.polyTimeComputable_output.comp
      (((hU.pairEncode (hZ.pairEncode (hMsg β))).pairEncode
        (polyTimeComputable_const [])).pairEncode (hTape β)))
  exact (polyTimeComputable_const [true]).pairEncode ((hCt true).append (hCt false))

/-- The adversary's input is the reduction input. -/
private theorem polyTimeComputable_encAdvIn :
    PolyTimeComputable fun ctx : List Bool => pairFstD (pairSndD ctx) :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-! ### The handler -/

/-- **The handler of the reduction (⇐)** for the scheme `S`: the forwarding handler
(`fwdHandler`) on the oracles of Definition 171.5, with a seed of two encryption tapes
(`2ρ(n)` bits), the adversary run on the reduction input `pk`, and a finalization without outer
queries whose output is `2 · ctLen(n)` bits: `Enc_pk(g^{msgLen(n)})` with the first tape, then
`Enc_pk((¬g)^{msgLen(n)})` with the second, where `g` is the adversary's first output bit. -/
def encHandler : InteractiveHandler 2 (acDin S) (acDout S) 2 (acDin S) (acDout S) :=
  fwdHandler (acDin S) (acDout S) (S.enc.coins.add S.enc.coins)
    (fun ctx => pairFstD (pairSndD ctx)) polyTimeComputable_encAdvIn (S.ctLen.add S.ctLen)
    (.const 0) (eFin S) (polyTimeComputable_eFin S)

/-- Two encryption tapes: `(encHandler S).seedLen = ρ + ρ`. -/
theorem encHandler_seedLen : (encHandler S).seedLen = S.enc.coins.add S.enc.coins := by
  rw [encHandler, fwdHandler_seedLen]

/-- One outer call per inner query: `(encHandler S).perCall = .const 1`. -/
theorem encHandler_perCall : (encHandler S).perCall = .const 1 := by
  rw [encHandler, fwdHandler_perCall]

/-- No outer query in the finalization: `(encHandler S).finCall = .const 0`. -/
theorem encHandler_finCall : (encHandler S).finCall = .const 0 := by
  rw [encHandler, fwdHandler_finCall]

/-- Two ciphertexts as output: `(encHandler S).outLen = ctLen + ctLen`. -/
theorem encHandler_outLen : (encHandler S).outLen = S.ctLen.add S.ctLen := by
  rw [encHandler, fwdHandler_outLen]

/-- The adversary runs on the reduction input: `(encHandler S).advInput n z ω = z`. -/
theorem encHandler_advInput (n : ℕ) (z : List Bool)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool) :
    (encHandler S).advInput n z ω = z := by
  rw [InteractiveHandler.advInput_eq]
  simp only [encHandler, fwdHandler_advIn]
  rw [seedIn_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- **The handler forwards** (`simulate_fwdHandler_impl`): `simulate (H.impl n z ω) c s =
c.bind fun a => pure (a, s)`. -/
theorem simulate_encHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt (acDin S) (acDout S) n) α)
    (s : Fin ((encHandler S).stateLen.eval n) → Bool) :
    simulate ((encHandler S).impl n z ω) c s = c.bind fun a => .pure (a, s) :=
  simulate_fwdHandler_impl (acDin S) (acDout S) (S.enc.coins.add S.enc.coins) _
    polyTimeComputable_encAdvIn (S.ctLen.add S.ctLen) (.const 0) (eFin S)
    (polyTimeComputable_eFin S) n z ω c s

/-- **The seed's two encryption tapes:** tape `true` is the first `ρ(n)` bits of the seed, tape
`false` the rest (`ρ(n)` bits), read as coins of `Enc`. -/
def encTape (n : ℕ) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (β : Bool) :
    S.enc.Coins n :=
  (NUPPT.coinsEquivPoly rfl n).symm (padFin _ (if β then (List.ofFn ω).take (S.enc.coins.eval n)
    else (List.ofFn ω).drop (S.enc.coins.eval n)))

/-- `encTape S n ω β = (coinsEquivPoly rfl n).symm (padFin _ (if β then ⟦ω⟧.take ρ(n) else
⟦ω⟧.drop ρ(n)))`. -/
theorem encTape_eq (n : ℕ) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (β : Bool) :
    encTape S n ω β = (NUPPT.coinsEquivPoly rfl n).symm (padFin _ (if β then
      (List.ofFn ω).take (S.enc.coins.eval n) else (List.ofFn ω).drop (S.enc.coins.eval n))) :=
  rfl

/-- The tapes as strings: `⟦encTape S n ω β⟧ = if β then ⟦ω⟧.take ρ(n) else ⟦ω⟧.drop ρ(n)`. -/
theorem ofFn_encTape (n : ℕ) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (β : Bool) :
    List.ofFn (encTape S n ω β) = if β then (List.ofFn ω).take (S.enc.coins.eval n)
      else (List.ofFn ω).drop (S.enc.coins.eval n) := by
  have hω : (List.ofFn ω).length = S.enc.coins.eval n + S.enc.coins.eval n := by
    rw [List.length_ofFn, encHandler_seedLen, PolyExpr.eval_add]
  rw [encTape_eq, NUPPT.coinsEquivPoly_symm_ofFn]
  cases β
  · exact GGMRed.ofFn_padFin_of_length (by
      rw [if_neg Bool.false_ne_true, List.length_drop, hω]; omega)
  · exact GGMRed.ofFn_padFin_of_length (by rw [if_pos rfl, List.length_take, hω]; omega)

/-- **Ciphertext `β` of the reduction's output**, for the public key `z`, the seed `ω` and the
guess `g`: `padL ctLen(n) (Enc_z(b^{msgLen(n)}); encTape β)` with `b = g` for `β = true` and
`b = ¬g` for `β = false`. -/
def encCt (n : ℕ) (z : List Bool) (ω : Fin ((encHandler S).seedLen.eval n) → Bool) (g β : Bool) :
    List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval n) (S.enc.runAt n
    (pairEncode z (List.ofFn fun _ : Fin (S.msgLen.eval n) => if β then g else !g))
    (encTape S n ω β))

/-- `encCt S n z ω g β = padL ctLen(n) (Enc_z((if β then g else ¬g)^{msgLen(n)}); encTape β)`. -/
theorem encCt_eq (n : ℕ) (z : List Bool) (ω : Fin ((encHandler S).seedLen.eval n) → Bool)
    (g β : Bool) :
    encCt S n z ω g β = EnsembleLemmas.padL (S.ctLen.eval n) (S.enc.runAt n
      (pairEncode z (List.ofFn fun _ : Fin (S.msgLen.eval n) => if β then g else !g))
      (encTape S n ω β)) :=
  rfl

/-- **The finalization outputs the two ciphertexts:** after the adversary's output `a` (guess
`g = ⟦a⟧.headD false`), `H.finish n z ω s a = pure (padFin _ (encCt … g true ++ encCt … g false))`,
asking nothing.

**Proof sketch.** With budget `0` the first round returns (`buildComp_zero_of_ret`): its word is
`⟨[true], c₁ ‖ c₂⟩` of the right length (`length_padL`, `decodeBitMove_ret`), and each `cᵢ` is
`encCt` by the input readers, `NUPPT.Uniform.runAt_eq` and `ofFn_encTape`. -/
theorem encHandler_finish (n : ℕ) (z : List Bool)
    (ω : Fin ((encHandler S).seedLen.eval n) → Bool)
    (s : Fin ((encHandler S).stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool) :
    (encHandler S).finish n z ω s a =
      .pure (padFin _ (encCt S n z ω ((List.ofFn a).headD false) true ++
        encCt S n z ω ((List.ofFn a).headD false) false)) := by
  have hfin : (encHandler S).finRun = eFin S := by
    funext w
    rw [encHandler, fwdHandler_finRun]
  rw [InteractiveHandler.finish_eq, encHandler_finCall, PolyExpr.eval_const]
  refine buildComp_zero_of_ret ?_
  obtain ⟨hU, hZ, hW, hA, -⟩ := fields_finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
    ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) 0).encodeLog [])
  have hCt : ∀ β, eCt S β (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
      (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
        0).encodeLog [])) = encCt S n z ω ((List.ofFn a).headD false) β := by
    intro β
    have hm : eMsg S β (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
        (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
          0).encodeLog [])) =
        List.ofFn fun _ : Fin (S.msgLen.eval n) =>
          if β then (List.ofFn a).headD false else !(List.ofFn a).headD false := by
      rw [List.ofFn_const, eMsg, eBit, hA, hU, List.length_replicate]
      cases β <;> cases (List.ofFn a).headD false <;> rfl
    rw [eCt, hm, hU, hZ, encCt_eq, NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq,
      ofFn_encTape, eTape, hW, hU, List.length_replicate]
  have hw : List.ofFn (padFin ((encHandler S).outLen.eval n)
      (encCt S n z ω ((List.ofFn a).headD false) true ++
        encCt S n z ω ((List.ofFn a).headD false) false)) =
      encCt S n z ω ((List.ofFn a).headD false) true ++
        encCt S n z ω ((List.ofFn a).headD false) false :=
    GGMRed.ofFn_padFin_of_length (by
      rw [List.length_append, encCt_eq, encCt_eq, EnsembleLemmas.length_padL,
        EnsembleLemmas.length_padL, encHandler_outLen, PolyExpr.eval_add])
  show decodeBitMove _ _ _ ((encHandler S).finRun _) = _
  rw [hfin, eFin, hCt, hCt]
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### The distinguisher -/

/-- **The distinguisher's verdict** on the concatenated decryptions `w = v₁ ‖ v₂`: the bit after
the first validity flag if that flag is set, and the negated last bit of `w` otherwise. -/
def guessBit (w : List Bool) : Bool :=
  if w.headD false then (w.drop 1).headD false else !w.reverse.headD false

/-- `guessBit w = if w.headD false then (w.drop 1).headD false else ¬ w.reverse.headD false`. -/
theorem guessBit_eq (w : List Bool) :
    guessBit w = if w.headD false then (w.drop 1).headD false else !w.reverse.headD false := rfl

/-- The distinguisher's raw function on the machine input `⟨⟨⟨1^n, w⟩, α⟩, ρ⟩`. -/
private def guessFun (x : List Bool) : List Bool :=
  if (pairSndD (pairFstD (pairFstD x))).headD false then
    [((pairSndD (pairFstD (pairFstD x))).drop 1).headD false]
  else [!(pairSndD (pairFstD (pairFstD x))).reverse.headD false]

/-- The distinguisher's raw function is polynomial-time. -/
private theorem polyTimeComputable_guessFun : PolyTimeComputable guessFun := by
  have hw : PolyTimeComputable fun x => pairSndD (pairFstD (pairFstD x)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hw)
    (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hw))
    (polyTimeComputable_not
      (polyTimeComputable_headD.comp (BinArith.polyTimeComputable_reverse.comp hw)))

/-- **The distinguisher** of the reduction (⇐): the uniform machine without coins computing
`[guessBit w]` on its argument `w`. -/
noncomputable def guessDist : NUPPT :=
  NUPPT.ofPolyTimeUniform polyTimeComputable_guessFun (.const 0)

/-- The distinguisher accepts `w` exactly when `guessBit w`:
`guessDist.distinguisherL n w ρ = guessBit w`. -/
theorem guessDist_distinguisherL (n : ℕ) (w : List Bool) (ρ : guessDist.Coins n) :
    guessDist.distinguisherL n w ρ = guessBit w := by
  have hrun : ∀ y r, guessDist.runAtL n y r = guessFun (pairEncode (pairEncode
      (NUPPT.advInput n y) []) r) := fun y r =>
    NUPPT.runAtL_ofPolyTimeUniform polyTimeComputable_guessFun (.const 0) n y r
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_eq, hrun, guessFun, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode, guessBit_eq]
  split <;> simp

/-- **A valid first decryption gives the guess:** if `v₁` encodes the message `g^m` with `m > 0`,
then `guessBit (v₁ ‖ v₂) = g`. -/
theorem guessBit_valid {m : ℕ} (hm : 0 < m) (g : Bool) (v₂ : List Bool) :
    guessBit (List.ofFn (FixedLengthScheme.decAnswer (some fun _ : Fin m => g)) ++ v₂) = g := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [FixedLengthScheme.decAnswer_some, guessBit_eq, List.ofFn_succ, List.ofFn_succ]
  simp

/-- **A refused first decryption is answered by the second:** if `v₁` is `⊥ = 0` and `v₂`
encodes `(¬g)^m` with `m > 0`, then `guessBit (v₁ ‖ v₂) = g`. -/
theorem guessBit_refused {m : ℕ} (hm : 0 < m) (g : Bool) :
    guessBit (List.ofFn (zeroBits (m + 1)) ++
      List.ofFn (FixedLengthScheme.decAnswer (some fun _ : Fin m => !g))) = g := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h2 : List.ofFn (Fin.cons (α := fun _ => Bool) true (fun _ : Fin (m' + 1) => !g)) =
      true :: (List.replicate m' (!g) ++ [!g]) := by
    rw [List.ofFn_succ, Fin.cons_zero, ← List.replicate_succ', ← List.ofFn_const]
    rfl
  rw [FixedLengthScheme.decAnswer_some, h2, guessBit_eq, ofFn_zeroBits, List.replicate_succ]
  simp

/-! ### Empty messages -/

/-- **With empty messages the two CCA2 oracles coincide:** if `msgLen(n) = 0`, then
`S.indImpl atk false n pk sk = S.indImpl atk true n pk sk` (both halves of a challenge are the
empty message).

**Proof sketch.** Compare query by query through the published equations: decryption does not
depend on the bit (`indImpl_dec_onSpec`), a repeated challenge repeats the record
(`indImpl_challenge_repeat_onSpec`), and a first challenge encrypts a half of the query
(`indImpl_challenge_none_onSpec`), whose string is `[]` either way. -/
theorem indImpl_eq_of_msgLen_eq_zero (atk : Attack) (n : ℕ) (pk sk : List Bool)
    (h : S.msgLen.eval n = 0) : S.indImpl atk false n pk sk = S.indImpl atk true n pk sk := by
  have h0 : ∀ f : Fin (S.msgLen.eval n) → Bool, List.ofFn f = [] := fun f =>
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, h])
  funext i x s
  match i with
  | 0 => rw [S.indImpl_dec_onSpec, S.indImpl_dec_onSpec]
  | 1 =>
    cases s with
    | some c => rw [S.indImpl_challenge_repeat_onSpec, S.indImpl_challenge_repeat_onSpec]
    | none =>
      rw [S.indImpl_challenge_none_onSpec, S.indImpl_challenge_none_onSpec]
      simp only [h0]

end TCSlib.Cryptography.Composability.NMCCA2
