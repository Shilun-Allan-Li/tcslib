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
# The reduction from non-malleability to CCA2 security

Direction (⇒) of [PS10, Theorem 175.9]. Given a non-malleability adversary `A` whose output is
`ℓ(n)` ciphertexts and a distinguisher `D`, the CCA2 adversary runs `A` on the public key and
forwards all of `A`'s queries to its own oracles (`NMCCA2.fwdHandler`). In the finalization it
asks its decryption oracle for each of `A`'s `ℓ(n)` ciphertexts in turn and outputs `D`'s
verdict on the concatenated answers. Under CCA2 the decryption oracle refuses the recorded
challenge with `⊥`, exactly as the non-malleability experiment decrypts a copy of the challenge.

This file builds the handler (`decHandler S ℓ D`): its seed is `D`'s coins, and the reduction
input is `⟨pk, α⟩`, where `α` is `D`'s advice. It proves the finalization's equation against
any outer oracle whose decryption answers are deterministic and keep the state
(`simulate_decHandler_finish`). The advice is hard-wired afterwards (`exists_withAdviceOn`,
from `NUPPT.exists_comp` and `NUPPT.exists_withAdvice`).

## Main definitions

* `NMCCA2.cntRead`, `NMCCA2.ansRead`: the per-entry readings of a log (one token, the answer).
* `NMCCA2.decHandler`: the handler of the reduction.

## Main results

* `NMCCA2.simulate_decHandler_impl`: the handler forwards.
* `NMCCA2.simulate_decHandler_finish`: the finalization decrypts the `ℓ` blocks and runs `D`.
* `NMCCA2.exists_withAdviceOn`: hard-wiring a second component of the input.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.9 (book p. 175).
-/

namespace TCSlib.Cryptography.Composability.NMCCA2

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open AdaptiveCPA (acDin acDout acDin_zero acDout_zero)

/-! ### Readings of a log entry -/

/-- One token for a nonempty log and nothing for the empty one:
`cntRead v = if v = [] then [] else [true]`. With `logEmit` it counts the entries of a log. -/
def cntRead (v : List Bool) : List Bool := if decide (v = []) then [] else [true]

/-- `cntRead v = if v = [] then [] else [true]`. -/
theorem cntRead_eq (v : List Bool) : cntRead v = if decide (v = []) then [] else [true] := rfl

/-- The token reading is polynomial-time: `PolyTimeComputable cntRead`. -/
theorem polyTimeComputable_cntRead : PolyTimeComputable cntRead :=
  polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
    (polyTimeComputable_const [true])

/-- The answer `y` of the first entry `⟨1^i, ⟨x, y⟩⟩` of a log:
`ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
def ansRead (v : List Bool) : List Bool := pairSndD (pairSndD (pairFstD v))

/-- `ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
theorem ansRead_eq (v : List Bool) : ansRead v = pairSndD (pairSndD (pairFstD v)) := rfl

/-- The answer reading is polynomial-time: `PolyTimeComputable ansRead`. -/
theorem polyTimeComputable_ansRead : PolyTimeComputable ansRead :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)

section Readings

variable {k : ℕ} {din dout : Fin k → ℕ} {dα : ℕ}

/-- **Counting the entries:** `|logEmit cntRead ⟦h⟧| = |h|`. -/
theorem length_logEmit_cntRead (h : QueryLog (bitSpec din dout)) :
    (logEmit cntRead ((bitCodec din dout dα).encodeLog h)).length = h.length := by
  rw [logEmit_encodeLog _ cntRead (fun _ => [true]) rfl
    (fun e t => by rw [cntRead_eq, decide_eq_false (pairEncode_ne_nil _ _)]; rfl)]
  simp only [List.length_flatMap, List.length_singleton, List.map_const', List.sum_replicate,
    smul_eq_mul, mul_one]

/-- **Collecting the answers:** `logEmit ansRead ⟦h⟧` is the concatenation of the entries'
answers, `h.flatMap fun e => ⟦e.2.2⟧`. -/
theorem logEmit_ansRead (h : QueryLog (bitSpec din dout)) :
    logEmit ansRead ((bitCodec din dout dα).encodeLog h) = h.flatMap fun e => List.ofFn e.2.2 :=
  logEmit_encodeLog _ ansRead _ (by
    rw [ansRead_eq, pairFstD_nil, pairSndD_of_pairDecode_eq_none pairDecode_nil,
      pairSndD_of_pairDecode_eq_none pairDecode_nil]) (fun e t => by
    rw [ansRead_eq, pairFstD_pairEncode, bitCodec_encodeEntry, pairSndD_pairEncode,
      pairSndD_pairEncode]) h

end Readings

/-! ### The finalization -/

variable (S : FixedLengthPKScheme) (ℓ : PolyExpr) (D : NUPPT)

/-- The number of decryptions asked so far, in unary. -/
private def dCnt (w : List Bool) : List Bool := logEmit cntRead (finL w)

/-- The next block of the adversary's output: `ctLen(n)` bits from position `j · ctLen(n)`, for
`j` the decryptions asked so far, padded with `false`. -/
private def dCt (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (finU w).length)
    ((finA w).drop ((dCnt w).length * S.ctLen.eval (finU w).length))

/-- `D`'s input layout: parameter `1^n`, the collected answers, the advice (the second component
of the reduction input) and the seed as coins. -/
private def dIn (w : List Bool) : List Bool :=
  pairEncode (pairEncode (pairEncode (finU w) (logEmit ansRead (finL w))) (pairSndD (finZ w)))
    (finW w)

/-- **One round of the finalization.** After `ℓ(n)` decryptions, output `D`'s verdict
`[D(answers) = [true]]`; before, ask the decryption oracle (index `0`) the next block. -/
private def dFin (w : List Bool) : List Bool :=
  if decide (ℓ.eval (finU w).length ≤ (dCnt w).length) then
    pairEncode [true] [decide (D.output (dIn w) = [true])]
  else pairEncode [false] (pairEncode [] (dCt S w))

/-- The finalization round is polynomial-time. -/
private theorem polyTimeComputable_dFin : PolyTimeComputable (dFin S ℓ D) := by
  obtain ⟨hU, hZ, hW, hA, hL⟩ := polyTimeComputable_finFields
  have hCnt : PolyTimeComputable dCnt :=
    (polyTimeComputable_logEmit polyTimeComputable_cntRead).comp hL
  have hAns : PolyTimeComputable fun w => logEmit ansRead (finL w) :=
    (polyTimeComputable_logEmit polyTimeComputable_ansRead).comp hL
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((dCnt w).length * S.ctLen.eval (finU w).length) true :=
    (OneWay.polyTimeComputable_unaryMulPair.comp
      (hCnt.pairEncode ((polyTimeComputable_unaryPoly S.ctLen).comp hU))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  have hDrop : PolyTimeComputable fun w =>
      (finA w).drop ((dCnt w).length * S.ctLen.eval (finU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hA)).congr fun w => by
      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
  have hCt : PolyTimeComputable (dCt S) := EnsembleLemmas.polyTimeComputable_padL S.ctLen hU hDrop
  have hIn : PolyTimeComputable dIn :=
    ((hU.pairEncode hAns).pairEncode (polyTimeComputable_pairSndD.comp hZ)).pairEncode hW
  have hV : PolyTimeComputable fun w => [decide (D.output (dIn w) = [true])] :=
    (polyTimeComputable_pairEq.comp ((D.polyTimeComputable_output.comp hIn).pairEncode
      (polyTimeComputable_const [true]))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hT : PolyTimeComputable fun w => [decide (ℓ.eval (finU w).length ≤ (dCnt w).length)] :=
    (polyTimeComputable_lenLe.comp (hCnt.pairEncode
      ((polyTimeComputable_unaryPoly ℓ).comp hU))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  exact polyTimeComputable_ite hT ((polyTimeComputable_const [true]).pairEncode hV)
    ((polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hCt))

/-- The adversary's input is the first component of the reduction input. -/
private theorem polyTimeComputable_decAdvIn :
    PolyTimeComputable fun ctx : List Bool => pairFstD (pairFstD (pairSndD ctx)) :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)

/-! ### The handler -/

/-- **The handler of the reduction (⇒)** for the scheme `S`, `ℓ` output ciphertexts and the
distinguisher `D`: the forwarding handler (`fwdHandler`) on the oracles of Definition 171.5, with
the seed of `D`'s coins, the adversary run on the first component `pk` of the reduction input
`⟨pk, α⟩`, and a finalization with at most `ℓ(n)` outer queries and a one-bit output: it asks
the decryption oracle for each of the `ℓ(n)` blocks of the adversary's output, then outputs
`[D(1^n, answers; α, ω) = [true]]`. -/
def decHandler : InteractiveHandler 2 (acDin S) (acDout S) 2 (acDin S) (acDout S) :=
  fwdHandler (acDin S) (acDout S) D.coins (fun ctx => pairFstD (pairFstD (pairSndD ctx)))
    polyTimeComputable_decAdvIn (.const 1) ℓ (dFin S ℓ D) (polyTimeComputable_dFin S ℓ D)

/-- The handler's seed is `D`'s coins: `(decHandler S ℓ D).seedLen = D.coins`. -/
theorem decHandler_seedLen : (decHandler S ℓ D).seedLen = D.coins := by
  rw [decHandler, fwdHandler_seedLen]

/-- One outer call per inner query: `(decHandler S ℓ D).perCall = .const 1`. -/
theorem decHandler_perCall : (decHandler S ℓ D).perCall = .const 1 := by
  rw [decHandler, fwdHandler_perCall]

/-- At most `ℓ(n)` outer queries in the finalization: `(decHandler S ℓ D).finCall = ℓ`. -/
theorem decHandler_finCall : (decHandler S ℓ D).finCall = ℓ := by
  rw [decHandler, fwdHandler_finCall]

/-- A one-bit output: `(decHandler S ℓ D).outLen = .const 1`. -/
theorem decHandler_outLen : (decHandler S ℓ D).outLen = .const 1 := by
  rw [decHandler, fwdHandler_outLen]

/-- The adversary runs on the first component of the reduction input:
`(decHandler S ℓ D).advInput n z ω = pairFstD z`. -/
theorem decHandler_advInput (n : ℕ) (z : List Bool)
    (ω : Fin ((decHandler S ℓ D).seedLen.eval n) → Bool) :
    (decHandler S ℓ D).advInput n z ω = pairFstD z := by
  rw [InteractiveHandler.advInput_eq]
  simp only [decHandler, fwdHandler_advIn]
  rw [seedIn_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- **The handler forwards** (`simulate_fwdHandler_impl`): `simulate (H.impl n z ω) c s =
c.bind fun a => pure (a, s)`. -/
theorem simulate_decHandler_impl (n : ℕ) (z : List Bool)
    (ω : Fin ((decHandler S ℓ D).seedLen.eval n) → Bool) {α : Type}
    (c : OracleComp (bitSpecAt (acDin S) (acDout S) n) α)
    (s : Fin ((decHandler S ℓ D).stateLen.eval n) → Bool) :
    simulate ((decHandler S ℓ D).impl n z ω) c s = c.bind fun a => .pure (a, s) :=
  simulate_fwdHandler_impl (acDin S) (acDout S) D.coins _ polyTimeComputable_decAdvIn (.const 1) ℓ
    (dFin S ℓ D) (polyTimeComputable_dFin S ℓ D) n z ω c s

/-- The `i`-th block of `ctLen(n)` bits of a string `a`, padded with `false`, as a decryption
query: `padFin _ (⟦a⟧.drop (i · ctLen(n)))`. -/
def decBlock (n : ℕ) {d : ℕ} (a : Fin d → Bool) (i : ℕ) : Fin ((acDin S 0).eval n) → Bool :=
  padFin _ ((List.ofFn a).drop (i * S.ctLen.eval n))

/-- `decBlock S n a i = padFin _ (⟦a⟧.drop (i · ctLen(n)))`. -/
theorem decBlock_eq (n : ℕ) {d : ℕ} (a : Fin d → Bool) (i : ℕ) :
    decBlock S n a i = padFin _ ((List.ofFn a).drop (i * S.ctLen.eval n)) := rfl

/-- **The finalization decrypts the blocks and runs `D`.** Against an outer oracle `O` whose
decryption answers `ans x st` are deterministic and keep the state `st`, the finalization after
the adversary's output `a` asks the `ℓ(n)` blocks of `a` and returns `D`'s verdict on the
concatenated answers:
`simulate O (H.finish n z ω s a) st = pure (padFin _ [D.output (layout 1^n ans* (snd z) ω) =
[true]], st)` with `ans* = ⟦ans (block 0) st⟧ ++ ⋯ ++ ⟦ans (block (ℓ(n) − 1)) st⟧`.

**Proof sketch.** Induction on the remaining budget along the finalization's log: after `j`
decryptions the log holds the entries `(0, block i, ans (block i) st)` for `i < j`. Its count is
`j` (`length_logEmit_cntRead`), so for `j < ℓ(n)` the round asks block `j` (its offset is
`j · ctLen(n)`, `decodeBitMove_query`), which `O` answers without changing `st`, and the log
grows by that entry. At `j = ℓ(n)` the budget is spent and the round returns the verdict on the
collected answers (`logEmit_ansRead`, `decodeBitMove_ret`). -/
theorem simulate_decHandler_finish (n : ℕ) (z : List Bool)
    (ω : Fin ((decHandler S ℓ D).seedLen.eval n) → Bool)
    (s : Fin ((decHandler S ℓ D).stateLen.eval n) → Bool) {d : ℕ} (a : Fin d → Bool) {σ : Type}
    (O : QueryImpl (bitSpecAt (acDin S) (acDout S) n) σ unifSpec)
    (ans : (Fin ((acDin S 0).eval n) → Bool) → σ → (Fin ((acDout S 0).eval n) → Bool))
    (hO : ∀ x st, O 0 x st = .pure (ans x st, st)) (st : σ) :
    simulate O ((decHandler S ℓ D).finish n z ω s a) st =
      .pure (padFin _ [decide (D.output (NUPPT.layout (List.replicate n true)
          ((List.range (ℓ.eval n)).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
          (pairSndD z) (List.ofFn ω)) = [true])], st) := by
  -- The log after `j` decryptions.
  obtain ⟨hist, hhist⟩ : ∃ hist : ℕ → QueryLog (bitSpecAt (acDin S) (acDout S) n),
      hist = fun j => (List.range j).map fun i =>
        (⟨0, decBlock S n a i, ans (decBlock S n a i) st⟩ : Σ i, _) := ⟨_, rfl⟩
  have hfin : (decHandler S ℓ D).finRun = dFin S ℓ D := by
    funext w
    rw [decHandler, fwdHandler_finRun]
  have hctl : (acDin S 0).eval n = S.ctLen.eval n := by rw [acDin_zero]
  have hout : (decHandler S ℓ D).outLen.eval n = 1 := by
    rw [decHandler_outLen, PolyExpr.eval_const]
  -- The fields of the round input on the log `hist j`.
  have hfields : ∀ (j : ℕ) (w : List Bool),
      w = InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s) (List.ofFn a)
        ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) 0).encodeLog
          (hist j)) →
      (dCnt w).length = j ∧ finU w = List.replicate n true ∧
      dIn w = NUPPT.layout (List.replicate n true)
        ((List.range j).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
        (pairSndD z) (List.ofFn ω) ∧
      dCt S w = List.ofFn (decBlock S n a j) := by
    intro j w hw
    obtain ⟨hU, hZ, hW, hA, hL⟩ := fields_finInput n z (List.ofFn ω) (List.ofFn s)
      (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
        0).encodeLog (hist j))
    rw [← hw] at hU hZ hW hA hL
    have hc : (dCnt w).length = j := by
      rw [dCnt, hL, length_logEmit_cntRead, hhist, List.length_map, List.length_range]
    refine ⟨hc, hU, ?_, ?_⟩
    · rw [dIn, hU, hZ, hW, hL, logEmit_ansRead, NUPPT.layout_eq, hhist, List.flatMap_map,
        List.flatMap_def]
    · rw [dCt, hU, hA, hc, List.length_replicate, decBlock_eq, ofFn_padFin_eq_take,
        EnsembleLemmas.padL_eq, hctl]
  -- Induction on the remaining budget.
  have key : ∀ m j, j + m = ℓ.eval n →
      simulate O (buildComp (fun L => decodeBitMove (fun i => (acDin S i).eval n)
          (fun i => (acDout S i).eval n) ((decHandler S ℓ D).outLen.eval n)
          ((decHandler S ℓ D).finRun (InteractiveHandler.finInput n z (List.ofFn ω) (List.ofFn s)
            (List.ofFn a) ((bitCodec (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n)
              0).encodeLog L)))) (zeroBits _) m (hist j)) st =
        .pure (padFin _ [decide (D.output (NUPPT.layout (List.replicate n true)
          ((List.range (ℓ.eval n)).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
          (pairSndD z) (List.ofFn ω)) = [true])], st) := by
    intro m
    induction m with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      subst hj
      obtain ⟨hc, hU, hIn, -⟩ := hfields (ℓ.eval n) _ rfl
      rw [buildComp_zero_of_ret, simulate_pure]
      rw [hfin, dFin, hc, hU, List.length_replicate, if_pos (decide_eq_true le_rfl), hIn]
      have hw : List.ofFn (padFin ((decHandler S ℓ D).outLen.eval n)
          [decide (D.output (NUPPT.layout (List.replicate n true)
            ((List.range (ℓ.eval n)).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
            (pairSndD z) (List.ofFn ω)) = [true])]) =
          [decide (D.output (NUPPT.layout (List.replicate n true)
            ((List.range (ℓ.eval n)).map fun i => List.ofFn (ans (decBlock S n a i) st)).flatten
            (pairSndD z) (List.ofFn ω)) = [true])] :=
        ofFn_padFin_of_length (by rw [List.length_singleton, hout])
      exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
        (decodeBitMove_ret _ _ _ _)
    | succ m ih =>
      intro j hj
      obtain ⟨hc, hU, -, hCt⟩ := hfields j _ rfl
      rw [buildComp_succ_of_query (i := 0) (x := decBlock S n a j) (by
        rw [hfin, dFin, hc, hU, List.length_replicate,
          if_neg (fun h => by have := of_decide_eq_true h; omega), hCt]
        exact decodeBitMove_query (fun i => (acDin S i).eval n) (fun i => (acDout S i).eval n) _
          0 (decBlock S n a j))]
      rw [simulate_query, hO, OracleComp.pure_bind]
      have hh : hist j ++ [⟨0, decBlock S n a j, ans (decBlock S n a j) st⟩] = hist (j + 1) := by
        simp only [hhist, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      rw [hh]
      exact ih (j + 1) (by omega)
  have h0 : hist 0 = [] := by simp only [hhist, List.range_zero, List.map_nil]
  rw [InteractiveHandler.finish_eq, decHandler_finCall, ← h0]
  exact key (ℓ.eval n) 0 (Nat.zero_add _)

/-! ### Hard-wiring the advice -/

/-- **Hard-wiring a second input component** [PS10, §2.1, implicit]: for a machine `B` and a
polynomially bounded family `β n` there is a machine `B'` with the same coins (`h`) whose
computation on the input `x` is `B`'s on `⟨x, β n⟩`, for every codec and budget:
`B'.toCompOn codec n q x (coinsCongr h n r) = B.toCompOn codec n q ⟨x, β n⟩ r`.

**Proof sketch.** `B₁ := NUPPT.exists_comp B` with the re-pairing
`⟨⟨x, L⟩, β⟩ ↦ ⟨⟨x, β⟩, L⟩`, then `B' := NUPPT.exists_withAdvice B₁ β`; on `⟨x, L⟩` (the input
and the encoded log) `B'` runs `B` on `⟨⟨x, β n⟩, L⟩`. -/
theorem exists_withAdviceOn (B : NUPPT) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ (B' : NUPPT) (h : B.coins = B'.coins), ∀ (n : ℕ) {ι α : Type} {spec : OracleSpec ι}
      (codec : MachineCodec spec α) (q : ℕ) (x : List Bool) (r : B.Coins n),
      B'.toCompOn codec n q x (NUPPT.coinsCongr h n r) =
        B.toCompOn codec n q (pairEncode x (β n)) r := by
  have hpre : PolyTimeComputable fun w : List Bool =>
      pairEncode (pairEncode (pairFstD (pairFstD w)) (pairSndD w)) (pairSndD (pairFstD w)) :=
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD).pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
  obtain ⟨B₁, hc₁, -, -, hB₁⟩ := NUPPT.exists_comp B hpre polyTimeComputable_id
  obtain ⟨B', hc', hB'⟩ := NUPPT.exists_withAdvice B₁ β b hβ
  refine ⟨B', (hc'.trans hc₁).symm, fun n ι α spec codec q x r => ?_⟩
  rw [NUPPT.toCompOn_eq, NUPPT.toCompOn_eq]
  congr 1
  funext hist
  rw [NUPPT.runAt_coinsCongr, hB', hB₁, NUPPT.runAt_eq]
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, id_eq]

end TCSlib.Cryptography.Composability.NMCCA2
