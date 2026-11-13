/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The NM distinguisher of IND ⇒ SIM

Direction IND ⇒ SIM of [PS10, Theorem 174.8] ([PSV07, Theorem 3], at one message). The NM
experiment hands its distinguisher the decryptions of the NM adversary's ciphertexts (`⊥` on a copy
of the challenge). The distinguisher `recDist S D` reads back the SIM experiment's view
`(a, m, (d_i)_i, σ)` from them and runs `D` on it:
* each of `A`'s ciphertexts comes with the encoding of its copy flag: the entry `d_i` is `COPY` if
  the flag is set, and the decryption otherwise (`entF`);
* each bit `x` of `a`, `m`, `σ` is encoded by `Enc_pk(x^{msgLen})`, `Enc_pk((¬x)^{msgLen})`; by
  correctness at most one of them is the challenge, and `guessBit` reads `x` from the two
  decryptions (`guessBit_encPair`).

## Main definitions

* `NMSim.entF`, `NMSim.bitG`, `NMSim.recView`: the reading of the view.
* `NMSim.recDist`: the distinguisher.

## Main results

* `NMSim.recDist_distinguisherL`, `NMSim.nmOutput_flatten`, `NMSim.guessBit_encPair`,
  `NMSim.recView_nmOutL`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Theorem 3.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open NMCCA2 (guessBit guessBit_eq guessBit_valid guessBit_refused)

variable (S : FixedLengthPKScheme)

/-! ### Reading the view -/

/-- `guessBit` is polynomial-time (DL-30–36 overlap: the content of the private
`polyTimeComputable_guessFun` of `Indistinguishability/Encrypt.lean`, on the bare string). -/
theorem polyTimeComputable_guessBit : PolyTimeComputable fun w => [guessBit w] :=
  (polyTimeComputable_ite polyTimeComputable_headD
    (polyTimeComputable_headD.comp polyTimeComputable_tail)
    (polyTimeComputable_not
      (polyTimeComputable_headD.comp BinArith.polyTimeComputable_reverse))).congr fun w => by
    rw [guessBit_eq]
    split <;> rfl

/-- **An entry read back** from the decryptions `v ‖ v₁ ‖ v₂` (`msgLen(n) + 1` bits each) of a
ciphertext and the encoding of its copy flag, on the context `⟨1^n, _⟩`: `COPY` if
`guessBit (v₁ ‖ v₂)`,
and `false` followed by `v` otherwise. -/
def entF (ctx ch : List Bool) : List Bool :=
  if guessBit (ch.drop ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length)) then
    true :: List.replicate ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length) false
  else false :: ch.take ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length)

/-- `entF S ctx ch =
if guessBit (ch.drop (msgLen + 1)) then COPY else false :: ch.take (msgLen + 1)`. -/
theorem entF_eq (ctx ch : List Bool) :
    entF S ctx ch =
      if guessBit (ch.drop ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length)) then
        true :: List.replicate ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length) false
      else false :: ch.take ((S.msgLen.add (.const 1)).eval (pairFstD ctx).length) := rfl

/-- **A bit read back** from the decryptions of its encoding: `[guessBit ch]`. -/
def bitG (_ctx ch : List Bool) : List Bool := [guessBit ch]

/-- `bitG ctx ch = [guessBit ch]`. -/
theorem bitG_eq (ctx ch : List Bool) : bitG ctx ch = [guessBit ch] := rfl

/-- `entF` is polynomial-time, as a function of `⟨ctx, ch⟩`. -/
theorem polyTimeComputable_entF : PolyTimeComputable fun z => entF S (pairFstD z) (pairSndD z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hcut : PolyTimeComputable fun z => pairEncode (pairFstD (pairFstD z)) (pairSndD z) :=
    (hF.comp hF).pairEncode hD
  have hdrop : PolyTimeComputable fun z =>
      (pairSndD z).drop ((S.msgLen.add (.const 1)).eval (pairFstD (pairFstD z)).length) :=
    ((polyTimeComputable_pairDropPoly (S.msgLen.add (.const 1))).comp hcut).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have htake : PolyTimeComputable fun z =>
      (pairSndD z).take ((S.msgLen.add (.const 1)).eval (pairFstD (pairFstD z)).length) :=
    ((polyTimeComputable_pairTakePoly (S.msgLen.add (.const 1))).comp hcut).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact polyTimeComputable_ite (polyTimeComputable_guessBit.comp hdrop)
    (BinArith.polyTimeComputable_cons (polyTimeComputable_const [true])
      (EnsembleLemmas.polyTimeComputable_zeros (S.msgLen.add (.const 1)) (hF.comp hF)))
    (BinArith.polyTimeComputable_cons (polyTimeComputable_const [false]) htake)

/-- `bitG` is polynomial-time, as a function of `⟨ctx, ch⟩`. -/
theorem polyTimeComputable_bitG : PolyTimeComputable fun z => bitG (pairFstD z) (pairSndD z) :=
  polyTimeComputable_guessBit.comp polyTimeComputable_pairSndD

variable (pl : PolyExpr) (r sl : PolyExpr)

/-- **The view read back** on the parameter string `U = 1^n` from the decryptions `u`: the entries
`E` (`chunkMap` of `entF` over the first `r` groups of three decryptions) and the bits `B`
(`chunkMap`
of `bitG` over the remaining pairs); the view is `B.take pl ‖ (B.drop pl).take msgLen ‖ E ‖
B.drop (pl + msgLen)`. -/
def recView (U u : List Bool) : List Bool :=
  (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
      (pairEncode (pairEncode U [])
        (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length)))).take
      (pl.eval U.length) ++
    ((chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
      (pairEncode (pairEncode U [])
        (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length)))).drop
      (pl.eval U.length)).take (S.msgLen.eval U.length) ++
    chunkMap ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))) (entF S)
      (pairEncode (pairEncode U [])
        (u.take ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length))) ++
    (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
      (pairEncode (pairEncode U [])
        (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length)))).drop
      ((pl.add S.msgLen).eval U.length)

/-- `recView S pl r U u = B.take pl ++ (B.drop pl).take msgLen ++ E ++ B.drop (pl + msgLen)`. -/
theorem recView_eq (U u : List Bool) :
    recView S pl r U u =
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
          (pairEncode (pairEncode U [])
            (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
              U.length)))).take (pl.eval U.length) ++
        ((chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
          (pairEncode (pairEncode U [])
            (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
              U.length)))).drop (pl.eval U.length)).take (S.msgLen.eval U.length) ++
        chunkMap ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))) (entF S)
          (pairEncode (pairEncode U [])
            (u.take ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval U.length))) ++
        (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
          (pairEncode (pairEncode U [])
            (u.drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
              U.length)))).drop ((pl.add S.msgLen).eval U.length) := rfl

/-- The reading of the view is polynomial-time, as a function of `⟨U, u⟩`.

**Proof sketch.** The chunk maps `B` (of `bitG`, on the `drop` of `u` after the `r` groups) and
`E` (of `entF`, on the matching `take`) are `polyTimeComputable_chunkMap` composed with
`pairTakePoly`/`pairDropPoly`. The three pieces of `B` cut `⟨U, B⟩` the same way (`take pl`,
`take msgLen` of `drop pl`, `drop (pl + msgLen)`), and `recView_eq` joins the four parts by
`append`. -/
theorem polyTimeComputable_recView :
    PolyTimeComputable fun z => recView S pl r (pairFstD z) (pairSndD z) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hcut : ∀ p : PolyExpr,
      PolyTimeComputable (fun z => (pairSndD z).take (p.eval (pairFstD z).length)) ∧
      PolyTimeComputable (fun z => (pairSndD z).drop (p.eval (pairFstD z).length)) := fun p =>
    ⟨polyTimeComputable_pairTakePoly p, polyTimeComputable_pairDropPoly p⟩
  have hctx : PolyTimeComputable fun z => pairEncode (pairFstD z) ([] : List Bool) :=
    hF.pairEncode (polyTimeComputable_const [])
  have hB : PolyTimeComputable fun z =>
      chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length))) :=
    (polyTimeComputable_chunkMap _ polyTimeComputable_bitG).comp
      (hctx.pairEncode (hcut _).2)
  have hE : PolyTimeComputable fun z =>
      chunkMap ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))) (entF S)
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).take ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length))) :=
    (polyTimeComputable_chunkMap _ (polyTimeComputable_entF S)).comp
      (hctx.pairEncode (hcut _).1)
  have hBU : ∀ p : PolyExpr, PolyTimeComputable (fun z => pairEncode (pairFstD z)
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length))))) := fun _ => hF.pairEncode hB
  have h1 : PolyTimeComputable fun z =>
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).take (pl.eval (pairFstD z).length) :=
    ((hcut pl).1.comp (hBU pl)).congr fun z => by
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have h2a : PolyTimeComputable fun z =>
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).drop (pl.eval (pairFstD z).length) :=
    ((hcut pl).2.comp (hBU pl)).congr fun z => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have h2 : PolyTimeComputable fun z =>
      ((chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).drop (pl.eval (pairFstD z).length)).take
        (S.msgLen.eval (pairFstD z).length) :=
    ((hcut S.msgLen).1.comp (hF.pairEncode h2a)).congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have h3 : PolyTimeComputable fun z =>
      (chunkMap ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))) bitG
        (pairEncode (pairEncode (pairFstD z) [])
          ((pairSndD z).drop ((r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval
            (pairFstD z).length)))).drop ((pl.add S.msgLen).eval (pairFstD z).length) :=
    ((hcut (pl.add S.msgLen)).2.comp (hBU pl)).congr fun z => by
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact (((h1.append h2).append hE).append h3).congr fun z => by rw [recView_eq]

variable (D : NUPPT)

/-- `recDist`'s raw function on `⟨⟨⟨1^n, u⟩, α⟩, ρ⟩`: `D`'s output (advice `α`, coins `ρ`) on the
view read back from `u`. -/
private def recFun (z : List Bool) : List Bool :=
  D.output (NUPPT.layout (NUPPT.inParam z) (recView S pl r (NUPPT.inParam z) (NUPPT.inArg z))
    (NUPPT.inAdvice z) (NUPPT.inCoins z))

/-- The raw function is polynomial-time. -/
private theorem polyTimeComputable_recFun : PolyTimeComputable (recFun S pl r D) :=
  D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
    ((polyTimeComputable_recView S pl r).comp (NUPPT.polyTimeComputable_inParam.pairEncode
      NUPPT.polyTimeComputable_inArg) |>.congr fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
    NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins)

/-- **The NM distinguisher** built from `D`, with `D`'s coins and advice: it reads the SIM view back
from the decryptions (`recView`) and runs `D` on it. -/
noncomputable def recDist : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_recFun S pl r D) D.coins D.adv D.advice D.advice_length

/-- The NM distinguisher has `D`'s coins. -/
theorem recDist_coins : (recDist S pl r D).coins = D.coins := by
  rw [recDist, NUPPT.coins_ofPolyTime]

/-- **The NM distinguisher's verdict** on the decryptions `u`, with `D`'s coins `rD` carried over,
is `D`'s verdict on the view read back: `recDist.distinguisherL n u rD = D.distinguisherL n
(recView 1^n u) rD`. -/
theorem recDist_distinguisherL (n : ℕ) (u : List Bool) (rD : D.Coins n) :
    (recDist S pl r D).distinguisherL n u (NUPPT.coinsCongr (recDist_coins S pl r D).symm n rD) =
      D.distinguisherL n (recView S pl r (List.replicate n true) u) rD := by
  have hlay : pairEncode (pairEncode (NUPPT.advInput n u) (D.advice n)) (List.ofFn rD) =
      NUPPT.layout (List.replicate n true) u (D.advice n) (List.ofFn rD) := by
    rw [NUPPT.layout_eq, NUPPT.advInput_eq]
  rw [NUPPT.distinguisherL_eq, NUPPT.runAt_coinsCongr, recDist, NUPPT.runAtL_ofPolyTime, recFun,
    hlay]
  simp only [NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inAdvice_layout,
    NUPPT.inCoins_layout]
  rw [← NUPPT.runAtL_eq_output_layout, ← NUPPT.runAt_eq, ← NUPPT.distinguisherL_eq]

/-! ### The view is read back -/

/-- **The decryptions of concatenated ciphertexts:** for `ℓ` ciphertexts `cs` of `ctLen(n)` bits,
`nmOutput sk s' (padFin _ cs.flatten)` is the concatenation of the entries' tails
`(entryL … [c is the challenge] c).drop 1` (`nmOutput_eq_entryTails`, `map_coinBlock_flatten`). -/
theorem nmOutput_flatten (n ℓ : ℕ) (sk : List Bool) (s' : Option (Fin (S.ctLen.eval n) → Bool))
    (cs : List (List Bool)) (hℓ : cs.length = ℓ) (hc : ∀ c ∈ cs, c.length = S.ctLen.eval n) :
    S.nmOutput sk s' (padFin (ℓ * S.ctLen.eval n) cs.flatten) =
      (cs.map fun c => (entryL S n sk (decide (s'.map List.ofFn = some c)) c).drop 1).flatten := by
  have hlen : cs.flatten.length = ℓ * S.ctLen.eval n := by
    rw [List.length_flatten, ← hℓ]
    have : cs.map List.length = cs.map fun _ => S.ctLen.eval n := List.map_congr_left hc
    rw [this, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [nmOutput_eq_entryTails S n ℓ sk s' _ hlen, ← hℓ,
    map_coinBlock_flatten (S.ctLen.eval n) (fun c => (entryL S n sk
      (decide (s'.map List.ofFn = some c)) c).drop 1) cs hc]

variable (samp : NUPPT)

/-- **The ciphertexts are not empty** when the messages are not: with `msgLen(n) > 0`, correctness
gives `ctLen(n) > 0` (two different messages cannot both decrypt from the empty ciphertext). -/
theorem ctLen_pos (n : ℕ) (rg : S.gen.Coins n) (re : S.enc.Coins n) (hL : 0 < S.msgLen.eval n) :
    0 < S.ctLen.eval n := by
  by_contra h
  have h0 : S.ctLen.eval n = 0 := by omega
  have hnil : ∀ m : Fin (S.msgLen.eval n) → Bool,
      S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re = [] := fun m =>
    List.eq_nil_of_length_eq_zero ((S.enc_length n rg m re).trans h0)
  have h₁ := S.correct n (fun _ => true) rg re
  have h₂ := S.correct n (fun _ => false) rg re
  rw [hnil] at h₁ h₂
  have := congrFun (Option.some.inj (h₁.symm.trans h₂)) ⟨0, hL⟩
  exact absurd this (by decide)

/-- **The encoding of a bit is read back** from its decryptions: under generated keys, with
`msgLen(n) > 0`, for the context `⟨1^n, ⟨z, ⟨ω, st⟩⟩⟩` with `pk = fst z` and the tape `re` after
`2·coins(n)` bits of `ω`, `guessBit (v(Enc_pk(x^{msgLen})) ‖ v(Enc_pk((¬x)^{msgLen}))) = x`, where
`v c` is the decryption of `c` in the NM output (`⊥` on the challenge `s'`).

**Proof sketch.** The two ciphertexts decrypt to `x^{msgLen}` and `(¬x)^{msgLen}` (correctness), so
they differ and at most one is the challenge: `guessBit_valid` or `guessBit_refused`. -/
theorem guessBit_encPair (n : ℕ) (rg : S.gen.Coins n) (s' : Option (Fin (S.ctLen.eval n) → Bool))
    (hL : 0 < S.msgLen.eval n) (z ω st : List Bool)
    (hz : pairFstD z = pairFstD (S.gen.runAt n [] rg))
    (re : S.enc.Coins n) (hω : ω.drop ((samp.coins.add samp.coins).eval n) = List.ofFn re)
    (x : Bool) :
    guessBit ((entryL S n (pairSndD (S.gen.runAt n [] rg))
        (decide (s'.map List.ofFn = some (encBit S samp
          (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st))) x)))
        (encBit S samp (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)))
          x)).drop 1 ++
      (entryL S n (pairSndD (S.gen.runAt n [] rg))
        (decide (s'.map List.ofFn = some (encBit S samp
          (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st))) (!x))))
        (encBit S samp (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)))
          (!x))).drop 1) = x := by
  have henc : ∀ y,
      encBit S samp (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)))
      y = S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => y)) re := by
    intro y
    rw [encBit_eq, pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode,
      pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate, hω, hz, List.ofFn_const,
      EnsembleLemmas.padL_eq, NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq]
    refine List.take_left' ?_
    have := S.enc_length n rg (fun _ => y) re
    rw [NUPPT.Uniform.runAt_eq S.enc_uniform, NUPPT.advInput_eq, List.ofFn_const] at this
    exact this
  have hdec : ∀ y, decodeFin (S.msgLen.eval n) (S.dec (pairEncode (pairSndD (S.gen.runAt n [] rg))
      (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => y)) re))) = some fun _ => y :=
    fun y => S.correct n _ rg re
  have hne : S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
      (List.ofFn fun _ : Fin (S.msgLen.eval n) => x)) re ≠
      S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => !x)) re := by
    intro heq
    have h₁ := hdec x
    rw [heq, hdec (!x)] at h₁
    have := congrFun (Option.some.inj h₁) ⟨0, hL⟩
    cases x <;> exact absurd this (by decide)
  rw [henc, henc, entryL_drop_one, entryL_drop_one, hdec, hdec]
  by_cases h : s'.map List.ofFn = some (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
    (List.ofFn fun _ : Fin (S.msgLen.eval n) => x)) re)
  · have h' : ¬ s'.map List.ofFn = some (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg))
        (List.ofFn fun _ : Fin (S.msgLen.eval n) => !x)) re) := by
      rw [h]
      exact fun h'' => hne (Option.some.inj h'')
    rw [if_pos (decide_eq_true h), if_neg (by simpa using h'), ← ofFn_zeroBits]
    exact guessBit_refused hL x
  · rw [if_neg (by simpa using h)]
    exact guessBit_valid hL x _

/-- **The view is read back from the NM output** (under generated keys, `msgLen(n) > 0`): for the
NM adversary's output on the context `⟨1^n, ⟨z, ⟨ω, st⟩⟩⟩` (`A`'s output `a`, the parameter `aP`,
the message `mP`), whose copy flags agree with the challenge `s'` (`hflag`), `recView` of the
decryptions is `aP ‖ mP ‖ (d_i)_i ‖ σ` with `d_i = entryL … [c_i is the challenge] c_i`.

**Proof sketch.** The output is a concatenation of `ctLen(n)`-bit ciphertexts
(`nmOutput_flatten`): for each `c_i`, its decryption and those of its flag's encoding; for each bit
of `aP ‖ mP ‖ σ`, the decryptions of its encoding. `entF` turns each group of three into `d_i`
(`guessBit_encPair`, `hflag`) and `bitG` each pair into its bit (`chunkMap_flatten`). -/
theorem recView_nmOutL (n : ℕ) (rg : S.gen.Coins n) (hL : 0 < S.msgLen.eval n)
    (s' : Option (Fin (S.ctLen.eval n) → Bool)) (z ω st a aP mP : List Bool)
    (hz : pairFstD z = pairFstD (S.gen.runAt n [] rg)) (re : S.enc.Coins n)
    (hω : ω.drop ((samp.coins.add samp.coins).eval n) = List.ofFn re)
    (ha : a.length = r.eval n * S.ctLen.eval n + sl.eval n) (haP : aP.length = pl.eval n)
    (hmP : mP.length = S.msgLen.eval n)
    (hflag : ∀ c : List Bool, (st.headD false && decide (c = (st.drop 1).take (S.ctLen.eval n))) =
      decide (s'.map List.ofFn = some c)) :
    recView S pl r (List.replicate n true) (S.nmOutput (pairSndD (S.gen.runAt n [] rg)) s'
        (padFin ((nmLen S pl r sl).eval n * S.ctLen.eval n) (nmOutL S samp r n
          (pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st))) a aP mP))) =
      aP ++ mP ++ ((List.range (r.eval n)).map fun i => entryL S n (pairSndD (S.gen.runAt n [] rg))
        (decide (s'.map List.ofFn = some (coinBlock (S.ctLen.eval n) i a)))
        (coinBlock (S.ctLen.eval n) i a)).flatten ++ a.drop (r.eval n * S.ctLen.eval n) := by
  set sk := pairSndD (S.gen.runAt n [] rg) with hsk
  set ctx := pairEncode (List.replicate n true) (pairEncode z (pairEncode ω st)) with hctx
  set v : List Bool → List Bool := fun c =>
    (entryL S n sk (decide (s'.map List.ofFn = some c)) c).drop 1 with hvdef
  set f : ℕ → Bool := fun i => st.headD false &&
    decide (coinBlock (S.ctLen.eval n) i a = (st.drop 1).take (S.ctLen.eval n)) with hfdef
  set bits := aP ++ mP ++ a.drop (r.eval n * S.ctLen.eval n) with hbits
  have hct := ctLen_pos S n rg re hL
  have hci : ∀ i < r.eval n, (coinBlock (S.ctLen.eval n) i a).length = S.ctLen.eval n := fun i hi =>
    length_coinBlock (by
      rw [ha]
      have := Nat.mul_le_mul_right (S.ctLen.eval n) (show i + 1 ≤ r.eval n from hi)
      omega)
  have hv : ∀ c, (v c).length = S.msgLen.eval n + 1 := fun c => by
    rw [hvdef, List.length_drop, length_entryL]
    omega
  have he : ∀ x, (encBit S samp ctx x).length = S.ctLen.eval n := fun x =>
    length_encBit S samp n _ x
  set cs : List (List Bool) := ((List.range (r.eval n)).map fun i =>
      [coinBlock (S.ctLen.eval n) i a, encBit S samp ctx (f i),
        encBit S samp ctx (!f i)]).flatten ++
    (bits.map fun x => [encBit S samp ctx x, encBit S samp ctx (!x)]).flatten with hcs
  have hW : nmOutL S samp r n ctx a aP mP = cs.flatten := by
    rw [nmOutL_eq, hcs, List.flatten_append, List.flatten_flatten, List.flatten_flatten,
      List.map_map, List.map_map]
    refine congrArg₂ (· ++ ·) (congrArg List.flatten ?_) (congrArg List.flatten ?_)
    · refine List.map_congr_left fun i _ => ?_
      rw [Function.comp_apply, encF_eq, encPair_eq, ctxSt_eq, hctx]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, List.flatten_cons,
        List.flatten_nil, List.append_nil, hfdef]
    · refine List.map_congr_left fun x _ => ?_
      rw [Function.comp_apply, encPair_eq]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  have hcs_len : cs.length = (nmLen S pl r sl).eval n := by
    rw [hcs, List.length_append, List.length_flatten, List.length_flatten, List.map_map,
      List.map_map]
    have h3 : (List.map (List.length ∘ fun i =>
        [coinBlock (S.ctLen.eval n) i a, encBit S samp ctx (f i), encBit S samp ctx (!f i)])
        (List.range (r.eval n))) = List.replicate (r.eval n) 3 := by
      rw [List.eq_replicate_iff, List.length_map, List.length_range]
      refine ⟨rfl, fun b hb => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
      rfl
    have h2 : (List.map (List.length ∘ fun x => [encBit S samp ctx x, encBit S samp ctx (!x)])
        bits) = List.replicate bits.length 2 := by
      rw [List.eq_replicate_iff, List.length_map]
      refine ⟨rfl, fun b hb => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
      rfl
    rw [h3, h2, List.sum_replicate, List.sum_replicate, smul_eq_mul, smul_eq_mul, nmLen_eval, hbits,
      List.length_append, List.length_append, List.length_drop, haP, hmP, ha]
    omega
  have hcs_ct : ∀ c ∈ cs, c.length = S.ctLen.eval n := by
    intro c hc
    rcases List.mem_append.1 hc with h | h
    · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 h
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
      rw [List.mem_range] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl | rfl
      · exact hci i hi
      · exact he _
      · exact he _
    · obtain ⟨l, hl, hcl⟩ := List.mem_flatten.1 h
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
      rcases hcl with rfl | rfl
      · exact he _
      · exact he _
  rw [hW, nmOutput_flatten S n _ sk s' cs hcs_len hcs_ct]
  have hP : (cs.map v).flatten =
      ((List.range (r.eval n)).map fun i => v (coinBlock (S.ctLen.eval n) i a) ++
        (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).flatten ++
      (bits.map fun x => v (encBit S samp ctx x) ++ v (encBit S samp ctx (!x))).flatten := by
    rw [hcs, List.map_append, List.flatten_append, List.map_flatten, List.map_flatten,
      List.flatten_flatten, List.flatten_flatten, List.map_map, List.map_map, List.map_map,
      List.map_map]
    refine congrArg₂ (· ++ ·) (congrArg List.flatten ?_) (congrArg List.flatten ?_)
    · refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
    · refine List.map_congr_left fun x _ => ?_
      simp only [Function.comp_apply, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
  have h3 : ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))).eval n =
      3 * (S.msgLen.eval n + 1) := by
    rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_const]
  have h2 : ((PolyExpr.const 2).mul (S.msgLen.add (.const 1))).eval n =
      2 * (S.msgLen.eval n + 1) := by
    rw [PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_const]
  have h1 : (S.msgLen.add (.const 1)).eval n = S.msgLen.eval n + 1 := by
    rw [PolyExpr.eval_add, PolyExpr.eval_const]
  have hg3 : ∀ i < r.eval n, (v (coinBlock (S.ctLen.eval n) i a) ++
      (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).length =
      ((PolyExpr.const 3).mul (S.msgLen.add (.const 1))).eval n := fun i _ => by
    rw [List.length_append, List.length_append, hv, hv, hv, h3]
    ring
  have hP1 : (((List.range (r.eval n)).map fun i => v (coinBlock (S.ctLen.eval n) i a) ++
      (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))).flatten).length =
      (r.mul ((PolyExpr.const 3).mul (S.msgLen.add (.const 1)))).eval n := by
    rw [length_flatten_map_range _ _ _ hg3]
    exact (PolyExpr.eval_mul _ _ _).symm
  rw [hP, recView_eq, List.length_replicate, List.take_left' hP1, List.drop_left' hP1,
    chunkMap_flatten _ _ n [] _ (fun ch hch => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hch
      rw [List.length_append, hv, hv, h2]
      ring) (by rw [h2]; omega),
    chunkMap_flatten _ _ n [] _ (fun ch hch => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hch
      exact hg3 i (List.mem_range.1 hi)) (by rw [h3]; omega), List.map_map, List.map_map]
  have hB : (bits.map (bitG (pairEncode (List.replicate n true) []) ∘ fun x =>
      v (encBit S samp ctx x) ++ v (encBit S samp ctx (!x)))).flatten = bits := by
    have hx : ∀ x, (bitG (pairEncode (List.replicate n true) []) ∘ fun x =>
        v (encBit S samp ctx x) ++ v (encBit S samp ctx (!x))) x = [x] := by
      intro x
      rw [Function.comp_apply, bitG_eq, hvdef]
      exact congrArg (· :: []) (guessBit_encPair S samp n rg s' hL z ω st hz re hω x)
    have hfl : ∀ l : List Bool, (l.map fun x => [x]).flatten = l := by
      intro l
      induction l with
      | nil => rfl
      | cons x t ih => rw [List.map_cons, List.flatten_cons, ih]; rfl
    rw [List.map_congr_left (fun x _ => hx x), hfl]
  have hE : (List.range (r.eval n)).map (entF S (pairEncode (List.replicate n true) []) ∘ fun i =>
      v (coinBlock (S.ctLen.eval n) i a) ++
        (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i)))) =
      (List.range (r.eval n)).map fun i => entryL S n sk
        (decide (s'.map List.ofFn = some (coinBlock (S.ctLen.eval n) i a)))
        (coinBlock (S.ctLen.eval n) i a) := by
    refine List.map_congr_left fun i _ => ?_
    have hg : guessBit (v (encBit S samp ctx (f i)) ++ v (encBit S samp ctx (!f i))) = f i := by
      rw [hvdef]
      exact guessBit_encPair S samp n rg s' hL z ω st hz re hω (f i)
    have hf : f i = decide (s'.map List.ofFn = some (coinBlock (S.ctLen.eval n) i a)) := hflag _
    rw [Function.comp_apply, entF_eq, pairFstD_pairEncode, List.length_replicate, h1,
      List.drop_left' (hv _), List.take_left' (hv _), hg, hf, entryL_eq]
    by_cases hc : s'.map List.ofFn = some (coinBlock (S.ctLen.eval n) i a)
    · rw [if_pos (decide_eq_true hc), if_pos (decide_eq_true hc)]
    · rw [if_neg (by simpa using hc), if_neg (by simpa using hc), hvdef]
      simp only [hc, decide_false, entryL_eq, Bool.false_eq_true, ↓reduceIte, List.drop_one,
        List.tail_cons]
  rw [hB, hE, hbits, PolyExpr.eval_add]
  have hmP' : (aP ++ mP).length = pl.eval n + S.msgLen.eval n := by
    rw [List.length_append, haP, hmP]
  rw [List.append_assoc aP mP, List.take_left' (by rw [haP]), List.drop_left' (by rw [haP]),
    List.take_left' hmP, ← List.append_assoc, List.drop_left' hmP']

end TCSlib.Cryptography.Composability.NMSim
