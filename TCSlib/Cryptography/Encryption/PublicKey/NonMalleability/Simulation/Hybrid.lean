/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hybrid oracle of Theorem 174.8

The real experiment of SIM-NME′ [PSV07, Definition 1] (`Simulation.lean`) runs the adversary
against two oracles: `Dec` (per the attack) and a challenge that, on the sampler's parameter `a`,
draws `m = M(a; ρ)`, encrypts it and answers `⟨Enc_pk(m), h(m)⟩`. Both directions of
[PS10, Theorem 174.8] compare runs against variants of these oracles. This file states them
once, generically in the sampler (a machine `samp`, the parameter length `pl`, the history
function `hist` and its length `hl`), on the lengths that T2 machines use (`snmDin`, `snmDout`):

* `rImpl … b … ρ ρ' ce` encrypts `M(a; ρ)` for `b = false` and `M(a; ρ')` for `b = true`, always
  answering the history of `m = M(a; ρ)`. With `b = false` it is the real experiment's oracle; with
  `b = true` it is the hybrid in which the adversary sees an encryption of an independent draw. The
  encryption coins are sampled (`ce = none`) or given in advance (`ce = some re`).
* `realView` and `idealView` are the experiments' outputs `(a, m, (d_i)_i, σ)` as strings, read
  from the adversary's (respectively the simulator's) output string and the final state.

## Main definitions

* `NMSim.snmDin`, `NMSim.snmDout`: the oracle lengths as polynomials.
* `NMSim.drawWith`, `NMSim.histWith`, `NMSim.encWith`: `M(a; ρ)`, `h(m)` and `Enc_pk(m; re)`.
* `NMSim.rImpl`: the hybrid oracle.
* `NMSim.chunkAt`, `NMSim.entryL`, `NMSim.realView`, `NMSim.idealView`.

## Main results

* `NMSim.snmDin_eval_inLens`, `NMSim.snmDout_eval_outLens`: with `pl = 2·msgLen` and `hl = 0` the
  lengths are those of Definition 171.5.
* `NMSim.rImpl_dec`, `_some`, `_none_lazy`, `_none_eager`, `_dec_cpa`: the oracle's answers.
* `NMSim.rImpl_eq_of_msgLen_eq_zero`: with empty messages the two hybrids coincide.
* `NMSim.expect_simulate_rImpl_eager`: the encryption coins may be drawn in advance.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.6, Theorem 174.8 (book p. 174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definition 1.
-/

namespace TCSlib.Cryptography.Composability.NMSim

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

variable (S : FixedLengthPKScheme)

/-! ### Lengths -/

/-- The query lengths of the real experiment's oracles as polynomials: ciphertexts for `Dec`, the
sampler's parameter (`pl(n)` bits) for the challenge. -/
def snmDin (pl : PolyExpr) : Fin 2 → PolyExpr
  | 0 => S.ctLen
  | 1 => pl

/-- `Dec` queries are ciphertexts: `snmDin S pl 0 = S.ctLen`. -/
theorem snmDin_zero (pl : PolyExpr) : snmDin S pl 0 = S.ctLen := rfl

/-- Challenge queries are parameters: `snmDin S pl 1 = pl`. -/
theorem snmDin_one (pl : PolyExpr) : snmDin S pl 1 = pl := rfl

/-- The answer lengths as polynomials: a flag and a message for `Dec`, a ciphertext and the
history (`hl(n)` bits) for the challenge. -/
def snmDout (hl : PolyExpr) : Fin 2 → PolyExpr
  | 0 => S.msgLen.add (.const 1)
  | 1 => S.ctLen.add hl

/-- `Dec` answers a flag and a message: `snmDout S hl 0 = msgLen + 1`. -/
theorem snmDout_zero (hl : PolyExpr) : snmDout S hl 0 = S.msgLen.add (.const 1) := rfl

/-- The challenge answers a ciphertext and the history: `snmDout S hl 1 = ctLen + hl`. -/
theorem snmDout_one (hl : PolyExpr) : snmDout S hl 1 = S.ctLen.add hl := rfl

/-- With the parameter `⟨m₀, m₁⟩` (`pl = msgLen + msgLen`) the query lengths are those of
Definition 171.5: `(snmDin S (msgLen + msgLen) ·).eval n = S.inLens n`. -/
theorem snmDin_eval_inLens (n : ℕ) :
    (fun i => (snmDin S (S.msgLen.add S.msgLen) i).eval n) = S.inLens n := by
  funext i
  match i with
  | 0 => rw [snmDin_zero, S.inLens_zero]
  | 1 => rw [snmDin_one, PolyExpr.eval_add, S.inLens_one]

/-- With an empty history (`hl = 0`) the answer lengths are those of Definition 171.5:
`(snmDout S 0 ·).eval n = S.outLens n`. -/
theorem snmDout_eval_outLens (n : ℕ) :
    (fun i => (snmDout S (.const 0) i).eval n) = S.outLens n := by
  funext i
  match i with
  | 0 => rw [snmDout_zero, PolyExpr.eval_add, PolyExpr.eval_const, S.outLens_zero]
  | 1 => rw [snmDout_one, PolyExpr.eval_add, PolyExpr.eval_const, Nat.add_zero, S.outLens_one]

/-! ### Draws, histories and encryptions -/

/-- The message `M(a; ρ)` drawn by the sampler `samp` on the parameter `a` with coins `ρ`, read at
`ℓ` bits: `drawWith samp ℓ n a ρ = padFin ℓ (samp.runAt n ⟦a⟧ ρ)`. -/
def drawWith (samp : NUPPT) (ℓ n : ℕ) {k : ℕ} (a : Fin k → Bool) (ρ : samp.Coins n) :
    Fin ℓ → Bool :=
  padFin ℓ (samp.runAt n (List.ofFn a) ρ)

/-- `drawWith samp ℓ n a ρ = padFin ℓ (samp.runAt n ⟦a⟧ ρ)`. -/
theorem drawWith_eq (samp : NUPPT) (ℓ n : ℕ) {k : ℕ} (a : Fin k → Bool) (ρ : samp.Coins n) :
    drawWith samp ℓ n a ρ = padFin ℓ (samp.runAt n (List.ofFn a) ρ) := rfl

/-- The history `h(m)` read at `hl` bits: `histWith hist hl m = padFin hl (hist ⟦m⟧)`. -/
def histWith (hist : List Bool → List Bool) (hl : ℕ) {ℓ : ℕ} (m : Fin ℓ → Bool) : Fin hl → Bool :=
  padFin hl (hist (List.ofFn m))

/-- `histWith hist hl m = padFin hl (hist ⟦m⟧)`. -/
theorem histWith_eq (hist : List Bool → List Bool) (hl : ℕ) {ℓ : ℕ} (m : Fin ℓ → Bool) :
    histWith hist hl m = padFin hl (hist (List.ofFn m)) := rfl

/-- The encryption `Enc_pk(m; re)` read at `ctLen(n)` bits:
`encWith S n pk m re = padFin ctLen(n) (Enc.runAt n ⟨pk, ⟦m⟧⟩ re)`. -/
def encWith (n : ℕ) (pk : List Bool) {ℓ : ℕ} (m : Fin ℓ → Bool) (re : S.enc.Coins n) :
    Fin (S.ctLen.eval n) → Bool :=
  padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn m)) re)

/-- `encWith S n pk m re = padFin ctLen(n) (Enc.runAt n ⟨pk, ⟦m⟧⟩ re)`. -/
theorem encWith_eq (n : ℕ) (pk : List Bool) {ℓ : ℕ} (m : Fin ℓ → Bool) (re : S.enc.Coins n) :
    encWith S n pk m re = padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn m)) re) := rfl

/-! ### The hybrid oracle -/

/-- **The hybrid oracle** at parameter `n`, for the keys `pk`, `sk`, the sampler `samp` (parameter
length `pl`, history `hist` of length `hl`) and its coins `ρ`, `ρ'`, on T2's lengths
(`snmDin`, `snmDout`); the state is the challenge with its parameter, once asked.
- `Dec` answers as in Definition 171.5: `⟨1, Dec_sk(c)⟩` when it is open (`decOpen`) and `c` is not
  the challenge, and `⊥` (all `false`) otherwise.
- The challenge on the parameter `a`, the first time: `m = M(a; ρ)`; it encrypts `M(a; ρ)` for
  `b = false` and `M(a; ρ')` for `b = true`, with coins sampled (`ce = none`) or given (`ce = some
  re`), answers `⟨y, h(m)⟩` and records `(y, a)`. Later it repeats `⟨y, h(M(a₀; ρ))⟩` for the
  recorded `(y, a₀)`. -/
noncomputable def rImpl (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
    (ce : Option (S.enc.Coins n)) :
    QueryImpl (bitSpecAt (snmDin S pl) (snmDout S hl) n)
      (Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) unifSpec
  | 0, c, s =>
    if FixedLengthScheme.decOpen atk s.isSome &&
        !decide (s.map Prod.fst = some (padFin _ (List.ofFn c))) then
      .pure (padFin _ (List.ofFn (FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c)))))), s)
    else .pure (zeroBits _, s)
  | 1, _, some (y, a) =>
    .pure (padFin _ (List.ofFn y ++ List.ofFn (histWith hist (hl.eval n)
      (drawWith samp (S.msgLen.eval n) n a ρ))), some (y, a))
  | 1, x, none =>
    match ce with
    | some re =>
      .pure (padFin _ (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
          (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re) ++
          List.ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) ρ))),
        some (encWith S n pk (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
          (if b then ρ' else ρ)) re, padFin (pl.eval n) (List.ofFn x)))
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun re =>
        .pure (padFin _ (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re) ++
            List.ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
              (padFin (pl.eval n) (List.ofFn x)) ρ))),
          some (encWith S n pk (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re,
            padFin (pl.eval n) (List.ofFn x)))

section Readers

variable (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
  (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
  (ce : Option (S.enc.Coins n))

/-- **Decryption** as in Definition 171.5: `⟨1, Dec_sk(c)⟩` when open and not the recorded
challenge, `⊥` otherwise; the state is kept. -/
theorem rImpl_dec (c : Fin ((snmDin S pl 0).eval n) → Bool)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome &&
          !decide (s.map Prod.fst = some (padFin _ (List.ofFn c))) then
        .pure (padFin _ (List.ofFn (FixedLengthScheme.decAnswer
          (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c)))))), s)
      else .pure (zeroBits _, s) := rfl

/-- **Under CPA, `Dec` answers `⊥`** and keeps the state. -/
theorem rImpl_dec_cpa (b : Bool) (c : Fin ((snmDin S pl 0).eval n) → Bool)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    rImpl S .cpa b samp pl hl hist n pk sk ρ ρ' ce 0 c s = .pure (zeroBits _, s) := by
  rw [rImpl_dec, FixedLengthScheme.decOpen_cpa, Bool.false_and, if_neg Bool.false_ne_true]

/-- **A repeated challenge** answers `⟨y, h(M(a₀; ρ))⟩` for the recorded `(y, a₀)` and keeps the
state. -/
theorem rImpl_some (x : Fin ((snmDin S pl 1).eval n) → Bool) (y : Fin (S.ctLen.eval n) → Bool)
    (a : Fin (pl.eval n) → Bool) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 1 x (some (y, a)) =
      .pure (padFin _ (List.ofFn y ++ List.ofFn (histWith hist (hl.eval n)
        (drawWith samp (S.msgLen.eval n) n a ρ))), some (y, a)) := rfl

/-- **A first challenge with coins drawn in advance:** on `x` (read as the parameter `a`) it
answers `⟨Enc_pk(M(a; ρ_b); re), h(M(a; ρ))⟩` and records the ciphertext with `a`. -/
theorem rImpl_none_eager (x : Fin ((snmDin S pl 1).eval n) → Bool) (re : S.enc.Coins n) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' (some re) 1 x none =
      .pure (padFin _ (List.ofFn (encWith S n pk (drawWith samp (S.msgLen.eval n) n
          (padFin (pl.eval n) (List.ofFn x)) (if b then ρ' else ρ)) re) ++
          List.ofFn (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n
            (padFin (pl.eval n) (List.ofFn x)) ρ))),
        some (encWith S n pk (drawWith samp (S.msgLen.eval n) n (padFin (pl.eval n) (List.ofFn x))
          (if b then ρ' else ρ)) re, padFin (pl.eval n) (List.ofFn x))) := rfl

/-- **A first challenge with sampled coins** samples `re` and answers as with `re` in advance. -/
theorem rImpl_none_lazy (x : Fin ((snmDin S pl 1).eval n) → Bool) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' none 1 x none =
      (ProbComp.sample (S.enc.Coins n)).bind fun re =>
        rImpl S atk b samp pl hl hist n pk sk ρ ρ' (some re) 1 x none := rfl

/-- Decryption does not read the encryption coins. -/
theorem rImpl_dec_ce (ce' : Option (S.enc.Coins n)) (c : Fin ((snmDin S pl 0).eval n) → Bool)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 0 c s =
      rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce' 0 c s := rfl

/-- A repeated challenge does not read the encryption coins. -/
theorem rImpl_some_ce (ce' : Option (S.enc.Coins n)) (x : Fin ((snmDin S pl 1).eval n) → Bool)
    (y : Fin (S.ctLen.eval n) → Bool) (a : Fin (pl.eval n) → Bool) :
    rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce 1 x (some (y, a)) =
      rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce' 1 x (some (y, a)) := rfl

end Readers

/-- Every call keeps a recorded state recorded: from `some _`, every successor is `some _`. -/
theorem rImpl_allOutputs_isSome (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
    (ce : Option (S.enc.Coins n)) (i : Fin 2) (x : (bitSpecAt (snmDin S pl) (snmDout S hl) n).dom i)
    (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) (hs : s.isSome) :
    (rImpl S atk b samp pl hl hist n pk sk ρ ρ' ce i x s).AllOutputs fun p => p.2.isSome := by
  obtain ⟨⟨y, a⟩, rfl⟩ := Option.isSome_iff_exists.1 hs
  match i with
  | 0 =>
    rw [rImpl_dec]
    split <;> exact OracleComp.allOutputs_pure.2 rfl
  | 1 => exact OracleComp.allOutputs_pure.2 rfl

/-- **The encryption coins may be drawn in advance:** for every computation `c` and function `G`,
the run against the hybrid oracle with sampled coins has the law of the runs with coins `re`
drawn in advance, averaged over `re` (`expect_simulate_eager`; the coins are spent at the first
challenge). -/
theorem expect_simulate_rImpl_eager (atk : Attack) (b : Bool) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n) {α : Type}
    (c : OracleComp (bitSpecAt (snmDin S pl) (snmDout S hl) n) α)
    (G : α × Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool)) → ℝ) :
    ProbComp.expect (simulate (rImpl S atk b samp pl hl hist n pk sk ρ ρ' none) c none) G =
      ProbComp.expect (ProbComp.sample (S.enc.Coins n)) fun re =>
        ProbComp.expect (simulate (rImpl S atk b samp pl hl hist n pk sk ρ ρ' (some re)) c none)
          G := by
  refine expect_simulate_eager _ _ (fun s => s.isSome = true) (fun re i x s hs => ?_)
    (fun i x s hs => rImpl_allOutputs_isSome S atk b samp pl hl hist n pk sk ρ ρ' none i x s hs)
    (fun i x s hs => ?_) c G (by simp)
  · obtain ⟨⟨y, a⟩, rfl⟩ := Option.isSome_iff_exists.1 hs
    match i with
    | 0 => exact rImpl_dec_ce S atk b samp pl hl hist n pk sk ρ ρ' (some re) none x _
    | 1 => exact rImpl_some_ce S atk b samp pl hl hist n pk sk ρ ρ' (some re) none x y a
  · have hs' : s = none := by simpa using hs
    subst hs'
    match i with
    | 0 =>
      refine Or.inl fun re => ⟨rImpl_dec_ce S atk b samp pl hl hist n pk sk ρ ρ' _ _ x none, ?_⟩
      rw [rImpl_dec]
      split <;> exact OracleComp.allOutputs_pure.2 (by simp)
    | 1 =>
      refine Or.inr ⟨rImpl_none_lazy S atk b samp pl hl hist n pk sk ρ ρ' x, fun re => ?_⟩
      rw [rImpl_none_eager]
      exact OracleComp.allOutputs_pure.2 rfl

/-- **With empty messages the two hybrids coincide:** if `msgLen(n) = 0`, then the oracle encrypting
`M(a; ρ')` is the one encrypting `M(a; ρ)` (both draws are the empty message). -/
theorem rImpl_eq_of_msgLen_eq_zero (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ' : samp.Coins n)
    (ce : Option (S.enc.Coins n)) (h : S.msgLen.eval n = 0) :
    rImpl S atk true samp pl hl hist n pk sk ρ ρ' ce =
      rImpl S atk false samp pl hl hist n pk sk ρ ρ' ce := by
  have hsub : ∀ {k : ℕ} (a : Fin k → Bool),
      drawWith samp (S.msgLen.eval n) n a ρ' = drawWith samp (S.msgLen.eval n) n a ρ := by
    intro k a
    funext j
    have := j.isLt
    omega
  funext i x s
  match i, s with
  | 0, s => rfl
  | 1, some (y, a) => rfl
  | 1, none =>
    cases ce with
    | some re => rw [rImpl_none_eager, rImpl_none_eager, if_pos rfl, if_neg Bool.false_ne_true,
        hsub]
    | none =>
      rw [rImpl_none_lazy, rImpl_none_lazy]
      simp only [rImpl_none_eager, Bool.false_eq_true, ↓reduceIte, hsub]

/-- **With `b = false` the hybrid does not read `ρ'`:** the oracles for `ρ₁` and `ρ₂` coincide. -/
theorem rImpl_false_coins (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (n : ℕ) (pk sk : List Bool) (ρ ρ₁ ρ₂ : samp.Coins n)
    (ce : Option (S.enc.Coins n)) :
    rImpl S atk false samp pl hl hist n pk sk ρ ρ₁ ce =
      rImpl S atk false samp pl hl hist n pk sk ρ ρ₂ ce := by
  funext i x s
  match i, s with
  | 0, s => rfl
  | 1, some (y, a) => rfl
  | 1, none => cases ce <;> rfl

/-! ### The history oracle -/

/-- **The ideal experiment's oracle** on T2's lengths (`pl(n)`-bit queries, `hl(n)`-bit answers):
on the parameter `a` (the first one asked, recorded) it answers `h(M(a; ρ))`. -/
noncomputable def histImpl (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool)
    (n : ℕ) (ρ : samp.Coins n) :
    QueryImpl (bitSpecAt (fun _ : Fin 1 => pl) (fun _ => hl) n) (Option (Fin (pl.eval n) → Bool))
      unifSpec :=
  fun _ a s => .pure (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ),
    some (s.getD a))

/-- `histImpl … ρ i a s = pure (h(M(s.getD a; ρ)), some (s.getD a))`. -/
theorem histImpl_eq (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool) (n : ℕ)
    (ρ : samp.Coins n) (i : Fin 1) (a : Fin (pl.eval n) → Bool)
    (s : Option (Fin (pl.eval n) → Bool)) :
    histImpl S samp pl hl hist n ρ i a s =
      .pure (histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ),
        some (s.getD a)) := rfl

/-- **With an empty history the oracle ignores the sampler's coins:** if `hl(n) = 0`, then
`histImpl … ρ = histImpl … ρ'`. -/
theorem histImpl_coins (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool) (n : ℕ)
    (ρ ρ' : samp.Coins n) (h : hl.eval n = 0) :
    histImpl S samp pl hl hist n ρ = histImpl S samp pl hl hist n ρ' := by
  funext i a s
  rw [histImpl_eq, histImpl_eq]
  have hv : histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ) =
      histWith hist (hl.eval n) (drawWith samp (S.msgLen.eval n) n (s.getD a) ρ') := by
    funext j
    have := j.isLt
    omega
  rw [hv]

/-! ### Blocks of fixed-length strings -/

/-- Block `i` of `k` bits of a string: `chunkAt k i w = (w.drop (i·k)).take k`. -/
def chunkAt (k i : ℕ) (w : List Bool) : List Bool := (w.drop (i * k)).take k

/-- `chunkAt k i w = (w.drop (i·k)).take k`. -/
theorem chunkAt_eq (k i : ℕ) (w : List Bool) : chunkAt k i w = (w.drop (i * k)).take k := rfl

/-- **Block `i` of a string of `r` blocks of `k` bits and a tail:**
`⟦j ↦ w (castAdd sl (finProdFinEquiv (i, j)))⟧ = chunkAt k i ⟦w⟧`. -/
theorem ofFn_block {r k sl : ℕ} (w : Fin (r * k + sl) → Bool) (i : Fin r) :
    List.ofFn (fun j : Fin k => w (Fin.castAdd sl (finProdFinEquiv (i, j)))) =
      chunkAt k i (List.ofFn w) := by
  have hle : (i : ℕ) * k + k ≤ r * k := by
    have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at this
    exact this
  rw [chunkAt_eq]
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine congrArg w (Fin.ext ?_)
    rw [Fin.coe_castAdd, finProdFinEquiv_apply_val]
    show j + k * i = i * k + j
    rw [Nat.mul_comm]
    omega

/-- **The tail of a string:** `⟦j ↦ w (natAdd k j)⟧ = ⟦w⟧.drop k`. -/
theorem ofFn_natAdd_eq_drop {k sl : ℕ} (w : Fin (k + sl) → Bool) :
    List.ofFn (fun j : Fin sl => w (Fin.natAdd k j)) = (List.ofFn w).drop k := by
  rw [List.ofFn_add, List.drop_left' List.length_ofFn]

/-- A list of `r` values is a map over `List.range r`: if `f i = g i` for `i < r`, then
`List.ofFn f = (List.range r).map g`. -/
theorem ofFn_eq_map_range {α : Type} {r : ℕ} (f : Fin r → α) (g : ℕ → α)
    (h : ∀ i : Fin r, f i = g i) : List.ofFn f = (List.range r).map g := by
  refine List.ext_getElem (by rw [List.length_ofFn, List.length_map, List.length_range])
    fun i h₁ h₂ => ?_
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  exact h _

/-- Comparing strings is comparing their lists:
`decide (o.map ofFn = some ⟦c⟧) = decide (o = some c)`. -/
theorem decide_map_ofFn {k : ℕ} (o : Option (Fin k → Bool)) (c : Fin k → Bool) :
    decide (o.map List.ofFn = some (List.ofFn c)) = decide (o = some c) := by
  cases o with
  | none => simp
  | some c' => simp [List.ofFn_inj]

/-! ### The experiments' outputs as strings -/

/-- **An entry `d_i` as a string:** `COPY` (`true` followed by `msgLen(n) + 1` falses) if `copy`,
and `false` followed by `Dec`'s answer on the ciphertext `c` otherwise. -/
def entryL (n : ℕ) (sk : List Bool) (copy : Bool) (c : List Bool) : List Bool :=
  if copy then true :: List.replicate (S.msgLen.eval n + 1) false
  else false :: List.ofFn (FixedLengthScheme.decAnswer
    (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk c))))

/-- `entryL S n sk copy c = if copy then true :: 0^{msgLen + 1} else false :: ⟦decAnswer (Dec_sk c)⟧`.
-/
theorem entryL_eq (n : ℕ) (sk : List Bool) (copy : Bool) (c : List Bool) :
    entryL S n sk copy c = if copy then true :: List.replicate (S.msgLen.eval n + 1) false
      else false :: List.ofFn (FixedLengthScheme.decAnswer
        (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk c)))) := rfl

/-- **The real experiment's output** `(a, m, (d_i)_i, σ)` as a string, from the adversary's output
string `w` (`r` ciphertexts, then `σ`) and the final state `s`: `a` is the recorded parameter
(`0` if none), `m = M(a; ρ)`, and `d_i` is `COPY` exactly when ciphertext `i` is the recorded
challenge. -/
def realView (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    List Bool :=
  List.ofFn ((s.map Prod.snd).getD (zeroBits _)) ++
    List.ofFn (drawWith samp (S.msgLen.eval n) n ((s.map Prod.snd).getD (zeroBits _)) ρ) ++
    ((List.range r).map fun i => entryL S n sk
      (decide ((s.map Prod.fst).map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
      (chunkAt (S.ctLen.eval n) i w)).flatten ++
    w.drop (r * S.ctLen.eval n)

/-- `realView … w s = ⟦a⟧ ++ ⟦M(a; ρ)⟧ ++ (d_0 ++ ⋯ ++ d_{r-1}) ++ σ` as defined. -/
theorem realView_eq (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (s : Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (pl.eval n) → Bool))) :
    realView S samp pl n r sk ρ w s =
      List.ofFn ((s.map Prod.snd).getD (zeroBits _)) ++
        List.ofFn (drawWith samp (S.msgLen.eval n) n ((s.map Prod.snd).getD (zeroBits _)) ρ) ++
        ((List.range r).map fun i => entryL S n sk
          (decide ((s.map Prod.fst).map List.ofFn = some (chunkAt (S.ctLen.eval n) i w)))
          (chunkAt (S.ctLen.eval n) i w)).flatten ++
        w.drop (r * S.ctLen.eval n) := rfl

/-- **The ideal experiment's output** `(a, m, (d_i)_i, σ)` as a string, from the simulator's output
string `w` (`r` entries of a flag and a ciphertext, then `σ`) and the history oracle's state `sa`:
`a` is the recorded parameter (`0` if none), `m = M(a; ρ)`, and `d_i` is `COPY` exactly when entry
`i` is flagged. -/
def idealView (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (sa : Option (Fin (pl.eval n) → Bool)) : List Bool :=
  List.ofFn (sa.getD (zeroBits _)) ++
    List.ofFn (drawWith samp (S.msgLen.eval n) n (sa.getD (zeroBits _)) ρ) ++
    ((List.range r).map fun i => entryL S n sk
      ((chunkAt (S.ctLen.eval n + 1) i w).headD false)
      (chunkAt (S.ctLen.eval n + 1) i w).tail).flatten ++
    w.drop (r * (S.ctLen.eval n + 1))

/-- `idealView … w sa = ⟦a⟧ ++ ⟦M(a; ρ)⟧ ++ (d_0 ++ ⋯ ++ d_{r-1}) ++ σ` as defined. -/
theorem idealView_eq (samp : NUPPT) (pl : PolyExpr) (n r : ℕ) (sk : List Bool) (ρ : samp.Coins n)
    (w : List Bool) (sa : Option (Fin (pl.eval n) → Bool)) :
    idealView S samp pl n r sk ρ w sa =
      List.ofFn (sa.getD (zeroBits _)) ++
        List.ofFn (drawWith samp (S.msgLen.eval n) n (sa.getD (zeroBits _)) ρ) ++
        ((List.range r).map fun i => entryL S n sk
          ((chunkAt (S.ctLen.eval n + 1) i w).headD false)
          (chunkAt (S.ctLen.eval n + 1) i w).tail).flatten ++
        w.drop (r * (S.ctLen.eval n + 1)) := rfl

/-! ### The acceptance rates of the experiments -/

/-- **The real experiment's acceptance rate** for the sampler `samp` (parameter length `pl`,
history `hist` of length `hl`), the adversary `A` (budget `q`, `r` ciphertexts and an `sl`-bit `σ`)
and the distinguisher `X`, on T2's lengths: over the keys and the coins of the sampler, `A` and
`X`, the probability that `X` accepts `realView` of `A`'s run against `rImpl … false … ρ ρ none`. -/
noncomputable def realAcc (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) : ℝ :=
  ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
  ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
  ProbComp.expect (ProbComp.sample (A.Coins n)) fun rA =>
  ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
  ProbComp.expect (simulate (rImpl S atk false samp pl hl hist n (pairFstD (S.gen.runAt n [] rg))
      (pairSndD (S.gen.runAt n [] rg)) ρ ρ none)
    (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
      (r * S.ctLen.eval n + sl)) n q (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
    if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
      (List.ofFn p.1) p.2) rX = true then 1 else 0

/-- `realAcc … = 𝔼_{rg, ρ, rA, rX} 𝔼[1{X accepts realView}]` over `A`'s run against `rImpl`. -/
theorem realAcc_eq (atk : Attack) (samp : NUPPT) (pl hl : PolyExpr)
    (hist : List Bool → List Bool) (A : NUPPT) (q r sl : ℕ) (X : NUPPT) (n : ℕ) :
    realAcc S atk samp pl hl hist A q r sl X n =
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
      ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
      ProbComp.expect (ProbComp.sample (A.Coins n)) fun rA =>
      ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
      ProbComp.expect (simulate (rImpl S atk false samp pl hl hist n
          (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ ρ none)
        (A.toCompOn (bitCodec (fun i => (snmDin S pl i).eval n) (fun i => (snmDout S hl i).eval n)
          (r * S.ctLen.eval n + sl)) n q (pairFstD (S.gen.runAt n [] rg)) rA) none) fun p =>
        if X.distinguisherL n (realView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
          (List.ofFn p.1) p.2) rX = true then 1 else 0 := rfl

/-- **The ideal experiment's acceptance rate** for the sampler `samp` (as in `realAcc`), the
simulator `Sim` (budget `1`, `r` entries and an `sl`-bit `σ`) and the distinguisher `X`: over the
keys and the coins of the sampler, `Sim` and `X`, the probability that `X` accepts `idealView` of
`Sim`'s run against `histImpl … ρ`. -/
noncomputable def idealAcc (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool)
    (Sim : NUPPT) (r sl : ℕ) (X : NUPPT) (n : ℕ) : ℝ :=
  ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
  ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
  ProbComp.expect (ProbComp.sample (Sim.Coins n)) fun rS =>
  ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
  ProbComp.expect (simulate (histImpl S samp pl hl hist n ρ)
    (Sim.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
      (r * (S.ctLen.eval n + 1) + sl)) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none) fun p =>
    if X.distinguisherL n (idealView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
      (List.ofFn p.1) p.2) rX = true then 1 else 0

/-- `idealAcc … = 𝔼_{rg, ρ, rS, rX} 𝔼[1{X accepts idealView}]` over `Sim`'s run against
`histImpl`. -/
theorem idealAcc_eq (samp : NUPPT) (pl hl : PolyExpr) (hist : List Bool → List Bool)
    (Sim : NUPPT) (r sl : ℕ) (X : NUPPT) (n : ℕ) :
    idealAcc S samp pl hl hist Sim r sl X n =
      ProbComp.expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
      ProbComp.expect (ProbComp.sample (samp.Coins n)) fun ρ =>
      ProbComp.expect (ProbComp.sample (Sim.Coins n)) fun rS =>
      ProbComp.expect (ProbComp.sample (X.Coins n)) fun rX =>
      ProbComp.expect (simulate (histImpl S samp pl hl hist n ρ)
        (Sim.toCompOn (bitCodec (fun _ => pl.eval n) (fun _ => hl.eval n)
          (r * (S.ctLen.eval n + 1) + sl)) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none) fun p =>
        if X.distinguisherL n (idealView S samp pl n r (pairSndD (S.gen.runAt n [] rg)) ρ
          (List.ofFn p.1) p.2) rX = true then 1 else 0 := rfl

end TCSlib.Cryptography.Composability.NMSim
