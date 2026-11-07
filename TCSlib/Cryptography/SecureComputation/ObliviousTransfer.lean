/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Defs
import TCSlib.Cryptography.Asymptotic.Collections

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer from trapdoor permutations (statement phase)

[PS10, Protocol 160.4]: for a collection of trapdoor permutations `{f_i}` with a hard-core
predicate `h`,
- Alice (sender, input `a₁, a₂`) runs `(i, t) ← Gen(1^n)` and sends `i`;
- Bob (receiver, input `b`) samples `x`, sets `y_b = f_i(x)` and `y_{1−b}` a random element, and
  sends `(y₁, y₂)`;
- Alice sends `z_j = h(f_i^{-1}(y_j)) ⊕ a_j` for `j = 1, 2`;
- Bob outputs `h(x) ⊕ z_b`.

[PS10, Proposition 161.5]: the protocol is an honest-but-curious one-out-of-two oblivious transfer
(Definition 155.1 for `otFunctionality`).

**On the ch. 2–4 layer.** The collection is a `TrapdoorCollection`, used as Algorithm 104.3 uses it:
`Gen`, the domain sampler, the evaluator `eval`, and the trapdoor inverter run on the all-`true`
coin string. The hard-core predicate is evaluated by a polynomial-time `H`, specified by
`H ⟨i, encD i x⟩ = [h i x]` on canonical encodings. Canonical decoding extends this specification
to every string decoding to `x` (`Collection.apply_of_decD`). The evaluator and its polynomial
cost are passed explicitly, so this module needs only `Asymptotic/Collections`.

**Deviations and source notes.**
- **Five messages.** The ch. 2–4 model (D8) reads a party's output as its next-message function
  on its complete history, so the last mover's last message is its output. With the source's
  three messages Alice would move last and output `(z₁, z₂)`, not `⊥`. Two empty messages are
  added (Bob, then Alice), so Alice's output is `[]` (the empty `⊥` of `otFunctionality`) and
  Bob's is computed on his complete history `[i, (z₁, z₂), []]`.
- **The source's typo:** Alice sends `(z₁, z₂)`, not `(z₁, …, z₄)` (inventory Prot-160.4).
- **Random elements, not random strings.** The source's `y_j ← {0,1}^n` becomes the collection's
  domain sampler, as in Algorithm 104.3. `y_b = f_i(x) = encD (perm x)` is a canonical encoding.
  `y_{1−b}` must be one too, or Alice tells the two apart and learns `b`. Canonical decoding and
  the sampler contract guarantee this (`Collection.sample_eq_encD`, stated here as the theorem
  `SamplerCanonical`).
- **An enhanced hard-core predicate** (gate 03b review; ruling of 2026-11-05). `y_{1−b}` is a
  raw sample, and Bob's view holds the coins that produced it. If the sampler computes its
  output as `f_i(u)` from a uniform `u`, those coins reveal `u = f_i⁻¹(y_{1−b})` and so
  `a_{1−b}`; the hard-core property of [PS10] (from `⟨i, f_i(u)⟩` alone) does not exclude this,
  and the proposition is not provable under it. Proposition 161.5 therefore assumes that `h` is
  **enhanced** hard-core (`EnhancedHardCore`): unpredictable on the preimage of a sampled element
  even given the sampler's coins. This is the standard repair of this protocol (enhanced trapdoor
  permutations, [Gol04, Appendix C.1]).

## Main definitions

* `SecureComputation.otSender`, `otReceiver`, `otProtocol`: Protocol 160.4.
* `SecureComputation.otSimA`, `otSimB`: the simulators of Proposition 161.5.
* `SecureComputation.EnhancedHardCore`: an enhanced hard-core predicate.

## Main results

* The `otMask_eq`, `otKnown_eq`, `otRaw_eq`, simulator-function equations and explicit
  `otSender`, `otReceiver`, `otProtocol` field equations expose the protocol's computations.
* `SecureComputation.enhancedHardCore_iff`: the enhanced prediction bound.
* `SecureComputation.otSimA_coins`, `otSimA_uniform`, `runAt_otSimA`: Alice's simulator contract.
* `SecureComputation.otSimB_coins`, `otSimB_uniform`, `runAt_otSimB`: Bob's simulator contract.
* `SecureComputation.SamplerCanonical`: the sampler outputs canonical encodings.
* `SecureComputation.otProtocol_outV`, `otProtocol_outP`: correctness: Bob outputs `a_b` and
  Alice outputs `⊥ = []`, on every coin string.
* `SecureComputation.otProtocol_polyTime` (the parties run in polynomial time, stated; a `sorry`
  under its sketch).
* `SecureComputation.otProtocol_simulators` (Prop 161.5 with the explicit simulators, stated; a
  `sorry` under its sketch), and `otProtocol_hbcSecure` (Prop 161.5, proved from the two).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Protocol 160.4 and Proposition 161.5 (book pp. 160–162).
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
  2004, Appendix C.1 (enhanced trapdoor permutations).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection)

/-! ### The protocol -/

/-- Alice's mask `z_j = h(f_i^{-1}(y_j)) ⊕ a_j`: the trapdoor inverter on `⟨t, y_j⟩` (all-`true`
coins, as in Algorithm 104.3), the predicate evaluator `H` on `⟨i, ·⟩`, then XOR with `[a_j]`. -/
def otMask (H : List Bool → List Bool) (n : ℕ) (i t yj : List Bool) (a : Bool) : List Bool :=
  List.zipWith xor (H (pairEncode i (T.inv.runAtL n (pairEncode t yj)
    (List.replicate (T.inv.coins.eval n) true)))) [a]

/-- Alice's mask XORs her bit with the predicate evaluated on the trapdoor inversion,
using the all-`true` inverter tape. -/
theorem otMask_eq (H : List Bool → List Bool) (n : ℕ) (i t yj : List Bool) (a : Bool) :
    otMask T H n i t yj a =
      List.zipWith xor (H (pairEncode i (T.inv.runAtL n (pairEncode t yj)
        (List.replicate (T.inv.coins.eval n) true)))) [a] := rfl

/-- **Alice, the sender** [PS10, Protocol 160.4], on common input `1^n`, input `⟨a₁, a₂⟩` and the
coins of `Gen`: first `i`, then `⟨z₁, z₂⟩` on Bob's `⟨y₁, y₂⟩`, then `[]`. -/
def otSender (H : List Bool → List Bool) : Strategy where
  next x y r hist :=
    if hist.length = 0 then pairFstD (T.gen.runAtL x.length [] r)
    else if hist.length = 1 then
      pairEncode
        (otMask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
          (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD (hist.headD [])) (y.getD 0 false))
        (otMask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
          (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD (hist.headD [])) (y.getD 1 false))
    else []
  coins := T.gen.coins

/-- Alice uses the index generator's coin polynomial. -/
theorem otSender_coins (H : List Bool → List Bool) : (otSender T H).coins = T.gen.coins := rfl

/-- Alice sends the generated index initially, both masks after one received message,
and the empty word on every later history. -/
theorem otSender_next (H : List Bool → List Bool) (x y r : List Bool)
    (hist : List (List Bool)) :
    (otSender T H).next x y r hist =
      if hist.length = 0 then pairFstD (T.gen.runAtL x.length [] r)
      else if hist.length = 1 then
        pairEncode
          (otMask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
            (pairSndD (T.gen.runAtL x.length [] r)) (pairFstD (hist.headD [])) (y.getD 0 false))
          (otMask T H x.length (pairFstD (T.gen.runAtL x.length [] r))
            (pairSndD (T.gen.runAtL x.length [] r)) (pairSndD (hist.headD [])) (y.getD 1 false))
      else [] := rfl

/-- Bob's sampled element `w` (decoding to `x`), from the first half of his coins. -/
def otKnown (n : ℕ) (i r : List Bool) : List Bool :=
  T.sample.runAtL n i (r.take (T.sample.coins.eval n))

/-- Bob's known element is the sample obtained from the first sampler-sized coin block. -/
theorem otKnown_eq (n : ℕ) (i r : List Bool) :
    otKnown T n i r = T.sample.runAtL n i (r.take (T.sample.coins.eval n)) := rfl

/-- Bob's raw element `y_{1−b}`, from the second half of his coins. -/
def otRaw (n : ℕ) (i r : List Bool) : List Bool :=
  T.sample.runAtL n i (r.drop (T.sample.coins.eval n))

/-- Bob's raw element is the sample obtained after dropping the first sampler-sized block. -/
theorem otRaw_eq (n : ℕ) (i r : List Bool) :
    otRaw T n i r = T.sample.runAtL n i (r.drop (T.sample.coins.eval n)) := rfl

/-- **Bob, the receiver** [PS10, Protocol 160.4], on common input `1^n`, input `[b]` and two
blocks of sampler coins: on `[i]`, the pair with `y_b = f_i(x)` (by `eval`) and `y_{1−b}` the raw
element; on `[i, z]`, `[]`; and on his complete history, `h(x) ⊕ z_b`. -/
def otReceiver (H : List Bool → List Bool) : Strategy where
  next x z r hist :=
    if hist.length = 1 then
      if z.headD false then
        pairEncode (otRaw T x.length (hist.headD []) r)
          (T.eval (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
      else
        pairEncode (T.eval (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
          (otRaw T x.length (hist.headD []) r)
    else if hist.length = 2 then []
    else List.zipWith xor (H (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
      (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 []))
  coins := .add T.sample.coins T.sample.coins

/-- Bob uses two consecutive blocks of sampler coins. -/
theorem otReceiver_coins (H : List Bool → List Bool) :
    (otReceiver T H).coins = .add T.sample.coins T.sample.coins := rfl

/-- Bob sends the choice-ordered element pair after one message, an empty filler after two,
and the XOR of the predicate word and selected mask on every other history. -/
theorem otReceiver_next (H : List Bool → List Bool) (x z r : List Bool)
    (hist : List (List Bool)) :
    (otReceiver T H).next x z r hist =
      if hist.length = 1 then
        if z.headD false then
          pairEncode (otRaw T x.length (hist.headD []) r)
            (T.eval (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
        else
          pairEncode (T.eval (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
            (otRaw T x.length (hist.headD []) r)
      else if hist.length = 2 then []
      else List.zipWith xor (H (pairEncode (hist.headD []) (otKnown T x.length (hist.headD []) r)))
        (if z.headD false then pairSndD (hist.getD 1 []) else pairFstD (hist.getD 1 [])) := rfl

/-- **Protocol 160.4** [PS10], with five messages, Alice first. -/
def otProtocol (H : List Bool → List Bool) : Protocol where
  P := otSender T H
  V := otReceiver T H
  rounds := .const 5
  verifierFirst := false

/-- Alice, the OT sender, is the protocol's prover-side strategy. -/
theorem otProtocol_P (H : List Bool → List Bool) : (otProtocol T H).P = otSender T H := rfl

/-- Bob, the OT receiver, is the protocol's verifier-side strategy. -/
theorem otProtocol_V (H : List Bool → List Bool) : (otProtocol T H).V = otReceiver T H := rfl

/-- The OT protocol makes five moves. -/
theorem otProtocol_rounds (H : List Bool → List Bool) : (otProtocol T H).rounds = .const 5 := rfl

/-- The OT protocol starts with Alice, rather than the verifier-side party. -/
theorem otProtocol_verifierFirst (H : List Bool → List Bool) :
    (otProtocol T H).verifierFirst = false := rfl

/-- **The sampler outputs canonical encodings** [PS10, Definition 41.1 (2)]: at every generated
index, every output of the domain sampler is `encD i x` for some `x ∈ D_i`
(`Collection.sample_eq_encD`, from the sampler contract and canonical decoding). -/
theorem SamplerCanonical :
    ∀ n (r : T.gen.Coins n) (s : T.sample.Coins n), ∃ x,
      T.sample.runAt n (T.index n r) s = T.encD (T.index n r) x :=
  T.toCollection.sample_eq_encD

/-- **An enhanced hard-core predicate** [Gol04, Appendix C.1] (a declared strengthening of
[PS10, Proposition 161.5]'s hypothesis; see the module docstring): for every non-uniform PPT `A`,
predicting `h(f_i⁻¹(y))` for a sampled element `y`, given the index `i` and **the sampler's
coins** that produced `y`, succeeds with probability at most `½` plus a negligible amount, on
average over the generated indices. The element `y` is read through the decoder (a sampled
string decodes, `Collection.sample_spec`), and its preimage is `perm⁻¹` of it (`f_perm`). -/
def EnhancedHardCore (h : ∀ i, T.D i → Bool) : Prop :=
  ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    uexp (fun r : T.gen.Coins n =>
      uprob fun z : T.sample.Coins n × A.Coins n =>
        A.distinguisherL n (pairEncode (T.index n r) (List.ofFn z.1)) z.2 =
          h (T.index n r) ((T.perm (T.index n r)).symm
            ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) z.1)).getD default)))
      ≤ 1 / 2 + ε n

/-- Enhanced hard-core security bounds prediction of a sampled element's preimage bit by
one half plus a negligible function, even when the predictor receives the sampler's coins. -/
theorem enhancedHardCore_iff (h : ∀ i, T.D i → Bool) :
    EnhancedHardCore T h ↔
      ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
        uexp (fun r : T.gen.Coins n =>
          uprob fun z : T.sample.Coins n × A.Coins n =>
            A.distinguisherL n (pairEncode (T.index n r) (List.ofFn z.1)) z.2 =
              h (T.index n r) ((T.perm (T.index n r)).symm
                ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) z.1)).getD default)))
          ≤ 1 / 2 + ε n := Iff.rfl

/-! ### Correctness -/

section Correctness

variable {h : ∀ i, T.D i → Bool} (H : List Bool → List Bool)
  (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x])

include henc in
/-- **Bob outputs `a_b`** on every coin string (the output clause of Proposition 161.5).

**Proof sketch.**
1. Unfold the five moves. Bob's known element `w` is the sampler on his first coin block, and it
   decodes to some `x` with `eval ⟨i, w⟩ = encD(perm x)` (`sample_spec`, `f_perm`).
2. So `y_b = encD(perm x)`, and Alice's trapdoor inverter maps it back to an encoding of `x`
   (`inv_spec`). Canonical decoding extends the supplied specification of `H` to all decodable
   strings (`Collection.apply_of_decD`), so `H` gives `[h(x)]` on both sides.
3. Bob outputs `h(x) ⊕ z_b = h(x) ⊕ h(x) ⊕ a_b = a_b`, by cases on `b` and on `h(x)`. -/
theorem otProtocol_outV (x : List Bool) (a : Fin 2 → Bool) (b : Fin 1 → Bool)
    (r : (otProtocol T H).ExecCoins (otProtocol T H).P x) :
    (otProtocol T H).outV (otProtocol T H).P x (List.ofFn a) (List.ofFn b) r =
      [a (if b 0 then 1 else 0)] := by
  have hspec : ∀ i w (xx : T.D i),
      T.decD i w = some xx → H (pairEncode i w) = [h i xx] :=
    fun _ _ _ hw =>
      T.toCollection.apply_of_decD (v := fun i xx => [h i xx]) henc hw
  obtain ⟨rA₀, rB₀⟩ := r
  have hA : (otSender T H).coinLen x.length = T.gen.coinLen x.length :=
    (Strategy.coinLen_eq (otSender T H) x.length).trans (T.gen.coinLen_eq x.length).symm
  have hB : (otReceiver T H).coinLen x.length =
      T.sample.coinLen x.length + T.sample.coinLen x.length :=
    (Strategy.coinLen_eq (otReceiver T H) x.length).trans
      ((PolyExpr.eval_add T.sample.coins T.sample.coins x.length).trans
        (congrArg₂ Nat.add (T.sample.coinLen_eq x.length).symm
          (T.sample.coinLen_eq x.length).symm))
  let rA : T.gen.Coins x.length := fun j => rA₀ (Fin.cast hA.symm j)
  let rB : Fin (T.sample.coinLen x.length + T.sample.coinLen x.length) → Bool :=
    fun j => rB₀ (Fin.cast hB.symm j)
  have hAr : List.ofFn rA₀ = List.ofFn rA := List.ofFn_congr hA rA₀
  have hBr : List.ofFn rB₀ = List.ofFn rB := List.ofFn_congr hB rB₀
  simp [Protocol.outV_eq, Protocol.transcriptWith_eq, otProtocol, exec_succ, exec_zero,
    otSender, otReceiver]
  rw [hAr, hBr]
  have hg : T.gen.runAtL x.length [] (List.ofFn fun i => rA i) =
      T.gen.runAt x.length [] rA :=
    (T.gen.runAt_eq x.length [] rA).symm
  erw [hg]
  -- Bob's first coin block, typed
  let s1 : T.sample.Coins x.length := fun j => rB ⟨j.1,
    show (j : ℕ) < T.sample.coinLen x.length + T.sample.coinLen x.length from
      Nat.lt_of_lt_of_le j.2 (Nat.le_add_right _ _)⟩
  have hs1 : (List.ofFn fun i => rB i).take (T.sample.coins.eval x.length) = List.ofFn s1 := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_ofFn]
      rw [← T.sample.coinLen_eq x.length]
      omega
    · intro j h₁ h₂
      simp only [List.getElem_take, List.getElem_ofFn]
      rfl
  have hknown : otKnown T x.length (pairFstD (T.gen.runAt x.length [] rA))
      (List.ofFn fun i => rB i) =
      T.sample.runAt x.length (pairFstD (T.gen.runAt x.length [] rA)) s1 := by
    rw [otKnown, hs1]
    exact (T.sample.runAt_eq x.length _ s1).symm
  obtain ⟨xx, hdec, heval⟩ := T.sample_spec x.length rA s1
  have hyb : T.eval (pairEncode (pairFstD (T.gen.runAt x.length [] rA))
      (otKnown T x.length (pairFstD (T.gen.runAt x.length [] rA)) (List.ofFn fun i => rB i))) =
      T.encD _ (T.perm _ xx) := by
    rw [hknown, heval, T.f_perm]
  have hinv := T.inv_spec x.length rA (T.perm _ xx) (fun _ => true)
  rw [Equiv.symm_apply_apply] at hinv
  have hHinv : H (pairEncode (pairFstD (T.gen.runAt x.length [] rA))
      (T.inv.runAtL x.length
        (pairEncode (pairSndD (T.gen.runAt x.length [] rA)) (T.encD _ (T.perm _ xx)))
        (List.replicate (T.inv.coins.eval x.length) true))) = [h _ xx] := by
    rw [← T.inv.coinLen_eq x.length, ← List.ofFn_const, ← NUPPT.runAt_eq]
    exact hspec _ _ _ hinv
  have hHw : H (pairEncode (pairFstD (T.gen.runAt x.length [] rA))
      (otKnown T x.length (pairFstD (T.gen.runAt x.length [] rA)) (List.ofFn fun i => rB i))) =
      [h _ xx] := by
    rw [hknown]
    exact hspec _ _ _ hdec
  cases hb : b 0
  · simp only [Bool.false_eq_true, if_false, pairFstD_pairEncode, pairSndD_pairEncode]
    erw [hyb]
    simp only [otMask]
    erw [hHinv, hHw]
    cases h _ xx <;> simp
  · simp only [if_true, pairFstD_pairEncode, pairSndD_pairEncode]
    erw [hyb]
    simp only [otMask]
    erw [hHinv, hHw]
    cases h _ xx <;> simp

/-- **Alice outputs `⊥ = []`** on every coin string. -/
theorem otProtocol_outP (x : List Bool) (a : Fin 2 → Bool) (b : Fin 1 → Bool)
    (r : (otProtocol T H).ExecCoins (otProtocol T H).P x) :
    (otProtocol T H).outP x (List.ofFn a) (List.ofFn b) r = [] := by
  obtain ⟨rA, rB⟩ := r
  simp [Protocol.outP_eq, Protocol.transcriptWith_eq, otProtocol, exec_succ, exec_zero,
    otSender, otReceiver]

end Correctness

/-! ### The simulators -/

/-- The coin segment of length `q(n)` after the first `p(n)` coins of a raw layout. -/
def coinSeg (p q : PolyExpr) (z : List Bool) : List Bool :=
  ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take (q.eval (NUPPT.inParam z).length)

/-- The coin segment drops the first `p(|parameter|)` bits and takes the next
`q(|parameter|)` bits of the raw tape. -/
theorem coinSeg_eq (p q : PolyExpr) (z : List Bool) :
    coinSeg p q z =
      ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take
        (q.eval (NUPPT.inParam z).length) := rfl

/-- A coin segment is polynomial-time (`polyTimeComputable_pairDropPoly`,
`polyTimeComputable_pairTakePoly`). -/
theorem polyTimeComputable_coinSeg (p q : PolyExpr) : PolyTimeComputable (coinSeg p q) := by
  have h₁ := (polyTimeComputable_pairDropPoly p).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)
  have h₂ := (polyTimeComputable_pairTakePoly q).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode h₁)
  refine (congrArg PolyTimeComputable (?_ : coinSeg p q = _)).mpr h₂
  funext z
  simp only [coinSeg, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- The index `i` a simulator generates from its first `coins_Gen(n)` coins. -/
def simIdx (z : List Bool) : List Bool :=
  pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
    (coinSeg (.const 0) T.gen.coins z)))

/-- The simulated index is the first component of the generator's output on its designated
coin segment, with empty argument and advice. -/
theorem simIdx_eq (z : List Bool) :
    simIdx T z = pairFstD (T.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
      (coinSeg (.const 0) T.gen.coins z))) := rfl

/-- The simulated index is polynomial-time. -/
theorem polyTimeComputable_simIdx : PolyTimeComputable (simIdx T) := by
  have h := polyTimeComputable_pairFstD.comp (T.gen.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (polyTimeComputable_const []) (polyTimeComputable_const [])
      (polyTimeComputable_coinSeg (.const 0) T.gen.coins)))
  refine (congrArg PolyTimeComputable (?_ : simIdx T = _)).mpr h
  funext z
  simp only [simIdx, Function.comp_apply]

/-- A sampled element at the simulated index, from the sampler-coin segment after `p(n)` coins. -/
def simSample (p : PolyExpr) (z : List Bool) : List Bool :=
  T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIdx T z) [] (coinSeg p T.sample.coins z))

/-- A simulated sample runs the sampler at the simulated index on its designated coin
segment, with empty advice. -/
theorem simSample_eq (p : PolyExpr) (z : List Bool) :
    simSample T p z =
      T.sample.output (NUPPT.layout (NUPPT.inParam z) (simIdx T z) []
        (coinSeg p T.sample.coins z)) := rfl

/-- A simulated sample is polynomial-time. -/
theorem polyTimeComputable_simSample (p : PolyExpr) : PolyTimeComputable (simSample T p) := by
  have h := T.sample.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
      (polyTimeComputable_simIdx T) (polyTimeComputable_const [])
      (polyTimeComputable_coinSeg p T.sample.coins))
  refine (congrArg PolyTimeComputable (?_ : simSample T p = _)).mpr h
  funext z
  simp only [simSample, Function.comp_apply]

/-- **`S_A`** on `⟨1^n, ⟨⟨a₁, a₂⟩, ⊥⟩⟩`: Alice's view, with `Gen`'s coins as her tape and two
fresh sampled elements as Bob's message: `⟨⟨1^n, ⟨a₁, a₂⟩⟩, ⟨r_Gen, [⟨y₁, y₂⟩, []]⟩⟩`. -/
def otSimAFun (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
    (pairEncode (coinSeg (.const 0) T.gen.coins z)
      (pairEncode (pairEncode (simSample T T.gen.coins z)
          (simSample T (.add T.gen.coins T.sample.coins) z))
        (pairEncode [] [])))

/-- Alice's simulator word encodes her parameter, input and generator coins, followed by
the two simulated samples and an empty received message. -/
theorem otSimAFun_eq (z : List Bool) :
    otSimAFun T z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
        (pairEncode (coinSeg (.const 0) T.gen.coins z)
          (pairEncode (pairEncode (simSample T T.gen.coins z)
              (simSample T (.add T.gen.coins T.sample.coins) z))
            (pairEncode [] []))) := rfl

/-- `S_A` is polynomial-time. -/
theorem polyTimeComputable_otSimAFun : PolyTimeComputable (otSimAFun T) := by
  have h := (NUPPT.polyTimeComputable_inParam.pairEncode
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)).pairEncode
    ((polyTimeComputable_coinSeg (.const 0) T.gen.coins).pairEncode
      (((polyTimeComputable_simSample T T.gen.coins).pairEncode
          (polyTimeComputable_simSample T (.add T.gen.coins T.sample.coins))).pairEncode
        (polyTimeComputable_const (pairEncode [] []))))
  refine (congrArg PolyTimeComputable (?_ : otSimAFun T = _)).mpr h
  funext z
  simp only [otSimAFun, Function.comp_apply]

/-- **The simulator `S_A`** of Proposition 161.5: `Gen`'s coins and two blocks of sampler coins. -/
noncomputable def otSimA : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_otSimAFun T)
    (.add T.gen.coins (.add T.sample.coins T.sample.coins))

/-- Alice's simulator uses generator coins followed by two sampler blocks. -/
theorem otSimA_coins :
    (otSimA T).coins = .add T.gen.coins (.add T.sample.coins T.sample.coins) :=
  NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_otSimAFun T) _

/-- Alice's simulator is uniform. -/
theorem otSimA_uniform : (otSimA T).Uniform :=
  NUPPT.ofPolyTimeUniform_uniform (polyTimeComputable_otSimAFun T) _

/-- Alice's simulator at parameter `n` computes its view word on the unary-parameter layout,
with the supplied argument and tape and empty advice. -/
theorem runAt_otSimA (n : ℕ) (y : List Bool) (r : (otSimA T).Coins n) :
    (otSimA T).runAt n y r =
      otSimAFun T (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) := by
  rw [NUPPT.runAt_eq]
  unfold otSimA
  rw [NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput_eq, NUPPT.layout_eq]

/-- `S_B`'s mask `z_b = h(x) ⊕ a_b`, with `x` its first sampled element and `[a_b]` the second
part of its argument. -/
def otSimZb (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (simIdx T z) (simSample T T.gen.coins z)))
    (pairSndD (NUPPT.inArg z))

/-- Bob's selected mask XORs the predicate word of the first simulated sample with the
second component of the supplied argument. -/
theorem otSimZb_eq (H : List Bool → List Bool) (z : List Bool) :
    otSimZb T H z =
      List.zipWith xor (H (pairEncode (simIdx T z) (simSample T T.gen.coins z)))
        (pairSndD (NUPPT.inArg z)) := rfl

/-- `S_B`'s pair `(z₁, z₂)`: `z_b` from `otSimZb`, `z_{1−b}` one fresh coin. -/
def otSimZ (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  if (pairFstD (NUPPT.inArg z)).headD false then
    pairEncode (coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
      (otSimZb T H z)
  else
    pairEncode (otSimZb T H z)
      (coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)

/-- Bob's simulated mask pair places the final coin segment in the unselected position and
the computed mask in the position selected by the first input bit. -/
theorem otSimZ_eq (H : List Bool → List Bool) (z : List Bool) :
    otSimZ T H z =
      if (pairFstD (NUPPT.inArg z)).headD false then
        pairEncode (coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
          (otSimZb T H z)
      else
        pairEncode (otSimZb T H z)
          (coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z) := rfl

/-- **`S_B`** on `⟨1^n, ⟨[b], [a_b]⟩⟩`: Bob's view, with two blocks of sampler coins as his tape,
the simulated index as Alice's first message, `(z₁, z₂)` from `otSimZ` as her second, and `[]`:
`⟨⟨1^n, [b]⟩, ⟨r_B, [i, ⟨z₁, z₂⟩, []]⟩⟩`. -/
def otSimBFun (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
    (pairEncode (coinSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
      (pairEncode (simIdx T z) (pairEncode (otSimZ T H z) (pairEncode [] []))))

/-- Bob's simulator word encodes his parameter, choice bit and sampler coins, followed by
the simulated index, mask pair and empty received message. -/
theorem otSimBFun_eq (H : List Bool → List Bool) (z : List Bool) :
    otSimBFun T H z =
      pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
        (pairEncode (coinSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
          (pairEncode (simIdx T z) (pairEncode (otSimZ T H z) (pairEncode [] [])))) := rfl

/-- `S_B` is polynomial-time when `H` is.

**Proof sketch.** `S_B` is built from polynomial-time pieces by pairing: the parameter and input
readers, the coin segments (`polyTimeComputable_coinSeg`), the simulated index and sample, `H`,
one XOR, and a branch on `b` (`polyTimeComputable_ite`). Each piece is matched to its definition
by `funext`. -/
theorem polyTimeComputable_otSimBFun {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    PolyTimeComputable (otSimBFun T H) := by
  have hzb : PolyTimeComputable (otSimZb T H) := by
    have h := polyTimeComputable_pairXor.comp ((hH.comp ((polyTimeComputable_simIdx T).pairEncode
      (polyTimeComputable_simSample T T.gen.coins))).pairEncode
      (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg))
    refine (congrArg PolyTimeComputable (?_ : otSimZb T H = _)).mpr h
    funext z
    simp only [otSimZb, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hu := polyTimeComputable_coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins))
    (.const 1)
  have hb₀ := polyTimeComputable_headD.comp
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)
  have hb : PolyTimeComputable fun z => [(pairFstD (NUPPT.inArg z)).headD false] := by
    refine (congrArg PolyTimeComputable
      (?_ : (fun z => [(pairFstD (NUPPT.inArg z)).headD false]) = _)).mpr hb₀
    funext z
    simp only [Function.comp_apply]
  have hz : PolyTimeComputable (otSimZ T H) := by
    have h := polyTimeComputable_ite (p := fun z => (pairFstD (NUPPT.inArg z)).headD false)
      hb (hu.pairEncode hzb) (hzb.pairEncode hu)
    refine (congrArg PolyTimeComputable (?_ : otSimZ T H = _)).mpr h
    funext z
    simp only [otSimZ]
  have h := (NUPPT.polyTimeComputable_inParam.pairEncode
    (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)).pairEncode
    ((polyTimeComputable_coinSeg T.gen.coins (.add T.sample.coins T.sample.coins)).pairEncode
      ((polyTimeComputable_simIdx T).pairEncode
        (hz.pairEncode (polyTimeComputable_const (pairEncode [] [])))))
  refine (congrArg PolyTimeComputable (?_ : otSimBFun T H = _)).mpr h
  funext z
  simp only [otSimBFun, Function.comp_apply]

/-- **The simulator `S_B`** of Proposition 161.5: `Gen`'s coins, two blocks of sampler coins and
one coin for `z_{1−b}`. -/
noncomputable def otSimB {H : List Bool → List Bool} (hH : PolyTimeComputable H) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_otSimBFun T hH)
    (.add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))))

/-- Bob's simulator uses generator coins, two sampler blocks and one fresh mask coin. -/
theorem otSimB_coins {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    (otSimB T hH).coins =
      .add T.gen.coins (.add T.sample.coins (.add T.sample.coins (.const 1))) :=
  NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_otSimBFun T hH) _

/-- Bob's simulator is uniform. -/
theorem otSimB_uniform {H : List Bool → List Bool} (hH : PolyTimeComputable H) :
    (otSimB T hH).Uniform :=
  NUPPT.ofPolyTimeUniform_uniform (polyTimeComputable_otSimBFun T hH) _

/-- Bob's simulator at parameter `n` computes its view word on the unary-parameter layout,
with the supplied argument and tape and empty advice. -/
theorem runAt_otSimB {H : List Bool → List Bool} (hH : PolyTimeComputable H)
    (n : ℕ) (y : List Bool) (r : (otSimB T hH).Coins n) :
    (otSimB T hH).runAt n y r =
      otSimBFun T H (NUPPT.layout (List.replicate n true) y [] (List.ofFn r)) := by
  rw [NUPPT.runAt_eq]
  unfold otSimB
  rw [NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput_eq, NUPPT.layout_eq]

/-! ### Proposition 161.5 -/

section Security

variable {h : ∀ i, T.D i → Bool} (H : List Bool → List Bool) (hH : PolyTimeComputable H)
  (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x])

include henc in
/-- **Proposition 161.5 with its simulators** [PS10]: for a collection of trapdoor permutations
`T` with an enhanced hard-core predicate `h` evaluated on encodings by polynomial-time `H`,
`S_A = otSimA` and `S_B = otSimB` simulate the two sides of Protocol 160.4 within a negligible
advantage, uniformly over the inputs.

**Proof sketch.**
1. *Correctness* (`otProtocol_outV`, `otProtocol_outP`): the real outputs are `a_b` for Bob and
   `[]` for Alice on every coin string, which are the ideal outputs. So each side reduces to its
   view.
2. *Alice's side* (`S_A`). Alice's real view differs from `S_A`'s only in Bob's message.
   - Real: `y_b = encD(perm x)` for a sampled `x`, and `y_{1−b}` a sampled element.
   - Simulated: two sampled elements, canonical by `SamplerCanonical`.

   The sampler is within `δ(n)` of uniform on `D_i` (`T.OneWay.sampleClose`), and `perm` is a
   bijection, so each coordinate is within `δ(n)` of `encD` of a uniform element, independently
   of `b`. The views are `2δ(n)`-close statistically, so any distinguisher's advantage is at most
   `2δ(n)` (`distAdv_le_of_statClose`).
3. *Bob's side* (`S_B`).
   - Bob's real view is his tape, `i`, and `(z₁, z₂)` with `z_b = h(x) ⊕ a_b` and
     `z_{1−b} = h(u) ⊕ a_{1−b}`, where `u = perm⁻¹(x')` for Bob's raw element `x'`.
   - `S_B` produces the same, but with `z_{1−b}` a fresh coin.
   - A distinguisher of the two gives a predictor of `h(u)` from `⟨i, s'⟩`, where `s'` are the
     sampler coins of `x'`: build the view around the challenge (Bob's tape contains `s'`), run
     the distinguisher, and flip according to `a_{1−b}` (the signed-predictor identity
     `exists_pkPredictor` of Algorithm 104.3).
   - Its advantage is at most `2 ε_EHC(n)` by `hEHC` (enhanced hard-core: the predictor sees the
     sampler's coins, which the plain hard-core property would not allow).
   - The predictor depends on `(b, a_{1−b})`, four cases, so the bound is uniform over the
     inputs: take the maximum of the four negligible functions.
4. *Efficiency.* The predictor runs Bob's sampler, the distinguisher, and one XOR: a machine by
   composition (`NUPPT.exists_comp`).

The source writes out `S_A` only and leaves `S_B` "as an exercise"; step 3 is that exercise. -/
theorem otProtocol_simulators (hT : T.OneWay) (hEHC : EnhancedHardCore T h) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
        (y : Fin (otFunctionality.inB.eval n) → Bool),
        distAdv (otFunctionality.realA (otProtocol T H) n x y)
            (otFunctionality.idealA (otSimA T) n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv (otFunctionality.realB (otProtocol T H) n x y)
            (otFunctionality.idealB (otSimB T hH) n x y) (D.distinguisherL n) ≤ ε n := by
  sorry

include hH in
/-- **Protocol 160.4 runs in polynomial time** (Definition 155.1's efficiency requirement,
`Functionality.PolyTime`).

**Proof sketch.**
1. *Alice.* On the empty history she outputs `Gen`'s index; on one message, the two masks (the
   trapdoor inverter, `H` and one XOR each, paired); otherwise `[]`. `Gen` and the inverter are
   uniform machines and `H` is polynomial-time, so a uniform machine computes her next-message
   function by composition, as for Algorithm 104.3's machines.
2. *Bob.* His sampler twice, `eval` and a pairing on one message; `[]` on two; `H` and one XOR on
   his complete history. The same composition gives a uniform machine.
3. *Messages.* The index has at most `Gen`'s output length (`NUPPT.runLenPoly`). Bob's pair is
   two sampler outputs or evaluations, polynomial in `n` and the index. The masks have one bit
   each, paired, and the fillers are empty. Their maximum is a polynomial `B`. -/
theorem otProtocol_polyTime : otFunctionality.PolyTime (otProtocol T H) := by
  sorry

include henc hH in
/-- **Proposition 161.5** [PS10]: Protocol 160.4 is an honest-but-curious one-out-of-two
oblivious transfer (Definition 155.1 for `otFunctionality`), for a collection of trapdoor
permutations with an enhanced hard-core predicate evaluated on canonical encodings by a
polynomial-time `H`. Sampler canonicity follows from the collection contract. -/
theorem otProtocol_hbcSecure (hT : T.OneWay) (hEHC : EnhancedHardCore T h) :
    HBCSecure (otProtocol T H) otFunctionality :=
  ⟨otProtocol_polyTime T H hH, otSimA T, otSimB T hH,
    otProtocol_simulators T H hH henc hT hEHC⟩

end Security

end TCSlib.Cryptography.SecureComputation
