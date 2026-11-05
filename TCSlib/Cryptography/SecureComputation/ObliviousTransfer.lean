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
coin string. The hard-core predicate is evaluated by `H` with `H ⟨i, w⟩ = [h i x]` for every `w`
decoding to `x` (the fields of `Collection.PredEvaluator`, passed unbundled so that this module
needs only `Asymptotic/Collections`).

**Deviations and source notes.**
- **Five messages.** The ch. 2–4 model (D8) reads a party's output as its next-message function
  on its complete history, so the last mover's last message is its output. With the source's
  three messages Alice would move last and output `(z₁, z₂)`, not `⊥`. Two empty messages are
  added (Bob, then Alice), so Alice's output is `[]` (the empty `⊥` of `otFunctionality`) and
  Bob's is computed on his complete history `[i, (z₁, z₂), []]`.
- **The source's typo:** Alice sends `(z₁, z₂)`, not `(z₁, …, z₄)` (inventory Prot-160.4).
- **Random elements, not random strings.** The source's `y_j ← {0,1}^n` becomes the collection's
  domain sampler, as in Algorithm 104.3. `y_b = f_i(x) = encD (perm x)` is a canonical encoding.
  `y_{1−b}` must be one too, or Alice tells the two apart and learns `b`. A total decoder may
  accept non-canonical strings, so Proposition 161.5 assumes that the sampler outputs canonical
  encodings (`SamplerCanonical`).
- **Bob knows no preimage of `y_{1−b}`.** It is a raw sample: Bob knows the element, not its
  preimage under the permutation.

## Main definitions

* `SecureComputation.otSender`, `otReceiver`, `otProtocol`: Protocol 160.4.
* `SecureComputation.otSimA`, `otSimB`: the simulators of Proposition 161.5.
* `SecureComputation.SamplerCanonical`: the sampler outputs canonical encodings.

## Main results

* `SecureComputation.otProtocol_outV`, `otProtocol_outP`: correctness: Bob outputs `a_b` and
  Alice outputs `⊥ = []`, on every coin string.
* `SecureComputation.otProtocol_simulators` (Prop 161.5 with the explicit simulators, stated; a
  `sorry` under its sketch), and `otProtocol_hbcSecure` (Prop 161.5, proved from it).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Protocol 160.4 and Proposition 161.5 (book pp. 160–162).
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

/-- Bob's sampled element `w` (decoding to `x`), from the first half of his coins. -/
def otKnown (n : ℕ) (i r : List Bool) : List Bool :=
  T.sample.runAtL n i (r.take (T.sample.coins.eval n))

/-- Bob's raw element `y_{1−b}`, from the second half of his coins. -/
def otRaw (n : ℕ) (i r : List Bool) : List Bool :=
  T.sample.runAtL n i (r.drop (T.sample.coins.eval n))

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

/-- **Protocol 160.4** [PS10], with five messages, Alice first. -/
def otProtocol (H : List Bool → List Bool) : Protocol where
  P := otSender T H
  V := otReceiver T H
  rounds := .const 5
  verifierFirst := false

/-- **The sampler outputs canonical encodings**: at every generated index, every output of the
domain sampler is `encD i x` for some `x ∈ D_i`. -/
def SamplerCanonical : Prop :=
  ∀ n (r : T.gen.Coins n) (s : T.sample.Coins n), ∃ x,
    T.sample.runAt n (T.index n r) s = T.encD (T.index n r) x

/-! ### Correctness -/

section Correctness

variable {h : ∀ i, T.D i → Bool} (H : List Bool → List Bool)
  (hspec : ∀ i w x, T.decD i w = some x → H (pairEncode i w) = [h i x])

include hspec in
/-- **Bob outputs `a_b`** on every coin string (the output clause of Proposition 161.5). -/
theorem otProtocol_outV (x : List Bool) (a : Fin 2 → Bool) (b : Fin 1 → Bool)
    (r : (otProtocol T H).ExecCoins (otProtocol T H).P x) :
    (otProtocol T H).outV (otProtocol T H).P x (List.ofFn a) (List.ofFn b) r =
      [a (if b 0 then 1 else 0)] := by
  obtain ⟨rA, rB⟩ := r
  simp [Protocol.outV, Protocol.transcriptWith, otProtocol, exec, otSender, otReceiver]
  have hg : T.gen.runAtL x.length [] (List.ofFn fun i => rA i) = T.gen.runAt x.length [] rA := rfl
  erw [hg]
  -- Bob's first coin block, typed
  let s1 : T.sample.Coins x.length := fun j => rB ⟨j.1,
    show (j : ℕ) < T.sample.coinLen x.length + T.sample.coinLen x.length from
      Nat.lt_of_lt_of_le j.2 (Nat.le_add_right _ _)⟩
  have hs1 : (List.ofFn fun i => rB i).take (T.sample.coins.eval x.length) = List.ofFn s1 := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_ofFn]
      show min (T.sample.coinLen x.length)
        (T.sample.coinLen x.length + T.sample.coinLen x.length) = T.sample.coinLen x.length
      omega
    · intro j h₁ h₂
      simp only [List.getElem_take, List.getElem_ofFn]
      rfl
  have hknown : otKnown T x.length (pairFstD (T.gen.runAt x.length [] rA))
      (List.ofFn fun i => rB i) =
      T.sample.runAt x.length (pairFstD (T.gen.runAt x.length [] rA)) s1 := by
    rw [otKnown, hs1]
    rfl
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
    rw [← List.ofFn_const]
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
  simp [Protocol.outP, Protocol.transcriptWith, otProtocol, exec, otSender, otReceiver]

end Correctness

/-! ### The simulators -/

/-- The coin segment of length `q(n)` after the first `p(n)` coins of a raw layout. -/
def coinSeg (p q : PolyExpr) (z : List Bool) : List Bool :=
  ((NUPPT.inCoins z).drop (p.eval (NUPPT.inParam z).length)).take (q.eval (NUPPT.inParam z).length)

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

/-- `S_B`'s mask `z_b = h(x) ⊕ a_b`, with `x` its first sampled element and `[a_b]` the second
part of its argument. -/
def otSimZb (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  List.zipWith xor (H (pairEncode (simIdx T z) (simSample T T.gen.coins z)))
    (pairSndD (NUPPT.inArg z))

/-- `S_B`'s pair `(z₁, z₂)`: `z_b` from `otSimZb`, `z_{1−b}` one fresh coin. -/
def otSimZ (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  if (pairFstD (NUPPT.inArg z)).headD false then
    pairEncode (coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)
      (otSimZb T H z)
  else
    pairEncode (otSimZb T H z)
      (coinSeg (.add T.gen.coins (.add T.sample.coins T.sample.coins)) (.const 1) z)

/-- **`S_B`** on `⟨1^n, ⟨[b], [a_b]⟩⟩`: Bob's view, with two blocks of sampler coins as his tape,
the simulated index as Alice's first message, `(z₁, z₂)` from `otSimZ` as her second, and `[]`:
`⟨⟨1^n, [b]⟩, ⟨r_B, [i, ⟨z₁, z₂⟩, []]⟩⟩`. -/
def otSimBFun (H : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode (pairEncode (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)))
    (pairEncode (coinSeg T.gen.coins (.add T.sample.coins T.sample.coins) z)
      (pairEncode (simIdx T z) (pairEncode (otSimZ T H z) (pairEncode [] []))))

/-- `S_B` is polynomial-time when `H` is. -/
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

/-! ### Proposition 161.5 -/

section Security

variable {h : ∀ i, T.D i → Bool} (H : List Bool → List Bool) (hH : PolyTimeComputable H)
  (hspec : ∀ i w x, T.decD i w = some x → H (pairEncode i w) = [h i x])

include hspec in
/-- **Proposition 161.5 with its simulators** [PS10]: for a collection of trapdoor permutations
`T` with hard-core predicate `h` (evaluated by `H`), whose sampler outputs canonical encodings,
`S_A = otSimA` and `S_B = otSimB` simulate the two sides of Protocol 160.4 within a negligible
advantage, uniformly over the inputs.

**Proof sketch.**
1. *Correctness* (`otProtocol_outV`, `otProtocol_outP`): the real outputs are `a_b` for Bob and
   `[]` for Alice on every coin string, which are the ideal outputs. So each side reduces to its
   view.
2. *Alice's side* (`S_A`). Alice's real view differs from `S_A`'s only in Bob's message.
   - Real: `y_b = encD(perm x)` for a sampled `x`, and `y_{1−b}` a sampled element.
   - Simulated: two sampled elements, canonical by `hcanon`.

   The sampler is within `δ(n)` of uniform on `D_i` (`T.OneWay.sampleClose`), and `perm` is a
   bijection, so each coordinate is within `δ(n)` of `encD` of a uniform element, independently
   of `b`. The views are `2δ(n)`-close statistically, so any distinguisher's advantage is at most
   `2δ(n)` (`distAdv_le_of_statClose`).
3. *Bob's side* (`S_B`).
   - Bob's real view is his tape, `i`, and `(z₁, z₂)` with `z_b = h(x) ⊕ a_b` and
     `z_{1−b} = h(u) ⊕ a_{1−b}`, where `u = perm⁻¹(x')` for Bob's raw element `x'`.
   - `S_B` produces the same, but with `z_{1−b}` a fresh coin.
   - A distinguisher of the two gives a predictor of `h(u)` from `⟨i, encD(x')⟩ = ⟨i, f_i(u)⟩`:
     run it on the view built around the challenge, and flip according to `a_{1−b}` (the
     signed-predictor identity `exists_pkPredictor` of Algorithm 104.3).
   - `x'` is within `δ(n)` of uniform, so `u` is too, and the advantage is at most
     `2(ε_HC(n) + δ(n))` by `hHC`.
   - The predictor depends on `(b, a_{1−b})`, four cases, so the bound is uniform over the
     inputs: take the maximum of the four negligible functions.
4. *Efficiency.* The predictor runs Bob's sampler, the distinguisher, and one XOR: a machine by
   composition (`NUPPT.exists_comp`).

The source writes out `S_A` only and leaves `S_B` "as an exercise"; step 3 is that exercise. -/
theorem otProtocol_simulators (hT : T.OneWay) (hHC : T.toCollection.HardCore h)
    (hcanon : SamplerCanonical T) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
        (y : Fin (otFunctionality.inB.eval n) → Bool),
        distAdv (otFunctionality.realA (otProtocol T H) n x y)
            (otFunctionality.idealA (otSimA T) n x y) (D.distinguisherL n) ≤ ε n ∧
          distAdv (otFunctionality.realB (otProtocol T H) n x y)
            (otFunctionality.idealB (otSimB T hH) n x y) (D.distinguisherL n) ≤ ε n := by
  sorry

include hspec hH in
/-- **Proposition 161.5** [PS10]: Protocol 160.4 is an honest-but-curious one-out-of-two
oblivious transfer (Definition 155.1 for `otFunctionality`), for a collection of trapdoor
permutations with a hard-core predicate whose sampler outputs canonical encodings. -/
theorem otProtocol_hbcSecure (hT : T.OneWay) (hHC : T.toCollection.HardCore h)
    (hcanon : SamplerCanonical T) : HBCSecure (otProtocol T H) otFunctionality :=
  ⟨otSimA T, otSimB T hH, otProtocol_simulators T H hH hspec hT hHC hcanon⟩

end Security

end TCSlib.Cryptography.SecureComputation
