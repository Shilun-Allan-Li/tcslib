/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Encryption

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge encryption

The simulation-based notion of secure private-key encryption of [PS10, §4.2]: a scheme is
*zero-knowledge* if there is a PPT simulator `S` such that, for every non-uniform PPT `D`,
`S(1^n)` is indistinguishable from the encryption `Enc_k(m)` of every message `m ∈ {0,1}^n`
under a fresh key `k ← Gen(1^n)` [PS10, Definition 111.1] — "the ciphertext allows the
eavesdropper to compute nothing she could not have computed without it". The theorem of the
section, [PS10, Theorem 112.2], is that zero-knowledge encryption is the same as
single-message security [PS10, Definition 91.1]: security gives zero knowledge with the
simulator "encrypt a canonical message" (`SingleMessageSecure.zeroKnowledge`), and zero
knowledge gives security by the two-step hybrid `Enc_k(m₀) ≈ S(1^n) ≈ Enc_k(m₁)`
(`ZeroKnowledge.singleMessageSecure`, proved). The optional perfect variant
(`PerfectZeroKnowledge`, the two distributions identical, Def-111.a) implies the
computational one.

The scheme, the ciphertext distribution `PrivateKeyScheme.encDist` and single-message
security are those of `TCSlib.Cryptography.Asymptotic.Encryption`; the simulator is a uniform
`Complexity.NUPPT` activated at parameter `n` on the empty argument (`Sim.runAt n []`), and
the distinguisher a non-uniform PPT on the ciphertext string (`Complexity.NUPPT.distinguisherL`).

**Deviation:** `ZeroKnowledge`: the simulator is a strict PPT (D8); the distinguisher receives
`1^n` with the ciphertext (D5); the bound is `≤ ε(n)`; the message `m` is fixed per `n`
(the text's `∀ m ∈ {0,1}^n`).

**Deviation:** `singleMessageSecure_iff_zeroKnowledge` (Theorem 112.2): the text's hypothesis
"a polynomial-time `M` with `M(1^n) ∈ {0,1}^n`" is discharged by the canonical message `0^n`
(the gap list of `PassShelatChapter2-4Plan.md`), so the theorem has no hypothesis beyond the
scheme; the text's hypothesis "`Gen`, `Enc` PPT" is part of `PrivateKeyScheme`.

## Main definitions

* `TCSlib.Cryptography.PrivateKeyScheme.ZeroKnowledge` — zero-knowledge encryption
  [PS10, Definition 111.1].
* `TCSlib.Cryptography.PrivateKeyScheme.PerfectZeroKnowledge` — the perfect variant
  (the simulated and real ciphertext distributions identical; Def-111.a, optional).

## Main results

* `TCSlib.Cryptography.PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge` —
  [PS10, Theorem 112.2]: single-message security and zero knowledge are equivalent.
* `TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure.zeroKnowledge` — the direction
  security ⇒ zero knowledge (Thm-112.2.i; simulator `Enc_k(0^n)`).
* `TCSlib.Cryptography.PrivateKeyScheme.ZeroKnowledge.singleMessageSecure` — the direction
  zero knowledge ⇒ security (Thm-112.2.ii; two-step hybrid, proved).
* `TCSlib.Cryptography.PrivateKeyScheme.PerfectZeroKnowledge.zeroKnowledge` — perfect zero
  knowledge is zero knowledge (sanity, proved).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.2: Definition 111.1, Theorem 112.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.2 (the concrete `distAdv`).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

namespace PrivateKeyScheme

/-! ### Zero-knowledge encryption [PS10, Definition 111.1] -/

/-- **Zero-knowledge encryption** [PS10, Definition 111.1]: there is a PPT simulator `Sim`
such that for every non-uniform PPT `D` there is a negligible `ε` with, for all `n` and all
`m ∈ {0,1}^n`, `D` distinguishes `{k ← Gen(1^n) : Enc_k(m)}` from `{Sim(1^n)}` with
advantage at most `ε(n)`. The simulator is activated at parameter `n` on the empty argument
(it receives `1^n` only).

**Deviation:** the simulator is a strict PPT (D8); the distinguisher receives `1^n` with the
ciphertext (D5); the bound is `≤ ε(n)`. -/
def ZeroKnowledge (S : PrivateKeyScheme) : Prop :=
  ∃ Sim : NUPPT, Sim.Uniform ∧ ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (m : Fin n → Bool),
      distAdv (S.encDist n m) (Sim.runAt n []) (D.distinguisherL n) ≤ ε n

/-- **Perfect zero-knowledge encryption** (Def-111.a, [PS10, p. 111, "we can strengthen the
definition to require that the above distributions are identical"]): a PPT simulator whose
output distribution at every `n` is exactly the ciphertext distribution of every message
(`StatClose … 0`, every test set has the same probability). -/
def PerfectZeroKnowledge (S : PrivateKeyScheme) : Prop :=
  ∃ Sim : NUPPT, Sim.Uniform ∧ ∀ n (m : Fin n → Bool),
    StatClose (S.encDist n m) (Sim.runAt n []) 0

/-- **Perfect zero knowledge is zero knowledge** (sanity): identical distributions are
indistinguishable, every advantage being `0` (`distAdv_le_of_statClose`, `negligible_zero`). -/
theorem PerfectZeroKnowledge.zeroKnowledge {S : PrivateKeyScheme} (h : S.PerfectZeroKnowledge) :
    S.ZeroKnowledge := by
  obtain ⟨Sim, hSim, hclose⟩ := h
  exact ⟨Sim, hSim, fun D => ⟨fun _ => 0, negligible_zero,
    fun n m => distAdv_le_of_statClose _ _ (hclose n m) _⟩⟩

/-! ### [PS10, Theorem 112.2]: security ⇔ zero knowledge -/

/-- **Zero knowledge implies single-message security** (Thm-112.2.ii, the direction "ZK
implies Security" of [PS10, Theorem 112.2]): with `Sim` the zero-knowledge simulator and
`ε_D` its negligible bound for `D`, for all `n`, `m₀`, `m₁`,
`distAdv (Enc_k(m₀)) (Enc_k(m₁)) D ≤ distAdv (Enc_k(m₀)) (Sim(1^n)) D + distAdv (Sim(1^n)) (Enc_k(m₁)) D ≤ 2 ε_D(n)`
— the text's "by the hybrid lemma `D` distinguishes `H¹` from `H³` or `H³` from `H²` with
probability `1/(2p(n))`" is this two-step chain (`abs_sub_le`, `Negligible.const_mul`). -/
theorem ZeroKnowledge.singleMessageSecure {S : PrivateKeyScheme} (h : S.ZeroKnowledge) :
    S.SingleMessageSecure := by
  obtain ⟨Sim, -, hSim⟩ := h
  intro D
  obtain ⟨ε, hε, hD⟩ := hSim D
  refine ⟨fun n => 2 * ε n, hε.const_mul 2, fun n m₀ m₁ => ?_⟩
  have h₀ := hD n m₀
  have h₁ := hD n m₁
  unfold distAdv at h₀ h₁ ⊢
  calc |acceptProb (S.encDist n m₀) (D.distinguisherL n) -
        acceptProb (S.encDist n m₁) (D.distinguisherL n)|
      ≤ |acceptProb (S.encDist n m₀) (D.distinguisherL n) -
          acceptProb (Sim.runAt n []) (D.distinguisherL n)| +
        |acceptProb (Sim.runAt n []) (D.distinguisherL n) -
          acceptProb (S.encDist n m₁) (D.distinguisherL n)| := abs_sub_le _ _ _
    _ ≤ ε n + ε n := add_le_add h₀ (by rw [abs_sub_comm]; exact h₁)
    _ = 2 * ε n := by ring

/-- Masking a string with itself gives the zero string: `u ⊕ u = 0^{|u|}` (the canonical
message `0^n` of the simulator is computed from `1^n` this way). -/
private theorem zipWith_xor_self (u : List Bool) :
    List.zipWith xor u u = List.replicate u.length false := by
  rw [List.zipWith_self]
  simp [List.map_const']

/-- The raw string function of the simulator of [PS10, Theorem 112.2]: on the layout
`⟨⟨⟨u, y⟩, α⟩, r⟩` with `u = 1^n`, cut the coins `r` at `Gen`'s coin length `gen.coins n`, run
`Gen` on the first part to obtain the key `k`, and run `Enc` on `⟨k, 0^n⟩` (`0^n = u ⊕ u`)
with the second part. -/
private def zkSimFun (S : PrivateKeyScheme) (z : List Bool) : List Bool :=
  S.enc.output (NUPPT.layout (NUPPT.inParam z)
    (pairEncode
      (S.gen.output (NUPPT.layout (NUPPT.inParam z) [] []
        ((NUPPT.inCoins z).take (S.gen.coins.eval (NUPPT.inParam z).length))))
      (List.zipWith xor (NUPPT.inParam z) (NUPPT.inParam z)))
    [] ((NUPPT.inCoins z).drop (S.gen.coins.eval (NUPPT.inParam z).length)))

/-- `zkSimFun S` is polynomial-time: the layout projections, the coin cuts
`Complexity.polyTimeComputable_pairTakePoly`/`pairDropPoly` at `gen.coins`, the zero message
by `Complexity.polyTimeComputable_pairXor` on `⟨u, u⟩`, and the output functions of `Gen`
and `Enc` (`Complexity.NUPPT.polyTimeComputable_output`), assembled by
`Complexity.NUPPT.polyTimeComputable_layout`.

**Proof sketch.** The two coin segments are `pairTakePoly`/`pairDropPoly gen.coins` applied to
the re-pairing `⟨inParam z, inCoins z⟩` (as in `Complexity.NUPPT.exists_seq`); the key is
`gen.output` of the layout `⟨⟨⟨u, []⟩, []⟩, r₁⟩`; the zero message is `pairXor` of `⟨u, u⟩`;
`enc.output` of the layout `⟨⟨⟨u, ⟨k, 0^n⟩⟩, []⟩, r₂⟩` is the composite, equal to `zkSimFun S`
by unfolding `Function.comp` (`PolyTimeComputable.comp`, `PolyTimeComputable.pairEncode`,
`polyTimeComputable_const`). -/
private theorem polyTimeComputable_zkSimFun (S : PrivateKeyScheme) :
    PolyTimeComputable (zkSimFun S) := by
  have hcut := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have hr₁ : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).take (S.gen.coins.eval (NUPPT.inParam z).length) := by
    have := (polyTimeComputable_pairTakePoly S.gen.coins).comp hcut
    convert this using 1
    funext z
    simp [Function.comp]
  have hr₂ : PolyTimeComputable fun z =>
      (NUPPT.inCoins z).drop (S.gen.coins.eval (NUPPT.inParam z).length) := by
    have := (polyTimeComputable_pairDropPoly S.gen.coins).comp hcut
    convert this using 1
    funext z
    simp [Function.comp]
  have hzero : PolyTimeComputable fun z =>
      List.zipWith xor (NUPPT.inParam z) (NUPPT.inParam z) := by
    have := polyTimeComputable_pairXor.comp
      (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inParam)
    convert this using 1
    funext z
    simp [Function.comp]
  have hk := S.gen.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam (polyTimeComputable_const [])
      (polyTimeComputable_const []) hr₁)
  have h := S.enc.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam (hk.pairEncode hzero)
      (polyTimeComputable_const []) hr₂)
  convert h using 1

/-- The simulator of [PS10, Theorem 112.2]: the PPT with output function `zkSimFun S` and
coins `gen.coins + enc.coins` ("`Sim(1^n)` draws `k ← Gen(1^n)` and outputs `Enc_k(0^n)`"). -/
private noncomputable def zkSim (S : PrivateKeyScheme) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_zkSimFun S) (.add S.gen.coins S.enc.coins)

/-- On the coin string `r₁ ‖ r₂` (`Fin.appendEquiv`) the simulator outputs exactly the
ciphertext `Enc_k(0^n)` with `k = Gen(1^n; r₁)` and encryption coins `r₂`, i.e.
`encDist n 0^n (r₁, r₂)` (`runAtL_ofPolyTimeUniform`, `List.ofFn_fin_append`, the cuts
`List.take_left'`/`List.drop_left'`, `gen_uniform`, `enc_uniform`, `zipWith_xor_self`). -/
private theorem zkSim_runAt (S : PrivateKeyScheme) (n : ℕ) (r₁ : S.gen.Coins n)
    (r₂ : S.enc.Coins n) :
    (zkSim S).runAt n [] (Fin.appendEquiv (S.gen.coinLen n) (S.enc.coinLen n) (r₁, r₂)) =
      S.encDist n (fun _ => false) (r₁, r₂) := by
  have ht : (List.ofFn r₁ ++ List.ofFn r₂).take (S.gen.coins.eval n) = List.ofFn r₁ :=
    List.take_left' (by simp [NUPPT.coinLen])
  have hd : (List.ofFn r₁ ++ List.ofFn r₂).drop (S.gen.coins.eval n) = List.ofFn r₂ :=
    List.drop_left' (by simp [NUPPT.coinLen])
  show (NUPPT.ofPolyTimeUniform (polyTimeComputable_zkSimFun S)
    (.add S.gen.coins S.enc.coins)).runAtL n [] (List.ofFn (Fin.append r₁ r₂)) = _
  rw [NUPPT.runAtL_ofPolyTimeUniform, List.ofFn_fin_append]
  simp only [encDist, NUPPT.runAt, NUPPT.advInput, S.gen_uniform n, S.enc_uniform n, zkSimFun,
    NUPPT.layout, NUPPT.inParam, NUPPT.inCoins, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, ht, hd, zipWith_xor_self, List.ofFn_const]

/-- The output distribution of the simulator is the ciphertext distribution of `0^n`: every
distinguisher accepts `Sim(1^n)` and `{k ← Gen(1^n) : Enc_k(0^n)}` with the same probability
(the coin split `Fin.appendEquiv` is a bijection of the seed spaces, `acceptProb_comp_equiv`,
and `zkSim_runAt`). -/
private theorem acceptProb_zkSim (S : PrivateKeyScheme) (n : ℕ) {ρ : Type*} [Fintype ρ]
    (Dst : List Bool → ρ → Bool) :
    acceptProb ((zkSim S).runAt n []) Dst = acceptProb (S.encDist n fun _ => false) Dst := by
  rw [← acceptProb_comp_equiv (Fin.appendEquiv (S.gen.coinLen n) (S.enc.coinLen n) :
    S.gen.Coins n × S.enc.Coins n ≃ (zkSim S).Coins n) ((zkSim S).runAt n []) Dst]
  congr 1
  funext s
  exact zkSim_runAt S n s.1 s.2

/-- **Single-message security implies zero knowledge** (Thm-112.2.i, the direction "Security
implies ZK" of [PS10, Theorem 112.2]): the simulator `Sim(1^n)` draws `k ← Gen(1^n)` and
outputs `Enc_k(0^n)`, the encryption of the canonical message `0^n` (the text's
`M(1^n)`); for every `D` and `m`, `Sim(1^n)` *is* the sampler `encDist n 0^n`, so the
advantage of `D` between `Enc_k(m)` and `Sim(1^n)` is its advantage between `Enc_k(m)` and
`Enc_k(0^n)`, at most `ε_D(n)` by Definition 91.1 with `m₀ := m`, `m₁ := 0^n`.

**Deviation:** the text's hypothesis "a polynomial-time `M` with `M(1^n) ∈ {0,1}^n`" is
discharged by the canonical message `0^n`.

**Proof sketch.** Machine step: `Sim := NUPPT.ofPolyTimeUniform` of the raw function
`z ↦ S.enc.output (layout u ⟨S.gen.output (layout u [] [] r₁), 0^{|u|}⟩ [] r₂)` with
`u := inParam z`, `r₁ := (inCoins z).take (S.gen.coins.eval |u|)`, `r₂` the rest, and coins
`S.gen.coins + S.enc.coins`: polynomial-time by `NUPPT.polyTimeComputable_layout`, the
projections `polyTimeComputable_inParam`/`_inCoins`, `polyTimeComputable_pairTakePoly`/
`_pairDropPoly` at `S.gen.coins`, `NUPPT.polyTimeComputable_output` of `gen` and `enc`,
`PolyTimeComputable.pairEncode`, and the canonical message `0^{|u|} = u ⊕ u`
(`Complexity.polyTimeComputable_pairXor` on `⟨u, u⟩`, `zipWith_xor_self`) — the machine
`zkSim S` with raw function `zkSimFun S` (`polyTimeComputable_zkSimFun`). Uniform by
`ofPolyTimeUniform_uniform`. Functional identity (`zkSim_runAt`: `runAtL_ofPolyTimeUniform`,
`S.gen_uniform`, `S.enc_uniform`, `List.length_replicate`): for `(r₁, r₂)`,
`Sim.runAt n [] (r₁ ‖ r₂) = S.encDist n 0^n (r₁, r₂)` where the coin string is split by
`Fin.appendEquiv` (`List.ofFn_fin_append`, `List.take_left'`, `List.drop_left'`), hence
`acceptProb (Sim.runAt n []) D' = acceptProb (S.encDist n 0^n) D'` by
`acceptProb_comp_equiv` (`acceptProb_zkSim`). Asymptotic step: for `D` take `ε` from `h D`; then
`distAdv (encDist n m) (Sim.runAt n []) (D.distinguisherL n)
  = distAdv (encDist n m) (encDist n 0^n) (D.distinguisherL n) ≤ ε n`. -/
theorem SingleMessageSecure.zeroKnowledge {S : PrivateKeyScheme} (h : S.SingleMessageSecure) :
    S.ZeroKnowledge := by
  refine ⟨zkSim S, NUPPT.ofPolyTimeUniform_uniform _ _, fun D => ?_⟩
  obtain ⟨ε, hε, hD⟩ := h D
  refine ⟨ε, hε, fun n m => ?_⟩
  have := hD n m (fun _ => false)
  unfold distAdv at this ⊢
  rwa [acceptProb_zkSim]

/-- **[PS10, Theorem 112.2]: a private-key encryption scheme is single-message secure iff it
is zero-knowledge.** The two directions are `SingleMessageSecure.zeroKnowledge` (simulator
`Enc_k(0^n)`) and `ZeroKnowledge.singleMessageSecure` (two-step hybrid through the simulated
ciphertext).

**Deviation:** the text's hypothesis "a polynomial-time `M` with `M(1^n) ∈ {0,1}^n`" is
discharged by the canonical message `0^n`; "`Gen`, `Enc` PPT" is part of `PrivateKeyScheme`. -/
theorem singleMessageSecure_iff_zeroKnowledge (S : PrivateKeyScheme) :
    S.SingleMessageSecure ↔ S.ZeroKnowledge :=
  ⟨SingleMessageSecure.zeroKnowledge, ZeroKnowledge.singleMessageSecure⟩

end PrivateKeyScheme

end TCSlib.Cryptography
