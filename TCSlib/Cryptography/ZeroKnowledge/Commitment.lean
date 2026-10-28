/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Commitment schemes and their construction from a one-way permutation

The material of [PS10, §4.7.1]: single-message commitment schemes [PS10, Definition 126.3]
(a deterministic polynomial-time `Com` with randomness polynomial `ℓ`; *binding*: distinct
values never commit to the same string; *hiding*: commitments to any two values of the same
length are computationally indistinguishable), multi-value hiding "by a simple hybrid
argument" (Claim-126.a), and the construction from a one-way permutation `f` with a hard-core
predicate `h` [PS10, Theorem 126.4]: `Com(b, r) = f(r) ‖ (b ⊕ h(r))` for one bit (Alg-127.a),
extended bitwise to `n`-bit values with independent randomness (`ℓ(n) = n²`). Binding
"directly follows from the construction" (Claim-127.b: `f` is injective and `⊕` cancels);
one-bit hiding is the predictor reduction of [PS10, Theorem 104.4] (Claim-127.c: a
distinguisher between `Com(0, ·)` and `Com(1, ·)` with advantage `ε` predicts `h(r)` from
`f(r)` with probability exactly `1/2 + ε/2`); `n`-bit hiding is the "show this!" hybrid over
the bits (Claim-127.d, Claim-126.a with single-bit values).

Two layers (foundation decision D2). The *concrete* layer reuses the frozen Garg development:
the one-bit scheme `Com(b, ·)` is `owpGen`/`owpGenNot` with `β := Unit`
(`Pseudorandom/GeneratorFromPermutation.lean`), its predictor is `owpPredictorSnoc` of
`Asymptotic/HardCore.lean`, and `predProb_owpPredictor_false/true` **are** Claim-127.c; the
coordinatewise hybrid lemma `exists_pairRed_ge` (new, concrete) generalises
`exists_multicopyRed_ge` and carries Claim-126.a and Claim-127.d. The *asymptotic* layer states
the frozen `Commitment` structure, multi-value hiding and Theorem 126.4 for `NUPPT`
distinguishers. The hiding fills do **not** sample the other coordinates of the hybrid: by
averaging over the reduction's coins (`CommitmentLemmas.exists_fixCoins`) a fixed choice of
the other commitments does at least as well, and the reduction machine merely splices the
challenge between two hard-wired strings (`CommitmentLemmas.exists_spliceRed`,
`exists_pairSpliceRed`) — the non-uniformity of [PS10, Definition 126.3] at work, so no
evaluator of `Com` is needed. The proof infrastructure (averaging, coin transport, tuple
splitting, the splice machines and the bitwise commitment loop `ComLoop` behind the
polynomial-time evaluator of Alg-127.a) is `TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas`.

**Deviation:** `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit
argument, colours padded to `n` bits (DQ4). In the string form `Com ⟨v, r⟩` the parameter is
`n = |v|`; the 3-colouring protocol pads its 2-bit colours to `n` bits.

## Main definitions

* `TCSlib.Cryptography.Commitment` — commitment scheme [PS10, Definition 126.3] (Def-126.3);
  `TCSlib.Cryptography.multiCom` — a vector of commitments as one string (Claim-126.a).
* `TCSlib.Cryptography.pairTuple`, `pairHybrid`, `pairRed` — coordinatewise products, their
  hybrids and the hybrid reduction (the concrete content of Claim-126.a and Claim-127.d).
* `TCSlib.Cryptography.bitCom` — the one-bit scheme `Com(b, r) = f(r) ‖ (b ⊕ h(r))`
  (Alg-127.a); `TCSlib.Cryptography.owpCom`, `owpComAt`, `owpComStr`, `owpComLen` — the
  `n`-bit scheme (typed, at a parameter, as the string function of `Commitment`; `ℓ(n) = n²`).
* `TCSlib.Cryptography.BitHiding` — hiding of the one-bit scheme against `NUPPT`s.

## Main results

* `TCSlib.Cryptography.exists_pairRed_ge` — the coordinatewise hybrid lemma (concrete);
  `TCSlib.Cryptography.Commitment.multiHiding` — multi-value hiding (Claim-126.a).
* `TCSlib.Cryptography.bitCom_inj`, `owpCom_inj`, `owpComStr_binding` — binding of
  Alg-127.a (Claim-127.b, proved).
* `TCSlib.Cryptography.exists_bitComPredictor` — single-bit hiding is the predictor
  reduction (Claim-127.c, concrete, proved); `HardCore.bitHiding` — its asymptotic form;
  `BitHiding.owpComStr_hides` — the bitwise hybrid (Claim-127.d).
* `TCSlib.Cryptography.owp_commitment` — **[PS10, Theorem 126.4]**: a one-way permutation
  with a hard-core predicate gives a commitment scheme; `exists_commitment_of_owp_hardCore` —
  the existential headline; `bitCom_false_eq_owpGenPRG` — `Com(0, ·)` is the generator of
  [PS10, Theorem 79.4]; `owpComStr_polyTimeComputable` — its `Com` is polynomial-time
  (the bitwise loop `CommitmentLemmas.ComLoop`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7.1: Definition 126.3, Theorem 126.4; §3.3.3–3.3.4: Definition 78.3, Theorem 79.4;
  §3.5.2: Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3.2 (Construction 3.2, Theorem 3.2) and Lemma 3.3 (the
  multicopy hybrid argument).
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ## Commitment schemes [PS10, Definition 126.3] -/

/-- A **commitment scheme** [PS10, Definition 126.3] (Def-126.3): a deterministic
polynomial-time string function `Com` (on the pair `⟨v, r⟩`) with a randomness polynomial `ℓ`
such that (1) *binding*: for all `n`, all distinct `v₀, v₁ ∈ {0,1}^n` and all
`r₀, r₁ ∈ {0,1}^{ℓ(n)}`, `Com(v₀, r₀) ≠ Com(v₁, r₁)`; (2) *hiding*: for every non-uniform PPT
`D` there is a negligible `ε` such that for every `n` and `v₀, v₁ ∈ {0,1}^n`, `D` (run at
parameter `n`) distinguishes `{r ← {0,1}^{ℓ(n)} : Com(v₀, r)}` from
`{r ← {0,1}^{ℓ(n)} : Com(v₁, r)}` with advantage at most `ε(n)`.

**Deviation:** `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit
argument, colours padded to `n` bits (DQ4). As printed, binding is unsatisfiable (`v₀ = v₁`,
`r₀ = r₁`); the string form's parameter is `n = |v|`, typed users supply `n` explicitly; the
distinguisher's verdict is the string `[true]` (`NUPPT.distinguisherL`, Deviation 4). -/
structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where
  /-- `Com` is computable in deterministic polynomial time. -/
  easy : PolyTimeComputable Com
  /-- Binding: distinct values of length `n` never commit to the same string. -/
  binding : ∀ n (v₀ v₁ r₀ r₁ : List Bool), v₀.length = n → v₁.length = n →
    r₀.length = ℓ.eval n → r₁.length = ℓ.eval n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  /-- Hiding: commitments to any two `n`-bit values are indistinguishable for every `NUPPT`. -/
  hides : ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
      (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r)))
      (D.distinguisherL n) ≤ ε n

/-- Binding in typed form [PS10, Definition 126.3 (1)]: distinct `n`-bit values with any
`ℓ(n)`-bit randomness commit to different strings (used by Lem-127.f). -/
theorem Commitment.binding_ofFn {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {n : ℕ} {v₀ v₁ : Fin n → Bool} (hne : v₀ ≠ v₁)
    (r₀ r₁ : Fin (ℓ.eval n) → Bool) :
    Com (pairEncode (List.ofFn v₀) (List.ofFn r₀)) ≠
      Com (pairEncode (List.ofFn v₁) (List.ofFn r₁)) :=
  hC.binding n _ _ _ _ (List.length_ofFn) (List.length_ofFn) (List.length_ofFn)
    (List.length_ofFn) (fun h => hne (List.ofFn_injective h))

/-! ## The coordinatewise hybrid lemma (concrete content of Claim-126.a) -/

section Hybrids

variable {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] {t : ℕ}

/-- The coordinatewise product of a family of samplers: coordinate `i` is `X i` on the `i`-th
seed, all seeds independent (`copies t X` when all `X i` coincide). -/
def pairTuple (X : Fin t → σ → γ) : (Fin t → σ) → Fin t → γ :=
  fun s i => X i (s i)

/-- The `k`-th hybrid between the products of `X` and `Y`: coordinates `< k` are sampled from
`Y`, the others from `X` [PS10, Lemma 71.6, the hybrids `H_k` of Claim-126.a]. -/
def pairHybrid (X : Fin t → σ → γ) (Y : Fin t → τ → γ) (k : ℕ) :
    (Fin t → σ) × (Fin t → τ) → Fin t → γ :=
  fun s i => if (i : ℕ) < k then Y i (s.2 i) else X i (s.1 i)

/-- The hybrid reduction at coordinate `k`: on a challenge `z` (a sample of `X k` or of `Y k`)
it samples coordinates `< k` from `Y`, coordinates `> k` from `X`, plants `z` at position `k`
and calls `D` once (the reduction of Claim-126.a). -/
def pairRed (X : Fin t → σ → γ) (Y : Fin t → τ → γ) (k : Fin t) (D : (Fin t → γ) → ρ → Bool) :
    γ → ((Fin t → σ) × (Fin t → τ)) × ρ → Bool :=
  fun z c => D (fun i => if (i : ℕ) < k then Y i (c.1.2 i) else if (i : ℕ) = k then z
    else X i (c.1.1 i)) c.2

/-- The zeroth hybrid is the product of `X`. -/
theorem acceptProb_pairHybrid_zero [Nonempty τ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (pairHybrid X Y 0) D = acceptProb (pairTuple X) D := by
  have h : pairHybrid X Y 0 = fun s => pairTuple X s.1 := by
    funext s i; simp [pairHybrid, pairTuple]
  rw [h, acceptProb_fst]

/-- The `t`-th hybrid is the product of `Y`. -/
theorem acceptProb_pairHybrid_self [Nonempty σ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (pairHybrid X Y t) D = acceptProb (pairTuple Y) D := by
  have h : pairHybrid X Y t = fun s => pairTuple Y s.2 := by
    funext s i; simp [pairHybrid, pairTuple, i.isLt]
  rw [h, acceptProb_snd]

/-- On a sample of `X k`, the reduction at `k` simulates the `k`-th hybrid for `D`.

**Proof sketch.** Position `k` holds a sample of `X k` in the `k`-th hybrid; overwriting the
ignored seed at position `k` with the challenge's seed leaves the seed tuple uniform
(`acceptProb_update`), as in `acceptProb_multicopyRed_left`. -/
theorem acceptProb_pairRed_left [Nonempty σ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (k : Fin t) (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (X k) (pairRed X Y k D) = acceptProb (pairHybrid X Y k) D := by
  refine (acceptProb_bind (X k) (fun z (s : (Fin t → σ) × (Fin t → τ)) (i : Fin t) =>
    if (i : ℕ) < k then Y i (s.2 i) else if (i : ℕ) = k then z else X i (s.1 i)) D).trans ?_
  refine Eq.trans ?_ (acceptProb_update (ρ := ρ) k
    (fun u (s' : Fin t → τ) => pairHybrid X Y k (u, s')) D)
  congr 1
  funext w i
  simp only [pairHybrid, Function.update_apply, Fin.ext_iff]
  rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
  · simp [hlt]
  · have hik : i = k := Fin.ext heq
    subst hik
    simp
  · simp [hgt.ne', not_lt.mpr hgt.le]

/-- On a sample of `Y k`, the reduction at `k` simulates the `(k + 1)`-th hybrid for `D`.

**Proof sketch.** As `acceptProb_pairRed_left`: position `k` holds a sample of `Y k` in the
`(k + 1)`-th hybrid (`acceptProb_update` after swapping the two seed vectors). -/
theorem acceptProb_pairRed_right [Nonempty τ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (k : Fin t) (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (Y k) (pairRed X Y k D) = acceptProb (pairHybrid X Y (k + 1)) D := by
  let e : τ × ((Fin t → σ) × (Fin t → τ)) ≃ τ × ((Fin t → τ) × (Fin t → σ)) :=
    (Equiv.refl τ).prodCongr (Equiv.prodComm _ _)
  refine (acceptProb_bind (Y k) (fun z (s : (Fin t → σ) × (Fin t → τ)) (i : Fin t) =>
    if (i : ℕ) < k then Y i (s.2 i) else if (i : ℕ) = k then z else X i (s.1 i)) D).trans ?_
  refine Eq.trans ?_ ((acceptProb_comp_equiv e _ D).trans
    ((acceptProb_update (ρ := ρ) k
      (fun u (s : Fin t → σ) => pairHybrid X Y (k + 1) (s, u)) D).trans
    (acceptProb_comp_equiv (Equiv.prodComm _ _) (pairHybrid X Y (k + 1)) D)))
  congr 1
  funext w i
  simp only [e, pairHybrid, Function.update_apply, Fin.ext_iff, Equiv.prodCongr_apply,
    Equiv.coe_refl, Equiv.prodComm_apply, Prod.map, Prod.fst_swap, Prod.snd_swap, id]
  rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
  · simp [hlt, Nat.lt_succ_of_lt hlt, hlt.ne]
  · have hik : i = k := Fin.ext heq
    subst hik
    simp
  · simp [hgt.ne', not_lt.mpr hgt.le, not_lt.mpr (Nat.succ_le_of_lt hgt)]

/-- **The coordinatewise hybrid lemma** (concrete content of Claim-126.a and Claim-127.d;
[PS10, Lemma 71.6] as in [Gar26, Lemma 3.3]): if `D` distinguishes `(X_1(s_1), …, X_t(s_t))`
from `(Y_1(s_1), …, Y_t(s_t))` with advantage `ε` and `t ≥ 1`, then at some coordinate `k`
`pairRed X Y k D` distinguishes `X k` from `Y k` with advantage `≥ ε / t`
(`exists_multicopyRed_ge` is the case of equal pairs).

**Proof sketch.** `exists_hybrid_gap` on `k ↦ Pr[D(H_k) = 1]`; the ends are the two
products (`acceptProb_pairHybrid_zero/self`) and the reduction at `k` accepts `X k`, `Y k`
with the acceptance probabilities of `H_k`, `H_{k+1}` (`acceptProb_pairRed_left/right`). -/
theorem exists_pairRed_ge [Nonempty σ] [Nonempty τ] (X : Fin t → σ → γ) (Y : Fin t → τ → γ)
    (ht : 0 < t) (D : (Fin t → γ) → ρ → Bool) :
    ∃ k : Fin t, distAdv (pairTuple X) (pairTuple Y) D / t ≤
      distAdv (X k) (Y k) (pairRed X Y k D) := by
  obtain ⟨k, hk, hgap⟩ := exists_hybrid_gap (fun i => acceptProb (pairHybrid X Y i) D) ht
  refine ⟨⟨k, hk⟩, ?_⟩
  unfold distAdv
  rw [acceptProb_pairRed_left, acceptProb_pairRed_right, ← acceptProb_pairHybrid_zero X Y D,
    ← acceptProb_pairHybrid_self X Y D]
  exact hgap

end Hybrids

/-! ## Multi-value hiding (Claim-126.a) -/

/-- A vector of `q` commitments as one string: the right-nested pair encoding
(`Strategy.encodeMsgs`) of the list `Com(v_1, r_1), …, Com(v_q, r_q)` — the form in which the
3-colouring prover sends its commitments ([PS10, Protocol 127.5]). -/
def multiCom (Com : List Bool → List Bool) {q n m : ℕ} (v : Fin q → Fin n → Bool)
    (r : Fin q → Fin m → Bool) : List Bool :=
  Strategy.encodeMsgs (List.ofFn fun i => Com (pairEncode (List.ofFn (v i)) (List.ofFn (r i))))

/-- The advice bound of the multi-value hiding reduction: `3 q(n) (2 C (2n + 3 + ℓ(n))^c + 2) + 2`,
where `C (|x|+1)^c` bounds `|Com x|` — the length of the pair `⟨pre_n, suf_n⟩` of the two
hard-wired strings of commitments (`CommitmentLemmas.length_encodeMsgs_le`). -/
private def multiAdvBound (ℓ q : PolyExpr) (C c : ℕ) : PolyExpr :=
  .add (.mul (.const 3) (.mul q (.add (.mul (.const 2) (.mul (.const C)
    (.pow (.add (.add (.mul (.const 2) .var) (.const 3)) ℓ) c))) (.const 2)))) (.const 2)

/-- Unfolding the advice bound of the multi-value hiding reduction. -/
private theorem multiAdvBound_eval (ℓ q : PolyExpr) (C c n : ℕ) :
    (multiAdvBound ℓ q C c).eval n =
      3 * (q.eval n * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2)) + 2 := rfl

open CommitmentLemmas in
/-- **The per-parameter bound of Claim-126.a**: at each `n` there are two strings `pre`, `suf`
of bounded length and two values `a, a' ∈ {0,1}^n` such that every pair of `q(n)`-vectors of
values is distinguished by `D` with advantage at most `q(n)` times the advantage of the
spliced distinguisher `z ↦ D(1^n, pre ++ ⟨z, suf⟩)` between `Com(a, ·)` and `Com(a', ·)`.

**Proof sketch.** For `t := q(n) = 0` both distributions coincide. Otherwise take a worst pair
`(v, v')` (`Finset.exists_max_image`); `multiCom` is `encodeMsgs ∘ List.ofFn ∘ pairTuple` of
`X i := r ↦ Com ⟨v i, r⟩`, `Y i := r ↦ Com ⟨v' i, r⟩`, so `exists_pairRed_ge` against
`D' := D ∘ encodeMsgs ∘ List.ofFn` gives a coordinate `k`; averaging over the reduction's seed
vectors (`CommitmentLemmas.exists_fixCoins`) fixes them to some `(c_X, c_Y)`, and with the tuple
`W` of fixed commitments the reduction at `k` is `z ↦ D'(update W k z)`, which is
`D(1^n, encodeMsgs (W|_{<k}) ++ ⟨z, encodeMsgs (W|_{>k})⟩)` by
`CommitmentLemmas.encodeMsgs_ofFn_update`; `a := v k`, `a' := v' k`. The length bound is
`CommitmentLemmas.length_encodeMsgs_le` with `|W i| ≤ C (2n + 3 + ℓ(n))^c`. -/
private theorem exists_multiRed_bound {Com : List Bool → List Bool} (ℓ q : PolyExpr) (D : NUPPT)
    {C c : ℕ} (hCc : ∀ x, (Com x).length ≤ C * (x.length + 1) ^ c) (n : ℕ) :
    ∃ (pre suf : List Bool) (a a' : Fin n → Bool),
      2 * pre.length + 2 + suf.length ≤ (multiAdvBound ℓ q C c).eval n ∧
      ∀ v v' : Fin (q.eval n) → Fin n → Bool,
        distAdv (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v r)
          (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v' r)
          (D.distinguisherL n) ≤
        q.eval n * distAdv
          (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn a) (List.ofFn r)))
          (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn a') (List.ofFn r)))
          (fun z c => D.distinguisherL n (pre ++ pairEncode z suf) c) := by
  rw [multiAdvBound_eval]
  set t := q.eval n with ht
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · refine ⟨[], [], fun _ => false, fun _ => false, by simp, fun v v' => ?_⟩
    have hvv : v = v' := funext fun i => absurd i.2 (by omega)
    rw [hvv]
    simp only [distAdv, sub_self, abs_zero]
    positivity
  set cm : (Fin t → Fin n → Bool) → Fin t → (Fin (ℓ.eval n) → Bool) → List Bool :=
    fun v i s => Com (pairEncode (List.ofFn (v i)) (List.ofFn s)) with hcm
  set D' : (Fin t → List Bool) → D.Coins n → Bool :=
    fun w c => D.distinguisherL n (Strategy.encodeMsgs (List.ofFn w)) c with hD'
  have hadv : ∀ v v' : Fin t → Fin n → Bool,
      distAdv (fun r : Fin t → Fin (ℓ.eval n) → Bool => multiCom Com v r)
        (fun r : Fin t → Fin (ℓ.eval n) → Bool => multiCom Com v' r) (D.distinguisherL n) =
      distAdv (pairTuple (cm v)) (pairTuple (cm v')) D' := fun v v' => rfl
  obtain ⟨⟨v, v'⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : (Fin t → Fin n → Bool) × (Fin t → Fin n → Bool) =>
      distAdv (pairTuple (cm p.1)) (pairTuple (cm p.2)) D') Finset.univ_nonempty
  obtain ⟨k, hk⟩ := exists_pairRed_ge (cm v) (cm v') htpos D'
  obtain ⟨c₀, hc₀⟩ := exists_fixCoins (cm v k) (cm v' k) (pairRed (cm v) (cm v') k D')
  set W : Fin t → List Bool :=
    fun i => if (i : ℕ) < k then cm v' i (c₀.2 i) else cm v i (c₀.1 i) with hW
  set pre : List Bool := Strategy.encodeMsgs (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i))
    with hpre
  set suf : List Bool :=
    Strategy.encodeMsgs (List.ofFn fun i : Fin (t - k - 1) => W ⟨k + 1 + i, by omega⟩) with hsuf
  have hred : ∀ z c, pairRed (cm v) (cm v') k D' z (c₀, c) =
      D.distinguisherL n (pre ++ pairEncode z suf) c := by
    intro z c
    have hTz : (fun i : Fin t => if (i : ℕ) < k then cm v' i (c₀.2 i)
        else if (i : ℕ) = k then z else cm v i (c₀.1 i)) = Function.update W k z := by
      funext i
      rw [Function.update_apply]
      simp only [hW]
      rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
      · have hne : i ≠ k := fun hik => by rw [hik] at hlt; exact lt_irrefl _ hlt
        simp [hlt, hne]
      · have : i = k := Fin.ext heq
        subst this
        simp
      · have hne : i ≠ k := fun hik => by rw [hik] at hgt; exact lt_irrefl _ hgt
        simp [hgt.ne', not_lt.mpr hgt.le, hne]
    dsimp only [pairRed]
    simp only [hD']
    rw [hTz, encodeMsgs_ofFn_update]
  have hWlen : ∀ i, (W i).length ≤ C * (2 * n + 3 + ℓ.eval n) ^ c := by
    intro i
    simp only [hW, hcm]
    split_ifs <;>
    · refine (hCc _).trans (le_of_eq ?_)
      rw [length_pairEncode, List.length_ofFn, List.length_ofFn]
      ring_nf
  refine ⟨pre, suf, v k, v' k, ?_, fun v₀ v₁ => ?_⟩
  · have h1 := length_encodeMsgs_le (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i))
      (C * (2 * n + 3 + ℓ.eval n) ^ c) (List.forall_mem_ofFn_iff.2 fun j => hWlen _)
    have h2 := length_encodeMsgs_le (List.ofFn fun i : Fin (t - k - 1) => W ⟨k + 1 + i, by omega⟩)
      (C * (2 * n + 3 + ℓ.eval n) ^ c) (List.forall_mem_ofFn_iff.2 fun j => hWlen _)
    rw [List.length_ofFn] at h1 h2
    have hk1 : (k : ℕ) * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) ≤
        t * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) := Nat.mul_le_mul_right _ k.2.le
    have hk2 : (t - k - 1) * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) ≤
        t * (2 * (C * (2 * n + 3 + ℓ.eval n) ^ c) + 2) := Nat.mul_le_mul_right _ (by omega)
    simp only [hpre, hsuf]
    omega
  · rw [hadv v₀ v₁]
    refine (hmax (v₀, v₁) (Finset.mem_univ _)).trans ?_
    have ht' : (0 : ℝ) < t := Nat.cast_pos.2 htpos
    rw [div_le_iff₀ ht'] at hk
    have h1 : distAdv (pairTuple (cm v)) (pairTuple (cm v')) D' ≤
        t * distAdv (cm v k) (cm v' k) (pairRed (cm v) (cm v') k D') := by linarith
    refine h1.trans (mul_le_mul_of_nonneg_left (hc₀.trans (le_of_eq ?_)) (Nat.cast_nonneg t))
    rw [show (fun z c => pairRed (cm v) (cm v') k D' z (c₀, c)) =
      fun z c => D.distinguisherL n (pre ++ pairEncode z suf) c
      from funext fun z => funext fun c => hred z c]

/-- **Every commitment scheme is multi-value hiding** [PS10, p. 126, "it directly follows by
a simple hybrid argument that any commitment scheme is multi-value secure"] (Claim-126.a):
for a commitment scheme `(Com, ℓ)`, a polynomial `q` and a non-uniform PPT `D` there is a
negligible `ε` such that for every `n` and every two vectors `v, v'` of `q(n)` values of `n`
bits, `D` (at parameter `n`) distinguishes `(Com(v_i, r_i))_i` from `(Com(v'_i, r_i))_i`,
with independent uniform `r_i ∈ {0,1}^{ℓ(n)}`, with advantage at most `ε(n)`.

**Deviation:** the text does not state the notion; this is the analogue of multi-message
security [PS10, Definition 93.1], the vector encoded by `Strategy.encodeMsgs`, values after `ε`.

**Proof sketch.** Fix `D` and let `C (|x|+1)^c` bound `|Com x|` (`hC.easy.output_length_le`).
At each `n`, `exists_multiRed_bound` chooses a worst pair `(v_n, v'_n)`
(`Finset.exists_max_image`), a coordinate `k_n` from the coordinatewise hybrid lemma
`exists_pairRed_ge` applied to `X i := r ↦ Com ⟨v_n i, r⟩`, `Y i := r ↦ Com ⟨v'_n i, r⟩`
against `D' := D.distinguisherL n ∘ encodeMsgs ∘ List.ofFn`, and — by averaging over the
reduction's seed vectors (`CommitmentLemmas.exists_fixCoins`) — a fixed choice of the other
`q(n) − 1` commitments, so that the reduction is `z ↦ D(1^n, pre_n ++ ⟨z, suf_n⟩)` for two
strings `pre_n`, `suf_n` of total length `≤ multiAdvBound` (`CommitmentLemmas.encodeMsgs_ofFn_update`,
`length_encodeMsgs_le`), and `ε_D(n) ≤ q(n) · distAdv (Com ⟨v_n k_n, ·⟩) (Com ⟨v'_n k_n, ·⟩) (that reduction)`.
The machine `B := CommitmentLemmas.exists_pairSpliceRed D pre suf` has `D`'s coins, advice
`⟨⟨pre_n, suf_n⟩, D.advice n⟩` and calls `D` once (`NUPPT.exists_comp`, `NUPPT.exists_withAdvice`);
by coin transport (`CommitmentLemmas.acceptProb_distinguisherL_of_runAtL`) its advantage is the
reduction's, so `hC.hides B` gives `ε_D(n) ≤ q(n) ε_B(n)`, negligible by
`EnsembleLemmas.negligible_polyExpr_mul`; take `ε := q · ε_B`. -/
theorem Commitment.multiHiding {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) (q : PolyExpr) (D : NUPPT) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (v v' : Fin (q.eval n) → Fin n → Bool),
      distAdv (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v r)
        (fun r : Fin (q.eval n) → Fin (ℓ.eval n) → Bool => multiCom Com v' r)
        (D.distinguisherL n) ≤ ε n := by
  obtain ⟨C, c, hCc⟩ := hC.easy.output_length_le
  choose pre suf a a' hlen hkey using exists_multiRed_bound ℓ q D hCc
  obtain ⟨B, hBc, hB⟩ := CommitmentLemmas.exists_pairSpliceRed D pre suf
    (multiAdvBound ℓ q C c) hlen
  obtain ⟨ε, hε, hεB⟩ := hC.hides B
  refine ⟨fun n => q.eval n * ε n, EnsembleLemmas.negligible_polyExpr_mul q hε, fun n v v' => ?_⟩
  refine (hkey n v v').trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  have hε' := hεB n (a n) (a' n)
  unfold distAdv at hε' ⊢
  rwa [CommitmentLemmas.acceptProb_distinguisherL_of_runAtL hBc _
    (fun y => pre n ++ pairEncode y (suf n)) (hB n),
    CommitmentLemmas.acceptProb_distinguisherL_of_runAtL hBc _
    (fun y => pre n ++ pairEncode y (suf n)) (hB n)] at hε'

/-! ## The construction from a one-way permutation [PS10, Theorem 126.4] -/

/-- **The one-bit commitment of [PS10, proof of Theorem 126.4]** (Alg-127.a):
`Com(b, r) = f(r) ‖ (b ⊕ h(r))` for a permutation `f` of `{0,1}^n`, a predicate `h` and
randomness `r ∈ {0,1}^n` (`ℓ(n) = n`), an `(n + 1)`-bit string with the masked bit last
(`owpGen f h` / `owpGenNot f h` of the Garg layer up to the trivial `Unit` coordinate). -/
def bitCom {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool)
    (b : Bool) (r : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.snoc (f r) (xor b (h r))

/-- Unfolding: the first `n` bits of `Com(b, r)` are `f(r)`. -/
@[simp] theorem bitCom_castSucc {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool))
    (h : (Fin n → Bool) → Bool) (b : Bool) (r : Fin n → Bool) (i : Fin n) :
    bitCom f h b r i.castSucc = f r i := by
  simp [bitCom]

/-- Unfolding: the last bit of `Com(b, r)` is `b ⊕ h(r)`. -/
@[simp] theorem bitCom_last {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool))
    (h : (Fin n → Bool) → Bool) (b : Bool) (r : Fin n → Bool) :
    bitCom f h b r (Fin.last n) = xor b (h r) := by
  simp [bitCom]

/-- `Com(0, ·)` is `f(r) ‖ h(r)`. -/
theorem bitCom_false {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool) :
    bitCom f h false = fun r => Fin.snoc (f r) (h r) := by
  funext r; simp [bitCom]

/-- `Com(1, ·)` is `f(r) ‖ ¬h(r)`. -/
theorem bitCom_true {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool) :
    bitCom f h true = fun r => Fin.snoc (f r) (!h r) := by
  funext r; simp [bitCom]

/-- The commitment to `0` is the generator `G(s) = f(s) ‖ h(s)` of [PS10, Theorem 79.4]: the
hiding of Alg-127.a and the pseudorandomness of `owpGenPRG` rest on the same reduction. -/
theorem bitCom_false_eq_owpGenPRG (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (r : Fin n → Bool) (i : Fin (n + 1)) :
    bitCom (P.f n) (h n) false r i = (owpGenPRG P h).G n r i := by
  simp [bitCom, owpGenPRG, PRG.oneBit]

/-- **Binding of the one-bit scheme** [PS10, proof of Theorem 126.4, "it directly follows from
the construction that `Com` is binding"] (Claim-127.b, single bit): `Com(b₀, r₀) = Com(b₁, r₁)`
forces `r₀ = r₁` (the first `n` bits are `f(r)` and `f` is injective) and then `b₀ = b₁`
(`⊕ h(r)` cancels). -/
theorem bitCom_inj {n : ℕ} (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool)
    {b₀ b₁ : Bool} {r₀ r₁ : Fin n → Bool} (heq : bitCom f h b₀ r₀ = bitCom f h b₁ r₁) :
    b₀ = b₁ ∧ r₀ = r₁ := by
  have hf : f r₀ = f r₁ := by
    funext i
    have := congrFun heq i.castSucc
    simpa using this
  have hr : r₀ = r₁ := f.injective hf
  subst hr
  refine ⟨?_, rfl⟩
  have hb := congrFun heq (Fin.last n)
  simp only [bitCom_last] at hb
  cases b₀ <;> cases b₁ <;> cases h r₀ <;> simp_all

/-- **The `n`-bit commitment of [PS10, proof of Theorem 126.4]** (Alg-127.a): "a full-fledged
commitment scheme to a value `v ∈ {0,1}^n` can be obtained by individually committing to each
bit of `v`" — `Com(v, (r_i)_i) = (Com(v_i, r_i))_i`, `n` independent `n`-bit `r_i` (`ℓ(n) = n²`). -/
def owpCom (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (v : Fin n → Bool)
    (r : Fin n → Fin n → Bool) : Fin n → Fin (n + 1) → Bool :=
  fun i => bitCom (P.f n) (h n) (v i) (r i)

/-- The typed `n`-bit scheme is the coordinatewise product of the one-bit schemes to the
bits of `v` (the form `exists_pairRed_ge` applies to). -/
theorem owpCom_eq_pairTuple (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ)
    (v : Fin n → Bool) : owpCom P h n v = pairTuple fun i => bitCom (P.f n) (h n) (v i) := rfl

/-- **Binding of the `n`-bit scheme** (Claim-127.b): equal commitment vectors have equal values
and equal randomness, coordinate by coordinate from `bitCom_inj`. -/
theorem owpCom_inj (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    {v₀ v₁ : Fin n → Bool} {r₀ r₁ : Fin n → Fin n → Bool}
    (heq : owpCom P h n v₀ r₀ = owpCom P h n v₁ r₁) : v₀ = v₁ ∧ r₀ = r₁ := by
  have hi := fun i => bitCom_inj (P.f n) (h n) (congrFun heq i)
  exact ⟨funext fun i => (hi i).1, funext fun i => (hi i).2⟩

/-- The `n`-bit scheme at an explicit parameter `n` on strings: the value is read as `n` bits,
the randomness as `n²` bits (`padFin`, total), the `n` commitments of `n + 1` bits are
concatenated into one `n(n+1)`-bit string (`FunFamily.blocks`). -/
def owpComAt (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (n : ℕ) (v r : List Bool) :
    List Bool :=
  List.ofFn ((FunFamily.blocks n (n + 1)).symm
    (owpCom P h n (padFin n v) (FunFamily.blocks n n (padFin (n * n) r))))

/-- **The string function `Com` of Alg-127.a**: on `⟨v, r⟩` it commits to the `|v|` bits of
`v` with the `|v|²` bits of `r` (`owpComAt` at `n = |v|`); the `Com` of `Commitment`. -/
def owpComStr (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (w : List Bool) : List Bool :=
  owpComAt P h (pairFstD w).length (pairFstD w) (pairSndD w)

/-- The randomness polynomial of Alg-127.a: `ℓ(n) = n · n`. -/
def owpComLen : PolyExpr := .mul .var .var

/-- `ℓ(n) = n²`. -/
@[simp] theorem owpComLen_eval (n : ℕ) : owpComLen.eval n = n * n := rfl

/-- Unfolding `owpComStr` on a well-formed pair. -/
theorem owpComStr_pairEncode (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (v r : List Bool) : owpComStr P h (pairEncode v r) = owpComAt P h v.length v r := by
  simp [owpComStr]

/-- Unfolding `owpComAt` on encoded typed arguments. -/
theorem owpComAt_ofFn (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    (v : Fin n → Bool) (r : Fin (n * n) → Bool) :
    owpComAt P h n (List.ofFn v) (List.ofFn r) =
      List.ofFn ((FunFamily.blocks n (n + 1)).symm (owpCom P h n v (FunFamily.blocks n n r))) := by
  simp [owpComAt, padFin_ofFn]

/-- The string scheme on encoded typed arguments is the encoded typed scheme (the bridge
between the `hides` clause and `owpCom`). -/
theorem owpComStr_ofFn (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    (v : Fin n → Bool) (r : Fin (owpComLen.eval n) → Bool) :
    owpComStr P h (pairEncode (List.ofFn v) (List.ofFn r)) =
      List.ofFn ((FunFamily.blocks n (n + 1)).symm (owpCom P h n v (FunFamily.blocks n n r))) := by
  rw [owpComStr_pairEncode, List.length_ofFn, owpComAt_ofFn]

/-- Two strings of length `n` with the same `n`-bit padding are equal. -/
private theorem padFin_inj {n : ℕ} {v₀ v₁ : List Bool} (hv₀ : v₀.length = n) (hv₁ : v₁.length = n)
    (h : padFin n v₀ = padFin n v₁) : v₀ = v₁ := by
  refine List.ext_getElem (hv₀.trans hv₁.symm) fun i h₁ h₂ => ?_
  have := congrFun h ⟨i, hv₀ ▸ h₁⟩
  simpa [padFin, List.getD_eq_getElem, h₁, h₂] using this

/-- **Binding of `owpComAt`** (Claim-127.b, string form at a parameter): equal commitment
strings of two `n`-bit values force the values to be equal.

**Proof sketch.** `List.ofFn` and the block equivalence are injective, so the typed
commitment vectors agree; `owpCom_inj` gives equal padded values; strings of length `n` with
equal paddings are equal. -/
theorem owpComAt_inj (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) {n : ℕ}
    {v₀ v₁ r₀ r₁ : List Bool} (hv₀ : v₀.length = n) (hv₁ : v₁.length = n)
    (heq : owpComAt P h n v₀ r₀ = owpComAt P h n v₁ r₁) : v₀ = v₁ := by
  have h1 := List.ofFn_injective heq
  have h2 := (FunFamily.blocks n (n + 1)).symm.injective h1
  exact padFin_inj hv₀ hv₁ (owpCom_inj P h h2).1

/-- **Binding of Alg-127.a** [PS10, proof of Theorem 126.4] (Claim-127.b): the binding clause
of `Commitment` for `owpComStr` — for all `n`, distinct `v₀, v₁ ∈ {0,1}^n` and any
`r₀, r₁ ∈ {0,1}^{n²}`, `Com ⟨v₀, r₀⟩ ≠ Com ⟨v₁, r₁⟩`. Only the injectivity of `f` is used. -/
theorem owpComStr_binding (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) :
    ∀ n (v₀ v₁ r₀ r₁ : List Bool), v₀.length = n → v₁.length = n →
      r₀.length = owpComLen.eval n → r₁.length = owpComLen.eval n → v₀ ≠ v₁ →
      owpComStr P h (pairEncode v₀ r₀) ≠ owpComStr P h (pairEncode v₁ r₁) := by
  intro n v₀ v₁ r₀ r₁ hv₀ hv₁ _ _ hne heq
  rw [owpComStr_pairEncode, owpComStr_pairEncode, hv₀, hv₁] at heq
  exact hne (owpComAt_inj P h hv₀ hv₁ heq)

/-! ### Hiding of the one-bit scheme (Claim-127.c) -/

/-- **Single-bit hiding is the predictor reduction** [PS10, proof of Theorem 126.4, "hiding
follows using identically the same proof as in the proof of Theorem 104.4"] (Claim-127.c,
concrete): for every distinguisher `D` between `Com(0, ·) = f(r) ‖ h(r)` and
`Com(1, ·) = f(r) ‖ ¬h(r)` there is a sign `flip` such that `owpPredictorSnoc D flip` (one call
of `D` on `f(r) ‖ σ` for a fresh coin `σ`) predicts `h(r)` from `f(r)` with probability exactly
`1/2 + distAdv(Com(0), Com(1), D) / 2`. Only bijectivity of `f` is used [Gar26, Theorem 3.2].

**Proof sketch.** This is `predProb_owpPredictor_false`/`_true` with `β := Unit`: under the
bijection `(y, (), b) ↦ y ‖ b`, `owpGen f h'` is `Com(0, ·)` and `owpGenNot f h'` is
`Com(1, ·)` (`acceptProb_fst` removes the `Unit` seed coordinate), and the prediction
experiments correspond under `(s, c) ↦ ((s, ()), c)` (`uprob_eq_of_equiv`); choose `flip`
by the sign of `Pr[D(Com(0)) = 1] - Pr[D(Com(1)) = 1]`. -/
theorem exists_bitComPredictor {ρ : Type*} [Fintype ρ] [Nonempty ρ] {n : ℕ}
    (f : (Fin n → Bool) ≃ (Fin n → Bool)) (h : (Fin n → Bool) → Bool)
    (D : (Fin (n + 1) → Bool) → ρ → Bool) :
    ∃ flip : Bool, predProb f h (owpPredictorSnoc D flip) =
      1 / 2 + distAdv (bitCom f h false) (bitCom f h true) D / 2 := by
  let e : (Fin n → Bool) × Unit × Bool ≃ (Fin (n + 1) → Bool) :=
    { toFun := fun z => Fin.snoc z.1 z.2.2
      invFun := fun t => (Fin.init t, (), t (Fin.last n))
      left_inv := fun z => by
        obtain ⟨a, -, b⟩ := z
        simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun t => by simp [Fin.snoc_init_self] }
  have h1 : ∀ flip, predProb f h (owpPredictorSnoc D flip) =
      predProb (owpPair f) (fun w : (Fin n → Bool) × Unit => h w.1)
        (owpPredictor (fun z r => D (e z) r) flip) := fun flip => by
    unfold predProb
    exact uprob_eq_of_equiv
      ({ toFun := fun z : (Fin n → Bool) × (Bool × ρ) => ((z.1, ()), z.2)
         invFun := fun z => (z.1.1, z.2)
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl } :
        (Fin n → Bool) × (Bool × ρ) ≃ ((Fin n → Bool) × Unit) × (Bool × ρ))
      fun _ => Iff.rfl
  have h0 : acceptProb (owpGen f fun w : (Fin n → Bool) × Unit => h w.1) (fun z r => D (e z) r) =
      acceptProb (bitCom f h false) D := by
    rw [bitCom_false, ← acceptProb_fst (τ := Unit) (fun r => Fin.snoc (f r) (h r)) D]
    rfl
  have h0' : acceptProb (owpGenNot f fun w : (Fin n → Bool) × Unit => h w.1)
      (fun z r => D (e z) r) = acceptProb (bitCom f h true) D := by
    rw [bitCom_true, ← acceptProb_fst (τ := Unit) (fun r => Fin.snoc (f r) (!h r)) D]
    rfl
  rcases le_total 0 (acceptProb (bitCom f h false) D - acceptProb (bitCom f h true) D) with
    hs | hs
  · refine ⟨false, ?_⟩
    rw [h1, predProb_owpPredictor_false, h0, h0', distAdv, abs_of_nonneg hs]
  · refine ⟨true, ?_⟩
    rw [h1, predProb_owpPredictor_true, h0, h0', distAdv, abs_of_nonpos hs]
    ring

/-- **Hiding of the one-bit scheme against non-uniform PPTs**: for every `NUPPT` `D` there is
a negligible `ε` such that at every `n`, `D` (at parameter `n`, on the `(n+1)`-bit string)
distinguishes `Com(0, ·)` from `Com(1, ·)` with advantage `≤ ε(n)` [PS10, Def. 126.3 (2)]. -/
def BitHiding (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
    distAdv (bitCom (P.f n) (h n) false) (bitCom (P.f n) (h n) true)
      (D.distinguisher n (n + 1)) ≤ ε n

/-- **A hard-core predicate makes the one-bit scheme hiding** [PS10, proof of Theorem 126.4,
via the proof of Theorem 104.4] (Claim-127.c, asymptotic): if `h` is hard-core for the
permutation family `f`, then `Com(b, r) = f(r) ‖ (b ⊕ h(r))` is hiding — every `NUPPT` has
negligible advantage between `Com(0, ·)` and `Com(1, ·)` (in fact `≤ 2 ε_h(n)` for the
predictor's bound `ε_h`).

**Deviation:** the text's proof goes through the prediction lemma [PS10, Lemma 73.8]; here the
reduction is the exact one of [Gar26, Theorem 3.2] (`exists_bitComPredictor`), with the sign
of the advantage as non-uniform advice.

**Proof sketch.** Fix `D : NUPPT`. At each `n`, `exists_bitComPredictor (P.f n) (h n)
(D.distinguisher n (n+1))` gives a sign `flip_n` (`Classical.choose`) with
`predProb (P.f n) (h n) (owpPredictorSnoc D' flip_n) = 1/2 + distAdv(Com(0), Com(1), D')/2`.
The predictor machine is `owpPredMachine D flip` of `Asymptotic/HardCoreLemmas.lean` (the
machine of Theorem 79.4: advice `⟨[flip_n], D.advice n⟩`, coins `1 + D.coins`; on `⟨1^n, y⟩` it
reads the first coin `σ`, calls `D` once on `⟨1^n, y ++ [σ]⟩` with the remaining coins and
outputs `[xor (if D accepts then σ else !σ) flip_n]`), whose prediction probability is that
of `owpPredictorSnoc (D.distinguisher n (n+1)) (flip n)` (`owpPredMachine_predProb`). Then
`hh.hard A` (note `P.toFunFamily.outLen.eval n = n`) gives a negligible `ε_h` with
`1/2 + distAdv/2 ≤ 1/2 + ε_h n`, hence `distAdv ≤ 2 ε_h n`; take `ε := 2 ε_h`
(`Negligible.const_mul`). -/
theorem HardCore.bitHiding {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool}
    (hh : HardCore P.toFunFamily h) : BitHiding P h := by
  intro D
  have hflip : ∀ n, ∃ flip : Bool,
      predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) flip) =
        1 / 2 + distAdv (bitCom (P.f n) (h n) false) (bitCom (P.f n) (h n) true)
          (D.distinguisher n (n + 1)) / 2 :=
    fun n => exists_bitComPredictor (P.f n) (h n) _
  choose flip hflip using hflip
  obtain ⟨ε, hε, hbound⟩ := hh.hard (owpPredMachine D flip)
  refine ⟨fun n => 2 * ε n, hε.const_mul 2, fun n => ?_⟩
  have h1 : predProb (P.f n) (h n) ((owpPredMachine D flip).predictor n n) ≤ 1 / 2 + ε n :=
    hbound n
  rw [owpPredMachine_predProb] at h1
  have h3 : predProb (P.f n) (h n) (owpPredictorSnoc (D.distinguisher n (n + 1)) (flip n)) =
      predProb (P.f n) (h n) (fun y (c : Bool × D.Coins n) =>
        xor (if D.distinguisher n (n + 1) (Fin.snoc y c.1) c.2 then c.1 else !c.1) (flip n)) := rfl
  rw [← h3, hflip n] at h1
  linarith

/-! ### Hiding of the `n`-bit scheme (Claim-127.d) and Theorem 126.4 -/

open CommitmentLemmas in
/-- **The per-parameter bound of Claim-127.d**: at each `n` there are two strings `pre`, `suf`
of total length `≤ 3n(n+1)` such that every pair of `n`-bit values is distinguished by `D`
with advantage at most `n` times the advantage of the spliced distinguisher
`z ↦ D(1^n, pre ++ z ++ suf)` between `Com(0, ·)` and `Com(1, ·)`.

**Proof sketch.** For `n = 0` there is one value. Otherwise `owpComStr_ofFn` and the seed
reindexing `acceptProb_comp_equiv (blocks n n)` turn the advantage into
`distAdv (pairTuple (bc v₀)) (pairTuple (bc v₁)) D'` with `bc v i := bitCom (f n) (h n) (v i)`
and `D' := D ∘ List.ofFn ∘ (blocks n (n+1)).symm`. Take a worst pair `(v, v')`
(`Finset.exists_max_image`), a bit position `k` from `exists_pairRed_ge`, and by averaging over
the reduction's seed vectors (`CommitmentLemmas.exists_fixCoins`) a fixed choice `(c_X, c_Y)`;
with the tuple `W` of fixed one-bit commitments the reduction at `k` is `z ↦ D'(update W k z)`,
i.e. `D(1^n, pre ++ z ++ suf)` for the block strings before and after `k`
(`CommitmentLemmas.ofFn_blocks_symm_update`, lengths by `length_flatten_ofFn`). If
`v k = v' k` the advantage is `0`; otherwise the pair is `(Com(0), Com(1))` up to
`distAdv_comm`. -/
private theorem exists_bitRed_bound (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool) (D : NUPPT)
    (n : ℕ) :
    ∃ pre suf : List Bool, 2 * pre.length + 2 + suf.length ≤ 3 * (n * (n + 1)) + 2 ∧
      ∀ v₀ v₁ : Fin n → Bool,
        distAdv (fun r : Fin (owpComLen.eval n) → Bool =>
            owpComStr P h (pairEncode (List.ofFn v₀) (List.ofFn r)))
          (fun r : Fin (owpComLen.eval n) → Bool =>
            owpComStr P h (pairEncode (List.ofFn v₁) (List.ofFn r)))
          (D.distinguisherL n) ≤
        n * distAdv (bitCom (P.f n) (h n) false) (bitCom (P.f n) (h n) true)
          (fun z c => D.distinguisherL n (pre ++ List.ofFn z ++ suf) c) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨[], [], by simp, fun v₀ v₁ => ?_⟩
    rw [Subsingleton.elim v₀ v₁]
    simp [distAdv]
  set D' : (Fin n → Fin (n + 1) → Bool) → D.Coins n → Bool :=
    fun w c => D.distinguisherL n (List.ofFn ((FunFamily.blocks n (n + 1)).symm w)) c with hD'
  set bc : (Fin n → Bool) → Fin n → (Fin n → Bool) → Fin (n + 1) → Bool :=
    fun v i => bitCom (P.f n) (h n) (v i) with hbc
  have hadv : ∀ v₀ v₁ : Fin n → Bool,
      distAdv (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₀) (List.ofFn r)))
        (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₁) (List.ofFn r)))
        (D.distinguisherL n) = distAdv (pairTuple (bc v₀)) (pairTuple (bc v₁)) D' := by
    intro v₀ v₁
    simp only [owpComStr_ofFn]
    unfold distAdv
    rw [← acceptProb_comp_equiv (FunFamily.blocks n n) (pairTuple (bc v₀)) D',
      ← acceptProb_comp_equiv (FunFamily.blocks n n) (pairTuple (bc v₁)) D']
    rfl
  obtain ⟨⟨v, v'⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun p : (Fin n → Bool) × (Fin n → Bool) =>
      distAdv (pairTuple (bc p.1)) (pairTuple (bc p.2)) D') Finset.univ_nonempty
  obtain ⟨k, hk⟩ := exists_pairRed_ge (bc v) (bc v') hn D'
  obtain ⟨c₀, hc₀⟩ := exists_fixCoins (bc v k) (bc v' k) (pairRed (bc v) (bc v') k D')
  set W : Fin n → Fin (n + 1) → Bool :=
    fun i => if (i : ℕ) < k then bc v' i (c₀.2 i) else bc v i (c₀.1 i) with hW
  set pre : List Bool := (List.ofFn fun i : Fin k => List.ofFn (W (Fin.castLE k.2.le i))).flatten
    with hpre
  set suf : List Bool :=
    (List.ofFn fun i : Fin (n - k - 1) => List.ofFn (W ⟨k + 1 + i, by omega⟩)).flatten with hsuf
  have hred : ∀ z c, pairRed (bc v) (bc v') k D' z (c₀, c) =
      D.distinguisherL n (pre ++ List.ofFn z ++ suf) c := by
    intro z c
    have hTz : (fun i : Fin n => if (i : ℕ) < k then bc v' i (c₀.2 i)
        else if (i : ℕ) = k then z else bc v i (c₀.1 i)) = Function.update W k z := by
      funext i
      rw [Function.update_apply]
      simp only [hW]
      rcases lt_trichotomy (i : ℕ) k with hlt | heq | hgt
      · have hne : i ≠ k := fun hik => by rw [hik] at hlt; exact lt_irrefl _ hlt
        simp [hlt, hne]
      · have : i = k := Fin.ext heq
        subst this
        simp
      · have hne : i ≠ k := fun hik => by rw [hik] at hgt; exact lt_irrefl _ hgt
        simp [hgt.ne', not_lt.mpr hgt.le, hne]
    dsimp only [pairRed]
    simp only [hD']
    rw [hTz, ofFn_blocks_symm_update]
  refine ⟨pre, suf, ?_, fun v₀ v₁ => ?_⟩
  · simp only [hpre, hsuf]
    rw [length_flatten_ofFn, length_flatten_ofFn]
    have h1 : (k : ℕ) * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right _ k.2.le
    have h2 : (n - k - 1) * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [hadv v₀ v₁]
    refine (hmax (v₀, v₁) (Finset.mem_univ _)).trans ?_
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [div_le_iff₀ hn'] at hk
    have h1 : distAdv (pairTuple (bc v)) (pairTuple (bc v')) D' ≤
        n * distAdv (bc v k) (bc v' k) (pairRed (bc v) (bc v') k D') := by linarith
    refine h1.trans (mul_le_mul_of_nonneg_left (hc₀.trans ?_) (Nat.cast_nonneg n))
    rw [show (fun z c => pairRed (bc v) (bc v') k D' z (c₀, c)) =
      fun z c => D.distinguisherL n (pre ++ List.ofFn z ++ suf) c
      from funext fun z => funext fun c => hred z c]
    simp only [hbc]
    cases v k <;> cases v' k
    · simp only [distAdv, sub_self, abs_zero]; exact abs_nonneg _
    · exact le_rfl
    · rw [distAdv_comm]
    · simp only [distAdv, sub_self, abs_zero]; exact abs_nonneg _

/-- **Hiding of the bitwise scheme by the hybrid lemma** [PS10, proof of Theorem 126.4, "the
security of the full-fledged construction follows as a simple application of the
hybrid lemma (show this!)"] (Claim-127.d): if the one-bit scheme is hiding, the `n`-bit scheme
`owpComStr` satisfies the hiding clause of [PS10, Definition 126.3] — for every `NUPPT` `D`
there is a negligible `ε` with `distAdv(Com⟨v₀, ·⟩, Com⟨v₁, ·⟩, D) ≤ ε(n)` for all `n` and
`v₀, v₁ ∈ {0,1}^n` (the special case of Claim-126.a with `q = n` and single-bit values).

**Proof sketch.** Fix `D`. At each `n`, `exists_bitRed_bound` chooses a worst pair `(v_n, v'_n)`
(`Finset.exists_max_image`), a bit position `k_n` from the coordinatewise hybrid lemma
`exists_pairRed_ge` (after `owpComStr_ofFn`, `distAdv_comp` and the seed reindexing
`acceptProb_comp_equiv (blocks n n)` have turned the two distributions into
`pairTuple (fun i => bitCom (f n) (h n) (v_n i))` and the same for `v'_n`), and — by averaging
over the reduction's seed vectors (`CommitmentLemmas.exists_fixCoins`) — a fixed choice of the
other `n − 1` one-bit commitments, so that the reduction is `z ↦ D(1^n, pre_n ++ z ++ suf_n)`
for two block strings of total length `≤ 3n(n+1)` (`CommitmentLemmas.ofFn_blocks_symm_update`)
and `ε_D(n) ≤ n · distAdv (Com(0)) (Com(1)) (that reduction)` (if `v_n k_n = v'_n k_n` the
advantage is `0`, otherwise up to `distAdv_comm`). The machine
`B := CommitmentLemmas.exists_spliceRed D pre suf` has `D`'s coins, advice
`⟨⟨pre_n, suf_n⟩, D.advice n⟩` and calls `D` once (`NUPPT.exists_comp`,
`NUPPT.exists_withAdvice`); by coin transport (`CommitmentLemmas.acceptProb_distinguisher_of_runAtL`)
its advantage is the reduction's, so `hBit B` gives `ε_D(n) ≤ n ε_B(n)`;
`EnsembleLemmas.negligible_polyExpr_mul` closes with `ε := n · ε_B`. No evaluator of `f` or `h`
is needed: the other commitments are hard-wired, not sampled. -/
theorem BitHiding.owpComStr_hides {P : PermFamily} {h : ∀ n, (Fin n → Bool) → Bool}
    (hBit : BitHiding P h) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
      distAdv (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₀) (List.ofFn r)))
        (fun r : Fin (owpComLen.eval n) → Bool =>
          owpComStr P h (pairEncode (List.ofFn v₁) (List.ofFn r)))
        (D.distinguisherL n) ≤ ε n := by
  intro D
  choose pre suf hlen hkey using exists_bitRed_bound P h D
  obtain ⟨B, hBc, hB⟩ := CommitmentLemmas.exists_spliceRed D pre suf
    (.add (.mul (.const 3) (.mul .var (.add .var (.const 1)))) (.const 2))
    (fun n => by simpa using hlen n)
  obtain ⟨ε, hε, hεB⟩ := hBit B
  refine ⟨fun n => n * ε n, by simpa using EnsembleLemmas.negligible_polyExpr_mul .var hε,
    fun n v₀ v₁ => ?_⟩
  refine (hkey n v₀ v₁).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n))
  have hε' := hεB n
  unfold distAdv at hε' ⊢
  rwa [CommitmentLemmas.acceptProb_distinguisher_of_runAtL hBc _ (fun y => pre n ++ y ++ suf n)
    (hB n), CommitmentLemmas.acceptProb_distinguisher_of_runAtL hBc _
    (fun y => pre n ++ y ++ suf n) (hB n)] at hε'

open CommitmentLemmas in
/-- **The string commitment is the output of the bitwise loop**: for evaluators `F`, `H` of
`f`, `h` on `⟨1^n, x⟩`, `owpComStr P h w = ComLoop.loopOut F H (ComLoop.init w)` for every
string `w` (`n = |fst w|`).

**Proof sketch.** With `v := fst w`, `r := snd w`, `n := |v|` the loop runs from
`⟨1^n, ⟨v, padL (n²) r⟩⟩` for `|init w| + 1 ≥ n` rounds; round `i < n` emits
`F ⟨1^n, r_i⟩ ++ [v[i] ⊕ H ⟨1^n, r_i⟩]` with `r_i` the `i`-th block of `padFin (n²) r`
(`ComLoop.emit_init_of_lt`), which is `List.ofFn (bitCom (f n) (h n) (padFin n v i) r_i)` by
`hF`, `hH` and `ofFn_snoc_eq`, and rounds `i ≥ n` emit nothing (`ComLoop.emit_init_of_le`,
`CommitmentLemmas.flatMap_range_eq_of_nil`); the concatenation of the `n` block strings is
`List.ofFn ((blocks n (n+1)).symm (owpCom …))` (`EnsembleLemmas.ofFn_blocks_symm`), i.e.
`owpComAt P h n v r`. -/
private theorem owpComStr_eq_loopOut (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    {F H : List Bool → List Bool}
    (hFx : ∀ n (x : Fin n → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (P.f n x))
    (hHx : ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x]) (w : List Bool) :
    owpComStr P h w = ComLoop.loopOut F H (ComLoop.init w) := by
  rw [ComLoop.init_eq]
  show owpComAt P h (pairFstD w).length (pairFstD w) (pairSndD w) = _
  generalize pairFstD w = v
  generalize pairSndD w = r
  unfold owpComAt ComLoop.loopOut
  set n := v.length with hn
  set T := owpCom P h n (padFin n v) (FunFamily.blocks n n (padFin (n * n) r)) with hT
  set E : ℕ → List Bool :=
    fun i => ComLoop.emit F H (ComLoop.step^[i] (ComLoop.init (pairEncode v r))) with hE
  have hEi : ∀ i (hi : i < n), E i = List.ofFn (T ⟨i, hi⟩) := by
    intro i hi
    simp only [hE]
    rw [ComLoop.emit_init_of_lt F H hi, hFx, hHx, List.headD_cons, ← ofFn_snoc_eq]
    rfl
  have hb : FunFamily.blocks n (n + 1) = EnsembleLemmas.blocks n (n + 1) := rfl
  rw [hb, EnsembleLemmas.ofFn_blocks_symm T E hEi]
  refine (flatMap_range_eq_of_nil E ?_ fun i hi => ComLoop.emit_init_of_le F H hi).symm
  simp only [ComLoop.init, ComLoop.st, length_pairEncode, pairFstD_pairEncode]
  omega

/-- **`Com` of Alg-127.a is polynomial-time** [PS10, Definition 126.3, "a polynomial-time
machine `Com`"; Theorem 126.4]: if `f` and `h` have polynomial-time evaluators on `⟨1^n, x⟩`
(the efficiency clauses of [PS10, Definitions 27.3 and 78.3]), then `owpComStr` is
polynomial-time computable.

**Proof sketch.** On `w`, read `v := pairFstD w`, form `1^n := 1^{|v|}`
(`polyTimeComputable_unary`), pad/cut `pairSndD w` to `n²` bits
(`EnsembleLemmas.polyTimeComputable_padL`) — the initial state `ComLoop.init w` of the bitwise
commitment loop `CommitmentLemmas.ComLoop` — and run the loop `ComLoop.loopOut F H`
(`polyTimeComputable_iterateEmit`, state `⟨1^n, ⟨v.drop i, rest⟩⟩`: each round drops one value
bit and one `n`-bit block and emits `F ⟨1^n, r_i⟩ ++ [v_i ⊕ H ⟨1^n, r_i⟩]`, nothing once the
value bits are exhausted; `StateLoop.headBit_poly`, `StateLoop.xor_poly`,
`PolyTimeComputable.append`, `pairTakePoly/pairDropPoly`). The result equals `owpComStr P h w`
by `owpComStr_eq_loopOut` (`hF`, `hH`, `List.ofFn` of `(blocks n (n+1)).symm` being the
concatenation of the blocks, and `padFin` matching the padding). -/
theorem owpComStr_polyTimeComputable (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (hF : P.toFunFamily.Easy)
    (hH : ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n (x : Fin n → Bool), H (NUPPT.advInput n (List.ofFn x)) = [h n x]) :
    PolyTimeComputable (owpComStr P h) := by
  obtain ⟨F, hF, hFx⟩ := hF
  obtain ⟨H, hH, hHx⟩ := hH
  convert (CommitmentLemmas.ComLoop.loopOut_poly F H hF hH).comp
    CommitmentLemmas.ComLoop.init_poly using 1
  funext w
  exact owpComStr_eq_loopOut P h hFx hHx w

/-- **Commitment schemes from one-way permutations** [PS10, Theorem 126.4]: if `f` is a
one-way permutation with a hard-core predicate `h`, then `Com(v, (r_i)_i) = (f(r_i) ‖
(v_i ⊕ h(r_i)))_i` (Alg-127.a, `ℓ(n) = n²`) is a commitment scheme: polynomial-time
(`owpComStr_polyTimeComputable`), binding (Claim-127.b, `owpComStr_binding`) and hiding
(Claim-127.c `HardCore.bitHiding` for one bit, Claim-127.d `BitHiding.owpComStr_hides` for `n`
bits).

**Deviation:** the text's hypothesis is "if one-way permutations exist"; its proof uses a
hard-core predicate `h` without stating it (source error 47: [PS10, Theorem 87.3] produces one
for `g(x, r) = (f(x), r)`, not for `f`) and a single permutation family `f` (as in
Theorem 79.4), not the collection of [PS10, Definition 55.1]. Both `OneWayPermutation P` and
`HardCore P.toFunFamily h` are hypotheses here; besides the hard-core property only
`P.toFunFamily.Easy` and the injectivity of `f` are used. -/
theorem owp_commitment (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool)
    (hP : OneWayPermutation P) (hh : HardCore P.toFunFamily h) :
    Commitment (owpComStr P h) owpComLen where
  easy := owpComStr_polyTimeComputable P h hP.easy hh.easy
  binding := owpComStr_binding P h
  hides := hh.bitHiding.owpComStr_hides

/-- **[PS10, Theorem 126.4], existential form**: if there is a one-way permutation with a
hard-core predicate, then commitment schemes exist. -/
theorem exists_commitment_of_owp_hardCore
    (hex : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily h) :
    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ := by
  obtain ⟨P, h, hP, hh⟩ := hex
  exact ⟨owpComStr P h, owpComLen, owp_commitment P h hP hh⟩

end TCSlib.Cryptography
