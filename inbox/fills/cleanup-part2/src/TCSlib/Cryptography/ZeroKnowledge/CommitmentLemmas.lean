/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.ZeroKnowledge.Interaction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the commitment theorems

The machine constructions and probability bookkeeping behind the theorems of
`TCSlib.Cryptography.ZeroKnowledge.Commitment` [PS10, §4.7.1]: multi-value hiding of a
commitment scheme (Claim-126.a), the hiding of the bitwise scheme of Theorem 126.4
(Claim-127.d) and the polynomial-time evaluator of its `Com` (Alg-127.a). Nothing here mentions
the commitment definitions themselves; the file supplies

* **averaging over a coin factor** (`exists_fixCoins`): for a distinguisher whose coins split as
  `κ × ρ`, some fixed value `c₀` of the first factor has at least the advantage of the
  distinguisher. This is the non-uniform way to run the coordinatewise hybrid reduction
  `pairRed` of Claim-126.a without any sampler: the randomness of the other coordinates is
  hard-wired as advice, so neither hiding theorem needs an efficient evaluator of the scheme
  (the text's "simple hybrid argument" tacitly uses the non-uniformity of [PS10, Definition 126.3]);
* **coin transport** (`acceptProb_distinguisher_of_runAtL`, `acceptProb_distinguisherL_of_runAtL`):
  a machine with `D`'s coins whose activation is `D` on a pre-processed input has the acceptance
  probabilities of the pre-processed distinguisher;
* **splitting a tuple at a position** (`ofFn_update_eq`, `ofFn_blocks_symm_update`,
  `encodeMsgs_ofFn_update`): the block string, respectively the message encoding
  `Strategy.encodeMsgs`, of a tuple with one position replaced by a challenge `z` is a fixed
  prefix, then `z` (respectively the pair `⟨z, ·⟩`), then a fixed suffix;
* **the splice machines** (`exists_spliceRed`, `exists_pairSpliceRed`): the `NUPPT`s that
  plant their argument between two hard-wired strings and call `D` once
  (`Complexity.NUPPT.exists_comp`, `Complexity.NUPPT.exists_withAdvice`);
* **the bitwise commitment loop** (`ComLoop`): the state loop evaluating
  `Com(v, (r_i)_i) = (F ⟨1^n, r_i⟩ ‖ (v_i ⊕ H ⟨1^n, r_i⟩))_i` from evaluators `F`, `H` of `f`, `h`
  (`Complexity.polyTimeComputable_iterateEmit`), with the closed form of its emissions.

## Main definitions

* `TCSlib.Cryptography.CommitmentLemmas.spliceFun`, `pairSpliceFun` — the splice pre-processings.
* `TCSlib.Cryptography.CommitmentLemmas.ComLoop.step`, `ComLoop.emit`, `ComLoop.loopOut`,
  `ComLoop.init` — the bitwise commitment loop.

## Main results

* `TCSlib.Cryptography.CommitmentLemmas.exists_fixCoins` — averaging over a coin factor.
* `TCSlib.Cryptography.CommitmentLemmas.acceptProb_distinguisher_of_runAtL`,
  `acceptProb_distinguisherL_of_runAtL` — coin transport.
* `TCSlib.Cryptography.CommitmentLemmas.ofFn_blocks_symm_update`,
  `encodeMsgs_ofFn_update` — splitting a tuple at a position.
* `TCSlib.Cryptography.CommitmentLemmas.exists_spliceRed`, `exists_pairSpliceRed` — the
  splice machines.
* `TCSlib.Cryptography.CommitmentLemmas.ComLoop.loopOut_poly`, `ComLoop.emit_init_of_lt`,
  `ComLoop.emit_init_of_le` — the loop is polynomial-time and its emissions are the one-bit
  commitments.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7.1: Definition 126.3, Theorem 126.4; §3.1.1: Lemma 71.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.3 (the multicopy hybrid argument).
-/

namespace TCSlib.Cryptography.CommitmentLemmas

open Complexity Turing Finset

/-! ### Averaging over a coin factor -/

/-- Some point of a finite nonempty type carries at least the absolute value of the average:
`|E f| ≤ |f c₀|` for some `c₀` (`Finset.exists_le_of_sum_le` against the constant `|E f|`). -/
theorem exists_abs_uexp_le {κ : Type*} [Fintype κ] [Nonempty κ] (f : κ → ℝ) :
    ∃ c₀, |uexp f| ≤ |f c₀| := by
  have hcard : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hsum : ∑ _c : κ, |uexp f| ≤ ∑ c, |f c| := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, uexp, abs_div, abs_of_pos hcard,
      mul_div_cancel₀ _ hcard.ne']
    exact Finset.abs_sum_le_sum_abs _ _
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨c₀, hc₀⟩

/-- The acceptance probability of a distinguisher with coins `κ × ρ` is the average over the
first coin factor of the acceptance probabilities with that factor fixed (`uprob_prod` after
regrouping the sample space). -/
theorem acceptProb_eq_uexp_fst {σ γ κ ρ : Type*} [Fintype σ] [Fintype κ] [Fintype ρ]
    (X : σ → γ) (D : γ → κ × ρ → Bool) :
    acceptProb X D = uexp fun c₀ => acceptProb X fun z c => D z (c₀, c) := by
  unfold acceptProb
  refine ((uprob_comp_equiv (EnsembleLemmas.swapAux κ σ ρ)
    fun z : σ × (κ × ρ) => D (X z.1) z.2 = true).symm.trans ?_)
  rw [uprob_prod]
  rfl

/-- **Averaging over a coin factor**: for a distinguisher `D` whose coins split as `κ × ρ`,
some fixed value `c₀` of the first factor does at least as well as `D` itself,
`distAdv X Y D ≤ distAdv X Y (D(·, (c₀, ·)))`. This is how a non-uniform reduction hard-wires
the randomness of the other coordinates of a hybrid argument instead of sampling them
([PS10, Definition 26.8], advice).

**Proof sketch.** Both acceptance probabilities are averages over `c₀`
(`acceptProb_eq_uexp_fst`), so the advantage is `|E_{c₀}[a(c₀) − b(c₀)]|`, and some `c₀` has
`|a(c₀) − b(c₀)|` at least the average (`exists_abs_uexp_le`). -/
theorem exists_fixCoins {σ τ γ κ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype κ] [Fintype ρ]
    [Nonempty κ] (X : σ → γ) (Y : τ → γ) (D : γ → κ × ρ → Bool) :
    ∃ c₀ : κ, distAdv X Y D ≤ distAdv X Y fun z c => D z (c₀, c) := by
  obtain ⟨c₀, hc₀⟩ := exists_abs_uexp_le fun c₀ : κ =>
    acceptProb X (fun z c => D z (c₀, c)) - acceptProb Y (fun z c => D z (c₀, c))
  refine ⟨c₀, ?_⟩
  unfold distAdv
  rw [acceptProb_eq_uexp_fst X D, acceptProb_eq_uexp_fst Y D]
  convert hc₀ using 2
  rw [uexp, uexp, uexp, ← sub_div, Finset.sum_sub_distrib]

/-- The distinguishing advantage is symmetric in the two distributions. -/
theorem distAdv_comm {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ) (Y : τ → γ)
    (D : γ → ρ → Bool) : distAdv X Y D = distAdv Y X D :=
  abs_sub_comm _ _

/-! ### Coin transport -/

/-- A machine `B` with `D`'s coins whose activation on `y` is `D`'s on `g y` has, as a typed
distinguisher, the acceptance probabilities of the distinguisher `D(1^n, g ·)` (the coin types
correspond along `B.coins = D.coins`). -/
theorem acceptProb_distinguisher_of_runAtL {σ : Type*} [Fintype σ] {B D : NUPPT}
    (hc : B.coins = D.coins) {n m : ℕ} (X : σ → Fin m → Bool) (g : List Bool → List Bool)
    (hrun : ∀ y r, B.runAtL n y r = D.runAtL n (g y) r) :
    acceptProb X (B.distinguisher n m) =
      acceptProb X fun z c => D.distinguisherL n (g (List.ofFn z)) c := by
  have hlen : D.coinLen n = B.coinLen n := by simp [NUPPT.coinLen, hc]
  let e : D.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← EnsembleLemmas.acceptProb_coins_equiv e]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisher, NUPPT.distinguisherL, NUPPT.runAt_eq, hofn, hrun]

/-- As `acceptProb_distinguisher_of_runAtL`, for untyped samples. -/
theorem acceptProb_distinguisherL_of_runAtL {σ : Type*} [Fintype σ] {B D : NUPPT}
    (hc : B.coins = D.coins) {n : ℕ} (X : σ → List Bool) (g : List Bool → List Bool)
    (hrun : ∀ y r, B.runAtL n y r = D.runAtL n (g y) r) :
    acceptProb X (B.distinguisherL n) = acceptProb X fun z c => D.distinguisherL n (g z) c := by
  have hlen : D.coinLen n = B.coinLen n := by simp [NUPPT.coinLen, hc]
  let e : D.Coins n ≃ B.Coins n := Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)
  rw [← EnsembleLemmas.acceptProb_coins_equiv e]
  congr 1
  funext z c
  have hofn : List.ofFn (e c) = List.ofFn c := (List.ofFn_congr hlen c).symm
  simp only [NUPPT.distinguisherL, NUPPT.runAt_eq, hofn, hrun]

/-! ### Splitting a tuple at a position -/

/-- Splitting `List.ofFn F` at position `j`: the first `j` entries, the entry `j`, the rest
(`List.ext_getElem` with `List.getElem_append`, `List.getElem_cons`; private copy of
`ofFn_eq_append_cons` of `Asymptotic/PublicKeyLemmas.lean`, which this file does not import). -/
theorem ofFn_eq_append_cons {α : Type*} {N : ℕ} (F : Fin N → α) (j : Fin N) :
    List.ofFn F = (List.ofFn fun i : Fin j => F (Fin.castLE j.2.le i)) ++
      F j :: List.ofFn fun i : Fin (N - j - 1) => F ⟨j + 1 + i, by omega⟩ := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons]
    omega
  · intro t h1 h2
    rw [List.getElem_append]
    simp only [List.length_ofFn]
    split_ifs with h
    · simp only [List.getElem_ofFn]
      congr 1
    · rw [List.getElem_cons]
      split_ifs with h'
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)

/-- `List.ofFn (update W k z)` is the entries before `k`, then `z`, then the entries after `k`.

**Proof sketch.** `ofFn_eq_append_cons` splits `List.ofFn (update W k z)` at `k`; the entry at
`k` is `z` (`Function.update_self`) and the entries before and after `k` are those of `W`
(`Function.update_of_ne`, the indices `castLE i < k` and `k + 1 + i` differing from `k`). -/
theorem ofFn_update_eq {α : Type*} {N : ℕ} (W : Fin N → α) (k : Fin N) (z : α) :
    List.ofFn (Function.update W k z) = (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i)) ++
      z :: List.ofFn fun i : Fin (N - k - 1) => W ⟨k + 1 + i, by omega⟩ := by
  rw [ofFn_eq_append_cons (Function.update W k z) k, Function.update_self]
  have h₁ : ∀ i : Fin k, Function.update W k z (Fin.castLE k.2.le i) = W (Fin.castLE k.2.le i) := by
    intro i
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    have hi := i.2
    simp only [Fin.coe_castLE] at hv
    omega
  have h₂ : ∀ i : Fin (N - k - 1),
      Function.update W k z ⟨k + 1 + i, by omega⟩ = W ⟨k + 1 + i, by omega⟩ := by
    intro i
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega
  simp only [h₁, h₂]

/-- The concatenation of `j` strings of `L` bits has `j · L` bits. -/
theorem length_flatten_ofFn {j L : ℕ} (f : Fin j → Fin L → Bool) :
    (List.ofFn fun i => List.ofFn (f i)).flatten.length = j * L := by
  simp [List.length_flatten, List.sum_ofFn]

/-- The block string of a tuple with block `k` replaced by `z`: the blocks before `k`, then
`z`, then the blocks after `k` (`FunFamily.ofFn_blocks_symm`, `ofFn_update_eq`). -/
theorem ofFn_blocks_symm_update {q ℓ : ℕ} (W : Fin q → Fin ℓ → Bool) (k : Fin q)
    (z : Fin ℓ → Bool) :
    List.ofFn ((FunFamily.blocks q ℓ).symm (Function.update W k z)) =
      (List.ofFn fun i : Fin k => List.ofFn (W (Fin.castLE k.2.le i))).flatten ++ List.ofFn z ++
        (List.ofFn fun i : Fin (q - k - 1) => List.ofFn (W ⟨k + 1 + i, by omega⟩)).flatten := by
  rw [FunFamily.ofFn_blocks_symm]
  have h2 : (fun i => List.ofFn (Function.update W k z i)) =
      Function.update (fun i => List.ofFn (W i)) k (List.ofFn z) := by
    funext i
    by_cases hi : i = k
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [h2, ofFn_update_eq, List.flatten_append, List.flatten_cons, List.append_assoc]

/-- The encoding of a concatenated history is the concatenation of the encodings
(`pairEncode a (b ++ c) = pairEncode a b ++ c`). -/
theorem encodeMsgs_append (L M : List (List Bool)) :
    Strategy.encodeMsgs (L ++ M) = Strategy.encodeMsgs L ++ Strategy.encodeMsgs M := by
  induction L with
  | nil => rfl
  | cons m L ih => simp [ih, pairEncode, List.append_assoc]

/-- The encoding of a history of messages of length `≤ M` has length at most
`|L| · (2M + 2)` (`length_pairEncode`). -/
theorem length_encodeMsgs_le (L : List (List Bool)) (M : ℕ) (hM : ∀ m ∈ L, m.length ≤ M) :
    (Strategy.encodeMsgs L).length ≤ L.length * (2 * M + 2) := by
  induction L with
  | nil => simp
  | cons m L ih =>
    have h1 := hM m (by simp)
    have h2 := ih fun m' hm' => hM m' (by simp [hm'])
    rw [Strategy.encodeMsgs_cons, length_pairEncode, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The encoding of a tuple with position `k` replaced by `z`: the encoding of the entries
before `k`, then the pair `⟨z, ·⟩` around the encoding of the entries after `k`
(`ofFn_update_eq`, `encodeMsgs_append`). -/
theorem encodeMsgs_ofFn_update {N : ℕ} (W : Fin N → List Bool) (k : Fin N) (z : List Bool) :
    Strategy.encodeMsgs (List.ofFn (Function.update W k z)) =
      Strategy.encodeMsgs (List.ofFn fun i : Fin k => W (Fin.castLE k.2.le i)) ++
        pairEncode z (Strategy.encodeMsgs
          (List.ofFn fun i : Fin (N - k - 1) => W ⟨k + 1 + i, by omega⟩)) := by
  rw [ofFn_update_eq, encodeMsgs_append, Strategy.encodeMsgs_cons]

/-- Chunks that are empty from index `n` on do not contribute: the concatenation over
`range m` equals the one over `range n` for `n ≤ m`. -/
theorem flatMap_range_eq_of_nil (F : ℕ → List Bool) {n m : ℕ} (hnm : n ≤ m)
    (hF : ∀ i, n ≤ i → F i = []) : (List.range m).flatMap F = (List.range n).flatMap F := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [List.range_add, List.flatMap_append, List.flatMap_map]
  have h : (List.range d).flatMap (fun a => F (n + a)) = [] :=
    List.flatMap_eq_nil_iff.2 fun x _ => hF _ (Nat.le_add_right n x)
  rw [h, List.append_nil]

/-- The head of a dropped list is the element at the dropping index (`List.getD`). -/
theorem headD_drop (l : List Bool) (i : ℕ) (d : Bool) : (l.drop i).headD d = l.getD i d := by
  rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]

/-! ### The splice machines -/

/-- The splice pre-processing on the argument `⟨z, ⟨pre, suf⟩⟩`: `pre ++ z ++ suf`. -/
def spliceFun (y : List Bool) : List Bool :=
  pairFstD (pairSndD y) ++ pairFstD y ++ pairSndD (pairSndD y)

/-- The splice pre-processing is polynomial-time. -/
theorem spliceFun_poly : PolyTimeComputable spliceFun :=
  ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).append
    polyTimeComputable_pairFstD).append
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The splice pre-processing on a well-formed argument. -/
@[simp] theorem spliceFun_pairEncode (z pre suf : List Bool) :
    spliceFun (pairEncode z (pairEncode pre suf)) = pre ++ z ++ suf := by
  simp [spliceFun]

/-- The pair-splice pre-processing on the argument `⟨z, ⟨pre, suf⟩⟩`: `pre ++ ⟨z, suf⟩`. -/
def pairSpliceFun (y : List Bool) : List Bool :=
  pairFstD (pairSndD y) ++ pairEncode (pairFstD y) (pairSndD (pairSndD y))

/-- The pair-splice pre-processing is polynomial-time. -/
theorem pairSpliceFun_poly : PolyTimeComputable pairSpliceFun :=
  (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).append
    (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-- The pair-splice pre-processing on a well-formed argument. -/
@[simp] theorem pairSpliceFun_pairEncode (z pre suf : List Bool) :
    pairSpliceFun (pairEncode z (pairEncode pre suf)) = pre ++ pairEncode z suf := by
  simp [pairSpliceFun]

/-- **The splice machine**: for an `NUPPT` `D` and polynomially bounded strings `pre n`, `suf n`
there is an `NUPPT` `B` with `D`'s coins computing `D(1^n, pre n ++ y ++ suf n; r)`
(`Complexity.NUPPT.exists_comp` with `spliceFun`, then `Complexity.NUPPT.exists_withAdvice`
hard-wiring `⟨pre n, suf n⟩`). -/
theorem exists_spliceRed (D : NUPPT) (pre suf : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, 2 * (pre n).length + 2 + (suf n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = D.coins ∧ ∀ n y r, B.runAtL n y r = D.runAtL n (pre n ++ y ++ suf n) r := by
  obtain ⟨B₁, hB₁c, -, -, hB₁⟩ := D.exists_comp spliceFun_poly polyTimeComputable_id
  obtain ⟨B, hBc, hB⟩ := B₁.exists_withAdvice (fun n => pairEncode (pre n) (suf n)) b
    (fun n => by rw [length_pairEncode]; exact hb n)
  refine ⟨B, hBc.trans hB₁c, fun n y r => ?_⟩
  rw [hB, hB₁, spliceFun_pairEncode]
  rfl

/-- **The pair-splice machine**: as `exists_spliceRed`, computing
`D(1^n, pre n ++ ⟨y, suf n⟩; r)` (the argument planted as a message of an encoded history). -/
theorem exists_pairSpliceRed (D : NUPPT) (pre suf : ℕ → List Bool) (b : PolyExpr)
    (hb : ∀ n, 2 * (pre n).length + 2 + (suf n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = D.coins ∧
      ∀ n y r, B.runAtL n y r = D.runAtL n (pre n ++ pairEncode y (suf n)) r := by
  obtain ⟨B₁, hB₁c, -, -, hB₁⟩ := D.exists_comp pairSpliceFun_poly polyTimeComputable_id
  obtain ⟨B, hBc, hB⟩ := B₁.exists_withAdvice (fun n => pairEncode (pre n) (suf n)) b
    (fun n => by rw [length_pairEncode]; exact hb n)
  refine ⟨B, hBc.trans hB₁c, fun n y r => ?_⟩
  rw [hB, hB₁, pairSpliceFun_pairEncode]
  rfl

/-! ### The bitwise commitment loop -/

namespace ComLoop

/-- The unary parameter slot `u` of the state word `⟨u, ⟨vs, rs⟩⟩`. -/
def p₁ (w : List Bool) : List Bool := pairFstD w

/-- The remaining value bits `vs` of the state word. -/
def p₂ (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The remaining randomness `rs` of the state word. -/
def p₃ (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- The state word `⟨u, ⟨vs, rs⟩⟩`. -/
def st (u vs rs : List Bool) : List Bool := pairEncode u (pairEncode vs rs)

/-- Reading the parameter slot. -/
@[simp] theorem p₁_st (u vs rs : List Bool) : p₁ (st u vs rs) = u := by simp [p₁, st]

/-- Reading the value bits. -/
@[simp] theorem p₂_st (u vs rs : List Bool) : p₂ (st u vs rs) = vs := by simp [p₂, st]

/-- Reading the randomness. -/
@[simp] theorem p₃_st (u vs rs : List Bool) : p₃ (st u vs rs) = rs := by simp [p₃, st]

/-- The projections are polynomial-time. -/
theorem p₁_poly : PolyTimeComputable p₁ := polyTimeComputable_pairFstD

/-- The projections are polynomial-time. -/
theorem p₂_poly : PolyTimeComputable p₂ :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The projections are polynomial-time. -/
theorem p₃_poly : PolyTimeComputable p₃ :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- Assembling a state word from three polynomial-time components is polynomial-time. -/
theorem st_poly {f₁ f₂ f₃ : List Bool → List Bool} (h₁ : PolyTimeComputable f₁)
    (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃) :
    PolyTimeComputable fun z => st (f₁ z) (f₂ z) (f₃ z) :=
  h₁.pairEncode (h₂.pairEncode h₃)

/-- The evaluators' argument at a state word: `⟨u, rs.take |u|⟩`, i.e. `⟨1^n, r_i⟩` for the
current randomness block. -/
def arg (w : List Bool) : List Bool := pairEncode (p₁ w) ((p₃ w).take (p₁ w).length)

/-- The argument is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly` on
`⟨u, rs⟩`). -/
theorem arg_poly : PolyTimeComputable arg := by
  convert p₁_poly.pairEncode
    ((polyTimeComputable_pairTakePoly .var).comp (p₁_poly.pairEncode p₃_poly)) using 1
  funext w
  simp [arg]

/-- The step: drop the first value bit and the first `|u|` randomness bits. -/
def step (w : List Bool) : List Bool := st (p₁ w) (p₂ w).tail ((p₃ w).drop (p₁ w).length)

/-- The step is polynomial-time (`StateLoop.tail_poly`,
`Complexity.polyTimeComputable_pairDropPoly` on `⟨u, rs⟩`). -/
theorem step_poly : PolyTimeComputable step := by
  convert st_poly p₁_poly (StateLoop.tail_poly.comp p₂_poly)
    ((polyTimeComputable_pairDropPoly .var).comp (p₁_poly.pairEncode p₃_poly)) using 1
  funext w
  simp [step]

/-- One step grows a word by at most four symbols (the pairing overhead; both components
only shrink). -/
theorem length_step_le (w : List Bool) : (step w).length ≤ w.length + 4 := by
  have h₁ := EnsembleLemmas.CopiesLoop.two_mul_length_pairFstD_add_le w
  have h₂ := EnsembleLemmas.CopiesLoop.two_mul_length_pairFstD_add_le (pairSndD w)
  simp only [step, st, length_pairEncode, List.length_tail, List.length_drop, p₁, p₂, p₃]
  omega

/-- The orbit of any word grows at most linearly in the number of rounds. -/
theorem length_iterate_step_le (w : List Bool) (i : ℕ) :
    (step^[i] w).length ≤ w.length + 4 * i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := length_step_le (step^[i] w)
    omega

/-- The closed form of the orbit from `⟨u, ⟨vs, rs⟩⟩`: after `i` rounds the state word is
`⟨u, ⟨vs.drop i, rs.drop (i · |u|)⟩⟩`. -/
theorem iterate_step (u vs rs : List Bool) (i : ℕ) :
    step^[i] (st u vs rs) = st u (vs.drop i) (rs.drop (i * u.length)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, p₁_st, p₂_st, p₃_st, List.tail_drop, List.drop_drop]
    congr 2
    ring

variable (F H : List Bool → List Bool)

/-- The emission at a state word: nothing once the value bits are exhausted, else the one-bit
commitment `F ⟨u, r_i⟩ ++ [v_i ⊕ H ⟨u, r_i⟩]` of the current value bit with the current block
(Alg-127.a). -/
def emit (w : List Bool) : List Bool :=
  if p₂ w = [] then [] else F (arg w) ++ [xor ((p₂ w).headD false) ((H (arg w)).headD false)]

/-- The emission is polynomial-time (`Complexity.polyTimeComputable_ite` on the emptiness test
`StateLoop.isNil_poly`, `StateLoop.headBit_poly`, `StateLoop.xor_poly`,
`PolyTimeComputable.append`). -/
theorem emit_poly (hF : PolyTimeComputable F) (hH : PolyTimeComputable H) :
    PolyTimeComputable (emit F H) := by
  convert polyTimeComputable_ite (StateLoop.isNil_poly.comp p₂_poly) (polyTimeComputable_const [])
    ((hF.comp arg_poly).append (StateLoop.xor_poly (StateLoop.headBit_poly.comp p₂_poly)
      (StateLoop.headBit_poly.comp (hH.comp arg_poly)))) using 1
  funext w
  simp [emit]

/-- The loop output: the emissions along the `|x| + 1` rounds from `x`, concatenated. -/
def loopOut (x : List Bool) : List Bool :=
  (List.range (x.length + 1)).flatMap fun i => emit F H (step^[i] x)

/-- The loop output is polynomial-time (`Complexity.polyTimeComputable_iterateEmit` with the
orbit bound `|x| + 4 |x| = 5 |x|`). -/
theorem loopOut_poly (hF : PolyTimeComputable F) (hH : PolyTimeComputable H) :
    PolyTimeComputable (loopOut F H) := by
  unfold loopOut
  refine polyTimeComputable_iterateEmit step_poly (emit_poly F H hF hH) .var (.mul (.const 5) .var)
    fun x i hi => ?_
  have := length_iterate_step_le x i
  simp only [PolyExpr.eval_var] at hi
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  omega

/-- The initial state from the argument `⟨v, r⟩`: `⟨1^{|v|}, ⟨v, padL (|v|²) r⟩⟩` (the
randomness padded or cut to `|v|²` bits, as `padFin` does). -/
def init (w : List Bool) : List Bool :=
  st (List.replicate (pairFstD w).length true) (pairFstD w)
    (EnsembleLemmas.padL ((pairFstD w).length * (pairFstD w).length) (pairSndD w))

/-- The initial state is polynomial-time (`Complexity.polyTimeComputable_unary`,
`EnsembleLemmas.polyTimeComputable_padL`). -/
theorem init_poly : PolyTimeComputable init := by
  convert st_poly (polyTimeComputable_unary.comp polyTimeComputable_pairFstD)
    polyTimeComputable_pairFstD (EnsembleLemmas.polyTimeComputable_padL (.mul .var .var)
      polyTimeComputable_pairFstD polyTimeComputable_pairSndD) using 1

/-- The initial state only depends on the two components of the argument. -/
theorem init_eq (w : List Bool) : init w = init (pairEncode (pairFstD w) (pairSndD w)) := by
  simp [init]

/-- Once the value bits are exhausted (round `i ≥ |v|`), the loop emits nothing. -/
theorem emit_init_of_le {v r : List Bool} {i : ℕ} (hi : v.length ≤ i) :
    emit F H (step^[i] (init (pairEncode v r))) = [] := by
  simp [init, iterate_step, emit, List.drop_eq_nil_of_le hi]

/-- At round `i < |v|` the loop emits the one-bit commitment of the bit `v[i]` with the `i`-th
block of the padded randomness: `F ⟨1^n, r_i⟩ ++ [v[i] ⊕ (H ⟨1^n, r_i⟩)[0]]` with
`r_i = blocks n n (padFin (n²) r) i`, `n = |v|` (`EnsembleLemmas.take_drop_ofFn_blocks`). -/
theorem emit_init_of_lt {v r : List Bool} {i : ℕ} (hi : i < v.length) :
    emit F H (step^[i] (init (pairEncode v r))) =
      F (NUPPT.advInput v.length (List.ofFn (EnsembleLemmas.blocks v.length v.length
        (padFin (v.length * v.length) r) ⟨i, hi⟩))) ++
      [xor (v.getD i false) ((H (NUPPT.advInput v.length (List.ofFn (EnsembleLemmas.blocks
        v.length v.length (padFin (v.length * v.length) r) ⟨i, hi⟩)))).headD false)] := by
  have hne : v.drop i ≠ [] := by
    rw [Ne, List.drop_eq_nil_iff]
    omega
  have hblock : ((EnsembleLemmas.padL (v.length * v.length) r).drop (i * v.length)).take v.length =
      List.ofFn (EnsembleLemmas.blocks v.length v.length (padFin (v.length * v.length) r) ⟨i, hi⟩) :=
    EnsembleLemmas.take_drop_ofFn_blocks (padFin (v.length * v.length) r) i hi
  simp only [init, pairFstD_pairEncode, pairSndD_pairEncode, iterate_step, List.length_replicate,
    emit, arg, p₁_st, p₂_st, p₃_st, hne, if_false, hblock, NUPPT.advInput, headD_drop]

end ComLoop

end TCSlib.Cryptography.CommitmentLemmas
