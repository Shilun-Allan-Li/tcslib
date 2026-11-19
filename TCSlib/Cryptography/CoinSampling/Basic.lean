/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Permutations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coin samplers: decoders from fair coins, exact on success

A *coin sampler* `CoinSampler Ω s` of a finite type `Ω` reads `s` fair coins and either outputs
an element of `Ω` or gives up (`none`), and is **exact on success**: any two elements of `Ω` are
output with the same probability, so that conditioned on success the output is exactly uniform.
This is the shape the library already proves for its rejection-type samplers
(`rejectionSample_uniform_of_some`, `firstHit_uniform_of_some`,
`permFromCoins_uniform_of_some`) and the hypothesis of `statClose_getD_of_uniform_of_some`;
`CoinSampler` names it. The failure probability `fail` is derived, not a field.

The statistical content of "exact on success, fallback on failure" is one exact identity, the
**mixture identity** `uexp_comp_dec`: averaging any `F : Option Ω → ℝ` over the decoded coins is
`fail · F none + (1 − fail) · 𝔼_{a ← Ω} F (some a)`. Its `Option` form `statClose_some` (fallback
branches) and its default-value form `statClose_getD` (the existing lemma, applied) follow.

Non-uniform exact laws are pushforwards of a uniform seed (`LWE.Noise`, the rational seeds of
`CoinSampling.Buckets`), so uniform targets suffice.

## Main definitions

* `CoinSampler Ω s`: a decoder `(Fin s → Bool) → Option Ω`, exact on success.
* `CoinSampler.fail`: the probability of giving up.
* `CoinSampler.congr`, `.reindex`: transport along a bijection of outcomes or of coin strings.
* `CoinSampling.block`, `blockEquiv`: the `n` blocks of `n · s` coins.
* `CoinSampler.pi`, `.prod`: independent draws.
* `CoinSampler.ofRejection`: the library's `rejectionSample` as a coin sampler.

## Main results

* `CoinSampler.uprob_dec_eq_some`: each outcome has probability `(1 − fail)/|Ω|`.
* `CoinSampler.uexp_comp_dec`: the mixture identity.
* `CoinSampler.statClose_some`, `.statClose_getD`: closeness to the exact draw.
* `CoinSampler.fail_pi_le`, `.fail_prod_le`, `.fail_ofRejection`: failure probabilities.
* `CoinSampler.forall_comp_getD`, `.forall_comp_elim`: every-seed properties survive fallbacks.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Lemma 51.17 (a rejection sampler is uniform conditioned on success) and Definition 181.1
  (`ε`-closeness).

**Disclosed overlap (design r1 §6, ruling Q8).** The mixture identity is proved here by the
fibre decomposition that is also the step `hdec` inside the proof of
`statClose_getD_of_uniform_of_some` (`Asymptotic/Sampling.lean`). That file is in the scope of
cleanup Stage 2 (S2-A) and is not edited here; once S2-A lands, the old lemma is to be
re-derived from `uexp_comp_dec` (follow-up in the implementation report).
-/

namespace TCSlib.Cryptography.CoinSampling

open Finset

/-- **Averaging along the fibres of a map**: the average of `F ∘ X` over a uniform seed is
`Σ_b F b · Pr[X = b]`. Glue: Mathlib's `Finset.sum_fiberwise` in `uexp` form (the library has
the event form `uprob_comp_eq_sum_fiber` and the `FinDist` form `uprob_comp_eq_sum_map`, but
no real-valued one). -/
theorem uexp_comp_eq_sum_fiber {Ω' β : Type*} [Fintype Ω'] [Fintype β] [DecidableEq β]
    (X : Ω' → β) (F : β → ℝ) :
    uexp (fun ω => F (X ω)) = ∑ b, F b * uprob (fun ω => X ω = b) := by
  rw [uexp_def, ← Finset.sum_fiberwise univ X (fun ω => F (X ω)), Finset.sum_div]
  refine sum_congr rfl fun b _ => ?_
  rw [uprob_eq_card_filter, Finset.sum_congr rfl (g := fun _ => F b) fun ω hω => by
    rw [(mem_filter.1 hω).2], sum_const, nsmul_eq_mul]
  ring

/-- **An event on one coordinate of a uniform tuple** has the probability of the event:
`Pr_{x ← (ι → α)}[p (x j)] = Pr_{a ← α}[p a]`. Glue: `Equiv.piSplitAt` and `uprob_fst`
(the step used inside `uexp_le_of_statClose`, not published there). -/
theorem uprob_apply_coord {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (j : ι) (p : α → Prop) : uprob (fun x : ι → α => p (x j)) = uprob p := by
  have h := uprob_comp_equiv (Equiv.piSplitAt j fun _ => α) (fun z => p z.1)
  rw [uprob_fst] at h
  exact h

/-- **A coin sampler** of the finite type `Ω` from `s` fair coins: a decoder `dec` from `s`-bit
coin strings to `Option Ω`, where `none` means that the sampler gives up, which is **exact on
success**: any two elements of `Ω` are decoded with the same probability, so that conditioned on
success the output is exactly uniform on `Ω` [PS10, Lemma 51.17] (the property of rejection
sampling, here as a contract; it is the hypothesis `huni` of
`statClose_getD_of_uniform_of_some`). The failure probability is the derived `fail`. -/
structure CoinSampler (Ω : Type) [Fintype Ω] (s : ℕ) where
  /-- The decoder: an element of `Ω`, or `none` when the sampler gives up. -/
  dec : (Fin s → Bool) → Option Ω
  /-- Exact on success: any two elements of `Ω` are decoded with the same probability. -/
  uniform_of_some : ∀ a a' : Ω,
    uprob (fun c => dec c = some a) = uprob (fun c => dec c = some a')

namespace CoinSampler

variable {Ω Ω' : Type} [Fintype Ω] [Fintype Ω'] {s s' : ℕ}

/-- The **failure probability** of `S`: the probability over `s` uniform coins that the decoder
gives up, `fail S = Pr_c[dec c = none]`. -/
noncomputable def fail (S : CoinSampler Ω s) : ℝ :=
  uprob fun c : Fin s → Bool => S.dec c = none

/-- `S.fail = Pr_c[S.dec c = none]`. -/
theorem fail_eq (S : CoinSampler Ω s) :
    S.fail = uprob fun c : Fin s → Bool => S.dec c = none := rfl

/-- A failure probability is nonnegative: `0 ≤ S.fail` (`uprob_nonneg`). -/
theorem fail_nonneg (S : CoinSampler Ω s) : 0 ≤ S.fail := uprob_nonneg _

/-- A failure probability is at most one: `S.fail ≤ 1` (`uprob_le_one`). -/
theorem fail_le_one (S : CoinSampler Ω s) : S.fail ≤ 1 := uprob_le_one _

/-- **The exact conditional law**: every element `a` of the nonempty type `Ω` is decoded with
probability `(1 − fail)/|Ω|`, `Pr_c[dec c = some a] = (1 − S.fail)/|Ω|` [PS10, Lemma 51.17],
abstract form.

**Proof sketch.** The `|Ω| + 1` events `{dec = some a}` and `{dec = none}` partition the coins
(`uprob_comp_eq_sum_fiber`, `Fintype.sum_option`), and the first `|Ω|` have one common value
(`uniform_of_some`), so `|Ω| · Pr[dec = some a] + fail = 1`. -/
theorem uprob_dec_eq_some [Nonempty Ω] (S : CoinSampler Ω s) (a : Ω) :
    uprob (fun c => S.dec c = some a) = (1 - S.fail) / Fintype.card Ω := by
  classical
  have hpart := uprob_comp_eq_sum_fiber S.dec (fun _ => True)
  rw [uprob_true, Finset.filter_true, Fintype.sum_option] at hpart
  have hsum : ∑ b : Ω, uprob (fun c => S.dec c = some b) =
      Fintype.card Ω * uprob (fun c => S.dec c = some a) := by
    rw [Finset.sum_congr rfl fun b _ => S.uniform_of_some b a, sum_const, card_univ,
      nsmul_eq_mul]
  have hG : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [hsum] at hpart
  rw [eq_div_iff hG.ne', fail_eq]
  linarith

/-- **The mixture identity**: averaging any `F : Option Ω → ℝ` over the decoded coins is the
mixture of `F none` with weight `fail` and of the uniform average of `F ∘ some` with weight
`1 − fail`: `𝔼_c F(dec c) = fail · F(none) + (1 − fail) · 𝔼_{a ← Ω} F(some a)`. This exact
identity is the whole statistical content of "exact on success, fallback on failure"
[PS10, Lemma 51.17], abstract form. (Disclosed overlap: the same fibre decomposition is the
step `hdec` of `statClose_getD_of_uniform_of_some`; see the module docstring.)

**Proof sketch.** Group the coin average by the value of `dec` (`uexp_comp_eq_sum_fiber`), split
`Option Ω` into `none` and `some a` (`Fintype.sum_option`), and substitute
`uprob_dec_eq_some`. -/
theorem uexp_comp_dec [Nonempty Ω] (S : CoinSampler Ω s) (F : Option Ω → ℝ) :
    uexp (fun c => F (S.dec c)) =
      S.fail * F none + (1 - S.fail) * uexp (fun a => F (some a)) := by
  classical
  rw [uexp_comp_eq_sum_fiber S.dec F, Fintype.sum_option, ← fail_eq, uexp_def]
  simp_rw [S.uprob_dec_eq_some]
  rw [mul_comm (F none), mul_div_assoc', Finset.mul_sum, Finset.sum_div]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  ring

/-- **The decoder is `fail`-close to the exact draw, failures included**: as samplers of
`Option Ω`, the coin decoder and `some` of a uniform element are `S.fail`-close,
`StatClose S.dec some S.fail` [PS10, Definition 181.1]. This is the `Option` form of
`statClose_getD_of_uniform_of_some` (which is its image under `getD d`), needed when the
fallback is a branch rather than a default value.

**Proof sketch.** For a test set `T` of `Option Ω`, the mixture identity with `F` the indicator
of `T` gives `Pr[T(dec c)] − Pr[T(some a)] = fail · (1_T(none) − Pr_a[T(some a)])`, of absolute
value at most `fail` (both indicator values lie in `[0, 1]`). -/
theorem statClose_some [Nonempty Ω] (S : CoinSampler Ω s) :
    StatClose S.dec (some : Ω → Option Ω) S.fail := by
  classical
  refine (statClose_iff _ _ _).2 fun T => ?_
  rw [uprob_eq_uexp, uprob_eq_uexp (fun a : Ω => T (some a)),
    S.uexp_comp_dec (fun o => if T o then (1 : ℝ) else 0)]
  have hu0 := uprob_nonneg (fun a : Ω => T (some a))
  have hu1 := uprob_le_one (fun a : Ω => T (some a))
  rw [uprob_eq_uexp] at hu0 hu1
  generalize uexp (fun a : Ω => if T (some a) then (1 : ℝ) else 0) = u at hu0 hu1 ⊢
  have hf0 := S.fail_nonneg
  have hf1 := S.fail_le_one
  generalize S.fail = f at hf0 hf1 ⊢
  by_cases hT : T none
  · rw [if_pos hT]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  · rw [if_neg hT]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

/-- **With a default value the decoder is `fail`-close to uniform**:
`StatClose (fun c => (dec c).getD d) id S.fail`. The existing abstract lemma
`statClose_getD_of_uniform_of_some` [PS10, Lemma 51.17], applied as it stands (no re-proof). -/
theorem statClose_getD [DecidableEq Ω] (S : CoinSampler Ω s) (d : Ω) :
    StatClose (fun c => (S.dec c).getD d) (id : Ω → Ω) S.fail :=
  statClose_getD_of_uniform_of_some S.dec S.uniform_of_some (S.fail_eq).ge d

omit [Fintype Ω] [Fintype Ω'] in
/-- `o.map e = some a ↔ o = some (e.symm a)` for a bijection `e`. Glue. -/
theorem option_map_equiv_eq_some_iff (e : Ω ≃ Ω') (o : Option Ω) (a : Ω') :
    o.map e = some a ↔ o = some (e.symm a) := by
  cases o with
  | none => exact ⟨fun h => Option.noConfusion h, fun h => Option.noConfusion h⟩
  | some b =>
    rw [Option.map_some, Option.some_inj, Option.some_inj]
    exact ⟨fun h => h ▸ (e.symm_apply_apply b).symm, fun h => h ▸ e.apply_symm_apply a⟩

/-- **Transport along a bijection** `e : Ω ≃ Ω'`: decode with `S`, then apply `e`. Exact on
success because `e` is a bijection; the failure event is unchanged. Glue. -/
def congr (S : CoinSampler Ω s) (e : Ω ≃ Ω') : CoinSampler Ω' s where
  dec c := (S.dec c).map e
  uniform_of_some a a' := by
    rw [OneWay.uprob_congr fun c => option_map_equiv_eq_some_iff e (S.dec c) a,
      OneWay.uprob_congr fun c => option_map_equiv_eq_some_iff e (S.dec c) a']
    exact S.uniform_of_some _ _

/-- `(S.congr e).dec c = (S.dec c).map e`. -/
theorem congr_dec (S : CoinSampler Ω s) (e : Ω ≃ Ω') (c : Fin s → Bool) :
    (S.congr e).dec c = (S.dec c).map e := rfl

/-- Transport keeps the failure probability: `(S.congr e).fail = S.fail`
(`Option.map_eq_none_iff`). -/
theorem fail_congr (S : CoinSampler Ω s) (e : Ω ≃ Ω') : (S.congr e).fail = S.fail := by
  rw [fail_eq, fail_eq]
  exact OneWay.uprob_congr fun c => by rw [congr_dec, Option.map_eq_none_iff]

/-- **Coins read through a bijection** `e` of coin strings: `(S.reindex e).dec c = S.dec (e c)`.
Exact on success, since a bijection of the coin space preserves `uprob` (`uprob_comp_equiv`).
Glue. -/
def reindex (S : CoinSampler Ω s) (e : (Fin s' → Bool) ≃ (Fin s → Bool)) :
    CoinSampler Ω s' where
  dec c := S.dec (e c)
  uniform_of_some a a' := by
    rw [uprob_comp_equiv e (fun c => S.dec c = some a),
      uprob_comp_equiv e (fun c => S.dec c = some a')]
    exact S.uniform_of_some a a'

/-- `(S.reindex e).dec c = S.dec (e c)`. -/
theorem reindex_dec (S : CoinSampler Ω s) (e : (Fin s' → Bool) ≃ (Fin s → Bool))
    (c : Fin s' → Bool) : (S.reindex e).dec c = S.dec (e c) := rfl

/-- Reindexing keeps the failure probability: `(S.reindex e).fail = S.fail`
(`uprob_comp_equiv`). -/
theorem fail_reindex (S : CoinSampler Ω s) (e : (Fin s' → Bool) ≃ (Fin s → Bool)) :
    (S.reindex e).fail = S.fail :=
  uprob_comp_equiv e (fun c => S.dec c = none)

end CoinSampler

/-- Block `j` of a string of `n · s` coins: the coins at the positions
`finProdFinEquiv (j, i) = i + s·j`, `i < s`. Glue. -/
def block {n s : ℕ} (c : Fin (n * s) → Bool) (j : Fin n) : Fin s → Bool :=
  fun i => c (finProdFinEquiv (j, i))

/-- `block c j i = c (finProdFinEquiv (j, i))`. -/
theorem block_apply {n s : ℕ} (c : Fin (n * s) → Bool) (j : Fin n) (i : Fin s) :
    block c j i = c (finProdFinEquiv (j, i)) := rfl

/-- The **block bijection**: `n · s` coins are `n` blocks of `s` coins (Mathlib's
`finProdFinEquiv`, `Equiv.arrowCongr` and `Equiv.curry`). Glue. -/
def blockEquiv (n s : ℕ) : (Fin (n * s) → Bool) ≃ (Fin n → Fin s → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin n) (Fin s) Bool)

/-- `blockEquiv n s c = block c`. -/
theorem blockEquiv_apply (n s : ℕ) (c : Fin (n * s) → Bool) : blockEquiv n s c = block c := rfl

/-- An event of the blocks has the probability of the event on independent blocks:
`Pr_c[P (block c)] = Pr_b[P b]` (`uprob_comp_equiv` along `blockEquiv`). -/
theorem uprob_block {n s : ℕ} (P : (Fin n → Fin s → Bool) → Prop) :
    uprob (fun c : Fin (n * s) → Bool => P (block c)) = uprob P :=
  uprob_comp_equiv (blockEquiv n s) P

namespace CoinSampler

variable {Ω Ω' : Type} [Fintype Ω] [Fintype Ω'] {s s' : ℕ}

/-- The decoder of `n` independent draws: decode each of the `n` blocks of `n · s` coins with
`S`; `some` of the tuple when every block succeeds, `none` otherwise. Glue. -/
def piDec (n : ℕ) (S : CoinSampler Ω s) (c : Fin (n * s) → Bool) : Option (Fin n → Ω) :=
  if h : ∀ j, (S.dec (block c j)).isSome then some fun j => (S.dec (block c j)).get (h j)
  else none

/-- `piDec n S c` decodes every block, and succeeds iff every block does. -/
theorem piDec_eq (n : ℕ) (S : CoinSampler Ω s) (c : Fin (n * s) → Bool) :
    piDec n S c = if h : ∀ j, (S.dec (block c j)).isSome then
      some fun j => (S.dec (block c j)).get (h j) else none := rfl

/-- The `n`-draw decoder outputs the tuple `f` exactly when every block decodes to its
coordinate: `piDec n S c = some f ↔ ∀ j, S.dec (block c j) = some (f j)`. -/
theorem piDec_eq_some_iff (n : ℕ) (S : CoinSampler Ω s) (c : Fin (n * s) → Bool)
    (f : Fin n → Ω) : piDec n S c = some f ↔ ∀ j, S.dec (block c j) = some (f j) := by
  rw [piDec_eq]
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · rintro rfl j
      exact (Option.some_get (h j)).symm
    · intro hg
      funext j
      exact (Option.eq_some_iff_get_eq.1 (hg j)).2
  · refine ⟨fun h' => by simp at h', fun hg => absurd (fun j => ?_) h⟩
    rw [hg j]
    rfl

/-- The `n`-draw decoder gives up exactly when some block does:
`piDec n S c = none ↔ ∃ j, S.dec (block c j) = none`. -/
theorem piDec_eq_none_iff (n : ℕ) (S : CoinSampler Ω s) (c : Fin (n * s) → Bool) :
    piDec n S c = none ↔ ∃ j, S.dec (block c j) = none := by
  rw [piDec_eq]
  split_ifs with h
  · refine ⟨fun h' => by simp at h', fun ⟨j, hj⟩ => ?_⟩
    have := h j
    rw [hj] at this
    exact absurd this Bool.false_ne_true
  · refine ⟨fun _ => ?_, fun _ => rfl⟩
    push_neg at h
    obtain ⟨j, hj⟩ := h
    exact ⟨j, Option.not_isSome_iff_eq_none.1 hj⟩

/-- **`n` independent draws** as a coin sampler on `Fin n → Ω` from `n · s` coins (`piDec`).
Exact on success, since the blocks of uniform coins are independent (`uprob_block`) and each is
exact on success (`uprob_pi_forall_dep`). Glue. -/
def pi (n : ℕ) (S : CoinSampler Ω s) : CoinSampler (Fin n → Ω) (n * s) where
  dec := piDec n S
  uniform_of_some f f' := by
    rw [OneWay.uprob_congr fun c => piDec_eq_some_iff n S c f,
      OneWay.uprob_congr fun c => piDec_eq_some_iff n S c f',
      uprob_block (fun b => ∀ j, S.dec (b j) = some (f j)),
      uprob_block (fun b => ∀ j, S.dec (b j) = some (f' j)),
      uprob_pi_forall_dep (fun j x => S.dec x = some (f j)),
      uprob_pi_forall_dep (fun j x => S.dec x = some (f' j))]
    exact Finset.prod_congr rfl fun j _ => S.uniform_of_some (f j) (f' j)

/-- `(pi n S).dec = piDec n S`. -/
theorem pi_dec (n : ℕ) (S : CoinSampler Ω s) : (pi n S).dec = piDec n S := rfl

/-- **Union bound for independent draws**: `(pi n S).fail ≤ n · S.fail`.

**Proof sketch.** `piDec_eq_none_iff` and the union bound `uprob_exists_le`; each block event
has probability `S.fail`, since the blocks of uniform coins are independent uniform blocks
(`uprob_block`, `uprob_apply_coord`). -/
theorem fail_pi_le (n : ℕ) (S : CoinSampler Ω s) : (pi n S).fail ≤ n * S.fail := by
  rw [fail_eq, pi_dec, OneWay.uprob_congr fun c => (piDec_eq_none_iff n S c).trans
    (by simp only [Finset.mem_univ, true_and] :
      (∃ j, S.dec (block c j) = none) ↔ ∃ j ∈ (univ : Finset (Fin n)), S.dec (block c j) = none)]
  refine (uprob_exists_le univ fun j c => S.dec (block c j) = none).trans (le_of_eq ?_)
  have hj : ∀ j : Fin n, uprob (fun c : Fin (n * s) → Bool => S.dec (block c j) = none) =
      S.fail := fun j => by
    rw [uprob_block (fun b => S.dec (b j) = none), uprob_apply_coord j
      (fun x => S.dec x = none), fail_eq]
  rw [Finset.sum_congr rfl fun j _ => hj j, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]

/-- **The two halves of uniform coins are an independent uniform pair**:
`Pr_c[P (c↾s, c↾s')] = Pr_{(a, b)}[P (a, b)]` for the first `s` and the last `s'` of `s + s'`
coins (`uprob_comp_equiv` along Mathlib's `Fin.appendEquiv`). Glue. -/
theorem uprob_halves (P : (Fin s → Bool) × (Fin s' → Bool) → Prop) :
    uprob (fun c : Fin (s + s') → Bool =>
      P ((fun i => c (Fin.castAdd s' i)), (fun i => c (Fin.natAdd s i)))) = uprob P :=
  uprob_comp_equiv (Fin.appendEquiv s s').symm P

/-- The decoder of two independent draws: the first `s` coins decoded by `S`, the last `s'`
by `S'`; `some (a, b)` when both succeed. Glue. -/
def prodDec (S : CoinSampler Ω s) (S' : CoinSampler Ω' s') (c : Fin (s + s') → Bool) :
    Option (Ω × Ω') :=
  (S.dec fun i => c (Fin.castAdd s' i)).bind fun a =>
    (S'.dec fun i => c (Fin.natAdd s i)).map fun b => (a, b)

/-- `prodDec S S' c` decodes the two coin blocks and pairs the results. -/
theorem prodDec_eq (S : CoinSampler Ω s) (S' : CoinSampler Ω' s') (c : Fin (s + s') → Bool) :
    prodDec S S' c = (S.dec fun i => c (Fin.castAdd s' i)).bind fun a =>
      (S'.dec fun i => c (Fin.natAdd s i)).map fun b => (a, b) := rfl

/-- The pair decoder outputs `q` exactly when the two halves decode to its coordinates. -/
theorem prodDec_eq_some_iff (S : CoinSampler Ω s) (S' : CoinSampler Ω' s')
    (c : Fin (s + s') → Bool) (q : Ω × Ω') :
    prodDec S S' c = some q ↔ S.dec (fun i => c (Fin.castAdd s' i)) = some q.1 ∧
      S'.dec (fun i => c (Fin.natAdd s i)) = some q.2 := by
  rw [prodDec_eq]
  cases S.dec fun i => c (Fin.castAdd s' i) with
  | none => exact ⟨fun h => Option.noConfusion h, fun h => Option.noConfusion h.1⟩
  | some a =>
    cases S'.dec fun i => c (Fin.natAdd s i) with
    | none => exact ⟨fun h => Option.noConfusion h, fun h => Option.noConfusion h.2⟩
    | some b =>
      rw [Option.bind_some, Option.map_some, Option.some_inj, Option.some_inj,
        Option.some_inj, Prod.ext_iff]

/-- The pair decoder gives up exactly when one of the two draws does. -/
theorem prodDec_eq_none_iff (S : CoinSampler Ω s) (S' : CoinSampler Ω' s')
    (c : Fin (s + s') → Bool) :
    prodDec S S' c = none ↔
      S.dec (fun i => c (Fin.castAdd s' i)) = none ∨
        S'.dec (fun i => c (Fin.natAdd s i)) = none := by
  rw [prodDec_eq]
  cases S.dec fun i => c (Fin.castAdd s' i) with
  | none => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | some a =>
    cases S'.dec fun i => c (Fin.natAdd s i) with
    | none => exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
    | some b =>
      rw [Option.bind_some, Option.map_some]
      exact ⟨fun h => Option.noConfusion h, fun h => h.elim (fun h' => Option.noConfusion h')
        fun h' => Option.noConfusion h'⟩

/-- **Two independent draws** as a coin sampler on `Ω × Ω'` from `s + s'` coins (`prodDec`).
Exact on success: the two halves of uniform coins are an independent uniform pair
(`Fin.appendEquiv`), and `uprob_prod_and` splits the event. Glue. -/
def prod (S : CoinSampler Ω s) (S' : CoinSampler Ω' s') : CoinSampler (Ω × Ω') (s + s') where
  dec := prodDec S S'
  uniform_of_some p p' := by
    have e : ∀ q : Ω × Ω', uprob (fun c => prodDec S S' c = some q) =
        uprob (fun z : (Fin s → Bool) × (Fin s' → Bool) =>
          S.dec z.1 = some q.1 ∧ S'.dec z.2 = some q.2) := fun q => by
      rw [OneWay.uprob_congr fun c => prodDec_eq_some_iff S S' c q]
      exact uprob_halves (fun z => S.dec z.1 = some q.1 ∧ S'.dec z.2 = some q.2)
    rw [e p, e p', HardcoreBit.uprob_prod_and (fun a => S.dec a = some p.1)
      (fun b => S'.dec b = some p.2), HardcoreBit.uprob_prod_and (fun a => S.dec a = some p'.1)
      (fun b => S'.dec b = some p'.2),
      S.uniform_of_some p.1 p'.1, S'.uniform_of_some p.2 p'.2]

/-- `(S.prod S').dec = prodDec S S'`. -/
theorem prod_dec (S : CoinSampler Ω s) (S' : CoinSampler Ω' s') :
    (S.prod S').dec = prodDec S S' := rfl

/-- Union bound for two draws: `(S.prod S').fail ≤ S.fail + S'.fail` (`uprob_or_le`, the
marginals of `Fin.appendEquiv`).

**Proof sketch.** The pair gives up iff one draw does (`prodDec_eq_none_iff`); bound the union
by the sum (`uprob_or_le`); read the two halves of the coins as an independent pair
(`uprob_comp_equiv` along `Fin.appendEquiv`), so each event has its own failure probability
(`uprob_prod_and` with the certain event on the other side). -/
theorem fail_prod_le (S : CoinSampler Ω s) (S' : CoinSampler Ω' s') :
    (S.prod S').fail ≤ S.fail + S'.fail := by
  rw [fail_eq, prod_dec, OneWay.uprob_congr (prodDec_eq_none_iff S S')]
  refine (uprob_or_le _ _).trans (le_of_eq ?_)
  have h₁ := uprob_halves (s := s) (s' := s') (fun z => S.dec z.1 = none ∧ True)
  have h₂ := uprob_halves (s := s) (s' := s') (fun z => True ∧ S'.dec z.2 = none)
  rw [HardcoreBit.uprob_prod_and (fun a => S.dec a = none) (fun _ => True), uprob_true,
    mul_one] at h₁
  rw [HardcoreBit.uprob_prod_and (fun _ => True) (fun b => S'.dec b = none), uprob_true,
    one_mul] at h₂
  rw [fail_eq, fail_eq, ← h₁, ← h₂]
  congr 1
  · exact OneWay.uprob_congr fun c => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  · exact OneWay.uprob_congr fun c => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩

/-- **The library's rejection sampler as a coin sampler**: `rejectionSample m k T` (`T` trials
of `k` bits, the first value below `m`) on the `T` blocks of `T · k` coins. Exact on success is
the existing `rejectionSample_uniform_of_some`, moved along the block bijection
[PS10, Lemma 51.17]. Reuse, not a new sampler. -/
def ofRejection (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) : CoinSampler (Fin m) (T * k) where
  dec c := rejectionSample m k T (block c)
  uniform_of_some a a' := by
    rw [uprob_block (fun b => rejectionSample m k T b = some a),
      uprob_block (fun b => rejectionSample m k T b = some a')]
    exact rejectionSample_uniform_of_some m k T hm hk a a'

/-- `(ofRejection m k T hm hk).dec c = rejectionSample m k T (block c)`. -/
theorem ofRejection_dec (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) (c : Fin (T * k) → Bool) :
    (ofRejection m k T hm hk).dec c = rejectionSample m k T (block c) := rfl

/-- The rejection sampler fails with probability `(1 − m/2^k)^T` [PS10, Lemma 51.17]: the
existing `uprob_rejectionSample_none`, moved along the block bijection. -/
theorem fail_ofRejection (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) :
    (ofRejection m k T hm hk).fail = (1 - (m : ℝ) / 2 ^ k) ^ T := by
  rw [fail_eq, ← uprob_rejectionSample_none m k T hm hk]
  exact uprob_block (fun b => rejectionSample m k T b = none)

/-- **Every-outcome properties survive a default fallback** (seed-function form, for algorithms
written as functions of their exact seed, such as `Regev.keygen`): if `P (f a)` holds for every
seed `a`, it holds for `f ((dec c).getD d)` at every coin string `c`. Glue. -/
theorem forall_comp_getD (S : CoinSampler Ω s) {β : Type} {P : β → Prop} (f : Ω → β) (d : Ω)
    (h : ∀ a, P (f a)) (c : Fin s → Bool) : P (f ((S.dec c).getD d)) :=
  h _

/-- **Every-outcome properties survive a fallback branch that is correct by construction**: if
`P (f a)` holds for every seed `a` and `P fb` holds for the fallback `fb`, then
`P ((dec c).elim fb f)` holds at every coin string `c`. Glue. -/
theorem forall_comp_elim (S : CoinSampler Ω s) {β : Type} {P : β → Prop} (f : Ω → β) (fb : β)
    (h : ∀ a, P (f a)) (hfb : P fb) (c : Fin s → Bool) : P ((S.dec c).elim fb f) := by
  cases S.dec c with
  | none => exact hfb
  | some a => exact h a

end CoinSampler

end TCSlib.Cryptography.CoinSampling
