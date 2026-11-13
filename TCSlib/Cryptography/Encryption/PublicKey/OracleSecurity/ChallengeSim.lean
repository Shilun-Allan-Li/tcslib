/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A deterministic challenge oracle under CPA

Under a chosen-plaintext attack the IND experiment of [PS10, Definition 171.5] has two oracles
in the encoding of `Encryption.PublicKey.OracleSecurity`: a decryption oracle that always
answers all-`false`, and a challenge oracle that answers the first query `⟨m₀, m₁⟩` with a
ciphertext and repeats it afterwards. This file studies that pair of oracles on bit strings of
arbitrary lengths (`bitSpec ins outs`) when the first challenge answer is a deterministic
function `g` of the query, for example once the encryption coins have been sampled in advance.

The run is a pure function of the computation (`chRun`). Its result depends on `g` only through
`g` at the first challenge query (`firstQ`), which does not depend on `g` at all
(`chRun_congr`). This replaces the informal "condition on the adversary's choice of messages"
in the proof of the claim after Definition 171.5. Both the run and the first query transport
along equalities of the length functions (`chRun_toCompOn_transport`), which aligns two codecs
with propositionally equal lengths.

The last section collects sampling identities used to rearrange the expectations of the CPA
reduction: reindexing by an equivalence, products, exchange of order, and singleton types.

## Main definitions

* `Composability.ChallengeSim.chRun g c s`: the run of `c` against the CPA oracles with the
  deterministic challenge answer `g`, from the challenge state `s`.
* `Composability.ChallengeSim.firstQ c`: the first challenge query of `c`, as a list.

## Main results

* `ChallengeSim.chRun_some_congr`: once the challenge is recorded, `g` no longer matters.
* `ChallengeSim.chRun_congr`: the run depends on `g` only at the first challenge query.
* `ChallengeSim.length_of_firstQ_eq_some`: the first challenge query has `ins 1` bits.
* `ChallengeSim.chRun_toCompOn_transport_list`, `ChallengeSim.chRun_toCompOn_transport`: transport
  along equal length functions, with a query-dependent and with a constant answer.
* `ChallengeSim.expect_simulate_eager`: eager challenge coins, for any CPA-shaped oracle.
* `ChallengeSim.expect_sample_prod`: sampling a product is sampling its factors (the other
  sampling identities are `Games.ProbComp`'s).
* `ChallengeSim.expect_indicator_sub`: the case split on the first challenge `(m₀, m₁)`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability.ChallengeSim

open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

variable {ins outs : Fin 2 → ℕ} {α : Type}

/-! ### The deterministic run -/

/-- **The run of `c` against the CPA oracles with the challenge answer `g`**, from the challenge
state `s`: oracle `0` answers all-`false` and keeps the state; oracle `1` answers the first query
`mm` with `padFin (outs 1) (g mm)` and records it, and later repeats the recorded answer. The
result is `c`'s output and the final state. -/
def chRun (g : (Fin (ins 1) → Bool) → List Bool) :
    OracleComp (bitSpec ins outs) α → Option (Fin (outs 1) → Bool) →
      α × Option (Fin (outs 1) → Bool)
  | .pure a, s => (a, s)
  | .query 0 _ k, s => chRun g (k (zeroBits _)) s
  | .query 1 mm k, none => chRun g (k (padFin _ (g mm))) (some (padFin _ (g mm)))
  | .query 1 _ k, some c => chRun g (k c) (some c)

/-- A return ends the run: `chRun g (pure a) s = (a, s)`. -/
theorem chRun_pure (g : (Fin (ins 1) → Bool) → List Bool) (a : α)
    (s : Option (Fin (outs 1) → Bool)) : chRun g (.pure a) s = (a, s) := rfl

/-- A query to oracle `0` is answered all-`false`, keeping the state:
`chRun g (query 0 x k) s = chRun g (k 0) s`. -/
theorem chRun_query_zero (g : (Fin (ins 1) → Bool) → List Bool) (x : Fin (ins 0) → Bool)
    (k : (Fin (outs 0) → Bool) → OracleComp (bitSpec ins outs) α)
    (s : Option (Fin (outs 1) → Bool)) :
    chRun g (.query 0 x k) s = chRun g (k (zeroBits _)) s := rfl

/-- The first challenge query `mm` is answered with `padFin (outs 1) (g mm)`, which is recorded. -/
theorem chRun_query_one_none (g : (Fin (ins 1) → Bool) → List Bool) (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) :
    chRun g (.query 1 mm k) none = chRun g (k (padFin _ (g mm))) (some (padFin _ (g mm))) := rfl

/-- A later challenge query repeats the recorded answer `c`. -/
theorem chRun_query_one_some (g : (Fin (ins 1) → Bool) → List Bool) (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) (c : Fin (outs 1) → Bool) :
    chRun g (.query 1 mm k) (some c) = chRun g (k c) (some c) := rfl

/-- **The first challenge query** of `c` against the CPA oracles, as a list: queries to oracle `0`
are answered all-`false` and skipped; the first query `mm` to oracle `1` gives `List.ofFn mm`; a
computation that returns before it gives `none`. -/
def firstQ : OracleComp (bitSpec ins outs) α → Option (List Bool)
  | .pure _ => none
  | .query 0 _ k => firstQ (k (zeroBits _))
  | .query 1 mm _ => some (List.ofFn mm)

/-- A return asks no challenge: `firstQ (pure a) = none`. -/
theorem firstQ_pure (a : α) : firstQ (ins := ins) (outs := outs) (.pure a) = none := rfl

/-- A query to oracle `0` is skipped: `firstQ (query 0 x k) = firstQ (k 0)`. -/
theorem firstQ_query_zero (x : Fin (ins 0) → Bool)
    (k : (Fin (outs 0) → Bool) → OracleComp (bitSpec ins outs) α) :
    firstQ (.query 0 x k) = firstQ (k (zeroBits _)) := rfl

/-- A query `mm` to oracle `1` is the first challenge: `firstQ (query 1 mm k) = some ⟦mm⟧`. -/
theorem firstQ_query_one (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) :
    firstQ (.query 1 mm k) = some (List.ofFn mm) := rfl

/-- **Once the challenge is recorded, the answer function no longer matters**:
`chRun g c (some C) = chRun g' c (some C)`.

**Proof sketch.** Induction on `c`: from a recorded state both runs answer oracle `0` with
all-`false` and oracle `1` with the recorded `C`, and keep the state. -/
theorem chRun_some_congr (g g' : (Fin (ins 1) → Bool) → List Bool)
    (c : OracleComp (bitSpec ins outs) α) (C : Fin (outs 1) → Bool) :
    chRun g c (some C) = chRun g' c (some C) := by
  induction c with
  | pure a => rfl
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih => rw [chRun_query_zero, chRun_query_zero, ih]
    | 1, x, k, ih => rw [chRun_query_one_some, chRun_query_one_some, ih]

/-- **Eager challenge coins, for any CPA-shaped oracle.** Let `impl` answer oracle `0`
all-`false`, a challenge from a recorded state `c` with `c`, and the first challenge `mm` by
sampling `re` and answering (and recording) `padFin d (g mm re)`; the state holds `d`-bit
strings, `d = outs 1`, read through the cast `e`. Then for every `G`,
`𝔼[G ∘ fst] (simulate impl c s) = 𝔼_{re} G (chRun (fun mm => g mm re) c (s.map (cast e))).1`.

**Proof sketch.** Substitute `d = outs 1`, so that the casts are identities. Induction on the
computation: decryption queries and repeated challenges are deterministic in both; at the first
challenge the lazy side samples `re` and continues from the recorded answer, by the induction
hypothesis an average over coins `re'` on which the recorded run does not depend
(`chRun_some_congr`), so `re'` marginalizes out (`expect_const`). -/
theorem expect_simulate_eager {ins outs : Fin 2 → ℕ} {d : ℕ} (hd : outs 1 = d)
    (e : (Fin d → Bool) = (Fin (outs 1) → Bool)) {R : Type} [Fintype R] [Nonempty R]
    (impl : QueryImpl (bitSpec ins outs) (Option (Fin d → Bool)) unifSpec)
    (g : (Fin (ins 1) → Bool) → R → List Bool)
    (h0 : ∀ x s, impl 0 x s = .pure (zeroBits _, s))
    (hrep : ∀ mm c, impl 1 mm (some c) = .pure (cast e c, some c))
    (hnew : ∀ mm, impl 1 mm none = (ProbComp.sample R).bind fun re =>
      .pure (cast e (padFin d (g mm re)), some (padFin d (g mm re))))
    {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α) (s : Option (Fin d → Bool)) :
    expect (simulate impl c s) (fun p => G p.1) =
      expect (ProbComp.sample R) fun re =>
        G (chRun (fun mm => g mm re) c (s.map (cast e))).1 := by
  subst hd
  have hc : ∀ x : Fin (outs 1) → Bool, cast e x = x := fun x => cast_eq e x
  have hmap : ∀ s : Option (Fin (outs 1) → Bool), s.map (cast e) = s := fun s => by
    cases s <;> simp
  simp only [hc] at hrep hnew
  simp only [hmap]
  induction c generalizing s with
  | pure a =>
    rw [simulate_pure, expect_pure]
    simp only [chRun_pure]
    exact (expect_const _ _).symm
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, h0, OracleComp.pure_bind]
      simp only [chRun_query_zero]
      exact ih _ s
    | 1, x, k, ih =>
      cases s with
      | some C =>
        rw [simulate_query, hrep, OracleComp.pure_bind]
        simp only [chRun_query_one_some]
        exact ih _ _
      | none =>
        rw [simulate_query, hnew, OracleComp.bind_assoc, expect_bind]
        refine congrArg _ (funext fun re => ?_)
        rw [OracleComp.pure_bind, ih, chRun_query_one_none]
        dsimp only
        exact (congrArg _ (funext fun re' =>
          congrArg (fun p : α × Option (Fin (outs 1) → Bool) => G p.1)
            (chRun_some_congr (fun mm => g mm re') (fun mm => g mm re) _ _))).trans
          (expect_const _ _)

/-- **First-challenge congruence:** if `g` and `g'` agree at the first challenge query of `c`
(vacuous when there is none), the runs from the unchallenged state agree:
`chRun g c none = chRun g' c none`.

**Proof sketch.** Induction on `c`. Queries to oracle `0` are answered all-`false` by both runs
and do not change the first challenge query. At the first query `mm` to oracle `1` both runs
record `padFin (g mm) = padFin (g' mm)`, and from then on `chRun_some_congr` applies. -/
theorem chRun_congr (g g' : (Fin (ins 1) → Bool) → List Bool)
    (c : OracleComp (bitSpec ins outs) α)
    (h : ∀ mm : Fin (ins 1) → Bool, firstQ c = some (List.ofFn mm) → g mm = g' mm) :
    chRun g c none = chRun g' c none := by
  induction c with
  | pure a => rfl
  | query i x k ih =>
    match i, x, k, ih, h with
    | 0, x, k, ih, h =>
      rw [chRun_query_zero, chRun_query_zero]
      exact ih _ fun mm hmm => h mm (by rw [firstQ_query_zero]; exact hmm)
    | 1, x, k, ih, h =>
      have hx : g x = g' x := h x (firstQ_query_one x k)
      rw [chRun_query_one_none, chRun_query_one_none, hx]
      exact chRun_some_congr g g' _ _

/-- **The first challenge query has the challenge length**: if `firstQ c = some l` then
`|l| = ins 1`.

**Proof sketch.** Induction on `c`: the first query to oracle `1` is `List.ofFn mm` with
`mm : Fin (ins 1) → Bool`. -/
theorem length_of_firstQ_eq_some (c : OracleComp (bitSpec ins outs) α) {l : List Bool}
    (h : firstQ c = some l) : l.length = ins 1 := by
  induction c with
  | pure a => exact absurd h (by rw [firstQ_pure]; exact Option.noConfusion)
  | query i x k ih =>
    match i, x, k, ih, h with
    | 0, x, k, ih, h =>
      rw [firstQ_query_zero] at h
      exact ih _ h
    | 1, x, k, _, h =>
      rw [firstQ_query_one, Option.some.injEq] at h
      rw [← h, List.length_ofFn]

/-- **Transport of a run with a query-dependent answer along equal lengths:** for a machine
adversary run through `bitCodec`, if `ins = ins'`, `outs = outs'` and `d = d'`, then for every
`G : List Bool → List Bool`,
`List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1`, and
the two runs have the same `firstQ`.

**Proof sketch.** Substitute the equalities; both sides become identical. -/
theorem chRun_toCompOn_transport_list {ins' outs' : Fin 2 → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool)
    (r : A.Coins n) (G : List Bool → List Bool) :
    List.ofFn (chRun (ins := ins) (outs := outs) (fun y => G (List.ofFn y))
        (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
      List.ofFn (chRun (ins := ins') (outs := outs') (fun y => G (List.ofFn y))
        (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
    firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) := by
  subst hi ho hd
  exact ⟨rfl, rfl⟩

/-- **Transport along equal lengths:** for a machine adversary run through `bitCodec`, if
`ins = ins'`, `outs = outs'` and `d = d'`, then
`List.ofFn (chRun (fun _ => w) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
List.ofFn (chRun (fun _ => w) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1` and the
two runs have the same `firstQ`.

**Proof sketch.** `chRun_toCompOn_transport_list` with the constant answer `G = fun _ => w`. -/
theorem chRun_toCompOn_transport {ins' outs' : Fin 2 → ℕ} {d d' : ℕ} (hi : ins = ins')
    (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool) (r : A.Coins n)
    (w : List Bool) :
    List.ofFn (chRun (ins := ins) (outs := outs) (fun _ => w)
        (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
      List.ofFn (chRun (ins := ins') (outs := outs') (fun _ => w)
        (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
    firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) :=
  chRun_toCompOn_transport_list hi ho hd A n q x r fun _ => w

/-! ### Sampling identities -/

section Sampling

variable {β : Type}

/-- **Sampling a product is sampling its factors:**
`𝔼_{(a, b) ← α × β} g (a, b) = 𝔼_{a ← α} 𝔼_{b ← β} g (a, b)`. -/
theorem expect_sample_prod [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (g : α × β → ℝ) :
    expect (sample (α × β)) g = expect (sample α) fun a => expect (sample β) fun b => g (a, b) := by
  rw [← Bridge.expect_sample_pair]
  simp only [expect_bind, expect_pure]

/-- **The pointwise case split of the CPA reduction:** for the first challenge `(m₀, m₁)`, the
difference of the acceptance rates of `A` against `Enc(m₀)` and `Enc(m₁)` equals the difference of
the acceptance rates of the post-processed bit `(m₀ ≠ m₁) ∧ (a ≠ m₀)` against `Enc(0)` and `Enc(1)`.

**Proof sketch.** Four cases. Equal messages give `0 = 0`; `(0, 1)` gives the same difference;
`(1, 0)` gives `(1 − p₀) − (1 − p₁) = p₁ − p₀` for the negated bit. -/
theorem expect_indicator_sub {ρ : Type} [Fintype ρ] [Nonempty ρ] (f : Bool → ρ → Bool)
    (m₀ m₁ : Bool) :
    expect (sample ρ) (fun re => if f m₀ re = true then (1 : ℝ) else 0) -
        expect (sample ρ) (fun re => if f m₁ re = true then (1 : ℝ) else 0) =
      expect (sample ρ)
          (fun re => if ((m₀ != m₁) && (f false re != m₀)) = true then (1 : ℝ) else 0) -
        expect (sample ρ)
          (fun re => if ((m₀ != m₁) && (f true re != m₀)) = true then (1 : ℝ) else 0) := by
  have hneg : ∀ x : Bool, (if (!x) = true then (1 : ℝ) else 0) = 1 - if x = true then 1 else 0 := by
    intro x
    cases x <;> norm_num
  have hf : ∀ x : Bool, (x != false) = x := fun x => by cases x <;> rfl
  have ht : ∀ x : Bool, (x != true) = !x := fun x => by cases x <;> rfl
  cases m₀ <;> cases m₁
  · simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false, expect_const,
      sub_self]
  · simp only [show (false != true) = true from rfl, Bool.true_and, hf]
  · simp only [show (true != false) = true from rfl, Bool.true_and, ht, hneg, expect_sub,
      expect_const]
    ring
  · simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false, expect_const,
      sub_self]

end Sampling

end TCSlib.Cryptography.Composability.ChallengeSim
