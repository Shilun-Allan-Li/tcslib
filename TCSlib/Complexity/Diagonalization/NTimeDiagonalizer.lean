/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.InputCall
import TCSlib.Complexity.TuringMachine.Build.Contract.Catalog
import TCSlib.Complexity.TuringMachine.Build.Contract.Seam
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Build.Rewind
import TCSlib.Complexity.TuringMachine.BufferWords
import TCSlib.Complexity.TuringMachine.Build.WordTests

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The lazy diagonalizer of the nondeterministic time hierarchy

[AB09, §3.2, proof of Theorem 3.2 and Figure 3.1] ([Coo72]): the machine `D` of the lazy
diagonalization, as two contracts over a pure description of its stages. C1-E's statement phase
(C1's fill plan, `audits/evidence/c1/C1-fill-plan.md`; the route of
`audits/evidence/c1/C1-design.md` §2.5 and the P3.3 gate's round 2,
`audits/ch3-p33-r2-findings.md` §§1–5).

* **The stages** are pure. The ladder is `ℓ₀ = 2` and `ℓᵢ₊₁ = 2 ^ (T*ᵢ)²`, with bottom `aᵢ = ℓᵢ + 1`
  and budget `T*ᵢ = (f aᵢ + aᵢ + 1)²` (`Turing.NTimeDiag.ladder`, `Turing.NTimeDiag.budget`). An
  input `1ⁿ` with `n ≥ 3` lies in the stage `i` with `ℓᵢ < n ≤ ℓᵢ₊₁` (`Turing.NTimeDiag.stage`).
  That stage diagonalizes against the code `αⱼ` with `j = (Nat.unpair i).1`
  (`Turing.NTimeDiag.stageCode`), so every code recurs at unboundedly many stages: the P3.3 gate's
  fixed-code schedule.
* **The stage query** (`Turing.NTimeDiag.query`) is the word that `D` hands to its simulators.
  - At the top `n = ℓᵢ₊₁` it is the flag `true` and the exponential decider's input
    `⟨⟨bits T*, α⟩, 1^a⟩`.
  - In the middle it is the flag `false` and `⟨⟨bits (g n), α⟩, 1^{n+1}⟩`; `D` rewrites its budget.
  - Off unary inputs of length at least `3` it is `[]`.

  One deterministic machine computes it in time linear in `g n + 1`
  (`Turing.NTimeDiag.exists_queryTM`). Its fill is the capped locator of the gate's round 2, `g`'s
  witness and the materialization.
* **The diagonalizer's contract** (`Turing.NTimeDiag.exists_diagonalizer`) is exactly what the chain
  of [AB09, Figure 3.1] reads:
  - every branch halts within a uniform `K · (g n + 1)`;
  - per code `α` there is a constant `C`;
  - in the middle of a stage of `α`, `D` accepts `1ⁿ` only if the coded machine accepts `1^{n+1}`
    within `g n`, and it does whenever the coded machine accepts within some `t'` with
    `C · (t' + 1) ≤ g n`;
  - at a top, once `C · 2^{C·(T* + 1)} ≤ n`, `D` accepts `1ⁿ` iff the coded machine does not accept
    the bottom `1^a` within `T*`.

## Main definitions

* `Turing.NTimeDiag.budget`, `Turing.NTimeDiag.ladder`, `Turing.NTimeDiag.stage`,
  `Turing.NTimeDiag.stageCode`, `Turing.NTimeDiag.query`.

## Main results

* `Turing.NTimeDiag.budget_eq`, `ladder_zero`, `ladder_succ`, `two_mul_lt_ladder_succ`,
  `stage_spec`, `stage_eq`, `stage_of_le_two`, `stageCode_eq`, `stageCode_frequently`, `query_eq`,
  `query_of_not_guard` — the stages' laws (proved).
* `Turing.NTimeDiag.acceptLang_mem_NTIME` — a halting NDTM's bounded language is in `NTIME`
  (proved).
* `Turing.NTimeDiag.exists_queryTM` — the stage query in linear time (sorried; C1-E's first fill).
* `Turing.NTimeDiag.exists_diagonalizer` — the diagonalizer (sorried; C1-E's second fill).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2, Theorem 3.2 and Figure 3.1.)
* [Coo72] S. Cook, *A hierarchy for nondeterministic time complexity*,
  STOC 1972. (Cited through [AB09]; no external text is required.)
-/

namespace Turing.NTimeDiag

/-- **The budget of a stage** with bottom ladder value `ℓ`: with the bottom `a = ℓ + 1`, the
budget is `T* = (f a + a + 1)²` [the P3.3 gate's round 2, §1]. -/
def budget (f : ℕ → ℕ) (ℓ : ℕ) : ℕ := (f (ℓ + 1) + (ℓ + 1) + 1) ^ 2

/-- The budget, unfolded: `budget f ℓ = (f (ℓ + 1) + (ℓ + 1) + 1) ^ 2`. -/
theorem budget_eq (f : ℕ → ℕ) (ℓ : ℕ) : budget f ℓ = (f (ℓ + 1) + (ℓ + 1) + 1) ^ 2 := rfl

/-- **The ladder** [AB09, Figure 3.1; the P3.3 gate's round 2, §1]: `ℓ₀ = 2` and
`ℓᵢ₊₁ = 2 ^ (T*ᵢ)²`, where `T*ᵢ = budget f ℓᵢ`. -/
def ladder (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 2
  | i + 1 => 2 ^ budget f (ladder f i) ^ 2

/-- The ladder starts at `2`: `ladder f 0 = 2`. -/
theorem ladder_zero (f : ℕ → ℕ) : ladder f 0 = 2 := rfl

/-- One more rung: `ladder f (i + 1) = 2 ^ (budget f (ladder f i)) ^ 2`. -/
theorem ladder_succ (f : ℕ → ℕ) (i : ℕ) :
    ladder f (i + 1) = 2 ^ budget f (ladder f i) ^ 2 := rfl

/-- **The ladder more than doubles**: `2 · ℓᵢ < ℓᵢ₊₁`.

**Proof sketch.** The budget is at least `(ℓᵢ + 2)²`, so its square exceeds `ℓᵢ + 1`, and
`2 · ℓᵢ < 2 ^ (ℓᵢ + 1)` (`Nat.lt_two_pow`). -/
theorem two_mul_lt_ladder_succ (f : ℕ → ℕ) (i : ℕ) : 2 * ladder f i < ladder f (i + 1) := by
  rw [ladder_succ]
  have hb : ladder f i + 1 ≤ budget f (ladder f i) ^ 2 := by
    unfold budget
    have h1 : ladder f i + 1 ≤ f (ladder f i + 1) + (ladder f i + 1) + 1 := by omega
    have h2 : f (ladder f i + 1) + (ladder f i + 1) + 1 ≤
        (f (ladder f i + 1) + (ladder f i + 1) + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h3 : (f (ladder f i + 1) + (ladder f i + 1) + 1) ^ 2 ≤
        ((f (ladder f i + 1) + (ladder f i + 1) + 1) ^ 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  calc 2 * ladder f i < 2 * 2 ^ ladder f i := by
        have := Nat.lt_two_pow_self (n := ladder f i); omega
    _ = 2 ^ (ladder f i + 1) := by rw [Nat.pow_succ]; ring
    _ ≤ 2 ^ budget f (ladder f i) ^ 2 := Nat.pow_le_pow_right (by norm_num) hb

/-- The ladder is above its index: `i + 2 ≤ ℓᵢ`.

**Proof sketch.** Induction on `i`, by `Turing.NTimeDiag.two_mul_lt_ladder_succ`. -/
theorem le_ladder (f : ℕ → ℕ) (i : ℕ) : i + 2 ≤ ladder f i := by
  induction i with
  | zero => exact le_of_eq (ladder_zero f).symm
  | succ i ih => have := two_mul_lt_ladder_succ f i; omega

/-- The ladder is strictly increasing.

**Proof sketch.** `Turing.NTimeDiag.two_mul_lt_ladder_succ` at each step. -/
theorem ladder_strictMono (f : ℕ → ℕ) : StrictMono (ladder f) :=
  strictMono_nat_of_lt_succ fun i => by have := two_mul_lt_ladder_succ f i; omega

/-- Every length is below some rung: `n ≤ ladder f (n + 1)`. -/
theorem exists_le_ladder_succ (f : ℕ → ℕ) (n : ℕ) : ∃ i, n ≤ ladder f (i + 1) :=
  ⟨n, by have := le_ladder f (n + 1); omega⟩

/-- **The stage of a length** `n`: the least `i` with `n ≤ ℓᵢ₊₁`. For `n ≥ 3` it is the unique `i`
with `ℓᵢ < n ≤ ℓᵢ₊₁` (`Turing.NTimeDiag.stage_spec`, `Turing.NTimeDiag.stage_eq`). -/
def stage (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.find (exists_le_ladder_succ f n)

/-- **The stage brackets its length**: for `n ≥ 3`, `ℓ_{stage n} < n ≤ ℓ_{stage n + 1}`.

**Proof sketch.** The upper bound is `Nat.find_spec`. For the lower bound, stage `0` has
`ℓ₀ = 2 < n`; a positive stage `i` has `n > ℓᵢ` by `Nat.find_min` at `i - 1`. -/
theorem stage_spec (f : ℕ → ℕ) {n : ℕ} (hn : 3 ≤ n) :
    ladder f (stage f n) < n ∧ n ≤ ladder f (stage f n + 1) := by
  refine ⟨?_, Nat.find_spec (exists_le_ladder_succ f n)⟩
  unfold stage
  rcases h : Nat.find (exists_le_ladder_succ f n) with _ | i
  · rw [ladder_zero]; omega
  · have hmin := Nat.find_min (exists_le_ladder_succ f n) (m := i) (by omega)
    omega

/-- **The stage is determined by its bracket**: `ℓᵢ < n ≤ ℓᵢ₊₁` gives `stage f n = i`.

**Proof sketch.** `Nat.find` is at most `i` by the upper bound, and a smaller stage `i'` would
give `n ≤ ℓ_{i'+1} ≤ ℓᵢ < n` by monotonicity. -/
theorem stage_eq (f : ℕ → ℕ) {n i : ℕ} (hlo : ladder f i < n) (hhi : n ≤ ladder f (i + 1)) :
    stage f n = i := by
  have hle : stage f n ≤ i := Nat.find_min' (exists_le_ladder_succ f n) hhi
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have hs := Nat.find_spec (exists_le_ladder_succ f n)
    have hm : ladder f (stage f n + 1) ≤ ladder f i :=
      (ladder_strictMono f).monotone (by unfold stage at hlt ⊢; omega)
    unfold stage at hm
    omega
  · exact heq

/-- **Short lengths are in stage `0`** (the statement gate, finding 3): for `n ≤ 2`,
`stage f n = 0`.

**Proof sketch.** `n ≤ 2 < 3 ≤ ℓ₁` (`Turing.NTimeDiag.le_ladder`), so `0` already satisfies the
search. -/
theorem stage_of_le_two (f : ℕ → ℕ) {n : ℕ} (hn : n ≤ 2) : stage f n = 0 :=
  (Nat.find_eq_zero (exists_le_ladder_succ f n)).2 (le_trans (by omega) (le_ladder f 1))

/-- **The code a stage diagonalizes against**: the binary word of index `j = (Nat.unpair i).1`,
`(Nat.bits (j + 1)).dropLast` (the binary expansion of `j + 1` without its top bit). Every word
arises for exactly one `j`, and every `j` for unboundedly many stages
(`Turing.NTimeDiag.stageCode_frequently`). -/
def stageCode (i : ℕ) : List Bool := (Nat.bits ((Nat.unpair i).1 + 1)).dropLast

/-- The scheduled code, unfolded: `stageCode i = (Nat.bits ((Nat.unpair i).1 + 1)).dropLast`. -/
theorem stageCode_eq (i : ℕ) : stageCode i = (Nat.bits ((Nat.unpair i).1 + 1)).dropLast := rfl

/-- **Every code recurs at unboundedly many stages** [the P3.3 gate's round 2, §1: the fixed-code
schedule]: for every word `α` and bound `N` some stage `i ≥ N` has `stageCode i = α`.

**Proof sketch.** Take `j + 1 = Nat.ofBits (α ++ [true])`, whose binary expansion is `α` followed
by its top bit, and `i = Nat.pair j N ≥ N` (`Nat.right_le_pair`, `Nat.unpair_pair`). -/
theorem stageCode_frequently (α : List Bool) (N : ℕ) : ∃ i, N ≤ i ∧ stageCode i = α := by
  obtain ⟨m, hm1, hm⟩ : ∃ m, 1 ≤ m ∧ Nat.bits m = α ++ [true] := by
    induction α with
    | nil => exact ⟨1, le_rfl, by simp⟩
    | cons b α ih =>
      obtain ⟨m, hm1, hm⟩ := ih
      refine ⟨Nat.bit b m, ?_, ?_⟩
      · cases b <;> simp only [Nat.bit, cond_true, cond_false] <;> omega
      · rw [Nat.bits_append_bit _ _ (fun h => absurd h (by omega)), hm, List.cons_append]
  refine ⟨Nat.pair (m - 1) N, Nat.right_le_pair _ _, ?_⟩
  simp only [stageCode, Nat.unpair_pair, Nat.sub_add_cancel hm1, hm, List.dropLast_concat]

/-- **The stage query** on an input `x`: the word the diagonalizer builds its rungs from. On a
unary `x = 1ⁿ` with `n ≥ 3`, in the stage `i = stage f n` with code `α = stageCode i` and bottom
`ℓ = ladder f i`:
- at the top `n = ladder f (i + 1)`: `true :: ⟨⟨bits (budget f ℓ), α⟩, 1^{ℓ + 1}⟩`;
- otherwise: `false :: ⟨⟨bits (g n), α⟩, 1^{n + 1}⟩`.

On every other input it is `[]`. -/
def query (f g : ℕ → ℕ) (x : List Bool) : List Bool :=
  if x = List.replicate x.length true ∧ 3 ≤ x.length then
    if x.length = ladder f (stage f x.length + 1) then
      true :: pairEncode (pairEncode (Nat.bits (budget f (ladder f (stage f x.length))))
        (stageCode (stage f x.length))) (List.replicate (ladder f (stage f x.length) + 1) true)
    else
      false :: pairEncode (pairEncode (Nat.bits (g x.length)) (stageCode (stage f x.length)))
        (List.replicate (x.length + 1) true)
  else []

/-- **The stage query on `1ⁿ`, unfolded**: for `n ≥ 3`, with `i = stage f n`, it is
`true :: ⟨⟨bits (budget f ℓᵢ), αᵢ⟩, 1^{ℓᵢ + 1}⟩` at the top `n = ℓᵢ₊₁` and
`false :: ⟨⟨bits (g n), αᵢ⟩, 1^{n + 1}⟩` otherwise. -/
theorem query_eq (f g : ℕ → ℕ) {n : ℕ} (hn : 3 ≤ n) :
    query f g (List.replicate n true) =
      if n = ladder f (stage f n + 1) then
        true :: pairEncode (pairEncode (Nat.bits (budget f (ladder f (stage f n))))
          (stageCode (stage f n))) (List.replicate (ladder f (stage f n) + 1) true)
      else
        false :: pairEncode (pairEncode (Nat.bits (g n)) (stageCode (stage f n)))
          (List.replicate (n + 1) true) := by
  simp only [query, List.length_replicate, true_and, hn, ↓reduceIte]

/-- **The stage query off its guard is empty** (the statement gate, finding 3): unless `x` is
unary of length at least `3`, `query f g x = []`. With `Turing.NTimeDiag.query_eq` it covers every
input. -/
theorem query_of_not_guard (f g : ℕ → ℕ) {x : List Bool}
    (hx : ¬(x = List.replicate x.length true ∧ 3 ≤ x.length)) : query f g x = [] := by
  unfold query
  exact if_neg hx

/-- **A halting NDTM's bounded language is in `NTIME`**: if every branch of `D` on every `x` halts
within `K · (g |x| + 1)`, then the language `{x | D accepts x within K · (g |x| + 1)}` is in
`NTIME (g + 1)`. It is the first half of the hierarchy's strictness argument, read off
`Turing.NTimeDiag.exists_diagonalizer`'s time clause.

**Proof sketch.** `Complexity.mem_NTIME_iff` at the constant `K`: the halting clause is the
hypothesis, and membership is acceptance by definition. -/
theorem acceptLang_mem_NTIME (D : FinNDTM Bool) (K : ℕ) (g : ℕ → ℕ)
    (h : ∀ x : List Bool, D.tm.HaltsWithin x (K * (g x.length + 1))) :
    {x : List Bool | D.AcceptsWithin x (K * (g x.length + 1))} ∈
      Complexity.NTIME fun n => g n + 1 :=
  ⟨K, D, fun x => ⟨h x, Iff.rfl⟩⟩

/-- The query of a word is the query of the unary word of the same length when the word is unary
of length at least three, and is empty otherwise. -/
private theorem qy_guard (f g : ℕ → ℕ) (x : List Bool) :
    query f g x = if x = List.replicate x.length true ∧ 3 ≤ x.length then
      query f g (List.replicate x.length true) else [] := by
  by_cases h : x = List.replicate x.length true ∧ 3 ≤ x.length
  · rw [if_pos h]
    exact congrArg (query f g) h.1
  · rw [if_neg h]
    exact query_of_not_guard f g h

/-- A linear-time decider recognizes all-true words of length at least three. It composes the
published all-true test `Turing.FinTM.computesFunInTime_allTrue` with three fixed-word tests
`Turing.FinTM.computesFunInTime_decideEq` by the timed conditional; it introduces no input scan
beyond those rows. No public row decides the length bound.

**Proof sketch.** The all-true test decides unarity. Three fixed-word tests reject the empty word
and the all-true words of lengths one and two. Each conditional preserves a linear time bound. -/
private theorem qy_guard_decider :
    ∃ (D : FinTM Bool) (c : ℕ),
      D.ComputesFunInTime
        (fun x => [decide (x = List.replicate x.length true ∧ 3 ≤ x.length)])
        (fun n => c * (n + 1)) := by
  have hcut (w : List Bool) {M : FinTM Bool} {p : List Bool → Bool} {C : ℕ}
      (hM : M.ComputesFunInTime (fun x => [p x]) (fun n => C * (n + 1))) :
      ∃ (D : FinTM Bool) (c : ℕ),
        D.ComputesFunInTime (fun x => [decide (x ≠ w) && p x])
          (fun n => c * (n + 1)) := by
    obtain ⟨E, a, hE'⟩ := FinTM.computesFunInTime_decideEq w
    obtain ⟨F, b, hF⟩ := FinTM.computesFunInTime_const [false]
    obtain ⟨D, d, hD⟩ := FinTM.computesFunInTime_cond hE' hF hM
    refine ⟨D, d * (a + b + C + 1), (FinTM.computesFunInTime_iff _ _ _).mpr ?_⟩
    intro x
    have hx := (FinTM.computesFunInTime_iff _ _ _).mp hD x
    have hout : (if decide (x = w) then [false] else [p x]) =
        [decide (x ≠ w) && p x] := by
      by_cases he : x = w <;> simp [he]
    rw [hout] at hx
    apply hx.mono
    calc
      _ ≤ d * ((a + b + C + 1) * (x.length + 1)) := by
        apply Nat.mul_le_mul_left
        have hm : max (b * (x.length + 1)) (C * (x.length + 1)) ≤
            b * (x.length + 1) + C * (x.length + 1) :=
          max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
        nlinarith
      _ = _ := by ring
  obtain ⟨U, c, hU'⟩ := FinTM.computesFunInTime_allTrue
  obtain ⟨D₀, c₀, h₀⟩ := hcut [] hU'
  obtain ⟨D₁, c₁, h₁⟩ := hcut [true] h₀
  obtain ⟨D₂, c₂, h₂⟩ := hcut [true, true] h₁
  refine ⟨D₂, c₂, ?_⟩
  convert h₂ using 1
  funext x
  refine congrArg (fun b => [b]) ?_
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hu, hn⟩
    have hz : x ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [List.length_nil] at this
      omega
    have ho : x ≠ [true] := by
      intro h
      have := congrArg List.length h
      simp only [List.length_cons, List.length_nil] at this
      omega
    have ht : x ≠ [true, true] := by
      intro h
      have := congrArg List.length h
      simp only [List.length_cons, List.length_nil] at this
      omega
    exact ⟨ht, ho, hz, hu⟩
  · rintro ⟨ht, ho, hz, hu⟩
    refine ⟨hu, ?_⟩
    by_contra hn
    have hlen : x.length = 0 ∨ x.length = 1 ∨ x.length = 2 := by omega
    rcases hlen with hlen | hlen | hlen
    · exact hz (by simpa only [hlen, List.replicate_zero] using hu)
    · exact ho (by simpa only [hlen, List.replicate_succ, List.replicate_zero] using hu)
    · exact ht (by simpa only [hlen, List.replicate_succ, List.replicate_zero] using hu)

/-- A machine for the query on the unary word of every input's length suffices for the full
query. The guard and the empty-output branch add only a uniform multiple of `g n + 1`.

**Proof sketch.** Use the linear guard to choose the supplied machine or the constant empty
output. The guard equation identifies the output. Since `n ≤ g n`, both the guard and the empty
branch fit the same bound as the supplied machine; absorb the conditional's constant. -/
private theorem qy_query_of_main {f g : ℕ → ℕ} (hg : Complexity.TimeConstructible g)
    {M : FinTM Bool} {A : ℕ}
    (hM : M.ComputesFunInTime (fun x => query f g (List.replicate x.length true))
      (fun n => A * (g n + 1))) :
    ∃ (G : FinTM Bool) (C : ℕ),
      G.ComputesFunInTime (query f g) (fun n => C * (g n + 1)) := by
  obtain ⟨D, a, hD⟩ := qy_guard_decider
  obtain ⟨E, b, hE⟩ := FinTM.computesFunInTime_const []
  obtain ⟨G, c, hG⟩ := FinTM.computesFunInTime_cond hD hM hE
  have hle := ((Complexity.timeConstructible_iff g).mp hg).1
  refine ⟨G, c * (a + A + b + 1), (FinTM.computesFunInTime_iff _ _ _).mpr ?_⟩
  intro x
  have hx := (FinTM.computesFunInTime_iff _ _ _).mp hG x
  have hout : (if decide (x = List.replicate x.length true ∧ 3 ≤ x.length) then
      query f g (List.replicate x.length true) else []) = query f g x := by
    simpa only [decide_eq_true_eq] using (qy_guard f g x).symm
  rw [hout] at hx
  apply hx.mono
  calc
    _ ≤ c * ((a + A + b + 1) * (g x.length + 1)) := by
      apply Nat.mul_le_mul_left
      have ha := Nat.mul_le_mul_left a (Nat.add_le_add_right (hle x.length) 1)
      have hb := Nat.mul_le_mul_left b (Nat.add_le_add_right (hle x.length) 1)
      have hm : max (A * (g x.length + 1)) (b * (x.length + 1)) ≤
          A * (g x.length + 1) + b * (g x.length + 1) :=
        max_le (Nat.le_add_right _ _) (hb.trans (Nat.le_add_left _ _))
      nlinarith
    _ = _ := by ring

/-- The next rung in terms of `X = f a + a + 1`: `ladder f (i + 1) = 2 ^ X ^ 4`. -/
private theorem qy_ladder_succ_eq (f : ℕ → ℕ) (i : ℕ) :
    ladder f (i + 1) = 2 ^ (f (ladder f i + 1) + (ladder f i + 1) + 1) ^ 4 := by
  rw [ladder_succ, budget_eq, ← pow_mul]

/-- The ledger: the rungs passed before stage `s` sum to at most twice its bottom. -/
private theorem qy_ledger (f : ℕ → ℕ) (s : ℕ) :
    ∑ h ∈ Finset.range s, ladder f (h + 1) ≤ 2 * ladder f s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have := two_mul_lt_ladder_succ f s
    omega

/-- **The all-ones counter's value**: `m` ones are worth `2 ^ m - 1`. -/
private theorem qy_ones_val (m : ℕ) :
    Nat.ofDigits 2 ((List.replicate m true).map Bool.toNat) = 2 ^ m - 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.map_cons, Nat.ofDigits_cons, ih, Bool.toNat_true, pow_succ]
    have := Nat.one_le_two_pow (n := m)
    omega

/-- **The next rung's counter value**: `m` zeros then a one are worth `2 ^ m`. -/
private theorem qy_rung_val (m : ℕ) :
    Nat.ofDigits 2 ((List.replicate m false ++ [true]).map Bool.toNat) = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.cons_append, List.map_cons, Nat.ofDigits_cons, ih,
      Bool.toNat_false, pow_succ]
    ring

/-- **The counter is large enough**: the all-ones word of width `|bits n| + |bits D|` is worth at
least `D (n + 1)`. -/
private theorem qy_ones_ge (n D : ℕ) :
    D * (n + 1) ≤ 2 ^ ((Nat.bits n).length + (Nat.bits D).length) - 1 := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, pow_add]
  have hn := Nat.lt_size_self n
  have hD := Nat.lt_size_self D
  have hprod : (n + 1) * (D + 1) ≤ 2 ^ Nat.size n * 2 ^ Nat.size D :=
    Nat.mul_le_mul hn hD
  have : D * (n + 1) + 1 ≤ (n + 1) * (D + 1) := by nlinarith
  omega

/-- **The counter is not too large**: `2 ^ |bits n| ≤ 2 n + 1`. -/
private theorem qy_two_pow_bits_le (n : ℕ) : 2 ^ (Nat.bits n).length ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.size_eq_bits_len]
    have hsz : Nat.size n = Nat.log 2 n + 1 := by
      apply le_antisymm
      · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) n)
      · by_contra h
        have hlt : n < 2 ^ Nat.log 2 n :=
          Nat.size_le.mp (by omega)
        exact absurd (Nat.pow_log_le_self 2 (by omega)) (not_le.mpr hlt)
    rw [hsz, pow_succ]
    have := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    omega

/-- **`⌊log₂ n⌋` from `bits n`**: for `n ≥ 1`, `Nat.log 2 n + 1 = |bits n|`. -/
private theorem qy_log_bits {n : ℕ} (hn : 1 ≤ n) : Nat.log 2 n + 1 = (Nat.bits n).length := by
  rw [Nat.size_eq_bits_len]
  apply le_antisymm
  · by_contra h
    have hlt : n < 2 ^ Nat.log 2 n := Nat.size_le.mp (by omega)
    exact absurd (Nat.pow_log_le_self 2 (by omega)) (not_le.mpr hlt)
  · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) n)

/-- **The install call's bound under `f a ≤ n`** (the timeout certificate's arithmetic): with
`a ≤ n` and `f a ≤ n`, the call's time bound `c' (c (f a + 1) + a + |bits (f a)| + 1)` is at most
`c' (c + 2) (n + 1)`. -/
private theorem qy_call_bound (f : ℕ → ℕ) (c c' a n : ℕ) (ha : a ≤ n) (hfa : f a ≤ n) :
    c' * (c * (f a + 1) + a + (Nat.bits (f a)).length + 1) ≤ c' * (c + 2) * (n + 1) := by
  have hb : (Nat.bits (f a)).length ≤ f a := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self)
  have h1 : c * (f a + 1) ≤ c * (n + 1) := Nat.mul_le_mul_left c (by omega)
  have h2 : c * (f a + 1) + a + (Nat.bits (f a)).length + 1 ≤ (c + 2) * (n + 1) := by nlinarith
  calc c' * (c * (f a + 1) + a + (Nat.bits (f a)).length + 1) ≤ c' * ((c + 2) * (n + 1)) :=
        Nat.mul_le_mul_left c' h2
    _ = c' * (c + 2) * (n + 1) := by ring

/-- The ladder is at least `2 ^ (i + 1)`. -/
private theorem qy_two_pow_le_ladder (f : ℕ → ℕ) (i : ℕ) : 2 ^ (i + 1) ≤ ladder f i := by
  induction i with
  | zero => rw [ladder_zero]; norm_num
  | succ i ih =>
    have := two_mul_lt_ladder_succ f i
    rw [pow_succ]
    omega

/-- **The stage index is below `log₂ n`**: for `n ≥ 3`, `stage f n < Nat.log 2 n`. -/
private theorem qy_stage_lt_log (f : ℕ → ℕ) {n : ℕ} (hn : 3 ≤ n) : stage f n < Nat.log 2 n := by
  have hlo := (stage_spec f hn).1
  have hp := qy_two_pow_le_ladder f (stage f n)
  have : stage f n + 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
  omega

/-- **The timeout certificate.** If the install call's exit time `t` is within its published
bound `c' (c (f a + 1) + a + |bits (f a)| + 1)`, `a ≤ n`, and the clock's all-ones counter of
width `|bits n| + |bits (c' (c + 2))|` (value `2 ^ m - 1`) runs out before `t`, then `n < f a`. -/
private theorem qy_timeout_cert (f : ℕ → ℕ) (c c' a n t : ℕ) (ha : a ≤ n)
    (ht : t ≤ c' * (c * (f a + 1) + a + (Nat.bits (f a)).length + 1))
    (hlate : 2 ^ ((Nat.bits n).length + (Nat.bits (c' * (c + 2))).length) - 1 < t) :
    n < f a := by
  by_contra h
  have hfa : f a ≤ n := by omega
  have h1 := qy_call_bound f c c' a n ha hfa
  have h2 := qy_ones_ge n (c' * (c + 2))
  exact absurd (hlate.trans_le (ht.trans (h1.trans h2))) (lt_irrefl _)

/-- A configuration in the normal form used by the main machine: a live state `s`, the input
head `ip`, the work tapes `T`, the work heads `P` and the output `o`. -/
private def qyC {K : ℕ} {S : Type} {x : List Bool} (s : S) (ip : Fin (x.length + 2))
    (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool) : Cfg K Bool S x :=
  ⟨some s, ip, T, P, o⟩

/-- Renaming the state of a normal-form configuration renames its state only. -/
private theorem qyC_mapState {K : ℕ} {S S' : Type} {x : List Bool} (f : S → S') (s : S)
    (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool) :
    (qyC s ip T P o : Cfg K Bool S x).mapState f = qyC (f s) ip T P o := by
  apply Cfg.ext
  · rw [Cfg.mapState_state]
    rfl
  · rw [Cfg.mapState_inputPos]
    rfl
  · funext j q
    rw [Cfg.mapState_workTapes]
    rfl
  · funext j
    rw [Cfg.mapState_workTapePos]
    rfl
  · rw [Cfg.mapState_output]
    rfl

/-- **A hosted phase is a segment.** If phase `k` of a phase host runs from a normal-form
configuration at `e` to one at the live exit `s'`, which the host redirects to `q'`, with no
redirect earlier, then the host runs, in one more step, from the tagged start to the redirected
endpoint, avoiding every set `F` of host states that contains no state the phase's run visits
up to its end. It is `Turing.phaseHostTM_run` with the tag of every intermediate state read
off. -/
private theorem qy_hosted' {K : ℕ} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM K Bool (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (k : I) {x : List Bool}
    (e s' : Ph k) (q' : Σ i, Ph i) (ip ip' : Fin (x.length + 2))
    (T T' : Fin K → ℤ → Option Bool) (P P' : Fin K → ℤ) (o o' : List Bool) (t : ℕ)
    (h : (M k).runFrom (qyC e ip T P o) t = qyC s' ip' T' P' o')
    (hred : red k s' = some q')
    (hguard : ∀ u < t, ∀ s, ((M k).runFrom (qyC e ip T P o) u).state = some s → red k s = none)
    (F : Set (Option (Σ i, Ph i)))
    (hF : ∀ u ≤ t, ∀ s, ((M k).runFrom (qyC e ip T P o) u).state = some s → some ⟨k, s⟩ ∉ F) :
    Segment (phaseHostTM M q0 red) F (fun _ => True) (qyC ⟨k, e⟩ ip T P o)
      (qyC q' ip' T' P' o') (t + 1) := by
  have H := phaseHostTM_run M q0 red k (qyC e ip T P o) _ t h s' rfl q' hred hguard
  rw [qyC_mapState, qyC_mapState] at H
  refine (segment_iff _ _ _ _ _ _).mpr ⟨H.2, fun u hu => ?_, fun _ _ => trivial⟩
  have hlive : ((M k).runFrom (qyC e ip T P o) u).state ≠ none :=
    MultiTapeTM.runFrom_state_ne_none_of_le (M k) _ t (by rw [h]; exact Option.some_ne_none _)
      u (by omega)
  have hu' := H.1 u (by omega)
  rw [hu', Cfg.mapState_state]
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
  rw [hs, Option.map_some]
  exact hF u (by omega) s hs

/-- **A hosted phase is a segment**, avoiding every set `F` of host states that contains neither
`none` nor a state of phase `k`: `qy_hosted'` with the avoided set checked once for all. -/
private theorem qy_hosted {K : ℕ} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM K Bool (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (k : I) {x : List Bool}
    (e s' : Ph k) (q' : Σ i, Ph i) (ip ip' : Fin (x.length + 2))
    (T T' : Fin K → ℤ → Option Bool) (P P' : Fin K → ℤ) (o o' : List Bool) (t : ℕ)
    (h : (M k).runFrom (qyC e ip T P o) t = qyC s' ip' T' P' o')
    (hred : red k s' = some q')
    (hguard : ∀ u < t, ∀ s, ((M k).runFrom (qyC e ip T P o) u).state = some s → red k s = none)
    (F : Set (Option (Σ i, Ph i))) (hF : ∀ s, some ⟨k, s⟩ ∉ F) :
    Segment (phaseHostTM M q0 red) F (fun _ => True) (qyC ⟨k, e⟩ ip T P o)
      (qyC q' ip' T' P' o') (t + 1) :=
  qy_hosted' M q0 red k e s' q' ip ip' T T' P P' o o' t h hred hguard F fun _ _ s _ => hF s

/-- **A hosted last phase is a segment** without dispatch: if phase `k` runs to a live endpoint
that the host does not redirect, with no redirect earlier, the host's run is the tagged phase run,
avoiding every set that the phase's run avoids before its end. -/
private theorem qy_hosted_last {K : ℕ} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM K Bool (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (k : I) {x : List Bool}
    (e s' : Ph k) (ip ip' : Fin (x.length + 2))
    (T T' : Fin K → ℤ → Option Bool) (P P' : Fin K → ℤ) (o o' : List Bool) (t : ℕ)
    (h : (M k).runFrom (qyC e ip T P o) t = qyC s' ip' T' P' o')
    (hguard : ∀ u < t, ∀ s, ((M k).runFrom (qyC e ip T P o) u).state = some s → red k s = none)
    (F : Set (Option (Σ i, Ph i)))
    (hF : ∀ u < t, ∀ s, ((M k).runFrom (qyC e ip T P o) u).state = some s → some ⟨k, s⟩ ∉ F) :
    Segment (phaseHostTM M q0 red) F (fun _ => True) (qyC ⟨k, e⟩ ip T P o)
      (qyC ⟨k, s'⟩ ip' T' P' o') t := by
  have H := phaseHostTM_run_le M q0 red k (qyC e ip T P o) t hguard
  refine (segment_iff _ _ _ _ _ _).mpr ⟨?_, fun u hu => ?_, fun _ _ => trivial⟩
  · have h1 := H t le_rfl
    rw [qyC_mapState, h, qyC_mapState] at h1
    exact h1
  · have hlive : ((M k).runFrom (qyC e ip T P o) u).state ≠ none :=
      MultiTapeTM.runFrom_state_ne_none_of_le (M k) _ t (by rw [h]; exact Option.some_ne_none _)
        u hu.le
    have hu' := H u hu.le
    rw [qyC_mapState] at hu'
    rw [hu', Cfg.mapState_state]
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
    rw [hs, Option.map_some]
    exact hF u hu s hs

/-- **A hosted phase's run.** The run part of `qy_hosted`, with no avoided set. -/
private theorem qy_hosted_run {K : ℕ} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM K Bool (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (k : I) {x : List Bool}
    (e s' : Ph k) (q' : Σ i, Ph i) (ip ip' : Fin (x.length + 2))
    (T T' : Fin K → ℤ → Option Bool) (P P' : Fin K → ℤ) (o o' : List Bool) (t : ℕ)
    (h : (M k).runFrom (qyC e ip T P o) t = qyC s' ip' T' P' o')
    (hred : red k s' = some q')
    (hguard : ∀ u < t, ∀ s, ((M k).runFrom (qyC e ip T P o) u).state = some s →
      red k s = none) :
    (phaseHostTM M q0 red).runFrom (qyC ⟨k, e⟩ ip T P o) (t + 1) = qyC q' ip' T' P' o' :=
  ((segment_iff _ _ _ _ _ _).mp
    (qy_hosted M q0 red k e s' q' ip ip' T T' P P' o o' t h hred hguard ∅ (fun _ h => h))).1

/-- A word written over a buffer at its right end extends it: the cells `[|u|, |u| + |w|)`
overwritten by `w`, and every other cell kept, is the buffer of `u ++ w`. -/
private theorem qy_patch_end (u w : List Bool) (p : ℤ) (hp : p = u.length) :
    (fun q => if p ≤ q ∧ q < p + (w.length : ℤ) then FinTM.bufferTape w (q - p)
      else FinTM.bufferTape u q) = FinTM.bufferTape (u ++ w) := by
  subst hp
  funext q
  by_cases h : (u.length : ℤ) ≤ q ∧ q < u.length + (w.length : ℤ)
  · rw [if_pos h]
    have h0 : 0 ≤ q - u.length := by omega
    have := FinTM.bufferTape_append_shift u w h0
    rw [show (u.length : ℤ) + (q - u.length) = q by ring] at this
    exact this.symm
  · rw [if_neg h]
    by_cases hq : 0 ≤ q ∧ q < u.length
    · rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq, if_pos hq.1, if_pos hq.1,
        List.getElem?_append_left (by omega)]
    · rw [FinTM.bufferTape_eq_none_of_not_mem u hq,
        FinTM.bufferTape_eq_none_of_not_mem (u ++ w) (by rw [List.length_append]; push_cast; omega)]

/-- The buffer of a mapped word is the mapped buffer. -/
private theorem qy_bufferTape_map (w : List Bool) (g : Bool → Bool) (z : ℤ) :
    FinTM.bufferTape (w.map g) z = (FinTM.bufferTape w z).map g := by
  rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq]
  split_ifs
  · rw [List.getElem?_map]
  · rfl


/-- A guard from a row's first-visit cut: before the exit, every live state of the phase is one
the host does not redirect. -/
private theorem qy_guard_of_cut {K : ℕ} {S α : Type} {x : List Bool} {M : MultiTapeTM K Bool S}
    {c : Cfg K Bool S x} {t : ℕ} (done : S) (r : S → Option α)
    (hr : ∀ s, s ≠ done → r s = none) (hcut : ∀ u < t, (M.runFrom c u).state ≠ some done) :
    ∀ u < t, ∀ s, (M.runFrom c u).state = some s → r s = none :=
  fun u hu s hs => hr s fun h => hcut u hu (h ▸ hs)

/-- **The mapped copy, appending.** `Turing.copyMapTM` copies the word `w` under the head of
`src`, mapped by `g`, onto `dst` right after the word `u` there; nothing else changes. -/
private theorem qy_copy {K : ℕ} {x : List Bool} (src dst : Fin K) (hne : src ≠ dst)
    (g : Bool → Bool)
    (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool)
    (w u : List Bool) (hsrc : T src = FinTM.bufferTape w) (hPs : P src = 0)
    (hdst : T dst = FinTM.bufferTape u) (hPd : P dst = u.length) :
    (copyMapTM K src dst g (fun _ b => b)).runFrom (qyC .sweep ip T P o) (2 * w.length + 2) =
        qyC SweepPhase.done ip (Function.update T dst (FinTM.bufferTape (u ++ w.map g))) P o ∧
      ∀ t < 2 * w.length + 2,
        ((copyMapTM K src dst g (fun _ b => b)).runFrom (qyC .sweep ip T P o) t).state ≠
          some .done := by
  obtain ⟨hrun, hcut, -⟩ := copyMapTM_run_ofCfg src dst hne g (fun _ b => b) w
    (qyC .sweep ip T P o) rfl (fun p _ _ => by
      show T src (P src + p) = _
      rw [hsrc, hPs, zero_add])
  refine ⟨hrun.trans ?_, hcut⟩
  dsimp only [qyC]
  congr 1
  funext j q
  by_cases hj : j = dst
  · subst hj
    rw [Function.update_self]
    have h := congrFun (qy_patch_end u (w.map g) (P j) hPd) q
    rw [← h, List.length_map]
    by_cases hq : P j ≤ q ∧ q < P j + (w.length : ℤ)
    · rw [if_pos ⟨rfl, hq⟩, if_pos hq, qy_bufferTape_map]
    · rw [if_neg (fun h => hq h.2), if_neg hq, hdst]
  · rw [if_neg (fun h => hj h.1), Function.update_of_ne hj]

/-- **The mapped copy, overwriting.** `Turing.copyMapTM` copies the word `w` under the head of
`src`, mapped by `g`, over the word `u` under the head of `dst`, which is no longer than `w`. -/
private theorem qy_copy_over {K : ℕ} {x : List Bool} (src dst : Fin K) (hne : src ≠ dst)
    (g : Bool → Bool) (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ)
    (o : List Bool) (w u : List Bool) (hu : u.length ≤ w.length)
    (hsrc : T src = FinTM.bufferTape w) (hPs : P src = 0)
    (hdst : T dst = FinTM.bufferTape u) (hPd : P dst = 0) :
    (copyMapTM K src dst g (fun _ b => b)).runFrom (qyC .sweep ip T P o) (2 * w.length + 2) =
        qyC SweepPhase.done ip (Function.update T dst (FinTM.bufferTape (w.map g))) P o ∧
      ∀ t < 2 * w.length + 2,
        ((copyMapTM K src dst g (fun _ b => b)).runFrom (qyC .sweep ip T P o) t).state ≠
          some .done := by
  obtain ⟨hrun, hcut, -⟩ := copyMapTM_run_ofCfg src dst hne g (fun _ b => b) w
    (qyC .sweep ip T P o) rfl (fun p _ _ => by
      show T src (P src + p) = _
      rw [hsrc, hPs, zero_add])
  refine ⟨hrun.trans ?_, hcut⟩
  dsimp only [qyC]
  congr 1
  funext j q
  by_cases hj : j = dst
  · subst hj
    rw [Function.update_self]
    by_cases hq : P j ≤ q ∧ q < P j + (w.length : ℤ)
    · rw [if_pos ⟨rfl, hq⟩, qy_bufferTape_map, hPd, sub_zero]
    · rw [if_neg (fun h => hq h.2), hdst, FinTM.bufferTape_eq_none_of_not_mem _ (by omega),
        FinTM.bufferTape_eq_none_of_not_mem _ (by rw [List.length_map]; omega)]
  · rw [if_neg (fun h => hj h.1), Function.update_of_ne hj]

/-- **The mapped move.** `Turing.transferMapTM` with a blank residue moves the word `w` under
the head of `src`, mapped by `g`, onto `dst` right after the word `u` there, blanking `src`.

**Proof sketch.** The row's endpoint (`Turing.transferMapTM_run_ofCfg`) rewrites, cell by cell,
the source's cells to blanks and the destination's interval to the mapped word; outside them the
tapes are kept. On `dst` the patched interval sits right after `u`, so it is the buffer of
`u ++ w.map g` (`qy_patch_end`); on `src` every cell is blank. -/
private theorem qy_transfer {K : ℕ} {x : List Bool} (src dst : Fin K) (hne : src ≠ dst)
    (g : Bool → Bool) (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ)
    (o : List Bool) (w u : List Bool) (hsrc : T src = FinTM.bufferTape w) (hPs : P src = 0)
    (hdst : T dst = FinTM.bufferTape u) (hPd : P dst = u.length) :
    (transferMapTM K src dst g (fun _ b => b) (fun _ => none)).runFrom (qyC .sweep ip T P o)
        (2 * w.length + 2) =
      qyC SweepPhase.done ip (Function.update (Function.update T src (FinTM.bufferTape []))
        dst (FinTM.bufferTape (u ++ w.map g))) P o ∧
      ∀ t < 2 * w.length + 2,
        ((transferMapTM K src dst g (fun _ b => b) (fun _ => none)).runFrom
          (qyC .sweep ip T P o) t).state ≠ some .done := by
  obtain ⟨hrun, hcut, -⟩ := transferMapTM_run_ofCfg src dst hne g (fun _ b => b) (fun _ => none)
    w (qyC .sweep ip T P o) rfl (fun p _ _ => by
      show T src (P src + p) = _
      rw [hsrc, hPs, zero_add])
  refine ⟨hrun.trans ?_, hcut⟩
  dsimp only [qyC]
  congr 1
  funext j q
  by_cases hj : j = dst
  · subst hj
    rw [Function.update_self, if_neg (fun h => hne h.1.symm)]
    have h := congrFun (qy_patch_end u (w.map g) (P j) hPd) q
    rw [← h, List.length_map]
    by_cases hq : P j ≤ q ∧ q < P j + (w.length : ℤ)
    · rw [if_pos ⟨rfl, hq⟩, if_pos hq, qy_bufferTape_map]
    · rw [if_neg (fun h => hq h.2), if_neg hq, hdst]
  · rw [Function.update_of_ne hj]
    by_cases hs : j = src
    · subst hs
      rw [Function.update_self, FinTM.bufferTape_nil]
      by_cases hq : P j ≤ q ∧ q < P j + (w.length : ℤ)
      · rw [if_pos ⟨rfl, hq⟩]
        cases FinTM.bufferTape w (q - P j) <;> rfl
      · rw [if_neg (fun h => hq h.2), if_neg (fun h => hj h.1), hsrc]
        rw [hPs] at hq
        exact FinTM.bufferTape_eq_none_of_not_mem w (by omega)
    · rw [if_neg (fun h => hs h.1), if_neg (fun h => hj h.1), Function.update_of_ne hs]

/-- **The clear.** `Turing.clearTM` blanks the word `w` under the head of tape `i`. -/
private theorem qy_clear {K : ℕ} {x : List Bool} (i : Fin K) (ip : Fin (x.length + 2))
    (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool) (w : List Bool)
    (hT : T i = FinTM.bufferTape w) (hP : P i = 0) :
    (clearTM K i).runFrom (qyC .sweep ip T P o) (2 * w.length + 2) =
        qyC SweepPhase.done ip (Function.update T i (FinTM.bufferTape [])) P o ∧
      ∀ t < 2 * w.length + 2, ((clearTM K i).runFrom (qyC .sweep ip T P o) t).state ≠
        some .done := by
  obtain ⟨hrun, hcut, -⟩ := clearTM_run_ofCfg i w (qyC .sweep ip T P o) rfl (fun p _ _ => by
    show T i (P i + p) = _
    rw [hT, hP, zero_add])
  refine ⟨hrun.trans ?_, hcut⟩
  dsimp only [qyC]
  congr 1
  funext j q
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, FinTM.bufferTape_nil]
    by_cases hq : P j ≤ q ∧ q < P j + (w.length : ℤ)
    · rw [if_pos ⟨rfl, hq⟩]
    · rw [if_neg (fun h => hq h.2), hT]
      rw [hP] at hq
      exact FinTM.bufferTape_eq_none_of_not_mem w (by omega)
  · rw [if_neg (fun h => hj h.1), Function.update_of_ne hj]

/-- **The constant writer, appending.** `Turing.writeConstTM` writes the fixed word `w₀` on tape
`i` right after the word `u` there, its head back where it started. -/
private theorem qy_writeConst {K : ℕ} {x : List Bool} (i : Fin K) (w₀ : List Bool)
    (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool)
    (u : List Bool) (hT : T i = FinTM.bufferTape u) (hP : P i = u.length) :
    (writeConstTM K i w₀).runFrom (qyC (.wr 0) ip T P o) (2 * w₀.length + 2) =
        qyC (WritePhase.done : WritePhase w₀.length) ip
          (Function.update T i (FinTM.bufferTape (u ++ w₀))) P o ∧
      ∀ t < 2 * w₀.length + 2,
        ((writeConstTM K i w₀).runFrom (qyC (.wr 0) ip T P o) t).state ≠ some .done := by
  obtain ⟨hrun, hcut, -⟩ := writeConstTM_run_ofCfg i w₀ (qyC (.wr 0) ip T P o) rfl
  refine ⟨hrun.trans ?_, hcut⟩
  dsimp only [qyC]
  congr 1
  funext j q
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    have h := congrFun (qy_patch_end u w₀ (P j) hP) q
    rw [← h]
    by_cases hq : P j ≤ q ∧ q < P j + (w₀.length : ℤ)
    · rw [if_pos ⟨rfl, hq⟩, if_pos hq]
    · rw [if_neg (fun h => hq h.2), if_neg hq, hT]
  · rw [if_neg (fun h => hj h.1), Function.update_of_ne hj]

/-- **The rewind.** `Turing.rewindTM` brings the head of tape `i`, `n` cells into the word `u`,
back to the word's start. -/
private theorem qy_rewind {K : ℕ} {x : List Bool} (i : Fin K) (ip : Fin (x.length + 2))
    (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool) (u : List Bool) (n : ℕ)
    (hn : n ≤ u.length) (hT : T i = FinTM.bufferTape u) (hP : P i = n) :
    (rewindTM K i).runFrom (qyC .start ip T P o) (n + 2) =
        qyC RewindPhase.done ip T (Function.update P i 0) o ∧
      ∀ t < n + 2, ((rewindTM K i).runFrom (qyC .start ip T P o) t).state ≠ some .done := by
  obtain ⟨hrun, hcut, -⟩ := rewindTM_run_ofCfg i u n hn (qyC .start ip T P o) rfl
    (fun p _ _ => by
      show T i (P i - n + p) = _
      rw [hT, hP, sub_self, zero_add])
  refine ⟨hrun.trans ?_, hcut⟩
  dsimp only [qyC]
  rw [hP, sub_self]

/-- **An embedded run, read through the transport.** The host run of `Turing.embedEmitTM` from a
normal-form configuration is the transport of the source run from its selected bank. -/
private theorem qy_embed_gen {m K : ℕ} {S : Type} {x : List Bool} (σ : Fin m ↪ Fin K)
    (M : MultiTapeTM m Bool S) (s : S) (ip : Fin (x.length + 2))
    (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool) (t : ℕ) :
    (embedEmitTM σ M).runFrom (qyC s ip T P o) t =
      embedEmitCfg σ T P o (M.runFrom (qyC s ip (fun i => T (σ i)) (fun i => P (σ i)) []) t) := by
  have hD : embedEmitCfg σ T P o (qyC s ip (fun i => T (σ i)) (fun i => P (σ i)) []) =
      (qyC s ip T P o : Cfg K Bool S x) :=
    embedEmitCfg_eq σ T P o _ _ rfl rfl (List.append_nil o) (fun _ => ⟨rfl, rfl⟩)
      (fun _ _ => ⟨rfl, rfl⟩)
  rw [← hD, embedEmitTM_runFrom]

/-- **An embedded run in normal form.** A source machine run along `σ` from the selected bank of
a normal-form configuration, ending in normal form, is the host run of `Turing.embedEmitTM`
from that configuration: the selected tapes and heads are the source's, every other one is
kept, and the source's output is appended. -/
private theorem qy_embed {m K : ℕ} {S : Type} {x : List Bool} (σ : Fin m ↪ Fin K)
    (M : MultiTapeTM m Bool S) (s s' : S) (ip ip' : Fin (x.length + 2))
    (T T' : Fin K → ℤ → Option Bool) (P P' : Fin K → ℤ) (o o' : List Bool)
    (T₀ : Fin m → ℤ → Option Bool) (P₀ : Fin m → ℤ) (t : ℕ)
    (hrun : M.runFrom (qyC s ip (fun i => T (σ i)) (fun i => P (σ i)) []) t =
      qyC s' ip' T₀ P₀ o')
    (hsel : ∀ i, T' (σ i) = T₀ i ∧ P' (σ i) = P₀ i)
    (hout : ∀ j, j ∉ Set.range σ → T' j = T j ∧ P' j = P j) :
    (embedEmitTM σ M).runFrom (qyC s ip T P o) t = qyC s' ip' T' P' (o ++ o') := by
  rw [qy_embed_gen, hrun]
  exact embedEmitCfg_eq σ T P o _ _ rfl rfl rfl (fun i => ⟨(hsel i).1.symm, (hsel i).2.symm⟩)
    (fun j hj => ⟨(hout j hj).1.symm, (hout j hj).2.symm⟩)

/-- **An embedded run's states.** At every time, the state of the embedded run from a
normal-form configuration is the source run's state from its selected bank. -/
private theorem qy_embed_state {m K : ℕ} {S : Type} {x : List Bool} (σ : Fin m ↪ Fin K)
    (M : MultiTapeTM m Bool S) (s : S) (ip : Fin (x.length + 2))
    (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool) (u : ℕ) :
    ((embedEmitTM σ M).runFrom (qyC s ip T P o) u).state =
      (M.runFrom (qyC s ip (fun i => T (σ i)) (fun i => P (σ i)) []) u).state := by
  rw [qy_embed_gen, embedEmitCfg_state]

/-- **A released call in normal form.** A call that reaches its exit first at the positive time
`t`, with `res` installed, run through the release adapter from its fresh state over the seam
of `arg`, reaches the right-tagged exit at `t`, with `res` installed, and not earlier.

**Proof sketch.** The normal-form start is the call's seam with its state replaced by the fresh
state, and the right-tagged seam of `res` is the normal-form endpoint (both by the fields of
`Turing.Cfg.mapState` and `Turing.Cfg.ofWords`). At every positive time the released run is the
call's run, right-tagged (`Turing.seamReleaseTM_runFrom_pos`), which gives the endpoint and, by
the call's positive cut, the cut at positive times; at time `0` the state is the left-tagged
fresh state. -/
private theorem qy_call {x : List Bool} (C : FinTM Bool) (entry exit : C.State)
    (arg res : List Bool) (t : ℕ) (hpos : 0 < t)
    (hcut : ∀ t', 0 < t' → t' < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t').state ≠ some exit)
    (hrun : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      Cfg.ofWords exit (stateWord C.k res)) :
    (seamReleaseTM C.tm entry).runFrom
        (qyC (x := x) (Sum.inl ()) 1 (fun i => FinTM.bufferTape (stateWord C.k arg i))
          (fun _ => 0) []) t =
      qyC (Sum.inr exit) 1 (fun i => FinTM.bufferTape (stateWord C.k res i)) (fun _ => 0) [] ∧
    ∀ u < t, ((seamReleaseTM C.tm entry).runFrom
        (qyC (x := x) (Sum.inl ()) 1 (fun i => FinTM.bufferTape (stateWord C.k arg i))
          (fun _ => 0) []) u).state ≠ some (Sum.inr exit) := by
  have hc : (Cfg.ofWords (input := x) entry (stateWord C.k arg)).state = some entry :=
    Cfg.ofWords_state entry _
  have hstart : (qyC (Sum.inl ()) 1 (fun i => FinTM.bufferTape (stateWord C.k arg i))
      (fun _ => 0) [] : Cfg C.k Bool (Unit ⊕ C.State) x) =
      (Cfg.ofWords (input := x) entry (stateWord C.k arg)).mapState fun _ => Sum.inl () := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, hc]
      rfl
    · rw [Cfg.mapState_inputPos, Cfg.ofWords_inputPos]
      rfl
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.ofWords_workTapes]
      rfl
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.ofWords_workTapePos]
      rfl
    · rw [Cfg.mapState_output, Cfg.ofWords_output]
      rfl
  have hend : ((Cfg.ofWords (input := x) exit (stateWord C.k res)).mapState
      (Sum.inr : C.State → Unit ⊕ C.State)) =
      qyC (Sum.inr exit) 1 (fun i => FinTM.bufferTape (stateWord C.k res i)) (fun _ => 0) [] := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, Cfg.ofWords_state]
      rfl
    · rw [Cfg.mapState_inputPos, Cfg.ofWords_inputPos]
      rfl
    · funext j q
      rw [Cfg.mapState_workTapes, Cfg.ofWords_workTapes]
      rfl
    · funext j
      rw [Cfg.mapState_workTapePos, Cfg.ofWords_workTapePos]
      rfl
    · rw [Cfg.mapState_output, Cfg.ofWords_output]
      rfl
  rw [hstart]
  refine ⟨?_, fun u hu => ?_⟩
  · rw [seamReleaseTM_runFrom_pos C.tm entry _ hc t hpos, hrun, hend]
  · rcases Nat.eq_zero_or_pos u with rfl | hu0
    · rw [MultiTapeTM.runFrom_zero, Cfg.mapState_state, hc]
      intro h
      exact Sum.inl_ne_inr (Option.some.inj h)
    · rw [seamReleaseTM_runFrom_pos C.tm entry _ hc u hu0, Cfg.mapState_state]
      intro h
      obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp h
      exact hcut u hu0 hu (hq.trans (congrArg some (Sum.inr.inj hqe)))

/-- **A hosted released call.** The install-call contract of `C` (positive exit time, positive
cut, endpoint), run through the release adapter embedded along `σ`, from a normal-form
configuration holding the argument's seam on the bank and the input head at `1`: at the call's
time the bank's tape `0` holds the result, everything else is kept, and the exit is not
reached earlier.

**Proof sketch.** The selected bank is the call's seam of `arg`, so the released call's run
(`qy_call`) transports along `σ` (`qy_embed`): the bank's tape `0` gets `res`, its other tapes
stay blank, and the unselected tapes are kept. The cut is the source's, read through
`qy_embed_state`. -/
private theorem qy_callHost {K : ℕ} {x : List Bool} (C : FinTM Bool) (hk : 0 < C.k)
    (σ : Fin C.k ↪ Fin K) (entry exit : C.State) (arg res : List Bool) (t : ℕ) (hpos : 0 < t)
    (hcut : ∀ t', 0 < t' → t' < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t').state ≠ some exit)
    (hrun : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      Cfg.ofWords exit (stateWord C.k res))
    (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool)
    (hT : ∀ i, T (σ i) = FinTM.bufferTape (stateWord C.k arg i)) (hP : ∀ i, P (σ i) = 0) :
    (embedEmitTM σ (seamReleaseTM C.tm entry)).runFrom (qyC (x := x) (Sum.inl ()) 1 T P o) t =
      qyC (Sum.inr exit) 1 (Function.update T (σ ⟨0, hk⟩) (FinTM.bufferTape res)) P o ∧
    ∀ u < t, ((embedEmitTM σ (seamReleaseTM C.tm entry)).runFrom
      (qyC (x := x) (Sum.inl ()) 1 T P o) u).state ≠ some (Sum.inr exit) := by
  have hT' : (fun i => T (σ i)) = fun i => FinTM.bufferTape (stateWord C.k arg i) := funext hT
  have hP' : (fun i => P (σ i)) = fun _ => (0 : ℤ) := funext hP
  obtain ⟨hr, hc⟩ := qy_call (x := x) C entry exit arg res t hpos hcut hrun
  refine ⟨?_, fun u hu => ?_⟩
  · have h := qy_embed σ (seamReleaseTM C.tm entry) (Sum.inl ()) (Sum.inr exit) 1 1 T
      (Function.update T (σ ⟨0, hk⟩) (FinTM.bufferTape res)) P P o []
      (fun i => FinTM.bufferTape (stateWord C.k res i)) (fun _ => 0) t (by rw [hT', hP']; exact hr)
      (fun i => ⟨?_, hP i⟩) (fun j hj => ⟨Function.update_of_ne
        (fun h => hj ⟨_, h.symm⟩) _ _, rfl⟩)
    · rw [List.append_nil] at h
      exact h
    · by_cases hi : i = ⟨0, hk⟩
      · subst hi
        dsimp only
        rw [Function.update_self, stateWord_eq, if_pos rfl]
      · have hne : σ i ≠ σ ⟨0, hk⟩ := fun h => hi (σ.injective h)
        have hi0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
        dsimp only
        rw [Function.update_of_ne hne, hT, stateWord_eq, stateWord_eq, if_neg hi0, if_neg hi0]
  · rw [qy_embed_state, hT', hP']
    exact hc u hu

/-- **One step of an own leaf.** At a live normal-form configuration, a transition that writes
nothing, keeps the input head, moves each work head by `mv j` and emits `out` gives the
normal-form configuration with the heads moved and the emission appended. -/
private theorem qy_step {K : ℕ} {S : Type} {x : List Bool} (M : MultiTapeTM K Bool S) (s s' : S)
    (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool)
    (mv : Fin K → SignType) (out : Option Bool)
    (htr : M.tr s (qyC s ip T P o : Cfg K Bool S x).inputSymbol (fun j => T j (P j)) =
      ⟨0, fun j => (none, mv j), out, some s'⟩) :
    M.step (qyC s ip T P o) = qyC s' ip T (fun j => P j + (mv j : ℤ)) (o ++ out.toList) := by
  have hw : (qyC s ip T P o : Cfg K Bool S x).workTapeSymbols = fun j => T j (P j) := by
    funext j
    rw [Cfg.workTapeSymbols_eq]
    rfl
  rw [MultiTapeTM.step_of_some (rfl : (qyC s ip T P o : Cfg K Bool S x).state = some s), hw, htr]
  apply Cfg.ext
  · rw [Action.apply_state]
    rfl
  · rw [Action.apply_inputPos, moveInputPos_zero]
    rfl
  · funext j q
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    show Function.update (T j) (P j) ((none : Option (Option Bool)).getD (T j (P j))) q = T j q
    rw [Option.getD_none, Function.update_eq_self]
  · funext j
    rw [Action.apply_workTapePos]
    rfl
  · rw [Action.apply_output]
    rfl

/-- The control states of the length comparison `Turing.NTimeDiag.qyCmpTM`: the forward scan,
the return pass carrying the verdict, and the live exits, one per verdict. -/
private inductive QyCmp
  | scan
  | back (v : Ordering)
  | done (v : Ordering)
  deriving DecidableEq, Fintype

/-- **The length comparison** (leaf L3, the unary compare). Started with the heads of tapes `a`
and `b` on the first cells of two words, it moves both heads right in lockstep while both read a
symbol. At the first blank under either head it knows how the lengths compare and walks both
heads back in lockstep to their starts, then enters the live exit `done` of the verdict. Nothing
is written and the input head stays. On unary words it compares the numbers. No public row
serves: `Turing.compareTM_contract` decides equality of the two words at `compareStop`, with no
order verdict, and `Turing.walkTM_run_ofCfg` moves heads by one word's length but reports
nothing about the other tape. -/
private def qyCmpTM (K : ℕ) (a b : Fin K) : MultiTapeTM K Bool QyCmp where
  q₀ := .scan
  tr := fun q _ w =>
    match q with
    | .scan =>
      match w a, w b with
      | some _, some _ =>
        ⟨0, fun j => (none, if j = a ∨ j = b then .pos else 0), none, some .scan⟩
      | none, none =>
        ⟨0, fun j => (none, if j = a ∨ j = b then .neg else 0), none, some (.back .eq)⟩
      | none, some _ =>
        ⟨0, fun j => (none, if j = a ∨ j = b then .neg else 0), none, some (.back .lt)⟩
      | some _, none =>
        ⟨0, fun j => (none, if j = a ∨ j = b then .neg else 0), none, some (.back .gt)⟩
    | .back v =>
      match w a with
      | some _ => ⟨0, fun j => (none, if j = a ∨ j = b then .neg else 0), none, some (.back v)⟩
      | none => ⟨0, fun j => (none, if j = a ∨ j = b then .pos else 0), none, some (.done v)⟩
    | .done v => ⟨0, fun _ => (none, 0), none, some (.done v)⟩


/-- The lockstep head vector of `Turing.NTimeDiag.qyCmpTM`: both compared heads at `i`. -/
private def qyAt2 {K : ℕ} (P : Fin K → ℤ) (a b : Fin K) (i : ℤ) : Fin K → ℤ :=
  Function.update (Function.update P a i) b i

/-- Moving both compared heads by one step in the same direction. -/
private theorem qyAt2_move {K : ℕ} (P : Fin K → ℤ) (a b : Fin K) (i : ℤ) (d : SignType) (dz : ℤ)
    (hd : (d : ℤ) = dz) :
    (fun j => qyAt2 P a b i j + ((if j = a ∨ j = b then d else 0 : SignType) : ℤ)) =
      qyAt2 P a b (i + dz) := by
  funext j
  unfold qyAt2
  by_cases hb : j = b
  · subst hb
    rw [Function.update_self, Function.update_self, if_pos (Or.inr rfl), hd]
  · rw [Function.update_of_ne hb, Function.update_of_ne hb]
    by_cases ha : j = a
    · subst ha
      rw [Function.update_self, Function.update_self, if_pos (Or.inl rfl), hd]
    · rw [Function.update_of_ne ha, Function.update_of_ne ha, if_neg (by tauto),
        SignType.coe_zero, add_zero]

/-- **The length comparison's run.** From the starts of words `u` and `v` on tapes `a` and `b`,
`Turing.NTimeDiag.qyCmpTM` reaches `done (compare |u| |v|)` after exactly
`2 · min |u| |v| + 2` steps, with nothing changed, and no exit earlier.

**Proof sketch.** Write `m = min |u| |v|`. By induction on `i ≤ m`, after `i` steps both heads
are at `i` in the scan (each step reads two symbols and moves right, `qy_step`). At `m` at least
one head reads a blank, and which ones do determines `compare |u| |v|`; one step turns into the
return pass at `m - 1`. By induction again both heads walk left over cells of `u`, reaching
`-1` after `m` more steps, and one step right enters the verdict's exit with the heads back at
`0`. The intermediate states are scan or return states, so no exit comes earlier. -/
private theorem qy_cmp_run {K : ℕ} {x : List Bool} (a b : Fin K) (hab : a ≠ b)
    (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool)
    (u v : List Bool) (hTa : T a = FinTM.bufferTape u) (hTb : T b = FinTM.bufferTape v)
    (hPa : P a = 0) (hPb : P b = 0) :
    (qyCmpTM K a b).runFrom (qyC .scan ip T P o) (2 * min u.length v.length + 2) =
        qyC (QyCmp.done (compare u.length v.length)) ip T P o ∧
      ∀ t < 2 * min u.length v.length + 2, ∀ w,
        ((qyCmpTM K a b).runFrom (qyC .scan ip T P o) t).state ≠ some (.done w) := by
  set m := min u.length v.length with hm
  have hP0 : qyAt2 P a b 0 = P := by
    funext j
    unfold qyAt2
    by_cases hb : j = b
    · subst hb; rw [Function.update_self, hPb]
    · rw [Function.update_of_ne hb]
      by_cases ha : j = a
      · subst ha; rw [Function.update_self, hPa]
      · rw [Function.update_of_ne ha]
  have hra : ∀ i : ℤ, T a (qyAt2 P a b i a) = FinTM.bufferTape u i := by
    intro i
    unfold qyAt2
    rw [Function.update_of_ne hab, Function.update_self, hTa]
  have hrb : ∀ i : ℤ, T b (qyAt2 P a b i b) = FinTM.bufferTape v i := by
    intro i
    unfold qyAt2
    rw [Function.update_self, hTb]
  -- the forward scan
  have hscan : ∀ i ≤ m, (qyCmpTM K a b).runFrom (qyC .scan ip T P o) i =
      qyC .scan ip T (qyAt2 P a b i) o := by
    intro i
    induction i with
    | zero => intro _; rw [MultiTapeTM.runFrom_zero, Nat.cast_zero, hP0]
    | succ i ih =>
      intro hi
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
      have hu : FinTM.bufferTape u (i : ℤ) = some u[i] := by
        rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem (by omega)]
      have hv : FinTM.bufferTape v (i : ℤ) = some v[i] := by
        rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem (by omega)]
      have h := qy_step (qyCmpTM K a b) QyCmp.scan QyCmp.scan ip T (qyAt2 P a b i) o
        (fun j => if j = a ∨ j = b then .pos else 0) none (by
          simp only [qyCmpTM]
          rw [hra, hrb, hu, hv])
      rw [h, qyAt2_move P a b i .pos 1 (by rfl), Option.toList_none, List.append_nil]
      push_cast
      rfl
  -- the turn
  have hturn : (qyCmpTM K a b).runFrom (qyC .scan ip T P o) (m + 1) =
      qyC (QyCmp.back (compare u.length v.length)) ip T (qyAt2 P a b ((m : ℤ) - 1)) o := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hscan m le_rfl]
    have hmv : (fun j => qyAt2 P a b m j + ((if j = a ∨ j = b then SignType.neg else 0 :
        SignType) : ℤ)) = qyAt2 P a b ((m : ℤ) - 1) := by
      rw [qyAt2_move P a b m .neg (-1) (by rfl), sub_eq_add_neg]
    rcases lt_trichotomy u.length v.length with hlt | heq | hgt
    · have hmu : m = u.length := by omega
      have hu : FinTM.bufferTape u (m : ℤ) = none := by
        rw [FinTM.bufferTape_nat, List.getElem?_eq_none (by omega)]
      have hv : FinTM.bufferTape v (m : ℤ) = some v[m] := by
        rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem (by omega)]
      rw [qy_step (qyCmpTM K a b) QyCmp.scan (QyCmp.back .lt) ip T (qyAt2 P a b m) o
        (fun j => if j = a ∨ j = b then .neg else 0) none (by
          simp only [qyCmpTM]
          rw [hra, hrb, hu, hv]), hmv, Option.toList_none, List.append_nil,
        (compare_lt_iff_lt.mpr hlt)]
    · have hu : FinTM.bufferTape u (m : ℤ) = none := by
        rw [FinTM.bufferTape_nat, List.getElem?_eq_none (by omega)]
      have hv : FinTM.bufferTape v (m : ℤ) = none := by
        rw [FinTM.bufferTape_nat, List.getElem?_eq_none (by omega)]
      rw [qy_step (qyCmpTM K a b) QyCmp.scan (QyCmp.back .eq) ip T (qyAt2 P a b m) o
        (fun j => if j = a ∨ j = b then .neg else 0) none (by
          simp only [qyCmpTM]
          rw [hra, hrb, hu, hv]), hmv, Option.toList_none, List.append_nil,
        (compare_eq_iff_eq.mpr heq)]
    · have hu : FinTM.bufferTape u (m : ℤ) = some u[m] := by
        rw [FinTM.bufferTape_nat, List.getElem?_eq_getElem (by omega)]
      have hv : FinTM.bufferTape v (m : ℤ) = none := by
        rw [FinTM.bufferTape_nat, List.getElem?_eq_none (by omega)]
      rw [qy_step (qyCmpTM K a b) QyCmp.scan (QyCmp.back .gt) ip T (qyAt2 P a b m) o
        (fun j => if j = a ∨ j = b then .neg else 0) none (by
          simp only [qyCmpTM]
          rw [hra, hrb, hu, hv]), hmv, Option.toList_none, List.append_nil,
        (compare_gt_iff_gt.mpr hgt)]
  -- the return pass
  have hback : ∀ i ≤ m, (qyCmpTM K a b).runFrom (qyC .scan ip T P o) (m + 1 + i) =
      qyC (QyCmp.back (compare u.length v.length)) ip T
        (qyAt2 P a b ((m : ℤ) - 1 - i)) o := by
    intro i
    induction i with
    | zero => intro _; rw [Nat.add_zero, hturn, Nat.cast_zero, sub_zero]
    | succ i ih =>
      intro hi
      rw [← Nat.add_assoc, MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
      have hu : FinTM.bufferTape u ((m : ℤ) - 1 - i) = some u[m - 1 - i] := by
        rw [show ((m : ℤ) - 1 - i) = ((m - 1 - i : ℕ) : ℤ) by omega, FinTM.bufferTape_nat,
          List.getElem?_eq_getElem (by omega)]
      rw [qy_step (qyCmpTM K a b) _ _ ip T _ o (fun j => if j = a ∨ j = b then .neg else 0) none
        (by
          simp only [qyCmpTM]
          rw [hra, hu]), qyAt2_move P a b _ .neg (-1) (by rfl), Option.toList_none,
        List.append_nil]
      congr 2
      push_cast
      ring
  have hend : (qyCmpTM K a b).runFrom (qyC .scan ip T P o) (2 * m + 2) =
      qyC (QyCmp.done (compare u.length v.length)) ip T P o := by
    rw [show 2 * m + 2 = m + 1 + m + 1 by ring, MultiTapeTM.runFrom_succ_eq_step',
      hback m le_rfl]
    have hu : FinTM.bufferTape u ((m : ℤ) - 1 - m) = none := by
      rw [show ((m : ℤ) - 1 - m) = -1 by ring, FinTM.bufferTape_left]
    rw [qy_step (qyCmpTM K a b) _ _ ip T _ o (fun j => if j = a ∨ j = b then .pos else 0) none
      (by
        simp only [qyCmpTM]
        rw [hra, hu]), qyAt2_move P a b _ .pos 1 (by rfl), Option.toList_none, List.append_nil,
      show ((m : ℤ) - 1 - m + 1) = 0 by ring, hP0]
  refine ⟨hend, fun t ht w => ?_⟩
  by_cases h1 : t ≤ m
  · rw [hscan t h1]
    intro h
    cases Option.some.inj h
  · obtain ⟨i, rfl⟩ : ∃ i, t = m + 1 + i := ⟨t - (m + 1), by omega⟩
    rw [hback i (by omega)]
    intro h
    cases Option.some.inj h


/-- The control states of the writer's emitter `Turing.NTimeDiag.qyEmitTM`: emitting the fixed
prefix, reading a cell, holding a read symbol while looking ahead, emitting its copies, emitting
the fixed suffix, and the exit, whose action halts. -/
private inductive QyEm (np ns rr : ℕ)
  | pre (j : Fin (np + 1))
  | rd
  | got (b : Bool)
  | em (b : Bool) (k : Fin (rr + 1))
  | suf (j : Fin (ns + 1))
  | done
  deriving DecidableEq, Fintype

/-- **The writer's emitter** (leaf L6). Emit the fixed word `pre`; then emit the word under the
head of tape `i`, each symbol `rr + 1` times, omitting its last symbol when `dl` holds (one cell
of lookahead); then emit the fixed word `suf` and enter `done`, whose action halts. Nothing is
written and the input head stays. It is the fixed-word emission chain of `Turing.FinTM.emitAction`
around a one-tape scan: no public row emits a tape word with repetition. -/
private def qyEmitTM (K : ℕ) (i : Fin K) (pre suf : List Bool) (rr : ℕ) (dl : Bool) :
    MultiTapeTM K Bool (QyEm pre.length suf.length rr) where
  q₀ := .pre 0
  tr := fun q _ w =>
    match q with
    | .pre j =>
      if h : (j : ℕ) < pre.length then
        ⟨0, fun _ => (none, 0), some pre[(j : ℕ)], some (.pre ⟨j + 1, by omega⟩)⟩
      else ⟨0, fun _ => (none, 0), none, some .rd⟩
    | .rd =>
      match w i with
      | some b => ⟨0, fun j => (none, if j = i then .pos else 0), none, some (.got b)⟩
      | none => ⟨0, fun _ => (none, 0), none, some (.suf 0)⟩
    | .got b =>
      if w i = none ∧ dl = true then ⟨0, fun _ => (none, 0), none, some (.suf 0)⟩
      else ⟨0, fun _ => (none, 0), none, some (.em b 0)⟩
    | .em b k =>
      if h : (k : ℕ) < rr then ⟨0, fun _ => (none, 0), some b, some (.em b ⟨k + 1, by omega⟩)⟩
      else ⟨0, fun _ => (none, 0), some b, some .rd⟩
    | .suf j =>
      if h : (j : ℕ) < suf.length then
        ⟨0, fun _ => (none, 0), some suf[(j : ℕ)], some (.suf ⟨j + 1, by omega⟩)⟩
      else ⟨0, fun _ => (none, 0), none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, none⟩

/-- The emitter's body: the word with each symbol written `rr + 1` times, its last symbol omitted
when `dl` holds. -/
private def qyBody (dl : Bool) (rr : ℕ) (w : List Bool) : List Bool :=
  (if dl then w.dropLast else w).flatMap fun b => List.replicate (rr + 1) b

/-- Heads unmoved: the zero displacement. -/
private theorem qy_noMove {K : ℕ} (P : Fin K → ℤ) :
    (fun j => P j + ((0 : SignType) : ℤ)) = P := by
  funext j
  rw [SignType.coe_zero, add_zero]

/-- One head moved right. -/
private theorem qy_moveOne {K : ℕ} (P : Fin K → ℤ) (i : Fin K) :
    (fun j => P j + ((if j = i then SignType.pos else 0 : SignType) : ℤ)) =
      Function.update P i (P i + 1) := by
  funext j
  by_cases h : j = i
  · subst h
    rw [Function.update_self, if_pos rfl]
    rfl
  · rw [Function.update_of_ne h, if_neg h, SignType.coe_zero, add_zero]

/-- One step of a run. -/
private theorem qy_run_one {K : ℕ} {S : Type} {x : List Bool} (M : MultiTapeTM K Bool S)
    (c : Cfg K Bool S x) : M.runFrom c 1 = M.step c := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]

/-- Two steps of a run. -/
private theorem qy_run_two {K : ℕ} {S : Type} {x : List Bool} (M : MultiTapeTM K Bool S)
    (c : Cfg K Bool S x) : M.runFrom c 2 = M.step (M.runFrom c 1) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step']

/-- **The emitter's run.** From the start of the word `w` on tape `i`, `qyEmitTM` emits
`pre ++ qyBody dl rr w ++ suf` and reaches `done`, the head of tape `i` at `|w|`, within
`|pre| + |suf| + 3 + |w| · (rr + 3)` steps, and not earlier.

**Proof sketch.** Three inductions over the emission chains and the word, each step read by
`qy_step`. The prefix chain emits `pre` in `|pre|` steps and one step enters the read state.
For the body, by induction on the rest of the word from cell `k`: a blank ends it; a symbol `b`
is read, the head moves on, and one look-ahead step either stops (the last symbol under `dl`) or
enters the copy chain, which emits `b` exactly `rr + 1` times and returns to the read state.
The suffix chain emits `suf` and enters `done`. Every intermediate state is a chain, read, hold
or copy state, so `done` is not reached earlier. -/
private theorem qy_emit_run {K : ℕ} {x : List Bool} (i : Fin K) (pre suf : List Bool) (rr : ℕ)
    (dl : Bool) (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ)
    (o : List Bool) (w : List Bool) (hT : T i = FinTM.bufferTape w) (hP : P i = 0) :
    ∃ t ≤ pre.length + suf.length + 3 + w.length * (rr + 3),
      (qyEmitTM K i pre suf rr dl).runFrom (qyC (.pre 0) ip T P o) t =
        qyC .done ip T (Function.update P i w.length) (o ++ pre ++ qyBody dl rr w ++ suf) ∧
      ∀ u < t, ((qyEmitTM K i pre suf rr dl).runFrom (qyC (.pre 0) ip T P o) u).state ≠
        some .done := by
  set M := qyEmitTM K i pre suf rr dl with hM
  -- the prefix
  have hpre : ∀ (j : ℕ) (hj : j ≤ pre.length), M.runFrom (qyC (.pre 0) ip T P o) j =
      qyC (.pre ⟨j, by omega⟩) ip T P (o ++ pre.take j) := by
    intro j
    induction j with
    | zero => intro _; rw [MultiTapeTM.runFrom_zero, List.take_zero, List.append_nil]; rfl
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        qy_step M _ (.pre ⟨j + 1, by omega⟩) ip T P _ (fun _ => 0) (some pre[j]) (by
          simp only [hM, qyEmitTM]
          rw [dif_pos (show j < pre.length by omega)]), qy_noMove, List.append_assoc,
        Option.toList_some, List.take_succ, List.getElem?_eq_getElem (by omega)]
      rfl
  have hpre' : M.runFrom (qyC (.pre 0) ip T P o) (pre.length + 1) =
      qyC .rd ip T P (o ++ pre) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hpre _ le_rfl,
      qy_step M _ .rd ip T P _ (fun _ => 0) none (by
        simp only [hM, qyEmitTM]
        rw [dif_neg (show ¬ (pre.length < pre.length) by omega)]), qy_noMove,
      List.take_length, Option.toList_none, List.append_nil]
  -- the copies of one symbol
  have hem : ∀ (b : Bool) (Q : Fin K → ℤ) (o' : List Bool) (k : ℕ) (hk : k ≤ rr),
      M.runFrom (qyC (.em b 0) ip T Q o') k =
        qyC (.em b ⟨k, by omega⟩) ip T Q (o' ++ List.replicate k b) := by
    intro b Q o' k
    induction k with
    | zero => intro _; rw [MultiTapeTM.runFrom_zero, List.replicate_zero, List.append_nil]; rfl
    | succ k ih =>
      intro hk
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        qy_step M _ (.em b ⟨k + 1, by omega⟩) ip T Q _ (fun _ => 0) (some b) (by
          simp only [hM, qyEmitTM]
          rw [dif_pos (show k < rr by omega)]), qy_noMove, List.append_assoc,
        Option.toList_some, List.replicate_succ']
  have hem' : ∀ (b : Bool) (Q : Fin K → ℤ) (o' : List Bool),
      M.runFrom (qyC (.em b 0) ip T Q o') (rr + 1) =
        qyC .rd ip T Q (o' ++ List.replicate (rr + 1) b) := by
    intro b Q o'
    rw [MultiTapeTM.runFrom_succ_eq_step', hem b Q o' rr le_rfl,
      qy_step M _ .rd ip T Q _ (fun _ => 0) (some b) (by
        simp only [hM, qyEmitTM]
        rw [dif_neg (show ¬ (rr < rr) by omega)]), qy_noMove, List.append_assoc,
      Option.toList_some, List.replicate_succ' (n := rr)]
  -- the body: from the cell `k`, with the rest of the word `rest`
  have hbody : ∀ (rest : List Bool) (k : ℕ) (o' : List Bool), k ≤ w.length → w.drop k = rest →
      ∃ t ≤ rest.length * (rr + 3) + 1,
        M.runFrom (qyC .rd ip T (Function.update P i k) o') t =
          qyC (.suf 0) ip T (Function.update P i w.length) (o' ++
            (if dl then rest.dropLast else rest).flatMap fun b => List.replicate (rr + 1) b) ∧
        ∀ u < t, (M.runFrom (qyC .rd ip T (Function.update P i k) o') u).state ≠ some .done := by
    intro rest
    induction rest with
    | nil =>
      intro k o' hkw' hk
      have hkw : k = w.length := by
        have := congrArg List.length hk
        rw [List.length_drop, List.length_nil] at this
        omega
      subst hkw
      refine ⟨1, by omega, ?_, ?_⟩
      · rw [qy_run_one, qy_step M _ (.suf 0) ip T _ _ (fun _ => 0) none (by
            have hn : T i (Function.update P i (w.length : ℤ) i) = none := by
              rw [Function.update_self, hT, FinTM.bufferTape_nat, List.getElem?_eq_none le_rfl]
            simp only [hM, qyEmitTM, hn]),
          qy_noMove, Option.toList_none, List.append_nil]
        cases dl <;> simp
      · intro u hu
        obtain rfl : u = 0 := by omega
        rw [MultiTapeTM.runFrom_zero]
        intro h
        cases Option.some.inj h
    | cons b rest ih =>
      intro k o' hkw' hk
      have hkb : FinTM.bufferTape w (k : ℤ) = some b := by
        rw [FinTM.bufferTape_nat, ← List.head?_drop, hk]
        rfl
      have hk1 : FinTM.bufferTape w ((k : ℤ) + 1) = rest.head? := by
        rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring, FinTM.bufferTape_nat,
          ← List.head?_drop, ← List.drop_drop, hk]
        rfl
      have hstep1 : M.runFrom (qyC .rd ip T (Function.update P i k) o') 1 =
          qyC (.got b) ip T (Function.update P i ((k : ℤ) + 1)) o' := by
        rw [qy_run_one, qy_step M _ (.got b) ip T _ _
            (fun j => if j = i then .pos else 0) none (by
            have hn : T i (Function.update P i (k : ℤ) i) = some b := by
              rw [Function.update_self, hT, hkb]
            simp only [hM, qyEmitTM, hn]), qy_moveOne, Function.update_self,
          Function.update_idem, Option.toList_none, List.append_nil]
      by_cases hlast : rest = [] ∧ dl = true
      · obtain ⟨rfl, hdl⟩ := hlast
        refine ⟨2, by simp only [List.length_cons, List.length_nil]; omega, ?_, ?_⟩
        · rw [qy_run_two, hstep1,
            qy_step M _ (.suf 0) ip T _ _ (fun _ => 0) none (by
              have hn : T i (Function.update P i ((k : ℤ) + 1) i) = none := by
                rw [Function.update_self, hT, hk1]
                rfl
              simp only [hM, qyEmitTM, hn, hdl]
              rfl), qy_noMove, Option.toList_none, List.append_nil, hdl]
          have hkw : k + 1 = w.length := by
            have := congrArg List.length hk
            rw [List.length_drop, List.length_cons, List.length_nil] at this
            omega
          rw [show ((k : ℤ) + 1) = ((w.length : ℕ) : ℤ) by omega]
          simp
        · intro u hu
          rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl
          · rw [MultiTapeTM.runFrom_zero]
            intro h
            cases Option.some.inj h
          · rw [hstep1]
            intro h
            cases Option.some.inj h
      · have hstep2 : M.runFrom (qyC .rd ip T (Function.update P i k) o') 2 =
            qyC (.em b 0) ip T (Function.update P i ((k : ℤ) + 1)) o' := by
          rw [qy_run_two, hstep1,
            qy_step M _ (.em b 0) ip T _ _ (fun _ => 0) none (by
              have hn : T i (Function.update P i ((k : ℤ) + 1) i) = rest.head? := by
                rw [Function.update_self, hT, hk1]
              have hc : ¬(rest.head? = none ∧ dl = true) := by
                rintro ⟨h1, h2⟩
                exact hlast ⟨List.head?_eq_none_iff.mp h1, h2⟩
              simp only [hM, qyEmitTM, hn, if_neg hc]), qy_noMove,
            Option.toList_none, List.append_nil]
        have hrd : M.runFrom (qyC .rd ip T (Function.update P i k) o') (2 + (rr + 1)) =
            qyC .rd ip T (Function.update P i ((k + 1 : ℕ) : ℤ))
              (o' ++ List.replicate (rr + 1) b) := by
          rw [MultiTapeTM.runFrom_add, hstep2, hem']
          push_cast
          rfl
        have hkl : k + 1 ≤ w.length := by
          have := congrArg List.length hk
          rw [List.length_drop, List.length_cons] at this
          omega
        obtain ⟨t, ht, hrun, hcut⟩ := ih (k + 1) (o' ++ List.replicate (rr + 1) b) hkl
          (by rw [← List.drop_drop, hk]; rfl)
        refine ⟨2 + (rr + 1) + t, by rw [List.length_cons]; nlinarith, ?_, ?_⟩
        · rw [MultiTapeTM.runFrom_add, hrd, hrun, List.append_assoc]
          congr 2
          have hd : (if dl then (b :: rest).dropLast else b :: rest) =
              b :: (if dl then rest.dropLast else rest) := by
            cases dl
            · rfl
            · have hr : rest ≠ [] := fun h => hlast ⟨h, rfl⟩
              simp only [if_true]
              exact List.dropLast_cons_of_ne_nil hr
          rw [hd, List.flatMap_cons]
        · intro u hu
          by_cases h2 : u < 2
          · rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl
            · rw [MultiTapeTM.runFrom_zero]
              intro h
              cases Option.some.inj h
            · rw [hstep1]
              intro h
              cases Option.some.inj h
          · by_cases h3 : u < 2 + (rr + 1)
            · obtain ⟨v, rfl⟩ : ∃ v, u = 2 + v := ⟨u - 2, by omega⟩
              rw [MultiTapeTM.runFrom_add, hstep2]
              rcases (show v ≤ rr by omega).lt_or_eq with hv | rfl
              · rw [hem b _ _ v hv.le]
                intro h
                cases Option.some.inj h
              · rw [hem b _ _ v le_rfl]
                intro h
                cases Option.some.inj h
            · obtain ⟨v, rfl⟩ : ∃ v, u = 2 + (rr + 1) + v := ⟨u - (2 + (rr + 1)), by omega⟩
              rw [MultiTapeTM.runFrom_add, hrd]
              exact hcut v (by omega)
  -- the suffix
  have hsuf : ∀ (Q : Fin K → ℤ) (o' : List Bool) (j : ℕ) (hj : j ≤ suf.length),
      M.runFrom (qyC (.suf 0) ip T Q o') j =
        qyC (.suf ⟨j, by omega⟩) ip T Q (o' ++ suf.take j) := by
    intro Q o' j
    induction j with
    | zero => intro _; rw [MultiTapeTM.runFrom_zero, List.take_zero, List.append_nil]; rfl
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        qy_step M _ (.suf ⟨j + 1, by omega⟩) ip T Q _ (fun _ => 0) (some suf[j]) (by
          simp only [hM, qyEmitTM]
          rw [dif_pos (show j < suf.length by omega)]), qy_noMove, List.append_assoc,
        Option.toList_some, List.take_succ, List.getElem?_eq_getElem (by omega)]
      rfl
  have hsuf' : ∀ (Q : Fin K → ℤ) (o' : List Bool),
      M.runFrom (qyC (.suf 0) ip T Q o') (suf.length + 1) = qyC .done ip T Q (o' ++ suf) := by
    intro Q o'
    rw [MultiTapeTM.runFrom_succ_eq_step', hsuf Q o' _ le_rfl,
      qy_step M _ .done ip T Q _ (fun _ => 0) none (by
        simp only [hM, qyEmitTM]
        rw [dif_neg (show ¬ (suf.length < suf.length) by omega)]), qy_noMove,
      List.take_length, Option.toList_none, List.append_nil]
  -- assembly
  obtain ⟨tb, htb, hbrun, hbcut⟩ := hbody w 0 (o ++ pre) (Nat.zero_le _) (List.drop_zero)
  have hP' : Function.update P i ((0 : ℕ) : ℤ) = P := by
    rw [Nat.cast_zero, ← hP, Function.update_eq_self]
  rw [hP'] at hbrun hbcut
  refine ⟨pre.length + 1 + tb + (suf.length + 1), by nlinarith, ?_, ?_⟩
  · rw [MultiTapeTM.runFrom_add _ (pre.length + 1 + tb) (suf.length + 1),
      MultiTapeTM.runFrom_add _ (pre.length + 1) tb, hpre', hbrun, hsuf']
    rfl
  · intro u hu
    by_cases h1 : u ≤ pre.length
    · rw [hpre u h1]
      intro h
      cases Option.some.inj h
    · by_cases h2 : u < pre.length + 1 + tb
      · obtain ⟨v, rfl⟩ : ∃ v, u = pre.length + 1 + v := ⟨u - (pre.length + 1), by omega⟩
        rw [MultiTapeTM.runFrom_add, hpre']
        exact hbcut v (by omega)
      · obtain ⟨v, rfl⟩ : ∃ v, u = pre.length + 1 + tb + v := ⟨u - (pre.length + 1 + tb), by omega⟩
        rw [MultiTapeTM.runFrom_add _ (pre.length + 1 + tb) v,
          MultiTapeTM.runFrom_add _ (pre.length + 1) tb, hpre', hbrun, hsuf _ _ v (by omega)]
        intro h
        cases Option.some.inj h

/-- **A released call stops first at its exit time.** From the install call's contract alone (a
positive exit time, the positive cut, the endpoint), the call wrapped by `seamReleaseTM` at its
entry, started at the fresh state and stopped at `Sum.inr exit`, first stops exactly at the
call's exit time, at the right-tagged endpoint. No `entry ≠ exit` is needed.

**Proof sketch.** At every positive time the released run is the call's run, right-tagged
(`Turing.seamReleaseTM_runFrom_pos`). At the exit time it is therefore the right-tagged
endpoint, stopped. Earlier it is the fresh state at time `0`, and the call's live, right-tagged
state off `exit` at positive times (the positive cut; liveness from the endpoint, by
`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`), so not stopped. -/
private theorem qy_release_first_stop (C : FinTM Bool) (entry exit : C.State)
    (x arg out : List Bool) (t : ℕ) (hpos : 0 < t)
    (hcut : ∀ t', 0 < t' → t' < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t').state ≠ some exit)
    (hrun : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      Cfg.ofWords exit (stateWord C.k out)) :
    ((seamReleaseTM C.tm entry).runFrom
        ((Cfg.ofWords (input := x) entry (stateWord C.k arg)).mapState fun _ => Sum.inl ())
        t).Stopped (fun s => decide (s = Sum.inr exit)) ∧
    (∀ u < t, ¬((seamReleaseTM C.tm entry).runFrom
        ((Cfg.ofWords (input := x) entry (stateWord C.k arg)).mapState fun _ => Sum.inl ())
        u).Stopped (fun s => decide (s = Sum.inr exit))) ∧
    (seamReleaseTM C.tm entry).runFrom
        ((Cfg.ofWords (input := x) entry (stateWord C.k arg)).mapState fun _ => Sum.inl ()) t =
      (Cfg.ofWords (input := x) exit (stateWord C.k out)).mapState Sum.inr := by
  have hc : (Cfg.ofWords (input := x) entry (stateWord C.k arg)).state = some entry :=
    Cfg.ofWords_state entry _
  have hend := seamReleaseTM_runFrom_pos C.tm entry _ hc t hpos
  rw [hrun] at hend
  have hlive : ∀ u ≤ t,
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) u).state ≠ none := by
    refine MultiTapeTM.runFrom_state_ne_none_of_le C.tm _ t ?_
    rw [hrun, Cfg.ofWords_state]
    exact Option.some_ne_none _
  refine ⟨?_, fun u hu => ?_, hend⟩
  · rw [hend, Cfg.stopped_iff, Cfg.mapState_state, Cfg.ofWords_state]
    exact Or.inr ⟨Sum.inr exit, rfl, decide_eq_true rfl⟩
  · rw [Cfg.stopped_iff]
    rintro (hnone | ⟨s, hs, hstop⟩)
    · rcases Nat.eq_zero_or_pos u with rfl | hu0
      · rw [MultiTapeTM.runFrom_zero, Cfg.mapState_state, hc] at hnone
        exact Option.some_ne_none _ hnone
      · rw [seamReleaseTM_runFrom_pos C.tm entry _ hc u hu0, Cfg.mapState_state] at hnone
        exact hlive u hu.le (Option.map_eq_none_iff.mp hnone)
    · have hse : s = Sum.inr exit := of_decide_eq_true hstop
      subst hse
      rcases Nat.eq_zero_or_pos u with rfl | hu0
      · rw [MultiTapeTM.runFrom_zero, Cfg.mapState_state, hc] at hs
        exact Sum.inl_ne_inr (Option.some.inj hs)
      · rw [seamReleaseTM_runFrom_pos C.tm entry _ hc u hu0, Cfg.mapState_state] at hs
        obtain ⟨q, hq, hqe⟩ := Option.map_eq_some_iff.mp hs
        exact hcut u hu0 hu (hq.trans (congrArg some (Sum.inr.inj hqe)))

/-- **A call before its exit is silent.** Every configuration of an install call before its exit
has empty output: output only grows, and the exit's output is `[]`. -/
private theorem qy_call_output_nil (C : FinTM Bool) (entry exit : C.State) (x arg out : List Bool)
    (t v : ℕ) (hv : v ≤ t)
    (hrun : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      Cfg.ofWords exit (stateWord C.k out)) :
    (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).output = [] := by
  have h := MultiTapeTM.output_prefix C.tm (Cfg.ofWords (input := x) entry (stateWord C.k arg)) hv
  rw [hrun, Cfg.ofWords_output] at h
  exact List.prefix_nil.mp h

/-- **The clocked, released install call** (the first-arrival cut). Clock the release adapter of
a call `C` at its entry, with the stop state `Sum.inr exit`, by the step clock with the identity
digit embedding. From the call's contract (a positive exit time `t`, the positive cut, the
endpoint) and an all-ones counter of width `m` on the clock's tape:
* if `t ≤ 2 ^ m - 1`, the host reaches `finish` at the call's endpoint, right-tagged, with the
  counter tape patched by a word of width `m`, and no exit earlier;
* if `t > 2 ^ m - 1`, the host reaches some `timeout r`, silent, and no exit earlier.
No `entry ≠ exit` is used.

**Proof sketch.** Instantiate `Turing.exists_stepClockTMVia` at the identity digit embedding,
the release adapter and the stop state `Sum.inr exit`; the all-ones counter is worth `2^m - 1`
(`qy_ones_val`). The released call first stops at `t` (`qy_release_first_stop`). If
`t ≤ 2^m - 1` the clock's finish clause gives the endpoint. Otherwise the call has not stopped
by `2^m - 1`, and the timeout clause gives a timeout at the call's configuration at that time,
whose output is a prefix of the exit's, which is empty (`qy_call_output_nil`). -/
private theorem qy_clocked_call (C : FinTM Bool) (entry exit : C.State) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (H : MultiTapeTM (C.k + 1) Bool Q)
      (inj : Unit ⊕ C.State → Q) (finish timeout : Option (Unit ⊕ C.State) → Q),
      Function.Injective finish ∧ Function.Injective timeout ∧ (∀ a b, finish a ≠ timeout b) ∧
      ∀ (x arg out : List Bool) (t : ℕ), 0 < t →
        (∀ t', 0 < t' → t' < t →
          (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t').state ≠
            some exit) →
        C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
          Cfg.ofWords exit (stateWord C.k out) →
        ∀ (m : ℕ) (ct : ℤ → Option Bool) (cp : ℤ),
          (∀ p : ℤ, -1 ≤ p → p ≤ (m : ℤ) →
            ct (cp + p) = FinTM.bufferTape (List.replicate m true) p) →
        ∀ c₀ : Cfg C.k Bool (Unit ⊕ C.State) x,
          c₀ = (Cfg.ofWords (input := x) entry (stateWord C.k arg)).mapState (fun _ => Sum.inl ()) →
          (t ≤ 2 ^ m - 1 →
            ∃ T ≤ 5 * t + 2 * m + 2, ∃ w' : List Bool, w'.length = m ∧
              H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) T =
                clockCfg (some (finish (some (Sum.inr exit))))
                  ((Cfg.ofWords (input := x) exit (stateWord C.k out)).mapState
                    (Sum.inr : C.State → Unit ⊕ C.State))
                  (wordPatch ct cp w') cp ∧
              ∀ u < T, ∀ r,
                (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) u).state ≠
                    some (finish r) ∧
                  (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) u).state ≠
                    some (timeout r)) ∧
          (2 ^ m - 1 < t →
            ∃ T ≤ 5 * (2 ^ m - 1) + 2 * m + 2, ∃ r : Option (Unit ⊕ C.State),
              (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) T).state =
                  some (timeout r) ∧
                (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) T).output = [] ∧
              ∀ u < T, ∀ r,
                (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) u).state ≠
                    some (finish r) ∧
                  (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) u).state ≠
                    some (timeout r)) := by
  obtain ⟨Q, hQ, hdQ, H, inj, finish, timeout, hfi, hti, hft, -, hH⟩ :=
    exists_stepClockTMVia (Function.Embedding.refl Bool) (seamReleaseTM C.tm entry)
      (fun s => decide (s = Sum.inr exit))
  refine ⟨Q, hQ, hdQ, H, inj, finish, timeout, hfi, hti, hft, ?_⟩
  intro x arg out t hpos hcut hrun m ct cp hct c₀ hc₀
  obtain ⟨hstop, hfirst, hend⟩ := qy_release_first_stop C entry exit x arg out t hpos hcut hrun
  have hc0state : c₀.state = some (Sum.inl ()) := by
    rw [hc₀, Cfg.mapState_state, Cfg.ofWords_state]
    rfl
  have hid : (List.replicate m true).map (Function.Embedding.refl Bool) =
      List.replicate m true := by
    rw [Function.Embedding.coe_refl, List.map_id]
  have hct' : ∀ p : ℤ, -1 ≤ p → p ≤ ((List.replicate m true).length : ℤ) →
      ct (cp + p) =
        FinTM.bufferTape ((List.replicate m true).map (Function.Embedding.refl Bool)) p := by
    intro p h1 h2
    rw [hid]
    rw [List.length_replicate] at h2
    exact hct p h1 h2
  obtain ⟨hfin, hto⟩ := hH c₀ (Sum.inl ()) hc0state (List.replicate m true) ct cp hct'
  rw [qy_ones_val m] at hfin hto
  rw [List.length_replicate] at hfin hto
  subst hc₀
  refine ⟨fun hle => ?_, fun hlt => ?_⟩
  · obtain ⟨T, hT, w', hw', hrunH, hcutH, -⟩ := hfin t hle hstop hfirst
    refine ⟨T, hT, w'.map (Function.Embedding.refl Bool), by rw [List.length_map, hw'], ?_, hcutH⟩
    rw [hrunH, hend, Cfg.mapState_state, Cfg.ofWords_state]
    rfl
  · have hns : ∀ u ≤ 2 ^ m - 1, ¬((seamReleaseTM C.tm entry).runFrom
        ((Cfg.ofWords (input := x) entry (stateWord C.k arg)).mapState fun _ => Sum.inl ())
        u).Stopped (fun s => decide (s = Sum.inr exit)) := fun u hu => hfirst u (by omega)
    obtain ⟨T, hT, w', -, hrunH, hcutH, -⟩ := hto hns
    refine ⟨T, hT, ((seamReleaseTM C.tm entry).runFrom
      ((Cfg.ofWords (input := x) entry (stateWord C.k arg)).mapState fun _ => Sum.inl ())
      (2 ^ m - 1)).state, by rw [hrunH, clockCfg_state], ?_, hcutH⟩
    rw [hrunH, clockCfg_output]
    rcases Nat.eq_zero_or_pos (2 ^ m - 1) with h0 | h0
    · rw [h0, MultiTapeTM.runFrom_zero, Cfg.mapState_output, Cfg.ofWords_output]
    · rw [seamReleaseTM_runFrom_pos C.tm entry _ (Cfg.ofWords_state entry _) _ h0,
        Cfg.mapState_output]
      exact qy_call_output_nil C entry exit x arg out t _ hlt.le hrun


/-- A word patched over an all-ones word of the same width is that word. -/
private theorem qy_wordPatch_ones (m : ℕ) (w : List Bool) (hw : w.length = m) :
    wordPatch (FinTM.bufferTape (List.replicate m true)) 0 w = FinTM.bufferTape w := by
  funext q
  by_cases h : (0 : ℤ) ≤ q ∧ q < 0 + (w.length : ℤ)
  · rw [wordPatch_of_mem _ _ _ h.1 h.2, sub_zero]
  · rw [wordPatch_of_not_mem _ _ _ h, FinTM.bufferTape_eq_none_of_not_mem _ (by
      rw [List.length_replicate]; omega), FinTM.bufferTape_eq_none_of_not_mem _ (by omega)]

/-- **The clocked call's clause**, for a call `C` with entry and exit and a step clock `H` over
its release adapter (the conclusion of `Turing.NTimeDiag.qy_clocked_call` after its witnesses). -/
private def QyClockSpec (C : FinTM Bool) (entry exit : C.State) {Q : Type}
    (H : MultiTapeTM (C.k + 1) Bool Q) (inj : Unit ⊕ C.State → Q)
    (finish timeout : Option (Unit ⊕ C.State) → Q) : Prop :=
  ∀ (x arg out : List Bool) (t : ℕ), 0 < t →
    (∀ t', 0 < t' → t' < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t').state ≠
        some exit) →
    C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      Cfg.ofWords exit (stateWord C.k out) →
    ∀ (m : ℕ) (ct : ℤ → Option Bool) (cp : ℤ),
      (∀ p : ℤ, -1 ≤ p → p ≤ (m : ℤ) →
        ct (cp + p) = FinTM.bufferTape (List.replicate m true) p) →
    ∀ c₀ : Cfg C.k Bool (Unit ⊕ C.State) x,
      c₀ = (Cfg.ofWords (input := x) entry (stateWord C.k arg)).mapState (fun _ => Sum.inl ()) →
      (t ≤ 2 ^ m - 1 →
        ∃ T ≤ 5 * t + 2 * m + 2, ∃ w' : List Bool, w'.length = m ∧
          H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) T =
            clockCfg (some (finish (some (Sum.inr exit))))
              ((Cfg.ofWords (input := x) exit (stateWord C.k out)).mapState
                (Sum.inr : C.State → Unit ⊕ C.State))
              (wordPatch ct cp w') cp ∧
          ∀ u < T, ∀ r,
            (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) u).state ≠
                some (finish r) ∧
              (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) u).state ≠
                some (timeout r)) ∧
      (2 ^ m - 1 < t →
        ∃ T ≤ 5 * (2 ^ m - 1) + 2 * m + 2, ∃ r : Option (Unit ⊕ C.State),
          (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) T).state =
              some (timeout r) ∧
            (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) T).output = [] ∧
          ∀ u < T, ∀ r,
            (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) u).state ≠
                some (finish r) ∧
              (H.runFrom (clockCfg (some (inj (Sum.inl ()))) c₀ ct cp) u).state ≠
                some (timeout r))

/-- The clocked call's start, in normal form: the call's seam on the bank, the all-ones counter on
the clock tape, the input head at `1`.

**Proof sketch.** Compare the fields with `Turing.clockCfg`'s equations, splitting each tape
index by `Fin.lastCases`: the body tapes are the released seam's, the last tape the counter. -/
private theorem qy_clock_start {K : ℕ} {x : List Bool} (C : FinTM Bool) (entry : C.State) {Q : Type}
    (q : Q) (σ : Fin (C.k + 1) ↪ Fin K) (σc : Fin C.k ↪ Fin K) (ct : Fin K)
    (hσ : ∀ i, σ i.castSucc = σc i) (hσl : σ (Fin.last C.k) = ct) (arg : List Bool)
    (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ)
    (hT : ∀ i, T (σc i) = FinTM.bufferTape (stateWord C.k arg i)) (hP : ∀ i, P (σc i) = 0)
    (hPc : P ct = 0) :
    (qyC (x := x) q 1 (fun i => T (σ i)) (fun i => P (σ i)) [] : Cfg (C.k + 1) Bool Q x) =
      clockCfg (some q) ((Cfg.ofWords (input := x) entry (stateWord C.k arg)).mapState
        (fun _ => (Sum.inl () : Unit ⊕ C.State))) (T ct) 0 := by
  apply Cfg.ext
  · rw [clockCfg_state]
    rfl
  · rw [clockCfg_inputPos, Cfg.mapState_inputPos, Cfg.ofWords_inputPos]
    rfl
  · funext j a
    rw [clockCfg_workTapes]
    induction j using Fin.lastCases with
    | last => rw [Fin.lastCases_last, ← hσl]; rfl
    | cast i =>
      rw [Fin.lastCases_castSucc, Cfg.mapState_workTapes, Cfg.ofWords_workTapes, ← hT, ← hσ]
      rfl
  · funext j
    rw [clockCfg_workTapePos]
    induction j using Fin.lastCases with
    | last => rw [Fin.lastCases_last, ← hPc, ← hσl]; rfl
    | cast i =>
      rw [Fin.lastCases_castSucc, Cfg.mapState_workTapePos, Cfg.ofWords_workTapePos, ← hP i,
        ← hσ]
      rfl
  · rw [clockCfg_output, Cfg.mapState_output, Cfg.ofWords_output]
    rfl

/-- **The hosted clocked call, finishing.** If the call returns within the all-ones counter's
value `2^m - 1`, the clock embedded along `σ` brings the normal-form configuration to `finish`,
with the result on the bank's tape `0`, the counter rewritten by some word `w'` of width `m`,
everything else kept, and no exit earlier.

**Proof sketch.** The selected bank is the clock's start (`qy_clock_start`). The clock's finish
clause (`QyClockSpec`) gives its endpoint, whose fields, read through `Turing.clockCfg`'s
equations, are the result's seam on the call's tapes and the patched counter, which is the
buffer of `w'` (`qy_wordPatch_ones`). Transport along `σ` (`qy_embed`); the unselected tapes are
kept. The cut is the clock's, read through `qy_embed_state`. -/
private theorem qy_clockHost_finish {K : ℕ} {x : List Bool} (C : FinTM Bool) (hk : 0 < C.k)
    (entry exit : C.State) {Q : Type} (H : MultiTapeTM (C.k + 1) Bool Q)
    (inj : Unit ⊕ C.State → Q) (finish timeout : Option (Unit ⊕ C.State) → Q)
    (hH : QyClockSpec C entry exit H inj finish timeout)
    (σ : Fin (C.k + 1) ↪ Fin K) (σc : Fin C.k ↪ Fin K) (ct : Fin K)
    (hσ : ∀ i, σ i.castSucc = σc i) (hσl : σ (Fin.last C.k) = ct)
    (arg out : List Bool) (t : ℕ) (hpos : 0 < t)
    (hcut : ∀ t', 0 < t' → t' < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t').state ≠ some exit)
    (hrun : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      Cfg.ofWords exit (stateWord C.k out))
    (m : ℕ) (ht : t ≤ 2 ^ m - 1) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool)
    (hT : ∀ i, T (σc i) = FinTM.bufferTape (stateWord C.k arg i)) (hP : ∀ i, P (σc i) = 0)
    (hTc : T ct = FinTM.bufferTape (List.replicate m true)) (hPc : P ct = 0) :
    ∃ T₁ ≤ 5 * t + 2 * m + 2, ∃ w' : List Bool, w'.length = m ∧
      (embedEmitTM σ H).runFrom (qyC (x := x) (inj (Sum.inl ())) 1 T P o) T₁ =
        qyC (finish (some (Sum.inr exit))) 1 (Function.update (Function.update T
          (σc ⟨0, hk⟩) (FinTM.bufferTape out)) ct (FinTM.bufferTape w')) P o ∧
      ∀ u < T₁, ∀ r,
        ((embedEmitTM σ H).runFrom (qyC (x := x) (inj (Sum.inl ())) 1 T P o) u).state ≠
            some (finish r) ∧
          ((embedEmitTM σ H).runFrom (qyC (x := x) (inj (Sum.inl ())) 1 T P o) u).state ≠
            some (timeout r) := by
  have hstart := qy_clock_start (x := x) C entry (inj (Sum.inl ())) σ σc ct hσ hσl arg T P hT hP
    hPc
  have hct : ∀ p : ℤ, -1 ≤ p → p ≤ (m : ℤ) →
      T ct (0 + p) = FinTM.bufferTape (List.replicate m true) p := by
    intro p _ _
    rw [zero_add, hTc]
  obtain ⟨hfin, -⟩ := hH x arg out t hpos hcut hrun m (T ct) 0 hct _ rfl
  obtain ⟨T₁, hT₁, w', hw', hrunH, hcutH⟩ := hfin ht
  have hne : ∀ i, σc i ≠ ct := by
    intro i h
    rw [← hσ, ← hσl] at h
    exact absurd (σ.injective h) (Fin.castSucc_ne_last i)
  set T' := Function.update (Function.update T (σc ⟨0, hk⟩) (FinTM.bufferTape out)) ct
    (FinTM.bufferTape w') with hT'
  have hsrc : H.runFrom (qyC (x := x) (inj (Sum.inl ())) 1 (fun i => T (σ i)) (fun i => P (σ i))
      []) T₁ = qyC (finish (some (Sum.inr exit))) 1 (fun i => T' (σ i)) (fun i => P (σ i)) [] := by
    rw [hstart, hrunH]
    apply Cfg.ext
    · rw [clockCfg_state]
      rfl
    · rw [clockCfg_inputPos, Cfg.mapState_inputPos, Cfg.ofWords_inputPos]
      rfl
    · funext j a
      rw [clockCfg_workTapes]
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.lastCases_last, hTc, qy_wordPatch_ones m w' hw']
        show _ = T' (σ (Fin.last C.k)) a
        rw [hσl, hT', Function.update_self]
      | cast i =>
        rw [Fin.lastCases_castSucc, Cfg.mapState_workTapes, Cfg.ofWords_workTapes]
        show _ = T' (σ i.castSucc) a
        rw [hσ, hT', Function.update_of_ne (hne i)]
        by_cases hi : i = ⟨0, hk⟩
        · subst hi
          rw [Function.update_self, stateWord_eq, if_pos rfl]
        · have hne0 : σc i ≠ σc ⟨0, hk⟩ := fun h => hi (σc.injective h)
          have hi0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
          rw [Function.update_of_ne hne0, hT, stateWord_eq, stateWord_eq, if_neg hi0,
            if_neg hi0]
    · funext j
      rw [clockCfg_workTapePos]
      induction j using Fin.lastCases with
      | last => rw [Fin.lastCases_last]; show (0 : ℤ) = P (σ (Fin.last C.k)); rw [hσl, hPc]
      | cast i =>
        rw [Fin.lastCases_castSucc, Cfg.mapState_workTapePos, Cfg.ofWords_workTapePos]
        show (0 : ℤ) = P (σ i.castSucc)
        rw [hσ, hP]
    · rw [clockCfg_output, Cfg.mapState_output, Cfg.ofWords_output]
      rfl
  refine ⟨T₁, hT₁, w', hw', ?_, fun u hu r => ?_⟩
  · have h := qy_embed σ H _ _ 1 1 T T' P P o [] _ _ T₁ hsrc (fun _ => ⟨rfl, rfl⟩)
      (fun j hj => ⟨?_, rfl⟩)
    · rw [List.append_nil] at h
      exact h
    · have h1 : j ≠ ct := fun h => hj ⟨Fin.last C.k, by rw [hσl, h]⟩
      have h2 : j ≠ σc ⟨0, hk⟩ := fun h => hj ⟨(⟨0, hk⟩ : Fin C.k).castSucc, by rw [hσ, h]⟩
      rw [hT', Function.update_of_ne h1, Function.update_of_ne h2]
  · rw [qy_embed_state, hstart]
    exact hcutH u hu r

/-- **The hosted clocked call, timing out.** If the call has not returned within the all-ones
counter's value, the clock embedded along `σ` reaches some `timeout` within
`5 (2^m - 1) + 2m + 2` steps, silent, with every tape outside the clock's bank kept (the input
head is wherever the call left it), and no exit earlier.

**Proof sketch.** The selected bank is the clock's start (`qy_clock_start`), and the clock's
timeout clause gives its state and its empty output. The host run is the transport of the
clock's run (`qy_embed_gen`), whose state and output are the source's (the transport's field
equations) and whose unselected tapes and heads are kept (`Turing.embedEmitCfg_unselected`). -/
private theorem qy_clockHost_timeout {K : ℕ} {x : List Bool} (C : FinTM Bool)
    (entry exit : C.State) {Q : Type} (H : MultiTapeTM (C.k + 1) Bool Q)
    (inj : Unit ⊕ C.State → Q) (finish timeout : Option (Unit ⊕ C.State) → Q)
    (hH : QyClockSpec C entry exit H inj finish timeout)
    (σ : Fin (C.k + 1) ↪ Fin K) (σc : Fin C.k ↪ Fin K) (ct : Fin K)
    (hσ : ∀ i, σ i.castSucc = σc i) (hσl : σ (Fin.last C.k) = ct)
    (arg out : List Bool) (t : ℕ) (hpos : 0 < t)
    (hcut : ∀ t', 0 < t' → t' < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t').state ≠ some exit)
    (hrun : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      Cfg.ofWords exit (stateWord C.k out))
    (m : ℕ) (ht : 2 ^ m - 1 < t) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool)
    (hT : ∀ i, T (σc i) = FinTM.bufferTape (stateWord C.k arg i)) (hP : ∀ i, P (σc i) = 0)
    (hTc : T ct = FinTM.bufferTape (List.replicate m true)) (hPc : P ct = 0) :
    ∃ T₁ ≤ 5 * (2 ^ m - 1) + 2 * m + 2, ∃ (r : Option (Unit ⊕ C.State))
      (ip' : Fin (x.length + 2)) (T' : Fin K → ℤ → Option Bool) (P' : Fin K → ℤ),
      (embedEmitTM σ H).runFrom (qyC (x := x) (inj (Sum.inl ())) 1 T P o) T₁ =
        qyC (timeout r) ip' T' P' o ∧
      (∀ j, j ∉ Set.range σ → T' j = T j ∧ P' j = P j) ∧
      ∀ u < T₁, ∀ r,
        ((embedEmitTM σ H).runFrom (qyC (x := x) (inj (Sum.inl ())) 1 T P o) u).state ≠
            some (finish r) ∧
          ((embedEmitTM σ H).runFrom (qyC (x := x) (inj (Sum.inl ())) 1 T P o) u).state ≠
            some (timeout r) := by
  have hstart := qy_clock_start (x := x) C entry (inj (Sum.inl ())) σ σc ct hσ hσl arg T P hT hP
    hPc
  have hct : ∀ p : ℤ, -1 ≤ p → p ≤ (m : ℤ) →
      T ct (0 + p) = FinTM.bufferTape (List.replicate m true) p := by
    intro p _ _
    rw [zero_add, hTc]
  obtain ⟨-, hto⟩ := hH x arg out t hpos hcut hrun m (T ct) 0 hct _ rfl
  obtain ⟨T₁, hT₁, r, hst, hout, hcutH⟩ := hto ht
  have hE' : (embedEmitTM σ H).runFrom (qyC (x := x) (inj (Sum.inl ())) 1 T P o) T₁ =
      embedEmitCfg σ T P o (H.runFrom (clockCfg (some (inj (Sum.inl ())))
      ((Cfg.ofWords (input := x) entry (stateWord C.k arg)).mapState
        (fun _ => (Sum.inl () : Unit ⊕ C.State))) (T ct) 0) T₁) := by
    rw [qy_embed_gen, hstart]
  refine ⟨T₁, hT₁, r,
    ((embedEmitTM σ H).runFrom (qyC (x := x) (inj (Sum.inl ())) 1 T P o) T₁).inputPos,
    ((embedEmitTM σ H).runFrom (qyC (x := x) (inj (Sum.inl ())) 1 T P o) T₁).workTapes,
    ((embedEmitTM σ H).runFrom (qyC (x := x) (inj (Sum.inl ())) 1 T P o) T₁).workTapePos,
    ?_, fun j hj => ?_, fun u hu r => ?_⟩
  · apply Cfg.ext
    · rw [hE', embedEmitCfg_state, hst]
      rfl
    · rfl
    · rfl
    · rfl
    · rw [hE', embedEmitCfg_output, hout, List.append_nil]
      rfl
  · rw [hE']
    exact embedEmitCfg_unselected σ T P o _ j hj
  · rw [qy_embed_state, hstart]
    exact hcutH u hu r


/-- The expansion's start, in normal form: the destination word under the body head and the
counter word under the counter head.

**Proof sketch.** `Turing.counter_cfg_eq` writes the counter layout explicitly; compare the
fields, splitting each of the two tape indices by `Fin.lastCases`. -/
private theorem qy_expand_start {K : ℕ} {x : List Bool} (σ : Fin 2 ↪ Fin K) (dst ctr : Fin K)
    (hσ0 : σ 0 = dst) (hσ1 : σ 1 = ctr) (ip : Fin (x.length + 2))
    (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) :
    (qyC (x := x) (CounterLoopState.dec FlagPhase.run) ip (fun i => T (σ i)) (fun i => P (σ i))
        [] : Cfg (1 + 1) Bool (CounterLoopState (Fin ([true].length + 1))) x) =
      counterLoopCfg (some (.dec .run))
        (qyC (x := x) (0 : Fin ([true].length + 1)) ip (fun _ => T dst) (fun _ => P dst) [])
        (T ctr) (P ctr) := by
  rw [counter_cfg_eq]
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    dsimp only [qyC]
    induction j using Fin.lastCases with
    | last => rw [Fin.lastCases_last, ← hσ1]; rfl
    | cast i =>
      rw [Fin.lastCases_castSucc, ← hσ0]
      obtain rfl : i = 0 := Subsingleton.elim _ _
      rfl
  · funext j
    dsimp only [qyC]
    induction j using Fin.lastCases with
    | last => rw [Fin.lastCases_last, ← hσ1]; rfl
    | cast i =>
      rw [Fin.lastCases_castSucc, ← hσ0]
      obtain rfl : i = 0 := Subsingleton.elim _ _
      rfl
  · rfl

/-- **The hosted expansion.** `Turing.expandTM` with the pattern `[true]`, embedded along `σ`
(body tape `dst`, counter tape `ctr`), with the word `u` on `dst` and its head at the end, and the
counter word `w` of value `d` on `ctr` at its start: it appends `1ᵈ` to `u`, its head moving to
the new end, turns the counter all `true`, keeps everything else, and reaches `done` at exactly
`2d + counterOverhead w (d + 1)`, not earlier.

**Proof sketch.** The selected bank is the expansion's start (`qy_expand_start`), and
`Turing.expandTM_run_ofCfg` gives its endpoint. Read through `Turing.counter_cfg_eq`, the body
tape holds `u` followed by `d` copies of `[true]`, which is the buffer of `u ++ 1^d`
(`qy_patch_end`, `List.flatten_replicate_singleton`), its head at the end, and the counter is all
`true` over its width. Transport along `σ` (`qy_embed`); the cut is the row's. -/
private theorem qy_expandHost {K : ℕ} {x : List Bool} (σ : Fin 2 ↪ Fin K) (dst ctr : Fin K)
    (hσ0 : σ 0 = dst) (hσ1 : σ 1 = ctr) (ip : Fin (x.length + 2))
    (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool) (u w : List Bool) (d : ℕ)
    (hd : Nat.ofDigits 2 (w.map Bool.toNat) = d)
    (hTd : T dst = FinTM.bufferTape u) (hPd : P dst = u.length)
    (hTc : T ctr = FinTM.bufferTape w) (hPc : P ctr = 0) :
    (embedEmitTM σ (expandTM 1 0 [true])).runFrom (qyC (.dec .run) ip T P o)
        (d * 2 + counterOverhead w (d + 1)) =
      qyC CounterLoopState.done ip (Function.update (Function.update T dst
        (FinTM.bufferTape (u ++ List.replicate d true))) ctr
          (FinTM.bufferTape (List.replicate w.length true)))
        (Function.update P dst ((u.length : ℤ) + d)) o ∧
    ∀ t < d * 2 + counterOverhead w (d + 1),
      ((embedEmitTM σ (expandTM 1 0 [true])).runFrom (qyC (.dec .run) ip T P o) t).state ≠
        some .done := by
  have hne : dst ≠ ctr := by
    rw [← hσ0, ← hσ1]
    exact fun h => absurd (σ.injective h) (by decide)
  have hstart := qy_expand_start (x := x) σ dst ctr hσ0 hσ1 ip T P
  have hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → T ctr (P ctr + p) = FinTM.bufferTape w p := by
    intro p _ _
    rw [hPc, zero_add, hTc]
  obtain ⟨hrun, hcut, -, -⟩ := expandTM_run_ofCfg (x := x) (0 : Fin 1) [true]
    (qyC (0 : Fin ([true].length + 1)) ip (fun _ => T dst) (fun _ => P dst) []) rfl w (T ctr)
    (P ctr) hw d hd
  set T' := Function.update (Function.update T dst
    (FinTM.bufferTape (u ++ List.replicate d true))) ctr
      (FinTM.bufferTape (List.replicate w.length true)) with hT'
  set P' := Function.update P dst ((u.length : ℤ) + d) with hP'
  have hsrc : (expandTM 1 0 [true]).runFrom (qyC (x := x) (CounterLoopState.dec FlagPhase.run) ip
      (fun i => T (σ i)) (fun i => P (σ i)) []) (d * 2 + counterOverhead w (d + 1)) =
      qyC CounterLoopState.done ip (fun i => T' (σ i)) (fun i => P' (σ i)) [] := by
    rw [hstart, show d * 2 = d * ([true].length + 1) from rfl, hrun, counter_cfg_eq]
    apply Cfg.ext
    · rfl
    · rfl
    · funext j a
      dsimp only [qyC]
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.lastCases_last]
        show _ = T' (σ 1) a
        rw [hσ1, hT', Function.update_self, hPc, hTc]
        by_cases h : (0 : ℤ) ≤ a ∧ a < 0 + (w.length : ℤ)
        · rw [if_pos h, FinTM.bufferTape_eq, if_pos h.1,
            List.getElem?_replicate_of_lt (by omega)]
        · rw [if_neg h, FinTM.bufferTape_eq_none_of_not_mem _ (by omega),
            FinTM.bufferTape_eq_none_of_not_mem _ (by rw [List.length_replicate]; omega)]
      | cast i =>
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [Fin.lastCases_castSucc]
        show _ = T' (σ 0) a
        rw [hσ0, hT', Function.update_of_ne hne, Function.update_self]
        have h := congrFun (qy_patch_end u (List.replicate d true) (P dst) hPd) a
        rw [List.length_replicate] at h
        rw [← h, List.flatten_replicate_singleton, List.length_singleton, mul_one, hTd]
        simp only [true_and]
    · funext j
      dsimp only [qyC]
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.lastCases_last]
        show _ = P' (σ 1)
        rw [hσ1, hP', Function.update_of_ne hne.symm]
      | cast i =>
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [Fin.lastCases_castSucc]
        show _ = P' (σ 0)
        rw [hσ0, hP', Function.update_self, Function.update_self, hPd, List.length_singleton,
          mul_one]
    · rfl
  refine ⟨?_, fun t ht => ?_⟩
  · have h := qy_embed σ (expandTM 1 0 [true]) _ _ ip ip T T' P P' o [] _ _ _ hsrc
      (fun _ => ⟨rfl, rfl⟩) (fun j hj => ⟨?_, ?_⟩)
    · rw [List.append_nil] at h
      exact h
    · have h1 : j ≠ ctr := fun h => hj ⟨1, by rw [hσ1, h]⟩
      have h2 : j ≠ dst := fun h => hj ⟨0, by rw [hσ0, h]⟩
      rw [hT', Function.update_of_ne h1, Function.update_of_ne h2]
    · have h2 : j ≠ dst := fun h => hj ⟨0, by rw [hσ0, h]⟩
      rw [hP', Function.update_of_ne h2]
  · rw [qy_embed_state, hstart]
    exact (hcut t ht).1

/-- **The hosted input seek.** The input seek of `Turing.exists_inputSeekTM`, embedded along `σ`
on tapes holding `[true]` and a blank, brings the input head home to `1` from anywhere within
`C (|[true]| + pos + 1 + 1)` steps, keeping everything else, and not earlier.

**Proof sketch.** Apply the seek's clause at `p = 1` with the word `[true]`, worth `1`, to the
selected bank: its endpoint is the bank with the input head at `1`, its tapes, heads and output
restored. Transport along `σ` (`qy_embed`); the cut is the seek's. -/
private theorem qy_seekHost {K : ℕ} {x : List Bool} {S : Type} (R : MultiTapeTM 2 Bool S)
    (entry exit : S) (C : ℕ)
    (hR : ∀ (p : ℕ) (w : List Bool), Nat.ofDigits 2 (w.map Bool.toNat) = p →
        p ≤ x.length + 1 → ∀ d : Cfg 2 Bool S x, d.state = some entry →
        (∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) →
          d.workTapes 0 (d.workTapePos 0 + q) = FinTM.bufferTape w q) →
        (∀ q, d.workTapes 1 q = none) →
        ∃ t ≤ C * (w.length + d.inputPos.val + p + 1),
          (∀ u < t, (R.runFrom d u).state ≠ some exit) ∧
          (∀ u ≤ t, ∀ j : Fin 2,
            |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ ((C * (w.length + 1) : ℕ) : ℤ)) ∧
          (R.runFrom d t).state = some exit ∧ ((R.runFrom d t).inputPos : ℕ) = p ∧
          (R.runFrom d t).workTapes = d.workTapes ∧ (R.runFrom d t).workTapePos = d.workTapePos ∧
          (R.runFrom d t).output = d.output)
    (σ : Fin 2 ↪ Fin K) (s0 s1 : Fin K) (hσ0 : σ 0 = s0) (hσ1 : σ 1 = s1)
    (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool)
    (hT0 : T s0 = FinTM.bufferTape [true]) (hP0 : P s0 = 0)
    (hT1 : T s1 = FinTM.bufferTape []) :
    ∃ t ≤ C * (1 + ip.val + 1 + 1),
      (embedEmitTM σ R).runFrom (qyC entry ip T P o) t = qyC exit 1 T P o ∧
      ∀ u < t, ((embedEmitTM σ R).runFrom (qyC entry ip T P o) u).state ≠ some exit := by
  have hv : Nat.ofDigits 2 (([true] : List Bool).map Bool.toNat) = 1 := by
    rw [List.map_cons, List.map_nil, Bool.toNat_true, Nat.ofDigits_singleton]
  obtain ⟨t, ht, hcut, -, hst, hpos, hwt, hwp, hout⟩ := hR 1 [true] hv (by omega)
    (qyC entry ip (fun i => T (σ i)) (fun i => P (σ i)) []) rfl
    (fun q _ _ => by
      show T (σ 0) (P (σ 0) + q) = _
      rw [hσ0, hP0, zero_add, hT0])
    (fun q => by
      show T (σ 1) q = none
      rw [hσ1, hT1, FinTM.bufferTape_nil])
  have hsrc : R.runFrom (qyC entry ip (fun i => T (σ i)) (fun i => P (σ i)) []) t =
      qyC exit 1 (fun i => T (σ i)) (fun i => P (σ i)) [] := by
    apply Cfg.ext
    · exact hst
    · exact Fin.ext hpos
    · exact hwt
    · exact hwp
    · exact hout
  refine ⟨t, ht, ?_, fun u hu => ?_⟩
  · have h := qy_embed σ R entry exit ip 1 T T P P o [] _ _ t hsrc (fun _ => ⟨rfl, rfl⟩)
      (fun _ _ => ⟨rfl, rfl⟩)
    rw [List.append_nil] at h
    exact h
  · rw [qy_embed_state]
    exact hcut u hu

/-- **The emitter halts at its exit.** One step from `done` halts with the output unchanged. -/
private theorem qy_emit_halt {K : ℕ} {x : List Bool} (i : Fin K) (pre suf : List Bool) (rr : ℕ)
    (dl : Bool) (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ)
    (o : List Bool) :
    ((qyEmitTM K i pre suf rr dl).runFrom (qyC .done ip T P o) 1).state = none ∧
      ((qyEmitTM K i pre suf rr dl).runFrom (qyC .done ip T P o) 1).output = o := by
  rw [qy_run_one, MultiTapeTM.step_of_some (rfl : (qyC (x := x) (K := K)
    (QyEm.done : QyEm pre.length suf.length rr) ip T P o).state = some .done)]
  constructor
  · rw [Action.apply_state]
    rfl
  · rw [Action.apply_output]
    show o ++ (none : Option Bool).toList = o
    rw [Option.toList_none, List.append_nil]

/-- **An install call's clause**: from the seam of every argument `arg`, over every native input,
`C` reaches its exit first at a positive time within `B arg`, with `F arg` installed. -/
private def QySpec (C : FinTM Bool) (entry exit : C.State) (F : List Bool → List Bool)
    (B : List Bool → ℕ) : Prop :=
  ∀ x arg : List Bool, ∃ t ≤ B arg, 0 < t ∧
    (∀ t', 0 < t' → t' < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t').state ≠ some exit) ∧
    C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      Cfg.ofWords exit (stateWord C.k (F arg))

/-- **An input call's clause**: from the blank seam over every native input `x`, `C` reaches its
exit first at a positive time within `B |x|`, with `F x` installed. -/
private def QyInSpec (C : FinTM Bool) (entry exit : C.State) (F : List Bool → List Bool)
    (B : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, ∃ t ≤ B x.length, 0 < t ∧
    (∀ t', 0 < t' → t' < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k [])) t').state ≠ some exit) ∧
    C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k [])) t =
      Cfg.ofWords exit (stateWord C.k (F x))

/-- An install call's clause is monotone in its bound. -/
private theorem QySpec.mono {C : FinTM Bool} {entry exit : C.State} {F : List Bool → List Bool}
    {B B' : List Bool → ℕ} (h : QySpec C entry exit F B) (hB : ∀ arg, B arg ≤ B' arg) :
    QySpec C entry exit F B' := by
  intro x arg
  obtain ⟨t, ht, h1, h2, h3⟩ := h x arg
  exact ⟨t, ht.trans (hB arg), h1, h2, h3⟩

/-- An install call of a function-level machine has the clause of its contract. -/
private theorem qy_installSpec (M : FinTM Bool) (F : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime F T) :
    ∃ (C : FinTM Bool) (entry exit : C.State) (c : ℕ), 0 < C.k ∧
      QySpec C entry exit F (fun arg => c * (T arg.length + arg.length + (F arg).length + 1)) := by
  obtain ⟨C, entry, exit, c, hk, h⟩ := FinTM.exists_installCallTM M F T hM
  exact ⟨C, entry, exit, c, hk, fun x arg => h x arg⟩

/-- An input call of a function-level machine has the clause of its contract. -/
private theorem qy_inputSpec (M : FinTM Bool) (F : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime F T) :
    ∃ (C : FinTM Bool) (entry exit : C.State) (c : ℕ), 0 < C.k ∧
      ∀ x : List Bool, ∃ t ≤ c * (T x.length + x.length + (F x).length + 1), 0 < t ∧
        (∀ t', 0 < t' → t' < t →
          (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k [])) t').state ≠
            some exit) ∧
        C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k [])) t =
          Cfg.ofWords exit (stateWord C.k (F x)) := by
  obtain ⟨C, entry, exit, c, hk, h⟩ := FinTM.exists_inputCallTM M F T hM
  have hw : (fun _ => ([] : List Bool)) = stateWord C.k [] := by
    funext i
    rw [stateWord_eq]
    split <;> rfl
  refine ⟨C, entry, exit, c, hk, fun x => ?_⟩
  obtain ⟨t, ht, h1, h2, h3⟩ := h x
  rw [hw] at h2 h3
  exact ⟨t, ht, h1, h2, h3⟩

/-- **The main machine's kit**: every called machine with its clause, the step clock over `f`'s
call, and the input seek. The clauses' bounds are simplified to the forms the ledger uses. -/
private structure QyKit (f g : ℕ → ℕ) : Type 1 where
  /-- the input call computing `bits |x|` -/
  cb : FinTM Bool
  cbE : cb.State
  cbX : cb.State
  cbK : 0 < cb.k
  cbA : ℕ
  cbS : QyInSpec cb cbE cbX (fun x => Nat.bits x.length) (fun n => cbA * (n + 1))
  /-- the install call of `f`'s witness -/
  cf : FinTM Bool
  cfE : cf.State
  cfX : cf.State
  cfK : 0 < cf.k
  cfA : ℕ
  cfc : ℕ
  cfS : QySpec cf cfE cfX (fun y => Nat.bits (f y.length))
    (fun y => cfA * (cfc * (f y.length + 1) + y.length + (Nat.bits (f y.length)).length + 1))
  /-- the step clock over the released call of `f`'s witness -/
  Q : Type
  [Qf : Fintype Q]
  [Qd : DecidableEq Q]
  H : MultiTapeTM (cf.k + 1) Bool Q
  inj : Unit ⊕ cf.State → Q
  fsh : Option (Unit ⊕ cf.State) → Q
  tmo : Option (Unit ⊕ cf.State) → Q
  hft : ∀ a b, fsh a ≠ tmo b
  hH : QyClockSpec cf cfE cfX H inj fsh tmo
  /-- the install call of `x ↦ 1^{(|x| + 1)⁴}` -/
  pu : FinTM Bool
  puE : pu.State
  puX : pu.State
  puK : 0 < pu.k
  puA : ℕ
  puS : QySpec pu puE puX (fun y => List.replicate ((y.length + 1) ^ 4) true)
    (fun y => puA * (y.length + 1) ^ 5)
  /-- the install call of `x ↦ x ++ [true]` -/
  ab : FinTM Bool
  abE : ab.State
  abX : ab.State
  abK : 0 < ab.k
  abA : ℕ
  abS : QySpec ab abE abX (fun y => y ++ [true]) (fun y => abA * (y.length + 1))
  /-- the install call prepending the counter's fixed tail -/
  pr : FinTM Bool
  prE : pr.State
  prX : pr.State
  prK : 0 < pr.k
  prA : ℕ
  prS : QySpec pr prE prX
    (fun y => List.replicate (Nat.bits (cfA * (cfc + 2))).length true ++ y)
    (fun y => prA * (y.length + 1))
  /-- the install call of `x ↦ bits |x|` -/
  cl : FinTM Bool
  clE : cl.State
  clX : cl.State
  clK : 0 < cl.k
  clA : ℕ
  clS : QySpec cl clE clX (fun y => Nat.bits y.length) (fun y => clA * (y.length + 1))
  /-- the install call of `x ↦ bits ((|x| + 1)²)` -/
  pb : FinTM Bool
  pbE : pb.State
  pbX : pb.State
  pbK : 0 < pb.k
  pbA : ℕ
  pbS : QySpec pb pbE pbX (fun y => Nat.bits ((y.length + 1) ^ 2))
    (fun y => pbA * (y.length + 1) ^ 3)
  /-- the input call of `g`'s witness -/
  cg : FinTM Bool
  cgE : cg.State
  cgX : cg.State
  cgK : 0 < cg.k
  cgA : ℕ
  cgS : QyInSpec cg cgE cgX (fun x => Nat.bits (g x.length)) (fun n => cgA * (g n + 1))
  /-- the input seek -/
  S : Type
  [Sf : Fintype S]
  [Sd : DecidableEq S]
  R : MultiTapeTM 2 Bool S
  rE : S
  rX : S
  rC : ℕ
  rS : ∀ {x : List Bool} (p : ℕ) (w : List Bool), Nat.ofDigits 2 (w.map Bool.toNat) = p →
    p ≤ x.length + 1 → ∀ d : Cfg 2 Bool S x, d.state = some rE →
    (∀ q : ℤ, -1 ≤ q → q ≤ (w.length : ℤ) →
      d.workTapes 0 (d.workTapePos 0 + q) = FinTM.bufferTape w q) →
    (∀ q, d.workTapes 1 q = none) →
    ∃ t ≤ rC * (w.length + d.inputPos.val + p + 1),
      (∀ u < t, (R.runFrom d u).state ≠ some rX) ∧
      (∀ u ≤ t, ∀ j : Fin 2,
        |(R.runFrom d u).workTapePos j - d.workTapePos j| ≤ ((rC * (w.length + 1) : ℕ) : ℤ)) ∧
      (R.runFrom d t).state = some rX ∧ ((R.runFrom d t).inputPos : ℕ) = p ∧
      (R.runFrom d t).workTapes = d.workTapes ∧ (R.runFrom d t).workTapePos = d.workTapePos ∧
      (R.runFrom d t).output = d.output

attribute [local instance] QyKit.Qf QyKit.Qd QyKit.Sf QyKit.Sd


/-- `(n + 1)^a ≤ (n + 1)^b` for `a ≤ b`. -/
private theorem qy_pow_mono (n a b : ℕ) (h : a ≤ b) : (n + 1) ^ a ≤ (n + 1) ^ b :=
  Nat.pow_le_pow_right (Nat.succ_pos n) h

/-- **The kit exists** for time-constructible `f` and `g`: the published calls, the step clock
over `f`'s call and the input seek, with their clauses' bounds simplified.

**Proof sketch.** Read `f`'s and `g`'s witnesses through `Complexity.timeConstructible_iff`.
The install calls (`Turing.FinTM.exists_installCallTM`) of `f`'s witness and of the published
rows `computesFunInTime_polyUnary 1 4`, `_appendBit true`, `_prepend`, `_lengthBits` and
`_polyBits 1 2`, the input calls (`Turing.FinTM.exists_inputCallTM`) of `_lengthBits` and of
`g`'s witness, the clocked call over `f`'s (`qy_clocked_call`) and the input seek
(`Turing.exists_inputSeekTM`) supply the fields. Each call's bound
`c (T |y| + |y| + |F y| + 1)` is at most the kit's simplified bound, since `|bits m| ≤ m`
(`Turing.length_bits_le_self`), the outputs' lengths are at most the time's polynomial, and
`n ≤ g n`. -/
private theorem qy_kit_exists {f g : ℕ → ℕ} (hf : Complexity.TimeConstructible f)
    (hg : Complexity.TimeConstructible g) : Nonempty (QyKit f g) := by
  obtain ⟨-, cfc, -, Mf, hMf⟩ := (Complexity.timeConstructible_iff f).mp hf
  obtain ⟨hgle, cgc, -, Mg, hMg⟩ := (Complexity.timeConstructible_iff g).mp hg
  have hMf' : Mf.ComputesFunInTime (fun y => Nat.bits (f y.length)) (fun m => cfc * (f m + 1)) :=
    (FinTM.computesFunInTime_iff _ _ _).mpr hMf
  have hMg' : Mg.ComputesFunInTime (fun y => Nat.bits (g y.length)) (fun m => cgc * (g m + 1)) :=
    (FinTM.computesFunInTime_iff _ _ _).mpr hMg
  -- f's call and its clock
  obtain ⟨cf, cfE, cfX, cfA, cfK, cfS⟩ := qy_installSpec Mf _ _ hMf'
  obtain ⟨Q, hQ, hdQ, H, inj, fsh, tmo, -, -, hft, hH⟩ := qy_clocked_call cf cfE cfX
  -- the bits of the input length
  obtain ⟨Lb, cL, hLb⟩ := FinTM.computesFunInTime_lengthBits
  obtain ⟨cb, cbE, cbX, cbc, cbK, cbS⟩ := qy_inputSpec Lb _ _ hLb
  -- the fourth power, the increment, the prefix, the length, the square
  obtain ⟨Mu, cu, hMu⟩ := FinTM.computesFunInTime_polyUnary 1 4
  have hMu' : Mu.ComputesFunInTime (fun y => List.replicate ((y.length + 1) ^ 4) true)
      (fun n => cu * (n + 1) ^ (4 + 1)) := by
    have he : (fun y : List Bool => List.replicate (1 * (y.length + 1) ^ 4) true) =
        fun y => List.replicate ((y.length + 1) ^ 4) true := by
      funext y
      rw [one_mul]
    rw [← he]
    exact hMu
  obtain ⟨pu, puE, puX, puc, puK, puS⟩ := qy_installSpec Mu _ _ hMu'
  obtain ⟨Ma, ca, hMa⟩ := FinTM.computesFunInTime_appendBit true
  obtain ⟨ab, abE, abX, abc, abK, abS⟩ := qy_installSpec Ma _ _ hMa
  obtain ⟨Mp, cp, hMp⟩ := FinTM.computesFunInTime_prepend
    (List.replicate (Nat.bits (cfA * (cfc + 2))).length true)
  obtain ⟨pr, prE, prX, prc, prK, prS⟩ := qy_installSpec Mp _ _ hMp
  obtain ⟨cl, clE, clX, clc, clK, clS⟩ := qy_installSpec Lb _ _ hLb
  obtain ⟨Mq, cq, hMq⟩ := FinTM.computesFunInTime_polyBits 1 2
  have hMq' : Mq.ComputesFunInTime (fun y => Nat.bits ((y.length + 1) ^ 2))
      (fun n => cq * (n + 1) ^ (2 + 1)) := by
    have he : (fun y : List Bool => Nat.bits (1 * (y.length + 1) ^ 2)) =
        fun y => Nat.bits ((y.length + 1) ^ 2) := by
      funext y
      rw [one_mul]
    rw [← he]
    exact hMq
  obtain ⟨pb, pbE, pbX, pbc, pbK, pbS⟩ := qy_installSpec Mq _ _ hMq'
  -- g's input call and the seek
  obtain ⟨cg, cgE, cgX, cgc', cgK, cgS⟩ := qy_inputSpec Mg _ _ hMg'
  obtain ⟨S, hS, hdS, R, rE, rX, rC, hR⟩ := exists_inputSeekTM
  have cbS' : QyInSpec cb cbE cbX (fun x => Nat.bits x.length)
      (fun n => cbc * (cL + 3) * (n + 1)) := by
    intro x
    obtain ⟨t, ht, h1, h2, h3⟩ := cbS x
    refine ⟨t, ht.trans ?_, h1, h2, h3⟩
    have hb := length_bits_le_self x.length
    dsimp only
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have puS' : QySpec pu puE puX (fun y => List.replicate ((y.length + 1) ^ 4) true)
      (fun y => puc * (cu + 3) * (y.length + 1) ^ 5) := by
    refine puS.mono fun y => ?_
    have h1 : y.length + 1 ≤ (y.length + 1) ^ 5 := by
      simpa using qy_pow_mono y.length 1 5 (by norm_num)
    have h2 : (y.length + 1) ^ 4 ≤ (y.length + 1) ^ 5 := qy_pow_mono y.length 4 5 (by norm_num)
    show puc * (cu * (y.length + 1) ^ (4 + 1) + y.length +
      (List.replicate ((y.length + 1) ^ 4) true).length + 1) ≤ puc * (cu + 3) * (y.length + 1) ^ 5
    rw [List.length_replicate, mul_assoc,
      show (y.length + 1) ^ (4 + 1) = (y.length + 1) ^ 5 from rfl]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have abS' : QySpec ab abE abX (fun y => y ++ [true])
      (fun y => abc * (ca + 3) * (y.length + 1)) := by
    refine abS.mono fun y => ?_
    dsimp only
    rw [List.length_append, List.length_singleton, mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have prS' : QySpec pr prE prX
      (fun y => List.replicate (Nat.bits (cfA * (cfc + 2))).length true ++ y)
      (fun y => prc * (cp + (Nat.bits (cfA * (cfc + 2))).length + 3) * (y.length + 1)) := by
    refine prS.mono fun y => ?_
    dsimp only
    rw [List.length_append, List.length_replicate, mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have clS' : QySpec cl clE clX (fun y => Nat.bits y.length)
      (fun y => clc * (cL + 3) * (y.length + 1)) := by
    refine clS.mono fun y => ?_
    have hb := length_bits_le_self y.length
    try dsimp only
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have pbS' : QySpec pb pbE pbX (fun y => Nat.bits ((y.length + 1) ^ 2))
      (fun y => pbc * (cq + 3) * (y.length + 1) ^ 3) := by
    refine pbS.mono fun y => ?_
    have hb := length_bits_le_self ((y.length + 1) ^ 2)
    have h1 : y.length + 1 ≤ (y.length + 1) ^ 3 := by
      simpa using qy_pow_mono y.length 1 3 (by norm_num)
    have h2 : (y.length + 1) ^ 2 ≤ (y.length + 1) ^ 3 := qy_pow_mono y.length 2 3 (by norm_num)
    show pbc * (cq * (y.length + 1) ^ (2 + 1) + y.length +
      (Nat.bits ((y.length + 1) ^ 2)).length + 1) ≤ pbc * (cq + 3) * (y.length + 1) ^ 3
    rw [mul_assoc, show (y.length + 1) ^ (2 + 1) = (y.length + 1) ^ 3 from rfl]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have cgS' : QyInSpec cg cgE cgX (fun x => Nat.bits (g x.length))
      (fun n => cgc' * (cgc + 3) * (g n + 1)) := by
    intro x
    obtain ⟨t, ht, h1, h2, h3⟩ := cgS x
    refine ⟨t, ht.trans ?_, h1, h2, h3⟩
    have hb := length_bits_le_self (g x.length)
    have hn := hgle x.length
    dsimp only
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  exact ⟨{ cb := cb, cbE := cbE, cbX := cbX, cbK := cbK, cbA := cbc * (cL + 3), cbS := cbS'
           cf := cf, cfE := cfE, cfX := cfX, cfK := cfK, cfA := cfA, cfc := cfc, cfS := cfS
           Q := Q, Qf := hQ, Qd := hdQ, H := H, inj := inj, fsh := fsh, tmo := tmo, hft := hft
           hH := hH
           pu := pu, puE := puE, puX := puX, puK := puK, puA := puc * (cu + 3), puS := puS'
           ab := ab, abE := abE, abX := abX, abK := abK, abA := abc * (ca + 3), abS := abS'
           pr := pr, prE := prE, prX := prX, prK := prK
           prA := prc * (cp + (Nat.bits (cfA * (cfc + 2))).length + 3), prS := prS'
           cl := cl, clE := clE, clX := clX, clK := clK, clA := clc * (cL + 3), clS := clS'
           pb := pb, pbE := pbE, pbX := pbX, pbK := pbK, pbA := pbc * (cq + 3), pbS := pbS'
           cg := cg, cgE := cgE, cgX := cgX, cgK := cgK, cgA := cgc' * (cgc + 3), cgS := cgS'
           S := S, Sf := hS, Sd := hdS, R := R, rE := rE, rX := rX, rC := rC, rS := hR }⟩

/-! ### The tape layout -/

/-- The tape count of the main machine: sixteen named tapes, then one block per call bank (each
call's tape `0` is a named tape; its other tapes are its block). -/
private def QyKit.K {f g : ℕ → ℕ} (κ : QyKit f g) : ℕ :=
  16 + κ.cb.k + κ.cf.k + κ.pu.k + κ.ab.k + κ.ab.k + κ.ab.k + κ.pr.k + κ.cl.k + κ.pb.k + κ.cg.k

/-- The sixteen named tapes come first. -/
private theorem QyKit.le_K {f g : ℕ → ℕ} (κ : QyKit f g) : 16 ≤ κ.K := by
  unfold QyKit.K
  omega

/-- The named tape `c`: `0` the unary `n + 1`, `1` the width word `1^{|bits n|}`, `2` the rung, `3`
the next rung, `4` the word `1^{X - 1}`, `5` its fourth power, `6` the next rung's counter, `7`
`f`'s call tape, `8` the clock's counter, `9` its saved copy, `10` and `11` the pair `unpair h`,
`12` and `13` the input seek's tapes, `14` `g`'s call tape, `15` a tape that stays blank. -/
private def QyKit.tp {f g : ℕ → ℕ} (κ : QyKit f g) (c : Fin 16) : Fin κ.K :=
  Fin.castLE κ.le_K c

/-- Named tapes are distinct when their names are. -/
private theorem QyKit.tp_inj {f g : ℕ → ℕ} (κ : QyKit f g) {a b : Fin 16} :
    κ.tp a = κ.tp b ↔ a = b :=
  (Fin.castLE_injective κ.le_K).eq_iff

/-- A call's bank: its tape `0` on the named tape `t0`, its other tapes on the block from `off`. -/
private def qyBank {K : ℕ} (t0 : Fin K) (off k : ℕ) (hK : off + k ≤ K) (h0 : (t0 : ℕ) < off) :
    Fin k ↪ Fin K where
  toFun i := if (i : ℕ) = 0 then t0 else ⟨off + i, by omega⟩
  inj' i j h := by
    dsimp only at h
    by_cases hi : (i : ℕ) = 0 <;> by_cases hj : (j : ℕ) = 0
    · exact Fin.ext (by omega)
    · rw [if_pos hi, if_neg hj] at h
      have := congrArg Fin.val h
      simp only at this
      omega
    · rw [if_neg hi, if_pos hj] at h
      have := congrArg Fin.val h
      simp only at this
      omega
    · rw [if_neg hi, if_neg hj] at h
      have := congrArg Fin.val h
      simp only at this
      exact Fin.ext (by omega)

/-- A bank's tape `0` is its named tape. -/
private theorem qyBank_zero {K : ℕ} (t0 : Fin K) (off k : ℕ) (hK : off + k ≤ K)
    (h0 : (t0 : ℕ) < off) (hk : 0 < k) : qyBank t0 off k hK h0 ⟨0, hk⟩ = t0 := rfl

/-- A bank's other tapes lie in its block. -/
private theorem qyBank_val {K : ℕ} (t0 : Fin K) (off k : ℕ) (hK : off + k ≤ K) (h0 : (t0 : ℕ) < off)
    (i : Fin k) (hi : (i : ℕ) ≠ 0) : (qyBank t0 off k hK h0 i : ℕ) = off + i := by
  simp only [qyBank, Function.Embedding.coeFn_mk, if_neg hi]

/-- Two tapes as a two-tape bank. -/
private def qyEmb2 {K : ℕ} (a b : Fin K) (h : a ≠ b) : Fin 2 ↪ Fin K where
  toFun i := if (i : ℕ) = 0 then a else b
  inj' i j hij := by
    dsimp only at hij
    have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
    have hj : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact Fin.ext (by omega)
    · rw [if_pos hi, if_neg (by omega)] at hij; exact absurd hij h
    · rw [if_neg (by omega), if_pos hj] at hij; exact absurd hij.symm h
    · exact Fin.ext (by omega)

/-- The value of a named tape. -/
private theorem QyKit.tp_val {f g : ℕ → ℕ} (κ : QyKit f g) (c : Fin 16) : (κ.tp c : ℕ) = c := rfl

/-- The banks, each at its block: the bank of `bits n`'s input call, tape `0` on tape `1`. -/
private def QyKit.bCb {f g : ℕ → ℕ} (κ : QyKit f g) : Fin κ.cb.k ↪ Fin κ.K :=
  qyBank (κ.tp 1) 16 κ.cb.k (by unfold QyKit.K; omega) (by rw [κ.tp_val]; decide)
/-- The bank of `f`'s call bank, tape `0` on tape `7`. -/
private def QyKit.bCf {f g : ℕ → ℕ} (κ : QyKit f g) : Fin κ.cf.k ↪ Fin κ.K :=
  qyBank (κ.tp 7) (16 + κ.cb.k) κ.cf.k (by unfold QyKit.K; omega)
    (by rw [κ.tp_val]; simp; omega)
/-- The bank of the fourth power's call bank, tape `0` on tape `5`. -/
private def QyKit.bPu {f g : ℕ → ℕ} (κ : QyKit f g) : Fin κ.pu.k ↪ Fin κ.K :=
  qyBank (κ.tp 5) (16 + κ.cb.k + κ.cf.k) κ.pu.k (by unfold QyKit.K; omega)
    (by rw [κ.tp_val]; simp; omega)
/-- The bank of the counter's increment bank, tape `0` on tape `6`. -/
private def QyKit.bAb0 {f g : ℕ → ℕ} (κ : QyKit f g) : Fin κ.ab.k ↪ Fin κ.K :=
  qyBank (κ.tp 6) (16 + κ.cb.k + κ.cf.k + κ.pu.k) κ.ab.k (by unfold QyKit.K; omega)
    (by rw [κ.tp_val]; simp; omega)
/-- The bank of the increment bank of `j`, tape `0` on tape `10`. -/
private def QyKit.bAbJ {f g : ℕ → ℕ} (κ : QyKit f g) : Fin κ.ab.k ↪ Fin κ.K :=
  qyBank (κ.tp 10) (16 + κ.cb.k + κ.cf.k + κ.pu.k + κ.ab.k) κ.ab.k (by unfold QyKit.K; omega)
    (by rw [κ.tp_val]; simp; omega)
/-- The bank of the increment bank of `k`, tape `0` on tape `11`. -/
private def QyKit.bAbK {f g : ℕ → ℕ} (κ : QyKit f g) : Fin κ.ab.k ↪ Fin κ.K :=
  qyBank (κ.tp 11) (16 + κ.cb.k + κ.cf.k + κ.pu.k + κ.ab.k + κ.ab.k) κ.ab.k
    (by unfold QyKit.K; omega) (by rw [κ.tp_val]; simp; omega)
/-- The bank of the prefix call's bank, tape `0` on tape `9`. -/
private def QyKit.bPr {f g : ℕ → ℕ} (κ : QyKit f g) : Fin κ.pr.k ↪ Fin κ.K :=
  qyBank (κ.tp 9) (16 + κ.cb.k + κ.cf.k + κ.pu.k + κ.ab.k + κ.ab.k + κ.ab.k) κ.pr.k
    (by unfold QyKit.K; omega) (by rw [κ.tp_val]; simp; omega)
/-- The bank of the length call's bank, tape `0` on tape `10`. -/
private def QyKit.bCl {f g : ℕ → ℕ} (κ : QyKit f g) : Fin κ.cl.k ↪ Fin κ.K :=
  qyBank (κ.tp 10) (16 + κ.cb.k + κ.cf.k + κ.pu.k + κ.ab.k + κ.ab.k + κ.ab.k + κ.pr.k) κ.cl.k
    (by unfold QyKit.K; omega) (by rw [κ.tp_val]; simp; omega)
/-- The bank of the square's call bank, tape `0` on tape `4`. -/
private def QyKit.bPb {f g : ℕ → ℕ} (κ : QyKit f g) : Fin κ.pb.k ↪ Fin κ.K :=
  qyBank (κ.tp 4) (16 + κ.cb.k + κ.cf.k + κ.pu.k + κ.ab.k + κ.ab.k + κ.ab.k + κ.pr.k + κ.cl.k)
    κ.pb.k (by unfold QyKit.K; omega) (by rw [κ.tp_val]; simp; omega)
/-- The bank of `g`'s call bank, tape `0` on tape `14`. -/
private def QyKit.bCg {f g : ℕ → ℕ} (κ : QyKit f g) : Fin κ.cg.k ↪ Fin κ.K :=
  qyBank (κ.tp 14) (16 + κ.cb.k + κ.cf.k + κ.pu.k + κ.ab.k + κ.ab.k + κ.ab.k + κ.pr.k + κ.cl.k +
    κ.pb.k) κ.cg.k (by unfold QyKit.K; omega) (by rw [κ.tp_val]; simp; omega)

/-- The clock's bank: `f`'s call bank, then the counter tape. -/
private def QyKit.bClk {f g : ℕ → ℕ} (κ : QyKit f g) : Fin (κ.cf.k + 1) ↪ Fin κ.K where
  toFun j := if h : (j : ℕ) < κ.cf.k then κ.bCf ⟨j, h⟩ else κ.tp 8
  inj' i j hij := by
    dsimp only at hij
    by_cases hi : (i : ℕ) < κ.cf.k <;> by_cases hj : (j : ℕ) < κ.cf.k
    · rw [dif_pos hi, dif_pos hj] at hij
      exact Fin.ext (Fin.mk.inj_iff.mp (κ.bCf.injective hij))
    · rw [dif_pos hi, dif_neg hj] at hij
      exfalso
      by_cases h0 : (i : ℕ) = 0
      · have : (⟨i, hi⟩ : Fin κ.cf.k) = ⟨0, κ.cfK⟩ := Fin.ext h0
        rw [this] at hij
        unfold QyKit.bCf at hij
        rw [qyBank_zero] at hij
        exact absurd (κ.tp_inj.mp hij) (by decide)
      · have := congrArg Fin.val hij
        unfold QyKit.bCf at this
        rw [qyBank_val _ _ _ _ _ ⟨i, hi⟩ h0, κ.tp_val] at this
        simp at this
        omega
    · rw [dif_neg hi, dif_pos hj] at hij
      exfalso
      by_cases h0 : (j : ℕ) = 0
      · have : (⟨j, hj⟩ : Fin κ.cf.k) = ⟨0, κ.cfK⟩ := Fin.ext h0
        rw [this] at hij
        unfold QyKit.bCf at hij
        rw [qyBank_zero] at hij
        exact absurd (κ.tp_inj.mp hij) (by decide)
      · have := congrArg Fin.val hij
        unfold QyKit.bCf at this
        rw [qyBank_val _ _ _ _ _ ⟨j, hj⟩ h0, κ.tp_val] at this
        simp at this
        omega
    · exact Fin.ext (by omega)


/-- The named tapes are distinct. -/
private theorem QyKit.tp_ne {f g : ℕ → ℕ} (κ : QyKit f g) {a b : Fin 16} (h : a ≠ b) :
    κ.tp a ≠ κ.tp b :=
  fun e => h (κ.tp_inj.mp e)

/-! ### The phase hosts -/

/-- The locator's phases, in round order: the anchor; the argument and the clocked call; the
length test; the word `1^{X - 1}` and its test; the fourth power and its test; the next rung and
its comparison with `n + 1`; the cleanup; the update of `unpair h`; the three escapes. -/
private inductive QyLK
  | anc | r1 | clk | r3 | r4 | r5 | r6 | r7 | r8 | pu | r10 | r11 | ab | r13 | r14 | r15 | r16
  | c1 | c2 | c3 | c4 | c5 | c6 | c7 | u1 | incJ | u2 | clrK | clrJ | incK
  | escI | escTop | escTO
  deriving DecidableEq, Fintype

/-- The locator's phase carriers. -/
private abbrev QyLPh {f g : ℕ → ℕ} (κ : QyKit f g) : QyLK → Type
  | .clk => κ.Q
  | .r3 | .r7 | .r10 | .r16 | .u1 | .u2 => QyCmp
  | .r4 | .r13 => CounterLoopState (Fin ([true].length + 1))
  | .r6 | .r15 => RewindPhase
  | .pu => Unit ⊕ κ.pu.State
  | .ab | .incJ | .incK => Unit ⊕ κ.ab.State
  | .r14 => WritePhase [true].length
  | _ => SweepPhase

/-- The locator's phase carriers are finite. -/
private instance qyLPhFintype {f g : ℕ → ℕ} (κ : QyKit f g) (i : QyLK) :
    Fintype (QyLPh κ i) := by
  cases i <;> dsimp only [QyLPh] <;> infer_instance

/-- The locator's phase carriers have decidable equality. -/
private instance qyLPhDecEq {f g : ℕ → ℕ} (κ : QyKit f g) (i : QyLK) :
    DecidableEq (QyLPh κ i) := by
  cases i <;> dsimp only [QyLPh] <;> infer_instance

/-- The locator's phase machines. -/
private def qyLocM {f g : ℕ → ℕ} (κ : QyKit f g) : (i : QyLK) → MultiTapeTM κ.K Bool (QyLPh κ i)
  | .anc => clearTM κ.K (κ.tp 15)
  | .r1 => copyMapTM κ.K (κ.tp 2) (κ.tp 7) (fun b => b) (fun _ b => b)
  | .clk => embedEmitTM κ.bClk κ.H
  | .r3 => qyCmpTM κ.K (κ.tp 7) (κ.tp 1)
  | .r4 => embedEmitTM (qyEmb2 (κ.tp 4) (κ.tp 7) (κ.tp_ne (by decide))) (expandTM 1 0 [true])
  | .r5 => copyMapTM κ.K (κ.tp 2) (κ.tp 4) (fun b => b) (fun _ b => b)
  | .r6 => rewindTM κ.K (κ.tp 4)
  | .r7 => qyCmpTM κ.K (κ.tp 4) (κ.tp 1)
  | .r8 => copyMapTM κ.K (κ.tp 4) (κ.tp 5) (fun b => b) (fun _ b => b)
  | .pu => embedEmitTM κ.bPu (seamReleaseTM κ.pu.tm κ.puE)
  | .r10 => qyCmpTM κ.K (κ.tp 5) (κ.tp 1)
  | .r11 => copyMapTM κ.K (κ.tp 5) (κ.tp 6) (fun _ => false) (fun _ b => b)
  | .ab => embedEmitTM κ.bAb0 (seamReleaseTM κ.ab.tm κ.abE)
  | .r13 => embedEmitTM (qyEmb2 (κ.tp 3) (κ.tp 6) (κ.tp_ne (by decide))) (expandTM 1 0 [true])
  | .r14 => writeConstTM κ.K (κ.tp 3) [true]
  | .r15 => rewindTM κ.K (κ.tp 3)
  | .r16 => qyCmpTM κ.K (κ.tp 3) (κ.tp 0)
  | .c1 => clearTM κ.K (κ.tp 2)
  | .c2 => transferMapTM κ.K (κ.tp 3) (κ.tp 2) (fun b => b) (fun _ b => b) (fun _ => none)
  | .c3 => clearTM κ.K (κ.tp 7)
  | .c4 => clearTM κ.K (κ.tp 4)
  | .c5 => clearTM κ.K (κ.tp 5)
  | .c6 => clearTM κ.K (κ.tp 6)
  | .c7 => copyMapTM κ.K (κ.tp 9) (κ.tp 8) (fun b => b) (fun _ b => b)
  | .u1 => qyCmpTM κ.K (κ.tp 10) (κ.tp 11)
  | .incJ => embedEmitTM κ.bAbJ (seamReleaseTM κ.ab.tm κ.abE)
  | .u2 => qyCmpTM κ.K (κ.tp 10) (κ.tp 11)
  | .clrK => clearTM κ.K (κ.tp 11)
  | .clrJ => clearTM κ.K (κ.tp 10)
  | .incK => embedEmitTM κ.bAbK (seamReleaseTM κ.ab.tm κ.abE)
  | .escI => clearTM κ.K (κ.tp 15)
  | .escTop => clearTM κ.K (κ.tp 15)
  | .escTO => clearTM κ.K (κ.tp 15)

/-- The locator's dispatch table. -/
private def qyLocRed {f g : ℕ → ℕ} (κ : QyKit f g) :
    (i : QyLK) → QyLPh κ i → Option (Σ j, QyLPh κ j)
  | .anc, _ => some ⟨.r1, SweepPhase.sweep⟩
  | .r1, s => if s = .done then some ⟨.clk, κ.inj (Sum.inl ())⟩ else none
  | .clk, s =>
    if ∃ r, s = κ.fsh r then some ⟨.r3, QyCmp.scan⟩
    else if ∃ r, s = κ.tmo r then some ⟨.escTO, SweepPhase.sweep⟩ else none
  | .r3, s =>
    match s with
    | .done v => if v = .gt then some ⟨.escI, SweepPhase.sweep⟩
      else some ⟨.r4, CounterLoopState.dec .run⟩
    | _ => none
  | .r4, s => if s = .done then some ⟨.r5, SweepPhase.sweep⟩ else none
  | .r5, s => if s = .done then some ⟨.r6, RewindPhase.start⟩ else none
  | .r6, s => if s = .done then some ⟨.r7, QyCmp.scan⟩ else none
  | .r7, s =>
    match s with
    | .done v => if v = .lt then some ⟨.r8, SweepPhase.sweep⟩
      else some ⟨.escI, SweepPhase.sweep⟩
    | _ => none
  | .r8, s => if s = .done then some ⟨.pu, Sum.inl ()⟩ else none
  | .pu, s => if s = Sum.inr κ.puX then some ⟨.r10, QyCmp.scan⟩ else none
  | .r10, s =>
    match s with
    | .done v => if v = .lt then some ⟨.r11, SweepPhase.sweep⟩
      else some ⟨.escI, SweepPhase.sweep⟩
    | _ => none
  | .r11, s => if s = .done then some ⟨.ab, Sum.inl ()⟩ else none
  | .ab, s => if s = Sum.inr κ.abX then some ⟨.r13, CounterLoopState.dec .run⟩ else none
  | .r13, s => if s = .done then some ⟨.r14, WritePhase.wr 0⟩ else none
  | .r14, s => if s = .done then some ⟨.r15, RewindPhase.start⟩ else none
  | .r15, s => if s = .done then some ⟨.r16, QyCmp.scan⟩ else none
  | .r16, s =>
    match s with
    | .done v => if v = .lt then some ⟨.c1, SweepPhase.sweep⟩
      else if v = .eq then some ⟨.escTop, SweepPhase.sweep⟩
      else some ⟨.escI, SweepPhase.sweep⟩
    | _ => none
  | .c1, s => if s = .done then some ⟨.c2, SweepPhase.sweep⟩ else none
  | .c2, s => if s = .done then some ⟨.c3, SweepPhase.sweep⟩ else none
  | .c3, s => if s = .done then some ⟨.c4, SweepPhase.sweep⟩ else none
  | .c4, s => if s = .done then some ⟨.c5, SweepPhase.sweep⟩ else none
  | .c5, s => if s = .done then some ⟨.c6, SweepPhase.sweep⟩ else none
  | .c6, s => if s = .done then some ⟨.c7, SweepPhase.sweep⟩ else none
  | .c7, s => if s = .done then some ⟨.u1, QyCmp.scan⟩ else none
  | .u1, s =>
    match s with
    | .done v => if v = .lt then some ⟨.incJ, Sum.inl ()⟩
      else if v = .eq then some ⟨.clrJ, SweepPhase.sweep⟩
      else some ⟨.incK, Sum.inl ()⟩
    | _ => none
  | .incJ, s => if s = Sum.inr κ.abX then some ⟨.u2, QyCmp.scan⟩ else none
  | .u2, s =>
    match s with
    | .done v => if v = .eq then some ⟨.clrK, SweepPhase.sweep⟩
      else some ⟨.anc, SweepPhase.sweep⟩
    | _ => none
  | .clrK, s => if s = .done then some ⟨.anc, SweepPhase.sweep⟩ else none
  | .clrJ, s => if s = .done then some ⟨.incK, Sum.inl ()⟩ else none
  | .incK, s => if s = Sum.inr κ.abX then some ⟨.anc, SweepPhase.sweep⟩ else none
  | .escI, _ => none
  | .escTop, _ => none
  | .escTO, _ => none

/-- **The locator**: the phase host over the round's phases, started at its anchor. -/
private def qyLoc {f g : ℕ → ℕ} (κ : QyKit f g) : MultiTapeTM κ.K Bool (Σ i, QyLPh κ i) :=
  phaseHostTM (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ)

/-- The setup's phases: `bits n`; `1^n`, one more cell, the rewind; the first rung `1^3`; the
test `n ≥ 3`; the seek's `[true]`; the counter's copy, its fixed tail, the counter. -/
private inductive QySK
  | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10
  deriving DecidableEq, Fintype

/-- The setup's phase carriers. -/
private abbrev QySPh {f g : ℕ → ℕ} (κ : QyKit f g) : QySK → Type
  | .s1 => Unit ⊕ κ.cb.State
  | .s2 => CounterLoopState (Fin ([true].length + 1))
  | .s3 | .s7 => WritePhase [true].length
  | .s4 => RewindPhase
  | .s5 => WritePhase [true, true, true].length
  | .s6 => QyCmp
  | .s9 => Unit ⊕ κ.pr.State
  | .s8 | .s10 => SweepPhase

/-- The setup's phase carriers are finite. -/
private instance qySPhFintype {f g : ℕ → ℕ} (κ : QyKit f g) (i : QySK) :
    Fintype (QySPh κ i) := by
  cases i <;> dsimp only [QySPh] <;> infer_instance

/-- The setup's phase carriers have decidable equality. -/
private instance qySPhDecEq {f g : ℕ → ℕ} (κ : QyKit f g) (i : QySK) :
    DecidableEq (QySPh κ i) := by
  cases i <;> dsimp only [QySPh] <;> infer_instance

/-- The setup's phase machines. -/
private def qySetM {f g : ℕ → ℕ} (κ : QyKit f g) : (i : QySK) → MultiTapeTM κ.K Bool (QySPh κ i)
  | .s1 => embedEmitTM κ.bCb (seamReleaseTM κ.cb.tm κ.cbE)
  | .s2 => embedEmitTM (qyEmb2 (κ.tp 0) (κ.tp 1) (κ.tp_ne (by decide))) (expandTM 1 0 [true])
  | .s3 => writeConstTM κ.K (κ.tp 0) [true]
  | .s4 => rewindTM κ.K (κ.tp 0)
  | .s5 => writeConstTM κ.K (κ.tp 2) [true, true, true]
  | .s6 => qyCmpTM κ.K (κ.tp 0) (κ.tp 2)
  | .s7 => writeConstTM κ.K (κ.tp 12) [true]
  | .s8 => copyMapTM κ.K (κ.tp 1) (κ.tp 9) (fun b => b) (fun _ b => b)
  | .s9 => embedEmitTM κ.bPr (seamReleaseTM κ.pr.tm κ.prE)
  | .s10 => copyMapTM κ.K (κ.tp 9) (κ.tp 8) (fun b => b) (fun _ b => b)

/-- The setup's dispatch table. -/
private def qySetRed {f g : ℕ → ℕ} (κ : QyKit f g) :
    (i : QySK) → QySPh κ i → Option (Σ j, QySPh κ j)
  | .s1, s => if s = Sum.inr κ.cbX then some ⟨.s2, CounterLoopState.dec .run⟩ else none
  | .s2, s => if s = .done then some ⟨.s3, WritePhase.wr 0⟩ else none
  | .s3, s => if s = .done then some ⟨.s4, RewindPhase.start⟩ else none
  | .s4, s => if s = .done then some ⟨.s5, WritePhase.wr 0⟩ else none
  | .s5, s => if s = .done then some ⟨.s6, QyCmp.scan⟩ else none
  | .s6, s => if s = .done .gt then some ⟨.s7, WritePhase.wr 0⟩ else none
  | .s7, s => if s = .done then some ⟨.s8, SweepPhase.sweep⟩ else none
  | .s8, s => if s = .done then some ⟨.s9, Sum.inl ()⟩ else none
  | .s9, s => if s = Sum.inr κ.prX then some ⟨.s10, SweepPhase.sweep⟩ else none
  | .s10, _ => none

/-- **The setup**: the phase host over the setup's phases. -/
private def qySet {f g : ℕ → ℕ} (κ : QyKit f g) : MultiTapeTM κ.K Bool (Σ i, QySPh κ i) :=
  phaseHostTM (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ)

/-- The top's phases: the code's argument `1^{j + 1}` and `bits (j + 1)`; the budget
`bits (X²)`; the three emissions. -/
private inductive QyTK
  | t1 | t2 | t3 | t4 | t5 | t6
  deriving DecidableEq, Fintype

/-- The top's phase carriers. -/
private abbrev QyTPh {f g : ℕ → ℕ} (κ : QyKit f g) : QyTK → Type
  | .t1 => Unit ⊕ κ.ab.State
  | .t2 => Unit ⊕ κ.cl.State
  | .t3 => Unit ⊕ κ.pb.State
  | .t4 => QyEm [true].length [false, false, true, true].length 3
  | .t5 => QyEm ([] : List Bool).length [false, true].length 1
  | .t6 => QyEm ([] : List Bool).length ([] : List Bool).length 0

/-- The top writer's phase carriers are finite. -/
private instance qyTPhFintype {f g : ℕ → ℕ} (κ : QyKit f g) (i : QyTK) :
    Fintype (QyTPh κ i) := by
  cases i <;> dsimp only [QyTPh] <;> infer_instance

/-- The top writer's phase carriers have decidable equality. -/
private instance qyTPhDecEq {f g : ℕ → ℕ} (κ : QyKit f g) (i : QyTK) :
    DecidableEq (QyTPh κ i) := by
  cases i <;> dsimp only [QyTPh] <;> infer_instance

/-- The top's phase machines. -/
private def qyTopM {f g : ℕ → ℕ} (κ : QyKit f g) : (i : QyTK) → MultiTapeTM κ.K Bool (QyTPh κ i)
  | .t1 => embedEmitTM κ.bAbJ (seamReleaseTM κ.ab.tm κ.abE)
  | .t2 => embedEmitTM κ.bCl (seamReleaseTM κ.cl.tm κ.clE)
  | .t3 => embedEmitTM κ.bPb (seamReleaseTM κ.pb.tm κ.pbE)
  | .t4 => qyEmitTM κ.K (κ.tp 4) [true] [false, false, true, true] 3 false
  | .t5 => qyEmitTM κ.K (κ.tp 10) [] [false, true] 1 true
  | .t6 => qyEmitTM κ.K (κ.tp 2) [] [] 0 false

/-- The top's dispatch table; the last emission's exit halts. -/
private def qyTopRed {f g : ℕ → ℕ} (κ : QyKit f g) :
    (i : QyTK) → QyTPh κ i → Option (Σ j, QyTPh κ j)
  | .t1, s => if s = Sum.inr κ.abX then some ⟨.t2, Sum.inl ()⟩ else none
  | .t2, s => if s = Sum.inr κ.clX then some ⟨.t3, Sum.inl ()⟩ else none
  | .t3, s => if s = Sum.inr κ.pbX then some ⟨.t4, QyEm.pre 0⟩ else none
  | .t4, s => if s = .done then some ⟨.t5, QyEm.pre 0⟩ else none
  | .t5, s => if s = .done then some ⟨.t6, QyEm.pre 0⟩ else none
  | .t6, _ => none

/-- **The top's writer**: the phase host over the top's phases. -/
private def qyTop {f g : ℕ → ℕ} (κ : QyKit f g) : MultiTapeTM κ.K Bool (Σ i, QyTPh κ i) :=
  phaseHostTM (qyTopM κ) ⟨.t1, Sum.inl ()⟩ (qyTopRed κ)

/-- The middle's phases: the input head home; the code; the budget `bits (g n)`; the three
emissions. -/
private inductive QyMK
  | m0 | m1 | m2 | m3 | m4 | m5 | m6
  deriving DecidableEq, Fintype

/-- The middle's phase carriers. -/
private abbrev QyMPh {f g : ℕ → ℕ} (κ : QyKit f g) : QyMK → Type
  | .m0 => κ.S
  | .m1 => Unit ⊕ κ.ab.State
  | .m2 => Unit ⊕ κ.cl.State
  | .m3 => Unit ⊕ κ.cg.State
  | .m4 => QyEm [false].length [false, false, true, true].length 3
  | .m5 => QyEm ([] : List Bool).length [false, true].length 1
  | .m6 => QyEm ([] : List Bool).length ([] : List Bool).length 0

/-- The middle writer's phase carriers are finite. -/
private instance qyMPhFintype {f g : ℕ → ℕ} (κ : QyKit f g) (i : QyMK) :
    Fintype (QyMPh κ i) := by
  cases i <;> dsimp only [QyMPh] <;> infer_instance

/-- The middle writer's phase carriers have decidable equality. -/
private instance qyMPhDecEq {f g : ℕ → ℕ} (κ : QyKit f g) (i : QyMK) :
    DecidableEq (QyMPh κ i) := by
  cases i <;> dsimp only [QyMPh] <;> infer_instance

/-- The middle's phase machines. -/
private def qyMidM {f g : ℕ → ℕ} (κ : QyKit f g) : (i : QyMK) → MultiTapeTM κ.K Bool (QyMPh κ i)
  | .m0 => embedEmitTM (qyEmb2 (κ.tp 12) (κ.tp 13) (κ.tp_ne (by decide))) κ.R
  | .m1 => embedEmitTM κ.bAbJ (seamReleaseTM κ.ab.tm κ.abE)
  | .m2 => embedEmitTM κ.bCl (seamReleaseTM κ.cl.tm κ.clE)
  | .m3 => embedEmitTM κ.bCg (seamReleaseTM κ.cg.tm κ.cgE)
  | .m4 => qyEmitTM κ.K (κ.tp 14) [false] [false, false, true, true] 3 false
  | .m5 => qyEmitTM κ.K (κ.tp 10) [] [false, true] 1 true
  | .m6 => qyEmitTM κ.K (κ.tp 0) [] [] 0 false

/-- The middle's dispatch table; the last emission's exit halts. -/
private def qyMidRed {f g : ℕ → ℕ} (κ : QyKit f g) :
    (i : QyMK) → QyMPh κ i → Option (Σ j, QyMPh κ j)
  | .m0, s => if s = κ.rX then some ⟨.m1, Sum.inl ()⟩ else none
  | .m1, s => if s = Sum.inr κ.abX then some ⟨.m2, Sum.inl ()⟩ else none
  | .m2, s => if s = Sum.inr κ.clX then some ⟨.m3, Sum.inl ()⟩ else none
  | .m3, s => if s = Sum.inr κ.cgX then some ⟨.m4, QyEm.pre 0⟩ else none
  | .m4, s => if s = .done then some ⟨.m5, QyEm.pre 0⟩ else none
  | .m5, s => if s = .done then some ⟨.m6, QyEm.pre 0⟩ else none
  | .m6, _ => none

/-- **The middle's writer**: the phase host over the middle's phases. -/
private def qyMid {f g : ℕ → ℕ} (κ : QyKit f g) : MultiTapeTM κ.K Bool (Σ i, QyMPh κ i) :=
  phaseHostTM (qyMidM κ) ⟨.m0, κ.rE⟩ (qyMidRed κ)

/-- The main machine's phases: the setup, the locator, the two writers, and the empty output. -/
private inductive QyMain
  | setup | loc | top | mid | halt
  deriving DecidableEq, Fintype

/-- The main machine's phase carriers. -/
private abbrev QyMainPh {f g : ℕ → ℕ} (κ : QyKit f g) : QyMain → Type
  | .setup => Σ i, QySPh κ i
  | .loc => Σ i, QyLPh κ i
  | .top => Σ i, QyTPh κ i
  | .mid => Σ i, QyMPh κ i
  | .halt => QyEm ([] : List Bool).length ([] : List Bool).length 0

/-- The main machine's phase carriers are finite. -/
private instance qyMainPhFintype {f g : ℕ → ℕ} (κ : QyKit f g) (i : QyMain) :
    Fintype (QyMainPh κ i) := by
  cases i <;> dsimp only [QyMainPh] <;> infer_instance

/-- The main machine's phase carriers have decidable equality. -/
private instance qyMainPhDecEq {f g : ℕ → ℕ} (κ : QyKit f g) (i : QyMain) :
    DecidableEq (QyMainPh κ i) := by
  cases i <;> dsimp only [QyMainPh] <;> infer_instance

/-- The main machine's phase machines. -/
private def qyMainM {f g : ℕ → ℕ} (κ : QyKit f g) :
    (i : QyMain) → MultiTapeTM κ.K Bool (QyMainPh κ i)
  | .setup => qySet κ
  | .loc => qyLoc κ
  | .top => qyTop κ
  | .mid => qyMid κ
  | .halt => qyEmitTM κ.K (κ.tp 15) [] [] 0 false

/-- The main machine's dispatch table: the setup's long exit to the locator's anchor and its
short exits to the empty output; the locator's top escape to the top's writer and its other
escapes to the middle's. -/
private def qyMainRed {f g : ℕ → ℕ} (κ : QyKit f g) :
    (i : QyMain) → QyMainPh κ i → Option (Σ j, QyMainPh κ j)
  | .setup, ⟨.s10, s⟩ =>
    if s = .done then some ⟨.loc, ⟨.anc, SweepPhase.sweep⟩⟩ else none
  | .setup, ⟨.s6, s⟩ =>
    if s = .done .lt ∨ s = .done .eq then some ⟨.halt, QyEm.pre 0⟩ else none
  | .setup, _ => none
  | .loc, ⟨.escI, _⟩ => some ⟨.mid, ⟨.m0, κ.rE⟩⟩
  | .loc, ⟨.escTO, _⟩ => some ⟨.mid, ⟨.m0, κ.rE⟩⟩
  | .loc, ⟨.escTop, _⟩ => some ⟨.top, ⟨.t1, Sum.inl ()⟩⟩
  | .loc, _ => none
  | .top, _ => none
  | .mid, _ => none
  | .halt, _ => none

/-- **The main machine `M₁`**: the phase host over the setup, the locator and the writers. -/
private def qyM₁ {f g : ℕ → ℕ} (κ : QyKit f g) : FinTM Bool where
  k := κ.K
  State := Σ i, QyMainPh κ i
  tm := phaseHostTM (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ)

/-- The clock's counter width on inputs of length `n`: the bits of `n` and of the call bound's
constant. -/
private def QyKit.m {f g : ℕ → ℕ} (κ : QyKit f g) (n : ℕ) : ℕ :=
  (Nat.bits (κ.cfA * (κ.cfc + 2))).length + (Nat.bits n).length

/-- **The anchor layout** at the rung `a - 1` with `unpair h = (j, k)`: `1^{n+1}` on tape `0`, the
width word on tape `1`, the rung `1^a` on tape `2`, `1^j` and `1^k` on tapes `10` and `11`, the
seek's `[true]` on tape `12`, the all-ones counter and its copy on tapes `8` and `9`, and every
other tape blank. -/
private def qyLay {f g : ℕ → ℕ} (κ : QyKit f g) (n a j k : ℕ) (t : Fin κ.K) : List Bool :=
  if t = κ.tp 0 then List.replicate (n + 1) true
  else if t = κ.tp 1 then List.replicate (Nat.bits n).length true
  else if t = κ.tp 2 then List.replicate a true
  else if t = κ.tp 10 then List.replicate j true
  else if t = κ.tp 11 then List.replicate k true
  else if t = κ.tp 12 then [true]
  else if t = κ.tp 8 then List.replicate (κ.m n) true
  else if t = κ.tp 9 then List.replicate (κ.m n) true
  else []

/-- Every tape is a named tape or none of them (`Classical.exists_or_forall_not`). -/
private theorem QyKit.tape_cases {f g : ℕ → ℕ} (κ : QyKit f g) (t : Fin κ.K) :
    (∃ c : Fin 16, t = κ.tp c) ∨ ∀ c : Fin 16, t ≠ κ.tp c :=
  Classical.exists_or_forall_not fun c => t = κ.tp c

/-- A bank's tapes other than its tape `0` lie in its block, off every named tape. -/
private theorem qyBank_ne_tp {f g : ℕ → ℕ} (κ : QyKit f g) (t0 : Fin κ.K) (off k : ℕ)
    (hK : off + k ≤ κ.K)
    (h0 : (t0 : ℕ) < off) (hoff : 16 ≤ off) (i : Fin k) (hi : (i : ℕ) ≠ 0) (c : Fin 16) :
    qyBank t0 off k hK h0 i ≠ κ.tp c := by
  intro h
  have := congrArg Fin.val h
  rw [qyBank_val _ _ _ _ _ _ hi, κ.tp_val] at this
  have := c.isLt
  omega

/-- The setup's exits: the long exit at the end, and the short exits of the test `n ≥ 3`. -/
private def qySetF {f g : ℕ → ℕ} (κ : QyKit f g) : Set (Option (Σ i, QySPh κ i)) :=
  {some ⟨.s10, SweepPhase.done⟩, some ⟨.s6, QyCmp.done .lt⟩, some ⟨.s6, QyCmp.done .eq⟩}

/-- The setup's time bound on inputs of length `n`. -/
private def qySetB {f g : ℕ → ℕ} (κ : QyKit f g) (n : ℕ) : ℕ :=
  (κ.cbA + κ.prA + 2 * (Nat.bits (κ.cfA * (κ.cfc + 2))).length + 60) * (n + 1)

/-- The bits of `n` are worth `n`. -/
private theorem qy_bits_val (n : ℕ) : Nat.ofDigits 2 ((Nat.bits n).map Bool.toNat) = n := by
  rw [← counterValue_eq, counterValue_bits]

/-- A blank bank holds the seam of the empty argument. -/
private theorem qy_blank_bank {K k : ℕ} (σ : Fin k ↪ Fin K) (T : Fin K → ℤ → Option Bool)
    (hT : ∀ i, T (σ i) = FinTM.bufferTape []) :
    ∀ i, T (σ i) = FinTM.bufferTape (stateWord k [] i) := by
  intro i
  rw [hT, stateWord_eq]
  split <;> rfl

/-- A bank holding `arg` on its tape `0` and blanks elsewhere holds the seam of `arg`. -/
private theorem qy_arg_bank {K k : ℕ} (σ : Fin k ↪ Fin K) (hk : 0 < k) (T : Fin K → ℤ → Option Bool)
    (arg : List Bool) (h0 : T (σ ⟨0, hk⟩) = FinTM.bufferTape arg)
    (hT : ∀ i : Fin k, (i : ℕ) ≠ 0 → T (σ i) = FinTM.bufferTape []) :
    ∀ i, T (σ i) = FinTM.bufferTape (stateWord k arg i) := by
  intro i
  rw [stateWord_eq]
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi]
    have : i = ⟨0, hk⟩ := Fin.ext hi
    rw [this, h0]
  · rw [if_neg hi, hT i hi]

/-- The prefix call's bank tapes other than tape `0` are off the named tapes. -/
private theorem QyKit.bPr_ne {f g : ℕ → ℕ} (κ : QyKit f g) (i : Fin κ.pr.k) (hi : (i : ℕ) ≠ 0)
    (c : Fin 16) :
    κ.bPr i ≠ κ.tp c := qyBank_ne_tp κ _ _ _ _ _ (by omega) i hi c

/-- The setup's tapes before its test: `bits n` expanded, `1^{n+1}` on tape `0`, the width word on
tape `1`, the rung `1^3` on tape `2`, every other tape blank. -/
private def qySetT5 {f g : ℕ → ℕ} (κ : QyKit f g) (n : ℕ) : Fin κ.K → ℤ → Option Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (fun _ => FinTM.bufferTape []) (κ.tp 1) (FinTM.bufferTape (Nat.bits n)))
    (κ.tp 0) (FinTM.bufferTape ([] ++ List.replicate n true))) (κ.tp 1)
    (FinTM.bufferTape (List.replicate (Nat.bits n).length true)))
    (κ.tp 0) (FinTM.bufferTape (List.replicate n true ++ [true])))
    (κ.tp 2) (FinTM.bufferTape ([] ++ [true, true, true]))

/-- **The setup's head**: from the blank seam, `bits n` by the input call, its expansion to
`1^{n+1}` on tape `0`, and the first rung `1^3` on tape `2`, within `cbA (n + 1) + 7n + 2|bits n| +
27` steps, avoiding the setup's exits.

**Proof sketch.** Five hosted phases (`qy_hosted`), chained by `Turing.Segment.trans`: the input
call of the length's bits (`qy_callHost`), the expansion of `bits n` onto tape `0`
(`qy_expandHost`, the counter worth `n` by `qy_bits_val`), one more cell (`qy_writeConst`), the
rewind (`qy_rewind`), and the rung `1^3` (`qy_writeConst`). Each guard is the row's cut. The
expansion's overhead is at most `4n + 2|bits n| + 2` (`Turing.counterOverhead_le`). -/
private theorem qy_setup_head {f g : ℕ → ℕ} (κ : QyKit f g) (x : List Bool) :
    ∃ t ≤ κ.cbA * (x.length + 1) + 7 * x.length + 2 * (Nat.bits x.length).length + 27,
      Segment (qySet κ) (qySetF κ) (fun _ => True)
        (qyC (x := x) ⟨.s1, Sum.inl ()⟩ 1 (fun _ => FinTM.bufferTape []) (fun _ => 0) [])
        (qyC ⟨.s6, QyCmp.scan⟩ 1 (qySetT5 κ x.length) (fun _ => 0) []) t := by
  set n := x.length with hnx
  set P₀ : Fin κ.K → ℤ := fun _ => 0 with hP₀
  -- s1: bits n by the input call
  obtain ⟨t1, ht1, hpos1, hcut1, hrun1⟩ := κ.cbS x
  set T0 : Fin κ.K → ℤ → Option Bool := fun _ => FinTM.bufferTape [] with hT0
  have c1 := qy_callHost κ.cb κ.cbK κ.bCb κ.cbE κ.cbX [] (Nat.bits n) t1 hpos1 hcut1 hrun1 T0 P₀ []
    (qy_blank_bank _ _ fun _ => rfl) (fun _ => rfl)
  have hb0 : κ.bCb ⟨0, κ.cbK⟩ = κ.tp 1 := rfl
  rw [hb0] at c1
  set T1 := Function.update T0 (κ.tp 1) (FinTM.bufferTape (Nat.bits n)) with hT1
  have seg1 := qy_hosted (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ) .s1 (Sum.inl ())
    (Sum.inr κ.cbX) ⟨.s2, CounterLoopState.dec .run⟩ 1 1 T0 T1 P₀ P₀ [] [] t1 c1.1
    (by simp [qySetRed])
    (qy_guard_of_cut (Sum.inr κ.cbX) (qySetRed κ .s1) (fun s hs => by simp [qySetRed, hs]) c1.2)
    (qySetF κ) (fun s h => by simp [qySetF] at h)
  -- s2: 1^n on tape 0 from the counter bits n on tape 1
  have c2 := qy_expandHost (x := x) (qyEmb2 (κ.tp 0) (κ.tp 1) (κ.tp_ne (by decide))) (κ.tp 0)
    (κ.tp 1) rfl rfl 1 T1 P₀ [] [] (Nat.bits n) n (qy_bits_val n)
    (by simp [hT1, hT0, κ.tp_ne]) (by simp [hP₀]) (by simp [hT1]) (by simp [hP₀])
  set T2 := Function.update (Function.update T1 (κ.tp 0)
    (FinTM.bufferTape ([] ++ List.replicate n true))) (κ.tp 1)
      (FinTM.bufferTape (List.replicate (Nat.bits n).length true)) with hT2
  set P2 := Function.update P₀ (κ.tp 0) (([] : List Bool).length + (n : ℤ)) with hP2
  have seg2 := qy_hosted (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ) .s2 (.dec .run) .done
    ⟨.s3, WritePhase.wr 0⟩ 1 1 T1 T2 P₀ P2 [] [] _ c2.1 (by simp [qySetRed])
    (qy_guard_of_cut CounterLoopState.done (qySetRed κ .s2) (fun s hs => by simp [qySetRed, hs])
      c2.2) (qySetF κ) (fun s h => by simp [qySetF] at h)
  -- s3: one more cell
  have c3 := qy_writeConst (x := x) (κ.tp 0) [true] 1 T2 P2 [] (List.replicate n true)
    (by simp [hT2, κ.tp_ne]) (by simp [hP2])
  set T3 := Function.update T2 (κ.tp 0) (FinTM.bufferTape (List.replicate n true ++ [true]))
    with hT3
  have seg3 := qy_hosted (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ) .s3 (.wr 0) .done
    ⟨.s4, RewindPhase.start⟩ 1 1 T2 T3 P2 P2 [] [] _ c3.1 (by simp [qySetRed])
    (qy_guard_of_cut WritePhase.done (qySetRed κ .s3) (fun s hs => by simp [qySetRed, hs]) c3.2)
    (qySetF κ) (fun s h => by simp [qySetF] at h)
  -- s4: rewind tape 0
  have c4 := qy_rewind (x := x) (κ.tp 0) 1 T3 P2 [] (List.replicate n true ++ [true]) n
    (by simp) (by simp [hT3]) (by simp [hP2])
  have hP4 : Function.update P2 (κ.tp 0) 0 = P₀ := by
    rw [hP2, Function.update_idem]
    exact Function.update_eq_self_iff.mpr rfl
  rw [hP4] at c4
  have seg4 := qy_hosted (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ) .s4 .start .done
    ⟨.s5, WritePhase.wr 0⟩ 1 1 T3 T3 P2 P₀ [] [] _ c4.1 (by simp [qySetRed])
    (qy_guard_of_cut RewindPhase.done (qySetRed κ .s4) (fun s hs => by simp [qySetRed, hs]) c4.2)
    (qySetF κ) (fun s h => by simp [qySetF] at h)
  -- s5: the first rung 1^3 on tape 2
  have c5 := qy_writeConst (x := x) (κ.tp 2) [true, true, true] 1 T3 P₀ [] []
    (by simp [hT3, hT2, hT1, hT0, κ.tp_ne]) (by simp [hP₀])
  set T5 := Function.update T3 (κ.tp 2) (FinTM.bufferTape ([] ++ [true, true, true])) with hT5
  have seg5 := qy_hosted (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ) .s5 (.wr 0) .done
    ⟨.s6, QyCmp.scan⟩ 1 1 T3 T5 P₀ P₀ [] [] _ c5.1 (by simp [qySetRed])
    (qy_guard_of_cut WritePhase.done (qySetRed κ .s5) (fun s hs => by simp [qySetRed, hs]) c5.2)
    (qySetF κ) (fun s h => by simp [qySetF] at h)
  refine ⟨_, ?_, seg1.trans (seg2.trans (seg3.trans (seg4.trans seg5)))⟩
  have hco := counterOverhead_le (Nat.bits n)
  rw [qy_bits_val] at hco
  have ht1' : t1 ≤ κ.cbA * (n + 1) := ht1
  simp only [List.length_cons, List.length_nil]
  show _ ≤ κ.cbA * (n + 1) + 7 * n + 2 * (Nat.bits n).length + 27
  omega

/-- **The setup, long path** (checkpoint 2): on inputs of length `n ≥ 3`, from the blank seam, the
setup reaches its long exit at the anchor layout of the first rung `ℓ₀ = 2` (`a = 3`) with
`unpair 0 = (0, 0)`, within `qySetB κ n` steps, avoiding its exits before.

**Proof sketch.** The head (`qy_setup_head`), then five more hosted phases: the test `n ≥ 3`
(`qy_cmp_run`, whose verdict is `gt` since `n + 1 > 3`), the seek's `[true]`, the width word's
copy, the prefix call that widens it to the counter `1^m` (`qy_callHost`), and its copy onto the
clock's tape, the last without dispatch (`qy_hosted_last`). The endpoint's tapes are the anchor
layout, tape by tape. The phase times sum to at most `qySetB κ n`, since `|bits n| ≤ n`. -/
private theorem qy_setup_long {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (hn : 3 ≤ x.length) :
    ∃ t ≤ qySetB κ x.length,
      Segment (qySet κ) (qySetF κ) (fun _ => True)
        (qyC (x := x) ⟨.s1, Sum.inl ()⟩ 1 (fun _ => FinTM.bufferTape []) (fun _ => 0) [])
        (qyC ⟨.s10, SweepPhase.done⟩ 1 (fun t => FinTM.bufferTape (qyLay κ x.length 3 0 0 t))
          (fun _ => 0) []) t := by
  obtain ⟨th, hth, seg5⟩ := qy_setup_head κ x
  set n := x.length with hnx
  set P₀ : Fin κ.K → ℤ := fun _ => 0 with hP₀
  set T5 := qySetT5 κ n with hT5
  -- s6: the test n ≥ 3
  have c6 := qy_cmp_run (x := x) (κ.tp 0) (κ.tp 2) (κ.tp_ne (by decide)) 1 T5 P₀ []
    (List.replicate n true ++ [true]) [true, true, true] (by simp [hT5, qySetT5, κ.tp_ne])
    (by simp [hT5, qySetT5]) rfl rfl
  have hcmp : compare (List.replicate n true ++ [true]).length [true, true, true].length =
      .gt := by
    rw [compare_gt_iff_gt]
    simp
    omega
  rw [hcmp] at c6
  have seg6 := qy_hosted' (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ) .s6 .scan (.done .gt)
    ⟨.s7, WritePhase.wr 0⟩ 1 1 T5 T5 P₀ P₀ [] [] _ c6.1 (by simp [qySetRed])
    (fun u hu s hs => by
      have := c6.2 u hu
      cases s with
      | done v => exact absurd hs (this v)
      | _ => simp [qySetRed])
    (qySetF κ) (fun u hu s hs h => by
      rcases Nat.lt_or_ge u (2 * min (List.replicate n true ++ [true]).length
        [true, true, true].length + 2) with hlt | hge
      · have := c6.2 u hlt
        simp only [qySetF, Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq,
          Sigma.mk.inj_iff, heq_eq_eq, reduceCtorEq, false_and, true_and, false_or] at h
        rcases h with rfl | rfl
        · exact this _ hs
        · exact this _ hs
      · obtain rfl : u = 2 * min (List.replicate n true ++ [true]).length
          [true, true, true].length + 2 := by omega
        rw [c6.1] at hs
        cases Option.some.inj hs
        simp [qySetF] at h)
  -- s7: the seek's [true] on tape 12
  have c7 := qy_writeConst (x := x) (κ.tp 12) [true] 1 T5 P₀ [] []
    (by simp [hT5, qySetT5, κ.tp_ne]) (by simp [hP₀])
  set T7 := Function.update T5 (κ.tp 12) (FinTM.bufferTape ([] ++ [true])) with hT7
  have seg7 := qy_hosted (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ) .s7 (.wr 0) .done
    ⟨.s8, SweepPhase.sweep⟩ 1 1 T5 T7 P₀ P₀ [] [] _ c7.1 (by simp [qySetRed])
    (qy_guard_of_cut WritePhase.done (qySetRed κ .s7) (fun s hs => by simp [qySetRed, hs]) c7.2)
    (qySetF κ) (fun s h => by simp [qySetF] at h)
  -- s8: the width word onto tape 9
  have c8 := qy_copy (x := x) (κ.tp 1) (κ.tp 9) (κ.tp_ne (by decide)) (fun b => b) 1 T7 P₀ []
    (List.replicate (Nat.bits n).length true) [] (by simp [hT7, hT5, qySetT5, κ.tp_ne])
    rfl (by simp [hT7, hT5, qySetT5, κ.tp_ne]) (by simp [hP₀])
  set T8 := Function.update T7 (κ.tp 9)
    (FinTM.bufferTape ([] ++ (List.replicate (Nat.bits n).length true).map fun b => b)) with hT8
  have seg8 := qy_hosted (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ) .s8 .sweep .done
    ⟨.s9, Sum.inl ()⟩ 1 1 T7 T8 P₀ P₀ [] [] _ c8.1 (by simp [qySetRed])
    (qy_guard_of_cut SweepPhase.done (qySetRed κ .s8) (fun s hs => by simp [qySetRed, hs]) c8.2)
    (qySetF κ) (fun s h => by simp [qySetF] at h)
  -- s9: the counter's fixed tail
  obtain ⟨t9, ht9, hpos9, hcut9, hrun9⟩ :=
    κ.prS x (List.replicate (Nat.bits n).length true)
  have hb9 : κ.bPr ⟨0, κ.prK⟩ = κ.tp 9 := rfl
  have c9 := qy_callHost κ.pr κ.prK κ.bPr κ.prE κ.prX (List.replicate (Nat.bits n).length true)
    _ t9 hpos9 hcut9 hrun9 T8 P₀ []
    (qy_arg_bank κ.bPr κ.prK T8 _ (by rw [hb9]; simp [hT8])
      (fun i hi => by simp [hT8, hT7, hT5, qySetT5, κ.bPr_ne i hi]))
    (fun _ => rfl)
  rw [hb9] at c9
  set T9 := Function.update T8 (κ.tp 9) (FinTM.bufferTape
    (List.replicate (Nat.bits (κ.cfA * (κ.cfc + 2))).length true ++
      List.replicate (Nat.bits n).length true)) with hT9
  have seg9 := qy_hosted (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ) .s9 (Sum.inl ())
    (Sum.inr κ.prX) ⟨.s10, SweepPhase.sweep⟩ 1 1 T8 T9 P₀ P₀ [] [] t9 c9.1
    (by simp [qySetRed])
    (qy_guard_of_cut (Sum.inr κ.prX) (qySetRed κ .s9) (fun s hs => by simp [qySetRed, hs]) c9.2)
    (qySetF κ) (fun s h => by simp [qySetF] at h)
  -- s10: the counter onto tape 8
  have hm : List.replicate (Nat.bits (κ.cfA * (κ.cfc + 2))).length true ++
      List.replicate (Nat.bits n).length true = List.replicate (κ.m n) true := by
    rw [List.replicate_append_replicate]
    rfl
  have c10 := qy_copy (x := x) (κ.tp 9) (κ.tp 8) (κ.tp_ne (by decide)) (fun b => b) 1 T9 P₀ []
    (List.replicate (κ.m n) true) [] (by simp [hT9, hm]) rfl
    (by simp [hT9, hT8, hT7, hT5, qySetT5, κ.tp_ne]) (by simp [hP₀])
  have seg10 := qy_hosted_last (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ) .s10 .sweep .done 1 1
    T9 _ P₀ P₀ [] [] _ c10.1 (fun u _ s _ => by simp [qySetRed])
    (qySetF κ) (fun u hu s hs h => by
      simp only [qySetF, Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq,
        Sigma.mk.inj_iff, heq_eq_eq, reduceCtorEq, false_and, true_and, or_false] at h
      subst h
      exact c10.2 u hu hs)
  -- the endpoint is the anchor layout
  have hend : Function.update T9 (κ.tp 8) (FinTM.bufferTape ([] ++
      (List.replicate (κ.m n) true).map fun b => b)) =
      fun t => FinTM.bufferTape (qyLay κ n 3 0 0 t) := by
    funext t
    rcases κ.tape_cases t with ⟨c, rfl⟩ | h
    · fin_cases c <;>
        simp [hT9, hT8, hT7, hT5, qySetT5, qyLay, QyKit.tp_inj, List.replicate_succ', hm]
    · simp [hT9, hT8, hT7, hT5, qySetT5, qyLay, h]
  rw [hend] at seg10
  refine ⟨_, ?_, seg5.trans (seg6.trans (seg7.trans (seg8.trans (seg9.trans seg10))))⟩
  -- the time bound
  have hbn := length_bits_le_self n
  have hmin : min (List.replicate n true ++ [true]).length [true, true, true].length ≤ 3 :=
    min_le_right _ _
  have ht9' : t9 ≤ κ.prA * ((Nat.bits n).length + 1) := by simpa using ht9
  have h1 : κ.prA * ((Nat.bits n).length + 1) ≤ κ.prA * (n + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (Nat.bits (κ.cfA * (κ.cfc + 2))).length ≤
      (Nat.bits (κ.cfA * (κ.cfc + 2))).length * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  simp only [List.length_replicate, List.length_append, List.length_cons, List.length_nil]
    at hmin ⊢
  unfold qySetB QyKit.m
  rw [← hnx]
  nlinarith

/-- **The setup, short path** (checkpoint 2): on inputs of length `n ≤ 2`, from the blank seam,
the setup stops at a short exit of its test `n ≥ 3` within `qySetB κ n` steps, avoiding its exits
before, with tape `15` blank and nothing emitted.

**Proof sketch.** The head (`qy_setup_head`), then the test `n ≥ 3` as the last phase
(`qy_hosted_last`): `n + 1 ≤ 3`, so the verdict is `lt` or `eq`, an exit the setup does not
redirect. -/
private theorem qy_setup_short {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (hn : x.length ≤ 2) :
    ∃ t ≤ qySetB κ x.length, ∃ v : Ordering, (v = .lt ∨ v = .eq) ∧
      Segment (qySet κ) (qySetF κ) (fun _ => True)
        (qyC (x := x) ⟨.s1, Sum.inl ()⟩ 1 (fun _ => FinTM.bufferTape []) (fun _ => 0) [])
        (qyC ⟨.s6, QyCmp.done v⟩ 1 (qySetT5 κ x.length) (fun _ => 0) []) t := by
  obtain ⟨th, hth, seg5⟩ := qy_setup_head κ x
  set n := x.length with hnx
  have c6 := qy_cmp_run (x := x) (κ.tp 0) (κ.tp 2) (κ.tp_ne (by decide)) 1 (qySetT5 κ n)
    (fun _ => 0) [] (List.replicate n true ++ [true]) [true, true, true]
    (by simp [qySetT5, κ.tp_ne]) (by simp [qySetT5]) rfl rfl
  have hv : compare (List.replicate n true ++ [true]).length [true, true, true].length = .lt ∨
      compare (List.replicate n true ++ [true]).length [true, true, true].length = .eq := by
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    rcases (show n + 1 < 3 ∨ n + 1 = 3 by omega) with h | h
    · exact Or.inl (compare_lt_iff_lt.mpr h)
    · exact Or.inr (compare_eq_iff_eq.mpr h)
  have seg6 := qy_hosted_last (qySetM κ) ⟨.s1, Sum.inl ()⟩ (qySetRed κ) .s6 .scan _ 1 1
    (qySetT5 κ n) _ (fun _ => 0) _ [] [] _ c6.1
    (fun u hu s hs => by
      have := c6.2 u hu
      cases s with
      | done w => exact absurd hs (this w)
      | _ => simp [qySetRed])
    (qySetF κ) (fun u hu s hs h => by
      have := c6.2 u hu
      simp only [qySetF, Set.mem_insert_iff, Set.mem_singleton_iff, Option.some.injEq,
        Sigma.mk.inj_iff, heq_eq_eq, reduceCtorEq, false_and, true_and, false_or] at h
      rcases h with rfl | rfl
      · exact this _ hs
      · exact this _ hs)
  refine ⟨_, ?_, _, hv, seg5.trans seg6⟩
  have hmin : min (List.replicate n true ++ [true]).length [true, true, true].length ≤ 3 :=
    min_le_right _ _
  have hbn := length_bits_le_self n
  simp only [List.length_cons, List.length_nil] at hmin ⊢
  unfold qySetB
  nlinarith

/-! ### The locator's round: arithmetic -/

/-- The length of `bits` is monotone. -/
private theorem qy_bits_len_mono {a b : ℕ} (h : a ≤ b) :
    (Nat.bits a).length ≤ (Nat.bits b).length := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Nat.zero_bits, List.length_nil]
    exact Nat.zero_le _
  · rw [← qy_log_bits ha, ← qy_log_bits (ha.trans_le h)]
    exact Nat.succ_le_succ (Nat.log_mono_right h)

/-- Every number is below two to the length of its bits. -/
private theorem qy_lt_two_pow_bits (n : ℕ) : n < 2 ^ (Nat.bits n).length := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_bits, List.length_nil]
    exact Nat.one_pos
  · rw [← qy_log_bits hn]
    exact Nat.lt_pow_succ_log_self (by norm_num) n

/-- The successor of a pair below the diagonal's next corner: `(j, k) ↦ (j + 1, k)` when
`j + 1 < k`. -/
private theorem qy_unpair_succ_lt {h j k : ℕ} (H : Nat.unpair h = (j, k)) (hjk : j + 1 < k) :
    Nat.unpair (h + 1) = (j + 1, k) := by
  have hp := Nat.pair_eq_of_unpair_eq H
  have e : Nat.pair j k + 1 = Nat.pair (j + 1) k := by
    show (if j < k then k * k + j else j * j + j + k) + 1 =
      if j + 1 < k then k * k + (j + 1) else (j + 1) * (j + 1) + (j + 1) + k
    rw [if_pos (by omega), if_pos hjk]
    omega
  rw [← hp, e, Nat.unpair_pair]

/-- The successor at the column's last pair below the diagonal: `(k - 1, k) ↦ (k, 0)`. -/
private theorem qy_unpair_succ_last {h j k : ℕ} (H : Nat.unpair h = (j, k)) (hjk : j + 1 = k) :
    Nat.unpair (h + 1) = (k, 0) := by
  have hp := Nat.pair_eq_of_unpair_eq H
  have e : Nat.pair j k + 1 = Nat.pair k 0 := by
    show (if j < k then k * k + j else j * j + j + k) + 1 =
      if k < 0 then 0 * 0 + k else k * k + k + 0
    rw [if_pos (by omega), if_neg (by omega)]
    subst hjk
    ring
  rw [← hp, e, Nat.unpair_pair]

/-- The successor on the diagonal: `(j, j) ↦ (0, j + 1)`. -/
private theorem qy_unpair_succ_diag {h j : ℕ} (H : Nat.unpair h = (j, j)) :
    Nat.unpair (h + 1) = (0, j + 1) := by
  have hp := Nat.pair_eq_of_unpair_eq H
  have e : Nat.pair j j + 1 = Nat.pair 0 (j + 1) := by
    show (if j < j then j * j + j else j * j + j + j) + 1 =
      if 0 < j + 1 then (j + 1) * (j + 1) + 0 else 0 * 0 + 0 + (j + 1)
    rw [if_neg (lt_irrefl j), if_pos (Nat.succ_pos j)]
    ring
  rw [← hp, e, Nat.unpair_pair]

/-- The successor above the diagonal: `(j, k) ↦ (j, k + 1)` when `k < j`. -/
private theorem qy_unpair_succ_gt {h j k : ℕ} (H : Nat.unpair h = (j, k)) (hjk : k < j) :
    Nat.unpair (h + 1) = (j, k + 1) := by
  have hp := Nat.pair_eq_of_unpair_eq H
  have e : Nat.pair j k + 1 = Nat.pair j (k + 1) := by
    show (if j < k then k * k + j else j * j + j + k) + 1 =
      if j < k + 1 then (k + 1) * (k + 1) + j else j * j + j + (k + 1)
    rw [if_neg (by omega), if_neg (by omega)]
    ring
  rw [← hp, e, Nat.unpair_pair]

/-! ### The locator's round: banks, anchor and escapes -/

/-- The clock's bank on the call's tapes is the call's bank. -/
private theorem QyKit.bClk_castSucc {f g : ℕ → ℕ} (κ : QyKit f g) (i : Fin κ.cf.k) :
    κ.bClk i.castSucc = κ.bCf i := by
  unfold QyKit.bClk
  rw [Function.Embedding.coeFn_mk, dif_pos (by rw [Fin.coe_castSucc]; exact i.isLt)]
  rfl

/-- The clock's last tape is the counter tape `8`. -/
private theorem QyKit.bClk_last {f g : ℕ → ℕ} (κ : QyKit f g) :
    κ.bClk (Fin.last κ.cf.k) = κ.tp 8 := by
  unfold QyKit.bClk
  rw [Function.Embedding.coeFn_mk, dif_neg (by rw [Fin.val_last]; exact lt_irrefl _)]

/-- `f`'s call bank tapes other than tape `0` are off the named tapes. -/
private theorem QyKit.bCf_ne {f g : ℕ → ℕ} (κ : QyKit f g) (i : Fin κ.cf.k) (hi : (i : ℕ) ≠ 0)
    (c : Fin 16) : κ.bCf i ≠ κ.tp c := qyBank_ne_tp κ _ _ _ _ _ (by omega) i hi c

/-- The fourth power's call bank tapes other than tape `0` are off the named tapes. -/
private theorem QyKit.bPu_ne {f g : ℕ → ℕ} (κ : QyKit f g) (i : Fin κ.pu.k) (hi : (i : ℕ) ≠ 0)
    (c : Fin 16) : κ.bPu i ≠ κ.tp c := qyBank_ne_tp κ _ _ _ _ _ (by omega) i hi c

/-- The counter's increment bank tapes other than tape `0` are off the named tapes. -/
private theorem QyKit.bAb0_ne {f g : ℕ → ℕ} (κ : QyKit f g) (i : Fin κ.ab.k) (hi : (i : ℕ) ≠ 0)
    (c : Fin 16) : κ.bAb0 i ≠ κ.tp c := qyBank_ne_tp κ _ _ _ _ _ (by omega) i hi c

/-- The increment bank of `j`: tapes other than tape `0` are off the named tapes. -/
private theorem QyKit.bAbJ_ne {f g : ℕ → ℕ} (κ : QyKit f g) (i : Fin κ.ab.k) (hi : (i : ℕ) ≠ 0)
    (c : Fin 16) : κ.bAbJ i ≠ κ.tp c := qyBank_ne_tp κ _ _ _ _ _ (by omega) i hi c

/-- The increment bank of `k`: tapes other than tape `0` are off the named tapes. -/
private theorem QyKit.bAbK_ne {f g : ℕ → ℕ} (κ : QyKit f g) (i : Fin κ.ab.k) (hi : (i : ℕ) ≠ 0)
    (c : Fin 16) : κ.bAbK i ≠ κ.tp c := qyBank_ne_tp κ _ _ _ _ _ (by omega) i hi c

/-- The anchor layout's tapes. -/
private def qyLayT {f g : ℕ → ℕ} (κ : QyKit f g) (n a j k : ℕ) : Fin κ.K → ℤ → Option Bool :=
  fun t => FinTM.bufferTape (qyLay κ n a j k t)

/-- The locator's anchor. -/
private def qyAnc {f g : ℕ → ℕ} (κ : QyKit f g) : Σ i, QyLPh κ i := ⟨.anc, SweepPhase.sweep⟩

/-- The locator's escape phases: interior, top and timeout. -/
private def QyLK.isEsc : QyLK → Bool
  | .escI | .escTop | .escTO => true
  | _ => false

/-- The locator's escapes: every state of an escape phase. -/
private def qyLocE {f g : ℕ → ℕ} (κ : QyKit f g) : Set (Option (Σ i, QyLPh κ i)) :=
  {q | ∃ p, q = some p ∧ p.1.isEsc = true}

/-- A state of a phase other than the anchor and the escapes is off the round's stop set. -/
private theorem qy_notStop {f g : ℕ → ℕ} (κ : QyKit f g) (i : QyLK) (hi : i ≠ .anc)
    (he : i.isEsc = false) (s : QyLPh κ i) :
    some (⟨i, s⟩ : Σ i, QyLPh κ i) ∉ roundStop (qyAnc κ) (qyLocE κ) :=
  not_mem_roundStop.mpr ⟨_, rfl, fun h => hi (congrArg Sigma.fst h), fun ⟨p, hp, hpe⟩ => by
    rw [← Option.some.inj hp, he] at hpe
    exact Bool.false_ne_true hpe⟩

/-- An escape phase's sweep state is an endpoint of a round. -/
private theorem qy_esc_mem {f g : ℕ → ℕ} (κ : QyKit f g) (i : QyLK) (he : i.isEsc = true)
    (s : QyLPh κ i) :
    some (⟨i, s⟩ : Σ i, QyLPh κ i) ∈ insert (some (qyAnc κ)) (qyLocE κ) :=
  Set.mem_insert_of_mem _ ⟨_, rfl, he⟩

/-- The tapes a round may leave dirty: the clock's bank (the call's and the counter) and the
round's scratch tapes `3` to `6`. -/
private def qyScratch {f g : ℕ → ℕ} (κ : QyKit f g) (t : Fin κ.K) : Prop :=
  t ∈ Set.range κ.bClk ∨ t = κ.tp 3 ∨ t = κ.tp 4 ∨ t = κ.tp 5 ∨ t = κ.tp 6

/-- **An escape's tapes**: off the round's scratch, the anchor layout, every head at `0`. -/
private def QyEscT {f g : ℕ → ℕ} (κ : QyKit f g) (n a j k : ℕ) (T : Fin κ.K → ℤ → Option Bool)
    (P : Fin κ.K → ℤ) : Prop :=
  ∀ t, ¬ qyScratch κ t → T t = FinTM.bufferTape (qyLay κ n a j k t) ∧ P t = 0

/-- `f`'s call tape is in the clock's bank. -/
private theorem qy_tp7_mem {f g : ℕ → ℕ} (κ : QyKit f g) : κ.tp 7 ∈ Set.range κ.bClk :=
  ⟨(⟨0, κ.cfK⟩ : Fin κ.cf.k).castSucc, by rw [κ.bClk_castSucc]; rfl⟩

/-- The counter tape is in the clock's bank. -/
private theorem qy_tp8_mem {f g : ℕ → ℕ} (κ : QyKit f g) : κ.tp 8 ∈ Set.range κ.bClk :=
  ⟨Fin.last κ.cf.k, κ.bClk_last⟩

/-- Off the scratch means off the named scratch tapes `3` to `8`. -/
private theorem qy_not_scratch {f g : ℕ → ℕ} (κ : QyKit f g) {t : Fin κ.K} (h : ¬ qyScratch κ t) :
    t ≠ κ.tp 3 ∧ t ≠ κ.tp 4 ∧ t ≠ κ.tp 5 ∧ t ≠ κ.tp 6 ∧ t ≠ κ.tp 7 ∧ t ≠ κ.tp 8 :=
  ⟨fun e => h (Or.inr (Or.inl e)), fun e => h (Or.inr (Or.inr (Or.inl e))),
    fun e => h (Or.inr (Or.inr (Or.inr (Or.inl e)))),
    fun e => h (Or.inr (Or.inr (Or.inr (Or.inr e)))),
    fun e => h (Or.inl (e ▸ qy_tp7_mem κ)), fun e => h (Or.inl (e ▸ qy_tp8_mem κ))⟩

/-- **A round from its first step and a segment.** If the run from `c`, at the anchor, reaches
`c₁` in one step, and from `c₁` a segment avoiding the round's stop set reaches `c'`, at the
anchor or an escape, then the run from `c` is a round to `c'`, of one more step. -/
private theorem qy_round_of_seg {K : ℕ} {S : Type} {x : List Bool} {M : MultiTapeTM K Bool S}
    {a : S}
    {E : Set (Option S)} {c c₁ c' : Cfg K Bool S x} {t : ℕ} (hc : c.state = some a)
    (h1 : M.runFrom c 1 = c₁) (hseg : Segment M (roundStop a E) (fun _ => True) c₁ c' t)
    (hend : c'.state ∈ insert (some a) E) : Round M a E (fun _ => True) c c' (1 + t) := by
  obtain ⟨hrun, hcut, -⟩ := (segment_iff _ _ _ _ _ _).mp hseg
  refine (round_iff _ _ _ _ _ _ _).mpr
    ⟨hc, by omega, ?_, hend, fun u hu hut => ?_, fun _ _ => trivial⟩
  · rw [MultiTapeTM.runFrom_add, h1, hrun]
  · obtain ⟨v, rfl⟩ : ∃ v, u = 1 + v := ⟨u - 1, by omega⟩
    rw [MultiTapeTM.runFrom_add, h1]
    exact hcut v (by omega)

/-! ### The locator's round: the clocked call -/

/-- **The round's call** (checkpoint 3): from the anchor layout at the rung `1^a`, `a ≤ n`, the
locator copies the rung onto `f`'s call tape and runs `f`'s witness under the clock. Either the
call returns: `bits (f a)` on tape `7`, a word of the counter's width on tape `8`, at the length
test, within the clock's two bounds; or the counter runs out: then `n < f a`, and the locator is
at its timeout escape with the tapes off the clock's bank untouched.

**Proof sketch.** Two hosted phases: the copy (`qy_copy`) and the clocked call
(`qy_clockHost_finish` or `qy_clockHost_timeout`, split on the call's time against `2 ^ m - 1`),
the call's bank holding the seam of `1^a` (`qy_arg_bank`). The timeout's `n < f a` is
`qy_timeout_cert`. -/
private theorem qy_rnd_call {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (a j k : ℕ)
    (ha : a ≤ x.length) :
    (∃ t ≤ 2 * a + 3 + (5 * (2 ^ κ.m x.length - 1) + 2 * κ.m x.length + 3),
      t ≤ 2 * a + 3 + (5 * (κ.cfA * (κ.cfc * (f a + 1) + a + (Nat.bits (f a)).length + 1)) +
        2 * κ.m x.length + 3) ∧
      ∃ w' : List Bool, w'.length = κ.m x.length ∧
        Segment (qyLoc κ) (roundStop (qyAnc κ) (qyLocE κ)) (fun _ => True)
          (qyC (x := x) ⟨.r1, SweepPhase.sweep⟩ 1 (qyLayT κ x.length a j k) (fun _ => 0) [])
          (qyC ⟨.r3, QyCmp.scan⟩ 1 (Function.update (Function.update (qyLayT κ x.length a j k)
            (κ.tp 7) (FinTM.bufferTape (Nat.bits (f a)))) (κ.tp 8) (FinTM.bufferTape w'))
            (fun _ => 0) []) t) ∨
    (x.length < f a ∧ ∃ t ≤ 2 * a + 3 + (5 * (2 ^ κ.m x.length - 1) + 2 * κ.m x.length + 3),
      ∃ (ip : Fin (x.length + 2)) (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ),
        Segment (qyLoc κ) (roundStop (qyAnc κ) (qyLocE κ)) (fun _ => True)
          (qyC (x := x) ⟨.r1, SweepPhase.sweep⟩ 1 (qyLayT κ x.length a j k) (fun _ => 0) [])
          (qyC ⟨.escTO, SweepPhase.sweep⟩ ip T P []) t ∧
        QyEscT κ x.length a j k T P) := by
  set n := x.length with hnx
  set T₀ := qyLayT κ n a j k with hT₀
  set P₀ : Fin κ.K → ℤ := fun _ => 0 with hP₀
  unfold qyLoc
  -- r1: the rung onto f's call tape
  have c1 := qy_copy (x := x) (κ.tp 2) (κ.tp 7) (κ.tp_ne (by decide)) (fun b => b) 1 T₀ P₀ []
    (List.replicate a true) [] (by simp [hT₀, qyLayT, qyLay, QyKit.tp_inj]) rfl
    (by simp [hT₀, qyLayT, qyLay, QyKit.tp_inj]) (by simp [hP₀])
  rw [List.nil_append, List.map_id'] at c1
  set T₁ := Function.update T₀ (κ.tp 7) (FinTM.bufferTape (List.replicate a true)) with hT₁
  have seg1 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r1 .sweep .done
    ⟨.clk, κ.inj (Sum.inl ())⟩ 1 1 T₀ T₁ P₀ P₀ [] [] _ c1.1 (by simp [qyLocRed])
    (qy_guard_of_cut SweepPhase.done (qyLocRed κ .r1) (fun s hs => by simp [qyLocRed, hs]) c1.2)
    _ (qy_notStop κ .r1 (by decide) rfl)
  -- clk: the clocked call of f's witness on 1^a
  obtain ⟨tc, htc, hposc, hcutc, hrunc⟩ := κ.cfS x (List.replicate a true)
  simp only [List.length_replicate] at htc hrunc
  have hb0 : κ.bCf ⟨0, κ.cfK⟩ = κ.tp 7 := rfl
  have hbank : ∀ i, T₁ (κ.bCf i) = FinTM.bufferTape (stateWord κ.cf.k (List.replicate a true) i) :=
    qy_arg_bank κ.bCf κ.cfK T₁ _ (by rw [hb0]; simp [hT₁])
      (fun i hi => by simp [hT₁, hT₀, qyLayT, qyLay, κ.bCf_ne i hi])
  have hTc : T₁ (κ.tp 8) = FinTM.bufferTape (List.replicate (κ.m n) true) := by
    simp [hT₁, hT₀, qyLayT, qyLay, QyKit.tp_inj]
  have hcall := qy_call_bound f κ.cfc κ.cfA a n ha
  by_cases hlate : tc ≤ 2 ^ κ.m n - 1
  · -- the call returns in time
    obtain ⟨T1, hT1, w', hw', hrun, hcut⟩ := qy_clockHost_finish κ.cf κ.cfK κ.cfE κ.cfX κ.H κ.inj
      κ.fsh κ.tmo κ.hH κ.bClk κ.bCf (κ.tp 8) κ.bClk_castSucc κ.bClk_last
      (List.replicate a true) _ tc hposc hcutc hrunc (κ.m n) hlate T₁ P₀ [] hbank
      (fun _ => rfl) hTc rfl
    have hT2 : Function.update (Function.update T₁ (κ.bCf ⟨0, κ.cfK⟩)
        (FinTM.bufferTape (Nat.bits (f a)))) (κ.tp 8) (FinTM.bufferTape w') =
        Function.update (Function.update T₀ (κ.tp 7) (FinTM.bufferTape (Nat.bits (f a))))
          (κ.tp 8) (FinTM.bufferTape w') := by
      rw [hb0, hT₁, Function.update_idem]
    rw [hT2] at hrun
    have seg2 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .clk
      (κ.inj (Sum.inl ())) (κ.fsh (some (Sum.inr κ.cfX))) ⟨.r3, QyCmp.scan⟩ 1 1 T₁ _ P₀ P₀ [] []
      T1 hrun (by simp only [qyLocRed]; rw [if_pos ⟨_, rfl⟩])
      (fun u hu s hs => by
        have h1 : ¬ ∃ r, s = κ.fsh r := fun ⟨r, hr⟩ => (hcut u hu r).1 (hr ▸ hs)
        have h2 : ¬ ∃ r, s = κ.tmo r := fun ⟨r, hr⟩ => (hcut u hu r).2 (hr ▸ hs)
        simp only [qyLocRed]
        rw [if_neg h1, if_neg h2])
      _ (qy_notStop κ .clk (by decide) rfl)
    have e1 : 2 ^ κ.m x.length = 2 ^ κ.m n := rfl
    have e2 : κ.m x.length = κ.m n := rfl
    have e3 : (List.replicate a true).length = a := List.length_replicate
    refine Or.inl ⟨_, ?_, ?_, w', hw', seg1.trans seg2⟩
    · omega
    · omega
  · -- the counter runs out
    obtain ⟨T1, hT1, r, ip', T', P', hrun, hkeep, hcut⟩ := qy_clockHost_timeout κ.cf κ.cfE κ.cfX
      κ.H κ.inj κ.fsh κ.tmo κ.hH κ.bClk κ.bCf (κ.tp 8) κ.bClk_castSucc κ.bClk_last
      (List.replicate a true) _ tc hposc hcutc hrunc (κ.m n) (by omega) T₁ P₀ [] hbank
      (fun _ => rfl) hTc rfl
    have seg2 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .clk
      (κ.inj (Sum.inl ())) (κ.tmo r) ⟨.escTO, SweepPhase.sweep⟩ 1 ip' T₁ T' P₀ P' [] []
      T1 hrun
      (by
        simp only [qyLocRed]
        rw [if_neg (fun ⟨r', h⟩ => κ.hft r' r h.symm), if_pos ⟨r, rfl⟩])
      (fun u hu s hs => by
        have h1 : ¬ ∃ r, s = κ.fsh r := fun ⟨r, hr⟩ => (hcut u hu r).1 (hr ▸ hs)
        have h2 : ¬ ∃ r, s = κ.tmo r := fun ⟨r, hr⟩ => (hcut u hu r).2 (hr ▸ hs)
        simp only [qyLocRed]
        rw [if_neg h1, if_neg h2])
      _ (qy_notStop κ .clk (by decide) rfl)
    have e1 : 2 ^ κ.m x.length = 2 ^ κ.m n := rfl
    have e2 : κ.m x.length = κ.m n := rfl
    have e3 : (List.replicate a true).length = a := List.length_replicate
    refine Or.inr ⟨?_, _, by omega, ip', T', P', seg1.trans seg2, fun t ht => ?_⟩
    · have hm : κ.m n = (Nat.bits n).length + (Nat.bits (κ.cfA * (κ.cfc + 2))).length := by
        unfold QyKit.m
        omega
      exact qy_timeout_cert f κ.cfc κ.cfA a n tc ha htc (by rw [← hm]; omega)
    · obtain ⟨h3, h4, h5, h6, h7, h8⟩ := qy_not_scratch κ ht
      obtain ⟨e1, e2⟩ := hkeep t (fun hm => ht (Or.inl hm))
      rw [e1, e2, hT₁, Function.update_of_ne h7]
      exact ⟨rfl, rfl⟩

/-! ### The locator's round: the tests -/

/-- The tapes after the round's call: `bits F` on `f`'s call tape `7` and the counter's word `w'`
on tape `8`, over the anchor layout. -/
private def qyTA {f g : ℕ → ℕ} (κ : QyKit f g) (n a j k F : ℕ) (w' : List Bool) :
    Fin κ.K → ℤ → Option Bool :=
  Function.update (Function.update (qyLayT κ n a j k) (κ.tp 7) (FinTM.bufferTape (Nat.bits F)))
    (κ.tp 8) (FinTM.bufferTape w')

/-- The tapes after a passed round's tests: `1^{F + a}` on tape `4`, the expanded counter on
tape `7`, `1^{X⁴}` and `1^{X⁴ + 1}` on tapes `5` and `6`, and the next rung `1^{ℓ' + 1}` on
tape `3`. -/
private def qyTB {f g : ℕ → ℕ} (κ : QyKit f g) (T : Fin κ.K → ℤ → Option Bool) (F a X4 ℓ' : ℕ) :
    Fin κ.K → ℤ → Option Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update T
    (κ.tp 4) (FinTM.bufferTape (List.replicate (F + a) true)))
    (κ.tp 7) (FinTM.bufferTape (List.replicate (Nat.bits F).length true)))
    (κ.tp 5) (FinTM.bufferTape (List.replicate X4 true)))
    (κ.tp 6) (FinTM.bufferTape (List.replicate (X4 + 1) true)))
    (κ.tp 3) (FinTM.bufferTape (List.replicate (ℓ' + 1) true))

/-- The tests' time bound when the round stops: linear in `n`, plus the fourth power's call on a
word shorter than `|bits n|`. -/
private def qyTestS {f g : ℕ → ℕ} (κ : QyKit f g) (n a : ℕ) : ℕ :=
  40 * (n + 1) + 4 * a + 16 * (Nat.bits n).length + κ.puA * (Nat.bits n).length ^ 5 +
    κ.abA * ((Nat.bits n).length + 1) + 60

/-- The tests' time bound when the round passes: the next rung, plus polylogarithmic terms. -/
private def qyTestP {f g : ℕ → ℕ} (κ : QyKit f g) (n ℓ' : ℕ) : ℕ :=
  9 * ℓ' + 25 * (Nat.bits n).length + κ.puA * (Nat.bits n).length ^ 5 +
    κ.abA * ((Nat.bits n).length + 1) + 50

/-- **The round's tests** (checkpoint 3): from the length test after a returned call (`bits F`,
`F = f a`, on tape `7`), with `X = F + a + 1` and the next rung `ℓ' = 2 ^ X⁴`, the locator ends
at its interior escape if `n < ℓ'`, at its top escape if `ℓ' = n` (with `1^{X - 1}` on tape `4`
for the budget), and otherwise at the cleanup with the tapes `qyTB`, `X < |bits n|` and
`X⁴ < |bits n|`.

**Proof sketch.** Fourteen hosted phases (`qy_hosted`), each a row's run: `|bits F|` against
`|bits n|` (L2, `qy_cmp_run`; longer gives `F > n`); `F` expanded to `1^F` (`qy_expandHost`, the
counter worth `F`), `1^a` appended, the rewind; `X - 1` against `|bits n|` (not shorter gives
`ℓ' ≥ 2 ^ |bits n| > n`); the copy and the fourth power's call (`qy_callHost`); `X⁴` against
`|bits n|`; the copy as `0^{X⁴}`, the increment's call to `0^{X⁴} 1` (worth `ℓ'`,
`qy_rung_val`), its expansion to `1^{ℓ'}` (at most `n` cells, since `X⁴ ≤ log₂ n`), one more
cell and the rewind; `ℓ' + 1` against `n + 1`. The tapes off the scratch keep the layout; the
times are summed with `Turing.counterOverhead_le`. -/
private theorem qy_rnd_tests {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (a j k : ℕ)
    (w' : List Bool) :
    (x.length < 2 ^ (f a + a + 1) ^ 4 ∧ ∃ t ≤ qyTestS κ x.length a,
      ∃ (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ),
        Segment (qyLoc κ) (roundStop (qyAnc κ) (qyLocE κ)) (fun _ => True)
          (qyC (x := x) ⟨.r3, QyCmp.scan⟩ 1 (qyTA κ x.length a j k (f a) w') (fun _ => 0) [])
          (qyC ⟨.escI, SweepPhase.sweep⟩ 1 T P []) t ∧ QyEscT κ x.length a j k T P) ∨
    (2 ^ (f a + a + 1) ^ 4 = x.length ∧ ∃ t ≤ qyTestS κ x.length a,
      ∃ (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ),
        Segment (qyLoc κ) (roundStop (qyAnc κ) (qyLocE κ)) (fun _ => True)
          (qyC (x := x) ⟨.r3, QyCmp.scan⟩ 1 (qyTA κ x.length a j k (f a) w') (fun _ => 0) [])
          (qyC ⟨.escTop, SweepPhase.sweep⟩ 1 T P []) t ∧ QyEscT κ x.length a j k T P ∧
        T (κ.tp 4) = FinTM.bufferTape (List.replicate (f a + a) true) ∧ P (κ.tp 4) = 0) ∨
    (2 ^ (f a + a + 1) ^ 4 < x.length ∧ f a + a + 1 ≤ (Nat.bits x.length).length ∧
      (f a + a + 1) ^ 4 < (Nat.bits x.length).length ∧
      ∃ t ≤ qyTestP κ x.length (2 ^ (f a + a + 1) ^ 4),
        Segment (qyLoc κ) (roundStop (qyAnc κ) (qyLocE κ)) (fun _ => True)
          (qyC (x := x) ⟨.r3, QyCmp.scan⟩ 1 (qyTA κ x.length a j k (f a) w') (fun _ => 0) [])
          (qyC ⟨.c1, SweepPhase.sweep⟩ 1 (qyTB κ (qyTA κ x.length a j k (f a) w') (f a) a
            ((f a + a + 1) ^ 4) (2 ^ (f a + a + 1) ^ 4)) (fun _ => 0) []) t) := by
  simp only [qyTestS, qyTestP]
  set n := x.length with hnx
  set F := f a with hF
  set Lb := (Nat.bits n).length with hLb
  set X4 := (F + a + 1) ^ 4 with hX4
  set ℓ' := 2 ^ X4 with hℓ'
  set T₀ := qyLayT κ n a j k with hT₀
  set P₀ : Fin κ.K → ℤ := fun _ => 0 with hP₀
  set TA := qyTA κ n a j k F w' with hTA
  unfold qyLoc
  have hX : F + a + 1 ≤ X4 := Nat.le_self_pow (by norm_num) _
  have hnLb : n < 2 ^ Lb := qy_lt_two_pow_bits n
  have hesc : ∀ T : Fin κ.K → ℤ → Option Bool, (∀ t, t ≠ κ.tp 3 → t ≠ κ.tp 4 → t ≠ κ.tp 5 →
      t ≠ κ.tp 6 → t ≠ κ.tp 7 → t ≠ κ.tp 8 → T t = T₀ t) → QyEscT κ n a j k T P₀ :=
    fun T hT t ht => by
      obtain ⟨h3, h4, h5, h6, h7, h8⟩ := qy_not_scratch κ ht
      exact ⟨hT t h3 h4 h5 h6 h7 h8, rfl⟩
  -- r3: |bits F| against |bits n|
  have c3 := qy_cmp_run (x := x) (κ.tp 7) (κ.tp 1) (κ.tp_ne (by decide)) 1 TA P₀ []
    (Nat.bits F) (List.replicate Lb true) (by simp [hTA, qyTA, QyKit.tp_inj])
    (by simp [hTA, qyTA, qyLayT, qyLay, QyKit.tp_inj, hLb]) rfl rfl
  rw [List.length_replicate] at c3
  have hg3 : ∀ u < 2 * min (Nat.bits F).length Lb + 2, ∀ s,
      ((qyLocM κ .r3).runFrom (qyC QyCmp.scan 1 TA P₀ []) u).state = some s →
        qyLocRed κ .r3 s = none := fun u hu s hs => by
    cases s with
    | done w => exact absurd hs (c3.2 u hu w)
    | _ => simp [qyLocRed]
  have hm3 := min_le_right (Nat.bits F).length Lb
  by_cases hgt : compare (Nat.bits F).length Lb = .gt
  · -- interior: |bits F| > |bits n| gives F > n
    rw [hgt] at c3
    have seg3 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r3 .scan (.done .gt)
      ⟨.escI, SweepPhase.sweep⟩ 1 1 TA TA P₀ P₀ [] [] _ c3.1 (by simp [qyLocRed]) hg3 _
      (qy_notStop κ .r3 (by decide) rfl)
    refine Or.inl ⟨?_, _, by omega, TA, P₀, seg3, hesc TA fun t _ _ _ _ h7 h8 => by
      simp [hTA, qyTA, hT₀, Function.update_of_ne h7, Function.update_of_ne h8]⟩
    have hFn : n < F := by
      by_contra hc
      exact absurd (compare_gt_iff_gt.mp hgt) (not_lt.mpr (qy_bits_len_mono (not_lt.mp hc)))
    have := Nat.lt_two_pow_self (n := X4)
    omega
  have hFL : (Nat.bits F).length ≤ Lb := not_lt.mp fun h => hgt (compare_gt_iff_gt.mpr h)
  have hF2 : F ≤ 2 * n := by
    have h1 := qy_lt_two_pow_bits F
    have h2 : 2 ^ (Nat.bits F).length ≤ 2 ^ (Nat.bits n).length :=
      Nat.pow_le_pow_right (by norm_num) hFL
    have h3 := qy_two_pow_bits_le n
    omega
  have seg3 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r3 .scan
    (.done (compare (Nat.bits F).length Lb)) ⟨.r4, CounterLoopState.dec .run⟩ 1 1 TA TA P₀ P₀ []
    [] _ c3.1 (by simp [qyLocRed, hgt]) hg3 _ (qy_notStop κ .r3 (by decide) rfl)
  -- r4: F in unary on tape 4, from the counter bits F on tape 7
  have c4 := qy_expandHost (x := x) (qyEmb2 (κ.tp 4) (κ.tp 7) (κ.tp_ne (by decide))) (κ.tp 4)
    (κ.tp 7) rfl rfl 1 TA P₀ [] [] (Nat.bits F) F (qy_bits_val F)
    (by simp [hTA, qyTA, qyLayT, qyLay, QyKit.tp_inj]) (by simp [hP₀])
    (by simp [hTA, qyTA, QyKit.tp_inj]) (by simp [hP₀])
  rw [List.nil_append] at c4
  set T4 := Function.update (Function.update TA (κ.tp 4)
    (FinTM.bufferTape (List.replicate F true))) (κ.tp 7)
    (FinTM.bufferTape (List.replicate (Nat.bits F).length true)) with hT4
  set P4 := Function.update P₀ (κ.tp 4) ((([] : List Bool).length : ℤ) + F) with hP4
  have seg4 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r4 (.dec .run) .done
    ⟨.r5, SweepPhase.sweep⟩ 1 1 TA T4 P₀ P4 [] [] _ c4.1 (by simp [qyLocRed])
    (qy_guard_of_cut CounterLoopState.done (qyLocRed κ .r4) (fun s hs => by simp [qyLocRed, hs])
      c4.2) _ (qy_notStop κ .r4 (by decide) rfl)
  have hco4 := counterOverhead_le (Nat.bits F)
  rw [qy_bits_val] at hco4
  have hbF := length_bits_le_self F
  -- r5: 1^a appended to tape 4
  have c5 := qy_copy (x := x) (κ.tp 2) (κ.tp 4) (κ.tp_ne (by decide)) (fun b => b) 1 T4 P4 []
    (List.replicate a true) (List.replicate F true)
    (by simp [hT4, hTA, qyTA, qyLayT, qyLay, QyKit.tp_inj])
    (by simp [hP4, hP₀, QyKit.tp_inj]) (by simp [hT4, QyKit.tp_inj]) (by simp [hP4])
  rw [List.map_id', List.replicate_append_replicate] at c5
  set T5 := Function.update T4 (κ.tp 4) (FinTM.bufferTape (List.replicate (F + a) true))
    with hT5
  have seg5 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r5 .sweep .done
    ⟨.r6, RewindPhase.start⟩ 1 1 T4 T5 P4 P4 [] [] _ c5.1 (by simp [qyLocRed])
    (qy_guard_of_cut SweepPhase.done (qyLocRed κ .r5) (fun s hs => by simp [qyLocRed, hs]) c5.2)
    _ (qy_notStop κ .r5 (by decide) rfl)
  -- r6: rewind tape 4
  have c6 := qy_rewind (x := x) (κ.tp 4) 1 T5 P4 [] (List.replicate (F + a) true) F
    (by simp) (by simp [hT5]) (by simp [hP4])
  have hP6 : Function.update P4 (κ.tp 4) 0 = P₀ := by
    rw [hP4, Function.update_idem]
    exact Function.update_eq_self_iff.mpr rfl
  rw [hP6] at c6
  have seg6 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r6 .start .done
    ⟨.r7, QyCmp.scan⟩ 1 1 T5 T5 P4 P₀ [] [] _ c6.1 (by simp [qyLocRed])
    (qy_guard_of_cut RewindPhase.done (qyLocRed κ .r6) (fun s hs => by simp [qyLocRed, hs]) c6.2)
    _ (qy_notStop κ .r6 (by decide) rfl)
  -- r7: X - 1 = F + a against |bits n|
  have c7 := qy_cmp_run (x := x) (κ.tp 4) (κ.tp 1) (κ.tp_ne (by decide)) 1 T5 P₀ []
    (List.replicate (F + a) true) (List.replicate Lb true) (by simp [hT5])
    (by simp [hT5, hT4, hTA, qyTA, qyLayT, qyLay, QyKit.tp_inj, hLb]) rfl rfl
  rw [List.length_replicate, List.length_replicate] at c7
  have hg7 : ∀ u < 2 * min (F + a) Lb + 2, ∀ s,
      ((qyLocM κ .r7).runFrom (qyC QyCmp.scan 1 T5 P₀ []) u).state = some s →
        qyLocRed κ .r7 s = none := fun u hu s hs => by
    cases s with
    | done w => exact absurd hs (c7.2 u hu w)
    | _ => simp [qyLocRed]
  have hm7 := min_le_right (F + a) Lb
  have hT5esc : ∀ t, t ≠ κ.tp 3 → t ≠ κ.tp 4 → t ≠ κ.tp 5 → t ≠ κ.tp 6 → t ≠ κ.tp 7 →
      t ≠ κ.tp 8 → T5 t = T₀ t := fun t _ h4 _ _ h7 h8 => by
    simp [hT5, hT4, hTA, qyTA, hT₀, Function.update_of_ne h4, Function.update_of_ne h7,
      Function.update_of_ne h8]
  by_cases hlt7 : compare (F + a) Lb = .lt
  swap
  · -- interior: X - 1 ≥ |bits n|
    have seg7 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r7 .scan
      (.done (compare (F + a) Lb)) ⟨.escI, SweepPhase.sweep⟩ 1 1 T5 T5 P₀ P₀ [] [] _ c7.1
      (by simp [qyLocRed, hlt7]) hg7 _ (qy_notStop κ .r7 (by decide) rfl)
    have hge : Lb ≤ F + a := not_lt.mp fun h => hlt7 (compare_lt_iff_lt.mpr h)
    refine Or.inl ⟨?_, _, ?_, T5, P₀,
      seg3.trans (seg4.trans (seg5.trans (seg6.trans seg7))), hesc T5 hT5esc⟩
    · have : 2 ^ Lb ≤ 2 ^ X4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · simp only [List.length_replicate] at *
      omega
  have hlt7' : F + a < Lb := compare_lt_iff_lt.mp hlt7
  have seg7 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r7 .scan
    (.done (compare (F + a) Lb)) ⟨.r8, SweepPhase.sweep⟩ 1 1 T5 T5 P₀ P₀ [] [] _ c7.1
    (by simp [qyLocRed, hlt7]) hg7 _ (qy_notStop κ .r7 (by decide) rfl)
  -- r8: the copy 1^{F + a} onto the fourth power's tape 5
  have c8 := qy_copy (x := x) (κ.tp 4) (κ.tp 5) (κ.tp_ne (by decide)) (fun b => b) 1 T5 P₀ []
    (List.replicate (F + a) true) [] (by simp [hT5]) rfl
    (by simp [hT5, hT4, hTA, qyTA, qyLayT, qyLay, QyKit.tp_inj]) (by simp [hP₀])
  rw [List.map_id', List.nil_append] at c8
  set T8 := Function.update T5 (κ.tp 5) (FinTM.bufferTape (List.replicate (F + a) true))
    with hT8
  have seg8 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r8 .sweep .done
    ⟨.pu, Sum.inl ()⟩ 1 1 T5 T8 P₀ P₀ [] [] _ c8.1 (by simp [qyLocRed])
    (qy_guard_of_cut SweepPhase.done (qyLocRed κ .r8) (fun s hs => by simp [qyLocRed, hs]) c8.2)
    _ (qy_notStop κ .r8 (by decide) rfl)
  -- pu: the fourth power 1^{X⁴}
  obtain ⟨tq, htq, hposq, hcutq, hrunq⟩ := κ.puS x (List.replicate (F + a) true)
  simp only [List.length_replicate] at htq hrunq
  have hb5 : κ.bPu ⟨0, κ.puK⟩ = κ.tp 5 := rfl
  have c9 := qy_callHost κ.pu κ.puK κ.bPu κ.puE κ.puX (List.replicate (F + a) true) _ tq hposq
    hcutq hrunq T8 P₀ []
    (qy_arg_bank κ.bPu κ.puK T8 _ (by rw [hb5]; simp [hT8])
      (fun i hi => by
        simp [hT8, hT5, hT4, hTA, qyTA, qyLayT, qyLay, κ.bPu_ne i hi]))
    (fun _ => rfl)
  rw [hb5] at c9
  set T9 := Function.update T8 (κ.tp 5) (FinTM.bufferTape (List.replicate X4 true)) with hT9
  have seg9 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .pu (Sum.inl ())
    (Sum.inr κ.puX) ⟨.r10, QyCmp.scan⟩ 1 1 T8 T9 P₀ P₀ [] [] tq c9.1 (by simp [qyLocRed])
    (qy_guard_of_cut (Sum.inr κ.puX) (qyLocRed κ .pu) (fun s hs => by simp [qyLocRed, hs]) c9.2)
    _ (qy_notStop κ .pu (by decide) rfl)
  have hpu5 : κ.puA * (F + a + 1) ^ 5 ≤ κ.puA * Lb ^ 5 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 5)
  -- r10: X⁴ against |bits n|
  have c10 := qy_cmp_run (x := x) (κ.tp 5) (κ.tp 1) (κ.tp_ne (by decide)) 1 T9 P₀ []
    (List.replicate X4 true) (List.replicate Lb true) (by simp [hT9])
    (by simp [hT9, hT8, hT5, hT4, hTA, qyTA, qyLayT, qyLay, QyKit.tp_inj, hLb]) rfl rfl
  rw [List.length_replicate, List.length_replicate] at c10
  have hg10 : ∀ u < 2 * min X4 Lb + 2, ∀ s,
      ((qyLocM κ .r10).runFrom (qyC QyCmp.scan 1 T9 P₀ []) u).state = some s →
        qyLocRed κ .r10 s = none := fun u hu s hs => by
    cases s with
    | done w => exact absurd hs (c10.2 u hu w)
    | _ => simp [qyLocRed]
  have hm10 := min_le_right X4 Lb
  have hT9esc : ∀ t, t ≠ κ.tp 3 → t ≠ κ.tp 4 → t ≠ κ.tp 5 → t ≠ κ.tp 6 → t ≠ κ.tp 7 →
      t ≠ κ.tp 8 → T9 t = T₀ t := fun t h3 h4 h5 h6 h7 h8 => by
    rw [hT9, Function.update_of_ne h5, hT8, Function.update_of_ne h5]
    exact hT5esc t h3 h4 h5 h6 h7 h8
  by_cases hlt10 : compare X4 Lb = .lt
  swap
  · -- interior: X⁴ ≥ |bits n|
    have seg10 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r10 .scan
      (.done (compare X4 Lb)) ⟨.escI, SweepPhase.sweep⟩ 1 1 T9 T9 P₀ P₀ [] [] _ c10.1
      (by simp [qyLocRed, hlt10]) hg10 _ (qy_notStop κ .r10 (by decide) rfl)
    have hge : Lb ≤ X4 := not_lt.mp fun h => hlt10 (compare_lt_iff_lt.mpr h)
    refine Or.inl ⟨?_, _, ?_, T9, P₀, seg3.trans (seg4.trans (seg5.trans (seg6.trans
      (seg7.trans (seg8.trans (seg9.trans seg10)))))), hesc T9 hT9esc⟩
    · have : 2 ^ Lb ≤ 2 ^ X4 := Nat.pow_le_pow_right (by norm_num) hge
      omega
    · simp only [List.length_replicate] at *
      omega
  have hlt10' : X4 < Lb := compare_lt_iff_lt.mp hlt10
  have hℓn : ℓ' ≤ n := by
    have hn0 : n ≠ 0 := by
      rintro h0
      rw [h0, Nat.zero_bits, List.length_nil] at hLb
      omega
    have h1 := qy_log_bits (Nat.pos_of_ne_zero hn0)
    have h2 := Nat.pow_log_le_self 2 hn0
    have h3 : 2 ^ X4 ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have seg10 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r10 .scan
    (.done (compare X4 Lb)) ⟨.r11, SweepPhase.sweep⟩ 1 1 T9 T9 P₀ P₀ [] [] _ c10.1
    (by simp [qyLocRed, hlt10]) hg10 _ (qy_notStop κ .r10 (by decide) rfl)
  -- r11: the copy 0^{X⁴} onto the counter tape 6
  have c11 := qy_copy (x := x) (κ.tp 5) (κ.tp 6) (κ.tp_ne (by decide)) (fun _ => false) 1 T9 P₀
    [] (List.replicate X4 true) [] (by simp [hT9]) rfl
    (by simp [hT9, hT8, hT5, hT4, hTA, qyTA, qyLayT, qyLay, QyKit.tp_inj]) (by simp [hP₀])
  rw [List.map_replicate, List.nil_append] at c11
  set T11 := Function.update T9 (κ.tp 6) (FinTM.bufferTape (List.replicate X4 false)) with hT11
  have seg11 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r11 .sweep .done
    ⟨.ab, Sum.inl ()⟩ 1 1 T9 T11 P₀ P₀ [] [] _ c11.1 (by simp [qyLocRed])
    (qy_guard_of_cut SweepPhase.done (qyLocRed κ .r11) (fun s hs => by simp [qyLocRed, hs])
      c11.2) _ (qy_notStop κ .r11 (by decide) rfl)
  -- ab: the increment to 0^{X⁴} 1, worth ℓ'
  obtain ⟨tb, htb, hposb, hcutb, hrunb⟩ := κ.abS x (List.replicate X4 false)
  simp only [List.length_replicate] at htb
  have hb6 : κ.bAb0 ⟨0, κ.abK⟩ = κ.tp 6 := rfl
  have c12 := qy_callHost κ.ab κ.abK κ.bAb0 κ.abE κ.abX (List.replicate X4 false) _ tb hposb
    hcutb hrunb T11 P₀ []
    (qy_arg_bank κ.bAb0 κ.abK T11 _ (by rw [hb6]; simp [hT11])
      (fun i hi => by
        simp [hT11, hT9, hT8, hT5, hT4, hTA, qyTA, qyLayT, qyLay, κ.bAb0_ne i hi]))
    (fun _ => rfl)
  rw [hb6] at c12
  set T12 := Function.update T11 (κ.tp 6) (FinTM.bufferTape (List.replicate X4 false ++ [true]))
    with hT12
  have seg12 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .ab (Sum.inl ())
    (Sum.inr κ.abX) ⟨.r13, CounterLoopState.dec .run⟩ 1 1 T11 T12 P₀ P₀ [] [] tb c12.1
    (by simp [qyLocRed])
    (qy_guard_of_cut (Sum.inr κ.abX) (qyLocRed κ .ab) (fun s hs => by simp [qyLocRed, hs])
      c12.2) _ (qy_notStop κ .ab (by decide) rfl)
  -- r13: the next rung 1^{ℓ'} on tape 3
  have c13 := qy_expandHost (x := x) (qyEmb2 (κ.tp 3) (κ.tp 6) (κ.tp_ne (by decide))) (κ.tp 3)
    (κ.tp 6) rfl rfl 1 T12 P₀ [] [] (List.replicate X4 false ++ [true]) ℓ' (qy_rung_val X4)
    (by simp [hT12, hT11, hT9, hT8, hT5, hT4, hTA, qyTA, qyLayT, qyLay, QyKit.tp_inj])
    (by simp [hP₀]) (by simp [hT12]) (by simp [hP₀])
  rw [List.nil_append] at c13
  set T13 := Function.update (Function.update T12 (κ.tp 3)
    (FinTM.bufferTape (List.replicate ℓ' true))) (κ.tp 6)
    (FinTM.bufferTape (List.replicate (List.replicate X4 false ++ [true]).length true)) with hT13
  set P13 := Function.update P₀ (κ.tp 3) ((([] : List Bool).length : ℤ) + ℓ') with hP13
  have seg13 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r13 (.dec .run)
    .done ⟨.r14, WritePhase.wr 0⟩ 1 1 T12 T13 P₀ P13 [] [] _ c13.1 (by simp [qyLocRed])
    (qy_guard_of_cut CounterLoopState.done (qyLocRed κ .r13) (fun s hs => by simp [qyLocRed, hs])
      c13.2) _ (qy_notStop κ .r13 (by decide) rfl)
  have hco13 : counterOverhead (List.replicate X4 false ++ [true]) (ℓ' + 1) ≤
      4 * ℓ' + 2 * (List.replicate X4 false ++ [true]).length + 2 := by
    have h := counterOverhead_le (List.replicate X4 false ++ [true])
    rwa [qy_rung_val] at h
  -- r14: one more cell
  have c14 := qy_writeConst (x := x) (κ.tp 3) [true] 1 T13 P13 [] (List.replicate ℓ' true)
    (by simp [hT13, QyKit.tp_inj]) (by simp [hP13])
  set T14 := Function.update T13 (κ.tp 3) (FinTM.bufferTape (List.replicate ℓ' true ++ [true]))
    with hT14
  have seg14 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r14 (.wr 0) .done
    ⟨.r15, RewindPhase.start⟩ 1 1 T13 T14 P13 P13 [] [] _ c14.1 (by simp [qyLocRed])
    (qy_guard_of_cut WritePhase.done (qyLocRed κ .r14) (fun s hs => by simp [qyLocRed, hs])
      c14.2) _ (qy_notStop κ .r14 (by decide) rfl)
  -- r15: rewind tape 3
  have c15 := qy_rewind (x := x) (κ.tp 3) 1 T14 P13 [] (List.replicate ℓ' true ++ [true]) ℓ'
    (by simp) (by simp [hT14]) (by simp [hP13])
  have hP15 : Function.update P13 (κ.tp 3) 0 = P₀ := by
    rw [hP13, Function.update_idem]
    exact Function.update_eq_self_iff.mpr rfl
  rw [hP15] at c15
  have seg15 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r15 .start .done
    ⟨.r16, QyCmp.scan⟩ 1 1 T14 T14 P13 P₀ [] [] _ c15.1 (by simp [qyLocRed])
    (qy_guard_of_cut RewindPhase.done (qyLocRed κ .r15) (fun s hs => by simp [qyLocRed, hs])
      c15.2) _ (qy_notStop κ .r15 (by decide) rfl)
  -- r16: ℓ' + 1 against n + 1
  have c16 := qy_cmp_run (x := x) (κ.tp 3) (κ.tp 0) (κ.tp_ne (by decide)) 1 T14 P₀ []
    (List.replicate ℓ' true ++ [true]) (List.replicate (n + 1) true) (by simp [hT14])
    (by simp [hT14, hT13, hT12, hT11, hT9, hT8, hT5, hT4, hTA, qyTA, qyLayT, qyLay,
      QyKit.tp_inj]) rfl rfl
  have hl16 : (List.replicate ℓ' true ++ [true]).length = ℓ' + 1 := by simp
  rw [hl16, List.length_replicate] at c16
  have hg16 : ∀ u < 2 * min (ℓ' + 1) (n + 1) + 2, ∀ s,
      ((qyLocM κ .r16).runFrom (qyC QyCmp.scan 1 T14 P₀ []) u).state = some s →
        qyLocRed κ .r16 s = none := fun u hu s hs => by
    cases s with
    | done w => exact absurd hs (c16.2 u hu w)
    | _ => simp [qyLocRed]
  have hm16 := min_le_left (ℓ' + 1) (n + 1)
  have hT14esc : ∀ t, t ≠ κ.tp 3 → t ≠ κ.tp 4 → t ≠ κ.tp 5 → t ≠ κ.tp 6 → t ≠ κ.tp 7 →
      t ≠ κ.tp 8 → T14 t = T₀ t := fun t h3 h4 h5 h6 h7 h8 => by
    rw [hT14, Function.update_of_ne h3, hT13, Function.update_of_ne h6, Function.update_of_ne h3,
      hT12, Function.update_of_ne h6, hT11, Function.update_of_ne h6]
    exact hT9esc t h3 h4 h5 h6 h7 h8
  have hl12 : (List.replicate X4 false ++ [true]).length = X4 + 1 := by simp
  have htb' : tb ≤ κ.abA * (X4 + 1) := htb
  have hab : κ.abA * (X4 + 1) ≤ κ.abA * (Lb + 1) := Nat.mul_le_mul_left _ (by omega)
  have hl5 : (List.replicate (F + a) true).length = F + a := List.length_replicate
  have hla : (List.replicate a true).length = a := List.length_replicate
  have hlX : (List.replicate X4 true).length = X4 := List.length_replicate
  have hlF : (List.replicate F true).length = F := List.length_replicate
  rcases Nat.lt_or_ge ℓ' n with hlt | hge
  · -- next: ℓ' < n
    have hv : compare (ℓ' + 1) (n + 1) = .lt := compare_lt_iff_lt.mpr (by omega)
    have seg16 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r16 .scan
      (.done (compare (ℓ' + 1) (n + 1))) ⟨.c1, SweepPhase.sweep⟩ 1 1 T14 T14 P₀ P₀ [] [] _ c16.1
      (by simp [qyLocRed, hv]) hg16 _ (qy_notStop κ .r16 (by decide) rfl)
    have hend : T14 = qyTB κ TA F a X4 ℓ' := by
      funext t
      by_cases h3 : t = κ.tp 3
      · subst h3
        simp [hT14, qyTB, List.replicate_succ']
      by_cases h6 : t = κ.tp 6
      · subst h6
        simp [hT14, hT13, qyTB, QyKit.tp_inj, hl12]
      by_cases h5 : t = κ.tp 5
      · subst h5
        simp [hT14, hT13, hT12, hT11, hT9, qyTB, QyKit.tp_inj]
      by_cases h7 : t = κ.tp 7
      · subst h7
        simp [hT14, hT13, hT12, hT11, hT9, hT8, hT5, hT4, qyTB, QyKit.tp_inj]
      by_cases h4 : t = κ.tp 4
      · subst h4
        simp [hT14, hT13, hT12, hT11, hT9, hT8, hT5, qyTB, QyKit.tp_inj]
      simp [hT14, hT13, hT12, hT11, hT9, hT8, hT5, hT4, qyTB, Function.update_of_ne h3,
        Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h6,
        Function.update_of_ne h7]
    have chain := seg3.trans (seg4.trans (seg5.trans (seg6.trans (seg7.trans (seg8.trans
      (seg9.trans (seg10.trans (seg11.trans (seg12.trans (seg13.trans (seg14.trans
      (seg15.trans seg16))))))))))))
    rw [hend] at chain
    refine Or.inr (Or.inr ⟨hlt, by omega, hlt10', _, ?_, chain⟩)
    simp only [List.length_replicate, List.length_cons, List.length_nil] at *
    omega
  · -- top: ℓ' = n
    have heq : ℓ' = n := le_antisymm hℓn hge
    have hv : compare (ℓ' + 1) (n + 1) = .eq := compare_eq_iff_eq.mpr (by omega)
    have seg16 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .r16 .scan
      (.done (compare (ℓ' + 1) (n + 1))) ⟨.escTop, SweepPhase.sweep⟩ 1 1 T14 T14 P₀ P₀ [] [] _
      c16.1 (by simp [qyLocRed, hv]) hg16 _ (qy_notStop κ .r16 (by decide) rfl)
    refine Or.inr (Or.inl ⟨heq, _, ?_, T14, P₀, seg3.trans (seg4.trans (seg5.trans
      (seg6.trans (seg7.trans (seg8.trans (seg9.trans (seg10.trans (seg11.trans (seg12.trans
      (seg13.trans (seg14.trans (seg15.trans seg16)))))))))))), hesc T14 hT14esc, ?_, rfl⟩)
    · simp only [List.length_replicate, List.length_cons, List.length_nil] at *
      omega
    · simp [hT14, hT13, hT12, hT11, hT9, hT8, hT5, QyKit.tp_inj]

/-! ### The locator's round: the cleanup and the pair's update -/

/-- **A passed round's cleanup** (checkpoint 3): from the tapes `qyTB` after the tests, the
locator clears the old rung, moves the next rung `1^{ℓ' + 1}` onto the rung's tape, clears the
scratch tapes `4` to `7`, and restores the counter from its copy, ending at the pair's update on
the anchor layout of the rung `ℓ' + 1`.

**Proof sketch.** Seven hosted phases, each a row's run: `qy_clear` on tape `2`, `qy_transfer`
from tape `3` to tape `2`, `qy_clear` on tapes `7`, `4`, `5`, `6`, and `qy_copy_over` from tape
`9` to tape `8` (the counter's word `w'` has the copy's width). The endpoint's tapes are the
layout, tape by tape. -/
private theorem qy_rnd_clean {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (a j k F X4 ℓ' : ℕ)
    (w' : List Bool) (hw' : w'.length = κ.m x.length) :
    ∃ t ≤ 2 * a + 2 * (ℓ' + 1) + 2 * (Nat.bits F).length + 2 * (F + a) + 2 * X4 +
        2 * (X4 + 1) + 2 * κ.m x.length + 21,
      Segment (qyLoc κ) (roundStop (qyAnc κ) (qyLocE κ)) (fun _ => True)
        (qyC (x := x) ⟨.c1, SweepPhase.sweep⟩ 1
          (qyTB κ (qyTA κ x.length a j k F w') F a X4 ℓ') (fun _ => 0) [])
        (qyC ⟨.u1, QyCmp.scan⟩ 1 (qyLayT κ x.length (ℓ' + 1) j k) (fun _ => 0) []) t := by
  set n := x.length with hnx
  set P₀ : Fin κ.K → ℤ := fun _ => 0 with hP₀
  set TB := qyTB κ (qyTA κ n a j k F w') F a X4 ℓ' with hTB
  unfold qyLoc
  -- c1: clear the old rung
  have c1 := qy_clear (x := x) (κ.tp 2) 1 TB P₀ [] (List.replicate a true)
    (by simp [hTB, qyTB, qyTA, qyLayT, qyLay, QyKit.tp_inj]) rfl
  set T1 := Function.update TB (κ.tp 2) (FinTM.bufferTape []) with hT1
  have seg1 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .c1 .sweep .done
    ⟨.c2, SweepPhase.sweep⟩ 1 1 TB T1 P₀ P₀ [] [] _ c1.1 (by simp [qyLocRed])
    (qy_guard_of_cut SweepPhase.done (qyLocRed κ .c1) (fun s hs => by simp [qyLocRed, hs]) c1.2)
    _ (qy_notStop κ .c1 (by decide) rfl)
  -- c2: the next rung onto the rung's tape
  have c2 := qy_transfer (x := x) (κ.tp 3) (κ.tp 2) (κ.tp_ne (by decide)) (fun b => b) 1 T1 P₀ []
    (List.replicate (ℓ' + 1) true) [] (by simp [hT1, hTB, qyTB, QyKit.tp_inj]) rfl
    (by simp [hT1]) (by simp [hP₀])
  rw [List.map_id', List.nil_append] at c2
  set T2 := Function.update (Function.update T1 (κ.tp 3) (FinTM.bufferTape [])) (κ.tp 2)
    (FinTM.bufferTape (List.replicate (ℓ' + 1) true)) with hT2
  have seg2 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .c2 .sweep .done
    ⟨.c3, SweepPhase.sweep⟩ 1 1 T1 T2 P₀ P₀ [] [] _ c2.1 (by simp [qyLocRed])
    (qy_guard_of_cut SweepPhase.done (qyLocRed κ .c2) (fun s hs => by simp [qyLocRed, hs]) c2.2)
    _ (qy_notStop κ .c2 (by decide) rfl)
  -- c3: clear f's call tape
  have c3 := qy_clear (x := x) (κ.tp 7) 1 T2 P₀ [] (List.replicate (Nat.bits F).length true)
    (by simp [hT2, hT1, hTB, qyTB, QyKit.tp_inj]) rfl
  set T3 := Function.update T2 (κ.tp 7) (FinTM.bufferTape []) with hT3
  have seg3 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .c3 .sweep .done
    ⟨.c4, SweepPhase.sweep⟩ 1 1 T2 T3 P₀ P₀ [] [] _ c3.1 (by simp [qyLocRed])
    (qy_guard_of_cut SweepPhase.done (qyLocRed κ .c3) (fun s hs => by simp [qyLocRed, hs]) c3.2)
    _ (qy_notStop κ .c3 (by decide) rfl)
  -- c4: clear tape 4
  have c4 := qy_clear (x := x) (κ.tp 4) 1 T3 P₀ [] (List.replicate (F + a) true)
    (by simp [hT3, hT2, hT1, hTB, qyTB, QyKit.tp_inj]) rfl
  set T4 := Function.update T3 (κ.tp 4) (FinTM.bufferTape []) with hT4
  have seg4 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .c4 .sweep .done
    ⟨.c5, SweepPhase.sweep⟩ 1 1 T3 T4 P₀ P₀ [] [] _ c4.1 (by simp [qyLocRed])
    (qy_guard_of_cut SweepPhase.done (qyLocRed κ .c4) (fun s hs => by simp [qyLocRed, hs]) c4.2)
    _ (qy_notStop κ .c4 (by decide) rfl)
  -- c5: clear tape 5
  have c5 := qy_clear (x := x) (κ.tp 5) 1 T4 P₀ [] (List.replicate X4 true)
    (by simp [hT4, hT3, hT2, hT1, hTB, qyTB, QyKit.tp_inj]) rfl
  set T5 := Function.update T4 (κ.tp 5) (FinTM.bufferTape []) with hT5
  have seg5 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .c5 .sweep .done
    ⟨.c6, SweepPhase.sweep⟩ 1 1 T4 T5 P₀ P₀ [] [] _ c5.1 (by simp [qyLocRed])
    (qy_guard_of_cut SweepPhase.done (qyLocRed κ .c5) (fun s hs => by simp [qyLocRed, hs]) c5.2)
    _ (qy_notStop κ .c5 (by decide) rfl)
  -- c6: clear tape 6
  have c6 := qy_clear (x := x) (κ.tp 6) 1 T5 P₀ [] (List.replicate (X4 + 1) true)
    (by simp [hT5, hT4, hT3, hT2, hT1, hTB, qyTB, QyKit.tp_inj]) rfl
  set T6 := Function.update T5 (κ.tp 6) (FinTM.bufferTape []) with hT6
  have seg6 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .c6 .sweep .done
    ⟨.c7, SweepPhase.sweep⟩ 1 1 T5 T6 P₀ P₀ [] [] _ c6.1 (by simp [qyLocRed])
    (qy_guard_of_cut SweepPhase.done (qyLocRed κ .c6) (fun s hs => by simp [qyLocRed, hs]) c6.2)
    _ (qy_notStop κ .c6 (by decide) rfl)
  -- c7: restore the counter from its copy
  have c7 := qy_copy_over (x := x) (κ.tp 9) (κ.tp 8) (κ.tp_ne (by decide)) (fun b => b) 1 T6 P₀
    [] (List.replicate (κ.m n) true) w' (by simp [hw'])
    (by simp [hT6, hT5, hT4, hT3, hT2, hT1, hTB, qyTB, qyTA, qyLayT, qyLay, QyKit.tp_inj]) rfl
    (by simp [hT6, hT5, hT4, hT3, hT2, hT1, hTB, qyTB, qyTA, QyKit.tp_inj]) rfl
  rw [List.map_id'] at c7
  have hend : Function.update T6 (κ.tp 8) (FinTM.bufferTape (List.replicate (κ.m n) true)) =
      qyLayT κ n (ℓ' + 1) j k := by
    funext t
    rcases κ.tape_cases t with ⟨c, rfl⟩ | h
    · fin_cases c <;>
        simp [hT6, hT5, hT4, hT3, hT2, hT1, hTB, qyTB, qyTA, qyLayT, qyLay, QyKit.tp_inj]
    · simp [hT6, hT5, hT4, hT3, hT2, hT1, hTB, qyTB, qyTA, qyLayT, qyLay, h]
  rw [hend] at c7
  have seg7 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .c7 .sweep .done
    ⟨.u1, QyCmp.scan⟩ 1 1 T6 _ P₀ P₀ [] [] _ c7.1 (by simp [qyLocRed])
    (qy_guard_of_cut SweepPhase.done (qyLocRed κ .c7) (fun s hs => by simp [qyLocRed, hs]) c7.2)
    _ (qy_notStop κ .c7 (by decide) rfl)
  refine ⟨_, ?_, seg1.trans (seg2.trans (seg3.trans (seg4.trans (seg5.trans (seg6.trans
    seg7)))))⟩
  have e : κ.m x.length = κ.m n := rfl
  simp only [List.length_replicate]
  omega

/-- The anchor layout with the pair's tapes changed is the layout of the new pair. -/
private theorem qy_layT_pair {f g : ℕ → ℕ} (κ : QyKit f g) (n a j k j' k' : ℕ)
    (T : Fin κ.K → ℤ → Option Bool) (h10 : T (κ.tp 10) = FinTM.bufferTape (List.replicate j' true))
    (h11 : T (κ.tp 11) = FinTM.bufferTape (List.replicate k' true))
    (hrest : ∀ t, t ≠ κ.tp 10 → t ≠ κ.tp 11 → T t = qyLayT κ n a j k t) :
    T = qyLayT κ n a j' k' := by
  funext t
  by_cases e10 : t = κ.tp 10
  · subst e10
    rw [h10]
    simp [qyLayT, qyLay, QyKit.tp_inj]
  by_cases e11 : t = κ.tp 11
  · subst e11
    rw [h11]
    simp [qyLayT, qyLay, QyKit.tp_inj]
  rw [hrest t e10 e11]
  simp [qyLayT, qyLay, e10, e11]

/-- **A passed round's pair update** (checkpoint 3): from the anchor layout with
`(j, k) = unpair h` on tapes `10` and `11`, the locator moves the pair to `unpair (h + 1)` by the
successor rule of `Nat.unpair` and returns to its anchor.

**Proof sketch.** The comparison `j` against `k` (L2), then by its verdict: `lt`, the increment
of `j` (the `appendBit` call on tape `10`) and the comparison `j + 1` against `k`, with the clear
of `k` on `eq` (`qy_unpair_succ_last`) and nothing on `lt` (`qy_unpair_succ_lt`); `eq`, the clear
of `j` and the increment of `k` (`qy_unpair_succ_diag`); `gt`, the increment of `k`
(`qy_unpair_succ_gt`). The last phase dispatches to the anchor; the layout is
`qy_layT_pair`. -/
private theorem qy_rnd_pair {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (a h j k : ℕ)
    (H : Nat.unpair h = (j, k)) :
    ∃ t ≤ κ.abA * (j + k + 2) + 6 * (j + k) + 30,
      Segment (qyLoc κ) (roundStop (qyAnc κ) (qyLocE κ)) (fun _ => True)
        (qyC (x := x) ⟨.u1, QyCmp.scan⟩ 1 (qyLayT κ x.length a j k) (fun _ => 0) [])
        (qyC (qyAnc κ) 1 (qyLayT κ x.length a (Nat.unpair (h + 1)).1 (Nat.unpair (h + 1)).2)
          (fun _ => 0) []) t := by
  set n := x.length with hnx
  set P₀ : Fin κ.K → ℤ := fun _ => 0 with hP₀
  set T₀ := qyLayT κ n a j k with hT₀
  unfold qyLoc qyAnc
  have hJ : T₀ (κ.tp 10) = FinTM.bufferTape (List.replicate j true) := by
    simp [hT₀, qyLayT, qyLay, QyKit.tp_inj]
  have hK : T₀ (κ.tp 11) = FinTM.bufferTape (List.replicate k true) := by
    simp [hT₀, qyLayT, qyLay, QyKit.tp_inj]
  -- u1: j against k
  have c1 := qy_cmp_run (x := x) (κ.tp 10) (κ.tp 11) (κ.tp_ne (by decide)) 1 T₀ P₀ []
    (List.replicate j true) (List.replicate k true) hJ hK rfl rfl
  rw [List.length_replicate, List.length_replicate] at c1
  have hg1 : ∀ u < 2 * min j k + 2, ∀ s,
      ((qyLocM κ .u1).runFrom (qyC QyCmp.scan 1 T₀ P₀ []) u).state = some s →
        qyLocRed κ .u1 s = none := fun u hu s hs => by
    cases s with
    | done w => exact absurd hs (c1.2 u hu w)
    | _ => simp [qyLocRed]
  have hm1 := min_le_left j k
  have hab : ∀ i, i ≤ j + k + 1 → κ.abA * (i + 1) ≤ κ.abA * (j + k + 2) :=
    fun i hi => Nat.mul_le_mul_left _ (by omega)
  rcases Nat.lt_trichotomy j k with hlt | heq | hgt
  · -- j < k: increment j
    have hv : compare j k = .lt := compare_lt_iff_lt.mpr hlt
    have seg1 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .u1 .scan
      (.done (compare j k)) ⟨.incJ, Sum.inl ()⟩ 1 1 T₀ T₀ P₀ P₀ [] [] _ c1.1
      (by simp [qyLocRed, hv]) hg1 _ (qy_notStop κ .u1 (by decide) rfl)
    obtain ⟨tb, htb, hposb, hcutb, hrunb⟩ := κ.abS x (List.replicate j true)
    simp only [List.length_replicate] at htb
    have hb10 : κ.bAbJ ⟨0, κ.abK⟩ = κ.tp 10 := rfl
    have c2 := qy_callHost κ.ab κ.abK κ.bAbJ κ.abE κ.abX (List.replicate j true) _ tb hposb
      hcutb hrunb T₀ P₀ []
      (qy_arg_bank κ.bAbJ κ.abK T₀ _ (by rw [hb10]; exact hJ)
        (fun i hi => by simp [hT₀, qyLayT, qyLay, κ.bAbJ_ne i hi]))
      (fun _ => rfl)
    beta_reduce at c2
    rw [hb10, ← List.replicate_succ'] at c2
    set T2 := Function.update T₀ (κ.tp 10) (FinTM.bufferTape (List.replicate (j + 1) true))
      with hT2
    have seg2 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .incJ (Sum.inl ())
      (Sum.inr κ.abX) ⟨.u2, QyCmp.scan⟩ 1 1 T₀ T2 P₀ P₀ [] [] tb c2.1 (by simp [qyLocRed])
      (qy_guard_of_cut (Sum.inr κ.abX) (qyLocRed κ .incJ) (fun s hs => by simp [qyLocRed, hs])
        c2.2) _ (qy_notStop κ .incJ (by decide) rfl)
    -- u2: j + 1 against k
    have c3 := qy_cmp_run (x := x) (κ.tp 10) (κ.tp 11) (κ.tp_ne (by decide)) 1 T2 P₀ []
      (List.replicate (j + 1) true) (List.replicate k true) (by simp [hT2])
      (by simp [hT2, hT₀, qyLayT, qyLay, QyKit.tp_inj]) rfl rfl
    rw [List.length_replicate, List.length_replicate] at c3
    have hg3 : ∀ u < 2 * min (j + 1) k + 2, ∀ s,
        ((qyLocM κ .u2).runFrom (qyC QyCmp.scan 1 T2 P₀ []) u).state = some s →
          qyLocRed κ .u2 s = none := fun u hu s hs => by
      cases s with
      | done w => exact absurd hs (c3.2 u hu w)
      | _ => simp [qyLocRed]
    have hm3 := min_le_right (j + 1) k
    rcases Nat.lt_or_ge (j + 1) k with hlt' | hge'
    · -- j + 1 < k: the pair (j + 1, k)
      have hv' : compare (j + 1) k = .lt := compare_lt_iff_lt.mpr hlt'
      have seg3 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .u2 .scan
        (.done (compare (j + 1) k)) ⟨.anc, SweepPhase.sweep⟩ 1 1 T2 T2 P₀ P₀ [] [] _ c3.1
        (by simp [qyLocRed, hv']) hg3 _ (qy_notStop κ .u2 (by decide) rfl)
      have hend : T2 = qyLayT κ n a (Nat.unpair (h + 1)).1 (Nat.unpair (h + 1)).2 := by
        rw [qy_unpair_succ_lt H hlt']
        exact qy_layT_pair κ n a j k _ _ T2 (by simp [hT2]) (by simp [hT2, hK, QyKit.tp_inj])
          (fun t e10 _ => by simp [hT2, hT₀, Function.update_of_ne e10])
      have chain := seg1.trans (seg2.trans seg3)
      rw [hend] at chain
      refine ⟨_, ?_, chain⟩
      have := hab j (by omega)
      omega
    · -- j + 1 = k: the pair (k, 0)
      have he : j + 1 = k := by omega
      have hv' : compare (j + 1) k = .eq := compare_eq_iff_eq.mpr he
      have seg3 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .u2 .scan
        (.done (compare (j + 1) k)) ⟨.clrK, SweepPhase.sweep⟩ 1 1 T2 T2 P₀ P₀ [] [] _ c3.1
        (by simp [qyLocRed, hv']) hg3 _ (qy_notStop κ .u2 (by decide) rfl)
      have c4 := qy_clear (x := x) (κ.tp 11) 1 T2 P₀ [] (List.replicate k true)
        (by simp [hT2, hK, QyKit.tp_inj]) rfl
      have hend : Function.update T2 (κ.tp 11) (FinTM.bufferTape []) =
          qyLayT κ n a (Nat.unpair (h + 1)).1 (Nat.unpair (h + 1)).2 := by
        rw [qy_unpair_succ_last H he]
        refine qy_layT_pair κ n a j k _ _ _ (by simp [hT2, he, QyKit.tp_inj]) (by simp)
          (fun t e10 e11 => by
            simp [hT2, hT₀, Function.update_of_ne e10, Function.update_of_ne e11])
      rw [hend] at c4
      have seg4 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .clrK .sweep .done
        ⟨.anc, SweepPhase.sweep⟩ 1 1 T2 _ P₀ P₀ [] [] _ c4.1 (by simp [qyLocRed])
        (qy_guard_of_cut SweepPhase.done (qyLocRed κ .clrK) (fun s hs => by simp [qyLocRed, hs])
          c4.2) _ (qy_notStop κ .clrK (by decide) rfl)
      refine ⟨_, ?_, seg1.trans (seg2.trans (seg3.trans seg4))⟩
      have := hab j (by omega)
      simp only [List.length_replicate]
      omega
  · -- j = k: clear j, increment k
    subst heq
    have seg1 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .u1 .scan
      (.done (compare j j)) ⟨.clrJ, SweepPhase.sweep⟩ 1 1 T₀ T₀ P₀ P₀ [] [] _ c1.1
      (by simp [qyLocRed]) hg1 _ (qy_notStop κ .u1 (by decide) rfl)
    have c2 := qy_clear (x := x) (κ.tp 10) 1 T₀ P₀ [] (List.replicate j true) hJ rfl
    set T2 := Function.update T₀ (κ.tp 10) (FinTM.bufferTape []) with hT2
    have seg2 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .clrJ .sweep .done
      ⟨.incK, Sum.inl ()⟩ 1 1 T₀ T2 P₀ P₀ [] [] _ c2.1 (by simp [qyLocRed])
      (qy_guard_of_cut SweepPhase.done (qyLocRed κ .clrJ) (fun s hs => by simp [qyLocRed, hs])
        c2.2) _ (qy_notStop κ .clrJ (by decide) rfl)
    obtain ⟨tb, htb, hposb, hcutb, hrunb⟩ := κ.abS x (List.replicate j true)
    simp only [List.length_replicate] at htb
    have hb11 : κ.bAbK ⟨0, κ.abK⟩ = κ.tp 11 := rfl
    have c3 := qy_callHost κ.ab κ.abK κ.bAbK κ.abE κ.abX (List.replicate j true) _ tb hposb
      hcutb hrunb T2 P₀ []
      (qy_arg_bank κ.bAbK κ.abK T2 _ (by rw [hb11]; simp [hT2, hK, QyKit.tp_inj])
        (fun i hi => by simp [hT2, hT₀, qyLayT, qyLay, κ.bAbK_ne i hi]))
      (fun _ => rfl)
    beta_reduce at c3
    rw [hb11, ← List.replicate_succ'] at c3
    have hend : Function.update T2 (κ.tp 11) (FinTM.bufferTape (List.replicate (j + 1) true)) =
        qyLayT κ n a (Nat.unpair (h + 1)).1 (Nat.unpair (h + 1)).2 := by
      rw [qy_unpair_succ_diag H]
      refine qy_layT_pair κ n a j j _ _ _ (by simp [hT2, QyKit.tp_inj]) (by simp)
        (fun t e10 e11 => by simp [hT2, hT₀, Function.update_of_ne e10, Function.update_of_ne e11])
    rw [hend] at c3
    have seg3 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .incK (Sum.inl ())
      (Sum.inr κ.abX) ⟨.anc, SweepPhase.sweep⟩ 1 1 T2 _ P₀ P₀ [] [] tb c3.1 (by simp [qyLocRed])
      (qy_guard_of_cut (Sum.inr κ.abX) (qyLocRed κ .incK) (fun s hs => by simp [qyLocRed, hs])
        c3.2) _ (qy_notStop κ .incK (by decide) rfl)
    refine ⟨_, ?_, seg1.trans (seg2.trans seg3)⟩
    have := hab j (by omega)
    simp only [List.length_replicate]
    omega
  · -- k < j: increment k
    have hv : compare j k = .gt := compare_gt_iff_gt.mpr hgt
    have seg1 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .u1 .scan
      (.done (compare j k)) ⟨.incK, Sum.inl ()⟩ 1 1 T₀ T₀ P₀ P₀ [] [] _ c1.1
      (by simp [qyLocRed, hv]) hg1 _ (qy_notStop κ .u1 (by decide) rfl)
    obtain ⟨tb, htb, hposb, hcutb, hrunb⟩ := κ.abS x (List.replicate k true)
    simp only [List.length_replicate] at htb
    have hb11 : κ.bAbK ⟨0, κ.abK⟩ = κ.tp 11 := rfl
    have c2 := qy_callHost κ.ab κ.abK κ.bAbK κ.abE κ.abX (List.replicate k true) _ tb hposb
      hcutb hrunb T₀ P₀ []
      (qy_arg_bank κ.bAbK κ.abK T₀ _ (by rw [hb11]; exact hK)
        (fun i hi => by simp [hT₀, qyLayT, qyLay, κ.bAbK_ne i hi]))
      (fun _ => rfl)
    beta_reduce at c2
    rw [hb11, ← List.replicate_succ'] at c2
    have hend : Function.update T₀ (κ.tp 11) (FinTM.bufferTape (List.replicate (k + 1) true)) =
        qyLayT κ n a (Nat.unpair (h + 1)).1 (Nat.unpair (h + 1)).2 := by
      rw [qy_unpair_succ_gt H hgt]
      refine qy_layT_pair κ n a j k _ _ _ (by simp [hJ, QyKit.tp_inj]) (by simp)
        (fun t _ e11 => by simp [hT₀, Function.update_of_ne e11])
    rw [hend] at c2
    have seg2 := qy_hosted (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .incK (Sum.inl ())
      (Sum.inr κ.abX) ⟨.anc, SweepPhase.sweep⟩ 1 1 T₀ _ P₀ P₀ [] [] tb c2.1 (by simp [qyLocRed])
      (qy_guard_of_cut (Sum.inr κ.abX) (qyLocRed κ .incK) (fun s hs => by simp [qyLocRed, hs])
        c2.2) _ (qy_notStop κ .incK (by decide) rfl)
    refine ⟨_, ?_, seg1.trans seg2⟩
    have := hab k (by omega)
    omega

/-! ### The locator's round -/

/-- A passed round's time bound: the next rung `ℓ'`, the counter's width `m`, the call's bound on
arguments below `|bits n|`, the polylogarithmic calls, and the pair `(j, k)`. -/
private def qyRndP {f g : ℕ → ℕ} (κ : QyKit f g) (n ℓ' j k : ℕ) : ℕ :=
  11 * ℓ' + 50 * (Nat.bits n).length + 4 * κ.m n +
    5 * (κ.cfA * ((κ.cfc + 3) * ((Nat.bits n).length + 1))) + κ.puA * (Nat.bits n).length ^ 5 +
    κ.abA * ((Nat.bits n).length + 1) + κ.abA * (j + k + 2) + 6 * (j + k) + 150

/-- A stopping round's time bound: linear in `n` and in the clock's budget `2 ^ m`, plus the
fourth power's call on a word shorter than `|bits n|`. -/
private def qyRndS {f g : ℕ → ℕ} (κ : QyKit f g) (n a : ℕ) : ℕ :=
  6 * a + 5 * 2 ^ κ.m n + 2 * κ.m n + 40 * (n + 1) + 16 * (Nat.bits n).length +
    κ.puA * (Nat.bits n).length ^ 5 + κ.abA * ((Nat.bits n).length + 1) + 70

/-- **One round of the locator** (checkpoint 3), as a `Turing.Round` at the anchor with the three
escapes: from the anchor layout at the rung `1^a`, `a ≤ n`, with `(j, k) = unpair h`, and with
`X = f a + a + 1` and `ℓ' = 2 ^ X⁴`:
* if `ℓ' < n`, the round returns to the anchor on the layout of the rung `ℓ' + 1` and the pair
  `unpair (h + 1)`, within `qyRndP`;
* if `n < ℓ'`, it ends at the interior or the timeout escape, the tapes off the scratch untouched,
  within `qyRndS`;
* if `ℓ' = n`, it ends at the top escape, with `1^{X - 1}` on tape `4`, within `qyRndS`.

**Proof sketch.** The anchor's dispatch (`qy_hosted_run`), then the call (`qy_rnd_call`): its
timeout is the timeout escape (`n < f a < ℓ'`). After a returned call, the tests
(`qy_rnd_tests`) give the interior and the top escapes, or the passed tests, followed by the
cleanup (`qy_rnd_clean`) and the pair's update (`qy_rnd_pair`). The segments are chained by
`Turing.Segment.trans` and made a round by `qy_round_of_seg`; the time bounds are summed, with
`X < |bits n|` and `X⁴ < |bits n|` on a passed round. -/
private theorem qy_round {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (a h j k : ℕ)
    (ha : a ≤ x.length) (H : Nat.unpair h = (j, k)) :
    ∃ (c' : Cfg κ.K Bool (Σ i, QyLPh κ i) x) (t : ℕ),
      Round (qyLoc κ) (qyAnc κ) (qyLocE κ) (fun _ => True)
        (qyC (x := x) (qyAnc κ) 1 (qyLayT κ x.length a j k) (fun _ => 0) []) c' t ∧
      ((2 ^ (f a + a + 1) ^ 4 < x.length ∧
          c' = qyC (qyAnc κ) 1 (qyLayT κ x.length (2 ^ (f a + a + 1) ^ 4 + 1)
            (Nat.unpair (h + 1)).1 (Nat.unpair (h + 1)).2) (fun _ => 0) [] ∧
          t ≤ qyRndP κ x.length (2 ^ (f a + a + 1) ^ 4) j k) ∨
        (x.length < 2 ^ (f a + a + 1) ^ 4 ∧ t ≤ qyRndS κ x.length a ∧
          ∃ (ip : Fin (x.length + 2)) (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ),
            (c' = qyC ⟨.escI, SweepPhase.sweep⟩ ip T P [] ∨
              c' = qyC ⟨.escTO, SweepPhase.sweep⟩ ip T P []) ∧ QyEscT κ x.length a j k T P) ∨
        (2 ^ (f a + a + 1) ^ 4 = x.length ∧ t ≤ qyRndS κ x.length a ∧
          ∃ (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ),
            c' = qyC ⟨.escTop, SweepPhase.sweep⟩ 1 T P [] ∧ QyEscT κ x.length a j k T P ∧
            T (κ.tp 4) = FinTM.bufferTape (List.replicate (f a + a) true) ∧ P (κ.tp 4) = 0)) := by
  have h1 : (qyLoc κ).runFrom (qyC (x := x) (qyAnc κ) 1 (qyLayT κ x.length a j k)
      (fun _ => 0) []) 1 = qyC ⟨.r1, SweepPhase.sweep⟩ 1 (qyLayT κ x.length a j k)
      (fun _ => 0) [] := by
    unfold qyLoc qyAnc
    exact qy_hosted_run (qyLocM κ) ⟨.anc, SweepPhase.sweep⟩ (qyLocRed κ) .anc .sweep .sweep
      ⟨.r1, SweepPhase.sweep⟩ 1 1 _ _ _ _ [] [] 0 MultiTapeTM.runFrom_zero (by simp [qyLocRed])
      (fun u hu => absurd hu (Nat.not_lt_zero u))
  have hc : (qyC (x := x) (qyAnc κ) 1 (qyLayT κ x.length a j k) (fun _ => 0) []).state =
      some (qyAnc κ) := rfl
  have hX : f a + a + 1 ≤ (f a + a + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have hXl := Nat.lt_two_pow_self (n := (f a + a + 1) ^ 4)
  rcases qy_rnd_call κ (x := x) a j k ha with
    ⟨t1, ht1, ht1', w', hw', seg1⟩ | ⟨hFn, t1, ht1, ip, T, P, seg1, hesc⟩
  · rcases qy_rnd_tests κ (x := x) a j k w' with
      ⟨hI, t2, ht2, T, P, seg2, hesc⟩ | ⟨hT, t2, ht2, T, P, seg2, hesc, h4, hP4⟩ |
        ⟨hN, hXb, hX4b, t2, ht2, seg2⟩
    · -- interior
      refine ⟨_, _, qy_round_of_seg hc h1 (seg1.trans seg2) (qy_esc_mem κ .escI rfl _),
        Or.inr (Or.inl ⟨hI, ?_, 1, T, P, Or.inl rfl, hesc⟩)⟩
      unfold qyRndS
      unfold qyTestS at ht2
      omega
    · -- top
      refine ⟨_, _, qy_round_of_seg hc h1 (seg1.trans seg2) (qy_esc_mem κ .escTop rfl _),
        Or.inr (Or.inr ⟨hT, ?_, T, P, rfl, hesc, h4, hP4⟩)⟩
      unfold qyRndS
      unfold qyTestS at ht2
      omega
    · -- next
      obtain ⟨t3, ht3, seg3⟩ := qy_rnd_clean κ (x := x) a j k (f a) ((f a + a + 1) ^ 4)
        (2 ^ (f a + a + 1) ^ 4) w' hw'
      obtain ⟨t4, ht4, seg4⟩ := qy_rnd_pair κ (x := x) (2 ^ (f a + a + 1) ^ 4 + 1) h j k H
      refine ⟨_, _, qy_round_of_seg hc h1 (seg1.trans (seg2.trans (seg3.trans seg4)))
        (Set.mem_insert _ _), Or.inl ⟨hN, rfl, ?_⟩⟩
      have hbF := length_bits_le_self (f a)
      have hq1 : κ.cfc * (f a + 1) ≤ κ.cfc * ((Nat.bits x.length).length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hq2 : κ.cfc * (f a + 1) + a + (Nat.bits (f a)).length + 1 ≤
          (κ.cfc + 3) * ((Nat.bits x.length).length + 1) := by
        rw [add_mul]
        omega
      have hq3 := Nat.mul_le_mul_left κ.cfA hq2
      unfold qyRndP
      unfold qyTestP at ht2
      omega
  · -- timeout
    refine ⟨_, _, qy_round_of_seg hc h1 seg1 (qy_esc_mem κ .escTO rfl _),
      Or.inr (Or.inl ⟨by omega, ?_, ip, T, P, Or.inr rfl, hesc⟩)⟩
    unfold qyRndS
    omega

/-! ### The locator's loop and its ledger -/

/-- **A sixth power is at most exponential**: `x ^ 6 ≤ 6 ^ 6 · 2 ^ x`. -/
private theorem qy_pow6_le (x : ℕ) : x ^ 6 ≤ 6 ^ 6 * 2 ^ x := by
  have hq : x / 6 + 1 ≤ 2 ^ (x / 6) := Nat.lt_two_pow_self
  have h1 : x ≤ 6 * 2 ^ (x / 6) := by omega
  have h2 : 2 ^ (6 * (x / 6)) ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le x 6)
  calc x ^ 6 ≤ (6 * 2 ^ (x / 6)) ^ 6 := Nat.pow_le_pow_left h1 6
    _ = 6 ^ 6 * 2 ^ (6 * (x / 6)) := by rw [mul_pow, ← pow_mul, mul_comm (x / 6) 6]
    _ ≤ 6 ^ 6 * 2 ^ x := Nat.mul_le_mul_left _ h2

/-- A sum of an affine family: `∑_{r < s} (11 u r + c) = 11 ∑_{r < s} u r + s c`. -/
private theorem qy_sum_affine (u : ℕ → ℕ) (c s : ℕ) :
    ∑ r ∈ Finset.range s, (11 * u r + c) = 11 * ∑ r ∈ Finset.range s, u r + s * c := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- The kit's polylogarithmic constant: the coefficient of `(|bits n| + 1) ^ 5` in a round. -/
private def qyCk {f g : ℕ → ℕ} (κ : QyKit f g) : ℕ :=
  210 + 4 * (Nat.bits (κ.cfA * (κ.cfc + 2))).length + 5 * (κ.cfA * (κ.cfc + 3)) + κ.puA +
    3 * κ.abA

/-- The kit's linear constant: the coefficient of `n + 1` in a stopping round. -/
private def qyDk {f g : ℕ → ℕ} (κ : QyKit f g) : ℕ :=
  134 + 10 * 2 ^ (Nat.bits (κ.cfA * (κ.cfc + 2))).length +
    2 * (Nat.bits (κ.cfA * (κ.cfc + 2))).length

/-- The locator's constant: its whole run on inputs of length `n ≥ 3` is within
`qyLoopA (n + 1)`. -/
private def qyLoopA {f g : ℕ → ℕ} (κ : QyKit f g) : ℕ :=
  22 + qyDk κ + 8 * 6 ^ 6 * qyCk κ

/-- **A passed round's bound, simplified**: with `j + k ≤ |bits n|`, the bound `qyRndP` is at
most `11 ℓ'` plus the polylogarithmic `qyCk (|bits n| + 1) ^ 5`. -/
private theorem qy_rndP_le {f g : ℕ → ℕ} (κ : QyKit f g) (n ℓ' j k : ℕ)
    (hjk : j + k ≤ (Nat.bits n).length) :
    qyRndP κ n ℓ' j k ≤ 11 * ℓ' + qyCk κ * ((Nat.bits n).length + 1) ^ 5 := by
  unfold qyRndP qyCk QyKit.m
  set L := (Nat.bits n).length with hL
  set D := (Nat.bits (κ.cfA * (κ.cfc + 2))).length with hD
  set P := (L + 1) ^ 5 with hP
  have hP1 : L + 1 ≤ P := Nat.le_self_pow (by norm_num) _
  have hP5 : L ^ 5 ≤ P := Nat.pow_le_pow_left (Nat.le_succ L) 5
  have e1 : κ.cfA * ((κ.cfc + 3) * (L + 1)) ≤ κ.cfA * (κ.cfc + 3) * P := by
    rw [← mul_assoc]
    exact Nat.mul_le_mul_left _ hP1
  have e2 : κ.puA * L ^ 5 ≤ κ.puA * P := Nat.mul_le_mul_left _ hP5
  have e3 : κ.abA * (L + 1) ≤ κ.abA * P := Nat.mul_le_mul_left _ hP1
  have e4 : κ.abA * (j + k + 2) ≤ 2 * (κ.abA * P) := by
    calc κ.abA * (j + k + 2) ≤ κ.abA * (2 * P) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (κ.abA * P) := by ring
  have e5 : D ≤ D * P := Nat.le_mul_of_pos_right _ (by omega)
  have e6 : (210 + 4 * D + 5 * (κ.cfA * (κ.cfc + 3)) + κ.puA + 3 * κ.abA) * P =
      210 * P + 4 * (D * P) + 5 * (κ.cfA * (κ.cfc + 3) * P) + κ.puA * P + 3 * (κ.abA * P) := by
    ring
  rw [e6]
  omega

/-- **A stopping round's bound, simplified**: with `a ≤ n`, the bound `qyRndS` is at most
`qyDk (n + 1)` plus the polylogarithmic `qyCk (|bits n| + 1) ^ 5`.

**Proof sketch.** `6 a ≤ 6 n`; the clock's budget `2 ^ m = 2 ^ |bits D₀| · 2 ^ |bits n| ≤
2 ^ |bits D₀| (2 n + 1)` (`qy_two_pow_bits_le`); `|bits n| ≤ n`; the two calls' terms are at most
`(|bits n| + 1) ^ 5` times their constants. Expand both products and add. -/
private theorem qy_rndS_le {f g : ℕ → ℕ} (κ : QyKit f g) (n a : ℕ) (ha : a ≤ n) :
    qyRndS κ n a ≤ qyDk κ * (n + 1) + qyCk κ * ((Nat.bits n).length + 1) ^ 5 := by
  unfold qyRndS qyDk qyCk QyKit.m
  have hLn := length_bits_le_self n
  have h2L := qy_two_pow_bits_le n
  set L := (Nat.bits n).length with hL
  set D := (Nat.bits (κ.cfA * (κ.cfc + 2))).length with hD
  set P := (L + 1) ^ 5 with hP
  have hP1 : L + 1 ≤ P := Nat.le_self_pow (by norm_num) _
  have hP5 : L ^ 5 ≤ P := Nat.pow_le_pow_left (Nat.le_succ L) 5
  have e2 : κ.puA * L ^ 5 ≤ κ.puA * P := Nat.mul_le_mul_left _ hP5
  have e3 : κ.abA * (L + 1) ≤ κ.abA * P := Nat.mul_le_mul_left _ hP1
  have e4 : 2 ^ (D + L) ≤ 2 ^ D * (2 * n + 1) := by
    rw [pow_add]
    exact Nat.mul_le_mul_left _ h2L
  have e5 : 2 ^ D * (2 * n + 1) ≤ 2 * (2 ^ D * (n + 1)) := by
    calc 2 ^ D * (2 * n + 1) ≤ 2 ^ D * (2 * (n + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (2 ^ D * (n + 1)) := by ring
  have e6 : D ≤ D * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have e7 : (134 + 10 * 2 ^ D + 2 * D) * (n + 1) =
      134 * (n + 1) + 10 * (2 ^ D * (n + 1)) + 2 * (D * (n + 1)) := by ring
  have e8 : (210 + 4 * D + 5 * (κ.cfA * (κ.cfc + 3)) + κ.puA + 3 * κ.abA) * P =
      210 * P + 4 * (D * P) + 5 * (κ.cfA * (κ.cfc + 3) * P) + κ.puA * P + 3 * (κ.abA * P) := by
    ring
  rw [e7, e8]
  omega

/-- The locator's anchor configuration at the stage `i` on inputs of length `n`: the rung
`ℓᵢ + 1` and the pair `unpair i`. -/
private def qyAt {f g : ℕ → ℕ} (κ : QyKit f g) (x : List Bool) (i : ℕ) :
    Cfg κ.K Bool (Σ i, QyLPh κ i) x :=
  qyC (qyAnc κ) 1 (qyLayT κ x.length (ladder f i + 1) (Nat.unpair i).1 (Nat.unpair i).2)
    (fun _ => 0) []

/-- **The locator's loop** (checkpoint 4): on inputs of length `n ≥ 3`, from the anchor at the
first rung, the locator runs, avoiding its escapes before the end, to an escape at the stage
`s = stage f n`, within `qyLoopA (n + 1)` steps: an interior or timeout escape when
`n < ℓ_{s+1}`, the top escape when `n = ℓ_{s+1}` (with `1^{X - 1}` on tape `4`,
`X = f (ℓ_s + 1) + ℓ_s + 2`), the tapes off the round's scratch on the anchor layout of the
stage `s` with their heads at `0`.

**Proof sketch.** The rounds at the stages `i < s` pass (`qy_round`; `ℓᵢ₊₁ ≤ ℓ_s < n` by
`stage_spec` and `ladder_strictMono`), each from `qyAt κ x i` to `qyAt κ x (i + 1)` with the
rung `ladder f (i + 1) + 1` (`qy_ladder_succ_eq`); their times are chosen first, then
`Turing.Round.iterate_seq` gives one segment against the escapes. The round at `s` stops
(`stage_spec`), and `Turing.Round.segment` appends it. The ledger: the passed rounds cost at
most `11 ∑ ℓᵢ₊₁ ≤ 22 ℓ_s` (`qy_ledger`) plus `s · qyCk (|bits n| + 1)⁵` (`qy_rndP_le`, with
`j + k ≤ i < s < log₂ n`, `Nat.unpair_add_le`, `qy_stage_lt_log`); the stopping round at most
`qyDk (n + 1) + qyCk (|bits n| + 1)⁵` (`qy_rndS_le`); and `(|bits n| + 1)⁶ ≤ 6⁶ · 2 ^ (|bits n| + 1)
≤ 6⁶ · 4 (n + 1)` (`qy_pow6_le`, `qy_two_pow_bits_le`). -/
private theorem qy_loop {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (hn : 3 ≤ x.length) :
    ∃ t ≤ qyLoopA κ * (x.length + 1), ∃ c' : Cfg κ.K Bool (Σ i, QyLPh κ i) x,
      Segment (qyLoc κ) (qyLocE κ) (fun _ => True) (qyAt κ x 0) c' t ∧
      ((x.length < ladder f (stage f x.length + 1) ∧
          ∃ (ip : Fin (x.length + 2)) (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ),
            (c' = qyC ⟨.escI, SweepPhase.sweep⟩ ip T P [] ∨
              c' = qyC ⟨.escTO, SweepPhase.sweep⟩ ip T P []) ∧
            QyEscT κ x.length (ladder f (stage f x.length) + 1)
              (Nat.unpair (stage f x.length)).1 (Nat.unpair (stage f x.length)).2 T P) ∨
        (ladder f (stage f x.length + 1) = x.length ∧
          ∃ (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ),
            c' = qyC ⟨.escTop, SweepPhase.sweep⟩ 1 T P [] ∧
            QyEscT κ x.length (ladder f (stage f x.length) + 1)
              (Nat.unpair (stage f x.length)).1 (Nat.unpair (stage f x.length)).2 T P ∧
            T (κ.tp 4) = FinTM.bufferTape (List.replicate
              (f (ladder f (stage f x.length) + 1) + (ladder f (stage f x.length) + 1)) true) ∧
            P (κ.tp 4) = 0)) := by
  have hspec := stage_spec f hn
  have hlog := qy_stage_lt_log f hn
  have hLb := qy_log_bits (n := x.length) (by omega)
  have hanc : some (qyAnc κ) ∉ qyLocE κ := fun ⟨p, hp, hpe⟩ => by
    rw [← Option.some.inj hp] at hpe
    exact Bool.false_ne_true hpe
  -- the passed rounds, with their times chosen first
  have hpass : ∀ i, ∃ t, i < stage f x.length →
      Round (qyLoc κ) (qyAnc κ) (qyLocE κ) (fun _ => True) (qyAt κ x i) (qyAt κ x (i + 1)) t ∧
        t ≤ 11 * ladder f (i + 1) + qyCk κ * ((Nat.bits x.length).length + 1) ^ 5 := by
    intro i
    by_cases hi : i < stage f x.length
    · have hlt : ladder f (i + 1) < x.length :=
        lt_of_le_of_lt ((ladder_strictMono f).monotone hi) hspec.1
      have hle : ladder f i + 1 ≤ x.length := by
        have := (ladder_strictMono f) (show i < i + 1 by omega)
        omega
      obtain ⟨c', t, hR, hcase⟩ := qy_round κ (x := x) (ladder f i + 1) i (Nat.unpair i).1
        (Nat.unpair i).2 hle rfl
      rw [← qy_ladder_succ_eq] at hcase
      rcases hcase with ⟨_, hc', ht⟩ | ⟨hI, _⟩ | ⟨hT, _⟩
      · refine ⟨t, fun _ => ⟨?_, ?_⟩⟩
        · rw [hc'] at hR
          exact hR
        · have hjk := Nat.unpair_add_le i
          exact ht.trans (qy_rndP_le κ _ _ _ _ (by omega))
      · omega
      · omega
    · exact ⟨0, fun h => absurd h hi⟩
  choose τ hτ using hpass
  have hseq := Round.iterate_seq (qyAt κ x) τ hanc trivial (stage f x.length)
    (fun r hr => (hτ r hr).1)
  -- the stopping round
  have hle : ladder f (stage f x.length) + 1 ≤ x.length := by omega
  obtain ⟨c', t, hR, hcase⟩ := qy_round κ (x := x) (ladder f (stage f x.length) + 1)
    (stage f x.length) (Nat.unpair (stage f x.length)).1 (Nat.unpair (stage f x.length)).2 hle
    rfl
  rw [← qy_ladder_succ_eq] at hcase
  have hseg := hseq.trans (hR.segment hanc)
  -- the ledger
  have hsum : ∑ r ∈ Finset.range (stage f x.length), τ r ≤
      11 * (2 * ladder f (stage f x.length)) +
        stage f x.length * (qyCk κ * ((Nat.bits x.length).length + 1) ^ 5) := by
    calc ∑ r ∈ Finset.range (stage f x.length), τ r
        ≤ ∑ r ∈ Finset.range (stage f x.length),
            (11 * ladder f (r + 1) + qyCk κ * ((Nat.bits x.length).length + 1) ^ 5) :=
          Finset.sum_le_sum fun r hr => (hτ r (Finset.mem_range.mp hr)).2
      _ = 11 * ∑ r ∈ Finset.range (stage f x.length), ladder f (r + 1) +
            stage f x.length * (qyCk κ * ((Nat.bits x.length).length + 1) ^ 5) := by
          exact qy_sum_affine _ _ _
      _ ≤ _ := by
          have := qy_ledger f (stage f x.length)
          omega
  set L := (Nat.bits x.length).length with hL
  have hP6 := qy_pow6_le (L + 1)
  have h2L : 2 ^ L ≤ 2 * x.length + 1 := qy_two_pow_bits_le x.length
  have hsP : stage f x.length * (qyCk κ * (L + 1) ^ 5) ≤ qyCk κ * (L + 1) ^ 6 := by
    calc stage f x.length * (qyCk κ * (L + 1) ^ 5) ≤ (L + 1) * (qyCk κ * (L + 1) ^ 5) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = qyCk κ * (L + 1) ^ 6 := by ring
  have hP56 : (L + 1) ^ 5 ≤ (L + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hCP : qyCk κ * (L + 1) ^ 5 ≤ qyCk κ * (L + 1) ^ 6 := Nat.mul_le_mul_left _ hP56
  have hC6 : qyCk κ * (L + 1) ^ 6 ≤ qyCk κ * (6 ^ 6 * (4 * (x.length + 1))) := by
    apply Nat.mul_le_mul_left
    calc (L + 1) ^ 6 ≤ 6 ^ 6 * 2 ^ (L + 1) := hP6
      _ ≤ 6 ^ 6 * (4 * (x.length + 1)) := Nat.mul_le_mul_left _ (by rw [pow_succ]; omega)
  have hA : qyLoopA κ * (x.length + 1) = 22 * (x.length + 1) + qyDk κ * (x.length + 1) +
      2 * (qyCk κ * (6 ^ 6 * (4 * (x.length + 1)))) := by
    unfold qyLoopA
    ring
  rcases hcase with ⟨hN, _⟩ | ⟨hI, ht, ip, T, P, hc', hesc⟩ | ⟨hT, ht, T, P, hc', hesc, h4, hP4⟩
  · omega
  · have ht' : t ≤ qyDk κ * (x.length + 1) + qyCk κ * (L + 1) ^ 5 :=
      ht.trans (qy_rndS_le κ _ _ hle)
    refine ⟨_, ?_, c', hseg, Or.inl ⟨hI, ip, T, P, hc', hesc⟩⟩
    rw [hA]
    omega
  · have ht' : t ≤ qyDk κ * (x.length + 1) + qyCk κ * (L + 1) ^ 5 :=
      ht.trans (qy_rndS_le κ _ _ hle)
    refine ⟨_, ?_, c', hseg, Or.inr ⟨hT, T, P, hc', hesc, h4, hP4⟩⟩
    rw [hA]
    omega

/-! ### After the loop: the input seek and the stage code -/

/-- A tape past the blocks of the input call and `f`'s call is off the round's scratch.

**Proof sketch.** The clock's bank is `f`'s call bank (tape `7` and the block after the input
call's) and the counter tape `8`, and the other scratch tapes are `3` to `6`: compare indices
(`qyBank_zero`, `qyBank_val`, `QyKit.tp_val`). -/
private theorem qy_not_scratch_ge {f g : ℕ → ℕ} (κ : QyKit f g) (t : Fin κ.K)
    (ht : 16 + κ.cb.k + κ.cf.k ≤ (t : ℕ)) : ¬ qyScratch κ t := by
  rintro (⟨i, hi⟩ | h | h | h | h)
  · unfold QyKit.bClk at hi
    rw [Function.Embedding.coeFn_mk] at hi
    by_cases hlt : (i : ℕ) < κ.cf.k
    · rw [dif_pos hlt] at hi
      by_cases h0 : (i : ℕ) = 0
      · have e : (⟨i, hlt⟩ : Fin κ.cf.k) = ⟨0, κ.cfK⟩ := Fin.ext h0
        rw [e] at hi
        have := congrArg Fin.val hi
        unfold QyKit.bCf at this
        rw [qyBank_zero, κ.tp_val] at this
        simp at this
        omega
      · have := congrArg Fin.val hi
        unfold QyKit.bCf at this
        rw [qyBank_val _ _ _ _ _ ⟨i, hlt⟩ h0] at this
        simp at this
        omega
    · rw [dif_neg hlt] at hi
      have := congrArg Fin.val hi
      rw [κ.tp_val] at this
      simp at this
      omega
  all_goals
    have := congrArg Fin.val h
    rw [κ.tp_val] at this
    simp at this
    omega

/-- A named tape other than `3` to `8` is off the round's scratch. -/
private theorem qy_not_scratch_tp {f g : ℕ → ℕ} (κ : QyKit f g) (c : Fin 16)
    (hc : (c : ℕ) < 3 ∨ 8 < (c : ℕ)) : ¬ qyScratch κ (κ.tp c) := by
  rintro (⟨i, hi⟩ | h | h | h | h)
  · unfold QyKit.bClk at hi
    rw [Function.Embedding.coeFn_mk] at hi
    by_cases hlt : (i : ℕ) < κ.cf.k
    · rw [dif_pos hlt] at hi
      by_cases h0 : (i : ℕ) = 0
      · have e : (⟨i, hlt⟩ : Fin κ.cf.k) = ⟨0, κ.cfK⟩ := Fin.ext h0
        rw [e] at hi
        have := congrArg Fin.val (κ.tp_inj.mp hi)
        simp at this
        omega
      · exact κ.bCf_ne ⟨i, hlt⟩ h0 c hi
    · rw [dif_neg hlt] at hi
      have := congrArg Fin.val (κ.tp_inj.mp hi)
      simp at this
      omega
  all_goals
    have := congrArg Fin.val (κ.tp_inj.mp h)
    simp at this
    omega

/-- A bank tape other than tape `0`, at an offset past `f`'s call bank, is off the scratch. -/
private theorem qy_bank_not_scratch {f g : ℕ → ℕ} (κ : QyKit f g) (t0 : Fin κ.K) (off k : ℕ)
    (hK : off + k ≤ κ.K) (h0 : (t0 : ℕ) < off) (hoff : 16 + κ.cb.k + κ.cf.k ≤ off) (i : Fin k)
    (hi : (i : ℕ) ≠ 0) : ¬ qyScratch κ (qyBank t0 off k hK h0 i) :=
  qy_not_scratch_ge κ _ (by rw [qyBank_val _ _ _ _ _ _ hi]; omega)

/-- An escape's tapes at a named tape off the scratch: the layout's word, its head at `0`. -/
private theorem QyEscT.tp {f g : ℕ → ℕ} {κ : QyKit f g} {n a j k : ℕ}
    {T : Fin κ.K → ℤ → Option Bool} {P : Fin κ.K → ℤ} (h : QyEscT κ n a j k T P) (c : Fin 16)
    (hc : (c : ℕ) < 3 ∨ 8 < (c : ℕ)) :
    T (κ.tp c) = FinTM.bufferTape (qyLay κ n a j k (κ.tp c)) ∧ P (κ.tp c) = 0 :=
  h _ (qy_not_scratch_tp κ c hc)

/-- An escape's tapes at a bank tape past `f`'s call bank: blank, its head at `0`. -/
private theorem QyEscT.bank {f g : ℕ → ℕ} {κ : QyKit f g} {n a j k : ℕ}
    {T : Fin κ.K → ℤ → Option Bool} {P : Fin κ.K → ℤ} (h : QyEscT κ n a j k T P) (t0 : Fin κ.K)
    (off kb : ℕ) (hK : off + kb ≤ κ.K) (h0 : (t0 : ℕ) < off) (hoff : 16 + κ.cb.k + κ.cf.k ≤ off)
    (i : Fin kb) (hi : (i : ℕ) ≠ 0) :
    T (qyBank t0 off kb hK h0 i) = FinTM.bufferTape [] ∧ P (qyBank t0 off kb hK h0 i) = 0 := by
  obtain ⟨e1, e2⟩ := h _ (qy_bank_not_scratch κ t0 off kb hK h0 hoff i hi)
  refine ⟨?_, e2⟩
  rw [e1]
  congr 1
  have hne : ∀ c : Fin 16, qyBank t0 off kb hK h0 i ≠ κ.tp c :=
    qyBank_ne_tp κ t0 off kb hK h0 (by omega) i hi
  simp [qyLay, hne]

/-- The length call's bank tapes other than tape `0` are off the named tapes. -/
private theorem QyKit.bCl_ne {f g : ℕ → ℕ} (κ : QyKit f g) (i : Fin κ.cl.k) (hi : (i : ℕ) ≠ 0)
    (c : Fin 16) : κ.bCl i ≠ κ.tp c := qyBank_ne_tp κ _ _ _ _ _ (by omega) i hi c

/-- **The stage code's calls after an escape** (checkpoint 5): on an escape's tapes with the input
head at `1`, the increment's call on the bank of tape `10` gives `1^{j + 1}`, and the length call
on the same tape then gives `bits (j + 1)` (the code `α` is its top bit dropped,
`stageCode_eq`), within `abA (j + 1)` and `clA (j + 2)` steps, each reaching its exit first at
its end.

**Proof sketch.** Two calls (`qy_callHost`), each bank holding the seam of its argument
(`qy_arg_bank`; the banks' other tapes blank by `QyEscT.bank`); `Function.update_idem` merges the
two writes to tape `10`. -/
private theorem qy_code_calls {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (a j k : ℕ)
    (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ) (hesc : QyEscT κ x.length a j k T P) :
    (∃ tb ≤ κ.abA * (j + 1),
      (embedEmitTM κ.bAbJ (seamReleaseTM κ.ab.tm κ.abE)).runFrom
          (qyC (x := x) (Sum.inl ()) 1 T P []) tb =
        qyC (Sum.inr κ.abX) 1 (Function.update T (κ.tp 10)
          (FinTM.bufferTape (List.replicate (j + 1) true))) P [] ∧
      ∀ u < tb, ((embedEmitTM κ.bAbJ (seamReleaseTM κ.ab.tm κ.abE)).runFrom
          (qyC (x := x) (Sum.inl ()) 1 T P []) u).state ≠ some (Sum.inr κ.abX)) ∧
    (∃ tc ≤ κ.clA * (j + 2),
      (embedEmitTM κ.bCl (seamReleaseTM κ.cl.tm κ.clE)).runFrom
          (qyC (x := x) (Sum.inl ()) 1 (Function.update T (κ.tp 10)
            (FinTM.bufferTape (List.replicate (j + 1) true))) P []) tc =
        qyC (Sum.inr κ.clX) 1 (Function.update T (κ.tp 10)
          (FinTM.bufferTape (Nat.bits (j + 1)))) P [] ∧
      ∀ u < tc, ((embedEmitTM κ.bCl (seamReleaseTM κ.cl.tm κ.clE)).runFrom
          (qyC (x := x) (Sum.inl ()) 1 (Function.update T (κ.tp 10)
            (FinTM.bufferTape (List.replicate (j + 1) true))) P []) u).state ≠
          some (Sum.inr κ.clX)) := by
  obtain ⟨hT10, hP10⟩ := hesc.tp 10 (by decide)
  have hJ : T (κ.tp 10) = FinTM.bufferTape (List.replicate j true) := by
    rw [hT10]
    simp [qyLay, QyKit.tp_inj]
  constructor
  · obtain ⟨tb, htb, hposb, hcutb, hrunb⟩ := κ.abS x (List.replicate j true)
    simp only [List.length_replicate] at htb
    have hb10 : κ.bAbJ ⟨0, κ.abK⟩ = κ.tp 10 := rfl
    have c := qy_callHost κ.ab κ.abK κ.bAbJ κ.abE κ.abX (List.replicate j true) _ tb hposb
      hcutb hrunb T P []
      (qy_arg_bank κ.bAbJ κ.abK T _ (by rw [hb10]; exact hJ)
        (fun i hi => (hesc.bank _ _ _ _ _ (by omega) i hi).1))
      (fun i => by
        by_cases hi : (i : ℕ) = 0
        · have e : i = ⟨0, κ.abK⟩ := Fin.ext hi
          rw [e, hb10]
          exact hP10
        · exact (hesc.bank _ _ _ _ _ (by omega) i hi).2)
    beta_reduce at c
    rw [hb10, ← List.replicate_succ'] at c
    exact ⟨tb, htb, c⟩
  · obtain ⟨tc, htc, hposc, hcutc, hrunc⟩ := κ.clS x (List.replicate (j + 1) true)
    simp only [List.length_replicate] at htc hrunc
    have hb10 : κ.bCl ⟨0, κ.clK⟩ = κ.tp 10 := rfl
    have c := qy_callHost κ.cl κ.clK κ.bCl κ.clE κ.clX (List.replicate (j + 1) true) _ tc hposc
      hcutc hrunc (Function.update T (κ.tp 10) (FinTM.bufferTape (List.replicate (j + 1) true)))
      P []
      (qy_arg_bank κ.bCl κ.clK _ _ (by rw [hb10]; simp)
        (fun i hi => by
          rw [Function.update_of_ne (κ.bCl_ne i hi 10)]
          exact (hesc.bank _ _ _ _ _ (by omega) i hi).1))
      (fun i => by
        by_cases hi : (i : ℕ) = 0
        · have e : i = ⟨0, κ.clK⟩ := Fin.ext hi
          rw [e, hb10]
          exact hP10
        · exact (hesc.bank _ _ _ _ _ (by omega) i hi).2)
    rw [hb10, Function.update_idem] at c
    exact ⟨tc, by omega, c⟩

/-- **The input seek after an escape** (checkpoint 5): on an escape's tapes, from any input
head position, the seek on tapes `12` and `13` (`[true]`, worth `1`, and a blank tape) returns
the input head to `1` within `rC (n + 4)` steps, every work tape and head unchanged.

**Proof sketch.** `qy_seekHost` on the kit's seek clause, its two tapes read off `QyEscT.tp`;
`ip ≤ n + 1` bounds its time. -/
private theorem qy_seek_run {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (a j k : ℕ)
    (ip : Fin (x.length + 2)) (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ)
    (hesc : QyEscT κ x.length a j k T P) :
    ∃ t ≤ κ.rC * (x.length + 4),
      (embedEmitTM (qyEmb2 (κ.tp 12) (κ.tp 13) (κ.tp_ne (by decide))) κ.R).runFrom
          (qyC (x := x) κ.rE ip T P []) t = qyC κ.rX 1 T P [] ∧
      ∀ u < t, ((embedEmitTM (qyEmb2 (κ.tp 12) (κ.tp 13) (κ.tp_ne (by decide))) κ.R).runFrom
          (qyC (x := x) κ.rE ip T P []) u).state ≠ some κ.rX := by
  obtain ⟨hT12, hP12⟩ := hesc.tp 12 (by decide)
  obtain ⟨hT13, -⟩ := hesc.tp 13 (by decide)
  obtain ⟨t, ht, hrun⟩ := qy_seekHost κ.R κ.rE κ.rX κ.rC (κ.rS (x := x))
    (qyEmb2 (κ.tp 12) (κ.tp 13) (κ.tp_ne (by decide))) (κ.tp 12) (κ.tp 13) rfl rfl ip T P []
    (by rw [hT12]; simp [qyLay, QyKit.tp_inj]) hP12 (by rw [hT13]; simp [qyLay, QyKit.tp_inj])
  refine ⟨t, ht.trans (Nat.mul_le_mul_left _ ?_), hrun⟩
  have := ip.isLt
  omega

/-- **The middle writer's head** (checkpoint 5): from its entry on an escape's tapes, the input
seek, the increment of `j` and the length call reach the budget's call with the input head at `1`
and `bits (j + 1)` on tape `10`.

**Proof sketch.** Three hosted phases (`qy_hosted`): `qy_seek_run`, then `qy_code_calls`' two
calls, each guard its cut (`qy_guard_of_cut`). -/
private theorem qy_mid_code {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (a j k : ℕ)
    (ip : Fin (x.length + 2)) (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ)
    (hesc : QyEscT κ x.length a j k T P) :
    ∃ t ≤ κ.rC * (x.length + 4) + κ.abA * (j + 1) + κ.clA * (j + 2) + 3,
      Segment (qyMid κ) ∅ (fun _ => True) (qyC (x := x) ⟨.m0, κ.rE⟩ ip T P [])
        (qyC ⟨.m3, Sum.inl ()⟩ 1 (Function.update T (κ.tp 10)
          (FinTM.bufferTape (Nat.bits (j + 1)))) P []) t := by
  unfold qyMid
  obtain ⟨t0, ht0, c0⟩ := qy_seek_run κ (x := x) a j k ip T P hesc
  have seg0 := qy_hosted (qyMidM κ) ⟨.m0, κ.rE⟩ (qyMidRed κ) .m0 κ.rE κ.rX ⟨.m1, Sum.inl ()⟩ ip 1
    T T P P [] [] t0 c0.1 (by simp [qyMidRed])
    (qy_guard_of_cut κ.rX (qyMidRed κ .m0) (fun s hs => by simp [qyMidRed, hs]) c0.2) ∅
    (fun _ h => h)
  obtain ⟨⟨tb, htb, c1⟩, ⟨tc, htc, c2⟩⟩ := qy_code_calls κ (x := x) a j k T P hesc
  have seg1 := qy_hosted (qyMidM κ) ⟨.m0, κ.rE⟩ (qyMidRed κ) .m1 (Sum.inl ()) (Sum.inr κ.abX)
    ⟨.m2, Sum.inl ()⟩ 1 1 T _ P P [] [] tb c1.1 (by simp [qyMidRed])
    (qy_guard_of_cut (Sum.inr κ.abX) (qyMidRed κ .m1) (fun s hs => by simp [qyMidRed, hs]) c1.2)
    ∅ (fun _ h => h)
  have seg2 := qy_hosted (qyMidM κ) ⟨.m0, κ.rE⟩ (qyMidRed κ) .m2 (Sum.inl ()) (Sum.inr κ.clX)
    ⟨.m3, Sum.inl ()⟩ 1 1 _ _ P P [] [] tc c2.1 (by simp [qyMidRed])
    (qy_guard_of_cut (Sum.inr κ.clX) (qyMidRed κ .m2) (fun s hs => by simp [qyMidRed, hs]) c2.2)
    ∅ (fun _ h => h)
  exact ⟨_, by omega, seg0.trans (seg1.trans seg2)⟩

/-- **The top writer's head** (checkpoint 5): from its entry on an escape's tapes with the input
head at `1`, the increment of `j` and the length call reach the budget's call with
`bits (j + 1)` on tape `10`.

**Proof sketch.** Two hosted phases (`qy_hosted`): `qy_code_calls`' two calls. -/
private theorem qy_top_code {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (a j k : ℕ)
    (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ) (hesc : QyEscT κ x.length a j k T P) :
    ∃ t ≤ κ.abA * (j + 1) + κ.clA * (j + 2) + 2,
      Segment (qyTop κ) ∅ (fun _ => True) (qyC (x := x) ⟨.t1, Sum.inl ()⟩ 1 T P [])
        (qyC ⟨.t3, Sum.inl ()⟩ 1 (Function.update T (κ.tp 10)
          (FinTM.bufferTape (Nat.bits (j + 1)))) P []) t := by
  unfold qyTop
  obtain ⟨⟨tb, htb, c1⟩, ⟨tc, htc, c2⟩⟩ := qy_code_calls κ (x := x) a j k T P hesc
  have seg1 := qy_hosted (qyTopM κ) ⟨.t1, Sum.inl ()⟩ (qyTopRed κ) .t1 (Sum.inl ())
    (Sum.inr κ.abX) ⟨.t2, Sum.inl ()⟩ 1 1 T _ P P [] [] tb c1.1 (by simp [qyTopRed])
    (qy_guard_of_cut (Sum.inr κ.abX) (qyTopRed κ .t1) (fun s hs => by simp [qyTopRed, hs]) c1.2)
    ∅ (fun _ h => h)
  have seg2 := qy_hosted (qyTopM κ) ⟨.t1, Sum.inl ()⟩ (qyTopRed κ) .t2 (Sum.inl ())
    (Sum.inr κ.clX) ⟨.t3, Sum.inl ()⟩ 1 1 _ _ P P [] [] tc c2.1 (by simp [qyTopRed])
    (qy_guard_of_cut (Sum.inr κ.clX) (qyTopRed κ .t2) (fun s hs => by simp [qyTopRed, hs]) c2.2)
    ∅ (fun _ h => h)
  exact ⟨_, by omega, seg1.trans seg2⟩

/-! ### The budget field and the writer -/

/-- Doubling twice is quadrupling: `(B.flatMap dbl).flatMap dbl = B.flatMap (replicate 4)`. -/
private theorem qy_flatMap_dbl_dbl (B : List Bool) :
    ((B.flatMap fun b => [b, b]).flatMap fun b => [b, b]) =
      B.flatMap fun b => List.replicate (3 + 1) b := by
  induction B with
  | nil => rfl
  | cons b B ih =>
    rw [List.flatMap_cons, List.flatMap_append, ih, List.flatMap_cons]
    rfl

/-- **The writer's word** (L6's three emissions): the flag, the budget field's bits each written
four times and `[false, false, true, true]`; the code's bits but the top one, doubled, and
`[false, true]`; the tail. It is `b :: pairEncode (pairEncode B W.dropLast) N`. -/
private theorem qy_writer_word (b : Bool) (B W N : List Bool) :
    ((([] ++ [b] ++ qyBody false 3 B ++ [false, false, true, true]) ++ [] ++ qyBody true 1 W ++
      [false, true]) ++ [] ++ qyBody false 0 N ++ []) =
      b :: pairEncode (pairEncode B W.dropLast) N := by
  have hN : (N.flatMap fun b => List.replicate (0 + 1) b) = N := by
    induction N with
    | nil => rfl
    | cons c N ih =>
      rw [List.flatMap_cons, ih]
      rfl
  have hW : (W.dropLast.flatMap fun b => List.replicate (1 + 1) b) =
      W.dropLast.flatMap fun b => [b, b] := rfl
  unfold qyBody
  rw [if_neg Bool.false_ne_true, if_pos rfl, if_neg Bool.false_ne_true, hN, hW, pairEncode_eq,
    pairEncode_eq, List.flatMap_append, List.flatMap_append, qy_flatMap_dbl_dbl]
  simp

/-- **A hosted phase that halts**: if phase `k` halts at time `t`, with no redirect before, the
host halts at `t` with the phase's output. -/
private theorem qy_hosted_halt {K : ℕ} {I : Type} {Ph : I → Type}
    (M : (i : I) → MultiTapeTM K Bool (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (k : I) {x : List Bool} (e : Ph k)
    (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool)
    (t : ℕ) (c' : Cfg K Bool (Ph k) x) (h : (M k).runFrom (qyC e ip T P o) t = c')
    (hc : c'.state = none)
    (hguard : ∀ u < t, ∀ s, ((M k).runFrom (qyC e ip T P o) u).state = some s → red k s = none) :
    ((phaseHostTM M q0 red).runFrom (qyC ⟨k, e⟩ ip T P o) t).state = none ∧
      ((phaseHostTM M q0 red).runFrom (qyC ⟨k, e⟩ ip T P o) t).output = c'.output := by
  have H := phaseHostTM_run_le M q0 red k (qyC e ip T P o) t hguard t le_rfl
  rw [qyC_mapState] at H
  rw [H, h, Cfg.mapState_state, Cfg.mapState_output, hc]
  exact ⟨rfl, rfl⟩

/-- An emitter's run to its halt: the run of `qy_emit_run` and one more step (`qy_emit_halt`). -/
private theorem qy_emit_stop {K : ℕ} {x : List Bool} (i : Fin K) (pre suf : List Bool) (rr : ℕ)
    (dl : Bool) (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ)
    (o : List Bool) (w : List Bool) (hT : T i = FinTM.bufferTape w) (hP : P i = 0) :
    ∃ t ≤ pre.length + suf.length + 4 + w.length * (rr + 3),
      ((qyEmitTM K i pre suf rr dl).runFrom (qyC (.pre 0) ip T P o) t).state = none ∧
      ((qyEmitTM K i pre suf rr dl).runFrom (qyC (.pre 0) ip T P o) t).output =
        o ++ pre ++ qyBody dl rr w ++ suf := by
  obtain ⟨t, ht, hrun, -⟩ := qy_emit_run (x := x) i pre suf rr dl ip T P o w hT hP
  have h1 := qy_emit_halt (x := x) i pre suf rr dl ip T
    (Function.update P i w.length) (o ++ pre ++ qyBody dl rr w ++ suf)
  refine ⟨t + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, hrun]
  exact h1

/-- `g`'s call bank tapes other than tape `0` are off the named tapes. -/
private theorem QyKit.bCg_ne {f g : ℕ → ℕ} (κ : QyKit f g) (i : Fin κ.cg.k) (hi : (i : ℕ) ≠ 0)
    (c : Fin 16) : κ.bCg i ≠ κ.tp c := qyBank_ne_tp κ _ _ _ _ _ (by omega) i hi c

/-- The square's call bank tapes other than tape `0` are off the named tapes. -/
private theorem QyKit.bPb_ne {f g : ℕ → ℕ} (κ : QyKit f g) (i : Fin κ.pb.k) (hi : (i : ℕ) ≠ 0)
    (c : Fin 16) : κ.bPb i ≠ κ.tp c := qyBank_ne_tp κ _ _ _ _ _ (by omega) i hi c

/-- The middle writer's time bound: the seek, the code's calls, `g`'s call and the emissions. -/
private def qyMidB {f g : ℕ → ℕ} (κ : QyKit f g) (n j : ℕ) : ℕ :=
  κ.rC * (n + 4) + κ.abA * (j + 1) + κ.clA * (j + 2) + κ.cgA * (g n + 1) + 6 * g n +
    4 * (j + 1) + 3 * (n + 1) + 30

/-- The top writer's time bound: the code's calls, the square's call on `1^{X - 1}` and the
emissions. -/
private def qyTopB {f g : ℕ → ℕ} (κ : QyKit f g) (X a j : ℕ) : ℕ :=
  κ.abA * (j + 1) + κ.clA * (j + 2) + κ.pbA * X ^ 3 + 6 * X ^ 2 + 4 * (j + 1) + 3 * a + 30

/-- **The middle writer** (checkpoint 6): from its entry on an escape's tapes, it halts within
`qyMidB` steps with the output `false :: ⟨⟨bits (g n), α⟩, 1^{n + 1}⟩`, `α` the bits of `j + 1`
but the top one.

**Proof sketch.** The head (`qy_mid_code`), then `g`'s input call (`qy_callHost` from the blank
seam, `qy_blank_bank`) and the three emissions (`qy_emit_run`, the last to its halt by
`qy_emit_stop` and `qy_hosted_halt`): `bits (g n)` each four times between the flag `false` and
`[false, false, true, true]`; `bits (j + 1)` but its top bit, doubled, and `[false, true]`; the
tail `1^{n + 1}` from tape `0`. The output is the word by `qy_writer_word`. -/
private theorem qy_mid_run {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (a j k : ℕ)
    (ip : Fin (x.length + 2)) (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ)
    (hesc : QyEscT κ x.length a j k T P) :
    ∃ t ≤ qyMidB κ x.length j,
      ((qyMid κ).runFrom (qyC (x := x) ⟨.m0, κ.rE⟩ ip T P []) t).state = none ∧
      ((qyMid κ).runFrom (qyC (x := x) ⟨.m0, κ.rE⟩ ip T P []) t).output =
        false :: pairEncode (pairEncode (Nat.bits (g x.length)) (Nat.bits (j + 1)).dropLast)
          (List.replicate (x.length + 1) true) := by
  obtain ⟨t0, ht0, seg0⟩ := qy_mid_code κ (x := x) a j k ip T P hesc
  obtain ⟨hT14, hP14⟩ := hesc.tp 14 (by decide)
  obtain ⟨hT0, hP0⟩ := hesc.tp 0 (by decide)
  obtain ⟨-, hP10⟩ := hesc.tp 10 (by decide)
  set T₂ := Function.update T (κ.tp 10) (FinTM.bufferTape (Nat.bits (j + 1))) with hT₂
  unfold qyMid at seg0 ⊢
  -- m3: g's input call
  obtain ⟨t3, ht3, hpos3, hcut3, hrun3⟩ := κ.cgS x
  have hb14 : κ.bCg ⟨0, κ.cgK⟩ = κ.tp 14 := rfl
  have c3 := qy_callHost κ.cg κ.cgK κ.bCg κ.cgE κ.cgX [] _ t3 hpos3 hcut3 hrun3 T₂ P []
    (qy_blank_bank κ.bCg T₂ fun i => by
      by_cases hi : (i : ℕ) = 0
      · have e : i = ⟨0, κ.cgK⟩ := Fin.ext hi
        rw [e, hb14, hT₂, Function.update_of_ne (κ.tp_ne (by decide)), hT14]
        simp [qyLay, QyKit.tp_inj]
      · rw [hT₂, Function.update_of_ne (κ.bCg_ne i hi 10)]
        exact (hesc.bank _ _ _ _ _ (by omega) i hi).1)
    (fun i => by
      by_cases hi : (i : ℕ) = 0
      · have e : i = ⟨0, κ.cgK⟩ := Fin.ext hi
        rw [e, hb14]
        exact hP14
      · exact (hesc.bank _ _ _ _ _ (by omega) i hi).2)
  rw [hb14] at c3
  set T₃ := Function.update T₂ (κ.tp 14) (FinTM.bufferTape (Nat.bits (g x.length))) with hT₃
  have seg3 := qy_hosted (qyMidM κ) ⟨.m0, κ.rE⟩ (qyMidRed κ) .m3 (Sum.inl ()) (Sum.inr κ.cgX)
    ⟨.m4, QyEm.pre 0⟩ 1 1 T₂ T₃ P P [] [] t3 c3.1 (by simp [qyMidRed])
    (qy_guard_of_cut (Sum.inr κ.cgX) (qyMidRed κ .m3) (fun s hs => by simp [qyMidRed, hs]) c3.2)
    ∅ (fun _ h => h)
  -- m4: the flag, the budget field four times, the inner separator
  obtain ⟨t4, ht4, c4, hcut4⟩ := qy_emit_run (x := x) (κ.tp 14) [false] [false, false, true, true]
    3 false 1 T₃ P [] (Nat.bits (g x.length)) (by simp [hT₃]) hP14
  set P₄ := Function.update P (κ.tp 14) ((Nat.bits (g x.length)).length : ℤ) with hP₄
  have seg4 := qy_hosted (qyMidM κ) ⟨.m0, κ.rE⟩ (qyMidRed κ) .m4 (.pre 0) .done
    ⟨.m5, QyEm.pre 0⟩ 1 1 T₃ T₃ P P₄ [] _ t4 c4 (by simp [qyMidRed])
    (qy_guard_of_cut QyEm.done (qyMidRed κ .m4) (fun s hs => by simp [qyMidRed, hs]) hcut4)
    ∅ (fun _ h => h)
  -- m5: the code doubled, the outer separator
  obtain ⟨t5, ht5, c5, hcut5⟩ := qy_emit_run (x := x) (κ.tp 10) [] [false, true] 1 true 1 T₃ P₄
    _ (Nat.bits (j + 1)) (by simp [hT₃, hT₂, QyKit.tp_inj])
    (by rw [hP₄, Function.update_of_ne (κ.tp_ne (by decide))]; exact hP10)
  set P₅ := Function.update P₄ (κ.tp 10) ((Nat.bits (j + 1)).length : ℤ) with hP₅
  have seg5 := qy_hosted (qyMidM κ) ⟨.m0, κ.rE⟩ (qyMidRed κ) .m5 (.pre 0) .done
    ⟨.m6, QyEm.pre 0⟩ 1 1 T₃ T₃ P₄ P₅ _ _ t5 c5 (by simp [qyMidRed])
    (qy_guard_of_cut QyEm.done (qyMidRed κ .m5) (fun s hs => by simp [qyMidRed, hs]) hcut5)
    ∅ (fun _ h => h)
  -- m6: the tail 1^{n+1}, and the halt
  obtain ⟨t6, ht6, c6, c6o⟩ := qy_emit_stop (x := x) (κ.tp 0) [] [] 0 false 1 T₃ P₅ _
    (List.replicate (x.length + 1) true)
    (by
      rw [hT₃, Function.update_of_ne (κ.tp_ne (by decide)), hT₂,
        Function.update_of_ne (κ.tp_ne (by decide)), hT0]
      simp [qyLay])
    (by
      rw [hP₅, Function.update_of_ne (κ.tp_ne (by decide)), hP₄,
        Function.update_of_ne (κ.tp_ne (by decide))]
      exact hP0)
  have h6 := qy_hosted_halt (qyMidM κ) ⟨.m0, κ.rE⟩ (qyMidRed κ) .m6 (.pre 0) 1 T₃ P₅ _ t6 _ rfl
    c6 (fun _ _ _ _ => by simp [qyMidRed])
  have hseg := (segment_iff _ _ _ _ _ _).mp (seg0.trans (seg3.trans (seg4.trans seg5)))
  refine ⟨t0 + (t3 + 1 + (t4 + 1 + (t5 + 1))) + t6, ?_, ?_⟩
  · have hbg := length_bits_le_self (g x.length)
    have hbj := length_bits_le_self (j + 1)
    have ht3' : t3 ≤ κ.cgA * (g x.length + 1) := ht3
    unfold qyMidB
    simp only [List.length_cons, List.length_nil] at ht4 ht5 ht6
    have e4 : (Nat.bits (g x.length)).length * (3 + 3) ≤ 6 * g x.length := by omega
    have e5 : (Nat.bits (j + 1)).length * (1 + 3) ≤ 4 * (j + 1) := by omega
    have e6 : (List.replicate (x.length + 1) true).length * (0 + 3) = 3 * (x.length + 1) := by
      simp [mul_comm]
    omega
  · rw [MultiTapeTM.runFrom_add, hseg.1]
    refine ⟨h6.1, ?_⟩
    rw [h6.2, c6o, qy_writer_word]

/-- **The top writer** (checkpoint 6): from its entry on an escape's tapes with `1^{F + a}` on
tape `4` (`F = f a`, `a` the rung), it halts within `qyTopB` steps with the output
`true :: ⟨⟨bits ((F + a + 1)²), α⟩, 1^a⟩`.

**Proof sketch.** The head (`qy_top_code`), then the square's call on tape `4`
(`qy_callHost`, `1^{F + a} ↦ bits ((F + a + 1)²)`) and the three emissions, as in
`qy_mid_run`, with the flag `true` and the tail `1^a` from the rung's tape `2`. -/
private theorem qy_top_run {f g : ℕ → ℕ} (κ : QyKit f g) {x : List Bool} (a j k : ℕ)
    (T : Fin κ.K → ℤ → Option Bool) (P : Fin κ.K → ℤ) (hesc : QyEscT κ x.length a j k T P)
    (h4 : T (κ.tp 4) = FinTM.bufferTape (List.replicate (f a + a) true)) (hP4 : P (κ.tp 4) = 0) :
    ∃ t ≤ qyTopB κ (f a + a + 1) a j,
      ((qyTop κ).runFrom (qyC (x := x) ⟨.t1, Sum.inl ()⟩ 1 T P []) t).state = none ∧
      ((qyTop κ).runFrom (qyC (x := x) ⟨.t1, Sum.inl ()⟩ 1 T P []) t).output =
        true :: pairEncode (pairEncode (Nat.bits ((f a + a + 1) ^ 2)) (Nat.bits (j + 1)).dropLast)
          (List.replicate a true) := by
  obtain ⟨t0, ht0, seg0⟩ := qy_top_code κ (x := x) a j k T P hesc
  obtain ⟨hT2, hP2⟩ := hesc.tp 2 (by decide)
  obtain ⟨-, hP10⟩ := hesc.tp 10 (by decide)
  set T₂ := Function.update T (κ.tp 10) (FinTM.bufferTape (Nat.bits (j + 1))) with hT₂
  unfold qyTop at seg0 ⊢
  -- t3: the square's call on 1^{F + a}
  obtain ⟨t3, ht3, hpos3, hcut3, hrun3⟩ := κ.pbS x (List.replicate (f a + a) true)
  simp only [List.length_replicate] at ht3 hrun3
  have hb4 : κ.bPb ⟨0, κ.pbK⟩ = κ.tp 4 := rfl
  have c3 := qy_callHost κ.pb κ.pbK κ.bPb κ.pbE κ.pbX (List.replicate (f a + a) true) _ t3 hpos3
    hcut3 hrun3 T₂ P []
    (qy_arg_bank κ.bPb κ.pbK T₂ _
      (by rw [hb4, hT₂, Function.update_of_ne (κ.tp_ne (by decide))]; exact h4)
      (fun i hi => by
        rw [hT₂, Function.update_of_ne (κ.bPb_ne i hi 10)]
        exact (hesc.bank _ _ _ _ _ (by omega) i hi).1))
    (fun i => by
      by_cases hi : (i : ℕ) = 0
      · have e : i = ⟨0, κ.pbK⟩ := Fin.ext hi
        rw [e, hb4]
        exact hP4
      · exact (hesc.bank _ _ _ _ _ (by omega) i hi).2)
  rw [hb4] at c3
  set T₃ := Function.update T₂ (κ.tp 4) (FinTM.bufferTape (Nat.bits ((f a + a + 1) ^ 2)))
    with hT₃
  have seg3 := qy_hosted (qyTopM κ) ⟨.t1, Sum.inl ()⟩ (qyTopRed κ) .t3 (Sum.inl ())
    (Sum.inr κ.pbX) ⟨.t4, QyEm.pre 0⟩ 1 1 T₂ T₃ P P [] [] t3 c3.1 (by simp [qyTopRed])
    (qy_guard_of_cut (Sum.inr κ.pbX) (qyTopRed κ .t3) (fun s hs => by simp [qyTopRed, hs]) c3.2)
    ∅ (fun _ h => h)
  -- t4: the flag, the budget field four times, the inner separator
  obtain ⟨t4, ht4, c4, hcut4⟩ := qy_emit_run (x := x) (κ.tp 4) [true] [false, false, true, true]
    3 false 1 T₃ P [] (Nat.bits ((f a + a + 1) ^ 2)) (by simp [hT₃]) hP4
  set P₄ := Function.update P (κ.tp 4) ((Nat.bits ((f a + a + 1) ^ 2)).length : ℤ) with hP₄
  have seg4 := qy_hosted (qyTopM κ) ⟨.t1, Sum.inl ()⟩ (qyTopRed κ) .t4 (.pre 0) .done
    ⟨.t5, QyEm.pre 0⟩ 1 1 T₃ T₃ P P₄ [] _ t4 c4 (by simp [qyTopRed])
    (qy_guard_of_cut QyEm.done (qyTopRed κ .t4) (fun s hs => by simp [qyTopRed, hs]) hcut4)
    ∅ (fun _ h => h)
  -- t5: the code doubled, the outer separator
  obtain ⟨t5, ht5, c5, hcut5⟩ := qy_emit_run (x := x) (κ.tp 10) [] [false, true] 1 true 1 T₃ P₄
    _ (Nat.bits (j + 1)) (by simp [hT₃, hT₂, QyKit.tp_inj])
    (by rw [hP₄, Function.update_of_ne (κ.tp_ne (by decide))]; exact hP10)
  set P₅ := Function.update P₄ (κ.tp 10) ((Nat.bits (j + 1)).length : ℤ) with hP₅
  have seg5 := qy_hosted (qyTopM κ) ⟨.t1, Sum.inl ()⟩ (qyTopRed κ) .t5 (.pre 0) .done
    ⟨.t6, QyEm.pre 0⟩ 1 1 T₃ T₃ P₄ P₅ _ _ t5 c5 (by simp [qyTopRed])
    (qy_guard_of_cut QyEm.done (qyTopRed κ .t5) (fun s hs => by simp [qyTopRed, hs]) hcut5)
    ∅ (fun _ h => h)
  -- t6: the tail 1^a from the rung, and the halt
  obtain ⟨t6, ht6, c6, c6o⟩ := qy_emit_stop (x := x) (κ.tp 2) [] [] 0 false 1 T₃ P₅ _
    (List.replicate a true)
    (by
      rw [hT₃, Function.update_of_ne (κ.tp_ne (by decide)), hT₂,
        Function.update_of_ne (κ.tp_ne (by decide)), hT2]
      simp [qyLay, QyKit.tp_inj])
    (by
      rw [hP₅, Function.update_of_ne (κ.tp_ne (by decide)), hP₄,
        Function.update_of_ne (κ.tp_ne (by decide))]
      exact hP2)
  have h6 := qy_hosted_halt (qyTopM κ) ⟨.t1, Sum.inl ()⟩ (qyTopRed κ) .t6 (.pre 0) 1 T₃ P₅ _ t6 _
    rfl c6 (fun _ _ _ _ => by simp [qyTopRed])
  have hseg := (segment_iff _ _ _ _ _ _).mp (seg0.trans (seg3.trans (seg4.trans seg5)))
  refine ⟨t0 + (t3 + 1 + (t4 + 1 + (t5 + 1))) + t6, ?_, ?_⟩
  · have hbX := length_bits_le_self ((f a + a + 1) ^ 2)
    have hbj := length_bits_le_self (j + 1)
    unfold qyTopB
    simp only [List.length_cons, List.length_nil] at ht4 ht5 ht6
    have e4 : (Nat.bits ((f a + a + 1) ^ 2)).length * (3 + 3) ≤ 6 * (f a + a + 1) ^ 2 := by
      omega
    have e5 : (Nat.bits (j + 1)).length * (1 + 3) ≤ 4 * (j + 1) := by omega
    have e6 : (List.replicate a true).length * (0 + 3) = 3 * a := by simp [mul_comm]
    omega
  · rw [MultiTapeTM.runFrom_add, hseg.1]
    refine ⟨h6.1, ?_⟩
    rw [h6.2, c6o, qy_writer_word]

/-! ### The main machine `M₁` -/

/-- `M₁`'s initial configuration is the blank seam at the setup's entry. -/
private theorem qy_initCfg {f g : ℕ → ℕ} (κ : QyKit f g) (x : List Bool) :
    (qyM₁ κ).tm.initCfg x =
      qyC ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ 1 (fun _ => FinTM.bufferTape []) (fun _ => 0) [] := by
  rw [initCfg_ofWords]
  show Cfg.ofWords (phaseHostTM (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ)).q₀
    (fun _ => []) = _
  rw [phaseHostTM_q₀]
  apply Cfg.ext
  · rw [Cfg.ofWords_state]
    rfl
  · rw [Cfg.ofWords_inputPos]
    rfl
  · funext j q
    rw [Cfg.ofWords_workTapes]
    rfl
  · funext j
    rw [Cfg.ofWords_workTapePos]
    rfl
  · rw [Cfg.ofWords_output]
    rfl

/-- `M₁` dispatches from its setup only at the setup's exits. -/
private theorem qy_mainRed_setup {f g : ℕ → ℕ} (κ : QyKit f g) (s : Σ i, QySPh κ i)
    (hs : some s ∉ qySetF κ) : qyMainRed κ .setup s = none := by
  rcases s with ⟨i, s⟩
  cases i
  case s10 =>
    have : s ≠ SweepPhase.done := fun h => hs (by subst h; simp [qySetF])
    simp [qyMainRed, this]
  case s6 =>
    have h1 : s ≠ QyCmp.done .lt := fun h => hs (by subst h; simp [qySetF])
    have h2 : s ≠ QyCmp.done .eq := fun h => hs (by subst h; simp [qySetF])
    simp [qyMainRed, h1, h2]
  all_goals simp [qyMainRed]

/-- `M₁` dispatches from its locator only at the locator's escapes. -/
private theorem qy_mainRed_loc {f g : ℕ → ℕ} (κ : QyKit f g) (s : Σ i, QyLPh κ i)
    (hs : some s ∉ qyLocE κ) : qyMainRed κ .loc s = none := by
  rcases s with ⟨i, s⟩
  have he : i.isEsc = false := by
    by_contra h
    exact hs ⟨_, rfl, by simpa using h⟩
  cases i <;> simp_all [qyMainRed, QyLK.isEsc]

/-- The writers' constant: the coefficient of `g n + 1` in either writer. -/
private def qyWk {f g : ℕ → ℕ} (κ : QyKit f g) : ℕ :=
  4 * κ.rC + κ.abA + 2 * κ.clA + κ.cgA + κ.pbA + 60

/-- `M₁`'s constant `A`: the setup's, the locator's and the writers'. -/
private def qyMainA {f g : ℕ → ℕ} (κ : QyKit f g) : ℕ :=
  (κ.cbA + κ.prA + 2 * (Nat.bits (κ.cfA * (κ.cfc + 2))).length + 60) + qyLoopA κ + qyWk κ + 8

/-- The middle writer's bound is linear in `g n + 1` when `j ≤ n ≤ g n`. -/
private theorem qy_midB_le {f g : ℕ → ℕ} (κ : QyKit f g) (n j : ℕ) (hj : j ≤ n) (hg : n ≤ g n) :
    qyMidB κ n j ≤ qyWk κ * (g n + 1) := by
  unfold qyMidB qyWk
  have e1 : κ.rC * (n + 4) ≤ 4 * (κ.rC * (g n + 1)) := by
    calc κ.rC * (n + 4) ≤ κ.rC * (4 * (g n + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * (κ.rC * (g n + 1)) := by ring
  have e2 : κ.abA * (j + 1) ≤ κ.abA * (g n + 1) := Nat.mul_le_mul_left _ (by omega)
  have e3 : κ.clA * (j + 2) ≤ 2 * (κ.clA * (g n + 1)) := by
    calc κ.clA * (j + 2) ≤ κ.clA * (2 * (g n + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (κ.clA * (g n + 1)) := by ring
  have e4 : κ.pbA * 0 ≤ κ.pbA * (g n + 1) := Nat.mul_le_mul_left _ (by omega)
  have e5 : (4 * κ.rC + κ.abA + 2 * κ.clA + κ.cgA + κ.pbA + 60) * (g n + 1) =
      4 * (κ.rC * (g n + 1)) + κ.abA * (g n + 1) + 2 * (κ.clA * (g n + 1)) +
        κ.cgA * (g n + 1) + κ.pbA * (g n + 1) + 60 * (g n + 1) := by ring
  rw [e5]
  omega

/-- The top writer's bound is linear in `n + 1` when `X³, X², a, j ≤ n`. -/
private theorem qy_topB_le {f g : ℕ → ℕ} (κ : QyKit f g) (n X a j : ℕ) (hX3 : X ^ 3 ≤ n)
    (hX2 : X ^ 2 ≤ n) (ha : a ≤ n) (hj : j ≤ n) :
    qyTopB κ X a j ≤ qyWk κ * (n + 1) := by
  unfold qyTopB qyWk
  have e2 : κ.abA * (j + 1) ≤ κ.abA * (n + 1) := Nat.mul_le_mul_left _ (by omega)
  have e3 : κ.clA * (j + 2) ≤ 2 * (κ.clA * (n + 1)) := by
    calc κ.clA * (j + 2) ≤ κ.clA * (2 * (n + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (κ.clA * (n + 1)) := by ring
  have e4 : κ.pbA * X ^ 3 ≤ κ.pbA * (n + 1) := Nat.mul_le_mul_left _ (by omega)
  have e5 : (4 * κ.rC + κ.abA + 2 * κ.clA + κ.cgA + κ.pbA + 60) * (n + 1) =
      4 * (κ.rC * (n + 1)) + κ.abA * (n + 1) + 2 * (κ.clA * (n + 1)) +
        κ.cgA * (n + 1) + κ.pbA * (n + 1) + 60 * (n + 1) := by ring
  rw [e5]
  omega

/-- **`M₁` on inputs of length `n ≥ 3`** (checkpoint 7): from its initial configuration it halts
within `qyMainA (g n + 1)` steps with the stage query of `1ⁿ` as its output.

**Proof sketch.** Three hosted phases of `M₁` (`qy_hosted`, each guard read off the phase's
segment by `qy_mainRed_setup`, `qy_mainRed_loc`): the setup (`qy_setup_long`), the locator
(`qy_loop`), and the writer its escape selects, run to its halt (`qy_mid_run` or `qy_top_run`,
then `qy_hosted_halt`). The output is `query_eq`'s word: in the middle `n < ℓ_{s+1}`, at the top
`n = ℓ_{s+1}` with `X² = budget f ℓ_s` (`budget_eq`), the code `stageCode_eq`. The time: the
setup's `qySetB`, the locator's `qyLoopA (n + 1)`, the writer's (`qy_midB_le`, `qy_topB_le`, with
`j ≤ s < n` and, at the top, `X⁴ < 2 ^ X⁴ = n`), and `n ≤ g n`. -/
private theorem qy_main_long {f g : ℕ → ℕ} (κ : QyKit f g) (hle : ∀ n, n ≤ g n) {x : List Bool}
    (hn : 3 ≤ x.length) :
    ∃ t ≤ qyMainA κ * (g x.length + 1),
      ((qyM₁ κ).tm.runFrom ((qyM₁ κ).tm.initCfg x) t).state = none ∧
      ((qyM₁ κ).tm.runFrom ((qyM₁ κ).tm.initCfg x) t).output =
        query f g (List.replicate x.length true) := by
  rw [qy_initCfg]
  show ∃ t ≤ _, ((phaseHostTM (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ)).runFrom
    _ t).state = none ∧ ((phaseHostTM (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩
      (qyMainRed κ)).runFrom _ t).output = _
  -- the setup
  obtain ⟨t1, ht1, seg1⟩ := qy_setup_long κ hn
  obtain ⟨h1, hc1, -⟩ := (segment_iff _ _ _ _ _ _).mp seg1
  have hs1 := qy_hosted (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ) .setup
    ⟨.s1, Sum.inl ()⟩ ⟨.s10, SweepPhase.done⟩ ⟨.loc, ⟨.anc, SweepPhase.sweep⟩⟩ 1 1 _ _ _ _ [] []
    t1 h1 (by simp [qyMainRed]) (fun u hu s hs => qy_mainRed_setup κ s (hs ▸ hc1 u hu)) ∅
    (fun _ h => h)
  -- the locator
  obtain ⟨t2, ht2, c', seg2, hcase⟩ := qy_loop κ hn
  have hq0 : qyAt κ x 0 = qyC ⟨.anc, SweepPhase.sweep⟩ 1
      (fun t => FinTM.bufferTape (qyLay κ x.length 3 0 0 t)) (fun _ => 0) [] := by
    unfold qyAt qyAnc qyLayT
    rw [ladder_zero, Nat.unpair_zero]
    rfl
  rw [hq0] at seg2
  obtain ⟨h2, hc2, -⟩ := (segment_iff _ _ _ _ _ _).mp seg2
  have hs := stage_spec f hn
  have hlog := qy_stage_lt_log f hn
  have hlogn := Nat.log_le_self 2 x.length
  have hj := Nat.unpair_left_le (stage f x.length)
  have hS : qySetB κ x.length ≤
      (κ.cbA + κ.prA + 2 * (Nat.bits (κ.cfA * (κ.cfc + 2))).length + 60) * (g x.length + 1) := by
    unfold qySetB
    exact Nat.mul_le_mul_left _ (by have := hle x.length; omega)
  have hL : qyLoopA κ * (x.length + 1) ≤ qyLoopA κ * (g x.length + 1) :=
    Nat.mul_le_mul_left _ (by have := hle x.length; omega)
  have hA : qyMainA κ * (g x.length + 1) =
      (κ.cbA + κ.prA + 2 * (Nat.bits (κ.cfA * (κ.cfc + 2))).length + 60) * (g x.length + 1) +
        qyLoopA κ * (g x.length + 1) + qyWk κ * (g x.length + 1) + 8 * (g x.length + 1) := by
    unfold qyMainA
    ring
  rcases hcase with ⟨hI, ip, T, P, hc', hesc⟩ | ⟨hT, T, P, hc', hesc, h4, hP4⟩
  · -- the middle
    have hmid : Segment (phaseHostTM (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ)) ∅
        (fun _ => True) (qyC ⟨.loc, ⟨.anc, SweepPhase.sweep⟩⟩ 1
          (fun t => FinTM.bufferTape (qyLay κ x.length 3 0 0 t)) (fun _ => 0) [])
        (qyC ⟨.mid, ⟨.m0, κ.rE⟩⟩ ip T P []) (t2 + 1) := by
      rcases hc' with hc' | hc' <;> subst hc' <;>
        exact qy_hosted (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ) .loc
          ⟨.anc, SweepPhase.sweep⟩ _ ⟨.mid, ⟨.m0, κ.rE⟩⟩ 1 ip _ T _ P [] [] t2 h2
          (by simp [qyMainRed]) (fun u hu s hs => qy_mainRed_loc κ s (hs ▸ hc2 u hu)) ∅
          (fun _ h => h)
    obtain ⟨t3, ht3, hh3, ho3⟩ := qy_mid_run κ (x := x) _ _ _ ip T P hesc
    have h3 := qy_hosted_halt (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ) .mid
      ⟨.m0, κ.rE⟩ ip T P [] t3 _ rfl hh3 (fun _ _ _ _ => by simp [qyMainRed])
    have hseg := (segment_iff _ _ _ _ _ _).mp (hs1.trans hmid)
    refine ⟨t1 + 1 + (t2 + 1) + t3, ?_, ?_⟩
    · have hW := qy_midB_le κ x.length (Nat.unpair (stage f x.length)).1 (by omega)
        (hle x.length)
      rw [hA]
      omega
    · rw [MultiTapeTM.runFrom_add]
      erw [hseg.1]
      refine ⟨h3.1, ?_⟩
      rw [h3.2, ho3, query_eq f g hn, if_neg (by omega), stageCode_eq]
  · -- the top
    subst hc'
    have htop := qy_hosted (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ) .loc
      ⟨.anc, SweepPhase.sweep⟩ _ ⟨.top, ⟨.t1, Sum.inl ()⟩⟩ 1 1 _ T _ P [] [] t2 h2
      (by simp [qyMainRed]) (fun u hu s hs => qy_mainRed_loc κ s (hs ▸ hc2 u hu)) ∅
      (fun _ h => h)
    obtain ⟨t3, ht3, hh3, ho3⟩ := qy_top_run κ (x := x) _ _ _ T P hesc h4 hP4
    have h3 := qy_hosted_halt (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ) .top
      ⟨.t1, Sum.inl ()⟩ 1 T P [] t3 _ rfl hh3 (fun _ _ _ _ => by simp [qyMainRed])
    have hseg := (segment_iff _ _ _ _ _ _).mp (hs1.trans htop)
    refine ⟨t1 + 1 + (t2 + 1) + t3, ?_, ?_⟩
    · have hX := qy_ladder_succ_eq f (stage f x.length)
      rw [hT] at hX
      set X := f (ladder f (stage f x.length) + 1) + (ladder f (stage f x.length) + 1) + 1
        with hXd
      have hX4 : X ^ 4 < x.length := by
        rw [hX]
        exact Nat.lt_two_pow_self
      have hX1 : 1 ≤ X := by omega
      have hX3 : X ^ 3 ≤ x.length := by
        have : X ^ 3 ≤ X ^ 4 := Nat.pow_le_pow_right hX1 (by norm_num)
        omega
      have hX2 : X ^ 2 ≤ x.length := by
        have : X ^ 2 ≤ X ^ 4 := Nat.pow_le_pow_right hX1 (by norm_num)
        omega
      have hW := qy_topB_le κ x.length X (ladder f (stage f x.length) + 1)
        (Nat.unpair (stage f x.length)).1 hX3 hX2 (by omega) (by omega)
      have hW' : qyWk κ * (x.length + 1) ≤ qyWk κ * (g x.length + 1) :=
        Nat.mul_le_mul_left _ (by have := hle x.length; omega)
      rw [hA]
      omega
    · rw [MultiTapeTM.runFrom_add]
      erw [hseg.1]
      refine ⟨h3.1, ?_⟩
      rw [h3.2, ho3, query_eq f g hn, if_pos hT.symm, stageCode_eq, budget_eq]

/-- **`M₁` on inputs of length `n ≤ 2`** (checkpoint 7): from its initial configuration it halts
within `qyMainA (g n + 1)` steps with the empty output, the stage query of `1ⁿ`.

**Proof sketch.** The setup's short path (`qy_setup_short`), hosted; then the halting phase, an
emitter of nothing (`qy_emit_stop`, `qy_hosted_halt`). The query is `[]` off its guard
(`query_of_not_guard`). -/
private theorem qy_main_short {f g : ℕ → ℕ} (κ : QyKit f g) (hle : ∀ n, n ≤ g n) {x : List Bool}
    (hn : x.length ≤ 2) :
    ∃ t ≤ qyMainA κ * (g x.length + 1),
      ((qyM₁ κ).tm.runFrom ((qyM₁ κ).tm.initCfg x) t).state = none ∧
      ((qyM₁ κ).tm.runFrom ((qyM₁ κ).tm.initCfg x) t).output =
        query f g (List.replicate x.length true) := by
  rw [qy_initCfg]
  show ∃ t ≤ _, ((phaseHostTM (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ)).runFrom
    _ t).state = none ∧ ((phaseHostTM (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩
      (qyMainRed κ)).runFrom _ t).output = _
  obtain ⟨t1, ht1, v, hv, seg1⟩ := qy_setup_short κ hn
  obtain ⟨h1, hc1, -⟩ := (segment_iff _ _ _ _ _ _).mp seg1
  have hs1 := qy_hosted (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ) .setup
    ⟨.s1, Sum.inl ()⟩ ⟨.s6, QyCmp.done v⟩ ⟨.halt, QyEm.pre 0⟩ 1 1 _ _ _ _ [] [] t1 h1
    (by rcases hv with rfl | rfl <;> simp [qyMainRed])
    (fun u hu s hs => qy_mainRed_setup κ s (hs ▸ hc1 u hu)) ∅ (fun _ h => h)
  obtain ⟨t2, ht2, hh2, ho2⟩ := qy_emit_stop (x := x) (κ.tp 15) [] [] 0 false 1 (qySetT5 κ x.length)
    (fun _ => 0) [] [] (by simp [qySetT5, QyKit.tp_inj]) rfl
  have h2 := qy_hosted_halt (qyMainM κ) ⟨.setup, ⟨.s1, Sum.inl ()⟩⟩ (qyMainRed κ) .halt
    (QyEm.pre 0) 1 (qySetT5 κ x.length) (fun _ => 0) [] t2 _ rfl hh2
    (fun _ _ _ _ => by simp [qyMainRed])
  have hseg := (segment_iff _ _ _ _ _ _).mp hs1
  refine ⟨t1 + 1 + t2, ?_, ?_⟩
  · simp only [List.length_nil, zero_mul] at ht2
    have hS : qySetB κ x.length ≤
        (κ.cbA + κ.prA + 2 * (Nat.bits (κ.cfA * (κ.cfc + 2))).length + 60) * (g x.length + 1) := by
      unfold qySetB
      exact Nat.mul_le_mul_left _ (by have := hle x.length; omega)
    have hA : qyMainA κ * (g x.length + 1) =
        (κ.cbA + κ.prA + 2 * (Nat.bits (κ.cfA * (κ.cfc + 2))).length + 60) * (g x.length + 1) +
          qyLoopA κ * (g x.length + 1) + qyWk κ * (g x.length + 1) + 8 * (g x.length + 1) := by
      unfold qyMainA
      ring
    rw [hA]
    omega
  · rw [MultiTapeTM.runFrom_add]
    erw [hseg.1]
    refine ⟨h2.1, ?_⟩
    rw [h2.2, ho2, query_of_not_guard f g (by simp only [List.length_replicate]; omega)]
    simp [qyBody]

/-- **The main machine computes the query on the unary word of every input's length**
(checkpoint 7, the target's `hmain`): for time-constructible `f` and `g`, `M₁` halts on every
input `x` within `qyMainA (g |x| + 1)` steps with `query f g 1^{|x|}`.

**Proof sketch.** The kit (`qy_kit_exists`); `n ≤ g n` from `Complexity.timeConstructible_iff`;
on each input, `qy_main_long` or `qy_main_short`, read through `Turing.FinTM.computesInTime_iff`
and widened to the bound by `Turing.FinTM.ComputesInTime.mono`. -/
private theorem qy_main {f g : ℕ → ℕ} (hf : Complexity.TimeConstructible f)
    (hg : Complexity.TimeConstructible g) :
    ∃ (M : FinTM Bool) (A : ℕ),
      M.ComputesFunInTime (fun x => query f g (List.replicate x.length true))
        (fun n => A * (g n + 1)) := by
  obtain ⟨κ⟩ := qy_kit_exists hf hg
  have hle := ((Complexity.timeConstructible_iff g).mp hg).1
  refine ⟨qyM₁ κ, qyMainA κ, (FinTM.computesFunInTime_iff _ _ _).mpr fun x => ?_⟩
  rcases Nat.lt_or_ge x.length 3 with h | h
  · obtain ⟨t, ht, h1, h2⟩ := qy_main_short κ hle (x := x) (by omega)
    exact ((FinTM.computesInTime_iff _ _ _ _).mpr ⟨h1, h2⟩).mono ht
  · obtain ⟨t, ht, h1, h2⟩ := qy_main_long κ hle h
    exact ((FinTM.computesInTime_iff _ _ _ _).mpr ⟨h1, h2⟩).mono ht

/-- **The stage query in linear time** (C1-E; [the P3.3 gate's round 2, §2]): for
time-constructible `f` and `g` there is a deterministic machine computing the stage query within
`C · (g n + 1)`.

**Proof sketch.**
- Reject a non-unary input or one shorter than `3` by a scan, output `[]`.
- Otherwise run the **capped locator** of the gate's round 2, §2, from `ℓ₀ = 2`. At each stage
  prepare `1^a`, with `a = ℓ + 1 ≤ n`, and run `f`'s witness capped at `c_f · (n + 1)` steps (the
  step clock `Turing.exists_stepClockTMVia`). A timeout, or an output above `n`, places `n` inside
  the current stage. Otherwise compare `(f a + a + 1)⁴` with `⌊log₂ n⌋`, testing whether `n` is a
  power of two at equality, and either stop (`n` is inside the stage, or is its top, keeping `T*`)
  or write `ℓᵢ₊₁` in binary and advance.
- At the stage found, compute `j = (Nat.unpair i).1` and the code `(Nat.bits (j + 1)).dropLast`.
- For the middle, run `g`'s witness.
- Materialize the query with the `pairEncode` writer: bit doubling, the separator, the unary tail.

The ledger is the gate's: preparations and completed witness runs sum to less than `2n`, the last
capped run is `O(n)`, and the binary arithmetic is `O(log³ n)` over `O(log n)` stages. So the
locator is `O(n + 1) ≤ O(g n + 1)` by `n ≤ g n`, and `g`'s witness and the materialization add
`O(g n + 1)`. Fill obligations, named: the locator and its private arithmetic rows (numeric `≤`,
fixed-degree binary arithmetic, the `⌊log₂⌋` comparison, the power-of-two test, `Nat.unpair` on
binary words, the unranking); the `pairEncode` writer; the ledger.

**Implementation status.** Proved. The guard reduces the query to a machine computing it on the
unary word of every input's length. That machine is a phase host of: a linear-time setup
(`bits n` by the input call, `1^{n+1}`, the first rung, the test `n ≥ 3`, the input seek's tape
and an all-ones clock counter); the locator, whose rounds run `f`'s witness under the step clock
on the rung `1^a` and build the next rung `2 ^ (f a + a + 1)⁴` in unary only when it is at most
`n`, each a round at the locator's anchor with interior, top and timeout escapes, the passed
rungs summing to less than `2n`; and two writers, which seek the input head home, compute the
stage code, run `g`'s witness or the budget's square, and emit the `pairEncode` word. -/
theorem exists_queryTM {f g : ℕ → ℕ} (hf : Complexity.TimeConstructible f)
    (hg : Complexity.TimeConstructible g) :
    ∃ (G : FinTM Bool) (C : ℕ), G.ComputesFunInTime (query f g) fun n => C * (g n + 1) := by
  suffices hmain : ∃ (M : FinTM Bool) (A : ℕ),
      M.ComputesFunInTime (fun x => query f g (List.replicate x.length true))
        (fun n => A * (g n + 1)) by
    obtain ⟨M, A, hM⟩ := hmain
    exact qy_query_of_main hg hM
  exact qy_main hf hg

/-- **The diagonalizer** (C1-E; [AB09, proof of Theorem 3.2]; the route of C1's design §2.5 and the
P3.3 gate's round 2, §§3–5): for time-constructible `f`, `g`, an effective scheme `c` and a
deterministic decider of the coded machines' bounded acceptance in exponential time (`hBF`, the
conclusion of `Turing.exists_ndAcceptsWithin_decider`) there are a nondeterministic machine `D` and
a constant `K` with:
- every branch of `D` on every input `x` halts within `K · (g |x| + 1)`;
- for every code `α` a constant `C` such that, on `1ⁿ` with `n ≥ 3` in a stage of `α`:
  - in the middle (`n` not the stage's top): if `D` accepts `1ⁿ` within `K · (g n + 1)`, the coded
    machine accepts `1^{n + 1}` within `g n`; and if the coded machine accepts `1^{n + 1}` within
    some `t'` with `C · (t' + 1) ≤ g n`, `D` accepts `1ⁿ` within `K · (g n + 1)`;
  - at the top (`n = ℓᵢ₊₁`), when `C · 2^{C · (T* + 1)} ≤ n`: `D` accepts `1ⁿ` within
    `K · (g n + 1)` iff the coded machine does not accept the bottom `1^{ℓᵢ + 1}` within
    `T* = budget f ℓᵢ`.

**Why the decider is a hypothesis.** It is stated in
`TCSlib.Complexity.Diagonalization.NTimeHierarchy`, whose `ntime_hierarchy` needs this module,
so this module cannot import it. That proof supplies it from
`Turing.exists_ndAcceptsWithin_decider`; taking it as a hypothesis keeps the two modules' imports
acyclic.

**Proof sketch.** `D` is assembled by the nondeterministic phase host
`Turing.NDTM.phaseHostND`:
- **query:** the stage query by `Turing.NTimeDiag.exists_queryTM`'s machine, called on the native
  input (`Turing.FinTM.exists_inputCallTM`);
- **guess:** `bits (g n)` by `g`'s witness, expanded to a block (`Turing.expandTM`), overwritten by
  the choice writer (`Turing.ndWriterTM_run_block`) and rewound: the stream `s`, with `|s| = g n`.
  In the middle, also a **nominal budget** `b` (C1's design §3.6, the fallback): a word of the
  width of `bits (g n)` from the choice writer, rejected unless its value is at most `g n`, and
  normalized to `bits b`;
- **middle:** the query word with its budget field rewritten from `bits (g n)` to `bits b`, that
  is `⟨⟨bits b, α⟩, 1^{n + 1}⟩`, run by the interpreter core `Turing.exists_ndInterpreterCore` with
  the stream `s` (`b ≤ |s|`), under the step clock (`Turing.exists_stepClockTMVia`) with the body
  allowance `g n` (its counter is `bits (g n)`), accepting iff the interpreter accepts in time;
- **top:** the exponential decider of `hBF` on the query word
  (hosted by `Turing.vhostSilentTM`), under the same clock, accepting iff it completes with
  `[false]`;
- default reject.

**Time.** Every phase before the simulators is code-independent and costs at most `P · (g n + 1)`
for a uniform `P`: the query, the stream, and the budget's guess, test, normalization and rewrite.
The clock runs a simulator for at most its body allowance, `g n` steps, at a physical cost of at
most `5 · g n + 2 · |bits (g n)| + 2 ≤ 7 · (g n + 1)`, and the final dispatch costs a constant `P'`.
So `K = P + 7 + P'` bounds every branch; the body allowance and `K` are distinct quantities.
- **Middle completeness:** if the coded machine accepts `1^{n + 1}` along a word of length `t'`
  with `C · (t' + 1) ≤ g n`, take `b = t'` and a stream whose first `t'` bits are that word. The
  interpreter's total-time clause, `T ≤ C_R · (b + 1)` with no `|x|` term, gives
  `T ≤ C · (t' + 1) ≤ g n` when `C ≥ C_R`: inside the allowance, with the verdict `accept`.
- **Middle soundness:** an accepting interpreter run is an accepting branch along `s.take b` (the
  replay lemma), and acceptance within `b ≤ g n` is acceptance within `g n`
  (`Turing.FinNDTM.AcceptsWithin.mono`). A guess `b` below every acceptance time sees no halted
  accepting branch and rejects.
- **Top:** the decider's time is `C_BF · 2^{C_BF · (T* + 1)} ≤ n ≤ g n`, inside the allowance.

The interpreter's prefix clause is not used: its `|x|` term (`|x| = n + 1`) carries the per-code
constant, which the uniform `K` cannot absorb when `g n = n` (the statement gate, finding 1).

Fill obligations, named: the assembly; the budget's guess, test, normalization and rewrite (a
private leaf in `O(g n + 1)`); the transfer to every branch
(`Turing.NDTM.runWith_mapState_of_agreeOn_det`); the clock's two exits per rung; the per-code
constant `C = max 1 (max C_R C_BF)`. -/
theorem exists_diagonalizer {f g : ℕ → ℕ} (hf : Complexity.TimeConstructible f)
    (hg : Complexity.TimeConstructible g) (c : EffectiveNDMachineCode)
    (hBF : ∃ BF : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      ((c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (C * 2 ^ (C * (t + 1)))) ∧
      (¬(c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (C * 2 ^ (C * (t + 1))))) :
    ∃ (D : FinNDTM Bool) (K : ℕ),
      (∀ x : List Bool, D.tm.HaltsWithin x (K * (g x.length + 1))) ∧
      ∀ α : List Bool, ∃ C : ℕ, ∀ n : ℕ, 3 ≤ n → stageCode (stage f n) = α →
        (n ≠ ladder f (stage f n + 1) →
          (D.AcceptsWithin (List.replicate n true) (K * (g n + 1)) →
            (c.decode α).toFinNDTM.AcceptsWithin (List.replicate (n + 1) true) (g n)) ∧
          (∀ t' : ℕ, (c.decode α).toFinNDTM.AcceptsWithin (List.replicate (n + 1) true) t' →
            C * (t' + 1) ≤ g n →
            D.AcceptsWithin (List.replicate n true) (K * (g n + 1)))) ∧
        (n = ladder f (stage f n + 1) →
          C * 2 ^ (C * (budget f (ladder f (stage f n)) + 1)) ≤ n →
          (D.AcceptsWithin (List.replicate n true) (K * (g n + 1)) ↔
            ¬(c.decode α).toFinNDTM.AcceptsWithin
              (List.replicate (ladder f (stage f n) + 1) true)
              (budget f (ladder f (stage f n))))) := by
  sorry

end Turing.NTimeDiag
