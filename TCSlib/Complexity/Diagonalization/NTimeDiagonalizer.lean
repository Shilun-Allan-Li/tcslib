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
import TCSlib.Complexity.TuringMachine.Build.NDHost
import TCSlib.Complexity.TuringMachine.NDCodeSimulator
import TCSlib.Complexity.TuringMachine.Build.VirtualInput

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
* `Turing.NTimeDiag.exists_queryTM` — the stage query in linear time (proved).
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
off.

**Proof sketch.** `Turing.phaseHostTM_run` gives the host's run as the tagged phase run up to `t`
and the redirected endpoint at `t + 1`. Before its end the phase is live
(`MultiTapeTM.runFrom_state_ne_none_of_le`), so each intermediate host state is `some ⟨k, s⟩` for a
state `s` the phase's run visits, which `hF` keeps out of `F`; `Turing.segment_iff` assembles the
segment. -/
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
avoiding every set that the phase's run avoids before its end.

**Proof sketch.** `Turing.phaseHostTM_run_le` gives the host's run as the tagged phase run at every
time up to `t`, so at `t` it is the tagged endpoint. Before `t` each host state is a tagged live
phase state, kept out of `F` by `hF`; `Turing.segment_iff` assembles the segment. -/
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
`src`, mapped by `g`, onto `dst` right after the word `u` there; nothing else changes.

**Proof sketch.** `Turing.copyMapTM_run_ofCfg` gives the run and its first arrival. Its endpoint
patches `dst` from its head with `w.map g`; that head is at the end of `u`, so the patched tape is
the buffer of `u ++ w.map g` (`qy_patch_end`). Every other tape is unchanged. -/
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
`src`, mapped by `g`, over the word `u` under the head of `dst`, which is no longer than `w`.

**Proof sketch.** `Turing.copyMapTM_run_ofCfg` gives the run and its first arrival. Its endpoint
overwrites `dst` from cell `0` with `w.map g`; since `u` is no longer than `w`, no cell of `u`
survives beyond it (`FinTM.bufferTape_eq_none_of_not_mem`), so the tape is the buffer of `w.map g`.
Every other tape is unchanged. -/
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

/-- **The clear.** `Turing.clearTM` blanks the word `w` under the head of tape `i`.

**Proof sketch.** `Turing.clearTM_run_ofCfg` gives the run and its first arrival. Its endpoint
blanks the `|w|` cells from the head at `0`, and the cells of `w`'s buffer outside them were already
blank (`FinTM.bufferTape_eq_none_of_not_mem`), so tape `i` is the empty buffer. Every other tape is
unchanged. -/
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
`i` right after the word `u` there, its head back where it started.

**Proof sketch.** `Turing.writeConstTM_run_ofCfg` gives the run and its first arrival. Its endpoint
patches tape `i` from its head, at the end of `u`, with `w₀`, which is the buffer of `u ++ w₀`
(`qy_patch_end`). Every other tape is unchanged. -/
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
normal-form configuration with the heads moved and the emission appended.

**Proof sketch.** `MultiTapeTM.step_of_some` at the live state applies the transition's action to
the configuration, whose work reads are the cells under the heads (`Cfg.workTapeSymbols_eq`). Each
field of the result is read through the `Action.apply_*` equations: the state `s'`, the input head
unmoved (`moveInputPos_zero`), every tape unchanged (the writes are `none`), the heads moved by
`mv`, the emission appended. -/
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

/-- **The length comparison**. Started with the heads of tapes `a`
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

/-- **The writer's emitter**. Emit the fixed word `pre`; then emit the word under the
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

/-- **The setup, long path**: on inputs of length `n ≥ 3`, from the blank seam, the
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

/-- **The setup, short path**: on inputs of length `n ≤ 2`, from the blank seam,
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
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  exact Nat.size_le_size h

/-- Every number is below two to the length of its bits. -/
private theorem qy_lt_two_pow_bits (n : ℕ) : n < 2 ^ (Nat.bits n).length := by
  rw [Nat.size_eq_bits_len]
  exact Nat.lt_size_self n

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

/-- **The round's call**: from the anchor layout at the rung `1^a`, `a ≤ n`, the
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

/-- **The round's tests**: from the length test after a returned call (`bits F`,
`F = f a`, on tape `7`), with `X = F + a + 1` and the next rung `ℓ' = 2 ^ X⁴`, the locator ends
at its interior escape if `n < ℓ'`, at its top escape if `ℓ' = n` (with `1^{X - 1}` on tape `4`
for the budget), and otherwise at the cleanup with the tapes `qyTB`, `X < |bits n|` and
`X⁴ < |bits n|`.

**Proof sketch.** Fourteen hosted phases (`qy_hosted`), each a row's run: `|bits F|` against
`|bits n|` (`qy_cmp_run`; longer gives `F > n`); `F` expanded to `1^F` (`qy_expandHost`, the
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

/-- **A passed round's cleanup**: from the tapes `qyTB` after the tests, the
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

/-- **A passed round's pair update**: from the anchor layout with
`(j, k) = unpair h` on tapes `10` and `11`, the locator moves the pair to `unpair (h + 1)` by the
successor rule of `Nat.unpair` and returns to its anchor.

**Proof sketch.** The comparison `j` against `k`, then by its verdict: `lt`, the increment
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

/-- **One round of the locator**, as a `Turing.Round` at the anchor with the three
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
most `11 ℓ'` plus the polylogarithmic `qyCk (|bits n| + 1) ^ 5`.

**Proof sketch.** Unfold the file's own `qyRndP` and `qyCk`. With `L = |bits n|` and `P = (L + 1) ^
5`, bound each polylogarithmic term by a multiple of `P` (`L + 1 ≤ P`, `L ^ 5 ≤ P`, and `j + k + 2 ≤
2 P` from `hjk`), then collect the constants (`ring`, `omega`). -/
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

/-- **The locator's loop**: on inputs of length `n ≥ 3`, from the anchor at the
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

/-- A named tape other than `3` to `8` is off the round's scratch.

**Proof sketch.** Case on the disjuncts of `qyScratch`. A tape of the clock's bank is the call's
first tape or the counter, each a named tape `κ.tp` with index from `3` to `8`, excluded by the
injectivity of `κ.tp`; or another tape of the call's bank, which is never a named tape
(`QyKit.bCf_ne`). The other four disjuncts name `κ.tp 3` to `κ.tp 6`, excluded by injectivity. -/
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

/-- **The stage code's calls after an escape**: on an escape's tapes with the input
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

/-- **The input seek after an escape**: on an escape's tapes, from any input
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

/-- **The middle writer's head**: from its entry on an escape's tapes, the input
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

/-- **The top writer's head**: from its entry on an escape's tapes with the input
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

/-- **The writer's word** (three emissions): the flag, the budget field's bits each written
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

/-- **The middle writer**: from its entry on an escape's tapes, it halts within
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

/-- **The top writer**: from its entry on an escape's tapes with `1^{F + a}` on
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

/-- **`M₁` on inputs of length `n ≥ 3`**: from its initial configuration it halts
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

/-- **`M₁` on inputs of length `n ≤ 2`**: from its initial configuration it halts
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
(the target's `hmain`): for time-constructible `f` and `g`, `M₁` halts on every
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

/-! ### The diagonalizer's leaf: the one-cell take -/

/-- **The one-cell take**. From its reading state `none`, in one step it reads the cell under the
head of tape `i`, writes a blank there, moves that head one cell right and enters `some o`, `o` the
symbol read; nothing else is written or moved and nothing is emitted. A state `some o` idles (the
host redirects it). It makes the left delimiter that every framed row needs before a word inside a
nonblank block: no public row writes a blank at one cell (`Turing.writeConstTM` writes symbols,
`Turing.clearTM` and `Turing.transferMapTM` blank a whole delimited word). -/
private def dzTakeTM (K : ℕ) (i : Fin K) : MultiTapeTM K Bool (Option (Option Bool)) where
  q₀ := none
  tr := fun q _ w =>
    match q with
    | none =>
      ⟨0, fun j => if j = i then (some none, .pos) else (none, 0), none, some (some (w i))⟩
    | some o => ⟨0, fun _ => (none, 0), none, some (some o)⟩

/-- **The take's step.** From its reading state, `dzTakeTM` holds the symbol under the head of tape
`i` after one step, with that cell blanked and that head one cell right; the input head, every other
tape and head, and the output are unchanged.

**Proof sketch.** `MultiTapeTM.step_of_some` at the reading state applies the take's action, whose
work reads are the cells under the heads (`Cfg.workTapeSymbols_eq`). Each field is read through the
`Action.apply_*` equations: tape `i` is updated at its head with a blank
(`Action.apply_workTapes`), every other tape writes nothing, the head of tape `i` moves by one. -/
private theorem dz_take_run {K : ℕ} {x : List Bool} (i : Fin K) (ip : Fin (x.length + 2))
    (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool) :
    (dzTakeTM K i).runFrom (qyC none ip T P o) 1 =
      qyC (some (T i (P i))) ip (Function.update T i (Function.update (T i) (P i) none))
        (Function.update P i (P i + 1)) o := by
  have hs : (qyC none ip T P o : Cfg K Bool (Option (Option Bool)) x).state = some none := rfl
  have hw : (qyC none ip T P o : Cfg K Bool (Option (Option Bool)) x).workTapeSymbols =
      fun j => T j (P j) := by
    funext j
    rw [Cfg.workTapeSymbols_eq]
    rfl
  have htr : (dzTakeTM K i).tr none
      (qyC none ip T P o : Cfg K Bool (Option (Option Bool)) x).inputSymbol
      (fun j => T j (P j)) =
      ⟨0, fun j => if j = i then (some none, .pos) else (none, 0), none,
        some (some (T i (P i)))⟩ := by
    simp only [dzTakeTM]
  rw [qy_run_one, MultiTapeTM.step_of_some hs, hw, htr]
  apply Cfg.ext
  · rw [Action.apply_state]
    rfl
  · rw [Action.apply_inputPos, moveInputPos_zero]
    rfl
  · funext j q
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    dsimp only
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl, Option.getD_some]
      show Function.update (T j) (P j) none q = Function.update T j _ j q
      rw [Function.update_self]
    · rw [if_neg hj, Option.getD_none]
      show Function.update (T j) (P j) (T j (P j)) q = Function.update T i _ j q
      rw [Function.update_eq_self, Function.update_of_ne hj]
  · funext j
    rw [Action.apply_workTapePos]
    dsimp only
    by_cases hj : j = i
    · subst hj
      rw [if_pos rfl]
      show P j + ((SignType.pos : SignType) : ℤ) = Function.update P j (P j + 1) j
      rw [Function.update_self]
      rfl
    · rw [if_neg hj]
      show P j + ((0 : SignType) : ℤ) = Function.update P i (P i + 1) j
      rw [Function.update_of_ne hj, SignType.coe_zero, add_zero]
  · rw [Action.apply_output]
    show o ++ (none : Option Bool).toList = o
    rw [Option.toList_none, List.append_nil]

/-! ### The silent capture in normal form -/

/-- **The silent transport, reconstructed.** A configuration whose state, input head and output
agree with the source's state, input head and the given physical output, whose selected tapes are
the source's, whose capture tape holds the recorded word `pre ++ c.output` with its head after it,
and whose other tapes are the frame, is the silent transport `Turing.embedSilentCfg`.

**Proof sketch.** Field by field: the state, input head and output by the transport's equations;
a selected tape by `Turing.embedSilentCfg_selected_tape` and `_selected_pos`; the capture tape by
`Turing.embedSilentCfg_cap`; every other tape by `Turing.embedSilentCfg_unselected`. -/
private theorem dz_silentCfg_eq {m K : ℕ} {S : Type} {x : List Bool} (ι : Fin m ↪ Fin K)
    (cap : Fin K) (hcap : cap ∉ Set.range ι) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ)
    (pre o : List Bool) (c : Cfg m Bool S x) (d : Cfg K Bool S x) (hs : c.state = d.state)
    (hin : c.inputPos = d.inputPos) (hout : o = d.output)
    (hsel : ∀ i, c.workTapes i = d.workTapes (ι i) ∧ c.workTapePos i = d.workTapePos (ι i))
    (hc : FinTM.bufferTape (pre ++ c.output) = d.workTapes cap ∧
      ((pre ++ c.output).length : ℤ) = d.workTapePos cap)
    (hfr : ∀ j, j ∉ Set.range ι → j ≠ cap → T j = d.workTapes j ∧ P j = d.workTapePos j) :
    embedSilentCfg ι cap T P pre o c = d := by
  have fields (j : Fin K) :
      (embedSilentCfg ι cap T P pre o c).workTapes j = d.workTapes j ∧
        (embedSilentCfg ι cap T P pre o c).workTapePos j = d.workTapePos j := by
    by_cases hj : j ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hj
      rw [embedSilentCfg_selected_tape, embedSilentCfg_selected_pos]
      exact hsel i
    · by_cases hjc : j = cap
      · subst hjc
        obtain ⟨h1, h2⟩ := embedSilentCfg_cap ι j hcap T P pre o c
        exact ⟨h1.trans hc.1, h2.trans hc.2⟩
      · obtain ⟨h1, h2⟩ := embedSilentCfg_unselected ι cap T P pre o c j hj hjc
        exact ⟨h1.trans (hfr j hj hjc).1, h2.trans (hfr j hj hjc).2⟩
  exact Cfg.ext ((embedSilentCfg_state ι cap T P pre o c).trans hs)
    ((embedSilentCfg_inputPos ι cap T P pre o c).trans hin)
    (funext fun j => (fields j).1) (funext fun j => (fields j).2)
    ((embedSilentCfg_output ι cap T P pre o c).trans hout)

/-- **A captured run in normal form.** A source machine run along `ι` from the selected bank of a
normal-form configuration, ending in normal form with the emission `o'`, is the run of the capture
wrapper `Turing.embedSilentTM ι cap` from that configuration when the capture tape holds `pre` with
its head after it: the selected tapes and heads become the source's, the capture tape holds
`pre ++ o'` with its head after it, every other tape is kept, and the output is unchanged. At every
time the wrapper's state is the source's.

**Proof sketch.** The normal-form start is the silent transport of the source's start
(`dz_silentCfg_eq`), so `Turing.embedSilentTM_runFrom` transports the source run; the endpoint is
the transport of the source's endpoint, again by `dz_silentCfg_eq`, and the state at every time is
the source's (`Turing.embedSilentCfg_state`). -/
private theorem dz_silent {m K : ℕ} {S : Type} {x : List Bool} (ι : Fin m ↪ Fin K) (cap : Fin K)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S) (s s' : S) (ip : Fin (x.length + 2))
    (T T' : Fin K → ℤ → Option Bool) (P P' : Fin K → ℤ) (o pre o' : List Bool)
    (T₀ : Fin m → ℤ → Option Bool) (P₀ : Fin m → ℤ) (t : ℕ)
    (hTc : T cap = FinTM.bufferTape pre) (hPc : P cap = pre.length)
    (hrun : M.runFrom (qyC s ip (fun i => T (ι i)) (fun i => P (ι i)) []) t = qyC s' ip T₀ P₀ o')
    (hsel : ∀ i, T' (ι i) = T₀ i ∧ P' (ι i) = P₀ i)
    (hc : T' cap = FinTM.bufferTape (pre ++ o') ∧ P' cap = ((pre ++ o').length : ℤ))
    (hfr : ∀ j, j ∉ Set.range ι → j ≠ cap → T' j = T j ∧ P' j = P j) :
    (embedSilentTM ι cap M).runFrom (qyC s ip T P o) t = qyC s' ip T' P' o ∧
      ∀ u, ((embedSilentTM ι cap M).runFrom (qyC s ip T P o) u).state =
        (M.runFrom (qyC s ip (fun i => T (ι i)) (fun i => P (ι i)) []) u).state := by
  have hstart : embedSilentCfg ι cap T P pre o
      (qyC s ip (fun i => T (ι i)) (fun i => P (ι i)) []) = qyC s ip T P o :=
    dz_silentCfg_eq ι cap hcap T P pre o _ _ rfl rfl rfl (fun _ => ⟨rfl, rfl⟩)
      ⟨by show FinTM.bufferTape (pre ++ []) = T cap; rw [List.append_nil, hTc],
        by show ((pre ++ []).length : ℤ) = P cap; rw [List.append_nil, hPc]⟩
      (fun _ _ _ => ⟨rfl, rfl⟩)
  refine ⟨?_, fun u => ?_⟩
  · rw [← hstart, embedSilentTM_runFrom ι cap hcap, hrun]
    exact dz_silentCfg_eq ι cap hcap T P pre o _ _ rfl rfl rfl
      (fun i => ⟨(hsel i).1.symm, (hsel i).2.symm⟩) ⟨hc.1.symm, hc.2.symm⟩
      (fun j hj hjc => ⟨(hfr j hj hjc).1.symm, (hfr j hj hjc).2.symm⟩)
  · rw [← hstart, embedSilentTM_runFrom ι cap hcap, embedSilentCfg_state]

/-! ### The hosted clock -/

/-- **The hosted clock's tape map.** A step clock over `Turing.vhostSilentTM` of an `m`-tape machine
has `((1 + m) + 1) + 1` tapes: the virtual input's buffer, the hosted machine's tapes, the capture
tape and the counter. This map places the buffer on `buf`, the hosted tapes along `β`, the capture
tape on `cap` and the counter on `ctr`.

**Proof sketch.** Injectivity by cases on `Fin.lastCases` (twice) and `Fin.addCases`: the four
targets are distinct, and `β` is injective with its range avoiding the other three. -/
private def dzClkEmb {m K : ℕ} (buf cap ctr : Fin K) (β : Fin m ↪ Fin K) (h1 : buf ≠ cap)
    (h2 : buf ≠ ctr) (h3 : cap ≠ ctr) (hb : buf ∉ Set.range β) (hc : cap ∉ Set.range β)
    (hk : ctr ∉ Set.range β) : Fin (((1 + m) + 1) + 1) ↪ Fin K where
  toFun := Fin.lastCases ctr (Fin.lastCases cap (Fin.addCases (fun _ => buf) β))
  inj' := by
    have hin : ∀ a : Fin (1 + m), Fin.addCases (fun _ => buf) β a = buf ∨
        ∃ i, Fin.addCases (fun _ => buf) β a = β i ∧ a = Fin.natAdd 1 i := by
      intro a
      induction a using Fin.addCases with
      | left a => exact Or.inl (Fin.addCases_left _)
      | right i => exact Or.inr ⟨i, Fin.addCases_right _, rfl⟩
    have hinj : Function.Injective (Fin.addCases (fun _ : Fin 1 => buf) β) := by
      intro a b h
      dsimp only at h
      induction a using Fin.addCases with
      | left a =>
        induction b using Fin.addCases with
        | left b => rw [Subsingleton.elim a b]
        | right j =>
          rw [Fin.addCases_left, Fin.addCases_right] at h
          exact absurd ⟨j, h.symm⟩ hb
      | right i =>
        induction b using Fin.addCases with
        | left b =>
          rw [Fin.addCases_left, Fin.addCases_right] at h
          exact absurd ⟨i, h⟩ hb
        | right j =>
          rw [Fin.addCases_right, Fin.addCases_right] at h
          rw [β.injective h]
    have hne_cap : ∀ a : Fin (1 + m), Fin.addCases (fun _ => buf) β a ≠ cap := by
      intro a h
      rcases hin a with h' | ⟨i, h', -⟩
      · exact h1 (h'.symm.trans h)
      · exact hc ⟨i, h'.symm.trans h⟩
    have hne_ctr : ∀ a : Fin (1 + m), Fin.addCases (fun _ => buf) β a ≠ ctr := by
      intro a h
      rcases hin a with h' | ⟨i, h', -⟩
      · exact h2 (h'.symm.trans h)
      · exact hk ⟨i, h'.symm.trans h⟩
    have hinj2 : Function.Injective (Fin.lastCases cap (Fin.addCases (fun _ : Fin 1 => buf) β) :
        Fin ((1 + m) + 1) → Fin K) := by
      intro a b h
      dsimp only at h
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b =>
          rw [Fin.lastCases_last, Fin.lastCases_castSucc] at h
          exact absurd h.symm (hne_cap b)
      | cast a =>
        induction b using Fin.lastCases with
        | last =>
          rw [Fin.lastCases_last, Fin.lastCases_castSucc] at h
          exact absurd h (hne_cap a)
        | cast b =>
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc] at h
          rw [hinj h]
    intro a b h
    dsimp only at h
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast b =>
        rw [Fin.lastCases_last, Fin.lastCases_castSucc] at h
        induction b using Fin.lastCases with
        | last => rw [Fin.lastCases_last] at h; exact absurd h.symm h3
        | cast b => rw [Fin.lastCases_castSucc] at h; exact absurd h.symm (hne_ctr b)
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        rw [Fin.lastCases_last, Fin.lastCases_castSucc] at h
        induction a using Fin.lastCases with
        | last => rw [Fin.lastCases_last] at h; exact absurd h h3
        | cast a => rw [Fin.lastCases_castSucc] at h; exact absurd h (hne_ctr a)
      | cast b =>
        rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc] at h
        rw [hinj2 h]

/-- The hosted clock's map sends the counter to `ctr`. -/
private theorem dzClkEmb_ctr {m K : ℕ} (buf cap ctr : Fin K) (β : Fin m ↪ Fin K) (h1 : buf ≠ cap)
    (h2 : buf ≠ ctr) (h3 : cap ≠ ctr) (hb : buf ∉ Set.range β) (hc : cap ∉ Set.range β)
    (hk : ctr ∉ Set.range β) :
    dzClkEmb buf cap ctr β h1 h2 h3 hb hc hk (Fin.last _) = ctr := by
  simp only [dzClkEmb, Function.Embedding.coeFn_mk, Fin.lastCases_last]

/-- The hosted clock's map sends the capture tape to `cap`. -/
private theorem dzClkEmb_cap {m K : ℕ} (buf cap ctr : Fin K) (β : Fin m ↪ Fin K) (h1 : buf ≠ cap)
    (h2 : buf ≠ ctr) (h3 : cap ≠ ctr) (hb : buf ∉ Set.range β) (hc : cap ∉ Set.range β)
    (hk : ctr ∉ Set.range β) :
    dzClkEmb buf cap ctr β h1 h2 h3 hb hc hk (Fin.last _).castSucc = cap := by
  simp only [dzClkEmb, Function.Embedding.coeFn_mk, Fin.lastCases_castSucc, Fin.lastCases_last]

/-- The hosted clock's map sends the buffer to `buf`. -/
private theorem dzClkEmb_buf {m K : ℕ} (buf cap ctr : Fin K) (β : Fin m ↪ Fin K) (h1 : buf ≠ cap)
    (h2 : buf ≠ ctr) (h3 : cap ≠ ctr) (hb : buf ∉ Set.range β) (hc : cap ∉ Set.range β)
    (hk : ctr ∉ Set.range β) (a : Fin 1) :
    dzClkEmb buf cap ctr β h1 h2 h3 hb hc hk (Fin.castAdd m a).castSucc.castSucc = buf := by
  simp only [dzClkEmb, Function.Embedding.coeFn_mk, Fin.lastCases_castSucc, Fin.addCases_left]

/-- The hosted clock's map sends the hosted machine's tape `i` to `β i`. -/
private theorem dzClkEmb_bank {m K : ℕ} (buf cap ctr : Fin K) (β : Fin m ↪ Fin K) (h1 : buf ≠ cap)
    (h2 : buf ≠ ctr) (h3 : cap ≠ ctr) (hb : buf ∉ Set.range β) (hc : cap ∉ Set.range β)
    (hk : ctr ∉ Set.range β) (i : Fin m) :
    dzClkEmb buf cap ctr β h1 h2 h3 hb hc hk (Fin.natAdd 1 i).castSucc.castSucc = β i := by
  simp only [dzClkEmb, Function.Embedding.coeFn_mk, Fin.lastCases_castSucc, Fin.addCases_right]

/-- **The hosted clock's clause** for a machine `M`, a stop predicate `stop` and a step clock `H`
over `Turing.vhostSilentTM M` (with the stop predicate read on the hosted state): embedded along
`dzClkEmb` in a normal-form configuration whose buffer holds the virtual input `y`, whose hosted
tapes hold `M`'s configuration `c` (live, input head `1`, empty output), whose capture tape is blank
and whose counter tape holds `w` (value `d`), every head of these at `0`,
* if `M` first stops at `τ ≤ d`, the host reaches `fin` of `M`'s state at `τ` (tagged) within
  `5τ + 2|w| + 2` steps, with `M`'s output at `τ` captured on `cap`, its output unchanged;
* if `M` does not stop by `d`, the host reaches some `tmo r` within `5d + 2|w| + 2` steps;
and neither `fin` nor `tmo` is reached earlier. -/
private def DzClockSpec {m : ℕ} {S : Type} (M : MultiTapeTM m Bool S) (stop : S → Bool) {Qc : Type}
    (H : MultiTapeTM (((1 + m) + 1) + 1) Bool Qc) (inj : S × Bool → Qc)
    (fin tmo : Option (S × Bool) → Qc) : Prop :=
  ∀ {K : ℕ} {x y : List Bool} (buf cap ctr : Fin K) (β : Fin m ↪ Fin K) (h1 : buf ≠ cap)
    (h2 : buf ≠ ctr) (h3 : cap ≠ ctr) (hb : buf ∉ Set.range β) (hc : cap ∉ Set.range β)
    (hk : ctr ∉ Set.range β) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool)
    (c : Cfg m Bool S y) (q : S) (w : List Bool),
    c.state = some q → c.inputPos = 1 → c.output = [] →
    T buf = FinTM.bufferTape y → P buf = 0 →
    (∀ i, T (β i) = c.workTapes i ∧ P (β i) = c.workTapePos i) →
    T cap = FinTM.bufferTape [] → P cap = 0 → T ctr = FinTM.bufferTape w → P ctr = 0 →
    (∀ τ ≤ Nat.ofDigits 2 (w.map Bool.toNat), (M.runFrom c τ).Stopped stop →
      (∀ u < τ, ¬(M.runFrom c u).Stopped stop) →
      ∃ t ≤ 5 * τ + 2 * w.length + 2, ∃ (b : Bool) (T' : Fin K → ℤ → Option Bool)
        (P' : Fin K → ℤ),
        (embedEmitTM (dzClkEmb buf cap ctr β h1 h2 h3 hb hc hk) H).runFrom
            (qyC (x := x) (inj (q, true)) 1 T P o) t =
          qyC (fin ((M.runFrom c τ).state.map fun s => (s, b))) 1 T' P' o ∧
        T' cap = FinTM.bufferTape (M.runFrom c τ).output ∧
        P' cap = ((M.runFrom c τ).output.length : ℤ) ∧
        ∀ u < t, ∀ r,
          ((embedEmitTM (dzClkEmb buf cap ctr β h1 h2 h3 hb hc hk) H).runFrom
            (qyC (x := x) (inj (q, true)) 1 T P o) u).state ≠ some (fin r) ∧
          ((embedEmitTM (dzClkEmb buf cap ctr β h1 h2 h3 hb hc hk) H).runFrom
            (qyC (x := x) (inj (q, true)) 1 T P o) u).state ≠ some (tmo r)) ∧
    ((∀ u ≤ Nat.ofDigits 2 (w.map Bool.toNat), ¬(M.runFrom c u).Stopped stop) →
      ∃ t ≤ 5 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 2,
        ∃ (r : Option (S × Bool)) (T' : Fin K → ℤ → Option Bool) (P' : Fin K → ℤ),
        (embedEmitTM (dzClkEmb buf cap ctr β h1 h2 h3 hb hc hk) H).runFrom
            (qyC (x := x) (inj (q, true)) 1 T P o) t = qyC (tmo r) 1 T' P' o ∧
        ∀ u < t, ∀ r,
          ((embedEmitTM (dzClkEmb buf cap ctr β h1 h2 h3 hb hc hk) H).runFrom
            (qyC (x := x) (inj (q, true)) 1 T P o) u).state ≠ some (fin r) ∧
          ((embedEmitTM (dzClkEmb buf cap ctr β h1 h2 h3 hb hc hk) H).runFrom
            (qyC (x := x) (inj (q, true)) 1 T P o) u).state ≠ some (tmo r))

/-- **The clocked, hosted run** (a composition of the step clock and the virtual-input host, not a
new host): for every finite machine `M` and stop predicate there is a step clock over
`Turing.vhostSilentTM M` whose `fin` is injective and distinct from its `tmo`, with the hosted
clock's clause `DzClockSpec`. Both of the diagonalizer's simulators run through it.

**Proof sketch.** Take `Turing.exists_stepClockTMVia` over `Turing.vhostSilentTM M` with the
identity digit embedding and the stop predicate read on the hosted state. The selected bank of the
normal-form configuration is the clock's start over `Turing.vhostSilentCfg c true 1 [] []`, field by
field (`Turing.clockCfg`'s equations, `Turing.vhostSilentCfg_eq`, the silent transport's and
`Turing.vhostCfg`'s field equations, split by `Fin.lastCases` and `Fin.addCases`). The hosted run is
`M`'s run transported (`Turing.vhostSilentTM_runFrom`, the tag `true` valid at input head `1` by
`Turing.FinTM.VirtualTag_iff`), and it stops exactly when `M` does (`Turing.Cfg.stopped_iff`). The
clock's two clauses then give the endpoints, read back through the forwarding embedding
(`qy_embed_gen`, `Turing.embedEmitCfg`'s equations): the state is `fin` or `tmo` of the hosted
state, the input head stays `1`, the output gains `M`'s physical output, which is empty, and the
capture tape holds `M`'s output (`Turing.embedSilentCfg_cap`). The cuts are the clock's, read
through `qy_embed_state`. -/
private theorem dz_clock_exists {m : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (M : MultiTapeTM m Bool S) (stop : S → Bool) :
    ∃ (Qc : Type) (_ : Fintype Qc) (_ : DecidableEq Qc)
      (H : MultiTapeTM (((1 + m) + 1) + 1) Bool Qc) (inj : S × Bool → Qc)
      (fin tmo : Option (S × Bool) → Qc),
      Function.Injective fin ∧ (∀ a b, fin a ≠ tmo b) ∧ DzClockSpec M stop H inj fin tmo := by
  obtain ⟨Qc, hQ, hdQ, H, inj, fin, tmo, hfi, -, hft, -, hH⟩ :=
    exists_stepClockTMVia (Function.Embedding.refl Bool) (vhostSilentTM M)
      (fun qb : S × Bool => stop qb.1)
  refine ⟨Qc, hQ, hdQ, H, inj, fin, tmo, hfi, hft, ?_⟩
  intro K x y buf cap ctr β h1 h2 h3 hb hc hk T P o c q w hcs hci hco hTb hPb hβ hTc hPc hTk hPk
  set σ := dzClkEmb buf cap ctr β h1 h2 h3 hb hc hk with hσ
  have hcapL : (Fin.last (1 + m) : Fin ((1 + m) + 1)) = vhostCap m := by
    rw [vhostCap_eq]
    exact Fin.ext (by simp)
  have hcapR : vhostCap m ∉ Set.range (Fin.castAddEmb 1 : Fin (1 + m) ↪ Fin ((1 + m) + 1)) := by
    rintro ⟨i, hi⟩
    have := congrArg Fin.val hi
    rw [vhostCap_eq] at this
    simp at this
    omega
  -- the fields of a hosted configuration
  have hVst : ∀ (c' : Cfg m Bool S y) (b : Bool),
      (vhostSilentCfg c' b (1 : Fin (x.length + 2)) [] []).state =
        c'.state.map fun s => (s, b) := by
    intro c' b
    rw [vhostSilentCfg_eq, embedSilentCfg_state, vhostCfg_state]
  have hVin : ∀ (c' : Cfg m Bool S y) (b : Bool),
      (vhostSilentCfg c' b (1 : Fin (x.length + 2)) [] []).inputPos = 1 := by
    intro c' b
    rw [vhostSilentCfg_eq, embedSilentCfg_inputPos, vhostCfg_inputPos]
  have hVout : ∀ (c' : Cfg m Bool S y) (b : Bool),
      (vhostSilentCfg c' b (1 : Fin (x.length + 2)) [] []).output = [] := by
    intro c' b
    rw [vhostSilentCfg_eq, embedSilentCfg_output]
  have hVcap : ∀ (c' : Cfg m Bool S y) (b : Bool),
      (vhostSilentCfg c' b (1 : Fin (x.length + 2)) [] []).workTapes (Fin.last (1 + m)) =
        FinTM.bufferTape c'.output ∧
      (vhostSilentCfg c' b (1 : Fin (x.length + 2)) [] []).workTapePos (Fin.last (1 + m)) =
        (c'.output.length : ℤ) := by
    intro c' b
    rw [hcapL, vhostSilentCfg_eq]
    obtain ⟨e1, e2⟩ := embedSilentCfg_cap (Fin.castAddEmb 1) (vhostCap m) hcapR
      (fun _ _ => none) (fun _ => 0) [] [] (vhostCfg c' b (1 : Fin (x.length + 2)) [])
    rw [e1, e2, vhostCfg_output, List.nil_append, List.nil_append]
    exact ⟨rfl, rfl⟩
  have hVsel : ∀ (c' : Cfg m Bool S y) (b : Bool) (j : Fin (1 + m)),
      (vhostSilentCfg c' b (1 : Fin (x.length + 2)) [] []).workTapes j.castSucc =
        (vhostCfg c' b (1 : Fin (x.length + 2)) []).workTapes j ∧
      (vhostSilentCfg c' b (1 : Fin (x.length + 2)) [] []).workTapePos j.castSucc =
        (vhostCfg c' b (1 : Fin (x.length + 2)) []).workTapePos j := by
    intro c' b j
    have e : j.castSucc = Fin.castAddEmb 1 j := rfl
    rw [e, vhostSilentCfg_eq, embedSilentCfg_selected_tape, embedSilentCfg_selected_pos]
    exact ⟨rfl, rfl⟩
  set V : Cfg ((1 + m) + 1) Bool (S × Bool) x := vhostSilentCfg c true 1 [] [] with hV
  have hVs : V.state = some (q, true) := by rw [hV, hVst, hcs]; rfl
  -- the selected bank is the clock's start
  have hstart : (qyC (x := x) (inj (q, true)) 1 (fun i => T (σ i)) (fun i => P (σ i)) [] :
      Cfg (((1 + m) + 1) + 1) Bool Qc x) = clockCfg (some (inj (q, true))) V (T ctr) 0 := by
    apply Cfg.ext
    · rw [clockCfg_state]
      rfl
    · rw [clockCfg_inputPos, hV, hVin]
      rfl
    · funext j a
      rw [clockCfg_workTapes]
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.lastCases_last]
        show T (σ (Fin.last _)) a = _
        rw [hσ, dzClkEmb_ctr]
      | cast j =>
        rw [Fin.lastCases_castSucc]
        induction j using Fin.lastCases with
        | last =>
          show T (σ (Fin.last _).castSucc) a = _
          rw [hσ, dzClkEmb_cap, hTc, (hVcap c true).1, hco]
        | cast j =>
          rw [(hVsel c true j).1, vhostCfg_workTapes]
          induction j using Fin.addCases with
          | left a0 =>
            show T (σ (Fin.castAdd m a0).castSucc.castSucc) a = _
            rw [hσ, dzClkEmb_buf, Fin.addCases_left, hTb]
          | right i =>
            show T (σ (Fin.natAdd 1 i).castSucc.castSucc) a = _
            rw [hσ, dzClkEmb_bank, Fin.addCases_right, (hβ i).1]
    · funext j
      rw [clockCfg_workTapePos]
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.lastCases_last]
        show P (σ (Fin.last _)) = _
        rw [hσ, dzClkEmb_ctr, hPk]
      | cast j =>
        rw [Fin.lastCases_castSucc]
        induction j using Fin.lastCases with
        | last =>
          show P (σ (Fin.last _).castSucc) = _
          rw [hσ, dzClkEmb_cap, hPc, (hVcap c true).2, hco]
          rfl
        | cast j =>
          rw [(hVsel c true j).2, vhostCfg_workTapePos]
          induction j using Fin.addCases with
          | left a0 =>
            show P (σ (Fin.castAdd m a0).castSucc.castSucc) = _
            rw [hσ, dzClkEmb_buf, Fin.addCases_left, hPb, hci]
            rfl
          | right i =>
            show P (σ (Fin.natAdd 1 i).castSucc.castSucc) = _
            rw [hσ, dzClkEmb_bank, Fin.addCases_right, (hβ i).2]
    · rw [clockCfg_output, hV, hVout]
      rfl
  -- the hosted run is `M`'s run, and it stops when `M` does
  have htag : FinTM.VirtualTag c.inputPos true := by
    rw [FinTM.VirtualTag_iff, hci]
    exact ⟨fun h => absurd h (by simp), fun _ => rfl⟩
  have hrunV : ∀ τ, ∃ b, (vhostSilentTM M).runFrom V τ =
      vhostSilentCfg (M.runFrom c τ) b (1 : Fin (x.length + 2)) [] [] := by
    intro τ
    obtain ⟨b, -, h⟩ := vhostSilentTM_runFrom M c true htag (1 : Fin (x.length + 2)) [] [] τ
    exact ⟨b, h⟩
  have hstopV : ∀ τ, ((vhostSilentTM M).runFrom V τ).Stopped (fun qb : S × Bool => stop qb.1) ↔
      (M.runFrom c τ).Stopped stop := by
    intro τ
    obtain ⟨b, hb⟩ := hrunV τ
    rw [hb, Cfg.stopped_iff, Cfg.stopped_iff, hVst]
    constructor
    · rintro (h | ⟨s, hs, hst⟩)
      · exact Or.inl (Option.map_eq_none_iff.mp h)
      · obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp hs
        exact Or.inr ⟨s', hs', hst⟩
    · rintro (h | ⟨s, hs, hst⟩)
      · exact Or.inl (by rw [h]; rfl)
      · exact Or.inr ⟨(s, b), by rw [hs]; rfl, hst⟩
  have hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      T ctr (0 + p) = FinTM.bufferTape (w.map (Function.Embedding.refl Bool)) p := by
    intro p _ _
    rw [zero_add, hTk, Function.Embedding.coe_refl, List.map_id]
  obtain ⟨hfin, hto⟩ := hH V (q, true) hVs w (T ctr) 0 hw
  -- reading an endpoint of the clock back through the embedding
  have hread : ∀ (s : Qc) (c' : Cfg m Bool S y) (b : Bool) (ct : ℤ → Option Bool) (cp : ℤ),
      embedEmitCfg σ T P o
          (clockCfg (some s) (vhostSilentCfg c' b (1 : Fin (x.length + 2)) [] []) ct cp) =
        qyC s 1 (embedEmitCfg σ T P o
          (clockCfg (some s) (vhostSilentCfg c' b (1 : Fin (x.length + 2)) [] []) ct cp)).workTapes
          (embedEmitCfg σ T P o
          (clockCfg (some s) (vhostSilentCfg c' b (1 : Fin (x.length + 2)) [] []) ct
            cp)).workTapePos o := by
    intro s c' b ct cp
    apply Cfg.ext
    · rw [embedEmitCfg_state, clockCfg_state]
      rfl
    · rw [embedEmitCfg_inputPos, clockCfg_inputPos, hVin]
      rfl
    · rfl
    · rfl
    · rw [embedEmitCfg_output, clockCfg_output, hVout, List.append_nil]
      rfl
  have hcut : ∀ u, ((embedEmitTM σ H).runFrom (qyC (x := x) (inj (q, true)) 1 T P o) u).state =
      (H.runFrom (clockCfg (some (inj (q, true))) V (T ctr) 0) u).state := by
    intro u
    rw [qy_embed_state, hstart]
  refine ⟨fun τ hτ hst hfirst => ?_, fun hns => ?_⟩
  · obtain ⟨t, ht, w', -, hrunH, hcutH, -⟩ := hfin τ hτ ((hstopV τ).mpr hst)
      (fun u hu h => hfirst u hu ((hstopV u).mp h))
    obtain ⟨b, hb⟩ := hrunV τ
    rw [hb] at hrunH
    obtain ⟨E, hE⟩ : ∃ E, E = embedEmitCfg σ T P o
        (clockCfg (some (fin
            (vhostSilentCfg (M.runFrom c τ) b (1 : Fin (x.length + 2)) [] []).state))
          (vhostSilentCfg (M.runFrom c τ) b (1 : Fin (x.length + 2)) [] [])
          (wordPatch (T ctr) 0 (w'.map (Function.Embedding.refl Bool))) 0) := ⟨_, rfl⟩
    have ecap := embedEmitCfg_selected_tape σ T P o
      (clockCfg (some (fin (vhostSilentCfg (M.runFrom c τ) b (1 : Fin (x.length + 2)) [] []).state))
        (vhostSilentCfg (M.runFrom c τ) b (1 : Fin (x.length + 2)) [] [])
        (wordPatch (T ctr) 0 (w'.map (Function.Embedding.refl Bool))) 0) (Fin.last _).castSucc
    have epos := embedEmitCfg_selected_pos σ T P o
      (clockCfg (some (fin (vhostSilentCfg (M.runFrom c τ) b (1 : Fin (x.length + 2)) [] []).state))
        (vhostSilentCfg (M.runFrom c τ) b (1 : Fin (x.length + 2)) [] [])
        (wordPatch (T ctr) 0 (w'.map (Function.Embedding.refl Bool))) 0) (Fin.last _).castSucc
    rw [← hE, hσ, dzClkEmb_cap] at ecap epos
    refine ⟨t, ht, b, E.workTapes, E.workTapePos, ?_, ?_, ?_, fun u hu r => ?_⟩
    · rw [qy_embed_gen, hstart, hrunH, hread, ← hE, hVst]
    · funext a
      rw [ecap, clockCfg_workTapes, Fin.lastCases_castSucc, (hVcap _ b).1]
    · rw [epos, clockCfg_workTapePos, Fin.lastCases_castSucc, (hVcap _ b).2]
    · rw [hcut]
      exact hcutH u hu r
  · obtain ⟨t, ht, w', -, hrunH, hcutH, -⟩ := hto (fun u hu h => hns u hu ((hstopV u).mp h))
    obtain ⟨b, hb⟩ := hrunV (Nat.ofDigits 2 (w.map Bool.toNat))
    rw [hb] at hrunH
    obtain ⟨E, hE⟩ : ∃ E, E = embedEmitCfg σ T P o
        (clockCfg (some (tmo (vhostSilentCfg (M.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat))) b
          (1 : Fin (x.length + 2)) [] []).state))
          (vhostSilentCfg (M.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat))) b
            (1 : Fin (x.length + 2)) [] [])
          (wordPatch (T ctr) 0 (w'.map (Function.Embedding.refl Bool))) 0) := ⟨_, rfl⟩
    refine ⟨t, ht, (vhostSilentCfg (M.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat))) b
      (1 : Fin (x.length + 2)) [] []).state, E.workTapes, E.workTapePos, ?_, fun u hu r => ?_⟩
    · rw [qy_embed_gen, hstart, hrunH, hread, ← hE]
    · rw [hcut]
      exact hcutH u hu r

/-! ### The diagonalizer's kit -/

/-- **The inner second component** of a pair's first component: on `⟨⟨B, α⟩, N⟩` it is `α`
(`dz_alpha_eq`). It is the function of the composite extractor the middle calls on the query's
tail. -/
private def dzAlpha (z : List Bool) : List Bool :=
  ((pairDecode (((pairDecode z).map Prod.fst).getD [])).map Prod.snd).getD []

/-- The inner second component of `⟨⟨B, α⟩, N⟩` is `α`. -/
private theorem dz_alpha_eq (B α N : List Bool) : dzAlpha (pairEncode (pairEncode B α) N) = α := by
  unfold dzAlpha
  rw [pairDecode_pairEncode, Option.map_some, Option.getD_some, pairDecode_pairEncode,
    Option.map_some, Option.getD_some]

/-- A function computed in time `T` has outputs of length at most `T` of the input's length: each
step emits at most one symbol. -/
private theorem dz_out_le {M : FinTM Bool} {F : List Bool → List Bool} {T : ℕ → ℕ}
    (h : M.ComputesFunInTime F T) (y : List Bool) : (F y).length ≤ T y.length := by
  have h' := (FinTM.computesInTime_iff _ _ _ _).mp ((FinTM.computesFunInTime_iff _ _ _).mp h y)
  rw [← h'.2]
  exact MultiTapeTM.output_length_le _ _ _

/-- **The diagonalizer's kit** for time-constructible `f`, `g`, a scheme `c` and a decider `BF`: the
calls of the setup and of the middle's preparation with their clauses, the interpreter core with
its contract, and the hosted clocks over the core and over `BF` with their clauses. -/
private structure DzKit (f g : ℕ → ℕ) (c : EffectiveNDMachineCode) (BF : FinTM Bool) : Type 1 where
  /-- `g` is at least the identity -/
  hg : ∀ n, n ≤ g n
  /-- the input call of the stage query -/
  qc : FinTM Bool
  qcE : qc.State
  qcX : qc.State
  qcK : 0 < qc.k
  qcA : ℕ
  qcS : QyInSpec qc qcE qcX (query f g) (fun n => qcA * (g n + 1))
  qcL : ∀ x : List Bool, (query f g x).length ≤ qcA * (g x.length + 1)
  /-- the input call of `g`'s witness -/
  gc : FinTM Bool
  gcE : gc.State
  gcX : gc.State
  gcK : 0 < gc.k
  gcA : ℕ
  gcS : QyInSpec gc gcE gcX (fun x => Nat.bits (g x.length)) (fun n => gcA * (g n + 1))
  /-- the input call prepending `true` -/
  pc : FinTM Bool
  pcE : pc.State
  pcX : pc.State
  pcK : 0 < pc.k
  pcA : ℕ
  pcS : QyInSpec pc pcE pcX (fun x => [true] ++ x) (fun n => pcA * (g n + 1))
  /-- the install call of `y ↦ bits |y|` -/
  lc : FinTM Bool
  lcE : lc.State
  lcX : lc.State
  lcK : 0 < lc.k
  lcA : ℕ
  lcS : QySpec lc lcE lcX (fun y => Nat.bits y.length) (fun y => lcA * (y.length + 1))
  /-- the install call of the inner second component -/
  ac : FinTM Bool
  acE : ac.State
  acX : ac.State
  acK : 0 < ac.k
  acA : ℕ
  acS : QySpec ac acE acX dzAlpha (fun y => acA * (y.length + 1))
  /-- the interpreter core -/
  kR : ℕ
  SR : Type
  [SRf : Fintype SR]
  [SRd : DecidableEq SR]
  R : MultiTapeTM kR Bool SR
  jR : Fin kR
  rE : SR
  rA : SR
  rJ : SR
  hAJ : rA ≠ rJ
  hR : ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ) (s : List Bool), t ≤ s.length →
    ∃ T, T ≤ C * (t + 1) ∧
      (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR rE s) T).state =
        some (if ((c.decode α).toFinNDTM.tm.runWith (s.take t)
              ((c.decode α).toFinNDTM.tm.initCfg x)).state = none ∧
            ((c.decode α).toFinNDTM.tm.runWith (s.take t)
              ((c.decode α).toFinNDTM.tm.initCfg x)).output = [true] then rA else rJ) ∧
      ∀ u < T,
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR rE s) u).state ≠
            some rA ∧
          (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR rE s)
            u).state ≠ some rJ
  /-- the clock over the hosted core -/
  QR : Type
  [QRf : Fintype QR]
  [QRd : DecidableEq QR]
  HR : MultiTapeTM (((1 + kR) + 1) + 1) Bool QR
  iR : SR × Bool → QR
  fR : Option (SR × Bool) → QR
  oR : Option (SR × Bool) → QR
  fRi : Function.Injective fR
  fRo : ∀ a b, fR a ≠ oR b
  cR : DzClockSpec R (fun q => decide (q = rA ∨ q = rJ)) HR iR fR oR
  /-- the clock over the hosted decider -/
  QB : Type
  [QBf : Fintype QB]
  [QBd : DecidableEq QB]
  HB : MultiTapeTM (((1 + BF.k) + 1) + 1) Bool QB
  iB : BF.State × Bool → QB
  fB : Option (BF.State × Bool) → QB
  oB : Option (BF.State × Bool) → QB
  fBo : ∀ a b, fB a ≠ oB b
  cB : DzClockSpec BF.tm (fun _ => false) HB iB fB oB

attribute [local instance] DzKit.SRf DzKit.SRd DzKit.QRf DzKit.QRd DzKit.QBf DzKit.QBd

/-- **The kit exists** for time-constructible `f` and `g`, every scheme and every decider.

**Proof sketch.** Read `g`'s witness through `Complexity.timeConstructible_iff`. The input calls
(`Turing.FinTM.exists_inputCallTM`, through `qy_inputSpec`) of the stage query
(`Turing.NTimeDiag.exists_queryTM`), of `g`'s witness and of the published prepend row; the install
calls (`qy_installSpec`) of `computesFunInTime_lengthBits` and of the composite extractor
(`Turing.FinTM.computesFunInTime_comp` of `pairExtractTM_fst` and `pairExtractTM_snd`); the
interpreter core (`Turing.exists_ndInterpreterCore`, its start being `Turing.streamStartCfg` by the
field equations); and the hosted clocks (`dz_clock_exists`). Each call's bound
`c (T |y| + |y| + |F y| + 1)` is at most the kit's simplified bound, since a function computed in
time `T` has outputs of length at most `T` (`dz_out_le`), `|bits m| ≤ m`
(`Turing.length_bits_le_self`) and `n ≤ g n`. -/
private theorem dz_kit_exists {f g : ℕ → ℕ} (hf : Complexity.TimeConstructible f)
    (hg : Complexity.TimeConstructible g) (c : EffectiveNDMachineCode) (BF : FinTM Bool) :
    Nonempty (DzKit f g c BF) := by
  obtain ⟨hgle, cgc, -, Mg, hMg⟩ := (Complexity.timeConstructible_iff g).mp hg
  have hMg' : Mg.ComputesFunInTime (fun y => Nat.bits (g y.length)) (fun m => cgc * (g m + 1)) :=
    (FinTM.computesFunInTime_iff _ _ _).mpr hMg
  obtain ⟨G, CG, hG⟩ := exists_queryTM hf hg
  obtain ⟨qc, qcE, qcX, qcc, qcK, qcS⟩ := qy_inputSpec G _ _ hG
  obtain ⟨gc, gcE, gcX, gcc, gcK, gcS⟩ := qy_inputSpec Mg _ _ hMg'
  obtain ⟨Mp, cp, hMp⟩ := FinTM.computesFunInTime_prepend [true]
  obtain ⟨pc, pcE, pcX, pcc, pcK, pcS⟩ := qy_inputSpec Mp _ _ hMp
  obtain ⟨Lb, cL, hLb⟩ := FinTM.computesFunInTime_lengthBits
  obtain ⟨lc, lcE, lcX, lcc, lcK, lcS⟩ := qy_installSpec Lb _ _ hLb
  obtain ⟨Ma, ca, hMa⟩ := FinTM.computesFunInTime_comp FinTM.pairExtractTM_fst
    FinTM.pairExtractTM_snd (fun a b hab => by
      show 5 * (a + 1) ≤ 5 * (b + 1)
      omega)
  have he : ((fun x => (Option.map Prod.snd (pairDecode x)).getD []) ∘
      (fun x => (Option.map Prod.fst (pairDecode x)).getD [])) = dzAlpha := by
    funext z
    rfl
  rw [he] at hMa
  obtain ⟨ac, acE, acX, acc, acK, acS⟩ := qy_installSpec Ma _ _ hMa
  obtain ⟨kR, SR, hSRf, hSRd, R, jR, rE, rA, rJ, hAJ, hR⟩ := exists_ndInterpreterCore c
  obtain ⟨QR, hQRf, hQRd, HR, iR, fR, oR, hfR, hfoR, cR⟩ :=
    @dz_clock_exists _ _ hSRf hSRd R (fun q => decide (q = rA ∨ q = rJ))
  obtain ⟨QB, hQBf, hQBd, HB, iB, fB, oB, -, hfoB, cB⟩ := dz_clock_exists BF.tm (fun _ => false)
  -- the bounds
  have qcS' : QyInSpec qc qcE qcX (query f g)
      (fun n => (qcc + 1) * (2 * CG + 1) * (g n + 1)) := by
    intro x
    obtain ⟨t, ht, h1, h2, h3⟩ := qcS x
    refine ⟨t, ht.trans ?_, h1, h2, h3⟩
    have hL := dz_out_le hG x
    have hn := hgle x.length
    try dsimp only at hL ⊢
    nlinarith
  have qcL : ∀ x : List Bool,
      (query f g x).length ≤ (qcc + 1) * (2 * CG + 1) * (g x.length + 1) := by
    intro x
    have hL := dz_out_le hG x
    try dsimp only at hL
    nlinarith
  have gcS' : QyInSpec gc gcE gcX (fun x => Nat.bits (g x.length))
      (fun n => gcc * (cgc + 3) * (g n + 1)) := by
    intro x
    obtain ⟨t, ht, h1, h2, h3⟩ := gcS x
    refine ⟨t, ht.trans ?_, h1, h2, h3⟩
    have hb := length_bits_le_self (g x.length)
    have hn := hgle x.length
    try dsimp only
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have pcS' : QyInSpec pc pcE pcX (fun x => [true] ++ x) (fun n => pcc * (cp + 3) * (g n + 1)) := by
    intro x
    obtain ⟨t, ht, h1, h2, h3⟩ := pcS x
    refine ⟨t, ht.trans ?_, h1, h2, h3⟩
    have hn := hgle x.length
    try dsimp only
    rw [List.length_append, List.length_singleton, mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have lcS' : QySpec lc lcE lcX (fun y => Nat.bits y.length)
      (fun y => lcc * (cL + 3) * (y.length + 1)) := by
    refine lcS.mono fun y => ?_
    have hb := length_bits_le_self y.length
    try dsimp only
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have acS' : QySpec ac acE acX dzAlpha (fun y => acc * (72 * ca + 1) * (y.length + 1)) := by
    refine acS.mono fun y => ?_
    have hL := dz_out_le hMa y
    try dsimp only at hL ⊢
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have hss : ∀ (z s : List Bool), streamStartCfg z jR rE s =
      (⟨some rE, 1, fun i => if i = jR then FinTM.bufferTape s else fun _ => none, fun _ => 0, []⟩ :
        Cfg kR Bool SR z) := by
    intro z s
    apply Cfg.ext
    · rw [streamStartCfg_state]
    · rw [streamStartCfg_inputPos]
    · funext i a
      rw [streamStartCfg_workTapes]
    · funext i
      rw [streamStartCfg_workTapePos]
    · rw [streamStartCfg_output]
  have hR' : ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ) (s : List Bool), t ≤ s.length →
      ∃ T, T ≤ C * (t + 1) ∧
        (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR rE s) T).state =
          some (if ((c.decode α).toFinNDTM.tm.runWith (s.take t)
                ((c.decode α).toFinNDTM.tm.initCfg x)).state = none ∧
              ((c.decode α).toFinNDTM.tm.runWith (s.take t)
                ((c.decode α).toFinNDTM.tm.initCfg x)).output = [true] then rA else rJ) ∧
        ∀ u < T,
          (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR rE s)
              u).state ≠ some rA ∧
            (R.runFrom (streamStartCfg (pairEncode (pairEncode (Nat.bits t) α) x) jR rE s)
              u).state ≠ some rJ := by
    intro α
    obtain ⟨C, hC⟩ := hR α
    refine ⟨C, fun x t s hts => ?_⟩
    obtain ⟨T, -, hT, hst, hcut⟩ := hC x t s hts
    rw [hss]
    exact ⟨T, hT, hst, hcut⟩
  exact ⟨{ hg := hgle
           qc := qc, qcE := qcE, qcX := qcX, qcK := qcK, qcA := (qcc + 1) * (2 * CG + 1)
           qcS := qcS', qcL := qcL
           gc := gc, gcE := gcE, gcX := gcX, gcK := gcK, gcA := gcc * (cgc + 3), gcS := gcS'
           pc := pc, pcE := pcE, pcX := pcX, pcK := pcK, pcA := pcc * (cp + 3), pcS := pcS'
           lc := lc, lcE := lcE, lcX := lcX, lcK := lcK, lcA := lcc * (cL + 3), lcS := lcS'
           ac := ac, acE := acE, acX := acX, acK := acK, acA := acc * (72 * ca + 1), acS := acS'
           kR := kR, SR := SR, SRf := hSRf, SRd := hSRd, R := R, jR := jR, rE := rE, rA := rA
           rJ := rJ, hAJ := hAJ, hR := hR'
           QR := QR, QRf := hQRf, QRd := hQRd, HR := HR, iR := iR, fR := fR, oR := oR, fRi := hfR
           fRo := hfoR, cR := @cR
           QB := QB, QBf := hQBf, QBd := hQBd, HB := HB, iB := iB, fB := fB, oB := oB
           fBo := hfoB, cB := @cB }⟩

/-! ### The tape layout -/

/-- The tape count of the diagonalizer: fourteen named tapes, then one block per bank (a call's
tape `0` is a named tape, its other tapes its block; the core's stream tape is the block tape). -/
private def DzKit.K {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : ℕ :=
  14 + κ.qc.k + κ.gc.k + κ.pc.k + κ.lc.k + κ.ac.k + κ.kR + BF.k

/-- The named tapes come first. -/
private theorem DzKit.le_K {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : 14 ≤ κ.K := by
  unfold DzKit.K
  omega

/-- The named tape `i`: `0` the query, `1` the bits of `g n`, `2` the word `1^{n + 1}`, `3` the
clock's counter, `4` and `5` the block's expansion counters, `6` the block (the guessed stream and
budget word), `7` the ruler, `8` the query's tail, `9` the budget word, `10` its expansion and
bits, `11` the core's input, `12` the hosted capture, `13` the decider's first tape. -/
private def DzKit.tp {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (i : Fin 14) : Fin κ.K :=
  Fin.castLE κ.le_K i

/-- The value of a named tape. -/
private theorem DzKit.tp_val {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (i : Fin 14) : (κ.tp i : ℕ) = i := rfl

/-- Named tapes are distinct when their names are. -/
private theorem DzKit.tp_ne {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) {a b : Fin 14} (h : a ≠ b) : κ.tp a ≠ κ.tp b :=
  fun e => h (Fin.castLE_injective κ.le_K e)

/-- **A layout**: the named tapes' values `L`, and the default `d` on every other tape. -/
private def dzLay {K : ℕ} {α : Type} (L : Fin 14 → α) (d : α) : Fin K → α :=
  fun t => if h : (t : ℕ) < 14 then L ⟨t, h⟩ else d

/-- A layout on a named tape. -/
private theorem dzLay_tp {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) {α : Type} (L : Fin 14 → α) (d : α) (i : Fin 14) :
    dzLay L d (κ.tp i) = L i := by
  unfold dzLay
  rw [dif_pos (by rw [κ.tp_val]; exact i.isLt)]
  rfl

/-- A layout off the named tapes. -/
private theorem dzLay_off {K : ℕ} {α : Type} (L : Fin 14 → α) (d : α) (t : Fin K)
    (ht : 14 ≤ (t : ℕ)) : dzLay L d t = d := by
  unfold dzLay
  rw [dif_neg (by omega)]

/-- Updating a layout on a named tape updates its values. -/
private theorem dzLay_update {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) {α : Type} (L : Fin 14 → α) (d : α) (i : Fin 14) (v : α) :
    Function.update (dzLay L d) (κ.tp i) v = dzLay (Function.update L i v) d := by
  funext t
  by_cases ht : (t : ℕ) < 14
  · have e : t = κ.tp ⟨t, ht⟩ := Fin.ext rfl
    rw [e, dzLay_tp]
    by_cases hi : (⟨t, ht⟩ : Fin 14) = i
    · rw [hi, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (κ.tp_ne hi), Function.update_of_ne hi, dzLay_tp]
  · have hne : t ≠ κ.tp i := fun e => ht (by rw [e, κ.tp_val]; exact i.isLt)
    rw [Function.update_of_ne hne, dzLay_off _ _ _ (by omega), dzLay_off _ _ _ (by omega)]

/-- The blank tapes and the zero heads are layouts. -/
private theorem dzLay_const {K : ℕ} {α : Type} (d : α) :
    (fun _ => d : Fin K → α) = dzLay (fun _ => d) d := by
  funext t
  unfold dzLay
  split <;> rfl

/-- A bank tape other than tape `0` lies in its block, off the named tapes. -/
private theorem dz_bank_off {K : ℕ} (t0 : Fin K) (off k : ℕ) (hK : off + k ≤ K)
    (h0 : (t0 : ℕ) < off) (hoff : 14 ≤ off) (i : Fin k) (hi : (i : ℕ) ≠ 0) :
    14 ≤ (qyBank t0 off k hK h0 i : ℕ) := by
  rw [qyBank_val _ _ _ _ _ _ hi]
  omega

/-- The bank of the query's call, tape `0` on tape `0`. -/
private def DzKit.bQ {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Fin κ.qc.k ↪ Fin κ.K :=
  qyBank (κ.tp 0) 14 κ.qc.k (by unfold DzKit.K; omega) (by rw [κ.tp_val]; decide)

/-- The bank of `g`'s call, tape `0` on tape `1`. -/
private def DzKit.bG {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Fin κ.gc.k ↪ Fin κ.K :=
  qyBank (κ.tp 1) (14 + κ.qc.k) κ.gc.k (by unfold DzKit.K; omega)
    (by rw [κ.tp_val]; simp; omega)

/-- The bank of the prepend call, tape `0` on tape `2`. -/
private def DzKit.bP {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Fin κ.pc.k ↪ Fin κ.K :=
  qyBank (κ.tp 2) (14 + κ.qc.k + κ.gc.k) κ.pc.k (by unfold DzKit.K; omega)
    (by rw [κ.tp_val]; simp; omega)

/-- The bank of the length call, tape `0` on tape `10`. -/
private def DzKit.bL {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Fin κ.lc.k ↪ Fin κ.K :=
  qyBank (κ.tp 10) (14 + κ.qc.k + κ.gc.k + κ.pc.k) κ.lc.k (by unfold DzKit.K; omega)
    (by rw [κ.tp_val]; simp; omega)

/-- The bank of the extractor's call, tape `0` on tape `8`. -/
private def DzKit.bA {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Fin κ.ac.k ↪ Fin κ.K :=
  qyBank (κ.tp 8) (14 + κ.qc.k + κ.gc.k + κ.pc.k + κ.lc.k) κ.ac.k (by unfold DzKit.K; omega)
    (by rw [κ.tp_val]; simp; omega)

/-- The core's tapes: its stream tape `jR` on the block tape `6`, the others in their block. -/
private def DzKit.bR {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Fin κ.kR ↪ Fin κ.K :=
  (Equiv.swap (⟨0, Fin.pos κ.jR⟩ : Fin κ.kR) κ.jR).toEmbedding.trans
    (qyBank (κ.tp 6) (14 + κ.qc.k + κ.gc.k + κ.pc.k + κ.lc.k + κ.ac.k) κ.kR
      (by unfold DzKit.K; omega) (by rw [κ.tp_val]; simp; omega))

/-- The decider's tapes: its tape `0` on tape `13`, the others in their block. -/
private def DzKit.bB {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Fin BF.k ↪ Fin κ.K :=
  qyBank (κ.tp 13) (14 + κ.qc.k + κ.gc.k + κ.pc.k + κ.lc.k + κ.ac.k + κ.kR) BF.k
    (by unfold DzKit.K; omega) (by rw [κ.tp_val]; simp; omega)

/-- The core's stream tape is the block tape. -/
private theorem DzKit.bR_j {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : κ.bR κ.jR = κ.tp 6 := by
  unfold DzKit.bR
  rw [Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.swap_apply_right]
  rfl

/-- The core's other tapes are off the named tapes. -/
private theorem DzKit.bR_off {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (i : Fin κ.kR) (hi : i ≠ κ.jR) : 14 ≤ (κ.bR i : ℕ) := by
  unfold DzKit.bR
  rw [Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
  refine dz_bank_off _ _ _ _ _ (by omega) _ ?_
  intro h0
  have e : Equiv.swap (⟨0, Fin.pos κ.jR⟩ : Fin κ.kR) κ.jR i = ⟨0, Fin.pos κ.jR⟩ := Fin.ext h0
  rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at e
  exact hi e

/-! ### The setup -/

/-- The setup's phases: the three input calls (the query, `g`'s witness, the word `1^{n + 1}`); two
copies of `bits (g n)`; the block's stream cells by an expansion; the separator's counter and its
expansion; the budget word's copy into the block and the block's rewind; the ruler's expansion and
its rewind. -/
private inductive DzPK
  | q | g | p | c1 | c2 | e1 | w | e2 | cb | rb | e3 | rr

/-- The setup's phases have decidable equality (classically). -/
private noncomputable instance dzPKDecEq : DecidableEq DzPK := Classical.decEq _

/-- The setup's phases are finite. -/
private noncomputable instance dzPKFintype : Fintype DzPK :=
  Fintype.ofList [.q, .g, .p, .c1, .c2, .e1, .w, .e2, .cb, .rb, .e3, .rr]
    (by intro x; cases x <;> simp)

/-- The setup's phase carriers. -/
private abbrev DzPPh {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : DzPK → Type
  | .q => Unit ⊕ κ.qc.State
  | .g => Unit ⊕ κ.gc.State
  | .p => Unit ⊕ κ.pc.State
  | .c1 | .c2 | .cb => SweepPhase
  | .e1 | .e2 | .e3 => CounterLoopState (Fin ([true].length + 1))
  | .w => WritePhase [true].length
  | .rb | .rr => RewindPhase

/-- The setup's phase carriers are finite. -/
private instance dzPPhFintype {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (i : DzPK) : Fintype (DzPPh κ i) := by
  cases i <;> dsimp only [DzPPh] <;> infer_instance

/-- The setup's phase carriers have decidable equality. -/
private instance dzPPhDecEq {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (i : DzPK) : DecidableEq (DzPPh κ i) := by
  cases i <;> dsimp only [DzPPh] <;> infer_instance

/-- The setup's phase machines. -/
private def dzSetM {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : (i : DzPK) → MultiTapeTM κ.K Bool (DzPPh κ i)
  | .q => embedEmitTM κ.bQ (seamReleaseTM κ.qc.tm κ.qcE)
  | .g => embedEmitTM κ.bG (seamReleaseTM κ.gc.tm κ.gcE)
  | .p => embedEmitTM κ.bP (seamReleaseTM κ.pc.tm κ.pcE)
  | .c1 => copyMapTM κ.K (κ.tp 1) (κ.tp 3) (fun b => b) (fun _ b => b)
  | .c2 => copyMapTM κ.K (κ.tp 1) (κ.tp 4) (fun b => b) (fun _ b => b)
  | .e1 => embedEmitTM (qyEmb2 (κ.tp 6) (κ.tp 4) (κ.tp_ne (by decide))) (expandTM 1 0 [true])
  | .w => writeConstTM κ.K (κ.tp 5) [true]
  | .e2 => embedEmitTM (qyEmb2 (κ.tp 6) (κ.tp 5) (κ.tp_ne (by decide))) (expandTM 1 0 [true])
  | .cb => copyMapTM κ.K (κ.tp 1) (κ.tp 6) (fun b => b) (fun _ b => b)
  | .rb => rewindTM κ.K (κ.tp 6)
  | .e3 => embedEmitTM (qyEmb2 (κ.tp 7) (κ.tp 1) (κ.tp_ne (by decide))) (expandTM 1 0 [true])
  | .rr => rewindTM κ.K (κ.tp 7)

/-- The setup's dispatch table: each phase's exit enters the next; the last exit is the setup's. -/
private def dzSetRed {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : (i : DzPK) → DzPPh κ i → Option (Σ j, DzPPh κ j)
  | .q, s => if s = Sum.inr κ.qcX then some ⟨.g, Sum.inl ()⟩ else none
  | .g, s => if s = Sum.inr κ.gcX then some ⟨.p, Sum.inl ()⟩ else none
  | .p, s => if s = Sum.inr κ.pcX then some ⟨.c1, SweepPhase.sweep⟩ else none
  | .c1, s => if s = .done then some ⟨.c2, SweepPhase.sweep⟩ else none
  | .c2, s => if s = .done then some ⟨.e1, CounterLoopState.dec .run⟩ else none
  | .e1, s => if s = .done then some ⟨.w, WritePhase.wr 0⟩ else none
  | .w, s => if s = .done then some ⟨.e2, CounterLoopState.dec .run⟩ else none
  | .e2, s => if s = .done then some ⟨.cb, SweepPhase.sweep⟩ else none
  | .cb, s => if s = .done then some ⟨.rb, RewindPhase.start⟩ else none
  | .rb, s => if s = .done then some ⟨.e3, CounterLoopState.dec .run⟩ else none
  | .e3, s => if s = .done then some ⟨.rr, RewindPhase.start⟩ else none
  | .rr, _ => none

/-- **The setup** `P`: the phase host over the setup's phases, started at the query's call. -/
private def dzSet {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : MultiTapeTM κ.K Bool (Σ i, DzPPh κ i) :=
  phaseHostTM (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ)

/-- The setup's exit: the ruler's rewind done. -/
private def dzPexit {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Σ i, DzPPh κ i :=
  ⟨.rr, RewindPhase.done⟩

/-- **The block**: `g n` stream cells, the separator and the budget word, all `true` or the bits of
`g n` as the setup writes them; the guess overwrites it. -/
private def dzBlk (G : ℕ) : List Bool :=
  List.replicate G true ++ [true] ++ Nat.bits G

/-- The block's width: `g n + 1 + |bits (g n)|`. -/
private theorem dzBlk_length (G : ℕ) : (dzBlk G).length = G + 1 + (Nat.bits G).length := by
  unfold dzBlk
  simp only [List.length_append, List.length_replicate, List.length_singleton]

/-- The named tapes at the setup's exit: the query, the consumed counters (all `true`), the word
`1^{n + 1}`, the clock's counter `bits (g n)`, the block and the ruler; every other named tape
blank. -/
private def dzSetL (f g : ℕ → ℕ) (z : List Bool) : Fin 14 → ℤ → Option Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (fun _ => FinTM.bufferTape [])
      0 (FinTM.bufferTape (query f g z)))
      1 (FinTM.bufferTape (List.replicate (Nat.bits (g z.length)).length true)))
      2 (FinTM.bufferTape ([true] ++ z)))
      3 (FinTM.bufferTape (Nat.bits (g z.length))))
      4 (FinTM.bufferTape (List.replicate (Nat.bits (g z.length)).length true)))
      5 (FinTM.bufferTape (List.replicate 1 true)))
      6 (FinTM.bufferTape (dzBlk (g z.length))))
      7 (FinTM.bufferTape (List.replicate (g z.length) true))

/-- A call's bank over a layout whose bank tape `0` holds `arg`: the bank holds the seam of
`arg` (every other bank tape is off the named tapes, hence blank). -/
private theorem dz_arg_bank {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (L : Fin 14 → ℤ → Option Bool) (i0 : Fin 14) (off k : ℕ)
    (hK : off + k ≤ κ.K) (h0 : (κ.tp i0 : ℕ) < off) (hoff : 14 ≤ off) (hk : 0 < k)
    (arg : List Bool) (hL : L i0 = FinTM.bufferTape arg) :
    ∀ i, dzLay L (FinTM.bufferTape []) (qyBank (κ.tp i0) off k hK h0 i) =
      FinTM.bufferTape (stateWord k arg i) :=
  qy_arg_bank _ hk _ arg (by rw [qyBank_zero _ _ _ _ _ hk, dzLay_tp, hL])
    (fun i hi => dzLay_off _ _ _ (dz_bank_off _ _ _ _ _ hoff i hi))

/-- A call's bank over a head layout whose bank tape `0` is at `0`: every bank head is at `0`. -/
private theorem dz_zero_bank {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (Pn : Fin 14 → ℤ) (i0 : Fin 14) (off k : ℕ)
    (hK : off + k ≤ κ.K) (h0 : (κ.tp i0 : ℕ) < off) (hoff : 14 ≤ off) (hP : Pn i0 = 0) :
    ∀ i, dzLay Pn 0 (qyBank (κ.tp i0) off k hK h0 i) = 0 := by
  intro i
  by_cases hi : (i : ℕ) = 0
  · have hk : 0 < k := by have := i.isLt; omega
    rw [show i = ⟨0, hk⟩ from Fin.ext hi, qyBank_zero _ _ _ _ _ hk, dzLay_tp, hP]
  · exact dzLay_off _ _ _ (dz_bank_off _ _ _ _ _ hoff i hi)

/-- The setup's time bound for `g n = G`. -/
private def dzSetB {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (G : ℕ) : ℕ :=
  (κ.qcA + κ.gcA + κ.pcA + 40) * (G + 1)

/-- **The setup's run** (`P` as a contract): from the blank seam over the input `z`, the setup first
reaches its exit within `dzSetB κ (g |z|)` steps, at the layout `dzSetL z`, every head at `0`, the
input head at `1`, nothing emitted.

**Proof sketch.** Twelve hosted phases (`qy_hosted`, the last without dispatch by
`qy_hosted_last`), chained by `Turing.Segment.trans`: the three released input calls
(`qy_callHost` from the blank seam, `qy_blank_bank`) install the query, `bits (g n)` and
`1^{n + 1}` on tapes `0`, `1`, `2`; two copies of `bits (g n)` (`qy_copy`) give the clock's counter
and the block's first expansion counter; the expansions (`qy_expandHost`) write `1^{g n}` and one
more `true` (its counter `[true]` written by `qy_writeConst`) on the block tape; the copy of
`bits (g n)` appends the budget word; the rewind (`qy_rewind`) returns the block's head to `0`; the
ruler is `bits (g n)`'s expansion, rewound. Each guard is its row's cut, and only the last phase's
`done` is the exit. The tape function is a layout throughout (`dzLay_update`), and the times sum to
at most the bound since `|bits (g n)| ≤ g n` and each expansion's overhead is at most
`4d + 2|w| + 2` (`Turing.counterOverhead_le`). -/
private theorem dz_setup {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (z : List Bool) :
    ∃ TP ≤ dzSetB κ (g z.length),
      Segment (dzSet κ) {some (dzPexit κ)} (fun _ => True)
        (qyC (x := z) ⟨.q, Sum.inl ()⟩ 1 (fun _ => FinTM.bufferTape []) (fun _ => 0) [])
        (qyC (dzPexit κ) 1 (dzLay (dzSetL f g z) (FinTM.bufferTape []))
          (fun _ => 0) []) TP := by
  set G := g z.length with hG
  set F : Set (Option (Σ i, DzPPh κ i)) := {some (dzPexit κ)} with hF
  have hFq : ∀ (i : DzPK) (s : DzPPh κ i), i ≠ .rr → some ⟨i, s⟩ ∉ F := by
    intro i s hi h
    rw [hF, Set.mem_singleton_iff, Option.some_inj] at h
    exact hi (congrArg Sigma.fst h)
  set Bl : ℤ → Option Bool := FinTM.bufferTape [] with hBl
  set L0 : Fin 14 → ℤ → Option Bool := fun _ => Bl with hL0
  set Z0 : Fin 14 → ℤ := fun _ => 0 with hZ0
  have hT0 : (fun _ => Bl) = (dzLay L0 Bl : Fin κ.K → _) := dzLay_const _
  have hP0 : (fun _ => (0 : ℤ)) = (dzLay Z0 0 : Fin κ.K → ℤ) := dzLay_const _
  rw [hT0, hP0]
  -- q: the query
  obtain ⟨t1, ht1, hpos1, hcut1, hrun1⟩ := κ.qcS z
  have c1 := qy_callHost κ.qc κ.qcK κ.bQ κ.qcE κ.qcX [] (query f g z) t1 hpos1 hcut1 hrun1
    (dzLay L0 Bl) (dzLay Z0 0) [] (dz_arg_bank κ L0 0 _ _ _ _ le_rfl κ.qcK [] rfl)
    (dz_zero_bank κ Z0 0 _ _ _ _ le_rfl rfl)
  rw [show κ.bQ ⟨0, κ.qcK⟩ = κ.tp 0 from rfl, dzLay_update] at c1
  set L1 := Function.update L0 0 (FinTM.bufferTape (query f g z)) with hL1
  have seg1 := qy_hosted (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .q (Sum.inl ()) (Sum.inr κ.qcX)
    ⟨.g, Sum.inl ()⟩ 1 1 (dzLay L0 Bl) (dzLay L1 Bl) (dzLay Z0 0) (dzLay Z0 0) [] [] t1 c1.1
    (by simp [dzSetRed])
    (qy_guard_of_cut (Sum.inr κ.qcX) (dzSetRed κ .q) (fun s hs => by simp [dzSetRed, hs]) c1.2)
    F (fun s => hFq .q s (by simp))
  -- g: the bits of `g n`
  obtain ⟨t2, ht2, hpos2, hcut2, hrun2⟩ := κ.gcS z
  have c2 := qy_callHost κ.gc κ.gcK κ.bG κ.gcE κ.gcX [] (Nat.bits G) t2 hpos2 hcut2 hrun2
    (dzLay L1 Bl) (dzLay Z0 0) [] (dz_arg_bank κ L1 1 _ _ _ _ (by omega) κ.gcK [] rfl)
    (dz_zero_bank κ Z0 1 _ _ _ _ (by omega) rfl)
  rw [show κ.bG ⟨0, κ.gcK⟩ = κ.tp 1 from rfl, dzLay_update] at c2
  set L2 := Function.update L1 1 (FinTM.bufferTape (Nat.bits G)) with hL2
  have seg2 := qy_hosted (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .g (Sum.inl ()) (Sum.inr κ.gcX)
    ⟨.p, Sum.inl ()⟩ 1 1 (dzLay L1 Bl) (dzLay L2 Bl) (dzLay Z0 0) (dzLay Z0 0) [] [] t2 c2.1
    (by simp [dzSetRed])
    (qy_guard_of_cut (Sum.inr κ.gcX) (dzSetRed κ .g) (fun s hs => by simp [dzSetRed, hs]) c2.2)
    F (fun s => hFq .g s (by simp))
  -- p: the word `1^{n + 1}`
  obtain ⟨t3, ht3, hpos3, hcut3, hrun3⟩ := κ.pcS z
  have c3 := qy_callHost κ.pc κ.pcK κ.bP κ.pcE κ.pcX [] ([true] ++ z) t3 hpos3 hcut3 hrun3
    (dzLay L2 Bl) (dzLay Z0 0) [] (dz_arg_bank κ L2 2 _ _ _ _ (by omega) κ.pcK [] rfl)
    (dz_zero_bank κ Z0 2 _ _ _ _ (by omega) rfl)
  rw [show κ.bP ⟨0, κ.pcK⟩ = κ.tp 2 from rfl, dzLay_update] at c3
  set L3 := Function.update L2 2 (FinTM.bufferTape ([true] ++ z)) with hL3
  have seg3 := qy_hosted (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .p (Sum.inl ()) (Sum.inr κ.pcX)
    ⟨.c1, SweepPhase.sweep⟩ 1 1 (dzLay L2 Bl) (dzLay L3 Bl) (dzLay Z0 0) (dzLay Z0 0) [] [] t3
    c3.1 (by simp [dzSetRed])
    (qy_guard_of_cut (Sum.inr κ.pcX) (dzSetRed κ .p) (fun s hs => by simp [dzSetRed, hs]) c3.2)
    F (fun s => hFq .p s (by simp))
  -- c1: the clock's counter
  have c4 := qy_copy (x := z) (κ.tp 1) (κ.tp 3) (κ.tp_ne (by decide)) (fun b => b) 1
    (dzLay L3 Bl) (dzLay Z0 0) [] (Nat.bits G) [] (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp])
    (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; rfl)
  rw [dzLay_update, List.nil_append, List.map_id'] at c4
  set L4 := Function.update L3 3 (FinTM.bufferTape (Nat.bits G)) with hL4
  have seg4 := qy_hosted (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .c1 .sweep .done
    ⟨.c2, SweepPhase.sweep⟩ 1 1 (dzLay L3 Bl) (dzLay L4 Bl) (dzLay Z0 0) (dzLay Z0 0) [] [] _
    c4.1 (by simp [dzSetRed])
    (qy_guard_of_cut SweepPhase.done (dzSetRed κ .c1) (fun s hs => by simp [dzSetRed, hs]) c4.2)
    F (fun s => hFq .c1 s (by simp))
  -- c2: the block's first counter
  have c5 := qy_copy (x := z) (κ.tp 1) (κ.tp 4) (κ.tp_ne (by decide)) (fun b => b) 1
    (dzLay L4 Bl) (dzLay Z0 0) [] (Nat.bits G) [] (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp])
    (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; rfl)
  rw [dzLay_update, List.nil_append, List.map_id'] at c5
  set L5 := Function.update L4 4 (FinTM.bufferTape (Nat.bits G)) with hL5
  have seg5 := qy_hosted (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .c2 .sweep .done
    ⟨.e1, CounterLoopState.dec .run⟩ 1 1 (dzLay L4 Bl) (dzLay L5 Bl) (dzLay Z0 0) (dzLay Z0 0)
    [] [] _ c5.1 (by simp [dzSetRed])
    (qy_guard_of_cut SweepPhase.done (dzSetRed κ .c2) (fun s hs => by simp [dzSetRed, hs]) c5.2)
    F (fun s => hFq .c2 s (by simp))
  -- e1: the stream cells `1^{g n}` on the block tape
  have c6 := qy_expandHost (x := z) (qyEmb2 (κ.tp 6) (κ.tp 4) (κ.tp_ne (by decide))) (κ.tp 6)
    (κ.tp 4) rfl rfl 1 (dzLay L5 Bl) (dzLay Z0 0) [] [] (Nat.bits G) G (qy_bits_val G)
    (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp])
  rw [dzLay_update, dzLay_update, dzLay_update, List.nil_append] at c6
  set L6 := Function.update (Function.update L5 6 (FinTM.bufferTape (List.replicate G true))) 4
    (FinTM.bufferTape (List.replicate (Nat.bits G).length true)) with hL6
  set Z6 := Function.update Z0 6 ((([] : List Bool).length : ℤ) + G) with hZ6
  have seg6 := qy_hosted (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .e1 (.dec .run) .done
    ⟨.w, WritePhase.wr 0⟩ 1 1 (dzLay L5 Bl) (dzLay L6 Bl) (dzLay Z0 0) (dzLay Z6 0) [] [] _
    c6.1 (by simp [dzSetRed])
    (qy_guard_of_cut CounterLoopState.done (dzSetRed κ .e1) (fun s hs => by simp [dzSetRed, hs])
      c6.2) F (fun s => hFq .e1 s (by simp))
  -- w: the separator's counter `[true]`
  have c7 := qy_writeConst (x := z) (κ.tp 5) [true] 1 (dzLay L6 Bl) (dzLay Z6 0) [] []
    (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; rfl)
  rw [dzLay_update, List.nil_append] at c7
  set L7 := Function.update L6 5 (FinTM.bufferTape [true]) with hL7
  have seg7 := qy_hosted (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .w (.wr 0) .done
    ⟨.e2, CounterLoopState.dec .run⟩ 1 1 (dzLay L6 Bl) (dzLay L7 Bl) (dzLay Z6 0) (dzLay Z6 0)
    [] [] _ c7.1 (by simp [dzSetRed])
    (qy_guard_of_cut WritePhase.done (dzSetRed κ .w) (fun s hs => by simp [dzSetRed, hs]) c7.2)
    F (fun s => hFq .w s (by simp))
  -- e2: the separator
  have hv1 : Nat.ofDigits 2 (([true] : List Bool).map Bool.toNat) = 1 := by
    rw [List.map_cons, List.map_nil, Bool.toNat_true, Nat.ofDigits_singleton]
  have c8 := qy_expandHost (x := z) (qyEmb2 (κ.tp 6) (κ.tp 5) (κ.tp_ne (by decide))) (κ.tp 6)
    (κ.tp 5) rfl rfl 1 (dzLay L7 Bl) (dzLay Z6 0) [] (List.replicate G true) [true] 1 hv1
    (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; simp [hZ6]) (by rw [dzLay_tp]; rfl)
    (by rw [dzLay_tp]; rfl)
  rw [dzLay_update, dzLay_update, dzLay_update] at c8
  set L8 := Function.update (Function.update L7 6
    (FinTM.bufferTape (List.replicate G true ++ List.replicate 1 true))) 5
    (FinTM.bufferTape (List.replicate ([true] : List Bool).length true)) with hL8
  set Z8 := Function.update Z6 6 (((List.replicate G true).length : ℤ) + 1) with hZ8
  have seg8 := qy_hosted (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .e2 (.dec .run) .done
    ⟨.cb, SweepPhase.sweep⟩ 1 1 (dzLay L7 Bl) (dzLay L8 Bl) (dzLay Z6 0) (dzLay Z8 0) [] [] _
    c8.1 (by simp [dzSetRed])
    (qy_guard_of_cut CounterLoopState.done (dzSetRed κ .e2) (fun s hs => by simp [dzSetRed, hs])
      c8.2) F (fun s => hFq .e2 s (by simp))
  -- cb: the budget word, appended to the block
  have c9 := qy_copy (x := z) (κ.tp 1) (κ.tp 6) (κ.tp_ne (by decide)) (fun b => b) 1
    (dzLay L8 Bl) (dzLay Z8 0) [] (Nat.bits G) (List.replicate G true ++ List.replicate 1 true)
    (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; rfl)
    (by rw [dzLay_tp]; simp [hZ8])
  rw [dzLay_update, List.map_id'] at c9
  set L9 := Function.update L8 6
    (FinTM.bufferTape (List.replicate G true ++ List.replicate 1 true ++ Nat.bits G)) with hL9
  have seg9 := qy_hosted (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .cb .sweep .done
    ⟨.rb, RewindPhase.start⟩ 1 1 (dzLay L8 Bl) (dzLay L9 Bl) (dzLay Z8 0) (dzLay Z8 0) [] [] _
    c9.1 (by simp [dzSetRed])
    (qy_guard_of_cut SweepPhase.done (dzSetRed κ .cb) (fun s hs => by simp [dzSetRed, hs]) c9.2)
    F (fun s => hFq .cb s (by simp))
  -- rb: the block's rewind
  have c10 := qy_rewind (x := z) (κ.tp 6) 1 (dzLay L9 Bl) (dzLay Z8 0) []
    (List.replicate G true ++ List.replicate 1 true ++ Nat.bits G) (G + 1) (by simp)
    (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; simp [hZ8])
  rw [dzLay_update] at c10
  set Z10 := Function.update Z8 6 0 with hZ10
  have seg10 := qy_hosted (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .rb .start .done
    ⟨.e3, CounterLoopState.dec .run⟩ 1 1 (dzLay L9 Bl) (dzLay L9 Bl) (dzLay Z8 0) (dzLay Z10 0)
    [] [] _ c10.1 (by simp [dzSetRed])
    (qy_guard_of_cut RewindPhase.done (dzSetRed κ .rb) (fun s hs => by simp [dzSetRed, hs])
      c10.2) F (fun s => hFq .rb s (by simp))
  -- e3: the ruler `1^{g n}`, consuming `bits (g n)`
  have c11 := qy_expandHost (x := z) (qyEmb2 (κ.tp 7) (κ.tp 1) (κ.tp_ne (by decide))) (κ.tp 7)
    (κ.tp 1) rfl rfl 1 (dzLay L9 Bl) (dzLay Z10 0) [] [] (Nat.bits G) G (qy_bits_val G)
    (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; rfl)
    (by rw [dzLay_tp]; simp [hZ10, hZ8, hZ6, hZ0])
  rw [dzLay_update, dzLay_update, dzLay_update, List.nil_append] at c11
  set L11 := Function.update (Function.update L9 7 (FinTM.bufferTape (List.replicate G true))) 1
    (FinTM.bufferTape (List.replicate (Nat.bits G).length true)) with hL11
  set Z11 := Function.update Z10 7 ((([] : List Bool).length : ℤ) + G) with hZ11
  have seg11 := qy_hosted (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .e3 (.dec .run) .done
    ⟨.rr, RewindPhase.start⟩ 1 1 (dzLay L9 Bl) (dzLay L11 Bl) (dzLay Z10 0) (dzLay Z11 0) [] [] _
    c11.1 (by simp [dzSetRed])
    (qy_guard_of_cut CounterLoopState.done (dzSetRed κ .e3) (fun s hs => by simp [dzSetRed, hs])
      c11.2) F (fun s => hFq .e3 s (by simp))
  -- rr: the ruler's rewind, the setup's exit
  have c12 := qy_rewind (x := z) (κ.tp 7) 1 (dzLay L11 Bl) (dzLay Z11 0) []
    (List.replicate G true) G (by simp) (by rw [dzLay_tp]; rfl) (by rw [dzLay_tp]; simp [hZ11])
  rw [dzLay_update] at c12
  have hZ : Function.update Z11 7 0 = Z0 := by
    funext i
    simp only [hZ11, hZ10, hZ8, hZ6, hZ0, Function.update_apply]
    split_ifs <;> rfl
  have hL : L11 = dzSetL f g z := by
    funext i
    fin_cases i <;> rfl
  rw [hZ] at c12
  have seg12 := qy_hosted_last (dzSetM κ) ⟨.q, Sum.inl ()⟩ (dzSetRed κ) .rr .start .done 1 1
    (dzLay L11 Bl) (dzLay L11 Bl) (dzLay Z11 0) (dzLay Z0 0) [] [] _ c12.1
    (qy_guard_of_cut RewindPhase.done (dzSetRed κ .rr) (fun s _ => rfl) c12.2) F
    (fun u hu s hs h => by
      rw [hF, Set.mem_singleton_iff, Option.some_inj, dzPexit, Sigma.mk.inj_iff] at h
      exact c12.2 u hu (hs.trans (congrArg some (eq_of_heq h.2))))
  rw [← hL]
  refine ⟨_, ?_, seg1.trans (seg2.trans (seg3.trans (seg4.trans (seg5.trans (seg6.trans
    (seg7.trans (seg8.trans (seg9.trans (seg10.trans (seg11.trans seg12))))))))))⟩
  have hco1 := counterOverhead_le (Nat.bits G)
  rw [qy_bits_val] at hco1
  have hco2 := counterOverhead_le [true]
  rw [hv1] at hco2
  have hbG := length_bits_le_self G
  have ht1' : t1 ≤ κ.qcA * (G + 1) := ht1
  have ht2' : t2 ≤ κ.gcA * (G + 1) := ht2
  have ht3' : t3 ≤ κ.pcA * (G + 1) := ht3
  unfold dzSetB
  simp only [List.length_cons, List.length_nil] at hco2 ⊢
  nlinarith

/-! ### The run `Q` -/

/-- A single tape, as a one-tape bank. -/
private def dzOne {K : ℕ} (t : Fin K) : Fin 1 ↪ Fin K :=
  ⟨fun _ => t, fun a b _ => Subsingleton.elim a b⟩

/-- The core's tapes avoid every named tape but the block. -/
private theorem DzKit.bR_ne {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (i : Fin κ.kR) (j : Fin 14) (hj : j ≠ 6) : κ.bR i ≠ κ.tp j := by
  intro h
  by_cases hi : i = κ.jR
  · rw [hi, κ.bR_j] at h
    exact hj (Fin.castLE_injective κ.le_K h).symm
  · have := κ.bR_off i hi
    rw [h, κ.tp_val] at this
    omega

/-- The decider's tapes avoid every named tape but tape `13`. -/
private theorem DzKit.bB_ne {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (i : Fin BF.k) (j : Fin 14) (hj : j ≠ 13) : κ.bB i ≠ κ.tp j := by
  intro h
  by_cases hi : (i : ℕ) = 0
  · have hk : 0 < BF.k := by have := i.isLt; omega
    rw [show i = ⟨0, hk⟩ from Fin.ext hi] at h
    exact hj (Fin.castLE_injective κ.le_K h).symm
  · have : 14 ≤ (κ.bB i : ℕ) := by
      unfold DzKit.bB
      exact dz_bank_off _ _ _ _ _ (by omega) i hi
    rw [h, κ.tp_val] at this
    omega

/-- The hosted core's tape map: buffer on tape `11`, the core's tapes along `bR`, capture on tape
`12`, counter on tape `3`. -/
private def DzKit.sR {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Fin (((1 + κ.kR) + 1) + 1) ↪ Fin κ.K :=
  dzClkEmb (κ.tp 11) (κ.tp 12) (κ.tp 3) κ.bR (κ.tp_ne (by decide)) (κ.tp_ne (by decide))
    (κ.tp_ne (by decide)) (fun ⟨i, h⟩ => κ.bR_ne i 11 (by decide) h)
    (fun ⟨i, h⟩ => κ.bR_ne i 12 (by decide) h) (fun ⟨i, h⟩ => κ.bR_ne i 3 (by decide) h)

/-- The hosted decider's tape map: buffer on tape `8`, the decider's tapes along `bB`, capture on
tape `12`, counter on tape `3`. -/
private def DzKit.sB {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Fin (((1 + BF.k) + 1) + 1) ↪ Fin κ.K :=
  dzClkEmb (κ.tp 8) (κ.tp 12) (κ.tp 3) κ.bB (κ.tp_ne (by decide)) (κ.tp_ne (by decide))
    (κ.tp_ne (by decide)) (fun ⟨i, h⟩ => κ.bB_ne i 8 (by decide) h)
    (fun ⟨i, h⟩ => κ.bB_ne i 12 (by decide) h) (fun ⟨i, h⟩ => κ.bB_ne i 3 (by decide) h)

/-- The run's phases: the flag; the middle's tail copy, split (skip back, walk, take the
separator, move the budget word, skip back), test (expansion, rewind, comparison), normalization,
`α`, the three emissions, the capture's rewind and the hosted core; the top's tail copy, the hosted
decider, the capture's rewind and its read; the two verdicts. -/
private inductive DzQK
  | flag | mt | sb0 | walk | sep | xfer | sb1 | exp | rwU | cmp | lb | al | e1 | e2 | e3 | rwZ
  | runR | tt | runB | rwK | rd | acc | rej

/-- The run's phases have decidable equality (classically). -/
private noncomputable instance dzQKDecEq : DecidableEq DzQK := Classical.decEq _

/-- The run's phases are finite. -/
private noncomputable instance dzQKFintype : Fintype DzQK :=
  Fintype.ofList [.flag, .mt, .sb0, .walk, .sep, .xfer, .sb1, .exp, .rwU, .cmp, .lb, .al, .e1, .e2,
    .e3, .rwZ, .runR, .tt, .runB, .rwK, .rd, .acc, .rej] (by intro x; cases x <;> simp)

/-- The run's phase carriers. -/
private abbrev DzQPh {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : DzQK → Type
  | .flag | .sep | .rd => Option (Option Bool)
  | .mt | .xfer | .tt | .acc | .rej => SweepPhase
  | .sb0 | .walk | .sb1 => SeekPhase
  | .exp => CounterLoopState (Fin ([true].length + 1))
  | .rwU | .rwZ | .rwK => RewindPhase
  | .cmp => QyCmp
  | .lb => Unit ⊕ κ.lc.State
  | .al => Unit ⊕ κ.ac.State
  | .e1 => QyEm ([] : List Bool).length ([false, false, true, true] : List Bool).length 3
  | .e2 => QyEm ([] : List Bool).length ([false, true] : List Bool).length 1
  | .e3 => QyEm ([] : List Bool).length ([] : List Bool).length 0
  | .runR => κ.QR
  | .runB => κ.QB

/-- The run's phase carriers are finite. -/
private instance dzQPhFintype {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (i : DzQK) : Fintype (DzQPh κ i) := by
  cases i <;> dsimp only [DzQPh] <;> infer_instance

/-- The run's phase carriers have decidable equality. -/
private instance dzQPhDecEq {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (i : DzQK) : DecidableEq (DzQPh κ i) := by
  cases i <;> dsimp only [DzQPh] <;> infer_instance

/-- The run's phase machines. -/
private def dzQM {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : (i : DzQK) → MultiTapeTM κ.K Bool (DzQPh κ i)
  | .flag => dzTakeTM κ.K (κ.tp 0)
  | .mt => copyMapTM κ.K (κ.tp 0) (κ.tp 8) (fun b => b) (fun _ b => b)
  | .sb0 => skipBackTM κ.K (κ.tp 6)
  | .walk => walkTM κ.K (κ.tp 7) (fun i => i = κ.tp 7 ∨ i = κ.tp 6) .pos
  | .sep => dzTakeTM κ.K (κ.tp 6)
  | .xfer => transferMapTM κ.K (κ.tp 6) (κ.tp 9) (fun b => b) (fun _ b => b) (fun _ => none)
  | .sb1 => skipBackTM κ.K (κ.tp 6)
  | .exp => embedEmitTM (qyEmb2 (κ.tp 10) (κ.tp 9) (κ.tp_ne (by decide))) (expandTM 1 0 [true])
  | .rwU => rewindTM κ.K (κ.tp 10)
  | .cmp => qyCmpTM κ.K (κ.tp 10) (κ.tp 6)
  | .lb => embedEmitTM κ.bL (seamReleaseTM κ.lc.tm κ.lcE)
  | .al => embedEmitTM κ.bA (seamReleaseTM κ.ac.tm κ.acE)
  | .e1 =>
    embedSilentTM (dzOne (κ.tp 10)) (κ.tp 11) (qyEmitTM 1 0 [] [false, false, true, true] 3 false)
  | .e2 => embedSilentTM (dzOne (κ.tp 8)) (κ.tp 11) (qyEmitTM 1 0 [] [false, true] 1 false)
  | .e3 => embedSilentTM (dzOne (κ.tp 2)) (κ.tp 11) (qyEmitTM 1 0 [] [] 0 false)
  | .rwZ => rewindTM κ.K (κ.tp 11)
  | .runR => embedEmitTM κ.sR κ.HR
  | .tt => copyMapTM κ.K (κ.tp 0) (κ.tp 8) (fun b => b) (fun _ b => b)
  | .runB => embedEmitTM κ.sB κ.HB
  | .rwK => rewindTM κ.K (κ.tp 12)
  | .rd => dzTakeTM κ.K (κ.tp 12)
  | .acc => clearTM κ.K (κ.tp 13)
  | .rej => clearTM κ.K (κ.tp 13)

/-- The run's accepting verdict. -/
private def dzAcc {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Σ i, DzQPh κ i := ⟨.acc, SweepPhase.sweep⟩

/-- The run's rejecting verdict. -/
private def dzRej {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Σ i, DzQPh κ i := ⟨.rej, SweepPhase.sweep⟩

/-- The run's dispatch table: the flag selects the branch (`none` rejects); in the middle each
exit enters the next phase, the comparison rejects a budget above `g n`, and the hosted core's
`finish` at `accept` accepts, every other `finish` or `timeout` rejects; at the top the hosted
decider's `finish` goes to the capture's rewind, its `timeout` rejects, and the captured
`false` accepts, anything else rejects. -/
private def dzQRed {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : (i : DzQK) → DzQPh κ i → Option (Σ j, DzQPh κ j)
  | .flag, s =>
    match s with
    | none => none
    | some none => some (dzRej κ)
    | some (some true) => some ⟨.tt, SweepPhase.sweep⟩
    | some (some false) => some ⟨.mt, SweepPhase.sweep⟩
  | .mt, s => if s = .done then some ⟨.sb0, SeekPhase.run⟩ else none
  | .sb0, s => if s = .done then some ⟨.walk, SeekPhase.run⟩ else none
  | .walk, s => if s = .done then some ⟨.sep, none⟩ else none
  | .sep, s => if s = none then none else some ⟨.xfer, SweepPhase.sweep⟩
  | .xfer, s => if s = .done then some ⟨.sb1, SeekPhase.run⟩ else none
  | .sb1, s => if s = .done then some ⟨.exp, CounterLoopState.dec .run⟩ else none
  | .exp, s => if s = .done then some ⟨.rwU, RewindPhase.start⟩ else none
  | .rwU, s => if s = .done then some ⟨.cmp, QyCmp.scan⟩ else none
  | .cmp, s =>
    match s with
    | .done v => if v = .gt then some (dzRej κ) else some ⟨.lb, Sum.inl ()⟩
    | _ => none
  | .lb, s => if s = Sum.inr κ.lcX then some ⟨.al, Sum.inl ()⟩ else none
  | .al, s => if s = Sum.inr κ.acX then some ⟨.e1, QyEm.pre 0⟩ else none
  | .e1, s => if s = .done then some ⟨.e2, QyEm.pre 0⟩ else none
  | .e2, s => if s = .done then some ⟨.e3, QyEm.pre 0⟩ else none
  | .e3, s => if s = .done then some ⟨.rwZ, RewindPhase.start⟩ else none
  | .rwZ, s => if s = .done then some ⟨.runR, κ.iR (κ.rE, true)⟩ else none
  | .runR, s =>
    if ∃ b, s = κ.fR (some (κ.rA, b)) then some (dzAcc κ)
    else if ∃ r, s = κ.fR r then some (dzRej κ)
    else if ∃ r, s = κ.oR r then some (dzRej κ) else none
  | .tt, s => if s = .done then some ⟨.runB, κ.iB (BF.tm.q₀, true)⟩ else none
  | .runB, s =>
    if ∃ r, s = κ.fB r then some ⟨.rwK, RewindPhase.start⟩
    else if ∃ r, s = κ.oB r then some (dzRej κ) else none
  | .rwK, s => if s = .done then some ⟨.rd, none⟩ else none
  | .rd, s =>
    match s with
    | none => none
    | some (some false) => some (dzAcc κ)
    | some _ => some (dzRej κ)
  | .acc, _ => none
  | .rej, _ => none

/-- **The run** `Q`: the phase host over the run's phases, entered at the flag. -/
private def dzQ {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : MultiTapeTM κ.K Bool (Σ i, DzQPh κ i) :=
  phaseHostTM (dzQM κ) ⟨.flag, none⟩ (dzQRed κ)

/-- The run's verdicts, as the avoided set of its segments. -/
private def dzQF {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : Set (Option (Σ i, DzQPh κ i)) :=
  {some (dzAcc κ), some (dzRej κ)}

/-- Only the verdict phases' states are verdicts. -/
private theorem dz_notF {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (i : DzQK) (s : DzQPh κ i) (h1 : i ≠ .acc) (h2 : i ≠ .rej) :
    some ⟨i, s⟩ ∉ dzQF κ := by
  intro h
  rcases h with h | h
  · exact h1 (congrArg Sigma.fst (Option.some_inj.mp h))
  · exact h2 (congrArg Sigma.fst (Option.some_inj.mp h))

/-- The accepting and rejecting verdicts differ. -/
private theorem dz_acc_ne_rej {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) : dzAcc κ ≠ dzRej κ := by
  intro h
  have := congrArg Sigma.fst h
  exact absurd this (by simp [dzAcc, dzRej])

/-- **The handoff.** After the setup and the guess of a word `s` as wide as the block, the run's
entry configuration is the setup's layout with the block tape holding `s`, in normal form.

**Proof sketch.** Field by field through `Turing.guessRunCfg`'s equations: the block tape's head
is at `0`, so its cells `[0, |s|)` are overwritten by `s`, and the block is blank outside them,
as is the buffer of `s` (`FinTM.bufferTape_eq_none_of_not_mem`); the update is a layout update
(`dzLay_update`). -/
private theorem dz_handoff {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) (z s : List Bool) (hs : s.length = (dzBlk (g z.length)).length) :
    guessRunCfg (qyC (x := z) (dzPexit κ) 1 (dzLay (dzSetL f g z)
        (FinTM.bufferTape [])) (fun _ => 0) []) (κ.tp 6) s (⟨.flag, none⟩ : Σ i, DzQPh κ i) =
      qyC ⟨.flag, none⟩ 1 (dzLay (Function.update (dzSetL f g z) 6
        (FinTM.bufferTape s)) (FinTM.bufferTape [])) (fun _ => 0) [] := by
  apply Cfg.ext
  · rw [guessRunCfg_state]
    rfl
  · rw [guessRunCfg_inputPos]
    rfl
  · funext j a
    rw [guessRunCfg_workTapes]
    show Function.update (dzLay (dzSetL f g z) (FinTM.bufferTape [])) (κ.tp 6) (fun p =>
        if (0 : ℤ) ≤ p ∧ p < 0 + (s.length : ℤ) then FinTM.bufferTape s (p - 0)
        else dzLay (dzSetL f g z) (FinTM.bufferTape []) (κ.tp 6) p) j a =
      dzLay (Function.update (dzSetL f g z) 6 (FinTM.bufferTape s))
        (FinTM.bufferTape []) j a
    rw [← dzLay_update κ]
    by_cases hj : j = κ.tp 6
    · subst hj
      rw [Function.update_self, Function.update_self, dzLay_tp]
      by_cases ha : (0 : ℤ) ≤ a ∧ a < 0 + (s.length : ℤ)
      · rw [if_pos ha, sub_zero]
      · rw [if_neg ha]
        have h6 : dzSetL f g z 6 = FinTM.bufferTape (dzBlk (g z.length)) := by
          simp [dzSetL]
        rw [h6, FinTM.bufferTape_eq_none_of_not_mem _ (by omega),
          FinTM.bufferTape_eq_none_of_not_mem _ (by omega)]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  · funext j
    rw [guessRunCfg_workTapePos]
    rfl
  · rw [guessRunCfg_output]
    rfl

/-- **The flag.** From the run's entry over a layout whose tape `0` holds the query `q` with its
head at `0`, the run takes the query's first cell (`dzTakeTM`), blanking it and moving that head
to `1`, and dispatches on it in one more step, to the target `q'` of that cell's redirect.

**Proof sketch.** `dz_take_run` gives the take's step; it is the flag phase's exit, redirected to
`q'` (`qy_hosted`, the guard holding at the reading state). The updates are layout updates. -/
private theorem dz_flag {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) {z : List Bool} (L : Fin 14 → ℤ → Option Bool) (Pn : Fin 14 → ℤ)
    (q : List Bool) (hL : L 0 = FinTM.bufferTape q) (hP : Pn 0 = 0) (q' : Σ i, DzQPh κ i)
    (hq' : dzQRed κ .flag (some (FinTM.bufferTape q 0)) = some q') :
    Segment (dzQ κ) (dzQF κ) (fun _ => True)
      (qyC (x := z) ⟨.flag, none⟩ 1 (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) [])
      (qyC q' 1 (dzLay (Function.update L 0 (Function.update (FinTM.bufferTape q) 0 none))
        (FinTM.bufferTape [])) (dzLay (Function.update Pn 0 1) 0) []) 2 := by
  have h := dz_take_run (x := z) (κ.tp 0) 1 (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) []
  rw [dzLay_tp, dzLay_tp, hL, hP, zero_add, dzLay_update, dzLay_update] at h
  exact qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .flag none (some (FinTM.bufferTape q 0)) q' 1
    1 _ _ _ _ [] [] 1 h hq' (fun u hu s hs => by
      obtain rfl : u = 0 := by omega
      rw [MultiTapeTM.runFrom_zero] at hs
      cases Option.some.inj hs
      rfl) _ (fun s => dz_notF κ .flag s (by simp) (by simp))

/-- **The tail's copy.** With the query `b :: tail` on tape `src`, its first cell blanked and its
head at `1`, `Turing.copyMapTM` copies `tail` onto the blank tape `dst` from cell `0`; nothing else
changes. The framed row applies directly: the blanked flag is the tail's left delimiter.

**Proof sketch.** `Turing.copyMapTM_run_ofCfg` with the word `tail`: its delimiter hypothesis holds
at relative position `-1` (the blanked cell) and on the tail's cells
(`FinTM.bufferTape_append_shift` over `[b]`). Its endpoint patches `dst` from cell `0` with `tail`,
which is the buffer of `tail`, the destination being blank. -/
private theorem dz_tail_run {K : ℕ} {x : List Bool} (src dst : Fin K) (hne : src ≠ dst)
    (ip : Fin (x.length + 2)) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o : List Bool)
    (b : Bool) (tail : List Bool)
    (hT : T src = Function.update (FinTM.bufferTape (b :: tail)) 0 none)
    (hP : P src = 1) (hd : T dst = FinTM.bufferTape []) (hPd : P dst = 0) :
    (copyMapTM K src dst (fun b => b) (fun _ b => b)).runFrom (qyC .sweep ip T P o)
        (2 * tail.length + 2) =
      qyC SweepPhase.done ip (Function.update T dst (FinTM.bufferTape tail)) P o ∧
    ∀ t < 2 * tail.length + 2,
      ((copyMapTM K src dst (fun b => b) (fun _ b => b)).runFrom (qyC .sweep ip T P o) t).state ≠
        some .done := by
  obtain ⟨hrun, hcut, -⟩ := copyMapTM_run_ofCfg src dst hne (fun b => b) (fun _ b => b) tail
    (qyC .sweep ip T P o) rfl (fun p hp1 hp2 => by
      show T src (P src + p) = _
      rw [hT, hP]
      by_cases hp : p = -1
      · subst hp
        rw [show (1 : ℤ) + -1 = 0 by norm_num, Function.update_self,
          FinTM.bufferTape_of_neg _ (by norm_num)]
      · rw [Function.update_of_ne (by omega)]
        have := FinTM.bufferTape_append_shift [b] tail (z := p) (by omega)
        rw [List.length_singleton, Nat.cast_one] at this
        exact this)
  refine ⟨hrun.trans ?_, hcut⟩
  dsimp only [qyC]
  congr 1
  funext j a
  by_cases hj : j = dst
  · subst hj
    rw [Function.update_self, hPd]
    by_cases ha : (0 : ℤ) ≤ a ∧ a < 0 + (tail.length : ℤ)
    · rw [if_pos ⟨rfl, ha⟩, sub_zero]
      cases FinTM.bufferTape tail a <;> rfl
    · rw [if_neg (fun h => ha h.2), hd, FinTM.bufferTape_nil,
        FinTM.bufferTape_eq_none_of_not_mem _ (by omega)]
  · rw [if_neg (fun h => hj h.1), Function.update_of_ne hj]

/-! ### The middle's split, test and normalization -/

/-- **The block after the split.** The buffer of `s₁ ++ [b] ++ w` with its cell `|s₁|` blanked and
the cells of `w` blanked is the buffer of `s₁`. -/
private theorem dz_split_tape (s₁ w : List Bool) (b : Bool) :
    (fun q => if (s₁.length : ℤ) + 1 ≤ q ∧ q < (s₁.length : ℤ) + 1 + (w.length : ℤ) then
        (FinTM.bufferTape w (q - ((s₁.length : ℤ) + 1))).bind fun _ => none
      else Function.update (FinTM.bufferTape (s₁ ++ [b] ++ w)) (s₁.length : ℤ) none q) =
      FinTM.bufferTape s₁ := by
  funext q
  by_cases h1 : (s₁.length : ℤ) + 1 ≤ q ∧ q < (s₁.length : ℤ) + 1 + (w.length : ℤ)
  · rw [if_pos h1, FinTM.bufferTape_eq_none_of_not_mem s₁ (z := q) (by omega)]
    cases FinTM.bufferTape w (q - ((s₁.length : ℤ) + 1)) <;> rfl
  · rw [if_neg h1]
    by_cases h2 : q = (s₁.length : ℤ)
    · rw [h2, Function.update_self, FinTM.bufferTape_eq_none_of_not_mem _ (by omega)]
    · rw [Function.update_of_ne h2]
      by_cases h3 : 0 ≤ q ∧ q < (s₁.length : ℤ)
      · rw [FinTM.bufferTape_eq, FinTM.bufferTape_eq, if_pos h3.1, if_pos h3.1, List.append_assoc,
          List.getElem?_append_left (by omega)]
      · rw [FinTM.bufferTape_eq_none_of_not_mem _ h3, FinTM.bufferTape_eq_none_of_not_mem _ (by
          simp only [List.length_append, List.length_singleton]
          push_cast
          omega)]

/-- **The split.** From the middle's first split phase over a layout whose block tape holds the
stream `s₁` (of length `G`), a separator bit and the budget word `w`, whose ruler tape holds
`1^G` and whose budget tape is blank, every one of these heads at `0`, the run skips back over
the empty word, walks the block's head over the ruler onto the separator, takes the separator,
moves `w` onto the budget tape and skips back over `s₁`: the block tape holds exactly `s₁` and
the budget tape `w`, both heads at `0`, the ruler's head at `G + 1`.

**Proof sketch.** Five hosted phases (`qy_hosted`), chained by `Turing.Segment.trans`:
`Turing.skipBackTM_run_ofCfg` over the empty word (cells `-2`, `-1` are blank), the lockstep walk
`Turing.walkTM_run_ofCfg` with the ruler as its source (`G + 1` steps), the take `dz_take_run` (its
cell `G` is the separator, now blank: the budget word's left delimiter), the move
`Turing.transferMapTM_run_ofCfg` (its delimiters are the blanked separator and the block's right
blank; `FinTM.bufferTape_append_shift`), whose block tape is the buffer of `s₁`
(`dz_split_tape`), and `Turing.skipBackTM_run_ofCfg` over `s₁`. Each guard is its row's cut. -/
private theorem dz_split {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) {z : List Bool} (L : Fin 14 → ℤ → Option Bool) (Pn : Fin 14 → ℤ)
    (s₁ w : List Bool) (sp : Bool) (h6 : L 6 = FinTM.bufferTape (s₁ ++ [sp] ++ w))
    (h7 : L 7 = FinTM.bufferTape (List.replicate s₁.length true))
    (h9 : L 9 = FinTM.bufferTape []) (hP6 : Pn 6 = 0) (hP7 : Pn 7 = 0) (hP9 : Pn 9 = 0) :
    ∃ t ≤ 2 * s₁.length + 2 * w.length + 15, Segment (dzQ κ) (dzQF κ) (fun _ => True)
      (qyC (x := z) ⟨.sb0, SeekPhase.run⟩ 1 (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) [])
      (qyC ⟨.exp, CounterLoopState.dec .run⟩ 1
        (dzLay (Function.update (Function.update L 6 (FinTM.bufferTape s₁)) 9 (FinTM.bufferTape w))
          (FinTM.bufferTape []))
        (dzLay (Function.update Pn 7 ((s₁.length : ℤ) + 1)) 0) []) t := by
  set Bl : ℤ → Option Bool := FinTM.bufferTape [] with hBl
  set G := s₁.length with hG
  -- sb0: skip back over the empty word
  obtain ⟨r1, k1, -⟩ := skipBackTM_run_ofCfg (κ.tp 6) ([] : List Bool)
    (qyC (x := z) SeekPhase.run 1 (dzLay L Bl) (dzLay Pn 0) []) rfl (fun p hp1 hp2 => by
      show dzLay L Bl (κ.tp 6) (dzLay Pn 0 (κ.tp 6) - (([] : List Bool).length : ℤ) - 1 + p) = _
      rw [dzLay_tp, dzLay_tp, h6, hP6, FinTM.bufferTape_of_neg _ (by simp at hp2 ⊢; omega),
        FinTM.bufferTape_eq_none_of_not_mem _ (by simp)])
  obtain ⟨P1, hP1⟩ : ∃ P1 : Fin 14 → ℤ, P1 = Function.update Pn 6 (-1) := ⟨_, rfl⟩
  have e1 : (skipBackTM κ.K (κ.tp 6)).runFrom
      (qyC (x := z) SeekPhase.run 1 (dzLay L Bl) (dzLay Pn 0) []) (([] : List Bool).length + 3) =
      qyC SeekPhase.done 1 (dzLay L Bl) (dzLay P1 0) [] := by
    rw [r1, hP1, ← dzLay_update κ]
    dsimp only [qyC]
    rw [dzLay_tp, hP6]
    rfl
  have seg1 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .sb0 .run .done ⟨.walk, SeekPhase.run⟩
    1 1 _ _ _ _ [] [] _ e1 (by simp [dzQRed])
    (qy_guard_of_cut SeekPhase.done (dzQRed κ .sb0) (fun s hs => by simp [dzQRed, hs]) k1)
    (dzQF κ) (fun s => dz_notF κ .sb0 s (by simp) (by simp))
  -- walk: the block's head onto the separator, in lockstep with the ruler
  obtain ⟨r2, k2, -⟩ := walkTM_run_ofCfg (κ.tp 7) (fun i => i = κ.tp 7 ∨ i = κ.tp 6) (Or.inl rfl)
    .pos (List.replicate G true) (qyC (x := z) SeekPhase.run 1 (dzLay L Bl) (dzLay P1 0) []) rfl
    (fun p hp => by
      show dzLay L Bl (κ.tp 7) (dzLay P1 0 (κ.tp 7) + ((SignType.pos : SignType) : ℤ) * p) = _
      rw [dzLay_tp, dzLay_tp, h7, hP1, Function.update_of_ne (by decide), hP7,
        show ((SignType.pos : SignType) : ℤ) = 1 from rfl, one_mul, zero_add])
  have e2 : (walkTM κ.K (κ.tp 7) (fun i => i = κ.tp 7 ∨ i = κ.tp 6) .pos).runFrom
      (qyC (x := z) SeekPhase.run 1 (dzLay L Bl) (dzLay P1 0) [])
      ((List.replicate G true).length + 1)
      = qyC SeekPhase.done 1 (dzLay L Bl) (Function.update (Function.update (dzLay P1 0) (κ.tp 7)
        ((G : ℤ) + 1)) (κ.tp 6) (G : ℤ)) [] := by
    rw [r2]
    dsimp only [qyC]
    congr 1
    funext j
    rw [List.length_replicate, show ((SignType.pos : SignType) : ℤ) = 1 from rfl, one_mul]
    by_cases j6 : j = κ.tp 6
    · subst j6
      rw [if_pos (Or.inr rfl), Function.update_self, dzLay_tp, hP1, Function.update_self]
      push_cast
      ring
    · rw [Function.update_of_ne j6]
      by_cases j7 : j = κ.tp 7
      · subst j7
        rw [if_pos (Or.inl rfl), Function.update_self, dzLay_tp, hP1,
          Function.update_of_ne (by decide), hP7]
        push_cast
        ring
      · rw [if_neg (by tauto), add_zero, Function.update_of_ne j7]
  rw [dzLay_update, dzLay_update] at e2
  have seg2 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .walk .run .done ⟨.sep, none⟩
    1 1 _ _ _ _ [] [] _ e2 (by simp [dzQRed])
    (qy_guard_of_cut SeekPhase.done (dzQRed κ .walk) (fun s hs => by simp [dzQRed, hs]) k2)
    (dzQF κ) (fun s => dz_notF κ .walk s (by simp) (by simp))
  obtain ⟨P2, hP2⟩ : ∃ P2 : Fin 14 → ℤ,
      P2 = Function.update (Function.update P1 7 ((G : ℤ) + 1)) 6 (G : ℤ) := ⟨_, rfl⟩
  rw [← hP2] at seg2
  -- sep: take the separator
  have e3 := dz_take_run (x := z) (κ.tp 6) 1 (dzLay L Bl) (dzLay P2 0) []
  have hsep : FinTM.bufferTape (s₁ ++ [sp] ++ w) (G : ℤ) = some sp := by
    rw [FinTM.bufferTape_eq, if_pos (by omega), show (G : ℤ).toNat = G by omega,
      List.append_assoc, List.getElem?_append_right (by omega), hG, Nat.sub_self]
    rfl
  have hP2_6 : P2 6 = (G : ℤ) := by rw [hP2, Function.update_self]
  rw [dzLay_tp, dzLay_tp, h6, hP2_6, hsep, dzLay_update, dzLay_update] at e3
  have seg3 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .sep none (some (some sp))
    ⟨.xfer, SweepPhase.sweep⟩ 1 1 _ _ _ _ [] [] 1 e3 (by simp [dzQRed])
    (fun u hu s hs => by
      obtain rfl : u = 0 := by omega
      rw [MultiTapeTM.runFrom_zero] at hs
      cases Option.some.inj hs
      simp [dzQRed]) (dzQF κ) (fun s => dz_notF κ .sep s (by simp) (by simp))
  obtain ⟨L3, hL3⟩ : ∃ L3 : Fin 14 → ℤ → Option Bool,
      L3 = Function.update L 6
        (Function.update (FinTM.bufferTape (s₁ ++ [sp] ++ w)) (G : ℤ) none) :=
    ⟨_, rfl⟩
  obtain ⟨P3, hP3⟩ : ∃ P3 : Fin 14 → ℤ, P3 = Function.update P2 6 ((G : ℤ) + 1) := ⟨_, rfl⟩
  rw [← hL3, ← hP3] at seg3
  -- xfer: move the budget word onto the budget tape
  have hP3_6 : P3 6 = (G : ℤ) + 1 := by rw [hP3, Function.update_self]
  have hP3_9 : P3 9 = 0 := by
    rw [hP3, hP2, hP1]
    simp [hP9]
  obtain ⟨r4, k4, -⟩ := transferMapTM_run_ofCfg (κ.tp 6) (κ.tp 9) (κ.tp_ne (by decide))
    (fun b => b) (fun _ b => b) (fun _ => none) w
    (qyC (x := z) SweepPhase.sweep 1 (dzLay L3 Bl) (dzLay P3 0) []) rfl (fun p hp1 hp2 => by
      show dzLay L3 Bl (κ.tp 6) (dzLay P3 0 (κ.tp 6) + p) = _
      rw [dzLay_tp, dzLay_tp, hL3, hP3_6, Function.update_self]
      by_cases hp : p = -1
      · subst hp
        rw [show (G : ℤ) + 1 + -1 = G by ring, Function.update_self,
          FinTM.bufferTape_of_neg _ (by norm_num)]
      · rw [Function.update_of_ne (by omega)]
        have := FinTM.bufferTape_append_shift (s₁ ++ [sp]) w (z := p) (by omega)
        rw [List.length_append, List.length_singleton] at this
        rw [← this]
        congr 1)
  have e4 : (transferMapTM κ.K (κ.tp 6) (κ.tp 9) (fun b => b) (fun _ b => b)
      (fun _ => none)).runFrom (qyC (x := z) SweepPhase.sweep 1 (dzLay L3 Bl) (dzLay P3 0) [])
      (2 * w.length + 2) = qyC SweepPhase.done 1 (Function.update (Function.update (dzLay L3 Bl)
        (κ.tp 6) (FinTM.bufferTape s₁)) (κ.tp 9) (FinTM.bufferTape w)) (dzLay P3 0) [] := by
    rw [r4]
    dsimp only [qyC]
    congr 1
    funext j q
    by_cases j9 : j = κ.tp 9
    · subst j9
      rw [if_neg (fun h => κ.tp_ne (by decide) h.1), Function.update_self, dzLay_tp, hP3_9]
      by_cases hq : (0 : ℤ) ≤ q ∧ q < 0 + (w.length : ℤ)
      · rw [if_pos ⟨rfl, hq⟩, sub_zero]
        cases FinTM.bufferTape w q <;> rfl
      · rw [if_neg (fun h => hq h.2), dzLay_tp, hL3, Function.update_of_ne (by decide), h9,
          hBl, FinTM.bufferTape_nil, FinTM.bufferTape_eq_none_of_not_mem _ (by omega)]
    · rw [Function.update_of_ne j9]
      by_cases j6 : j = κ.tp 6
      · subst j6
        rw [Function.update_self, dzLay_tp, hP3_6]
        have hs := congrFun (dz_split_tape s₁ w sp) q
        rw [← hG] at hs
        by_cases hq : (G : ℤ) + 1 ≤ q ∧ q < (G : ℤ) + 1 + (w.length : ℤ)
        · rw [if_pos ⟨rfl, hq⟩, ← hs, if_pos hq]
        · rw [if_neg (fun h => hq h.2), if_neg (fun h => κ.tp_ne (by decide) h.1), dzLay_tp, hL3,
            Function.update_self, ← hs, if_neg hq]
      · rw [if_neg (fun h => j6 h.1), if_neg (fun h => j9 h.1), Function.update_of_ne j6]
  rw [dzLay_update, dzLay_update] at e4
  have seg4 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .xfer .sweep .done ⟨.sb1, SeekPhase.run⟩
    1 1 _ _ _ _ [] [] _ e4 (by simp [dzQRed])
    (qy_guard_of_cut SweepPhase.done (dzQRed κ .xfer) (fun s hs => by simp [dzQRed, hs]) k4)
    (dzQF κ) (fun s => dz_notF κ .xfer s (by simp) (by simp))
  have hL4 : Function.update (Function.update L3 6 (FinTM.bufferTape s₁)) 9 (FinTM.bufferTape w) =
      Function.update (Function.update L 6 (FinTM.bufferTape s₁)) 9 (FinTM.bufferTape w) := by
    rw [hL3, Function.update_idem]
  rw [hL4] at seg4
  -- sb1: skip back over the stream
  obtain ⟨L4, hL4'⟩ : ∃ L4 : Fin 14 → ℤ → Option Bool,
      L4 = Function.update (Function.update L 6 (FinTM.bufferTape s₁)) 9 (FinTM.bufferTape w) :=
    ⟨_, rfl⟩
  rw [← hL4'] at seg4 ⊢
  obtain ⟨r5, k5, -⟩ := skipBackTM_run_ofCfg (κ.tp 6) s₁
    (qyC (x := z) SeekPhase.run 1 (dzLay L4 Bl) (dzLay P3 0) []) rfl (fun p hp1 hp2 => by
      show dzLay L4 Bl (κ.tp 6) (dzLay P3 0 (κ.tp 6) - (s₁.length : ℤ) - 1 + p) = _
      rw [dzLay_tp, dzLay_tp, hL4', Function.update_of_ne (by decide), Function.update_self,
        hP3_6, ← hG]
      congr 1
      ring)
  have hPend : Function.update P3 6 ((G : ℤ) + 1 - (s₁.length : ℤ) - 1) =
      Function.update Pn 7 ((G : ℤ) + 1) := by
    funext i
    rw [hP3, hP2, hP1]
    simp only [Function.update_apply]
    split_ifs with h1 h2 h3 <;> first | rfl | (subst_vars; simp_all)
  have e5 : (skipBackTM κ.K (κ.tp 6)).runFrom
      (qyC (x := z) SeekPhase.run 1 (dzLay L4 Bl) (dzLay P3 0) []) (s₁.length + 3) =
      qyC SeekPhase.done 1 (dzLay L4 Bl) (dzLay (Function.update Pn 7 ((G : ℤ) + 1)) 0) [] := by
    rw [r5, ← hPend, ← dzLay_update κ]
    dsimp only [qyC]
    rw [dzLay_tp, hP3_6]
  have seg5 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .sb1 .run .done
    ⟨.exp, CounterLoopState.dec .run⟩ 1 1 _ _ _ _ [] [] _ e5 (by simp [dzQRed])
    (qy_guard_of_cut SeekPhase.done (dzQRed κ .sb1) (fun s hs => by simp [dzQRed, hs]) k5)
    (dzQF κ) (fun s => dz_notF κ .sb1 s (by simp) (by simp))
  refine ⟨_, ?_, seg1.trans (seg2.trans (seg3.trans (seg4.trans seg5)))⟩
  simp only [List.length_nil, List.length_replicate]
  clear_value G
  subst hG
  omega

/-- **The budget's test.** From the expansion phase over a layout with the stream `s₁` on the block
tape and the budget word `w` (value `b`) on the budget tape, the expansion tape blank, these heads
at `0`, the run expands `w` to `1^b` (top zeros included), rewinds it and compares it with `s₁`: it
enters the normalization when `b ≤ |s₁|` and rejects otherwise.

**Proof sketch.** Three hosted phases: `qy_expandHost` (counter `w`, worth `b`), `qy_rewind`, and
`qy_cmp_run` on `1^b` and `s₁`, whose verdict `compare b |s₁|` is `gt` exactly when `|s₁| < b`. The
expansion's overhead is at most `4b + 2|w| + 2` (`Turing.counterOverhead_le`). -/
private theorem dz_test {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) {z : List Bool} (L : Fin 14 → ℤ → Option Bool) (Pn : Fin 14 → ℤ)
    (s₁ w : List Bool) (h6 : L 6 = FinTM.bufferTape s₁) (h9 : L 9 = FinTM.bufferTape w)
    (h10 : L 10 = FinTM.bufferTape []) (hP6 : Pn 6 = 0) (hP9 : Pn 9 = 0) (hP10 : Pn 10 = 0) :
    ∃ t ≤ 9 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 12,
      Segment (dzQ κ) (dzQF κ) (fun _ => True)
        (qyC (x := z) ⟨.exp, CounterLoopState.dec .run⟩ 1 (dzLay L (FinTM.bufferTape []))
          (dzLay Pn 0) [])
        (qyC (if Nat.ofDigits 2 (w.map Bool.toNat) ≤ s₁.length then ⟨.lb, Sum.inl ()⟩
            else dzRej κ) 1
          (dzLay (Function.update (Function.update L 10
            (FinTM.bufferTape (List.replicate (Nat.ofDigits 2 (w.map Bool.toNat)) true))) 9
            (FinTM.bufferTape (List.replicate w.length true))) (FinTM.bufferTape [])) (dzLay Pn 0)
          []) t := by
  set Bl : ℤ → Option Bool := FinTM.bufferTape [] with hBl
  set b := Nat.ofDigits 2 (w.map Bool.toNat) with hb
  -- exp: `1^b` on the expansion tape
  have c1 := qy_expandHost (x := z) (qyEmb2 (κ.tp 10) (κ.tp 9) (κ.tp_ne (by decide))) (κ.tp 10)
    (κ.tp 9) rfl rfl 1 (dzLay L Bl) (dzLay Pn 0) [] [] w b hb.symm (by rw [dzLay_tp, h10])
    (by rw [dzLay_tp, hP10]; rfl) (by rw [dzLay_tp, h9]) (by rw [dzLay_tp, hP9])
  rw [dzLay_update, dzLay_update, dzLay_update, List.nil_append] at c1
  obtain ⟨L1, hL1⟩ : ∃ L1 : Fin 14 → ℤ → Option Bool, L1 = Function.update (Function.update L 10
      (FinTM.bufferTape (List.replicate b true))) 9
      (FinTM.bufferTape (List.replicate w.length true)) := ⟨_, rfl⟩
  rw [← hL1] at c1 ⊢
  have seg1 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .exp (.dec .run) .done
    ⟨.rwU, RewindPhase.start⟩ 1 1 _ _ _ _ [] [] _ c1.1 (by simp [dzQRed])
    (qy_guard_of_cut CounterLoopState.done (dzQRed κ .exp) (fun s hs => by simp [dzQRed, hs]) c1.2)
    (dzQF κ) (fun s => dz_notF κ .exp s (by simp) (by simp))
  -- rwU: rewind it
  have hL1_10 : L1 10 = FinTM.bufferTape (List.replicate b true) := by
    rw [hL1, Function.update_of_ne (by decide), Function.update_self]
  have c2 := qy_rewind (x := z) (κ.tp 10) 1 (dzLay L1 Bl)
    (dzLay (Function.update Pn 10 ((([] : List Bool).length : ℤ) + b)) 0) []
    (List.replicate b true) b (by simp) (by rw [dzLay_tp, hL1_10])
    (by rw [dzLay_tp, Function.update_self]; simp)
  have hPn : Function.update Pn (10 : Fin 14) 0 = Pn := Function.update_eq_self_iff.mpr hP10.symm
  rw [dzLay_update, Function.update_idem, hPn] at c2
  have seg2 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .rwU .start .done ⟨.cmp, QyCmp.scan⟩
    1 1 _ _ _ _ [] [] _ c2.1 (by simp [dzQRed])
    (qy_guard_of_cut RewindPhase.done (dzQRed κ .rwU) (fun s hs => by simp [dzQRed, hs]) c2.2)
    (dzQF κ) (fun s => dz_notF κ .rwU s (by simp) (by simp))
  -- cmp: compare `1^b` with the stream
  have c3 := qy_cmp_run (x := z) (κ.tp 10) (κ.tp 6) (κ.tp_ne (by decide)) 1 (dzLay L1 Bl)
    (dzLay Pn 0) [] (List.replicate b true) s₁ (by rw [dzLay_tp, hL1_10])
    (by rw [dzLay_tp, hL1, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      h6])
    (by rw [dzLay_tp, hP10]) (by rw [dzLay_tp, hP6])
  rw [List.length_replicate] at c3
  have hred : dzQRed κ .cmp (QyCmp.done (compare b s₁.length)) =
      some (if b ≤ s₁.length then ⟨.lb, Sum.inl ()⟩ else dzRej κ) := by
    by_cases hbs : b ≤ s₁.length
    · rw [if_pos hbs]
      have : compare b s₁.length ≠ .gt := by
        rw [Ne, compare_gt_iff_gt]
        omega
      simp [dzQRed, this]
    · rw [if_neg hbs]
      have : compare b s₁.length = .gt := by
        rw [compare_gt_iff_gt]
        omega
      simp [dzQRed, this]
  have seg3 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .cmp .scan
    (QyCmp.done (compare b s₁.length)) _ 1 1 _ _ _ _ [] [] _ c3.1 hred
    (fun u hu s hs => by
      cases s with
      | done v => exact absurd hs (c3.2 u hu v)
      | _ => rfl)
    (dzQF κ) (fun s => dz_notF κ .cmp s (by simp) (by simp))
  refine ⟨_, ?_, seg1.trans (seg2.trans seg3)⟩
  have hco := counterOverhead_le w
  rw [← hb] at hco
  have hmin : min b s₁.length ≤ b := min_le_left _ _
  omega

/-- **The normalization.** The install call of `y ↦ bits |y|` on the expansion tape's `1^b` leaves
`bits b` there and enters the extractor's call, within `lcA (b + 1) + 1` steps.

**Proof sketch.** The bank over the layout holds the seam of `1^b` (`dz_arg_bank`); the released
call (`qy_callHost`) installs `bits |1^b| = bits b` on the expansion tape. -/
private theorem dz_norm {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) {z : List Bool} (L : Fin 14 → ℤ → Option Bool) (Pn : Fin 14 → ℤ)
    (b : ℕ) (h10 : L 10 = FinTM.bufferTape (List.replicate b true)) (hP10 : Pn 10 = 0) :
    ∃ t ≤ κ.lcA * (b + 1) + 1, Segment (dzQ κ) (dzQF κ) (fun _ => True)
      (qyC (x := z) ⟨.lb, Sum.inl ()⟩ 1 (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) [])
      (qyC ⟨.al, Sum.inl ()⟩ 1 (dzLay (Function.update L 10 (FinTM.bufferTape (Nat.bits b)))
        (FinTM.bufferTape [])) (dzLay Pn 0) []) t := by
  obtain ⟨t, ht, hpos, hcut, hrun⟩ := κ.lcS z (List.replicate b true)
  have c1 := qy_callHost κ.lc κ.lcK κ.bL κ.lcE κ.lcX (List.replicate b true) _ t hpos hcut hrun
    (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) []
    (dz_arg_bank κ L 10 _ _ _ _ (by omega) κ.lcK _ h10)
    (dz_zero_bank κ Pn 10 _ _ _ _ (by omega) hP10)
  rw [show κ.bL ⟨0, κ.lcK⟩ = κ.tp 10 from rfl, dzLay_update] at c1
  simp only [List.length_replicate] at c1
  have seg := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .lb (Sum.inl ()) (Sum.inr κ.lcX)
    ⟨.al, Sum.inl ()⟩ 1 1 _ _ _ _ [] [] t c1.1 (by simp [dzQRed])
    (qy_guard_of_cut (Sum.inr κ.lcX) (dzQRed κ .lb) (fun s hs => by simp [dzQRed, hs]) c1.2)
    (dzQF κ) (fun s => dz_notF κ .lb s (by simp) (by simp))
  refine ⟨_, ?_, seg⟩
  have ht' : t ≤ κ.lcA * ((List.replicate b true).length + 1) := ht
  rw [List.length_replicate] at ht'
  omega

/-! ### The middle's rewrite: `α` and the core's input -/

/-- **The core's input word** in three emissions without a flag: the budget's bits each written
four times and `[false, false, true, true]`; the code doubled and `[false, true]`; the tail. It is
`⟨⟨B, α⟩, N⟩`, read off `qy_writer_word` with the code `α ++ [true]` and its flag cancelled. -/
private theorem dz_core_word (B α N : List Bool) :
    (([] ++ ([] ++ [] ++ qyBody false 3 B ++ [false, false, true, true])) ++
        ([] ++ [] ++ qyBody false 1 α ++ [false, true])) ++ ([] ++ [] ++ qyBody false 0 N ++ []) =
      pairEncode (pairEncode B α) N := by
  have h := qy_writer_word false B (α ++ [true]) N
  rw [List.dropLast_concat] at h
  have hb : qyBody true 1 (α ++ [true]) = qyBody false 1 α := by
    unfold qyBody
    rw [if_pos rfl, if_neg Bool.false_ne_true, List.dropLast_concat]
  rw [hb] at h
  apply List.cons_injective (a := false)
  rw [← h]
  simp only [List.nil_append, List.append_nil, List.append_assoc, List.cons_append]

/-- **An emission under the capture wrapper.** `qyEmitTM` on one tape `src` holding `wd` (head at
`0`), with no prefix, the suffix `suf`, each symbol written `rr + 1` times, run under
`Turing.embedSilentTM` with the capture tape `cap` holding `pre` (head after it): the capture tape
gains the emission, the head of `src` moves to the word's end, nothing else changes, nothing is
emitted, and `done` is reached first within `|suf| + 3 + |wd| (rr + 3)` steps.

**Proof sketch.** `qy_emit_run` on the one-tape source gives its run and cut; `dz_silent`
transports it through the capture wrapper. -/
private theorem dz_emit_run {K : ℕ} {x : List Bool} (src cap : Fin K) (hne : src ≠ cap)
    (suf : List Bool) (rr : ℕ) (T : Fin K → ℤ → Option Bool) (P : Fin K → ℤ) (o pre wd : List Bool)
    (hT : T src = FinTM.bufferTape wd) (hP : P src = 0) (hTc : T cap = FinTM.bufferTape pre)
    (hPc : P cap = pre.length) :
    ∃ t ≤ suf.length + 3 + wd.length * (rr + 3),
      (embedSilentTM (dzOne src) cap (qyEmitTM 1 0 [] suf rr false)).runFrom
          (qyC (x := x) (.pre 0) 1 T P o) t =
        qyC .done 1 (Function.update T cap
          (FinTM.bufferTape (pre ++ ([] ++ [] ++ qyBody false rr wd ++ suf))))
          (Function.update (Function.update P src wd.length) cap
            ((pre ++ ([] ++ [] ++ qyBody false rr wd ++ suf)).length : ℤ)) o ∧
      ∀ u < t, ((embedSilentTM (dzOne src) cap (qyEmitTM 1 0 [] suf rr false)).runFrom
          (qyC (x := x) (.pre 0) 1 T P o) u).state ≠ some .done := by
  have hcap : cap ∉ Set.range (dzOne src) := fun ⟨_, h⟩ => hne h
  obtain ⟨t, ht, hrun, hcut⟩ := qy_emit_run (x := x) (0 : Fin 1) [] suf rr false 1
    (fun i => T (dzOne src i)) (fun i => P (dzOne src i)) [] wd hT hP
  obtain ⟨h1, h2⟩ := dz_silent (dzOne src) cap hcap (qyEmitTM 1 0 [] suf rr false) (.pre 0) .done 1
    T (Function.update T cap
      (FinTM.bufferTape (pre ++ ([] ++ [] ++ qyBody false rr wd ++ suf))))
    P (Function.update (Function.update P src wd.length) cap
      ((pre ++ ([] ++ [] ++ qyBody false rr wd ++ suf)).length : ℤ)) o pre
    ([] ++ [] ++ qyBody false rr wd ++ suf) _ _ t hTc hPc hrun
    (fun i => ⟨by
      show Function.update T cap _ src = T src
      rw [Function.update_of_ne hne], by
      show Function.update (Function.update P src wd.length) cap _ src = _
      rw [Function.update_of_ne hne, Function.update_self]
      obtain rfl : i = 0 := Subsingleton.elim _ _
      rw [Function.update_self]⟩)
    ⟨Function.update_self _ _ _, Function.update_self _ _ _⟩
    (fun j hj hjc => ⟨Function.update_of_ne hjc _ _, by
      rw [Function.update_of_ne hjc,
        Function.update_of_ne (show j ≠ src from fun h => hj ⟨0, h.symm⟩)]⟩)
  refine ⟨t, by simpa using ht, h1, fun u hu => ?_⟩
  rw [h2]
  exact hcut u hu

/-- The length of a pair: `|⟨x, α⟩| = 2|x| + 2 + |α|`. -/
private theorem dz_pairEncode_length (x α : List Bool) :
    (pairEncode x α).length = 2 * x.length + 2 + α.length := by
  rw [pairEncode_eq]
  induction x with
  | nil => simp; omega
  | cons b x ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

/-- **The rewrite.** From the extractor's call over a layout with the query's tail on tape `8`, the
budget's bits `bits b` on tape `10`, the word `1^{n + 1}` on tape `2`, the core's input tape `11`
blank, these heads at `0`: the install call of the composite extractor leaves `α = dzAlpha tail` on
tape `8`; three emissions under the capture wrapper write `⟨⟨bits b, α⟩, 1^{n + 1}⟩` on tape `11`
(`dz_core_word`); its rewind returns that head to `0`, and the run enters the hosted core.

**Proof sketch.** Five hosted phases: `qy_callHost` with the extractor's bank holding the seam of
the tail (`dz_arg_bank`); `dz_emit_run` three times (`bits b` four times each with
`[false, false, true, true]`; `α` doubled with `[false, true]`; `1^{n + 1}` once), each appending to
the capture tape; `qy_rewind` on the captured word. The emitters' heads stay at their words'
ends. -/
private theorem dz_rewrite {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) {z : List Bool} (L : Fin 14 → ℤ → Option Bool) (Pn : Fin 14 → ℤ)
    (tail B : List Bool) (h2 : L 2 = FinTM.bufferTape ([true] ++ z))
    (h8 : L 8 = FinTM.bufferTape tail) (h10 : L 10 = FinTM.bufferTape B)
    (h11 : L 11 = FinTM.bufferTape []) (hP2 : Pn 2 = 0) (hP8 : Pn 8 = 0) (hP10 : Pn 10 = 0)
    (hP11 : Pn 11 = 0) :
    ∃ t ≤ κ.acA * (tail.length + 1) + 10 * B.length + 6 * (dzAlpha tail).length + 4 * z.length + 40,
      Segment (dzQ κ) (dzQF κ) (fun _ => True)
        (qyC (x := z) ⟨.al, Sum.inl ()⟩ 1 (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) [])
        (qyC ⟨.runR, κ.iR (κ.rE, true)⟩ 1
          (dzLay (Function.update (Function.update L 8 (FinTM.bufferTape (dzAlpha tail))) 11
            (FinTM.bufferTape (pairEncode (pairEncode B (dzAlpha tail)) ([true] ++ z))))
            (FinTM.bufferTape []))
          (dzLay (Function.update (Function.update (Function.update Pn 10 (B.length : ℤ)) 8
            ((dzAlpha tail).length : ℤ)) 2 ((([true] ++ z).length : ℕ) : ℤ)) 0) []) t := by
  set Bl : ℤ → Option Bool := FinTM.bufferTape [] with hBl
  -- al: `α` by the composite extractor
  obtain ⟨t1, ht1, hpos1, hcut1, hrun1⟩ := κ.acS z tail
  have c1 := qy_callHost κ.ac κ.acK κ.bA κ.acE κ.acX tail _ t1 hpos1 hcut1 hrun1
    (dzLay L Bl) (dzLay Pn 0) [] (dz_arg_bank κ L 8 _ _ _ _ (by omega) κ.acK _ h8)
    (dz_zero_bank κ Pn 8 _ _ _ _ (by omega) hP8)
  rw [show κ.bA ⟨0, κ.acK⟩ = κ.tp 8 from rfl, dzLay_update] at c1
  obtain ⟨L1, hL1⟩ : ∃ L1 : Fin 14 → ℤ → Option Bool,
      L1 = Function.update L 8 (FinTM.bufferTape (dzAlpha tail)) := ⟨_, rfl⟩
  rw [← hL1] at c1
  have seg1 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .al (Sum.inl ()) (Sum.inr κ.acX)
    ⟨.e1, QyEm.pre 0⟩ 1 1 _ _ _ _ [] [] t1 c1.1 (by simp [dzQRed])
    (qy_guard_of_cut (Sum.inr κ.acX) (dzQRed κ .al) (fun s hs => by simp [dzQRed, hs]) c1.2)
    (dzQF κ) (fun s => dz_notF κ .al s (by simp) (by simp))
  -- e1: the budget's bits, each four times, and the inner separator
  have hL1_10 : L1 10 = FinTM.bufferTape B := by rw [hL1, Function.update_of_ne (by decide), h10]
  have hL1_11 : L1 11 = FinTM.bufferTape [] := by rw [hL1, Function.update_of_ne (by decide), h11]
  obtain ⟨t2, ht2, c2, k2⟩ := dz_emit_run (x := z) (κ.tp 10) (κ.tp 11) (κ.tp_ne (by decide))
    [false, false, true, true] 3 (dzLay L1 Bl) (dzLay Pn 0) [] [] B (by rw [dzLay_tp, hL1_10])
    (by rw [dzLay_tp, hP10]) (by rw [dzLay_tp, hL1_11]) (by rw [dzLay_tp, hP11]; rfl)
  rw [dzLay_update, dzLay_update, dzLay_update] at c2
  set O1 := [] ++ ([] ++ [] ++ qyBody false 3 B ++ [false, false, true, true]) with hO1
  obtain ⟨P2, eP2⟩ : ∃ P2 : Fin 14 → ℤ,
      P2 = Function.update (Function.update Pn 10 (B.length : ℤ)) 11 (O1.length : ℤ) := ⟨_, rfl⟩
  rw [← eP2] at c2
  have seg2 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .e1 (.pre 0) .done ⟨.e2, QyEm.pre 0⟩
    1 1 _ _ _ _ [] [] _ c2 (by simp [dzQRed])
    (qy_guard_of_cut QyEm.done (dzQRed κ .e1) (fun s hs => by simp [dzQRed, hs]) k2)
    (dzQF κ) (fun s => dz_notF κ .e1 s (by simp) (by simp))
  -- e2: the code doubled and the outer separator
  obtain ⟨t3, ht3, c3, k3⟩ := dz_emit_run (x := z) (κ.tp 8) (κ.tp 11) (κ.tp_ne (by decide))
    [false, true] 1 (dzLay (Function.update L1 11 (FinTM.bufferTape O1)) Bl) (dzLay P2 0) [] O1
    (dzAlpha tail)
    (by rw [dzLay_tp, Function.update_of_ne (by decide), hL1, Function.update_self])
    (by rw [dzLay_tp, eP2, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      hP8])
    (by rw [dzLay_tp, Function.update_self]) (by rw [dzLay_tp, eP2, Function.update_self])
  rw [dzLay_update, dzLay_update, dzLay_update, Function.update_idem] at c3
  set O2 := O1 ++ ([] ++ [] ++ qyBody false 1 (dzAlpha tail) ++ [false, true]) with hO2
  obtain ⟨P3, eP3⟩ : ∃ P3 : Fin 14 → ℤ,
      P3 = Function.update (Function.update P2 8 ((dzAlpha tail).length : ℤ)) 11 (O2.length : ℤ) :=
    ⟨_, rfl⟩
  rw [← eP3] at c3
  have seg3 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .e2 (.pre 0) .done ⟨.e3, QyEm.pre 0⟩
    1 1 _ _ _ _ [] [] _ c3 (by simp [dzQRed])
    (qy_guard_of_cut QyEm.done (dzQRed κ .e2) (fun s hs => by simp [dzQRed, hs]) k3)
    (dzQF κ) (fun s => dz_notF κ .e2 s (by simp) (by simp))
  -- e3: the tail `1^{n + 1}`
  obtain ⟨t4, ht4, c4, k4⟩ := dz_emit_run (x := z) (κ.tp 2) (κ.tp 11) (κ.tp_ne (by decide))
    [] 0 (dzLay (Function.update L1 11 (FinTM.bufferTape O2)) Bl) (dzLay P3 0) [] O2
    ([true] ++ z)
    (by rw [dzLay_tp, Function.update_of_ne (by decide), hL1, Function.update_of_ne (by decide),
      h2])
    (by rw [dzLay_tp, eP3, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      eP2, Function.update_of_ne (by decide), Function.update_of_ne (by decide), hP2])
    (by rw [dzLay_tp, Function.update_self]) (by rw [dzLay_tp, eP3, Function.update_self])
  rw [dzLay_update, dzLay_update, dzLay_update, Function.update_idem] at c4
  set O3 := O2 ++ ([] ++ [] ++ qyBody false 0 ([true] ++ z) ++ []) with hO3
  have hword : O3 = pairEncode (pairEncode B (dzAlpha tail)) ([true] ++ z) := by
    rw [hO3, hO2, hO1]
    exact dz_core_word B (dzAlpha tail) ([true] ++ z)
  rw [hword] at c4
  obtain ⟨P4, eP4⟩ : ∃ P4 : Fin 14 → ℤ,
      P4 = Function.update (Function.update P3 2 ((([true] ++ z).length : ℕ) : ℤ)) 11
        ((pairEncode (pairEncode B (dzAlpha tail)) ([true] ++ z)).length : ℤ) := ⟨_, rfl⟩
  rw [← eP4] at c4
  have seg4 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .e3 (.pre 0) .done
    ⟨.rwZ, RewindPhase.start⟩ 1 1 _ _ _ _ [] [] _ c4 (by simp [dzQRed])
    (qy_guard_of_cut QyEm.done (dzQRed κ .e3) (fun s hs => by simp [dzQRed, hs]) k4)
    (dzQF κ) (fun s => dz_notF κ .e3 s (by simp) (by simp))
  -- rwZ: rewind the core's input
  obtain ⟨t5c, k5⟩ := qy_rewind (x := z) (κ.tp 11) 1
    (dzLay (Function.update L1 11 (FinTM.bufferTape
      (pairEncode (pairEncode B (dzAlpha tail)) ([true] ++ z)))) Bl) (dzLay P4 0) []
    (pairEncode (pairEncode B (dzAlpha tail)) ([true] ++ z))
    (pairEncode (pairEncode B (dzAlpha tail)) ([true] ++ z)).length le_rfl
    (by rw [dzLay_tp, Function.update_self])
    (by rw [dzLay_tp, eP4, Function.update_self])
  rw [dzLay_update] at t5c
  have hPend : Function.update P4 11 0 = Function.update (Function.update (Function.update Pn 10
      (B.length : ℤ)) 8 ((dzAlpha tail).length : ℤ)) 2 ((([true] ++ z).length : ℕ) : ℤ) := by
    funext i
    rw [eP4, eP3, eP2]
    simp only [Function.update_apply]
    split_ifs <;> first | rfl | (subst_vars; simp_all)
  rw [hPend] at t5c
  have seg5 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .rwZ .start .done
    ⟨.runR, κ.iR (κ.rE, true)⟩ 1 1 _ _ _ _ [] [] _ t5c (by simp [dzQRed])
    (qy_guard_of_cut RewindPhase.done (dzQRed κ .rwZ) (fun s hs => by simp [dzQRed, hs]) k5)
    (dzQF κ) (fun s => dz_notF κ .rwZ s (by simp) (by simp))
  rw [← hL1]
  refine ⟨_, ?_, seg1.trans (seg2.trans (seg3.trans (seg4.trans seg5)))⟩
  have hlen := dz_pairEncode_length (pairEncode B (dzAlpha tail)) ([true] ++ z)
  have hlen' := dz_pairEncode_length B (dzAlpha tail)
  have ht1' : t1 ≤ κ.acA * (tail.length + 1) := ht1
  simp only [List.length_cons, List.length_nil, List.length_append] at ht2 ht3 ht4 hlen ⊢
  nlinarith

/-! ### The two hosted runs and their verdicts -/

/-- **The middle's hosted run.** From the hosted core's entry over a layout with the core's input
`z'` on tape `11`, the stream `s₁` on the block tape, the capture tape blank, the clock's counter
`bits G` on tape `3`, these heads and every block tape's at `0`: if the core first reaches its
verdict `v` (`accept` or `reject`) at `TR`, the run accepts when `TR ≤ G` and `v` is `accept`, and
rejects otherwise, within `5G + 2|bits G| + 3` steps.

**Proof sketch.** The hosted clock's clause `κ.cR` at the core's start configuration
`Turing.streamStartCfg z' jR rE s₁` (read through its field equations), the counter worth `G`
(`qy_bits_val`). The core stops (at `accept`, `reject` or a halt) first at `TR`: before it, it is
live (`MultiTapeTM.runFrom_state_ne_none_of_le`) and off both verdicts. If `TR ≤ G`, the finish
clause gives `fR` of the verdict, which the dispatch sends to the matching verdict (`fR` injective,
`accept ≠ reject`); otherwise the timeout clause gives some `oR r`, rejected. The guard is the
clock's cut. -/
private theorem dz_runR {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) {z : List Bool} (L : Fin 14 → ℤ → Option Bool) (Pn : Fin 14 → ℤ)
    (z' s₁ : List Bool) (G : ℕ) (h3 : L 3 = FinTM.bufferTape (Nat.bits G))
    (h6 : L 6 = FinTM.bufferTape s₁) (h11 : L 11 = FinTM.bufferTape z')
    (h12 : L 12 = FinTM.bufferTape []) (hP3 : Pn 3 = 0) (hP6 : Pn 6 = 0) (hP11 : Pn 11 = 0)
    (hP12 : Pn 12 = 0) (TR : ℕ) (v : κ.SR) (hv : v = κ.rA ∨ v = κ.rJ)
    (hTR : (κ.R.runFrom (streamStartCfg z' κ.jR κ.rE s₁) TR).state = some v)
    (hcut : ∀ u < TR, (κ.R.runFrom (streamStartCfg z' κ.jR κ.rE s₁) u).state ≠ some κ.rA ∧
      (κ.R.runFrom (streamStartCfg z' κ.jR κ.rE s₁) u).state ≠ some κ.rJ) :
    ∃ t ≤ 5 * G + 2 * (Nat.bits G).length + 3, ∃ (T' : Fin κ.K → ℤ → Option Bool)
      (P' : Fin κ.K → ℤ), Segment (dzQ κ) (dzQF κ) (fun _ => True)
        (qyC (x := z) ⟨.runR, κ.iR (κ.rE, true)⟩ 1 (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) [])
        (qyC (if TR ≤ G ∧ v = κ.rA then dzAcc κ else dzRej κ) 1 T' P' []) t := by
  set c0 := streamStartCfg z' κ.jR κ.rE s₁ with hc0
  set stop : κ.SR → Bool := fun q => decide (q = κ.rA ∨ q = κ.rJ) with hstop
  have hlive : ∀ u ≤ TR, (κ.R.runFrom c0 u).state ≠ none :=
    MultiTapeTM.runFrom_state_ne_none_of_le _ _ TR (by rw [hTR]; exact Option.some_ne_none _)
  have hstopTR : (κ.R.runFrom c0 TR).Stopped stop := by
    rw [Cfg.stopped_iff]
    refine Or.inr ⟨v, hTR, ?_⟩
    rw [hstop]
    exact decide_eq_true hv
  have hnot : ∀ u < TR, ¬(κ.R.runFrom c0 u).Stopped stop := by
    intro u hu h
    rw [Cfg.stopped_iff] at h
    rcases h with h | ⟨s, hs, hst⟩
    · exact hlive u hu.le h
    · rw [hstop] at hst
      rcases of_decide_eq_true hst with rfl | rfl
      · exact (hcut u hu).1 hs
      · exact (hcut u hu).2 hs
  have hbits := qy_bits_val G
  have hspec := κ.cR (x := z) (κ.tp 11) (κ.tp 12) (κ.tp 3) κ.bR (κ.tp_ne (by decide))
    (κ.tp_ne (by decide)) (κ.tp_ne (by decide)) (fun ⟨i, h⟩ => κ.bR_ne i 11 (by decide) h)
    (fun ⟨i, h⟩ => κ.bR_ne i 12 (by decide) h) (fun ⟨i, h⟩ => κ.bR_ne i 3 (by decide) h)
    (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) [] c0 κ.rE (Nat.bits G)
    (by rw [hc0, streamStartCfg_state]) (by rw [hc0, streamStartCfg_inputPos])
    (by rw [hc0, streamStartCfg_output]) (by rw [dzLay_tp, h11]) (by rw [dzLay_tp, hP11])
    (fun i => by
      rw [hc0]
      constructor
      · funext a
        rw [streamStartCfg_workTapes]
        by_cases hi : i = κ.jR
        · rw [if_pos hi, hi, κ.bR_j, dzLay_tp, h6]
        · rw [if_neg hi, dzLay_off _ _ _ (κ.bR_off i hi), FinTM.bufferTape_nil]
      · rw [streamStartCfg_workTapePos]
        by_cases hi : i = κ.jR
        · rw [hi, κ.bR_j, dzLay_tp, hP6]
        · rw [dzLay_off _ _ _ (κ.bR_off i hi)])
    (by rw [dzLay_tp, h12]) (by rw [dzLay_tp, hP12]) (by rw [dzLay_tp, h3]) (by rw [dzLay_tp, hP3])
  rw [hbits] at hspec
  obtain ⟨hfin, hto⟩ := hspec
  have hguard : ∀ (t : ℕ), (∀ u < t, ∀ r,
      ((embedEmitTM κ.sR κ.HR).runFrom (qyC (x := z) (κ.iR (κ.rE, true)) 1
        (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) []) u).state ≠ some (κ.fR r) ∧
      ((embedEmitTM κ.sR κ.HR).runFrom (qyC (x := z) (κ.iR (κ.rE, true)) 1
        (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) []) u).state ≠ some (κ.oR r)) →
      ∀ u < t, ∀ s, ((dzQM κ .runR).runFrom (qyC (x := z) (κ.iR (κ.rE, true)) 1
        (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) []) u).state = some s →
          dzQRed κ .runR s = none := by
    intro t hc u hu s hs
    have h1 : ¬∃ b, s = κ.fR (some (κ.rA, b)) := fun ⟨b, hb⟩ =>
      (hc u hu (some (κ.rA, b))).1 (hs.trans (by rw [hb]))
    have h2 : ¬∃ r, s = κ.fR r := fun ⟨r, hr⟩ => (hc u hu r).1 (hs.trans (by rw [hr]))
    have h3 : ¬∃ r, s = κ.oR r := fun ⟨r, hr⟩ => (hc u hu r).2 (hs.trans (by rw [hr]))
    simp only [dzQRed, if_neg h1, if_neg h2, if_neg h3]
  by_cases hTG : TR ≤ G
  · obtain ⟨t, ht, b, T', P', hrun, -, -, hcutH⟩ := hfin TR hTG hstopTR hnot
    rw [hTR, Option.map_some] at hrun
    have hred : dzQRed κ .runR (κ.fR (some (v, b))) =
        some (if TR ≤ G ∧ v = κ.rA then dzAcc κ else dzRej κ) := by
      rcases hv with rfl | rfl
      · rw [if_pos ⟨hTG, rfl⟩]
        simp only [dzQRed]
        rw [if_pos ⟨b, rfl⟩]
      · rw [if_neg (fun h => κ.hAJ h.2.symm)]
        simp only [dzQRed]
        rw [if_neg (fun ⟨b', hb'⟩ =>
            κ.hAJ (congrArg Prod.fst (Option.some_inj.mp (κ.fRi hb'))).symm),
          if_pos ⟨_, rfl⟩]
    exact ⟨t + 1, by omega, T', P', qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .runR
      (κ.iR (κ.rE, true)) _ _ 1 1 _ _ _ _ [] [] t hrun hred (hguard t hcutH) (dzQF κ)
      (fun s => dz_notF κ .runR s (by simp) (by simp))⟩
  · obtain ⟨t, ht, r, T', P', hrun, hcutH⟩ := hto (fun u hu h => by
      rcases Nat.lt_or_ge u TR with h' | h'
      · exact hnot u h' h
      · omega)
    have hred : dzQRed κ .runR (κ.oR r) =
        some (if TR ≤ G ∧ v = κ.rA then dzAcc κ else dzRej κ) := by
      rw [if_neg (fun h => hTG h.1)]
      simp only [dzQRed]
      rw [if_neg (fun ⟨b, hb⟩ => κ.fRo _ _ hb.symm), if_neg (fun ⟨r', hr'⟩ => κ.fRo _ _ hr'.symm),
        if_pos ⟨r, rfl⟩]
    exact ⟨t + 1, by omega, T', P', qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .runR
      (κ.iR (κ.rE, true)) _ _ 1 1 _ _ _ _ [] [] t hrun hred (hguard t hcutH) (dzQF κ)
      (fun s => dz_notF κ .runR s (by simp) (by simp))⟩

/-- **The top's hosted run and its read.** From the hosted decider's entry over a layout with the
query's tail on tape `8`, the capture tape and the decider's tapes blank, the clock's counter
`bits G` on tape `3`, these heads at `0`, the run reaches a verdict within `6G + 2|bits G| + 10`
steps; whenever the decider has halted on the tail by some `τ ≤ G`, the verdict is the acceptance
exactly when the decider's output at `τ` starts with `false`.

**Proof sketch.** The hosted clock's clause `κ.cB` at `BF`'s initial configuration on the tail
(read through `MultiTapeTM.initCfg_eq` and `Cfg.init`'s equations), stopping at the halt. If the
decider halts by `G`, at its first halt `τ₀` (`Nat.find`) the finish clause leaves its output on the
capture tape (at most `τ₀` symbols, `MultiTapeTM.output_length_le`); the dispatch rewinds it
(`qy_rewind`) and the take (`dz_take_run`) reads its first cell: `false` accepts, anything else
rejects. A halted run is fixed (`MultiTapeTM.runFrom_of_halt`), so the output at every later
`τ ≤ G` is the same. Otherwise the timeout clause gives some `oB r`, rejected. -/
private theorem dz_top_run {f g : ℕ → ℕ} {c : EffectiveNDMachineCode} {BF : FinTM Bool}
    (κ : DzKit f g c BF) {z : List Bool} (L : Fin 14 → ℤ → Option Bool) (Pn : Fin 14 → ℤ)
    (tail : List Bool) (G : ℕ) (h3 : L 3 = FinTM.bufferTape (Nat.bits G))
    (h8 : L 8 = FinTM.bufferTape tail) (h12 : L 12 = FinTM.bufferTape [])
    (h13 : L 13 = FinTM.bufferTape []) (hP3 : Pn 3 = 0) (hP8 : Pn 8 = 0) (hP12 : Pn 12 = 0)
    (hP13 : Pn 13 = 0) :
    ∃ t ≤ 6 * G + 2 * (Nat.bits G).length + 10, ∃ (v : Σ i, DzQPh κ i)
      (T' : Fin κ.K → ℤ → Option Bool) (P' : Fin κ.K → ℤ), (v = dzAcc κ ∨ v = dzRej κ) ∧
      Segment (dzQ κ) (dzQF κ) (fun _ => True)
        (qyC (x := z) ⟨.runB, κ.iB (BF.tm.q₀, true)⟩ 1 (dzLay L (FinTM.bufferTape []))
          (dzLay Pn 0) [])
        (qyC v 1 T' P' []) t ∧
      ∀ τ ≤ G, (BF.tm.runFrom (BF.tm.initCfg tail) τ).state = none →
        (v = dzAcc κ ↔ (BF.tm.runFrom (BF.tm.initCfg tail) τ).output.head? = some false) := by
  set c0 := BF.tm.initCfg tail with hc0
  have hbits := qy_bits_val G
  have hspec := κ.cB (x := z) (κ.tp 8) (κ.tp 12) (κ.tp 3) κ.bB (κ.tp_ne (by decide))
    (κ.tp_ne (by decide)) (κ.tp_ne (by decide)) (fun ⟨i, h⟩ => κ.bB_ne i 8 (by decide) h)
    (fun ⟨i, h⟩ => κ.bB_ne i 12 (by decide) h) (fun ⟨i, h⟩ => κ.bB_ne i 3 (by decide) h)
    (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) [] c0 BF.tm.q₀ (Nat.bits G)
    (by rw [hc0, MultiTapeTM.initCfg_eq, Cfg.init_state])
    (by rw [hc0, MultiTapeTM.initCfg_eq, Cfg.init_inputPos])
    (by rw [hc0, MultiTapeTM.initCfg_eq, Cfg.init_output]) (by rw [dzLay_tp, h8])
    (by rw [dzLay_tp, hP8])
    (fun i => by
      rw [hc0, MultiTapeTM.initCfg_eq]
      constructor
      · funext a
        rw [Cfg.init_workTapes]
        by_cases hi : (i : ℕ) = 0
        · have hk : 0 < BF.k := by have := i.isLt; omega
          rw [show i = ⟨0, hk⟩ from Fin.ext hi, show κ.bB ⟨0, hk⟩ = κ.tp 13 from rfl, dzLay_tp,
            h13, FinTM.bufferTape_nil]
        · have : 14 ≤ (κ.bB i : ℕ) := by
            unfold DzKit.bB
            exact dz_bank_off _ _ _ _ _ (by omega) i hi
          rw [dzLay_off _ _ _ this, FinTM.bufferTape_nil]
      · rw [Cfg.init_workTapePos]
        by_cases hi : (i : ℕ) = 0
        · have hk : 0 < BF.k := by have := i.isLt; omega
          rw [show i = ⟨0, hk⟩ from Fin.ext hi, show κ.bB ⟨0, hk⟩ = κ.tp 13 from rfl, dzLay_tp,
            hP13]
        · have : 14 ≤ (κ.bB i : ℕ) := by
            unfold DzKit.bB
            exact dz_bank_off _ _ _ _ _ (by omega) i hi
          rw [dzLay_off _ _ _ this])
    (by rw [dzLay_tp, h12]) (by rw [dzLay_tp, hP12]) (by rw [dzLay_tp, h3]) (by rw [dzLay_tp, hP3])
  rw [hbits] at hspec
  obtain ⟨hfin, hto⟩ := hspec
  have hstopped : ∀ u, (BF.tm.runFrom c0 u).Stopped (fun _ => false) ↔
      (BF.tm.runFrom c0 u).state = none := by
    intro u
    rw [Cfg.stopped_iff]
    constructor
    · rintro (h | ⟨s, -, hs⟩)
      · exact h
      · exact absurd hs (by simp)
    · exact Or.inl
  have hguard : ∀ (t : ℕ), (∀ u < t, ∀ r,
      ((embedEmitTM κ.sB κ.HB).runFrom (qyC (x := z) (κ.iB (BF.tm.q₀, true)) 1
        (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) []) u).state ≠ some (κ.fB r) ∧
      ((embedEmitTM κ.sB κ.HB).runFrom (qyC (x := z) (κ.iB (BF.tm.q₀, true)) 1
        (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) []) u).state ≠ some (κ.oB r)) →
      ∀ u < t, ∀ s, ((dzQM κ .runB).runFrom (qyC (x := z) (κ.iB (BF.tm.q₀, true)) 1
        (dzLay L (FinTM.bufferTape [])) (dzLay Pn 0) []) u).state = some s →
          dzQRed κ .runB s = none := by
    intro t hc u hu s hs
    have h1 : ¬∃ r, s = κ.fB r := fun ⟨r, hr⟩ => (hc u hu r).1 (hs.trans (by rw [hr]))
    have h2 : ¬∃ r, s = κ.oB r := fun ⟨r, hr⟩ => (hc u hu r).2 (hs.trans (by rw [hr]))
    simp only [dzQRed, if_neg h1, if_neg h2]
  by_cases hh : ∃ τ ≤ G, (BF.tm.runFrom c0 τ).state = none
  · have h0 : ∃ τ, (BF.tm.runFrom c0 τ).state = none := by
      obtain ⟨τ, -, h⟩ := hh
      exact ⟨τ, h⟩
    set τ₀ := Nat.find h0 with hτ₀
    have hτ₀G : τ₀ ≤ G := by
      obtain ⟨τ, hτ, h⟩ := hh
      exact (Nat.find_min' h0 h).trans hτ
    have hst0 : (BF.tm.runFrom c0 τ₀).state = none := Nat.find_spec h0
    obtain ⟨t, ht, b, T', P', hrun, hcap, hpos, hcutH⟩ := hfin τ₀ hτ₀G ((hstopped τ₀).mpr hst0)
      (fun u hu h => Nat.find_min h0 hu ((hstopped u).mp h))
    rw [hst0, Option.map_none] at hrun
    set out := (BF.tm.runFrom c0 τ₀).output with hout
    have seg1 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .runB (κ.iB (BF.tm.q₀, true))
      (κ.fB none) ⟨.rwK, RewindPhase.start⟩ 1 1 _ _ _ _ [] [] t hrun
      (by simp only [dzQRed]; rw [if_pos ⟨none, rfl⟩]) (hguard t hcutH) (dzQF κ)
      (fun s => dz_notF κ .runB s (by simp) (by simp))
    -- rwK: rewind the captured output
    have c2 := qy_rewind (x := z) (κ.tp 12) 1 T' P' [] out out.length le_rfl hcap hpos
    have seg2 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .rwK .start .done ⟨.rd, none⟩
      1 1 _ _ _ _ [] [] _ c2.1 (by simp [dzQRed])
      (qy_guard_of_cut RewindPhase.done (dzQRed κ .rwK) (fun s hs => by simp [dzQRed, hs]) c2.2)
      (dzQF κ) (fun s => dz_notF κ .rwK s (by simp) (by simp))
    -- rd: read the captured output's first cell
    have c3 := dz_take_run (x := z) (κ.tp 12) 1 T' (Function.update P' (κ.tp 12) 0) []
    rw [Function.update_self, hcap] at c3
    set v : Σ i, DzQPh κ i := if out.head? = some false then dzAcc κ else dzRej κ with hv
    have hred : dzQRed κ .rd (some (FinTM.bufferTape out 0)) = some v := by
      rw [hv]
      rcases out with _ | ⟨b0, out'⟩
      · simp [dzQRed, FinTM.bufferTape_nil]
      · have e : FinTM.bufferTape (b0 :: out') 0 = some b0 := by
          rw [FinTM.bufferTape_eq, if_pos le_rfl]
          rfl
        rw [e]
        cases b0 <;> simp [dzQRed]
    have seg3 := qy_hosted (dzQM κ) ⟨.flag, none⟩ (dzQRed κ) .rd none
      (some (FinTM.bufferTape out 0)) v 1 1 _ _ _ _ [] [] 1 c3 hred (fun u hu s hs => by
        obtain rfl : u = 0 := by omega
        rw [MultiTapeTM.runFrom_zero] at hs
        cases Option.some.inj hs
        simp [dzQRed]) (dzQF κ) (fun s => dz_notF κ .rd s (by simp) (by simp))
    refine ⟨_, ?_, v, _, _, ?_, seg1.trans (seg2.trans seg3), fun τ hτ hstτ => ?_⟩
    · have hlen : out.length ≤ τ₀ := by
        rw [hout, hc0]
        exact MultiTapeTM.output_length_le _ _ _
      omega
    · rw [hv]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · have hle : τ₀ ≤ τ := Nat.find_min' h0 hstτ
      have hsame : BF.tm.runFrom c0 τ = BF.tm.runFrom c0 τ₀ := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
        rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hst0]
      rw [hsame, ← hout, hv]
      split_ifs with hf
      · exact ⟨fun _ => hf, fun _ => rfl⟩
      · exact ⟨fun h => absurd h (dz_acc_ne_rej κ).symm, fun h => absurd h hf⟩
  · obtain ⟨t, ht, r, T', P', hrun, hcutH⟩ := hto (fun u hu h => hh ⟨u, hu, (hstopped u).mp h⟩)
    have hred : dzQRed κ .runB (κ.oB r) = some (dzRej κ) := by
      simp only [dzQRed]
      rw [if_neg (fun ⟨r', hr'⟩ => κ.fBo _ _ hr'.symm), if_pos ⟨r, rfl⟩]
    refine ⟨t + 1, by omega, dzRej κ, T', P', Or.inr rfl, qy_hosted (dzQM κ) ⟨.flag, none⟩
      (dzQRed κ) .runB (κ.iB (BF.tm.q₀, true)) _ _ 1 1 _ _ _ _ [] [] t hrun hred (hguard t hcutH)
      (dzQF κ) (fun s => dz_notF κ .runB s (by simp) (by simp)), fun τ hτ hstτ => ?_⟩
    exact absurd ⟨τ, hτ, hstτ⟩ hh

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
