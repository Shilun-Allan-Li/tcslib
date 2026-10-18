/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassP.TimeConstructible

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
binary words, the unranking); the `pairEncode` writer; the ledger. -/
theorem exists_queryTM {f g : ℕ → ℕ} (hf : Complexity.TimeConstructible f)
    (hg : Complexity.TimeConstructible g) :
    ∃ (G : FinTM Bool) (C : ℕ), G.ComputesFunInTime (query f g) fun n => C * (g n + 1) := by
  sorry

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
