/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.OracleNondeterministic
import TCSlib.Complexity.ClassNP.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle complexity classes: `Pᴼ` and `NPᴼ`

[AB09, Definition 3.5]: for a language `O`, `Pᴼ` is the class of languages
decided by polynomial-time deterministic oracle machines with oracle `O`, and
`NPᴼ` the class decided by polynomial-time nondeterministic oracle machines with
oracle `O`. Both are rendered in the campaign's exact class normal forms —
`DTIMEOracle`/`NTIMEOracle` with the `c · T n` constant absorption and the
`⋃ c, (n ^ c + 1)` polynomial union — so that every lemma about `DTIME`/`NTIME`
has a mechanical oracle counterpart.

## Design

* **`NPᴼ` is machine-first.** Unrelativized `NP` is verifier-first and
  `NP = ⋃ c, NTIME (fun n => n ^ c + 1)` is Theorem 2.6 (the `+ 1` is load-bearing
  under the exact-budget conventions — P3.1 round 1, finding 1); but
  [AB09, Definition 3.5] *defines*
  `NPᴼ` directly by nondeterministic oracle machines, so here the `NTIMEOracle`
  union **is** the definition and no certificate form is claimed (a relativized
  certificate characterization would need oracle-aware verifiers and is not in
  the campaign's scope).
* **Clocks are relative to the given oracle.** `DecidesInTime` is stated at the
  oracle `O` being used, so a machine's time bound is a promise about its runs
  with *that* oracle only. [BGS75] instead clocks its enumerated machines under
  *every* oracle; that stronger, enumeration-friendly reading is a property of
  the *stage construction* of [AB09, Theorem 3.7] and is introduced there
  (phase P3.2), not baked into the classes. (Seeded to the P3.1 audit.)
* **The workhorse lemma** is `Complexity.mem_POracle_of_polyTimeReducible`:
  `L ≤ₚ O → L ∈ Pᴼ` — write the reduction's output on the query tape, query
  once, copy the answer out. Example 3.6(1), `NP ⊆ P^SAT`, and the easy halves
  of [AB09, Theorem 3.7] are all instances or corollaries.

## Main definitions

* `Complexity.DTIMEOracle`, `Complexity.NTIMEOracle` — timed oracle classes with
  constant absorption. [AB09, §3.4]
* `Complexity.POracle`, `Complexity.NPOracle` — `Pᴼ` and `NPᴼ`.
  [AB09, Definition 3.5]

## Main results (all sorried; phase-P3.1 statements)

* `Complexity.P_subset_POracle` — an oracle can only help: `P ⊆ Pᴼ`.
  [AB09, Example 3.6(2), first half]
* `Complexity.POracle_subset_NPOracle` — determinism is a special case of
  nondeterminism, relative to any oracle. [AB09, §3.4]
* `Complexity.mem_POracle_of_polyTimeReducible` — `L ≤ₚ O → L ∈ Pᴼ`.
* `Complexity.oracle_mem_POracle` — `O ∈ Pᴼ`.
* `Complexity.compl_mem_POracle` — `Pᴼ` is closed under complement.
* `Complexity.POracle_eq_P_of_mem_P` — a polynomial-time oracle is redundant:
  `O ∈ P → Pᴼ = P`. [AB09, Example 3.6(2)]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Definition 3.5, Example 3.6.)
* [BGS75] T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP
  question*, SIAM Journal on Computing 4(4), 1975. (The oracle-machine classes,
  pp. 431-433; the all-oracle clock convention noted above.)
-/

namespace Complexity

open Turing

/-- The class of languages decided, with oracle `O`, in time `c · T` for some
constant `c` by a finite well-formed deterministic oracle machine — the oracle
counterpart of `Complexity.DTIME`. [AB09, §3.4] -/
def DTIMEOracle (O : Language Bool) (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinOracleTM Bool), M.DecidesInTime O L fun n => c * T n}

/-- The class of languages decided, with oracle `O`, in nondeterministic time
`c · T` for some constant `c` by a finite well-formed nondeterministic oracle
machine — the oracle counterpart of `Complexity.NTIME`. [AB09, §3.4] -/
def NTIMEOracle (O : Language Bool) (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinOracleNDTM Bool), N.DecidesInTime O L fun n => c * T n}

/-- `Pᴼ`: the languages decidable in deterministic polynomial time with oracle
access to `O`, in the campaign's polynomial normal form `⋃ c, DTIMEOracle O (n^c + 1)`
mirroring `Complexity.P`. [AB09, Definition 3.5] -/
def POracle (O : Language Bool) : Set (Language Bool) :=
  ⋃ c : ℕ, DTIMEOracle O fun n => n ^ c + 1

/-- `NPᴼ`: the languages decidable in nondeterministic polynomial time with
oracle access to `O`. Machine-first, directly following [AB09, Definition 3.5]
(see the module docstring: no certificate form is claimed relative to an
oracle). -/
def NPOracle (O : Language Bool) : Set (Language Bool) :=
  ⋃ c : ℕ, NTIMEOracle O fun n => n ^ c + 1

/-- **An oracle can only help**: every language decidable in polynomial time is
decidable in polynomial time with any oracle, `P ⊆ Pᴼ`.
[AB09, Example 3.6(2), the trivial inclusion]

**Proof sketch.** A `P`-witness `M` embeds as the oracle machine
`Turing.FinTM.toFinOracleTM M`, which never queries;
`Turing.FinTM.toFinOracleTM_computesInTime` transfers `DecidesInTime` verbatim
(same `c`, same exponent) under every oracle `O`. -/
theorem P_subset_POracle (O : Language Bool) : P ⊆ POracle O := by
  sorry

/-- **Determinism is a special case of nondeterminism, relative to any oracle**:
`Pᴼ ⊆ NPᴼ`. [AB09, §3.4]

**Proof sketch.** A `Pᴼ`-witness `M` embeds as
`Turing.FinOracleTM.toFinOracleNDTM M`, whose two transition functions coincide.
By `Turing.OracleTM.toOracleNDTM_runWith` every choice word of length `t`
reproduces `M.tm.runFrom O · t`, so all-branch halting at the budget follows
from `M`'s halting, and some branch accepts iff `M`'s (unique) run outputs
`[true]`, i.e. iff `x ∈ L` by the indicator equation — mirroring
`Complexity.DTIME_subset_NTIME`'s proof over `Turing.MultiTapeTM.toNDTM_runWith`. -/
theorem POracle_subset_NPOracle (O : Language Bool) : POracle O ⊆ NPOracle O := by
  sorry

/-- **The workhorse of the light oracle results**: if `L` Karp-reduces to the
oracle in polynomial time, then `L ∈ Pᴼ` — compute the reduction onto the query
tape, query once, and emit the answer.

**Proof sketch.** Let `f` with machine `F` (time `C·(n+1)^c`) witness `L ≤ₚ O`.
Fill obligations, named for the brief: (i) a capture-style retarget of `F` that
writes its emissions to the **query tape** of the host oracle machine instead of
the physical output — `Turing.captureTM`'s core variant (W1) retargeted to a
designated work tape, run inside the oracle architecture via
`Turing.OracleTM.ofMultiTapeTM`-style state adjunction; (ii) a four-state
query-and-answer tail: enter `qQuery` at `F`'s return seam, then from `qYes`
emit `[true]` and halt, from `qNo` emit `[false]` and halt; (iii) the seam
composition of (i) and (ii) with additive budgets (the `machine-library-design.md`
§12 R2 shape; until the routine layer lands, the glue is the dispatch idiom of
`Turing.bufferedCompTM`). Total time `O(C·(n+1)^c)`; correctness is
`x ∈ L ↔ f x ∈ O` against the single query `f x` — the query string read back is
exactly `f x` by the capture contract and `Turing.OracleTM.queryString`'s
extraction. -/
theorem mem_POracle_of_polyTimeReducible {L O : Language Bool} (h : L ≤ₚ O) :
    L ∈ POracle O := by
  sorry

/-- The oracle itself is decidable with one query: `O ∈ Pᴼ`.

**Proof sketch.** `Complexity.mem_POracle_of_polyTimeReducible` at the identity
reduction `Complexity.PolyTimeReducible.refl`. -/
theorem oracle_mem_POracle (O : Language Bool) : O ∈ POracle O := by
  sorry

/-- **`Pᴼ` is closed under complement**: flip the final answer.

**Proof sketch.** Given a `Pᴼ`-witness `M` for `L`, compose with the one-bit
negation at the output: a wrapper that runs `M` with output captured (W1) and
emits the flipped indicator bit — the oracle-architecture analogue of the
negation closure in `Complexity.compl_mem_P`'s proof. Same budget shape,
constant overhead. -/
theorem compl_mem_POracle {L O : Language Bool} (h : L ∈ POracle O) :
    Lᶜ ∈ POracle O := by
  sorry

/-- **A polynomial-time oracle is redundant**: `O ∈ P → Pᴼ = P`.
[AB09, Example 3.6(2)]

**Proof sketch.** `⊇` is `Complexity.P_subset_POracle`. For `⊆`, let `M` decide
`L` with oracle `O` in time `c·(n^k + 1)`, and let `D` decide `O` in time
`d·(n^e + 1)`. Fill obligations, named for the brief: build a plain machine
simulating `M` step by step, where each `qQuery` step is replaced by running `D`
on the current query string. (i) At each query the host copies the query
tape's **extracted prefix only** — cell `0` up to the first blank — onto a
clean virtual-input region, blanks beyond it (garbage past the first blank or
at negative cells must not reach `D`: the round-1 audit's cell-`1` instance),
runs `D` there with output captured (W1) so the host stays silent, clears
`D`'s scratch, restores the suspended heads, and resumes in the answer state;
(ii) **the ledger, explicitly** (round-1 audit, finding 2): with oracle-time
budget `t = c·(n^k + 1)` there are at most `t` queries, each of length at most
`t` (`Turing.OracleTM.queryString_length_le`); positioning, prefix copy and
restoration cost `O(t + 1)` per query and `D`'s run plus cleanup
`O(d·((t+1)^e + 1))`, so the total is
`O(t + t·(t + 1 + d·((t+1)^e + 1))) = O((t+1)^(1+max 1 e)) =
O((n+1)^(k·(1+max 1 e)))` — the exponent depends on `k` and `e` jointly,
not `k·e + O(1)`; (iii) non-query steps are lockstep
(`Turing.OracleTM.step_eq_of_ne_qQuery`), and the preservation/reset
invariants (suspended tapes untouched, scratch cleared, fixed windows) are
named fill obligations. The composite bound sits inside `P`'s `⋃ c` by the
absorption `(n+1)^c ≤ 2^c·(n^c + 1)`. -/
theorem POracle_eq_P_of_mem_P {O : Language Bool} (h : O ∈ P) : POracle O = P := by
  sorry

end Complexity
