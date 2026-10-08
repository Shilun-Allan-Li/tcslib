/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Diagonalization.EXPCOM
import TCSlib.Complexity.TuringMachine.OracleAgreement

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Baker-Gill-Solovay relativization theorem

[AB09, Theorem 3.7] ([BGS75]): there are oracles `A` and `B` with
`P^A = NP^A` and `P^B ≠ NP^B` — so no proof technique that relativizes can
resolve `P` vs `NP`. The `A` half is the `EXPCOM` cluster
(`Diagonalization/EXPCOM`, [AB09, Example 3.6(3)]). The `B` half is this file:
the unary witness language `U_B` is in `NP^B` for every `B` (guess the
witness, ask the oracle), and a stage construction diagonalizes `B` against an
enumeration of deterministic polynomial-time oracle machines so that
`U_B ∉ P^B`.

## Design

* **Extrinsic clocks** ([BGS75, p. 432]; `AroraBarakChapters3-4Plan.md` §7,
  question 4): [BGS75] requires its enumerated machines' polynomial clocks to
  be meaningful under *every* oracle, whereas
  `Turing.FinOracleTM.DecidesInTime` is a promise about one oracle only. The
  enumeration statement below therefore never mentions `DecidesInTime`: it
  speaks of raw `Turing.FinOracleTM.ComputesInTime` horizons (explicit step
  budgets in the style of `Turing.FinOracleNDTM.AcceptsWithin`, oracle-uniform
  by construction), and the stage construction attaches the budget
  `fun n => n ^ i + i` to the index `i` extrinsically.
* **The enumeration is of deterministic machines**: the diagonalization runs
  against the would-be `P^B` deciders, so `Turing.FinOracleTM Bool` is
  enumerated; no universal oracle machine is needed
  (`AroraBarakChapters3-4Plan.md` §2.3).
* **Behavioral equality** ("runs coincide under every oracle") is rendered as
  equality of `ComputesInTime` verdicts at every oracle, input, output, and
  horizon — the state types of two bundled machines differ, so literal
  configuration equality is not expressible, and this observable form is
  exactly what the stage construction consumes.
* **The stage construction is mathematics, not machine-building**: its engine
  is the locality layer of `TCSlib.Complexity.TuringMachine.OracleAgreement`
  (query-set locality, the query-length bound, and the at-most-`t`-queries
  counting bound).

## Main definitions

* `Complexity.unaryWitnessLang` — the book's `U_B`. [AB09, Theorem 3.7]

## Main results (all sorried; phase-P3.2 statements)

* `Complexity.unaryWitnessLang_mem_NPOracle` — `U_B ∈ NP^B`, for every `B`.
* `Complexity.exists_finOracleTM_enumeration` — an enumeration of the
  deterministic finite oracle machines in which every machine recurs at
  arbitrarily late indices, up to behavioral equality under every oracle.
  [BGS75, p. 432]
* `Complexity.exists_oracle_ne` — the stage construction: some `B` has
  `U_B ∈ NP^B \ P^B`. [AB09, Theorem 3.7; BGS75, §3]
* `Complexity.baker_gill_solovay` — both halves assembled.
  [AB09, Theorem 3.7]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Theorem 3.7, pp. 74-75.)
* [BGS75] T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP
  question*, SIAM Journal on Computing 4(4), 1975. (pp. 431-433: the
  all-oracle clock convention; §3: the stage construction.)
-/

namespace Complexity

open Turing

/-- **The unary witness language** `U_B` of [AB09, Theorem 3.7]: the unary
strings `1ⁿ` such that `B` contains some string of length exactly `n`. Finding
the witness is one nondeterministic guess with oracle access to `B`, but a
deterministic polynomial-time machine can examine only polynomially many of
the `2ⁿ` candidates. -/
def unaryWitnessLang (B : Language Bool) : Language Bool :=
  {w | ∃ n : ℕ, w = List.replicate n true ∧ ∃ x : List Bool, x.length = n ∧ x ∈ B}

/-- **`U_B ∈ NP^B`, for every oracle `B`**: guess a string of the input's
length onto the query tape, query, and accept on a positive answer.
[AB09, Theorem 3.7, the easy half: "`U_B` is clearly in `NP^B`"]

**Proof sketch.** A small well-formed `Turing.FinOracleNDTM Bool`: scan the
input left to right, rejecting on every branch if any input symbol is `false`
(so non-unary inputs are out), and at each input position write the current
choice bit onto the query tape and advance both heads — the choice word *is*
the guessed witness ([AB09, §2.1.2], the certificate reading of choice words);
at the input boundary enter `qQuery`; from `qYes` emit `[true]` and halt, from
`qNo` emit `[false]` and halt. Budget: a constant times `n + 1`, inside
`NPOracle`'s `c · (n^1 + 1)` normal form; every branch runs the same number of
steps, so all-branch halting (`Turing.OracleNDTM.HaltsWithin`) holds at the
budget. Correctness, per branch along `Turing.OracleNDTM.runWith`: the string
read back by `Turing.OracleTM.queryString` at the query step is exactly the
first `n` choice bits (a write-and-advance invariant on the query tape — the
guess-writer contract), so on input `1ⁿ` some branch accepts iff some length-`n`
string lies in `B`, i.e. iff `1ⁿ ∈ U_B` (`Complexity.unaryWitnessLang`), and
on non-unary inputs no branch accepts. Fill obligations, named for the brief:
the guess-writer machine and its query-tape read-back contract; the four-state
answer tail shared with `Complexity.mem_POracle_of_polyTimeReducible`'s
obligation (ii) (flagged as a shared routine for the §12 catalog); the budget
arithmetic and `Turing.FinOracleNDTM.DecidesInTime` assembly. -/
theorem unaryWitnessLang_mem_NPOracle (B : Language Bool) :
    unaryWitnessLang B ∈ NPOracle B := by
  sorry

/-- **Enumeration of the deterministic finite oracle machines with infinite
recurrence** [BGS75, p. 432]: there is a family `N : ℕ → Turing.FinOracleTM
Bool` such that every finite oracle machine `M` recurs at arbitrarily late
indices, up to behavioral equality — equal `ComputesInTime` verdicts under
every oracle, at every input, output, and horizon.

The statement is deliberately *clock-free* (no `DecidesInTime`): [BGS75]
requires the enumerated machines' polynomial clocks to hold under **every**
oracle, so the stage construction supplies the budget `fun n => n ^ i + i`
extrinsically at index `i` — an explicit step count, meaningful under any
oracle — rather than reading a clock off the machine. Since every machine
recurs at arbitrarily late indices and the budgets grow with `i`, each machine
is eventually paired with every polynomial majorant (the index plays the role
of [BGS75]'s machine/clock-exponent pairing).

**Proof sketch.** For fixed tape count `k` and state count `m + 1`, the oracle
machines over `Bool` with state space `Fin (m + 1)` form a finite type (the
transition table is a function between finite types), so `Fintype.equivFin`
enumerates the well-formed ones; a pairing of `ℕ` with `ℕ × ℕ × ℕ` (tape
count, state count, table rank — with infinite fibers, supplying the
recurrence and the unbounded clock exponents) produces the family, totalized
by a fixed well-formed one-state default at indices whose rank overflows.
Every bundled `M : Turing.FinOracleTM Bool` relabels its state type along
`Fintype.equivFin` to some `Fin (m + 1)`, preserving runs
configuration-by-configuration under every oracle — the oracle transport of
`Turing.MultiTapeTM.relabelState` / `relabelState_runFrom_init`
(`TCSlib.Complexity.TuringMachine.StateRenaming`), with the query step
commuting with the renaming because `Turing.OracleTM.queryString` ignores the
state. Fill obligations, named for the brief: the `OracleTM` relabelling lemma
(its natural home is the frozen `StateRenaming`/`Oracle` pair, so it lands in
this phase's files — flagged for promotion); transfer of `ComputesInTime`
across the configuration bijection (`Turing.Cfg.mapState` preserves
haltedness and output, as in `Turing.exists_codeTM`); the arithmetic of the
triple pairing. -/
theorem exists_finOracleTM_enumeration :
    ∃ N : ℕ → FinOracleTM Bool,
      ∀ (M : FinOracleTM Bool) (i₀ : ℕ),
        ∃ i, i₀ ≤ i ∧
          ∀ (O : Language Bool) (x output : List Bool) (t : ℕ),
            ((N i).ComputesInTime O x output t ↔ M.ComputesInTime O x output t) := by
  sorry

/-- **The stage construction** [AB09, Theorem 3.7; BGS75, §3]: there is an
oracle `B` whose unary witness language lies in `NP^B` but not in `P^B`.

**Proof sketch.** Fix the enumeration `N` of
`Complexity.exists_finOracleTM_enumeration`, with the extrinsic budget
`T_i n := n ^ i + i` at index `i` ([BGS75]'s all-oracle clock, attached to the
index, never read off the machine).

*Stages.* Construct, by recursion on `i`, finite partial oracles: a finite set
of strings declared **in** `B` and a bound below which all lengths are
**decided**. At stage `i`: pick `nᵢ` exceeding every previously decided length
*and every earlier budget `nⱼ^j + j`* (so no earlier run ever queried a string
of length `≥ nᵢ`, and no later declaration can disturb an earlier answer), and
large enough that `2 ^ (nᵢ / 10) > nᵢ ^ i + i` — in particular the run below
cannot query all `2 ^ nᵢ` strings of length `nᵢ`. Run `N i` on input `1^nᵢ`
for exactly `nᵢ ^ i + i` steps with the partial oracle `Oᵢ` (the strings
declared in so far; every undetermined string answered "no").

*Flip.* If that run accepts — `(N i).ComputesInTime Oᵢ 1^nᵢ [true]
(nᵢ ^ i + i)` — declare every length-`nᵢ` string out of `B`, so
`1^nᵢ ∉ U_B`. Otherwise the run submitted at most `nᵢ ^ i + i` queries
(`Turing.OracleTM.queriesWithin_length_le`), each of length at most the budget
(`Turing.OracleTM.length_le_of_mem_queriesWithin`), so some length-`nᵢ` string
`x⋆` is unqueried (counting: `nᵢ ^ i + i < 2 ^ nᵢ` strings of length `nᵢ`);
declare `x⋆ ∈ B` and every other length-`nᵢ` string out, so `1^nᵢ ∈ U_B`.
In either case all lengths up to `max nᵢ (nᵢ ^ i + i)` become decided — the
`max` matters at small indices (`i = 0` has budget `1 < n₀`), where the flip
declares length-`nᵢ` strings that the budget alone would leave undecided.

*Consistency.* Let `B` be the union of the stage declarations. `B` agrees with
`Oᵢ` on every string stage `i`'s run queried: earlier declarations are
contained in `Oᵢ`; the flip inserts at most the *unqueried* `x⋆`; later stages
only insert strings longer than stage `i`'s budget, hence longer than every
stage-`i` query. By query-set locality
(`Turing.OracleTM.runFrom_eq_of_agree_queriesWithin`), the run of `N i` on
`1^nᵢ` under `B` coincides with the run under `Oᵢ` — the flipped verdict
survives to the completed oracle: for every `i`, `(N i).ComputesInTime B
1^nᵢ [true] (nᵢ ^ i + i)` holds iff `1^nᵢ ∉ U_B`.

*Conclusion.* `U_B ∈ NP^B` is `Complexity.unaryWitnessLang_mem_NPOracle`.
Suppose `U_B ∈ P^B`: some well-formed `M` decides it within `c · (n^k + 1)`.
The recurrence yields `i` with `N i` behaviorally equal to `M` and `i` so
large that `c · (nᵢ^k + 1) ≤ nᵢ ^ i + i` (the stages may also force `nᵢ ≥ i`,
absorbing the constants). `M`'s verdict on `1^nᵢ` at its clock transfers, by
monotonicity of `ComputesInTime` (halting is absorbing) and behavioral
equality, to `N i` at the budget `nᵢ ^ i + i` under `B` — contradicting the
flipped verdict in both cases (accept and reject). Fill obligations, named
for the brief: the stage recursion as a definition by strong recursion with
its monotonicity invariants (decided lengths grow, declarations are
preserved); the unqueried-string count (`Finset` cardinality of length-`nᵢ`
strings vs. the query list); the `DecidesInTime`-to-`ComputesInTime` verdict
extraction (indicator output plus `mono`); the final transfer along the
enumeration's behavioral equivalence. -/
theorem exists_oracle_ne :
    ∃ B : Language Bool,
      unaryWitnessLang B ∈ NPOracle B ∧ unaryWitnessLang B ∉ POracle B := by
  sorry

/-- **The Baker-Gill-Solovay theorem** [AB09, Theorem 3.7] ([BGS75]): there
are oracles `A`, `B` with `P^A = NP^A` and `P^B ≠ NP^B` — whether `P = NP`
does not relativize.

**Proof sketch.** `A := Complexity.EXPCOM` with
`Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM`; `B` from
`Complexity.exists_oracle_ne` — were `P^B = NP^B`, its `U_B ∈ NP^B` and
`U_B ∉ P^B` would collide. -/
theorem baker_gill_solovay :
    (∃ A : Language Bool, POracle A = NPOracle A) ∧
    ∃ B : Language Bool, POracle B ≠ NPOracle B := by
  sorry

end Complexity
