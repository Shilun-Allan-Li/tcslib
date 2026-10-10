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

## Main results (three phase-P3.2 statements remain sorried)

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

/-- R1: transport an oracle table along a state equivalence. The ordinary
transition uses `Action.mapState`; all distinguished states are transported.
The received relabelling API covers only plain machines, so this oracle
version is requested for `TuringMachine/Oracle.lean` when a second consumer
appears. -/
private def oracleRelabel {k : ℕ} {Symbol S S' : Type*}
    (tm : OracleTM k Symbol S) (e : S ≃ S') : OracleTM k Symbol S' where
  q₀ := e tm.q₀
  qQuery := e tm.qQuery
  qYes := e tm.qYes
  qNo := e tm.qNo
  tr q inp work := (tm.tr (e.symm q) inp work).mapState e

/-- R1: injectivity preserves the three required state inequalities. -/
private theorem oracleRelabel_wellFormed {k : ℕ} {Symbol S S' : Type*}
    (tm : OracleTM k Symbol S) (e : S ≃ S') (wf : tm.WellFormed) :
    (oracleRelabel tm e).WellFormed := by
  exact ⟨e.injective.ne wf.qQuery_ne_qYes,
    e.injective.ne wf.qQuery_ne_qNo, e.injective.ne wf.qYes_ne_qNo⟩

/-- R1: one oracle step commutes with state relabelling, including the
query-answer branch and absorbing halted configurations.

**Proof sketch.** Split the optional state. A halted configuration is fixed.
At the query state, injectivity identifies the same query branch; the query
string ignores the state, and mapping the answer commutes with its conditional.
Elsewhere the inverse equivalence recovers the original table row, and
`Cfg.mapState_apply` transports its action. This is the single step argument
used by all later run and behavior transfers. -/
private theorem oracleRelabel_step {k : ℕ} {Symbol S S' : Type*}
    {x : List Symbol} (tm : OracleTM k Symbol S) (e : S ≃ S')
    (O : Language Symbol) (cfg : Cfg (k + 1) Symbol S x) :
    (oracleRelabel tm e).step O (cfg.mapState e) = (tm.step O cfg).mapState e := by
  classical
  unfold OracleTM.step
  cases hs : cfg.state with
  | none => simp only [Cfg.mapState, hs, Option.map_none]
  | some q =>
      simp only [Cfg.mapState, hs, Option.map_some, oracleRelabel, e.injective.eq_iff]
      by_cases hq : q = tm.qQuery
      · rw [if_pos hq, if_pos hq]
        refine Cfg.ext ?_ rfl rfl rfl rfl
        change some (if OracleTM.queryString cfg ∈ O then e tm.qYes else e tm.qNo) =
          some (e (if OracleTM.queryString cfg ∈ O then tm.qYes else tm.qNo))
        rw [apply_ite e]
      · rw [if_neg hq, if_neg hq]
        simpa only [Equiv.symm_apply_apply] using
          Cfg.mapState_apply e (tm.tr q cfg.inputSymbol cfg.workTapeSymbols) cfg

/-- R1: arbitrary-start oracle runs commute with state relabelling, by the
standard iteration theorem applied to the single step commutation. -/
private theorem oracleRelabel_runFrom {k : ℕ} {Symbol S S' : Type*}
    {x : List Symbol} (tm : OracleTM k Symbol S) (e : S ≃ S')
    (O : Language Symbol) (cfg : Cfg (k + 1) Symbol S x) (t : ℕ) :
    (oracleRelabel tm e).runFrom O (cfg.mapState e) t =
      (tm.runFrom O cfg t).mapState e := by
  have h : Function.Semiconj (Cfg.mapState (input := x) e)
      (tm.step O) ((oracleRelabel tm e).step O) :=
    fun c => (oracleRelabel_step tm e O c).symm
  exact (h.iterate_right t cfg).symm

/-- R1: relabelling preserves every oracle-relative time-bounded output
verdict. Initialization transports definitionally; run transport preserves
output, and `Option.map_eq_none_iff` preserves haltedness. -/
private theorem oracleRelabel_computesInTime {k : ℕ} {Symbol S S' : Type*}
    (tm : OracleTM k Symbol S) (e : S ≃ S') (O : Language Symbol)
    (x out : List Symbol) (t : ℕ) :
    (oracleRelabel tm e).ComputesInTime O x out t ↔ tm.ComputesInTime O x out t := by
  have hinit : (oracleRelabel tm e).initCfg x = (tm.initCfg x).mapState e := rfl
  simp only [OracleTM.ComputesInTime, hinit, oracleRelabel_runFrom]
  simp only [Cfg.mapState, Option.map_eq_none_iff]

/-- R2: well-formed binary oracle tables over the canonical state type. -/
private abbrev CanonTab (k n : ℕ) :=
  {tm : OracleTM k Bool (Fin n) // tm.WellFormed}

set_option synthInstance.maxSize 1024 in
/-- R2: one named finiteness structure for canonical tables. All later ranks
and cardinalities use this structure explicitly to avoid instance diamonds.

**Proof sketch.** Inject the well-formed subtype into the tuple of its four
state fields and the transition table's four action fields. Each coordinate
is finite. Tuple injectivity, function extensionality and the two structure
constructor injectivity lemmas recover the original table. The oracle and
action layers do not yet supply this finiteness API; its requested shared
home is `TuringMachine/Oracle.lean` at a second consumer. -/
private noncomputable def canonTabFintype (k n : ℕ) : Fintype (CanonTab k n) := by
  let fields : OracleTM k Bool (Fin n) →
      Fin n × Fin n × Fin n × Fin n ×
        (Fin n → Option Bool → (Fin (k + 1) → Option Bool) →
          SignType × (Fin (k + 1) → Option (Option Bool) × SignType) ×
            Option Bool × Option (Fin n)) :=
    fun tm => ⟨tm.q₀, tm.qQuery, tm.qYes, tm.qNo, fun q inp work =>
      ⟨(tm.tr q inp work).inputTape, (tm.tr q inp work).workTapes,
        (tm.tr q inp work).output, (tm.tr q inp work).state⟩⟩
  refine Fintype.ofInjective (fun x : CanonTab k n => fields x.val) ?_
  intro a b hab
  apply Subtype.ext
  rcases a with ⟨⟨a₀, aQ, aY, aN, ta⟩, wa⟩
  rcases b with ⟨⟨b₀, bQ, bY, bN, tb⟩, wb⟩
  simp only [fields, Prod.mk.injEq] at hab
  rcases hab with ⟨h₀, hQ, hY, hN, ht⟩
  simp only [OracleTM.mk.injEq]
  refine ⟨h₀, hQ, hY, hN, ?_⟩
  funext q inp work
  have hrow := congrFun (congrFun (congrFun ht q) inp) work
  cases ha : ta q inp work
  cases hb : tb q inp work
  simpa only [ha, hb, Prod.mk.injEq, Action.mk.injEq] using hrow

/-- R3: the well-formed three-state fallback starts in the yes state and
halts on its first ordinary transition. No oracle-table default is supplied
by the construction layer; this explicit table totalizes invalid ranks. -/
private def oracleDefault : FinOracleTM Bool :=
  ⟨0, Fin 3, ⟨1, 0, 1, 2, fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩⟩,
    ⟨by decide, by decide, by decide⟩⟩

/-- R4: select a canonical table at an explicit rank, with the fixed
fallback for rank overflow. Keeping the three coordinates as arguments lets
the decoder simplify its pairing before opening the dependent rank branch. -/
private noncomputable def oracleTableAt (k n r : ℕ) : FinOracleTM Bool :=
  if h : r < @Fintype.card (CanonTab k n) (canonTabFintype k n) then
    let table := (@Fintype.equivFin (CanonTab k n) (canonTabFintype k n)).symm ⟨r, h⟩
    ⟨k, Fin n, table.val, table.property⟩
  else oracleDefault

/-- R4: decode the tape count, state count and rank using two pairings. -/
private noncomputable def decodeOracleTable (j : ℕ) : FinOracleTM Bool :=
  oracleTableAt (Nat.unpair j).1 (Nat.unpair (Nat.unpair j).2).1
    (Nat.unpair (Nat.unpair j).2).2

/-- R4: the code made from a canonical table's rank decodes to that table.

**Proof sketch.** Unpair the two coordinates. The rank's `Fin.isLt` proof
selects the valid branch without computing the cardinality. The inverse
law of the same explicitly instantiated equivalence recovers the table. -/
private theorem decodeOracleTable_rank (k n : ℕ) (table : CanonTab k n) :
    decodeOracleTable (Nat.pair k (Nat.pair n
      ((@Fintype.equivFin (CanonTab k n) (canonTabFintype k n)) table).val)) =
      (⟨k, Fin n, table.val, table.property⟩ : FinOracleTM Bool) := by
  simp only [decodeOracleTable, Nat.unpair_pair]
  rw [oracleTableAt, dif_pos ((@Fintype.equivFin (CanonTab k n) (canonTabFintype k n)) table).isLt]
  exact congrArg
    (fun a : CanonTab k n => (⟨k, Fin n, a.val, a.property⟩ : FinOracleTM Bool))
    ((@Fintype.equivFin (CanonTab k n) (canonTabFintype k n)).symm_apply_apply table)

/-- R5: forget the second coordinate, so every decoded table is repeated. -/
private noncomputable def oracleEnumeration (i : ℕ) : FinOracleTM Bool :=
  decodeOracleTable (Nat.unpair i).1

/-- R5: every repetition coordinate yields the same decoded table. -/
private theorem oracleEnumeration_pair (j r : ℕ) :
    oracleEnumeration (Nat.pair j r) = decodeOracleTable j := by
  simp only [oracleEnumeration, Nat.unpair_pair]

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
enumerates the well-formed ones; a pairing of `ℕ` with `ℕ × ℕ × ℕ × ℕ` —
tape count, state count, table rank, and an explicit **repetition
coordinate** (a bijective pairing alone has singleton fibers; the fourth
coordinate supplies the recurrence and the unbounded clock exponents —
round-1 finding 2) — produces the family, totalized by a fixed well-formed
**three-state** default at indices whose rank overflows (well-formedness
demands three pairwise-distinct special states, so no one-state machine
qualifies — round-1 finding 2; equivalently, embed a one-state plain
machine by `Turing.FinTM.toFinOracleTM`, which adjoins them).
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
four-coordinate pairing (round-2 finding 2).

**C1d proof-sketch appendix.** Canonical tables are indexed by every state
count `n`, including the empty table types at small counts; invalid ranks
use the three-state fallback. `oracleTableAt` exposes the three coordinates
before the dependent rank branch is opened. Every table rank and cardinality
uses the one named finiteness structure. Runs follow from the single step
transport by `Function.Semiconj.iterate_right`; `Nat.right_le_pair` gives
the recurrence bound directly. -/
theorem exists_finOracleTM_enumeration :
    ∃ N : ℕ → FinOracleTM Bool,
      ∀ (M : FinOracleTM Bool) (i₀ : ℕ),
        ∃ i, i₀ ≤ i ∧
          ∀ (O : Language Bool) (x output : List Bool) (t : ℕ),
            ((N i).ComputesInTime O x output t ↔ M.ComputesInTime O x output t) := by
  refine ⟨oracleEnumeration, ?_⟩
  intro M i₀
  rcases M with @⟨k, Q, hQ, dQ, tm, wf⟩
  letI : Fintype Q := hQ
  letI : DecidableEq Q := dQ
  let e := Fintype.equivFin Q
  let table : CanonTab k (Fintype.card Q) :=
    ⟨oracleRelabel tm e, oracleRelabel_wellFormed tm e wf⟩
  let j := Nat.pair k (Nat.pair (Fintype.card Q)
    ((@Fintype.equivFin (CanonTab k (Fintype.card Q))
      (canonTabFintype k (Fintype.card Q))) table).val)
  refine ⟨Nat.pair j i₀, Nat.right_le_pair j i₀, ?_⟩
  intro O x output t
  have htable : decodeOracleTable j =
      (⟨k, Fin (Fintype.card Q), table.val, table.property⟩ : FinOracleTM Bool) :=
    decodeOracleTable_rank k (Fintype.card Q) table
  rw [oracleEnumeration_pair, htable]
  exact oracleRelabel_computesInTime tm e O x output t

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
