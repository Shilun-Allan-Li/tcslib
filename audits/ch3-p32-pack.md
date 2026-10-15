# External audit pack — Chapter 3, phase P3.2 (relativization), statement gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase P3.2 —
the Baker-Gill-Solovay relativization theorem and its supporting cast. Statement
phase per `workflow.md` §2-3: definitions plus sorried statements with
policy-grade sketches; the gate closes on a round with zero blockers and zero
majors.

Audited at commit `7fbac9bd` (branch `complexity/arora-barak-ch3-4`). Under
audit: five new files — `TCSlib/Complexity/TuringMachine/OracleAgreement.lean`
and `TCSlib/Complexity/Diagonalization/{EXPCOM,Relativization,NotTimeConstructible}.lean`
plus the `Diagonalization.lean` facade. **17 sorried statements, 4 definitions.**

**Layering caveat, stated plainly**: this phase builds on the phase-P3.1 oracle
surface (`TuringMachine/{OracleFinite,OracleNondeterministic}.lean`,
`ClassOracle/{Classes,SATOracle}.lean`, attached verbatim), whose own statement
gate has **not yet run** — it is scheduled after the P0 reception gate closes.
Audit P3.2's statements against that surface as given; findings against the
P3.1 definitions themselves are welcome and will be filed to the P3.1 round,
labeled as such — they do not block this gate unless they falsify a P3.2
statement.

## Brief for the auditor

Statements and definitions only; the failure modes of `audits/TEMPLATE.md`
(infidelity, trivialization, unprovability-as-stated, missing hypotheses), plus
this phase's own: **a diagonalization statement whose quantifiers let the
adversary move after the diagonal is fixed**. For every definition: blind
restatement, then compare against the sources. For every sorried statement:
argue true-as-stated or exhibit the problem. At least **5 adversarial
instantiations**. No blanket approvals.

Sources: [AB09] §3.4 (pp. 72-75: Definition 3.4-3.5, Example 3.6, Theorem 3.7),
Chapter-3 Exercise 3.5; and [BGS75] Baker-Gill-Solovay, *Relativizations of the
P =? NP question*, SIAM J. Comput. 4(4), 1975 — scanned original at
https://cse.ucdenver.edu/~cscialtman/complexity/Relativizations%20of%20the%20P=NP%20Question%20(Original).pdf
(pp. 431-434: the query-machine model, the **all-oracle polynomial-clock
convention** for the enumerated machines `P_i`/`NP_i` on p. 432, Lemma 1 and
Theorems 1-2; §3: the stage construction). The campaign's route decision
(CH34-Q4, plan §2.3): the `A` half goes through `EXPCOM` ([AB09, Example
3.6(3)]); [BGS75, Theorem 1]'s self-referential oracle is the recorded fallback,
not under audit.

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch3-p32-sweep.log`, revision recorded at
  start): all five modules, 0 `error:` lines, fresh `.olean`s, exactly **17**
  `declaration uses 'sorry'` warnings (OracleAgreement 7, EXPCOM 5,
  Relativization 4, NotTimeConstructible 1).
* Style lint (`audits/logs/ch34-skeletons-stylelint.log`): `Diagonalization`
  0 FAIL / 0 WARN; `TuringMachine` 0 FAIL with only the pre-existing size
  WARNs.
* `sorry` tokens: 17, all in the files under audit; no `axiom`.
* Statement-freeze baseline: commit `7fbac9bd`.
* The P3.1 surface and every other file this phase imports are untouched by it
  (the five files are purely additive; checkable in the attached diff-free
  context files).
* Drafting provenance: drafted by a maintainer-directed agent, then reviewed
  line by line by the maintainer. Review repairs already applied: the stage
  construction sketch's decided-length bound corrected to `max nᵢ (nᵢ^i + i)`
  (the `i = 0` budget `1 < n₀` edge). Every existing lemma name cited in a
  sketch was verified to resolve in the codebase.

## Known deviations and design decisions (declared — verify each, flag others)

1. **`EXPCOM` encoding**: code-first nesting
   `pairEncode α (pairEncode x 1ⁿ)` (the book states no layout); the campaign's
   fixed scheme `Complexity.TimeHierarchy.code`, reused not re-chosen;
   "outputs `1` within `2ⁿ` steps" as `ComputesInTime x [true] (2 ^ n)`
   (monotone, halting absorbing); totalization by failure of the defining
   existential on non-parsing strings, uniqueness on genuine triples claimed
   from `pairEncode_injective` + `pairEncode_replicate_inj`.
2. **The enumeration is clock-free and deterministic-only**
   (`exists_finOracleTM_enumeration`): no `DecidesInTime` anywhere — [BGS75,
   p. 432] clocks its machines under *every* oracle, which the campaign's
   per-oracle `DecidesInTime` cannot express, so the budget `n^i + i` is
   attached to the index extrinsically in the stage construction. Behavioral
   equality is rendered as `ComputesInTime`-verdict equivalence at every
   oracle, input, output, and horizon (literal run equality is not typable
   across state types). Only `FinOracleTM` (deterministic) is enumerated — the
   diagonal runs against the would-be `P^B` deciders; no universal oracle
   machine is used anywhere.
3. **Stage-construction packaging**: `exists_oracle_ne` states the conjunction
   `U_B ∈ NP^B ∧ U_B ∉ P^B` (the first conjunct holds for every `B`; the
   packaging matches the book). The sketch strengthens "pick `n` larger than
   all previous" to "larger than all decided lengths *and all earlier
   budgets*", uses `2^(n/10) > n^i + i` as the mandated margin plus
   `n^i + i < 2^n` for the counting, and takes the accept-verdict to be
   `ComputesInTime Oᵢ 1^nᵢ [true] (nᵢ^i + i)` — non-halting-in-budget and
   wrong-output both count as reject, and the flip is stated against exactly
   that predicate.
4. **The locality layer** (`OracleAgreement.lean`): `queriesWithin` is a
   *list* (step order, multiplicity) over indices `s < t` whose configuration
   sits in `qQuery` — the query submitted by the step `s → s + 1`, so a
   `t`-step run's queries are exactly these; the query-set agreement lemma is
   deliberately asymmetric (queries computed along the *first* oracle's run —
   the shape the stage consumes); the ND variant runs along a fixed choice
   word with horizon `w.length`.
5. **Ex 3.5 non-trivialization**: `TimeConstructible` already bundles
   `∀ n, n ≤ T n`, so the statement demands a witness *dominating the
   identity* (`∃ T, (∀ n, n ≤ T n) ∧ ¬TimeConstructible T`); the sketch's
   witness oscillates by a `HALT` bit and refutes using only the
   constructibility witness's computability (no clock).
6. **Natural-home displacements, flagged for promotion at the P3.1 gate
   close** (statement-freeze discipline: the P3.1 files are not edited):
   the ND run invariant behind `length_le_of_mem_queriesAlong` (det twin is
   `private` in `Oracle.lean`); the `stepWith` oracle-independence analogue;
   oracle state-relabelling (`StateRenaming` transport); the four-state
   query-answer tail (shared with `mem_POracle_of_polyTimeReducible`,
   flagged as a §12 catalog candidate).
7. **Import posture**: `Relativization.lean` imports `OracleAgreement`, and
   `NotTimeConstructible.lean` imports `TimeHierarchy/Diagonal`, for
   sketch-level dependencies not appearing in statements (the `SATOracle` →
   `CookLevin` precedent).

## Specific questions (prioritized)

1. **Is the enumeration's behavioral equivalence strong enough — and not too
   strong?** The final transfer needs: `M` decides `U_B` within `c·(n^k + 1)`
   ⟹ for the recurrence index `i`, `N i`'s verdict at budget `nᵢ^i + i` under
   `B` matches `M`'s. Check this follows from verdict equivalence at all
   `(O, x, output, t)` plus `ComputesInTime` monotonicity — and check the
   equivalence is itself deliverable by state relabelling (in particular that
   enumerating only *well-formed* machines over `Fin (m+1)` state spaces
   reaches every `FinOracleTM Bool` up to it).
2. **Does the stage construction's statement+sketch survive your own
   reconstruction?** Specifically: the consistency argument under the
   corrected `max nᵢ (budget)` decided-length bookkeeping; whether the
   accept-case flip ("declare every length-`nᵢ` string out") is compatible
   with *earlier* stages' insertions; and whether `Oᵢ` (partial oracle,
   undetermined = no) matching `B` on `queriesWithin` is exactly what
   `runFrom_eq_of_agree_queriesWithin` needs, given its asymmetry.
3. **The `EXPCOM` definitional shape** (deviation 1): blind-restate it; check
   the uniqueness claim actually holds at the stated lemmas (is
   `pairEncode_replicate_inj` the right fact for the `1ⁿ` component?); check
   `2 ^ n` as an inclusive budget is faithful to "within `2ⁿ` steps"; and
   check nothing in the definition smuggles decidability it shouldn't have.
4. **The summit's feasibility as stated** (`NPOracle_EXPCOM_subset_EXP`): the
   sketch compounds the chapter-2 enumerator, a per-step `runWith` simulation,
   query parsing, and `timed_universal` at deadline `2^(n')` under a
   `2^(O(p n))` ledger. Is the *statement* (class inclusion) in the right
   form, and does the sketch's budget arithmetic (`n' ≤ p n` via
   `queryString_length_le`) hold at the boundary where a query is submitted at
   the very last step?
5. **The locality statements** (deviation 4): is the `s < t` indexing of
   `queriesWithin` exactly the set of oracle consultations of a `t`-step run
   (no off-by-one at either end)? Is the ND horizon convention (`w.length`,
   prefixes via `w.take`) consistent with `runWith`'s one-bit-per-step
   consumption at query steps (which consume-and-ignore)?
6. **Ex 3.5** (deviation 5): is identity-domination the right
   non-trivialization, or should the statement demand more (e.g.
   monotonicity)? Does the HALT-bit sketch's refutation really avoid needing
   the clock, given `TimeConstructible`'s witness computes `(T |x|).bits` on
   *every* input?
7. **`unaryWitnessLang_mem_NPOracle`**: the guess-writer's budget is linear
   and the choice word *is* the witness — check the statement's class-level
   form (`NPOracle`'s `c·(n^c + 1)` normal form) absorbs the construction,
   and that non-unary inputs are genuinely rejected on every branch by the
   stated language shape.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide: **blocker** = the fill campaign or a later phase would build on
a wrong statement; **major** = materially misleading but fixable; **minor** =
edge case or naming/attribution defect; **note** = observation. P3.1-surface
findings: same table, prefixed "[P3.1]". Findings go verbatim into
`audits/ch3-p32-findings.md`; the gate closes on zero blockers and majors.
