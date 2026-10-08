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


# ===== ATTACHMENTS =====


## ===== AroraBarakChapters3-4Plan.md =====

```
# Formalization Plan: Arora-Barak Chapters 3-4 — Diagonalization and Space Complexity

**Status: draft for maintainer review (2026-10-08).** Nothing below is decided until the
open questions in §7 are answered; the decision log (§8) records every row as *Proposed*.

Continuation of the Arora-Barak campaign (`AroraBarakChapter1Plan.md`,
`AroraBarakChapter2Plan.md`, both closed), now working from `main`: branch
`complexity/arora-barak-ch3-4`, created from `origin/main` at `99b187fc`. The methodology
is unchanged (`workflow.md`): audited statement phases with proof sketches,
cross-vendor LLM audit gates closing on zero blockers/majors, then fill epochs of
disjoint-ownership batches with zip delivery, drift attestations, and a blueprint
increment at closure. Artifact names: `audits/ch3-*`, `audits/ch4-*`, `briefs/ch3-*`,
`briefs/ch4-*`.

**What changed since Chapter 2.** Much of this plan's raw material already exists on
`main`, written by Hydroxyi (commit `f70c57c2`, 2026-10-06, sorry-free) — notably a time
hierarchy theorem, `P ⊊ EXP`, `SPACE`/`LOGSPACE`, implicitly logspace functions,
`LOGSPACE ⊆ P`, and a logspace register-machine compiler. The plan therefore starts with
a *reception* phase (§4, P0) that brings that surface under the campaign's audit, and
builds Chapter 4 on Hydroxyi's program layers rather than on hand-built machines.

## 1. Scope

Sources: [AB09] ch. 3, pp. 68-77; ch. 4, pp. 78-94. "Exists" means proved on `main`
today; tiers are **core** (this campaign), **core-late** (this campaign, last, and the
first candidates to descope), **deferred** (backlog).

### Chapter 3 — Diagonalization

| Item | Status on `main` | Tier |
|---|---|---|
| Machines as strings: every string is a code, every machine has infinitely many codes (§3 intro) | Exists (ch-1 `Encoding`, padding lemmas) | — |
| **Thm 3.1** time hierarchy | Exists at **`f²` strength**: `Complexity.time_hierarchy` (`A·(f n + n + 1)² ≤ g n` eventually ⇒ `DTIME f ⊂ DTIME (g + 1)`), `time_hierarchy_of_pos`, `P_ssubset_EXP` (`TimeHierarchy/`) | Received in P0; **strengthened to book form via Hennie-Stearns** (user decision 2026-10-08, §2.1) |
| Def 3.4 oracle TMs | Raw model exists: `Turing.OracleTM`, `WellFormed`, lockstep embeddings (`TuringMachine/Oracle.lean`, audited ch-1) | Core: bundle + oracle NDTM (P3.1) |
| Def 3.5 `Pᴼ`, `NPᴼ` | Missing | Core (P3.1) |
| Ex 3.6(1) `co-SAT ∈ P^SAT`; (2) `O ∈ P ⇒ Pᴼ = P` | Missing | Core (P3.1) |
| Ex 3.6(3) `P^EXPCOM = NP^EXPCOM = EXP` | Missing | **Core** (user decision 2026-10-08, CH34-Q4; P3.2) |
| **Thm 3.7** Baker-Gill-Solovay | Missing | Core (P3.2) |
| Ex 3.5 a non-time-constructible function | Missing | Core (P3.2, cheap) |
| **Thm 3.2** nondeterministic time hierarchy (lazy diagonalization), with Ex 2.6 universal NDTM | Missing (no NDTM codes, no universal NDTM) | **Core, mandatory, book strength** — linear-overhead universal NDTM (user decisions 2026-10-08; P3.3, CH34-Q8) |
| **Thm 3.3** Ladner, its Claim, and Ex 3.6(a)(b) | Missing | Core-late (P3.4) |
| Ex 3.1, 3.3, 3.4, 3.7-3.9; relativized hierarchy statements; Remark 3.8 and §3.4.1 (expository) | — | Deferred |

### Chapter 4 — Space complexity

| Item | Status on `main` | Tier |
|---|---|---|
| Def 4.1 `SPACE` | Exists: `Complexity.SPACE` (deterministic, halting, visited work cells, `c · s n`) | Received in P0 |
| Def 4.1 `NSPACE`; space-constructibility | Missing (no NDTM space measure at all) | Core (P4.1) |
| Thm 4.2 (i) `DTIME ⊆ SPACE`, (ii) `SPACE ⊆ NSPACE` | Missing | Core (P4.1) |
| Thm 4.2 (iii) `NSPACE(S) ⊆ DTIME(2^O(S))` | Deterministic core exists (`ComputesInTime.of_spaceUsed_le`, `configBound`); nondeterministic search missing | Core (P4.2) |
| Claim 4.4 (1) configuration count; (2) `O(S)`-size adjacency CNF | (1) deterministic only (`configBound`); (2) missing | Core (P4.2 / P4.3) |
| Def 4.5 `PSPACE`, `NPSPACE`, `L`, `NL` | `L` exists as `LOGSPACE` (`logSpace n = ⌊log₂ n⌋ + 1`); rest missing | Core (P4.1) |
| Ex 4.6 `3SAT ∈ PSPACE`, `NP ⊆ PSPACE` | Missing | Core (P4.1) |
| Ex 4.7 `EVEN`, `MULT ∈ L`; `PATH ∈ NL` | `dblLang ∈ LOGSPACE` exists as an ARM example | Core (P4.1 / P4.4) |
| **Thm 4.8** space hierarchy, with Ex 4.1 space-universal TM | Missing (both universal machines are time-only) | Core (P4.3) |
| Def 4.9 `PSPACE`-hard/complete; Def 4.10 QBF; `TQBF`; **Thm 4.13** | Missing (no QBF anywhere; `PolyHierarchy/` quantifies over strings, not formulas) | Core (P4.3) |
| **Thm 4.14** Savitch; `PSPACE = NPSPACE` | Missing | Core (P4.2) |
| Def 4.16 implicit logspace computability | Exists: `ImplicitlyLogspaceComputable` | Received in P0 |
| `≤ₗ`, `NL`-completeness; **Lemma 4.17** | Missing; a special case exists (`UnaryLogspace.counterProg`) | Core (P4.4) |
| **Thm 4.18** `PATH` is `NL`-complete | Missing (no `PATH` language or graph encoding) | Core (P4.4) |
| **Thm 4.20** Immerman-Szelepcsényi; **Cor 4.21** | Missing | Core (P4.4) |
| `L ⊆ NL ⊆ P`, `L ⊊ PSPACE` (the chain on p. 92) | `LOGSPACE ⊆ P` exists | Core (assembled in P4.2-P4.3) |
| Ex 3.2, **stated as `SPACE(n+1) ≠ NP`** (the literal `SPACE(n)` collapses to the zero-work-tape class — P0 round 1, finding 1) | Missing | Core (P4.3, cheap once Thm 4.8 exists) |
| Ex 4.3 (every nontrivial language is `NL`-complete under `≤ₚ`), Ex 4.10 (finite-game determinacy) | Missing | Core, cheap (P4.2 / P4.3) |
| Def 4.19 read-once certificates; Ex 4.7 | Missing | Deferred: Thm 4.20 can be proved directly on NDTMs |
| Example 4.15 (QBF game); Ex 4.2, 4.4-4.6, 4.8, 4.9, 4.12 | — | Deferred |

## 2. Foundation decisions (proposed; each is seeded to the relevant audit)

### 2.1 Thm 3.1 is received at `f²` strength, then strengthened to book form

Hydroxyi's theorem consumes the linear-time `Turing.universal` over one-work-tape codes,
so converting an arbitrary machine to that normal form costs a square. The book's
`f log f` needs the Hennie-Stearns `O(T log T)` simulation ([AB09] §1.7), which the
Chapter-1 plan deferred as phase 5. The received form still yields `P ⊊ EXP`, but **not**
the book's illustrative `DTIME(n) ⊊ DTIME(n^1.5)`, since `n²` exceeds `n^1.5`.

**Decision (user, 2026-10-08, CH34-Q3): strengthen.** Before the chapter-3/4 fill
epochs, the campaign builds (a) the Hennie-Stearns `k`-work-tapes-to-2 conversion at
`C·T log T` ([AB09] §1.7: parallel tracks, buffer zones of size `2^i`, amortized
shifts), and (b) a universal machine over *two-work-tape* codes at linear overhead.
Hydroxyi's diagonal argument then re-derives Thm 3.1 at `f log f`, and Theorem 1.9
reaches book strength, closing chapter 1's deferred phase 5. Until that lands, the
received form is documented as delivered strength, never as Thm 3.1 verbatim. Both
constructions are consumers of the machine-routine layer (§4a).

### 2.2 Oracle classes

- **A finite bundle `FinOracleTM`** carrying `Fintype`/`DecidableEq` for states, with
  `WellFormed` as a field. This is the Chapter-1 phase-1 obligation: "oracle complexity
  classes will introduce a finite oracle-machine bundle".
- **An oracle NDTM** combining the binary-choice NDTM with the oracle step. Def 3.4 says
  only that nondeterministic oracle machines are "defined similarly".
- **`Pᴼ` and `NPᴼ` mirror `P` and `NTIME`** literally: the same `c · T n` and
  `n^c + 1` normal forms, with all-branch halting for `NPᴼ`.
- **Query tape:** the existing persistent convention (no auto-erase). The Chapter-1
  obligation to prove polynomial equivalence with the auto-erased convention is scheduled
  only if some consumer imports an invariance; none in this plan does.
- **One general lemma does most of the light work:** `L ≤ₚ O ⇒ L ∈ Pᴼ`. It writes `f(x)`
  on the query tape, queries, and copies the answer. Ex 3.6(1), the `A` half of Thm 3.7,
  and `NP ⊆ P^SAT` all follow from it.

### 2.3 Baker-Gill-Solovay

- **The `B` half follows the book.** `U_B ∈ NP^B` is a small oracle-NDTM construction.
  `U_B ∉ P^B` is the stage construction. It is mathematics, not machine-building: runs
  that agree on every queried string agree (by lockstep); a run of `t` steps queries at
  most `t` strings, each of length at most `t` (`queryString_length_le` exists); and
  `FinOracleTM`s can be enumerated with every machine recurring infinitely often, through
  `Fintype.equivFin` plus state relabelling, with no universal oracle machine needed.
- **The `A` half takes the book's route: `A = EXPCOM`** (user decision 2026-10-08,
  CH34-Q4 — preferred as the more natural oracle, with `P^EXPCOM = NP^EXPCOM = EXP` the
  memorable byproduct), via the chain `EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP` (Ex 3.6(3)).
  - `EXP ⊆ P^EXPCOM`: the reduction `x ↦ ⟨M_L, x, 1^(n+1)^c⟩` (constant prefix, copy,
    unary padding emitter — chapter-2 padding-cluster precedents), then one query
    through the §2.2 lemma.
  - `NP^EXPCOM ⊆ EXP` is **a fill summit**: for each language, a deterministic
    exponential-time machine that enumerates all choice words of the fixed oracle NDTM
    (the `NP_subset_EXP` enumerator pattern), simulates it step by step under each word
    (2B-style invariant), and answers each query `⟨M', x', 1^(n')⟩` by parsing it
    (CodeParser) and running the timed universal machine for `2^(n')` steps (the
    `timed_universal` bridge), under a `2^O(p(n))` ledger. Continuation budget certain.
  - The machine-light alternative — [BGS75, Thm 1]'s own self-referential
    `A = K(A) = {⟨i, x, 0ⁿ⟩ : NPᵢᴬ accepts x in < n steps}`, well-founded because a
    `< n`-step run queries only shorter strings — is **recorded as the fallback**: if
    the summit stalls, switching requires only the oracle-locality lemma (needed for
    the `B` half anyway) plus a maintainer sign-off, and the blueprint would cite
    [BGS75, Thm 1] with a deviation note.

### 2.4 Space

- **Reuse `SPACE` and `LOGSPACE` unchanged**: deterministic, halting, counting visited
  work cells summed over the work tapes, with input and output excluded. [AB09] is itself
  inconsistent here: Def 4.1 counts *visited* cells for `SPACE` but *non-blank* cells for
  `NSPACE`. The vendored `Deterministic.lean` docstring and `SpaceComplexity/Basic.lean`
  currently disagree about what [AB09] says. P0 fixes the documentation, and the visited
  measure is used for both classes.
- **`NSPACE` (CH34-Q7, provisional answer: all branches halt).** It needs a new NDTM space
  measure along `runWith`, adapting the `visitedByTapeHead` pattern to choice words.
  Provisionally, `N` decides `L` in space `s` if on every input there is some `T` with
  `HaltsWithin x T`, every choice word stays within `s(|x|)` cells, and `x ∈ L` iff some
  choice word accepts. All-branch halting matches `NTIME`, lax-434930's convention and
  Remark 4.3's alternative, and it makes the configuration-count arguments direct.
- **Space-constructibility mirrors `TimeConstructible`.** A machine writes
  `(S |x|).bits` within space `c · (S |x|)`, and the definition carries
  `∀ n, logSpace n ≤ S n`, which is [AB09]'s standing `S(n) > log n` (p. 79).
  Theorems needing only weaker hypotheses say so. This is seeded to the P4.1 audit.
- **The classes:** `PSPACE := ⋃ c, SPACE (n^c + 1)`, and likewise `NPSPACE`;
  `NL := NSPACE logSpace`; `coNL` in complement form, like `coNP`.
- **Positive bounds everywhere (P0 round 1, finding 1).** Unnormalized `SPACE s`
  collapses to the zero-work-tape class as soon as `s` has one zero (every machine has
  `k ≤ spaceUsed`), so **every asymptotic chapter statement uses an everywhere-positive
  bound** (`n + 1`, `n^c + 1`, `logSpace`) — never a literal `fun n => n`. The collapse
  and the harmless-normalization identities are machine-checked in
  `SpaceComplexity/ZeroSpace.lean` (sanity targets S1-S4); the same applies verbatim to
  `NSPACE` (branch space also dominates the tape count).
- **`≤ₗ` reuses `ImplicitlyLogspaceComputable`** (Def 4.16, with its documented
  divergences: `C(|x|+1)^c` length bound and 0-based index).

### 2.5 Machine substrate for Chapter 4: program layers, not hand-built machines

Chapter 2's lesson, and the backlog's machine-routine-layer entry, is that hand-built
machines dominate the cost. For space the relevant layers already exist on `main`:

- **`LogProg.ARM`** (`SpaceComplexity/Machines/`) is an abstract register machine with
  `O(log n)`-bit registers and calls to `LOGSPACE` deciders. It compiles to `FinTM` with a
  space theorem (`compile_space`, `arm_decides`, `arm_decides_poly`). It is
  **deterministic only**.
- **`CounterProg`** (`TuringMachine/CounterProg{,Run}.lean`) has unary registers and
  forward input reading. It compiles with a time bound (`t` steps become at most
  `t(2t+3)`), so it suits the `2^O(S)`-time searches, where register values of size
  `2^O(S)` are affordable. Its input is one-way (`rd` only advances), but a configuration
  successor must read the input at the simulated head. Those searches therefore need
  either ARM-style indexed input access or a rewind instruction.

Proposed extensions, each a P4.x infrastructure statement with its own audit:

1. **A nondeterministic ARM**: a `choose` instruction compiling to `FinNDTM`, with the
   space theorem carried over. This serves `PATH ∈ NL`, Immerman-Szelepcsényi and
   Cor 4.21.
2. **A polynomial-width ARM variant** with registers of `poly(n)` bits, for the
   `PSPACE`-level algorithms: `TQBF ∈ PSPACE`, `NP ⊆ PSPACE`, Savitch at polynomial
   level. It is either a generalization of `compile_space` or a sibling.
3. **A configuration codec**, shared by Thm 4.2(iii), Savitch, Thm 4.18, Cor 4.21 and
   `TQBF` hardness. It encodes the configurations of a fixed machine, with work tapes
   windowed to `s` cells and the input head as a separate register, as `O(s)`-bit
   register contents, and provides a successor/adjacency test as a program. The counting
   half adapts cslib's new upstream `MultiTape/ConfigBound.lean` design (Sept 2026,
   `Storage`/`Cfg.core`) and extends Hydroxyi's deterministic `ConfigCount` to NDTMs.
   It must be cited and adapted, not vendored: cslib targets a newer Lean with the
   module system.

This requires Hydroxyi's agreement, since these are their modules (CH34-Q2).

### 2.6 Formulas and graphs

- **The QBF matrix (CH34-Q5).** Def 4.10 allows a general unquantified matrix; we have
  only `Std.Sat.CNF ℕ` and the DNF dual. Provisional choice: prenex QBF with a **CNF
  matrix**, reusing the CNF carrier, serialization and parser. [AB09] notes on p. 83 that
  the CNF restriction is harmless via auxiliary variables, so `TQBF` hardness pays a
  Tseitin step. A general-formula carrier is the alternative, which Chapter 5 and a
  general `TAUTOLOGY` would also want.
- **`PATH` needs the campaign's first graph encoding**: an adjacency-matrix
  serialization plus `s`, `t` in binary via `pairEncode`, with a parser and the
  `codeFallback`-style totalization. It stays in-house in `Complexity/`, with
  `GraphTheory.Digraph.Reachable` as the semantic target.

### 2.7 Universal machines

- **Thm 4.8 needs a space-efficient universal machine (Ex 4.1).** The existing `universal`
  and `timed_universal` are time-only, and their code scheme covers only the
  one-work-tape binary normal form. So either the Chapter-1 robustness conversions
  (`one_work_tape`, alphabet reduction) gain space theorems, or a fresh space-universal
  machine takes multi-tape codes. This is the largest single risk in Chapter 4 (§6).
- **Thm 3.2 needs NDTM codes and a clocked universal NDTM (Ex 2.6), at linear
  overhead** (user decision 2026-10-08, CH34-Q8). Polynomial overhead would deliver only
  `f(n+1)^c = o(g(n))`; linear overhead gives the book's `f(n+1) = o(g(n))`. The
  guess-then-verify technique (guess the whole tableau of choice/configuration data,
  then check each tape's consistency in one pass — Book-Greibach style) achieves a
  code-dependent constant factor, which is the strongest form possible: a simulation of
  `t` steps cannot run faster than the `t` steps it reproduces, and the code-dependent
  constant is necessary for the same reason as chapter 1's Argument E. Another
  routine-layer consumer.

## 3. Architecture and module layout

New campaign directories (namespace `Complexity`, facades per policy §1):

| Directory | Contents |
|---|---|
| `TuringMachine/OracleFinite.lean`, `TuringMachine/OracleNondeterministic.lean` | `FinOracleTM`, oracle NDTM, runs, and lockstep embeddings of plain machines |
| `ClassOracle/` | `Pᴼ`, `NPᴼ`, the `≤ₚ ⇒ Pᴼ` lemma, Ex 3.6, oracle-machine enumeration, `Relativization.lean` (Thm 3.7) |
| `Diagonalization/` | `NTimeHierarchy.lean` (Thm 3.2), `Ladner.lean` (Thm 3.3), `NotTimeConstructible.lean` (Ex 3.5) |
| `TuringMachine/NondeterministicSpace.lean`, `TuringMachine/NDCodes.lean` | NDTM space measure; NDTM codes and the universal NDTM |
| `SpaceComplexity/` (extending Hydroxyi's tree, subject to CH34-Q2) | `NSPACE.lean`, `Classes.lean` (`PSPACE`/`NPSPACE`/`NL`/`coNL`), `Constructible.lean`, `Inclusions.lean` (Thm 4.2), `ConfigGraph.lean`, `Savitch.lean`, `Hierarchy.lean`, `Logspace/{Reductions,Path,ImmermanSzelepcsenyi}.lean` |
| `Formulas/QBF.lean`, `Formulas/QBFEncoding.lean`; `ClassPSPACE/TQBF.lean` | the QBF carrier and serialization; Thm 4.13 |

Chapter-1/2 files stay frozen at their audited surface. Additions to Hydroxyi's trees
follow whatever ownership rule CH34-Q2 sets.

## 4. Phasing

Statement phases, each gated by an audit before the next one lands. The order reflects
infrastructure dependencies and retires risk early: the light half of Chapter 3, then
Chapter 4, then Chapter 3's two heavy diagonalizations.

| Phase | Contents | New sorried statements (est.) |
|---|---|---|
| **P0 — Reception** | Statements-only audit of the existing surface the campaign will build on: `time_hierarchy`, `P_ssubset_EXP`, `SPACE`, `LOGSPACE`, `ImplicitlyLogspaceComputable`, `LOGSPACE_subset_P`, `ComputesInTime.of_spaceUsed_le`, and the `arm_decides` and `compile_space` contracts. Docstring fixes (the §2.4 inconsistency; the stale "spec phase, sorried" notes in `Build/*`). Drift baseline recorded. No new sorries. | 0 |
| **P3.1 — Oracle classes** | `FinOracleTM`, the oracle NDTM, `Pᴼ`, `NPᴼ`; `P ⊆ Pᴼ`, `NPᴼ` contains `Pᴼ`; the `≤ₚ ⇒ Pᴼ` lemma; Ex 3.6(1)(2); `NP ⊆ P^SAT` as a sanity theorem | ~10 |
| **P3.2 — Relativization** | Oracle-machine enumeration; `U_B ∈ NP^B`; the stage construction; the EXPCOM cluster (`EXPCOM`, `EXP ⊆ P^EXPCOM`, `NP^EXPCOM ⊆ EXP`, `P^EXPCOM = NP^EXPCOM = EXP` — Ex 3.6(3)); Thm 3.7; Ex 3.5 | ~11 |
| **P4.1 — Space classes** | NDTM space measure, `NSPACE`, space-constructibility, the classes; Thm 4.2(i)(ii); `L ⊆ NL`; `3SAT ∈ PSPACE`, `NP ⊆ PSPACE`; `EVEN`, `MULT ∈ L`; the nondeterministic and polynomial-width ARM interfaces | ~14 |
| **P4.2 — Configuration graphs** | The configuration codec; Claim 4.4(1) for NDTMs; Thm 4.2(iii); Savitch; `PSPACE = NPSPACE`; `NL ⊆ P`; Ex 4.3 | ~10 |
| **P4.3 — `PSPACE`-completeness and space hierarchy** | Def 4.9; the QBF carrier, `TQBF`, Claim 4.4(2), Thm 4.13 (both halves); the space-universal machine (Ex 4.1); Thm 4.8; `L ⊊ PSPACE`; Ex 3.2; Ex 4.10 | ~12 |
| **P4.4 — Logspace and `NL`** | `≤ₗ`, `NL`-completeness, Lemma 4.17; the graph encoding, `PATH ∈ NL`, Thm 4.18; Thm 4.20; Cor 4.21 | ~10 |
| **P3.3 — Nondeterministic hierarchy** | NDTM codes, the clocked universal NDTM (Ex 2.6), Thm 3.2 at delivered strength | ~6 |
| **P3.4 — Ladner** | `SAT_H`; Ex 3.6(a) (`H` in polynomial time); the Claim; Ex 3.6(b); Thm 3.3 | ~6 |

That is roughly 78 new audited statements, against Chapter 2's 59.

### 4a. Pre-campaign infrastructure (user decisions 2026-10-08)

The machine-routine layer and its two headline consumers run **in parallel with the
statement phases**, and gate only the fill epochs:

1. **The routine layer** (`machine-library-design.md` §12, to be written): bank
   embedding, seam composition, catalog promotion — **scoped to amply support the
   chapter-1/2 retrofit**, not just the new consumers. Its catalog therefore covers the
   privately re-derived bank / relocation / dispatch / frame families of `Build/*`,
   `Universal*`, and `CookLevin/Hardness.lean` (the backlog retrofit entry's list), and
   **every routine carries a space cost alongside its time cost** from the start, so
   chapter 4 and the space statements (P4.x) can consume it without a second pass. The
   P0/P4.1 space statements are drafted while the layer is being designed, precisely so
   they can inform what else the layer needs (CH34-Q1).
2. **Hennie-Stearns + the two-work-tape universal machine** (§2.1): the layer's first
   new consumers, giving Thms 1.9 and 3.1 at book strength. The two-tape universal is a
   rewrite of `Universal.lean`, making it the natural retrofit pilot. Candidate bonus,
   to be checked at design time: carrying space bounds through it may also yield the
   space-efficient universal machine that Thm 4.8 needs (Ex 4.1).
3. **The chapter-1/2 retrofit** itself is *not* a gate for chapters 3-4: public surfaces
   are frozen, so retrofit batches run alongside the chapter-3/4 phases under the
   standard sweep + traversal + audit protocol.

**Fill campaign.** Fill work starts after the gates close, in epochs ordered by risk as
before. Two infrastructure prerequisites gate the machine-heavy epochs:

- the machine-routine layer as scoped above;
- the ARM extensions of §2.5.

**Integration with `main`.** Proposed: one PR per closed chapter (Chapter 3's light half
may go earlier), not one campaign-sized PR like #3. Main's CI runs only on pushes to
`main`, so each PR carries the local evidence: sweep, axiom prints, and the blueprint web
build.

## 5. Prior art to consult (design only; cite, never transcribe)

- **Édouard Bonnet's Lax Archive entries** (Lean 4.33, Mathlib `db584cd6`). They use a
  different machine model (stack machines, one work tape), so none of their code ports.
  - lax-434930 `classical-complexity` (commit `0c084031…`): `L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE =
    NPSPACE ⊆ EXPTIME`. Its space model counts every visited work cell, requires every
    branch to halt, and uses `c · log₂(n+2)`. It embeds the lax-307052 Savitch proof.
  - lax-362205 Immerman-Szelepcsényi (`EdouardBonnet/immerman-szelepcsenyi` @
    `e0ffe91e`): inductive counting on finite configuration graphs.
  - lax-783278 Arc Kayles: a machine-to-game `PSPACE`-hardness that bears on the shape of
    the `TQBF` hardness proof.
  - Licences: lax-434930 states Apache-2.0 for its incorporated helpers; the others' pages
    state none. Check each before any design adaptation, under the 2026-10-06 citation
    discipline.
- **cslib upstream** (`leanprover/cslib` `main`): `MultiTape/ConfigBound.lean` and
  `TapeLemmas.lean` (space-bounded configuration counting, `exists_spaceUsedByTape_max`).
  We already diverge from cslib's relational `MultiTapeNTM` (Chapter-2 decision log).
- **Szymon Toruńczyk, lax-218471**: compositional polynomial-time computation with
  black-box subroutines. It bears on the §2.2 `≤ₚ ⇒ Pᴼ` lemma and Ex 3.6(2).

## 6. Risks and honest effort assessment

- **Chapter 4 is the larger half**, and almost all of it is machine work with *space*
  ledgers. Every existing campaign construction (Chapters 1-2, `Build/*`) is time-only,
  and `machine-library-design.md` lists "no space bounds" among its non-goals. Building
  Chapter 4 on hand-built machines would repeat Chapter 2's cost profile several times
  over. The §2.5 program layers are the mitigation, and the plan depends on them.
- **The summits**, in rough order of size:
  1. the space-universal machine plus Thm 4.8 (or space theorems for the Chapter-1
     conversions);
  2. the `NP^EXPCOM ⊆ EXP` simulator (§2.3 — choice-word enumeration, per-step oracle
     NDTM simulation, and timed-universal query answering compounded in one machine);
  3. `TQBF` hardness (a polynomial-time emitter of the `ψᵢ` formula, comparable to the
     Cook-Levin emitter);
  4. Ladner's `H` in polynomial time;
  5. the universal NDTM at linear overhead (guess-then-verify, §2.7);
  6. Thm 4.2(iii) and Savitch over the configuration codec;
  7. Immerman-Szelepcsényi;
  8. Lemma 4.17.
- **Delivered-strength honesty**: Thms 3.1 and 3.2 land weaker than the book unless
  Hennie-Stearns is built. Every docstring must say so; this was the round-1 lesson of
  every prior audit.
- **Coordination**: Chapter 4 extends a colleague's live tree, and the plan needs their
  agreement before P4.1.
- **Estimated scale**: roughly 75 statements over eight statement phases plus P0. The
  total is larger than Chapter 2; Chapter 3 alone is comparable to Chapter 1.

## 7. Open design questions (human review required)

Answered 2026-10-08 by the maintainer except where marked open; the register below is
the record, and `backlog.md` §1 gets only the open ones.

1. **CH34-Q1 — sequencing against the machine-routine layer.** **Answered: yes to
   both.** Statement phases run in parallel with the §12 design; the space statements
   are drafted early to inform the layer's scope; the catalog records space costs
   alongside time. Addendum (same date): the layer is scoped to **amply support the
   chapter-1/2 retrofit** as well (§4a).
2. **CH34-Q2 — alignment with Hydroxyi.** **Answered: extend in place, co-owned.**
3. **CH34-Q3 — Thm 3.1 strength.** **Answered: strengthen** — Hennie-Stearns + the
   two-work-tape universal before the fill epochs (§2.1, §4a).
4. **CH34-Q4 — the `A` half of Thm 3.7.** **Answered (2026-10-08): the book's
   `EXPCOM` route** — more natural, and `P^EXPCOM = NP^EXPCOM = EXP` is the memorable
   identity; Ex 3.6(3) is core and `NP^EXPCOM ⊆ EXP` joins the summit list. Research
   note retained: the machine-light self-referential oracle is [BGS75, Thm 1]'s own
   proof (verified against the scanned original, pp. 433-434) and stays recorded as
   the fallback (§2.3). [BGS75] detail for the P3.1 audit: the polynomial clock must
   hold under *every* oracle, which constrains how `Pᴼ`/`NPᴼ` quantify the time bound.
5. **CH34-Q5 — QBF matrix.** **Answered: CNF.**
6. **CH34-Q6 — tiers.** **Answered: Thm 3.2 mandatory; Thm 3.3 (Ladner) core-late.**
7. **CH34-Q7 — `NSPACE` halting convention.** **Answered: all branches halt.**
8. **CH34-Q8 — universal-NDTM overhead.** **Answered (2026-10-08): linear overhead**,
   the strongest form possible (§2.7) — Thm 3.2 lands at the book's
   `f(n+1) = o(g(n))`.

## 8. Decision log

| Decision | Status |
|---|---|
| Chapters 3-4 run as one campaign on `complexity/arora-barak-ch3-4` (from `main` @ `99b187fc`), same methodology as Chapters 1-2; artifacts `ch3-*`/`ch4-*` | Proposed |
| Existing sorry-free Chapter-3/4 material on `main` (Hydroxyi, `f70c57c2`) is received and audited (P0), never duplicated | Proposed |
| Prior-art survey (2026-10-08): repository inventory (§1 tables); Bonnet lax-434930/362205/783278, cslib `ConfigBound`, Toruńczyk lax-218471 (§5) | Recorded |
| Chapter 4 machine work goes through program layers (`LogProg.ARM`, `CounterProg`, proposed extensions §2.5) | Proposed |
| §2 foundation choices and §7 provisional answers | **Answered 2026-10-08** (user): Q1 yes to both, Q2 extend in place co-owned, Q3 strengthen, Q5 CNF, Q6 Thm 3.2 mandatory / Ladner core-late, Q7 all branches halt. Q4 and Q8 open |
| Routine layer set up in parallel with the statement phases, scoped to **amply support the ch-1/2 retrofit** (full bank/relocation/dispatch/frame catalog), with space costs throughout; Hennie-Stearns + two-tape universal as first consumers; retrofit itself not a gate (§4a) | Decided (user, 2026-10-08) |
| §12 open decision 12.1 answered (user, 2026-10-08): R2 seam-composition space accounting takes the **sharper per-tape form** (max on disjointly-owned tapes) — sharpest available, for downstream applications | Decided |
| **P3.1 and P4.1 statement skeletons landed** (2026-10-08): `TuringMachine/{OracleFinite,OracleNondeterministic,NondeterministicSpace}.lean`, `ClassOracle/{Classes,SATOracle}.lean` + facade, `SpaceComplexity/{NSPACE,SpaceClasses,Constructible,Inclusions,Examples}.lean`; 24 sorried statements (10 oracle + 14 space), each with a policy-grade sketch; skeleton-time proofs: the `toFinOracleTM` bridge and the oracle `runWith` algebra (mirrors of proved infrastructure, flagged for the audits). All modules elaborate fresh (zero errors); style lint 0 FAIL; `Ex 4.7`'s `MULT` deferred to P4.4 (encoding conventions), the ARM extension interfaces deferred to the §12 gate + colleague sync. Audit packs for P3.1/P4.1 follow once P0's round returns | Recorded |
| **§12 statement skeleton landed** (2026-10-08, sub-agent drafted, maintainer-reviewed line by line): `Build/Embed.lean` (R1, two transformers over a shared core per 12.4, 9 sorried), `Build/Seam.lean` (R2, dispatch constant exactly 1, per-tape visited-set containment headline per 12.1, 6 sorried), `Build/Catalog.lean` (R3, five seam routines defined + W1-W3/L and P1-P15 space rows, 32 sorried; `Primitives.lean` byte-identical per 12.2a). Review: machine semantics traced phase by phase; restated time clauses spot-checked **verbatim** against `computesFunInTime_id`/`_prepend`/`_cond`/`exists_loopTM`; scope clarification: stream rows P16-P18 ride with the emitter-lazy scope (flagged to the gate). All modules elaborate, 0 errors; its statement-gate pack is next | Recorded |
| **P3.2 statement skeleton landed** (2026-10-08, sub-agent drafted, maintainer-reviewed line by line): `TuringMachine/OracleAgreement.lean` (7 sorried) + `Diagonalization/{EXPCOM,Relativization,NotTimeConstructible}.lean` + facade (10 sorried) — 17 statements; EXPCOM per CH34-Q4, extrinsic-clock enumeration per [BGS75], Ex 3.5 non-trivialized. Review fixes: stage-construction sketch's decided-length bound corrected to `max nᵢ (budget)` (the `i = 0` edge). Five natural-home promotions flagged for the P3.1 gate close; all cited lemma names verified to exist. P3.1 files untouched (layout decision: all of P3.2 lives in `Diagonalization/`) | Recorded |
| CH34-Q4 answered (user, 2026-10-08): **EXPCOM route** for the `A` half of Thm 3.7 — Ex 3.6(3) promoted to core, the `NP^EXPCOM ⊆ EXP` simulator added to the summit list (continuation budget certain); [BGS75, Thm 1]'s self-referential oracle recorded as fallback | Decided |
| **P0 reception audit, round 1** (2026-10-08, `audits/ch34-p0-findings.md`, verbatim): **0 blockers, 1 major, 7 minors, 2 notes — gate does not close**; repairs + re-audit round per `workflow.md` §3. The auditor confirmed the time-hierarchy family, `configBound`, `LOGSPACE_subset_P`, the compiler contracts and the index encoding under their actual hypotheses | Recorded |
| **Round-1 major repaired** (finding 1, maintainer-verified: `visitedByTapeHead` images a nonempty range, so `k ≤ spaceUsed` always; one zero of `s` collapses `SPACE s` to the zero-work-tape class): positive-bound convention adopted (§2.4), Ex 3.2 restated at `SPACE(n+1)`, documented in `SpaceComplexity/Basic.lean`, sanity layer `SpaceComplexity/ZeroSpace.lean` added (S1-S6, sorried statements). Minors swept: `sim_run` headline + S9 statement (`sim_run_of_regs_le`), `Mode`/`callSegs` zero-argument qualifier, `valP`/`valQ` canonical payloads, `lenEq`/`lenLe` totalization note, `ReachesB` strict-endpoint wording, `ARMSim`/`Compile`/`Layout` export-list corrections; finding 7 (sweep-log provenance) repaired by a fresh sweep whose log records its revision at start. Notes 9-10 require no change | Recorded |
| CH34-Q8 answered (user, 2026-10-08): the universal NDTM is built at **linear overhead** (guess-then-verify), so Thm 3.2 lands at book strength `f(n+1) = o(g(n))` | Decided |
| CH34-Q4 research (2026-10-08): the machine-light oracle `A = K(A)` **is** [BGS75]'s own Theorem 1 (verified against the scanned original, pp. 433-434), so no deviation from the primary source; [AB09]'s `EXPCOM` is the substitution. Awaiting maintainer confirmation of the route | Recorded |
| Citation audit (2026-10-08), prompted by the maintainer: no missing code-inspiration citation found in campaign-authored Lean code — vendored cslib files carry full headers (pin `a3747758`), `Composition.lean` cites [Balbach22], `Build/*` + `machine-library-design.md` §1-11 were frozen 2026-10-03, two days **before** the first Bonnet examination (2026-10-05, scratchpad-only, never imported; backlog records the after-the-fact cost comparison as convergence). No brief ever carried external code. Hydroxyi's `TimeHierarchy//SpaceComplexity//PolyHierarchy/` trees cite only [AB09]; two design similarities flagged to *ask* (not assertions): `LogProg` compiler vs lax-434930's `TimeCompiler`; `ConfigCount.core` vs cslib `ConfigBound`'s `Cfg.core` (upstream 2026-09-14). §12 citation duty ([lax-434930], Apache-2.0) remains binding when that design is written | Recorded |

```


## ===== policy.md =====

```
# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.

```


## ===== workflow.md =====

```
# TCSlib Formalization Workflow

How large formalization campaigns are run in this repository. [`policy.md`](policy.md)
says what landed Lean code must look like; this document says what *process* produces
it. The reference implementation is the Arora-Barak campaign
(`AroraBarakChapter1Plan.md`, complete and audited end to end;
`AroraBarakChapter2Plan.md`, in progress) — file paths below cite its artifacts as
worked examples. Where an older document describes a mechanism this one supersedes
(e.g. the PR-based fill delivery in `AroraBarakChapter1Plan.md` §5, since replaced by
zip delivery), this document records current practice.

```
plan  →  statement phases  →  audit gates  →  fill campaign  →  closure
          (sorry-skeletons)    (per phase)     (epochs/batches)   (attestation, final
                                                                   audit, blueprint)
```

The load-bearing idea: **statements are audited before proofs are attempted.** Lean
already checks proofs; the dominant failure mode of formalization is a wrong or
subtly-weakened *statement*, and that is cheapest to catch while everything is still a
`sorry`. Every phase therefore lands as a compiling skeleton, passes an adversarial
external audit gate, and only then becomes fill work.

## 1. The campaign plan

Each campaign (typically one textbook chapter) begins with a plan file at the repo
root — `<Source>Chapter<N>Plan.md` — containing:

* **Scope**: which results are mandatory core, which are deferred, with source
  citations.
* **Foundation decisions**: the definitional conventions, each with its rationale
  (these are where audits bite; see §3).
* **Architecture and module layout**: directories, namespaces, facades, per policy §1.
* **Phasing**: the statement phases and the anticipated fill epochs.
* **Risks and honest effort assessment**.
* **Open design questions (human review required)**: decisions reserved for a human
  maintainer. Audit rounds *verify* these but never *dispose* of them; each records
  the maintainer's provisional choice and stays open until a human closes it. The
  consolidated register — full statements, cross-links, and status — is
  [`backlog.md`](backlog.md); the plans keep stable numbered stubs, which is what
  audit documents cite.
* **Decision log**: an append-only table. Every methodological decision, every audit
  round's verdict, and every repair round gets a row. The log is the campaign's
  memory; when a decision is reversed, the old row is marked **Superseded** in place,
  never deleted.

## 2. Statement phases (sorry-skeletons)

A phase lands the definitions plus the theorem *statements* of one coherent slice,
every proof a `sorry` under a policy-grade proof sketch (policy §3: the sketch is
written at skeleton time and is the plan; a skeleton whose sketch cannot be written is
not ready to land). Ground rules:

* Definitions and sorried statements only. Proofs appear in a skeleton only for
  definitional-unfolding lemmas whose home module mirrors proved infrastructure (the
  precedent: the `runWith` algebra of `TuringMachine/Nondeterministic.lean`, mirroring
  the vendored `runFrom` lemmas), and any such deviation is flagged in the audit pack
  with the proofs declared part of the audited surface.
* Sketches name their obligations: a sketch that will need a machine construction
  names each sub-machine as an explicit fill obligation, so the eventual brief can
  inherit the list.
* Everything gate-verifies before commit: per-module checks plus a full fresh sweep
  (§6), style lint, and the headline axiom prints.

## 3. Audit gates (between phases)

Right after a skeleton lands — statements frozen — an **external adversarial audit**
runs before any fill or any next phase. The auditor is an LLM from a different vendor,
in a fresh context, reviewing the trusted surface (definitions, statements, sketches,
and any skeleton-time proofs) against the source text.

**Artifacts**, all committed under `audits/` with campaign-scoped names
(`ch2-phase1-*`, `epoch4-*`):

* `…-pack.md` — the auditor's instructions: the audited commit, repository-side
  attestations (freeze by path enumeration, sweep results, admission inventory, axiom
  prints, lint — stated so the auditor can verify or challenge them, with source facts
  kept separate from maintainer execution claims), the under-audit inventory, a
  prioritized brief (the plan's seeded design questions go here), and the findings
  table format with the severity guide: **blocker** (a downstream phase would build on
  a wrong statement) / **major** (fixable but materially misleading) / **minor** /
  **note**. `audits/TEMPLATE.md` is the skeleton.
* `…-bundle.md` — a single uploadable file: the pack verbatim, then every attachment
  under a `## ===== <path> =====` header (prior findings, both plans, `policy.md`,
  the root, and the full module tree).
* A short kickoff message (drafted per round, pasted by the maintainer into a fresh
  auditor chat with the bundle attached).
* `…-findings.md` — the auditor's report, preserved **verbatim**, including anything
  the maintainer disputes. Pack errata found later are acknowledged in the resolutions
  file; shipped packs are never edited retroactively.

**The gate rule**: a gate closes only on a round reporting **zero blockers and zero
majors**. A round with majors triggers repairs and a full re-audit round (minors may
be swept in the closing commit and re-verified). Repairs adopt the auditor's own
constructions where supplied, are re-gated, and are recorded in the decision log; when
the loop closes, `…-resolutions.md` summarizes every round, every repair, and the note
dispositions. The complete worked example is the three-round
`audits/ch2-phase1-{pack,findings,reaudit-…,round3-…,resolutions}.md` loop.

Audits complement, never replace, in-Lean sanity theorems — the machine-checked and
permanent form of the same checks.

## 4. The fill campaign (epochs and batches)

With all phase gates closed, the audited-true sorries are filled in **epochs** —
sequential, ordered by risk retirement, with an audit round at each epoch boundary —
each consisting of **batches** run in parallel by cloud agents with disjoint file
ownership, from self-contained briefs in `briefs/`.

**Binding batch ground rules** (full text repeated in every brief):

1. **Exclusive file ownership.** Helpers live `private` in owned files; a lemma that
   belongs in a shared file is *requested* in the report and added serially at epoch
   merge, flagged for the next audit.
2. **Statement freeze.** Audited declarations are never renamed, re-signatured, or
   re-stated by fill work. A target that looks unprovable as stated is an
   *escalation*, reported with the obstruction — never "fixed" inline.
3. **Verification per batch**: the check script (§6) over the owned files, zero
   `error:` lines, sorries only at documented out-of-scope items.

**Delivery is by zip, not PR.** Each batch returns an archive containing `REPORT.md`,
the full source files, a `git format-patch` series, a git bundle, the batch's sweep
log, the axiom-print log, and `SHA256SUMS`. The maintainer verifies before
integrating: checksums; the statement freeze (comment-stripped comparison of every
audited signature); enumeration of any removals; public-declaration drift; a full
fresh sweep; the headline axiom prints. Integration is `git am -3` from the patch
series, preserving the agent's authorship. Large fills that exhaust one agent's budget
continue via a continuation brief to a fresh agent (the `universal` B2 precedent).

**Epoch boundaries**: the maintainer re-runs the full sweep, produces a **drift
attestation** (§6), and prepares the epoch's audit pack with elaboration evidence;
the epoch's gate follows the same zero-blockers/majors rule as phase gates.

## 5. Closure

When the last sorry falls: a zero-sorry sweep with build evidence; a campaign-wide
drift attestation against the audited baselines; a final audit pack covering the fill
rounds; and the blueprint increment — dependency graph from `.ilean` artifacts,
`scripts/blueprint_{enumerate,assemble,validate}.py`, blueprint-writer agents, with
the blueprint **late-bound** throughout (extraction only at boundaries; no blueprint
LaTeX hand-written ahead of the Lean; `blueprint/BLUEPRINT_PIPELINE.md` has the
pipeline detail).

## 6. Verification tooling

* **`scripts/lean_check_tree.sh <module>`** — the campaign's elaboration gate: a
  direct `lean` invocation per module (**`lake build` is banned on campaign
  branches** — see the Chapter-1 decision log), emitting fresh `.olean`s into a
  scratch tree. Pass requires exit 0, zero `error:` lines, *and* a fresh olean, so a
  stale artifact can never satisfy the check. The full sweep runs it over every
  module, in dependency order, from `scripts/ab_ch1_module_order.txt`:

  ```
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < scripts/ab_ch1_module_order.txt )
  ```

  Admission counting is by `declaration uses 'sorry'` warnings in the sweep log; the
  expected count is attested in every pack.
* **`scripts/campaign_style_lint.py`** (named `scripts/style_lint.py` until the
  main merge, which adopted main's per-file policy linter under that name — the
  historical audit logs' invocations refer to this tool) — mechanical policy checks: statement-prose docstrings,
  sketch-before-sorry, file sizes, `## References`, facade coverage. Campaign
  baseline: zero FAIL (legacy pre-campaign files outside the audited surface are
  tolerated and listed).
* **Axiom prints** — `#print axioms` for every headline theorem on the *fresh* olean
  tree: closed results must show exactly `[propext, Classical.choice, Quot.sound]`;
  sorried statements show `sorryAx`, and any other axiom is a stop-the-line event.
* **Drift attestation** — the anti-tamper check between audited baselines: strip
  comments from every module, compare both the **multiset** of declarations and the
  **ordered declaration sequence** against the baseline, and enumerate public
  declarations (gained / lost / changed) so that "nothing audited moved" is a checked
  claim, not an impression.
* **Vendored files** are frozen at their recorded upstream pin and periodically
  byte-compared against upstream; local modifications live only in the header list.

## 7. Relationship to the other documents

* [`policy.md`](policy.md) — the standards this workflow enforces (modularity,
  attribution, sketches, review checklist).
* [`lean-glossary.md`](lean-glossary.md) — the Lean/Mathlib jargon appearing in
  declaration names and docstrings (fuel, Sigma, `Prop` vs `Bool`, the naming
  grammar, …), for readers fluent in TCS but not in Lean.
* [`AGENTS.md`](AGENTS.md) / `.claude/` — the sorry-ladder proof technique and agent
  roster; useful *inside* a fill batch, but campaign verification runs through §6, not
  through `lake build` or editor-only checks.
* [`blueprint/BLUEPRINT_PIPELINE.md`](blueprint/BLUEPRINT_PIPELINE.md) — blueprint
  generation and validation.
* [`.github/copilot-instructions.md`](.github/copilot-instructions.md) — main-branch
  build and CI; campaign branches deviate as recorded in their decision logs.

```


## ===== TCSlib/Complexity/TuringMachine/OracleAgreement.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.OracleNondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle locality: runs under agreeing oracles coincide

The locality layer of the relativization theorem ([AB09, Theorem 3.7]; [BGS75,
§3]): an oracle machine's `t`-step run from the initial configuration consults
the oracle only on the strings it actually submits, each of length less than
the elapsed time. Hence two oracles that agree on every submitted string — or,
more coarsely, on every string of length below the horizon — produce literally
the same run. This is what lets the Baker-Gill-Solovay stage construction run a
machine against a *partial* oracle (undetermined queries answered "no") and
transfer the verdict to the completed oracle, provided the completion never
touches a queried string.

## Design

* `Turing.OracleTM.queriesWithin M O x t` records the query strings submitted
  during the first `t` steps of the initialized run: one entry for each step
  index `s < t` at which the machine sits in `qQuery` (that step submits the
  current query-tape contents). It is a *list* (with multiplicity, in step
  order), so the stage construction's counting argument — at most `t` queries
  in `t` steps — is its length bound, with no finiteness side conditions.
* The nondeterministic variant `Turing.OracleNDTM.queriesAlong N O x w` runs
  along a fixed choice word `w`, mirroring `Turing.OracleNDTM.runWith`; its
  horizon is `w.length` (the first `t` steps along `w` are the queries along
  `w.take t`).
* The query-set form (`runFrom_eq_of_agree_queriesWithin`) is deliberately
  asymmetric: the query list is computed along the run under the *first*
  oracle, which is exactly the shape the stage construction consumes (run with
  the partial oracle, then extend it).

## Main definitions

* `Turing.OracleTM.queriesWithin` — the query strings submitted in the first
  `t` steps of a deterministic initialized oracle run.
* `Turing.OracleNDTM.queriesAlong` — the query strings submitted along a fixed
  choice word of a nondeterministic initialized oracle run.

## Main results (all sorried; phase-P3.2 statements)

* `Turing.OracleTM.runFrom_eq_of_agree_length_lt` — agreement on all strings of
  length `< t` makes the `t`-step runs coincide.
* `Turing.OracleTM.runFrom_eq_of_agree_queriesWithin` — agreement on the
  submitted queries alone makes the `t`-step runs coincide.
* `Turing.OracleNDTM.runWith_eq_of_agree_length_lt`,
  `Turing.OracleNDTM.runWith_eq_of_agree_queriesAlong` — the same two along a
  fixed choice word.
* `Turing.OracleTM.length_le_of_mem_queriesWithin`,
  `Turing.OracleNDTM.length_le_of_mem_queriesAlong` — every submitted query is
  short (length at most the horizon).
* `Turing.OracleTM.queriesWithin_length_le` — at most `t` queries in `t` steps
  (the stage construction's counting bound).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, proof of Theorem 3.7.)
* [BGS75] T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP
  question*, SIAM Journal on Computing 4(4), 1975. (§3: runs against finite
  partial oracles.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*}

namespace OracleTM

open Classical in
/-- The query strings submitted by the oracle machine `M`, with oracle `O`, on
input `x`, during the first `t` steps of the initialized run: one entry per step
index `s < t` at which the run sits in the query state (that step submits the
current contents of the query tape, `Turing.OracleTM.queryString`), in step
order and with multiplicity. [AB09, proof of Theorem 3.7: "the strings queried
by `M_i` on input `1^n`"] -/
noncomputable def queriesWithin (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) : List (List Symbol) :=
  (List.range t).filterMap fun s =>
    if (M.runFrom O (M.initCfg x) s).state = some M.qQuery then
      some (queryString (M.runFrom O (M.initCfg x) s))
    else none

/-- **Length-locality of deterministic oracle runs**: if two oracles agree on
every string of length less than `t`, the `t`-step initialized runs under them
coincide — a `t`-step run can only ever submit queries of length below `t`.
[AB09, proof of Theorem 3.7; BGS75, §3]

**Proof sketch.** Strengthen to: for every `s ≤ t` the two runs coincide at
horizon `s`, by induction on `s`. The configurations after `s` steps agree by
the inductive hypothesis; for the next step, either the common configuration is
not in the query state — then `Turing.OracleTM.step_eq_of_ne_qQuery` makes the
step oracle-independent — or it is, and the submitted string is the common
configuration's `Turing.OracleTM.queryString`, of length at most `s < t` by
`Turing.OracleTM.queryString_length_le`, on which `O` and `O'` agree, so both
steps move to the same answer state. Fill obligations: the `≤ t`-indexed
induction (successor unfolding `Function.iterate_succ_apply'` of
`Turing.OracleTM.runFrom`), and the two-case analysis of
`Turing.OracleTM.step` at a common configuration. -/
theorem runFrom_eq_of_agree_length_lt (M : OracleTM k Symbol State)
    (O O' : Language Symbol) (x : List Symbol) (t : ℕ)
    (h : ∀ z : List Symbol, z.length < t → (z ∈ O ↔ z ∈ O')) :
    M.runFrom O (M.initCfg x) t = M.runFrom O' (M.initCfg x) t := by
  sorry

/-- **Query-set locality of deterministic oracle runs** — the form the
Baker-Gill-Solovay stage construction consumes: if two oracles agree on every
string the run with the *first* oracle actually submits in its first `t` steps,
the `t`-step initialized runs coincide. In the stage construction `O` is the
finite partial oracle (undetermined strings answered "no") and `O'` the
completed oracle, which by construction never disturbs a queried string.
[AB09, proof of Theorem 3.7; BGS75, §3]

**Proof sketch.** As in `Turing.OracleTM.runFrom_eq_of_agree_length_lt`,
by induction on `s ≤ t` with the runs kept equal: at a non-query step
`Turing.OracleTM.step_eq_of_ne_qQuery` applies; at a query step the submitted
string is, by definition of `Turing.OracleTM.queriesWithin` (its step index
`s` lies in `List.range t` and the state condition holds along the `O`-run,
which the inductive hypothesis identifies with the `O'`-run), an element of
`M.queriesWithin O x t`, where `h` makes both oracles answer alike. Fill
obligations: the `List.mem_filterMap` membership introduction, and the same
run-equality induction as the length-locality lemma. -/
theorem runFrom_eq_of_agree_queriesWithin (M : OracleTM k Symbol State)
    (O O' : Language Symbol) (x : List Symbol) (t : ℕ)
    (h : ∀ z ∈ M.queriesWithin O x t, (z ∈ O ↔ z ∈ O')) :
    M.runFrom O (M.initCfg x) t = M.runFrom O' (M.initCfg x) t := by
  sorry

/-- **Submitted queries are short**: every string in `queriesWithin M O x t`
has length at most `t`. (Sharper: a query submitted at step `s < t` has length
at most `s`.) [AB09, proof of Theorem 3.7, the length bookkeeping]

**Proof sketch.** A member of the `List.filterMap` arises from some `s ∈
List.range t` with the run in the query state after `s` steps, and equals
`Turing.OracleTM.queryString` of that configuration;
`Turing.OracleTM.queryString_length_le` bounds its length by `s ≤ t`. -/
theorem length_le_of_mem_queriesWithin {M : OracleTM k Symbol State}
    {O : Language Symbol} {x : List Symbol} {t : ℕ} {z : List Symbol}
    (hz : z ∈ M.queriesWithin O x t) : z.length ≤ t := by
  sorry

/-- **At most `t` queries in `t` steps**: the query list of a `t`-step run has
length at most `t` — the counting half of the stage construction (a
polynomial-time run cannot touch all `2^n` strings of length `n`).
[AB09, proof of Theorem 3.7, the counting argument; BGS75, §3]

**Proof sketch.** `Turing.OracleTM.queriesWithin` is a `List.filterMap` over
`List.range t`: `List.length_filterMap_le` and `List.length_range`. -/
theorem queriesWithin_length_le (M : OracleTM k Symbol State)
    (O : Language Symbol) (x : List Symbol) (t : ℕ) :
    (M.queriesWithin O x t).length ≤ t := by
  sorry

end OracleTM

namespace OracleNDTM

open Classical in
/-- The query strings submitted by the nondeterministic oracle machine `N`,
with oracle `O`, on input `x`, along the choice word `w`: one entry per step
index `s < w.length` at which the branch (the run under `w.take s`) sits in the
query state, in step order and with multiplicity — the
`Turing.OracleNDTM.runWith` analogue of `Turing.OracleTM.queriesWithin`. The
queries of the first `t` steps along `w` are the queries along `w.take t`.
[AB09, proof of Theorem 3.7, applied branchwise] -/
noncomputable def queriesAlong (N : OracleNDTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (w : List Bool) : List (List Symbol) :=
  (List.range w.length).filterMap fun s =>
    if (N.runWith O (w.take s) (N.initCfg x)).state = some N.qQuery then
      some (OracleTM.queryString (N.runWith O (w.take s) (N.initCfg x)))
    else none

/-- **Length-locality of nondeterministic oracle runs, branchwise**: if two
oracles agree on every string of length less than `w.length`, the runs along
the fixed choice word `w` coincide. [AB09, proof of Theorem 3.7; Definition
3.4, "nondeterministic oracle TMs are defined similarly"]

**Proof sketch.** Induction on `s ≤ w.length` with the branch prefixes kept
equal (`Turing.OracleNDTM.runWith_cons` unfolds one consumed choice bit). A
`Turing.OracleNDTM.stepWith` from a common configuration under the common
choice bit is oracle-independent away from `qQuery` (the transition-table
branch does not mention the oracle; halted configurations are fixed by
`Turing.OracleNDTM.stepWith_of_halt`), and at `qQuery` both oracles resolve the
common query string alike, its length being below `w.length` by the
nondeterministic query-length bound (the invariant behind
`Turing.OracleNDTM.length_le_of_mem_queriesAlong` below, at horizon `s`). Fill
obligations: an `OracleNDTM.stepWith` analogue of
`Turing.OracleTM.step_eq_of_ne_qQuery`, and the `w.take`-indexed induction
(`List.take_succ` against `Turing.OracleNDTM.runWith_append`). -/
theorem runWith_eq_of_agree_length_lt (N : OracleNDTM k Symbol State)
    (O O' : Language Symbol) (x : List Symbol) (w : List Bool)
    (h : ∀ z : List Symbol, z.length < w.length → (z ∈ O ↔ z ∈ O')) :
    N.runWith O w (N.initCfg x) = N.runWith O' w (N.initCfg x) := by
  sorry

/-- **Query-set locality of nondeterministic oracle runs, branchwise**: if two
oracles agree on every string the branch under the *first* oracle actually
submits along `w`, the runs along `w` coincide.
[AB09, proof of Theorem 3.7; BGS75, §3]

**Proof sketch.** The same induction on `s ≤ w.length` as
`Turing.OracleNDTM.runWith_eq_of_agree_length_lt`, with the query-step case
discharged by membership of the submitted string in
`N.queriesAlong O x w` (its index lies in `List.range w.length` and the state
condition holds along the `O`-branch, which the inductive hypothesis identifies
with the `O'`-branch) and the agreement hypothesis `h` — mirroring the
deterministic `Turing.OracleTM.runFrom_eq_of_agree_queriesWithin`. -/
theorem runWith_eq_of_agree_queriesAlong (N : OracleNDTM k Symbol State)
    (O O' : Language Symbol) (x : List Symbol) (w : List Bool)
    (h : ∀ z ∈ N.queriesAlong O x w, (z ∈ O ↔ z ∈ O')) :
    N.runWith O w (N.initCfg x) = N.runWith O' w (N.initCfg x) := by
  sorry

/-- **Submitted queries are short, branchwise**: every string in
`queriesAlong N O x w` has length at most `w.length`.
[AB09, proof of Theorem 3.7, the length bookkeeping]

**Proof sketch.** The member arises at some step index `s < w.length`, as
`Turing.OracleTM.queryString` of the branch configuration after `s` steps. The
deterministic bound `Turing.OracleTM.queryString_length_le` rests on the
head-position/blank-cell invariant of initialized runs, which transfers
verbatim to `Turing.OracleNDTM.runWith`: a `stepWith` either applies a
transition-table action (writes only at the old head position, moves heads by
at most one — the same `Turing.Action.apply` facts), resolves a query (tapes
and heads unchanged), or is halted (identity). Fill obligations: the
nondeterministic run invariant (the `runWith` analogue of the private
`runFrom_workTapes_invariant` of `TCSlib.Complexity.TuringMachine.Oracle` —
its natural home is the frozen `Oracle`/`OracleNondeterministic` pair, so it
lands here; flagged for promotion), then the `Nat.find` bound exactly as in
`Turing.OracleTM.queryString_length_le`. -/
theorem length_le_of_mem_queriesAlong {N : OracleNDTM k Symbol State}
    {O : Language Symbol} {x : List Symbol} {w : List Bool} {z : List Symbol}
    (hz : z ∈ N.queriesAlong O x w) : z.length ≤ w.length := by
  sorry

end OracleNDTM

end Turing

```


## ===== TCSlib/Complexity/Diagonalization/EXPCOM.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassOracle.Classes
import TCSlib.Complexity.TimeHierarchy.Diagonal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `EXPCOM` oracle: `P^EXPCOM = NP^EXPCOM = EXP`

[AB09, Example 3.6(3)]: relative to the oracle
`EXPCOM = {⟨M, x, 1ⁿ⟩ : M outputs 1 on x within 2ⁿ steps}`, deterministic and
nondeterministic polynomial time coincide — both equal `EXP`, via the chain
`EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP`. This is the `A` half of the
Baker-Gill-Solovay theorem ([AB09, Theorem 3.7], `Diagonalization/Relativization`),
taken by the book's route per the campaign decision CH34-Q4
(`AroraBarakChapters3-4Plan.md` §2.3; the machine-light self-referential oracle
of [BGS75, Theorem 1] stays recorded there as the fallback).

## Design

* **The triple `⟨M, x, 1ⁿ⟩` is rendered code-first** as
  `Turing.pairEncode α (Turing.pairEncode x 1ⁿ)` — the universal machine's
  layout (code before payload, chapter-1 phase-3 audit, Argument B), nested
  right so each component is recovered by one aligned-pair parse.
* **The code scheme is the campaign's fixed `Complexity.TimeHierarchy.code`**,
  reused rather than re-chosen, so the timed universal machine
  (`Turing.timed_universal`) and every encoding lemma apply verbatim.
* **"Outputs `1` within `2ⁿ` steps"** is
  `Turing.FinTM.ComputesInTime x [true] (2 ^ n)`: halting is absorbing, so the
  predicate is monotone in the budget and "within" is faithful.
* **Totalization**: a string that does not parse as a triple is simply not in
  `EXPCOM` (the existential fails); on genuine triples the witnessing
  decomposition is unique (`Turing.pairEncode_injective`,
  `Turing.pairEncode_replicate_inj`), so the defining condition is
  unambiguous.

## Main definitions

* `Complexity.EXPCOM` — the oracle language. [AB09, Example 3.6(3)]

## Main results (all sorried; phase-P3.2 statements)

* `Complexity.EXP_subset_POracle_EXPCOM` — one padded query decides any
  `EXP` language.
* `Complexity.NPOracle_EXPCOM_subset_EXP` — the fill summit: deterministic
  exponential-time simulation of a polynomial-time oracle NDTM, answering its
  queries with the timed universal machine.
* `Complexity.POracle_EXPCOM_eq_EXP`, `Complexity.NPOracle_EXPCOM_eq_EXP`,
  `Complexity.POracle_EXPCOM_eq_NPOracle_EXPCOM` — the chained identities.
  [AB09, Example 3.6(3)]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Example 3.6(3); Claim 2.4.)
* [BGS75] T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP
  question*, SIAM Journal on Computing 4(4), 1975. (Theorem 1: the recorded
  fallback oracle for the `A` half.)
-/

namespace Complexity

open Turing

/-- **The `EXPCOM` oracle** [AB09, Example 3.6(3)]: the language of triples
`⟨M, x, 1ⁿ⟩` such that the machine `M` outputs `1` on `x` within `2ⁿ` steps —
rendered with the campaign's fixed code scheme `Complexity.TimeHierarchy.code`
and the code-first nesting `Turing.pairEncode α (Turing.pairEncode x 1ⁿ)`, with
"outputs `1` within `2ⁿ` steps" as
`Turing.FinTM.ComputesInTime x [true] (2 ^ n)` (monotone in the budget, since
halting is absorbing). Strings that do not parse as such a triple are not in
the language; on genuine triples the decomposition is unique
(`Turing.pairEncode_injective`, `Turing.pairEncode_replicate_inj`). -/
def EXPCOM : Language Bool :=
  {z | ∃ (α x : List Bool) (n : ℕ),
    z = pairEncode α (pairEncode x (List.replicate n true)) ∧
    ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x [true] (2 ^ n)}

/-- **One padded query decides any `EXP` language**: `EXP ⊆ P^EXPCOM`.
[AB09, Example 3.6(3), the first inclusion of the chain
`EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP`]

**Proof sketch.** Let `L ∈ EXP`, say decided by `M` within `a · 2^(n^c)`
(`Complexity.EXP` unfolds to such data). Normal-form `M` to a one-work-tape
binary machine (`Turing.FinTM.one_work_tape_binary`, quadratic slowdown) and
relabel it to a coded machine `N` (`Turing.exists_codeTM`); put
`α_L := TimeHierarchy.code.encode N`, recovered by
`code.toMachineCode.decode_encode`. Choose the padding exponent
`Q n := C · (n + 1)^c` with `C` absorbing `a`, the square, and the `+1`
normalizations, so that `N` outputs `[χ_L x]` within `2^(Q |x|)` steps on every
`x`. The reduction is `f x := pairEncode α_L (pairEncode x 1^(Q |x|))` —
polynomial-time by the chapter-2 padding cluster: the constant prefix
(`Complexity.polyTimeComputable_const`), the copy
(`Complexity.polyTimeComputable_id`), the unary padding emitter
(`Complexity.polyTimeComputable_polyUnary C c`), assembled by two applications
of `Complexity.PolyTimeComputable.pairEncode`. Membership: if `x ∈ L` then the
witness `(α_L, x, Q |x|)` puts `f x ∈ EXPCOM`; conversely a witness for
`f x ∈ EXPCOM` is forced to be exactly `(α_L, x, Q |x|)`
(`Turing.pairEncode_injective` twice, `Turing.pairEncode_replicate_inj`), and
output determinism (`Turing.FinTM.ComputesInTime.output_unique`) against `N`'s
verdict `[χ_L x]` forces `x ∈ L`. Conclude with
`Complexity.mem_POracle_of_polyTimeReducible`. -/
theorem EXP_subset_POracle_EXPCOM : EXP ⊆ POracle EXPCOM := by
  sorry

/-- **The fill summit of the `EXPCOM` cluster**: `NP^EXPCOM ⊆ EXP` — a
deterministic exponential-time machine can enumerate all branches of a
polynomial-time oracle NDTM and answer its `EXPCOM` queries itself.
[AB09, Example 3.6(3), the last inclusion; summit 2 of
`AroraBarakChapters3-4Plan.md` §6, continuation budget certain]

**Proof sketch.** Let `L ∈ NP^EXPCOM`: a well-formed oracle NDTM `N` decides
`L` with oracle `EXPCOM` within `p n := c · (n^k + 1)`. The deciding plain
machine, on input `x` of length `n`:

1. **Choice-word enumeration.** Iterate over all `2^(p n)` choice words of
   length exactly `p n` as a fixed-width counter, one round per word, in the
   `Complexity.NP_subset_EXP` enumerator pattern
   (`Complexity.exists_proj_decider` / `enumLoop_run`: fixed-width carry,
   captured round verdict, reversible scratch restoration, accept-or-increment
   control).
2. **Per-step simulation.** Within a round, simulate
   `Turing.OracleNDTM.runWith` step by step under the current word — the
   step-by-step compilation invariant of the chapter-2 2B cluster
   (`ClassNP/Nondeterminism.lean`), extended by one new case: the query state.
3. **Query answering.** When the simulated state is `qQuery`, read the
   simulated query tape `z` (`Turing.OracleTM.queryString` contract), parse it
   as `pairEncode α' (pairEncode x' 1^(n'))` by aligned two-bit parsing (the
   `Turing.pairDecode` layer; `TCSlib.Complexity.TuringMachine.CodeParser`
   machine precedent) — malformed strings answer "no" — and decide
   `z ∈ EXPCOM` by running the timed universal machine
   (`Turing.timed_universal` at the fixed scheme `TimeHierarchy.code`) on
   `(α', x')` with deadline `2^(n')`: answer "yes" exactly on success with
   simulated output `[true]` (report `true :: [true]`); the deadline-inclusive
   timeout clause makes the answer the exact membership bit, with
   parse-uniqueness (`Turing.pairEncode_injective`,
   `Turing.pairEncode_replicate_inj`) identifying the witness decomposition.
4. **Ledger.** Each branch submits queries of length at most the elapsed
   budget (`Turing.OracleTM.queryString_length_le` transferred along the
   simulation invariant), so `n' ≤ p n` and one oracle call costs
   `O((2^(p n) + 1)^2)` universal-machine steps; a round is `p n` simulated
   steps of which each costs at most one call: the total over `2^(p n)` rounds
   is `2^(O(p n) )·(2^(p n))^2 = 2^(O(n^k))`, inside `DTIME (2^(n^(k+1)))` by
   `Complexity.DTIME`'s constant absorption — so `L ∈ EXP`.
5. **Acceptance.** `x ∈ L` iff some length-`p n` branch accepts
   (`Turing.FinOracleNDTM.DecidesInTime`, with all-branch halting making every
   round's verdict defined); the enumerator's existential sweep returns exactly
   this disjunction.

Fill obligations, named for the brief: the query-dispatcher routine (parse +
clocked universal call + resume seam) and its capture discipline; the
simulation invariant tying the host's configuration coding to `runWith`; the
budget normalization into `EXP`'s `2^(n^c)` form. -/
theorem NPOracle_EXPCOM_subset_EXP : NPOracle EXPCOM ⊆ EXP := by
  sorry

/-- **`P^EXPCOM = EXP`** [AB09, Example 3.6(3)].

**Proof sketch.** `⊇` is `Complexity.EXP_subset_POracle_EXPCOM`; `⊆` chains
`Complexity.POracle_subset_NPOracle` with
`Complexity.NPOracle_EXPCOM_subset_EXP`. -/
theorem POracle_EXPCOM_eq_EXP : POracle EXPCOM = EXP := by
  sorry

/-- **`NP^EXPCOM = EXP`** [AB09, Example 3.6(3)].

**Proof sketch.** `⊆` is `Complexity.NPOracle_EXPCOM_subset_EXP`; `⊇` chains
`Complexity.EXP_subset_POracle_EXPCOM` with
`Complexity.POracle_subset_NPOracle`. -/
theorem NPOracle_EXPCOM_eq_EXP : NPOracle EXPCOM = EXP := by
  sorry

/-- **Relative to `EXPCOM`, determinism and nondeterminism coincide**:
`P^EXPCOM = NP^EXPCOM` — the `A` half of the Baker-Gill-Solovay theorem.
[AB09, Example 3.6(3), cited by the proof of Theorem 3.7]

**Proof sketch.** Chain `Complexity.POracle_EXPCOM_eq_EXP` with the inverse of
`Complexity.NPOracle_EXPCOM_eq_EXP`. -/
theorem POracle_EXPCOM_eq_NPOracle_EXPCOM : POracle EXPCOM = NPOracle EXPCOM := by
  sorry

end Complexity

```


## ===== TCSlib/Complexity/Diagonalization/Relativization.lean =====

```
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

```


## ===== TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.Uncomputability.Halting

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A function that is not time-constructible

[AB09, Exercise 3.5]: not every function is time-constructible. Stated
non-trivially: `Complexity.TimeConstructible` already packages the growth
condition `∀ n, n ≤ T n`, so a function violating that (`T = 0`, say) fails
for a vacuous reason; the statement below therefore demands a function
*dominating the identity* that still fails constructibility, pinning the
failure on the computability half — a constructibility witness for the
exhibited `T` would decide the halting problem.

## Design

* The witness oscillates between `n` and `n + 1` according to the halting
  function `Complexity.HALT` at the campaign's fixed effective scheme
  `Complexity.TimeHierarchy.code` (reused, not re-chosen), evaluated on the
  `n`-th binary string in the length-lexicographic (dyadic) order. The
  definition is classical and noncomputable — legitimate, since it lives
  inside an existence proof.
* The refutation uses only the *computability* of a constructibility witness
  (a machine computing `(T |x|).bits` on every input), not its time bound:
  `Complexity.Computable` carries no clock, so even the exponentially long
  intermediate strings of the reduction are harmless.

## Main results (sorried; phase-P3.2 statement)

* `Complexity.exists_not_timeConstructible` — some `T` with `∀ n, n ≤ T n` is
  not time-constructible. [AB09, Exercise 3.5]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Chapter 3, Exercise 3.5; §1.5.1,
  Theorem 1.11.)
-/

namespace Complexity

open Turing

/-- **Not every function is time-constructible** [AB09, Exercise 3.5]: there
is a function `T` dominating the identity (`∀ n, n ≤ T n` — so the failure is
not the vacuous growth-condition one, see the module docstring) that is not
time-constructible.

**Proof sketch.** Fix the campaign's effective scheme
`c := Complexity.TimeHierarchy.code` and the length-lexicographic (dyadic)
enumeration `str : ℕ → List Bool` of binary strings — the rank of a string
`s` is the value of `s` with a `1` prepended, read in binary, minus one, so
rank and un-rank are both bit-rewrites. Define, classically,

  `T n := n + (if HALT c.toMachineCode (str n) = true then 1 else 0)`.

Then `∀ n, n ≤ T n` by construction. Suppose `TimeConstructible T` held, with
witness machine `M` computing `(T |x|).bits` on every input `x` (the clock
`c₀ · (T n + 1)` of `Complexity.TimeConstructible` is not even needed — only
the witness's totality). Then `fun s => [HALT c.toMachineCode s]` would be
computable, contradicting `Complexity.HALT_not_computable c`: on input `s`,
(i) compute the rank word `(rank s).bits` (the dyadic bit-rewrite — the
string-of-index bridge obligation); (ii) emit a string of length `rank s`,
say `1^(rank s)`, by a binary-countdown unary emitter (the
`TimeHierarchy.ClockMachine`/`ClockLoop` counter precedent;
`Complexity.Computable` has no time bound, so the exponential length is
harmless); (iii) run `M` on it, producing `(T (rank s)).bits`; (iv) compare
that word against `(rank s).bits` (equality-test tail,
`Turing.FinTM.computesFunInTime_ifEq` precedent — for an even rank this is
[AB09]'s "read the low bit of `(T n).bits`", and the full equality test also
covers the odd-rank carry), outputting `[true]` exactly when the two differ,
i.e. when `T (rank s) = rank s + 1`, i.e. when `HALT c.toMachineCode s =
true`. Assemble the stages with `Turing.FinTM.exists_comp_partial`, collapsing
intermediate outputs by determinism (`Turing.FinTM.ComputesInTime.output_unique`),
exactly as in `Complexity.UC_computable_of_HALT_computable`. Fill obligations,
named for the brief: the rank machine and the unary emitter (i)-(ii); the
comparison tail (iv); the composition assembly; and the final classical case
split on `HALT` identifying the composite's output with the halting bit. -/
theorem exists_not_timeConstructible :
    ∃ T : ℕ → ℕ, (∀ n, n ≤ T n) ∧ ¬TimeConstructible T := by
  sorry

end Complexity

```


## ===== TCSlib/Complexity/Diagonalization.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.OracleAgreement
import TCSlib.Complexity.Diagonalization.EXPCOM
import TCSlib.Complexity.Diagonalization.Relativization
import TCSlib.Complexity.Diagonalization.NotTimeConstructible

/-!
# Diagonalization: relativization and its limits

[AB09, §3.4]: the Baker-Gill-Solovay relativization theorem and its
supporting cast. The headline results are `Complexity.baker_gill_solovay`
(oracles `A`, `B` with `P^A = NP^A` and `P^B ≠ NP^B` — [AB09, Theorem 3.7],
[BGS75]), the `EXPCOM` identities `Complexity.POracle_EXPCOM_eq_EXP` /
`Complexity.NPOracle_EXPCOM_eq_EXP` ([AB09, Example 3.6(3)]), and the
non-time-constructible function `Complexity.exists_not_timeConstructible`
([AB09, Exercise 3.5]).

## Contents

- `TuringMachine.OracleAgreement` (the locality layer, housed with the oracle
  machine model): submitted-query lists `queriesWithin`/`queriesAlong`, and
  agreement of runs under oracles that agree on the queries (deterministic
  and nondeterministic, length-locality and query-set forms)
- `Diagonalization.EXPCOM`: the `EXPCOM` oracle and the chain
  `EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP` with its three identities
- `Diagonalization.Relativization`: the unary witness language `U_B`,
  `U_B ∈ NP^B`, the extrinsically clocked enumeration of deterministic
  finite oracle machines, the stage construction, and Theorem 3.7
- `Diagonalization.NotTimeConstructible`: a function dominating the identity
  that is not time-constructible

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4.)
* [BGS75] T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP
  question*, SIAM Journal on Computing 4(4), 1975.
-/

```


## ===== TCSlib/Complexity/TuringMachine/OracleFinite.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Oracle
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bundled finite oracle Turing machines

The bundled finite layer over `Turing.OracleTM`, mirroring `Turing.FinTM` over
`Turing.MultiTapeTM`: a `FinOracleTM` carries its state type with `Fintype` and
`DecidableEq` instances **as data**, and — unlike the raw layer — carries
`Turing.OracleTM.WellFormed` as a field, so that oracle complexity classes
(`Complexity.POracle`, `Complexity.NPOracle`; [AB09, Definition 3.5]) can never
quantify over a machine whose three special states collide. This discharges the
Chapter-1 obligation that "oracle complexity classes will introduce a finite
oracle-machine bundle before they are defined" (`AroraBarakChapter1Plan.md` §2).

## Design

* `WellFormed` is bundled, finiteness is bundled, the alphabet stays an explicit
  parameter — exactly the `FinTM` conventions. `q₀ = qQuery` remains deliberately
  allowed (such a machine submits the empty query on its first step).
* Time bounds are the only resource at this layer, mirroring
  `Turing.FinTM.ComputesInTime`; an oracle *space* measure is deliberately not
  introduced here (the chapters-3-4 campaign defines space for plain and
  nondeterministic machines first — `AroraBarakChapters3-4Plan.md` §2.4).
* The embedding of a plain bundled machine is `Turing.FinTM.toFinOracleTM`, the
  bundled form of `Turing.OracleTM.ofMultiTapeTM`; its behavior is
  oracle-independent and agrees with the plain machine
  (`toFinOracleTM_computesInTime`, proved here as a definitional-unfolding bridge
  over the audited `Turing.OracleTM.computesInTime_ofMultiTapeTM` — a
  skeleton-time proof, declared part of the audited surface per `workflow.md` §2).

## Main definitions

* `Turing.FinOracleTM` — the bundled, well-formed finite oracle machine.
  [AB09, Definition 3.4]
* `Turing.FinOracleTM.ComputesInTime`, `Turing.FinOracleTM.DecidesInTime` —
  output/decision within a time bound, relative to an oracle. [AB09, §3.4]
* `Turing.FinTM.toFinOracleTM` — a plain bundled machine as a bundled oracle
  machine that never queries.

## Main results

* `Turing.FinTM.toFinOracleTM_computesInTime` — the embedded machine's
  input/output behavior and time bounds are oracle-independent and agree with
  the plain machine's.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Definitions 3.4-3.5.)
-/

namespace Turing

/-- A finite, well-formed oracle Turing machine over the alphabet `Symbol`: the raw
`Turing.OracleTM` bundled with `Fintype`/`DecidableEq` instances for its state type (as
data, since machine encodings must enumerate transition tables) and with the
`Turing.OracleTM.WellFormed` discipline (the three special states are pairwise
distinct) as a field. All oracle complexity classes are stated over this layer.
[AB09, Definition 3.4] -/
structure FinOracleTM (Symbol : Type) : Type 1 where
  /-- number of ordinary work tapes; the query tape is the extra work tape, giving
  `k + 1` work tapes in configurations -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible -/
  [decEqState : DecidableEq State]
  /-- the underlying oracle machine -/
  tm : OracleTM k Symbol State
  /-- the three special states are pairwise distinct — bundled so that no oracle
  complexity class can forget it -/
  wf : tm.WellFormed

namespace FinOracleTM

attribute [instance] FinOracleTM.fintypeState FinOracleTM.decEqState

variable {Symbol : Type}

/-- `M` with oracle `O` halts on `input` within `t` steps with `output` on its output
tape — the bundled form of `Turing.OracleTM.ComputesInTime`, mirroring
`Turing.FinTM.ComputesInTime` (time-only). -/
def ComputesInTime (M : FinOracleTM Symbol) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) : Prop :=
  M.tm.ComputesInTime O input output t

/-- The machine `M`, with oracle `O`, decides the language `L` within time `T`: on
every input `x` it halts within `T |x|` steps with output `[true]` if `x ∈ L` and
`[false]` otherwise — the oracle counterpart of `Turing.FinTM.DecidesInTime`.
[AB09, §3.4 with Definition 3.5] -/
def DecidesInTime (M : FinOracleTM Bool) (O : Language Bool) (L : Language Bool)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime O x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end FinOracleTM

/-- A plain bundled machine as a bundled oracle machine that never queries: the
`FinTM` layer of `Turing.OracleTM.ofMultiTapeTM`, with the three special states
adjoined to the state type and well-formedness supplied by
`Turing.OracleTM.ofMultiTapeTM_wellFormed`. -/
def FinTM.toFinOracleTM {Symbol : Type} (M : FinTM Symbol) : FinOracleTM Symbol :=
  ⟨M.k, M.State ⊕ Fin 3, OracleTM.ofMultiTapeTM M.tm,
    OracleTM.ofMultiTapeTM_wellFormed M.tm⟩

/-- The embedded plain machine's behavior is oracle-independent and agrees with the
original: under **every** oracle `O`, the embedding computes `output` from `input`
within `t` steps iff the plain machine does. The bundled form of
`Turing.OracleTM.computesInTime_ofMultiTapeTM`, through
`Turing.FinTM.computesInTime_iff`; this is the sanity theorem behind
`Complexity.P_subset_POracle`. -/
theorem FinTM.toFinOracleTM_computesInTime {Symbol : Type} (M : FinTM Symbol)
    (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) :
    M.toFinOracleTM.ComputesInTime O input output t ↔ M.ComputesInTime input output t := by
  rw [FinTM.computesInTime_iff]
  exact OracleTM.computesInTime_ofMultiTapeTM M.tm O input output t

end Turing

```


## ===== TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.OracleFinite
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic oracle Turing machines

[AB09, Definition 3.4] closes with "Nondeterministic oracle TMs are defined
similarly." This module is that definition: the binary-choice nondeterministic
machine of `TCSlib.Complexity.TuringMachine.Nondeterministic` equipped with the
query tape and query/answer states of `TCSlib.Complexity.TuringMachine.Oracle`.
It exists for `Complexity.NPOracle` ([AB09, Definition 3.5]) and for the
relativization theorem ([AB09, Theorem 3.7], phase P3.2).

## Design

* **The oracle answer consumes a choice bit but ignores it.** A step in state
  `qQuery` resolves the query exactly as `Turing.OracleTM.step` does — move to
  `qYes`/`qNo` according to membership of the current query string, tapes and
  heads unchanged — under **either** choice bit. Choice words therefore have one
  bit per step uniformly, keeping the choice-word run algebra (and the
  certificate reading of choice words, [AB09, §2.1.2]) identical to the plain
  NDTM's. The alternative (query steps consume no bit) would make branch length
  input-dependent in a way nothing downstream wants.
* Everything else mirrors the two parents: `Symbol`/`State` unconstrained at the
  raw layer, the bundled finite layer (`Turing.FinOracleNDTM`, in
  `TCSlib.Complexity.TuringMachine.OracleFinite`'s style) carries
  `Fintype`/`DecidableEq` as data and well-formedness as a field.
* The three-state distinctness discipline is `Turing.OracleNDTM.WellFormed`,
  verbatim the deterministic `Turing.OracleTM.WellFormed` rationale
  (`audits/phase1-findings.md`, finding 2).

## Main definitions

* `Turing.OracleNDTM` — the binary-choice oracle machine. [AB09, Def 3.4, last
  sentence]
* `Turing.OracleNDTM.WellFormed` — pairwise-distinct special states.
* `Turing.OracleNDTM.stepWith`, `Turing.OracleNDTM.runWith` — one step under a
  choice bit and an oracle; the run under a choice word.
* `Turing.OracleNDTM.HaltsWithin`, `Turing.FinOracleNDTM.AcceptsWithin`,
  `Turing.FinOracleNDTM.DecidesInTime` — all-branch halting, existential
  acceptance, and decision, mirroring the `NTIME` layer.
* `Turing.FinOracleNDTM` — the bundled finite, well-formed layer.
* `Turing.OracleTM.toOracleNDTM`, `Turing.FinOracleTM.toFinOracleNDTM` — a
  deterministic oracle machine as one that ignores its choices.

## Main results

* `Turing.OracleNDTM.runWith_append`, `Turing.OracleNDTM.runWith_of_halt` — the
  choice-word run algebra (proved; pure unfoldings mirroring the plain NDTM's,
  declared part of the audited surface per `workflow.md` §2).
* `Turing.OracleNDTM.HaltsWithin.mono` — all-branch halting is monotone (proved,
  same unfolding argument as `Turing.NDTM.HaltsWithin.mono`).
* `Turing.OracleTM.toOracleNDTM_runWith` — the embedded deterministic oracle
  machine ignores its choices (sorried; the lockstep obligation of phase P3.1).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Definitions 3.4-3.5; §2.1.2.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- A binary-choice nondeterministic oracle Turing machine: two total transition
functions on `k + 1` work tapes (the last being the query tape, as in
`Turing.OracleTM`), an initial state, and the designated `qQuery`/`qYes`/`qNo`
states. [AB09, Definition 3.4: "Nondeterministic oracle TMs are defined
similarly"] -/
structure OracleNDTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- entering this state submits the query tape's contents to the oracle -/
  qQuery : State
  /-- the state the oracle answer step moves to on a positive answer -/
  qYes : State
  /-- the state the oracle answer step moves to on a negative answer -/
  qNo : State
  /-- the two transition functions, indexed by the nondeterministic choice bit;
  consulted in every state except `qQuery` -/
  tr (choice : Bool) (q : State) (input : Option Symbol)
    (work : Fin (k + 1) → Option Symbol) : Action (k + 1) Symbol State

namespace OracleNDTM

variable {N : OracleNDTM k Symbol State}

/-- Well-formedness: the query state and the two answer states are pairwise
distinct — verbatim the `Turing.OracleTM.WellFormed` discipline and rationale
(`q₀ = qQuery` stays deliberately allowed). -/
structure WellFormed (N : OracleNDTM k Symbol State) : Prop where
  /-- the query state is not the positive-answer state -/
  qQuery_ne_qYes : N.qQuery ≠ N.qYes
  /-- the query state is not the negative-answer state -/
  qQuery_ne_qNo : N.qQuery ≠ N.qNo
  /-- the two answer states are distinct -/
  qYes_ne_qNo : N.qYes ≠ N.qNo

open Classical in
/-- One step under the choice bit `b` and the oracle `O`: in state `qQuery` the
machine resolves the query exactly as the deterministic oracle step does — the
choice bit is consumed but ignored — and in every other live state it applies the
action selected by `tr b`. Halting is absorbing under every choice. -/
noncomputable def stepWith (N : OracleNDTM k Symbol State) (O : Language Symbol)
    (b : Bool) (cfg : Cfg (k + 1) Symbol State input) : Cfg (k + 1) Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q =>
    if q = N.qQuery then
      { cfg with state := some (if OracleTM.queryString cfg ∈ O then N.qYes else N.qNo) }
    else
      (N.tr b q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration: all `k + 1` work tapes (including the query tape)
blank, input head on the first symbol. -/
@[simp]
def initCfg (N : OracleNDTM k Symbol State) (input : List Symbol) :
    Cfg (k + 1) Symbol State input :=
  Cfg.init N.q₀ input

/-- The configuration reached from `cfg` by running under the choice word `w` with
oracle `O`, one choice bit per step, consumed left to right. -/
noncomputable def runWith (N : OracleNDTM k Symbol State) (O : Language Symbol) :
    List Bool → Cfg (k + 1) Symbol State input → Cfg (k + 1) Symbol State input
  | [], cfg => cfg
  | b :: w, cfg => N.runWith O w (N.stepWith O b cfg)

/-- The empty choice word runs zero steps. -/
@[simp]
lemma runWith_nil (O : Language Symbol) {cfg : Cfg (k + 1) Symbol State input} :
    N.runWith O [] cfg = cfg := rfl

/-- Consuming one choice bit is one step. -/
lemma runWith_cons (O : Language Symbol) {b : Bool} {w : List Bool}
    {cfg : Cfg (k + 1) Symbol State input} :
    N.runWith O (b :: w) cfg = N.runWith O w (N.stepWith O b cfg) := rfl

/-- Running under `w ++ w'` is running under `w`, then under `w'` from the reached
configuration — the oracle counterpart of `Turing.NDTM.runWith_append`. -/
lemma runWith_append (O : Language Symbol) (w w' : List Bool)
    (cfg : Cfg (k + 1) Symbol State input) :
    N.runWith O (w ++ w') cfg = N.runWith O w' (N.runWith O w cfg) := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih => rw [List.cons_append, runWith_cons, runWith_cons, ih]

/-- Stepping a halted configuration is the identity, under either choice and any
oracle. -/
@[simp]
lemma stepWith_of_halt (O : Language Symbol) {b : Bool}
    {cfg : Cfg (k + 1) Symbol State input} (h : cfg.state = none) :
    N.stepWith O b cfg = cfg := by
  unfold stepWith
  rw [h]

/-- Running from a halted configuration stays there, under every choice word. -/
@[simp]
lemma runWith_of_halt (O : Language Symbol) (cfg : Cfg (k + 1) Symbol State input)
    (h : cfg.state = none) {w : List Bool} : N.runWith O w cfg = cfg := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [runWith_cons, stepWith_of_halt O h]; exact ih

/-- The machine halts on `input` within `t` steps along **every** branch, relative
to the oracle `O` — [AB09]'s all-branch totality condition, rendered over choice
words of length exactly `t` exactly as in `Turing.NDTM.HaltsWithin`. -/
def HaltsWithin (N : OracleNDTM k Symbol State) (O : Language Symbol)
    (input : List Symbol) (t : ℕ) : Prop :=
  ∀ w : List Bool, w.length = t → (N.runWith O w (N.initCfg input)).state = none

/-- All-branch halting is monotone in the time bound.

**Proof sketch.** Identical to `Turing.NDTM.HaltsWithin.mono`: split `w` at `t`
(`List.take_append_drop`), the run under `w.take t` is halted by hypothesis,
`runWith_append` factors the run and `runWith_of_halt` absorbs the remainder. -/
theorem HaltsWithin.mono {N : OracleNDTM k Symbol State} {O : Language Symbol}
    {input : List Symbol} {t t' : ℕ} (h : N.HaltsWithin O input t) (hle : t ≤ t') :
    N.HaltsWithin O input t' := by
  intro w hw
  have hlen : (w.take t).length = t := List.length_take_of_le (hle.trans_eq hw.symm)
  have hhalt := h (w.take t) hlen
  have hrun := runWith_append (N := N) O (w.take t) (w.drop t) (N.initCfg input)
  rw [List.take_append_drop, runWith_of_halt O _ hhalt] at hrun
  rw [hrun]
  exact hhalt

end OracleNDTM

/-- A nondeterministic oracle machine bundled with a finite state type and the
well-formedness discipline, mirroring `Turing.FinOracleTM`: all nondeterministic
oracle complexity definitions (`Complexity.NPOracle`) are stated over this layer. -/
structure FinOracleNDTM (Symbol : Type) : Type 1 where
  /-- number of ordinary work tapes (the query tape is the extra one) -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible -/
  [decEqState : DecidableEq State]
  /-- the underlying nondeterministic oracle machine -/
  tm : OracleNDTM k Symbol State
  /-- the three special states are pairwise distinct -/
  wf : tm.WellFormed

namespace FinOracleNDTM

attribute [instance] FinOracleNDTM.fintypeState FinOracleNDTM.decEqState

/-- The machine `N`, with oracle `O`, *accepts* `x` within `t` steps: some choice
word of length `t` leaves it halted with output exactly `[true]` — mirroring
`Turing.FinNDTM.AcceptsWithin` (output-based acceptance, same deviation record). -/
def AcceptsWithin (N : FinOracleNDTM Bool) (O : Language Bool) (x : List Bool)
    (t : ℕ) : Prop :=
  ∃ w : List Bool, w.length = t ∧
    (N.tm.runWith O w (N.tm.initCfg x)).state = none ∧
    (N.tm.runWith O w (N.tm.initCfg x)).output = [true]

/-- Acceptance is monotone in the branch length.

**Proof sketch.** Pad the accepting word with `false`s; `runWith_append` and
`runWith_of_halt` absorb the padding, as in `Turing.FinNDTM.AcceptsWithin.mono`. -/
theorem AcceptsWithin.mono {N : FinOracleNDTM Bool} {O : Language Bool}
    {x : List Bool} {t t' : ℕ} (h : N.AcceptsWithin O x t) (hle : t ≤ t') :
    N.AcceptsWithin O x t' := by
  obtain ⟨w, hw, hhalt, hout⟩ := h
  refine ⟨w ++ List.replicate (t' - t) false, ?_, ?_⟩
  · rw [List.length_append, List.length_replicate, hw, Nat.add_sub_of_le hle]
  · rw [OracleNDTM.runWith_append, OracleNDTM.runWith_of_halt O _ hhalt]
    exact ⟨hhalt, hout⟩

/-- The machine `N`, with oracle `O`, decides `L` within time `T`: on every input,
every branch of length `T |x|` has halted, and `x ∈ L` exactly when some such
branch accepts — mirroring `Turing.FinNDTM.DecidesInTime`.
[AB09, Definition 3.5, nondeterministic half] -/
def DecidesInTime (N : FinOracleNDTM Bool) (O : Language Bool) (L : Language Bool)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    N.tm.HaltsWithin O x (T x.length) ∧ (x ∈ L ↔ N.AcceptsWithin O x (T x.length))

end FinOracleNDTM

/-- A deterministic oracle machine as a nondeterministic one whose two transition
functions coincide — the oracle counterpart of `Turing.MultiTapeTM.toNDTM`, with
the special states carried over verbatim. -/
def OracleTM.toOracleNDTM (M : OracleTM k Symbol State) : OracleNDTM k Symbol State :=
  ⟨M.q₀, M.qQuery, M.qYes, M.qNo, fun _ => M.tr⟩

/-- The embedding preserves well-formedness (the special states are unchanged). -/
theorem OracleTM.toOracleNDTM_wellFormed {M : OracleTM k Symbol State}
    (h : M.WellFormed) : M.toOracleNDTM.WellFormed :=
  ⟨h.qQuery_ne_qYes, h.qQuery_ne_qNo, h.qYes_ne_qNo⟩

/-- The embedded deterministic oracle machine ignores its choices: running
`toOracleNDTM` under any choice word `w` with oracle `O` is running the original
machine for `|w|` steps with the same oracle — the oracle counterpart of
`Turing.MultiTapeTM.toNDTM_runWith`, and the engine of
`Complexity.POracle_subset_NPOracle`.

**Proof sketch.** Induction on `w` generalizing the configuration. One
`Turing.OracleNDTM.stepWith` of `toOracleNDTM` and one `Turing.OracleTM.step`
are the same match on the state: halted branches are both the identity; in state
`qQuery` both resolve the query through `Turing.OracleTM.queryString` with tapes
unchanged (the choice bit is ignored by construction); in any other live state
both apply the action `M.tr q …`, since `toOracleNDTM.tr b = M.tr` for either
`b`. The cons case is `Turing.OracleNDTM.runWith_cons` against the successor
unfolding of `Turing.OracleTM.runFrom` (`Function.iterate_succ_apply`). -/
theorem OracleTM.toOracleNDTM_runWith (M : OracleTM k Symbol State)
    (O : Language Symbol) {input : List Symbol} (w : List Bool)
    (cfg : Cfg (k + 1) Symbol State input) :
    M.toOracleNDTM.runWith O w cfg = M.runFrom O cfg w.length := by
  sorry

/-- A bundled deterministic oracle machine as a bundled nondeterministic one, with
the same tapes, state type, and special states. -/
def FinOracleTM.toFinOracleNDTM {Symbol : Type} (M : FinOracleTM Symbol) :
    FinOracleNDTM Symbol :=
  ⟨M.k, M.State, M.tm.toOracleNDTM, OracleTM.toOracleNDTM_wellFormed M.wf⟩

end Turing

```


## ===== TCSlib/Complexity/ClassOracle/Classes.lean =====

```
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
  `NP = ⋃ c, NTIME (n^c)` is Theorem 2.6; but [AB09, Definition 3.5] *defines*
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
on the current query string. (i) The query string lives on a work tape, so `D`
is run on a **virtual input** read from that tape — the virtual-input technique
of the universal machine (`TCSlib.Complexity.TuringMachine.UniversalStartup`
precedent), with `D`'s run captured (W1) so the simulation's output stays
silent; (ii) each simulated query costs `O(d·(q+1)^e)` with `q ≤` the elapsed
budget (`Turing.OracleTM.queryString_length_le`), so the total is polynomial
with exponent `k·e + O(1)`; (iii) the step-by-step simulation of `M`'s
non-query steps is lockstep (the `Turing.OracleTM.step_eq_of_ne_qQuery`
oracle-independence away from queries). The composite bound sits inside
`P`'s `⋃ c` by the usual `PolyBound` absorption. -/
theorem POracle_eq_P_of_mem_P {O : Language Bool} (h : O ∈ P) : POracle O = P := by
  sorry

end Complexity

```


## ===== TCSlib/Complexity/ClassOracle/SATOracle.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassOracle.Classes
import TCSlib.Complexity.ClassNP.CoNP
import TCSlib.Complexity.CookLevin.Hardness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `SAT` oracle: Example 3.6(1) and the `NP ⊆ P^SAT` sanity theorem

[AB09, Example 3.6(1)]: with oracle access to `SAT`, the complement of `SAT` is
decidable in polynomial time — query the oracle on the input and give the
opposite answer. Together with `SAT`'s `NP`-hardness (the Cook-Levin theorem,
`Complexity.SAT_NPHard`), the same one-query pattern puts all of `NP`, and by
complementation all of `coNP`, inside `P^SAT`. These are the standing sanity
checks that the `Complexity.POracle` interface composes with the chapter-2
surface before the relativization theorem (phase P3.2) builds on it.

## Main results (all sorried; phase-P3.1 statements)

* `Complexity.compl_SAT_mem_POracle_SAT` — `SATᶜ ∈ P^SAT`.
  [AB09, Example 3.6(1)]
* `Complexity.NP_subset_POracle_SAT` — `NP ⊆ P^SAT`.
* `Complexity.coNP_subset_POracle_SAT` — `coNP ⊆ P^SAT`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4, Example 3.6(1).)
-/

namespace Complexity

open Turing

/-- **With a `SAT` oracle, unsatisfiability is easy**: `SATᶜ ∈ P^SAT` — query
the oracle on the input formula and answer the opposite.
[AB09, Example 3.6(1), with the book's `co-SAT` rendered as the set complement
`SATᶜ`, so no formula-syntax carrier is involved]

**Proof sketch.** `Complexity.oracle_mem_POracle` gives `SAT ∈ P^SAT`;
`Complexity.compl_mem_POracle` flips the answer. -/
theorem compl_SAT_mem_POracle_SAT : (SATᶜ : Language Bool) ∈ POracle SAT := by
  sorry

/-- **Everything in `NP` is one `SAT`-query away**: `NP ⊆ P^SAT`.

**Proof sketch.** For `L ∈ NP`, Cook-Levin (`Complexity.SAT_NPHard`) gives
`L ≤ₚ SAT`, and `Complexity.mem_POracle_of_polyTimeReducible` turns the
reduction into a one-query oracle machine. -/
theorem NP_subset_POracle_SAT : NP ⊆ POracle SAT := by
  sorry

/-- **And so is everything in `coNP`**: `coNP ⊆ P^SAT`.

**Proof sketch.** `L ∈ coNP` means `Lᶜ ∈ NP`; `Complexity.NP_subset_POracle_SAT`
puts `Lᶜ` in `P^SAT`, and `Complexity.compl_mem_POracle` closes under the
complement back to `L`. -/
theorem coNP_subset_POracle_SAT : coNP ⊆ POracle SAT := by
  sorry

end Complexity

```


## ===== TCSlib/Complexity/TuringMachine/Oracle.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle Turing machines

An oracle Turing machine [AB09, §3.4, Definition 3.4; pulled forward to Chapter 1 to
validate the model architecture] is a multi-tape machine with one additional designated
*query tape* and three designated states `qQuery`, `qYes`, `qNo`. Whenever the machine
enters `qQuery`, the string currently written on the query tape is submitted to the oracle
`O`: in a single step the machine moves to `qYes` if the query is in `O` and to `qNo`
otherwise, with all tapes and heads unchanged.

## Design

This file is the architectural test of the `Action`/`Action.apply` split: an oracle machine
reuses the configurations `Turing.Cfg (k + 1)` (the query tape is the extra work tape, at
index `Fin.last k`) and the action application of the plain model, and differs *only* in how
the next action is chosen — the step function is parametrized by the oracle
`O : Language Symbol`. Time and space measures therefore transfer unchanged.

Definitional choices worth auditing:

* **The query string** (`OracleTM.queryString`) is read from cell `0` of the query tape
  rightward up to (excluding) the first blank cell; if the whole nonnegative half-tape is
  blank-free (possible for an arbitrary configuration, though not for one reachable from an
  initial configuration), the query is defined to be `[]`. [AB09] leaves the extraction
  convention implicit; this is one concrete faithful reading.
* **The answer step** changes only the state; heads and tapes stay put. Some texts
  instead erase the query tape on each answer. The two conventions are equivalent up to
  *polynomial* overhead, but **not** constant overhead: computing the parity of `n`
  distinct length-`n` queries takes `O(n)` steps with a persistent tape and `Ω(n²)`
  steps with auto-erasure (`audits/phase1-findings.md`, finding 3, case 12).
  Consequently, exact `DTIME`-level bounds must never be transferred across this
  convention; class-level results (`Pᴼ` etc.) are unaffected.
* `qYes`/`qNo` are ordinary states from the machine's point of view (its transition
  function handles them); only `qQuery` triggers special behavior. The machine may query
  repeatedly. This reading presumes the three special states are pairwise distinct,
  which the raw structure does not enforce (e.g. with `qYes = qQuery` the machine
  re-queries forever after a positive answer): results at the faithful interface assume
  `OracleTM.WellFormed`. Note that
  `q₀ = qQuery` is legitimate and deliberately allowed (the machine then submits the
  empty query on its first step).

## Main definitions

* `Turing.OracleTM` — the oracle machine. [AB09, Definition 3.4]
* `Turing.OracleTM.WellFormed` — the three special states are pairwise distinct; the
  standing hypothesis of the faithful interface (oracle complexity classes will require
  it).
* `Turing.OracleTM.step`, `Turing.OracleTM.runFrom` — semantics relative to an oracle.
* `Turing.OracleTM.ComputesInTime` — output and time bound relative to an oracle.
* `Turing.Action.extend`, `Turing.Cfg.embedOracle`, `Turing.OracleTM.ofMultiTapeTM` —
  the embedding of plain machines as oracle machines that never query (state renaming
  via `Turing.Action.mapState`, now in `TCSlib.Complexity.TuringMachine.StateRenaming`).
* `Turing.OracleTM.plainEmptyOracle` — the converse direction: an oracle machine run
  with the empty oracle, as a plain `k + 1`-tape machine in exact lockstep.

## Main results (sanity checks for the architecture)

* `Turing.OracleTM.step_eq_of_ne_qQuery` — away from `qQuery`, the step does not depend
  on the oracle.
* `Turing.OracleTM.ofMultiTapeTM_wellFormed` — the embedding produces well-formed
  machines.
* `Turing.OracleTM.runFrom_ofMultiTapeTM` — an embedded plain machine runs in lockstep
  with the original, under every oracle.
* `Turing.OracleTM.computesInTime_ofMultiTapeTM` — hence its input/output behavior and
  time bounds are oracle-independent and agree with the plain machine's.
* `Turing.OracleTM.runFrom_plainEmptyOracle` — the empty-oracle elimination runs in
  exact lockstep.
* `Turing.OracleTM.queryString_length_le` — in an initialized run, the query after `t`
  steps has length at most `t`.
* `Turing.OracleTM.runFrom_workTapes_blank` — in an initialized run, cells at distance
  `≥ t` are still blank after `t` steps; the certificate that the no-blank fallback in
  `queryString` is unreachable from initialization.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4: oracle machines; Definition 3.4.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- An oracle Turing machine with `k` ordinary work tapes, one query tape (the work tape
of index `Fin.last k` in its configurations `Cfg (k + 1)`), and designated query and
answer states. Finiteness of `State` is deferred exactly as for `MultiTapeTM`, and so is
distinctness of the three special states: the raw structure allows them to coincide
(with degenerate behavior, e.g. `qYes = qQuery` re-queries forever after a positive
answer), and the faithful interface imposes `OracleTM.WellFormed`.
[AB09, Definition 3.4] -/
structure OracleTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- entering this state submits the query tape's contents to the oracle -/
  qQuery : State
  /-- the state the oracle answer step moves to on a positive answer -/
  qYes : State
  /-- the state the oracle answer step moves to on a negative answer -/
  qNo : State
  /-- transition function on the `k + 1` work tapes (the last being the query tape);
  consulted in every state except `qQuery` -/
  tr (q : State) (input : Option Symbol) (work : Fin (k + 1) → Option Symbol) :
    Action (k + 1) Symbol State

namespace OracleTM

variable {M : OracleTM k Symbol State}

/-- Well-formedness of an oracle machine: the query state and the two answer states are
pairwise distinct. Without this, the advertised semantics degenerates: with
`qYes = qQuery` a positive answer re-queries the unchanged tape forever (a negative
answer may still reach a distinct `qNo` and halt normally), and with all three states
collapsed the machine loops once the common query state is reached (an initial state
elsewhere can still halt via the table without ever querying). Moreover `qYes = qNo`
alone makes the step function — hence every run — oblivious to the oracle. This is the
standing hypothesis of the faithful oracle interface —
oracle complexity classes will require it. `q₀ = qQuery` is deliberately allowed: such a
machine simply submits the empty query on its first step.
(`audits/phase1-findings.md`, finding 2.) -/
structure WellFormed (M : OracleTM k Symbol State) : Prop where
  /-- the query state is not the positive-answer state -/
  qQuery_ne_qYes : M.qQuery ≠ M.qYes
  /-- the query state is not the negative-answer state -/
  qQuery_ne_qNo : M.qQuery ≠ M.qNo
  /-- the two answer states are distinct -/
  qYes_ne_qNo : M.qYes ≠ M.qNo

/-- The index of the query tape among the `k + 1` work tapes. -/
def queryTapeIdx (k : ℕ) : Fin (k + 1) := Fin.last k

open Classical in
/-- The query string of a configuration: the contents of the query tape from cell `0`
rightward, up to (excluding) the first blank cell. If no blank cell exists on the
nonnegative half-tape — impossible in configurations reachable from an initial
configuration, but possible for an arbitrary one — the query is `[]`. -/
noncomputable def queryString (cfg : Cfg (k + 1) Symbol State input) : List Symbol :=
  if h : ∃ n : ℕ, cfg.workTapes (queryTapeIdx k) (n : ℤ) = none then
    (List.range (Nat.find h)).filterMap fun n => cfg.workTapes (queryTapeIdx k) (n : ℤ)
  else []

open Classical in
/-- One step of the oracle machine `M` relative to the oracle `O`. In state `qQuery` the
machine moves to `qYes` or `qNo` according to whether the current query string is in `O`,
leaving tapes, head positions and output unchanged; in every other state it steps by its
transition function exactly like a plain machine. [AB09, §3.4] -/
noncomputable def step (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) : Cfg (k + 1) Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q =>
    if q = M.qQuery then
      { cfg with state := some (if queryString cfg ∈ O then M.qYes else M.qNo) }
    else
      (M.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration of an oracle machine: all `k + 1` work tapes (including the
query tape) blank. -/
@[simp]
def initCfg (M : OracleTM k Symbol State) (input : List Symbol) :
    Cfg (k + 1) Symbol State input :=
  Cfg.init M.q₀ input

/-- The configuration reached by running `M` with oracle `O` for `t` steps from `cfg`. -/
noncomputable def runFrom (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ) : Cfg (k + 1) Symbol State input :=
  (M.step O)^[t] cfg

/-- `M` with oracle `O` halts on `input` within `t` steps with `output` on its output
tape. Time-only, mirroring `Turing.FinTM.ComputesInTime`. -/
def ComputesInTime (M : OracleTM k Symbol State) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) : Prop :=
  (M.runFrom O (M.initCfg input) t).state = none ∧
  (M.runFrom O (M.initCfg input) t).output = output

/-- Away from the query state, a step of an oracle machine does not depend on the oracle. -/
theorem step_eq_of_ne_qQuery (O₁ O₂ : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} (h : cfg.state ≠ some M.qQuery) :
    M.step O₁ cfg = M.step O₂ cfg := by
  unfold step
  cases hs : cfg.state with
  | none => rfl
  | some q =>
    have hne : q ≠ M.qQuery := fun hq => h (by rw [hs, hq])
    dsimp only
    rw [if_neg hne, if_neg hne]

/-- Applying any action changes a work-tape cell only at the old head position. -/
private lemma apply_workTapes_eq_of_ne {k' : ℕ} (a : Action k' Symbol State)
    (cfg : Cfg k' Symbol State input) (i : Fin k') {z : ℤ}
    (hz : z ≠ cfg.workTapePos i) :
    (a.apply cfg).workTapes i z = cfg.workTapes i z := by
  dsimp only [Action.apply]
  rcases h : (a.workTapes i).1 with _ | s
  · rfl
  · exact Function.update_of_ne hz _ _

/-- A work-tape head moves by at most one cell in a single oracle step. -/
lemma workTapePos_step_le (M : OracleTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg (k + 1) Symbol State input) (i : Fin (k + 1)) :
    |(M.step O cfg).workTapePos i - cfg.workTapePos i| ≤ 1 := by
  unfold step
  split
  · simp
  · split
    · simp
    · exact workTapePos_apply_le _ cfg i

/-- An oracle step writes only at the old head position. -/
lemma workTapes_step_eq_of_ne (M : OracleTM k Symbol State) (O : Language Symbol)
    {cfg : Cfg (k + 1) Symbol State input} (i : Fin (k + 1)) {z : ℤ}
    (hz : z ≠ cfg.workTapePos i) :
    (M.step O cfg).workTapes i z = cfg.workTapes i z := by
  unfold step
  split
  · rfl
  · split
    · rfl
    · exact apply_workTapes_eq_of_ne _ cfg i hz

/-- The two run invariants of an initialized oracle run: after `t` steps every work
head is within distance `t` of the origin, and every cell at distance at least `t` is
still blank. -/
private lemma runFrom_workTapes_invariant (M : OracleTM k Symbol State)
    (O : Language Symbol) (x : List Symbol) : ∀ t : ℕ,
    (∀ i, |(M.runFrom O (M.initCfg x) t).workTapePos i| ≤ (t : ℤ)) ∧
    (∀ i (z : ℤ), (t : ℤ) ≤ |z| → (M.runFrom O (M.initCfg x) t).workTapes i z = none) := by
  intro t
  induction t with
  | zero =>
    constructor
    · intro i
      simp [runFrom]
    · intro i z _
      simp [runFrom]
  | succ t ih =>
    obtain ⟨hpos, hblank⟩ := ih
    have hstep : M.runFrom O (M.initCfg x) (t + 1) =
        M.step O (M.runFrom O (M.initCfg x) t) :=
      Function.iterate_succ_apply' _ _ _
    constructor
    · intro i
      rw [hstep]
      have h1 := M.workTapePos_step_le O (M.runFrom O (M.initCfg x) t) i
      have h2 := hpos i
      rw [abs_le] at h1 h2 ⊢
      omega
    · intro i z hz
      rw [hstep]
      have hz' : (t : ℤ) ≤ |z| := le_trans (by omega) hz
      have hne : z ≠ (M.runFrom O (M.initCfg x) t).workTapePos i := by
        intro hzeq
        have h2 := hpos i
        rw [← hzeq] at h2
        have h3 : ((t : ℤ) + 1) ≤ |z| := by exact_mod_cast hz
        have h4 := le_trans h3 h2
        omega
      rw [M.workTapes_step_eq_of_ne O i hne]
      exact hblank i z hz'

/-- In an initialized run, the query after `t` steps has length at most `t`. In
particular the no-blank fallback branch of `queryString` is unreachable from an initial
configuration.

**Proof sketch.** By induction on `t`, every write performed in the first `t` steps
happened at a head position of absolute value at most `t - 1` (heads start at `0` and
move at most one cell per step, `Turing.workTapePos_apply_le`). Hence cell `t` of the
query tape is still blank at time `t`, so the least-blank search in `queryString`
terminates at an index `≤ t`. -/
theorem queryString_length_le (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) :
    (queryString (M.runFrom O (M.initCfg x) t)).length ≤ t := by
  have hblank : (M.runFrom O (M.initCfg x) t).workTapes (queryTapeIdx k) ((t : ℕ) : ℤ) =
      none :=
    (runFrom_workTapes_invariant M O x t).2 _ _ (le_abs_self _)
  classical
  simp only [queryString]
  rw [dif_pos ⟨t, hblank⟩]
  refine le_trans (List.length_filterMap_le _ _) ?_
  simpa using Nat.find_min'
    (p := fun n : ℕ =>
      (M.runFrom O (M.initCfg x) t).workTapes (queryTapeIdx k) (n : ℤ) = none)
    ⟨t, hblank⟩ hblank

/-- In an initialized run, every work-tape cell at distance at least `t` from the
origin is still blank after `t` steps. This is the certificate that the no-blank
fallback branch of `queryString` is unreachable from initialization (the length bound
`queryString_length_le` alone does not certify this, since the fallback also returns a
short list).

**Proof sketch.** Simultaneous induction on `t` with the head-position bound
`|workTapePos i| ≤ t`: at `t = 0` all tapes are blank and heads are at `0`; an ordinary
step writes only at the *old* head position (of absolute value `≤ t`, hence `< t + 1`;
`Action.apply` writes before moving) and moves each head by at most one cell
(`Turing.workTapePos_apply_le`); oracle-answer and halted steps change no tape. -/
theorem runFrom_workTapes_blank (M : OracleTM k Symbol State) (O : Language Symbol)
    (x : List Symbol) (t : ℕ) (i : Fin (k + 1)) (z : ℤ) (hz : (t : ℤ) ≤ |z|) :
    (M.runFrom O (M.initCfg x) t).workTapes i z = none :=
  (runFrom_workTapes_invariant M O x t).2 i z hz

end OracleTM

/-- Extend an action on `k` work tapes to `k + 1` work tapes: the extra (last) tape is
neither written nor moved. -/
def Action.extend (a : Action k Symbol State) : Action (k + 1) Symbol State where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < k then a.workTapes ⟨i, h⟩ else (none, 0)
  output := a.output
  state := a.state

/-- Embed a `k`-tape configuration into a `k + 1`-tape configuration over the extended
state type `State ⊕ Fin 3`: the extra work tape is blank with its head at `0`, and the
state is renamed along `Sum.inl`. -/
def Cfg.embedOracle (cfg : Cfg k Symbol State input) :
    Cfg (k + 1) Symbol (State ⊕ Fin 3) input where
  state := cfg.state.map Sum.inl
  inputPos := cfg.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < k then cfg.workTapes ⟨i, h⟩ else fun _ => none
  workTapePos := fun i => if h : (i : ℕ) < k then cfg.workTapePos ⟨i, h⟩ else 0
  output := cfg.output

/-- The embedding preserves the scanned input symbol. -/
lemma Cfg.embedOracle_inputSymbol (cfg : Cfg k Symbol State input) :
    cfg.embedOracle.inputSymbol = cfg.inputSymbol := rfl

/-- The embedding preserves the scanned work symbols on the original tapes. -/
lemma Cfg.embedOracle_workTapeSymbols (cfg : Cfg k Symbol State input) (i : Fin k) :
    cfg.embedOracle.workTapeSymbols i.castSucc = cfg.workTapeSymbols i := by
  simp [Cfg.workTapeSymbols, Cfg.embedOracle]

/-- The embedding preserves haltedness. -/
lemma Cfg.embedOracle_state_eq_none {cfg : Cfg k Symbol State input} :
    cfg.embedOracle.state = none ↔ cfg.state = none := by
  simp [Cfg.embedOracle, Option.map_eq_none_iff]

/-- The embedding preserves the output tape. -/
lemma Cfg.embedOracle_output (cfg : Cfg k Symbol State input) :
    cfg.embedOracle.output = cfg.output := rfl

/-- Applying an extended, state-renamed action to an embedded configuration is the
embedding of applying the original action. -/
lemma Cfg.embedOracle_apply (a : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    ((a.mapState (Sum.inl : State → State ⊕ Fin 3)).extend).apply cfg.embedOracle =
      (a.apply cfg).embedOracle := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_pos hi]
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_neg hi]
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_pos hi]
    · simp only [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle,
        dif_neg hi]
      simp
  · simp [Action.apply, Action.extend, Action.mapState, Cfg.embedOracle]

/-- The embedding sends initial configurations to initial configurations. -/
lemma Cfg.embedOracle_init (q₀ : State) (input : List Symbol) :
    (Cfg.init q₀ input : Cfg k Symbol State input).embedOracle =
      Cfg.init (Sum.inl q₀ : State ⊕ Fin 3) input := by
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Cfg.embedOracle]

namespace OracleTM

/-- Embed a plain machine as an oracle machine that never queries: the state type is
extended by three fresh states serving as `qQuery`, `qYes`, `qNo`, and the transition
function acts as before on original states (never moving into the fresh states, and
ignoring the query tape). The fresh states are unreachable from the initial
configuration. The *transition table* halts immediately from all three fresh states;
note that from `qQuery` itself the query override fires first (one answer step into
`qYes`/`qNo`, whose table entries then halt) — the table's `qQuery` row is dead code. -/
def ofMultiTapeTM (tm : MultiTapeTM k Symbol State) : OracleTM k Symbol (State ⊕ Fin 3) where
  q₀ := .inl tm.q₀
  qQuery := .inr 0
  qYes := .inr 1
  qNo := .inr 2
  tr q inp work :=
    match q with
    | .inl q => ((tm.tr q inp fun i => work i.castSucc).mapState Sum.inl).extend
    | .inr _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- The embedding of a plain machine is well-formed: its three fresh special states are
pairwise distinct by construction. -/
theorem ofMultiTapeTM_wellFormed (tm : MultiTapeTM k Symbol State) :
    (ofMultiTapeTM tm).WellFormed := by
  constructor <;> simp [ofMultiTapeTM]

/-- One step of an embedded plain machine, under any oracle, is the embedding of one
step of the original machine: the embedded state is never `qQuery = Sum.inr 0`, so the
oracle step reduces to applying the extended action, and `Cfg.embedOracle_apply` turns
that into the embedding of the original step. -/
lemma step_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg k Symbol State input) :
    (ofMultiTapeTM tm).step O cfg.embedOracle = (tm.step cfg).embedOracle := by
  unfold OracleTM.step MultiTapeTM.step
  cases hs : cfg.state with
  | none =>
    have h : cfg.embedOracle.state = none := by simp [Cfg.embedOracle, hs]
    rw [h]
  | some q =>
    have h : cfg.embedOracle.state = some (Sum.inl q) := by simp [Cfg.embedOracle, hs]
    rw [h]
    dsimp only
    have hne : (Sum.inl q : State ⊕ Fin 3) ≠ (ofMultiTapeTM tm).qQuery := by
      simp [ofMultiTapeTM]
    rw [if_neg hne]
    have hw : (fun i => cfg.embedOracle.workTapeSymbols i.castSucc) =
        cfg.workTapeSymbols :=
      funext fun i => Cfg.embedOracle_workTapeSymbols cfg i
    have htr : (ofMultiTapeTM tm).tr (Sum.inl q) cfg.embedOracle.inputSymbol
        cfg.embedOracle.workTapeSymbols =
        ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).mapState Sum.inl).extend := by
      show ((tm.tr q cfg.embedOracle.inputSymbol
        fun i => cfg.embedOracle.workTapeSymbols i.castSucc).mapState Sum.inl).extend = _
      rw [Cfg.embedOracle_inputSymbol, hw]
    rw [htr, Cfg.embedOracle_apply]

/-- **Sanity check for the oracle architecture** (plan §3.1): an embedded plain machine
runs in lockstep with the original under every oracle — `step_ofMultiTapeTM` pointwise,
then induction on `t`. -/
theorem runFrom_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (ofMultiTapeTM tm).runFrom O cfg.embedOracle t = (tm.runFrom cfg t).embedOracle := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : (ofMultiTapeTM tm).runFrom O cfg.embedOracle (t + 1) =
        (ofMultiTapeTM tm).step O ((ofMultiTapeTM tm).runFrom O cfg.embedOracle t) :=
      Function.iterate_succ_apply' _ _ _
    rw [h1, ih, MultiTapeTM.runFrom_succ_eq_step', step_ofMultiTapeTM]

/-- An embedded plain machine has the same input/output behavior and time bounds as the
original, relative to every oracle. In particular its behavior is oracle-independent.

**Proof sketch.** `Cfg.embedOracle` sends the initial configuration of `tm` to the initial
configuration of the embedded machine (both have blank work tapes and heads at `0`); by
`runFrom_ofMultiTapeTM` the runs correspond, and `Cfg.embedOracle` preserves haltedness
and the output tape. -/
theorem computesInTime_ofMultiTapeTM (tm : MultiTapeTM k Symbol State) (O : Language Symbol)
    (input output : List Symbol) (t : ℕ) :
    (ofMultiTapeTM tm).ComputesInTime O input output t ↔
      ((tm.runFrom (tm.initCfg input) t).state = none ∧
        (tm.runFrom (tm.initCfg input) t).output = output) := by
  have hinit : (ofMultiTapeTM tm).initCfg input = (tm.initCfg input).embedOracle := by
    simp only [OracleTM.initCfg, MultiTapeTM.initCfg, ofMultiTapeTM]
    exact (Cfg.embedOracle_init tm.q₀ input).symm
  simp only [OracleTM.ComputesInTime, hinit, runFrom_ofMultiTapeTM,
    Cfg.embedOracle_state_eq_none, Cfg.embedOracle_output]

open Classical in
/-- The converse of `ofMultiTapeTM` for the empty oracle: an oracle machine run with the
empty oracle is eliminated into a plain `k + 1`-tape machine over the *same* state type,
by replacing the query behavior with a stationary transition into `qNo` (the empty
oracle always answers no). (`audits/phase1-findings.md`, finding 8.) -/
noncomputable def plainEmptyOracle (M : OracleTM k Symbol State) :
    MultiTapeTM (k + 1) Symbol State where
  q₀ := M.q₀
  tr q inp work :=
    if q = M.qQuery then ⟨0, fun _ => (none, 0), none, some M.qNo⟩
    else M.tr q inp work

/-- One step of the empty-oracle elimination coincides with one step of the oracle
machine on the empty oracle: on a halted configuration both sides are fixed; in state
`qQuery` the empty oracle answers `qNo` and the stationary action's `Action.apply`
changes only the state; elsewhere both sides apply the same transition-table action. -/
lemma step_plainEmptyOracle (M : OracleTM k Symbol State)
    (cfg : Cfg (k + 1) Symbol State input) :
    M.plainEmptyOracle.step cfg = M.step (0 : Language Symbol) cfg := by
  unfold MultiTapeTM.step OracleTM.step plainEmptyOracle
  cases hs : cfg.state with
  | none => rfl
  | some q =>
    dsimp only
    by_cases hq : q = M.qQuery
    · rw [if_pos hq, if_pos hq, if_neg (Language.notMem_zero _)]
      refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Action.apply]
    · rw [if_neg hq, if_neg hq]

/-- **Sanity check, converse direction**: the empty-oracle elimination runs in exact
lockstep with the oracle machine on the empty oracle — same configurations at every
step, from every starting configuration (`step_plainEmptyOracle` pointwise, then
induction on `t`). -/
theorem runFrom_plainEmptyOracle (M : OracleTM k Symbol State)
    (cfg : Cfg (k + 1) Symbol State input) (t : ℕ) :
    -- `0` is the empty language (`Language`'s `Zero` instance)
    M.plainEmptyOracle.runFrom cfg t = M.runFrom (0 : Language Symbol) cfg t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : M.runFrom (0 : Language Symbol) cfg (t + 1) =
        M.step 0 (M.runFrom (0 : Language Symbol) cfg t) :=
      Function.iterate_succ_apply' _ _ _
    rw [MultiTapeTM.runFrom_succ_eq_step', h1, ih, step_plainEmptyOracle]

end OracleTM

end Turing

```


## ===== TCSlib/Complexity/TuringMachine/Nondeterministic.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic Multi-Tape Turing Machines

[AB09, §2.1.2]: a nondeterministic Turing machine (NDTM) is a standard TM with **two**
transition functions `δ₀` and `δ₁`; at every step the machine chooses which of the two to
apply. A finite run is therefore governed by a *choice word* — one bit per step — and the
run function is indexed by it. This module defines the raw machine, its choice-word
semantics in the style of the deterministic `Turing.MultiTapeTM.runFrom`, the all-branch
halting predicate that time bounds quantify over, the bundled finite layer `FinNDTM`, and
the embedding of deterministic machines. Acceptance and the class `NTIME` live one layer
up, in `TCSlib.Complexity.ClassNP.NTIME`, because they fix the binary alphabet.

## Design and deviations from [AB09]

* **Two total transition functions, `Bool`-indexed**: the single field
  `tr : Bool → …` carries [AB09]'s `δ₀` as `tr false` and `δ₁` as `tr true`. Both
  functions are total, so no configuration is ever *stuck* — every choice word of every
  length drives a complete run. (This is the load-bearing difference from a
  relational model such as cslib's `MultiTapeNTM`, surveyed and deliberately not
  ported — see the plan's decision log: with binary choice the accepting choice word
  *is* the polynomial-length certificate of [AB09, Theorem 2.6], while arbitrary
  branching relations have no canonical certificate encoding.)
* **Choice words are finite lists** (`List Bool`), consumed left to right, one bit per
  step: `runWith w cfg` is the configuration after `|w|` steps under the choices `w`.
  The alternative — infinite choice streams `ℕ → Bool` with a separate step count — is
  equivalent for every notion built here (only the first `t` bits of a stream are ever
  consulted); the list form makes the choice word a finite string that can be a
  certificate. **Design question (c) for the phase-2 audit.**
* **No `q_accept` state.** [AB09] equips NDTMs with a distinguished accepting state;
  our machines signal through their output tape, exactly as the deterministic
  development does (`Turing.FinTM.DecidesInTime` reads acceptance off the output
  `[true]`/`[false]`). Acceptance-by-output is defined in
  `TCSlib.Complexity.ClassNP.NTIME` and is **design question (a) for the phase-2
  audit**.
* **Halting is absorbing under every choice**: stepping a halted configuration is the
  identity regardless of the choice bit, mirroring the deterministic `step`. Extending
  a choice word beyond the halting time therefore never changes the reached
  configuration — the lemma `runWith_of_halt` below. This is what the exact-length
  quantifiers lean on, *directionally*: accepting witnesses pad to any larger exact
  length, and all-branch halting at a larger budget follows by splitting at the old
  one (`HaltsWithin.mono`). It does **not** make every bounded-length rewriting valid —
  "every word of length at most `t` is halted" already fails at the empty word — and
  the correct bounded readings are recorded in `TCSlib.Complexity.ClassNP.NTIME`
  (round-1 audit, finding 2).
* The model reuses the vendored configuration layer (`Turing.Cfg`, `Turing.Action`)
  unchanged: an NDTM step applies an `Action` exactly as a deterministic step does; only
  the *selection* of the action is new.

## Main definitions

* `Turing.NDTM` — the binary-choice nondeterministic machine. [AB09, §2.1.2]
* `Turing.NDTM.stepWith`, `Turing.NDTM.runWith` — one step under a choice bit; the run
  under a choice word. [AB09, §2.1.2]
* `Turing.NDTM.HaltsWithin` — every choice word of length `t` halts the machine on the
  given input; the totality condition of [AB09]'s "runs in `T(n)` time".
* `Turing.FinNDTM` — the bundled finite layer, mirroring `Turing.FinTM`.
* `Turing.MultiTapeTM.toNDTM`, `Turing.FinTM.toFinNDTM` — a deterministic machine as an
  NDTM whose two transition functions coincide.

## Main results

* `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt` — the choice-word run
  algebra (proved; pure unfoldings, the nondeterministic counterparts of the vendored
  `runFrom` lemmas).
* `Turing.NDTM.HaltsWithin.mono` — all-branch halting is monotone in the time bound.
* `Turing.MultiTapeTM.toNDTM_runWith` — the embedded deterministic machine ignores its
  choices: every choice word of length `t` reproduces `runFrom` at time `t`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2, pp. 41-42.)
* cslib (https://github.com/leanprover/cslib), `MultiTape/Nondeterministic.lean` at
  commit a3747758: a relational nondeterministic model (related work, not ported — see
  `AroraBarakChapter2Plan.md`, decision log).
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/-- A binary-choice nondeterministic multi-tape Turing machine [AB09, §2.1.2]: a
machine with **two** total transition functions, carried as the `Bool`-indexed field
`tr` — `tr false` is [AB09]'s `δ₀` and `tr true` is `δ₁`. Tapes, actions, and
configurations are exactly those of the deterministic `Turing.MultiTapeTM`; as there,
`Symbol` and `State` need not be finite at this layer (the bundled finite layer is
`Turing.FinNDTM` below). -/
structure NDTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- the two transition functions, indexed by the nondeterministic choice: `tr false`
  is `δ₀`, `tr true` is `δ₁`; each maps the state, input symbol, and work-head symbols
  to an action, exactly as the deterministic transition function does -/
  tr (choice : Bool) (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace NDTM

variable {input : List Symbol} {tm : NDTM k Symbol State}

/-- One step under the choice bit `b`: apply the action selected by transition function
`tr b`, or stay put when already halted. Halting is absorbing under **every** choice —
the halted branch does not consult `b` — mirroring `Turing.MultiTapeTM.step`. -/
def stepWith (b : Bool) (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q => (tm.tr b q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The initial configuration corresponding to an input string — identical to the
deterministic initialization (blank work tapes, input head on the first symbol). -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

/-- The configuration reached from `cfg` by running under the choice word `w`, one
choice bit per step, consumed left to right: `|w|` steps in total. This is the
nondeterministic counterpart of `Turing.MultiTapeTM.runFrom`; a "branch" of the
computation tree of [AB09, §2.1.2] is the run under one choice word. -/
def runWith : List Bool → Cfg k Symbol State input → Cfg k Symbol State input
  | [], cfg => cfg
  | b :: w, cfg => runWith w (tm.stepWith b cfg)

/-- The empty choice word runs zero steps. -/
@[simp]
lemma runWith_nil {cfg : Cfg k Symbol State input} : tm.runWith [] cfg = cfg := rfl

/-- Consuming one choice bit is one step: the run under `b :: w` is the run under `w`
from the configuration one `stepWith b` ahead. -/
lemma runWith_cons {b : Bool} {w : List Bool} {cfg : Cfg k Symbol State input} :
    tm.runWith (b :: w) cfg = tm.runWith w (tm.stepWith b cfg) := rfl

/-- Running under `w ++ w'` is running under `w`, then under `w'` from the reached
configuration — the counterpart of `Turing.MultiTapeTM.runFrom_add`. -/
lemma runWith_append (w w' : List Bool) (cfg : Cfg k Symbol State input) :
    tm.runWith (w ++ w') cfg = tm.runWith w' (tm.runWith w cfg) := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih => rw [List.cons_append, runWith_cons, runWith_cons, ih]

/-- Stepping a halted configuration is the identity, under either choice. -/
@[simp]
lemma stepWith_of_halt {b : Bool} {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.stepWith b cfg = cfg := by
  unfold stepWith
  rw [h]

/-- Running from a halted configuration stays there, under **every** choice word — the
counterpart of `Turing.MultiTapeTM.runFrom_of_halt`. Extending a choice word beyond the
halting time therefore never changes the reached configuration. -/
@[simp]
lemma runWith_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none)
    {w : List Bool} : tm.runWith w cfg = cfg := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [runWith_cons, stepWith_of_halt h]; exact ih

/-- The machine halts on `input` within `t` steps **along every branch**: after any `t`
nondeterministic choices the configuration is halted. This is the totality condition in
[AB09]'s "runs in `T(n)` time" (§2.1.2: *every* sequence of choices reaches the halting
state within the bound), rendered over choice words of length exactly `t`; by
`Turing.NDTM.runWith_of_halt` the exact-length quantifier already covers all longer
words, and `Turing.NDTM.HaltsWithin.mono` makes this precise. -/
def HaltsWithin (tm : NDTM k Symbol State) (input : List Symbol) (t : ℕ) : Prop :=
  ∀ w : List Bool, w.length = t → (tm.runWith w (tm.initCfg input)).state = none

/-- All-branch halting is monotone in the time bound.

**Proof sketch.** Given `w` with `|w| = t' ≥ t`, split `w = w.take t ++ w.drop t`
(`List.take_append_drop`) with `|w.take t| = t` (`List.length_take`, since `t ≤ t'`).
By the hypothesis the run under `w.take t` is halted; `Turing.NDTM.runWith_append`
factors the run under `w` through it, and `Turing.NDTM.runWith_of_halt` absorbs the
remaining choices, so the state at `w` equals the halted state at `w.take t`. -/
theorem HaltsWithin.mono {tm : NDTM k Symbol State} {input : List Symbol} {t t' : ℕ}
    (h : tm.HaltsWithin input t) (hle : t ≤ t') : tm.HaltsWithin input t' := by
  intro w hw
  have hlen : (w.take t).length = t := List.length_take_of_le (hle.trans_eq hw.symm)
  have hhalt := h (w.take t) hlen
  have hrun := runWith_append (tm := tm) (w.take t) (w.drop t) (tm.initCfg input)
  rw [List.take_append_drop, runWith_of_halt _ hhalt] at hrun
  rw [hrun]
  exact hhalt

end NDTM

/-- A nondeterministic machine bundled with a finite state type, mirroring
`Turing.FinTM`: the instances are data (`Fintype`/`DecidableEq`, not `Finite`) for the
same reason as there — a machine that is to be encoded as a string must enumerate its
transition tables. All headline nondeterministic-complexity definitions
(`Turing.FinNDTM.DecidesInTime`, `Complexity.NTIME`) are stated over this layer. -/
structure FinNDTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible -/
  [decEqState : DecidableEq State]
  /-- the underlying nondeterministic machine -/
  tm : NDTM k Symbol State

attribute [instance] FinNDTM.fintypeState FinNDTM.decEqState

/-- A deterministic machine as a nondeterministic one whose two transition functions
coincide: both choices apply the deterministic transition. This is the embedding behind
`DTIME ⊆ NTIME` ([AB09, §2.1.2]: a TM is an NDTM that ignores its choices). -/
def MultiTapeTM.toNDTM (tm : MultiTapeTM k Symbol State) : NDTM k Symbol State :=
  ⟨tm.q₀, fun _ => tm.tr⟩

/-- The embedded deterministic machine starts where the original does. -/
@[simp]
lemma MultiTapeTM.toNDTM_initCfg (tm : MultiTapeTM k Symbol State) (input : List Symbol) :
    tm.toNDTM.initCfg input = tm.initCfg input := rfl

/-- The embedded deterministic machine ignores its choices: running `toNDTM` under any
choice word `w` is running the original machine for `|w|` steps.

**Proof sketch.** Induction on `w` generalizing the configuration. For one step,
`Turing.NDTM.stepWith` on `toNDTM` and `Turing.MultiTapeTM.step` are the same match on
the state — halted branches are both the identity, and on a live state both apply the
action `tm.tr q …` since `toNDTM.tr b = tm.tr` for either `b`. The cons case is then
`Turing.NDTM.runWith_cons` against `Turing.MultiTapeTM.runFrom_succ_eq_step` (the step
count on the right is `|w| + 1`, `List.length_cons`). -/
theorem MultiTapeTM.toNDTM_runWith (tm : MultiTapeTM k Symbol State) {input : List Symbol}
    (w : List Bool) (cfg : Cfg k Symbol State input) :
    tm.toNDTM.runWith w cfg = tm.runFrom cfg w.length := by
  induction w generalizing cfg with
  | nil => rfl
  | cons b w ih =>
    rw [NDTM.runWith_cons, List.length_cons, runFrom_succ_eq_step]
    exact ih (tm.step cfg)

/-- A bundled deterministic machine as a bundled nondeterministic one — the `FinTM`
layer of `Turing.MultiTapeTM.toNDTM`, with the same tapes and state type. -/
def FinTM.toFinNDTM {Symbol : Type} (M : FinTM Symbol) : FinNDTM Symbol :=
  ⟨M.k, M.State, M.tm.toNDTM⟩

end Turing

```


## ===== TCSlib/Complexity/TuringMachine/StateRenaming.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# State renaming

Raw-layer transport of actions, configurations, and machines along maps of the
state type. This is the generic component shared by the oracle embedding
(`TCSlib.Complexity.TuringMachine.Oracle`, which renames states into
`State ⊕ Fin 3`) and the code normal form
(`TCSlib.Complexity.TuringMachine.Encoding`, which relabels states into
`Fin (numStates + 1)`), factored out per the epoch-1 audit (finding 5).

## Design

* `Turing.Action.mapState` and `Turing.Cfg.mapState` take an **arbitrary
  function** of the state types: mapping an action or configuration needs no
  injectivity, and the application lemma `Turing.Cfg.mapState_apply` holds for
  any function.
* `Turing.MultiTapeTM.relabelState` takes an **equivalence**: renaming a whole
  transition table along a non-injective map is not well defined (two states
  identified by the map may disagree on their transitions — epoch-1 audit,
  finding 5), and the inverse is used to read the table.
* The run-correspondence lemma is deliberately an **initialized-run** statement
  (`Turing.MultiTapeTM.relabelState_runFrom_init`), as the epoch-1 audit
  specified; an arbitrary-starting-configuration version can be added, with its
  own checked statement, if a result needs it.
* No finiteness assumptions anywhere: this is the raw parametric layer.

## Main definitions

* `Turing.Action.mapState` — rename an action's optional successor state
  (moved here from the oracle module; the definition is unchanged).
* `Turing.Cfg.mapState` — rename a configuration's optional state.
* `Turing.MultiTapeTM.relabelState` — transport a machine along a state
  equivalence.

## Main results

* `Turing.Cfg.mapState_apply` — renaming commutes with applying an action.
* `Turing.MultiTapeTM.relabelState_step` — renaming commutes with one step,
  including the absorbing halted case.
* `Turing.MultiTapeTM.relabelState_runFrom_init` — initialized runs correspond
  at every time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2 — the machine model whose state
  spaces are transported here; the module itself is internal infrastructure
  with no direct textbook counterpart.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*}

/-- Rename the states of an action along a function. -/
def Action.mapState {State' : Type*} (f : State → State') (a : Action k Symbol State) :
    Action k Symbol State' where
  inputTape := a.inputTape
  workTapes := a.workTapes
  output := a.output
  state := a.state.map f

/-- Rename a configuration's optional state along a function, preserving the
input position, work tapes, head positions, and output. -/
def Cfg.mapState {State' : Type*} {input : List Symbol} (f : State → State')
    (cfg : Cfg k Symbol State input) : Cfg k Symbol State' input :=
  { cfg with state := cfg.state.map f }

/-- State renaming commutes with applying an action (any function; no
injectivity needed, since the action is supplied explicitly). -/
lemma Cfg.mapState_apply {State' : Type*} {input : List Symbol} (f : State → State')
    (a : Action k Symbol State) (cfg : Cfg k Symbol State input) :
    (a.mapState f).apply (cfg.mapState f) = (a.apply cfg).mapState f := rfl

/-- Transport a machine along a state **equivalence**: the initial state is
mapped forward, and each transition reads the table through the inverse. An
arbitrary function would not suffice here — identifying two states with
different transitions leaves no well-defined table (epoch-1 audit, finding 5). -/
def MultiTapeTM.relabelState {State' : Type*} (tm : MultiTapeTM k Symbol State)
    (e : State ≃ State') : MultiTapeTM k Symbol State' where
  q₀ := e tm.q₀
  tr := fun q inp ws => (tm.tr (e.symm q) inp ws).mapState e

/-- Relabeling commutes with each step, including the absorbing halted case. -/
lemma MultiTapeTM.relabelState_step {State' : Type*} {input : List Symbol}
    (tm : MultiTapeTM k Symbol State) (e : State ≃ State')
    (cfg : Cfg k Symbol State input) :
    (tm.relabelState e).step (cfg.mapState e) = (tm.step cfg).mapState e := by
  have hin : (cfg.mapState e).inputSymbol = cfg.inputSymbol := rfl
  have hwork : (cfg.mapState e).workTapeSymbols = cfg.workTapeSymbols := rfl
  unfold MultiTapeTM.step
  cases hs : cfg.state with
  | none => simp [Cfg.mapState, hs]
  | some q =>
    rw [show (cfg.mapState e).state = some (e q) by
      simp only [Cfg.mapState, hs, Option.map_some]]
    dsimp only
    rw [hin, hwork]
    simp only [MultiTapeTM.relabelState, Equiv.symm_apply_apply]
    exact Cfg.mapState_apply e _ cfg

/-- Initialized runs correspond at every time. This is deliberately an
initialized-run lemma (epoch-1 audit, finding 5); an arbitrary-start version
would be a separate statement. -/
lemma MultiTapeTM.relabelState_runFrom_init {State' : Type*}
    (tm : MultiTapeTM k Symbol State) (e : State ≃ State') (input : List Symbol)
    (t : ℕ) :
    (tm.relabelState e).runFrom ((tm.relabelState e).initCfg input) t =
      (tm.runFrom (tm.initCfg input) t).mapState e :=
  MultiTapeTM.runFrom_comm_of_step (Cfg.mapState e)
    (tm.relabelState_step e) (tm.initCfg input) t

end Turing

```


## ===== TCSlib/Complexity/TuringMachine/Encoding.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import TCSlib.Complexity.TuringMachine.StateRenaming
import TCSlib.Complexity.TuringMachine.Robustness.SingleTape

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines as strings

[AB09, §1.4]: machines can be represented as binary strings, in such a way that
**(1)** every string represents some machine, and **(2)** every machine is represented
by infinitely many strings. This file provides the *code normal form* (`CodeTM`: one
work tape, binary alphabet, `Fin`-states — encodability requires fixing concrete
parameters, and by `Turing.FinTM.one_work_tape_binary` this normal form loses only a
quadratic factor), a fixed canonical serialization `CodeTM.serialize`, the
specification `MachineCode`/`EffectiveMachineCode` of a representation scheme, and the
self-delimiting pairing used by the universal machine.

## Design and deviations from [AB09]

* [AB09] fixes one concrete representation and standing conventions. We specify the
  representation *abstractly*, state the universal machine relative to it
  (`TCSlib.Complexity.TuringMachine.Universal`), and record the existence of a
  concrete scheme as a separate obligation.
* **The algebraic laws alone are not enough** (phase-3 audit, finding 1 and
  Argument A): a scheme satisfying only totality and padded round-trips may assign
  *noncomputable* meanings to codes — permuting the meanings of an honest scheme
  along an undecidable set preserves every law — and no universal machine can exist
  relative to such a scheme. Moreover requiring the scheme to canonize into *its own*
  encoding does not help (the pathological scheme's canonizer is computable). The
  effectivity contract must target a **fixed, scheme-independent** format: an
  `EffectiveMachineCode` carries a machine of this development computing
  `fun α => (decode α).serialize`, where `CodeTM.serialize` is the concrete
  serialization defined below. All universal-machine statements are relative to
  `EffectiveMachineCode`.
* Property (2) is stated as recovery under **`true`-padding of valid codes**
  (`decode_encode_pad`), the formal content of [AB09]'s "trailing 1s are ignored"
  convention; padding of *arbitrary* strings is deliberately not constrained.
  Property (1), totality, is enforced by `decode`'s type — this is a totality
  guarantee, not by itself a computability guarantee (audit finding 9).
* `CodeTM.serialize` records the state count, **the initial state** (audit finding 5:
  omitting it makes distinct machines collide), and the full transition table in a
  fixed enumeration order.

## Main definitions

* `Turing.CodeTM` — the code normal form; `Turing.CodeTM.toFinTM`;
  `Turing.CodeTM.serialize` — the fixed canonical serialization.
* `Turing.pairEncode` — self-delimiting pairing (first component doubled bitwise,
  separator `[false, true]`, second component verbatim); `Turing.dbl` — the doubling.
* `Turing.MachineCode` — the algebraic representation-scheme laws [AB09, §1.4].
* `Turing.EffectiveMachineCode` — a scheme together with an in-model machine
  computing `serialize ∘ decode`; the standing hypothesis of the universal machine.

## Main results

* `Turing.MachineCode.decode_encode` — decoding a code recovers the machine.
* `Turing.pairEncode_injective` — the pairing is injective (aligned-pair parsing).
* `Turing.length_pairEncode`, `Turing.pairEncode_eq_dbl`, `Turing.pairDecode_eq_none`,
  `Turing.eq_pairEncode_of_pairDecode`, `Turing.pairEncode_replicate_inj` — the shape of
  the pairing, shared by the machine-side developments.
* `Turing.length_bits_le_self` — `|bits m| ≤ m`.
* `Turing.computesFunInTime_pairEncode_diag` — the diagonal pairing `α ↦ ⟨α, α⟩` is
  computable in linear time (the only code computation the `HALT` reduction needs).
* `Turing.exists_codeTM` — every one-work-tape binary machine is equivalent to a
  coded machine (state relabeling).

The concrete parser/decoder realizing a scheme lives in
`TCSlib.Complexity.TuringMachine.CodeParser`, and the existence of an effective
scheme (`Turing.exists_effectiveMachineCode`) is proved in
`TCSlib.Complexity.TuringMachine.MathlibBridge`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

/-- A machine in *code normal form*: one work tape, binary alphabet, and states drawn
from a canonical nonempty finite type `Fin (numStates + 1)`. [AB09, §1.4] -/
structure CodeTM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying machine -/
  tm : MultiTapeTM 1 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded machine. -/
def CodeTM.toFinTM (M : CodeTM) : FinTM Bool where
  k := 1
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The bundled form of a coded machine has exactly one work tape. -/
@[simp]
lemma CodeTM.toFinTM_k (M : CodeTM) : M.toFinTM.k = 1 := rfl

/-- Self-delimiting pairing of two binary strings: the **first** string with every bit
doubled, then the separator `[false, true]`, then the second string verbatim. Parsing
reads aligned two-bit blocks: `00`/`11` are data, the first aligned `01` is the
separator (a `01` can only occur unaligned inside doubled data), and the suffix is the
second component. The universal machine's input convention is `pairEncode α x` —
**code first, input second**, deviating from [AB09]'s `⟨x, α⟩` order so that the
simulation's startup cost is independent of the input (phase-3 audit, finding 2 and
Argument B: with the input first, no bound `C · (t + 1)` with `C` independent of `x`
can hold). -/
def pairEncode (x α : List Bool) : List Bool :=
  (x.flatMap fun b => [b, b]) ++ [false, true] ++ α

/-- Parse aligned doubled bits until the separator, leaving its suffix untouched. -/
def pairDecode : List Bool → Option (List Bool × List Bool)
  | false :: false :: rest => (pairDecode rest).map fun p => (false :: p.1, p.2)
  | true :: true :: rest => (pairDecode rest).map fun p => (true :: p.1, p.2)
  | false :: true :: rest => some ([], rest)
  | _ => none

/-- The aligned parser recovers both components, by induction on the first word. -/
lemma pairDecode_pairEncode (x α : List Bool) :
    pairDecode (pairEncode x α) = some (x, α) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    have h := congrArg (Option.map fun p : List Bool × List Bool => (b :: p.1, p.2)) ih
    cases b <;> simpa [pairEncode, pairDecode] using h

/-- The pairing is injective.

**Proof sketch** (phase-3 audit, Argument D). The aligned two-bit parser recovers the
components: read blocks of two from the left; `00` yields `false`, `11` yields `true`,
and the first aligned `01` is the separator — no doubled bit produces an aligned `01`.
The remaining suffix is the second component verbatim. This parser is a left inverse
of the pairing, and a function with a left inverse is injective. Empty components are
unproblematic (`pairEncode [] α = [false, true] ++ α`). -/
theorem pairEncode_injective :
    Function.Injective fun p : List Bool × List Bool => pairEncode p.1 p.2 := by
  intro p q h
  have := congrArg pairDecode h
  simpa only [pairDecode_pairEncode, Prod.mk.eta, Option.some.injEq] using this

/-! ### Shape of the pairing

Generic list facts about `pairEncode` and `pairDecode`, shared by the machine-side
developments (the time hierarchy, the polynomial hierarchy, logspace machines, and
the circuit-evaluation machines). -/

/-- A word with every bit written twice — the first component of `Turing.pairEncode`. -/
def dbl (w : List Bool) : List Bool := w.flatMap fun b => [b, b]

/-- Doubling the empty word gives the empty word. -/
@[simp] lemma dbl_nil : dbl [] = [] := rfl

/-- Doubling `b :: w` is `b b` followed by doubling `w`. -/
@[simp] lemma dbl_cons (b : Bool) (w : List Bool) : dbl (b :: w) = b :: b :: dbl w := rfl

/-- Doubling a word doubles its length. -/
@[simp] lemma length_dbl (w : List Bool) : (dbl w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ih]; ring

/-- Both copies of bit `c` of a doubled word read `w[c]`. -/
lemma getElem?_dbl (w : List Bool) (c : ℕ) (hc : c < w.length) (p : Bool) :
    (dbl w)[2 * c + p.toNat]? = some w[c] := by
  induction w generalizing c with
  | nil => simp at hc
  | cons b w ih =>
    cases c with
    | zero => cases p <;> simp
    | succ c =>
      have := ih c (by simpa using hc)
      simp only [dbl_cons, List.getElem_cons_succ]
      rw [show 2 * (c + 1) + p.toNat = (2 * c + p.toNat) + 1 + 1 by ring]
      simpa using this

/-- `pairEncode x y` is the doubled first word, the separator `[false, true]`, and the
second word. -/
lemma pairEncode_eq_dbl (x y : List Bool) : pairEncode x y = dbl x ++ [false, true] ++ y :=
  rfl

/-- The length of a pair: `|pairEncode x y| = 2|x| + 2 + |y|`. -/
theorem length_pairEncode (x y : List Bool) :
    (pairEncode x y).length = 2 * x.length + 2 + y.length := by
  simp [pairEncode_eq_dbl]
  omega

/-- A string that is not a pair is a doubled word followed by a malformed tail: the end
of the string, a lone bit, or the aligned pair `10`.

**Proof sketch.** Functional induction along `pairDecode`: aligned `00`/`11` pairs extend
the doubled prefix; in the remaining case the string matches none of `00`, `11`, `01`,
so it is empty, a single bit, or starts with `10`. -/
theorem pairDecode_eq_none (z : List Bool) (h : pairDecode z = none) :
    ∃ w tail, z = dbl w ++ tail ∧
      (tail = [] ∨ (∃ b, tail = [b]) ∨ ∃ r, tail = true :: false :: r) := by
  induction z using pairDecode.induct with
  | case1 xs ih =>
    have h' : pairDecode xs = none := by simpa [pairDecode] using h
    obtain ⟨w, tail, hw, ht⟩ := ih h'
    exact ⟨false :: w, tail, by simp [hw], ht⟩
  | case2 xs ih =>
    have h' : pairDecode xs = none := by simpa [pairDecode] using h
    obtain ⟨w, tail, hw, ht⟩ := ih h'
    exact ⟨true :: w, tail, by simp [hw], ht⟩
  | case3 xs => simp [pairDecode] at h
  | case4 xs h₁ h₂ h₃ =>
    refine ⟨[], xs, by simp, ?_⟩
    rcases xs with _ | ⟨b, _ | ⟨c, r⟩⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨b, rfl⟩)
    · cases b <;> cases c
      · exact absurd rfl (h₁ r)
      · exact absurd rfl (h₃ r)
      · exact Or.inr (Or.inr ⟨r, rfl⟩)
      · exact absurd rfl (h₂ r)

/-- A successfully decoded string is the pairing of its components.

**Proof sketch.** Functional induction along `pairDecode`, inverting
`pairDecode_pairEncode` one aligned pair at a time. -/
theorem eq_pairEncode_of_pairDecode (z a b : List Bool) (h : pairDecode z = some (a, b)) :
    z = pairEncode a b := by
  induction z using pairDecode.induct generalizing a with
  | case1 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => false :: false :: zs) (ih ys hr)
  | case2 xs ih =>
    cases hr : pairDecode xs with
    | none => simp [pairDecode, hr] at h
    | some p =>
      rcases p with ⟨ys, tail⟩
      simp only [pairDecode, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simpa [pairEncode] using congrArg (fun zs => true :: true :: zs) (ih ys hr)
  | case3 xs =>
    simp only [pairDecode, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | case4 xs h₁ h₂ h₃ => simp [pairDecode] at h

/-- A unary-first pair `⟨1ⁿ, u⟩` determines both `n` and `u`. -/
lemma pairEncode_replicate_inj {n n' : ℕ} {u u' : List Bool}
    (h : pairEncode (List.replicate n true) u = pairEncode (List.replicate n' true) u') :
    n = n' ∧ u = u' := by
  have := pairEncode_injective (a₁ := (List.replicate n true, u))
    (a₂ := (List.replicate n' true, u')) h
  simp only [Prod.mk.injEq] at this
  obtain ⟨h1, h2⟩ := this
  exact ⟨by simpa using congrArg List.length h1, h2⟩

/-- The binary expansion of `m` has at most `m` bits. -/
lemma length_bits_le_self (m : ℕ) : m.bits.length ≤ m := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

/-- Six-state pairing controller: double-stay, double-move, emit-true,
first-left, rewind, and copy. The double-stay state's blank branch emits `false`. -/
private def pairDiagTM : FinTM Bool where
  k := 0
  State := Fin 6
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        match q with
        | 0 => match inp with
          | some b => ⟨.zero, fun i => i.elim0, some b, some 1⟩
          | none => ⟨.zero, fun i => i.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun i => i.elim0, inp, some 0⟩
        | 2 => ⟨.zero, fun i => i.elim0, some true, some 3⟩
        | 3 => ⟨.neg, fun i => i.elim0, none, some 4⟩
        | 4 => match inp with
          | some _ => ⟨.neg, fun i => i.elim0, none, some 4⟩
          | none => ⟨.pos, fun i => i.elim0, none, some 5⟩
        | _ => match inp with
          | some b => ⟨.pos, fun i => i.elim0, some b, some 5⟩
          | none => ⟨.zero, fun i => i.elim0, none, none⟩ }

/-- A pairing-machine configuration, with its vacuous work-tape fields suppressed. -/
private def pairDiagCfg (x : List Bool) (q : Option (Fin 6))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin 6) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- One live transition of the pairing controller, given its scanned input symbol. -/
private lemma pairDiag_step (x : List Bool) (q : Fin 6)
    (p : Fin (x.length + 2)) (out : List Bool) (b : Option Bool)
    (hb : (pairDiagCfg x (some q) p out).inputSymbol = b) :
    pairDiagTM.tm.step (pairDiagCfg x (some q) p out) =
      let a := pairDiagTM.tm.tr q b (fun i => i.elim0)
      pairDiagCfg x a.state (moveInputPos p a.inputTape) (out ++ a.output.toList) := by
  change (pairDiagTM.tm.tr q (pairDiagCfg x (some q) p out).inputSymbol
    (pairDiagCfg x (some q) p out).workTapeSymbols).apply _ = _
  rw [hb]
  exact Cfg.ext_zero_tapes rfl rfl rfl

/-- At position `j + 1`, the pairing machine reads the `j`-th input bit. -/
private lemma pairDiag_inner (x : List Bool) (q : Option (Fin 6)) (out : List Bool)
    (j : ℕ) (hj : j < x.length) :
    (pairDiagCfg x q ⟨j + 1, by omega⟩ out).inputSymbol = some x[j] :=
  inputSymbolInner j (by simp only [pairDiagCfg]; omega) hj

/-- At the right boundary the pairing machine reads blank, also on empty input. -/
private lemma pairDiag_right (x : List Bool) (q : Option (Fin 6)) (out : List Bool) :
    (pairDiagCfg x q ⟨x.length + 1, by omega⟩ out).inputSymbol = none := by
  simp [pairDiagCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- After `2t` transitions, the first pass has doubled exactly the first `t` bits.

**Proof sketch.** Induct on `t`. Each bit is first emitted without moving and then
emitted again while moving right. The two emissions extend the doubled prefix. -/
private lemma pairDiag_double (x : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (2 * t) =
      pairDiagCfg x (some 0) ⟨t + 1, by omega⟩ ((x.take t).flatMap fun b => [b, b]) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagTM, pairDiagCfg, MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 0) _ t (by omega))]
    simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
    rw [pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 1) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (((x.take t).flatMap fun b => [b, b]) ++ [x[t]]) ++ [x[t]] =
        (x.take (t + 1)).flatMap fun b => [b, b]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Rewinding from position `j ≤ n` takes `j + 1` steps and preserves the output.

**Proof sketch.** At position zero, move right and enter the copy state. At a
positive position at most `n`, the read is a symbol, so move left and apply the
induction hypothesis. The preceding unconditional left step reaches this range. -/
private lemma pairDiag_rewind (x out : List Bool) : ∀ j, (hj : j ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 4) ⟨j, by omega⟩ out) (j + 1) =
      pairDiagCfg x (some 5) 1 out := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      pairDiag_step _ _ _ _ none (by simp [pairDiagCfg, Cfg.inputSymbol])]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Cfg.ext_zero_tapes
    · rfl
    · apply Fin.ext; simp [pairDiagCfg]
    · rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step,
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 4) out j (by omega))]
    simp only [pairDiagTM, Option.toList_none, List.append_nil]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    simpa using ih (by omega)

/-- The second pass appends the first `t` input bits in `t` transitions.

**Proof sketch.** Induct on `t`, reading at position `t + 1`, appending that bit,
and moving right. The previously emitted doubled word and separator are preserved. -/
private lemma pairDiag_copy (x out : List Bool) : ∀ t, (ht : t ≤ x.length) →
    pairDiagTM.tm.runFrom (pairDiagCfg x (some 5) 1 out) t =
      pairDiagCfg x (some 5) ⟨t + 1, by omega⟩ (out ++ x.take t) := by
  intro t
  induction t with
  | zero =>
    intro _
    apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg]
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      pairDiag_step _ _ _ _ _ (pairDiag_inner x (some 5) _ t (by omega))]
    simp only [pairDiagTM, Option.toList_some]
    rw [moveInputPos_pos_of_ne_right _ (by change t + 1 ≠ x.length + 1; omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · rfl
    · change (out ++ x.take t) ++ [x[t]] = out ++ x.take (t + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simp only [Option.toList_some, List.append_assoc]

/-- Two stationary separator emissions followed by the unconditional first left move.

**Proof sketch.** At the right blank, states 0 and 2 emit `false` and `true`.
State 3 then moves from position `n + 1` to `n`, without emitting a bit. -/
private lemma pairDiag_separator (x out : List Bool) :
    pairDiagTM.tm.runFrom
      (pairDiagCfg x (some 0) ⟨x.length + 1, by omega⟩ out) 3 =
      pairDiagCfg x (some 4) ⟨x.length, by omega⟩ (out ++ [false, true]) := by
  rw [show 3 = (0 + 1) + 1 + 1 from rfl,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 0) out)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 2) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_some]
  rw [pairDiag_step _ _ _ _ _ (pairDiag_right x (some 3) _)]
  simp only [pairDiagTM, Option.toList_none, List.append_nil]
  rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
  apply Cfg.ext_zero_tapes <;> simp [pairDiagCfg, List.append_assoc]

/-- The complete pairing run is halted with the required output by step `4n + 5`.

**Proof sketch.** Chain the doubled pass (`2n`), the two separator steps and first
left move (`3`), the rewind from position `n` (`n + 1`), the copy (`n`), and the
halting transition (`1`). Each equality records the whole configuration. -/
private lemma pairDiag_run (x : List Bool) :
    pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 5) =
      pairDiagCfg x none ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
  have hd := pairDiag_double x x.length (le_refl _)
  simp only [List.take_length] at hd
  have hr : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (3 * x.length + 4) =
      pairDiagCfg x (some 5) 1 ((x.flatMap fun b => [b, b]) ++ [false, true]) := by
    rw [show 3 * x.length + 4 = 2 * x.length + (3 + (x.length + 1)) by omega,
      MultiTapeTM.runFrom_add, hd, MultiTapeTM.runFrom_add, pairDiag_separator,
      pairDiag_rewind x _ x.length (le_refl _)]
  have hc : pairDiagTM.tm.runFrom (pairDiagTM.tm.initCfg x) (4 * x.length + 4) =
      pairDiagCfg x (some 5) ⟨x.length + 1, by omega⟩ (pairEncode x x) := by
    rw [show 4 * x.length + 4 = (3 * x.length + 4) + x.length by omega,
      MultiTapeTM.runFrom_add, hr, pairDiag_copy x _ x.length (le_refl _)]
    simp only [List.take_length, pairEncode]
  rw [show 4 * x.length + 5 = (4 * x.length + 4) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', hc,
    pairDiag_step _ _ _ _ _ (pairDiag_right x (some 5) _)]
  simp only [pairDiagTM, SignType.zero_eq_zero, moveInputPos_zero, Option.toList_none, List.append_nil]

/-- The diagonal pairing `α ↦ pairEncode α α` — the self-application input of the
`HALT` reduction [AB09, proof of Theorem 1.11] — is computable in linear time. This
is the *only* computation on codes that reduction needs (phase-3 audit, round 2,
Argument F): `encode` itself is never computed by any machine of this development.

**Proof sketch.** Two sweeps of the input with a constant number of states. Pass one
walks the input left to right emitting each bit twice — one emitted symbol per
transition, so two steps per bit: emit staying put, emit moving right; on reading the
right boundary blank it emits the separator `false`, `true` (two steps) and rewinds
the input head to the start (one step left, then left while reading a symbol, then
one step right — the clamp at position `0` makes this safe, including on empty
input). Pass two walks the input again emitting each bit once, and halts on the
boundary blank. Total on inputs of length `n`: `2n` (doubled pass) `+ 2` (separator)
`+ (n + 2)` (rewind) `+ n` (second pass) `+ 1` (halt) `= 4n + 5 ≤ 6 · (n + 1)`
(phase-4 audit, finding 1: an earlier `3n + 6` figure undercounted the doubled
pass), absorbed as `c * (n + 1)`. -/
theorem computesFunInTime_pairEncode_diag :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun α => pairEncode α α) fun n => c * (n + 1) := by
  refine ⟨pairDiagTM, 6, fun x => ?_⟩
  have h : pairDiagTM.ComputesInTime x (pairEncode x x) (4 * x.length + 5) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [pairDiag_run]; rfl
    · rw [pairDiag_run]; rfl
  exact h.mono (by change 4 * x.length + 5 ≤ 6 * (x.length + 1); omega)

section Serialize

/-- Fixed two-bit serialization of a head move. -/
def signBits : SignType → List Bool
  | .neg => [true, true]
  | .zero => [false, false]
  | .pos => [true, false]

/-- Fixed two-bit serialization of an optional bit. -/
def optBoolBits : Option Bool → List Bool
  | none => [false, false]
  | some false => [true, false]
  | some true => [true, true]

/-- Fixed two-bit serialization of an optional write (which may itself write blank). -/
def optOptBoolBits : Option (Option Bool) → List Bool
  | none => [false, false]
  | some none => [false, true]
  | some (some false) => [true, false]
  | some (some true) => [true, true]

/-- Self-delimiting unary serialization of a state index. -/
def unaryFin {n : ℕ} (s : Fin n) : List Bool :=
  List.replicate (s : ℕ) true ++ [false]

/-- Serialization of an optional successor state (`none` = halt). -/
def optStateBits {n : ℕ} : Option (Fin n) → List Bool
  | none => [false]
  | some s => true :: unaryFin s

/-- Serialization of one transition record. -/
def actionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++ optOptBoolBits (a.workTapes 0).1 ++
    signBits (a.workTapes 0).2 ++ optBoolBits a.output ++ optStateBits a.state

/-- The **fixed, scheme-independent** canonical serialization of a coded machine: the
state count (self-delimiting via `pairEncode`'s doubled-bit region), then the initial
state (audit finding 5: it must be recorded — machines with equal tables and
different initial states differ), then the full transition table in the fixed
enumeration order (states in `Fin` order; input read and work read each ranging over
`none`, `some false`, `some true`). This is the target format of
`EffectiveMachineCode.canonizer`, which is what ties a scheme's `decode` to effective
semantics (audit finding 1). -/
def CodeTM.serialize (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w))

end Serialize

/-- The algebraic laws of a representation scheme for coded machines [AB09, §1.4]: a
total decoding (every string represents some machine — property 1), an encoding, and
recovery of the machine from its code under arbitrary `true`-padding (hence every
machine has infinitely many representations — property 2).

These laws alone do **not** support universal simulation — see the module docstring
and `Turing.EffectiveMachineCode`. -/
structure MachineCode where
  /-- encode a machine as a binary string, `⌞M⌟` -/
  encode : CodeTM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → CodeTM
  /-- a code followed by any amount of `true`-padding decodes to the machine
  (property 2: infinitely many representations) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine ([AB09, §1.4]; padding by zero symbols). -/
theorem MachineCode.decode_encode (c : MachineCode) (M : CodeTM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme: the algebraic laws together with a machine
of this development that computes the fixed serialization of the decoded machine,
within some time bound depending only on the code's length.

The target `CodeTM.serialize` is scheme-independent, which is essential: requiring
only a canonizer into the scheme's *own* `encode` is still satisfied by the
noncomputable-meaning pathology of audit Argument A, whereas computing
`serialize ∘ decode` for that pathology would decide an undecidable set, so no such
machine exists and the pathology is excluded. -/
structure EffectiveMachineCode extends MachineCode where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's time bound (arbitrary here; universal-machine constants absorb
  its value at each fixed code) -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- Every one-work-tape binary machine is equivalent, input by input and step for
step, to a coded machine.

**Proof sketch.** `State` carries `Fintype`/`DecidableEq` instances and is inhabited
by `q₀`, so `Fintype.equivFin` gives `e : State ≃ Fin n` with `n = numStates + 1` for
some `numStates`. Transport the transition function along `e` (renaming states with
`Turing.Action.mapState` and reading them back through `e.symm`); the induced map on
configurations is a bijection commuting with `step` (the tapes and heads are
untouched), so runs, halting, and outputs correspond at every step. The tape-count
cast uses `hk : M.k = 1`.

The implementation uses `Turing.MultiTapeTM.relabelState` (the shared state-renaming
module, `TCSlib.Complexity.TuringMachine.StateRenaming`), eliminates `hk` after
destructuring the bundle, and concludes with
`Turing.MultiTapeTM.relabelState_runFrom_init`. -/
theorem exists_codeTM (M : FinTM Bool) (hk : M.k = 1) :
    ∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ),
      M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t := by
  classical
  rcases M with @⟨k, Q, hQ, dQ, tm⟩
  dsimp only at hk
  subst k
  letI : Fintype Q := hQ
  letI : DecidableEq Q := dQ
  have hcard : Fintype.card Q = (Fintype.card Q - 1) + 1 := by
    have : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨tm.q₀⟩
    omega
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨Fintype.card Q - 1, tm.relabelState e⟩, ?_⟩
  intro x output t
  simp only [CodeTM.toFinTM, FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace,
    MultiTapeTM.relabelState_runFrom_init, Cfg.mapState, Option.map_eq_none_iff]
  constructor
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩
  · rintro ⟨s, hhalt, hout, -⟩
    exact ⟨_, hhalt, hout, rfl⟩

end Turing

```


## ===== TCSlib/Complexity/TimeHierarchy/Diagonal.lean =====

```
/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.TimeHierarchy.ClockLoop
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.MathlibBridge
import TCSlib.Complexity.TuringMachine.Universal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Time Hierarchy Theorem

[AB09, Theorem 3.1]: if `f, g` are time-constructible functions with
`f(n) log f(n) = o(g(n))`, then `DTIME(f) ⊊ DTIME(g)`. This file proves the theorem
in the form supported by this development's universal machine:

  if `g` is time constructible and `(f(n) + n + 1)² = o(g(n))`, then
  `DTIME(f) ⊊ DTIME(g + 1)`.

## The diagonal language

Fix the effective representation scheme `code` and the universal machine `univTM`
(`Turing.universal`). The simulator `diagSim` composes the prefix-duplication machine
`preTM` with `univTM`; on an input `x = pairEncode α w` it runs the machine coded by
`α` on `x` itself. The diagonal language is

  `diagLang g = {x | diagSim does not halt on x with output [true] within g(|x|) steps}`,

decided within `O(g(n))` by the clocked runner `clockTM K diagSim`, where `K` is the
time-constructibility witness of `g` (`diagLang_mem_DTIME`). If a machine `M`
decided `diagLang g` within `c·T(n)`, take a code `α` of its one-work-tape normal form
and the inputs `x = pairEncode α 1^m`: the simulation of `M` on `x` finishes within
`A·(T(n) + n + 1)²` steps for a constant `A` depending only on `M`, which is at most
`g(n)` for suitable `n` — and then `diagSim`'s verdict on `x` contradicts `M`'s
(`diagLang_not_mem_DTIME`).

## Divergences from [AB09, Theorem 3.1]

* **Overhead `f²` instead of `f log f`.** The book's universal machine has
  `O(T log T)` overhead ([AB09, Theorem 1.9 / §1.7]); this development's universal
  machine is linear on coded machines but coded machines are one-work-tape binary
  machines, and an arbitrary binary machine is normal-formed with quadratic slowdown
  (`Turing.FinTM.one_work_tape_binary`, [AB09, Claims 1.5–1.6]). The hypothesis is
  therefore `(f(n) + n + 1)² = o(g(n))`, written out as
  `∀ A, ∃ N, ∀ n ≥ N, A · (f n + n + 1)² ≤ g n`. The `+ n + 1` absorbs the linear
  cost of reading the input and the `+ 1` normalization of `DTIME` bounds. The
  sharper `f log f` form is out of reach until the `O(T log T)` simulation (phase-5
  stretch goal of the Chapter 1 plan) exists.
  Because of the `+ n + 1` term the hypothesis forces `g(n) = ω(n²)`, so finer
  separations below the quadratic threshold — e.g. the book's illustration
  `DTIME(n) ⊊ DTIME(n^1.5)` — are **not** derivable from this theorem; the best
  linear-time separation it yields is roughly `DTIME(n) ⊊ DTIME(n^(2+ε))`.
* **No time-constructibility hypothesis on `f`** — none is needed (the book assumes
  it only for symmetry).
* **`DTIME(g + 1)` instead of `DTIME(g)`.** `TimeConstructible g` permits `g 0 = 0`,
  and `DTIME` of a bound vanishing anywhere is empty
  (`Complexity.DTIME_eq_empty_of_exists_zero`); the `+ 1` repairs this degenerate
  case only (for `n ≥ 1`, `g n ≥ n ≥ 1`).
* **Padding the input, not the code.** The book uses that every machine has
  infinitely many codes. Here the universal machine's constant depends on the code
  string (`Turing.universal` — the canonizer time of the representation scheme is an
  opaque bound), so the diagonal argument fixes one code `α` and pads the *input*
  `pairEncode α 1^m`; the code is recovered from the input by `preTM`.
* **The clock counts the diagonal machine's own simulation steps**, via the clocked
  runner `Complexity.TimeHierarchy.clockTM`.
* The separation is proved in the stronger *infinitely-often* form:
  `diagLang_not_mem_DTIME` needs `A · (T n + n + 1)² ≤ g n` only for infinitely many
  `n`, for each `A`.

## Main definitions

* `Complexity.TimeHierarchy.code`, `univTM`, `diagSim` — the fixed scheme, universal
  machine, and simulator.
* `Complexity.TimeHierarchy.diagLang` — the diagonal language.

## Main results

* `Complexity.TimeHierarchy.diagLang_mem_DTIME` — `diagLang g ∈ DTIME (g + 1)`.
* `Complexity.TimeHierarchy.diagLang_not_mem_DTIME` — `diagLang g ∉ DTIME T` whenever
  `A · (T n + n + 1)² ≤ g n` infinitely often for every `A`.
* `Complexity.time_hierarchy` — [AB09, Theorem 3.1], in the form above.
* `Complexity.time_hierarchy_of_pos` — the same with `DTIME g` when `g` never vanishes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.1, Theorem 3.1, pp. 69–70; §1.4.)
-/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-- The fixed effective representation scheme of the hierarchy construction (any
scheme works; `Turing.exists_effectiveMachineCode` provides one). -/
noncomputable def code : EffectiveMachineCode := Classical.choice exists_effectiveMachineCode

/-- The universal machine for `code`, from `Turing.universal`. -/
noncomputable def univTM : FinTM Bool := Classical.choose (universal code)

/-- The universal machine's specification (`Turing.universal`). -/
lemma univTM_spec : ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
    (∀ (output : List Bool) (t : ℕ),
      (code.decode α).toFinTM.ComputesInTime x output t →
      univTM.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
    (∀ output : List Bool,
      (∃ t, univTM.ComputesInTime (pairEncode α x) output t) →
      ∃ t, (code.decode α).toFinTM.ComputesInTime x output t) :=
  Classical.choose_spec (universal code)

/-- The diagonal simulator: duplicate the code prefix (`preTM`), then run the
universal machine. On `x = pairEncode α w` it runs the machine coded by `α` on `x`. -/
noncomputable def diagSim : FinTM Bool := bufferedCompTM preTM univTM

/-- **The diagonal language** of the hierarchy theorem [AB09, Theorem 3.1, proof]:
the strings `x` on which the diagonal simulator does **not** halt with output `[true]`
within `g(|x|)` steps. -/
def diagLang (g : ℕ → ℕ) : Language Bool :=
  {x | ¬diagSim.ComputesInTime x [true] (g x.length)}

/-- **The diagonal language is decidable in time `O(g)`** [AB09, Theorem 3.1, proof:
"`D` runs in time `O(g(n))`"]: for time-constructible `g`,
`diagLang g ∈ DTIME (g + 1)`.

**Proof sketch.** Run the clocked runner `clockTM K diagSim`, with `K` the
time-constructibility witness of `g`: its budget word is `bits (g n)` of value `g n`,
so by `clockTM_spec` it outputs `[x ∈ diagLang g]` within
`c_K (g n + 1) + 4|bits (g n)| + n + 4 g n + 6 ≤ (c_K + 15)(g n + 1)` steps, using
`|bits m| ≤ m` and `n ≤ g n`. -/
theorem diagLang_mem_DTIME {g : ℕ → ℕ} (hg : TimeConstructible g) :
    diagLang g ∈ DTIME (fun n => g n + 1) := by
  classical
  obtain ⟨hgn, cK, _, K, hK⟩ := hg
  refine ⟨cK + 15, clockTM K diagSim, fun x => ?_⟩
  have h := clockTM_spec K diagSim x (g x.length).bits _ (hK x)
  rw [ctrVal_bits] at h
  have hout : [!(decide (diagSim.ComputesInTime x [true] (g x.length)))] =
      [MultiTapeTM.indicator (diagLang g : Set (List Bool)) x] := by
    by_cases hx : diagSim.ComputesInTime x [true] (g x.length)
    · have : x ∉ (diagLang g : Set (List Bool)) := fun h' => h' hx
      simp [MultiTapeTM.indicator, hx, this]
    · have : x ∈ (diagLang g : Set (List Bool)) := hx
      simp [MultiTapeTM.indicator, hx, this]
  rw [hout] at h
  apply h.mono
  have h1 := length_bits_le_self (g x.length)
  have h2 := hgn x.length
  nlinarith

/-- The polynomial bookkeeping of the diagonal argument: with `X = T + n + 1`, the
simulation cost `5n + 7 + C · (c₁ (c₀ T + 1)² + 1)` is at most
`(8 + C (c₁ (c₀ + 1)² + 1)) · X²`. -/
lemma diag_cost_le (n T c₀ c₁ C : ℕ) :
    5 * n + 7 + C * (c₁ * (c₀ * T + 1) ^ 2 + 1) ≤
      (8 + C * (c₁ * (c₀ + 1) ^ 2 + 1)) * (T + n + 1) ^ 2 := by
  have hX : 1 ≤ T + n + 1 := by omega
  have hX2 : T + n + 1 ≤ (T + n + 1) ^ 2 := by nlinarith
  have hlin : c₀ * T + 1 ≤ (c₀ + 1) * (T + n + 1) := by nlinarith
  have hsq : (c₀ * T + 1) ^ 2 ≤ (c₀ + 1) ^ 2 * (T + n + 1) ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hlin 2
  have hone : 1 ≤ (T + n + 1) ^ 2 := by nlinarith
  have hinner : c₁ * (c₀ * T + 1) ^ 2 + 1 ≤ (c₁ * (c₀ + 1) ^ 2 + 1) * (T + n + 1) ^ 2 := by
    have := Nat.mul_le_mul_left c₁ hsq
    nlinarith
  have hC := Nat.mul_le_mul_left C hinner
  nlinarith

/-- **The diagonal language is not in `DTIME T`** [AB09, Theorem 3.1, proof: "`D`
differs from every machine running in time `f`"], provided `g` dominates
`A · (T n + n + 1)²` for infinitely many `n`, for every constant `A`.

**Proof sketch.** Suppose `M` decides `diagLang g` within `c₀ T(n)`. Normal-form `M`
to a one-work-tape binary machine (time `c₁ (c₀ T + 1)²`,
`Turing.FinTM.one_work_tape_binary`), relabel it to a coded machine `N`
(`Turing.exists_codeTM`), and let `α = ⌞N⌟`; let `C` be the universal machine's
constant for `α`. With `A = 8 + C (c₁ (c₀ + 1)² + 1)` pick `n ≥ 2|α| + 2` with
`A (T n + n + 1)² ≤ g n` and put `x = pairEncode α 1^(n - 2|α| - 2)`, so `|x| = n`.
Then `preTM` maps `x` to `pairEncode α x` (`scanPre_pairEncode_append`), on which
`univTM` simulates `N` on `x`, producing `M`'s verdict `[χ(x)]`; altogether `diagSim`
halts on `x` with `[χ(x)]` within `5n + 7 + C(c₁(c₀T + 1)² + 1) ≤ g n` steps
(`bufferedCompTM_computesInTime`, `diag_cost_le`). If `χ(x) = true` then
`x ∈ diagLang g`, i.e. `diagSim` does *not* output `[true]` within `g n` — a
contradiction; if `χ(x) = false` then `x ∉ diagLang g`, so `diagSim` outputs `[true]`
within `g n`, contradicting determinism of its output `[false]`. -/
theorem diagLang_not_mem_DTIME {g T : ℕ → ℕ}
    (hT : ∀ A N : ℕ, ∃ n ≥ N, A * (T n + n + 1) ^ 2 ≤ g n) :
    diagLang g ∉ DTIME T := by
  classical
  rintro ⟨c₀, M, hM⟩
  let χ := MultiTapeTM.indicator (diagLang g : Set (List Bool))
  obtain ⟨M₁, c₁, hk, h₁⟩ :=
    one_work_tape_binary M (fun x => [χ x]) (fun n => c₀ * T n) hM
  obtain ⟨N, hN⟩ := exists_codeTM M₁ hk
  let α := code.encode N
  have hdec : code.decode α = N := code.toMachineCode.decode_encode N
  obtain ⟨C, hC⟩ := univTM_spec α
  obtain ⟨n, hn, hgn⟩ := hT (8 + C * (c₁ * (c₀ + 1) ^ 2 + 1)) (2 * α.length + 2)
  let w := List.replicate (n - (2 * α.length + 2)) true
  let x := pairEncode α w
  have hx : x.length = n := by
    simp only [x, w, length_pairEncode, List.length_replicate]; omega
  -- the simulated decider
  have hNx : (code.decode α).toFinTM.ComputesInTime x [χ x]
      (c₁ * (c₀ * T n + 1) ^ 2) := by
    rw [hdec, hN]
    have := h₁ x
    rw [hx] at this
    exact this
  have hU := (hC x).1 [χ x] _ hNx
  have hP := preTM_computes x
  rw [show scanPre x ++ x = pairEncode α x from scanPre_pairEncode_append α w] at hP
  have hD := bufferedCompTM_computesInTime preTM univTM hP hU
  have hlen : (pairEncode α x).length ≤ 2 * n := by
    rw [length_pairEncode, hx]; omega
  have hD' : diagSim.ComputesInTime x [χ x] (g x.length) := by
    apply hD.mono
    rw [hx]
    have := diag_cost_le n (T n) c₀ c₁ C
    calc 3 * n + 5 + (pairEncode α x).length + 2 + C * (c₁ * (c₀ * T n + 1) ^ 2 + 1)
        ≤ 5 * n + 7 + C * (c₁ * (c₀ * T n + 1) ^ 2 + 1) := by omega
      _ ≤ _ := this
      _ ≤ g n := hgn
  by_cases hmem : x ∈ (diagLang g : Set (List Bool))
  · have hχ : χ x = true := by simp [χ, MultiTapeTM.indicator, hmem]
    rw [hχ] at hD'
    exact hmem hD'
  · have hχ : χ x = false := by simp [χ, MultiTapeTM.indicator, hmem]
    rw [hχ] at hD'
    have htrue : diagSim.ComputesInTime x [true] (g x.length) := by
      by_contra hc
      exact hmem hc
    have := htrue.output_unique hD'
    simp at this

end Complexity.TimeHierarchy

namespace Complexity

open TimeHierarchy

/-- **The Time Hierarchy Theorem** [AB09, Theorem 3.1], in the form supported by this
development: if `g` is time constructible and `(f(n) + n + 1)² = o(g(n))` — i.e. for
every constant `A`, eventually `A · (f n + n + 1)² ≤ g n` — then
`DTIME(f) ⊊ DTIME(g + 1)`.

Deviations from the book (see the module docstring): the overhead is quadratic
(`(f + n + 1)²` in place of `f log f`), owing to the one-work-tape normal form of
coded machines; `f` need not be time constructible; and the larger class is
`DTIME (g + 1)`, which differs from `DTIME g` only in the degenerate case `g 0 = 0`.

**Proof sketch.** *Inclusion:* the hypothesis with `A = 1` gives `f n ≤ g n` for
`n ≥ N`; the finitely many smaller lengths are absorbed into the constant, so
`f n ≤ c (g n + 1)` for all `n`, and `DTIME` absorbs `c`. *Strictness:* the diagonal
language `diagLang g` lies in `DTIME (g + 1)` (`diagLang_mem_DTIME`) but not in
`DTIME f` (`diagLang_not_mem_DTIME`, whose infinitely-often hypothesis follows from the
eventual one). -/
theorem time_hierarchy {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1) := by
  refine ⟨?_, fun hsub => diagLang_not_mem_DTIME (g := g) (T := f) ?_
    (hsub (diagLang_mem_DTIME hg))⟩
  · -- inclusion
    obtain ⟨N, hN⟩ := hfg 1
    let F := ∑ i ∈ Finset.range N, f i
    have hle : ∀ n, f n ≤ (F + 1) * (g n + 1) := by
      intro n
      by_cases hn : n < N
      · have : f n ≤ F := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr hn)
        nlinarith
      · have h := hN n (by omega)
        have : f n ≤ g n := by nlinarith
        nlinarith
    rintro L ⟨c, M, hM⟩
    exact ⟨c * (F + 1), M, fun x => (hM x).mono (by
      simp only [Nat.mul_assoc]; exact Nat.mul_le_mul_left c (hle x.length))⟩
  · intro A N₀
    obtain ⟨N, hN⟩ := hfg A
    exact ⟨max N N₀, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- **The Time Hierarchy Theorem for a positive bound** [AB09, Theorem 3.1]: as
`Complexity.time_hierarchy`, with the larger class exactly `DTIME g` when `g` never
vanishes (then `DTIME (g + 1) = DTIME g`, the constant `2` being absorbed).

**Proof sketch.** `c (g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so `DTIME (g + 1) ⊆ DTIME g`;
the reverse inclusion is `Complexity.DTIME.mono`; conclude from
`Complexity.time_hierarchy`. -/
theorem time_hierarchy_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n + n + 1) ^ 2 ≤ g n) :
    DTIME f ⊂ DTIME g := by
  have heq : DTIME (fun n => g n + 1) = DTIME g := by
    apply Set.Subset.antisymm
    · rintro L ⟨c, M, hM⟩
      refine ⟨2 * c, M, fun x => (hM x).mono ?_⟩
      have := hpos x.length
      dsimp only
      nlinarith
    · exact DTIME.mono (fun n => Nat.le_succ _)
  rw [← heq]
  exact time_hierarchy hg hfg

end Complexity

```


## ===== TCSlib/Complexity/ClassP/TimeConstructible.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time-constructible functions

A function `T : ℕ → ℕ` is *time constructible* if `T n ≥ n` and some machine computes,
on every input `x`, the binary representation of `T |x|` within at most
`c · (T |x| + 1)` steps for a positive constant `c`. [AB09, §1.3, with the audit-mandated
budget repair below.] Time constructibility rules out pathological time bounds. It is
needed when a machine must *generate* a step budget from its input length, as in the
hierarchy theorems; note that the timed universal machine of [AB09, p. 21] receives its
budget as an explicit extra input and needs no constructibility hypothesis.

## Design and deviations from [AB09]

* Binary representation is `Nat.bits` (least-significant-bit first, with no redundant
  most-significant zeros; `Nat.bits 0 = []`), where [AB09] writes `⌞T(|x|)⌟` without
  fixing endianness. Nothing in Chapter 1 depends on the choice.
* **Deviation (audit-mandated).** [AB09] demands the computation run within exactly
  `T n` steps and then asserts that `n`, `n log n`, `n²`, `2ⁿ` are time constructible.
  The phase-1 external audit (`audits/phase1-findings.md`, finding 1, adversarial cases
  5-6) *proved the literal reading false in this model*: under the exact bound, the
  identity function — [AB09]'s own first example — is not time constructible (on the
  budget `T n = n`, the first transition on `[false]` and `[false, false]` is the same
  function call, and the length-1 budget forces it to halt with output `[true]`, which
  absorption then freezes at length 2), and even `T n = n + 1` fails by an append-only
  prefix argument. We therefore allow a positive constant factor on `T n + 1`, which
  suffices for every downstream use and restores the book's examples *after small-input
  normalization*: the literal `n · ⌈log₂ n⌉`, for instance, still violates `T n ≥ n` at
  `n = 1`, so such examples are stated with a `max`-with-`n` or `+ 1` normalization.
  Exact constants in downstream results must be derived from this form, not inherited
  from the strict reading.

## Main definitions

* `Complexity.TimeConstructible` — [AB09, §1.3], with the constant-slack repair above.

## Main results

* `Complexity.timeConstructible_id` — the identity function is time constructible,
  restoring [AB09]'s example under the repaired definition.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3, "Time-constructible functions".)
-/

namespace Complexity

open Turing

/-- `T` is time constructible: `T n ≥ n`, and some finite binary machine computes
`x ↦ ⌞T |x|⌟` (binary via `Nat.bits`) within `c · (T |x| + 1)` steps for a positive
constant `c`. [AB09, §1.3], with the constant-slack deviation documented in the module
docstring (the literal exact-`T n` bound is refuted in this model by
`audits/phase1-findings.md`, finding 1). -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ T n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool, ∀ x : List Bool,
    M.ComputesInTime x (T x.length).bits (c * (T x.length + 1))

/-- Increment a little-endian binary word, extending it on overflow. -/
private def counterInc : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: counterInc bs

/-- The number of initial true bits cleared by an increment. -/
private def counterCarry : List Bool → ℕ
  | true :: bs => counterCarry bs + 1
  | _ => 0

/-- Each cleared true bit decreases the potential by one; the final write adds one.
This is the local accounting identity behind the amortized bound. -/
private lemma counterInc_potential (bs : List Bool) :
    (counterInc bs).count true + counterCarry bs = bs.count true + 1 := by
  induction bs with
  | nil => simp [counterInc, counterCarry]
  | cons b bs ih =>
    cases b with
    | false => simp [counterInc, counterCarry]
    | true => simp [counterInc, counterCarry]; omega

/-- The list increment is exactly successor in `Nat.bits`, including overflow.
**Proof sketch.** Binary induction: a low zero becomes one without a carry; a
low one becomes zero and applies the induction hypothesis to the high part. -/
private lemma counterInc_bits (n : ℕ) : counterInc n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [counterInc]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false =>
      change true :: n.bits = (2 * n + 1).bits
      exact (Nat.bit1_bits n).symm
    | true =>
      simp only [counterInc, ih]
      have he : Nat.bit true n + 1 = 2 * (n + 1) := by simp [Nat.bit_val]; omega
      rw [he, Nat.bit0_bits _ (by omega)]

/-- An increment grows the word by at most one cell, and all cleared cells lie
within the incremented word. -/
private lemma counterInc_length (bs : List Bool) :
    (counterInc bs).length ≤ bs.length + 1 ∧
      counterCarry bs ≤ (counterInc bs).length := by
  induction bs with
  | nil => simp [counterInc, counterCarry]
  | cons b bs ih =>
    cases b <;> simp only [counterInc, counterCarry, List.length_cons] <;> omega

/-- One carry transition, with the first transition also advancing the input. -/
private def counterBump (d : SignType) (w : Option Bool) : Action 1 Bool (Fin 4) :=
  if w = some true then
    ⟨d, fun _ => (some (some false), .pos), none, some 1⟩
  else ⟨d, fun _ => (some (some true), .neg), none, some 2⟩

/-- The audit's four-state counter: count = 0, carry = 1, rewind = 2, emit = 3.
[AB09, §1.3 examples], implemented by the phase-1 reaudit's transition table. -/
private def counterTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp work =>
        if q = 0 then
          match inp with
          | none => ⟨.zero, fun _ => (none, .zero), none, some 3⟩
          | some _ => counterBump .pos (work 0)
        else if q = 1 then counterBump .zero (work 0)
        else if q = 2 then
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .pos), none, some 0⟩
          | some _ => ⟨.zero, fun _ => (none, .neg), none, some 2⟩
        else
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .zero), none, none⟩
          | some b => ⟨.zero, fun _ => (none, .pos), some b, some 3⟩ }

/-- A finite word on nonnegative cells, with a blank at every other cell. -/
private def counterTape (bs : List Bool) (z : ℤ) : Option Bool :=
  if z < 0 then none else bs[z.toNat]?

/-- Canonical configurations for carry, rewind, count, and emission invariants. -/
private def counterCfg (x : List Bool) (q : Fin 4) (p : Fin (x.length + 2))
    (z : ℤ) (bs out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨some q, p, fun _ => counterTape bs, fun _ => z, out⟩

/-- Reading after a prefix gives the head of the remaining word (blank if empty). -/
private lemma counterTape_read (pre bs : List Bool) :
    counterTape (pre ++ bs) pre.length = bs.head? := by
  simp only [counterTape, if_neg (by omega : ¬(pre.length : ℤ) < 0), Int.toNat_natCast,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Replace the first suffix bit, or extend the word if the suffix is empty.
**Proof sketch.** At the write position use the updated value. Before that
position both tapes read the unchanged prefix; afterwards both read the old tail.
Negative cells remain blank. -/
private lemma counterTape_write (pre bs : List Bool) (b : Bool) :
    Function.update (counterTape (pre ++ bs)) (pre.length : ℤ) (some b) =
      counterTape (pre ++ b :: bs.tail) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [counterTape_read]
  · rw [Function.update_of_ne hz]
    unfold counterTape
    by_cases hn : z < 0
    · simp only [if_pos hn]
    · simp only [if_neg hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
          List.getElem?_cons, if_neg (by omega), List.getElem?_tail]
        congr 1
        omega

/-- One carry transition updates exactly the currently scanned cell. -/
private lemma counter_carry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    counterTM.tm.step (counterCfg x 1 p pre.length (pre ++ bs) []) =
      if bs.head? = some true then
        counterCfg x 1 p (pre.length + 1) (pre ++ false :: bs.tail) []
      else counterCfg x 2 p (pre.length - 1) (pre ++ true :: bs.tail) [] := by
  unfold MultiTapeTM.step
  change (counterTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  simp only [counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (counterBump .zero (counterTape (pre ++ bs) pre.length)).apply _ = _
  rw [counterTape_read]
  unfold counterBump
  by_cases h : bs.head? = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext j; exact counterTape_write pre bs _
    · funext j; simp [Action.apply, counterCfg, sub_eq_add_neg]
    · rfl

/-- A carry flips precisely the initial true bits, then writes the final true bit.
**Proof sketch.** Induct on the suffix. The empty suffix and a leading false bit
finish in one step. A leading true bit is replaced by false and included in the
prefix before invoking the induction hypothesis on the tail. -/
private lemma counter_carry (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ pre : List Bool,
    counterTM.tm.runFrom (counterCfg x 1 p pre.length (pre ++ bs) [])
        (counterCarry bs + 1) =
      counterCfg x 2 p ((pre.length : ℤ) + counterCarry bs - 1)
        (pre ++ counterInc bs) [] := by
  induction bs with
  | nil =>
    intro pre
    simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero, counter_carry_step]
    simp [counterInc]
  | cons b bs ih =>
    intro pre
    cases b with
    | false =>
      simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step,
        MultiTapeTM.runFrom_zero, counter_carry_step]
      simp [counterInc]
    | true =>
      simp only [counterCarry, MultiTapeTM.runFrom_succ_eq_step, counter_carry_step,
        List.head?_cons, List.tail_cons, ↓reduceIte]
      have h := ih (pre ++ [false])
      rw [MultiTapeTM.runFrom_succ_eq_step] at h
      simpa [counterInc, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using h

/-- Rewind crosses the written prefix, detects the untouched blank at `-1`, and
returns to cell zero in the count state.
**Proof sketch.** Induct on the number of written cells still to cross.
Each bit causes one left move; at `-1` one right move ends the rewind. -/
private lemma counter_rewind (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ j (_hj : j ≤ bs.length),
    counterTM.tm.runFrom (counterCfg x 2 p ((j : ℤ) - 1) bs []) (j + 1) =
      counterCfg x 0 p 0 bs [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, counterTM, counterCfg, Cfg.workTapeSymbols,
        counterTape, Action.apply]
  | succ j ih =>
    intro hj
    have hw : (counterCfg x 2 p (j : ℤ) bs []).workTapeSymbols 0 = some bs[j] := by
      simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
        if_neg (by omega : ¬(j : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    have hs : counterTM.tm.step (counterCfg x 2 p (j : ℤ) bs []) =
        counterCfg x 2 p ((j : ℤ) - 1) bs [] := by
      unfold MultiTapeTM.step
      change (counterTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      simp only [counterTM, show (2 : Fin 4) ≠ 0 from by decide,
        show (2 : Fin 4) ≠ 1 from by decide, ↓reduceIte, hw]
      apply Cfg.ext
      · rfl
      · exact moveInputPos_zero p
      · rfl
      · funext k; simp [Action.apply, counterCfg, sub_eq_add_neg]
      · rfl
    have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
    rw [he, MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The first carry transition also consumes exactly one input symbol. -/
private lemma counter_start (x : List Bool) (i : ℕ) (hi : i < x.length) (bs : List Bool) :
    counterTM.tm.step (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []) =
      counterTM.tm.step (counterCfg x 1 ⟨i + 2, by omega⟩ 0 bs []) := by
  have hs : (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [counterCfg]; omega) hi
  unfold MultiTapeTM.step
  change (counterTM.tm.tr (0 : Fin 4) _ _).apply _ =
    (counterTM.tm.tr (1 : Fin 4) _ _).apply _
  rw [hs]
  simp only [counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (counterBump .pos (counterTape bs 0)).apply _ =
    (counterBump .zero (counterTape bs 0)).apply _
  unfold counterBump
  by_cases h : counterTape bs 0 = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val =
        (moveInputPos (⟨i + 2, by omega⟩ : Fin (x.length + 2)) 0).val
      rw [moveInputPos_zero, moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rfl
    · rfl
    · rfl

/-- One complete increment takes twice the carry length plus two transitions.
**Proof sketch.** The count transition is the first carry transition, with the
input advanced once. The carry uses `r + 1` steps and leaves the head at `r - 1`;
the rewind uses another `r + 1` steps and leaves the incremented word intact. -/
private lemma counter_increment (x : List Bool) (i : ℕ) (hi : i < x.length)
    (bs : List Bool) :
    counterTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
        (2 * counterCarry bs + 2) =
      counterCfg x 0 ⟨i + 2, by omega⟩ 0 (counterInc bs) [] := by
  have hc : counterTM.tm.runFrom (counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
      (counterCarry bs + 1) =
      counterCfg x 2 ⟨i + 2, by omega⟩ ((counterCarry bs : ℤ) - 1) (counterInc bs) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step, counter_start x i hi,
      ← MultiTapeTM.runFrom_succ_eq_step]
    simpa only [List.length_nil, Nat.cast_zero, zero_add, List.nil_append] using
      counter_carry x ⟨i + 2, by omega⟩ bs []
  rw [show 2 * counterCarry bs + 2 = (counterCarry bs + 1) + (counterCarry bs + 1) by omega,
    MultiTapeTM.runFrom_add, hc]
  exact counter_rewind x ⟨i + 2, by omega⟩ (counterInc bs) (counterCarry bs)
    (counterInc_length bs).2

/-- The counting invariant carries a nonnegative potential of twice the popcount.
**Proof sketch.** Initially both elapsed time and potential are zero. An increment
with `r` cleared bits costs `2r + 2` steps and changes the potential by `2 - 2r`.
Thus elapsed time plus potential increases by exactly four per input symbol.
The semantic invariant records the exact canonical binary word and head positions. -/
private lemma counter_count (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      counterTM.tm.runFrom (counterTM.tm.initCfg x) t =
        counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_⟩
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp [MultiTapeTM.initCfg, counterCfg, counterTape]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc⟩ := ih (by omega)
    refine ⟨t + 2 * counterCarry i.bits + 2, ?_, ?_⟩
    · have hp := counterInc_potential i.bits
      rw [counterInc_bits] at hp
      omega
    · rw [show t + 2 * counterCarry i.bits + 2 = t + (2 * counterCarry i.bits + 2) by omega,
        MultiTapeTM.runFrom_add, hc, counter_increment x i (by omega), counterInc_bits]

/-- The emit phase appends exactly the stored prefix, one bit per step.
**Proof sketch.** Induct on the emitted length, using the nonblank cell at each
index below the word length; the tape contents and input position never change. -/
private lemma counter_emit_run (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ i (_hi : i ≤ bs.length),
    counterTM.tm.runFrom (counterCfg x 3 p 0 bs []) i =
      counterCfg x 3 p i bs (bs.take i) := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (counterCfg x 3 p i bs (bs.take i)).workTapeSymbols 0 = some bs[i] := by
      simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
        if_neg (by omega : ¬(i : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    unfold MultiTapeTM.step
    change (counterTM.tm.tr (3 : Fin 4) _ _).apply _ = _
    simp only [counterTM, show (3 : Fin 4) ≠ 0 from by decide,
      show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
      ↓reduceIte, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · rfl
    · funext j; simp [Action.apply, counterCfg]
    · simp only [Action.apply, counterCfg]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- At the first blank after the stored word, emission halts without extra output. -/
private lemma counter_emit (x : List Bool) (p : Fin (x.length + 2)) (bs : List Bool) :
    let c := counterTM.tm.runFrom (counterCfg x 3 p 0 bs []) (bs.length + 1)
    c.state = none ∧ c.output = bs := by
  have hw : (counterCfg x 3 p bs.length bs (bs.take bs.length)).workTapeSymbols 0 =
      none := by
    simp only [counterCfg, Cfg.workTapeSymbols, counterTape,
      if_neg (by omega : ¬(bs.length : ℤ) < 0), Int.toNat_natCast]
    exact List.getElem?_eq_none (le_refl _)
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step', counter_emit_run x p bs bs.length (le_refl _)]
  unfold MultiTapeTM.step
  change ((counterTM.tm.tr (3 : Fin 4) _ _).apply _).state = none ∧ _
  simp only [counterTM, show (3 : Fin 4) ≠ 0 from by decide,
    show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    ↓reduceIte, hw]
  simp [Action.apply, counterCfg]

/-- The identity function is time constructible. [AB09, §1.3 examples]

**Proof sketch.** A one-work-tape machine maintains a little-endian binary counter on
its work tape while scanning the input left to right: for each input symbol it
increments the counter (walking right over `true` cells turning them `false` until the
first `false`/blank cell, which becomes `true`, then returning to cell 0). Incrementing
`n` times costs amortized `O(1)` per increment, `O(n)` in total. When the input head
reads the blank past the input, the machine walks the counter left to right emitting
each bit to the output tape (`O(log n)` steps) and halts. The total is at most
`c · (n + 1)` steps for an absolute constant `c`, and the emitted string is `n.bits`
(for `n = 0` the counter region is empty and nothing is emitted, matching
`Nat.bits 0 = []`). The formal proof uses twice the number of true counter bits as
potential: elapsed time plus potential is at most `4n` after `n` increments.
Entering emission and its final halting transition add two steps; the output length
is at most `n`, so `c = 5` suffices. -/
theorem timeConstructible_id : TimeConstructible id := by
  refine ⟨fun n => le_refl n, 5, by decide, counterTM, fun x => ?_⟩
  obtain ⟨t, ht, hc⟩ := counter_count x x.length (le_refl _)
  have hs : counterTM.tm.step
      (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    have hin : (counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol =
        none := by simp [Cfg.inputSymbol, counterCfg]
    unfold MultiTapeTM.step
    change (counterTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [counterTM, Action.apply, counterCfg]
  have hstart : counterTM.tm.runFrom (counterTM.tm.initCfg x) (t + 1) =
      counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hs]
  have he := counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits
  have hbase : counterTM.ComputesInTime x x.length.bits
      ((t + 1) + (x.length.bits.length + 1)) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.1
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.2
  apply hbase.mono
  have hl := Turing.length_bits_le_self x.length
  change (t + 1) + (x.length.bits.length + 1) ≤ 5 * (x.length + 1)
  omega

end Complexity

```


## ===== TCSlib/Complexity/Uncomputability/Halting.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Composition
import TCSlib.Complexity.TuringMachine.Universal
import TCSlib.Complexity.Uncomputability.Diagonalization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uncomputability of the halting problem

[AB09, §1.5.1, Theorem 1.11]: `HALT` is not computable — proved, as in the book, by
*reduction*: if `HALT` were computable then so would be `UC`, contradicting
[AB09, Theorem 1.10]. This is the chapter's (and history's) first reduction, and the
first consumer of the universal machine `Turing.universal` and of the guarded
composition combinators of `TCSlib.Complexity.TuringMachine.Composition`.

## Design and deviations from [AB09]

* `HALT` takes the pair `⟨α, x⟩` in exactly the universal machine's input format
  `Turing.pairEncode α x` (code first — the phase-3 layout), so the reduction can
  feed pairs it builds straight into the evaluator without re-encoding.
* [AB09] leaves the pairing convention implicit and does not say what `HALT` does on
  strings that are not pairs (the pairing is not surjective); we **totalize by
  `false`** off the image of `pairEncode` — "does not halt".
  `Turing.pairEncode_injective` makes the value on genuine pairs unambiguous
  (`Complexity.HALT_pairEncode_eq_true_iff`), and the reduction only ever evaluates
  `HALT` on genuine pairs, so the off-image convention is immaterial to
  Theorem 1.11. It is *not* immaterial in general — `HALT c [] = false` is a
  convention-dependent equality — so a downstream client evaluating `HALT` on
  arbitrary strings must keep the convention or prove its inputs are genuine pairs
  (phase-4 audit, finding 6).
* "Halts" is rendered as *has a completed output*: `∃ output t, ComputesInTime`.
  This is equivalent to reaching the halting state (every halted configuration has
  some finite output).
* Theorem 1.11 is stated relative to an **effective** scheme
  (`Turing.EffectiveMachineCode`): the reduction runs the universal evaluator,
  which exists only for effective schemes — in contrast to Theorem 1.10, which
  holds for every `Turing.MachineCode`. The reduction itself is a separate lemma
  (`Complexity.UC_computable_of_HALT_computable`), the book's "if `HALT` were
  computable, `UC` would be".

## Main definitions

* `Complexity.HALT` — the halting function. [AB09, §1.5.1]

## Main results

* `Complexity.UC_computable_of_HALT_computable` — the reduction
  [AB09, proof of Theorem 1.11].
* `Complexity.HALT_not_computable` — [AB09, Theorem 1.11].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.5.1, Theorem 1.11, pp. 22-23.)
-/

namespace Complexity

open Turing

open Classical in
/-- The halting function [AB09, §1.5.1]: `HALT c s = true` iff `s` is a pair
`Turing.pairEncode α x` — the universal machine's input format, code first — such
that the machine `α` denotes halts on `x`, i.e. completes *some* output in *some*
number of steps. Strings not of that form (the pairing is not surjective) map to
`false`. -/
noncomputable def HALT (c : MachineCode) (s : List Bool) : Bool :=
  if ∃ α x : List Bool, s = pairEncode α x ∧
      ∃ (output : List Bool) (t : ℕ), (c.decode α).toFinTM.ComputesInTime x output t
  then true else false

/-- `HALT c s = true` iff `s` is a pair `Turing.pairEncode α x` whose denoted
machine halts on `x` — completes some output in some number of steps. -/
theorem HALT_eq_true_iff (c : MachineCode) (s : List Bool) :
    HALT c s = true ↔
      ∃ α x : List Bool, s = pairEncode α x ∧
        ∃ (output : List Bool) (t : ℕ),
          (c.decode α).toFinTM.ComputesInTime x output t := by
  unfold HALT
  split <;> simp_all

/-- On a genuine pair, `HALT` says exactly whether the denoted machine halts:
injectivity of the pairing (`Turing.pairEncode_injective`) identifies the
components. -/
theorem HALT_pairEncode_eq_true_iff (c : MachineCode) (α x : List Bool) :
    HALT c (pairEncode α x) = true ↔
      ∃ (output : List Bool) (t : ℕ),
        (c.decode α).toFinTM.ComputesInTime x output t := by
  rw [HALT_eq_true_iff]
  constructor
  · rintro ⟨α', x', heq, hhalt⟩
    have hp : (α, x) = (α', x') := pairEncode_injective heq
    simp only [Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact hhalt
  · intro hhalt
    exact ⟨α, x, rfl, hhalt⟩

/-- **The reduction** [AB09, proof of Theorem 1.11]: if `HALT` were computable,
`UC` would be. Stated for an effective scheme, whose universal evaluator the
reduction runs.

**Proof sketch** (blueprint: phase-3 audit round 2, Argument F; every ingredient
below is a stated result of this development — the fill is assembly, not new
mathematics). Let `D` compute `fun s => [HALT c.toMachineCode s]`, let `U` be the
evaluator of `Turing.universal c`, and write
`p α := HALT c.toMachineCode (pairEncode α α)`.

1. `Turing.computesFunInTime_pairEncode_diag` gives a machine for the diagonal
   pairing `α ↦ pairEncode α α`; `Turing.FinTM.exists_comp_partial` composes it
   with `D`, and determinism (`Turing.FinTM.ComputesInTime.output_unique`)
   collapses the intermediate string, yielding a machine `D'` computing
   `fun α => [p α]`.
2. `Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]` gives the
   postprocessor `w ↦ if w = [true] then [false] else [true]`; two applications of
   `exists_comp_partial` chain the diagonal pairing, `U`, and the postprocessor
   into a machine `Mt` such that `Mt` halts on `α` with `w'` iff `U` halts on
   `pairEncode α α` with some `w` and `w'` is the postprocessed `w`.
3. `Turing.FinTM.computesFunInTime_const [true]` gives `Mf`, computing the constant
   `[true]`; `Turing.FinTM.exists_cond D' Mt Mf p` assembles the branch machine
   `R`.
4. Correctness of `R` at each `α`: if `p α = false`, then by
   `Complexity.HALT_pairEncode_eq_true_iff` the denoted machine never halts on `α`,
   so `Complexity.UC_eq_true_iff` gives `UC = true`, and the selected branch `Mf`
   outputs exactly `[true]`. If `p α = true`, the same lemma yields a completed
   output `w₀` within some `t₀`; the **forward clause** of `Turing.universal` makes
   `U` halt on `pairEncode α α` with `w₀` (the converse clause is not needed — the
   positive `HALT` answer already guarantees halting), so `Mt` halts on `α` with
   the postprocessed value, and `output_unique` identifies the condition
   `w₀ = [true]` with `Complexity.UC_eq_false_iff`'s, making that value
   `[UC c.toMachineCode α]` in both subcases. Hence `R` computes
   `fun α => [UC c.toMachineCode α]`. -/
theorem UC_computable_of_HALT_computable (c : EffectiveMachineCode)
    (h : Computable fun s => [HALT c.toMachineCode s]) :
    Computable fun α => [UC c.toMachineCode α] := by
  classical
  obtain ⟨D, hD⟩ := h
  obtain ⟨U, hU⟩ := universal c
  obtain ⟨P, _, hP⟩ := computesFunInTime_pairEncode_diag
  obtain ⟨Q, _, hQ⟩ := FinTM.computesFunInTime_ifEq [true] [false] [true]
  obtain ⟨Mf, _, hMf⟩ := FinTM.computesFunInTime_const [true]
  let p : List Bool → Bool := fun α => HALT c.toMachineCode (pairEncode α α)
  let r : List Bool → List Bool := fun w => if w = [true] then [false] else [true]
  -- First decide whether the decoded machine halts on its own code.
  obtain ⟨D', hD'⟩ := FinTM.exists_comp_partial P D
  have hDp : D'.Computes fun α => [p α] := by
    intro α
    exact (hD' α [p α]).2 ⟨pairEncode α α, hP.computes α, hD _⟩
  -- The positive branch evaluates the self-pair and postprocesses its output.
  obtain ⟨PU, hPU⟩ := FinTM.exists_comp_partial P U
  obtain ⟨Mt, hMt⟩ := FinTM.exists_comp_partial PU Q
  have hMt' (α z : List Bool) :
      (∃ t, Mt.ComputesInTime α z t) ↔
        ∃ w, (∃ t, U.ComputesInTime (pairEncode α α) w t) ∧ z = r w := by
    simp only [r, hMt, hPU, hP.computes.exists_computesInTime_iff,
      hQ.computes.exists_computesInTime_iff, exists_eq_left]
  obtain ⟨R, hR⟩ := FinTM.exists_cond D' Mt Mf p hDp
  refine ⟨R, fun α => (hR α _).2 ?_⟩
  cases hp : p α with
  | false =>
    have huc : UC c.toMachineCode α = true := (UC_eq_true_iff _ _).2 (by
      rintro ⟨t, ht⟩
      have htrue : p α = true :=
        (HALT_pairEncode_eq_true_iff _ _ _).2 ⟨[true], t, ht⟩
      simp only [hp, Bool.false_eq_true] at htrue)
    simpa only [hp, Bool.cond_false, huc] using hMf.computes α
  | true =>
    obtain ⟨w, t, hw⟩ := (HALT_pairEncode_eq_true_iff _ _ _).1 hp
    obtain ⟨C, hC⟩ := hU α
    have huw : ∃ s, U.ComputesInTime (pairEncode α α) w s :=
      ⟨C * (t + 1), (hC α).1 w t hw⟩
    have hr : r w = [UC c.toMachineCode α] := by
      by_cases hwtrue : w = [true]
      · have huc : UC c.toMachineCode α = false :=
          (UC_eq_false_iff _ _).2 ⟨t, hwtrue ▸ hw⟩
        simp only [r, if_pos hwtrue, huc]
      · have huc : UC c.toMachineCode α = true := (UC_eq_true_iff _ _).2 (by
          rintro ⟨t', ht'⟩
          exact hwtrue (hw.output_unique ht'))
        simp only [r, if_neg hwtrue, huc]
    have hMtuc := (hMt' α [UC c.toMachineCode α]).2 ⟨w, huw, hr.symm⟩
    simpa only [hp, Bool.cond_true] using hMtuc

/-- **`HALT` is not computable** [AB09, Theorem 1.11]: immediate from the reduction
`Complexity.UC_computable_of_HALT_computable` and the diagonal theorem
`Complexity.UC_not_computable`. -/
theorem HALT_not_computable (c : EffectiveMachineCode) :
    ¬Computable fun s => [HALT c.toMachineCode s] :=
  fun h => UC_not_computable c.toMachineCode (UC_computable_of_HALT_computable c h)

end Complexity

```


## ===== TCSlib/Complexity/ClassNP/EXP.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# EXP and NEXP

[AB09, Claim 2.4 and §2.6.2]: the exponential-time classes. `EXP` is
`⋃ c, DTIME (2^(n^c))` verbatim from Claim 2.4. `NEXP` is defined here in the
certificate form of [AB09, Exercise 2.27] — exponential-length certificates with
a polynomial-time verifier language — mirroring `Complexity.NP`; its equivalence
with the `NTIME` form of §2.6.2 is a phase-2 obligation, once nondeterministic
machines exist.

## Design and deviations from [AB09]

* `NEXP`'s verifier is a language `V ∈ P`: "polynomial time" is measured in the
  length of the padded string `x ++ u`, which is exponential in `|x|` — this is
  the standard certificate rendering and exactly Exercise 2.27's intent.
* **The certificate length is the explicit formula `C · 2^((|x|+1)^c)`** — the
  same phase-1 audit repair as `Complexity.NP` (finding 1, Argument A: an
  abstract `ExpBound` length function admits undecidable classes). `ExpBound`
  survives as a numerical helper only.
* The chain `P ⊆ NP ⊆ EXP ⊆ NEXP` [AB09, Claim 2.4 and §2.6.2] is stated as the
  three individual inclusions below (`P ⊆ NP` lives in `ClassNP/NP.lean`).

## Main definitions

* `Complexity.EXP` — [AB09, Claim 2.4].
* `Complexity.ExpBound`, `Complexity.NEXP` — [AB09, §2.6.2, in the form of
  Exercise 2.27].

## Main results

* `Complexity.P_subset_EXP` — [AB09, Claim 2.4].
* `Complexity.NP_subset_EXP` — certificate enumeration [AB09, Claim 2.4].
* `Complexity.EXP_subset_NEXP` — [AB09, §2.6.2].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 2.4, p. 41; §2.6.2, pp. 56-57;
  Exercise 2.27.)

**Maintainer note (E5 dedup).** The epoch-2 checkpoint's superseded
carry/capture machinery — the `enumCarry*` family, its `enumBump*`/
`enumBuffer_*`/`enumCarryPos*` vocabulary, `enumWord_no_repeat`, and the
`EnumCapture` section's `enumCapture*` family, twenty private
declarations in all — was removed under the epoch-2 gate's binding
live/dead inventory (`audits/ch2-epoch2-resolutions.md`): the
continuation's `exists_loopCfgTM` route replaced it, and the auditor's
kernel walk confirmed it absent from every final target closure. The
live checkpoint route `enumLoop_run` (consumed by `exists_proj_decider`) is
retained unchanged.
-/

namespace Complexity

/-- **The class EXP** [AB09, Claim 2.4]: languages decidable in time `2^(n^c)`
for some constant `c` (up to `DTIME`'s constant-factor slack). -/
def EXP : Set (Language Bool) :=
  ⋃ c : ℕ, DTIME fun n => 2 ^ n ^ c

/-- The bound `p : ℕ → ℕ` is *exponentially bounded*: `p n ≤ C · 2^((n+1)^c)` for
some constants — the certificate-length regime of `NEXP`. -/
def ExpBound (p : ℕ → ℕ) : Prop :=
  ∃ C c : ℕ, ∀ n, p n ≤ C * 2 ^ (n + 1) ^ c

/-- **The class NEXP**, in the certificate form of [AB09, Exercise 2.27]:
certificates of length exactly `C · 2^((|x|+1)^c)` — an explicit formula, per
the phase-1 audit repair — with a verifier language decidable in time
polynomial in the padded string `x ++ u`. The `NTIME` form of [AB09, §2.6.2] and
its equivalence with this one are phase-2 obligations. -/
def NEXP : Set (Language Bool) :=
  {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * 2 ^ (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- **`P ⊆ EXP`** [AB09, Claim 2.4].

**Proof sketch.** `n^c + 1 ≤ 2 · 2^(n^c)` for every `n` (as `n^c < 2^(n^c)`), so
each `DTIME (n^c + 1)` sits inside `DTIME (2 · 2^(n^c)) ⊆ EXP` by
`Complexity.DTIME.mono` and the constant-absorbing `Complexity.DTIME`
definition. -/
theorem P_subset_EXP : P ⊆ EXP := by
  intro L hL
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hL
  have hbound : ∀ n : ℕ, n ^ c + 1 ≤ 2 * 2 ^ n ^ c := by
    intro n
    have hn := Nat.lt_two_pow_self (n := n ^ c)
    omega
  obtain ⟨a, M, hM⟩ := DTIME.mono hbound hc
  refine Set.mem_iUnion.mpr ⟨c, a * 2, M, fun x => ?_⟩
  simpa only [Nat.mul_assoc] using hM x

open Turing Turing.FinTM

/-! ### Private certificate enumeration infrastructure -/

/-- Little-endian value, including leading zeroes at the high end. -/
private def enumValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * enumValue bs + if b then 1 else 0

/-- Increment without extending the width; `none` means exhaustion.
The empty word overflows, so its caller must test it before incrementing. -/
private def enumInc : List Bool → Option (List Bool)
  | [] => none
  | false :: bs => some (true :: bs)
  | true :: bs => (enumInc bs).map (false :: ·)

/-- **The width-`w` little-endian binary word** of `i`: its low `w` bits, least
significant first (high zeros kept). -/
def enumWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, i => decide (i % 2 = 1) :: enumWord w (i / 2)

/-- Every width-`w` word has value strictly below `2^w`. -/
private lemma enumValue_lt (u : List Bool) : enumValue u < 2 ^ u.length := by
  induction u with
  | nil => simp [enumValue]
  | cons b u ih =>
    cases b <;> simp only [enumValue, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, Nat.pow_succ] <;> omega

/-- The representation retains exactly the requested width, even at zero. -/
private lemma enumWord_length (w i : ℕ) : (enumWord w i).length = w := by
  induction w generalizing i with
  | zero => rfl
  | succ w ih => simp only [enumWord, List.length_cons, ih]

/-- The initial rank is represented by precisely the all-false word. -/
private lemma enumWord_zero (w : ℕ) : enumWord w 0 = List.replicate w false := by
  induction w with
  | zero => rfl
  | succ w ih => simp [enumWord, ih, List.replicate_succ]

/-- In range, the representation has the specified value.
**Proof sketch.** Remove the low bit by division by two. The quotient is
in range for the remaining width, and the remainder is either zero or one. -/
private lemma enumWord_value (w i : ℕ) (hi : i < 2 ^ w) :
    enumValue (enumWord w i) = i := by
  induction w generalizing i with
  | zero => simp only [Nat.pow_zero] at hi; simp [enumWord, enumValue, show i = 0 by omega]
  | succ w ih =>
    have hdiv : i / 2 < 2 ^ w := by rw [Nat.pow_succ] at hi; omega
    simp only [enumWord, enumValue, ih (i / 2) hdiv]
    have hmod := Nat.mod_lt i (by omega : 0 < 2)
    split <;> simp_all <;> omega

/-- Equal-length words with the same value are equal, including trailing
false bits. The parity determines the first bit; divide the remainder by two. -/
private lemma enumValue_injective (u v : List Bool) (hlen : u.length = v.length)
    (hval : enumValue u = enumValue v) : u = v := by
  induction u generalizing v with
  | nil => simpa using hlen.symm
  | cons b u ih =>
    cases v with
    | nil => simp at hlen
    | cons b' v =>
      have hlen' : u.length = v.length := by simpa using hlen
      cases b <;> cases b' <;> simp only [enumValue, Bool.false_eq_true, ↓reduceIte] at hval
      all_goals first | omega | exact congrArg (_ :: ·) (ih v hlen' (by omega))

/-- Every word is the unique representative of its rank at its own width. -/
private lemma enumWord_complete (u : List Bool) :
    enumWord u.length (enumValue u) = u := by
  exact enumValue_injective _ _ (enumWord_length _ _)
    (enumWord_value _ _ (enumValue_lt u))

/-- One fixed-width increment either preserves width and adds one to the
value, or reports overflow exactly at the last rank.
**Proof sketch.** A low false bit changes to true. A low true bit is cleared
and passes the carry to the suffix; suffix overflow is total overflow. -/
private lemma enumInc_spec (u : List Bool) :
    match enumInc u with
    | some v => v.length = u.length ∧ enumValue v = enumValue u + 1
    | none => enumValue u + 1 = 2 ^ u.length := by
  induction u with
  | nil => simp [enumInc, enumValue]
  | cons b u ih =>
    cases b with
    | false => simp [enumInc, enumValue]
    | true =>
      cases he : enumInc u with
      | none =>
        simp only [he] at ih
        simp only [enumInc, he, Option.map_none, enumValue, ↓reduceIte,
          List.length_cons, Nat.pow_succ]
        omega
      | some v =>
        simp only [he] at ih
        simp only [enumInc, he, Option.map_some, enumValue, Bool.false_eq_true,
          ↓reduceIte, List.length_cons]
        exact ⟨by omega, by omega⟩

/-- On canonical candidates, increment advances exactly one rank and reports
overflow only after the last rank. This includes width zero. -/
private lemma enumInc_word (w i : ℕ) (hi : i < 2 ^ w) :
    enumInc (enumWord w i) =
      if i + 1 < 2 ^ w then some (enumWord w (i + 1)) else none := by
  have hs := enumInc_spec (enumWord w i)
  rw [enumWord_length, enumWord_value w i hi] at hs
  cases he : enumInc (enumWord w i) with
  | none => simp only [he] at hs; simp [show ¬i + 1 < 2 ^ w by omega]
  | some v =>
    simp only [he] at hs
    have hv := enumValue_lt v
    rw [hs.1, hs.2] at hv
    rw [if_pos hv]
    congr 1
    exact enumValue_injective v _ (hs.1.trans (enumWord_length _ _).symm)
      (hs.2.trans (enumWord_value w (i + 1) hv).symm)

/-- Exact-width existential certificates are exactly the in-range candidates. -/
private lemma enumCandidates_iff (w : ℕ) (p : List Bool → Prop) :
    (∃ u, u.length = w ∧ p u) ↔ ∃ i, i < 2 ^ w ∧ p (enumWord w i) := by
  constructor
  · rintro ⟨u, rfl, hu⟩
    exact ⟨enumValue u, enumValue_lt u, by simpa only [enumWord_complete] using hu⟩
  · rintro ⟨i, hi, hp⟩
    exact ⟨enumWord w i, enumWord_length w i, hp⟩

/-- Boolean result of testing `count` consecutive candidate ranks, starting
with `i`. The recursive branch represents one rejected call. -/
private def enumAny (accept : ℕ → Bool) (i : ℕ) : ℕ → Bool
  | 0 => false
  | count + 1 => if accept i then true else enumAny accept (i + 1) count

/-- The abstract loop accepts exactly when an in-range candidate accepts.
**Proof sketch.** Separate the first rank from the remaining interval. -/
private lemma enumAny_iff (accept : ℕ → Bool) (i count : ℕ) :
    enumAny accept i count = true ↔
      ∃ j, i ≤ j ∧ j < i + count ∧ accept j = true := by
  induction count generalizing i with
  | zero =>
    simp only [enumAny, Bool.false_eq_true, false_iff]
    rintro ⟨j, hj, hj', _⟩
    omega
  | succ count ih =>
    change (if accept i then true else enumAny accept (i + 1) count) = true ↔ _
    by_cases h : accept i = true
    · simp only [if_pos h, true_iff]
      exact ⟨i, le_refl _, by omega, h⟩
    · rw [if_neg h, ih]
      constructor
      · rintro ⟨j, hj, hj', ha⟩
        exact ⟨j, by omega, by omega, ha⟩
      · rintro ⟨j, hj, hj', ha⟩
        have hne : j ≠ i := by intro he; subst j; exact h ha
        exact ⟨j, by omega, by omega, ha⟩

/-- For the actual verifier's indicator, testing all ranks gives exactly the
definition's existential over certificates of width `w`. This is independent
of the machine implementation, and includes width zero. -/
private lemma enumAny_certificates (x : List Bool) (w : ℕ) (V : Language Bool) :
    enumAny (fun i => MultiTapeTM.indicator V (x ++ enumWord w i)) 0 (2 ^ w) = true ↔
      ∃ u, u.length = w ∧ x ++ u ∈ V := by
  classical
  rw [enumAny_iff, enumCandidates_iff]
  simp [MultiTapeTM.indicator]

/-- A timed loop invariant combines bounded accept-or-advance segments into
one bounded singleton-output computation. The terminal configuration is the
post-overflow rejection configuration, so every candidate, including the last,
is tested before exhaustion.
**Proof sketch.** Induct on the remaining number of candidates. Acceptance
terminates immediately. Rejection advances to the next canonical configuration;
compose run segments and add their bounds. This lemma does not assert that
any particular machine satisfies the required per-round contracts. -/
private lemma enumLoop_run (M : FinTM Bool) (x : List Bool)
    (cfg : ℕ → Cfg M.k Bool M.State x) (accept : ℕ → Bool) (B i count : ℕ)
    (hend : (cfg (i + count)).state = none ∧ (cfg (i + count)).output = [false])
    (hround : ∀ j, i ≤ j → j < i + count → ∃ t, t ≤ B ∧
      if accept j then
        (M.tm.runFrom (cfg j) t).state = none ∧ (M.tm.runFrom (cfg j) t).output = [true]
      else M.tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t, t ≤ count * B ∧ (M.tm.runFrom (cfg i) t).state = none ∧
      (M.tm.runFrom (cfg i) t).output = [enumAny accept i count] := by
  induction count generalizing i with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simpa [enumAny] using hend
  | succ count ih =>
    obtain ⟨t, ht, hc⟩ := hround i (le_refl _) (by omega)
    by_cases hb : accept i = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · rw [Nat.succ_mul]; omega
      · simpa [enumAny, hb] using hc.2
    · simp only [hb] at hc
      have hend' : (cfg (i + 1 + count)).state = none ∧
          (cfg (i + 1 + count)).output = [false] := by
        simpa only [show i + 1 + count = i + (count + 1) by omega] using hend
      obtain ⟨s, hs, hhalt, hout⟩ := ih (i + 1) hend'
        (fun j hj hj' => hround j (by omega) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc]
        simpa [enumAny, hb] using hout

/-- A fixed polynomial in `n+1` in the exponent is absorbed into `n^e`,
with a uniform multiplicative constant for lengths zero and one.
**Proof sketch.** For `n ≥ 2`, use `K ≤ 2^K ≤ n^K` and `n+1 ≤ n^2`.
For `n ≤ 1`, bound the exponent by `K·2^k` and absorb its exponential. -/
private lemma enumExponent_bound (K k : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ, 2 ^ (K * (n + 1) ^ k) ≤ A * 2 ^ n ^ e := by
  refine ⟨2 ^ (K * 2 ^ k), K + 2 * k, fun n => ?_⟩
  by_cases hn : 2 ≤ n
  · have hK : K ≤ n ^ K :=
      (Nat.le_of_lt (Nat.lt_two_pow_self (n := K))).trans (Nat.pow_le_pow_left hn K)
    have hn' : n + 1 ≤ n ^ 2 := by
      calc n + 1 ≤ 2 * n := by omega
           _ ≤ n * n := Nat.mul_le_mul_right n hn
           _ = n ^ 2 := by ring
    have hexp : K * (n + 1) ^ k ≤ n ^ (K + 2 * k) := by
      calc K * (n + 1) ^ k ≤ n ^ K * (n ^ 2) ^ k :=
             Nat.mul_le_mul hK (Nat.pow_le_pow_left hn' k)
           _ = n ^ (K + 2 * k) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    exact (Nat.pow_le_pow_right (by omega) hexp).trans
      (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  · have hs : (n + 1) ^ k ≤ 2 ^ k := Nat.pow_le_pow_left (by omega) k
    calc 2 ^ (K * (n + 1) ^ k) ≤ 2 ^ (K * 2 ^ k) :=
           Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left K hs)
         _ ≤ 2 ^ (K * 2 ^ k) * 2 ^ n ^ (K + 2 * k) :=
           Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

/-- The audited round budget is pointwise bounded by an `EXP` budget, for
all coefficients and degrees, including zero.
**Proof sketch.** Set `k=max 1 c`. Both `n+1` and the width are bounded by
constant multiples of `(n+1)^k`. Replace the polynomial round overhead by
`2^(d·(n+width+1))`, add the exponents, and use `enumExponent_bound`. -/
private lemma enumBudget_bound (a C c d : ℕ) :
    ∃ A e : ℕ, ∀ n : ℕ,
      a * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ d ≤
        A * 2 ^ n ^ e := by
  let k := max 1 c
  let K := C + d * (C + 1)
  obtain ⟨A, e, hA⟩ := enumExponent_bound K k
  refine ⟨a * A, e, fun n => ?_⟩
  have hc : (n + 1) ^ c ≤ (n + 1) ^ k :=
    Nat.pow_le_pow_right (by omega) (Nat.le_max_right 1 c)
  have hn : n + 1 ≤ (n + 1) ^ k := by
    simpa only [Nat.pow_one] using
      Nat.pow_le_pow_right (by omega : 0 < n + 1) (Nat.le_max_left 1 c)
  have hw : n + C * (n + 1) ^ c + 1 ≤ (C + 1) * (n + 1) ^ k := by
    calc n + C * (n + 1) ^ c + 1 = (n + 1) + C * (n + 1) ^ c := by omega
         _ ≤ (n + 1) ^ k + C * (n + 1) ^ k :=
           Nat.add_le_add hn (Nat.mul_le_mul_left C hc)
         _ = (C + 1) * (n + 1) ^ k := by ring
  have he : C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1) ≤
      K * (n + 1) ^ k := by
    calc C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1) ≤
        C * (n + 1) ^ k + d * ((C + 1) * (n + 1) ^ k) :=
          Nat.add_le_add (Nat.mul_le_mul_left C hc) (Nat.mul_le_mul_left d hw)
         _ = K * (n + 1) ^ k := by dsimp [K]; ring
  have hb : (n + C * (n + 1) ^ c + 1) ^ d ≤
      2 ^ (d * (n + C * (n + 1) ^ c + 1)) := by
    calc (n + C * (n + 1) ^ c + 1) ^ d ≤
        (2 ^ (n + C * (n + 1) ^ c + 1)) ^ d :=
          Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self)) d
         _ = 2 ^ (d * (n + C * (n + 1) ^ c + 1)) := by
          rw [← Nat.pow_mul, Nat.mul_comm]
  calc a * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ d ≤
      a * (2 ^ (C * (n + 1) ^ c) * 2 ^ (d * (n + C * (n + 1) ^ c + 1))) := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hb
       _ = a * 2 ^ (C * (n + 1) ^ c + d * (n + C * (n + 1) ^ c + 1)) := by
        rw [Nat.pow_add]
       _ ≤ a * 2 ^ (K * (n + 1) ^ k) :=
        Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by omega) he)
       _ ≤ a * A * 2 ^ n ^ e := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left a (hA n)

/-- The catalog counter and the predecessor's counter have the same recursive
equations, including overflow on the empty word. -/
private lemma enumCont_inc_eq (s : List Bool) : incFixed s = enumInc s := by
  induction s with
  | nil => rfl
  | cons b s ih => cases b <;> simp only [incFixed, enumInc, ih]

/-- Stalling on overflow preserves the exact candidate width. -/
private lemma enumCont_step_length (s : List Bool) :
    ((incFixed s).getD s).length = s.length := by
  rw [enumCont_inc_eq]
  have h := enumInc_spec s
  cases hi : enumInc s with
  | none => rfl
  | some u => simp only [hi] at h; exact h.1

/-- Before exhaustion, the stalled catalog orbit is exactly the predecessor's
rank enumeration. No identity is asserted at the terminal rank `2^w`.
**Proof sketch.** The initial word is `enumWord w 0`. At a successor rank
still below `2^w`, the proved increment equation returns `some` of the next
word, so the fallback branch is never used. -/
private lemma enumCont_orbit (w : ℕ) : ∀ i, i < 2 ^ w →
    (fun s => (incFixed s).getD s)^[i] (List.replicate w false) =
      enumWord w i := by
  intro i
  induction i with
  | zero => intro _; exact (enumWord_zero w).symm
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega), enumCont_inc_eq,
      enumInc_word w i (by omega), if_pos hi]
    rfl

/-- The exact fuel word is a unary all-true word of the certificate width.
**Proof sketch.** At successor width, `2^(w+1)-1 = 2*(2^w-1)+1`;
`Nat.bit1_bits` prepends a true bit. The base case is zero fuel. -/
private lemma enumCont_fuel_bits (w : ℕ) :
    Nat.bits (2 ^ w - 1) = List.replicate w true := by
  induction w with
  | zero => simp
  | succ w ih =>
    have hp : 0 < 2 ^ w := Nat.pow_pos (by omega)
    have he : 2 ^ (w + 1) - 1 = 2 * (2 ^ w - 1) + 1 := by
      rw [Nat.pow_succ]
      omega
    rw [he, Nat.bit1_bits, ih, List.replicate_succ]

/-- A history tape can contain blank entries; its length is tracked on a
separate all-true clock tape. Cells outside its finite list are blank. -/
private def enumCont_sparse (w : List (Option Bool)) (z : ℤ) : Option Bool :=
  if 0 ≤ z then (w[z.toNat]?).join else none

/-- Appending a possibly blank history symbol writes just the next cell. -/
private lemma enumCont_sparse_append (w : List (Option Bool)) (b : Option Bool) :
    enumCont_sparse (w ++ [b]) =
      Function.update (enumCont_sparse w) (w.length : ℤ) b := by
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z; simp [enumCont_sparse]
  · rw [Function.update_of_ne hz]
    by_cases hnonneg : 0 ≤ z
    · have hne : z.toNat ≠ w.length := by omega
      simp only [enumCont_sparse, if_pos hnonneg]
      by_cases hlt : z.toNat < w.length
      · rw [List.getElem?_append_left hlt]
      · have hgt : w.length + 1 ≤ z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by omega)]
    · simp only [enumCont_sparse, if_neg hnonneg]

/-- Erasing the last history cell recovers its prefix, even if the erased
entry was itself blank. -/
private lemma enumCont_sparse_erase (w : List (Option Bool)) (b : Option Bool) :
    Function.update (enumCont_sparse (w ++ [b])) (w.length : ℤ) none =
      enumCont_sparse w := by
  rw [enumCont_sparse_append, Function.update_idem]
  have hblank : enumCont_sparse w (w.length : ℤ) = none := by
    simp [enumCont_sparse]
  rw [← hblank]
  exact Function.update_eq_self _ _

/-- Three tape symbols encode the three source head moves. -/
private def enumCont_moveCode : SignType → Option Bool
  | .neg => some false
  | .zero => none
  | .pos => some true

/-- Decode the inverse move for the backward restoration pass. -/
private def enumCont_unmove : Option Bool → SignType
  | some false => .pos
  | none => .zero
  | some true => .neg

/-- A recorded move and its inverse cancel as integer head displacements. -/
private lemma enumCont_unmove_cast (d : SignType) :
    (enumCont_unmove (enumCont_moveCode d)).cast = -(d.cast : ℤ) := by
  cases d <;> rfl

/-- A history entry retains every overwritten symbol and every source move.
No source state or native-input movement is needed for work-tape restoration. -/
private abbrev EnumContEntry (k : ℕ) :=
  (Fin k → Option Bool) × (Fin k → SignType)

/-- Instrument one source action with a clock cell and two history tracks per
source tape. The source action and output are otherwise unchanged. -/
private def enumCont_logAction {k : ℕ} {S : Type} (old : Fin k → Option Bool)
    (a : Action k Bool S) : Action (k + (1 + (k + k))) Bool S :=
  ⟨a.inputTape,
    tapeBlocks a.workTapes (some (some true), .pos)
      (Fin.addCases (fun i => (some (old i), .pos))
        (fun i => (some (enumCont_moveCode (a.workTapes i).2), .pos))),
    a.output, a.state⟩

/-- The logged source keeps its original finite state set. The extra tapes
are a unary step clock, old-symbol histories, and movement histories. -/
private def enumCont_logTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + (1 + (M.k + M.k))
  State := M.State
  tm := {
    q₀ := M.tm.q₀
    tr := fun q inp work =>
      let old := fun i : Fin M.k => work (Fin.castAdd (1 + (M.k + M.k)) i)
      enumCont_logAction old (M.tm.tr q inp old) }

/-- The correspondence stores exactly the source configuration and the
finite history; every history head is one cell past the recorded entries. -/
private def enumCont_logCfg {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (h : List (EnumContEntry k)) :
    Cfg (k + (1 + (k + k))) Bool S x :=
  ⟨c.state, c.inputPos,
    tapeBlocks c.workTapes (bufferTape (List.replicate h.length true))
      (Fin.addCases (fun i => enumCont_sparse (h.map (fun e => e.1 i)))
        (fun i => enumCont_sparse (h.map (fun e => enumCont_moveCode (e.2 i))))),
    tapeBlocks c.workTapePos (h.length : ℤ) (fun _ => h.length), c.output⟩

/-- One logged action preserves source semantics and appends exactly one
history entry, including a halting or emitting action.
**Proof sketch.** Split the physical tapes into source, clock, old-symbol,
and movement blocks. Source fields apply the original action; each history
field is the single-cell append identity at its current length. -/
private lemma enumCont_log_apply {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (h : List (EnumContEntry k)) (a : Action k Bool S) :
    (enumCont_logAction c.workTapeSymbols a).apply (enumCont_logCfg c h) =
      enumCont_logCfg (a.apply c)
        (h ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks,
          List.replicate_add, bufferTape_append]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks,
            enumCont_sparse_append, Fin.addCases]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [enumCont_logAction, enumCont_logCfg, Action.apply, tapeBlocks,
            Fin.addCases]

/-- Record precisely the actions actually executed by a source run. No entry
is added after the source has halted. -/
private def enumCont_history {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c₀ : Cfg k Bool S x) : ℕ → List (EnumContEntry k)
  | 0 => []
  | t + 1 =>
    let c := tm.runFrom c₀ t
    match c.state with
    | none => enumCont_history tm c₀ t
    | some q => enumCont_history tm c₀ t ++
        [(c.workTapeSymbols, fun i => ((tm.tr q c.inputSymbol c.workTapeSymbols).workTapes i).2)]

/-- Logging is lockstep with the source, from arbitrary prepared source
configurations. The source input, output, and halting time are unchanged.
**Proof sketch.** Induct on elapsed time. Halted configurations remain fixed;
otherwise the source-block reads agree and `enumCont_log_apply` records the
next action. This also covers the final emission on the halting action. -/
private lemma enumCont_log_run (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (t : ℕ) :
    (enumCont_logTM M).tm.runFrom (enumCont_logCfg c₀ []) t =
      enumCont_logCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    let c := M.tm.runFrom c₀ t
    have hr : (fun i : Fin M.k =>
        (enumCont_logCfg c (enumCont_history M.tm c₀ t)).workTapeSymbols
          (Fin.castAdd (1 + (M.k + M.k)) i)) = c.workTapeSymbols := by
      funext i
      simp [enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks]
    have hsrun : (M.tm.runFrom c₀ t).state = c.state := rfl
    cases hs : c.state with
    | none =>
      have hn : (M.tm.runFrom c₀ t).state = none := hsrun.trans hs
      simp only [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step,
        enumCont_history, enumCont_logCfg, hn]
    | some q =>
      have hq : (M.tm.runFrom c₀ t).state = some q := hsrun.trans hs
      have hstate : (enumCont_logCfg (M.tm.runFrom c₀ t)
          (enumCont_history M.tm c₀ t)).state = some q := hq
      simp only [MultiTapeTM.step, hstate]
      change (enumCont_logAction _ ((M.tm.tr q _ _))).apply _ = _
      rw [hr, enumCont_log_apply]
      simp only [enumCont_history, MultiTapeTM.runFrom_succ_eq_step',
        MultiTapeTM.step, hq]
      rfl

/-- The restoration controller alternates inverse head movement with writing
the old symbols. It erases history as it goes and halts with history heads at
zero when the clock's left blank is reached. Native input is stationary. -/
private def enumCont_undoTM (k : ℕ) : FinTM Bool where
  k := k + (1 + (k + k))
  State := Option (Fin k → Option Bool)
  tm := {
    q₀ := none
    tr := fun q _ work => match q with
      | none =>
        if (work (Fin.natAdd k (Fin.castAdd (k + k) 0))).isSome then
          ⟨0, tapeBlocks
            (fun i => (none, enumCont_unmove
              (work (Fin.natAdd k (Fin.natAdd 1 (Fin.natAdd k i))))))
            (some none, 0) (fun _ => (some none, 0)), none,
            some (some (fun i => work (Fin.natAdd k (Fin.natAdd 1 (Fin.castAdd k i)))))⟩
        else
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .pos)
            (fun _ => (none, .pos)), none, none⟩
      | some old =>
        ⟨0, tapeBlocks (fun i => (some (old i), 0)) (none, .neg)
          (fun _ => (none, .neg)), none, some none⟩ }

/-- At a restoration checkpoint the heads inspect the last remaining
history entry. The native input position and source control are irrelevant
to undoing the source work fields, so the former is explicit. -/
private def enumCont_undoCfg {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (h : List (EnumContEntry k)) (p : Fin (x.length + 2)) :
    Cfg (enumCont_undoTM k).k Bool (enumCont_undoTM k).State x :=
  ⟨some none, p, (enumCont_logCfg c h).workTapes,
    tapeBlocks c.workTapePos ((h.length : ℤ) - 1) (fun _ => (h.length : ℤ) - 1), []⟩

/-- The completed restoration retains exactly the source's initial work
fields and leaves every history tape blank with its head at zero. -/
private def enumCont_undoResult {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (p : Fin (x.length + 2)) :
    Cfg (enumCont_undoTM k).k Bool (enumCont_undoTM k).State x :=
  ⟨none, p, (enumCont_logCfg c []).workTapes,
    tapeBlocks c.workTapePos 0 (fun _ => 0), []⟩

/-- Undoing a tape write at the old head restores its original contents,
including no-write actions and writes of blank. -/
private lemma enumCont_restore_cell {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (i : Fin k) :
    Function.update ((a.apply c).workTapes i) (c.workTapePos i) (c.workTapeSymbols i) =
      c.workTapes i := by
  rw [Action.apply_workTapes, Function.update_idem]
  exact Function.update_eq_self _ _

/-- Erasing the last clock mark exposes exactly the preceding clock word. -/
private lemma enumCont_clock_erase (n : ℕ) :
    Function.update (bufferTape (List.replicate (n + 1) true)) (n : ℤ) none =
      bufferTape (List.replicate n true) := by
  rw [List.replicate_add, List.replicate_one, bufferTape_append,
    List.length_replicate, Function.update_idem]
  have hblank : bufferTape (List.replicate n true) (n : ℤ) = none := by simp
  rw [← hblank]
  exact Function.update_eq_self _ _

/-- Between inverse movement and inverse writing, the source heads are back
at their old positions and the last history entry is already erased. -/
private def enumCont_undoMid {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (h : List (EnumContEntry k))
    (p : Fin (x.length + 2)) :
    Cfg (enumCont_undoTM k).k Bool (enumCont_undoTM k).State x :=
  ⟨some (some c.workTapeSymbols), p, (enumCont_logCfg (a.apply c) h).workTapes,
    tapeBlocks c.workTapePos (h.length : ℤ) (fun _ => h.length), []⟩

/-- The first restoration transition reverses the last source head moves,
retains the old symbols in finite control, and erases their history cells.
**Proof sketch.** At the newest clock mark, the parallel tracks read the
last appended entry. The inverse displacement returns every source head to
its pre-action location. Single-cell erase identities recover each prefix. -/
private lemma enumCont_undo_back {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (h : List (EnumContEntry k))
    (p : Fin (x.length + 2)) :
    (enumCont_undoTM k).tm.step
      (enumCont_undoCfg (a.apply c)
        (h ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) p) =
      enumCont_undoMid c a h p := by
  let u := enumCont_undoCfg (a.apply c)
    (h ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) p
  have hc : u.workTapeSymbols (Fin.natAdd k (Fin.castAdd (k + k) 0)) = some true := by
    simp [u, enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks]
  have ho : (fun i : Fin k => u.workTapeSymbols
      (Fin.natAdd k (Fin.natAdd 1 (Fin.castAdd k i)))) = c.workTapeSymbols := by
    funext i
    simp [u, enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks,
      enumCont_sparse]
  have hm : (fun i : Fin k => u.workTapeSymbols
      (Fin.natAdd k (Fin.natAdd 1 (Fin.natAdd k i)))) =
      fun i => enumCont_moveCode (a.workTapes i).2 := by
    funext i
    simp [u, enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks,
      enumCont_sparse, Fin.addCases]
    congr 3
    apply Fin.ext
    simp
  change ((enumCont_undoTM k).tm.tr none _ u.workTapeSymbols).apply u = _
  simp only [enumCont_undoTM, hc, Option.isSome_some, ↓reduceIte]
  rw [ho]
  have hm' (i : Fin k) := congrFun hm i
  have herase (f : EnumContEntry k → Option Bool) (b : Option Bool) :
      Function.update (enumCont_sparse (h.map f ++ [b])) (h.length : ℤ) none =
        enumCont_sparse (h.map f) := by
    simpa only [List.length_map] using enumCont_sparse_erase (h.map f) b
  simp only [hm']
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [u, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [u, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg, Action.apply,
          tapeBlocks, enumCont_clock_erase]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [u, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg, Action.apply,
            tapeBlocks, Fin.addCases, herase]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [u, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks,
        enumCont_unmove_cast]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [u, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [u, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks, Fin.addCases]

/-- The second restoration transition writes the retained old symbols and
backs the history heads up to the preceding entry. -/
private lemma enumCont_undo_write {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (a : Action k Bool S) (h : List (EnumContEntry k))
    (p : Fin (x.length + 2)) :
    (enumCont_undoTM k).tm.step (enumCont_undoMid c a h p) =
      enumCont_undoCfg c h p := by
  change ((enumCont_undoTM k).tm.tr (some c.workTapeSymbols) _ _).apply _ = _
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg,
        Action.apply, tapeBlocks] using enumCont_restore_cell c a j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, enumCont_logCfg,
          Action.apply, tapeBlocks]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoTM, enumCont_undoMid, enumCont_undoCfg, Action.apply,
          tapeBlocks, sub_eq_add_neg]

/-- With no history left, one silent transition restores the history heads
to zero and halts. This also handles a source that took no steps. -/
private lemma enumCont_undo_empty {k : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) (p : Fin (x.length + 2)) :
    (enumCont_undoTM k).tm.step (enumCont_undoCfg c [] p) =
      enumCont_undoResult c p := by
  change ((enumCont_undoTM k).tm.tr none _ _).apply _ = _
  have hc : (enumCont_undoCfg c [] p).workTapeSymbols
      (Fin.natAdd k (Fin.castAdd (k + k) 0)) = none := by
    simp [enumCont_undoCfg, enumCont_logCfg, Cfg.workTapeSymbols, tapeBlocks]
  simp only [enumCont_undoTM, hc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_undoCfg, enumCont_undoResult, Action.apply, tapeBlocks]

/-- A logged live source prefix can be completely undone in `2t+1` steps.
The theorem restores the full original work tapes and heads, with blank
history, while preserving any supplied native input position.
**Proof sketch.** Peel the last source action. Two proved transitions first
reverse its moves and erase its history, then restore its overwritten cells.
Induction undoes the shorter prefix; the empty prefix takes one final step. -/
private lemma enumCont_undo_run (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (t : ℕ)
    (hlive : ∀ j < t, ¬(M.tm.runFrom c₀ j).Halted) :
    (enumCont_undoTM M.k).tm.runFrom
      (enumCont_undoCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) p) (2 * t + 1) =
      enumCont_undoResult c₀ p := by
  induction t with
  | zero =>
    simpa only [Nat.mul_zero, Nat.zero_add, MultiTapeTM.runFrom_zero,
      enumCont_history, MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
      using enumCont_undo_empty c₀ p
  | succ t ih =>
    have hs : (M.tm.runFrom c₀ t).state ≠ none := hlive t (by omega)
    cases hq : (M.tm.runFrom c₀ t).state with
    | none => exact False.elim (hs hq)
    | some q =>
      have he : 2 * (t + 1) + 1 = 2 + (2 * t + 1) := by omega
      let c := M.tm.runFrom c₀ t
      let a := M.tm.tr q c.inputSymbol c.workTapeSymbols
      have hsrun : M.tm.runFrom c₀ (t + 1) = a.apply c := by
        rw [MultiTapeTM.runFrom_succ_eq_step']
        simp only [MultiTapeTM.step, hq]
        rfl
      have hhist : enumCont_history M.tm c₀ (t + 1) =
          enumCont_history M.tm c₀ t ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)] := by
        simp only [enumCont_history, hq]
        rfl
      have htwo : (enumCont_undoTM M.k).tm.runFrom
          (enumCont_undoCfg (a.apply c)
            (enumCont_history M.tm c₀ t ++ [(c.workTapeSymbols, fun i => (a.workTapes i).2)]) p) 2 =
          enumCont_undoCfg c (enumCont_history M.tm c₀ t) p := by
        rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
          MultiTapeTM.runFrom_zero, enumCont_undo_back, enumCont_undo_write]
      rw [hsrun, hhist, he, MultiTapeTM.runFrom_add, htwo]
      exact ih (fun j hj => hlive j (by omega))

/-- Any known halted endpoint is reached at the first halting time, with a
live source at every earlier time. The bound is never increased. -/
private lemma enumCont_first_halt {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c₀ : Cfg k Bool S x) (T : ℕ)
    (hh : (tm.runFrom c₀ T).state = none) :
    ∃ t ≤ T, (∀ j < t, ¬(tm.runFrom c₀ j).Halted) ∧
      tm.runFrom c₀ t = tm.runFrom c₀ T := by
  classical
  have hex : ∃ t, (tm.runFrom c₀ t).state = none := ⟨T, hh⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hh
  refine ⟨t, ht, fun j hj => Nat.find_min hex hj, ?_⟩
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le ht
  rw [hr, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ (Nat.find_spec hex)]

/-- Administrative actions preserve the source bank and only move the native
input and the final capture tape. -/
private def enumCont_bufferAction {L : ℕ} {H : Type}
    (m d : SignType) (q : Option H) : Action (L + 1) Bool H :=
  ⟨m, fun i => (none, if i.val < L then 0 else d), none, q⟩

/-- Entry into restoration moves all history heads from the right blank to
the newest entry, leaving source heads fixed. -/
private def enumCont_undoEntry (k : ℕ) :
    Action (enumCont_undoTM k).k Bool (enumCont_undoTM k).State :=
  ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, .neg)),
    none, some none⟩

/-- A clean subroutine logs and captures a source, undoes all source work,
rewinds the native input and captured word, and halts silently. Its retained
output word lives on the last work tape; it emits no physical output. -/
private def enumCont_cleanTM (M : FinTM Bool) : FinTM Bool where
  k := (enumCont_logTM M).k + 1
  State := M.State ⊕ (Fin 6 ⊕ (enumCont_undoTM M.k).State)
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl q => captureAction Sum.inl (.inr (.inl 0))
          ((enumCont_logTM M).tm.tr q inp (fun i => work i.castSucc))
      | .inr (.inr q) => captureAction (fun q => .inr (.inr q)) (.inr (.inl 1))
          ((enumCont_undoTM M.k).tm.tr q inp (fun i => work i.castSucc))
      | .inr (.inl q) => match q.val with
        | 0 => captureAction (fun q => .inr (.inr q)) (.inr (.inl 1))
            (enumCont_undoEntry M.k)
        | 1 => controlAction .neg (some (.inr (.inl 2)))
        | 2 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 2)))
          | none => controlAction .pos (some (.inr (.inl 3)))
        | 3 => enumCont_bufferAction 0 .neg (some (.inr (.inl 4)))
        | 4 => match work (Fin.last (enumCont_logTM M).k) with
          | some _ => enumCont_bufferAction 0 .neg (some (.inr (.inl 4)))
          | none => enumCont_bufferAction 0 .pos (some (.inr (.inl 5)))
        | _ => controlAction 0 none }

/-- Clean administrative configurations expose only the native and capture
heads. The source work fields are already restored and the histories blank. -/
private def enumCont_cleanCfg (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool)
    (q : Option (enumCont_cleanTM M).State) (p : Fin (x.length + 2)) (h : ℤ) :
    Cfg (enumCont_cleanTM M).k Bool (enumCont_cleanTM M).State x :=
  ⟨q, p,
    (fun i => if hi : i.val < (enumCont_logTM M).k then
      (enumCont_logCfg c₀ []).workTapes ⟨i, hi⟩ else bufferTape y),
    (fun i => if hi : i.val < (enumCont_logTM M).k then
      (enumCont_logCfg c₀ []).workTapePos ⟨i, hi⟩ else h), []⟩

/-- The clean subroutine's first phase is the public captured simulation of
the logged source. Halting emissions are retained on the capture tape. -/
private lemma enumCont_clean_capture (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (t : ℕ)
    (hlive : ∀ j < t, ¬(M.tm.runFrom c₀ j).Halted) :
    (enumCont_cleanTM M).tm.runFrom
      (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) t =
      captureCfg Sum.inl (.inr (.inl 0)) [] []
        (enumCont_logCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t)) := by
  rw [capture_run (enumCont_logTM M).tm (enumCont_cleanTM M).tm Sum.inl (.inr (.inl 0))
    (fun _ _ _ => rfl) [] [] (enumCont_logCfg c₀ []) t]
  · rw [enumCont_log_run]
  · intro j hj
    rw [enumCont_log_run]
    exact hlive j hj

/-- After source halt, one silent dispatch parks every history head on its
last entry and starts the captured restoration, retaining the source output. -/
private lemma enumCont_clean_undo_entry (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (h : List (EnumContEntry M.k))
    (hs : c.state = none) :
    (enumCont_cleanTM M).tm.step
      (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c h)) =
      captureCfg (fun q => .inr (.inr q)) (.inr (.inl 1)) c.output []
        (enumCont_undoCfg c h c.inputPos) := by
  have hstate : (captureCfg (fun q => (Sum.inl q : (enumCont_cleanTM M).State))
      (.inr (.inl 0)) [] [] (enumCont_logCfg c h)).state = some (.inr (.inl 0)) := by
    simp [captureCfg, enumCont_logCfg, hs]
  simp only [MultiTapeTM.step, hstate]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, captureCfg, enumCont_undoEntry,
        enumCont_logCfg, enumCont_undoCfg, Action.apply]
    · simp only [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, enumCont_undoEntry, captureCfg,
        Fin.coe_castSucc, enumCont_undoCfg, Action.apply,
        enumCont_logCfg, List.nil_append, List.append_nil]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [tapeBlocks, Fin.addCases, j.isLt,
          show j.val < M.k + (1 + (M.k + M.k)) from Nat.lt_of_lt_of_le j.isLt (by omega)]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [tapeBlocks, Fin.addCases, j.isLt]
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, captureCfg, enumCont_undoEntry,
        enumCont_logCfg, enumCont_undoCfg, Action.apply]
    · simp only [enumCont_cleanTM, enumCont_logTM, enumCont_undoTM, captureAction, enumCont_undoEntry, captureCfg,
        Fin.coe_castSucc, enumCont_undoCfg, Action.apply,
        enumCont_logCfg]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [tapeBlocks, Fin.addCases, j.isLt,
          show j.val < M.k + (1 + (M.k + M.k)) from Nat.lt_of_lt_of_le j.isLt (by omega)]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [tapeBlocks, Fin.addCases, sub_eq_add_neg]

/-- The captured restoration returns within `2t+1` steps with the original
source work restored and its completed output retained separately.
**Proof sketch.** Take the restoration machine's first halt below its proved
exact bound, apply `capture_run`, and identify the returned configuration
field by field. Its empty output appends nothing to the retained source word. -/
private lemma enumCont_clean_restore (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (p : Fin (x.length + 2)) (t : ℕ)
    (hlive : ∀ j < t, ¬(M.tm.runFrom c₀ j).Halted) :
    ∃ r ≤ 2 * t + 1,
      (enumCont_cleanTM M).tm.runFrom
        (captureCfg (fun q => .inr (.inr q)) (.inr (.inl 1))
          (M.tm.runFrom c₀ t).output []
          (enumCont_undoCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) p)) r =
        enumCont_cleanCfg M c₀ (M.tm.runFrom c₀ t).output
          (some (.inr (.inl 1))) p ((M.tm.runFrom c₀ t).output.length : ℤ) := by
  have hu := enumCont_undo_run M c₀ p t hlive
  obtain ⟨r, hr, hl, he⟩ := enumCont_first_halt (enumCont_undoTM M.k).tm
    (enumCont_undoCfg (M.tm.runFrom c₀ t) (enumCont_history M.tm c₀ t) p)
    (2 * t + 1) (by rw [hu]; rfl)
  refine ⟨r, hr, ?_⟩
  rw [capture_run (enumCont_undoTM M.k).tm (enumCont_cleanTM M).tm
    (fun q => .inr (.inr q)) (.inr (.inl 1)) (fun _ _ _ => rfl)
    _ [] _ r hl, he, hu]
  simp [captureCfg, enumCont_undoResult, enumCont_cleanCfg, enumCont_logCfg,
    enumCont_logTM, enumCont_undoTM]
  exact ⟨rfl, rfl⟩

/-- Moving the clean subroutine's two exposed heads preserves every tape and
the empty physical output. -/
private lemma enumCont_buffer_apply (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool)
    (q q' : Option (enumCont_cleanTM M).State) (p : Fin (x.length + 2)) (h : ℤ)
    (m d : SignType) :
    (enumCont_bufferAction m d q').apply (enumCont_cleanCfg M c₀ y q p h) =
      enumCont_cleanCfg M c₀ y q' (moveInputPos p m) (h + d.cast) := by
  refine Cfg.ext rfl rfl rfl ?_ rfl
  funext i
  by_cases hi : i.val < (enumCont_logTM M).k <;>
    simp [enumCont_bufferAction, enumCont_cleanCfg, Action.apply, hi]

/-- A mandatory left step followed by a boundary scan restores the native
head in at most its old position plus two steps. This private derivation
uses the proved `rewind_scan`, following the timed wrapper's template. -/
private lemma enumCont_rewind {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]

/-- The retained output word rewinds without being erased. Starting just
left of cell `j`, the scan returns its head to zero in exactly `j+1` steps. -/
private lemma enumCont_clean_buffer_rewind (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool) (p : Fin (x.length + 2)) :
    ∀ j, j ≤ y.length →
      (enumCont_cleanTM M).tm.runFrom
        (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p ((j : ℤ) - 1)) (j + 1) =
        enumCont_cleanCfg M c₀ y (some (.inr (.inl 5))) p 0 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((enumCont_cleanTM M).tm.tr (.inr (.inl 4)) _ _).apply _ = _
    have hr : (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p ((0 : ℤ) - 1)).workTapeSymbols
        (Fin.last (enumCont_logTM M).k) = none := by
      simp [enumCont_cleanCfg, Cfg.workTapeSymbols]
    simp only [enumCont_cleanTM, Nat.cast_zero]
    rw [hr, enumCont_buffer_apply]
    simp [SignType.cast]
  | succ j ih =>
    intro hj
    have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
    rw [hz, MultiTapeTM.runFrom_succ_eq_step]
    have hs : (enumCont_cleanTM M).tm.step
        (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p j) =
        enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p ((j : ℤ) - 1) := by
      unfold MultiTapeTM.step
      change ((enumCont_cleanTM M).tm.tr (.inr (.inl 4)) _ _).apply _ = _
      have hr : (enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) p j).workTapeSymbols
          (Fin.last (enumCont_logTM M).k) = some (y[j]'(by omega)) := by
        simp [enumCont_cleanCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem (by omega : j < y.length)]
      simp only [enumCont_cleanTM, hr]
      rw [enumCont_buffer_apply]
      simp [SignType.cast, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- A halting source call can be made clean: retain its output on the final
tape, restore every source work field, blank all histories, and rewind both
exposed heads. The full duration is at most `3T+|x|+|y|+8`.
**Proof sketch.** Capture the logged run through its first halt; undo the
recorded actions; rewind native input; rewind the retained word; halt. Each
administrative transition is charged, and all phases keep physical output
empty. Only the actual source time is used in the restoration bound. -/
private lemma enumCont_clean_complete (M : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M.k Bool M.State x) (y : List Bool) (T : ℕ)
    (hh : (M.tm.runFrom c₀ T).state = none)
    (ho : (M.tm.runFrom c₀ T).output = y) :
    ∃ τ ≤ 3 * T + x.length + y.length + 8,
      (enumCont_cleanTM M).tm.runFrom
        (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) τ =
        enumCont_cleanCfg M c₀ y none 1 0 := by
  obtain ⟨t, ht, hlive, he⟩ := enumCont_first_halt M.tm c₀ T hh
  have hs : (M.tm.runFrom c₀ t).state = none := by rw [he]; exact hh
  have hout : (M.tm.runFrom c₀ t).output = y := by rw [he]; exact ho
  have hcap := enumCont_clean_capture M c₀ t hlive
  have hentry := enumCont_clean_undo_entry M (M.tm.runFrom c₀ t)
    (enumCont_history M.tm c₀ t) hs
  obtain ⟨r, hr, hrest⟩ := enumCont_clean_restore M c₀ (M.tm.runFrom c₀ t).inputPos t hlive
  have hfirst : (enumCont_cleanTM M).tm.runFrom
      (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) (t + 1 + r) =
      enumCont_cleanCfg M c₀ y (some (.inr (.inl 1)))
        (M.tm.runFrom c₀ t).inputPos (y.length : ℤ) := by
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step', hcap, hentry, hrest, hout]
  obtain ⟨u, hu, hrew⟩ := enumCont_rewind (enumCont_cleanTM M).tm
    (.inr (.inl 1)) (.inr (.inl 2)) (some (.inr (.inl 3)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (enumCont_cleanCfg M c₀ y (some (.inr (.inl 1)))
      (M.tm.runFrom c₀ t).inputPos (y.length : ℤ)) rfl
  have hrew' : (enumCont_cleanTM M).tm.runFrom
      (enumCont_cleanCfg M c₀ y (some (.inr (.inl 1)))
        (M.tm.runFrom c₀ t).inputPos (y.length : ℤ)) u =
      enumCont_cleanCfg M c₀ y (some (.inr (.inl 3))) 1 (y.length : ℤ) := hrew
  have hback : (enumCont_cleanTM M).tm.step
      (enumCont_cleanCfg M c₀ y (some (.inr (.inl 3))) 1 (y.length : ℤ)) =
      enumCont_cleanCfg M c₀ y (some (.inr (.inl 4))) 1 ((y.length : ℤ) - 1) := by
    change (enumCont_bufferAction 0 .neg _).apply _ = _
    rw [enumCont_buffer_apply]
    simp [sub_eq_add_neg, SignType.cast]
  have hlast : (enumCont_cleanTM M).tm.step
      (enumCont_cleanCfg M c₀ y (some (.inr (.inl 5))) 1 0) =
      enumCont_cleanCfg M c₀ y none 1 0 := by
    change (controlAction 0 none).apply _ = _
    rw [controlAction_apply]
    simp [moveInputPos_zero, enumCont_cleanCfg]
  refine ⟨t + 1 + r + u + 1 + (y.length + 1) + 1, ?_, ?_⟩
  · change u ≤ (M.tm.runFrom c₀ t).inputPos.val + 2 at hu
    have hp := (M.tm.runFrom c₀ t).inputPos.isLt
    omega
  · rw [MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_add _ _ (y.length + 1),
      MultiTapeTM.runFrom_succ_eq_step' (t := t + 1 + r + u),
      MultiTapeTM.runFrom_add _ _ u, hfirst, hrew', hback,
      enumCont_clean_buffer_rewind M c₀ y 1 y.length (le_refl _), hlast]

/-- The assembly source emits native input followed by the candidate already
on its sole work tape. Its two phases never write the candidate. -/
private def enumCont_concatTM : FinTM Bool where
  k := 1
  State := Bool
  tm := {
    q₀ := false
    tr := fun q inp work =>
      if q then match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some true⟩
        | none => controlAction 0 none
      else match inp with
        | some b => ⟨.pos, fun _ => (none, 0), some b, some false⟩
        | none => controlAction 0 (some true) }

/-- Assembly configurations keep the candidate word fixed while exposing
the input head, candidate head, and emitted prefix. -/
private def enumCont_concatCfg (x s : List Bool) (q : Option Bool)
    (p : Fin (x.length + 2)) (z : ℤ) (out : List Bool) :
    Cfg 1 Bool Bool x := ⟨q, p, fun _ => bufferTape s, fun _ => z, out⟩

/-- The native-input scan emits exactly the remaining input and switches to
the candidate phase, preserving the candidate and its head at zero.
**Proof sketch.** Induct on the remaining native suffix. A bit is emitted
and advances the native head; the right blank takes one silent phase change. -/
private lemma enumCont_concat_native (x s pre rest : List Bool) (hx : x = pre ++ rest) :
    enumCont_concatTM.tm.runFrom
      (enumCont_concatCfg x s (some false) ⟨pre.length + 1, by simp [hx]; omega⟩ 0 pre)
      (rest.length + 1) =
      enumCont_concatCfg x s (some true) (Fin.last (x.length + 1)) 0 x := by
  induction rest generalizing pre with
  | nil =>
    have hp : x = pre := by simpa using hx
    subst pre
    simp only [List.length_nil]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    have hr : (enumCont_concatCfg x s (some false) ⟨x.length + 1, by omega⟩ 0 x).inputSymbol =
        none := by simp [enumCont_concatCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change (enumCont_concatTM.tm.tr false _ _).apply _ = _
    simp only [enumCont_concatTM, Bool.false_eq_true, ↓reduceIte, hr]
    rw [controlAction_apply]
    simp [moveInputPos_zero, enumCont_concatCfg]
    rfl
  | cons b rest ih =>
    have hread : (enumCont_concatCfg x s (some false)
        ⟨pre.length + 1, by simp [hx]; omega⟩ 0 pre).inputSymbol = some b := by
      rw [inputSymbol_at _ pre.length (by simp [hx]) rfl]
      simp [hx]
    have hstep : enumCont_concatTM.tm.step
        (enumCont_concatCfg x s (some false) ⟨pre.length + 1, by simp [hx]; omega⟩ 0 pre) =
        enumCont_concatCfg x s (some false)
          ⟨(pre ++ [b]).length + 1, by simp [hx]⟩ 0 (pre ++ [b]) := by
      unfold MultiTapeTM.step
      change (enumCont_concatTM.tm.tr false _ _).apply _ = _
      simp only [enumCont_concatTM, Bool.false_eq_true, ↓reduceIte, hread]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · apply Fin.ext
        dsimp only [Action.apply, enumCont_concatCfg]
        rw [moveInputPos_pos_of_ne_right _ (by simp [hx])]
        simp
      · funext i; simp [Action.apply, enumCont_concatCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (pre ++ [b]) (by simpa only [List.append_assoc, List.singleton_append] using hx)

/-- The candidate scan appends the exact tape word to the emitted native
input and halts at its right blank. Empty candidates take the final step. -/
private lemma enumCont_concat_candidate (x s pre rest : List Bool) (p : Fin (x.length + 2)) (out : List Bool)
    (hs : s = pre ++ rest) :
    enumCont_concatTM.tm.runFrom
      (enumCont_concatCfg x s (some true) p pre.length (out ++ pre))
      (rest.length + 1) =
      enumCont_concatCfg x s none p s.length (out ++ s) := by
  induction rest generalizing pre with
  | nil =>
    have hp : s = pre := by simpa using hs
    subst pre
    simp only [List.length_nil]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (enumCont_concatTM.tm.tr true _ _).apply _ = _
    simp only [enumCont_concatTM, ↓reduceIte, enumCont_concatCfg, Cfg.workTapeSymbols,
      bufferTape_nat, List.getElem?_length]
    rw [controlAction_apply]
    simp [moveInputPos_zero]
  | cons b rest ih =>
    have hr : (enumCont_concatCfg x s (some true) p
        pre.length (out ++ pre)).workTapeSymbols 0 = some b := by
      simp [enumCont_concatCfg, Cfg.workTapeSymbols, hs]
    have hstep : enumCont_concatTM.tm.step
        (enumCont_concatCfg x s (some true) p pre.length (out ++ pre)) =
        enumCont_concatCfg x s (some true) p
          (pre ++ [b]).length (out ++ (pre ++ [b])) := by
      unfold MultiTapeTM.step
      change (enumCont_concatTM.tm.tr true _ _).apply _ = _
      simp only [enumCont_concatTM, ↓reduceIte, hr]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
      · funext i; simp [enumCont_concatCfg, Action.apply]
      · simp [enumCont_concatCfg, Action.apply, List.append_assoc]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (pre ++ [b]) (by simpa only [List.append_assoc, List.singleton_append] using hs)

/-- Assembly from the candidate seam emits exactly `x ++ s` in
`|x|+|s|+2` steps. The fixed candidate tape is retained. -/
private lemma enumCont_concat_run (x s : List Bool) :
    enumCont_concatTM.tm.runFrom
      (Cfg.ofWords (input := x) false (fun _ => s)) (x.length + s.length + 2) =
      enumCont_concatCfg x s none (Fin.last (x.length + 1)) s.length (x ++ s) := by
  have hn := enumCont_concat_native x s [] x rfl
  have hs := enumCont_concat_candidate x s [] s (Fin.last (x.length + 1)) x rfl
  simp only [List.length_nil, List.append_nil, Nat.zero_add,
    Nat.cast_zero] at hn hs
  have hp : (⟨1, by omega⟩ : Fin (x.length + 2)) = 1 := by apply Fin.ext; simp
  rw [hp] at hn
  change enumCont_concatTM.tm.runFrom (enumCont_concatCfg x s (some false) 1 0 []) _ = _
  rw [show x.length + s.length + 2 = (x.length + 1) + (s.length + 1) by omega,
    MultiTapeTM.runFrom_add, hn, hs]

/-- Buffered composition also works from a prepared first-machine work
configuration. Its second machine still receives genuine fresh work tapes.
**Proof sketch.** Use the first source halt, the public buffered lockstep and
rewind equations, then the public relocated second-phase simulation. -/
private lemma enumCont_prepared_comp (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c₀ : Cfg M₁.k Bool M₁.State x) (y z : List Bool) (T₁ T₂ : ℕ)
    (hh : (M₁.tm.runFrom c₀ T₁).state = none)
    (ho : (M₁.tm.runFrom c₀ T₁).output = y)
    (h₂ : M₂.ComputesInTime y z T₂) :
    ∃ t ≤ T₁ + y.length + 2 + T₂,
      ((bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c₀) t).state = none ∧
      ((bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c₀) t).output = z := by
  obtain ⟨t, ht, hlive, he⟩ := enumCont_first_halt M₁.tm c₀ T₁ hh
  let c := M₁.tm.runFrom c₀ t
  have hs : c.state = none := by dsimp [c]; rw [he]; exact hh
  have hout : c.output = y := by dsimp [c]; rw [he]; exact ho
  have hfirst := bufferedFirstCfg_run M₁ M₂ c₀ t hlive
  have hrew := bufferedFirstCfg_rewind M₁ M₂ c hs
  obtain ⟨tag, _, hrun⟩ := bufferedSecondCfg_run M₁ M₂ (M₂.tm.initCfg c.output) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init])
    c.inputPos c.workTapes c.workTapePos T₂
  have h₂' : (M₂.tm.runFrom (M₂.tm.initCfg c.output) T₂).state = none ∧
      (M₂.tm.runFrom (M₂.tm.initCfg c.output) T₂).output = z := by
    rw [hout]
    exact (computesInTime_iff _ _ _ _).mp h₂
  refine ⟨t + (c.output.length + 2) + T₂, by rw [hout]; omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hfirst, hrew, hrun]
  exact ⟨by simp only [bufferedSecondCfg, h₂'.1, Option.map_none], h₂'.2⟩

/-- The prepared assembly source occupies tape zero; the composition buffer
and verifier work tapes are exactly blank at the candidate seam. -/
private lemma enumCont_round_seam (MV : FinTM Bool) (x s : List Bool) (phase : Bool) :
    bufferedFirstCfg enumCont_concatTM MV (Cfg.ofWords (input := x) phase (fun _ => s)) =
      Cfg.ofWords (.inl (some phase) : (bufferedCompTM enumCont_concatTM MV).State)
        (stateWord (bufferedCompTM enumCont_concatTM MV).k s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hj : j.val = 0 := by have h := j.isLt; change j.val < 1 at h; omega
      simp [bufferedFirstCfg, Cfg.ofWords, stateWord, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [bufferedFirstCfg, Cfg.ofWords, stateWord, tapeBlocks, enumCont_concatTM]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [bufferedFirstCfg, Cfg.ofWords, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [bufferedFirstCfg, Cfg.ofWords, tapeBlocks]

/-- The prepared verifier call accepts the exact assembled input `x ++ s`.
Its bound includes assembly, the buffer rewind, and the verifier's actual
polynomial budget on that input. -/
private lemma enumCont_verifier_call (MV : FinTM Bool) (V : Language Bool) (Tv : ℕ → ℕ)
    (hV : MV.DecidesInTime V Tv) (x s : List Bool) :
    ∃ t ≤ Tv (x.length + s.length) + 2 * (x.length + s.length) + 4,
      ((bufferedCompTM enumCont_concatTM MV).tm.runFrom
        (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
          (stateWord (bufferedCompTM enumCont_concatTM MV).k s)) t).state = none ∧
      ((bufferedCompTM enumCont_concatTM MV).tm.runFrom
        (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
          (stateWord (bufferedCompTM enumCont_concatTM MV).k s)) t).output =
        [MultiTapeTM.indicator V (x ++ s)] := by
  obtain ⟨t, ht, hh, ho⟩ := enumCont_prepared_comp enumCont_concatTM MV
    (Cfg.ofWords (input := x) false (fun _ => s)) (x ++ s)
    [MultiTapeTM.indicator V (x ++ s)] (x.length + s.length + 2)
    (Tv (x ++ s).length)
    (by rw [enumCont_concat_run]; rfl) (by rw [enumCont_concat_run]; rfl) (hV (x ++ s))
  rw [enumCont_round_seam MV x s false] at hh ho
  simp only [List.length_append] at ht
  exact ⟨t, by omega, hh, ho⟩

/-- Relabel live states and redirect halt to a live return state, preserving
the complete action. This wrapper is used only for already-silent calls. -/
private def enumCont_returnAction {k : ℕ} {S H : Type}
    (emb : S → H) (ret : H) (a : Action k Bool S) : Action k Bool H :=
  ⟨a.inputTape, a.workTapes, a.output, some ((a.state.map emb).getD ret)⟩

/-- The live-return correspondence preserves all configuration fields except
the control state, including work-tape results. -/
private def enumCont_returnCfg {k : ℕ} {S H : Type} {x : List Bool}
    (emb : S → H) (ret : H) (c : Cfg k Bool S x) : Cfg k Bool H x :=
  ⟨some ((c.state.map emb).getD ret), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- A host with the redirected transition table simulates a source through
its first halt and returns the exact completed configuration.
**Proof sketch.** One redirected action commutes with the configuration map.
Induct through live source steps; a halting action selects the live return
state while preserving its final writes and output. -/
private lemma enumCont_return_run {k : ℕ} {S H : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
    (emb : S → H) (ret : H)
    (htr : ∀ q inp work, host.tr (emb q) inp work =
      enumCont_returnAction emb ret (tm.tr q inp work))
    (c₀ : Cfg k Bool S x) (t : ℕ)
    (hlive : ∀ j < t, ¬(tm.runFrom c₀ j).Halted) :
    host.runFrom (enumCont_returnCfg emb ret c₀) t =
      enumCont_returnCfg emb ret (tm.runFrom c₀ t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
      MultiTapeTM.runFrom_succ_eq_step']
    have hs : (tm.runFrom c₀ t).state ≠ none := hlive t (by omega)
    cases hq : (tm.runFrom c₀ t).state with
    | none => exact False.elim (hs hq)
    | some q =>
      simp only [MultiTapeTM.step, enumCont_returnCfg, hq, Option.map_some, Option.getD_some]
      rw [htr]
      rfl

/-- Pad an action with inactive high tapes and embed its finite control. -/
private def enumCont_padAction {k K : ℕ} {S H : Type}
    (emb : S → H) (a : Action k Bool S) : Action K Bool H :=
  ⟨a.inputTape, fun i => if hi : i.val < k then a.workTapes ⟨i, hi⟩ else (none, 0),
    a.output, a.state.map emb⟩

/-- Pad a source configuration with blank stationary high tapes. -/
private def enumCont_padCfg {k K : ℕ} {S H : Type} {x : List Bool}
    (emb : S → H) (c : Cfg k Bool S x) : Cfg K Bool H x :=
  ⟨c.state.map emb, c.inputPos,
    (fun i => if hi : i.val < k then c.workTapes ⟨i, hi⟩ else fun _ => none),
    (fun i => if hi : i.val < k then c.workTapePos ⟨i, hi⟩ else 0), c.output⟩

/-- Padding commutes with one action; the new high tapes remain blank. -/
private lemma enumCont_pad_apply {k K : ℕ} {S H : Type} {x : List Bool}
    (emb : S → H) (c : Cfg k Bool S x) (a : Action k Bool S) :
    (enumCont_padAction (K := K) emb a).apply (enumCont_padCfg emb c) =
      enumCont_padCfg emb (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : i.val < k <;> simp [enumCont_padAction, enumCont_padCfg, Action.apply, hi]
  · funext i
    by_cases hi : i.val < k <;> simp [enumCont_padAction, enumCont_padCfg, Action.apply, hi]

/-- A machine may run on an initial tape block of a larger controller.
**Proof sketch.** The source-block reads agree when the source fits. One
step commutes with padding, including the absorbing halted case; iterate. -/
private lemma enumCont_pad_run {k K : ℕ} {S H : Type} {x : List Bool}
    (hk : k ≤ K) (tm : MultiTapeTM k Bool S) (host : MultiTapeTM K Bool H)
    (emb : S → H)
    (htr : ∀ q inp work, host.tr (emb q) inp work =
      enumCont_padAction emb (tm.tr q inp
        (fun i => work ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩)))
    (c : Cfg k Bool S x) (t : ℕ) :
    host.runFrom (enumCont_padCfg emb c) t = enumCont_padCfg emb (tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step (enumCont_padCfg emb) ?_ c t
  intro c
  cases hq : c.state with
  | none => simp only [MultiTapeTM.step, enumCont_padCfg, hq, Option.map_none]
  | some q =>
    have hs : (enumCont_padCfg (K := K) emb c).state = some (emb q) := by
      simp only [enumCont_padCfg, hq, Option.map_some]
    have hw : (fun i : Fin k => (enumCont_padCfg (K := K) emb c).workTapeSymbols
        ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i
      simp [enumCont_padCfg, Cfg.workTapeSymbols, i.isLt]
    have hin : (enumCont_padCfg (K := K) emb c).inputSymbol = c.inputSymbol := rfl
    simp only [MultiTapeTM.step, hs, hq]
    rw [htr, hw, hin, enumCont_pad_apply]

/-- Three finite source routines share a common padded tape block. The
startup routine is the initial branch; prepared calls may select either
other branch without moving their candidate off tape zero. -/
private def enumCont_sources (Q R U : FinTM Bool) : FinTM Bool where
  k := Q.k + R.k + U.k
  State := Q.State ⊕ (R.State ⊕ U.State)
  tm := {
    q₀ := .inr (.inr U.tm.q₀)
    tr := fun q inp work => match q with
      | .inl q => enumCont_padAction Sum.inl
          (Q.tm.tr q inp (fun i => work ⟨i, by have := i.isLt; omega⟩))
      | .inr (.inl q) => enumCont_padAction (fun q => .inr (.inl q))
          (R.tm.tr q inp (fun i => work ⟨i, by have := i.isLt; omega⟩))
      | .inr (.inr q) => enumCont_padAction (fun q => .inr (.inr q))
          (U.tm.tr q inp (fun i => work ⟨i, by have := i.isLt; omega⟩)) }

/-- Move or write the candidate at tape zero and the final capture tape,
preserving every intervening tape. -/
private def enumCont_endsAction {L : ℕ} {H : Type}
    (a b : Option (Option Bool)) (d : SignType) (q : Option H) : Action (L + 1) Bool H :=
  ⟨0, fun i => if i.val = 0 then (a, d) else if i.val = L then (b, d) else (none, 0), none, q⟩

/-- The concrete body uses one clean source block for initialization,
verification, and increment. Administrative states are the anchor (0),
seed copy (1), unused reserve (2), verdict (3), increment check (4), result
copy (5), and synchronized rewind (6). The stopped variant freezes only
the anchor and is used to certify first returns without an interior visit. -/
private def enumCont_bodyTM (B : FinTM Bool) (qverify qinc : B.State) (stopped : Bool) :
    FinTM Bool where
  k := (enumCont_logTM B).k + 1
  State := ((enumCont_cleanTM B).State × Fin 3) ⊕ Fin 7
  tm := {
    q₀ := .inl ((enumCont_cleanTM B).tm.q₀, 0)
    tr := fun q inp work => match q with
      | .inl (q, mode) => enumCont_returnAction (fun q => .inl (q, mode))
          (.inr (if mode.val = 0 then 1 else if mode.val = 1 then 3 else 4))
          ((enumCont_cleanTM B).tm.tr q inp work)
      | .inr q => match q.val with
        | 0 => if stopped then controlAction 0 (some (.inr 0))
            else controlAction 0 (some (.inl (.inl qverify, 1)))
        | 3 => match work (Fin.last (enumCont_logTM B).k) with
          | some true => ⟨0, fun _ => (none, 0), some true, none⟩
          | _ => ⟨0, fun i => (if i.val = (enumCont_logTM B).k then some none else none, 0),
              none, some (.inl (.inl qinc, 2))⟩
        | 4 => if work (Fin.last (enumCont_logTM B).k) = none then
              controlAction 0 (some (.inr 0))
            else controlAction 0 (some (.inr 5))
        | 6 => match work 0 with
          | some _ => enumCont_endsAction none none .neg (some (.inr 6))
          | none => enumCont_endsAction none none .pos (some (.inr 0))
        | _ => match work (Fin.last (enumCont_logTM B).k) with
          | some b => enumCont_endsAction (some (some (if q.val = 1 then false else b)))
              (some none) .pos (some (.inr q))
          | none => enumCont_endsAction none none .neg (some (.inr 6)) }

/-- Starting assembly in its candidate phase supplies just that candidate to
the catalog incrementer. Its output is empty exactly on overflow; a clean
wrapper will retain the original candidate for that branch. -/
private lemma enumCont_increment_call (I : FinTM Bool) (j : ℕ)
    (hI : I.ComputesFunInTime (fun s => (incFixed s).getD []) (fun n => j * (n + 1)))
    (x s : List Bool) :
    ∃ t ≤ (j + 3) * (s.length + 1),
      ((bufferedCompTM enumCont_concatTM I).tm.runFrom
        (Cfg.ofWords (input := x) (.inl (some true))
          (stateWord (bufferedCompTM enumCont_concatTM I).k s)) t).state = none ∧
      ((bufferedCompTM enumCont_concatTM I).tm.runFrom
        (Cfg.ofWords (input := x) (.inl (some true))
          (stateWord (bufferedCompTM enumCont_concatTM I).k s)) t).output =
        (incFixed s).getD [] := by
  have hs := enumCont_concat_candidate x s [] s 1 [] rfl
  simp only [List.length_nil, List.nil_append, Nat.cast_zero] at hs
  obtain ⟨t, ht, hh, ho⟩ := enumCont_prepared_comp enumCont_concatTM I
    (Cfg.ofWords (input := x) true (fun _ => s)) s ((incFixed s).getD [])
    (s.length + 1) (j * (s.length + 1))
    (by change (enumCont_concatTM.tm.runFrom (enumCont_concatCfg x s (some true) 1 0 []) _).state = none
        rw [hs]; rfl)
    (by change (enumCont_concatTM.tm.runFrom (enumCont_concatCfg x s (some true) 1 0 []) _).output = s
        rw [hs]; rfl) (hI s)
  rw [enumCont_round_seam I x s true] at hh ho
  refine ⟨t, ht.trans ?_, hh, ho⟩
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- Padding preserves the candidate-on-zero convention when the source has
at least one work tape. All added tapes are blank and parked at zero. -/
private lemma enumCont_pad_words {k K : ℕ} {S H : Type} (hk : 0 < k) (_hle : k ≤ K)
    (emb : S → H) (q : S) (x s : List Bool) :
    enumCont_padCfg (K := K) emb (Cfg.ofWords (input := x) q (stateWord k s)) =
      Cfg.ofWords (emb q) (stateWord K s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : i.val < k
    · simp [enumCont_padCfg, Cfg.ofWords, stateWord, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [enumCont_padCfg, Cfg.ofWords, stateWord, hi, hn]
  · funext i
    simp [enumCont_padCfg, Cfg.ofWords]

/-- The same padding identity for empty initial work is valid even when the
source machine has no work tapes. -/
private lemma enumCont_pad_init {k K : ℕ} {S H : Type} (emb : S → H)
    (q : S) (x : List Bool) :
    enumCont_padCfg (k := k) (K := K) emb (Cfg.init q x) =
      Cfg.ofWords (emb q) (stateWord K []) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    simp [enumCont_padCfg, Cfg.init, Cfg.ofWords, stateWord]
  · funext i
    simp [enumCont_padCfg, Cfg.init, Cfg.ofWords]

/-- Overwriting the first remaining candidate cell extends the completed
prefix and drops the old cell, also when the old word is initially empty. -/
private lemma enumCont_overwrite (pre old : List Bool) (b : Bool) :
    Function.update (bufferTape (pre ++ old)) (pre.length : ℤ) (some b) =
      bufferTape (pre ++ b :: old.drop 1) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z; simp
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hn : z.toNat ≠ pre.length := by omega
      simp only [bufferTape, if_pos h0, List.getElem?_append]
      split
      · rfl
      · have hp : 0 < z.toNat - pre.length := by omega
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
        rw [hm]
        cases old <;> simp
    · simp [bufferTape, h0]

/-- The erased capture prefix consists entirely of blanks. Replacing its
next symbol by blank increases that prefix by one cell. -/
private lemma enumCont_sparse_clear (p : ℕ) (b : Bool) (rest : List Bool) :
    Function.update (enumCont_sparse (List.replicate p none ++ (b :: rest).map some))
      (p : ℤ) none =
      enumCont_sparse (List.replicate (p + 1) none ++ rest.map some) := by
  funext z
  by_cases hz : z = (p : ℤ)
  · subst z; simp [enumCont_sparse, List.getElem?_append]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hn : z.toNat ≠ p := by omega
      by_cases hp : z.toNat < p
      · simp [enumCont_sparse, h0, List.getElem?_append, hp,
          show z.toNat < p + 1 by omega]
      · simp [enumCont_sparse, h0, List.getElem?_append, hp,
          show ¬z.toNat < p + 1 by omega,
          show z.toNat - p = (z.toNat - (p + 1)) + 1 by omega]
    · simp [enumCont_sparse, h0]

/-- Tape configurations for the administrative copy and rewind scans. Only
the candidate and final capture tape may be nonblank; their heads coincide. -/
private def enumCont_pairCfg {L : ℕ} {S : Type} {x : List Bool}
    (q : Option S) (u v : ℤ → Option Bool) (h : ℤ) : Cfg (L + 1) Bool S x :=
  ⟨q, 1, (fun i => if i.val = 0 then u else if i.val = L then v else fun _ => none),
    (fun i => if i.val = 0 ∨ i.val = L then h else 0), []⟩

/-- The two-ended administrative action changes exactly those tape cells and
their common head, preserving native input and physical silence. -/
private lemma enumCont_ends_apply {L : ℕ} {S : Type} {x : List Bool} (_hL : 0 < L)
    (q q' : Option S) (u v : ℤ → Option Bool) (h : ℤ)
    (a b : Option (Option Bool)) (d : SignType) :
    (enumCont_endsAction (L := L) a b d q').apply (enumCont_pairCfg (x := x) q u v h) =
      enumCont_pairCfg q' (Function.update u h (a.getD (u h)))
        (Function.update v h (b.getD (v h))) (h + (d : ℤ)) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      subst i
      cases a <;> simp [enumCont_endsAction, enumCont_pairCfg, Action.apply,
        Function.update_eq_self]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      by_cases hl : i.val = L
      · cases b <;> simp [enumCont_endsAction, enumCont_pairCfg, Action.apply, he, hl,
          Function.update_eq_self]
      · simp [enumCont_endsAction, enumCont_pairCfg, Action.apply, he, hl]
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      subst i
      simp [enumCont_endsAction, enumCont_pairCfg, Action.apply]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      by_cases hl : i.val = L <;>
        simp [enumCont_endsAction, enumCont_pairCfg, Action.apply, he, hl]

/-- A sparse list of blank entries is an everywhere blank tape. -/
private lemma enumCont_sparse_blanks (n : ℕ) :
    enumCont_sparse (List.replicate n none) = fun _ => none := by
  funext z
  by_cases hz : 0 ≤ z <;> by_cases hn : z.toNat < n <;>
    simp [enumCont_sparse, hz, hn]

/-- Lifting every word symbol into the sparse representation gives the usual
buffer tape. -/
private lemma enumCont_sparse_some (w : List Bool) :
    enumCont_sparse (w.map some) = bufferTape w := by
  funext z
  by_cases hz : 0 ≤ z
  · simp only [enumCont_sparse, bufferTape, if_pos hz, List.getElem?_map]
    cases w[z.toNat]? <;> rfl
  · simp [enumCont_sparse, bufferTape, hz]

/-- The copy scan overwrites the candidate from left to right and erases each
captured symbol. The old suffix is explicit, so initialization from an empty
candidate and replacement of an equal-width candidate share this proof.
**Proof sketch.** One step uses the overwrite and sparse-clear identities;
induct on the remaining captured suffix. Its right blank starts rewind. -/
private lemma enumCont_copy_scan {L : ℕ} {S : Type} {x : List Bool} (hL : 0 < L)
    (tm : MultiTapeTM (L + 1) Bool S) (qc qr : S) (f : Bool → Bool)
    (htr : ∀ inp work, tm.tr qc inp work = match work (Fin.last L) with
      | some b => enumCont_endsAction (some (some (f b))) (some none) .pos (some qc)
      | none => enumCont_endsAction none none .neg (some qr))
    (pre old rest : List Bool) :
    tm.runFrom (enumCont_pairCfg (x := x) (some qc) (bufferTape (pre ++ old))
      (enumCont_sparse (List.replicate pre.length none ++ rest.map some)) pre.length)
      (rest.length + 1) =
      enumCont_pairCfg (some qr) (bufferTape (pre ++ rest.map f ++ old.drop rest.length))
        (fun _ => none) ((pre.length : ℤ) + rest.length - 1) := by
  induction rest generalizing pre old with
  | nil =>
    have hv : enumCont_sparse (List.replicate pre.length none ++ ([] : List Bool).map some) =
        (fun _ => none) := by simpa using enumCont_sparse_blanks pre.length
    rw [hv]
    simp only [List.length_nil, Nat.zero_add, List.map_nil, List.drop_zero, List.append_nil,
      Int.natCast_zero, add_zero]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    change (tm.tr qc _ _).apply _ = _
    rw [htr]
    have hr : (enumCont_pairCfg (L := L) (x := x) (some qc) (bufferTape (pre ++ old))
        (fun _ => none) pre.length).workTapeSymbols (Fin.last L) = none := by
      simp [enumCont_pairCfg, Cfg.workTapeSymbols, Nat.ne_of_gt hL]
    rw [hr, enumCont_ends_apply hL]
    simp only [Option.getD_none, Function.update_eq_self]
    simp [sub_eq_add_neg]
  | cons b rest ih =>
    let c := enumCont_pairCfg (L := L) (x := x) (some qc) (bufferTape (pre ++ old))
      (enumCont_sparse (List.replicate pre.length none ++ (b :: rest).map some)) pre.length
    have hr : c.workTapeSymbols (Fin.last L) = some b := by
      simp [c, enumCont_pairCfg, Cfg.workTapeSymbols, Nat.ne_of_gt hL, enumCont_sparse]
    have he : tm.step c = enumCont_pairCfg (some qc)
        (bufferTape ((pre ++ [f b]) ++ old.drop 1))
        (enumCont_sparse (List.replicate (pre ++ [f b]).length none ++ rest.map some))
        (pre ++ [f b]).length := by
      change (tm.tr qc _ _).apply c = _
      rw [htr, hr]
      dsimp only [c]
      rw [enumCont_ends_apply hL]
      simp only [Option.getD_some, enumCont_overwrite, enumCont_sparse_clear,
        List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      simp [List.append_assoc]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, he, ih]
    simp [List.map_cons, List.append_assoc, add_comm, add_left_comm]

/-- Rewind the two endpoint heads together across the completed candidate.
The left blank takes one positive move, restoring both heads to cell zero. -/
private lemma enumCont_pair_rewind {L : ℕ} {S : Type} {x : List Bool} (hL : 0 < L)
    (tm : MultiTapeTM (L + 1) Bool S) (qr qa : S)
    (htr : ∀ inp work, tm.tr qr inp work = match work 0 with
      | some _ => enumCont_endsAction none none .neg (some qr)
      | none => enumCont_endsAction none none .pos (some qa))
    (w : List Bool) (j : ℕ) (hj : j ≤ w.length) :
    tm.runFrom (enumCont_pairCfg (x := x) (some qr) (bufferTape w) (fun _ => none) (j - 1))
      (j + 1) = enumCont_pairCfg (some qa) (bufferTape w) (fun _ => none) 0 := by
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    change (tm.tr qr _ _).apply _ = _
    rw [htr]
    have hr : (enumCont_pairCfg (L := L) (x := x) (some qr) (bufferTape w)
        (fun _ => none) (0 - 1)).workTapeSymbols 0 = none := by
      simp [enumCont_pairCfg, Cfg.workTapeSymbols]
    simp only [Nat.cast_zero]
    rw [hr, enumCont_ends_apply hL]
    simp only [Option.getD_none, Function.update_eq_self]
    simp
  | succ j ih =>
    have hj' : j < w.length := by omega
    have hr : (enumCont_pairCfg (L := L) (x := x) (some qr) (bufferTape w)
        (fun _ => none) ((j + 1 : ℕ) - 1)).workTapeSymbols 0 = some w[j] := by
      simp [enumCont_pairCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem hj']
    have he : tm.step (enumCont_pairCfg (x := x) (some qr) (bufferTape w)
        (fun _ => none) ((j + 1 : ℕ) - 1)) =
        enumCont_pairCfg (some qr) (bufferTape w) (fun _ => none) (j - 1) := by
      change (tm.tr qr _ _).apply _ = _
      rw [htr, hr, enumCont_ends_apply hL]
      simp only [Option.getD_none, Function.update_eq_self]
      simp [sub_eq_add_neg, add_assoc]
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    exact ih (by omega)

/-- Copying a captured word at least as long as the old candidate completely
replaces it, erases capture, and restores the canonical seam in linear time. -/
private lemma enumCont_copy_complete {L : ℕ} {S : Type} {x : List Bool} (hL : 0 < L)
    (tm : MultiTapeTM (L + 1) Bool S) (qc qr qa : S) (f : Bool → Bool)
    (hc : ∀ inp work, tm.tr qc inp work = match work (Fin.last L) with
      | some b => enumCont_endsAction (some (some (f b))) (some none) .pos (some qc)
      | none => enumCont_endsAction none none .neg (some qr))
    (hr : ∀ inp work, tm.tr qr inp work = match work 0 with
      | some _ => enumCont_endsAction none none .neg (some qr)
      | none => enumCont_endsAction none none .pos (some qa))
    (old v : List Bool) (hv : old.length ≤ v.length) :
    tm.runFrom (enumCont_pairCfg (x := x) (some qc) (bufferTape old) (bufferTape v) 0)
      (2 * v.length + 2) =
      enumCont_pairCfg (some qa) (bufferTape (v.map f)) (fun _ => none) 0 := by
  have hc' := enumCont_copy_scan (x := x) hL tm qc qr f hc [] old v
  simp only [List.length_nil, List.replicate_zero, List.nil_append, Nat.cast_zero,
    zero_add, enumCont_sparse_some, List.drop_eq_nil_iff.mpr hv, List.append_nil] at hc'
  rw [show 2 * v.length + 2 = (v.length + 1) + (v.length + 1) by omega,
    MultiTapeTM.runFrom_add, hc']
  exact enumCont_pair_rewind hL tm qr qa hr (v.map f) v.length (by simp)

/-- Empty history adds only blank stationary tapes to a candidate seam. -/
private lemma enumCont_log_words (B : FinTM Bool) (hB : 0 < B.k)
    (x s : List Bool) (q : B.State) :
    enumCont_logCfg (Cfg.ofWords (input := x) q (stateWord B.k s)) [] =
      Cfg.ofWords q (stateWord (enumCont_logTM B).k s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logCfg, Cfg.ofWords, stateWord, tapeBlocks]
    · have hn : B.k + j.val ≠ 0 := by omega
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simp [enumCont_logCfg, Cfg.ofWords, stateWord, tapeBlocks, Nat.ne_of_gt hB]
      · refine Fin.addCases (fun l => ?_) (fun l => ?_) l <;>
          simp [enumCont_logCfg, Cfg.ofWords, stateWord, tapeBlocks,
            Fin.addCases, Nat.ne_of_gt hB] <;> exact enumCont_sparse_blanks 0
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [enumCont_logCfg, Cfg.ofWords, tapeBlocks]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [enumCont_logCfg, Cfg.ofWords, tapeBlocks]

/-- Appending one output tape to a candidate seam has the two-endpoint tape
layout used by the administrative controller. -/
private lemma enumCont_extend_words {L : ℕ} (hL : 0 < L) (s y : List Bool) :
    (fun i : Fin (L + 1) => if hi : i.val < L then
      bufferTape (stateWord L s ⟨i, hi⟩) else bufferTape y) =
      (fun i => if i.val = 0 then bufferTape s else if i.val = L then bufferTape y
        else fun _ => none) := by
  funext i
  by_cases hz : i.val = 0
  · have he : i = 0 := Fin.ext hz
    subst i
    simp [stateWord, hL]
  · have he : i ≠ 0 := by intro he; apply hz; simp [he]
    by_cases hi : i.val < L
    · have hn : i.val ≠ L := by omega
      simp [stateWord, hi, hz, hn]
    · have hl : i.val = L := by have := i.isLt; omega
      simp [hl, Nat.ne_of_gt hL]

/-- The clean wrapper's entry configuration at a prepared source seam. -/
private lemma enumCont_clean_entry_words (B : FinTM Bool) (hB : 0 < B.k)
    (x s : List Bool) (q : B.State) :
    captureCfg (fun q => (Sum.inl q : (enumCont_cleanTM B).State)) (.inr (.inl 0)) [] []
      (enumCont_logCfg (Cfg.ofWords (input := x) q (stateWord B.k s)) []) =
      enumCont_pairCfg (some (.inl q)) (bufferTape s) (fun _ => none) 0 := by
  rw [enumCont_log_words B hB]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · simpa only [captureCfg, Cfg.ofWords, List.append_nil, bufferTape_nil] using
      enumCont_extend_words (by omega) s []
  · funext i
    simp [captureCfg, Cfg.ofWords, enumCont_pairCfg]

/-- The completed clean call has restored the candidate seam and retained
only its captured output on the last tape. -/
private lemma enumCont_clean_exit_words (B : FinTM Bool) (hB : 0 < B.k)
    (x s y : List Bool) (q : B.State) (q' : Option (enumCont_cleanTM B).State) :
    enumCont_cleanCfg B (Cfg.ofWords (input := x) q (stateWord B.k s)) y q' 1 0 =
      enumCont_pairCfg q' (bufferTape s) (bufferTape y) 0 := by
  unfold enumCont_cleanCfg
  rw [enumCont_log_words B hB]
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact enumCont_extend_words (by dsimp [enumCont_logTM]; omega) s y
  · funext i
    simp [Cfg.ofWords, enumCont_pairCfg]

/-- A clean call inside the body redirects the clean wrapper's first halt to
the appropriate live administrative state. This is a complete configuration
equation: all scratch is blank, both endpoint heads are zero, and output is
physically empty. -/
private lemma enumCont_body_call (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi q : B.State) (stop : Bool) (mode : Fin 3) (x s y : List Bool) (T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) q (stateWord B.k s)) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) q (stateWord B.k s)) T).output = y) :
    ∃ t ≤ 3 * T + x.length + y.length + 8,
      (enumCont_bodyTM B qv qi stop).tm.runFrom
        (enumCont_pairCfg (x := x) (some (.inl (.inl q, mode)))
          (bufferTape s) (fun _ => none) 0) t =
        enumCont_pairCfg (some (.inr (if mode.val = 0 then 1 else if mode.val = 1 then 3 else 4)))
          (bufferTape s) (bufferTape y) 0 := by
  obtain ⟨r, hr, he⟩ := enumCont_clean_complete B
    (Cfg.ofWords (input := x) q (stateWord B.k s)) y T hh ho
  rw [enumCont_clean_entry_words B hB, enumCont_clean_exit_words B hB] at he
  obtain ⟨t, ht, hlive, hend⟩ := enumCont_first_halt (enumCont_cleanTM B).tm _ r
    (by rw [he]; rfl)
  have hrun := enumCont_return_run (enumCont_cleanTM B).tm (enumCont_bodyTM B qv qi stop).tm
    (fun q => .inl (q, mode))
    (.inr (if mode.val = 0 then 1 else if mode.val = 1 then 3 else 4))
    (fun _ _ _ => rfl) (enumCont_pairCfg (x := x) (some (.inl q))
      (bufferTape s) (fun _ => none) 0) t hlive
  rw [hend, he] at hrun
  exact ⟨t, ht.trans hr, hrun⟩

/-- With empty capture and zero endpoint heads, the administrative tape
layout is exactly the public canonical candidate seam. -/
private lemma enumCont_pair_words {L : ℕ} {S : Type} {x : List Bool}
    (q : S) (s : List Bool) :
    enumCont_pairCfg (L := L) (x := x) (some q) (bufferTape s) (fun _ => none) 0 =
      Cfg.ofWords q (stateWord (L + 1) s) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      simp [enumCont_pairCfg, Cfg.ofWords, stateWord, he]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      simp [enumCont_pairCfg, Cfg.ofWords, stateWord, he]
  · funext i; simp [enumCont_pairCfg, Cfg.ofWords]

/-- Initialization runs the clean unary generator, copies its marks as false
candidate bits, erases the marks, and rewinds to the canonical anchor. -/
private lemma enumCont_body_start (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (stop : Bool) (x : List Bool) (w T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).output =
      List.replicate w true) :
    ∃ t ≤ 3 * T + x.length + 3 * w + 10,
      (enumCont_bodyTM B qv qi stop).tm.runFrom ((enumCont_bodyTM B qv qi stop).tm.initCfg x) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi stop).k (List.replicate w false)) := by
  obtain ⟨t, ht, he⟩ := enumCont_body_call B hB qv qi B.tm.q₀ stop 0 x []
    (List.replicate w true) T hh ho
  have hi : enumCont_pairCfg (x := x) (some (.inl (.inl B.tm.q₀, (0 : Fin 3))))
      (bufferTape []) (fun _ => none) 0 = (enumCont_bodyTM B qv qi stop).tm.initCfg x := by
    rw [enumCont_pair_words]
    simp [enumCont_bodyTM, enumCont_cleanTM, enumCont_logTM,
      MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord]
  rw [hi] at he
  have hc := enumCont_copy_complete (x := x)
    (show 0 < (enumCont_logTM B).k by dsimp [enumCont_logTM]; omega)
    (enumCont_bodyTM B qv qi stop).tm (.inr 1) (.inr 6) (.inr 0) (fun _ => false)
    (by intro inp work; rfl) (by intro inp work; rfl) [] (List.replicate w true) (by simp)
  simp only [List.length_replicate, List.map_replicate, enumCont_pair_words] at hc
  refine ⟨t + (2 * w + 2), ?_, ?_⟩
  · simp only [List.length_replicate] at ht; omega
  · rw [MultiTapeTM.runFrom_add, he]
    exact hc

/-- A genuine round leaves the anchor in one silent stationary transition. -/
private lemma enumCont_body_depart (B : FinTM Bool) (qv qi : B.State) (x s : List Bool) :
    (enumCont_bodyTM B qv qi false).tm.step
      (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) =
      enumCont_pairCfg (some (.inl (.inl qv, 1))) (bufferTape s) (fun _ => none) 0 := by
  rw [enumCont_pair_words]
  change (controlAction 0 (some (.inl (.inl qv, (1 : Fin 3)) :
    (enumCont_bodyTM B qv qi false).State))).apply _ = _
  rw [controlAction_apply]
  simp [moveInputPos_zero, Cfg.ofWords]
  exact ⟨rfl, rfl⟩

/-- A captured true verdict emits the sole physical accepting bit and halts. -/
private lemma enumCont_body_accept (B : FinTM Bool) (qv qi : B.State) (stop : Bool)
    (x s : List Bool) :
    let c := enumCont_pairCfg (x := x) (some (.inr (3 : Fin 7))) (bufferTape s)
      (bufferTape [true]) 0
    ((enumCont_bodyTM B qv qi stop).tm.step c).state = none ∧
      ((enumCont_bodyTM B qv qi stop).tm.step c).output = [true] := by
  have hL : (enumCont_logTM B).k ≠ 0 := by dsimp [enumCont_logTM]; omega
  simp [MultiTapeTM.step, enumCont_bodyTM, enumCont_pairCfg, Cfg.workTapeSymbols,
    hL, Action.apply, bufferTape]

/-- A false verdict is erased before entering the clean increment call. -/
private lemma enumCont_body_reject (B : FinTM Bool) (qv qi : B.State) (stop : Bool)
    (x s : List Bool) :
    (enumCont_bodyTM B qv qi stop).tm.step
      (enumCont_pairCfg (x := x) (some (.inr 3)) (bufferTape s) (bufferTape [false]) 0) =
      enumCont_pairCfg (some (.inl (.inl qi, 2))) (bufferTape s) (fun _ => none) 0 := by
  have hL : (enumCont_logTM B).k ≠ 0 := by dsimp [enumCont_logTM]; omega
  have hv : Function.update (bufferTape [false]) (0 : ℤ) none = fun _ => none := by
    rw [show [false] = [] ++ [false] by rfl, bufferTape_append]
    simp only [List.length_nil, Nat.cast_zero, Function.update_idem]
    simp [Function.update_eq_self]
  have hr : (enumCont_pairCfg (L := (enumCont_logTM B).k) (x := x)
      (some (.inr (3 : Fin 7)) : Option (enumCont_bodyTM B qv qi stop).State)
      (bufferTape s) (bufferTape [false]) 0).workTapeSymbols (Fin.last (enumCont_logTM B).k) =
      some false := by simp [enumCont_pairCfg, Cfg.workTapeSymbols, hL, bufferTape]
  change ((enumCont_bodyTM B qv qi stop).tm.tr (.inr 3) _ _).apply _ = _
  simp only [enumCont_bodyTM, hr]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    by_cases hz : i.val = 0
    · have he : i = 0 := Fin.ext hz
      subst i
      simp [enumCont_pairCfg, Action.apply, Ne.symm hL]
    · have he : i ≠ 0 := by intro he; apply hz; simp [he]
      by_cases hl : i.val = (enumCont_logTM B).k <;>
        simp [enumCont_pairCfg, Action.apply, he, hl, hv]
  · funext i
    simp [enumCont_pairCfg, Action.apply]

/-- The catalog's empty overflow output preserves the old candidate. Every
nonempty increment result has the exact old width and is the stalled step. -/
private lemma enumCont_increment_cases (s : List Bool) :
    let v := (incFixed s).getD []
    (v = [] ∧ (incFixed s).getD s = s) ∨
      (v ≠ [] ∧ v.length = s.length ∧ (incFixed s).getD s = v) := by
  have hlen := enumCont_step_length s
  cases hi : incFixed s with
  | none => simp
  | some v =>
    rw [hi] at hlen
    simp only [Option.getD_some] at hlen ⊢
    by_cases hv : v = []
    · subst v
      have hs : s = [] := List.length_eq_zero_iff.mp hlen.symm
      simp [hs]
    · exact Or.inr ⟨hv, hlen, trivial⟩

/-- The increment-result check preserves all fields and chooses the anchor
on overflow or the copy phase on a nonempty result. -/
private lemma enumCont_body_check (B : FinTM Bool) (qv qi : B.State) (stop : Bool)
    (x s v : List Bool) :
    (enumCont_bodyTM B qv qi stop).tm.step
      (enumCont_pairCfg (x := x) (some (.inr 4)) (bufferTape s) (bufferTape v) 0) =
      enumCont_pairCfg (some (.inr (if v = [] then 0 else 5)))
        (bufferTape s) (bufferTape v) 0 := by
  have hL : (enumCont_logTM B).k ≠ 0 := by dsimp [enumCont_logTM]; omega
  have hv : bufferTape v 0 = none ↔ v = [] := by cases v <;> simp [bufferTape]
  change ((enumCont_bodyTM B qv qi stop).tm.tr (.inr 4) _ _).apply _ = _
  simp only [enumCont_bodyTM]
  have hr : (enumCont_pairCfg (L := (enumCont_logTM B).k) (x := x)
      (some (.inr (4 : Fin 7)) : Option (enumCont_bodyTM B qv qi stop).State)
      (bufferTape s) (bufferTape v) 0).workTapeSymbols (Fin.last (enumCont_logTM B).k) =
      bufferTape v 0 := by simp [enumCont_pairCfg, Cfg.workTapeSymbols, hL]
  rw [hr]
  simp only [hv]
  by_cases he : v = [] <;> simp only [he, ↓reduceIte, controlAction_apply]
  all_goals
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i
    simp [enumCont_pairCfg]

/-- A clean increment call followed by copy and rewind implements the exact
stalled fixed-width step. Empty overflow results preserve the candidate;
successful results replace every candidate cell in place. -/
private lemma enumCont_body_increment (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (stop : Bool) (x s : List Bool) (T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) T).output =
      (incFixed s).getD []) :
    ∃ t ≤ 3 * T + x.length + 3 * s.length + 11,
      (enumCont_bodyTM B qv qi stop).tm.runFrom
        (enumCont_pairCfg (x := x) (some (.inl (.inl qi, 2)))
          (bufferTape s) (fun _ => none) 0) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi stop).k ((incFixed s).getD s)) := by
  obtain ⟨t, ht, he⟩ := enumCont_body_call B hB qv qi qi stop 2 x s ((incFixed s).getD []) T hh ho
  simp only [show (2 : Fin 3).val = 2 by decide, show ¬(2 : ℕ) = 0 by decide,
    show ¬(2 : ℕ) = 1 by decide, ↓reduceIte] at he
  rcases enumCont_increment_cases s with ⟨hv, hs⟩ | ⟨hv, hl, hs⟩
  · refine ⟨t + 1, ?_, ?_⟩
    · rw [hv] at ht; simp only [List.length_nil] at ht; omega
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, enumCont_body_check, if_pos hv, hv,
        hs, bufferTape_nil, enumCont_pair_words]
      rfl
  · have hc := enumCont_copy_complete (x := x)
      (show 0 < (enumCont_logTM B).k by dsimp [enumCont_logTM]; omega)
      (enumCont_bodyTM B qv qi stop).tm (.inr 5) (.inr 6) (.inr 0) id
      (by intro inp work; rfl) (by intro inp work; rfl) s ((incFixed s).getD []) (by omega)
    simp only [List.map_id, enumCont_pair_words] at hc
    refine ⟨(t + 1) + (2 * ((incFixed s).getD []).length + 2), ?_, ?_⟩
    · rw [hl] at ht ⊢; omega
    · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step' (t := t), he,
        enumCont_body_check, if_neg hv, hc, hs]
      rfl

/-- Starting just after departure, one verifier call either emits acceptance
or clears the verdict and completes one exact candidate update. This raw
segment is valid in both controller variants; first-return guards are added
separately using the stopped anchor. -/
private lemma enumCont_body_round_raw (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (stop : Bool) (x s : List Bool) (b : Bool) (Tv Ti : ℕ)
    (hv : (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).output = [b])
    (hi : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).output =
        (incFixed s).getD []) :
    ∃ t ≤ 3 * Tv + 3 * Ti + 2 * x.length + 3 * s.length + 21,
      if b then
        ((enumCont_bodyTM B qv qi stop).tm.runFrom
          (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
            (bufferTape s) (fun _ => none) 0) t).state = none ∧
        ((enumCont_bodyTM B qv qi stop).tm.runFrom
          (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
            (bufferTape s) (fun _ => none) 0) t).output = [true]
      else (enumCont_bodyTM B qv qi stop).tm.runFrom
          (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
            (bufferTape s) (fun _ => none) 0) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi stop).k ((incFixed s).getD s)) := by
  obtain ⟨t, ht, he⟩ := enumCont_body_call B hB qv qi qv stop 1 x s [b] Tv hv.1 hv.2
  simp only [show (1 : Fin 3).val = 1 by decide, show ¬(1 : ℕ) = 0 by decide,
    ↓reduceIte] at he
  simp only [List.length_singleton] at ht
  cases b with
  | false =>
    obtain ⟨r, hr, hrun⟩ := enumCont_body_increment B hB qv qi stop x s Ti hi.1 hi.2
    refine ⟨(t + 1) + r, by omega, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step', he,
      enumCont_body_reject, hrun]
  | true =>
    refine ⟨t + 1, by omega, ?_⟩
    simp only [↓reduceIte, MultiTapeTM.runFrom_succ_eq_step', he]
    exact enumCont_body_accept B qv qi stop x s

/-- An anchor whose transition is a stationary self-loop preserves its
complete configuration for every subsequent step. -/
private lemma enumCont_absorb {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ inp work, tm.tr qa inp work = controlAction 0 (some qa))
    (c : Cfg k Bool S x) (hc : c.state = some qa) (t : ℕ) : tm.runFrom c t = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    simp only [MultiTapeTM.step, hc, ha, controlAction_apply]
    apply Cfg.ext
    · exact hc.symm
    · exact moveInputPos_zero _
    · rfl
    · rfl
    · rfl

/-- Two transition tables differing only at the anchor agree on every run
prefix that has not yet visited that anchor. -/
private lemma enumCont_agree_run {k : ℕ} {S : Type} {x : List Bool}
    (tm stop : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ q, q ≠ qa → ∀ inp work, tm.tr q inp work = stop.tr q inp work)
    (c : Cfg k Bool S x) (t : ℕ)
    (hn : ∀ j < t, (stop.runFrom c j).state ≠ some qa) :
    tm.runFrom c t = stop.runFrom c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hn j (by omega)),
      MultiTapeTM.runFrom_succ_eq_step']
    cases hs : (stop.runFrom c t).state with
    | none => simp only [MultiTapeTM.step, hs]
    | some q =>
      have hq : q ≠ qa := by intro he; subst q; exact hn t (by omega) hs
      simp only [MultiTapeTM.step, hs, ha q hq]

/-- The first visit to a stopped anchor transfers to the active machine with
the same full endpoint and no earlier anchor visit. Absorption identifies
the first endpoint with the supplied bounded endpoint. -/
private lemma enumCont_first_anchor {k : ℕ} {S : Type} {x : List Bool}
    (tm stop : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ q, q ≠ qa → ∀ inp work, tm.tr q inp work = stop.tr q inp work)
    (hs : ∀ inp work, stop.tr qa inp work = controlAction 0 (some qa))
    (c : Cfg k Bool S x) (T : ℕ) (hT : (stop.runFrom c T).state = some qa) :
    ∃ t ≤ T, (∀ j < t, (tm.runFrom c j).state ≠ some qa) ∧
      tm.runFrom c t = stop.runFrom c T := by
  classical
  have hex : ∃ t, (stop.runFrom c t).state = some qa := ⟨T, hT⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hT
  have hend : (stop.runFrom c t).state = some qa := Nat.find_spec hex
  have hn : ∀ j < t, (stop.runFrom c j).state ≠ some qa := fun j hj => Nat.find_min hex hj
  have he : stop.runFrom c T = stop.runFrom c t := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le ht
    rw [hr, MultiTapeTM.runFrom_add, enumCont_absorb stop qa hs _ hend]
  refine ⟨t, ht, ?_, ?_⟩
  · intro j hj
    rw [enumCont_agree_run tm stop qa ha c j (fun i hi => hn i (by omega))]
    exact hn j hj
  · rw [enumCont_agree_run tm stop qa ha c t hn, he]

/-- A halted stopped run never visited the live absorbing anchor. Its entire
bounded run therefore transfers unchanged to the active machine. -/
private lemma enumCont_halt_transfer {k : ℕ} {S : Type} {x : List Bool}
    (tm stop : MultiTapeTM k Bool S) (qa : S)
    (ha : ∀ q, q ≠ qa → ∀ inp work, tm.tr q inp work = stop.tr q inp work)
    (hs : ∀ inp work, stop.tr qa inp work = controlAction 0 (some qa))
    (c : Cfg k Bool S x) (T : ℕ) (hT : (stop.runFrom c T).state = none) :
    tm.runFrom c T = stop.runFrom c T ∧
      ∀ j ≤ T, (tm.runFrom c j).state ≠ some qa := by
  have hn : ∀ j ≤ T, (stop.runFrom c j).state ≠ some qa := by
    intro j hj hjq
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hj
    have he : stop.runFrom c T = stop.runFrom c j := by
      rw [hr, MultiTapeTM.runFrom_add, enumCont_absorb stop qa hs _ hjq]
    have he' := congrArg Cfg.state he
    rw [hT, hjq] at he'
    contradiction
  refine ⟨enumCont_agree_run tm stop qa ha c T (fun j hj => hn j (by omega)), ?_⟩
  intro j hj
  rw [enumCont_agree_run tm stop qa ha c j (fun i hi => hn i (by omega))]
  exact hn j hj

/-- The active and stopped body have identical transitions away from the
anchor. Their tape counts and finite state types are definitionally equal. -/
private lemma enumCont_body_agree (B : FinTM Bool) (qv qi : B.State)
    (q : (enumCont_bodyTM B qv qi false).State) (hq : q ≠ .inr 0) (inp work) :
    (enumCont_bodyTM B qv qi false).tm.tr q inp work =
      (enumCont_bodyTM B qv qi true).tm.tr q inp work := by
  cases q with
  | inl q => rfl
  | inr q =>
    have hz : q.val ≠ 0 := by
      intro he
      apply hq
      congr 1
      exact Fin.ext he
    simp only [enumCont_bodyTM]
    split <;> first | contradiction | rfl

/-- Startup satisfies the loop export's first-anchor guard as well as its
full canonical configuration equality. -/
private lemma enumCont_body_start_guarded (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (x : List Bool) (w T : ℕ)
    (hh : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).state = none)
    (ho : (B.tm.runFrom (Cfg.ofWords (input := x) B.tm.q₀ (stateWord B.k [])) T).output =
      List.replicate w true) :
    ∃ t ≤ 3 * T + x.length + 3 * w + 10,
      (∀ j < t, ((enumCont_bodyTM B qv qi false).tm.runFrom
        ((enumCont_bodyTM B qv qi false).tm.initCfg x) j).state ≠ some (.inr 0)) ∧
      (enumCont_bodyTM B qv qi false).tm.runFrom ((enumCont_bodyTM B qv qi false).tm.initCfg x) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k (List.replicate w false)) := by
  obtain ⟨r, hr, he⟩ := enumCont_body_start B hB qv qi true x w T hh ho
  change (enumCont_bodyTM B qv qi true).tm.runFrom
    ((enumCont_bodyTM B qv qi false).tm.initCfg x) r =
      Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k (List.replicate w false)) at he
  obtain ⟨t, ht, hn, hend⟩ := enumCont_first_anchor
    (enumCont_bodyTM B qv qi false).tm (enumCont_bodyTM B qv qi true).tm (.inr 0)
    (enumCont_body_agree B qv qi) (by intro inp work; rfl)
    ((enumCont_bodyTM B qv qi false).tm.initCfg x) r (by rw [he]; rfl)
  rw [he] at hend
  exact ⟨t, ht.trans hr, hn, hend⟩

/-- The active round has positive duration and no strict interior visit to
the anchor. Rejection uses the first stopped-anchor visit; acceptance never
visits that live absorbing state. In either case departure adds one step. -/
private lemma enumCont_body_round_guarded (B : FinTM Bool) (hB : 0 < B.k)
    (qv qi : B.State) (x s : List Bool) (b : Bool) (Tv Ti : ℕ)
    (hv : (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qv (stateWord B.k s)) Tv).output = [b])
    (hi : (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) qi (stateWord B.k s)) Ti).output =
        (incFixed s).getD []) :
    ∃ t, 0 < t ∧ t ≤ 3 * Tv + 3 * Ti + 2 * x.length + 3 * s.length + 22 ∧
      (∀ j, 0 < j → j < t →
        ((enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) j).state
            ≠ some (.inr 0)) ∧
      if b then
        ((enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) t).state
            = none ∧
        ((enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) t).output
            = [true]
      else (enumCont_bodyTM B qv qi false).tm.runFrom
          (Cfg.ofWords (input := x) (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k s)) t =
        Cfg.ofWords (.inr 0) (stateWord (enumCont_bodyTM B qv qi false).k ((incFixed s).getD s)) := by
  obtain ⟨r, hr, he⟩ := enumCont_body_round_raw B hB qv qi true x s b Tv Ti hv hi
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at he ⊢
    obtain ⟨t, ht, hn, hend⟩ := enumCont_first_anchor
      (enumCont_bodyTM B qv qi false).tm (enumCont_bodyTM B qv qi true).tm (.inr 0)
      (enumCont_body_agree B qv qi) (by intro inp work; rfl)
      (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
        (bufferTape s) (fun _ => none) 0) r (by rw [he]; rfl)
    refine ⟨t + 1, by omega, by omega, ?_, ?_⟩
    · intro j hj hjt
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart]
      exact hn i (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart, hend, he]
      rfl
  | true =>
    simp only [↓reduceIte] at he ⊢
    obtain ⟨hend, hn⟩ := enumCont_halt_transfer
      (enumCont_bodyTM B qv qi false).tm (enumCont_bodyTM B qv qi true).tm (.inr 0)
      (enumCont_body_agree B qv qi) (by intro inp work; rfl)
      (enumCont_pairCfg (x := x) (some (.inl (.inl qv, 1)))
        (bufferTape s) (fun _ => none) 0) r he.1
    refine ⟨r + 1, by omega, by omega, ?_, ?_⟩
    · intro j hj hjr
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart]
      exact hn i (by omega)
    · rw [MultiTapeTM.runFrom_succ_eq_step, enumCont_body_depart, hend]
      exact he

/-- A prepared source call may use the initial tape block of the shared
source machine; padding preserves its halt and exact emitted word. -/
private lemma enumCont_lift_call (M B : FinTM Bool) (hM : 0 < M.k) (hk : M.k ≤ B.k)
    (emb : M.State → B.State)
    (htr : ∀ q inp work, B.tm.tr (emb q) inp work =
      enumCont_padAction emb (M.tm.tr q inp
        (fun i => work ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩)))
    (q : M.State) (x s y : List Bool) (T : ℕ)
    (hh : (M.tm.runFrom (Cfg.ofWords (input := x) q (stateWord M.k s)) T).state = none)
    (ho : (M.tm.runFrom (Cfg.ofWords (input := x) q (stateWord M.k s)) T).output = y) :
    (B.tm.runFrom (Cfg.ofWords (input := x) (emb q) (stateWord B.k s)) T).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) (emb q) (stateWord B.k s)) T).output = y := by
  rw [← enumCont_pad_words hM hk emb q x s,
    enumCont_pad_run hk M.tm B.tm emb htr]
  exact ⟨by simp [enumCont_padCfg, hh], ho⟩

/-- Initial calls pad correctly even for a zero-work-tape source. -/
private lemma enumCont_lift_init (M B : FinTM Bool) (hk : M.k ≤ B.k)
    (emb : M.State → B.State)
    (htr : ∀ q inp work, B.tm.tr (emb q) inp work =
      enumCont_padAction emb (M.tm.tr q inp
        (fun i => work ⟨i, Nat.lt_of_lt_of_le i.isLt hk⟩)))
    (x y : List Bool) (T : ℕ) (h : M.ComputesInTime x y T) :
    (B.tm.runFrom (Cfg.ofWords (input := x) (emb M.tm.q₀) (stateWord B.k [])) T).state = none ∧
      (B.tm.runFrom (Cfg.ofWords (input := x) (emb M.tm.q₀) (stateWord B.k [])) T).output = y := by
  obtain ⟨hh, ho⟩ := (computesInTime_iff M x y T).mp h
  rw [← enumCont_pad_init (k := M.k) emb M.tm.q₀ x]
  change (B.tm.runFrom (enumCont_padCfg emb (M.tm.initCfg x)) T).state = none ∧
    (B.tm.runFrom (enumCont_padCfg emb (M.tm.initCfg x)) T).output = y
  rw [enumCont_pad_run hk M.tm B.tm emb htr]
  refine ⟨?_, ho⟩
  change ((M.tm.runFrom (M.tm.initCfg x) T).state.map emb) = none
  rw [hh]
  rfl

/-- A concrete body with polynomial startup and exact seam restoration gives
the frozen enumerator configuration contract by the audited loop export.
This lemma is conditional only on the two explicit body obligations below.
**Proof sketch.** Use the catalog unary generator for the fuel bits, enlarging
the common coefficient and degree to cover both fuel and body. Instantiate
`exists_loopCfgTM` with the exact-width invariant and stalled increment.
The terminal is `(2^w-1)+1=2^w`; on candidate indices use `enumCont_orbit`.
Finally absorb the export's additive one using `1 ≤ (n+w+1)^D`, exactly as
in infrastructure round 3, item 5. All constants are fixed before the input. -/
private lemma enumCont_from_body (C c : ℕ) (G : ℕ → ℕ) (V : Language Bool)
    (body : FinTM Bool) (anchor : body.State)
    (hstart : ∀ x : List Bool,
      ∃ t ≤ G x.length,
        (∀ t' < t, (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
        body.tm.runFrom (body.tm.initCfg x) t =
          Cfg.ofWords anchor (stateWord body.k (List.replicate (C * (x.length + 1) ^ c) false)))
    (hround : ∀ (x s : List Bool), s.length = C * (x.length + 1) ^ c →
      ∃ t, 0 < t ∧ t ≤ G x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
            ≠ some anchor) ∧
        if MultiTapeTM.indicator V (x ++ s) then
          (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output = [true]
        else
          body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k ((incFixed s).getD s))) :
    ∃ (b : ℕ) (E : FinTM Bool), ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
        startup ≤ b * (G x.length + (x.length + 1) ^ (c + 1) + 1) ∧
        E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
        ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
          t ≤ b * (G x.length + (x.length + 1) ^ (c + 1) + 1) ∧
          if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
            (E.tm.runFrom (cfg i) t).state = none ∧
              (E.tm.runFrom (cfg i) t).output = [true]
          else E.tm.runFrom (cfg i) t = cfg (i + 1) := by
  obtain ⟨F, f, hF⟩ := computesFunInTime_polyUnary C c
  let T := fun n => G n + f * (n + 1) ^ (c + 1)
  have hbody (n : ℕ) : G n ≤ T n := Nat.le_add_right _ _
  have hfuel : F.ComputesFunInTime
      (fun x => Nat.bits (2 ^ (C * (x.length + 1) ^ c) - 1)) T := by
    intro x
    dsimp only
    rw [enumCont_fuel_bits]
    apply (hF x).mono
    exact Nat.le_add_left _ _
  obtain ⟨E, K, hE⟩ := exists_loopCfgTM body F anchor
    (fun x s => s.length = C * (x.length + 1) ^ c)
    (fun _ s => (incFixed s).getD s)
    (fun x s => MultiTapeTM.indicator V (x ++ s))
    (fun x => List.replicate (C * (x.length + 1) ^ c) false)
    (fun n => 2 ^ (C * (n + 1) ^ c) - 1) T hfuel
    (by intro x; exact List.length_replicate)
    (by intro x s hs; exact (enumCont_step_length s).trans hs)
    (by
      intro x
      obtain ⟨t, ht, hi, hh⟩ := hstart x
      exact ⟨t, ht.trans (hbody x.length), hi, hh⟩)
    (by
      intro x s hs
      obtain ⟨t, htpos, ht, hi, hh⟩ := hround x s hs
      exact ⟨t, htpos, ht.trans (hbody x.length), hi, hh⟩)
  refine ⟨K * (f + 1), E, fun x => ?_⟩
  obtain ⟨cfg, startup, ht, hi, _, hend, hout, hr⟩ := hE x
  have hone : 1 ≤ 2 ^ (C * (x.length + 1) ^ c) := Nat.one_le_two_pow
  have hterminal : 2 ^ (C * (x.length + 1) ^ c) - 1 + 1 =
      2 ^ (C * (x.length + 1) ^ c) := Nat.sub_add_cancel hone
  rw [hterminal] at hend hout
  have hbudget : K * (T x.length + 1) ≤ K * (f + 1) *
      (G x.length + (x.length + 1) ^ (c + 1) + 1) := by
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left K
    dsimp only [T]
    have e : (f + 1) * (G x.length + (x.length + 1) ^ (c + 1) + 1) =
        f * G x.length + f * (x.length + 1) ^ (c + 1) + f + G x.length +
          (x.length + 1) ^ (c + 1) + 1 := by ring
    rw [e]
    omega
  refine ⟨cfg, startup, ht.trans hbudget, hi, hend, hout, ?_⟩
  intro i hi
  obtain ⟨t, ht, hh⟩ := hr i (by omega)
  rw [enumCont_orbit _ i hi] at hh
  exact ⟨t, ht.trans hbudget, hh⟩

/-- **The enumerator's configuration contract** (generalized verifier budget): one
uniform finite machine, from its initial configuration, reaches the round of the first
candidate within `b (Tv(n + w) + (n + w + 1)^{c+1})` steps (`w = C(n+1)^c`); each round
either accepts (when `x ++ u ∈ V`) or advances to the next candidate within the same
budget; after the last candidate it halts rejecting.

**Proof sketch.** Instantiate `enumCont_from_body` with the body of the original
construction (unary width generator, captured verifier call on `x ++ u`, reversible
cleanup, fixed-width increment), bounding its startup and round costs by
`A (n + w + 1)^{c+1} + 3 Tv(n + w)`. -/
private theorem enumMachine_contracts (C c : ℕ) (V : Language Bool) (Tv : ℕ → ℕ)
    (MV : FinTM Bool) (hV : MV.DecidesInTime V Tv) :
    ∃ (b : ℕ) (E : FinTM Bool), ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
        startup ≤ b * (Tv (x.length + C * (x.length + 1) ^ c) +
          (x.length + C * (x.length + 1) ^ c + 1) ^ (c + 1)) ∧
        E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
        (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
        ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
          t ≤ b * (Tv (x.length + C * (x.length + 1) ^ c) +
            (x.length + C * (x.length + 1) ^ c + 1) ^ (c + 1)) ∧
          if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
            (E.tm.runFrom (cfg i) t).state = none ∧
              (E.tm.runFrom (cfg i) t).output = [true]
          else E.tm.runFrom (cfg i) t = cfg (i + 1) := by
  obtain ⟨U, f, hU⟩ := computesFunInTime_polyUnary C c
  obtain ⟨I, j, hI⟩ := computesFunInTime_incFixed
  let Q := bufferedCompTM enumCont_concatTM MV
  let R := bufferedCompTM enumCont_concatTM I
  let B := enumCont_sources Q R U
  let qv : B.State := .inl Q.tm.q₀
  let qi : B.State := .inr (.inl (.inl (some true)))
  have hQ : 0 < Q.k := by dsimp [Q, bufferedCompTM, enumCont_concatTM]; omega
  have hR : 0 < R.k := by dsimp [R, bufferedCompTM, enumCont_concatTM]; omega
  have hQB : Q.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
  have hRB : R.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
  have hUB : U.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
  have hB : 0 < B.k := lt_of_lt_of_le hQ hQB
  let A := 3 * f + 3 * j + 60
  let P := fun n => (n + C * (n + 1) ^ c + 1) ^ (c + 1)
  let G := fun n => A * P n + 3 * Tv (n + C * (n + 1) ^ c)
  have hP1 : ∀ n, n + C * (n + 1) ^ c + 1 ≤ P n := by
    intro n
    calc n + C * (n + 1) ^ c + 1 = (n + C * (n + 1) ^ c + 1) ^ 1 := (pow_one _).symm
      _ ≤ P n := Nat.pow_le_pow_right (by omega) (by omega)
  have hP2 : ∀ n, (n + 1) ^ (c + 1) ≤ P n := fun n => Nat.pow_le_pow_left (by omega) _
  obtain ⟨b, E, hE⟩ := enumCont_from_body C c G V (enumCont_bodyTM B qv qi false) (.inr 0)
    (by
      intro x
      have hu := enumCont_lift_init U B hUB (fun q => .inr (.inr q))
        (by intro q inp work; rfl) x (List.replicate (C * (x.length + 1) ^ c) true)
        (f * (x.length + 1) ^ (c + 1)) (hU x)
      obtain ⟨t, ht, hn, he⟩ := enumCont_body_start_guarded B hB qv qi x
        (C * (x.length + 1) ^ c) (f * (x.length + 1) ^ (c + 1)) hu.1 hu.2
      refine ⟨t, ht.trans ?_, hn, he⟩
      have h1 := hP1 x.length
      have h2 := Nat.mul_le_mul_left f (hP2 x.length)
      have e : (3 * f + 3 * j + 60) * P x.length =
          3 * (f * P x.length) + 3 * (j * P x.length) + 60 * P x.length := by ring
      show _ ≤ (3 * f + 3 * j + 60) * P x.length + 3 * Tv (x.length + C * (x.length + 1) ^ c)
      rw [e]
      have : 0 ≤ j * P x.length := Nat.zero_le _
      omega)
    (by
      intro x s hs
      obtain ⟨tv, htv, hhv, hov⟩ := enumCont_verifier_call MV V Tv hV x s
      obtain ⟨ti, hti, hhi, hoi⟩ := enumCont_increment_call I j hI x s
      have hv := enumCont_lift_call Q B hQ hQB Sum.inl
        (by intro q inp work; rfl) Q.tm.q₀ x s [MultiTapeTM.indicator V (x ++ s)] tv hhv hov
      have hi := enumCont_lift_call R B hR hRB (fun q => .inr (.inl q))
        (by intro q inp work; rfl) (.inl (some true)) x s ((incFixed s).getD []) ti hhi hoi
      obtain ⟨t, htpos, ht, hn, he⟩ := enumCont_body_round_guarded B hB qv qi x s
        (MultiTapeTM.indicator V (x ++ s)) tv ti hv hi
      refine ⟨t, htpos, ?_, hn, he⟩
      have h1 := hP1 x.length
      have h3 : (j + 3) * (s.length + 1) ≤ (j + 3) * P x.length :=
        Nat.mul_le_mul_left _ (by rw [hs]; omega)
      have ht' : t ≤ 3 * (Tv (x.length + s.length) + 2 * (x.length + s.length) + 4) +
          3 * ((j + 3) * (s.length + 1)) + 2 * x.length + 3 * s.length + 22 := by omega
      rw [hs] at ht' h3
      have e : (3 * f + 3 * j + 60) * P x.length =
          3 * (f * P x.length) + 3 * ((j + 3) * P x.length) + 51 * P x.length := by ring
      show _ ≤ (3 * f + 3 * j + 60) * P x.length + 3 * Tv (x.length + C * (x.length + 1) ^ c)
      rw [e]
      have : 0 ≤ f * P x.length := Nat.zero_le _
      omega)
  refine ⟨b * (A + 3), E, fun x => ?_⟩
  obtain ⟨cfg, startup, hst, hi, hend, hout, hr⟩ := hE x
  have hbound : b * (G x.length + (x.length + 1) ^ (c + 1) + 1) ≤
      b * (A + 3) * (Tv (x.length + C * (x.length + 1) ^ c) + P x.length) := by
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left b
    have h1 := hP1 x.length
    have h2 := hP2 x.length
    show (A * P x.length + 3 * Tv (x.length + C * (x.length + 1) ^ c)) +
      (x.length + 1) ^ (c + 1) + 1 ≤ (A + 3) * (Tv (x.length + C * (x.length + 1) ^ c) + P x.length)
    have e : (A + 3) * (Tv (x.length + C * (x.length + 1) ^ c) + P x.length) =
        A * Tv (x.length + C * (x.length + 1) ^ c) + 3 * Tv (x.length + C * (x.length + 1) ^ c) +
          A * P x.length + 3 * P x.length := by ring
    rw [e]
    have : 0 ≤ A * Tv (x.length + C * (x.length + 1) ^ c) := Nat.zero_le _
    omega
  refine ⟨cfg, startup, hst.trans hbound, hi, hend, hout, fun i hi' => ?_⟩
  obtain ⟨t, ht, hh⟩ := hr i hi'
  exact ⟨t, ht.trans hbound, hh⟩

/-! **Continuation completion note (batch E2-cont A).** The historical
partial-fill descriptions above and below are retained under the statement
freeze. The former `enumMachine_contracts` admission is now discharged.
The new private body has proved initialization, exact buffered verifier
input, captured silent output, complete reversible scratch restoration,
in-place candidate replacement, and positive first-return round contracts.
`enumCont_from_body` supplies the audited exact-width loop instantiation,
catalog-generated `2^w-1` fuel, bounded rank orbit, terminal `2^w`, and
uniform startup/round budgets. -/

/-- **Brute-force enumeration with an arbitrary-time verifier** [AB09, Claim 2.4, the
enumeration argument]: if `MV` decides `V` within `Tv`, then some machine decides the
existential projection `{x | ∃ u, |u| = C(|x|+1)^c ∧ x ++ u ∈ V}` within
`b · 2^{C(n+1)^c} · (Tv(n + C(n+1)^c) + (n + C(n+1)^c + 1)^{c+1})`.

**Proof sketch.** The loop combinator runs one round per candidate `u` of width
`w = C(n+1)^c` (in fixed-width binary, starting from `0^w`); each round calls `MV` on
the assembled input `x ++ u` (at most `Tv(n + w)` steps plus polynomial overhead),
captures the verdict, restores the scratch tapes from a reversible log, and either halts
accepting or increments `u`; after `2^w` rejecting rounds it halts rejecting. -/
theorem exists_proj_decider (C c : ℕ) (V : Language Bool) (Tv : ℕ → ℕ)
    (MV : FinTM Bool) (hV : MV.DecidesInTime V Tv) :
    ∃ (b : ℕ) (E : FinTM Bool),
      E.DecidesInTime {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}
        (fun n => b * 2 ^ (C * (n + 1) ^ c) *
          (Tv (n + C * (n + 1) ^ c) + (n + C * (n + 1) ^ c + 1) ^ (c + 1))) := by
  classical
  obtain ⟨b, E, hE⟩ := enumMachine_contracts C c V Tv MV hV
  refine ⟨2 * b, E, fun x => ?_⟩
  obtain ⟨cfg, startup, hstartup, hinit, hend, hout, hround⟩ := hE x
  let w := C * (x.length + 1) ^ c
  let B := b * (Tv (x.length + w) + (x.length + w + 1) ^ (c + 1))
  let accept := fun i => MultiTapeTM.indicator V (x ++ enumWord w i)
  obtain ⟨t, ht, hh, ho⟩ := enumLoop_run E x cfg accept B 0 (2 ^ w)
    (by simpa only [Nat.zero_add] using And.intro hend hout)
    (fun j _ hj => hround j (by simpa only [Nat.zero_add] using hj))
  have hb : enumAny accept 0 (2 ^ w) =
      MultiTapeTM.indicator
        {z | ∃ u, u.length = C * (z.length + 1) ^ c ∧ z ++ u ∈ V} x := by
    have ha := enumAny_certificates x w V
    change enumAny accept 0 (2 ^ w) = true ↔ _ at ha
    cases he : enumAny accept 0 (2 ^ w) with
    | false =>
      have hx : ¬∃ u, u.length = w ∧ x ++ u ∈ V := by
        intro hx
        have := ha.mpr hx
        rw [he] at this
        contradiction
      simp [MultiTapeTM.indicator, w] at hx ⊢
      exact hx
    | true =>
      have hx := ha.mp he
      simp [MultiTapeTM.indicator, w] at hx ⊢
      exact hx
  have hcomp : E.ComputesInTime x [enumAny accept 0 (2 ^ w)] (startup + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hinit]
    exact ⟨hh, ho⟩
  rw [hb] at hcomp
  apply hcomp.mono
  have hB : B ≤ 2 ^ w * B := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
  calc startup + t ≤ B + 2 ^ w * B := Nat.add_le_add hstartup ht
       _ ≤ 2 ^ w * B + 2 ^ w * B := Nat.add_le_add_right hB _
       _ = 2 * b * 2 ^ (C * (x.length + 1) ^ c) *
           (Tv (x.length + C * (x.length + 1) ^ c) +
             (x.length + C * (x.length + 1) ^ c + 1) ^ (c + 1)) := by dsimp [B, w]; ring


/-- **`NP ⊆ EXP`** [AB09, Claim 2.4]: brute-force certificate enumeration.

**Proof sketch.** Let `L ∈ NP` with certificate length exactly `Q n = C(n+1)^c`
and verifier `V ∈ P` decided by machine `MV`. The deciding machine, on input
`x` of length `n`: evaluate the explicit formula `Q n` (the explicit formula is
what makes the width computable at all, phase-1 audit finding 1 and question 4)
and lay out a width-`Q n` all-`false` candidate certificate; in each round,
assemble `x ++ u` on a buffer, run `MV`, accept if it accepts, else increment
the candidate as a **fixed-width** counter and repeat, rejecting on width
overflow after the `2^(Q n)`-th round. Enumeration is over certificates of
exactly the definition's length — no majorant mismatch (audit question 4). The
verifier call is simulated with its decision bit captured in finite control, its
physical emissions suppressed and its halt redirected to the loop controller, so
the real output stays empty until the final answer (the output tape is
append-only); `MV`'s simulated state, heads, work region and the captured bit are
reset between rounds. This is the enumerator `Complexity.exists_proj_decider`
(the fixed-width carry, buffered captured call, timed loop invariant and budget
normalization are proved above), instantiated at `Tv = a (n+1)^d`. Budget: at
most `2^(Q n)` rounds of cost polynomial in `n + Q n + 1`, i.e.
`a · 2^(Q n) (n + Q n + 1)^d ≤ 2^(n^e)` for a fixed degree `e`, small lengths
absorbed into `DTIME`'s constant: `L ∈ EXP`. -/
theorem NP_subset_EXP : NP ⊆ EXP := by
  rintro L ⟨C, c, V, hV, hL⟩
  obtain ⟨a, d, MV, hMV⟩ := mem_P_iff.mp hV
  obtain ⟨b, E, hE⟩ := exists_proj_decider C c V (fun n => a * (n + 1) ^ d) MV hMV
  obtain ⟨A, f, hbound⟩ := enumBudget_bound (b * (a + 1)) C c (d + c + 1)
  have hpoly : ∀ n : ℕ, b * 2 ^ (C * (n + 1) ^ c) *
      (a * (n + C * (n + 1) ^ c + 1) ^ d + (n + C * (n + 1) ^ c + 1) ^ (c + 1)) ≤
      b * (a + 1) * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ (d + c + 1) := by
    intro n
    set X := n + C * (n + 1) ^ c + 1
    have h1 : X ^ d ≤ X ^ (d + c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : X ^ (c + 1) ≤ X ^ (d + c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : a * X ^ d + X ^ (c + 1) ≤ (a + 1) * X ^ (d + c + 1) := by
      have := Nat.mul_le_mul_left a h1
      rw [Nat.add_mul, one_mul]; omega
    calc b * 2 ^ (C * (n + 1) ^ c) * (a * X ^ d + X ^ (c + 1)) ≤
        b * 2 ^ (C * (n + 1) ^ c) * ((a + 1) * X ^ (d + c + 1)) := Nat.mul_le_mul_left _ h3
      _ = _ := by ring
  have heq : {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V} = L :=
    Set.ext (fun x => (hL x).symm)
  rw [heq] at hE
  exact Set.mem_iUnion.mpr ⟨f, A, E, fun x =>
    (hE x).mono ((hpoly x.length).trans (hbound x.length))⟩

/-! ### A3 exponential split and clean padding verifier
The binary evaluator below is re-derived from the pinned `e3ShiftTM`
family in `Nondeterminism.lean`, under the private-harvest rule; the original
family remains unchanged and no file-scoped declaration is cited. -/

/-- Multiplication by a power of two prefixes zeroes to a nonzero binary word.
This is an exact binary representation, not an exponential unary emission. -/
private lemma a3_bits_shift (C p : ℕ) (hC : C ≠ 0) :
    Nat.bits (C * 2 ^ p) = List.replicate p false ++ Nat.bits C := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hp : C * 2 ^ p ≠ 0 := Nat.mul_ne_zero hC (Nat.ne_of_gt (Nat.pow_pos (by omega)))
    rw [show C * 2 ^ (p + 1) = 2 * (C * 2 ^ p) by ring, Nat.bit0_bits _ hp, ih]
    simp [List.replicate_succ]

/-- Replace each input symbol by a zero bit, then append a fixed binary word.
The scanner and fixed emission chain use no work tapes. -/
private def a3ShiftTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Unit ⊕ Fin (w.length + 1)
  tm := {
    q₀ := .inl ()
    tr := fun q inp _ => match q with
      | .inl _ => match inp with
        | some _ => ⟨.pos, fun i => i.elim0, some false, some (.inl ())⟩
        | none => controlAction 0 (some (.inr 0))
      | .inr i => emitAction w Sum.inr i }

/-- The shift scanner advances one input position and emits one zero per
step, retaining its live scanner state until the boundary blank.
**Proof sketch.** Induct on the number of consumed symbols. The input-head invariant
identifies the next bit, and the transition advances the head and appends
exactly one false bit without entering the fixed emission chain. -/
private lemma a3_shift_scan (w x : List Bool) : ∀ t, t ≤ x.length →
    ((a3ShiftTM w).tm.runFrom ((a3ShiftTM w).tm.initCfg x) t).state = some (.inl ()) ∧
    (((a3ShiftTM w).tm.runFrom ((a3ShiftTM w).tm.initCfg x) t).inputPos : ℕ) = t + 1 ∧
    ((a3ShiftTM w).tm.runFrom ((a3ShiftTM w).tm.initCfg x) t).output =
      List.replicate t false := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rfl, ?_, rfl⟩
    simp [MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    obtain ⟨hs, hp, ho⟩ := ih (by omega)
    have hstep : (a3ShiftTM w).tm.runFrom ((a3ShiftTM w).tm.initCfg x) (t + 1) =
        ((a3ShiftTM w).tm.tr (.inl ()) (some (x[t]'(by omega)))
          (((a3ShiftTM w).tm.runFrom ((a3ShiftTM w).tm.initCfg x) t).workTapeSymbols)).apply
          ((a3ShiftTM w).tm.runFrom ((a3ShiftTM w).tm.initCfg x) t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [inputSymbolInner (p := t) (by omega) (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hstep]
      simp [a3ShiftTM, Action.apply]
    · rw [hstep]
      simp only [a3ShiftTM, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      show (((a3ShiftTM w).tm.runFrom ((a3ShiftTM w).tm.initCfg x) t).inputPos : ℕ) + 1 = t + 2
      omega
    · rw [hstep]
      simp only [a3ShiftTM, Action.apply, ho]
      exact List.replicate_succ'.symm

/-- The scanner's blank transition enters the emission chain; the final
halting transition is charged explicitly. The total is `|x|+|w|+2`.
**Proof sketch.** Use the scanner invariant at the right boundary. The blank
transition enters the fixed emission chain with the accumulated zero bits;
the library emission theorem supplies the remaining word and halting step. -/
private lemma a3_shift_computes (w x : List Bool) :
    (a3ShiftTM w).ComputesInTime x (List.replicate x.length false ++ w)
      (x.length + w.length + 2) := by
  obtain ⟨hs, hp, ho⟩ := a3_shift_scan w x x.length (le_refl _)
  let cfg := (a3ShiftTM w).tm.runFrom ((a3ShiftTM w).tm.initCfg x) x.length
  have hp' : (cfg.inputPos : ℕ) = x.length + 1 := hp
  have hzero : cfg.inputPos ≠ 0 := by
    intro h
    rw [h] at hp'
    simp at hp'
  have hinp : cfg.inputSymbol = none := by
    unfold Cfg.inputSymbol
    rw [dif_neg hzero, dif_pos (by omega)]
  have henter : (a3ShiftTM w).tm.runFrom ((a3ShiftTM w).tm.initCfg x) (x.length + 1) =
      (controlAction 0 (some (.inr (0 : Fin (w.length + 1))))).apply cfg := by
    rw [MultiTapeTM.runFrom_succ_eq_step']
    change (a3ShiftTM w).tm.step cfg = _
    simp only [MultiTapeTM.step, show cfg.state = some (.inl ()) from hs, a3ShiftTM, hinp]
  let next := (a3ShiftTM w).tm.runFrom ((a3ShiftTM w).tm.initCfg x) (x.length + 1)
  have hnext : next.state = some (.inr (0 : Fin (w.length + 1))) := by
    dsimp only [next]
    rw [henter]
    rfl
  have houtput : next.output = List.replicate x.length false := by
    dsimp only [next]
    rw [henter]
    simp only [controlAction, Action.apply, Option.toList_none, List.append_nil]
    exact ho
  obtain ⟨hh, hout⟩ := emit_halts (a3ShiftTM w).tm w Sum.inr
    (fun _ _ _ => rfl) next hnext
  apply (computesInTime_iff _ _ _ _).mpr
  rw [show x.length + w.length + 2 = (x.length + 1) + (w.length + 1) by omega,
    MultiTapeTM.runFrom_add]
  exact ⟨hh, by simpa only [houtput] using hout⟩

/-- The fixed-word binary shift has a monotone linear budget on all inputs. -/
private lemma a3_shift_timed (w : List Bool) :
    (a3ShiftTM w).ComputesFunInTime (fun x => List.replicate x.length false ++ w)
      (fun n => (w.length + 2) * (n + 1)) := by
  intro x
  apply (a3_shift_computes w x).mono
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- The exact binary value of exponential padding is polynomial-time
computable before any validity check.
**Proof sketch.** At coefficient zero emit the empty binary word. Otherwise
the catalog emits `(n+1)^c` unary symbols. The native shift scanner emits
that many zeroes followed by the fixed nonzero coefficient's bits. Timed
buffered composition and the binary shift identity identify the value;
the monotone linear second-stage cost yields degree `c+1` uniformly. -/
private lemma a3_exp_bits_timed (C c : ℕ) :
    ∃ (M : FinTM Bool) (A : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits (C * 2 ^ (x.length + 1) ^ c))
        (fun n => A * (n + 1) ^ (c + 1)) := by
  by_cases hC : C = 0
  · obtain ⟨M, A, hM⟩ := computesFunInTime_const ([] : List Bool)
    refine ⟨M, A, fun x => ?_⟩
    simpa only [hC, Nat.zero_mul, Nat.zero_bits] using (hM x).mono
      (Nat.mul_le_mul_left A (by
        simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
          (show 1 ≤ c + 1 by omega)))
  · obtain ⟨U, a, hU⟩ := computesFunInTime_polyUnary 1 c
    obtain ⟨M, b, hM⟩ := computesFunInTime_comp hU (a3_shift_timed (Nat.bits C))
      (by intro m n h; exact Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1))
    let k := (Nat.bits C).length + 2
    refine ⟨M, b * (a + 1) * (k + 1), fun x => ?_⟩
    have hc := hM x
    simp only [Function.comp_apply, List.length_replicate, Nat.one_mul,
      ← a3_bits_shift C _ hC] at hc
    apply hc.mono
    let p := (x.length + 1) ^ (c + 1)
    have hp : 1 ≤ p := Nat.one_le_pow _ _ (Nat.succ_pos _)
    change b * (a * p + k * (a * p + 1) + 1) ≤ b * (a + 1) * (k + 1) * p
    calc
      _ = b * (a * (k + 1) * p + (k + 1)) := by ring
      _ ≤ b * (a * (k + 1) * p + (k + 1) * p) :=
        Nat.mul_le_mul_left b (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hp) _)
      _ = _ := by ring

/-- Turn a clean installed singleton call into an ordinary decider. Copying
and simultaneous rewinding prepare the exact argument seam. The dedicated
entry state executes one source action before testing the return state. -/
private def a3RunTM (C : FinTM Bool) (hk : 0 < C.k) (entry exit : C.State) : FinTM Bool where
  k := C.k
  State := Fin 3 ⊕ C.State
  tm := {
    q₀ := .inl 0
    tr := fun q inp work => match q with
      | .inl i => if i = 0 then
          match inp with
          | some b => ⟨.pos, fun j => if j.val = 0 then (some (some b), .pos)
              else (none, 0), none, some (.inl 0)⟩
          | none => ⟨.neg, fun j => if j.val = 0 then (none, .neg)
              else (none, 0), none, some (.inl 1)⟩
        else if i = 1 then
          match work ⟨0, hk⟩ with
          | some _ => ⟨.neg, fun j => if j.val = 0 then (none, .neg)
              else (none, 0), none, some (.inl 1)⟩
          | none => ⟨.pos, fun j => if j.val = 0 then (none, .pos)
              else (none, 0), none, some (.inl 2)⟩
        else (C.tm.tr entry inp work).mapState Sum.inr
      | .inr q => if q = exit then
          ⟨0, fun _ => (none, 0), work ⟨0, hk⟩, none⟩
        else (C.tm.tr q inp work).mapState Sum.inr }

/-- The copy/rewind phase keeps all scratch tapes blank. -/
private def a3LoadCfg (C : FinTM Bool) {x : List Bool} (q : Fin 3)
    (p : Fin (x.length + 2)) (u : List Bool) (h : ℤ) :
    Cfg C.k Bool (Fin 3 ⊕ C.State) x :=
  ⟨some (.inl q), p, (fun i => if i.val = 0 then bufferTape u else fun _ => none),
    (fun i => if i.val = 0 then h else 0), []⟩

/-- One copy transition appends the next input bit to tape zero.
**Proof sketch.** Read the current input symbol using its indexed position.
The tape-update identity appends it to the copied prefix, while every other
tape remains blank and stationary; both active heads advance together. -/
private lemma a3_copy_step (C : FinTM Bool) (hk : 0 < C.k) (entry exit : C.State)
    (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (a3RunTM C hk entry exit).tm.step
      (a3LoadCfg C (x := x) 0 ⟨i + 1, by omega⟩ (x.take i) i) =
      a3LoadCfg C (x := x) 0 ⟨i + 2, by omega⟩ (x.take (i + 1)) (i + 1) := by
  have hr : (a3LoadCfg C (x := x) 0 ⟨i + 1, by omega⟩ (x.take i) i).inputSymbol =
      some x[i] := inputSymbolInner i (by simp [a3LoadCfg]; omega) hi
  unfold MultiTapeTM.step
  change ((a3RunTM C hk entry exit).tm.tr (.inl 0) _ _).apply _ = _
  simp only [a3RunTM, ↓reduceIte]
  rw [hr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · apply Fin.ext
    change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 2
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext j
    by_cases hz : j.val = 0
    · simp only [Action.apply, a3LoadCfg, hz, ↓reduceIte]
      rw [List.take_succ_eq_append_getElem hi, bufferTape_append,
        List.length_take_of_le (Nat.le_of_lt hi)]
    · simp [Action.apply, a3LoadCfg, hz]
  · funext j; by_cases hz : j.val = 0 <;> simp [Action.apply, a3LoadCfg, hz]

/-- Copying starts from genuine blank tapes and charges every input symbol. -/
private lemma a3_copy_run (C : FinTM Bool) (hk : 0 < C.k) (entry exit : C.State)
    (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    (a3RunTM C hk entry exit).tm.runFrom ((a3RunTM C hk entry exit).tm.initCfg x) i =
      a3LoadCfg C (x := x) 0 ⟨i + 1, by omega⟩ (x.take i) i := by
  induction i with
  | zero =>
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext j z; simp [MultiTapeTM.initCfg, Cfg.init, a3LoadCfg, bufferTape]
    · funext j; simp [MultiTapeTM.initCfg, Cfg.init, a3LoadCfg]
  | succ i ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), a3_copy_step C hk entry exit x i (by omega)]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc]

/-- Rewind input and copied argument together, including the empty input.
The mandatory left move preceding this phase starts at the correct blank.
**Proof sketch.** Induct on the number of copied cells still to cross. Each
nonblank cell moves both heads left. At the left blank, one right move
places both heads at zero and leaves all other tapes at their blank seam. -/
private lemma a3_load_rewind (C : FinTM Bool) (hk : 0 < C.k) (entry exit : C.State)
    (x : List Bool) (j : ℕ) (hj : j ≤ x.length) :
    (a3RunTM C hk entry exit).tm.runFrom
      (a3LoadCfg C (x := x) 1 ⟨j, by omega⟩ x ((j : ℤ) - 1)) (j + 1) =
      Cfg.ofWords (.inl (2 : Fin 3)) (stateWord C.k x) := by
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [a3RunTM, a3LoadCfg, Cfg.workTapeSymbols, Nat.cast_zero, zero_sub,
      show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, bufferTape_left]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · apply Fin.ext
      change (moveInputPos (⟨0, by omega⟩ : Fin (x.length + 2)) .pos).val = 1
      rw [moveInputPos_pos_of_ne_right _ (by simp)]
    · funext i; by_cases hz : i.val = 0 <;> simp [Action.apply, Cfg.ofWords, stateWord, bufferTape, hz]
    · funext i; by_cases hz : i.val = 0 <;> simp [Action.apply, Cfg.ofWords, hz]
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (a3RunTM C hk entry exit).tm.step
        (a3LoadCfg C (x := x) 1 ⟨j + 1, by omega⟩ x ((j + 1 : ℕ) - 1)) =
        a3LoadCfg C (x := x) 1 ⟨j, by omega⟩ x ((j : ℤ) - 1) := by
      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [a3RunTM, a3LoadCfg, Cfg.workTapeSymbols,
        show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < x.length)]
      refine Cfg.ext rfl ?_ ?_ ?_ rfl
      · apply Fin.ext
        change (moveInputPos (⟨j + 1, by omega⟩ : Fin (x.length + 2)) .neg).val = j
        rw [moveInputPos_neg_val]
        simp
      · funext i; by_cases hz : i.val = 0 <;> simp [Action.apply, a3LoadCfg, hz]
      · funext i; by_cases hz : i.val = 0 <;> simp [Action.apply, a3LoadCfg, hz, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- The ordinary input loader reaches the exact clean-call seam in linear time.
**Proof sketch.** Copy the entire input, take the mandatory left move at its
right blank, and apply the rewind invariant. The two phases and their
boundary actions cost exactly twice the input length plus two. -/
private lemma a3_run_start (C : FinTM Bool) (hk : 0 < C.k) (entry exit : C.State)
    (x : List Bool) :
    (a3RunTM C hk entry exit).tm.runFrom ((a3RunTM C hk entry exit).tm.initCfg x)
      (2 * x.length + 2) = Cfg.ofWords (.inl (2 : Fin 3)) (stateWord C.k x) := by
  have hc := a3_copy_run C hk entry exit x x.length (le_refl _)
  rw [List.take_length] at hc
  have hs : (a3RunTM C hk entry exit).tm.step
      (a3LoadCfg C (x := x) 0 ⟨x.length + 1, by omega⟩ x x.length) =
      a3LoadCfg C (x := x) 1 ⟨x.length, by omega⟩ x ((x.length : ℤ) - 1) := by
    have hr : (a3LoadCfg C (x := x) 0 ⟨x.length + 1, by omega⟩ x x.length).inputSymbol = none :=
      by simp [Cfg.inputSymbol, a3LoadCfg]
    unfold MultiTapeTM.step
    change ((a3RunTM C hk entry exit).tm.tr (.inl 0) _ _).apply _ = _
    simp only [a3RunTM, ↓reduceIte]
    rw [hr]
    refine Cfg.ext rfl ?_ ?_ ?_ rfl
    · apply Fin.ext
      change (moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) .neg).val = x.length
      rw [moveInputPos_neg_val]
      simp
    · funext i; by_cases hz : i.val = 0 <;> simp [Action.apply, a3LoadCfg, hz]
    · funext i; by_cases hz : i.val = 0 <;> simp [Action.apply, a3LoadCfg, hz, sub_eq_add_neg]
  have he : (a3RunTM C hk entry exit).tm.runFrom
      ((a3RunTM C hk entry exit).tm.initCfg x) (x.length + 1) =
      a3LoadCfg C (x := x) 1 ⟨x.length, by omega⟩ x ((x.length : ℤ) - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hs]
  rw [show 2 * x.length + 2 = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, he]
  exact a3_load_rewind C hk entry exit x x.length (le_refl _)

/-- The host follows a clean call until its first return, preserving every
configuration field through state renaming. -/
private lemma a3_run_guarded (C : FinTM Bool) (hk : 0 < C.k) (entry exit : C.State)
    {x : List Bool} (cfg : Cfg C.k Bool C.State x) (t : ℕ)
    (hguard : ∀ j < t, (C.tm.runFrom cfg j).state ≠ some exit) :
    (a3RunTM C hk entry exit).tm.runFrom (cfg.mapState Sum.inr) t =
      (C.tm.runFrom cfg t).mapState Sum.inr := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hguard j (by omega)),
      MultiTapeTM.runFrom_succ_eq_step']
    cases hs : (C.tm.runFrom cfg t).state with
    | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
    | some q =>
      have hq : q ≠ exit := by intro he; subst q; exact hguard t (by omega) hs
      simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
      simp only [a3RunTM, if_neg hq]
      rfl

/-- A dedicated entry action handles the permitted entry-equals-exit case;
all later actions dispatch at the actual first positive return.
**Proof sketch.** Execute the first source action unconditionally, then transfer
the remaining source run through the state embedding. The first-positive-
return hypothesis prevents any earlier interception, including when the
entry and return states coincide. -/
private lemma a3_run_call (C : FinTM Bool) (hk : 0 < C.k) (entry exit : C.State)
    (x y : List Bool) (t : ℕ) (ht : 0 < t)
    (hfirst : ∀ j, 0 < j → j < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k x)) j).state ≠ some exit)
    (hr : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k x)) t =
      Cfg.ofWords exit (stateWord C.k y)) :
    (a3RunTM C hk entry exit).tm.runFrom
      (Cfg.ofWords (input := x) (.inl (2 : Fin 3)) (stateWord C.k x)) t =
      (Cfg.ofWords exit (stateWord C.k y)).mapState Sum.inr := by
  let cfg := Cfg.ofWords (input := x) entry (stateWord C.k x)
  have hstep : (a3RunTM C hk entry exit).tm.step
      (Cfg.ofWords (input := x) (.inl (2 : Fin 3)) (stateWord C.k x)) =
      (C.tm.step cfg).mapState Sum.inr := by
    simp only [MultiTapeTM.step, Cfg.ofWords, a3RunTM,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte]
    rfl
  have hguard : ∀ j < t - 1, (C.tm.runFrom (C.tm.step cfg) j).state ≠ some exit := by
    intro j hj
    have h := hfirst (j + 1) (by omega) (by omega)
    simpa only [MultiTapeTM.runFrom_succ_eq_step] using h
  have hrun := a3_run_guarded C hk entry exit (C.tm.step cfg) (t - 1) hguard
  have hrest : C.tm.runFrom (C.tm.step cfg) (t - 1) =
      Cfg.ofWords exit (stateWord C.k y) := by
    rw [← MultiTapeTM.runFrom_succ_eq_step, Nat.sub_add_cancel ht]
    exact hr
  rw [hrest] at hrun
  conv_lhs => rw [← Nat.sub_add_cancel ht, MultiTapeTM.runFrom_succ_eq_step, hstep]
  exact hrun

/-- Extract the installed singleton from a genuine tape zero, after the
complete captured call and cleanup. No source emission is exposed early. -/
private lemma a3_run_singleton (C : FinTM Bool) (hk : 0 < C.k) (entry exit : C.State)
    (x : List Bool) (b : Bool) (t : ℕ) (ht : 0 < t)
    (hfirst : ∀ j, 0 < j → j < t →
      (C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k x)) j).state ≠ some exit)
    (hr : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k x)) t =
      Cfg.ofWords exit (stateWord C.k [b])) :
    (a3RunTM C hk entry exit).ComputesInTime x [b] (2 * x.length + 2 + t + 1) := by
  apply (computesInTime_iff _ _ _ _).mpr
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
    a3_run_start, a3_run_call C hk entry exit x [b] t ht hfirst hr]
  simp [MultiTapeTM.step, Cfg.mapState, Cfg.ofWords, stateWord, a3RunTM,
    Cfg.workTapeSymbols, Action.apply, bufferTape]

/-- An installed clean call implements an ordinary decider with explicit
linear loading overhead. The result may subsequently be run on a recovered
prefix with the source time charged at that prefix's actual length.
**Proof sketch.** The public install bridge supplies positive tape count,
first positive return, and a fully restored singleton-result seam. Copy and
rewind the ordinary input, execute the mandatory first action, follow the
call until its observed return, then emit the installed decision bit. -/
private lemma a3_decider_clean (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ)
    (hM : M.DecidesInTime L T) :
    ∃ (R : FinTM Bool) (B : ℕ),
      R.DecidesInTime L (fun n => B * (T n + n + 2)) := by
  classical
  obtain ⟨C, entry, exit, A, hk, hC⟩ := exists_installCallTM M
    (fun x => [MultiTapeTM.indicator L x]) T hM
  refine ⟨a3RunTM C hk entry exit, A + 3, fun x => ?_⟩
  obtain ⟨t, ht, hp, hfirst, hr⟩ := hC x x
  have h := a3_run_singleton C hk entry exit x (MultiTapeTM.indicator L x) t hp hfirst hr
  apply h.mono
  have ht' : t ≤ A * (T x.length + x.length + 2) := by
    simpa only [List.length_singleton, Nat.add_assoc] using ht
  calc
    _ ≤ A * (T x.length + x.length + 2) + 3 * (T x.length + x.length + 2) := by omega
    _ = _ := by ring

/-- Timed buffered composition at the actual intermediate word. This keeps
source time bounds at their validated lengths rather than at a coarse
output-size majorant. -/
private lemma a3_comp_at (F G : FinTM Bool) (x y z : List Bool) (s t : ℕ)
    (hF : F.ComputesInTime x y s) (hG : G.ComputesInTime y z t) :
    (bufferedCompTM F G).ComputesInTime x z (s + y.length + 2 + t) := by
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ := bufferedComp_start F G x y s hF
  obtain ⟨tag, _, hr⟩ := bufferedSecondCfg_run F G (G.tm.initCfg y) true
    (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads t
  have hc := (computesInTime_iff _ _ _ _).mp hG
  have hh : (bufferedCompTM F G).ComputesInTime x z (a + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [bufferedSecondCfg, Option.map_eq_none_iff] using hc.1, hc.2⟩
  exact hh.mono (by omega)

/-- Reject an empty failure payload; on a nonempty payload start the
supplied machine from its genuine initial configuration after one step. -/
private def a3NonemptyTM (M : FinTM Bool) : FinTM Bool where
  k := M.k
  State := Unit ⊕ M.State
  tm := {
    q₀ := .inl ()
    tr := fun q inp work => match q with
      | .inl _ => match inp with
        | none => ⟨0, fun _ => (none, 0), some false, none⟩
        | some _ => controlAction 0 (some (.inr M.tm.q₀))
      | .inr q => (M.tm.tr q inp work).mapState Sum.inr }

/-- After the nonempty guard, the source run is preserved exactly. -/
private lemma a3_nonempty_run (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (t : ℕ) :
    (a3NonemptyTM M).tm.runFrom (cfg.mapState Sum.inr) t =
      (M.tm.runFrom cfg t).mapState Sum.inr := by
  apply MultiTapeTM.runFrom_comm_of_step (fun cfg => cfg.mapState Sum.inr) ?_ cfg t
  intro cfg
  cases hs : cfg.state with
  | none => simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_none]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rfl

/-- The failed-search payload emits exactly one rejecting bit. -/
private lemma a3_nonempty_nil (M : FinTM Bool) :
    (a3NonemptyTM M).ComputesInTime [] [false] 1 := by
  apply (computesInTime_iff _ _ _ _).mpr
  simp [MultiTapeTM.runFrom, MultiTapeTM.step, MultiTapeTM.initCfg, Cfg.init,
    Cfg.inputSymbol, a3NonemptyTM, Action.apply]

/-- Successful split payloads enter the source machine, charging the guard. -/
private lemma a3_nonempty_computes (M : FinTM Bool) (x y : List Bool) (t : ℕ)
    (hx : x ≠ []) (hM : M.ComputesInTime x y t) :
    (a3NonemptyTM M).ComputesInTime x y (t + 1) := by
  have hs : (a3NonemptyTM M).tm.step ((a3NonemptyTM M).tm.initCfg x) =
      (M.tm.initCfg x).mapState Sum.inr := by
    cases x with
    | nil => contradiction
    | cons b x =>
      simp [MultiTapeTM.step, MultiTapeTM.initCfg, Cfg.init, Cfg.inputSymbol,
        a3NonemptyTM, controlAction, Action.apply, Cfg.mapState, moveInputPos_zero]
  apply (computesInTime_iff _ _ _ _).mpr
  rw [MultiTapeTM.runFrom_succ_eq_step, hs, a3_nonempty_run]
  have hc := (computesInTime_iff _ _ _ _).mp hM
  exact ⟨by simpa only [Cfg.mapState, Option.map_eq_none_iff] using hc.1, hc.2⟩

/-- Exponential padding has a unique split, including coefficient zero and
degree zero: the prefix length increases strictly and the suffix length
is nondecreasing. -/
private lemma a3_split_strictMono (C c : ℕ) :
    StrictMono (fun n : ℕ => n + C * 2 ^ (n + 1) ^ c) := by
  intro n m hnm
  exact Nat.add_lt_add_of_lt_of_le hnm (Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left (by omega) c)))

/-- The finite exponential-length search, with an explicit failure value. -/
private def a3Split (C c m : ℕ) : Option ℕ :=
  (List.range (m + 1)).find? (fun n => decide (n + C * 2 ^ (n + 1) ^ c = m))

/-- A successful search certifies its exact length equation and input bound. -/
private lemma a3_split_spec (C c m n : ℕ) (h : a3Split C c m = some n) :
    n ≤ m ∧ n + C * 2 ^ (n + 1) ^ c = m := by
  have hn := List.mem_of_find?_eq_some h
  have he := List.find?_some h
  exact ⟨Nat.le_of_lt_succ (List.mem_range.mp hn), of_decide_eq_true he⟩

/-- Exhaustion excludes every natural split, not only a chosen default. -/
private lemma a3_split_none_iff (C c m : ℕ) :
    a3Split C c m = none ↔ ¬∃ n, n + C * 2 ^ (n + 1) ^ c = m := by
  rw [a3Split, List.find?_eq_none]
  constructor
  · intro h hex
    obtain ⟨n, hn⟩ := hex
    exact h n (List.mem_range.mpr (by omega)) (by simpa using hn)
  · intro h n _ hn
    exact h ⟨n, of_decide_eq_true hn⟩

/-- Every valid exponential split is recovered by the finite search. -/
private lemma a3_split_complete (C c m n : ℕ)
    (hn : n + C * 2 ^ (n + 1) ^ c = m) : a3Split C c m = some n := by
  cases hs : a3Split C c m with
  | none => exact False.elim ((a3_split_none_iff C c m).mp hs ⟨n, hn⟩)
  | some k =>
    have hk := (a3_split_spec C c m k hs).2
    exact congrArg some ((a3_split_strictMono C c).injective (hk.trans hn.symm))

/-- A positive exponential coefficient rejects the empty verifier input. -/
private lemma a3_split_empty (C c : ℕ) (hC : 0 < C) : a3Split C c 0 = none := by
  apply (a3_split_none_iff C c 0).mpr
  rintro ⟨n, hn⟩
  have hp : 0 < C * 2 ^ (n + 1) ^ c := Nat.mul_pos hC (Nat.pow_pos (by omega))
  omega

/-- The exponential search returns a threaded pair, or an empty rejection word. -/
private def a3SplitWord (C c : ℕ) (y : List Bool) : List Bool :=
  match a3Split C c y.length with
  | some i => pairEncode (y.take i) (y.drop i)
  | none => []

/-- The emitted split has a linear length bound, including malformed inputs. -/
private lemma a3_split_length (C c : ℕ) (y : List Bool) :
    (a3SplitWord C c y).length ≤ 2 * y.length + 2 := by
  cases hs : a3Split C c y.length with
  | none => simp [a3SplitWord, hs]
  | some i =>
    have hi := (a3_split_spec C c y.length i hs).1
    simp [a3SplitWord, hs, pairEncode]
    omega

/-- The width-parametric search has a polynomial budget before validation.
**Proof sketch.** Instantiate the public search at the exponential binary
width evaluator. Its candidate length is at most one past the input length;
`n+2 ≤ 2(n+1)` absorbs this allowance and the linear search overhead. -/
private lemma a3_split_timed (C c : ℕ) :
    ∃ (M : FinTM Bool) (A : ℕ), M.ComputesFunInTime (a3SplitWord C c)
      (fun n => A * (n + 1) ^ (c + 2)) := by
  obtain ⟨E, B, hE⟩ := a3_exp_bits_timed C c
  obtain ⟨M, D, hM⟩ := computesFunInTime_splitSolveWith
    (fun n => C * 2 ^ (n + 1) ^ c) E (fun n => B * (n + 1) ^ (c + 1))
    (by
      intro n m h
      exact Nat.mul_le_mul_left B
        (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) (c + 1))) hE
  refine ⟨M, D * (B * 2 ^ (c + 1) + 2), fun w => ?_⟩
  have halign : a3Split C c w.length =
      solveSplitWith (fun n => C * 2 ^ (n + 1) ^ c) w.length := by
    simp only [a3Split, solveSplitWith, Bool.beq_eq_decide_eq]
  have hm := hM w
  change M.ComputesInTime w (a3SplitWord C c w) _
  unfold a3SplitWord
  rw [halign]
  apply hm.mono
  have hp : w.length + 1 ≤ (w.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos w.length)
      (show 1 ≤ c + 1 by omega)
  have hshift : (w.length + 1 + 1) ^ (c + 1) ≤
      2 ^ (c + 1) * (w.length + 1) ^ (c + 1) := by
    simpa only [Nat.mul_pow] using Nat.pow_le_pow_left
      (show w.length + 1 + 1 ≤ 2 * (w.length + 1) by omega) (c + 1)
  have hsum : B * (w.length + 1 + 1) ^ (c + 1) + w.length + 2 ≤
      (B * 2 ^ (c + 1) + 2) * (w.length + 1) ^ (c + 1) := by
    have h := Nat.mul_le_mul_left B hshift
    calc
      _ ≤ B * (2 ^ (c + 1) * (w.length + 1) ^ (c + 1)) +
          2 * (w.length + 1) ^ (c + 1) := by omega
      _ = _ := by ring
  calc
    _ ≤ D * (w.length + 1) *
        ((B * 2 ^ (c + 1) + 2) * (w.length + 1) ^ (c + 1)) :=
      Nat.mul_le_mul_left _ hsum
    _ = _ := by rw [Nat.pow_succ]; ring

/-- The padding verifier ignores certificate bits and decides the unique
recovered prefix. Failed split searches reject explicitly. -/
private def a3Verifier (L : Language Bool) (c : ℕ) : Language Bool :=
  {y | match a3Split 1 c y.length with
    | none => False
    | some n => y.take n ∈ L}

/-- On every exact-width concatenation, split recovery returns its own prefix. -/
private lemma a3_verifier_append (L : Language Bool) (c : ℕ) (x u : List Bool)
    (hu : u.length = 2 ^ (x.length + 1) ^ c) :
    x ++ u ∈ a3Verifier L c ↔ x ∈ L := by
  have hs := a3_split_complete 1 c (x ++ u).length x.length
    (by simp [hu])
  change (match a3Split 1 c (x ++ u).length with
    | none => False | some n => (x ++ u).take n ∈ L) ↔ x ∈ L
  simp only [hs, List.take_left]

/-- The exact split equation bounds the captured source deadline by the
whole verifier-input length, including degree zero. -/
private lemma a3_source_budget (a c m n : ℕ)
    (h : a3Split 1 c m = some n) : a * 2 ^ n ^ c ≤ a * m := by
  have he := (a3_split_spec 1 c m n h).2
  simp only [Nat.one_mul] at he
  have hp : 2 ^ n ^ c ≤ 2 ^ (n + 1) ^ c :=
    Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left (Nat.le_succ n) c)
  exact Nat.mul_le_mul_left a (by omega)

/-- Split recovery, failed-search rejection, and a captured clean decider
call form a polynomial-time verifier.
**Proof sketch.** First recover the pair, with an empty failure payload.
A native one-step guard rejects failure. On success, extract the prefix
and run the clean installed source decider on its actual length. The split
equation bounds the source exponential time by the whole input length;
the pair has linear length. Timed buffered composition includes every
capture, rewind, and dispatch cost, uniformly over all inputs. -/
private lemma a3_verifier_mem_P (L : Language Bool) (a c : ℕ) (M : FinTM Bool)
    (hM : M.DecidesInTime L (fun n => a * 2 ^ n ^ c)) : a3Verifier L c ∈ P := by
  classical
  obtain ⟨R, B, hR⟩ := a3_decider_clean M L _ hM
  obtain ⟨F, A, hF⟩ := computesFunInTime_pairFst
  obtain ⟨S, D, hS⟩ := a3_split_timed 1 c
  let H := a3NonemptyTM (bufferedCompTM F R)
  let K := 3 * A + B * (a + 3) + 10
  refine mem_P_iff.mpr ⟨D + K, c + 2, bufferedCompTM S H, fun w => ?_⟩
  let P := (w.length + 1) ^ (c + 2)
  have hp : w.length + 1 ≤ P := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos w.length)
      (show 1 ≤ c + 2 by omega)
  cases hs : a3Split 1 c w.length with
  | none =>
    have hsource : S.ComputesInTime w [] (D * P) := by
      simpa only [a3SplitWord, hs] using hS w
    have hd : H.ComputesInTime [] [false] 1 := a3_nonempty_nil _
    have hc := a3_comp_at S H w [] [false] (D * P) 1 hsource hd
    have hv : MultiTapeTM.indicator (a3Verifier L c) w = false := by
      simp [MultiTapeTM.indicator, a3Verifier, hs]
    rw [hv]
    apply hc.mono
    simp only [List.length_nil]
    have hk : 3 ≤ K := by dsimp [K]; omega
    have hkP : 3 ≤ K * P := hk.trans (Nat.le_mul_of_pos_right K (by omega))
    calc
      _ ≤ D * P + K * P := by omega
      _ = _ := by dsimp [P]; ring
  | some n =>
    let x := w.take n
    let u := w.drop n
    let y := pairEncode x u
    obtain ⟨hn, he⟩ := a3_split_spec 1 c w.length n hs
    have hx : x.length = n := List.length_take_of_le hn
    have hy : y.length ≤ 2 * w.length + 2 := by
      have h := a3_split_length 1 c w
      simpa only [a3SplitWord, hs] using h
    have hF' : F.ComputesInTime y x (A * (y.length + 1)) := by
      simpa only [y, pairDecode_pairEncode, Option.map_some, Prod.fst,
        Option.getD_some] using hF y
    have hr : R.ComputesInTime x [MultiTapeTM.indicator L x]
        (B * (a * 2 ^ n ^ c + n + 2)) := by
      simpa only [hx] using hR x
    have hc := a3_comp_at F R y x [MultiTapeTM.indicator L x]
      (A * (y.length + 1)) (B * (a * 2 ^ n ^ c + n + 2)) hF' hr
    have hyne : y ≠ [] := by
      intro hz
      have hlen := congrArg List.length hz
      simp [y, pairEncode] at hlen
    have hg := a3_nonempty_computes (bufferedCompTM F R) y
      [MultiTapeTM.indicator L x] _ hyne hc
    have hsource : S.ComputesInTime w y (D * P) := by
      simpa only [a3SplitWord, hs] using hS w
    have hcomp := a3_comp_at S H w y [MultiTapeTM.indicator L x] (D * P) _ hsource hg
    have hv : MultiTapeTM.indicator (a3Verifier L c) w = MultiTapeTM.indicator L x := by
      simp only [MultiTapeTM.indicator, a3Verifier, Set.mem_setOf_eq, hs, x]
    rw [hv]
    apply hcomp.mono
    have hb := a3_source_budget a c w.length n hs
    have htime : B * (a * 2 ^ n ^ c + n + 2) ≤
        B * (a + 3) * (w.length + 1) := by
      calc
        _ ≤ B * ((a + 3) * (w.length + 1)) := Nat.mul_le_mul_left B (by
          simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
          omega)
        _ = _ := by ring
    have hlinear : A * (y.length + 1) ≤ 3 * A * (w.length + 1) := by
      calc
        _ ≤ A * (3 * (w.length + 1)) := Nat.mul_le_mul_left A (by omega)
        _ = _ := by ring
    have hsum : y.length + 2 +
        (A * (y.length + 1) + x.length + 2 + B * (a * 2 ^ n ^ c + n + 2) + 1) ≤
        K * (w.length + 1) := by
      rw [hx]
      calc
        _ ≤ 3 * A * (w.length + 1) + B * (a + 3) * (w.length + 1) +
            10 * (w.length + 1) := by omega
        _ = _ := by dsimp [K]; ring
    calc
      _ ≤ D * P + K * (w.length + 1) := by omega
      _ ≤ D * P + K * P := Nat.add_le_add_left (Nat.mul_le_mul_left K hp) _
      _ = _ := by dsimp [P]; ring

/-- **`EXP ⊆ NEXP`** [AB09, §2.6.2].

**Proof sketch.** Given `L ∈ EXP` decided in time `2^(n^c)`, take `C = 1` and
certificate length `p n = 2^((n+1)^c)` — nondecreasing in `n` (constant `2` at
`c = 0`), so that `n ↦ n + p n` is **strictly increasing** (the monotonicity
belongs to the sum, not to `p` — phase-1 audit, finding 8) — and the verifier
`V = {x ++ u : x ∈ L, |u| = p |x|}`. `V ∈ P`: on a string `y` of length `m`,
recover the unique `n` with `n + p n = m` by scanning `n ≤ m` (each evaluation
writes `2^((n+1)^c)` in binary, `(n+1)^c + 1 ≤ (m+1)^c + 1` bits — polynomial
in `m`, the audit's own check), reject if no split exists (including `m = 0`),
split off `x`, and run `L`'s decider: its `a · 2^(n^c)` budget is at most
`a · m`. Fixed-degree arithmetic and the split/copy machinery are named new
machine obligations for the fill. Certificates carry no information; padding
buys the verifier its time.

**A3 completion.** The local `a3ShiftTM` family re-derives the binary
width evaluator from the frozen in-file-scope predecessor template.
`a3_split_timed` instantiates the proved width-parametric search, and
`a3_nonempty_nil` rejects its empty failure payload, including input length
zero by `a3_split_empty`. `a3_decider_clean` uses `exists_installCallTM`
with its positive-tape and first-positive-return clauses; `a3_source_budget`
charges the relocated captured decider at the uniquely recovered prefix
length. `a3_verifier_mem_P` accounts for the complete timed pipeline. -/
theorem EXP_subset_NEXP : EXP ⊆ NEXP := by
  intro L hL
  obtain ⟨c, a, M, hM⟩ := Set.mem_iUnion.mp hL
  refine ⟨1, c, a3Verifier L c, a3_verifier_mem_P L a c M hM, fun x => ?_⟩
  constructor
  · intro hx
    let u := List.replicate (2 ^ (x.length + 1) ^ c) false
    have hu : u.length = 2 ^ (x.length + 1) ^ c := List.length_replicate ..
    exact ⟨u, by simpa only [Nat.one_mul] using hu,
      (a3_verifier_append L c x u hu).mpr hx⟩
  · rintro ⟨u, hu, hv⟩
    exact (a3_verifier_append L c x u (by simpa only [Nat.one_mul] using hu)).mp hv

end Complexity

```


## ===== audits/logs/ch3-p32-sweep.log =====

```
P3.2 GATE SWEEP at commit 7fbac9bdff79aee148b916e077ad93b6ce4693f9 (7fbac9bd), branch complexity/arora-barak-ch3-4, started 2026-10-08 15:28:16
== TCSlib/Complexity/TuringMachine/OracleAgreement
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:109:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:132:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:146:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:158:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:199:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:217:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:240:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/Diagonalization/EXPCOM
TCSlib/Complexity/Diagonalization/EXPCOM.lean:111:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/EXPCOM.lean:162:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/EXPCOM.lean:170:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/EXPCOM.lean:178:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/EXPCOM.lean:187:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/Diagonalization/Relativization
TCSlib/Complexity/Diagonalization/Relativization.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/Relativization.lean:148:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/Relativization.lean:209:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/Relativization.lean:222:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/Diagonalization/NotTimeConstructible
TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean:89:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/Diagonalization
P32_SWEEP_DONE

```


## ===== audits/logs/ch34-skeletons-stylelint.log =====

```
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5713 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7636 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1109 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  990 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  990 lines; 39 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean               157 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    406 lines; 13 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5713 lines; 8 public / 214 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7636 lines; 18 public / 318 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     292 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 739 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 739 lines; 10 public / 19 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     790 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     790 lines; 13 public / 49 private declarations
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    685 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    685 lines; 8 public / 11 private declarations
INFO  TCSlib/Complexity/TuringMachine/Configuration.lean                  224 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProg.lean                    562 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProgRun.lean                 433 lines; 35 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Deterministic.lean                  430 lines; 34 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       606 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       606 lines; 30 public / 10 private declarations
INFO  TCSlib/Complexity/TuringMachine/Finite.lean                         257 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1109 lines; 2 public / 75 private declarations
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               248 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean          112 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         517 lines; 29 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleAgreement.lean                247 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleFinite.lean                   131 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean         290 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   600 lines; 1 public / 50 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       464 lines; 2 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines; 1 public / 38 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines; 47 public / 42 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean     219 lines; 4 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines; 19 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines; 8 public / 59 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          981 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          981 lines; 2 public / 53 private declarations
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     948 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     948 lines; 49 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/StateRenaming.lean                  124 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Sweep.lean                          392 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/UnaryTape.lean                      84 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines; 4 public / 129 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines; 6 public / 17 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines; 37 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               591 lines; 10 public / 21 private declarations

style_lint: 0 FAIL, 8 WARN over 38 files
INFO  TCSlib/Complexity/Diagonalization/EXPCOM.lean                190 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean  93 lines; 1 public / 0 private declarations
INFO  TCSlib/Complexity/Diagonalization/Relativization.lean        227 lines; 5 public / 0 private declarations

style_lint: 0 FAIL, 0 WARN over 3 files

```
