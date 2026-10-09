# External audit pack — zone/virtual-input layer (§13), tranche A-S2, round 2

Round 1 (`audits/zone-infra-pack.md`, findings verbatim in
`audits/zone-infra-findings.md`) returned **1 blocker, 1 major, 2 minors**.
This round audits the repairs. Audited at commit `fb721402` (branch
`complexity/arora-barak-ch3-4`); the repaired files are attached in full,
with the round-1 pack and findings. The gate closes on zero blockers and
zero majors.

## Disposition table (verify each)

| Round-1 finding | Disposition |
|---|---|
| A-S2-1 (blocker: the inward room premise; the full-chain `Ω(T²)` family) | **Repaired as proposed.** `zoneShiftInW` carries no room condition (its guard is `1 ≤ i < ℓ` and lower-zone emptiness only); `zoneShiftOutW`'s receiving-room condition moved **inside its guard**; the dependent-hypothesis wrapper `zoneShift` is **removed**, replaced by hypothesis-free `zoneShiftIn`/`zoneShiftOut`; the head steps gain the guarded-total `zoneMove`; both machine rows drop the room binder and now realize the total guarded operation, identity branch included. **The required gate material is added**: `zoneShiftInW_full_donor` (the full-donor regression), `zoneStepPair`/`zoneCascadeRight` (your descending/move/ascending schedule as a pure fold), `zoneSide_cascadeRight` and `zoneCascadeRight_lengths` (the one-virtual-move and half-full-restoration statements, your schedule analysis adopted verbatim as the binding sketches), and `zoneCascade_cost_le` (the geometric charge bound, stated over `Finset.range` for import hygiene: `∑_{i<j} 4·(2^(i+1) + (i+1) + 1) ≤ 16·2^j`). Re-run your dead-end and full-chain instantiations against the repaired interface: both must now be served by legal inward shifts. |
| A-S2-2 (major: the received `sweepTM` refuted as the Z4 witness) | **Repaired as proposed**: the `one_work_tape_spaceUsed` sketch now names your counterexample as binding, routes the fill through a **demand-grown** sweep witness (reuse-and-refactor, no copying), and carries the all-`Γ'` retraction with the empty-alphabet and zero-tape cases; the composite's sketch names the corrected first stage and your `c₂·(c₁+1)` calculation. The statements are unchanged, as you judged them true. |
| A-S2-3 (minor: 25 vs 22 definitions) | Pack erratum acknowledged (the shipped round-1 pack stays verbatim); your inventory is adopted for fill ownership. The repair adds 6 sorried declarations and 3 definitions (`zoneShiftIn`, `zoneShiftOut`, `zoneMove`, `zoneStepPair`, `zoneCascadeRight` — recount and report the round-2 inventory). |
| A-S2-4 (minor: guard semantics; export names) | Docstrings corrected: the rows "realize the total guarded operation, including its identity branch"; the module's main-results list names `zoneShiftInW`/`OutW`, the new wrappers, the cascade exports, and `MultiTapeTM.spaceUsedByTape_le_card_Icc`. |
| A-S2-5 (note: the Ex 4.1 assessment overstated) | Adopted: design §13c downgrades it to a design-level verdict — stage 1 must specify a space-accounted input interface and parser ledger; a materialized input copy's `Ω(|x|)` is named. |
| A-S2-6 — A-S2-11 | No-findings rows and the evidence-boundary note carried; your layout/capacity arithmetic and Z3 record/guard numbers (record length 13; `351·(numStates+1)`; minimum 354 bits) are adopted into the eventual fill brief. |

## Brief for the auditor

1. Verify each disposition above against the attached repaired sources —
   in particular, blind-restate the **new** declarations
   (`zoneShiftIn`/`zoneShiftOut`, `zoneMove`, `zoneStepPair`,
   `zoneCascadeRight`, `zoneShiftInW_full_donor`, the three cascade
   contracts) and re-run your round-1 counterexamples: the `ℓ = 2`
   dead end, the full-chain family, and the four-move cycle must all be
   served by the repaired interface with the geometric ledger intact.
2. Check the repaired guards for new defects: the outward guard now
   conjoins fullness and receiving room — verify the identity branch is
   taken (not an ill-typed state) when either fails, and that the six
   sorried capacity fields remain provable under the new guards.
3. Check the cascade statements' preconditions (the classical pre-state)
   are the ones your schedule analysis needs — no stronger, no weaker —
   and that `zoneCascade_cost_le`'s reindexed form is your charge bound.
4. Confirm the Z4 sketches now carry your binding route and that no
   statement changed.
5. Report in the standard table; the debt screen (failure mode 5) applies
   to the repair delta (expected: no new copies — the cascade is a fold of
   the layer's own ops).

## Repository-side attestations (verify or challenge)

* Elaboration: the repaired `Build/Zone.lean` (588 lines) and
  `Robustness/SingleTape.lean` check at exit 0, zero `error:` lines;
  `Zone.lean` carries **22** sorry warnings (the round-1 18 declarations
  minus the removed `zoneShift`, plus the six repair declarations); lint
  0 FAIL both directories.
* The repair touched only `Build/Zone.lean` (rework) and the two Z4
  sketches in `SingleTape.lean` (docstring prose; statements byte-equal);
  `Codes2Tape.lean` and `AlphabetReduction.lean` are unchanged from
  round 1.
* Duplication ledger: new copies — none.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/zone-infra-r2-findings.md`; the gate closes on zero blockers and
majors.

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
  and the harmless-normalization identities are stated as the sanity layer
  `SpaceComplexity/ZeroSpace.lean` (S1-S4; elaborated, proofs deferred to fill,
  each certified true as stated by the P0 round-2 audit); the same applies verbatim to
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

### 4b. Post-statement-program roadmap (recorded 2026-10-09; user-directed)

Recorded at the close of the statement program — every statement gate shut
(P0, P3.1-P3.3, P4.1-P4.4, §12; decision log) — with roughly 150
audited-true sorried statements frozen and the carried obligations
collected in the nine `audits/*-resolutions.md` files. The remaining
stages, in order:

1. **Fill prerequisites** (gate the machine-heavy epochs, per §4a):
   - the **§12 routine-layer fill** (56 statements; partition in §4c) —
     the engine nearly every chapter-3/4 sketch names;
   - the **ARM extensions** (§2.5: nondeterministic and polynomial-width
     program layers; first customers the `PATH` walk and the counting
     verifier) — the open **colleague-sync item** on Hydroxyi's `LogProg`
     tree;
   - **Hennie-Stearns + the two-work-tape universal** (§2.1, CH34-Q3):
     Thms 1.9/3.1 to book strength; the retrofit pilot; candidate bonus:
     space bounds through it may yield Ex 4.1's space-efficient universal
     for the Thm 4.8 fill.
2. **The fill epochs** (`workflow.md` §4): sequential, risk-ordered,
   parallel disjoint-ownership batches from `briefs/`, epoch-boundary
   audits. Summit order per §6: the space-universal + Thm 4.8; the
   `NP^EXPCOM ⊆ EXP` simulator; the `TQBF` `ψᵢ` emitter; the
   linear-overhead universal NDTM; Thm 4.2(iii) + Savitch; Immerman-
   Szelepcsényi; Lemma 4.17. (Ladner's `H` rides with P3.4.)
3. **P3.4 (Ladner)** — on hold (user, 2026-10-09); drafts from the
   backlog §2 entry whenever called, independent of the fills.
4. **The chapter-1/2 retrofit** — not a gate; batches alongside the
   epochs. Queued housekeeping with it: the per-theme `Catalog` split
   (12.2c), the P3.1 natural-home promotions (unblocked), the additive
   sanity layers (`NSPACE` twins, `mem_NL_of_logspaceReducible`,
   `Cfg.InWindow` promotion).
5. **Closure** (`workflow.md` §5): zero-sorry sweep, campaign-wide drift
   attestation, final audit pack, blueprint increment (late-bound).
6. **Integration with `main`**: one PR per closed chapter (chapter 3's
   light half may go early), each carrying sweep, axiom prints, and the
   blueprint build, since main's CI runs only on `main`.

### 4c. Routine-layer fill: epoch/batch partition (recorded 2026-10-09)

The §12 surface is three files, 56 audited-true statements (Embed 13,
Seam 11, Catalog 32). Exclusive file ownership (workflow §4, ground
rule 1) shapes the partition; the proof plans inherited from the audit
loop (`audits/routine-infra-{findings,r2-findings,r3-findings}.md`,
summarized in `audits/routine-infra-resolutions.md`) make this the
best-documented fill surface of the campaign.

**Epoch F1 — kernels and routines (3 parallel batches, 37 targets).**

| Batch | Owns | Targets | Contents and risk notes |
|---|---|---|---|
| F1A | `Build/Embed.lean` | 13 | The `embedSlot` equations and one-step commutation core first, then the four flavor families: silent lockstep/frame/visited/cap (5), emit lockstep/frame/visited (4), the returning through-halt contracts and visited equalities (4). The round-3 report's five-step induction (component check, `Option.elim` successor equations, last-step case) is the mandated proof plan for the returning pair; the `hc ↔ 0 < T` equivalence uses both first-halt hypotheses |
| F1B | `Build/Seam.lean` | 11 | The **general-configuration trio first** (`_ofCfg` run / first-return / visited — the round-2/3 reports verify the lockstep decomposition and the `(Cfg.ofWords q w).mapState f = Cfg.ofWords (f q) w` identity), then the three canonical statements **as instances** (F1 audit, finding 1: 3+3+2+1+2 = 11), the two additive and one max space corollaries by projection, and the release pair (fresh-step equation + `Sum.inr` lockstep) |
| F1C | `Build/Catalog.lean` | 13 | Part 1: the five routines' 11 run/space contracts — the round-1 report's exact movement table (forward `L`/`d`/`p`, one turn, return, one entry; visited exactly `[-1, ·]`) is the mandated ledger, including equal-word compare, aliased indices, and the `2p + 2` increment count — plus W1 (`capture_visitedByTapeHead`, prefix-by-prefix over `capture_run`) and W2 (`redirectTM_spaceUsedByTape`, trajectory agreement through and past the halt) |

No F1 batch consumes another's file or fills; Part-1 routines are
self-contained transition inductions. Epoch-boundary audit after F1.

**Epoch F2 — the space annotations (1 batch, 19 targets, Catalog-owned).**

| Batch | Owns | Targets | Contents and risk notes |
|---|---|---|---|
| F2A | `Build/Catalog.lean` | 19 | The Part-2 rows, risk-ordered: (i) same-witness constant rows (`id`, `const`, `prepend`, `pairEncodeFixed`, `pairValid`, `pairDup`, `incFixed`); (ii) same-witness linear rows (`pairFst`, `pairSnd`, `pairConcat`); (iii) the case-split rows (`polyUnary`; `polyBits` with the **mandatory `C = 0` / `e = 0` constant-witness splits**, round-1 R5); (iv) `lengthBits` (the direct variable-width-counter construction — the imported sharp witness is explicitly not relied on), `pairLenCheck`, `stripLast` (linear banks; quadratic time is slack), `splitSolve`; (v) `cond` (W3: disjoint decider/branch banks) and `exists_loopTM_spaceUsed` (L: the round-1 answer-5 ledger — interval-union argument, fuel width `\|bits (R n)\|`, no per-round accumulation); (vi) **`pairMapSnd` last — the epoch summit and the only new machine of the fill**: the commissioned forwarding controller (validate/buffer, emit prefix, forward payload output; coefficient 1 on `Sg`; the round-2 R4 ledger), with the captured-payload witness disclaimed. Continuation brief anticipated |

F2 follows F1 so its constructions may consume proved F1 seams, though
none is required to. Epoch-boundary audit after F2 closes the §12 fill;
the S1-S12 sanity statements of the round-1 report are offered to both
epochs as optional permanent lemmas, landing wherever their batch owns.

**Ground rules** as `workflow.md` §4 (exclusive ownership, statement
freeze with escalation on unprovable-as-stated, per-batch sweeps over the
owned file, zip delivery with freeze verification, `git am -3`
integration). Every brief embeds its inherited audit material verbatim:
the movement tables (F1C), the through-halt induction (F1A), the general-
seam decomposition (F1B), and the R4/R5/answer-5 ledgers (F2A).

### 4d. Chapter-1/2 retrofit: inventories, partition, decisions (recorded 2026-10-09)

Three commissioned read-only inventories (verbatim under
`audits/retrofit-inventory/{primitives,loop,hardness}.md`; source-text
liveness — token matching, comments stripped, reachability from the public
declarations; deletion safety at integration is the compile sweep, since a
falsely-dead private fails loudly). Ground rules: the **strict-simplification
bar** (replace only where the citation is strictly simpler; non-canonical
seams are LEAVE), public surfaces byte-identical, the **`Universal*` cluster
excluded** (two-tape-universal pilot territory), and the **integration rule**:
retrofit output goes to a side branch and a PR into the campaign branch; the
user merges manually.

**What the inventories established.** The §12-shaped glue in the old files is
overwhelmingly **LEAVE** for structural reasons the agents verified against
the sources: the hosts are monolithic hand-built transition tables (R2
composes exactly two machines, has no back-edge, and cannot start inside a
phase); catalog rows are canonical-`Cfg.ofWords`-only; and R1 exports no
selected-tape facts (`embedSlot_selected`/`_unselected` are private) nor an
agreeing-host (`hagree`) lockstep. The realizable conservative scope is
dominated by **dead code** (76 privates, ≈1,505 lines — including
`emitterBank*`, the backlog's named R1 target, which was superseded rather
than consumed) plus a handful of clean replacements:

| Batch | File | Contents | Net impact |
|---|---|---|---|
| **RB1** (maintainer-serial proposed) | `Build/Loop.lean` | 8 dead privates (the standalone debit machine F4 + 2 orphans); H4's local `emit_run` re-derivation → the now-proved `Turing.emit_run` + `leftCfg_run`; the stale docstring sentence at 2205 | ≈ −200 lines |
| **RB2** (one external batch) | `Build/Primitives.lean` | 62 dead privates (the superseded emitter batch F24a–f + 3 split orphans); `emitterCompare*` → `compareTM` and `emitterP2Erase*` → `clearTM` (both seams verified canonical, glue itemized in the inventory); the two `Encoding.lean` duplicate swaps; the three stale comment blocks. **Optional stretch (D-R2(c))**: derive `splitSolve` from `splitSolveWith` + `polyBits` (−38 more privates, ≈ −909 lines, one new bound proof, no new import) | ≈ −1,520 lines (−2,430 with the stretch) |
| **RB3** (maintainer-serial proposed) | `CookLevin/Hardness.lean` | 6 dead privates; `clCompute_comp` → the public composition row; `clBuffer_append_bit` → `bufferTape_append`; `clA5_pt_unaryLength` → `clNative_fill true`; `clFresh*` → R2 (seams match `seamCompTM_run_ofCfg` exactly, no glue); the `clCount_width` docstring fix | ≈ −190 lines |

All three batches are file-disjoint and can run in parallel; each ships with
the full verification protocol (public-surface byte-identity, fresh sweeps,
axiom prints of the file's publics unchanged, lint) on its side branch.
Honest total: ≈ **−98 privates / −1,900 lines** — consistent with the
recorded expectation that the retrofit's payoff is hygiene and idiom, not
transformation; the five theorems of Hardness lose at most ~6% of their file
even in the best case.

**Decisions (user):**
- **D-R1 — R1 selected-tape exports.** All three inventories independently
  hit the same blocker: `Embed.lean` exports no selected-tape field lemmas
  and no agreeing-host lockstep. Adding them is additive Embed surface
  growth and unlocks ≈ −300–350 further lines in Hardness (families M/N/AM/U
  and the Z/AB/AG glue) and the strongest Loop/Primitives R1 candidates.
  **Proposed: fold into the §13 (Z1) statement phase** — same file family,
  same audit gate, one shared-file window instead of two.
- **D-R2 — Primitives ownership.** The inventory proved Catalog does *not*
  import Primitives: the catalog's rows rest on `f2_` copies of 150
  Primitives privates (147 byte-identical; correspondence mapped). Option
  (a) — import Catalog into Primitives (no cycle, verified) and project 11
  public rows from their twins — frees a further −100 privates/−2,370
  lines but inverts the layer's ownership; **proposed: defer (a) to the
  recorded 12.2c window** (feasibility now on record), take the (c) stretch
  inside RB2, and let 12.2c also consume the complete Loop↔Catalog
  correspondence map (95 privates, 92 byte-identical) the Loop inventory
  produced.
- **D-R3 — machine-agreement transfer lemma** (deferred candidate): Loop's
  largest duplication is internal (14 phase lemmas, ≈550 lines, re-proved
  verbatim for the forwarding host); an agreement-transfer lemma would
  collapse it and is the same `hagree` genre as D-R1. Weigh at the §13 spec
  phase; not part of this retrofit.

**D-R1 and D-R3 RESOLVED (user, 2026-10-09):** D-R1 — the R1 selected-tape
exports ride the §13 Z1 statement gate (additive `Embed.lean` growth,
recorded as the Z1 rider in `machine-library-design.md`); D-R3 — the
machine-agreement transfer lemma is **commissioned** as §13 item **Z5**
(the `hagree` lockstep made standalone; collapses Loop's ≈550-line
forwarding-host duplication and serves Hardness's 13 guarded agreement
sites; placement open decision 13.5).

**D-R2 RESOLVED (user, 2026-10-09):** conservative RB2 plus the stretch
(c) (`splitSolve` via `splitSolveWith` — a logical subsumption that
survives any layout); **no option (a)** (a half-measure 12.2c would
churn); and **12.2c is PROMOTED** from "queued indefinitely" to **the next
window after the RB batches land** — the per-theme split making each
implementation live once with both its time and space contracts,
`Primitives.lean` and `Catalog.lean` reduced to facades re-exporting the
frozen public names, consuming the recorded dedup maps (Primitives↔Catalog
150 twins, Loop↔Catalog 95, the Wrappers copies), dropping the dead twins
on both sides, and folding in the F2-audit dedup assignments and the
queued `redirectTM` projection. 12.2c runs with its own audit gate under
the new duplication governance. **Sequencing amendment (user, 2026-10-09):**
the two RB2 catalog replacements (F25a `emitterCompare*` → `compareTM`,
F27a `emitterP2Erase*` → `clearTM`) **move out of RB2 into the 12.2c
window** — they require the Catalog→Primitives import that 12.2c redesigns,
and doing them first would wire and then rewire it. RB2 is thereby purely
layout-independent (deletions, in-file swaps, the stretch), ≈ −1,260 lines
(−2,170 with the stretch); RB1/RB3 unchanged and churn-free against 12.2c
(RB1's edits survive any later layout verbatim; Hardness is untouched by
12.2c). Order confirmed: **RB1 ∥ RB2 ∥ RB3 → 12.2c** (dead code dies
before anything moves; the split runs on the shrunken files per its
recorded precondition; the structural change gets its own clean review).
Retrofit epoch **R1** = the three batches, briefs
`briefs/retrofit-rb{1,2,3}.md`.
| **§13 decisions 13.1-13.5 resolved; track A opens in two tranches** (user, 2026-10-09): zones-with-fullness; paired presence/data cells; new file renamed **`Codes2Tape.lean`**; Z1 mode shape inherits 12.4 (silent/emit pair over one core); Z5 in `Simulation.lean`. Statement phase split (`machine-library-design.md` §13a): **A-S1** = the virtual-input half (Z5 + Z1 + the Z1 rider — harvest-grade, near-term consumers: the blocked retrofit R1 families, 12.2c, Loop H3, EXPCOM) then its gate; **A-S2** = the zone half (Z2 + Z3 + Z4 — the carrier is the design risk and gets an undiluted gate; the Ex 4.1 bonus check discharges in its pack). Z1 canonical shape recorded: `1 + M.k` tapes (buffer first), relocation by R1 composition, never baked in. A-S1 spec layer is maintainer-serial, in progress | Decided |
| **A-S1 spec layer LANDED** (maintainer-serial, 2026-10-09): **Z5** — `MultiTapeTM.AgreeOn` + `step_eq_of_agreeOn`/`runFrom_eq_of_agreeOn` appended to `Simulation.lean` (2 sorried; the file crosses the 600/1000 policy line at 1,005 lines — **justification recorded here**: decision 13.5 fixed Z5's home beside the lockstep gadgets it generalizes, the growth is 57 additive lines, and any split belongs to the queued D7 window); **Z1 rider** — four selected-tape projections (`embedSilentCfg_selected_tape`/`_pos`, `embedEmitCfg_selected_tape`/`_pos`) added to `Embed.lean` as **skeleton-time proofs** (rfl-grade at the private `embedSlot_selected`; Embed stays zero-sorry; flagged for the A-S1 audit); **Z1** — new `Build/VirtualInput.lean` (323 lines): `vhostCfg` transport, `vhostEmitTM` (canonical `1+m` layout, tag in control, `q₀` tag `true`), and **`vhostSilentTM` defined as the layer composing with itself** (`embedSilentTM` of `vhostEmitTM` at `castAddEmb` with one appended capture tape — no third lockstep), plus 9 sorried contracts with sketches naming `bufferedSecondCfg_step`/`_run` as the fill template: step/run lockstep (no liveness/nonemptiness premises), bank visited **equality**, buffer-trajectory equality, the clamp-interval and emitting-halt **permanent regression lemmas** (F2-audit-adopted), and the coefficient-one space ledgers for both flavors. Elaboration: all three modules exit 0, exactly 11 sorries (9+2), lint 0 FAIL. The A-S1 statement-gate pack follows | Recorded |
| **A-S1 statement gate CLOSED** (round 1, 2026-10-09: **PASS, 0 blockers / 0 majors / 2 minors** — `audits/vhost-infra-findings.md` verbatim; loop summary `audits/vhost-infra-resolutions.md`). All eight definitions and four riders blind-restated with no daylight; the silent-composition layout arithmetic verified (unselected = exactly the capture tape, ambient parameters inert, `m = 0` included); all eleven sorried contracts argued true as literally stated — **the auditor's per-statement arguments are adopted as the binding fill routes**; sixteen adversarial families + ~10,700 finite model checks; failure-mode-5 debt screen clean ("new copies: none"). Minors swept: A-S1-1 pack erratum acknowledged (eight definitions, not seven); A-S1-2 design-doc note §13b (the rider's `ofWords` form is supplied by specialization; named form on need at 12.2c). The audit's four recommended sanity exports adopted as **optional permanent lemmas** of the fill; its Z5 composition-of-responsibilities reading (transport first, then agree) is binding on retrofit consumers. **Fill brief `briefs/vhost-f1.md` issued** (one batch, both files, 11 targets) | Recorded |
| **Retrofit epoch R1: RB2 MERGED (PR #9, user), RB1 integrated awaiting merge (PR #10)** (2026-10-09). RB2: 62/62 dead privates deleted (−1,222 lines), both Encoding swaps (one via the maintainer's flagged E1-resolution commit `7224d118`, **approved by the user's merge** — the escalated `catalogPair_inverse` use sat in `computesFunInTime_stripLast`'s public proof body, an **inventory erratum**: the "two strict Encoding swaps" row missed that public-body use), three authorized comment blocks rewritten, stretch not attempted; `Primitives.lean` 7,636 → 6,374 lines, 318 → 254 privates; freeze verified decl-level (18/18 publics byte-identical), 18/18 independent axiom prints clean, lint 0 FAIL, ledger "new copies: none" (logs `audits/logs/retrofit-rb2-*`). RB1 (side branch `retrofit/rb1`, PR #10, mergeable): 8/8 dead privates deleted + the H4 `emit_run` citation per the glue plan (`emLoopForwardCfg` def sensibly retained — frame proofs consume it); `Loop.lean` 5,713 → 5,515 (−198), 214 → 204 privates; publics byte-identical, replay Loop+Catalog+facade clean, 8/8 axiom prints baseline-identical, no shim in this delivery, ledger clean (logs `audits/logs/retrofit-rb1-*`). RB3 zip pending | Recorded |
| **A-S2 spec layer LANDED** (maintainer-serial, 2026-10-09): **Z2** — new `Build/Zone.lean` (455 lines, 28 publics): the paired-cell codec (13.2), the layout arithmetic (`zoneCapacity i = 2·2^i`, `zoneBase i = 2·(2^i−1)`, `zoneIndex` by `Nat.log2`), the `ZoneContents` carrier with **fullness deliberately excluded** (the H-S invariant is the consumer's), `zoneTape` physical realization (home at 0/1, the left/right presence-data asymmetry fixed and documented), **pairwise order-preserving shifts** (spec-time refinement: level-`i` in/out move `2^(i−1)` cells between zones `i−1` and `i` only — the honesty lemmas `zoneSide_shiftInW/OutW` make representation-preservation structural and the classical cascade stays mathematics-on-top), pure head-step/home-write ops, two machine rows (`exists_zoneShift{In,Out}TM`: one two-tape machine per direction+side, **level in unary on the scratch tape** — a single H-S simulator cannot bake levels into control — exact `c·(2^i+i+1)` budgets, visited-interval and scratch-space clauses), and the cardinality exports (`zoneTape_blank_outside`, `spaceUsedByTape_le_card_Icc`) that Z4 consumes. **Z3** — new `Codes2Tape.lean` (199 lines): `Code2TM`/`serialize` over the same `actionBits₂` record (27 records per state, no choice bit), `MachineCode2`/`EffectiveMachineCode2`/`UniformMachineCode2` mirroring the received schemes incl. the P3.2 uniform-simulator clause, 2 sorried existence statements. **Z4** — 3 sorried space-annotation statements appended to `Robustness/{AlphabetReduction,SingleTape}.lean` via the shared-file mechanism (flagged): `alphabet_reduction_spaceUsed`, `one_work_tape_spaceUsed`, `one_work_tape_binary_spaceUsed` — the §2.7 Ex 4.1 fallback in deliverable shape (`space ≤ c·(S+1)`, all-time). **`SingleTape.lean` crosses the size line at 1,029 — justification recorded here**: 48 additive Z4 lines under the shared-file mechanism; any split belongs to the D7 window. Elaboration: Zone, Codes2Tape, both Robustness files, and the facade all exit 0; the tranche adds exactly 21 sorry warnings over 18 sorried declarations (13+2+3, incl. Zone's three defs with sorried capacity fields); lint 0 FAIL both dirs. The A-S2 statement-gate pack follows | Recorded |
| **Retrofit epoch R1 integrations COMPLETE; both gate packs issued** (2026-10-09): PR #10 (RB1 + RB3) merged by the user at 20:22Z — the epoch's net effect is **−1,639 lines / −85 privates** (Loop 5,515; Primitives 6,374; Hardness 8,725), `Hardness` the first §12 consumer outside `Build/`, and the E1 human-approval loop exercised end to end (escalation → flagged commit → user merge). **Two packs out**: `audits/retrofit-r1-{pack,bundle}.md` (the epoch-boundary audit — freezes from patches, deletions-as-dead, the three citations as strict simplifications, the E1 governance trail, the cumulative duplication ledger; 20 attachments, sha `3d0a0f74…`) and `audits/zone-infra-{pack,bundle}.md` (the **A-S2 statement gate** — Z2's layout arithmetic and pairwise-shift design flagged as the campaign's highest-risk spec, Z3's 27-record fidelity, Z4's fallback shapes, and the **Ex 4.1 design-time obligation DISCHARGED in the pack**: two-tape-universal route preferred, Z4 retained as the audited fallback, stage-1 design selects; 13 attachments, sha `58e86447…`). Close of either gate follows the standard loop | Recorded |
| **vhost-f1 integrated — tranche A-S1 fully proved, 11/11** (2026-10-09): one-batch fill delivered complete at base `44d25413`, integrated `git am -3` (`4ae4e9b2`, Codex authorship). `Build/VirtualInput.lean` and the Z5 statements of `Simulation.lean` are **zero-sorry**; exactly one new private (`vhostSilent_layout`, the capture-disjointness layout arithmetic the gate audit pre-verified); optional exports and shared-lemma requests: none; **duplication ledger: new copies none** (the host proofs adapt and cite the `bufferedSecondCfg` template — technique notes recorded in the report: `virtualMove_correct` consumed at `c.mapState (fun _ => ())` to bridge `Type*`/`Type` without a duplicate input lemma; the buffer/bank sum split via `Fin.addCases` + `Finset.sum_bij`/`sum_erase_add` within the frozen import surface). Maintainer verification: checksums clean; patch removals exactly the 11 `sorry` bodies; delivered sources byte-identical; replay of the five prescribed modules 0 errors / 0 sorries; **11/11 independent axiom prints** within the standard triple (the two Z5 transfers at `[propext, Quot.sound]`), no `sorryAx`; lint 0 FAIL (logs `audits/logs/vhost-f1-*`). The stale `VirtualInput` status header refreshed post-fill (maintainer, doc-only — the inventories' stale-header lesson applied same-day). The A-S1 fill-gate pack follows | Recorded |
| **A-S2 round 1 FAILED; repairs landed** (2026-10-09: **1 blocker / 1 major / 2 minors** — `audits/zone-infra-findings.md` verbatim). **A-S2-1 (blocker, maintainer-introduced)**: one shared `hroom` premise sat on both shift directions, making a full donor illegal inward — the exact classical case; the auditor's full-chain family forced `Ω(T²)` through the delivered interface, **and the auditor supplied the repair plus its correctness analysis** (the descending/move/ascending cascade with the charge bound). Repaired in `Build/Zone.lean`: no inward room premise; the outward room moved inside the guard; hypothesis-free wrappers `zoneShiftIn`/`zoneShiftOut` (the old `zoneShift` removed); guarded-total `zoneMove`; rows realize the total guarded op, identity branch included; **the required gate material added** — `zoneShiftInW_full_donor`, `zoneCascadeRight` + `zoneSide_cascadeRight` + `zoneCascadeRight_lengths` + `zoneCascade_cost_le` (over `Finset.range`; the audit's schedule analysis is the binding route). Zone.lean now 588 lines, 22 sorry warnings, exit 0. **A-S2-2 (major)**: the Z4 sketch falsely credited the received `sweepTM` (unconditional window growth; refuted by the stationary-head scanner) — sketch replaced with the demand-grown witness route incl. the all-`Γ'` retraction; statements unchanged. **A-S2-5 adopted**: the Ex 4.1 assessment downgraded to design-level in §13c (a materialized input copy costs `Ω(|x|)`; stage 1 must specify a space-accounted input interface). Minors acknowledged (22 defs not 25; export-list/guard-semantics docstrings fixed). **Round-2 pack follows** | Recorded |
| **Retrofit-R1 round 1: gate OPEN; repairs landed** (2026-10-09: **0 blockers / 2 majors / 2 minors / 8 notes** — `audits/retrofit-r1-findings.md` verbatim; no code defect found — both majors are evidence-packaging gaps). **R1-1**: the pack attached no complete sources, so reconstruction/rehash and the E1 statement comparison were impossible — round-2 pack attaches the three complete final sources + `Encoding.lean`. **R1-2**: the governance's *cumulative* ledger was not supplied in totals-and-fractions form — created as the standing `audits/duplication-ledger.md` (convention + per-file rows; headline: Catalog is **59% copied material by declarations**, acknowledged and scheduled under D-R2/D-R3; epoch delta: 0 new copies, 233 remaining original-side twins, one pair collapsed by E1). **Errata (R1-3/R1-4, acknowledged)**: the epoch removed **−83** privates (76 dead + 7 replaced), not 85, and `catalogPair_length` was double-listed; Loop has **8** publics; the earlier "18/18 publics byte-identical" row is qualified — all 31 signatures/statements/docstrings unchanged, 30/31 complete bodies unchanged, the one authorized E1 substitution. Round-2 pack follows | Recorded |

**Duplication-governance amendments landed (user-directed, 2026-10-09; from
the D-R2 post-mortem — the `f2_` accumulation was disclosed and recorded at
every step but never escalated to a human decision):** `audits/TEMPLATE.md`
failure mode 5 (**debt**, reported at major; gates cannot close over it
without explicit human acknowledgment; screened cumulatively);
`workflow.md` §4 duplication ledger at maintainer verification (hard
escalation threshold: one-fifth copied material, or repeat copies across
epochs, auto-opens a backlog §1 item) and in every epoch pack, auditor-
verified; `policy.md` **Duplication.** paragraph — forced or deliberate,
duplication of proved material is always disclosed, always ledgered,
**always human-approved**; undisclosed duplication is a freeze violation.
Campaign branch `2f61ef88`; **merged to `main` via PR #8** (single
cherry-picked commit, the PR #6/#7 precedent); all three files verified
byte-identical on both branches. Noted in passing: `main` has moved
substantially (colleague activity in `BooleanAnalysis/`) — relevant to the
pending colleague sync.

**Logged housekeeping (maintainer, not retrofit output):** stale "statement
skeleton / sorried" module headers in `Embed`/`Seam`/`Catalog` (all
zero-sorry since today); two library-docstring overclaims (Embed's R1 "is
the generic form of `clBank*`" — `clBankTM` is a simultaneous product, not
a relocation; Catalog's copy/compare row provenance wording vs
`clCopyTM`/`clCmpTM`'s actual semantics); bookkeeping corrections — the
generated-kernel-artifact count is 12 (in `Nondeterminism`/`EXP`/`SAT`, none
in Hardness), Hardness holds 553 privates (618 at A5 close − 65 at E5), and
two kernel-dead names (`clRefClockCfg`, `clReadFields`) are missing from the
E5 record.

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
| **Two statement-gate packs out in parallel** (2026-10-08): `audits/routine-infra-{pack,bundle}.md` (the §12 layer: 47 statements; bundle sha256 `e9216b8b…`, 14 attachments incl. the byte-identical `Build/` context) and `audits/ch3-p32-{pack,bundle}.md` (P3.2: 17 statements; bundle sha256 `dbfadcfb…`, 22 attachments incl. the unaudited P3.1 surface with the layering caveat declared, [BGS75] scanned-original link supplied). Fresh per-pack sweeps with revisions recorded at start (0 errors; 47 and 17 sorry warnings exactly); both gates close on zero blockers/majors. Disjoint audit surfaces — concurrent repairs cannot collide with each other or with the P0/R2 surface | Recorded |
| **P0 reception gate CLOSED** (round 2, 2026-10-08, `audits/ch34-p0-r2-findings.md`: **PASS, 0 blockers / 0 majors / 3 minors**; loop summary `audits/ch34-p0-resolutions.md`). The repair diff was reconstructed hash-exactly by the auditor; all ten S-statements independently derived true as stated; S9 admits the tighter `t·(2B+3)` (recorded for fill, statement unchanged). The three minors swept in the closing commit and re-verified: the `Reaches.toB` reference corrected (finding 6 residual), "machine-checked" wording honestied to "elaborated, proofs deferred" (finding 11), and the two timed zero-tape witness statements added to `ZeroSpace.lean` (finding 12; now 11 sorried there). Two pack errata acknowledged in the resolutions. The received 44-module surface is adopted; the P3.1 and P4.1 statement gates are unblocked | Recorded |
| **P3.1 and P4.1 statement-gate packs out** (2026-10-08, unblocked by the P0 closure): `audits/ch3-p31-{pack,bundle}.md` (10 statements + declared skeleton-time proofs; bundle sha256 `37d2fd94…`, 19 attachments; concurrent-P3.2 cross-filing note) and `audits/ch4-p41-{pack,bundle}.md` (14 statements; bundle sha256 `58bdb768…`, 22 attachments; sits on the P0-closed surface, inherits and declares the zero-bound collapse for `NSPACE`, seeds the `NSPACE` sanity-twin question and the `evenLang` zero-tape harmonization). Fresh per-pack sweeps with revisions at start: 0 errors, exactly 10 and 14 sorry warnings. **All four early statement phases are now under concurrent external audit** on pairwise-disjoint surfaces | Recorded |
| **P4.2 statement skeleton landed** (2026-10-08, maintainer-drafted): `SpaceComplexity/ConfigGraph.lean` (the vertex = core **plus a three-valued output summary** — the P0 fitness note's acceptance gap closed by design; `CfgStep`/reachability dictionary; ND Claim 4.4(1) in acceptance form; the packaged `DecidesInSpace` iff; Thm 4.2(iii) with the `2^(c·(S n + 1))` union rendering; `NL ⊆ P`; Ex 4.3 as nontrivial-NL-hardness, with the exercise's moral in the docstring) and `SpaceComplexity/Savitch.lean` (`spaceConstructible_poly` at degree ≥ 1 — degree 0 provably fails the bundled `logSpace ≤ S`; Savitch via the iterative frame stack, a §12 R1/R2 consumer; `PSPACE = NPSPACE`). 10 sorried statements, zero errors, lint 0 FAIL. **The P4.1-frozen facade is untouched**: both modules wired through the root import only, facade wiring deferred to the P4.1 gate close. Layering: builds on P4.1 (under audit) + P0-closed surface; its gate pack follows the P3.2-over-P3.1 declared-caveat pattern, after the P4.1 round returns | Recorded |
| **P4.3 statement skeleton landed** (2026-10-08, maintainer-drafted): `Formulas/{QBF,QBFEncoding}.lean` (prenex QBF with CNF matrix per CH34-Q5; free-variables-read-false totalization; true-fallback decode matching the `SAT` polarity; the Example-4.12 `SAT` embedding), `ClassPSPACE/{TQBF,Games}.lean` + facade (Def 4.9 over `≤ₚ`; the collapse corollary; **Claim 4.4(2) existentially packaged with two declared deviations** — `O(s+n)` one-hot-input codec for locality, polynomial rather than linear CNF size, both harmless to Thm 4.13; `TQBF` + both halves of Thm 4.13, hardness = the `ψᵢ`-emitter summit; Zermelo determinacy), `SpaceComplexity/Hierarchy.lean` (the space-universal machine with the `+ logSpace` clock addend declared against Ex 4.1's literal `Ct`; Thm 4.8 at **constant-factor** hypothesis strength — no square, no log, the space story's advantage over the received `f²` time hierarchy; `L ⊊ PSPACE`; Ex 3.2 at the `n+1` normalization with the `NP` `≤ₚ`-closure named as a derived obligation). 12 sorried statements, zero errors, lint 0 FAIL. Facade wiring: new `ClassPSPACE` facade + `Formulas` facade extended (closed-campaign, not frozen); `Hierarchy` root-wired since the `SpaceComplexity` facade stays P4.1-frozen. Its gate pack follows the layered-caveat pattern once P4.1/P4.2 rounds allow | Recorded |
| **P4.4 statement skeleton landed** (2026-10-08, maintainer-drafted) — **the chapter-4 statement program is complete**: `SpaceComplexity/Logspace/{Reductions,Path,ImmermanSzelepcsenyi,Mult}.lean`, 11 sorried statements. `≤ₗ` over the received implicit-logspace layer; **general Lemma 4.17 now stated** (`ImplicitlyLogspaceComputable.comp` — the composition the P0 round recorded as undelivered), with transitivity, the `L`-downward closure, the `≤ₚ` refinement, and the `NL = L` collapse corollary; the campaign's first graph encoding (`encodePATH`, EXPCOM-pattern existential membership) with `GraphReach` **in-house** (deviation from plan §2.6's `Digraph.Reachable` target: the GraphTheory tree carries admissions outside the audited closure; bridging lemma recorded as future work); `PATH ∈ NL` and Thm 4.18 (hardness via the P4.2 vertex layer, the accepting normalization discharging the P0 unique-terminal caveat; the reduction's bit queries assembled by the received `arm_decides`); Thm 4.20 both as `PATHᶜ ∈ NL` and `NL = coNL`, with **no read-once certificate model** — the binary-choice NDTM's choice words are natively read-once, a declared simplification; Cor 4.21 over the P4.2 configuration-graph layer; `MULT ∈ L` closing Ex 4.7. The nondeterministic ARM extension gains its first two named customers (the `PATH` walk, the counting verifier). Zero errors; lint 0 FAIL; root-wired (facade stays P4.1-frozen) | Recorded |
| **P3.1 gate CLOSED** (round 1, 2026-10-08: **PASS, 0 blockers / 0 majors / 2 minors / 4 notes** — `audits/ch3-p31-findings.md` verbatim, loop summary `audits/ch3-p31-resolutions.md`). Minors swept in the closing commit: the Theorem-2.6 docstring equation regains its load-bearing `+1` (auditor-refuted, maintainer-verified against `NP_eq_iUnion_NTIME`), and the Ex 3.6(2) sketch carries the explicit query ledger at degree `k·(1+max 1 e)` with the extracted-prefix-only virtual-input obligation. The fixed-oracle clock split is confirmed sound, with the timeout-wrapper reconciliation carried to the P3.2 gate. Natural-home promotions stay deferred until P3.2 closes | Recorded |
| **P4.1 gate CLOSED** (round 1, 2026-10-08: **PASS, 0 blockers / 0 majors / 5 minors / 4 notes** — `audits/ch4-p41-findings.md` verbatim, loop summary `audits/ch4-p41-resolutions.md`). Minors swept: both constructibility sketches corrected at `n = 0` (bits-length identity; counter initialized at `1`), the exact-space refutation claim retracted (time's argument does not transfer), the `evenLang` route kept direct (the pack's harmonization suggestion was cycle-inducing — pack erratum acknowledged, with the inventory undercount), SAT3 at delivered polynomial strength. Carried obligations: `NSPACE` sanity twins as a future additive layer; the short-prefix argument into the invariance fill; `NP ⊆ PSPACE`'s five host obligations and its hard §12 R1/R2/R3 dependency into the fill brief. **The `SpaceComplexity` facade is unfrozen and now carries the P4.2-P4.4 modules**; the P4.2 pack is unblocked | Recorded |
| **P4.3 landing erratum repaired** (2026-10-08): the `Formulas.lean` facade extension of 572304e5 appended its two QBF imports **after** the module docstring — invalid Lean. The landing sweep did not include the facade module, so the error went undetected, and the facade's sole dependent (the root `TCSlib.lean`) elaborated against the stale pre-P4.3 olean. Repaired in place (imports moved into the header block, `## Contents` rows added for `QBF`/`QBFEncoding`); the facade re-elaborates fresh, 0 errors (the root itself stays outside the campaign sweep surface — it imports non-campaign trees with no scratch oleans — so its exposure was import-order only). Sweep-hygiene consequence adopted: every gate sweep lists the touched facades explicitly | Recorded |
| **Three statement-gate packs out in parallel** (2026-10-08): `audits/ch4-p42-{pack,bundle}.md` (P4.2: 10 statements; bundle sha256 `5139d5ae…`, 24 attachments), `audits/ch4-p43-{pack,bundle}.md` (P4.3: 12 statements; bundle sha256 `5a52f398…`, 30 attachments, P4.2-unaudited layering caveat declared), `audits/ch4-p44-{pack,bundle}.md` (P4.4: 11 statements; bundle sha256 `899d3c43…`, 24 attachments, same caveat). All three audited at `200f4693`; fresh per-pack sweeps with revisions recorded at start (0 errors; 10/12/11 sorry warnings exactly); style lint re-scoped after assembly review caught the single-directory linter CLI (SpaceComplexity 42 + Formulas 5 + ClassPSPACE 2 files, 0 FAIL / 0 WARN). Review repairs applied before shipping (the P3.2 pattern, each disclosed in its pack): the QBF sketch's `eval_congr_of_lt_numVars` namespace (`0a1982a0`); `PSPACE_eq_NPSPACE`'s degree-0 routing off bare `NSPACE.mono` (fails pointwise at `n = 0`) and the splice-padding clause in `acceptsWithin_of_spaceUsedWith_le` (`200f4693`). Attachment manifests extended per the P4.1 erratum lesson (TEMPLATE, closed resolutions, `NTIME.lean`; P0 findings where quoted). Disjoint audit surfaces; **five rounds now live** (§12, P3.2, P4.2, P4.3, P4.4) — the chapter-3/4 statement program has every drafted phase under external audit | Recorded |
| **P3.3 statement skeleton landed** (2026-10-08, maintainer-drafted): `TuringMachine/NDCodes.lean` (the two-work-tape coded normal form `CodeNDTM` — two tapes because the [BGW70]-style guess-then-verify reduction is linear into two, not one — with `actionBits₂` serialization mirroring `CodeTM.serialize` record for record, the `NDMachineCode`/`EffectiveNDMachineCode` scheme laws, the skeleton-time `decode_encode` mirror, and the sorried scheme existence; 1 sorried) and `Diagonalization/NTimeHierarchy.lean` (the clocked universal NDTM at **linear overhead** per CH34-Q8 — iff-packaged with an unconditional fused clock, the book's timeout-accept polarity declared absorbed; the exponential deterministic acceptance evaluator; the linear coded-normal-form transfer with deliberately unbounded backward direction + the truncation note; **Thm 3.2 at book strength** with the extra `f n` domination addend declared (covers the inclusion half without monotonicity); the positive-bound form; the showcase `NTIME(n+1) ⊊ NTIME((n+1)²)` with the squared-overhead impossibility note; 6 sorried). 7 sorried total, 0 errors, lint 0 FAIL (Diagonalization 0 WARN; TuringMachine only the pre-existing size WARNs). **Root-wired**: the `Diagonalization.lean` facade is frozen under the live P3.2 gate and `TuringMachine.lean` is untouched — facade wiring at the respective closes (the P4.2 precedent). Gate pack after the relevant rounds return | Recorded |
| **P3.4 (Ladner) moved to backlog** (user, 2026-10-08): per CH34-Q6 core-late — `backlog.md` §2 entry with scope (`SAT_H`, Ex 3.6(a)/(b), the Claim, Thm 3.3, ~6 statements) and the trigger (draft when the live rounds settle; independent of P3.3's code layer). With P3.3 drafted, **every core phase of the chapter-3/4 statement program is drafted**; P3.4 is the sole remaining statement phase | Recorded |
| **P4.2 gate CLOSED** (round 1, 2026-10-08: **PASS, 0 blockers / 0 majors / 5 minors / 3 notes** — `audits/ch4-p42-findings.md` verbatim, loop summary `audits/ch4-p42-resolutions.md`). Minors swept: the splice sketch's sibling-halting assertion dropped (the statement has no such hypothesis — the accepting branch alone pads, auditor counterexample confirmed), Exercise 4.3's printed "complete" recorded as a **textbook erratum** (hardness only; completeness needs `L ∈ NL`), the received count cited as `Turing.FinTM.configBound`, `LOGSPACE_subset_P` described as count-arithmetic precedent rather than "the same search", the `+ 1` described as normalization (the `c = 0` exponent is `0`). Carried: the carrier-bridge obligations (quotient lifting, outside-window rejection, reflexive base), the resource ledgers (constructor time through the received count theorem, fixed-interval frame reuse, exact `(n^c+1).bits` output), and the pack's question-3 sibling erratum acknowledged | Recorded |
| **P4.4 gate CLOSED** (round 1, 2026-10-08: **PASS, 0 blockers / 0 majors / 2 minors / 5 notes** — `audits/ch4-p44-findings.md` verbatim, loop summary `audits/ch4-p44-resolutions.md`). Minors swept, both in `mem_LOGSPACE_of_logspaceReducible`'s sketch: the characteristic function's length language is **exactly** `{pairEncode x []}` (regular, not total), and the index-`0` step is a **paired-input** specialization on `dbl x ++ [false, true]`, proved directly (no circularity). Note-4 accuracy edit: the P0 unique-terminal caveat is *assigned* to `PATH_NLComplete`'s fill, not already closed (`cleanTM` does not reset the input head). Carried: the `comp` query ledger, the counting-verifier disciplines (ascending order, exact counts, direction-sensitive negative test), `mem_NL_of_logspaceReducible` as a future additive statement | Recorded |
| **P4.3 round 1: FAIL — gate open** (2026-10-08: **1 blocker / 4 majors / 4 minors / 3 notes** — `audits/ch4-p43-findings.md` verbatim). The blocker: `exists_adjacency_codec_cnf` was **false as stated** — fixed-length injective codes on *full* configurations are impossible, the output tape being unbounded (the auditor's pigeonhole at `n = s = 0`). **Repairs landed same day**: the codec restated over the quotient carrier (input + `Turing.NDTM.coreSum`) with the new `Turing.Cfg.InWindow`, in-package validity/adjacency/acceptance CNFs (the junk-midpoint guard), serialized-length size bounds (the empty-clause gap), and cross-input rejection; the hardness sketch rebuilt (`Valid`-guarded ψ with the `a = b ∨ Next` base, Tseitin-after-prefix, the **uniform emitter declared a private fill obligation** — the existential is not an algorithm); `space_universal`'s sketch now tests visited-interval **cardinality** with probe-then-replay output; `space_hierarchy`'s sketch now uses the **capped increasing-budget loop** with one fixed padded code and names the space-preserving normal form; membership validates the whole encoding before any verdict; `Games.determined`'s value fixed to the player-one perspective; the padding sketch concretized. Re-audit round per `workflow.md` §3; pack `audits/ch4-p43-r2-pack.md` | Recorded |
| **P4.3 round-2 pack out** (2026-10-08): `audits/ch4-p43-r2-{pack,bundle}.md` — re-audit of the round-1 repairs at `aa02db41`, per-finding disposition table, the complete repair diff attached (`audits/evidence/ch4-p43-r2-repairs.diff`: one statement restated, one definition added, six sketches + one docstring bullet rewritten; every other declaration byte-identical). Bundle sha256 `beb69f18…`, 32 attachments (round-1 findings verbatim, the closed P4.2 resolutions as the updated layering context, fresh r2 sweep 12/0 and lint 0 FAIL over 5+2+42 files). Gate closes on zero blockers/majors | Recorded |
| **P3.3 statement-gate pack out** (2026-10-08): `audits/ch3-p33-{pack,bundle}.md` — 7 statements (NDCodes 1, NTimeHierarchy 6), 7 definitions, one declared skeleton-time proof (`NDMachineCode.decode_encode`, mirror of proved infrastructure). Audited at `a664c3e4`, files byte-identical to landing `72718693`; fresh sweep 7/0, lint 0 FAIL (Diagonalization 0 WARN over 4 files; TuringMachine the 8 pre-existing size WARNs over 39). **Closed-surfaces-only layering** — no sorried concurrent statement is consumed; §12 cited as fill engine only; root-wired (Diagonalization facade frozen under live P3.2, TuringMachine facade untouched). Ten declared deviations incl. the two-work-tape normal form, the iff-packaged unconditional clock, the fused linear clock vs `timed_universal`'s `C·(t+1)²`, the unbounded backward transfer, the `f n` domination addend, and the no-`|x|` budgets. Bundle sha256 `45339e25…`, 23 attachments (incl. `Universal.lean` and `MathlibBridge.lean` as mirror/contrast context, per the P4.1 erratum lesson). Gate closes on zero blockers/majors | Recorded |
| **Four rounds returned, all FAIL** (2026-10-08/09, findings verbatim in `audits/{routine-infra,ch3-p32,ch4-p43-r2,ch3-p33}-findings.md`): **§12** 0 blockers / 4 majors (R1 the closed embeddings cannot express the halt-to-live return — the final emission is lost either way, formal trace supplied; R2 seam composition exports canonical-endpoint theorems only, cannot consume arbitrary frames or output-carrying seams; R3 the first-return cut excludes positive entry-equals-exit calls — a fresh-entry/release adapter is needed; R4 `pairMapSnd`'s documented witness is refuted — the capture tape visits output-length cells, a forwarding controller is commissioned); **P3.2** 1 blocker (`EXPCOM` over the arbitrary `TimeHierarchy.code`: `EffectiveMachineCode` bounds no decoding time, and a tagged scheme embeds an arbitrarily hard decidable language into decoding — statements 9-12 unprovable as stated; the locality layer, stage construction, and the BGS existential all survive); **P4.3 r2** 1 blocker (the serialized-size bound `C·(s+n+1)^C` is self-contradictory at `n = s = 0`: the code width equals `C` while one literal reading the second block already serializes to `C + 6`; all four round-1 majors otherwise resolved); **P3.3** 0 blockers / 2 majors (both in `ntime_hierarchy`'s sketch: the per-code universal constant cannot be absorbed by padded-index choice — padding preserves `decode` but no law preserves cost — and the ladder locator as sketched is not computable within the allowance). No headline theorem refuted anywhere; every verdict names its repair route. Repairs follow per phase | Recorded |
| **Four repair batches landed and four re-audit packs out** (2026-10-09, audited at `9a92fa1a`): **§12 r2** — the returning embeddings `embedSilentRetTM`/`embedEmitRetTM` (halt-to-live through-halt contracts), the general-configuration seam theorems (`seamCompTM_run_ofCfg` + first-return + visited), the `seamReleaseTM` fresh-entry adapter, the forwarding `pairMapSnd` controller, three minor sketch repairs; 47 → **56 sorried** (`audits/routine-infra-r2-{pack,bundle}.md`, sha256 `fc7afcb8…`, 20 attachments); `Build/Catalog.lean` crosses 1000 lines — justified by the queued per-theme split (backlog §2, decision 12.2c). **P3.2 r2** — `Turing.UniformMachineCode` (bounded-acceptance simulator at one polynomial in code+input+deadline jointly), sorried existence, `EXPCOM` redefined over the chosen scheme (choice-over-sorried-existence declared); 17 → **18 sorried** (`audits/ch3-p32-r2-{pack,bundle}.md`, sha256 `9de1defa…`, 24 attachments, `Universal`/`MathlibBridge`/`CodeParser` attached per the round-1 request). **P4.3 r3** — serialized-size bounds to base `s+n+2`, the quotient clause an iff, five wordings; r2-pack "equal codes required" erratum acknowledged (`audits/ch4-p43-r3-{pack,bundle}.md`, sha256 `6a04a9cc…`, 33 attachments). **P3.3 r2** — the hierarchy sketch rebuilt (fixed-code schedule `pair(j,r)`, `f`-adaptive tower ladder with capped-comparison locating, self-clocked interpreter at uniform `K·(g n + 1)`, both transfer instantiations), six sketch corrections; round-1 pack's `g 0 = 0` claim acknowledged as erratum (`audits/ch3-p33-r2-{pack,bundle}.md`, sha256 `fedeadf8…`, 25 attachments). Fresh sweeps 56/18/12/7 with 0 errors at `9a92fa1a`; combined lint 0 FAIL. Four rounds live again | Recorded |
| **P4.3 gate CLOSED** (round 3, 2026-10-09: **PASS, 0 blockers / 0 majors / 0 minors / 2 notes** — `audits/ch4-p43-r3-findings.md` verbatim; loop summary `audits/ch4-p43-resolutions.md`, the campaign's first three-round statement loop). The amended `s+n+2` base verified with one shared constant uniformly; the factorization iff and all five wordings accepted; no sweeps. Carried: the uniform-emitter family and the quotient path lift as private hardness-fill obligations; the probe-then-replay universal and capped increasing-budget hierarchy disciplines. **Chapter 4 fully closed at the statement level** | Recorded |
| **§12 round 2: FAIL — repaired, round-3 pack out** (2026-10-09: **1 blocker / 0 majors / 0 minors / 1 note** — `audits/routine-infra-r2-findings.md` verbatim; the seven other new contracts and all round-1 dispositions accepted, S7/S8/S9 replayed successfully). The blocker: both through-halt contracts were false at `T = 0` for an initially halted configuration (the handover projection demands `none = some (Sum.inr ())`). Repair at `2b82cbb3`: `(hc : c.state ≠ none)` on both — equivalent to `0 < T` under the first-halt hypothesis — with the counterexample recorded in the docstring. The round-2 pack's 6+3 inventory subdivision acknowledged as an erratum (5 run/first-return + 4 visited-set). Round-3 pack `audits/routine-infra-r3-{pack,bundle}.md` (bundle sha256 `bb651440…`, 21 attachments, the 38-line diff attached); fresh sweep 56/0, lint 0 FAIL. **The §12 round is the campaign's last open statement gate** | Recorded |
| **§12 gate CLOSED** (round 3, 2026-10-09: **PASS, 0 blockers / 0 majors / 1 minor / 0 notes** — `audits/routine-infra-r3-findings.md` verbatim; loop summary `audits/routine-infra-resolutions.md`, a three-round loop). The round-2 counterexample verified excluded, the full positive-time through-halt induction supplied, consumers discharge `hc` at every live seam, byte-identity confirmed to blob hashes. Minor swept: the `hc ↔ 0 < T` equivalence stated under **both** first-halt hypotheses (forward `hhalt`, reverse `hlive 0`); two pack errata acknowledged in the resolutions. **Facade wiring**: `Build/{Embed,Seam,Catalog}.lean` join `TuringMachine.lean`, root temporary imports removed. **EVERY STATEMENT GATE OF THE CAMPAIGN IS NOW CLOSED** (P0, P3.1-P3.3, P4.1-P4.4, §12); remaining statement work: P3.4 (Ladner, backlog); next: fill epochs | Recorded |
| **Post-statement-program roadmap and §12 fill partition recorded** (user-directed, 2026-10-09): new plan sections **§4b** (the six remaining stages: fill prerequisites — §12 fill, ARM extensions with the colleague sync, Hennie-Stearns + two-tape universal; the fill epochs on the §6 summit order; P3.4 on hold; the ch1-2 retrofit alongside; closure; one PR per chapter) and **§4c** (the routine-layer fill partition: **epoch F1**, 3 parallel disjoint-file batches — F1A Embed 13, F1B Seam 11 general-trio-first, F1C Catalog Part 1 + W1/W2 13 — then **epoch F2**, F2A the 19 Part-2 space rows risk-ordered with the `pairMapSnd` forwarding controller as summit; audit at each epoch boundary; briefs embed the audit-inherited proof plans verbatim). P3.4 explicitly held (user, 2026-10-09) | Recorded |
| **Epoch-F1 briefs issued** (2026-10-09): `briefs/routine-f1-batch{A,B,C}.md` per the §4c partition — A: `Build/Embed.lean`, 13 targets, the round-3 through-halt induction embedded verbatim as the binding plan; B: `Build/Seam.lean`, 11 targets, general-configuration trio first with the round-2 lockstep identities and the `ofWords`/`mapState` substitution embedded; C: `Build/Catalog.lean` Part 1 + W1/W2, 13 targets, the round-1 exact movement-count table embedded with the slack/trajectory clarifications, the 19 epoch-F2 rows explicitly frozen-in-place (final sweep must show exactly 19 sorry warnings). All three: hardened repo/branch headers (issued at `f7f4f0f7`), zip delivery, D1 axiom wording (at-most-triple, no `sorryAx`), continuation-budget clauses. Batches dispatched by the maintainer in parallel chats | Recorded |
| **Epoch F1 integrated** (2026-10-09): all three batches returned complete and verified — A 13/13 (`Build/Embed.lean` now zero-sorry; 14 private additions incl. the `embedThroughHalt` core), B 11/11 (`Build/Seam.lean` zero-sorry; general cores with canonical instances, 13 privates), C 13/13 (`Build/Catalog.lean` Part 1 + W1/W2; **exactly 19 F2 sorries remain, byte-identical**; the `catalogTrace` full-configuration traces). Maintainer verification: SHA256SUMS 15/12/14 OK; each patch touches only its owned file; mechanical freeze audit — every removed line a `sorry` body plus two flagged Fill appendices in A; fresh replay sweep 0 errors (`audits/logs/routine-f1-integration-sweep.log`); **37/37 independent axiom prints** at most the standard triple, zero `sorryAx` (`audits/logs/routine-f1-axioms.log`); lint 0 FAIL. Integration by `git am -3`, Codex authorship preserved (d20ab758, a5012741, 2f67e910). Agent reports archived under `audits/routine-f1-agent-reports/`; patches under `audits/evidence/`. Deliveries also contained environment-shim C files (LD_PRELOAD `/proc/self/exe` workarounds per their reports) — **excluded per the standing instruction**: not compiled, not run, not integrated, unreferenced by the patches. C's requested shared lemma (a public `redirectTM` head-trajectory projection) recorded for the natural-home queue. The F1 epoch-boundary audit pack follows | Recorded |
| **Epoch-F1 fill-gate pack out** (2026-10-09): `audits/routine-f1-{pack,bundle}.md` — the epoch audit over the 37 kernel-checked fills: blind restatement of the sixty new private declarations (A 14, B 13, C 33), contract fidelity against the binding inherited plans, the declared anomalies (A's two unused-`hcap` warnings on frozen signatures; the two Fill appendices; C's shared-lemma request; the excluded environment-shim C files), and drift verification against the attached patch series. Bundle sha256 `b610b75e…`, 22 attachments (the three agent reports and patches verbatim, the maintainer's independent sweep/axiom/lint logs). Gate closes on zero blockers/majors; epoch F2 dispatches at its close | Recorded |
| **Epoch F1 gate CLOSED** (round 1, 2026-10-09: **PASS, 0 blockers / 0 majors / 1 minor / 4 notes** — `audits/routine-f1-findings.md` verbatim; loop summary `audits/routine-f1-resolutions.md`). All sixty new private declarations blind-restated clean; contract fidelity verified; the freeze re-established independently down to reconstructed blobs. Minor swept: the plan §4c F1B row's "four canonical statements" → three (3+3+2+1+2 = 11). Dispositions: the unused-`hcap` premise **retained** (it carries the capture interpretation); both Fill appendices verified append-only; the public `redirectTM` head-trajectory projection queued for `Wrappers.lean` (the seven local copies collapse then); the shim exclusion confirmed at source level (no FFI/foreign/unsafe/native anywhere). **§12 is 37/56; Embed and Seam are complete zero-sorry files** | Recorded |
| **Epoch-F2 brief issued** (2026-10-09): `briefs/routine-f2-batchA.md` — the final 19 Catalog space rows in the §4c risk order ((i) constant-witness ×7, (ii) linear ×3, (iii) the R5 case-split pair, (iv) four constructions incl. the direct `lengthBits` counter, (v) `cond` + the loop row with the answer-5 ledger embedded verbatim, (vi) **the `pairMapSnd` forwarding controller last — the fill's only new machine**, the R4 ledger embedded). F1C's in-file private helpers declared available; the queued `Wrappers.lean` projection explicitly off-limits; delivery completes `Catalog.lean` to zero-sorry | Recorded |
| **F2A partial integrated; continuation A2 issued** (2026-10-09): batch F2A delivered **17/19** in the prescribed risk order under ground rule 7, frontier exactly the loop ledger and the `pairMapSnd` summit (both original sorries untouched; no admitted helpers — 306 new privates all proved, incl. the reopened local copies `f2_loopHost*`/`catalog_redirect*`). Maintainer verification: checksums 14/14; single-file patch; **freeze verified by direct content comparison** — all 72 original declarations verbatim and in order (the diff's non-sorry removals were Myers-pairing artifacts of the large insertions); replay 0 errors, exactly 2 sorries; independent axiom prints 18 clean + `sorryAx` on exactly the two frontier rows (`audits/logs/routine-f2a-{integration-sweep,axioms,stylelint}.log`). Integrated `git am -3` (64f02699, Codex authorship). The delivery's environment-shim C file again excluded, unreferenced. `Catalog.lean` now 9,404 lines (reopened private witnesses; split stays queued, 12.2c). **Continuation brief `briefs/routine-f2-batchA2.md` issued** (the B2 precedent): the two targets with the F2A frontier text, the answer-5 ledger, and the R4 controller obligations binding | Recorded |
| **Construction-reuse policy adopted** (user-directed, 2026-10-09): new `policy.md` §1 paragraph — machines come from the verified construction layers (`Build/` combinators + catalog with `machine-library-design.md` as the registry, and the program layers); existing routines are cited, never re-derived; near-misses are commissioned into the shared layer (private copy + requested promotion), never privately re-derived a third time; hand-built machines need a recorded reason naming the gap; the discipline extends to circuits when the gadget layer exists. On the campaign branch as `811e95c8`; **merged to `main` via PR #7** (the PR #6 single-file precedent); `policy.md` identical on both branches | Recorded |
| **A2 integrated — §12 routine layer COMPLETE, 56/56 proved** (2026-10-09): continuation batch A2 delivered **2/2** — the loop ledger (`exists_loopTM_spaceUsed`: common radius `S n + 4ℓ + 8`, `c = c₀ + 19k`, **no round-count multiplication**, per the binding answer-5 six-step ledger) and the commissioned forwarding controller (`computesFunInTime_pairMapSnd_spaceUsed`: new `a2_mapTM` witness — buffer/validate, emit `pairEncode a []`, simulate with virtual input incl. both boundary clamps and empty `b`; **coefficient one on `Sg`**, `A=22`, `B=5`, single `c=22`; the refuted `pairMapTM` capture witness nowhere used). 45 new privates, all proved, inventory matched head-for-head. Maintainer verification: checksums 20/20; both patches touch only `Catalog.lean`; **freeze by direct content** — exactly two removed lines (both `sorry` bodies), all 378 base declaration heads verbatim and in order; `git am -3` (97daf8a5, 47880f58, Codex authorship), delivered source byte-identical; replay **0 errors, 0 sorry warnings** on Catalog + facade; **20/20 independent axiom prints** exactly the standard triple, no `sorryAx` (`audits/logs/routine-f2a2-{integration-sweep,axioms,stylelint}.log`); lint 0 FAIL (Catalog 10,876 lines — split stays queued, 12.2c). The delivery's environment-shim C file again **excluded per the standing instruction**, unreferenced by the patches. The F2 epoch-boundary audit pack follows | Recorded |
| **Epoch F2 gate CLOSED — §12 fill campaign COMPLETE** (round 1, 2026-10-09: **PASS, 0 blockers / 0 majors / 1 minor / 6 no-findings rows** — `audits/routine-f2-findings.md` verbatim; loop summary `audits/routine-f2-resolutions.md`). The auditor independently recomputed the bundle hash, reconstructed all three source states by bidirectional patch replay (blobs `b239b408…`/`f4b449b2…`/`798fb8ac…`), re-established both freezes, re-enumerated the 306+45 inventory, blind-restated all 45 A2 privates individually + the F2A load-bearers over a 30-family partition, verified the answer-5 and R4 ledgers (joint `S+T+1` coefficient, no round-count space factor; coefficient-one `Sg`, both empty-`b` clamps, no output buffer, `pairMapTM` absent), audited all six `f2_space_of_time` call sites, and ran fourteen adversarial instantiations. Minor F2-1 **swept at close** (prose only): the `f2_loopHost_start` sketch's "no-anchor prefix includes time zero" now qualified — zero-time startup already occupies the anchor (vacuous premise) and takes the two administrative steps directly; post-sweep fresh sweep clean (`audits/logs/routine-f2-close-sweep.log`). Carried: copy provenance of the unattached Loop/Primitives reopenings audited on merits (Wrappers copies verified literal); optional regression corollaries (zero-startup, both virtual clamps, emitting-halt seam) noted for the 12.2c refactor, not required. **The routine layer stands 56/56 proved — statement gate (3 rounds) + F1 (round 1) + F2 (round 1); §4b stage 2 (ARM extensions + colleague sync) is unblocked** | Recorded |
| **ARM extensions + colleague sync moved to backlog §2** (user, 2026-10-09; outreach to Hydroxyi initiated the same day). The §2.5 extensions wait on their reply and leave the backlog by a decision row here. They **block fills only, never statements** (the machine-heavy P4.x fills — `PATH ∈ NL`, Immerman-Szelepcsényi, Cor 4.21 on the ND ARM; `TQBF ∈ PSPACE`, `NP ⊆ PSPACE`, polynomial Savitch on the wide ARM — plus the ARM interface statements deferred out of P4.1). Stage 1's remaining prerequisite is Hennie-Stearns + the two-work-tape universal | Decided |
| **Tracks A and B opened in parallel** (user, 2026-10-09): **A** — the zone/virtual-input layer, `machine-library-design.md` **§13 drafted for review** (Z1 virtual-input hosting promoting the four-times-rebuilt `a2_mapVirtual` pattern; Z2 zoned carrier + shift rows for Hennie-Stearns, `SingleTape`/`ObliviousSetup` as harvest precedents; Z3 deterministic two-work-tape codes over the `actionBits₂` record; Z4 additive Robustness space annotation = the §2.7 Ex 4.1 fallback, with the design-time check of the universal's space bonus recorded as an obligation; open decisions 13.1-13.4). **B** — the chapter-1/2 retrofit under a **strict-simplification bar**: kernel-derived private inventories of `Build/Primitives`, `Build/Loop`, `CookLevin/Hardness` commissioned (classification REPLACE-R1/R2/CATALOG vs KEEP vs DEAD); the **`Universal*` cluster is excluded** (two-tape-universal pilot territory); partition §4d to follow from the inventories. **Retrofit integration rule (user, binding)**: retrofit batch output is never pushed to the campaign branch directly — integrate on a side branch, open a PR into `complexity/arora-barak-ch3-4`, the user merges manually. 12.2c stays queued post-retrofit | Decided |
| **P3.2 gate CLOSED** (round 2, 2026-10-09: **PASS, 0 blockers / 0 majors / 2 minors / 1 note** — `audits/ch3-p32-r2-findings.md` verbatim; loop summary `audits/ch3-p32-resolutions.md`). Both round-1 counterconstructions verified to violate the new `UniformMachineCode` clauses; `exists_uniformMachineCode` confirmed true by the auditor's independent polynomial construction over the concrete grammar (adopted into the sketch — minor R2-1: the received compiler route is arbitrary-time, no received polynomial ledger is claimed); "four-coordinate pairing" wording (R2-2). Carried: the fill-gate axiom-closure check for the choice-over-sorried-existence chain. **Natural-home promotions into the P3.1 files unblocked** | Recorded |
| **P3.3 gate CLOSED** (round 2, 2026-10-09: **PASS, 0 blockers / 0 majors / 2 minors / 2 notes** — `audits/ch3-p33-r2-findings.md` verbatim; loop summary `audits/ch3-p33-resolutions.md`). Both round-1 majors closed (fixed-code repetition; the concrete O(n) capped locator, no monotonicity needed). Minors swept: the ladder pinned (`ℓ₀ := 2` seed, the source formula authoritative — round-2 pack paraphrase acknowledged as an offset erratum) and the clock-allowance split stated with the interpreter prefix-bound obligation; the stage-bottom comparison attributed to the square (note 3). **Facade rewiring**: `NDCodes` joins `TuringMachine.lean`, `NTimeHierarchy` joins `Diagonalization.lean` (P3.2+P3.3 both closed), the root's two temporary imports removed; `Robustness/Bidirectional` added to the scratch tree (facade sweep gap). **Every drafted phase of the chapter-3/4 statement program is now gated closed except the §12 routine layer**; P3.4 (Ladner) remains the sole undrafted phase | Recorded |
| CH34-Q4 answered (user, 2026-10-08): **EXPCOM route** for the `A` half of Thm 3.7 — Ex 3.6(3) promoted to core, the `NP^EXPCOM ⊆ EXP` simulator added to the summit list (continuation budget certain); [BGS75, Thm 1]'s self-referential oracle recorded as fallback | Decided |
| **P0 reception audit, round 1** (2026-10-08, `audits/ch34-p0-findings.md`, verbatim): **0 blockers, 1 major, 7 minors, 2 notes — gate does not close**; repairs + re-audit round per `workflow.md` §3. The auditor confirmed the time-hierarchy family, `configBound`, `LOGSPACE_subset_P`, the compiler contracts and the index encoding under their actual hypotheses | Recorded |
| **Round-1 major repaired** (finding 1, maintainer-verified: `visitedByTapeHead` images a nonempty range, so `k ≤ spaceUsed` always; one zero of `s` collapses `SPACE s` to the zero-work-tape class): positive-bound convention adopted (§2.4), Ex 3.2 restated at `SPACE(n+1)`, documented in `SpaceComplexity/Basic.lean`, sanity layer `SpaceComplexity/ZeroSpace.lean` added (S1-S6, sorried statements). Minors swept: `sim_run` headline + S9 statement (`sim_run_of_regs_le`), `Mode`/`callSegs` zero-argument qualifier, `valP`/`valQ` canonical payloads, `lenEq`/`lenLe` totalization note, `ReachesB` strict-endpoint wording, `ARMSim`/`Compile`/`Layout` export-list corrections; finding 7 (sweep-log provenance) repaired by a fresh sweep whose log records its revision at start. Notes 9-10 require no change | Recorded |
| CH34-Q8 answered (user, 2026-10-08): the universal NDTM is built at **linear overhead** (guess-then-verify), so Thm 3.2 lands at book strength `f(n+1) = o(g(n))` | Decided |
| CH34-Q4 research (2026-10-08): the machine-light oracle `A = K(A)` **is** [BGS75]'s own Theorem 1 (verified against the scanned original, pp. 433-434), so no deviation from the primary source; [AB09]'s `EXPCOM` is the substitution. Awaiting maintainer confirmation of the route | Recorded |
| Citation audit (2026-10-08), prompted by the maintainer: no missing code-inspiration citation found in campaign-authored Lean code — vendored cslib files carry full headers (pin `a3747758`), `Composition.lean` cites [Balbach22], `Build/*` + `machine-library-design.md` §1-11 were frozen 2026-10-03, two days **before** the first Bonnet examination (2026-10-05, scratchpad-only, never imported; backlog records the after-the-fact cost comparison as convergence). No brief ever carried external code. Hydroxyi's `TimeHierarchy//SpaceComplexity//PolyHierarchy/` trees cite only [AB09]; two design similarities flagged to *ask* (not assertions): `LogProg` compiler vs lax-434930's `TimeCompiler`; `ConfigCount.core` vs cslib `ConfigBound`'s `Cfg.core` (upstream 2026-09-14). §12 citation duty ([lax-434930], Apache-2.0) remains binding when that design is written | Recorded |
```

## ===== audits/TEMPLATE.md =====

```
# External audit pack — TEMPLATE

Copy this file to `audits/phaseN-pack.md`, fill every `⟨…⟩`, and hand the result (plus
the listed attachments) to an external LLM from a different vendor, in a fresh context
with no access to this repository's development history. Record the findings in
`audits/phaseN-findings.md`. A phase's findings must be addressed (fixed, or explicitly
waived with a reason) before the next phase begins.

---

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions, theorem
statements, and remaining `sorry`s. The proofs that exist are machine-checked — do not
review tactic scripts for correctness. The failure modes you are hunting are:

1. **Infidelity** — a definition that does not mean what the cited source means.
2. **Trivialization** — a definition or statement satisfiable for degenerate reasons
   (vacuous hypotheses, a class that collapses, an encoding that makes a theorem empty).
3. **Unprovability** — a `sorry`d statement that is false as stated, or whose stated
   form is subtly weaker/stronger than intended (boundary cases: empty input, `n = 0`,
   `k = 0` tapes, constant absorption).
4. **Missing hypotheses** — especially finiteness, positivity, and well-formedness side
   conditions the informal source leaves implicit.
5. **Debt** — wholesale duplication of existing proved material (private copies of
   another file's declarations, re-derivations of registry routines), even when
   disclosed and mechanically forced by file ownership. Report it at **major** with
   the proposed fix "human acknowledgment required": it does not block the gate on
   soundness, but the gate must not close without the human maintainer explicitly
   accepting the debt and naming its scheduled resolution. Screen for it
   cumulatively — verify the pack's duplication ledger (per-file copied-material
   totals) rather than assessing each copy in isolation.

For **every definition** in scope: restate it in your own mathematical English *without
looking at the docstring first*, then compare your restatement against the cited source
location, and report any daylight. For **every `sorry`d theorem**: argue in 2-5 sentences
why it is true as literally stated, or exhibit the problem (ideally a concrete
counterexample or degenerate instance). Attempt at least ⟨3⟩ *adversarial
instantiations* — concrete pathological objects plugged into the definitions to check
they behave as the theory intends. Propose any machine-checkable sanity theorems you
believe are missing.

Do not give a blanket approval. Your deliverable is the findings table; an empty table
must be accompanied by the per-definition restatements that justify it.

## Scope

| Item | Where |
|---|---|
| Lean files under audit | ⟨list of files, with line ranges if partial⟩ |
| Source text | ⟨book/paper, edition, page/theorem numbers — auditor must have it at hand⟩ |
| Plan/context documents | `AroraBarakChapter1Plan.md`, `policy.md` §2-3 ⟨adjust⟩ |
| Out of scope | tactic proofs; vendored files' upstream design ⟨adjust⟩ |

## Known deviations (declared by the authors — verify they are benign, flag any others)

⟨Bulleted list: every deviation the docstrings declare, one line each.⟩

## Specific questions for this phase

⟨Numbered list of the doubts the authors actually have. Be concrete.⟩

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = statement is fixable but materially misleading as is, **or** accumulated
debt (failure mode 5) that the gate may not close over without explicit human
acknowledgment; **minor** = edge case or naming/attribution defect; **note** =
observation, no change required.
```

## ===== machine-library-design.md =====

```
# Machine-construction library — design document

Status: **FROZEN 2026-10-03** — the open decisions in §9 were resolved by the
user (resolutions recorded inline there). No code exists yet; every Lean
snippet below is an interface *shape*, not a final signature — final
signatures are fixed at spec time and audited.

Evidence base: the epoch-2 checkpoint integration (decision-log row,
2026-10-03). All five open fill frontiers are concrete-machine construction;
147 private helpers were delivered in one epoch, dominated by re-built
copiers, scanners, counters, capture wrappers, and phase glue. The
capture/silence wrapper alone now has four private incarnations
(`universalCaptureTM`, `enumCaptureTM`, `acceptTM`, and the private engine
inside `Composition.lean`'s `exists_cond`).

Prior-art disposition (2026-10-03 discussion): Mathlib's TM2 framework is a
stack-machine model whose poly-time layer contains one machine (the identity)
and no composition theorem; its inter-model compilations are semantics-only.
Decision: build on our own `FinTM` multi-tape model, which owns all the
quantitative assets; adopt the *design idiom* of Mathlib's TM1 statement
language (labelled structured control) for how named machines are written,
import nothing.

## 1. Goals and non-goals

**Goal.** Make "build a finite machine with a proved polynomial time bound"
a library-call activity rather than a bespoke construction, at the
granularity the fill briefs actually need: parse, measure, evaluate a
polynomial, search, split, compare, copy, emit, run a subroutine silently,
branch, loop.

**Non-goals.**
- No deep-embedded language, no verified compiler, no cost-sound surface
  syntax. (Mature end state; not justified by the remaining campaign.)
- No model change, no Mathlib TM2 dependency, no space bounds (the design
  must not *obstruct* a later space story, but proves nothing about space).
- No retroactive migration of audited epoch-1/2 proofs (see §8).

## 2. Architecture

Three layers over the existing run calculus:

```
Layer 2  CONTROL      timed cond · loop · capture/silence · halt-redirect
Layer 1  PRIMITIVES   named machines with ComputesFunInTime specs, ABI-compliant
Layer 0  (exists)     run calculus · bufferedCompTM/computesFunInTime_comp ·
                      bufferTape/virtualMove relocation · DecidesInTime
Consumer EXISTENTIAL  PolyTimeComputable / ∈ P corollaries only
```

**Design rule (the bridge lesson).** Constructive layers export *named*
`def` machines plus spec theorems; existential packaging (`∃ M c, …`)
appears only at the consumer layer. Quantifier shape is where audits bite —
a consumer may never need to bound an existential witness.

**Composition stance.** The default sequencing mechanism is *whole-machine*
composition via the public `bufferedCompTM` (already proved, `c = 2`
overhead): chain function machines, don't hand-build phase transitions. The
epoch-2 agents could not do this only because (i) the component machines
didn't exist, (ii) branching has no timed combinator, (iii) loops have no
combinator at all. The library supplies exactly (i)–(iii) and otherwise
stops people from proving phase compositions by hand.

## 3. The calling convention (ABI)

The model already gives whole machines a clean boundary: read-only input
tape, `k` work tapes, write-only (append-only) output tape, start at
`initCfg` with blank work tapes. The ABI therefore governs the only places
where configurations cross a seam *inside* a construction: round boundaries
of the loop combinator and entry/exit of wrapped subroutines.

**Canonical configuration** (the single formal notion, defined once):

- designated *state tapes* hold the round data (specified contents, heads at
  origin);
- all *scratch tapes* are blank with heads at origin;
- the output is empty (nothing emitted yet);
- the control state is a designated live anchor.

Loop bodies and wrappers prove "canonical-in ⟹ canonical-out" lemmas; the
combinators own everything else (startup from `initCfg`, final emission,
fuel exhaustion). Proposed discipline for scratch: **the body restores its
own scratch to blank as part of its contract** (it knows its own footprint,
so the proof is its own invariant run backwards), supported by a generic
`clearTM` primitive that sweeps a length-`m` region in `2m + 2` steps.
Rationale: 2A's killer was a *generic* reset proof; a body-specific restore
is mechanical. The alternative (combinator-driven clearing bounded by the
visited-region lemma in `Sweep.lean`) is recorded as the fallback if
body-restore proves heavier than expected. **[Open decision 9.2]**

**Multi-argument functions.** The ABI for arity > 1 is the existing
`pairEncode` idiom; the codec machines (§4) make it mechanical. No tuple
tapes, no new conventions.

**Deciders.** A decider is a function machine emitting the singleton
indicator (`[true]`/`[false]`), i.e. `DecidesInTime` as it already exists.
The decision layer (§6) builds AND/OR/NOT/guard over that, so `∈ P` goals
decompose without touching configurations.

## 4. Layer 1 — the primitive catalog

Rule of admission: a primitive enters the catalog only with **two named
customers** among the open frontiers (2A controller, 2B `choiceVerifier` +
reverse direction, 2C two verifier memberships, 2D `D-MEM`/`D-WRAP`/`D-EMIT`)
and the E3/E4 briefs. Current cut — 12 entries:

| # | Primitive | Spec (shape) | Source | Customers |
|---|---|---|---|---|
| P1 | `copyTM` | id in `n + 1` | exists (`Composition.lean`) | everywhere |
| P2 | `constTM w` | `fun _ => w` in `\|w\| + 1` | exists | 2D D-EMIT, E4 |
| P3 | `prefixTM w` | `fun x => w ++ x` in `\|w\| + \|x\| + 1` | harvest 2C (promotion already requested) | 2C, 2D D-EMIT |
| P4 | `lengthTM` | `fun x => bits \|x\|` (binary length) | new (2D's counter composition is the engine) | 2B, 2C, 2D D-MEM |
| P5 | `polyEvalTM C c` | `fun x => bits (C·(\|x\|+1)^c)` and unary variant | harvest 2D (`polyUnaryTM` + counter) | 2A startup, 2B, 2C |
| P6 | `pairSplitTM` / `pairJoinTM` | the `pairEncode` codec, both directions | new over existing grammar lemmas (2C/2D parsers are drafts) | 2C, 2D D-MEM/D-WRAP, E4 |
| P7 | `replicateTM` | `fun x => List.replicate (f \|x\|) true` for emitted-count `f` | harvest 2D emission chains | 2D D-EMIT, E4 ledger |
| P8 | `compareTM` | equality / `≤` test of two encoded numbers, singleton verdict | new (small) | 2B, 2C bound re-check |
| P9 | `scanLastTM` | split at last `true` (strip discipline), failure verdict | harvest 2C (`stripCertificate` semantics are proved; machine is new) | 2C, 2B split search |
| P10 | `searchTM` | least `i ≤ n` with `p i`, for `p` decided by a supplied decider on encoded `i` | new (uses W1 + loop L) | 2B split, 2C split |
| P11 | `incrementTM` | fixed-width binary increment + overflow flag + rewind | harvest 2A (`enumCarryTM`) | 2A, E3 padding counters, ch3 |
| P12 | `clearTM` | blank a length-`m` region, `2m + 2` steps | new (trivial) | loop bodies, 2A reset |

Each entry ships as: named `def` + one `ComputesFunInTime`/`DecidesInTime`
spec + an ABI-compliance lemma (canonical-out where applicable). Internal
idiom: TM1-style labelled control (a small inductive of labelled phases with
a `step` match), which is what 2D's `PolyControl` was reaching for.

Harvesting means **reimplementation against the ABI with the original proof
as the template** — the audited originals stay untouched in place; see §8.

## 5. Layer 2 — control

**W1. `captureTM` (silence/capture wrapper).** Given machine `D`: run `D`
with every emission suppressed and recorded — core variant records the full
output on a dedicated capture tape; register corollary extracts the first
bit for deciders. Spec: configuration-preserving lockstep, emission on the
halting transition included (the trap every private build re-proved), return
within `T_D + 1` into a live dispatch state, physical output empty.
Consolidates all four private incarnations; the obligations are already
enumerated by the phase-1 and phase-4 audit tables. **[Open decision 9.3 on
variants]**

**W2. `haltRedirectTM`.** 2C's `acceptTM` pattern as a named transformation:
halt iff captured bit is `b`, else enter the one-state live loop (with its
two-line non-halting lemma). Customers: 2A overflow wiring, HALT-style
control modifications, ch3 diagonalization.

**W3. `condTM` (timed branch).** The timed version of `exists_cond`: given
decider `D` (time `T_D`) and machines `M₁, M₂` (times `T₁, T₂`), a named
machine computing `if p x then f₁ x else f₂ x` within
`c · (T_D + max T₁ T₂ + overhead)`. Engine: W1 + the existing private
capture machinery of `Composition.lean`, made public and timed. Customers:
2C/2D reject-on-malformed guards, every parser.

**L. `loopTM` (the centerpiece — bounded loop with tape-resident state).**
Interface factored from 2A's admitted `enumMachine_contracts`, which is the
validated draft:

```
-- SHAPE ONLY. Final quantifiers to be fixed at spec time, audited.
structure LoopSpec where
  (round data σ, encoded on the state tapes; canonical config family cfg : σ → Cfg)
  (body B; fuel R : ℕ → ℕ; per-round budget T : ℕ → ℕ)
  contract : ∀ s, canonical s →
    within T n, B either EMITS a final verdict and halts,
    or reaches canonical (next s)      -- accept-or-advance
  exhaustion : after R n rounds without emission, halted rejection

theorem loopTM_decides …  :
  (loop machine) decides/computes … within
    startup + R n · (T n + c) + c'
```

The combinator owns: startup from `initCfg` (via an init machine composed
with `bufferedCompTM`), the fuel countdown (P11 as the engine), the final
rejection, and the summation. The body owns: accept-or-advance and its own
scratch restore (§3). 2A's proved `enumLoop_run` is the summation lemma's
template; `enumMachine_contracts` then becomes a *library instantiation*
rather than a bespoke admission. Customers: 2A (directly), P10, 2B reverse
direction, E3 padding, E4 stage loops, ch3 clocked simulation.

**Explicitly deferred from layer 2:** a general tape-embedding transformation
(run a `k`-tape machine on a tape subset of a larger machine). The wrappers
and the loop internally preserve "retained tapes" the way 2A/2B already do;
if a third site needs the general form, it gets designed then — not
speculatively now.

## 6. Decision layer (consumer-facing)

Over `DecidesInTime`: negation, conjunction/disjunction (W1-composition),
`guard` (W3 with constant-reject branch), `decideOfFun` (function machine +
P8-style final test), and the `∈ P` glue through the existing
`mem_P_of_dtime_le`/`mem_P_iff`. Everything here is existential and cheap;
its purpose is that goals like `pairedVerifier C c V ∈ P` decompose into
catalog calls plus the semantic lemmas the agents already proved.

## 7. Placement, naming, policy

- New subdirectory `TCSlib/Complexity/TuringMachine/Build/` (precedent:
  `Robustness/`): `Convention.lean` (ABI notions + canonical-config lemmas),
  `Primitives.lean` (P1–P12; split if the 600-line target demands),
  `Wrappers.lean` (W1–W3), `Loop.lean` (L). Namespace `Turing.FinTM`
  throughout (no new namespace).
- Order list: insert after `Simulation`/`Composition`/`Sweep`, before
  `Encoding` — the library depends only on the run calculus and the public
  relocation/composition machinery; nothing Chapter-1-headline depends on it
  (no import cycles, Chapter-1 statements untouched).
- Attribution: standard constructions, tagged [AB09 §1.2–1.4] where the text
  has them (claim-by-claim as policy requires); module docstring records the
  TM1 statement-language idiom as a design reference (Mathlib) alongside the
  Asperti–Ricciotti and Forster–Kunze precedents.
- This is frozen Chapter-1 surface growth → it gets its own audit (§9.4 for
  the vehicle). Spec statements land sorried first (statement-phase
  discipline), the pack leads with the quantifier shapes (ABI, W1 lockstep,
  L's contract) since that is where this design can be wrong.

## 8. Harvest and migration policy

- Harvest = reimplement against the ABI using the original proof as
  template. Originals (2A/2B/2C/2D privates, audited epoch-1 material) stay
  byte-identical; no re-audit of closed work.
- Deduplication (retiring privates in favor of library calls) is an **E5
  closure task**, recorded in the backlog, not done opportunistically.
- 2C's pending shared-lemma requests (`prefixTM`/`fixedPair`) are subsumed
  by P3 + P6 and get their disposition in this design's audit round.

## 9. Decisions (resolved by the user, 2026-10-03)

1. **Primitive cut** (§4): P1–P12 confirmed as listed.
2. **Scratch discipline** (§3): body-restores-scratch, with
   combinator-driven clearing via the visited-region bound recorded as the
   fallback if body-restore proves heavier than expected.
3. **Capture variants** (§5 W1): tape-capture core + register corollary.
4. **Audit vehicle**: one shared infrastructure round carrying the library
   spec layer *and* the Chapter-1 bridge export.
5. **Build sequencing**: campaign structure — maintainer writes the spec
   layer serially (quantifier-sensitive), shared audit round, then fills
   dispatched as harvest-adaptation batches, the loop fill flagged for
   continuation budget.
6. **Naming**: `Build/` and the P/W/L working names stand; any rename
   happens before the spec audit (renames after it are drift).

## 9a. Spec-phase refinements (2026-10-03, recorded when the spec layer landed)

The spec layer (`TuringMachine/Build/{Convention,Wrappers,Loop,Primitives}.lean`)
realizes the catalog with these refinements against §4–§5, none touching the
frozen §9 decisions:

- **Seam notion**: `Cfg.ofWords` is a *constructor* (anchor state, input head
  at 1, word-per-tape from the origin via `bufferTape`, heads at origin,
  empty output) and seam contracts are `runFrom`-equations against it —
  rewrite-friendly, and `initCfg` is provably the empty-words seam.
- **Packaging**: contracts are existential in the house idiom of
  `Composition.lean`; fills implement named private machines and close them.
  The §2 named-machine rule is realized as quantifier discipline inside each
  statement (machine fixed after its parameters, before all inputs — the
  bridge lesson), not as global naming.
- **P6** is realized as `pairEncodeFixed` (provably an instance of P3 at the
  doubled-word-plus-separator prefix) plus threaded extractors
  `pairFst`/`pairSnd`/`pairValid`.
- **P7** is subsumed by P5's unary clause, whose instances are what the
  emission customers consume. **P8** is realized in threaded form
  (`pairLenCheck` on `pairEncode a b`, so the original input travels with
  the payload and the audited original-bound re-check is against it).
  **P12** has no standalone contract: clearing is intra-machine, part of the
  loop fill's toolkit.
- **W1** is host-parametric (`captureAction`/`captureCfg` transformers + one
  lockstep equation guarded by source liveness), so consumers embed the
  source into their own controller state type; the register corollary is
  derived at fill time. **W2** is the closed `redirectTM` with an
  `Option Bool` last-emission register (`none` = no emission yet; a source
  with empty output never halts the redirect).
- The lint-mandated construction sketches surfaced a real obligation worth
  recording: append-only output means every parser/extractor must **buffer
  until validity is known** — the output-silence discipline reappears at
  the primitive level (extractors, strip, increment's overflow detection).

## 9b. Round-2 repairs (2026-10-03, after `audits/ch1-infra-findings.md`)

The round-1 audit refuted `exists_loopTM` (blocker: a zero-step identity
"advance" made the hypotheses vacuous while the conclusion violated the
input-head information bound; major: quantifying rounds over *all* state
words at budget `T |x|` excluded the intended customers) and rejected
disposition D5 (missing dynamic assembly and result-bearing search). The
repairs, all in the spec layer:

**The loop contract, redesigned.** Rounds take positive time (`0 < t`);
rounds are required only on words satisfying an input-indexed
admissibility invariant `Inv x s`, established at `s0` and preserved by
the step; and `stepF`/`acceptF`/payload take the input explicitly (the
enumerator's acceptance runs the verifier on `x ++ s`). Two forms:
`exists_loopTM` (Boolean verdict) and the new `exists_loopFindTM` (first
accepting orbit point's payload; `[]` on exhaustion). The countdown sketch
debits from the **second** anchor entry, so `R = 0` still checks `s0 x`
(round-1 finding 4), and the amortized-borrow budget argument was
validated by the auditor.

**Instantiation tables** (the customer-coverage evidence round 1 asked
for; `m n := C·(n+1)^c` abbreviates the certificate-width polynomial):

| Parameter | Enumerator (2A's `enumMachine_contracts`) | Split search (P10) |
|---|---|---|
| `Inv x s` | `s.length = m x.length` | `s.length ≤ x.length + 1` |
| `s0 x` | `List.replicate (m x.length) false` | `[]` |
| `stepF x s` | `(incFixed s).getD s` (stall on overflow keeps the width) | `if s.length ≤ x.length then s ++ [true] else s` (stall keeps `Inv` step-closed) |
| `acceptF x s` | the captured verifier's verdict on `x ++ s` | `s.length + C·(s.length+1)^e = x.length` |
| payload | — (decision form) | `pairEncode (x.take s.length) (x.drop s.length)`, never `[]` |
| `R n` | `2^(m n) − 1` | `n` |
| fuel bits | `Nat.bits (2^(m n) − 1) = replicate (m n) true` — writable within `T` | `Nat.bits n` — writable within `T` |
| orbit, `i ≤ R n` | all `2^(m n)` width-`m` words, each once (`incFixed` enumeration; the stall is beyond fuel) | the candidates `0, …, n` in unary; `find?` = `solveSplit`'s least solution |
| conclusion shape | `[decide (∃ u, u.length = m n ∧ verifier accepts x ++ u)]` | exactly P10's stated function |

Both invariants bound the state-word length by the input, which is
precisely what dissolves the round-1 finding-2 obstruction (no body is
asked to transform words longer than its budget can traverse).

**Catalog additions** (finding 3): P13 `pairConcat`
(`pairEncode x u ↦ x ++ u`, the D-WRAP shape), P14 `pairDup`
(`x ↦ pairEncode x x`), and the combinator C1 `pairMapSnd` (transform a
pair's payload, retain its head; the data-retaining assembly sequential
composition cannot provide). D-EMIT's nested quadruple then factors as
`pairEncodeFixed α₀ ∘ pairMapSnd (unary-runs generator) ∘ pairDup`, and
D-MEM's parser chains through the extractors with `pairMapSnd` carrying
retained components. **P10 narrowing recorded**: the implemented search is
the fixed length-equation search, not the catalog's supplied-predicate
search; the general form is `exists_loopFindTM` itself.

## 9c. Round-3 repairs (2026-10-03, after `audits/ch1-infra-r2-findings.md`)

Round 2 passed the redesigned loops, P13/P14/C1, and the §9b tables, and
discharged both round-1 refutations; its one major (finding 1) showed the
loop's *final-answer* conclusion cannot discharge the frozen
`enumMachine_contracts`, which is a *configuration-level* contract — the
auditor's delay machine answers correctly yet violates every per-round
bound. Repairs:

**The configuration-level export.** `exists_loopCfgTM` (same hypotheses
as the decision form) concludes with the host's round-configuration
family: startup ≤ `c·(T+1)` reaching `cfg 0`, empty output at rounds
`0…R`, per-round accept-or-advance segments each within `c·(T+1)`, and
the halted `[false]` terminal at index `R+1`. The decision form becomes a
fill-time corollary through an already-halted-terminal summation lemma
plus monotonicity (R3-1: the frozen `loop_run` requires an empty-output
terminal, so it is not invoked directly on the exported family). **Index/budget
translation to `enumMachine_contracts`** (under the §9b enumerator
instantiation, `w := m n`): candidates `2^w = R n + 1`, so the terminal
index matches; the customer's uniform bound `b·(n + w + 1)^e` dominates
`c·(T n + 1)` once `T` is chosen as a polynomial in `n + w` and `b, e`
absorb `c` and its degree; the per-round indicator matches via the fill's
orbit bridge `(stepF x)^[i] (s0 x) = enumWord w i` (little-endian rank
enumeration, `incFixed` = `enumInc` per the round-2 vocabulary note).

**Vocabulary coefficient shift (round-2 note 5, adopted).** The proved
equalities are `splitAtLastTrue = stripCertificate`, `incFixed = enumInc`,
and `solveSplit (C+1) c = certificateSplit C c` — the split-search
equality is false without the shift (R3-3 corrected this pointer). Consequently the padded-verifier pipeline uses P10 at
`(C + 1, c)` while P8 keeps `(C, c)` for the original witness bound.

**General pairing assembly (round-2 item 10's derivation, adopted
verbatim as the canonical recipe).** For computed `f, g`:
`H x := pairEncode (f x) []` (P14 + C1 at the constant-empty function);
`s x := pairEncode x (H x)`; `t x := pairEncode (s x) (g x)` (P14 + C1,
the second with `g ∘ pairFst`); then
`pairSnd (pairConcat (t x)) = pairEncode (f x) (g x)` — the
self-delimiting grammar makes concatenation-into-payload well-formed at
every stage. A C1 call on `pairEncode a b` computes `g b` only; any
cross-component operation goes through this retained-whole-request
pattern, never through C1 directly (round-2 item 10's D-MEM caveat).

**D5 scope (round-2 items 6/10).** The disposition is re-issued for the
epoch-2 frontiers and P10 only; the E3/E4 rows are component-level
plausibility and their full coverage check is deferred to those epochs'
brief audits, where the six-stage/boundary/ledger tables are in scope.

## 10. Cost and sequencing (estimate, campaign points)

| Work | Est. | Note |
|---|---|---|
| Spec layer (all signatures + ABI) | 8 | maintainer, serial; the design-sensitive part |
| Spec audit round | — | rides with bridge export per 9.4 |
| P1–P12 fills | 14 | mostly harvest-adaptation; parallelizable |
| W1–W3 fills | 9 | W1 obligations already tabulated by past audits |
| L fill | 13 | the real risk concentration; continuation budget anticipated |
| **Total** | **≈ 44** | one mid-size batch equivalent |

Sequencing: freeze this design → spec statements + bridge export → shared
audit round → fills → **then** E2 continuation briefs, which cite the
library instead of re-deriving machines. E2 continuations, E3, E4, and the
ch3 skeleton are the customers that pay this back; the loop combinator is
the piece to watch for slippage.

## 11. The emitter increment (proposed 2026-10-05, post-E3 integration)

**Evidence.** E3's outcome maps the library boundary exactly: everything
recognizer-shaped closed in one round through the catalog (3B's memberships
via `computesFunInTime_splitSolve 1 1` + capture + the audited wrappers; 3D
via P10 + capture + composition), while both stalls sit on the producer
side — 3B at a streaming transducer (`satRedTM` states 9–34, defined,
unproved), 3A at a loop body that must internally run an evaluator and emit
a payload, over a width family the catalog's split instance doesn't cover.
The loop contracts deliberately require **empty output through every round**
(round-2/3 audit repairs), and composition offers only input-pipelining —
there is no output-append mode anywhere in the library. E4's summit
(`SAT_NPHard`, 15 pts, continuation certain) is an emitter of exactly this
shape: a per-index loop appending clause groups under the six-stage
output-silence contract with an exact serialization-length ledger.

**Rule of admission check** (§4): every item below has at least two named
customers among 3B-cont, 4A, 4B, and 3A-cont.

### E1. `emitLoop` — the emitting loop (control layer)

The loop engine's output clause generalized: rounds append exact per-round
emissions instead of staying silent. Shape (final quantifiers at spec time,
audited):

```
-- SHAPE ONLY. Sibling of exists_loopCfgTM, sharing its host machinery.
Inv, s0, stepF as in the decision loop; additionally
  emitF : input → σ → List Bool        -- the exact chunk of round i
contract: startup ≤ c(T+1); per-round segments ≤ c(T+1); positive
  first-return; for every i ≤ R:
    (cfg i).output = (List.range i).flatMap (fun j => emitF x (stepF^[j] s0))
  terminal: halted, output = the full concatenation (no verdict bit — the
  machine COMPUTES the concatenation; a deciding variant is NOT included).
```

Body obligations unchanged (accept-or-advance becomes advance-and-emit;
scratch restore per §3/9.2). The summation lemma is `loop_run`'s template
with the output clause threaded. **Customers:** 4A (the per-snapshot clause
emitter — the design driver), 3B-cont (`satRedTM`'s streaming core as an
instantiation), 4B (dual reduction emitter).

### E2. `emitPhase` — the forwarding wrapper (control layer)

The dual of W1: run an embedded transducer `T` (a `ComputesFunInTime`
contract) inside a host, with `T`'s emissions landing on the **host's**
output tape, source tapes isolated, halt redirected to a live return state;
lockstep lemma in `capture_run`'s mold with "physical output = host prefix
++ T's output so far". This is what lets a catalog transducer serve as one
emission stage of a larger machine — today's only option is whole-machine
input-pipelining. **Customers:** E1's per-round chunk calls (4A emits each
clause group through a sub-transducer), 3B-cont (fresh-literal chain
emission), 3A-cont marginally (the success payload `pairEncode` emission).

### E3′. Stream primitives (catalog rows P16–P18)

| # | Primitive | Spec (shape) | Source | Customers |
|---|---|---|---|---|
| P16 | `tokenStepTM` | consume one self-delimiting token (unary index / marker) from the input head, land head after it, expose the token in control | harvest: 3B's proved `satScanTM`/`satSyntaxStep`, 3D's six-state scan, 2D's parsers (fourth re-derivation otherwise) | 3B-cont, 4A, 4B |
| P17 | `chunkEmitTM w` / parametric | append a control-determined word to output, `\|w\|` steps, no tape movement | new (trivial); the per-token emission atom | E1 bodies, 4A |
| P18 | `unaryAccTM` | dedicated-tape unary accumulator: append one, read-length-in-binary via P4 composition, rewind | harvest: 3B's proved counter stages (`satRedCounter_write`, `satRed_maxOnes`, startup to state 9) | 3B-cont, 4A fresh indices |

### E4′. `splitSolveWith` — width-parametric split search (control layer)

Generalize P15's split search from the hardwired polynomial family to a
hypothesis-supplied width evaluator: given a machine `E` with a captured
`ComputesFunInTime (fun s => bits (f s.length)) T_E` contract and
monotonicity of `n ↦ n + f n`, a machine solving `n + f n = m` (first
success payload `pairEncode (take n) (drop n)`, exhaustion verdict) within
the loopFind envelope over `T_E`. **Harvest source:** 3A-cont's bespoke
body, whose contracts are already displayed in its REPORT — build the
parametric form against that template once it lands (or directly, if this
increment executes first). **Customers:** 3A-cont's equation (plug the
proved `e3_exp_bits_timed`), every future padding argument (ch3+ time
hierarchy pads the same way).

### Placement, cost, open decisions

- **Placement:** E1 extends `Loop.lean` **in-file** to reuse the audited
  `loopHost` privates (a separate `Build/Emit.lean` cannot see them — the
  D7 cross-file-privates qualification; re-deriving the host would be a
  second 2,500-line proof). `Loop.lean`'s size exception grows and the D7
  split trails as already recorded. E2 joins `Wrappers.lean`; P16–P18 join
  `Primitives.lean`; E4′ joins `Loop.lean` beside P15's engine.
- **Non-goals:** no deciding variant of the emitting loop (compose E1 with
  the existing decision layer instead); no general transducer algebra; no
  speculative tape-embedding (unchanged from §5's deferral).
- **Cost estimate:** spec layer 4; one shared-infra audit round (the ch1
  pattern, expected lighter — one host extension, not a new host); fills:
  E1 8, E2 4, P16–P18 5, E4′ 6 — **≈ 27 points**, roughly the L batch.
- **Sequencing:** freeze this section → spec statements → audit round →
  fills → 3B-cont consumes E1/E2/P16–P18; 4A's brief cites the layer
  instead of a bespoke emitter. **3A-cont dispatches in parallel, bespoke**
  (disjoint ownership; its body becomes E4′'s harvest template; later
  dedup is a recorded E5-style maintainer task, never the fill's).
- **Open decisions (user):** (11.1) approve the increment and this scope;
  (11.2) E1 as a sibling contract beside `exists_loopCfgTM` (recommended)
  vs a generalization replacing it (touches audited statements — not
  recommended); (11.3) whether 4A's brief waits for this gate to close
  (recommended) or anticipates it.

## 11a. Spec-phase refinements (2026-10-05, recorded when the emitter spec landed)

Decisions 11.1–11.3 resolved by the user (2026-10-05): increment approved;
E1 is a **sibling** contract beside `exists_loopCfgTM` (no audited statement
is generalized or touched); 4A's brief **waits** for this gate.

Refinements against §11 as drafted, all narrowing:

1. **P17 is subsumed** (no new statement): a constant chunk emission is
   `emitPhase` (E2) applied to the existing P2 `constTM` — recorded here
   the way D4 recorded the prefix/fixed-pair subsumptions.
   *[Superseded by §11b item 6 and §11c: the discharging rule is body
   finite control for fixed words, or `exists_emitCallTM` for computed
   chunks — never the private `constTM` (round-2 audit, finding 3).]*
2. **P18 narrowed to `computesFunInTime_appendBit`**: the drafted
   accumulator row conflated the append atom with cross-phase persistence,
   and persistence is already the loop engine's state-word mechanism; the
   catalog takes only the atom.
3. **E4′ lives in `Primitives.lean`**, not `Loop.lean`: its conclusion
   speaks `pairEncode`, which `Loop.lean` does not import, and P15's own
   public contract already lives there — the engine/contract split follows
   P15 exactly. Its pure vocabulary `solveSplitWith` joins `Convention.lean`
   beside `solveSplit`, which it definitionally generalizes.
4. **E1 is function-level only** (`exists_emitLoopTM` concluding a
   `ComputesFunInTime` of the chunk concatenation): all three named
   customers deliver `PolyTimeComputable` reductions, i.e. function-level
   contracts, and in-host composition of an emitter is E2's job, which
   takes function-level transducers. The round-2 lesson (final-answer vs
   configuration gap) was checked against each customer before choosing
   this form; a configuration-level export would follow the round-3
   precedent if a consumer ever surfaces.
5. **No emission-size hypothesis on E1**: the round seam equality itself
   bounds each chunk by the round's duration (output grows by at most one
   symbol per step), so the statement carries no redundant bound to drift.

Spec surface: **five sorried contracts** (`Turing.emit_run`,
`Turing.FinTM.exists_emitLoopTM`,
`Turing.FinTM.computesFunInTime_splitSolveWith`,
`Turing.FinTM.computesFunInTime_unaryToken`,
`Turing.FinTM.computesFunInTime_appendBit`), two real transformers
(`emitAction`, `emitCfg`), two pure vocabulary definitions
(`solveSplitWith`, `unaryTokenSplit`). Convention's module-docstring
vocabulary bullets extend at fill time (append-only).

## 11b. Round-2 repairs (2026-10-05, after `audits/emitter-infra-findings.md`)

Round 1: **0 blockers, 2 majors, 3 minors** — no false statement among
the five contracts; both majors are adequacy obligations, repaired here.

1. **The clean-call bridge (finding 1, major).** A function-level
   contract cannot deliver the loop seam: a witness may dirty scratch or
   leave heads displaced on its final transition and still compute `f`
   within `T`. Two new sorried bridge contracts supply the
   prepared-input/clean-return interface, both with canonical
   `Cfg.ofWords`/`stateWord` entry **and** exit seams, first-positive-
   visit discipline, and envelopes charged to `T + |arg| + |f arg| + 1`:
   `Turing.FinTM.exists_installCallTM` (result installed as the
   tape-resident word, nothing emitted) and
   `Turing.FinTM.exists_emitCallTM` (argument preserved, the computed
   chunk forwarded to physical output). Both live in `Loop.lean` beside
   the seams they serve (`stateWord` is defined there). Fill route: the
   A-continuation's proved log/undo pattern around the capture wrapper,
   with virtual-input preparation from the tape-resident argument.
   `emitCfg`'s docstring now states explicitly that it does not
   normalize terminal configurations — the bridges do.
2. **The 3B normalization mapping (finding 1, required resolution).**
   The reported `satRedTM` is **not** the promised instantiation as it
   stands (its permanent position-−1 marker contradicts the blank
   `ofWords` seam; its raw head positions cannot cross seams). The
   committed instantiation plan: loop state word encodes
   `(cursor, consumed-prefix length, phase tag)` via the audited pairing
   vocabulary — the raw streaming position is re-derived each round by
   advancing past the consumed prefix, and **the permanent marker is
   eliminated** (round-local buffering restores its tape by round end).
   Per round: decode the state word; `exists_installCallTM` over
   `computesFunInTime_unaryToken` reads the next token of the remaining
   serialization; finite control classifies marker/polarity bits; the
   emitted clause fragment goes out through `exists_emitCallTM` (chunks
   are of token-bounded length) or directly by finite control for
   fixed fragments; the fresh-variable counter updates through
   `computesFunInTime_appendBit` + install. Rounds have positive
   duration and input-length-only budget; `R` = the serialized input
   length (each round consumes at least one input position); once the
   formula terminator is consumed, an **absorbing finished phase emits
   empty chunks** for all remaining rounds. Token output is decoded by
   `pairDecode`-side vocabulary (proved); append output becomes the
   next state word by the install call. The banked `satReduction_*`
   semantics close the function identity; `satRed_start`'s proved
   maximum-pass survives as the `s0` computation.
3. **The 4A stage mapping (finding 2, required resolution — recorded
   here, certified against the attached phase-4 records in round 2).**
   All-string validation runs **before any irreversible emission**: the
   validation stages run as a decision prefix (the audited conditional
   W3 over the parser/boundary checks); only the valid branch enters
   the emitting loop, and the invalid branch emits the fixed fallback
   through finite control. Logical round count: `R` = the
   snapshot-index bound of the six-stage contract (an input-length-only
   polynomial), one clause group per round through `exists_emitCallTM`;
   the exact serialization-length ledger is the sum of the per-round
   chunk lengths — never constant-per-clause, exactly as the phase-4
   ledger demands. Serialization terminators: the final terminator is
   the last round's chunk tail (or a post-loop constant emission by
   finite control); both options keep the concatenation exact.
4. **Host routing correction (finding 3, minor).**
   `exists_emitLoopTM`'s construction sketch now specifies the
   **forwarding host variant** (body dispatched through `emitAction`;
   fuel/countdown machinery reused; contracts proved over
   arbitrary-accumulated-output configurations; a **new**
   prefix-summation lemma modeled on `loop_run`) — the unchanged
   find-mode host is refuted by the auditor's one-state witness, since
   `captureAction` suppresses the body's physical output.
5. **Token conventions (finding 4, minor).** `unaryTokenSplit`'s
   docstring now states it consumes unary tokens only, with the
   auditor's separating example; standalone markers and polarity bits
   are scanner grammar states.
6. **P17's actual rule (finding 1's visibility note).** Fixed
   finite-control chunks are emitted directly by body control (no
   primitive, no appeal to the private `constTM`); unbounded
   tape-dependent chunks go through `exists_emitCallTM`. §11a item 1 is
   corrected accordingly: the subsumption's discharging rule is body
   finite control, or the emit call, never the private constant
   machine.
7. **Documentation (finding 5, minor).** The four definitions now carry
   customers and construction notes; attestation 4's "every new
   declaration" claim is restated in the round-2 pack as exactly what
   each class of declaration carries.

Spec surface after round 2: **seven sorried contracts** (round 1's five
plus the two bridges), two transformers, two vocabulary definitions.

## 11c. Round-3 repairs (2026-10-05, after `audits/emitter-infra-r2-findings.md`)

Round 2: **0 blockers, 2 majors, 1 minor** — round-1 findings 3–5 closed;
the bridge construction and the 3B normalization validated (r2 findings
4–5, including a 5,908-case finite corroboration of the normalized
schedule); the two cumulative majors repaired here.

1. **Positive tape count on both bridges (r2 finding 1, major).** At
   `C.k = 0`, `stateWord 0 a = stateWord 0 b` by empty domain, so the
   install conclusion was satisfiable by a two-state zero-tape machine
   for an arbitrary — even noncomputable — `f`: vacuous as a data
   interface. Both conclusions now carry `0 < C.k`, making the seam
   equality yield the genuine `bufferTape` content at index zero. The
   auditor's r2 finding 4 confirms the log/undo construction delivers
   the strengthened interface at the stated envelope.
2. **The 4A mapping rewritten (r2 finding 2, major) — this supersedes
   §11b item 3 in full.** §11b item 3 wrongly substituted parser
   validation for Cook–Levin's silent preparation stages: the 4A source
   is an arbitrary `NP` language, every binary word is a legitimate
   instance, and there is no CNF well-formedness condition on `x` (the
   auditor's empty-language witness: validation-plus-fallback would
   emit the satisfiable `serialize [] = [false]` for a no-instance).
   Parse-before-emission belongs to the 3B/4B decode-based transducers
   only. The corrected stage-to-seam mapping:
   - **Silent preparation (inherited stages s1–s5).** A silent startup
     phase computes and packs the preparation records into `s0 x`:
     exact `Q(n)`, `m = n + Q(n)`, and the horizon `T` (s1, exact
     arithmetic, certificate length never enlarged); the virtual
     reference input `false^m` with clamped virtual head, source
     writes/moves executed on the halting transition, source output
     suppressed and halt internalized (s2–s3, through the capture and
     install-call interfaces at positive tape count); the inclusive
     trajectory records for **all** times `0..T` with administrative
     transitions outside simulated time and frozen positions after an
     early halt (s4); greatest-strictly-earlier-visit records with
     sequential comparison costs (s5). All of s1–s5 end with empty
     physical output and the packed records as the clean persistent
     word — the emitting loop's `s0`.
   - **Ordered emission (s6).** One **family member per round**, the
     cursor walking the fixed family order of the phase-4 contract.
     With `T + 1` snapshot times and `k` work tapes, the six families
     have `n, 1, T, T+1, k(T+1), T` members; the round count is their
     sum: `R = n + (k+3)·T + k + 1` (an input-length-only polynomial).
     Rounds with empty template output still take positive time. The
     single final formula terminator is appended to the last round's
     chunk. The serialization-length ledger is the exact sum
     `1 + 2·#clauses + Σ (v+3)` over literal occurrences — total
     output `O_M(T²)`, never constant-per-clause.
   - The alternative `R = T` time-major grouping is **not** adopted:
     it would need a separate proof that its interleaving reserializes
     to the fixed family order.
   Certification of this mapping against the phase-4 round-2
   boundary-check table is round 3's business — that table
   (`audits/ch2-phase4-reaudit-findings.md`) rides in the r3 bundle,
   and the 4A brief inherits it verbatim per the standing rule.
3. **P17 cross-reference (r2 finding 3, minor).** §11a item 1 now
   carries an explicit supersession marker pointing at §11b item 6;
   the historical text is preserved as history.
4. **Provenance upgrades for round 3.** The log/undo fill route now has
   fresh in-repo provenance beyond the epoch-2 enumerator: the
   A-continuation checkpoint (integrated 2026-10-05) banked exactly the
   track/clear/compare phase family the r2 finding-4 construction
   describes (`e3cTrackTM`/`e3c_track_run`/`e3cClearTM`/`e3c_clear_run`
   — logged simulation over a visited interval with origin markers,
   exact single-triple cleanup at `6T+7`, positive first returns), as
   proved privates in `Nondeterminism.lean`; its REPORT and source ride
   in the r3 bundle.

Spec surface after round 3: unchanged in count — **seven sorried
contracts** (the two bridges now carrying `0 < C.k`), two transformers,
two vocabulary definitions.

## 11d. Gate close (2026-10-05, after `audits/emitter-infra-r3-findings.md`)

Round 3: **0 blockers, 0 majors, 1 minor, 4 notes — GATE CLOSED**
(`audits/emitter-infra-resolutions.md`). Both cumulative majors
discharged: the positive-tape bridges export the data interface (the
auditor's projection-table derivation), and §11c's 4A mapping is
certified against the inherited boundary table, including the exact
per-member chunk rule. The minor — swept in the closing commit — was an
attribution error of §11b item 1/§11c item 4 and the install-call
sketch: the A-continuation's delivered provenance is
**visited-interval tracking and clearing** (`e3cTrackTM`/`e3cClearTM`),
not an overwritten-symbol history/undo implementation; at a clean
entry seam, clearing is restoring, so the track/clear route fills the
bridges directly, and history/undo stands only as the independently
derived alternative (r2 finding 4). Two clarifications from r3
finding 3 bind the 4A brief: `R = n+(k+3)T+k+1` is the last round
index (member count `R + 1`), and the chunk rule emits per-member
flatMaps with the single terminator on the last chunk only. Fill
batches proceed under the resolutions' binding section, partitioned
Loop / Primitives / Wrappers.

## 12. The routine layer (proposed 2026-10-08, pre-ch3/4 campaign)

**Mandate** (user decisions 2026-10-06 and 2026-10-08, recorded in `backlog.md` §2
and `AroraBarakChapters3-4Plan.md` §4a/§8): built after the Chapter-2 closure and
**before the chapter-3/4 fill epochs**, in parallel with their statement phases;
scoped to **amply support the chapter-1/2 retrofit**, not merely the new
consumers; and — superseding §1's "no space bounds" non-goal for this increment —
**every item below carries a space clause alongside its time cost**, so that the
chapter-4 campaign and the P4.x statements consume the layer without a second
pass. The space measure is the house one: `Turing.MultiTapeTM.spaceUsed`
(work-tape cells visited; input and output tapes excluded).

**Evidence.** The 4A chain is the measurement: roughly half of the A2/A3
deliveries' 202 native privates are hand-rebuilt bank/relocation/dispatch
routines; the `emitterBank*`/`emitterP2*` relocation family was privately
re-harvested three times; and A3's proved costs (`3|w| + 3` copy, `2|w| + 2`
clear) match the external prior art's `3w + 2`/`2w + 2` to within one step —
independent convergence on the same catalog, discovered in the 2026-10-06
survey. The emitter round-1 finding stands: *function-level* contracts cannot
deliver clean-return seams, so the gap is configuration-level. §5 deferred the
general tape-embedding transformation "until a third site needs it"; the third,
fourth, and fifth sites have now arrived (the retrofit families, the
Hennie-Stearns conversion, the two-work-tape universal machine).

**What already exists and is consumed, not duplicated** (colleague modules,
Hydroxyi/Jason Dong, on `main` since `f70c57c2`): the *function-level half* —
`TuringMachine/CounterProg{,Run}.lean` (goto programs over unary registers
compiled once into `FinTM`, `t` abstract steps within `t(2t+3)` machine steps,
FP bridge via `ClassNP/CounterProgPolyTime.lean`), `ClassNP/Transducer.lean`,
`ClassNP/{PolyTimePairing,PClosure}.lean`, `TuringMachine/UnaryTape.lean`; and,
on the space side, `SpaceComplexity/Machines/` (the `LogProg` register-program
compiler with `compile_space`/`arm_decides`). §12 supplies the
configuration-level half those layers sit on.

### R1. Bank embedding (the §5 deferral, promoted)

A verified routine on its own `m`-tape set runs on any injectively selected
subset of a `k`-tape host's work tapes, cost unchanged, everything else framed.
Spec shape (final quantifiers fixed at spec time, audited): for an embedding
`ι : Fin m ↪ Fin k`, transported actions and configurations with

* **lockstep** — transported `runFrom` commutes with the source `runFrom`;
* **frame** — tapes outside `range ι` are byte-identical before and after, their
  heads unmoved; input position tracks the source; emission policy is a
  parameter (suppressed or forwarded — the W1/E2 pair fixes the two modes;
  whether this is one transformer with a mode or two transformers is open
  decision 12.4);
* **time** — step count preserved exactly;
* **space** — cells visited on host tape `ι i` equal cells visited on source
  tape `i`; unselected tapes visit nothing new.

Generic form of: `emitterBank*`, the `emitterP2*` relocation family,
`clBank*`/`clSlot*` (4A chain), and their chapter-1 analogues in
`Build/Primitives.lean`/`Build/Loop.lean` internals.

### R2. Seam composition

Sequential composition of two controllers at a canonical `Turing.Cfg.ofWords`
seam (Convention.lean's ABI notion): if `M₁` carries seam `c₀` to seam `c₁`
within `T₁` under a first-return cut, and `M₂` carries `c₁` to `c₂` within
`T₂`, the dispatch-glued machine carries `c₀` to `c₂` within `T₁ + T₂ + O(1)`,
with the glue state-sum and dispatch lemmas owned by the combinator. Space
clause: visited sets union, so per-tape space is bounded by the sum of the
parts' per-tape spaces (whether the spec states the sharper per-tape `max` for
disjointly-owned tapes is open decision 12.1). Generic form of the per-batch
dispatch gluing re-proved in every A-chain and emitter batch.

### R3. Catalog promotion, with space costs

Promotion of the remaining audited A-chain privates as public machines with
exact time *and* space costs: transfer (word from tape `i` to tape `j`,
`3|w| + 3`), copy (`3|w| + 3`), clear (`2m + 2`, = P12's engine), compare, and
increment — D6-style promotion, not new proof work, seeded from the named
private families. Additionally, the existing catalog rows (P1-P12, P16-P18)
and the W/L/E combinators are **retro-annotated with space theorems** — new
`spaceUsed` lemmas beside the existing specs, no signature changes, so the
audited statement surface is untouched (additive growth; open decision 12.3 on
doing this here versus lazily per consumer — the amply-support mandate argues
for here).

### Consumers (rule-of-admission check, §4: two named customers per item)

| Consumer | Uses |
|---|---|
| Chapter-1/2 retrofit (backlog §2) | R1 for the bank/relocation families; R2 for the dispatch families; R3 for `clCopy*`/`clCmp*`/`clRead*`/`clCount*` and the `Build/` harvest families |
| Hennie-Stearns `k`→2 conversion ([AB09] §1.7; ch3-4 plan §2.1) | zones as banks (R1), shifts as R3 transfers, seam discipline (R2); the amortization is mathematics on top |
| Two-work-tape universal machine (ch3-4 plan §2.1, §4a) | R1 + R2 throughout; the retrofit pilot; candidate space-bounded variant feeding Thm 4.8 / Ex 4.1 |
| Chapter-4 ARM extensions (ch3-4 plan §2.5: nondeterministic and polynomial-width variants of `LogProg`) | R1/R2 at their `FinTM` compilation boundary; R3 space rows |

### Placement, sequencing, cost

* New files `Build/Embed.lean` (R1) and `Build/Seam.lean` (R2); R3's new rows in
  a new `Build/Catalog.lean` (`Primitives.lean` is already over the size policy;
  final name is open decision 12.2, settled before the spec audit per §9.6).
  Namespace `Turing.FinTM`; order list after `Build/Loop`.
* Process per `workflow.md`: maintainer-serial spec layer (quantifier-sensitive,
  as §10), statement gate, fills as harvest-adaptation batches, fill audit. The
  gate must close before the first chapter-3/4 fill epoch (plan §4a); statement
  phases of chapters 3-4 run in parallel.
* Estimate (campaign points): R1 spec+fill ≈ 10 (the lockstep is the risk
  concentration, L-style), R2 ≈ 8, R3 promotions + space retro-annotation ≈ 12,
  serial spec layer ≈ 6. Total ≈ 36, one mid-size batch equivalent.

### Open decisions (human review; audit verifies, never disposes)

* **12.1** R2 space accounting — **answered (user, 2026-10-08): the sharper
  form.** The spec states per-tape bounds, with the max for disjointly-owned
  tapes (sharpest available; downstream applications may depend on the
  sharpness).
* **12.2** R3's file layout — **answered (user, 2026-10-08): option (a)**, a
  new `Build/Catalog.lean` holding the new rows and the space lemmas for the
  old rows, keeping `Primitives.lean` byte-identical; a backlog item records
  the later refactor toward the symmetrical per-theme layout (option (c)),
  via the D7 split window.
* **12.3** Space retro-annotation — **answered (user, 2026-10-08): the refined
  now-option**: the primitives as realized (P1-P15), wrappers (W1-W3) and the
  loop (L) get `spaceUsed` theorems in this increment; the emitter combinators
  (E1-E4′) stay lazy until a space consumer appears, **and the E3′ stream rows
  P16-P18 ride with that lazy scope** (their only consumers are the emitters —
  scope clarification recorded at skeleton time, 2026-10-08, flagged to the
  §12 statement-gate audit and reversible there if the gate reads the
  original "P1-P18" wording as binding).
* **12.4** R1 emission policy — **answered (user, 2026-10-08): two named
  transformers** (suppressing and forwarding) over a shared private core, so
  each spec stays crisp and downstream applications cite whichever fits.

### Citations (policy.md §2, *Design adaptation*)

The configuration-level design is adapted from — with nothing transcribed —
**Édouard Bonnet's `classical-complexity`** (Lax Archive lax-434930), module
`proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`: `StackProgram`'s
`compile_correct`, `StackRename`'s `rename_executes`/`executes_in_sum` (the
bank-embedding and seam-composition shapes), and the
transfer/clear/copy/for/repeat routine catalog; commit
`0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0; examined 2026-10-05,
different toolchain (Lean 4.33 vs our 4.25) and machine model (TM2-style keyed
stacks vs `FinTM` tapes with heads). Suggested tag: `[Bon26]`. The R-modules'
docstrings and their blueprint entries must carry this citation, alongside the
existing `[Balbach22]` (AFP `Cook_Levin`) for the composition architecture and
the in-repo credits to the colleague modules named above.

### 12.5 Round-1 audit repairs (2026-10-09)

The §12 statement-gate round 1 (`audits/routine-infra-findings.md`: 0
blockers, 4 majors) drove four repairs, landed with the round-2 pack:

* **R1 → the returning embeddings** `embedSilentRetTM`/`embedEmitRetTM`
  (states `S ⊕ Unit`): the closed transformers lose a final halting
  emission to either the halt or a premature seam dispatch — the audit's
  formal trace. The returning flavors execute every source action through
  the halting transition and land in the live anchor `Sum.inr ()`.
* **R2 → general-configuration seam composition**
  (`seamCompTM_run_ofCfg` + first-return and visited forms): the canonical
  `Cfg.ofWords` theorems cannot consume arbitrary frames, displaced
  inactive heads, or accumulated output; the general form starts phase two
  from phase one's returned configuration with only the control state
  replaced.
* **R3 → the fresh-entry/release adapter** `seamReleaseTM`: positive
  calls returning to their own anchor are now seam-consumable (the entry
  action executes unconditionally from a fresh start state).
* **R4 → the threaded-map witness** is re-commissioned as a forwarding
  controller (validate/buffer, emit prefix, forward payload output);
  the received captured-payload machine is refuted as a witness for the
  linear-administration bound.

Scope notes R9 (physical-tape selection is not zone multiplexing) and R10
(loop sibling contracts not exported) are recorded at their definition
sites.

## 13. The zone and virtual-input layer (proposed 2026-10-09, post-§12 close)

**Mandate** (user direction 2026-10-09, at the §12 fill-campaign close —
track A of the two parallel tracks, the other being the chapter-1/2
retrofit): the §12 scope note **R9 promoted**. R9 drew the line at
physical-tape selection — `ι` relocates whole tapes and "the Hennie-Stearns
and universal-machine consumers get their zone/virtual-input representation
layers separately" (`Build/Embed.lean` header). This increment is that
separate layer. It gates the two stage-1 builds (the Hennie-Stearns `k`→2
conversion and the two-work-tape universal machine, plan §2.1/§4b) and is
scoped, like §12, beyond its first consumers: the virtual-input half serves
the `NP^EXPCOM ⊆ EXP` summit and the 12.2c dedup, and the zone half is
shaped so the chapter-1 Robustness conversions can gain **space theorems
additively** (plan §2.7's fallback route to Ex 4.1/Thm 4.8). §12's space
mandate continues: **every item carries a space clause alongside its time
cost** (`Turing.MultiTapeTM.spaceUsed`, work tapes only).

**Evidence.** The virtual-input pattern has now been hand-built four times
over the proved corpus: the A2 forwarding controller's
`a2_mapVirtual`/`a2_mapVirtual_step`/`a2_mapVirtual_run` lockstep (15 of
its 45 privates; both boundary clamps, empty-word case, halt absorption —
all proved), F2A's `f2_splitCountAction`/`f2_splitCount_run`
(virtual *empty* input over preinstalled banks), the universal
interpreter's prefix-input discipline, and the oblivious candidate's
`obliviousVisit` virtual-tape transduction. All four sit on the same public
primitive — `virtualMove`/`VirtualTag`/`virtualNextTag` and
`bufferTape_inputSymbol` (`Simulation.lean`) — and each rebuilt the hosting
and lockstep privately. On the zone side, the in-repo precedents are the
`SingleTape.lean` multiplexing encoding (`SweepCell`/`tapeRow`) and
`ObliviousSetup.lean`'s guide-zone layout with its two-directional run
identities; what does not exist anywhere is a *reusable* zoned carrier with
shift routines. The F2 epoch audit's three optional regression corollaries
(zero-time startup, both virtual-input clamps, setup followed by an
emitting halting step) are adopted here as permanent lemmas of Z1.

**What already exists and is consumed, not duplicated**: the §12 layer
itself (R1/R2 and the catalog rows are the assembly language of every
construction below); `virtualMove`/`VirtualTag` (`Simulation.lean`);
`Turing.actionBits₂` and the `CodeNDTM` two-work-tape serialization
(`NDCodes.lean`, statement-frozen under the closed P3.3 gate) — Z3 builds
the deterministic sibling against the same record format, never a second
serialization; `UnaryTape.lean`; the harvest policy of §8 (reimplement
against the ABI with the original proof as template; audited originals stay
in place until the separately-tracked retrofit/12.2c dedup).

### Z1. Virtual-input hosting (the `a2_mapVirtual` pattern, promoted)

A transformer hosting a machine whose input is a **designated buffered
word** rather than the native input: given a host with an injective tape
selection (R1's `ι`) plus one buffer tape holding `y`, the hosted machine
runs with `y` as its virtual input, buffer head at
`source.inputPos - 1` under a `VirtualTag` boundary discipline. Spec shape:

* **lockstep** — one host step per source step, transported `runFrom`
  identity (the A2 `a2_mapVirtual_run` shape, generalized from its
  two-buffer controller to the R1 selection);
* **clamps** — both boundary clamps hold with **no nonempty-`y` premise**
  (empty `y`: position `0` is the right boundary, `-1` the left; outward
  moves stay, inward moves cross) — the binding A2/F2 audit contract;
* **halt absorption** — the source's halting action executes before the
  host control dies; later times are fixed;
* **emission policy** — suppressed or forwarded, mirroring R1's two modes
  (open decision 12.4 resolves both at once);
* **time** — exact; **space** — coefficient-one containment: each selected
  tape's host visited set is contained in the source's visited set on `y`
  at the same horizon (the R4 ledger shape, proved in `a2_map_space`).

Permanent regression lemmas (audit-adopted): the zero-time startup
instance, the two empty-`y` clamp instances, and the setup-then-emitting-
halt seam. Generic form of: `a2_mapVirtual*` (A2), `f2_splitCount*` (F2A,
the `y = []` specialization), the universal interpreter's input phase, and
the query simulation every oracle-summit machine will need.

**Z1 rider — the R1 selected-tape exports (decision D-R1, user
2026-10-09, from the retrofit inventories, plan §4d).** The three retrofit
inventories independently identified the same R1 API gap: `Embed.lean`
exports no selected-tape field lemmas (`embedSlot_selected`/`_unselected`
are private) and no agreeing-host lockstep, so no old-code R1 consumer can
be proved from the public surface. This statement phase adds, **additively
in `Embed.lean`** (shared-file mechanism, audited under this gate): public
selected-tape projections of `embedSilentCfg`/`embedEmitCfg` (contents and
head of tape `ι i`), and an `ofWords` transport form. Unlocks the blocked
Hardness families (M/N/AM/U, Z/AB/AG — ≈ 300-350 lines) at the next
retrofit window.

### Z5. Machine-agreement transfer (decision D-R3, user 2026-10-09)

A general lockstep-transfer lemma, the `hagree` genre of
`capture_run`/`emit_run` made standalone: two machines over the same tape
count and state type whose transition tables **agree on a set of states**
run identically, configuration for configuration, from agreeing starts for
as long as the run stays inside the agreement set; a guarded variant takes
the agreement hypothesis per reachable state. Natural home:
`Simulation.lean` beside the existing lockstep gadgets (placement open
decision 13.5: Simulation versus a `Build/` module). Customers (rule of
admission): the Loop forwarding host (H3's 14 verbatim re-proved phase
lemmas, ≈ 550 lines, collapse to one transfer — `emLoopHost` agrees with
`loopHost` on every non-body state); the 13 guarded `clSlot_run` agreement
sites in `CookLevin/Hardness.lean`; every future mode-variant host (the
§12 loop hosts' decision/find/emit triplet is exactly this pattern).
Estimate: ≈ 4 points spec + fill; the risk is quantifier placement on the
agreement set, not proof content.

### Z2. Zoned tape carrier (the Hennie-Stearns representation)

The representation of `m` virtual work tapes on **one** physical tape with
amortizable locality: a `ZoneLayout` (level count `ℓ`; per-level zones
`L_i`/`R_i` of capacity `2^i` around a home origin, [AB09] §1.7) and a
carrier predicate `ZoneCfg` relating one physical word to `m` virtual words
plus per-zone fullness states (empty / half / full). The layer owns:

* **the carrier** — `ZoneCfg` well-formedness, read/write-at-home
  contracts (the virtual heads always sit at the physical origin), and the
  cell-encoding convention (open decision 13.2: how `Option Bool` virtual
  cells embed into binary physical cells — paired-cell presence/data
  tracks, with `SingleTape.lean`'s `SweepCell` encoding as the precedent);
* **the shift routines** — per-level `shiftIn`/`shiftOut` rebalancing
  rows with **exact** costs `O(2^i)`, assembled from R3
  transfer/copy/clear via R2 seams, each with its space row (visited cells
  within the touched zones);
* **the cardinality lemmas** — visited-set bookkeeping for multiplexed
  tapes: physical space bounded by the sum of touched zone extents, the
  piece the Robustness space annotation (Z4) consumes.

Explicitly **on top, not inside**: the `2^i`-fullness invariant across a
run, the amortized `O(T log T)` charge, and the simulation theorem itself —
those are the Hennie-Stearns consumer's mathematics (plan §2.1), as the
§12 precedent kept the loop ledgers out of the loop host. Scope note:
Z2 is sized for the H-S discipline (one zoned tape + one scratch tape);
a general `k`→`k'` conversion is not in scope.

### Z3. Two-work-tape codes (the deterministic `actionBits₂` sibling)

The deterministic code layer currently covers only the one-work-tape
binary normal form (`EffectiveMachineCode`/`UniformMachineCode`,
`Encoding.lean`), which is why Thm 3.1 arrives at `f²` (plan §2.1). Z3
extends it: a deterministic two-work-tape code scheme over the
**same `actionBits₂` record format** as `CodeNDTM` (one branch instead of
two), with the `CodeParser` extension and the `UniformMachineCode`-style
uniform-decoding clause (the P3.2 lesson: variable-code consumers need the
uniformly-timed form). The two-work-tape **universal machine itself** is
the stage-1 consumer build, not part of this layer; Z3 ships the codes it
reads. Space rows on the parser rows from the start.

### Z4. Space annotation for the Robustness conversions (consumer-driven)

Additive `spaceUsed` theorems for the chapter-1 conversions
(`one_work_tape`, the alphabet reduction) via Z2's cardinality lemmas — no
signature changes, the audited surface untouched (the R3 retro-annotation
precedent). This is plan §2.7's fallback route to the space-efficient
universal (Ex 4.1, Thm 4.8). **Design-time obligation, recorded here**: at
the Z1-Z3 spec phase, assess whether the two-work-tape universal carrying
Z1/Z2 space rows yields Ex 4.1 directly; the answer (and hence whether Z4
is needed at all, and at which strength) is recorded before the statement
gate, so the chapter-4 risk register (§6 summit 1) is settled either way.

### Consumers (rule-of-admission check, §4: two named customers per item)

| Item | Customers |
|---|---|
| Z1 virtual-input hosting | the two-work-tape universal (stage 1); the `NP^EXPCOM ⊆ EXP` summit's query simulation; the 12.2c dedup of `a2_mapVirtual*`/`f2_splitCount*`; the P3.3 universal-NDTM fill's code/input discipline |
| Z2 zoned carrier + shifts | the Hennie-Stearns `k`→2 conversion (plan §2.1); the Robustness space annotation (Z4); the Ex 1.6 oblivious sharpening (recorded stretch goal, `Robustness/Oblivious.lean`) |
| Z3 two-work-tape codes | the two-work-tape universal; the Thm 3.1 re-derivation at `f log f` (Hydroxyi's diagonal argument over the new codes) |
| Z4 space annotation | Thm 4.8/Ex 4.1 fallback (plan §2.7); `L ⊊ PSPACE`/space-hierarchy fills (P4.3) if the universal route stalls |

### Placement, sequencing, cost

* New files `Build/VirtualInput.lean` (Z1) and `Build/Zone.lean` (Z2),
  namespace `Turing.FinTM`, order list after `Build/Catalog`; Z3 as a new
  `TuringMachine/Codes2.lean` beside `Encoding.lean` (placement open
  decision 13.3: a new file versus extending `Encoding.lean` — the frozen
  audited surface of `Encoding.lean` argues for the new file); Z4 lands
  additively in the `Robustness/` files through the shared-file mechanism,
  flagged for its own audit.
* Process per `workflow.md`, the §12 precedent verbatim: maintainer-serial
  spec layer (quantifier-sensitive), statement gate by external audit,
  fills as briefed batches with exclusive ownership, epoch-boundary fill
  audit. The gate must close before the H-S/two-tape-universal builds
  start; chapter-3/4 fill briefs written while this layer is open simply
  do not cite it (the EXPCOM brief prefers Z1 only if Z1 is closed).
* Estimate (campaign points): Z1 ≈ 8 (harvest-grade — the lockstep is
  proved four times over; the risk is quantifier hygiene, not proof
  content), Z2 ≈ 14 (genuinely new; the carrier predicate is the risk
  concentration, L-style), Z3 ≈ 6 (format fixed by `actionBits₂`), Z4 ≈ 6
  (retro-annotation against Z2's lemmas). Total ≈ 34, between the §12
  statement layer and one fill epoch.
* **Citation duty** (binding, the 2026-10-06 guideline and the 2026-10-08
  citation-audit row): the design adapts [AB09] §1.7 (Hennie-Stearns) and
  Exercise 1.5/1.6; the §12 duty extends here — Édouard Bonnet's
  lax-434930 `classical-complexity` (Apache-2.0, commit `0c084031…`) is
  cited in this addendum, the module docstrings, and the blueprint entries
  wherever its stack-machine routine catalog informed a row's shape; no
  external code is imported or transcribed.

### Open decisions (13.x, for the user at spec time)

1. **13.1 Zone discipline**: zones-with-fullness (the [AB09] §1.7 layout,
   proposed) versus plain interleaving (simpler carrier, no amortized
   locality — insufficient for H-S alone, but cheaper if Z2's only
   customer were Z4). Proposed: zones; interleaving is not built.
2. **13.2 Cell encoding**: how `Option Bool` virtual cells embed in binary
   physical cells (paired presence/data cells proposed; `SweepCell` as
   precedent).
3. **13.3 Z3 placement**: new `Codes2.lean` (proposed) versus extending
   the frozen `Encoding.lean`.
4. **13.4 Z1 mode shape**: one transformer with an emission-mode parameter
   versus two transformers — inherits open decision 12.4's resolution.
5. **13.5 Z5 placement**: the agreement-transfer lemma in `Simulation.lean`
   beside the lockstep gadgets (proposed) versus a `Build/` module.

### 13a. Decisions resolved; epoch structure (user, 2026-10-09)

All five open decisions resolved as proposed, with one rename:
**13.1** zones-with-fullness (interleaving is not built); **13.2** paired
presence/data cells (`SweepCell` precedent); **13.3** a new file, renamed
**`TuringMachine/Codes2Tape.lean`** so the "2" reads as *two-tape*;
**13.4** Z1 inherits 12.4's resolution (a silent/emit transformer pair over
one shared core); **13.5** Z5 lands in `Simulation.lean`.

**The statement phase runs in two tranches, each with its own gate:**

* **A-S1 — the virtual-input half**: Z5 (the agreement transfer,
  `Simulation.lean`, additive), Z1 (`Build/VirtualInput.lean`, new), and
  the Z1 rider (the R1 selected-tape exports, `Embed.lean`, additive via
  the shared-file mechanism). Rationale: harvest-grade risk (the lockstep
  is proved four times over; the rider's facts are proved privately), and
  its consumers are the *near-term* ones — the blocked retrofit R1
  families, the 12.2c dedup, the Loop H3 collapse, the EXPCOM summit.
* **A-S2 — the zone half**: Z2 (`Build/Zone.lean`), Z3
  (`Codes2Tape.lean`), Z4 (the Robustness space annotation). Rationale:
  Z2's carrier predicate is the genuine design risk and deserves an
  undiluted gate; its consumers (Hennie-Stearns, the two-tape universal)
  sit one stage later. The Z4 design-time obligation (does the two-tape
  universal's space bonus yield Ex 4.1?) is discharged in the A-S2 pack.

The canonical Z1 shape (spec-time refinement, recorded before drafting):
the transformer is defined on exactly `1 + M.k` work tapes — the buffer
first, the payload bank after it — and **relocation is not baked in**:
a consumer needing the buffer or bank elsewhere composes with R1. One
shared hosting core; `silent`/`emit` flavors per 12.4; the tag lives in
the transported control state (the `a2_MapState.run q tag` precedent).

### 13b. A-S1 gate close (2026-10-09, after `audits/vhost-infra-findings.md`)

Round-1 **PASS, 0 blockers / 0 majors / 2 minors**; loop summary
`audits/vhost-infra-resolutions.md`. Minor sweep recorded here per the
audit's proposed fix (A-S1-2): the Z1 rider's promised **`ofWords`
transport form is supplied by specialization** of the four delivered
selected-tape projections (instantiate `c := Cfg.ofWords …`); no
separately named specialization is exported now — if a consumer wants the
whole-configuration identity (with its frame, capture, head, and output
parameters spelled out), it is commissioned on need at the 12.2c window.
A-S1-1 (the pack under-counted the definitions: eight with
`MultiTapeTM.AgreeOn`, 23 audited declarations) is acknowledged as a pack
erratum; shipped packs stay verbatim. The audit's four recommended sanity
exports (initial-tag validity + `q₀`-independence, fixed-parameter
transport injectivity, native-head constancy for arbitrary host
configurations, named boundary/seam specializations) are **adopted as
optional permanent lemmas of the A-S1 fill brief** — offered, not
required. The audit's Z5 composition-of-responsibilities reading is
affirmed and binding on retrofit consumers: Z5 equates runs on one
carrier; heterogeneous `clSlot_run`-style sites first transport
(R1 + state renaming), then agree — a public guarded
configuration-transport theorem is a possible later export, not promised.

### 13c. A-S2 round-1 repairs (2026-10-09, after `audits/zone-infra-findings.md`)

The A-S2 statement gate returned **FAIL: 1 blocker, 1 major, 2 minors**;
repairs landed with the round-2 pack:

* **A-S2-1 (blocker) → the inward room premise removed and the wrappers
  split.** The spec had one shared room hypothesis on both shift
  directions; inward shifts *remove* donor cells, so a full donor — the
  exact classical case — was illegal, and the audit's full-chain family
  showed the delivered interface forcing `Ω(T²)` behavior. Repair:
  `zoneShiftInW` carries no room condition; `zoneShiftOutW`'s receiving
  room moved **inside its guard**; the contents wrappers are the
  hypothesis-free `zoneShiftIn`/`zoneShiftOut`; the head steps gain the
  guarded-total `zoneMove`; and the audit's required gate material landed —
  the full-donor regression (`zoneShiftInW_full_donor`) and the cascade
  statements (`zoneCascadeRight` with its represented-word, length, and
  geometric-cost lemmas), whose proofs adopt the audit's schedule analysis
  as the binding route. The rows now realize the **total guarded
  operation, identity branch included**.
* **A-S2-2 (major) → the Z4 one-tape sketch replaced.** The received
  `sweepTM` grows its window unconditionally (the audit's stationary-head
  scanner refutes it as a witness); the statement stands, and the binding
  route is now a **demand-grown** sweep witness with the audit's
  union-of-origin-intervals bound, interleaving factor, and the
  all-`Γ'`-inputs retraction (empty-alphabet and zero-tape cases named).
* **A-S2-5 (note, adopted) → the Ex 4.1 assessment stands as a
  *design-level* verdict, not an implementation discharge**: the stage-1
  universal must specify a space-accounted input interface (native/suffix
  access or an accounted buffer — a materialized input copy costs
  `Ω(|x|)` work cells, absent from the sketched ledger) and a parser with
  its own space ledger; the uniform scheme (Z3), not an arbitrary
  effective scheme, is what a space-accounted canonizer route would use.
* Minors: the pack's definition count corrected (22, not 25; inventory in
  the findings); the module's export list and the guard semantics
  docstrings corrected in place (A-S2-4).
```

## ===== audits/zone-infra-pack.md =====

```
# External audit pack — zone/virtual-input layer (§13), statement gate, tranche A-S2

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4b,
track A; design `machine-library-design.md` §13/§13a/§13b). Tranche A-S1
(the virtual-input half) closed in one round
(`audits/vhost-infra-resolutions.md`); this round audits **A-S2, the zone
half**: Z2 (`Build/Zone.lean`, new — the Hennie-Stearns carrier), Z3
(`Codes2Tape.lean`, new — deterministic two-work-tape codes), and Z4
(three space-annotation statements appended to
`Robustness/{AlphabetReduction,SingleTape}.lean` via the shared-file
mechanism). The gate closes on zero blockers and zero majors
(`workflow.md` §3), failure-mode-5 rule in force.

Audited at commit `c43f3a53` (branch `complexity/arora-barak-ch3-4`; the
A-S2 spec commit is `ca2bb11b`). **The audit object is the statement
surface**: 25 new definitions/structures, **18 `sorry`d declarations
(21 sorry warnings — three `Zone.lean` definitions carry sorried capacity
proof fields)**, and 3 skeleton-time proofs (`zoneCellOf_bits`,
`zoneBase_succ`, `MachineCode2.decode_encode`). Z2 is the campaign's
single highest-risk spec (§13a): assume it is wrong until your own
arithmetic says otherwise.

## Brief for the auditor

1. **Blind-restate every definition** from its body before its docstring,
   and **re-derive the layout arithmetic yourself**: `zoneCapacity i =
   2·2^i`, `zoneBase i = 2·(2^i − 1)` (verify the telescope), `zoneIndex`
   via `Nat.log2 (s / 2 + 1)` (verify the floor-division sandwich claimed
   by `zoneIndex_eq_iff` at even and odd `s`, at `s = 0`, and at zone
   boundaries), the home/slot-to-cell maps including the **documented
   left/right presence-data asymmetry**, and the physical extent bound of
   `zoneTape_blank_outside` (`|c| > 2·zoneBase ℓ + 1` — check both signs
   and `ℓ = 0`). Then `ZoneContents` (note what it does **not** carry),
   `zoneTape`, `zoneSlot`, `zoneSide`, the shift ops, the head-step ops
   (including the `headI`-on-empty convention: popping an empty `R_0`
   yields the blank virtual cell), `Code2TM`/`serialize` (compare
   record-for-record against the attached `CodeNDTM.serialize`: 27 vs
   2·27 records per state, same `actionBits₂`), the three scheme
   structures (compare against the attached `Encoding.lean` and
   `EXPCOM.lean` mirrors), and the three Z4 statements.
2. **Assess the spec-time design refinements** (recorded in §13a and the
   module docstring; each is a deviation from the textbook's surface
   presentation and needs a verdict):
   (a) **pairwise shifts** — level `i` moves `2^(i−1)` cells between
   zones `i − 1` and `i` only, with the classical multi-level rebalance
   as a cascade of these ops; verify the honesty lemmas
   (`zoneSide_shiftInW/OutW`) are true *structurally* (adjacent zones in
   the inner-first concatenation) and that a cascade of pairwise ops can
   reproduce the [AB09] §1.7 discipline with the same geometric amortized
   cost — if the pairwise decomposition loses the amortization, that is a
   **blocker**;
   (b) **fullness excluded from the carrier** — the `{empty, half, full}`
   invariant is the consumer's; check no sorried contract silently needs
   it (the shift rows' guards and `hroom` hypotheses are the suspect
   spots);
   (c) **one shift machine per direction and side, level in unary on the
   scratch tape** — verify the row statements quantify correctly over
   `ℓ`, `i`, and contents, that the budget `c·(2^i + i + 1)` is the right
   shape for the amortization, and that the visited-interval clause
   (`±(2·zoneBase (i+1) + 2)`) actually contains every cell a level-`i`
   shift must touch, scratch staging included;
   (d) the `zoneShift` wrapper's **dependent `hroom` hypothesis** and its
   guard semantics ("realizes the pure op exactly where the guard fires")
   — is the contract honest, or can a row be instantiated outside its
   guard to claim a false transformation?
3. **Argue each of the 18 sorried statements true as literally stated**,
   or exhibit the problem (boundary cases: `ℓ = 0`, `i = 1`, empty zone
   words, exactly-full zones, `s` at `zoneBase` boundaries, even/odd
   cells, blank home, `numStates = 0`, `t = 0`). The three `Zone.lean`
   defs with sorried capacity fields (`zoneShift`, `zoneMoveRight`,
   `zoneMoveLeft`) need their field obligations checked for provability
   under their hypotheses — a false capacity field is a **blocker** (the
   def is then uninhabitable as specified).
4. **Z3 fidelity**: the serialization's fixed enumeration order against
   `CodeNDTM.serialize` with the choice bit removed; the
   `UniformMachineCode2` clauses against `UniformMachineCode` (the
   deterministic `decode`'s `toFinTM`, the joint polynomial, both
   branches); the sketches' claimed constants (27 records per state, the
   halved minimum-length guard) — the round-1 miscount lesson of the ND
   gate (finding 3 there) applies squarely here.
5. **Z4 shapes**: all three statements carry `space ≤ c·(S + 1)` at
   **every** horizon with coefficient-constant form; verify the sweep
   argument (union of origin-containing intervals bounded by the sum of
   cardinalities), the block-coding argument, and that the composed
   `one_work_tape_binary_spaceUsed` is literally the plan §2.7 fallback
   deliverable. Flag any missing hypothesis (monotonicity of `S`? the
   statements avoid it deliberately — check they can).
6. **The Ex 4.1 design-time obligation** (§13 Z4; recorded to be
   discharged in this pack): the maintainer's assessment is below —
   sanity-check its reasoning and flag disagreements as notes.
7. **Debt screen (failure mode 5)**: the tranche must add no copies; the
   ledger line is below. `Zone.lean` deliberately does **not** copy the
   `SweepCell` machinery it cites as precedent — verify.
8. Report in the standard table and severity scale; propose missing
   machine-checkable sanity statements (candidates to weigh: a
   `zoneTape`-injectivity-from-contents lemma; `zoneSide` length
   arithmetic; a named `zoneIndex` computation table for small `s`; a
   `Code2TM.serialize`-length lemma mirroring the received grammar
   bounds).

## The Ex 4.1 design-time assessment (maintainer; the §13 Z4 obligation)

Plan §2.7 flags Thm 4.8's space-efficient universal (Ex 4.1) as chapter
4's largest single risk, with two candidate routes. Assessment at A-S2
spec time: **the two-tape universal route is plausible and preferred; Z4
is retained as the audited fallback.** Reasoning: the stage-1 universal
over `Code2TM` codes hosts the coded machine's two work tapes on two
physical tapes (no tape reduction inside the universal — the Z1
virtual-input layer carries the input discipline), so its work space is
the hosted space plus the table/clock administration,
`O(S + |α| + log t)` — Ex 4.1 grade — *provided* the stage-1 design
carries the Z1/Z2 space rows through its interpreter loop, which is
exactly what the §12/§13 space mandate makes routine. The fallback
(`one_work_tape_binary_spaceUsed` + the received conversions) is
independent of the universal and additionally serves the chapter-1
retrofit surface, so its three statements are kept and audited now; the
stage-1 design review selects the primary route, and this obligation is
thereby **discharged** (the risk register no longer waits on an unmade
assessment).

## Known deviations and declared anomalies (verify they are benign)

* The three skeleton-time proofs (flagged, rfl/arith-grade).
* The Z4 statements re-sorry two closed audited files (the shared-file
  mechanism, flagged); their existing audited surfaces are untouched —
  verify additivity from the attached sources.
* `SingleTape.lean` crosses the size line (1,029); justification recorded
  in the plan's decision log (48 additive Z4 lines; splits belong to D7).
* `Codes2Tape.lean` imports `NDCodes.lean` (a chapter-3 statement surface)
  solely for `actionBits₂`/`workPair` — the recorded
  "never a second serialization" decision; flag if anything else leaks
  through that import.

## Repository-side attestations (verify or challenge)

* Elaboration: `Build/Zone`, `Codes2Tape`,
  `Robustness/{AlphabetReduction,SingleTape}`, and the `TuringMachine`
  facade all check at exit 0, zero `error:` lines, fresh `.olean`s; the
  tranche adds exactly 21 sorry warnings over 18 sorried declarations
  (13 + 2 + 3).
* Style lint: 0 FAIL over both directories; every sorry carries a literal
  **Proof sketch**; the one new size WARN is justified as above.
* **Duplication ledger (failure mode 5): new copies — none.**
* The A-S1 fill (11 targets) is concurrently dispatched and owns
  `Build/VirtualInput.lean` + `Simulation.lean`; this tranche touches
  neither.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md` (including failure mode 5);
findings verbatim into `audits/zone-infra-findings.md`; the gate closes on
zero blockers and majors, after which the A-S2 fill epoch dispatches and
the stage-1 builds (Hennie-Stearns + the two-tape universal) have their
complete statement substrate.
```

## ===== audits/zone-infra-findings.md =====

```
# §13 A-S2 statement-gate audit

**FAIL — 1 blocker, 1 major, 2 minors. The gate must remain open.**

Audited: the 13 attachments in `zone-infra-bundle.md`, attributed by the pack to `c43f3a53` (spec commit `ca2bb11b`). Audit date: 2026-10-09. Bundle SHA-256: `58e86447461c2f68c02fb616b90059ba845f5623add84adac7c14a519385c2d0`.

The blocker concerns the delivered inward-shift interface and the claimed Hennie–Stearns amortization. The major concerns a false claim about the existing one-tape witness. **Neither finding is a counterexample to an embedded capacity obligation; those obligations are provable.** The existential theorem statements admit the mathematical constructions described below, but the advertised consumer interface and binding proof route need repair before filling.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| A-S2-1 | **blocker** | `Build/Zone.lean` · `zoneShift`, `FinTM.exists_zoneShiftInTM`; module design | The delivered shifts can reproduce the classical rebalance with its geometric amortized cost. | Inward shifting requires upper-word length plus `2^(i-1)` to fit, although it removes cells from that word. A full donor therefore cannot be read inward. Already at `ℓ=2`, right lengths `(0,4)` and left lengths `(2,0)` satisfy the classical fullness/complement invariant but admit no legal shift that changes `R₁`. With more levels, the full-chain example below forces a level-`m+1` transfer during an index-1 classical shift; a four-step cycle repeats this cost, giving quadratic rather than logarithmic-overhead behavior for exact classical rebalancing. | Remove the room premise from the inward row. Split the wrappers, or make `zoneShift`'s room obligation conditional on `inward = false`. Retain the outward premise. Add a full-donor regression and the two-pass cascade/charge lemma below before closing this gate. |
| A-S2-2 | **major** | `Robustness/SingleTape.lean` · `one_work_tape_spaceUsed`, proof sketch; dependent composite | The received `sweepTM` sweeps only source-visited intervals and therefore supplies the new space bound. | Its `.growLeft` and `.growRight` phases unconditionally extend the window every source step. For a one-work-tape machine that scans its native input while keeping its work head at zero, source space is always 1, but the received simulator reaches `-(n+2)` on length-`n` input. No constant bounds this by `c*(1+1)`. See the explicit ledger below. | Replace the sketch with a space-preserving, demand-grown sweep construction, reusing/refactoring existing infrastructure without copying it. Account for the factor from interleaving and for **all target-alphabet inputs**, as the statement requires. The existential statement can remain unchanged; a new witness/proof route is necessary. |
| A-S2-3 | minor | Audit pack · inventory | There are 25 new definitions/structures. | The supplied surface has **22**: 16 in `Zone.lean`, 6 in `Codes2Tape.lean`, none in the Z4 appendices. The 18 sorried declarations, 21 `sorry` terms, and 3 skeleton-time proofs do agree with the source inventory. | Acknowledge a pack erratum; retain the shipped bundle verbatim. Use the inventory below for fill ownership. |
| A-S2-4 | minor | `Build/Zone.lean` · machine-row docstrings and main-results list | The rows “must not be invoked” outside the pure guards; listed exports name the actual API. | Neither row assumes lower-zone emptiness/fullness. Its equality instead requires the machine to implement the **identity** when that guard fails. The main-results list also names absent `zoneShiftIn`/`zoneShiftOut` and `zoneSide_shiftIn`/`zoneSide_shiftOut`, and omits `MultiTapeTM` from the interval-cardinality export. | State that the machine realizes the total guarded operation, including its identity branch. Correct the export names to the `W` operations, `zoneShift`, and `MultiTapeTM.spaceUsedByTape_le_card_Icc`. |
| A-S2-5 | note | Pack · Ex 4.1 design assessment; design §13 Z1/Z4 | The primary route is plausible, but the assessment does not establish its proposed space ledger. | Z1 hosts a **buffered virtual input** on an extra work tape. Materializing or fully traversing a copy of `x` costs `Ω(length(x))` visited work cells, which is absent from `O(S + length(α) + log t)`. The selected-payload-tape bound does not pay for that buffer. Also, an arbitrary effective scheme has no code-length space bound on its canonizer. | Keep this as a completed design assessment, not a discharged implementation proof. The stage-1 review must specify native/suffix input access or another space-accounted input interface, and a concrete parser with its own space ledger. If an input copy is intended, its length must appear or be justified by a hypothesis. |
| A-S2-6 | note — no findings | `Build/Zone.lean` · layout, carrier, pure list identities, six capacity fields | Layout and local data operations are consistent as literally stated. | Independent telescope, logarithm sandwich, signed-cell calculation, and capacity proofs are below. Fullness is not needed for any of these local facts. | No repair beyond A-S2-1/A-S2-4. Add the suggested sanity lemmas. |
| A-S2-7 | note — no findings | `Build/Zone.lean` · both machine existence statements, considered literally | A uniform two-work-tape implementation with unary level and the stated local budgets is possible on the stated domain. | The level is an input to one fixed machine, not a finite-control parameter. Constantly many bounded scans and staged transfers suffice; the data interval contains both affected zones, and scratch has its separate space clause. False pure guards must take the identity branch. | Preserve the uniform quantifier order and geometric budget when repairing the inward domain. |
| A-S2-8 | note — no findings | `Codes2Tape.lean` · all six definitions and both existence statements | Deterministic serialization and scheme laws faithfully mirror the attached references. | Enumeration matches `CodeNDTM.serialize` after deleting only the outer choice enumeration and its transition argument. The shared record has minimum length 13, hence the table guard is `351*(numStates+1)`, versus 702 for ND. The uniform record matches `UniformMachineCode` field-for-field after type/name substitution. | Add the exact serialization-length and parser-guard lemmas. Only the **table term**, not the header-inclusive length, halves. |
| A-S2-9 | note — no findings | Z4 · alphabet reduction, statement shapes, composition | All-time coefficient-constant bounds need no monotonicity assumption on `S`. | Every simulation horizon is compared with a source horizon on an input of the **same length**, and `hS` covers every such horizon. Fixed block width, finite tape count, and additive boundary allowances are absorbed into a single coefficient. The binary composite has the promised fallback shape. | Retain the shapes; resolve A-S2-2 before claiming the composite has a proved route using the received sweep. |
| A-S2-10 | note — no findings | Tranche · debt screen | No new copied proved machinery is present in the supplied increment. | `Zone.lean` contains no copied `SweepCell`/sweep-controller family. Z3 directly reuses `actionBits₂` and `workPair`; its type-specific scheme mirrors are the commissioned surface, not duplicated proof infrastructure. The Z4 appendices contain statements, not private copies. | No human debt acknowledgment is required for this supplied increment. Apply the same screen to the replacement Z4 witness at fill time. |
| A-S2-11 | note | Pack · execution, freeze, and additivity attestations | Source checks are distinguishable from maintainer execution claims. | I verified attachment/declaration counts, the locations of the Z4 appendices, absence of earlier `sorry` terms in the two attached Robustness files, and the recorded size exception. The packet contains no pre-change blobs/diff or sweep logs, and this environment has no `lean`/`lake`. | Elaboration, fresh `.olean`s, lint, facade reachability, and byte-identical historical prefixes remain maintainer attestations. Attach the two pre-Z4 blobs or their diff if independent byte-level freeze verification is required. |

## Blind restatements and inventory

I extracted the attachments, removed Lean comments with a nested-comment/string-aware pass, and recorded these readings **before** reading declaration docstrings. The subsequent docstring comparison found the discrepancies identified above.

| Definition/structure | Body-derived meaning and comparison |
|---|---|
| `zoneCellBits` | An optional bit becomes its presence bit and its data bit, with false data for absence. Faithful. |
| `zoneCellOf` | False presence decodes to absence; true presence decodes to the supplied bit. Faithful; it need not invert all four bit pairs. |
| `zoneCapacity` | Level `i` has capacity `2*2^i` virtual cells on each side. Faithful to the resolved layout. |
| `zoneBase` | Level `i` begins at virtual slot `2*(2^i-1)`, with natural subtraction. This is the sum of preceding capacities. |
| `zoneIndex` | The owning level is `⌊log₂(⌊s/2⌋+1)⌋`. The floor operations are essential and correct. |
| `ZoneContents` | One optional home bit and two `Fin ℓ`-indexed word families, each bounded above by its level's capacity. No fullness, cross-side balance, lower-zone nonemptiness, implicit blank padding, or simulation invariant is stored. This exclusion is explicit and locally sound. |
| `zoneSlot` | An in-range level lookup followed by a word lookup at the slot's offset from that level's base. Outer `none` means an unoccupied slot; `some none` means an occupied virtual blank. |
| `zoneTape` | Home presence/data are at 0/1. Right slot `s` has presence/data at `2s+2`/`2s+3`; left slot `s` has presence/data at `-2s-2`/`-2s-1`. Occupied slots always occupy both physical cells, including virtual blanks. Faithful, including the reversed offset parity on the left. |
| `ZoneContents.empty` | Blank home and empty words on both sides at every existing level. Its physical tape still has two nonblank false bits at home. |
| `zoneSide` | Concatenate the zone words in increasing level order; no padding or reversal is inserted. Faithful. |
| `zoneShiftInW` | Identity unless `1≤i<ℓ` and the lower word is empty. Otherwise put the upper word's first `2^(i-1)` cells, or all available cells if fewer, in the lower zone and retain its suffix upstairs. |
| `zoneShiftOutW` | Identity unless `1≤i<ℓ` and the lower word is full. Otherwise retain its first `2^(i-1)` cells and prepend its remaining half to the upper word. The raw family operation itself does not enforce target capacity. |
| `zoneShift` | Keep home and the opposite side; apply the chosen raw operation to the selected side (`true` means right). Require selected upper length plus `2^(i-1)` to fit **even for inward or inactive operations**. The fields are inhabitable, but this excess domain restriction causes A-S2-1. |
| `zoneHomeWrite` | Change only home. The frame theorem says that only the two home cells can change, not that either must change. |
| `zoneMoveRight` | Push old home onto `L₀`; pop `R₀` into home and remove its head. On empty `R₀`, `headI` is `none`, the default for `Option Bool`. Require room on the pushed side. This is a genuine virtual move only under the consumer's refill/blank-extension condition. |
| `zoneMoveLeft` | The same operation with sides exchanged and the corresponding room hypothesis. |
| `Code2TM` | A deterministic Boolean machine with exactly two work tapes and state type `Fin (numStates+1)`. Thus `numStates=0` still supplies one state. |
| `Code2TM.toFinTM` | Bundle that same transition system with tape count 2 and the same state type. |
| `Code2TM.serialize` | Pair-frame binary `numStates` with unary initial state followed by transitions ordered by state, input read, work-0 read, work-1 read. Each read uses `[none, some false, some true]`; each record uses the existing `actionBits₂`. |
| `MachineCode2` | Total encoder and decoder, with exact machine recovery after any finite all-true padding of an encoded machine. Padding lengths are distinct, so each machine has infinitely many codes; the zero-padding case also forces encoding injectivity. |
| `EffectiveMachineCode2` | Add a finite deterministic canonizer and an arbitrary length-only running-time bound for producing the fixed serialization of `decode α`. No polynomial canonization bound is present. |
| `UniformMachineCode2` | Add one finite deterministic bounded-acceptance decider, with a single coefficient/degree bounding time jointly in code length, input length, and numeric deadline. Its complementary branches decide exact halting output `[true]` by that deadline versus its negation. It is not a space-universal or linear-time-universal contract. |

| File group | Definitions/structures | Sorried declarations | Literal `sorry` terms | Skeleton-time proofs |
|---|---:|---:|---:|---:|
| `Zone.lean` | 16 | 13 | 16 | 2 |
| `Codes2Tape.lean` | 6 | 2 | 2 | 1 |
| Z4 appendices | 0 | 3 | 3 | 0 |
| **Total** | **22** | **18** | **21** | **3** |

The three sorried definitions are included in both the definitions and sorried-declarations columns. There are 40 distinct new declarations: 22 definitions/structures, 15 sorried theorems, and 3 proved theorems.

## Independent layout and capacity arithmetic

The geometric sum is

\[
\sum_{j<i}\operatorname{zoneCapacity}(j)
=2\sum_{j<i}2^j
=2(2^i-1)
=\operatorname{zoneBase}(i).
\]

Since `2^i≥1`, the natural subtraction loses nothing. Consequently

\[
\operatorname{zoneBase}(i+1)-\operatorname{zoneBase}(i)
=2(2^{i+1}-2^i)=2^{i+1}
=\operatorname{zoneCapacity}(i).
\]

For the index lemma, write `s=2r+ε` with `ε∈{0,1}`. Both base endpoints are even, so

\[
\begin{aligned}
2(2^i-1)\le 2r+\varepsilon<2(2^{i+1}-1)
&\iff 2^i-1\le r<2^{i+1}-1\\
&\iff 2^i\le r+1<2^{i+1}\\
&\iff \lfloor\log_2(r+1)\rfloor=i.
\end{aligned}
\]

Here `r+1≥1`, so there is no logarithm-at-zero case. In particular:

| Slots `s` | 0–1 | 2–5 | 6–13 | 14–29 | 30–61 |
|---|---:|---:|---:|---:|---:|
| `zoneIndex s` | 0 | 1 | 2 | 3 | 4 |

At `zoneBase i` the answer is `i`; for `i>0`, at `zoneBase i-1` the answer is `i-1`. At the upper boundary minus one it is still `i`. These facts handle both parities.

For right slot `s`, substituting `c=2s+2` or `2s+3` yields `n=2s` or `2s+1`, hence presence then data. For the left, `c=-2s-2` yields `n=2s+1` and presence, while `c=-2s-1` yields `n=2s` and data. Thus every integer is exactly a home cell or one member of one side's slot pair; there is no overlap.

The last possible slot is `zoneBase ℓ-1`. Its physical cells give the sharper containing interval

\[
[-2\operatorname{zoneBase}(\ell),\;2\operatorname{zoneBase}(\ell)+1].
\]

The stated symmetric bound is therefore safe, with one extra blank cell allowed on the left. At `ℓ=0`, only home cells 0 and 1 can be nonblank; the strict hypothesis `1<|c|` is sufficient. A blank home is represented by `(some false,some false)`, not physical blanks.

For a valid shift level, the lower capacity is `2*2^(i-1)`. Inward transfer gives lower length at most `2^(i-1)` and never increases upper length. Outward transfer from a full lower word gives exactly

\[
\begin{aligned}
|\text{new lower}|&=2^{i-1},\\
|\text{moved suffix}|&=2\cdot2^{i-1}-2^{i-1}=2^{i-1},\\
|\text{new upper}|&=2^{i-1}+|\text{old upper}|\le\operatorname{zoneCapacity}(i).
\end{aligned}
\]

The last inequality is precisely the necessary **outward** room premise. Disabled guards leave all lengths unchanged. The other side is unchanged. For either head move, the pushed word grows by exactly one, covered by its premise, and the popped word's tail cannot grow. These arguments discharge all six embedded capacity fields, without fullness assumptions.

## A-S2-1: locality failure and repair

The source comparison used the available [AB09 §1.7 excerpt](https://kubokovac.eu/zlozitost/arora.pdf), which states that stable zones are empty/half/full, paired occupancies sum to capacity, and a head move rebalances through the first nonempty donor zone. The following counterexamples and charge calculation are independent derivations from those rules and the attached definitions.

**Finite dead end.** Set `ℓ=2`, with right word lengths `(0,4)` and left lengths `(2,0)`. Fill the right outer word with, for example, four `some true` cells and take blank home. Each side fits, every zone is empty or full, and paired lengths are 2 at level 0 and 4 at level 1. A right head move needs the first cell of `R₁`, but the inward row at `i=1` requires

\[
4+2^0\le4,
\]

which is false. Outward shifting into `R₁` has the same impossible room premise. There is no level 2. Every legal provided shift therefore leaves `R₁` unchanged; home writes and head moves only access home/level zero. Calling `zoneMoveRight` directly would read blank instead of the required `some true`.

This is a domain defect, not an inconsistent capacity proof: `zoneShiftInW 1` itself would safely transform right lengths `(0,4)` into `(1,3)`.

**An extra outer zone does not preserve the claimed amortization.** For arbitrary `m≥1`, take `ℓ=m+2` and stable right lengths

\[
|R_0|=0,\qquad |R_j|=2^{j+1}\ (1\le j\le m),\qquad
|R_{m+1}|=2^{m+1},
\]

with left lengths complementary to the capacities. For each `1≤i≤m`, the full upper word makes the common room premise false. At level `m+1`, the lower word is full and the upper word half-full, so an outward shift is legal. Thus the **only initially enabled nonidentity right-side shift is level `m+1` outward**.

The intended right move has classical index 1, but obtaining any donor data via these rows first requires touching level `m+1`. That transformation changes physical cells at distance `Ω(2^m)` from home. A unit-speed physical head starting and ending at home must spend `Ω(2^m)` steps.

Now perform virtual directions `right, left, left, right`, restoring the classical representation after each move. Right lengths at levels 0 and 1 evolve as

\[
(0,4)\longrightarrow(1,2)\longrightarrow(2,2)
\longrightarrow(1,4)\longrightarrow(0,4),
\]

and all levels above 1 stay unchanged. The classical shift indices are `1,0,1,0`. Nevertheless, every repetition starts with the same blocked full chain and requires another `Ω(2^m)` excursion through the delivered API. This is an occupancy argument and does not depend on choosing distinguishable payload symbols.

The state is reachable from all-half initialization: `2^(m+1)-2` consecutive left moves make level 0 half-full and levels 1 through `m` full on the right; one right move empties level 0. This follows by induction on `m`: the next carry resets all lower levels to half-full, increments the next level, and the remaining lower-level moves repeat the smaller instance. Repeating the four-move cycle `2^m` times after this `O(2^m)` prefix gives

\[
T=\Theta(2^m),\qquad
\text{physical time}=\Omega(2^m\cdot2^m)=\Omega(T^2).
\]

This refutes the promised realization of the **classical stable discipline** with the delivered guarded rows. It is not a lower bound against every alternative zone invariant or a new machine that directly implements the raw inward operation. Either such a replacement would require a different, audited construction; the direct repair is to remove the unnecessary inward room condition.

**The pairwise decomposition itself works after that repair.** Consider a right move of classical index `j≥1`. Before it, `R₀,…,Rⱼ₋₁` are empty and `L₀,…,Lⱼ₋₁` full; the top donor `Rⱼ` is half-full or full. Use this schedule:

1. For `i=j,j-1,…,1`, apply inward-right and outward-left at level `i`.
2. Perform `zoneMoveRight` once.
3. For `i=1,2,…,j`, again apply inward-right and outward-left at level `i`.

On the descending pass, each lower receiving word becomes half-full; the upper word retains the remainder. On the ascending pass, the already-processed lower word is empty on the right and full on the left, so every guard fires again. Each intermediate outward target has the required room. At completion, all levels below `j` are half-full on both sides, and

\[
|R_j|'=|R_j|-2^j,\qquad |L_j|'=|L_j|+2^j.
\]

Exactly two inward and two outward operations occur per level. Order preservation of the raw operations and the single nonempty level-zero pop give the correct virtual word and home. Importantly, intermediate occupancies need not be empty/half/full; this justifies keeping fullness out of the carrier.

Let `c` dominate the four machine constants. Since `i+1≤2^i` for `i≥1`, the shift-row part of one cascade costs at most

\[
4c\sum_{i=1}^j(2^i+i+1)
\le8c\sum_{i=1}^j2^i
=16c(2^j-1).
\]

Finding the level and changing the unary level word between calls adds `O(2^j+j²)=O(2^j)` time. After an event reaching level `i`, all lower levels are half-full, so their total right length is `2^i-1`. Before another event reaching level `i`, that length must reach either 0 or `2*(2^i-1)`. Each intervening virtual move changes it by one; including the next triggering move requires at least `2^i` moves. Thus there are at most `T/2^i` such events from all-half initialization, and each level contributes `O(T)` time. Lazy blank-zone initialization and `O(log(T+1))` reached levels yield the intended `O(T log(T+1))` total.

## The machine rows and the guard semantics

The quantifiers are correctly uniform: for each fixed side, one machine and one coefficient work for **every** level count, level, contents, native input, and allowed starting native-input position. The machine need not discover `ℓ` or scan outer zones. It can ignore native input and emit nothing throughout.

A direct implementation tests the lower guard, stages the affected words on tape 1, and rewrites the two adjacent windows. Word ends are distinguishable because a stored virtual blank occupies two nonblank false cells. Staging may copy the whole two-zone window; its size is still `O(2^i)`. A false guard returns the original tape and scratch word unchanged. A true guard uses `take`/`drop` for inward motion or splits/prepends for outward motion. There are only constantly many scan/copy/erase/rewind phases, and no other contents need be changed.

Unary level input is a sound uniform design. Navigation counters and boundaries must be implemented with a geometric total ledger, rather than performing an `i`-cell counter scan for every cell moved. For example, counting down a binary power of two with its least significant bit anchored has total carry/borrow work

\[
\sum_{r=1}^{2^i}(1+v_2(r))<2^{i+1},
\]

up to a constant return-to-anchor factor; initializing the counter from unary `i` costs at most a polynomial in `i`, absorbed by `O(2^i)`. Bounded staging can use reserved invalid pair codes as temporary delimiters, saving overwritten boundary pairs in finite control and restoring them. This supplies a linear-scan construction route with a fixed controller; merely claiming that a naive single-tape unary-doubling subroutine is linear would not suffice. These are mathematical implementation arguments, not supplied Lean transition tables.

The entire affected data window is contained in

\[
[-2\operatorname{zoneBase}(i+1),\;2\operatorname{zoneBase}(i+1)+1],
\]

which lies inside the row's `±(2*zoneBase(i+1)+2)` interval. Temporary data-tape marks can be placed within the affected windows. Scratch staging is on **tape 1**, whose separate bound is `c*(2^i+i+1)`; the data-tape interval does not claim to bound tape 1. Every finite pass has a bounded stopping condition, cleanup restores the unary level and both heads, and choosing the first halt time supplies the no-earlier-halt clause. Initial state is live, so this halt time is positive.

For `i=0` or `i≥ℓ`, the raw operations are identity; the rows deliberately exclude these levels. For `1≤i<ℓ` but a false lower guard, the rows do **not** exclude the input: their exact final equality requires identity. The dependent proof argument to `zoneShift` does not let a caller smuggle through a false room inequality or alter computational behavior by choosing another proof.

## A-S2-2 and the three Z4 bounds

Take a fixed Boolean machine with one work tape, whose work head never moves, whose work tape stays blank, and which advances along its native input until the right boundary, then halts without output. It computes the constantly empty output with

\[
T(n)=n+1,\qquad S(n)=1,
\]

and its source space is 1 at **every** horizon, including after halt.

The attached `sweep_run_to_halt` places the received witness's work head, after `t` simulated steps, at

\[
-t\,M.k-1=-t-1.
\]

At the source's halt time `t=n+1`, this is `-(n+2)`. Its physical head began at 0 and moves at unit speed, so at least `n+3` distinct cells were visited. The promised space estimate for this particular witness would imply

\[
n+3\le c(S(n)+1)=2c\qquad\text{for every }n,
\]

a contradiction. This uses mapped valid inputs, so it does not rely on an invalid-alphabet corner case. The controller body explains the failure: `.growLeft` and `.growRight` add a blank interleaved block every macro-step, regardless of source head motion.

**The existential one-tape statement remains mathematically true.** Use a sweep machine that extends a boundary only when a simulated head first crosses it. If `I_h` is the interval visited by source tape `h`, each contains 0, and therefore

\[
\left|\bigcup_{h<M.k}I_h\right|
\le\sum_{h<M.k}|I_h|
=\operatorname{spaceUsed}_{M}.
\]

A product-track realization pays a constant number of extra boundary cells. A realization interleaving `M.k` tagged cells per coordinate pays an additional factor `M.k`; the attached received construction is of this latter kind. Either factor is fixed by `M` and can be absorbed into `c`. Mid-sweep visits, including a boundary extension for the next simulated transition, lie in the representation of source-visited intervals through that transition plus a constant boundary allowance. Each source step still uses `O(t+1)` physical steps, giving `O((T(n)+1)²)` total time.

There is an additional quantifier obligation: the space conclusion ranges over **all** words over the enlarged alphabet `Γ'`, whereas correctness ranges only over `x.map e`. When `Γ` is nonempty, choose a finite-control retraction from `Γ'` to `Γ` that fixes `e`; simulate the corresponding source input without materializing a copy. Its length is unchanged, so `hS` applies without monotonicity. When `Γ` is empty, every source input and output is empty; an immediately halting one-work-tape machine supplies the required statement. For `M.k=0`, the unused-tape embedding uses exactly one visited cell, covered by `c*(S+1)`.

**Alphabet reduction.** Let the fixed block width be `W=Fintype.card Γ+1`. The received `arTM`'s read pass can momentarily reach the first cell immediately beyond the current block; that boundary must be counted. For each source visited interval `I_h`, all corresponding physical visits lie between `W*min I_h` and `W*(max I_h+1)`, so

\[
\operatorname{spaceUsed}_{arTM}
\le W\sum_h|I_h|+M.k
\le (W+1)S(n).
\]

The final inequality uses the time-zero fact `M.k≤S(n)`. If there are zero tapes, both sides' work space is zero. The existing fixed-length macro-cycle supplies the linear time factor; enlarging one coefficient handles both time and space. The hypotheses apply on `x.map e`, which has the same length as `x`.

**Composition.** If the corrected first stage uses coefficient `c₁`, the second stage's space bound is

\[
c_2\bigl(c_1(S(n)+1)+1\bigr)
\le c_2(c_1+1)(S(n)+1).
\]

Writing `Q=(T(n)+1)²≥1`, its time is likewise at most

\[
c_2(c_1Q+1)\le c_2(c_1+1)Q.
\]

Thus one coefficient works for the binary composite. No argument compares `S(n)` with `S(n+1)` or with any other input length. No monotonicity premise is missing.

## Z3 record and scheme fidelity

The exact record order is:

| Component | Width |
|---|---:|
| Native-input move (`signBits`) | 2 |
| Work-0 optional write (`optOptBoolBits`) | 2 |
| Work-0 move | 2 |
| Work-1 optional write | 2 |
| Work-1 move | 2 |
| Output (`optBoolBits`) | 2 |
| Successor (`optStateBits`) | 1 for halt; `s.val+2` for successor `s` |

Hence each record has length 13 for halt, or `14+s.val` for a successor. The enumeration contains

\[
(numStates+1)\cdot3\cdot3\cdot3=27(numStates+1)
\]

records. The ND mirror has twice that many, with the choice bit outermost; it does not interleave choices per state. The deterministic body is exactly its single-table counterpart.

The exact serializer-length identity is

\[
\begin{aligned}
|M.serialize|={}&2|Nat.bits(M.numStates)|+M.tm.q_0.val+3\\
&+351(M.numStates+1)\\
&+\sum_{\text{records with successor }s}(s.val+1).
\end{aligned}
\]

In particular, `351*(numStates+1)` is a safe necessary table-length guard, versus `702*(numStates+1)` for ND. The header and initial-state word do not halve. At `numStates=0`, the minimum complete deterministic serialization is `2+1+27*13=354` bits, versus `2+1+54*13=705` for ND. There is still one initial state and 27 records.

All three scheme structures match their references. The algebraic scheme supplies total decoding and arbitrarily padded recovery. The effective extension targets the fixed serialization and imposes only an arbitrary length-dependent time bound. The uniform extension uses the deterministic `toFinTM`, the same nested pairing, the same **joint** polynomial, and genuinely complementary acceptance/rejection premises; it neither omits rejection nor replaces numeric `t` by `log t` in the budget.

For existence, parse and range-check the concrete grammar, accept only all-true suffix padding, and fall back to a fixed one-state halting machine on failure. A table has a fixed number of self-delimiting successor records; appended true bits cannot change already-parsed records. Finite tables over finite domains reconstruct the exact machine, including initial state. A terminating canonizer reserializes the result; a maximum over the finitely many strings of each length supplies its arbitrary time bound.

For the uniform version, check the table's lower-length guard in binary **before** expanding the stated number of states. On success the table/state administration is polynomial in code length; on failure use the fixed fallback. Simulate at most `t` transitions under a binary countdown and track output as empty / exactly `[true]` / permanently other, since output is append-only. Inspect the result after the `t`-th transition before declaring timeout. At `t=0`, the initial configuration is live and its output empty, so the answer is false. Fixed scan and lookup costs yield a polynomial jointly in `|α|+|x|+t+1`; increasing the degree/coefficient gives precisely the record's single-parameter bound.

`NDCodes.lean` contributes exactly `actionBits₂` and `workPair` to these definition bodies. No new body invokes `exists_effectiveNDMachineCode` or assumes ND acceptance. Its transitive import does make that module visible; this is not evidence that the new theorem proofs depend on its sorried existence statement. A fill-time axiom/dependency check remains appropriate.

## Every sorried declaration: literal truth assessment

These are mathematical arguments for the exact statements, not claims of Lean kernel certification.

| # | Declaration | Argument |
|---|---|---|
| 1 | `zoneIndex_eq_iff` | The even/odd division sandwich above is equivalent to the positive-argument logarithm sandwich. It includes `s=0`, every even boundary, and the last odd slot of each zone. |
| 2 | `zoneTape_empty` | Every word lookup into `[]` fails, irrespective of the level guard. Both side branches are therefore physical blank, while the home branches compute false presence and false default data. |
| 3 | `zoneTape_blank_outside` | Every owned slot is below `zoneBase ℓ`; its two cells lie in the sharper signed interval calculated above. A cell satisfying the stated strict inequality is neither home nor any owned slot, so the level guard returns blank. |
| 4 | `zoneSide_shiftInW` | A disabled guard gives identity. When enabled, the adjacent segment `[] ++ wᵢ` is replaced by `take q wᵢ ++ drop q wᵢ = wᵢ`, where the cutoff is the defined `2^(i-1)`; no capacity or fullness hypothesis is used. |
| 5 | `zoneSide_shiftOutW` | A disabled guard again gives identity. When enabled, the adjacent segment is reassociated as `take q wᵢ₋₁ ++ (drop q wᵢ₋₁ ++ wᵢ) = wᵢ₋₁ ++ wᵢ`; the rest of `finRange` is untouched. |
| 6 | `zoneShift` — both capacity fields | The inward lower prefix fits and its upper suffix cannot grow. The outward lower word is exactly twice the cutoff, so its moved suffix has cutoff length and the given room premise bounds the enlarged upper word; inactive/opposite words retain their existing bounds. The definition is inhabitable, although its inward domain is unnecessarily restricted. |
| 7 | `zoneTape_homeWrite` | For `c≠0,1`, neither home branch is used. The selected side families are unchanged, hence the physical value is unchanged. |
| 8 | `zoneMoveRight` — both capacity fields | The left level-zero length increases by one, exactly covered by `hroom`; the right level-zero tail has no greater length. All other levels retain their original bounds, including when the popped list is empty. |
| 9 | `zoneMoveLeft` — both capacity fields | Exchange left and right in the preceding proof. The premise covers the right push, and the left tail never increases length. |
| 10 | `zoneSide_moveRight` | `finRange ℓ` begins with zero because `hℓ` supplies `ℓ>0`. The left concatenation gains old home at its front; nonempty `R₀` ensures that taking the concatenation's tail removes exactly the head of `R₀`, giving the stated right equality. |
| 11 | `exists_zoneShiftInTM` | On the restricted domain, the uniform local implementation described above tests emptiness, stages/copies the required prefix and suffix, and cleans up within a constant number of geometric scans. It preserves arbitrary outer contents, input position, and empty output, and returns scratch/head positions exactly; its first halt and visited bounds follow from that bounded schedule. A-S2-1 is a failure of consumer coverage, not a false equality on this domain. |
| 12 | `exists_zoneShiftOutTM` | Test lower fullness, returning identity if false; otherwise stage the outer half, move the upper word outward, and prepend the staged cells. `hroom` ensures every final occupied slot remains inside the upper zone, and the same finite-pass cleanup and geometric interval/time ledger apply. |
| 13 | `MultiTapeTM.spaceUsedByTape_le_card_Icc` | Every member of the finite visited-head image has a time index `u≤t`; the premise places it inside the integer interval. Set inclusion and interval cardinality give `(hi+1-lo).toNat`; if `lo>hi`, the premise is impossible already at `u=0`. |
| 14 | `exists_effectiveMachineCode2` | The concrete parser/fallback/padding construction above defines a total scheme with exact round-trip. Its canonizer is an ordinary computable finite-string function, and maxima over finite length classes give the unrestricted time function required by the statement. |
| 15 | `exists_uniformMachineCode2` | Use the same concrete grammar with the binary minimum-length check and bounded simulator, not an arbitrary effective scheme's canonizer-time guarantee. The joint polynomial ledger and complementary output-status decision above supply both branches, including malformed codes and `t=0`. |
| 16 | `alphabet_reduction_spaceUsed` | The existing fixed-width witness has a constant-time macro-cycle and at most `W` physical cells per source visited cell plus one boundary position per tape. Applying `hS` to the same-length mapped input bounds every partial cycle and every post-halt horizon, with one enlarged coefficient. |
| 17 | `one_work_tape_spaceUsed` | The demand-grown construction above proves the existential shape with quadratic time and linear-in-source-space usage; a retraction handles all enlarged-alphabet inputs, with separate empty-alphabet and zero-tape cases. The supplied claim that the **received** `sweepTM` already has this property is false, and its replacement is a substantive fill obligation. |
| 18 | `one_work_tape_binary_spaceUsed` | Apply the corrected existential one-tape theorem, then alphabet reduction with the first stage's all-input/all-time bound. The explicit coefficient calculation above absorbs both additive ones into one common coefficient; tape count remains one. |

The three skeleton-time statements also have the intended semantics: the three optional-bit cases give `zoneCellOf_bits`; the telescope gives `zoneBase_succ`; and padding by zero gives `MachineCode2.decode_encode`. Their tactic scripts were not re-audited.

## Adversarial checks and missing sanity exports

| Instantiation | Result |
|---|---|
| `ℓ=0`, arbitrary home | Empty side functions; exactly the home pair can be nonblank. The extent theorem is correct. |
| `s=0,1,2,5,6,13,14` | Zone indices `0,0,1,1,2,2,3`, respectively; both parities and successive boundaries work. |
| Occupied virtual blank versus absent slot | Respectively `(some false,some false)` versus `(none,none)`; representation preserves the distinction. |
| `i=0` and `i≥ℓ` | Raw shifts are identity; `hroom` is vacuous only when `i≥ℓ`, not merely because the operation is inactive. |
| `i=1`, empty donor, empty lower zone | Inward operation is identity on both words, with provable capacity fields. |
| `i=1`, upper word of length 1 | Inward transfer moves all of it and leaves the upper zone empty. No half-full assumption is needed. |
| `i=1`, full upper word of length 4 | Safe raw inward transformation, but wrapper and machine row unavailable: A-S2-1. |
| Full lower zone, upper length exactly capacity minus cutoff | Outward result exactly fills the upper zone. One additional upper cell invalidates `hroom`, as it should. |
| Nonempty inward lower word / nonfull outward lower word | Pure operation is identity, and the literal machine row still requires that identity behavior. |
| Empty `R₀`, nonempty `R₁` | `zoneMoveRight` returns blank home, not the outer word's head. This is intentional only before imposing the consumer's refill condition; `zoneSide_moveRight` correctly excludes it. |
| Nonempty `R₀` containing a single virtual blank | `hne` holds, new home is blank, and right concatenation loses exactly that stored blank. |
| `numStates=0` | One state, 27 records, minimum serialization 354 bits. |
| Arbitrarily huge binary state count in a short code | Binary guard must reject before any state enumeration; the uniform construction supports this. |
| `t=0` for bounded acceptance | Live initial state means acceptance is false, including when the first transition would emit true and halt. |
| Work-space horizon 0; zero work tapes | Initial visited space is the tape count, or zero with no tapes; the `+1` accommodates the one unused tape in the one-tape conversion. |
| Stationary-work-head input scanner | Refutes the received Z4 witness, not the existential theorem: A-S2-2. |
| Nonmonotone `S`; arbitrary target-alphabet word | Same-length retraction and all-horizon source bounds suffice; no comparison between different lengths is needed. |

An independent executable finite model corroborated **310,169 checks**: 245,760 logarithm-sandwich checks; 9,459 physical-layout checks; 29,032 raw-shift concatenation checks; 24,262 guarded capacity checks; 1,632 head-tail checks; and 24 repaired cascades through level 12. Nine additional full-chain tests checked reachability, the four-move cycle, and the unique initial enabled right-side shift. Whitespace-normalized source comparisons also confirmed the deterministic/ND serialization correspondence and exact uniform-record correspondence. These checks are corroboration; the general arguments and counterexamples above carry the audit conclusions.

Recommended machine-checkable additions, in priority order:

1. **Required for the blocker repair:** inward realization from a full donor with no room premise; the descending/head/ascending cascade, its final lengths and represented tape, and the level-event separation/charge bound.
2. Fixed-`ℓ` injectivity of `zoneTape` on `ZoneContents ℓ`, recovering home and each word from occupied pairs. Do not claim injectivity over an unknown level count: empty outer zones are invisible.
3. `zoneSide` length equals the sum of zone-word lengths and is at most `zoneBase ℓ`; direct slot readout at `zoneBase i + offset`.
4. A named small-`s` index computation table, the sharper signed extent, and the guard-false identity specializations.
5. Home readout for both head moves, the mirrored `zoneSide_moveLeft`, and an explicit all-empty-side blank-extension lemma.
6. `actionBits₂` exact/minimum lengths, the serializer-length identity, the 351-per-state parser guard, and `numStates=0` regression.
7. For the replacement Z4 witness, a trajectory-containment theorem valid inside a sweep and on all target-alphabet inputs. Keep the stationary-head scanner as a regression showing why unconditional radius growth is forbidden.

**Evidence boundary.** The audit used the supplied source packet and public source excerpts, not repository development history or GitHub mutations. Direct web opens of the full textbook PDF were unavailable; the retrieved §1.7 text supplied the stated invariant and shift rule, while the arithmetic, counterexamples, and charge proof above were derived independently. No Lean kernel check was performed. The supplied two Robustness prefixes contain no `sorry` terms, and all three new Z4 statements lie in the declared appended sections; historical byte identity cannot be proved from a single version. The 1,029-line `SingleTape.lean` exception is explicitly recorded in the attached plan.

**Notation introduced in this report.** `r, ε`: quotient and remainder in `s=2r+ε`; `m`: highest level in the full-donor chain; `j`: classical cascade level; `c₁,c₂`: the two conversion coefficients; `I_h`: source tape `h`'s visited interval; `W`: fixed alphabet-code block width; `Q=(T(n)+1)²`; `q`: the already-defined transfer cutoff `2^(i-1)` in the list identities; `v₂(r)`: the exponent of 2 dividing the positive integer `r`. Other identifiers are from the audited source or pack.
```

## ===== TCSlib/Complexity/TuringMachine/Build/Zone.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: the zoned tape carrier (Z2)

The zone representation of the machine-construction library
(`machine-library-design.md` §13, Z2; decisions 13.1 and 13.2): the data
of two stacks of **zones** — level `i` holding up to `2 · 2^i` virtual
cells per side — realized on one physical binary tape around a two-cell
home, with each virtual `Option Bool` cell stored as a **paired
presence/data cell** (decision 13.2; the `SweepAlphabet` product cells of
`Robustness/SingleTape.lean` are the in-repo precedent this replaces with
pairing, keeping the binary alphabet). This is the Hennie-Stearns
representation ([AB09] §1.7): the virtual head always reads at the home,
and locality is restored by per-level rebalancing shifts whose costs are
geometric in the level.

## Design (13a; spec-time refinements, amended by the round-1 audit)

* **The carrier is data, the invariant is the consumer's.** `ZoneContents`
  carries per-zone words bounded by capacity; the Hennie-Stearns
  `{empty, half, full}` fullness discipline, the `2^i`-credit amortization,
  and the simulation theorem live with the consumer (plan §2.1).
* **Shifts are pairwise, order-preserving, and totally guarded** (round-1
  repair, finding A-S2-1): the level-`i` inward shift moves the inner
  `2^(i-1)` stored cells of zone `i` into the **empty** zone `i - 1`, and
  carries **no room premise** — it removes cells from the donor, so a full
  donor is always a legal source. The outward shift moves the outer half
  of a **full** zone `i - 1` onto the front of zone `i`, and its room
  condition on the receiving zone lives **inside its guard**. Outside its
  guard every operation is the identity, and the machine rows realize the
  total guarded operation — identity branch included. The classical
  multi-level rebalance is the descending/move/ascending cascade of these
  ops (`zoneCascadeRight` below), whose represented-word, length, and
  geometric-cost statements are part of this gate per the round-1 audit.
* **One shift machine per direction and side**, taking the level in unary
  on the scratch tape: the Hennie-Stearns simulator is a single machine,
  so the level cannot be baked into finite control.
* **Left/right asymmetry of the cell pairing** is fixed by the layout
  (below) and documented once: on the right, even offsets carry presence
  bits; on the left, odd offsets do.

## The physical layout

Home: cells `0` (presence) and `1` (data). Right virtual slot `s`: cells
`2s + 2` (presence) and `2s + 3` (data). Left virtual slot `s`: cells
`-2s - 2` (presence) and `-2s - 1` (data). Zone `i` owns the slots
`[zoneBase i, zoneBase i + zoneCapacity i)` of its side, where
`zoneCapacity i = 2 · 2^i` and `zoneBase i = 2 · (2^i - 1)` (the exact sum
of the inner capacities). Every integer cell is owned by exactly one slot
or the home.

## Status: statement skeleton (§13 statement phase, tranche A-S2, round 2)

Definitions are real; every contract is `sorry`d with a proof sketch. The
round-1 gate (`audits/zone-infra-findings.md`) returned one blocker
(A-S2-1, repaired here: the inward room premise removed, the wrappers
split, the cascade statements added) and docstring corrections (A-S2-4,
applied).

## Main definitions and results

* `Turing.zoneCellBits`/`Turing.zoneCellOf` — the paired-cell codec.
* `Turing.ZoneContents`, `Turing.zoneTape` — the carrier and its physical
  realization.
* `Turing.zoneSide` — the represented virtual half-word (inner zones
  first).
* `Turing.zoneShiftInW`/`Turing.zoneShiftOutW` — the pure pairwise
  rebalancing ops on one side's family, totally guarded, with
  `Turing.zoneSide_shiftInW`/`Turing.zoneSide_shiftOutW` the honesty
  lemmas: rebalancing never changes the represented word.
* `Turing.zoneShiftIn`/`Turing.zoneShiftOut` — the hypothesis-free
  contents-level wrappers (round-1 repair).
* `Turing.zoneMoveRight`/`Turing.zoneMoveLeft`, `Turing.zoneMove`,
  `Turing.zoneHomeWrite` — the pure head-step and write ops.
* `Turing.zoneShiftInW_full_donor` — the full-donor regression required by
  the round-1 audit: a full donor above an empty zone shifts inward with
  no side condition.
* `Turing.zoneCascadeRight`, `Turing.zoneSide_cascadeRight`,
  `Turing.zoneCascadeRight_lengths`, `Turing.zoneCascade_cost_le` — the
  classical rebalance as a cascade of pairwise ops: it realizes one
  virtual right move, leaves every inner level half-full, and its summed
  row budgets stay geometric.
* `Turing.FinTM.exists_zoneShiftInTM`/`exists_zoneShiftOutTM` — the
  machine rows: one two-tape machine per direction and side, level in
  unary on the scratch tape, exact `O(2^i)` budgets, visited sets inside
  the level-`i` physical extent, realizing the total guarded op.
* `Turing.zoneTape_blank_outside`,
  `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` — the cardinality
  exports the Z4 space annotation consumes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge University Press, 2009. (§1.7, the Hennie-Stearns
  simulation; Exercise 1.6.)
* In-repo precedents: `SweepCell`/`SweepAlphabet`
  (`Robustness/SingleTape.lean`); `ObliviousSetup.lean`'s guide-zone
  layout.
-/

namespace Turing

/-! ### The paired-cell codec (decision 13.2) -/

/-- Encode one virtual `Option Bool` cell as its presence and data bits. -/
def zoneCellBits (v : Option Bool) : Bool × Bool := (v.isSome, v.getD false)

/-- Decode a presence/data bit pair back to the virtual cell. -/
def zoneCellOf (p d : Bool) : Option Bool := if p then some d else none

/-- The codec round-trips (skeleton-time proof; flagged). -/
theorem zoneCellOf_bits (v : Option Bool) :
    zoneCellOf (zoneCellBits v).1 (zoneCellBits v).2 = v := by
  cases v <;> rfl

/-! ### Layout arithmetic -/

/-- The capacity of zone `i`, in virtual cells per side. -/
def zoneCapacity (i : ℕ) : ℕ := 2 * 2 ^ i

/-- The first virtual slot of zone `i`: the exact total capacity of the
zones inside it. -/
def zoneBase (i : ℕ) : ℕ := 2 * (2 ^ i - 1)

/-- Bases telescope by capacities (skeleton-time proof; flagged). -/
theorem zoneBase_succ (i : ℕ) : zoneBase (i + 1) = zoneBase i + zoneCapacity i := by
  have h : 0 < 2 ^ i := Nat.two_pow_pos i
  simp only [zoneBase, zoneCapacity, pow_succ]
  omega

/-- The zone owning virtual slot `s`: the unique `i` with
`zoneBase i ≤ s < zoneBase (i + 1)`. -/
def zoneIndex (s : ℕ) : ℕ := Nat.log2 (s / 2 + 1)

/-- `zoneIndex` is the inverse of the base arithmetic: a slot lies in the
zone it indexes.

**Proof sketch.** Write `s = 2r + ε`; both base endpoints are even, so the
sandwich `zoneBase i ≤ s < zoneBase (i + 1)` is equivalent to
`2^i ≤ r + 1 < 2^(i+1)`, which characterizes `Nat.log2 (r + 1)` (the
argument is positive, so there is no logarithm-at-zero case). The round-1
audit's independent derivation is the route. -/
theorem zoneIndex_eq_iff (s i : ℕ) :
    zoneIndex s = i ↔ zoneBase i ≤ s ∧ s < zoneBase (i + 1) := by
  sorry

/-! ### The carrier -/

/-- The zone contents of one tape: the home cell and, per level and side,
the stored word (inner end first), bounded by capacity. Fullness
discipline is deliberately **not** carried here (design §13a): the
Hennie-Stearns `{empty, half, full}` invariant is the consumer's, and the
round-1 audit's cascade analysis confirms intermediate cascade states
leave the discipline anyway. -/
structure ZoneContents (ℓ : ℕ) where
  /-- the virtual cell under the virtual head -/
  home : Option Bool
  /-- the left zone words, inner end first -/
  left : Fin ℓ → List (Option Bool)
  /-- the right zone words, inner end first -/
  right : Fin ℓ → List (Option Bool)
  /-- left words fit their zones -/
  left_le : ∀ i, (left i).length ≤ zoneCapacity i.val
  /-- right words fit their zones -/
  right_le : ∀ i, (right i).length ≤ zoneCapacity i.val

/-- The stored virtual cell at slot `s` of one side, or `none` when the
slot is beyond the stored words (an unoccupied slot, physically blank —
distinct, through the pairing, from an occupied slot storing a blank). -/
def zoneSlot {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) (s : ℕ) :
    Option (Option Bool) :=
  if h : zoneIndex s < ℓ then (w ⟨zoneIndex s, h⟩)[s - zoneBase (zoneIndex s)]?
  else none

/-- The physical realization of zone contents: home at cells `0`/`1`,
right slot `s` at `2s + 2`/`2s + 3`, left slot `s` at `-2s - 2`/`-2s - 1`;
occupied slots store their presence and data bits, unoccupied slots and
cells beyond every zone are blank. On the right, even cells (relative to
the slot base) carry presence; on the left the roles are mirrored, so odd
negative offsets carry data — the one asymmetry of the layout, fixed
here. -/
def zoneTape {ℓ : ℕ} (z : ZoneContents ℓ) : ℤ → Option Bool := fun c =>
  if c = 0 then some z.home.isSome
  else if c = 1 then some (z.home.getD false)
  else if 2 ≤ c then
    let n := (c - 2).toNat
    match zoneSlot z.right (n / 2) with
    | some v => some (if n % 2 = 0 then v.isSome else v.getD false)
    | none => none
  else
    let n := (-c - 1).toNat
    match zoneSlot z.left (n / 2) with
    | some v => some (if n % 2 = 1 then v.isSome else v.getD false)
    | none => none

/-- The empty contents (blank home, every zone empty). -/
def ZoneContents.empty (ℓ : ℕ) : ZoneContents ℓ where
  home := none
  left := fun _ => []
  right := fun _ => []
  left_le := fun _ => by simp
  right_le := fun _ => by simp

/-- The empty contents realize the almost-blank tape: the home pair
stores the blank cell, and every other physical cell is blank.

**Proof sketch.** `zoneSlot` of the empty family is `none` at every slot
(`List.getElem?` of `[]`), so both side branches of `zoneTape` return
`none`; the home cells compute `zoneCellBits none = (false, false)`. -/
theorem zoneTape_empty (ℓ : ℕ) (c : ℤ) :
    zoneTape (ZoneContents.empty ℓ) c =
      if c = 0 then some false else if c = 1 then some false else none := by
  sorry

/-- Cells beyond the physical extent of `ℓ` levels are blank, for every
contents: the zones' slots stop at `zoneBase ℓ`, so the tape is `none`
outside `[-(2 * zoneBase ℓ + 1), 2 * zoneBase ℓ + 1]`.

**Proof sketch.** A cell at distance beyond the extent maps to a slot
`s ≥ zoneBase ℓ`; `zoneIndex_eq_iff` puts `zoneIndex s ≥ ℓ`, so `zoneSlot`
returns `none` by its guard. (The round-1 audit computed the sharper
asymmetric extent `[-2·zoneBase ℓ, 2·zoneBase ℓ + 1]`; the stated
symmetric bound is the safe envelope.) -/
theorem zoneTape_blank_outside {ℓ : ℕ} (z : ZoneContents ℓ) (c : ℤ)
    (hc : (2 * zoneBase ℓ + 1 : ℤ) < |c|) : zoneTape z c = none := by
  sorry

/-! ### The represented word -/

/-- The virtual half-word one side represents: the zone words
concatenated inner-first. -/
def zoneSide {ℓ : ℕ} (w : Fin ℓ → List (Option Bool)) : List (Option Bool) :=
  (List.finRange ℓ).flatMap fun i => w i

/-! ### Pure rebalancing (pairwise, order-preserving, totally guarded) -/

/-- The level-`i` inward shift on one side's family: when `1 ≤ i < ℓ` and
zone `i - 1` is **empty**, move the inner `2^(i-1)` stored cells (or all
of them, if fewer) of zone `i` into it; identity otherwise. **No room
premise exists** (round-1 repair, A-S2-1): the operation removes cells
from the donor, so a full donor is always legal — the exact case the
classical rebalance needs. -/
def zoneShiftInW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    Fin ℓ → List (Option Bool) := fun j =>
  if hi : 1 ≤ i ∧ i < ℓ then
    if w ⟨i - 1, by omega⟩ = [] then
      if j.val = i - 1 then (w ⟨i, hi.2⟩).take (2 ^ (i - 1))
      else if j.val = i then (w ⟨i, hi.2⟩).drop (2 ^ (i - 1))
      else w j
    else w j
  else w j

/-- The level-`i` outward shift on one side's family: when `1 ≤ i < ℓ`,
zone `i - 1` is **full**, and the receiving zone `i` has room for the
moved half, move zone `i - 1`'s outer half onto the front of zone `i`;
identity otherwise. The room condition lives **inside the guard**
(round-1 repair): no caller carries a hypothesis, and a cramped receiver
makes the op the identity rather than ill-defined. -/
def zoneShiftOutW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    Fin ℓ → List (Option Bool) := fun j =>
  if hi : 1 ≤ i ∧ i < ℓ then
    if (w ⟨i - 1, by omega⟩).length = zoneCapacity (i - 1) ∧
        (w ⟨i, hi.2⟩).length + 2 ^ (i - 1) ≤ zoneCapacity i then
      if j.val = i - 1 then (w ⟨i - 1, by omega⟩).take (2 ^ (i - 1))
      else if j.val = i then
        (w ⟨i - 1, by omega⟩).drop (2 ^ (i - 1)) ++ w ⟨i, hi.2⟩
      else w j
    else w j
  else w j

/-- Inward rebalancing never changes the represented half-word.

**Proof sketch.** A disabled guard gives the identity. When enabled, zones
`i - 1` and `i` are adjacent in the inner-first concatenation, zone
`i - 1` was empty, and `take ++ drop` restores zone `i`'s word, so the
concatenation is unchanged. -/
theorem zoneSide_shiftInW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    zoneSide (zoneShiftInW i w) = zoneSide w := by
  sorry

/-- Outward rebalancing never changes the represented half-word.

**Proof sketch.** A disabled guard gives the identity. When enabled, the
adjacent two-zone segment is literally re-associated:
`take q ++ (drop q ++ wᵢ) = wᵢ₋₁ ++ wᵢ` at the cutoff `q = 2^(i-1)`. -/
theorem zoneSide_shiftOutW {ℓ : ℕ} (i : ℕ) (w : Fin ℓ → List (Option Bool)) :
    zoneSide (zoneShiftOutW i w) = zoneSide w := by
  sorry

/-- **The full-donor regression** (required by the round-1 audit,
A-S2-1): above an empty zone, a donor of any length — a full one included —
shifts inward with no side condition: the receiving zone gets the inner
`2^(i-1)` cells (or all, if fewer) and the donor keeps the rest.

**Proof sketch.** Unfold `zoneShiftInW`: both guards fire by the
hypotheses, and the two branch equations are the stated `take`/`drop`. -/
theorem zoneShiftInW_full_donor {ℓ : ℕ} (i : ℕ) (hi : 1 ≤ i) (hℓ : i < ℓ)
    (w : Fin ℓ → List (Option Bool)) (hempty : w ⟨i - 1, by omega⟩ = []) :
    zoneShiftInW i w ⟨i - 1, by omega⟩ = (w ⟨i, hℓ⟩).take (2 ^ (i - 1)) ∧
    zoneShiftInW i w ⟨i, hℓ⟩ = (w ⟨i, hℓ⟩).drop (2 ^ (i - 1)) := by
  sorry

/-- Lift the inward shift to contents: `side = false` acts on the left
family, `side = true` on the right. Hypothesis-free (round-1 repair).

**Proof sketch** (capacity fields): the receiving zone gets at most
`2^(i-1) ≤ zoneCapacity (i-1)` cells; the donor's word only shrinks;
untouched zones keep their bounds. -/
def zoneShiftIn {ℓ : ℕ} (side : Bool) (i : ℕ) (z : ZoneContents ℓ) :
    ZoneContents ℓ where
  home := z.home
  left := if side then z.left else zoneShiftInW i z.left
  right := if side then zoneShiftInW i z.right else z.right
  left_le := by sorry
  right_le := by sorry

/-- Lift the outward shift to contents. Hypothesis-free: the receiving
zone's room condition is inside the family op's guard.

**Proof sketch** (capacity fields): when the guard fires, the shrunk
lower word fits trivially and the enlarged upper word fits by the guard's
own room conjunct; otherwise everything is unchanged. -/
def zoneShiftOut {ℓ : ℕ} (side : Bool) (i : ℕ) (z : ZoneContents ℓ) :
    ZoneContents ℓ where
  home := z.home
  left := if side then z.left else zoneShiftOutW i z.left
  right := if side then zoneShiftOutW i z.right else z.right
  left_le := by sorry
  right_le := by sorry

/-! ### Pure head steps and the home write -/

/-- Overwrite the virtual cell under the head. -/
def zoneHomeWrite {ℓ : ℕ} (z : ZoneContents ℓ) (v : Option Bool) :
    ZoneContents ℓ := { z with home := v }

/-- Writing the home changes exactly the two home cells of the physical
tape.

**Proof sketch.** `zoneTape` consults `home` only in its first two
branches; every slot branch reads the untouched families. -/
theorem zoneTape_homeWrite {ℓ : ℕ} (z : ZoneContents ℓ) (v : Option Bool)
    (c : ℤ) (h0 : c ≠ 0) (h1 : c ≠ 1) :
    zoneTape (zoneHomeWrite z v) c = zoneTape z c := by
  sorry

/-- The virtual head steps right: the home is pushed onto the inner end of
the left stack's zone `0`, and the new home is popped from the right
stack's zone `0` (blank when that zone is empty — the virtual tape is
blank past its stored extent; the Hennie-Stearns consumer's invariant
makes this the genuinely-blank case). Capacity of `L_0` is the consumer's
rebalancing obligation, carried here as a hypothesis; the hypothesis-free
guarded form is `Turing.zoneMove`. -/
def zoneMoveRight {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    ZoneContents ℓ where
  home := ((z.right ⟨0, hℓ⟩).headI : Option Bool)
  left := fun j => if j.val = 0 then z.home :: z.left j else z.left j
  right := fun j => if j.val = 0 then (z.right j).tail else z.right j
  left_le := by sorry
  right_le := by sorry

/-- The mirrored left step. -/
def zoneMoveLeft {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.right ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0) :
    ZoneContents ℓ where
  home := ((z.left ⟨0, hℓ⟩).headI : Option Bool)
  left := fun j => if j.val = 0 then (z.left j).tail else z.left j
  right := fun j => if j.val = 0 then z.home :: z.right j else z.right j
  left_le := by sorry
  right_le := by sorry

/-- The totally guarded head step (`dir = true` is right): acts when
`0 < ℓ` and the pushed side has room, else identity — the foldable form
the cascade uses. -/
def zoneMove {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  if hℓ : 0 < ℓ then
    match dir with
    | true =>
      if h : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 then
        zoneMoveRight hℓ z h
      else z
    | false =>
      if h : (z.right ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0 then
        zoneMoveLeft hℓ z h
      else z
  else z

/-- A right step transforms the represented tape as the virtual head move:
the old home joins the left word's inner end, and the right word loses its
inner cell (a nonempty `R_0` case; the blank-extension case pads with the
virtual blank).

**Proof sketch.** Pure list bookkeeping on `zoneSide`: `finRange`'s head
is zone `0`, and only zone `0` changes on each side. -/
theorem zoneSide_moveRight {ℓ : ℕ} (hℓ : 0 < ℓ) (z : ZoneContents ℓ)
    (hroom : (z.left ⟨0, hℓ⟩).length + 1 ≤ zoneCapacity 0)
    (hne : z.right ⟨0, hℓ⟩ ≠ []) :
    zoneSide (zoneMoveRight hℓ z hroom).left = z.home :: zoneSide z.left ∧
    zoneSide (zoneMoveRight hℓ z hroom).right = (zoneSide z.right).tail := by
  sorry

/-! ### The classical rebalance as a cascade (round-1 repair, A-S2-1)

The round-1 audit supplied the schedule and its analysis; the statements
below are the required gate material. One classical right move at index
`j`: a descending pass of inward-right/outward-left pairs from level `j`
down to `1`, the head step, and the ascending pass back up. -/

/-- One cascade stage at level `i`: shift inward on the right (feeding the
head's side) and outward on the left (draining the side the head leaves). -/
def zoneStepPair {ℓ : ℕ} (i : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  zoneShiftOut false i (zoneShiftIn true i z)

/-- The classical right-move rebalance at index `j`: descend `j → 1`,
step right, ascend `1 → j`. -/
def zoneCascadeRight {ℓ : ℕ} (j : ℕ) (z : ZoneContents ℓ) : ZoneContents ℓ :=
  (List.range j).foldl (fun z i => zoneStepPair (i + 1) z)
    (zoneMove true
      ((List.range j).reverse.foldl (fun z i => zoneStepPair (i + 1) z) z))

/-- The cascade realizes exactly one virtual right move. Preconditions are
the classical pre-state at index `j`: on the right, zones below `j` empty
and the donor `j` nonempty; on the left, zones below `j` full.

**Proof sketch** (the round-1 audit's schedule analysis, adopted as the
binding route): on the descending pass each inward-right guard fires into
an empty lower zone and each outward-left guard fires from a full lower
zone with room above; after the head step, the ascending pass re-fires the
same guards on the half-full intermediate state. Order preservation of the
raw ops (`zoneSide_shiftInW`/`OutW`) and the single nonempty level-zero pop
(`zoneSide_moveRight`) give the stated word transformation. -/
theorem zoneSide_cascadeRight {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)
    (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : z.right ⟨j, hj⟩ ≠ []) :
    zoneSide (zoneCascadeRight j z).left = z.home :: zoneSide z.left ∧
    zoneSide (zoneCascadeRight j z).right = (zoneSide z.right).tail := by
  sorry

/-- The cascade restores the half-full discipline below its index: after a
classical right move at index `j` from a donor holding at least `2^j`
cells, every level below `j` is half-full on both sides, the right donor
loses exactly `2^j` cells, and the left zone `j` gains exactly `2^j`.

**Proof sketch.** Track the two passes level by level (the round-1 audit's
ledger): the descending pass makes each lower receiving word half-full and
leaves the remainder upstairs; the ascending pass halves the level-zero
surplus back upward symmetrically. -/
theorem zoneCascadeRight_lengths {ℓ : ℕ} (j : ℕ) (hj : j < ℓ)
    (z : ZoneContents ℓ)
    (hr : ∀ k (hk : k < j), z.right ⟨k, by omega⟩ = [])
    (hl : ∀ k (hk : k < j),
      (z.left ⟨k, by omega⟩).length = zoneCapacity k)
    (hdonor : 2 ^ j ≤ (z.right ⟨j, hj⟩).length) :
    (∀ k (hk : k < j),
      ((zoneCascadeRight j z).right ⟨k, by omega⟩).length = 2 ^ k ∧
      ((zoneCascadeRight j z).left ⟨k, by omega⟩).length = 2 ^ k) ∧
    ((zoneCascadeRight j z).right ⟨j, hj⟩).length =
      (z.right ⟨j, hj⟩).length - 2 ^ j ∧
    ((zoneCascadeRight j z).left ⟨j, hj⟩).length =
      (z.left ⟨j, hj⟩).length + 2 ^ j := by
  sorry

/-- The cascade's summed row budgets stay geometric: the charge lemma the
Hennie-Stearns amortization consumes (two shift pairs per level, each
within the row budget `2^i + i + 1`).

**Proof sketch.** `i + 1 ≤ 2^i` for `i ≥ 1`, so each summand is at most
`4 · 2 · 2^i = 8 · 2^i`, and the geometric sum over `1 ≤ i ≤ j` is
`8 · (2^(j+1) - 2) ≤ 16 · 2^j` — the round-1 audit's charge calculation. -/
theorem zoneCascade_cost_le (j : ℕ) :
    ∑ i ∈ Finset.range j, 4 * (2 ^ (i + 1) + (i + 1) + 1) ≤ 16 * 2 ^ j := by
  sorry

/-! ### The machine rows -/

namespace FinTM

/-- **Z2, the inward shift row.** One two-tape machine per side: tape `0`
carries a zoned tape, tape `1` the level in unary (`replicate i true` as a
buffered word). From any configuration holding `zoneTape z` at origin and
the level word at origin, the machine halts at
`zoneTape (zoneShiftIn side i z)` — **realizing the total guarded
operation, identity branch included** (round-1 repair: there is no room
premise, and a false guard means the machine restores the original tape) —
with both heads home, the level word intact, within `c * (2^i + i + 1)`
steps, first return at the halt, the data head inside the level-`i + 1`
physical extent, and the scratch tape's space in the same budget.

**Proof sketch** (fill plan): scan the level word; test the lower zone's
emptiness by one pass over its window (a stored virtual blank occupies two
nonblank cells, so word ends are detectable); on a live guard, stage the
donor's inner `2^(i-1)` pairs through tape `1` with the R3 transfer
discipline and write them inward; on a dead guard, rewind and halt with
the tape untouched. Navigation counters follow the round-1 audit's
geometric-ledger route (anchored binary countdown, `O(2^i)` total carry
work; unary-level initialization polynomial in `i`, absorbed). R2 seams
join the constantly many phases. -/
theorem exists_zoneShiftInTM (side : Bool) :
    ∃ (Z : FinTM Bool) (c : ℕ), Z.k = 2 ∧
      ∀ (ℓ i : ℕ) (hi : 1 ≤ i) (hℓ : i < ℓ) (z : ZoneContents ℓ)
        {x : List Bool} (d : Cfg Z.k Bool Z.State x)
        (hstate : d.state = some Z.tm.q₀)
        (htape : d.workTapes = fun j =>
          if j.val = 0 then zoneTape z else bufferTape (List.replicate i true))
        (hheads : d.workTapePos = fun _ => 0) (hout : d.output = []),
        ∃ T ≤ c * (2 ^ i + i + 1),
          (Z.tm.runFrom d T).state = none ∧
          (Z.tm.runFrom d T).workTapes = (fun j =>
            if j.val = 0 then zoneTape (zoneShiftIn side i z)
            else bufferTape (List.replicate i true)) ∧
          (Z.tm.runFrom d T).workTapePos = (fun _ => 0) ∧
          (Z.tm.runFrom d T).output = [] ∧
          (Z.tm.runFrom d T).inputPos = d.inputPos ∧
          (∀ t < T, (Z.tm.runFrom d t).state ≠ none) ∧
          (∀ j (hj : j.val = 0) (t : ℕ), t ≤ T →
            (Z.tm.runFrom d t).workTapePos j ∈
              Finset.Icc (-(2 * (zoneBase (i + 1) : ℤ) + 2))
                (2 * (zoneBase (i + 1) : ℤ) + 2)) ∧
          (∀ j : Fin Z.k, j.val = 1 →
            Z.tm.spaceUsedByTape d T j ≤ c * (2 ^ i + i + 1)) := by
  sorry

/-- **Z2, the outward shift row**: the mirrored contract realizing the
total guarded outward operation (the room condition is inside the pure
op's guard; a cramped receiver yields the identity), with the same budget
shape, interval clause, and scratch bound.

**Proof sketch** (fill plan): as the inward row with the fullness and
room tests up front (both by bounded window passes) and the transfer
direction reversed; the full lower zone's outer half is staged through
tape `1` and written to zone `i`'s front after its stored word is slid
outward by `2^(i-1)` slots — one extra pass over the level-`i` window,
inside the same geometric budget. -/
theorem exists_zoneShiftOutTM (side : Bool) :
    ∃ (Z : FinTM Bool) (c : ℕ), Z.k = 2 ∧
      ∀ (ℓ i : ℕ) (hi : 1 ≤ i) (hℓ : i < ℓ) (z : ZoneContents ℓ)
        {x : List Bool} (d : Cfg Z.k Bool Z.State x)
        (hstate : d.state = some Z.tm.q₀)
        (htape : d.workTapes = fun j =>
          if j.val = 0 then zoneTape z else bufferTape (List.replicate i true))
        (hheads : d.workTapePos = fun _ => 0) (hout : d.output = []),
        ∃ T ≤ c * (2 ^ i + i + 1),
          (Z.tm.runFrom d T).state = none ∧
          (Z.tm.runFrom d T).workTapes = (fun j =>
            if j.val = 0 then zoneTape (zoneShiftOut side i z)
            else bufferTape (List.replicate i true)) ∧
          (Z.tm.runFrom d T).workTapePos = (fun _ => 0) ∧
          (Z.tm.runFrom d T).output = [] ∧
          (Z.tm.runFrom d T).inputPos = d.inputPos ∧
          (∀ t < T, (Z.tm.runFrom d t).state ≠ none) ∧
          (∀ j (hj : j.val = 0) (t : ℕ), t ≤ T →
            (Z.tm.runFrom d t).workTapePos j ∈
              Finset.Icc (-(2 * (zoneBase (i + 1) : ℤ) + 2))
                (2 * (zoneBase (i + 1) : ℤ) + 2)) ∧
          (∀ j : Fin Z.k, j.val = 1 →
            Z.tm.spaceUsedByTape d T j ≤ c * (2 ^ i + i + 1)) := by
  sorry

end FinTM

/-! ### The cardinality export (consumed by Z4) -/

/-- A head confined to an integer interval visits at most its cardinality.

**Proof sketch.** The visited set is a finite image contained in the
interval by hypothesis; `Finset.card_le_card` and `Int.card_Icc` finish. -/
theorem MultiTapeTM.spaceUsedByTape_le_card_Icc {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (d : Cfg k Symbol State input) (t : ℕ) (i : Fin k) (lo hi : ℤ)
    (h : ∀ u ≤ t, (tm.runFrom d u).workTapePos i ∈ Finset.Icc lo hi) :
    tm.spaceUsedByTape d t i ≤ (hi + 1 - lo).toNat := by
  sorry

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.Sigma.Basic
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Sweep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to one work tape

[AB09, Claim 1.6]: `k` work tapes are simulated by a single work tape with a quadratic
slowdown.

## Deviations from [AB09]

* [AB09]'s Claim 1.6 merges input, work, *and output* into one single tape (the
  standard model of Sipser's text). Our model structurally always has a separate
  read-only input tape and write-only output tape, so the faithful in-model rendering
  is **one work tape**: the interesting content — interleaving `k` tapes on one, with
  marked head positions and full sweeps — is identical, while the merged-single-tape
  model itself is out of scope (it is a different structure, not an instance of
  `MultiTapeTM`).
* [AB09] states the slowdown as `5k T(n)²`; we existentialize the constant and use
  `(T n + 1)²`.
* The retained structure is a genuinely different model from [AB09]'s merged one, not
  a notational variant: with a separate input tape, palindromes are decidable in
  linear time (`TCSlib.Complexity.ClassP.Examples`), while the merged single-tape
  model has an `Ω(n²)` lower bound for them ([AB09], chapter notes, citing Maass).
  Accordingly, the theorems below are *in-model analogues* of Claim 1.6, and no
  identification with the merged model is claimed anywhere in this development
  (phase-2 audit, finding 5).

## Main results

* `Turing.FinTM.one_work_tape` — [AB09, Claim 1.6] over an enlarged alphabet.
* `Turing.FinTM.one_work_tape_binary` — combined with alphabet reduction
  ([AB09, Claim 1.5]): one work tape *and* binary alphabet, still quadratic.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Claim 1.6, p. 17; Remark 1.7.)
-/

namespace Turing.FinTM


/-- Add one unused work tape to a machine with no work tapes. -/
private def unusedTapeTM {Γ : Type} (M : FinTM Γ) (hk : M.k = 0) : FinTM Γ where
  k := 1
  State := M.State
  tm :=
    { q₀ := M.tm.q₀
      tr := fun q inp _ =>
        let a := M.tm.tr q inp (fun i => (Fin.cast hk i).elim0)
        ⟨a.inputTape, fun _ => (none, 0), a.output, a.state⟩ }

/-- The unused tape is blank and its head stays at the origin. -/
private def unusedTapeCfg {Γ : Type} (M : FinTM Γ) {x : List Γ}
    (c : Cfg M.k Γ M.State x) : Cfg 1 Γ M.State x :=
  ⟨c.state, c.inputPos, fun _ _ => none, fun _ => 0, c.output⟩

/-- The zero-tape embedding commutes with a single transition, including halt. -/
private lemma unusedTape_step {Γ : Type} (M : FinTM Γ) (hk : M.k = 0)
    {x : List Γ} (c : Cfg M.k Γ M.State x) :
    (unusedTapeTM M hk).tm.step (unusedTapeCfg M c) =
      unusedTapeCfg M (M.tm.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp only [unusedTapeCfg, hs]
  | some q =>
    have hw : (fun i : Fin M.k => (Fin.cast hk i).elim0) = c.workTapeSymbols := by
      funext i
      exact (Fin.cast hk i).elim0
    dsimp only [unusedTapeCfg]
    rw [hs]
    dsimp only [unusedTapeTM]
    rw [hw]
    apply Cfg.ext <;> rfl

/-- The zero-tape path is a lockstep simulation; no sweep or initialization is needed. -/
private lemma unusedTape_computes {Γ : Type} (M : FinTM Γ) (hk : M.k = 0)
    (f : List Γ → List Γ) (T : ℕ → ℕ) (hM : M.ComputesFunInTime f T) :
    (unusedTapeTM M hk).ComputesFunInTime f T := by
  intro x
  have hr := MultiTapeTM.runFrom_comm_of_step (unusedTapeCfg M)
    (unusedTape_step M hk) (M.tm.initCfg x) (T x.length)
  have hi : unusedTapeCfg M (M.tm.initCfg x) = (unusedTapeTM M hk).tm.initCfg x := rfl
  rw [hi] at hr
  obtain ⟨hs, ho⟩ := (computesInTime_iff M x (f x) (T x.length)).mp (hM x)
  apply (computesInTime_iff _ _ _ _).mpr
  rw [hr]
  exact ⟨hs, ho⟩

/-- A cell stores a tape index, an optional payload, the head flag, and the
left-neighbor head flag recorded by the forward sweep. -/
private abbrev SweepCell (Γ : Type) (k : ℕ) := Fin k × (Option Γ × Bool × Bool)

/-- The forward rule reads marked payloads and records the preceding head flag. -/
private def readVisit {Γ : Type} {k : ℕ} :
    (Fin k → Option Γ × Bool) → SweepCell Γ k →
      (Fin k → Option Γ × Bool) × SweepCell Γ k :=
  indexedVisit fun _ s a => ((if a.2.1 then a.1 else s.1, a.2.1),
    (a.1, a.2.1, s.2))

/-- The return rule writes the old head's payload and determines the new head
from the old flags at its left, current, and right neighbors. -/
private def writeVisit {Γ S : Type} {k : ℕ} (act : Action k Γ S) :
    (Fin k → Bool) → SweepCell Γ k → (Fin k → Bool) × SweepCell Γ k :=
  indexedVisit fun i right a =>
    (a.2.1, (if a.2.1 then (act.workTapes i).1.getD a.1 else a.1,
      (match (act.workTapes i).2 with
        | .neg => right
        | .zero => a.2.1
        | .pos => a.2.2), false))

/-- The ghost head flag at a source coordinate. -/
private def headAt {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (i : Fin k) (j : ℤ) : Bool := decide (c.workTapePos i = j)

/-- One interleaved block; `read = true` includes the recorded left flag. -/
private def tapeRow {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (read : Bool) : List (SweepCell Γ k) :=
  (List.finRange k).map fun i =>
    (i, c.workTapes i j, headAt c i j, if read then headAt c i (j - 1) else false)

/-- The forward control immediately before reading block `j`. -/
private def readState {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) : Fin k → Option Γ × Bool := fun i =>
  (if c.workTapePos i < j then c.workTapeSymbols i else none, headAt c i (j - 1))

/-- Reading a whole block advances the control invariant by one coordinate. -/
private lemma read_row {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) :
    sweepFold readVisit (readState c j) (tapeRow c j false) =
      (readState c (j + 1), tapeRow c j true) := by
  unfold readVisit tapeRow
  rw [indexedFold_block]
  apply Prod.ext
  · funext i
    dsimp only [readState]
    apply Prod.ext
    · dsimp only
      by_cases he : c.workTapePos i = j
      · simp [headAt, he, Cfg.workTapeSymbols]
      · have hlt : c.workTapePos i < j + 1 ↔ c.workTapePos i < j := by omega
        simp [headAt, he, hlt]
    · simp [headAt]
  · rfl

/-- A return-sweep block performs exactly the source action on that coordinate.
**Proof sketch.** A payload changes only at its old head. A new head at `j`
comes from `j+1`, `j`, or `j-1`, according to its movement; these are exactly
the right-control, current-cell, and stored-left flags. -/
private lemma write_row {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (act : Action k Γ S) (j : ℤ) :
    sweepFold (writeVisit act) (fun i => headAt c i (j + 1)) (tapeRow c j true).reverse =
      (fun i => headAt c i j, (tapeRow (act.apply c) j false).reverse) := by
  unfold writeVisit tapeRow
  rw [indexedFold_block_reverse]
  apply Prod.ext
  · rfl
  · dsimp only
    congr 1
    apply List.map_congr_left
    intro i _
    refine Prod.ext (by rfl) ?_
    apply Prod.ext
    · dsimp only
      by_cases he : c.workTapePos i = j
      · cases hw : (act.workTapes i).1 <;>
          simp [headAt, he, Action.apply, hw, Function.update_apply]
      · have he' : j ≠ c.workTapePos i := Ne.symm he
        cases hw : (act.workTapes i).1 <;> simp [headAt, he, he', Action.apply, hw]
    · dsimp only
      refine Prod.ext ?_ (by rfl)
      dsimp only
      cases hm : (act.workTapes i).2 <;>
        simp only [headAt, Action.apply, hm, SignType.cast]
      all_goals simp only [↓reduceIte, decide_eq_decide]; omega

/-- Consecutive interleaved blocks, in ascending coordinate order. -/
private def tapeZone {C : Type} (row : ℤ → List C) (j : ℤ) : ℕ → List C
  | 0 => []
  | n + 1 => row j ++ tapeZone row (j + 1) n

/-- The forward sweep processes any consecutive block interval. -/
private lemma read_zone {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (n : ℕ) :
    sweepFold readVisit (readState c j) (tapeZone (fun z => tapeRow c z false) j n) =
      (readState c (j + n), tapeZone (fun z => tapeRow c z true) j n) := by
  induction n generalizing j with
  | zero => simp [tapeZone, sweepFold]
  | succ n ih =>
    simp only [tapeZone, sweepFold_append, read_row, ih]
    congr 2
    omega

/-- The return sweep processes the same interval in reverse order. -/
private lemma write_zone {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (act : Action k Γ S) (j : ℤ) (n : ℕ) :
    sweepFold (writeVisit act) (fun i => headAt c i (j + n))
      (tapeZone (fun z => tapeRow c z true) j n).reverse =
      (fun i => headAt c i j,
        (tapeZone (fun z => tapeRow (act.apply c) z false) j n).reverse) := by
  induction n generalizing j with
  | zero => simp [tapeZone, sweepFold]
  | succ n ih =>
    have he : j + (n + 1 : ℕ) = j + 1 + n := by omega
    simp only [tapeZone, List.reverse_append, sweepFold_append, he, ih]
    rw [write_row]

/-- An enlarged symbol is input/output data, an internal cell, or a boundary. -/
private abbrev SweepAlphabet (Γ : Type) (k : ℕ) := Γ ⊕ Option (SweepCell Γ k)

/-- Encode a source symbol as an unmarked data symbol. -/
private def sweepEmbed (Γ : Type) (k : ℕ) : Γ ↪ SweepAlphabet Γ k :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- A nonblank internal boundary, distinct from every payload (including blank). -/
private def sweepBoundary {Γ : Type} {k : ℕ} : SweepAlphabet Γ k := .inr none

/-- Tag a complete internal cell. -/
private def sweepSymbol {Γ : Type} {k : ℕ} (c : SweepCell Γ k) : SweepAlphabet Γ k :=
  .inr (some c)

/-- Interpret the unchanged native input alphabet. -/
private def sweepInput {Γ : Type} {k : ℕ} : Option (SweepAlphabet Γ k) → Option Γ
  | some (.inl a) => some a
  | _ => none

/-- Finite controller phases; unbounded coordinates never enter the state. -/
private inductive SweepState (Γ S : Type) (k : ℕ) where
  | init : Fin (k + 1) → SweepState Γ S k
  | back : SweepState Γ S k
  | growLeft : S → Fin (k + 1) → SweepState Γ S k
  | read : S → (Fin k → Option Γ × Bool) → SweepState Γ S k
  | growRight : S → (Fin k → Option Γ × Bool) → Fin (k + 1) → SweepState Γ S k
  | write : S → Option Γ → (Fin k → Option Γ) → (Fin k → Bool) → SweepState Γ S k

/-- Enumerate the finite control through its finite sum/product representation. -/
private instance sweepStateFintype (Γ S : Type) [Fintype Γ] [Fintype S] (k : ℕ) :
    Fintype (SweepState Γ S k) := derive_fintype% _

/-- Equality of controller states is decidable through the same representation. -/
private instance sweepStateDecidableEq (Γ S : Type) [DecidableEq Γ] [DecidableEq S] (k : ℕ) :
    DecidableEq (SweepState Γ S k) :=
  -- The nested sum/sigma representation exceeds the default instance-size bound.
  set_option synthInstance.maxSize 8192 in
  (proxy_equiv% (SweepState Γ S k)).symm.decidableEq

/-- A stationary-input/output action that preserves the cell it scans. -/
private def sweepMove {A S : Type} (q : Option S) (d : SignType) : Action 1 A S :=
  ⟨0, fun _ => (none, d), none, q⟩

/-- The finite controller for the two sweeps and their boundary extensions.
The forward sweep records left-neighbor flags in the cells. The backward sweep
keeps right-neighbor flags in its control, so it needs no extra scan. -/
private def sweepTM {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) : FinTM (SweepAlphabet Γ M.k) where
  k := 1
  State := SweepState Γ M.State M.k
  tm :=
    { q₀ := .init 0
      tr := fun q inp work =>
        match q with
        | .init i =>
          if h : i.val < M.k then
            sweepAct (.init ⟨i.val + 1, by omega⟩)
              (some (sweepSymbol (⟨i.val, h⟩, none, true, false))) .pos
          else
            sweepAct .back (some sweepBoundary) .neg
        | .back =>
          match work 0 with
          | none => sweepAct (.growLeft M.tm.q₀ 0) (some sweepBoundary) .zero
          | some a => sweepAct .back (some a) .neg
        | .growLeft q i =>
          if h : i.val < M.k then
            sweepAct (.growLeft q ⟨i.val + 1, by omega⟩)
              (some (sweepSymbol (⟨M.k - 1 - i.val, by omega⟩, none, false, false))) .neg
          else
            sweepAct (.read q (fun _ => (none, false))) (some sweepBoundary) .pos
        | .read q s =>
          match work 0 with
          | some (.inr (some c)) =>
            let v := readVisit s c
            sweepAct (.read q v.1) (some (sweepSymbol v.2)) .pos
          | _ => sweepMove (some (.growRight q s 0)) .zero
        | .growRight q s i =>
          if h : i.val < M.k then
            sweepAct (.growRight q s ⟨i.val + 1, by omega⟩)
              (some (sweepSymbol (⟨i.val, h⟩, none, false, (s ⟨i.val, h⟩).2))) .pos
          else
            let a := M.tm.tr q (sweepInput inp) (fun i => (s i).1)
            ⟨a.inputTape, fun _ => (some (some sweepBoundary), .neg),
              a.output.map Sum.inl,
              some (.write q (sweepInput inp) (fun i => (s i).1) (fun _ => false))⟩
        | .write q inp reads right =>
          let a := M.tm.tr q inp reads
          match work 0 with
          | some (.inr (some c)) =>
            let v := writeVisit a right c
            sweepAct (.write q inp reads v.1) (some (sweepSymbol v.2)) .neg
          | _ => sweepMove (a.state.map (fun q => .growLeft q 0)) .zero }

/-- The initialized interleaving has `k` marked blank cells. -/
private def blankRow {Γ : Type} (k : ℕ) (mark : Bool) : List (SweepCell Γ k) :=
  (List.finRange k).map fun i => (i, none, mark, false)

/-- A row outside both the source heads and the written support is blank. -/
private lemma tapeRow_blank {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (hp : ∀ i, c.workTapePos i ≠ j)
    (ht : ∀ i, c.workTapes i j = none) :
    tapeRow c j false = blankRow k false := by
  unfold tapeRow blankRow
  apply List.map_congr_left
  intro i _
  simp [headAt, hp i, ht i]

/-- The size of each block is the number of source tapes. -/
private lemma tapeRow_length {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (b : Bool) : (tapeRow c j b).length = k := by
  simp [tapeRow]

/-- Zone length is the block count times the source tape count. -/
private lemma tapeZone_length {Γ S : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (j : ℤ) (n : ℕ) (b : Bool) :
    (tapeZone (fun z => tapeRow c z b) j n).length = n * k := by
  induction n generalizing j with
  | zero => simp [tapeZone]
  | succ n ih =>
    simp only [tapeZone, List.length_append, tapeRow_length, ih, Nat.add_mul, Nat.one_mul]
    omega

/-- Split a zone at a block boundary. -/
private lemma tapeZone_append {C : Type} (row : ℤ → List C) (j : ℤ) (n m : ℕ) :
    tapeZone row j (n + m) = tapeZone row j n ++ tapeZone row (j + n) m := by
  induction n generalizing j with
  | zero => simp [tapeZone]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [tapeZone, ih, List.append_assoc]
    rw [show j + 1 + (n : ℤ) = j + (n + 1 : ℕ) by omega]

/-- The native input position is unchanged numerically by symbol embedding. -/
private def sweepPos {Γ : Type} {x : List Γ} (k : ℕ) (p : Fin (x.length + 2)) :
    Fin ((x.map (sweepEmbed Γ k)).length + 2) :=
  ⟨p.val, by simpa only [List.length_map] using p.isLt⟩

/-- Input-head movement commutes with the unchanged-length symbol embedding. -/
private lemma sweepPos_move {Γ : Type} {x : List Γ} (k : ℕ)
    (p : Fin (x.length + 2)) (d : SignType) :
    moveInputPos (sweepPos k p) d = sweepPos k (moveInputPos p d) := by
  apply Fin.ext
  simp only [moveInputPos, sweepPos, List.length_map]
  split <;> rfl

/-- The input read by an encoded configuration is the encoded source read. -/
private lemma sweepInput_read {Γ S S' : Type} {k : ℕ} {x : List Γ}
    (c : Cfg k Γ S x) (d : Cfg 1 (SweepAlphabet Γ k) S' (x.map (sweepEmbed Γ k)))
    (hp : d.inputPos = sweepPos k c.inputPos) :
    sweepInput d.inputSymbol = c.inputSymbol := by
  have hzero : sweepPos k c.inputPos = 0 ↔ c.inputPos = 0 := by
    simp only [Fin.ext_iff, sweepPos, Fin.val_zero]
  have hv : (sweepPos k c.inputPos).val = c.inputPos.val := rfl
  simp only [Cfg.inputSymbol, hp, hzero, hv, List.length_map]
  split
  · rfl
  · split
    · rfl
    · simp only [List.getElem_map, sweepEmbed, Function.Embedding.coeFn_mk, sweepInput]

/-- Canonical configurations at the left boundary between simulated steps. -/
private def sweepStart {Γ : Type} [Fintype Γ] [DecidableEq Γ] (M : FinTM Γ)
    {x : List Γ} (c : Cfg M.k Γ M.State x) (j : ℤ) (n : ℕ) (z : ℤ) :
    Cfg 1 (SweepAlphabet Γ M.k) (SweepState Γ M.State M.k)
      (x.map (sweepEmbed Γ M.k)) :=
  sweepRevCfg (c.state.map (fun q => .growLeft q 0)) (sweepPos M.k c.inputPos) z
    ((tapeZone (fun j => tapeRow c j false) j n).map (fun a => some (sweepSymbol a)) ++
      [some sweepBoundary]) [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k))

/-- Replacing the current cell preserves both tails of the zipper. -/
private lemma sweepTape_write {A : Type} (z : ℤ) (l r : List (Option A)) (b : Option A) :
    Function.update (sweepTape z l r) z b = sweepTape z l (b :: r.tail) := by
  funext p
  by_cases hp : p = z
  · subst p
    simp [sweepTape_read]
  · rw [Function.update_of_ne hp]
    by_cases h : p < z
    · simp only [sweepTape, if_pos h]
    · have he : (p - z).toNat = (p - z - 1).toNat + 1 := by omega
      simp only [sweepTape, if_neg h, he, List.getElem?_cons_succ]
      cases r <;> rfl

/-- Write a boundary and turn from a forward scan into a backward scan. -/
private lemma sweep_turn_left {A S : Type} {x : List A} (q q' : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b emit : Option A) (di : SignType) :
    (⟨di, fun _ => (some b, .neg), emit, q'⟩ : Action 1 A S).apply
      (sweepCfg q p z l r out) =
    sweepRevCfg q' (moveInputPos p di) (z - 1) (b :: r.tail) l (out ++ emit.toList) := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext i w
  change Function.update (sweepTape z l r) z b w = _
  rw [sweepTape_write, sweepTape_turn]
  rfl

/-- Write the left boundary and turn toward the first forward-scan cell. -/
private lemma sweep_turn_right {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .pos).apply (sweepRevCfg q p z l r out) =
      sweepCfg (some q') p (z + 1) (b :: r.tail) l out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ rfl (List.append_nil _)
  funext i w
  have h := congrFun (sweepTape_write (-z) l r b) (-w)
  have ht := congrFun (sweepTape_turn (z + 1) (b :: r.tail) l) w
  have he : z + 1 - 1 = z := by omega
  rw [he] at ht
  change Function.update (fun w => sweepTape (-z) l r (-w)) z b w =
    sweepTape (z + 1) (b :: r.tail) l w
  rw [ht]
  simpa only [Function.update_apply, neg_inj] using h

/-- Initialization writes the marked origin block in exactly `k` steps. -/
private lemma sweep_init_block {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) {x : List (SweepAlphabet Γ M.k)} (p : Fin (x.length + 2))
    (out : List (SweepAlphabet Γ M.k)) (z : ℤ) (l r : List (Option (SweepAlphabet Γ M.k))) :
    (sweepTM M).tm.runFrom (sweepCfg (some (.init 0)) p z l r out) M.k =
      sweepCfg (some (.init ⟨M.k, by omega⟩)) p (z + M.k)
        (((blankRow M.k true).map (fun a => some (sweepSymbol a))).reverse ++ l)
        (r.drop M.k) out := by
  let w := (blankRow (Γ := Γ) M.k true).map sweepSymbol
  have hw : w.length = M.k := by simp [w, blankRow]
  have h := sweep_generate (sweepTM M).tm w
    (fun i z l r => sweepCfg (some (.init ⟨i.val, by simpa [hw] using i.isLt⟩)) p z l r out)
    1 (fun i hi z l r => ?_) z l r M.k (by omega)
  · rw [List.take_of_length_le (show w.length ≤ M.k by omega)] at h
    simpa [hw, w, List.map_map] using h
  · have hik : i < M.k := by omega
    change (sweepTM M).tm.step (sweepCfg (some (.init ⟨i, by omega⟩)) p z l r out) = _
    change ((sweepTM M).tm.tr (.init ⟨i, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, dif_pos hik]
    have he : w[i] = sweepSymbol (⟨i, hik⟩, none, true, false) := by
      simp [w, blankRow]
    rw [he]
    exact sweepCfg_right_any _ _ p z l r out _

/-- Growing the left boundary writes exactly one reversed blank block. -/
private lemma sweep_grow_left_block {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (q : M.State) {x : List (SweepAlphabet Γ M.k)}
    (p : Fin (x.length + 2)) (out : List (SweepAlphabet Γ M.k))
    (z : ℤ) (l r : List (Option (SweepAlphabet Γ M.k))) :
    (sweepTM M).tm.runFrom (sweepRevCfg (some (.growLeft q 0)) p z l r out) M.k =
      sweepRevCfg (some (.growLeft q ⟨M.k, by omega⟩)) p (z - M.k)
        ((blankRow M.k false).map (fun a => some (sweepSymbol a)) ++ l)
        (r.drop M.k) out := by
  let w := ((blankRow (Γ := Γ) M.k false).map sweepSymbol).reverse
  have hw : w.length = M.k := by simp [w, blankRow]
  have h := sweep_generate (sweepTM M).tm w
    (fun i z l r => sweepRevCfg (some (.growLeft q ⟨i.val, by simpa [hw] using i.isLt⟩))
      p z l r out) (-1) (fun i hi z l r => ?_) z l r M.k (by omega)
  · rw [List.take_of_length_le (show w.length ≤ M.k by omega)] at h
    simpa [hw, w, List.map_reverse, List.map_map, sub_eq_add_neg] using h
  · have hik : i < M.k := by omega
    change (sweepTM M).tm.step (sweepRevCfg (some (.growLeft q ⟨i, by omega⟩)) p z l r out) = _
    change ((sweepTM M).tm.tr (.growLeft q ⟨i, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, dif_pos hik]
    have he : w[i] = sweepSymbol (⟨M.k - 1 - i, by omega⟩, none, false, false) := by
      simp [w, blankRow, List.getElem_reverse]
    rw [he]
    exact sweepRevCfg_left_any _ _ p z l r out _

/-- The right guard block records the flags from the last scanned block. -/
private def rightRow {Γ : Type} {k : ℕ} (s : Fin k → Option Γ × Bool) :
    List (SweepCell Γ k) := (List.finRange k).map fun i => (i, none, false, (s i).2)

/-- Growing the right boundary writes one guard block, retaining the collected reads. -/
private lemma sweep_grow_right_block {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (q : M.State) (s : Fin M.k → Option Γ × Bool)
    {x : List (SweepAlphabet Γ M.k)} (p : Fin (x.length + 2))
    (out : List (SweepAlphabet Γ M.k)) (z : ℤ) (l r : List (Option (SweepAlphabet Γ M.k))) :
    (sweepTM M).tm.runFrom (sweepCfg (some (.growRight q s 0)) p z l r out) M.k =
      sweepCfg (some (.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
        (((rightRow s).map (fun a => some (sweepSymbol a))).reverse ++ l)
        (r.drop M.k) out := by
  let w := (rightRow s).map sweepSymbol
  have hw : w.length = M.k := by simp [w, rightRow]
  have h := sweep_generate (sweepTM M).tm w
    (fun i z l r => sweepCfg (some (.growRight q s ⟨i.val, by simpa [hw] using i.isLt⟩))
      p z l r out) 1 (fun i hi z l r => ?_) z l r M.k (by omega)
  · rw [List.take_of_length_le (show w.length ≤ M.k by omega)] at h
    simpa [hw, w, List.map_map] using h
  · have hik : i < M.k := by omega
    change ((sweepTM M).tm.tr (.growRight q s ⟨i, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, dif_pos hik]
    have he : w[i] = sweepSymbol (⟨i, hik⟩, none, false, (s ⟨i, hik⟩).2) := by
      simp [w, rightRow]
    rw [he]
    exact sweepCfg_right_any _ _ p z l r out _

/-- A sweep with the identity rule only changes the physical scan frontier. -/
private lemma sweepFold_id {R C : Type} (s : R) (as : List C) :
    sweepFold (fun s a => (s, a)) s as = (s, as) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [sweepFold, ih]

/-- Writing without moving in a backward-facing zipper. -/
private lemma sweepRevCfg_write {A S : Type} {x : List A} (q : Option S) (q' : S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A)
    (b : Option A) :
    (sweepAct q' b .zero).apply (sweepRevCfg q p z l r out) =
      sweepRevCfg (some q') p z l (b :: r.tail) out := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (List.append_nil _)
  · funext i w
    have h := congrFun (sweepTape_write (-z) l r b) (-w)
    change Function.update (fun w => sweepTape (-z) l r (-w)) z b w = _
    simpa only [Function.update_apply, neg_inj] using h
  · funext i
    exact add_zero z

/-- Initialization builds the marked origin block and both boundaries.
**Proof sketch.** Write `k` marked blank cells, write the right boundary and
turn left, traverse the same `k` cells without altering them, then write the
left boundary. All four phases preserve the native input and output. -/
private lemma sweep_init {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (x : List Γ) :
    (sweepTM M).tm.runFrom ((sweepTM M).tm.initCfg (x.map (sweepEmbed Γ M.k))) (2 * M.k + 2) =
      sweepStart M (M.tm.initCfg x) 0 1 (-1) := by
  let p := sweepPos M.k (M.tm.initCfg x).inputPos
  let B := (blankRow (Γ := Γ) M.k true).map (fun a => some (sweepSymbol a))
  have hlen : (blankRow (Γ := Γ) M.k true).length = M.k := by simp [blankRow]
  have hp : p = 1 := by apply Fin.ext; simp [p, sweepPos]
  have hinit : (sweepTM M).tm.initCfg (x.map (sweepEmbed Γ M.k)) =
      sweepCfg (some (.init 0)) p 0 [] [] [] := by
    refine Cfg.ext rfl hp.symm ?_ rfl rfl
    funext i z
    simp [sweepCfg, sweepTape]
  have hturn : (sweepTM M).tm.step
      (sweepCfg (some (.init ⟨M.k, by omega⟩)) p M.k B.reverse [] []) =
      sweepRevCfg (some .back) p ((M.k : ℤ) - 1) [some sweepBoundary] B.reverse [] := by
    change ((sweepTM M).tm.tr (.init ⟨M.k, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, lt_self_iff_false, ↓reduceDIte]
    simpa only [sweepAct, SignType.zero_eq_zero, moveInputPos_zero, List.tail_nil,
      Option.toList_none, List.append_nil] using
      sweep_turn_left (S := SweepState Γ M.State M.k)
        (some (.init ⟨M.k, by omega⟩)) (some .back) p (M.k : ℤ)
        B.reverse [] [] (some sweepBoundary) none .zero
  have hback := sweep_run_reverse (sweepTM M).tm (fun _ : Unit => SweepState.back)
    sweepSymbol (fun s a => (s, a)) (by intro s a inp; rfl) p []
    (blankRow (Γ := Γ) M.k true).reverse () ((M.k : ℤ) - 1) [some sweepBoundary] []
  have hback' : (sweepTM M).tm.runFrom
      (sweepRevCfg (some .back) p ((M.k : ℤ) - 1) [some sweepBoundary] B.reverse []) M.k =
      sweepRevCfg (some .back) p (-1) (B ++ [some sweepBoundary]) [] [] := by
    simpa [B, List.map_reverse, hlen, sweepFold_id] using hback
  have hlast : (sweepTM M).tm.step
      (sweepRevCfg (some .back) p (-1) (B ++ [some sweepBoundary]) [] []) =
      sweepRevCfg (some (.growLeft M.tm.q₀ 0)) p (-1)
        (B ++ [some sweepBoundary]) [some sweepBoundary] [] := by
    have hr : (sweepRevCfg (some (SweepState.back (Γ := Γ) (S := M.State) (k := M.k)))
        p (-1) (B ++ [some sweepBoundary]) [] []).workTapeSymbols = fun _ => none := by
      funext i
      simp [Cfg.workTapeSymbols, sweepRevCfg, sweepTape]
    change ((sweepTM M).tm.tr .back _ _).apply _ = _
    rw [hr]
    exact sweepRevCfg_write _ _ _ _ _ _ _ _
  rw [show 2 * M.k + 2 = (M.k + 1) + M.k + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_succ_eq_step', hinit, sweep_init_block]
  simp only [zero_add, List.append_nil, List.drop_nil]
  rw [hturn, hback', hlast]
  congr 1
  simp [tapeZone, tapeRow, blankRow, headAt, B]

/-- A stationary phase change preserves a forward-facing tape. -/
private lemma sweepCfg_stay {A S : Type} {x : List A} (q q' : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    (sweepMove q' .zero).apply (sweepCfg q p z l r out) = sweepCfg q' p z l r out := by
  apply Cfg.ext <;> simp [sweepMove, sweepCfg, Action.apply]

/-- A stationary phase change preserves a backward-facing tape. -/
private lemma sweepRevCfg_stay {A S : Type} {x : List A} (q q' : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    (sweepMove q' .zero).apply (sweepRevCfg q p z l r out) = sweepRevCfg q' p z l r out := by
  apply Cfg.ext <;> simp [sweepMove, sweepRevCfg, Action.apply]

/-- The first half of a simulated step grows the left guard and collects all
marked source symbols. Its exact cost includes both phase changes.
**Proof sketch.** The head lower bound makes the new left block blank and gives
the empty initial read table. Write that block, place the new boundary, and turn.
The forward transduction processes all blocks through the old right edge,
recording the marked symbols and left-neighbor flags. A stationary boundary
transition enters the right-extension phase. Concatenate these four runs. -/
private lemma sweep_prepare {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) {x : List Γ} (c : Cfg M.k Γ M.State x)
    (q : M.State) (hs : c.state = some q) (a : ℤ) (n : ℕ) (z : ℤ)
    (hp : ∀ i, a ≤ c.workTapePos i)
    (hl : ∀ i, c.workTapes i (a - 1) = none) :
    (sweepTM M).tm.runFrom (sweepStart M c a n z)
      (M.k + 1 + (n + 1) * M.k + 1) =
    sweepCfg (some (.growRight q (readState c (a + n)) 0)) (sweepPos M.k c.inputPos)
      (z - M.k + 1 + ((n + 1) * M.k : ℕ))
      (((tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)).map
        (fun b => some (sweepSymbol b))).reverse ++ [some sweepBoundary])
      [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k)) := by
  let p := sweepPos M.k c.inputPos
  let out := c.output.map (sweepEmbed Γ M.k)
  let D := (tapeZone (fun j => tapeRow c j false) a n).map (fun b => some (sweepSymbol b))
  let F := tapeZone (fun j => tapeRow c j false) (a - 1) (n + 1)
  let R := tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)
  have hf : F = blankRow M.k false ++ tapeZone (fun j => tapeRow c j false) a n := by
    dsimp [F]
    rw [tapeZone, show a - 1 + 1 = a by omega,
      tapeRow_blank c (a - 1) (fun i => by have := hp i; omega) hl]
  have hr0 : readState c (a - 1) = fun _ => (none, false) := by
    funext i
    have h := hp i
    simp only [readState, headAt]
    rw [if_neg (by omega)]
    simp [show c.workTapePos i ≠ a - 1 - 1 by omega]
  have hdrop : ([some (sweepBoundary (Γ := Γ) (k := M.k))] : List _).drop M.k = [] := by
    apply List.drop_eq_nil_of_le
    simpa using hk
  have hturn : (sweepTM M).tm.step
      (sweepRevCfg (some (.growLeft q ⟨M.k, by omega⟩)) p (z - M.k)
        ((blankRow M.k false).map (fun b => some (sweepSymbol b)) ++ (D ++ [some sweepBoundary]))
        [] out) =
      sweepCfg (some (.read q (readState c (a - 1)))) p (z - M.k + 1)
        [some sweepBoundary] (F.map (fun b => some (sweepSymbol b)) ++ [some sweepBoundary]) out := by
    change ((sweepTM M).tm.tr (.growLeft q ⟨M.k, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, lt_self_iff_false, ↓reduceDIte]
    rw [sweep_turn_right]
    simp only [hr0, hf, List.map_append, List.append_assoc, D, List.tail_nil]
  have hread := sweep_run (sweepTM M).tm (fun s => SweepState.read q s) sweepSymbol readVisit
    (by intro s b inp; rfl) p out F (readState c (a - 1)) (z - M.k + 1)
    [some sweepBoundary] [some sweepBoundary]
  have hfold : sweepFold readVisit (readState c (a - 1)) F =
      (readState c (a + n), R) := by
    simpa [F, R, show a - 1 + (n + 1 : ℕ) = a + n by omega] using
      read_zone c (a - 1) (n + 1)
  have hflen : F.length = (n + 1) * M.k := tapeZone_length c _ _ _
  rw [hfold, hflen] at hread
  have hend : (sweepTM M).tm.step
      (sweepCfg (some (.read q (readState c (a + n)))) p
        (z - M.k + 1 + ((n + 1) * M.k : ℕ))
        (R.map (fun b => some (sweepSymbol b)) |>.reverse |>.append [some sweepBoundary])
        [some sweepBoundary] out) =
      sweepCfg (some (.growRight q (readState c (a + n)) 0)) p
        (z - M.k + 1 + ((n + 1) * M.k : ℕ))
        (R.map (fun b => some (sweepSymbol b)) |>.reverse |>.append [some sweepBoundary])
        [some sweepBoundary] out := by
    have hsym : (sweepCfg (some (SweepState.read q (readState c (a + n)))) p
        (z - M.k + 1 + ((n + 1) * M.k : ℕ))
        (R.map (fun b => some (sweepSymbol b)) |>.reverse |>.append [some sweepBoundary])
        [some sweepBoundary] out).workTapeSymbols = fun _ => some sweepBoundary := by
      funext i
      exact sweepTape_read _ _ _
    change ((sweepTM M).tm.tr (.read q (readState c (a + n))) _ _).apply _ = _
    rw [hsym]
    exact sweepCfg_stay _ _ _ _ _ _ _
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_succ_eq_step']
  unfold sweepStart
  rw [hs]
  dsimp only [Option.map]
  rw [sweep_grow_left_block, hdrop]
  change (sweepTM M).tm.step ((sweepTM M).tm.runFrom
    ((sweepTM M).tm.step (sweepRevCfg (some (.growLeft q ⟨M.k, by omega⟩)) p (z - M.k)
      ((blankRow M.k false).map (fun b => some (sweepSymbol b)) ++ (D ++ [some sweepBoundary]))
      [] out)) ((n + 1) * M.k)) = _
  rw [hturn, hread]
  exact hend

/-- The second half grows the right guard, executes the native input/output
action once, rewrites the zone, and enters the next boundary configuration.
**Proof sketch.** The head upper bound identifies the completed read table with
the source's scanned symbols. Append a blank right block carrying the last
block's head flags, then place its boundary and perform the source input/output
action while turning left. The reverse transduction applies the source action
to every block. At the left boundary, install the next source state (or halt),
and identify the resulting zipper with the enlarged canonical zone. -/
private lemma sweep_finish {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) {x : List Γ} (c : Cfg M.k Γ M.State x)
    (q : M.State) (a : ℤ) (n : ℕ) (z : ℤ)
    (hp : ∀ i, c.workTapePos i < a + n)
    (hr : ∀ i, c.workTapes i (a + n) = none) :
    (sweepTM M).tm.runFrom
      (sweepCfg (some (.growRight q (readState c (a + n)) 0)) (sweepPos M.k c.inputPos) z
        (((tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)).map
          (fun b => some (sweepSymbol b))).reverse ++ [some sweepBoundary])
        [some sweepBoundary] (c.output.map (sweepEmbed Γ M.k)))
      (M.k + 1 + (n + 2) * M.k + 1) =
    sweepStart M ((M.tm.tr q c.inputSymbol c.workTapeSymbols).apply c) (a - 1) (n + 2)
      (z + M.k - 1 - ((n + 2) * M.k : ℕ)) := by
  let act := M.tm.tr q c.inputSymbol c.workTapeSymbols
  let p := sweepPos M.k c.inputPos
  let out := c.output.map (sweepEmbed Γ M.k)
  let s := readState c (a + n)
  let R := tapeZone (fun j => tapeRow c j true) (a - 1) (n + 1)
  let W := tapeZone (fun j => tapeRow c j true) (a - 1) (n + 2)
  let V := tapeZone (fun j => tapeRow (act.apply c) j false) (a - 1) (n + 2)
  let put : SweepCell Γ M.k → Option (SweepAlphabet Γ M.k) := fun b => some (sweepSymbol b)
  let p' := sweepPos M.k (act.apply c).inputPos
  let out' := (act.apply c).output.map (sweepEmbed Γ M.k)
  have hrs : (fun i => (s i).1) = c.workTapeSymbols := by
    funext i
    simp only [s, readState, if_pos (hp i)]
  have hrow : rightRow s = tapeRow c (a + n) true := by
    unfold rightRow tapeRow
    apply List.map_congr_left
    intro i _
    have hh : c.workTapePos i ≠ a + n := by have := hp i; omega
    simp [s, readState, hr i, headAt, hh]
  have hwhole : W = R ++ rightRow s := by
    rw [hrow]
    dsimp [W, R]
    rw [show n + 2 = (n + 1) + 1 by omega, tapeZone_append]
    simp only [tapeZone, List.append_nil]
    rw [show a - 1 + (n + 1 : ℕ) = a + n by omega]
  have hbuf : (((rightRow s).map put).reverse.append ((R.map put).reverse ++ [some sweepBoundary])) =
      (W.map put).reverse ++ [some sweepBoundary] := by
    rw [hwhole]
    simp [List.map_append, List.reverse_append, List.append_assoc]
  have hdrop : ([some (sweepBoundary (Γ := Γ) (k := M.k))] : List _).drop M.k = [] := by
    apply List.drop_eq_nil_of_le
    simpa using hk
  have hturn : (sweepTM M).tm.step
      (sweepCfg (some (.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
        ((W.map put).reverse ++ [some sweepBoundary]) [] out) =
      sweepRevCfg (some (.write q c.inputSymbol c.workTapeSymbols (fun _ => false)))
        p' (z + M.k - 1) [some sweepBoundary] ((W.map put).reverse ++ [some sweepBoundary]) out' := by
    have hin := sweepInput_read c
      (sweepCfg (some (SweepState.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
        ((W.map put).reverse ++ [some sweepBoundary]) [] out) rfl
    change ((sweepTM M).tm.tr (.growRight q s ⟨M.k, by omega⟩) _ _).apply _ = _
    simp only [sweepTM, lt_self_iff_false, ↓reduceDIte]
    rw [hin, hrs]
    change (⟨act.inputTape, fun _ => (some (some sweepBoundary), .neg),
      act.output.map Sum.inl, some (.write q c.inputSymbol c.workTapeSymbols (fun _ => false))⟩ :
      Action 1 (SweepAlphabet Γ M.k) (SweepState Γ M.State M.k)).apply _ = _
    rw [sweep_turn_left]
    have hm : moveInputPos p act.inputTape = p' := sweepPos_move _ _ _
    rw [hm]
    have ho : out ++ (act.output.map Sum.inl).toList = out' := by
      dsimp [out, out', Action.apply]
      cases act.output <;> simp [sweepEmbed, List.map_append]
    rw [ho]
    rfl
  have hzero : (fun i => headAt c i (a - 1 + (n + 2 : ℕ))) = fun _ => false := by
    funext i
    have hh : c.workTapePos i ≠ a - 1 + (n + 2 : ℕ) := by have := hp i; omega
    simpa only [headAt, decide_eq_false_iff_not] using hh
  have hfold : sweepFold (writeVisit act) (fun _ => false) W.reverse =
      (fun i => headAt c i (a - 1), V.reverse) := by
    have h := write_zone c act (a - 1) (n + 2)
    rw [hzero] at h
    exact h
  have hwlen : W.length = (n + 2) * M.k := tapeZone_length c _ _ _
  have hwrite := sweep_run_reverse (sweepTM M).tm
    (fun right => SweepState.write q c.inputSymbol c.workTapeSymbols right)
    sweepSymbol (writeVisit act) (by intro right b inp; rfl) p' out'
    W.reverse (fun _ => false) (z + M.k - 1) [some sweepBoundary] [some sweepBoundary]
  simp only [List.length_reverse, hwlen, hfold, List.map_reverse, List.reverse_reverse] at hwrite
  have hlast : (sweepTM M).tm.step
      (sweepRevCfg (some (.write q c.inputSymbol c.workTapeSymbols (fun i => headAt c i (a - 1))))
        p' (z + M.k - 1 - ((n + 2) * M.k : ℕ))
        (V.map put ++ [some sweepBoundary]) [some sweepBoundary] out') =
      sweepStart M (act.apply c) (a - 1) (n + 2)
        (z + M.k - 1 - ((n + 2) * M.k : ℕ)) := by
    have hsym : (sweepRevCfg
        (some (SweepState.write q c.inputSymbol c.workTapeSymbols (fun i => headAt c i (a - 1))))
        p' (z + M.k - 1 - ((n + 2) * M.k : ℕ))
        (V.map put ++ [some sweepBoundary]) [some sweepBoundary] out').workTapeSymbols =
        fun _ => some sweepBoundary := by
      funext i
      exact sweepTape_read _ _ _
    change ((sweepTM M).tm.tr (.write q c.inputSymbol c.workTapeSymbols _) _ _).apply _ = _
    rw [hsym]
    exact sweepRevCfg_stay _ _ _ _ _ _ _
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_succ_eq_step', sweep_grow_right_block, hdrop]
  change (sweepTM M).tm.step ((sweepTM M).tm.runFrom
    ((sweepTM M).tm.step (sweepCfg (some (.growRight q s ⟨M.k, by omega⟩)) p (z + M.k)
      ((rightRow s).map put |>.reverse |>.append ((R.map put).reverse ++ [some sweepBoundary]))
      [] out)) ((n + 2) * M.k)) = _
  rw [hbuf, hturn, hwrite]
  exact hlast

/-- One source transition is one bounded burst, preserving the complete zone
shape and growing it by one block at each end. -/
private lemma sweep_step {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) {x : List Γ} (c : Cfg M.k Γ M.State x)
    (q : M.State) (hs : c.state = some q) (a : ℤ) (n : ℕ) (z : ℤ)
    (hp : ∀ i, a ≤ c.workTapePos i ∧ c.workTapePos i < a + n)
    (hl : ∀ i, c.workTapes i (a - 1) = none)
    (hr : ∀ i, c.workTapes i (a + n) = none) :
    (sweepTM M).tm.runFrom (sweepStart M c a n z) ((2 * n + 5) * M.k + 4) =
      sweepStart M (M.tm.step c) (a - 1) (n + 2) (z - M.k) := by
  rw [show (2 * n + 5) * M.k + 4 =
    (M.k + 1 + (n + 1) * M.k + 1) + (M.k + 1 + (n + 2) * M.k + 1) by ring,
    MultiTapeTM.runFrom_add, sweep_prepare M hk c q hs a n z (fun i => (hp i).1) hl,
    sweep_finish M hk c q a n _ (fun i => (hp i).2) hr]
  have hz : z - M.k + 1 + ((n + 1) * M.k : ℕ) + M.k - 1 - ((n + 2) * M.k : ℕ) =
      z - M.k := by push_cast; ring
  rw [hz]
  simp only [MultiTapeTM.step, hs]

/-- Exact transition count after a given number of source steps. -/
private def sweepTime (k : ℕ) : ℕ → ℕ
  | 0 => 2 * k + 2
  | t + 1 => sweepTime k t + ((4 * t + 7) * k + 4)

/-- Summing the exact per-step costs gives a quadratic polynomial. -/
private lemma sweepTime_eq (k t : ℕ) :
    sweepTime k t = 2 * k * t ^ 2 + (5 * k + 4) * t + (2 * k + 2) := by
  induction t with
  | zero => simp [sweepTime]
  | succ t ih => rw [sweepTime, ih]; ring

/-- A single constant bounds initialization and all sweeps, at every input size. -/
private lemma sweepTime_le (k t : ℕ) : sweepTime k t ≤ (9 * k + 6) * (t + 1) ^ 2 := by
  have hpow : 1 ≤ (t + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  have ht : t ≤ (t + 1) ^ 2 :=
    (Nat.le_succ _).trans (by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have ht2 : t ^ 2 ≤ (t + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ _) _
  rw [sweepTime_eq]
  calc
    2 * k * t ^ 2 + (5 * k + 4) * t + (2 * k + 2)
        ≤ 2 * k * (t + 1) ^ 2 + (5 * k + 4) * (t + 1) ^ 2 +
          (2 * k + 2) * (t + 1) ^ 2 := by
            exact Nat.add_le_add
              (Nat.add_le_add (Nat.mul_le_mul_left _ ht2) (Nat.mul_le_mul_left _ ht))
              (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 * k + 2) hpow)
    _ = (9 * k + 6) * (t + 1) ^ 2 := by ring

/-- Up to the source's first halt, initialized runs agree at every macro boundary.
**Proof sketch.** Initialization gives time zero. At each live source state,
the elapsed-time support bound justifies fresh blank guards; the macro-step
lemma advances both the source configuration and the zone radius by one. -/
private lemma sweep_run_to_halt {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (hk : 0 < M.k) (x : List Γ) (τ : ℕ)
    (hlive : ∀ t < τ, (M.tm.runFrom (M.tm.initCfg x) t).state ≠ none) :
    ∀ t ≤ τ,
      (sweepTM M).tm.runFrom ((sweepTM M).tm.initCfg (x.map (sweepEmbed Γ M.k))) (sweepTime M.k t) =
        sweepStart M (M.tm.runFrom (M.tm.initCfg x) t) (-(t : ℤ)) (2 * t + 1)
          (-(t : ℤ) * M.k - 1) := by
  intro t
  induction t with
  | zero => intro _; simpa [sweepTime] using sweep_init M x
  | succ t ih =>
    intro ht
    obtain ⟨q, hs⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
    obtain ⟨hp, hc⟩ := source_bounds M x t
    have hpos : ∀ i, -(t : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
        (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i < -(t : ℤ) + (2 * t + 1 : ℕ) := by
      intro i
      have := hp i
      constructor <;> omega
    have hleft : ∀ i, (M.tm.runFrom (M.tm.initCfg x) t).workTapes i (-(t : ℤ) - 1) = none := by
      intro i
      exact hc i _ (by left; omega)
    have hright : ∀ i, (M.tm.runFrom (M.tm.initCfg x) t).workTapes i
        (-(t : ℤ) + (2 * t + 1 : ℕ)) = none := by
      intro i
      exact hc i _ (by right; omega)
    rw [sweepTime, MultiTapeTM.runFrom_add, ih (by omega)]
    rw [show (4 * t + 7) * M.k + 4 = (2 * (2 * t + 1) + 5) * M.k + 4 by ring]
    rw [sweep_step M hk _ q hs _ _ _ hpos hleft hright,
      ← MultiTapeTM.runFrom_succ_eq_step']
    have ha : -(t : ℤ) - 1 = -(t + 1 : ℕ) := by omega
    have hn : 2 * t + 1 + 2 = 2 * (t + 1) + 1 := by omega
    have hz : -(t : ℤ) * M.k - 1 - M.k = -(t + 1 : ℕ) * M.k - 1 := by push_cast; ring
    rw [ha, hn, hz]

/-- **One work tape suffices** [AB09, Claim 1.6]: a `Γ`-machine computing `f` within
`T` is simulated by a machine with a single work tape, over an enlarged finite
alphabet, within `c · (T n + 1)²`.

**Proof sketch.** For `k = 0`, simulate `M` directly with one unused work tape.
For `k ≥ 1`, the single work tape of `M'` stores the `k` tapes of `M` interleaved:
cell `j·k + i` of the simulated layout holds cell `j` of tape `i` (centered at `0` in
both directions). The alphabet is enlarged to cells carrying a *tagged payload*
`Option Γ` — so a marked blank is representable, which a bare `Γ × flag` product
would miss — together with a "head here" flag and zone-boundary tags; `Γ` embeds via
`e` as an unmarked non-blank payload. To simulate one step of `M`, `M'` sweeps its work tape once
left-to-right across the visited zone recording the `k` marked symbols in its state,
computes `M`'s transition, and sweeps back right-to-left updating the marked cells and
moving the marks. After `t` steps of `M` the visited zone spans `O(k · (t + 1))`
cells, so each simulated step costs `O(k · (T n + 1))` and the total is
`c · (T n + 1)²`. Input reads and output emissions pass through unchanged.

**Implementation note.** The forward pass records the preceding block's head
flags in the cells; the return pass carries the following block's flags in its
finite control. This implements both movement directions using exactly the two
stated sweeps. Each macro-step extends the zone by one blank block at each end.
For positive `k`, initialization costs `2k + 2` transitions and source step `t`
costs `(4t + 7)k + 4`; `sweepTime_le` supplies the constant `9k + 6`.
The zero-tape branch is a separate lockstep embedding with constant `1`. -/
theorem one_work_tape {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) ^ 2 := by
  by_cases hk : M.k = 0
  · refine ⟨Γ, inferInstance, inferInstance, Function.Embedding.refl Γ,
      unusedTapeTM M hk, 1, rfl, ?_⟩
    intro x
    simpa only [Function.Embedding.coe_refl, List.map_id, one_mul] using
      ((unusedTape_computes M hk f T hM) x).mono
        (show T x.length ≤ (T x.length + 1) ^ 2 from
          (Nat.le_succ _).trans (by
            rw [pow_two]
            exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
  · refine ⟨SweepAlphabet Γ M.k, inferInstance, inferInstance, sweepEmbed Γ M.k,
      sweepTM M, 9 * M.k + 6, rfl, ?_⟩
    intro x
    obtain ⟨hhalt, hout⟩ := (computesInTime_iff M x (f x) (T x.length)).mp (hM x)
    have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T x.length, hhalt⟩
    let τ := Nat.find hex
    have hτ : (M.tm.runFrom (M.tm.initCfg x) τ).state = none := Nat.find_spec hex
    have ht : τ ≤ T x.length := Nat.find_min' hex hhalt
    have hlive : ∀ t < τ, (M.tm.runFrom (M.tm.initCfg x) t).state ≠ none :=
      fun _ h => Nat.find_min hex h
    have hrun := sweep_run_to_halt M (Nat.pos_of_ne_zero hk) x τ hlive τ (le_refl _)
    have houtτ : (M.tm.runFrom (M.tm.initCfg x) τ).output = f x := by
      have h := M.tm.runFrom_output_eq_of_halt (M.tm.initCfg x) ht hτ
      exact h.symm.trans hout
    have hc : (sweepTM M).ComputesInTime (x.map (sweepEmbed Γ M.k))
        ((f x).map (sweepEmbed Γ M.k)) (sweepTime M.k τ) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [hrun]
      constructor
      · change (M.tm.runFrom (M.tm.initCfg x) τ).state.map (fun q => SweepState.growLeft q 0) = none
        rw [hτ]
        rfl
      · change (M.tm.runFrom (M.tm.initCfg x) τ).output.map (sweepEmbed Γ M.k) = _
        rw [houtτ]
    exact hc.mono ((sweepTime_le M.k τ).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right ht 1) 2)))

/-- One work tape and the binary alphabet suffice simultaneously: the composition of
[AB09, Claim 1.6] with [AB09, Claim 1.5], possible because alphabet reduction
preserves the number of work tapes.

**Proof sketch.** Apply `Turing.FinTM.one_work_tape` to `M` with `Γ = Bool`,
obtaining a one-work-tape machine over some `Γ'` that computes `f` via an embedding
`Bool ↪ Γ'` within `c₁ · (T n + 1)²` — exactly the hypothesis of
`Turing.FinTM.alphabet_reduction`, which keeps `k = 1` and returns to the binary
alphabet within `c₂ · (c₁ · (T n + 1)² + 1) ≤ c · (T n + 1)²`. -/
theorem one_work_tape_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTime f fun n => c * (T n + 1) ^ 2 := by
  obtain ⟨Γ', instF, instD, e, M₁, c₁, hk₁, h₁⟩ := one_work_tape M f T hM
  haveI := instF
  haveI := instD
  obtain ⟨c₂, M₂, hk₂, h₂⟩ :=
    alphabet_reduction e M₁ f (fun n => c₁ * (T n + 1) ^ 2) h₁
  refine ⟨M₂, c₂ * (c₁ + 1), by rw [hk₂, hk₁], fun x => (h₂ x).mono ?_⟩
  have hpow : 0 < (T x.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  calc c₂ * (c₁ * (T x.length + 1) ^ 2 + 1)
      ≤ c₂ * (c₁ * (T x.length + 1) ^ 2 + (T x.length + 1) ^ 2) :=
        Nat.mul_le_mul (le_refl c₂) (Nat.add_le_add_left hpow _)
    _ = c₂ * (c₁ + 1) * (T x.length + 1) ^ 2 := by ring

end Turing.FinTM

/-! ### Space annotation (§13 Z4; additive, shared-file mechanism, flagged
for the A-S2 audit) -/

namespace Turing.FinTM

/-- The one-work-tape reduction preserves space up to a constant: the
single-tape machine of `Turing.FinTM.one_work_tape` can be taken with an
all-time space bound of coefficient-constant shape in the source's. Part
of the Z4 space annotation (`machine-library-design.md` §13), plan §2.7's
fallback route to the space-efficient universal (Ex 4.1).

**Proof sketch** (round-1 repair, A-S2-2 of `audits/zone-infra-findings.md`
— the received `sweepTM` witness does NOT satisfy this bound: its
`.growLeft`/`.growRight` phases extend the swept window unconditionally
every macro-step, so a stationary-work-head input scanner has source space
`1` but simulator space `Ω(n)`; the audit's counterexample is binding).
The fill constructs a **demand-grown** sweep witness, reusing and
refactoring the existing sweep infrastructure without copying it: extend a
boundary only when a simulated head first crosses it. Each source tape's
visited interval contains the origin, so the union's cardinality is at
most the sum of the source cardinalities — the total source space; an
interleaved `M.k`-cells-per-coordinate realization pays a factor `M.k`
and a constant boundary allowance, absorbed into `c`. Mid-sweep visits lie
inside the represented source-visited intervals through the current
transition plus the allowance; a halted simulation is fixed. The space
conclusion ranges over **all** `Γ'`-words: for nonempty `Γ`, a
finite-control retraction fixing `e` simulates the same-length retracted
source input (so `hS` applies with no monotonicity); for empty `Γ`, every
source word is empty and an immediately halting one-tape machine suffices;
for `M.k = 0`, the unused-tape embedding visits one cell, inside
`c * (S + 1)`. -/
theorem one_work_tape_spaceUsed {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T S : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T)
    (hS : ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ S x.length) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTimeVia e f (fun n => c * (T n + 1) ^ 2) ∧
      ∀ x t, M'.tm.spaceUsed (M'.tm.initCfg x) t ≤ c * (S x.length + 1) := by
  sorry

/-- The binary one-work-tape normal form preserves space up to a constant:
the composed conversion of `Turing.FinTM.one_work_tape_binary` with the
space clause carried through both stages. This is the exact deliverable
shape of plan §2.7's fallback for Ex 4.1/Thm 4.8: a space-faithful route
into the one-tape binary normal form.

**Proof sketch.** Chain the **corrected** first stage
(`Turing.FinTM.one_work_tape_spaceUsed`, whose round-2 route is the
demand-grown witness) with `Turing.FinTM.alphabet_reduction_spaceUsed`;
with first-stage coefficient `c₁` and second-stage `c₂`, both clauses are
absorbed by the single coefficient `c₂ * (c₁ + 1)` (the round-1 audit's
composition calculation). -/
theorem one_work_tape_binary_spaceUsed (M : FinTM Bool)
    (f : List Bool → List Bool) (T S : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T)
    (hS : ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ S x.length) :
    ∃ (M' : FinTM Bool) (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTime f (fun n => c * (T n + 1) ^ 2) ∧
      ∀ x t, M'.tm.spaceUsed (M'.tm.initCfg x) t ≤ c * (S x.length + 1) := by
  sorry

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Codes2Tape.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.NDCodes

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic two-work-tape machine codes (Z3)

The deterministic code layer currently covers only the one-work-tape
binary normal form (`Turing.CodeTM`/`Turing.MachineCode`/
`Turing.EffectiveMachineCode`, `Encoding.lean`), which is why the received
time hierarchy arrives at `f²` strength (plan §2.1): converting to that
normal form costs a square. This file is §13's Z3: the **deterministic
two-work-tape** code scheme, the codes the two-work-tape universal machine
(stage 1, plan §4b) reads, over **the same `Turing.actionBits₂` record
format** that `Turing.CodeNDTM` fixed for the nondeterministic two-tape
codes (design §13a: one branch instead of two — never a second
serialization). The file name reads *codes for two-tape machines*
(decision 13.3, renamed from `Codes2` by the user).

Mirrors: `Turing.CodeTM` → `Turing.Code2TM`; `Turing.MachineCode` →
`Turing.MachineCode2`; `Turing.EffectiveMachineCode` →
`Turing.EffectiveMachineCode2`; and, per the P3.2 lesson (a variable-code
consumer needs uniformly timed decoding — `EffectiveMachineCode` bounds no
decoding time), `UniformMachineCode` (`Diagonalization/EXPCOM.lean`) →
`Turing.UniformMachineCode2`.

## Status: statement skeleton (§13 statement phase, tranche A-S2)

The structures and serialization are real definitions; the two existence
statements are `sorry`d with proof sketches naming the received routes.

## Main definitions and results

* `Turing.Code2TM`, `Turing.Code2TM.serialize` — the deterministic
  two-work-tape normal form and its fixed, scheme-independent
  serialization (27 `Turing.actionBits₂` records per state: three input
  reads by three reads on each of the two work tapes).
* `Turing.MachineCode2`, `Turing.EffectiveMachineCode2`,
  `Turing.UniformMachineCode2` — the scheme laws, the effective scheme,
  and the uniformly timed scheme.
* `Turing.exists_effectiveMachineCode2`,
  `Turing.exists_uniformMachineCode2` — the sorried existence statements.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge University Press, 2009. (§1.4, machine codes;
  §1.7/§3.1 for the two-tape consumer.)
-/

namespace Turing

/-- The coded normal form of a deterministic machine with **two** work
tapes: a binary-alphabet machine with state space `Fin (numStates + 1)`
(never empty). Two work tapes, not one, because the Hennie-Stearns
conversion lands there at `O(T log T)` and the two-tape universal machine
(its consumer) runs such codes at linear overhead — the whole point of
strengthening past `Turing.CodeTM`'s square. Mirrors `Turing.CodeTM` and
`Turing.CodeNDTM`. [AB09, §1.4, §1.7] -/
structure Code2TM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying two-work-tape deterministic machine -/
  tm : MultiTapeTM 2 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded two-tape machine. -/
def Code2TM.toFinTM (M : Code2TM) : FinTM Bool where
  k := 2
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The **fixed, scheme-independent** canonical serialization, mirroring
`Turing.CodeTM.serialize` and `Turing.CodeNDTM.serialize` over the same
`Turing.actionBits₂` record: the state count, the initial state, then the
full transition table in the fixed enumeration order — states in `Fin`
order, then the input read and the two work reads each over `none`,
`some false`, `some true` (27 records per state; the nondeterministic
table's outermost choice bit is absent). This is the target format of
`Turing.EffectiveMachineCode2.canonizer` and the input format of the
two-work-tape universal machine. -/
def Code2TM.serialize (M : Code2TM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      (List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
            ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
              actionBits₂ (M.tm.tr q inp (workPair w₀ w₁)))

/-- The algebraic laws of a representation scheme for coded two-tape
machines, mirroring `Turing.MachineCode` [AB09, §1.4]: a total decoding
(property 1), an encoding, and recovery under arbitrary `true`-padding
(property 2 — every machine has infinitely many representations). -/
structure MachineCode2 where
  /-- encode a machine as a binary string -/
  encode : Code2TM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → Code2TM
  /-- a code followed by any amount of `true`-padding decodes to the
  machine (property 2) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine (padding by zero symbols).
Skeleton-time proof, mirroring `Turing.MachineCode.decode_encode`. -/
theorem MachineCode2.decode_encode (c : MachineCode2) (M : Code2TM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme for two-tape machines: the
algebraic laws together with a machine of this development computing the
fixed serialization of the decoded machine — the mirror of
`Turing.EffectiveMachineCode`, with the same Argument-A rationale (the
target `Turing.Code2TM.serialize` is scheme-independent). As there, the
canonizer's time bound is arbitrary: fixed-code consumers absorb it into
their constants, and variable-code consumers must use
`Turing.UniformMachineCode2` instead. -/
structure EffectiveMachineCode2 extends MachineCode2 where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's (arbitrary) time bound -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- **An effective two-tape code scheme exists** (spec, fill pending —
tranche A-S2).

**Proof sketch.** Mirror the received constructions over the
single-branch table: `encode := Code2TM.serialize` itself; `decode`
parses the `Turing.pairEncode`d state count, the initial state, and the
transition table by the received parser architecture
(`TCSlib.Complexity.TuringMachine.CodeParser`, retargeted to the
`Turing.actionBits₂` record at **27 records per state** — the
nondeterministic retarget's `2 · 27 = 54` without the choice bit, so its
minimum-length guard scales by exactly half), with the single-state
do-nothing machine as the fallback on parse failure and trailing
`true`-padding tolerated by the end-marker discipline (property 2); the
canonizer re-serializes the parsed record by the arbitrary-time
computability route of the received deterministic construction
(`TCSlib.Complexity.TuringMachine.MathlibBridge`), so no polynomial
canonizer is claimed. Fill obligations, named: the record parser and its
fallback totalization; the pad-tolerance lemma; the canonizer assembly
and its time bound. -/
theorem exists_effectiveMachineCode2 : Nonempty EffectiveMachineCode2 := by
  sorry

/-- A *uniformly timed* scheme for two-tape codes: the effective scheme
together with a bounded-acceptance simulator whose budget is one
polynomial **jointly** in the code length, input length, and time bound —
the mirror of `UniformMachineCode` (`Diagonalization/EXPCOM.lean`), which
exists because `EffectiveMachineCode2` deliberately bounds no decoding
time (the P3.2 lesson: with an arbitrary scheme, a variable-code consumer
can be made to pay unboundedly for decoding). -/
structure UniformMachineCode2 extends EffectiveMachineCode2 where
  /-- the uniformly timed bounded-acceptance simulator -/
  simulator : FinTM Bool
  /-- the simulator's single polynomial degree and coefficient -/
  simDegree : ℕ
  /-- on bounded acceptance, the simulator answers `[true]` within the
  uniform polynomial budget -/
  simulator_accepts : ∀ (α x : List Bool) (t : ℕ),
    (decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)
  /-- otherwise it answers `[false]` within the same budget -/
  simulator_rejects : ∀ (α x : List Bool) (t : ℕ),
    ¬(decode α).toFinTM.ComputesInTime x [true] t →
    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
      (simDegree * (α.length + x.length + t + 1) ^ simDegree)

/-- **A uniformly timed two-tape scheme exists** (spec, fill pending —
tranche A-S2).

**Proof sketch.** The concrete scheme of
`Turing.exists_effectiveMachineCode2` with the uniform simulator built as
in the received `exists_uniformMachineCode` route
(`Diagonalization/EXPCOM.lean`, P3.2 round 2): parse the nested input
keeping the deadline in binary; check the table's minimum-length guard by
binary arithmetic before any per-state iteration (a huge declared state
count is never expanded in unary; the guard constant halves against the
nondeterministic table); then run the clocked step-by-step simulation of
the decoded two-tape machine, charging one uniform polynomial jointly in
`|α| + |x| + t + 1`. The two-work-tape simulation is *easier* than the
received one-tape case for the step itself (the simulator hosts the two
coded tapes on two physical tapes — no tape reduction), and the Z1
virtual-input layer supplies the input discipline. -/
theorem exists_uniformMachineCode2 : Nonempty UniformMachineCode2 := by
  sorry

end Turing
```
