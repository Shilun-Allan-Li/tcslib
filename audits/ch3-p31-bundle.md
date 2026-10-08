# External audit pack — Chapter 3, phase P3.1 (oracle machines and classes), statement gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase P3.1 —
the bundled finite oracle machines, the nondeterministic oracle machine, and the
classes `Pᴼ`/`NPᴼ`. Statement phase per `workflow.md` §2-3; the gate closes on a
round with zero blockers and zero majors.

Audited at commit `edea2663` (branch `complexity/arora-barak-ch3-4`); the five
files under audit are byte-identical to their landing commit `2cf44f1d`. Under
audit: `TCSlib/Complexity/TuringMachine/OracleFinite.lean`,
`TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean`,
`TCSlib/Complexity/ClassOracle/{Classes,SATOracle}.lean`, and the
`ClassOracle.lean` facade — **10 sorried statements, plus the declared
skeleton-time proofs listed below**, which are part of the audited surface.

**Concurrent-round note**: the phase-P3.2 gate (relativization,
`audits/ch3-p32-pack.md`) is running in parallel and *builds on* this surface;
its auditor was invited to file "[P3.1]"-prefixed findings, which will be
triaged into this gate's rounds. Neither round edits the other's files.

## Brief for the auditor

Definitions, statements, docstrings, and the skeleton-time proofs' *statements*
(their tactic bodies are machine-checked; audit what they claim, not how).
Failure modes per `audits/TEMPLATE.md`: infidelity to [AB09, §3.4, Definitions
3.4-3.5, Example 3.6], trivialization, unprovability-as-stated, missing
hypotheses. Blind restatements for every definition; 2-5-sentence
true-as-stated arguments (or refutations) for every sorried statement; at
least **5 adversarial instantiations**; no blanket approvals.

The raw oracle model (`TuringMachine/Oracle.lean`, attached) was audited in the
chapter-1 campaign and is **frozen context**, not under re-audit: its
`WellFormed` discipline, the persistent query tape (with the documented
never-transfer-exact-DTIME-bounds caveat), and `queryString`'s extraction
convention are inherited design, flag-worthy only if a P3.1 statement misuses
them.

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch3-p31-sweep.log`, revision recorded at
  start): all five modules, 0 `error:` lines, fresh `.olean`s, exactly **10**
  `declaration uses 'sorry'` warnings (OracleNondeterministic 1, Classes 6,
  SATOracle 3).
* Style lint (`audits/logs/ch34-p31-p41-stylelint.log`): `ClassOracle` 0 FAIL /
  0 WARN; `TuringMachine` 0 FAIL with only the pre-existing size WARNs.
* Statement-freeze baseline: commit `edea2663` (= `2cf44f1d` for these files).
* The P0 reception gate closed before this round
  (`audits/ch34-p0-resolutions.md`); nothing in this phase touches that
  surface.

## Declared skeleton-time proofs (audited surface; `workflow.md` §2)

Pure-unfolding mirrors of proved chapter-1/2 infrastructure, proved at
skeleton time exactly as the chapter-2 `runWith` algebra precedent:

* `OracleNondeterministic.lean`: `runWith_nil`/`runWith_cons`/`runWith_append`,
  `stepWith_of_halt`/`runWith_of_halt`, `HaltsWithin.mono`,
  `AcceptsWithin.mono`, `toOracleNDTM_wellFormed`.
* `OracleFinite.lean`: `FinTM.toFinOracleTM_computesInTime` — the bundled
  embedding bridge, proved through the chapter-1-audited
  `OracleTM.computesInTime_ofMultiTapeTM` and `FinTM.computesInTime_iff`.

## Known deviations and design decisions (declared — verify each, flag others)

1. **`WellFormed` is bundled as a field** of `FinOracleTM` and `FinOracleNDTM`,
   so no oracle class can quantify over a machine with colliding special
   states; `q₀ = qQuery` stays deliberately allowed. This discharges the
   chapter-1 obligation verbatim.
2. **Time is the only resource at this layer** — no oracle space measure is
   introduced (deliberate; the chapters-3/4 campaign defines space for plain
   and nondeterministic machines first).
3. **Clocks are relative to the given oracle**: `DecidesInTime` is a promise
   about runs with *that* oracle. [BGS75]'s all-oracle clock convention is
   deliberately **not** baked into the classes; phase P3.2 attaches budgets
   extrinsically (its pack carries that design). The seeded question: is this
   split the right one, or must the class definitions themselves quantify over
   oracles anywhere?
4. **`NPᴼ` is machine-first**: `⋃ c, NTIMEOracle O (n^c + 1)` *is* the
   definition, directly following [AB09, Definition 3.5]; no certificate form
   is claimed relative to an oracle (a relativized Theorem 2.6 is explicitly
   out of scope).
5. **The oracle NDTM's query step consumes-and-ignores a choice bit**, keeping
   one bit per step uniformly and the certificate reading of choice words
   intact; the alternative (query steps consume no bit) is rejected in the
   module docstring.
6. **Class normal forms mirror the unrelativized ones exactly**:
   `DTIMEOracle`/`NTIMEOracle` with `c · T n` absorption, the classes as
   `⋃ c, … (n ^ c + 1)`.
7. **Ex 3.6(1) is rendered on the set complement** `SATᶜ` (no formula-syntax
   carrier for "unsatisfiable formulae"; `SAT`'s fallback convention makes
   every non-well-formed string satisfiable, hence *out* of `SATᶜ` — check
   this reading against the book's `co-SAT` and flag if the fallback
   interacts badly).
8. **The workhorse sketch** (`mem_POracle_of_polyTimeReducible`) names §12
   seam-composition as its intended glue with the audited `bufferedCompTM`
   dispatch as the fallback — the §12 gate runs concurrently; the sketch does
   not depend on its outcome for the *statement*.
9. `SATOracle.lean` imports `CookLevin/Hardness.lean` for `SAT_NPHard`
   (`theorem SAT_NPHard : NPHard SAT`, chapter-2-audited; the 8.9k-line home
   file is not attached — the statement is quoted here and its gate records
   are `audits/ch2-epoch*`).

## Specific questions (prioritized)

1. **Definition fidelity** ([AB09, Def 3.4-3.5]): blind-restate `FinOracleTM`,
   `OracleNDTM`, `FinOracleNDTM`, `DTIMEOracle`, `NTIMEOracle`, `POracle`,
   `NPOracle` and compare. Does anything about the bundled `WellFormed`, the
   persistent query tape, or the `k + 1`-tape layout weaken or strengthen the
   book's classes?
2. **The oracle-NDTM choice-bit convention** (deviation 5): exhibit any
   downstream consumer (Theorem 2.6-style certificate readings, the P3.2
   stage construction, `NPᴼ` monotonicity) for which consume-and-ignore at
   query steps is wrong or lossy.
3. **`POracle_eq_P_of_mem_P`** (Ex 3.6(2)): is the *statement* exactly the
   book's claim, and is the sketch's construction (virtual-input decider runs
   at query states, capture discipline, `queryString_length_le` budget)
   plausibly within the stated polynomial — in particular the exponent
   arithmetic `k·e + O(1)` when the query grows along the run?
4. **The one-query workhorse and complement closure**: are
   `mem_POracle_of_polyTimeReducible` and `compl_mem_POracle` stated at the
   right generality (arbitrary `O`, no well-formedness or decidability
   hypothesis on the *oracle*), and do the three `SATOracle` corollaries
   really reduce to them plus `SAT_NPHard` as sketched?
5. **Skeleton-time proof statements**: do the proved mirrors claim exactly
   their chapter-2 counterparts' content (especially
   `toFinOracleTM_computesInTime`'s "under every oracle" iff), with no
   accidental strengthening?
6. **Degenerate instantiations to attempt**: the empty oracle; `O = Set.univ`;
   a machine with `q₀ = qQuery` (allowed); `T n = 0` budgets in
   `DTIMEOracle`/`NTIMEOracle` (do the emptiness conventions match
   `DTIME`/`NTIME`'s?); `L = ∅` and `L = Set.univ` through the workhorse
   lemma.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch3-p31-findings.md`; the gate closes on zero blockers and majors.


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


## ===== TCSlib/Complexity/ClassOracle.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassOracle.Classes
import TCSlib.Complexity.ClassOracle.SATOracle

/-!
# Oracle complexity classes

[AB09, §3.4, Definition 3.5]: `Pᴼ` and `NPᴼ`, the polynomial-time classes
relative to an oracle `O`, over the bundled finite oracle machines of
`TCSlib.Complexity.TuringMachine.OracleFinite` and
`TCSlib.Complexity.TuringMachine.OracleNondeterministic`. The headline
statements of this surface (phase P3.1 of `AroraBarakChapters3-4Plan.md`) are
the workhorse `Complexity.mem_POracle_of_polyTimeReducible` (`L ≤ₚ O → L ∈ Pᴼ`),
Example 3.6's redundancy of polynomial-time oracles, and the `SAT`-oracle sanity
theorems; the relativization theorem [AB09, Theorem 3.7] is phase P3.2.

## Contents

- `ClassOracle.Classes`: `DTIMEOracle`, `NTIMEOracle`, `POracle`, `NPOracle`,
  the inclusion and closure statements, and Example 3.6(2)
- `ClassOracle.SATOracle`: Example 3.6(1) and `NP ⊆ P^SAT` / `coNP ⊆ P^SAT`

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.4.)
-/

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


## ===== TCSlib/Complexity/TuringMachine/Finite.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Basic
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bundled finite Turing machines

The raw model `Turing.MultiTapeTM k Symbol State` deliberately does not require `Symbol` or
`State` to be finite: semantics, simulations, and resource counting do not need it, and
compound state types arise freely in constructions. Finiteness is nevertheless
mathematically essential for complexity theory — with infinitely many states a machine can
memorize its whole input in the state and decide any language in linear time, and an
infinite transition table has no string encoding.

This file provides the bundled layer `Turing.FinTM`: a machine together with `Fintype` and
`DecidableEq` instances for its state type. All headline definitions of the Chapter 1
development (`DTIME`, `P`, machine encodings, the universal machine) are stated exclusively
over `FinTM`, so the finiteness hypothesis can never be dropped by accident. The instances
are carried as *data* (not `Finite` propositions) because the machine-encoding function
`⌞M⌟` must enumerate the transition table.

The alphabet parameter `Symbol` stays explicit and unbundled: the Chapter 1 headline
definitions fix `Symbol := Bool` (see `TCSlib.Complexity.ClassP.DTIME`), and results that
need a finite alphabet for a general `Symbol` take `[Fintype Symbol]` hypotheses at use
sites.

## Main definitions

* `Turing.FinTM Symbol` — a multi-tape TM over alphabet `Option Symbol` with a bundled
  finite state type. [AB09, §1.2]
* `Turing.FinTM.ComputesInTime` — the machine halts on `input` within `t` steps with
  `output` on the output tape (time-only variant of
  `Turing.MultiTapeTM.ComputesInTimeAndSpace`). [AB09, Definition 1.3]
* `Turing.FinTM.ComputesFunInTime` — the machine computes `f` in time `T`.
  [AB09, Definition 1.3]
* `Turing.FinTM.Computes` — the machine computes `f` with no time constraint; the
  notion of computability underlying the uncomputability results. [AB09, §1.4, p. 20]

## Main results

* `Turing.FinTM.ComputesInTime.mono` — halting is absorbing, so the time bound can be
  weakened.
* `Turing.FinTM.ComputesInTime.output_unique` — determinism: a machine has at most one
  completed output on a given input.
* `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.Computes.exists_computesInTime_iff` —
  the space-free unfolding of a timed computation, and the completed-output
  characterization of a total machine (promoted from the epoch-1 fill).
* `Turing.FinTM.not_computesInTime_zero` — no machine computes anything in zero steps
  (the initial state is not the halting state).
* `Turing.MultiTapeTM.output_length_le`, `Turing.MultiTapeTM.output_prefix` — raw-layer
  output lemmas (at most one symbol is emitted per step, and output only grows), stated
  here rather than in the vendored `Deterministic.lean` to keep the vendored files
  unmodified.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.3.)
-/

namespace Turing

/-!
### Raw-layer output lemmas

Additions on top of the vendored files (kept here so the vendored `Deterministic.lean`
stays byte-comparable with upstream).
-/

namespace MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The output of an initialized run after `t` steps has length at most `t`: each step
appends at most one symbol.

**Proof sketch.** Induction on `t` with `Turing.MultiTapeTM.runFrom_succ_eq_step'` and
`Turing.MultiTapeTM.step_output` (`Option.toList` has length at most one); the initial
output is `[]`. -/
theorem output_length_le (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    ((tm.runFrom (tm.initCfg input) t).output).length ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    have hone : (tm.outputSymbol (tm.runFrom (tm.initCfg input) t)).toList.length ≤ 1 := by
      cases tm.outputSymbol (tm.runFrom (tm.initCfg input) t) <;> simp
    simp only [List.length_append]
    omega

/-- Output is monotone along a run: the output at an earlier time is a prefix of the
output at any later time.

**Proof sketch.** It suffices to treat one step (`Turing.MultiTapeTM.step_output`: a
step appends), then induct on the difference using
`Turing.MultiTapeTM.runFrom_add` and transitivity of `List.IsPrefix`. -/
theorem output_prefix (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    {t t' : ℕ} (h : t ≤ t') :
    (tm.runFrom cfg t).output <+: (tm.runFrom cfg t').output := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  rw [MultiTapeTM.runFrom_add]
  generalize tm.runFrom cfg t = c
  induction d with
  | zero => simp
  | succ d ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    exact ih.trans (List.prefix_append _ _)

end MultiTapeTM

/-- A multi-tape Turing machine over the alphabet `Option Symbol` bundled with a finite
state type. This is the machine of [AB09, §1.2] up to the declared model variations
(append-only output tape, start-marker-free initialization — see the deviations list in
`TCSlib.Complexity.ClassP.DTIME`): the raw `MultiTapeTM` is internal plumbing, and
every headline complexity-theoretic definition is stated over `FinTM`.

The instances are data (`Fintype`/`DecidableEq`, not `Finite`) because encoding a machine
as a string requires enumerating its transition table. -/
structure FinTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible, needed to tabulate the transition function -/
  [decEqState : DecidableEq State]
  /-- the underlying machine -/
  tm : MultiTapeTM k Symbol State

namespace FinTM

attribute [instance] FinTM.fintypeState FinTM.decEqState

variable {Symbol : Type}

/-- The machine `M` halts on `input` within `t` steps with `output` written on its output
tape. Time-only variant of `Turing.MultiTapeTM.ComputesInTimeAndSpace` (the space used is
existentially discarded). [AB09, Definition 1.3] -/
def ComputesInTime (M : FinTM Symbol) (input output : List Symbol) (t : ℕ) : Prop :=
  ∃ s, M.tm.ComputesInTimeAndSpace input output t s

/-- The machine `M` computes the string function `f`, halting within `T |input|` steps on
every input. [AB09, Definition 1.3: "M computes f in T(n)-time"] -/
def ComputesFunInTime (M : FinTM Symbol) (f : List Symbol → List Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ input : List Symbol, M.ComputesInTime input (f input) (T input.length)

/-- The machine `M`, over alphabet `Γ`, computes the string function `f` on `α`-strings
*via* the symbol embedding `e : α ↪ Γ`: on every input `x.map e` it halts within
`T |x|` steps with `(f x).map e` on its output tape. This is how a machine over a
larger alphabet is said to compute a function on a smaller one; it is the interface of
the alphabet-robustness results [AB09, §1.3.1]. -/
def ComputesFunInTimeVia {α Γ : Type} (M : FinTM Γ) (e : α ↪ Γ)
    (f : List α → List α) (T : ℕ → ℕ) : Prop :=
  ∀ x : List α, M.ComputesInTime (x.map e) ((f x).map e) (T x.length)

/-- The machine `M` *computes* the string function `f`, with no time constraint: on
every input it eventually halts with `f input` on the output tape. This is the notion
of computability underlying the uncomputability results [AB09, §1.4, p. 20; §1.5];
`Turing.FinTM.ComputesFunInTime` is the time-bounded refinement, and the two are
related by `Turing.FinTM.ComputesFunInTime.computes` (below) and
`Turing.FinTM.Computes.exists_computesFunInTime`
(in `TCSlib.Complexity.Uncomputability.Computable`). -/
def Computes (M : FinTM Symbol) (f : List Symbol → List Symbol) : Prop :=
  ∀ input : List Symbol, ∃ t, M.ComputesInTime input (f input) t

/-- Halting is absorbing, so a time bound can be weakened: if `M` produces `output`
within `t` steps it also does so within any `t' ≥ t` steps.

**Proof sketch.** By `Turing.MultiTapeTM.runFrom_add` the run to step `t'` factors through
step `t`; the state there is `none`, so `Turing.MultiTapeTM.runFrom_of_halt` shows the
configuration no longer changes, and in particular state and output at step `t'` agree with
step `t`. The space used up to step `t'` exists (it is whatever `spaceUsed` evaluates to),
which discharges the existential. -/
theorem ComputesInTime.mono {M : FinTM Symbol} {input output : List Symbol} {t t' : ℕ}
    (h : M.ComputesInTime input output t) (hle : t ≤ t') :
    M.ComputesInTime input output t' := by
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h ⊢
  obtain ⟨s, hhalt, hout, -⟩ := h
  have hrun : M.tm.runFrom (M.tm.initCfg input) t' = M.tm.runFrom (M.tm.initCfg input) t := by
    conv_lhs => rw [← Nat.add_sub_cancel' hle]
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
  exact ⟨_, by rw [hrun]; exact hhalt, by rw [hrun]; exact hout, rfl⟩

/-- No machine computes anything in zero steps: the initial configuration is in the
initial state, which is not the halting state. In particular a time budget of `0`
(e.g. from a vanishing time bound) is never satisfiable. -/
theorem not_computesInTime_zero (M : FinTM Symbol) (input output : List Symbol) :
    ¬M.ComputesInTime input output 0 := by
  rintro ⟨s, hhalt, -⟩
  simp [MultiTapeTM.runFrom_zero] at hhalt

/-- Determinism of completed outputs: a machine has at most one completed output on a
given input — if `M` halts on `input` with `w` within `t` steps and with `w'` within
`t'` steps, then `w = w'`. Together with `Turing.FinTM.ComputesInTime.mono` this
makes the halting relation of a machine a partial function.

**Proof.** Absorb both computations to time `max t t'`
(`Turing.FinTM.ComputesInTime.mono`); both then name the output of one and the same
run. -/
theorem ComputesInTime.output_unique {M : FinTM Symbol} {input w w' : List Symbol}
    {t t' : ℕ} (h : M.ComputesInTime input w t) (h' : M.ComputesInTime input w' t') :
    w = w' := by
  have h₁ := h.mono (Nat.le_max_left t t')
  have h₂ := h'.mono (Nat.le_max_right t t')
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h₁ h₂
  obtain ⟨s, -, hout, -⟩ := h₁
  obtain ⟨s', -, hout', -⟩ := h₂
  rw [← hout, ← hout']

/-- A time-bounded computation is in particular a computation. -/
theorem ComputesFunInTime.computes {M : FinTM Symbol} {f : List Symbol → List Symbol}
    {T : ℕ → ℕ} (h : M.ComputesFunInTime f T) : M.Computes f :=
  fun input => ⟨T input.length, h input⟩

/-- `ComputesInTime` without the space witness: the machine has halted by time `t`
with completed output exactly `w`. The space existential is uniquely determined by
the run, so it can always be discharged. (Promoted from the epoch-1 fill and
generalized from `Bool` to an arbitrary alphabet, per the epoch-1 audit,
finding 4.) -/
theorem computesInTime_iff (M : FinTM Symbol) (x w : List Symbol) (t : ℕ) :
    M.ComputesInTime x w t ↔
      (M.tm.runFrom (M.tm.initCfg x) t).state = none ∧
      (M.tm.runFrom (M.tm.initCfg x) t).output = w := by
  constructor
  · rintro ⟨s, hs, ho, -⟩
    exact ⟨hs, ho⟩
  · rintro ⟨hs, ho⟩
    exact ⟨_, hs, ho, rfl⟩

/-- A total machine's completed outputs are exactly its prescribed values: if `M`
computes `g`, then `M` halts on `x` with completed output `w` — in some number of
steps — iff `w = g x`. Existence of a computation together with determinism of
completed outputs (`Turing.FinTM.ComputesInTime.output_unique`). (Promoted from
the epoch-1 fill per the epoch-1 audit, finding 4.) -/
theorem Computes.exists_computesInTime_iff {M : FinTM Symbol}
    {g : List Symbol → List Symbol} (hM : M.Computes g) (x w : List Symbol) :
    (∃ t, M.ComputesInTime x w t) ↔ w = g x := by
  obtain ⟨t, ht⟩ := hM x
  constructor
  · rintro ⟨s, hs⟩
    exact hs.output_unique ht
  · rintro rfl
    exact ⟨t, ht⟩

end FinTM

end Turing

```


## ===== TCSlib/Complexity/ClassP/DTIME.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deciding languages and the classes DTIME

Languages are sets of binary strings, `Mathlib`'s `Language Bool`. A bundled finite
machine over the binary alphabet (`Turing.FinTM Bool`, tape alphabet
`Option Bool = {0, 1, blank}`) *decides* a language `L` in time `T` if on every input `x`
it halts within `T |x|` steps with the single-symbol output `[true]` if `x ∈ L` and
`[false]` otherwise. `DTIME T` is the class of languages decided in time `c · T` for some
constant `c`. [AB09, §1.6, Definition 1.12]

## Design and deviations from [AB09]

* [AB09] fixes the four-symbol alphabet `{▷, □, 0, 1}` for the definition and remarks the
  choice is immaterial. Our machines use the three-symbol tape alphabet
  `Option Bool = {0, 1, blank}` over bidirectional tapes, which need no start symbol
  ([AB09, Claim 1.8] direction). The alphabet-reduction theorem ([AB09, Claim 1.5],
  phase 2) will show that machines over any finite alphabet are simulated by binary ones
  with a constant-factor slowdown — absorbed by the `∃ c` in `DTIME` — so defining
  `DTIME` over binary machines loses no generality.
* Acceptance is by output (`[true]`/`[false]`), not by accepting states: the vendored
  model has a single halting state and distinguishes outcomes by output, which [AB09]
  does via the output tape as well.
* **The output tape is append-only** (the transition emits at most one symbol per step,
  and emitted symbols cannot be erased), whereas [AB09, §1.2] designates a read-write
  work tape as the output tape — [AB09, p. 19] itself lists write-only output among the
  benign model variations. This bridge is **waived** (phase-2 audit, finding 3; see
  the plan's decision log): [AB09]'s read-write-output machine is not formalized in
  this development, so no simulation between the conventions is even statable; the
  compensating restriction is that no exact [AB09] step count is ever imported as a
  formal bound. The in-model buffer-and-flush technique lives in
  `TCSlib.Complexity.TuringMachine.Composition`.
* **Initialization differs from [AB09]**: there are no start-marker (`▷`) cells — the
  bidirectional tapes make them unnecessary — and the input head begins on the first
  input symbol (on the boundary blank for empty input), with all work tapes blank.
* The constant `c` ranges over all of `ℕ`; `c = 0` yields the bound `0`, within which no
  machine can halt (the initial state is not the halting state), so it contributes
  nothing — this matches [AB09]'s `c > 0` without carrying a positivity side condition.

## Main definitions

* `Turing.FinTM.DecidesInTime` — `M` decides `L` within time `T`. [AB09, §1.6 with
  Definition 1.3]
* `Complexity.DTIME` — the class of languages decidable in time `c · T`.
  [AB09, Definition 1.12]

## Main results

* `Complexity.DTIME.mono` — `DTIME` is monotone in the time bound.
* `Complexity.DTIME_eq_empty_of_exists_zero` — a time bound that vanishes at some
  length has an empty class (every machine needs at least one step to halt).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definitions 1.3, 1.12.)
-/

namespace Turing.FinTM

/-- The machine `M` decides the language `L` within time `T`: on every input `x` it halts
within `T |x|` steps with output `[true]` if `x ∈ L` and `[false]` otherwise.
[AB09, §1.6 with Definition 1.3] -/
def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- The class of languages decidable in time `c · T` for some constant `c`: a language
`L` is in `DTIME T` iff some finite binary-alphabet multi-tape machine decides it within
`c · T n` steps on inputs of length `n`. [AB09, Definition 1.12] -/
def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}

/-- `DTIME` is monotone in the time bound.

**Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
same output) within `c · T₂ n ≥ c · T₁ n` steps, by `Turing.FinTM.ComputesInTime.mono`
(halting is absorbing). -/
theorem DTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : DTIME T₁ ⊆ DTIME T₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, fun x => (hM x).mono (Nat.mul_le_mul (le_refl c) (h x.length))⟩

/-- If the time bound vanishes at even one input length, the class is empty: the
initial state is not the halting state, so no machine halts in `c · 0 = 0` steps on an
input of that length (e.g. `List.replicate n false`).

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate `DecidesInTime` at
the input `List.replicate n false`; the budget is `c * T n = 0`, contradicting
`Turing.FinTM.not_computesInTime_zero`. -/
theorem DTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : DTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, M, hM⟩
  have hx := hM (List.replicate n false)
  simp only [List.length_replicate] at hx
  rw [hn, Nat.mul_zero] at hx
  exact M.not_computesInTime_zero _ _ hx

end Complexity

```


## ===== TCSlib/Complexity/ClassP/P.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassP.DTIME

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class P

`P` is the class of languages decidable in polynomial time: the union over `c` of
`DTIME (n^c + 1)`. [AB09, Definition 1.13, with the `+ 1` padding explained below —
every *positive*-degree component of the literal unpadded union is empty in this model,
since `n^c` vanishes at `n = 0` and no machine halts in zero steps; [AB09]'s union
ranges over `c ≥ 1`, so its literal reading is empty, while including degree `0` would
give exactly `DTIME 1` (in Lean `0 ^ 0 = 1`).]

## Design and deviations from [AB09]

* We take the union of `DTIME (fun n => n ^ c + 1)` over all `c : ℕ` where [AB09] writes
  `⋃_{c ≥ 1} DTIME(n^c)`. The `+ 1` repairs the empty-input degeneracy: a machine needs
  at least one step to halt, so for the degrees `d ≥ 1` of [AB09]'s union no language
  whatsoever is decided within `c · 0^d = 0` steps on the empty input, and the literal
  [AB09] definition would (vacuously) exclude even constant-time machines on that input. For `n ≥ 1` the bounds `c · (n^d + 1)` and
  `c' · n^d` sandwich each other, so this is the standard reading of the same class.
  Ranging over `c = 0` too is harmless: `n^0 + 1 = 2` is a constant bound, subsumed by
  larger `c`.

## Main definitions

* `Complexity.P` — [AB09, Definition 1.13].

## Main results

* `Complexity.dtime_poly_subset_P` — each `DTIME (n^c + 1)` is contained in `P`.
* `Complexity.mem_P_iff` — `P` is exactly the class decidable within `C · (n + 1) ^ d`
  for some constants, certifying that the `+ 1` padding has the conventional
  polynomial-time content.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definition 1.13.)
-/

namespace Complexity

open Turing

/-- The class of polynomial-time decidable languages:
`P = ⋃ c, DTIME (n^c + 1)`. [AB09, Definition 1.13] -/
def P : Set (Language Bool) := ⋃ c : ℕ, DTIME fun n => n ^ c + 1

/-- Every fixed-degree polynomial time class is contained in `P`. -/
theorem dtime_poly_subset_P (c : ℕ) : DTIME (fun n => n ^ c + 1) ⊆ P :=
  Set.subset_iUnion (fun c : ℕ => DTIME fun n => n ^ c + 1) c

/-- Membership in `P` from a concrete polynomial bound: if `L` is decidable within any
time bound that is pointwise dominated by a polynomial, then `L ∈ P`. (Pointwise, not
eventual, domination: an eventual-bound variant follows with the *same machine* by
absorbing the finitely many exceptional bounds into the constant, and is deferred.)

**Proof sketch.** Pick `c` and `d` with `T n ≤ c * (n ^ d + 1)` for all `n`. By
`Complexity.DTIME.mono`, `DTIME T ⊆ DTIME (fun n => c * (n ^ d + 1))`; the latter equals
a subclass of `DTIME (fun n => n ^ d + 1)` because the constant `c` is absorbed by the
existential constant in the definition of `DTIME` (the two constants multiply). Conclude
with `Complexity.dtime_poly_subset_P`. -/
theorem mem_P_of_dtime_le {L : Language Bool} {T : ℕ → ℕ}
    (hL : L ∈ DTIME T) (c d : ℕ) (hT : ∀ n, T n ≤ c * (n ^ d + 1)) : L ∈ P := by
  obtain ⟨a, M, hM⟩ := hL
  refine dtime_poly_subset_P d ⟨a * c, M, fun x => (hM x).mono ?_⟩
  calc a * T x.length ≤ a * (c * (x.length ^ d + 1)) :=
        Nat.mul_le_mul (le_refl a) (hT x.length)
    _ = a * c * (x.length ^ d + 1) := by ring

/-- The key pointwise inequality behind the padding normalization:
`(n + 1) ^ d ≤ 2 ^ d · (n ^ d + 1)` for every `n` and `d`. -/
lemma succ_pow_le (n d : ℕ) : (n + 1) ^ d ≤ 2 ^ d * (n ^ d + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.succ_pos _)
  · calc (n + 1) ^ d ≤ (2 * n) ^ d := Nat.pow_le_pow_left (by omega) d
      _ = 2 ^ d * n ^ d := Nat.mul_pow 2 n d
      _ ≤ 2 ^ d * (n ^ d + 1) := Nat.mul_le_mul (le_refl _) (Nat.le_succ _)

/-- `P` is exactly the class of languages decidable within `C · (n + 1) ^ d` steps for
some constants `C` and `d`. This certifies that the `+ 1` padding in the definition of
`P` has the conventional polynomial-time content: forward, a witness for the degree-`c`
component gives a bound `a · (n ^ c + 1) ≤ 2a · (n + 1) ^ c`; backward, `succ_pow_le`
turns a `C · (n + 1) ^ d` decider into a `(C · 2 ^ d) · (n ^ d + 1)` decider, landing
in the degree-`d` component. (`audits/phase1-findings.md`, "Polynomial-time
normalization".) -/
theorem mem_P_iff {L : Language Bool} :
    L ∈ P ↔ ∃ (C d : ℕ) (M : FinTM Bool),
      M.DecidesInTime L fun n => C * (n + 1) ^ d := by
  constructor
  · intro hL
    obtain ⟨c, hs⟩ := Set.mem_iUnion.mp hL
    obtain ⟨a, M, hM⟩ := hs
    refine ⟨2 * a, c, M, fun x => (hM x).mono ?_⟩
    have h1 : x.length ^ c ≤ (x.length + 1) ^ c :=
      Nat.pow_le_pow_left (Nat.le_succ _) c
    have h2 : 0 < (x.length + 1) ^ c := Nat.pow_pos (Nat.succ_pos _)
    calc a * (x.length ^ c + 1)
        ≤ a * ((x.length + 1) ^ c + (x.length + 1) ^ c) :=
          Nat.mul_le_mul (le_refl a) (Nat.add_le_add h1 h2)
      _ = 2 * a * (x.length + 1) ^ c := by ring
  · rintro ⟨C, d, M, hM⟩
    refine Set.mem_iUnion.mpr ⟨d, C * 2 ^ d, M, fun x => (hM x).mono ?_⟩
    calc C * (x.length + 1) ^ d
        ≤ C * (2 ^ d * (x.length ^ d + 1)) :=
          Nat.mul_le_mul (le_refl C) (succ_pow_le x.length d)
      _ = C * 2 ^ d * (x.length ^ d + 1) := by ring

/-- Constant time is polynomial time.

**Proof sketch.** `Complexity.mem_P_of_dtime_le` with `T = fun _ => 1`, `c = 1`,
`d = 1`, since `1 ≤ 1 * (n ^ 1 + 1)`. -/
theorem dtime_one_subset_P : DTIME (fun _ => 1) ⊆ P := fun _ hL =>
  mem_P_of_dtime_le hL 1 1 fun n => by
    rw [one_mul]
    exact Nat.le_add_left 1 (n ^ 1)

end Complexity

```


## ===== TCSlib/Complexity/ClassNP/NTIME.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic deciding and the classes NTIME

[AB09, §2.1.2, Definition 2.5]: a language `L` is in `NTIME T` when some binary-choice
NDTM decides it within time `c · T` — on every input, **every** branch halts within the
budget, and the input is in `L` exactly when **some** branch accepts. This module fixes
the binary alphabet (as `TCSlib.Complexity.ClassP.DTIME` does for the deterministic
classes), defines acceptance, the deciding predicate, and `NTIME`, and states the
deterministic embedding `DTIME ⊆ NTIME`.

## Design and deviations from [AB09]

* **Acceptance is by output, not by a `q_accept` state**: a branch *accepts* when it has
  halted with output exactly `[true]`. [AB09] gives NDTMs a distinguished accepting
  state; our machine model (single halting state, append-only output tape)
  distinguishes outcomes by output, and the deterministic `Turing.FinTM.DecidesInTime`
  already reads `[true]`/`[false]` off the output tape — acceptance-by-output keeps the
  two layers aligned, at the price that a branch halting with output `[]`, `[false]`,
  or any string other than the singleton `[true]` is non-accepting. Nothing constrains
  the outputs of non-accepting branches. **Design question (a) for the phase-2
  audit.**
* **The totality bound quantifies over all inputs and all branches**
  ([AB09, §2.1.2] verbatim: "for every input `x` and every sequence of nondeterministic
  choices"): `Turing.FinNDTM.DecidesInTime` demands `HaltsWithin` on **every** input —
  members and non-members alike — conjoined per input with the acceptance equivalence.
  Placing the halting quantifier per input (rather than as one global conjunct) is
  presentational; demanding it on non-members is not, and is the standard reading.
  **Design question (b) for the phase-2 audit.**
* **Exact-length choice words**: both `AcceptsWithin` and `HaltsWithin` quantify over
  choice words of length exactly `t`; the equivalent bounded-length readings differ by
  quantifier shape (round-1 audit, finding 2). For **acceptance** the bounded
  existential is equivalent: some `w` with `|w| ≤ t` reaching a halted configuration
  with output `[true]` pads with `false`-bits to exact length
  (`Turing.NDTM.runWith_of_halt`). For **all-branch halting** the bounded reading is
  prefix-shaped: every word of length `t` has a halted prefix `w.take r` with `r ≤ t`
  (forward take `r = t`; backward absorb the suffix) — **not** "every word of length
  at most `t` is already halted", which fails at the empty word against the live
  initial state. Moreover, under `HaltsWithin x t` the run of any longer word `w`
  *equals* the run of `w.take t` — the whole configuration, not merely the halting
  flag — which is what the backward (truncation) directions of `Complexity.NTIME.mono`
  and the compilation sketches use.
* As with `Complexity.DTIME`, the constant `c` in `NTIME` ranges over all of `ℕ`; the
  value `c = 0` gives the unsatisfiable budget `0` (no machine is halted at time `0`)
  and contributes nothing, matching [AB09]'s `c > 0` without a positivity side
  condition.

## Main definitions

* `Turing.FinNDTM.AcceptsWithin` — some branch of length `t` halts with output
  `[true]`. [AB09, §2.1.2: "`M(x) = 1`"]
* `Turing.FinNDTM.DecidesInTime` — all-branch halting plus the acceptance
  characterization of membership. [AB09, §2.1.2]
* `Complexity.NTIME` — the class of languages decided nondeterministically in time
  `c · T`. [AB09, Definition 2.5]

## Main results

* `Turing.FinNDTM.AcceptsWithin.mono` — acceptance is monotone in the branch length.
* `Complexity.NTIME.mono` — `NTIME` is monotone in the time bound.
* `Complexity.DTIME_subset_NTIME` — deterministic time is nondeterministic time.
  [AB09, §2.1.2]
* `Complexity.NTIME_eq_empty_of_exists_zero` — a vanishing time bound gives the empty
  class, as for `DTIME`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2, Definition 2.5, pp. 41-42.)
-/

namespace Turing.FinNDTM

/-- The machine `N` *accepts* `x` within `t` steps: **some** choice word of length `t`
leaves the machine halted with output exactly `[true]`. This is [AB09, §2.1.2]'s
"`M(x) = 1`" with acceptance read off the output tape in place of the `q_accept` state
(see the deviations list; design question (a)). A branch halted with any other output —
including `[]` and `[false]` — is non-accepting. -/
def AcceptsWithin (N : FinNDTM Bool) (x : List Bool) (t : ℕ) : Prop :=
  ∃ w : List Bool, w.length = t ∧
    (N.tm.runWith w (N.tm.initCfg x)).state = none ∧
    (N.tm.runWith w (N.tm.initCfg x)).output = [true]

/-- Acceptance is monotone in the branch length: an accepting branch stays accepting
when the choice word is extended.

**Proof sketch.** Pad the accepting word `w` to `w ++ List.replicate (t' - t) false`
(length `t'` by `List.length_append` and `List.length_replicate`, since `t ≤ t'`);
`Turing.NDTM.runWith_append` factors the padded run through the halted configuration
reached by `w`, and `Turing.NDTM.runWith_of_halt` absorbs the padding, preserving both
the halted state and the output `[true]`. -/
theorem AcceptsWithin.mono {N : FinNDTM Bool} {x : List Bool} {t t' : ℕ}
    (h : N.AcceptsWithin x t) (hle : t ≤ t') : N.AcceptsWithin x t' := by
  obtain ⟨w, hw, hhalt, hout⟩ := h
  refine ⟨w ++ List.replicate (t' - t) false, ?_, ?_⟩
  · rw [List.length_append, List.length_replicate, hw, Nat.add_sub_of_le hle]
  · rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hhalt]
    exact ⟨hhalt, hout⟩

/-- The machine `N` *decides* the language `L` within time `T`, nondeterministically:
on every input `x`, every branch of length `T |x|` has halted
(`Turing.NDTM.HaltsWithin` — [AB09]'s totality condition, demanded on members and
non-members alike), and `x ∈ L` exactly when some such branch accepts.
[AB09, §2.1.2 with Definition 2.5] -/
def DecidesInTime (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    N.tm.HaltsWithin x (T x.length) ∧ (x ∈ L ↔ N.AcceptsWithin x (T x.length))

end Turing.FinNDTM

namespace Complexity

open Turing

/-- The class of languages decidable nondeterministically in time `c · T` for some
constant `c`: a language `L` is in `NTIME T` iff some finite binary-alphabet NDTM
decides it within `c · T n` steps on inputs of length `n`, in the sense of
`Turing.FinNDTM.DecidesInTime`. [AB09, Definition 2.5] -/
def NTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.DecidesInTime L fun n => c * T n}

/-- `NTIME` is monotone in the time bound.

**Proof sketch.** The same machine works at the larger budget `c · T₂ n ≥ c · T₁ n`.
All-branch halting transfers by `Turing.NDTM.HaltsWithin.mono`. The acceptance
equivalence transfers in both directions: forward by
`Turing.FinNDTM.AcceptsWithin.mono` (pad the accepting word); backward by truncation —
given an accepting word `w` at the larger budget, its prefix `w.take (c * T₁ n)` has
halted (all-branch halting at the smaller budget), and `Turing.NDTM.runWith_append` on
`w = w.take _ ++ w.drop _` with `Turing.NDTM.runWith_of_halt` shows the full run equals
the truncated one, so the truncated word already accepts. -/
theorem NTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : NTIME T₁ ⊆ NTIME T₂ := by
  rintro L ⟨c, N, hN⟩
  refine ⟨c, N, ?_⟩
  intro x
  obtain ⟨hhalt, haccept⟩ := hN x
  have hle := Nat.mul_le_mul_left c (h x.length)
  refine ⟨hhalt.mono hle, ?_⟩
  constructor
  · intro hx
    exact (haccept.mp hx).mono hle
  · rintro ⟨w, hw, _, hout⟩
    apply haccept.mpr
    have hlen : (w.take (c * T₁ x.length)).length = c * T₁ x.length :=
      List.length_take_of_le (hle.trans_eq hw.symm)
    have hprefix := hhalt (w.take (c * T₁ x.length)) hlen
    refine ⟨w.take (c * T₁ x.length), hlen, hprefix, ?_⟩
    have hrun := NDTM.runWith_append (tm := N.tm)
      (w.take (c * T₁ x.length)) (w.drop (c * T₁ x.length)) (N.tm.initCfg x)
    rw [List.take_append_drop, NDTM.runWith_of_halt _ hprefix] at hrun
    rw [← hrun]
    exact hout

/-- **Deterministic time is nondeterministic time** [AB09, §2.1.2]: a TM is an NDTM
that ignores its choices, so `DTIME T ⊆ NTIME T`.

**Proof sketch.** Given `M` deciding `L` within `c · T n`, take
`Turing.FinTM.toFinNDTM M`. By `Turing.MultiTapeTM.toNDTM_runWith`, the run under
**any** choice word of length `t` is `M`'s deterministic run to time `t`, so: every
branch of length `c · T n` is halted because `M`'s computation has halted by then
(`Turing.FinTM.DecidesInTime` unfolded through `Turing.FinTM.computesInTime_iff`),
giving `HaltsWithin`; and some branch of that length is halted with output `[true]` iff
`M`'s output at that time is `[true]`, which by the indicator contract
(`Turing.MultiTapeTM.indicator`) holds iff `x ∈ L` — for `x ∉ L` the output is
`[false] ≠ [true]` on every branch, so no branch accepts. -/
theorem DTIME_subset_NTIME (T : ℕ → ℕ) : DTIME T ⊆ NTIME T := by
  classical
  rintro L ⟨c, M, hM⟩
  refine ⟨c, M.toFinNDTM, ?_⟩
  intro x
  obtain ⟨hhalt, hout⟩ := (M.computesInTime_iff _ _ _).mp (hM x)
  have hrun (w : List Bool) :
      M.toFinNDTM.tm.runWith w (M.toFinNDTM.tm.initCfg x) =
        M.tm.runFrom (M.tm.initCfg x) w.length :=
    M.tm.toNDTM_runWith w (M.tm.initCfg x)
  constructor
  · intro w hw
    rw [hrun, hw]
    exact hhalt
  · constructor
    · intro hx
      refine ⟨List.replicate (c * T x.length) false, List.length_replicate .., ?_, ?_⟩
      · rw [hrun, List.length_replicate]
        exact hhalt
      · rw [hrun, List.length_replicate, hout]
        simp only [MultiTapeTM.indicator, if_pos hx]
    · rintro ⟨w, hw, _, hwout⟩
      rw [hrun, hw, hout] at hwout
      by_contra hx
      simp only [MultiTapeTM.indicator, if_neg hx] at hwout
      cases hwout

/-- If the time bound vanishes at even one input length, the class is empty, exactly as
for `Complexity.DTIME_eq_empty_of_exists_zero`: the initial configuration is not
halted, so all-branch halting already fails at budget `c * 0 = 0`.

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate
`Turing.FinNDTM.DecidesInTime` at the input `List.replicate n false`
(`List.length_replicate`); its `HaltsWithin` conjunct applied to the empty choice word
(`Turing.NDTM.runWith_nil`) asserts that the initial configuration is halted,
contradicting `Turing.Cfg.init`'s state `some q₀`. -/
theorem NTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : NTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  apply Set.eq_empty_iff_forall_not_mem.mpr
  rintro L ⟨c, N, hN⟩
  have hhalt := (hN (List.replicate n false)).1
  simp only [List.length_replicate, hn, Nat.mul_zero] at hhalt
  have hzero : (some N.tm.q₀ : Option N.State) = none := hhalt [] rfl
  cases hzero

end Complexity

```


## ===== TCSlib/Complexity/ClassNP/Reductions.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.Uncomputability.Halting

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Karp reductions, NP-hardness, and NP-completeness

[AB09, §2.2, Definition 2.7]: `L ≤ₚ L'` when a polynomial-time computable
function maps members to members and non-members to non-members; `L'` is
`NP`-hard when every `NP` language reduces to it, `NP`-complete when it is also
in `NP`. Theorem 2.8 packages the basic laws: transitivity, and the collapse
consequences of an `NP`-hard language landing in `P`.

The module closes with [AB09, Exercise 2.8], the chapter's bridge back to
Chapter 1: `HALT` is `NP`-hard but — being undecidable — not in `NP`, hence not
`NP`-complete.

## Main definitions

* `Complexity.PolyTimeReducible` (scoped notation `≤ₚ`) — [AB09, Definition 2.7].
* `Complexity.NPHard`, `Complexity.NPComplete` — [AB09, Definition 2.7].

## Main results

* `Complexity.PolyTimeReducible.refl`, `Complexity.PolyTimeReducible.trans` —
  [AB09, Theorem 2.8.1 and Exercise 2.9].
* `Complexity.mem_P_of_polyTimeReducible` — downward closure of `P` under `≤ₚ`
  [AB09, Figure 2.1].
* `Complexity.P_eq_NP_of_NPHard_mem_P` — [AB09, Theorem 2.8.2].
* `Complexity.NPComplete.mem_P_iff` — [AB09, Theorem 2.8.3].
* `Complexity.HALT_NPHard`, `Complexity.HALT_not_mem_NP` — [AB09, Exercise 2.8].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, Definition 2.7, Theorem 2.8,
  pp. 42-44; Exercises 2.8-2.9.)
-/

namespace Complexity

open Turing

/-- **Polynomial-time Karp reducibility** [AB09, Definition 2.7]: `L ≤ₚ L'` when
some polynomial-time computable `f` satisfies `x ∈ L ↔ f x ∈ L'` for every
string `x`. -/
def PolyTimeReducible (L L' : Language Bool) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ x, x ∈ L ↔ f x ∈ L'

@[inherit_doc] scoped infix:50 " ≤ₚ " => PolyTimeReducible

/-- Karp reducibility is reflexive [AB09, Exercise 2.9]: the identity reduces
`L` to itself.

**Proof sketch.** `Complexity.polyTimeComputable_id` with the trivial membership
equivalence. -/
theorem PolyTimeReducible.refl (L : Language Bool) : L ≤ₚ L := by
  exact ⟨id, polyTimeComputable_id, fun _ => Iff.rfl⟩

/-- **Karp reducibility is transitive** [AB09, Theorem 2.8.1].

**Proof sketch.** Compose the two reduction functions with
`Complexity.PolyTimeComputable.comp` and chain the membership equivalences —
the polynomial-composition observation of [AB09]'s proof lives inside `comp`. -/
theorem PolyTimeReducible.trans {L L' L'' : Language Bool}
    (h : L ≤ₚ L') (h' : L' ≤ₚ L'') : L ≤ₚ L'' := by
  obtain ⟨f, hf, hL⟩ := h
  obtain ⟨g, hg, hL'⟩ := h'
  exact ⟨g ∘ f, hg.comp hf, fun x => (hL x).trans (hL' (f x))⟩

/-- **`P` is closed downward under `≤ₚ`** [AB09, Figure 2.1 and the remark after
Definition 2.7]: if `L ≤ₚ L'` and `L' ∈ P` then `L ∈ P`.

**Proof sketch.** Compose the reduction machine with a polynomial-time decider of
`L'` (`Complexity.mem_P_iff`, read pointwise as computing the total
singleton-indicator function) via the **timed** total composition
`Turing.FinTM.computesFunInTime_comp` — the untimed `exists_comp_partial`
carries no time bound (phase-1 audit, finding 4). The intermediate string `f x`
has polynomially bounded length
(`Complexity.PolyTimeComputable.output_length_le`), so the decider's budget on
it is polynomial in `|x|` by monotonicity of the explicit polynomial, and the
composite decides `L` since `x ∈ L ↔ f x ∈ L'`; return through
`Complexity.mem_P_of_dtime_le`.

The implementation packages the decider as a polynomial-time computable
singleton-indicator function and applies `PolyTimeComputable.comp`, whose
proof invokes the timed interface above with its intermediate-output bound.
Finally `succ_pow_le` converts the resulting `(n+1)^d` budget to the
`n^d+1` form consumed by `mem_P_of_dtime_le`. -/
theorem mem_P_of_polyTimeReducible {L L' : Language Bool}
    (h : L ≤ₚ L') (h' : L' ∈ P) : L ∈ P := by
  classical
  obtain ⟨f, hf, hL⟩ := h
  obtain ⟨C, c, M, hM⟩ := mem_P_iff.mp h'
  have hg : PolyTimeComputable (fun y => [MultiTapeTM.indicator (L' : Set (List Bool)) y]) :=
    ⟨M, C, c, hM⟩
  obtain ⟨S, A, d, hS⟩ := hg.comp hf
  have hdec : S.DecidesInTime L (fun n => A * (n + 1) ^ d) := by
    intro x
    have hi : MultiTapeTM.indicator (L : Set (List Bool)) x =
        MultiTapeTM.indicator (L' : Set (List Bool)) (f x) := by
      simp only [MultiTapeTM.indicator, hL x]
    simpa only [Function.comp_apply, hi] using hS x
  refine mem_P_of_dtime_le (T := fun n => A * (n + 1) ^ d)
    ⟨1, S, ?_⟩ (A * 2 ^ d) d ?_
  · intro x
    simpa only [Nat.one_mul] using hdec x
  · intro n
    calc
      A * (n + 1) ^ d ≤ A * (2 ^ d * (n ^ d + 1)) :=
        Nat.mul_le_mul_left A (succ_pow_le n d)
      _ = A * 2 ^ d * (n ^ d + 1) := (Nat.mul_assoc _ _ _).symm

/-- **`NP`-hardness** [AB09, Definition 2.7]: every `NP` language Karp-reduces to
`L`. -/
def NPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ NP, L' ≤ₚ L

/-- **`NP`-completeness** [AB09, Definition 2.7]: `L` is in `NP` and `NP`-hard. -/
def NPComplete (L : Language Bool) : Prop :=
  L ∈ NP ∧ NPHard L

/-- **If an `NP`-hard language is in `P`, then `P = NP`** [AB09, Theorem 2.8.2].

**Proof sketch.** `P ⊆ NP` is `Complexity.P_subset_NP`; conversely every
`L' ∈ NP` reduces to the `NP`-hard `L ∈ P`, so `L' ∈ P` by
`Complexity.mem_P_of_polyTimeReducible`. -/
theorem P_eq_NP_of_NPHard_mem_P {L : Language Bool}
    (hL : NPHard L) (h : L ∈ P) : P = NP := by
  apply Set.Subset.antisymm P_subset_NP
  intro L' hL'
  exact mem_P_of_polyTimeReducible (hL L' hL') h

/-- **An `NP`-complete language is in `P` iff `P = NP`** [AB09, Theorem 2.8.3].

**Proof sketch.** (⇒) is `Complexity.P_eq_NP_of_NPHard_mem_P` on the hardness
half; (⇐) rewrites `L ∈ NP` along `P = NP`. -/
theorem NPComplete.mem_P_iff {L : Language Bool} (hL : NPComplete L) :
    L ∈ P ↔ P = NP := by
  constructor
  · exact P_eq_NP_of_NPHard_mem_P hL.2
  · intro h
    rw [h]
    exact hL.1


/-- Encode the simulated state and remembered bit. The inner `none` is a live
loop state, distinct from the outer `none` that denotes actual halting. -/
private def acceptState {Q : Type} (q : Option Q) (b : Bool) : Option (Option (Q × Bool)) :=
  match q with
  | some q => some (some (q, b))
  | none => if b then none else some none

/-- Update the bit before redirecting the successor state. In particular a bit
emitted by a halting transition is remembered. Physical output is suppressed. -/
private def acceptAction {k : ℕ} {Q : Type} (a : Action k Bool Q) (b : Bool) :
    Action k Bool (Option (Q × Bool)) :=
  ⟨a.inputTape, a.workTapes, none, acceptState a.state (a.output.getD b)⟩

/-- The halting recognizer associated to a Boolean-output decider. It uses the
same work tapes and either simulates a source state or stays in its live loop. -/
private def acceptTM (M : FinTM Bool) : FinTM Bool where
  k := M.k
  State := Option (M.State × Bool)
  tm :=
    { q₀ := some (M.tm.q₀, false)
      tr := fun q inp work => match q with
        | none => ⟨0, fun _ => (none, 0), none, some none⟩
        | some (q, b) => acceptAction (M.tm.tr q inp work) b }

/-- Configuration correspondence: the finite register holds the last emitted
bit (initially false), while the recognizer's real output stays empty. -/
private def acceptCfg (M : FinTM Bool) {x : List Bool} (cfg : Cfg M.k Bool M.State x) :
    Cfg (acceptTM M).k Bool (acceptTM M).State x :=
  ⟨acceptState cfg.state (cfg.output.getLast?.getD false), cfg.inputPos,
    cfg.workTapes, cfg.workTapePos, []⟩

/-- A live loop configuration never changes and therefore never halts. -/
private lemma acceptTM_loop (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg (acceptTM M).k Bool (acceptTM M).State x) (h : cfg.state = some none)
    (t : ℕ) : (acceptTM M).tm.runFrom cfg t = cfg := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    apply Cfg.ext <;> simp [MultiTapeTM.step, h, acceptTM, Action.apply]

/-- Capturing an action agrees with capturing its resulting configuration. -/
private lemma acceptCfg_apply (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (a : Action M.k Bool M.State) :
    (acceptAction a (cfg.output.getLast?.getD false)).apply (acceptCfg M cfg) =
      acceptCfg M (a.apply cfg) := by
  have hlast : (cfg.output ++ a.output.toList).getLast?.getD false =
      a.output.getD (cfg.output.getLast?.getD false) := by
    cases a.output <;> simp
  apply Cfg.ext
  · dsimp only [acceptCfg, acceptAction, Action.apply]
    rw [hlast]
  · rfl
  · rfl
  · rfl
  · rfl

/-- The control transform commutes with every step, including a halt that
emits the decision bit. Rejection maps to the stationary live loop. -/
private lemma acceptCfg_step (M : FinTM Bool) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    (acceptTM M).tm.step (acceptCfg M cfg) = acceptCfg M (M.tm.step cfg) := by
  cases hs : cfg.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs]
    cases hb : cfg.output.getLast?.getD false with
    | false =>
      exact acceptTM_loop M (acceptCfg M cfg) (by simp [acceptCfg, acceptState, hs, hb]) 1
    | true =>
      exact MultiTapeTM.step_of_halt (by simp [acceptCfg, acceptState, hs, hb])
  | some q =>
    have hi : (acceptCfg M cfg).inputSymbol = cfg.inputSymbol := rfl
    have hw : (acceptCfg M cfg).workTapeSymbols = cfg.workTapeSymbols := rfl
    simp only [MultiTapeTM.step, acceptCfg, acceptState, hs]
    change (acceptAction (M.tm.tr q (acceptCfg M cfg).inputSymbol
      (acceptCfg M cfg).workTapeSymbols) (cfg.output.getLast?.getD false)).apply
        (acceptCfg M cfg) = _
    rw [hi, hw]
    exact acceptCfg_apply M cfg _

/-- Initialized runs commute with the control transformation, by the step
correspondence. This is the run invariant for the HALT reduction. -/
private lemma acceptTM_run (M : FinTM Bool) (x : List Bool) (t : ℕ) :
    (acceptTM M).tm.runFrom ((acceptTM M).tm.initCfg x) t =
      acceptCfg M (M.tm.runFrom (M.tm.initCfg x) t) := by
  have hi : (acceptTM M).tm.initCfg x = acceptCfg M (M.tm.initCfg x) := rfl
  rw [hi]
  exact MultiTapeTM.runFrom_comm_of_step (acceptCfg M) (acceptCfg_step M)
    (M.tm.initCfg x) t

/-- The transformed machine halts exactly when the total source decider's bit
is true. This lemma assumes totality only for the source decider, never for the
deliberately divergent result.

**Proof sketch.** The run invariant says a transformed run can halt only when
the source has halted and its last bit is true. Determinism identifies that
completed output with the source decider's singleton output. Conversely, at a
completed accepting run the invariant immediately gives transformed halting. -/
private lemma acceptTM_halts_iff (M : FinTM Bool) (p : List Bool → Bool)
    (hM : M.Computes fun x => [p x]) (x : List Bool) :
    (∃ w t, (acceptTM M).ComputesInTime x w t) ↔ p x = true := by
  constructor
  · rintro ⟨w, t, ht⟩
    have hhalt := ((FinTM.computesInTime_iff _ _ _ _).mp ht).1
    rw [acceptTM_run] at hhalt
    change acceptState (M.tm.runFrom (M.tm.initCfg x) t).state
      ((M.tm.runFrom (M.tm.initCfg x) t).output.getLast?.getD false) = none at hhalt
    have hs : (M.tm.runFrom (M.tm.initCfg x) t).state = none := by
      cases h : (M.tm.runFrom (M.tm.initCfg x) t).state with
      | none => rfl
      | some q => simp only [acceptState, h, reduceCtorEq] at hhalt
    have hcomp : M.ComputesInTime x (M.tm.runFrom (M.tm.initCfg x) t).output t :=
      (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
    obtain ⟨s, hMs⟩ := hM x
    have hout := hcomp.output_unique hMs
    rw [hs, hout] at hhalt
    simpa [acceptState] using hhalt
  · intro hp
    obtain ⟨t, ht⟩ := hM x
    obtain ⟨hs, hout⟩ := (FinTM.computesInTime_iff _ _ _ _).mp ht
    refine ⟨[], t, (FinTM.computesInTime_iff _ _ _ _).mpr ?_⟩
    rw [acceptTM_run]
    constructor
    · change acceptState (M.tm.runFrom (M.tm.initCfg x) t).state
        ((M.tm.runFrom (M.tm.initCfg x) t).output.getLast?.getD false) = none
      rw [hs, hout]
      simp [acceptState, hp]
    · rfl

/-- Emit the fixed prefix, then copy the input verbatim. No work tape is needed;
the last finite state is the copy state. -/
private def prefixTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm :=
    { q₀ := 0
      tr := fun q inp _ =>
        if h : q.val < w.length then
          ⟨0, fun i => i.elim0, some w[q.val], some ⟨q.val + 1, by omega⟩⟩
        else match inp with
          | some b => ⟨1, fun i => i.elim0, some b, some q⟩
          | none => ⟨0, fun i => i.elim0, none, none⟩ }

/-- A prefixing-machine configuration with the vacuous work fields suppressed. -/
private def prefixCfg (w x : List Bool) (q : Option (Fin (w.length + 1)))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin (w.length + 1)) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- After `i` prefix steps exactly the first `i` fixed bits have been emitted,
and the input head has not moved. -/
private lemma prefixTM_emit (w x : List Bool) : ∀ i (hi : i ≤ w.length),
    (prefixTM w).tm.runFrom ((prefixTM w).tm.initCfg x) i =
      prefixCfg w x (some ⟨i, by omega⟩) 1 (w.take i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext_zero_tapes <;> simp [prefixCfg, prefixTM]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hlt : i < w.length := by omega
    simp only [MultiTapeTM.step, prefixCfg, prefixTM, dif_pos hlt, Action.apply]
    apply Cfg.ext_zero_tapes
    · rfl
    · simp
    · rw [List.take_succ, List.getElem?_eq_getElem hlt]

/-- The copy phase emits one input bit per step and preserves the fixed prefix. -/
private lemma prefixTM_copy (w x : List Bool) : ∀ i (hi : i ≤ x.length),
    (prefixTM w).tm.runFrom
      (prefixCfg w x (some ⟨w.length, by omega⟩) 1 w) i =
      prefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i) := by
  intro i
  induction i with
  | zero => intro hi; simp [prefixCfg]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hsym : (prefixCfg w x (some ⟨w.length, by omega⟩)
        ⟨i + 1, by omega⟩ (w ++ x.take i)).inputSymbol = some (x[i]'(by omega)) :=
      inputSymbolInner i (by simp only [prefixCfg]; omega) (by omega)
    change ((prefixTM w).tm.tr ⟨w.length, by omega⟩
      (prefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i)).inputSymbol _).apply _ = _
    rw [hsym]
    simp only [prefixTM, Nat.lt_irrefl, ↓reduceDIte, Action.apply, prefixCfg]
    apply Cfg.ext_zero_tapes
    · rfl
    · change moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos = _
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · rw [List.take_succ, List.getElem?_eq_getElem (by omega), List.append_assoc]

/-- Prefixing computes `w ++ x` in exactly the bound `|w| + |x| + 1`,
including the final blank-reading halting step.

**Proof sketch.** Concatenate the fixed-word emission run and the input-copy
run; the input head then scans the right boundary, so one final step halts
without emitting anything further. This also covers empty prefix and input. -/
private lemma prefixTM_computes (w : List Bool) :
    (prefixTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 1) := by
  intro x
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  dsimp only
  rw [show w.length + x.length + 1 = w.length + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, prefixTM_emit w x w.length (Nat.le_refl _)]
  simp only [List.take_length]
  rw [MultiTapeTM.runFrom_succ_eq_step', prefixTM_copy w x x.length (Nat.le_refl _)]
  simp [prefixTM, prefixCfg, MultiTapeTM.step, Cfg.inputSymbol, Fin.ext_iff, Action.apply]

/-- The fixed-code pairing machine has the audited budget
`2|α| + |x| + 3`: two emissions per code bit, two for the delimiter, one per
input bit, and one final blank-reading step. -/
private lemma fixedPair_computes (α : List Bool) :
    (prefixTM ((α.flatMap fun b => [b, b]) ++ [false, true])).ComputesFunInTime
      (fun x => pairEncode α x) (fun n => 2 * α.length + n + 3) := by
  have hlen : (α.flatMap fun b => [b, b]).length = 2 * α.length := by
    induction α with
    | nil => rfl
    | cons b α ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      omega
  intro x
  have h := prefixTM_computes ((α.flatMap fun b => [b, b]) ++ [false, true]) x
  have ht : ((α.flatMap fun b => [b, b]) ++ [false, true]).length + x.length + 1 =
      2 * α.length + x.length + 3 := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    omega
  simpa only [pairEncode, ht] using h

/-- The fixed-code pairing machine is polynomial-time computable. -/
private lemma fixedPair_polyTime (α : List Bool) :
    PolyTimeComputable (fun x => pairEncode α x) := by
  refine ⟨prefixTM ((α.flatMap fun b => [b, b]) ++ [false, true]),
    2 * α.length + 3, 1, fun x => (fixedPair_computes α x).mono ?_⟩
  simp only [Nat.pow_one, Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega


/-- **`HALT` is `NP`-hard** [AB09, Exercise 2.8] — for **every** representation
scheme, effective or not: the reduction embeds one *fixed* code, so only
`Turing.MachineCode.decode_encode` is used (phase-1 audit, finding 11; compare
Chapter 1's Theorem 1.10/1.11 split, where only the evaluator direction needs
effectivity).

**Proof sketch** (the audit's repaired construction, finding 6 — the earlier
divergent-searcher route is unusable because
`Turing.FinTM.one_work_tape_binary` requires a *total* function). Fix `L ∈ NP`.
(1) Obtain a **total** exponential-time decider `D` of `L` from the repaired
`Complexity.NP_subset_EXP`. (2) Normal-form `D` with
`Turing.FinTM.one_work_tape_binary` (legal: `D` is total). (3) Modify the
one-work-tape machine's finite control with a register remembering the Boolean
emission — including a bit emitted on the halting transition — and replace its
halt: halt iff the remembered bit is `true`, otherwise enter a stationary
one-state live loop (such a deliberately divergent state exists: emit nothing,
move nothing, return the same live state). This control modification needs its
own run/halting lemma — a named fill obligation. The result `S` halts on `x`
iff `x ∈ L`. (4) Code `S` with `Turing.exists_codeTM` (no totality hypothesis)
and set `α := c.encode S`. The reduction maps `x ↦ Turing.pairEncode α x`: a
fixed doubled prefix of length `2|α| + 2` followed by the verbatim input,
computable by an emit-then-copy machine in `2|α| + |x| + 3` steps (a small new
machine or prefixing lemma — the audited `pairDiagTM` computes the diagonal
pair, not this fixed-prefix function). `Complexity.HALT_pairEncode_eq_true_iff`
and `Turing.MachineCode.decode_encode` turn membership of the image in `HALT`
into "`S` halts on `x`", which is `x ∈ L`. -/
theorem HALT_NPHard (c : MachineCode) :
    NPHard {s | HALT c s = true} := by
  classical
  intro L hL
  obtain ⟨d, a, D, hD⟩ := Set.mem_iUnion.mp (NP_subset_EXP hL)
  let p : List Bool → Bool := MultiTapeTM.indicator (L : Set (List Bool))
  have hdec : D.ComputesFunInTime (fun x => [p x]) (fun n => a * 2 ^ n ^ d) := hD
  obtain ⟨M, b, hk, hM⟩ := FinTM.one_work_tape_binary D _ _ hdec
  obtain ⟨S, hS⟩ := exists_codeTM (acceptTM M) hk
  refine ⟨fun x => pairEncode (c.encode S) x, fixedPair_polyTime _, fun x => ?_⟩
  change x ∈ L ↔ HALT c (pairEncode (c.encode S) x) = true
  rw [HALT_pairEncode_eq_true_iff, c.decode_encode]
  simp only [hS]
  rw [acceptTM_halts_iff M p hM.computes x]
  simp [p, MultiTapeTM.indicator]

/-- **`HALT` is not in `NP`** [AB09, Exercise 2.8] — so, despite being `NP`-hard,
it is not `NP`-complete: `NP` languages are decidable, `HALT` is not.

**Proof sketch.** If `HALT`'s language were in `NP`, it would be in `EXP` by
the repaired `Complexity.NP_subset_EXP`, so some machine would decide it — and
a decider's output is exactly `[HALT c s]` (off the pair image `HALT` is
`false` and the rejection bit matches, per the totalization convention), making
`fun s => [HALT c s]` computable
(`Complexity.Computable` via `Turing.FinTM.ComputesFunInTime.computes`),
contradicting `Complexity.HALT_not_computable`. The audit certified this chain
valid once `NP_subset_EXP` is repaired. The `Turing.EffectiveMachineCode`
hypothesis is a **proof-route restriction, not a mathematical necessity**
(round-2 audit, finding 3 — the pre-repair docstring's trivial-machine
"counterexample" violates `decode_encode` and is unlawful): this proof reuses
Chapter 1's `HALT_not_computable`, whose own proof runs the universal
evaluator and hence needs effectivity. The round-2 audit exhibited a direct
diagonalization (diagonal pairing, the searcher's control transform with the
halt/loop roles swapped, `Turing.exists_codeTM`, no evaluator) proving `HALT`
undecidable for **every** lawful `Turing.MachineCode`; whether to add that
diagonal lemma and generalize this statement is a recorded human-review
design question (`AroraBarakChapter2Plan.md`, open design questions). Until
decided, this statement stays at the generality its cited API supports. -/
theorem HALT_not_mem_NP (c : EffectiveMachineCode) :
    {s | HALT c.toMachineCode s = true} ∉ NP := by
  classical
  intro h
  apply HALT_not_computable c
  obtain ⟨d, a, M, hM⟩ := Set.mem_iUnion.mp (NP_subset_EXP h)
  have hi : MultiTapeTM.indicator
      ({s | HALT c.toMachineCode s = true} : Set (List Bool)) = HALT c.toMachineCode := by
    funext s
    simp only [MultiTapeTM.indicator, Set.mem_setOf_eq]
    split
    · rename_i hb; exact hb.symm
    · rename_i hb; exact (Bool.eq_false_iff.mpr hb).symm
  have hdec : M.ComputesFunInTime (fun s => [HALT c.toMachineCode s])
      (fun n => a * 2 ^ n ^ d) := by
    simpa only [FinTM.DecidesInTime, hi] using hM
  exact ⟨M, hdec.computes⟩

end Complexity

```


## ===== TCSlib/Complexity/ClassNP/CoNP.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class coNP

[AB09, §2.6.1]: `coNP` is the class of complements of `NP` languages
(Definition 2.19), equivalently the class of languages whose membership is
certified by *every* polynomial-length certificate (Definition 2.20); the
equivalence is [AB09, Exercise 2.24]. This module also records the closure of
`P` under complement that the equivalence rides on, and the two standard
containment facts `P ⊆ NP ∩ coNP` and `P = NP → NP = coNP`.

## Design

* The complement-form Definition 2.19 is primary (it is one line); the
  ∀-certificate form is the characterization theorem, matching [AB09]'s own
  pedagogical ordering in reverse.
* `Complexity.compl_mem_P` is a statement *about the Chapter-1 class `P`* that
  Chapter 1 never needed; it is a new addition beyond the audited Chapter-1
  surface, placed here (its first consumer) and flagged for the phase-1 audit.

## Main definitions

* `Complexity.coNP` — the class coNP. [AB09, Definition 2.19]

## Main results

* `Complexity.compl_mem_P` — `P` is closed under complement.
* `Complexity.mem_coNP_iff_forall` — the ∀-certificate characterization
  [AB09, Definition 2.20 and Exercise 2.24].
* `Complexity.P_subset_NP_inter_coNP` — [AB09, Exercise 2.23].
* `Complexity.NP_eq_coNP_of_P_eq_NP` — [AB09, Exercise 2.25].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.6.1, Definitions 2.19-2.20, pp. 55-56;
  Exercises 2.23-2.25.)
-/

namespace Complexity

/-- **The class coNP** [AB09, Definition 2.19]: the complements of `NP` languages. -/
def coNP : Set (Language Bool) :=
  {L | Lᶜ ∈ NP}

/-- **`P` is closed under complement**: if `L` is decidable in polynomial time then
so is its complement.

**Proof sketch.** Obtain a decider of `L` from `Complexity.mem_P_iff`, read it
pointwise as computing the total singleton-indicator function (the decider's
output is exactly `[indicator L x]`), and postcompose with the Boolean-negation
postprocessor `Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]`
(`w ↦ if w = [true] then [false] else [true]`) via the **timed** total
composition `Turing.FinTM.computesFunInTime_comp` — the untimed
`exists_comp_partial` carries no time bound (phase-1 audit, finding 4). The
composite computes the complement's indicator within a budget polynomial by the
composition ledger and the monotonicity of the explicit polynomial; return
through `Complexity.mem_P_of_dtime_le`. Buffered composition keeps the
intermediate bit off the real output. This is a new statement about the
Chapter-1 class, flagged for audit (plan §6) and certified by the phase-1
round (finding 10). -/
theorem compl_mem_P {L : Language Bool} (h : L ∈ P) : Lᶜ ∈ P := by
  classical
  obtain ⟨C, d, M, hM⟩ := mem_P_iff.mp h
  obtain ⟨N, a, hN⟩ := Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]
  have hfun : M.ComputesFunInTime (fun x => [Turing.MultiTapeTM.indicator L x])
      (fun n => C * (n + 1) ^ d) := fun x => hM x
  -- Buffer the decider's singleton output and apply the timed Boolean postprocessor.
  obtain ⟨M', b, hcomp⟩ := Turing.FinTM.computesFunInTime_comp
    hfun hN
    (fun _ _ hle => Nat.mul_le_mul_left a (Nat.add_le_add_right hle 1))
  have hdec : M'.DecidesInTime Lᶜ
      (fun n => b * (C * (n + 1) ^ d + a * (C * (n + 1) ^ d + 1) + 1)) := by
    intro x
    by_cases hx : x ∈ L
    · have hxc : x ∉ (Lᶜ : Language Bool) := fun hnot => hnot hx
      simpa [Function.comp_apply, Turing.MultiTapeTM.indicator, hx, hxc] using hcomp x
    · have hxc : x ∈ (Lᶜ : Language Bool) := hx
      simpa [Function.comp_apply, Turing.MultiTapeTM.indicator, hx, hxc] using hcomp x
  -- Absorb the linear postprocessor and composition overhead into the same degree.
  refine mem_P_of_dtime_le
    (T := fun n => b * (C * (n + 1) ^ d + a * (C * (n + 1) ^ d + 1) + 1))
    ⟨1, M', by simpa only [one_mul] using hdec⟩
    (b * (C + a * (C + 1) + 1) * 2 ^ d) d ?_
  intro n
  have hpow : 1 ≤ (n + 1) ^ d := Nat.pow_pos (Nat.succ_pos n)
  have hsum : C * (n + 1) ^ d + 1 ≤ (C + 1) * (n + 1) ^ d := by
    calc C * (n + 1) ^ d + 1 ≤ C * (n + 1) ^ d + (n + 1) ^ d :=
        Nat.add_le_add_left hpow _
      _ = (C + 1) * (n + 1) ^ d := by ring
  calc b * (C * (n + 1) ^ d + a * (C * (n + 1) ^ d + 1) + 1)
      ≤ b * (C * (n + 1) ^ d + a * ((C + 1) * (n + 1) ^ d) + (n + 1) ^ d) :=
        Nat.mul_le_mul_left b
          (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left a hsum) _) hpow)
    _ = b * (C + a * (C + 1) + 1) * (n + 1) ^ d := by ring
    _ ≤ b * (C + a * (C + 1) + 1) * (2 ^ d * (n ^ d + 1)) :=
        Nat.mul_le_mul_left _ (succ_pow_le n d)
    _ = b * (C + a * (C + 1) + 1) * 2 ^ d * (n ^ d + 1) := by ring

/-- **The ∀-certificate characterization of coNP** [AB09, Definition 2.20,
equivalence per Exercise 2.24]: `L ∈ coNP` iff there are a certificate
coefficient `C`, degree `c`, and a verifier `V ∈ P` with
`x ∈ L ↔ ∀ u, |u| = C(|x|+1)^c → x ++ u ∈ V` — the same explicit length
formula as `Complexity.NP` (phase-1 audit repair, finding 1).

**Proof sketch.** Negate the exact-length existential in `NP`'s membership
equivalence for `Lᶜ`: `x ∈ L ↔ ¬(∃ u, |u| = C(|x|+1)^c ∧ x ++ u ∈ V₀)
↔ ∀ u, |u| = C(|x|+1)^c → x ++ u ∈ V₀ᶜ`, and `V₀ᶜ ∈ P` by
`Complexity.compl_mem_P`; both directions instantiate the same `C, c`,
complementing the verifier. Purely logical — no certificate-length computation
is needed (audit finding table). -/
theorem mem_coNP_iff_forall {L : Language Bool} :
    L ∈ coNP ↔ ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔
        ∀ u : List Bool, u.length = C * (x.length + 1) ^ c → x ++ u ∈ V := by
  classical
  constructor
  · rintro ⟨C, c, V, hV, hmem⟩
    refine ⟨C, c, Vᶜ, compl_mem_P hV, fun x => ?_⟩
    have hx : x ∉ L ↔ ∃ u : List Bool,
        u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V := hmem x
    change x ∈ L ↔ ∀ u : List Bool,
      u.length = C * (x.length + 1) ^ c → x ++ u ∉ V
    simpa only [not_not, not_exists, not_and] using not_congr hx
  · rintro ⟨C, c, V, hV, hmem⟩
    refine ⟨C, c, Vᶜ, compl_mem_P hV, fun x => ?_⟩
    change x ∉ L ↔ ∃ u : List Bool,
      u.length = C * (x.length + 1) ^ c ∧ x ++ u ∉ V
    simpa only [not_forall, exists_prop] using not_congr (hmem x)

/-- **`P ⊆ NP ∩ coNP`** [AB09, Exercise 2.23].

**Proof sketch.** `P ⊆ NP` is `Complexity.P_subset_NP`; for the `coNP` half,
`L ∈ P` gives `Lᶜ ∈ P ⊆ NP` by `Complexity.compl_mem_P`, i.e. `L ∈ coNP`. -/
theorem P_subset_NP_inter_coNP : P ⊆ NP ∩ coNP := by
  intro L hL
  exact ⟨P_subset_NP hL, P_subset_NP (compl_mem_P hL)⟩

/-- **If `P = NP` then `NP = coNP`** [AB09, Exercise 2.25].

**Proof sketch.** Under `P = NP`: `L ∈ NP → L ∈ P → Lᶜ ∈ P → Lᶜ ∈ NP → L ∈ coNP`
by `Complexity.compl_mem_P`, and symmetrically `L ∈ coNP → Lᶜ ∈ NP = P → L ∈ P =
NP` by closing under complement once more. -/
theorem NP_eq_coNP_of_P_eq_NP (h : P = NP) : NP = coNP := by
  apply Set.Subset.antisymm
  · intro L hL
    change Lᶜ ∈ NP
    rw [← h] at hL ⊢
    exact compl_mem_P hL
  · intro L hL
    change Lᶜ ∈ NP at hL
    rw [← h] at hL ⊢
    simpa only [compl_compl] using compl_mem_P hL

end Complexity

```


## ===== TCSlib/Complexity/ClassNP/SAT.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNFEncoding
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.ClassNP.Reductions
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.MinMax

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SAT and 3SAT

[AB09, §2.3.1]: `SAT` is the language of (strings representing) satisfiable CNF
formulas, `3SAT` its restriction to 3CNF formulas (at most three literals per
clause). This module defines both over the audited serialization layer, states
their membership in `NP`, and states [AB09, Lemma 2.14] (`SAT ≤ₚ 3SAT`) — the
(b) half of the Cook-Levin proof plan, whose (a) half (Lemma 2.11, `SAT` is
`NP`-hard) is phase-4 material.

## Design and deviations from [AB09]

* **Strings, not formulas, are the language elements**: membership goes through
  the total `Std.Sat.CNF.decode` ([AB09, footnote 3]). With the fallback being
  the empty formula — satisfiable, and vacuously 3CNF — **every non-well-formed
  string lies in `SAT` and in `3SAT`**. [AB09] declares the fallback choice
  immaterial, and every stated result survives any fixed fallback — but not
  "uniformly": each language's malformed-input branch follows **its own
  predicate** on the fallback (a satisfiable fallback of width four would put
  the non-well-formed strings in `SAT` and out of `3SAT` — round-1 audit,
  finding 5), and the Lemma-2.14 reduction maps a non-well-formed input to the
  serialization of the **transformed** fallback, which keeps the reduction
  equivalence whatever the fixed choice.
* **`TAUTOLOGY` and [AB09, Example 2.21] are deferred to phase 4** (plan
  decision log): [AB09]'s `TAUTOLOGY` ranges over general Boolean formulas, and
  its coNP-hardness reduction negates the Cook-Levin CNF into a **DNF** — while
  the CNF-restricted tautology language is polynomial-time decidable (a CNF is
  a tautology iff every clause contains a complementary literal pair), i.e. it
  is **not** [AB09]'s language. The faithful carrier (the DNF dual layer) and
  the hardness half's prerequisite (Lemma 2.11) both belong to phase 4, so the
  whole package moves there rather than stating a wrong-language definition
  here.

## Main definitions

* `Complexity.SAT` — satisfiable CNF strings. [AB09, §2.3.1]
* `Complexity.SAT3` — satisfiable 3CNF strings. [AB09, §2.3.1]

## Main results

* `Complexity.SAT_mem_NP`, `Complexity.SAT3_mem_NP` — the assignment is the
  certificate. [AB09, Theorem 2.10, membership part]
* `Complexity.SAT_reducible_SAT3` — clause splitting with fresh variables.
  [AB09, Lemma 2.14]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.3.1, pp. 44-45; Theorem 2.10, p. 45;
  Lemma 2.14, p. 48 with §2.3.5, pp. 50-51.)
-/

namespace Complexity

open Std.Sat (CNF)
open Turing

/-! Local names for the shared polynomial-time toolkit (`ClassNP/PolyTimePairing.lean`,
`TuringMachine/Composition.lean`), kept so this file's proofs can keep using its
historical `sat_*` names. -/

/-- A function computed in linear time is polynomial-time computable
(`polyTimeComputable_of_linear`). -/
private lemma sat_pt_linear (f : List Bool → List Bool)
    (h : ∃ (M : FinTM Bool) (C : ℕ),
      M.ComputesFunInTime f (fun n => C * (n + 1))) : PolyTimeComputable f :=
  polyTimeComputable_of_linear h

/-- A fixed word is polynomial-time computable (`polyTimeComputable_const`). -/
private lemma sat_pt_const (w : List Bool) : PolyTimeComputable (fun _ => w) :=
  polyTimeComputable_const w

/-- Polynomial-time branching on a polynomial-time bit (`polyTimeComputable_ite`). -/
private lemma sat_pt_cond {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => if p x then f x else g x) :=
  polyTimeComputable_ite hp hf hg

/-- The conjunction of two polynomial-time bits is polynomial-time
(`polyTimeComputable_and`). -/
private lemma sat_pt_and {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x && q x]) :=
  polyTimeComputable_and hp hq

/-- Composition of a function machine with a machine correct on its image
(`FinTM.exists_comp_on_image`). -/
private lemma sat_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
    (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
    (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
    ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2 * T₁ n + T₂ n + 2) :=
  FinTM.exists_comp_on_image M U f g T₁ T₂ hM hU

/-- **The language `SAT`** [AB09, §2.3.1]: binary strings whose decoded CNF
formula is satisfiable. Decoding is total ([AB09, footnote 3]), with the empty —
satisfiable — formula as fallback, so every non-well-formed string is in `SAT`
(see the deviations list). -/
def SAT : Language Bool :=
  {x | (CNF.decode x).Satisfiable}

/-- **The language `3SAT`** [AB09, §2.3.1]: binary strings whose decoded formula
is a satisfiable 3CNF — every clause with at most three literals. The fallback
formula has no clauses, so non-well-formed strings are in `3SAT` as well. -/
def SAT3 : Language Bool :=
  {x | (CNF.decode x).WidthAtMost 3 ∧ (CNF.decode x).Satisfiable}

/-! **Epoch-3 fill note.** The private verifier layer below uses the audited
`(1,1)` split. Syntax validation is a separate complete pass; neither width
nor evaluation is allowed to reject an incompletely parsed prefix. -/

/-- The finite assignment carried by a certificate, with the agreed default. -/
private def satAssignment (u : List Bool) : ℕ → Bool := fun v => u.getD v false

/-- Restricting a total assignment to the prescribed certificate length keeps
every variable used by the decoded formula. [AB09, Theorem 2.10, membership]

**Proof sketch.** Tabulate the first `|x|+1` bits. The decoded variable bound
puts each relevant index inside the tabulation; evaluation congruence applies. -/
private lemma sat_certificate (x : List Bool) :
    (CNF.decode x).Satisfiable ↔ ∃ u : List Bool,
      u.length = x.length + 1 ∧ (CNF.decode x).eval (satAssignment u) = true := by
  constructor
  · rintro ⟨a, ha⟩
    let u := List.ofFn (fun i : Fin (x.length + 1) => a i.val)
    refine ⟨u, List.length_ofFn, ?_⟩
    rw [← ha]
    apply eval_congr_of_lt_numVars
    intro v hv
    have hlt : v < x.length + 1 := Nat.lt_of_lt_of_le hv
      (Nat.le_trans (CNF.numVars_decode_le x) (Nat.le_succ _))
    simp only [satAssignment, u, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      dif_pos hlt, Option.getD_some]
  · rintro ⟨u, _, hu⟩
    exact ⟨satAssignment u, hu⟩

/-- A successful catalog split has the exact odd-length equation. -/
private lemma sat_split_some (N i : ℕ) (h : solveSplit 1 1 N = some i) :
    i + (i + 1) = N := by
  have he := List.find?_some h
  simpa [Nat.pow_one] using he

/-- The unique solution is found, including `N=1`, `i=0`. -/
private lemma sat_split_exists (N i : ℕ) (h : i + (i + 1) = N) :
    solveSplit 1 1 N = some i := by
  cases hs : solveSplit 1 1 N with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp <;> omega)
    simp [h] at hn
  | some j =>
    have hj := sat_split_some N j hs
    congr 1
    omega

/-- Boolean width test; repeated literals count as distinct occurrences. -/
private def satWidth (φ : CNF ℕ) : Bool := φ.all fun C => decide (C.length ≤ 3)

/-- The Boolean width scan is precisely the frozen formula predicate. -/
private lemma satWidth_spec (φ : CNF ℕ) :
    satWidth φ = true ↔ φ.WidthAtMost 3 := by
  simp [satWidth, CNF.WidthAtMost]

/-- The total mathematical verifier, with explicit rejection on split failure.
`decode` completes the syntax check before either semantic test is applied. -/
private def satVerdict (three : Bool) (z : List Bool) : Bool :=
  match solveSplit 1 1 z.length with
  | none => false
  | some i =>
      let φ := CNF.decode (z.take i)
      (!three || satWidth φ) && φ.eval (satAssignment (z.drop i))

/-- Verifier languages for the two prescribed `(1,1)` witnesses. -/
private def satVerifier (three : Bool) : Language Bool := {z | satVerdict three z = true}

/-- A correctly sized concatenation is recovered literally by the verifier. -/
private lemma satVerdict_append (three : Bool) (x u : List Bool)
    (hu : u.length = x.length + 1) :
    satVerdict three (x ++ u) =
      ((!three || satWidth (CNF.decode x)) && (CNF.decode x).eval (satAssignment u)) := by
  unfold satVerdict
  rw [sat_split_exists (x ++ u).length x.length (by simp [hu])]
  simp

/-- The SAT certificate equivalence, with exactly the audited `n+1` bits. -/
private lemma sat_verifier_equiv (x : List Bool) :
    x ∈ SAT ↔ ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ satVerifier false := by
  rw [show x ∈ SAT ↔ (CNF.decode x).Satisfiable from Iff.rfl, sat_certificate]
  apply exists_congr
  intro u
  apply and_congr_right
  intro hu
  change _ ↔ satVerdict false (x ++ u) = true
  simp [satVerdict_append false x u hu]

/-- Width depends only on the instance, so the same certificate suffices for 3SAT. -/
private lemma sat3_verifier_equiv (x : List Bool) :
    x ∈ SAT3 ↔ ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ satVerifier true := by
  change (CNF.decode x).WidthAtMost 3 ∧ (CNF.decode x).Satisfiable ↔ _
  rw [sat_certificate]
  constructor
  · rintro ⟨hw, u, hu, he⟩
    refine ⟨u, hu, ?_⟩
    change satVerdict true (x ++ u) = true
    simp [satVerdict_append true x u hu, (satWidth_spec _).mpr hw, he]
  · rintro ⟨u, hu, hv⟩
    change satVerdict true (x ++ u) = true at hv
    have hh : satWidth (CNF.decode x) = true ∧
        (CNF.decode x).eval (satAssignment u) = true := by
      simpa [satVerdict_append true x u hu] using hv
    exact ⟨(satWidth_spec _).mp hh.1, u, hu, hh.2⟩

/-- The unary scanner partitions its input into the counted run and its suffix. -/
private lemma sat_takeTrues_repr (x : List Bool) :
    List.replicate (CNF.takeTrues x).1 true ++ (CNF.takeTrues x).2 = x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b with
    | false => rfl
    | true => simpa [CNF.takeTrues, List.replicate_succ] using congrArg (true :: ·) ih

/-- A successful literal parse reconstructs exactly the consumed input. -/
private lemma sat_parseLit_repr {x r : List Bool} {ℓ : Std.Sat.Literal ℕ}
    (h : CNF.parseLit x = some (ℓ, r)) : x = CNF.serializeLit ℓ ++ r := by
  have ht := sat_takeTrues_repr x
  unfold CNF.parseLit at h
  split at h
  · cases h
  · rename_i k b rest he
    cases h
    simpa [he, CNF.serializeLit, List.append_assoc] using ht.symm
  · cases h

/-- Clause parsing reconstructs its terminator as well as every literal.

**Proof sketch.** Induct on fuel. The leading zero case succeeds even at
zero fuel. Otherwise invert both successful subparses and concatenate their
reconstruction equalities; no premature end of the input can succeed. -/
private lemma sat_parseClause_repr {fuel : ℕ} {x r : List Bool} {C : CNF.Clause ℕ}
    (h : CNF.parseClause fuel x = some (C, r)) : x = CNF.serializeClause C ++ r := by
  induction fuel generalizing x C r with
  | zero =>
    cases x with
    | nil => cases h
    | cons b s =>
      cases b with
      | false => cases h; rfl
      | true => cases h
  | succ fuel ih =>
    cases x with
    | nil => cases h
    | cons b s =>
      cases b with
      | false => cases h; rfl
      | true =>
        cases hl : CNF.parseLit (true :: s) with
        | none => simp [CNF.parseClause, hl] at h
        | some p =>
          obtain ⟨ℓ, t⟩ := p
          cases hc : CNF.parseClause fuel t with
          | none => simp [CNF.parseClause, hl, hc] at h
          | some p =>
            obtain ⟨D, v⟩ := p
            simp only [CNF.parseClause, hl, hc, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rw [sat_parseLit_repr hl, ih hc]
            simp [CNF.serializeClause, List.append_assoc]

/-- Formula parsing reconstructs every clause marker and the final terminator.

**Proof sketch.** Induct on fuel, retaining the unconsumed suffix. A clause
marker spends one unit of fuel before the clause and formula subparses.
The leading zero case works independently of the remaining fuel. -/
private lemma sat_parseClauses_repr {fuel : ℕ} {x r : List Bool} {φ : CNF ℕ}
    (h : CNF.parseClauses fuel x = some (φ, r)) : x = CNF.serialize φ ++ r := by
  induction fuel generalizing x φ r with
  | zero =>
    cases x with
    | nil => cases h
    | cons b s =>
      cases b with
      | false => cases h; rfl
      | true => cases h
  | succ fuel ih =>
    cases x with
    | nil => cases h
    | cons b s =>
      cases b with
      | false => cases h; rfl
      | true =>
        cases hc : CNF.parseClause fuel s with
        | none => simp [CNF.parseClauses, hc] at h
        | some p =>
          obtain ⟨C, t⟩ := p
          cases ht : CNF.parseClauses fuel t with
          | none => simp [CNF.parseClauses, hc, ht] at h
          | some p =>
            obtain ⟨ψ, v⟩ := p
            simp only [CNF.parseClauses, hc, ht, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rw [sat_parseClause_repr hc, ih ht]
            simp [CNF.serialize, CNF.serializeClause, List.append_assoc]

/-- Exact-consumption parsing is inverse serialization on every successful input. -/
private lemma sat_parse_repr {x : List Bool} {φ : CNF ℕ}
    (h : CNF.parse x = some φ) : x = CNF.serialize φ := by
  unfold CNF.parse at h
  split at h
  · rename_i ψ hp
    cases h
    simpa using sat_parseClauses_repr hp
  · cases h

/-- The six LL(1) positions: formula, clause, unary index, polarity, exact
end, and error. The end position becomes error on any trailing bit. -/
private def satSyntaxStep (q : Fin 6) (b : Bool) : Fin 6 :=
  match q.val with
  | 0 => if b then 1 else 4
  | 1 => if b then 2 else 0
  | 2 => if b then 2 else 3
  | 3 => 1
  | _ => 5

/-- Residual grammar at each finite-control position. Unary indices remain
unbounded strings; the finite control stores only their grammar position. -/
private def satSyntaxSuffix (q : Fin 6) (x : List Bool) : Prop :=
  match q.val with
  | 0 => ∃ φ : CNF ℕ, x = CNF.serialize φ
  | 1 => ∃ (C : CNF.Clause ℕ) (φ : CNF ℕ), x = CNF.serializeClause C ++ CNF.serialize φ
  | 2 => ∃ (v : ℕ) (b : Bool) (C : CNF.Clause ℕ) (φ : CNF ℕ),
      x = List.replicate v true ++ [false, b] ++ CNF.serializeClause C ++ CNF.serialize φ
  | 3 => ∃ (b : Bool) (C : CNF.Clause ℕ) (φ : CNF ℕ),
      x = b :: (CNF.serializeClause C ++ CNF.serialize φ)
  | 4 => x = []
  | _ => False

/-- Each transition consumes exactly one grammar bit.

**Proof sketch.** Invert the first clause, literal, or unary-run constructor
as appropriate. Formula and clause zero-markers are distinct states; the
polarity state consumes its bit unconditionally. No bit can follow the
exact-end state, which is how trailing garbage forces the fallback. -/
private lemma satSyntaxSuffix_cons (q : Fin 6) (b : Bool) (x : List Bool) :
    satSyntaxSuffix q (b :: x) ↔ satSyntaxSuffix (satSyntaxStep q b) x := by
  fin_cases q <;> cases b
  · change (∃ φ, false :: x = CNF.serialize φ) ↔ x = []
    constructor
    · rintro ⟨φ, h⟩; cases φ <;> simpa [CNF.serialize] using h
    · rintro rfl; exact ⟨[], rfl⟩
  · change (∃ φ, true :: x = CNF.serialize φ) ↔
      ∃ C φ, x = CNF.serializeClause C ++ CNF.serialize φ
    constructor
    · rintro ⟨φ, h⟩
      cases φ with
      | nil => simp [CNF.serialize] at h
      | cons C φ => exact ⟨C, φ, by simpa [CNF.serialize, List.append_assoc] using h⟩
    · rintro ⟨C, φ, rfl⟩
      exact ⟨C :: φ, by simp [CNF.serialize, List.append_assoc]⟩
  · change (∃ C φ, false :: x = CNF.serializeClause C ++ CNF.serialize φ) ↔
      ∃ φ, x = CNF.serialize φ
    constructor
    · rintro ⟨C, φ, h⟩
      cases C with
      | nil => exact ⟨φ, by simpa [CNF.serializeClause] using h⟩
      | cons ℓ C => simp [CNF.serializeClause, CNF.serializeLit, List.replicate_succ] at h
    · rintro ⟨φ, rfl⟩; exact ⟨[], φ, rfl⟩
  · change (∃ C φ, true :: x = CNF.serializeClause C ++ CNF.serialize φ) ↔
      ∃ v b C φ, x = List.replicate v true ++ [false, b] ++
        CNF.serializeClause C ++ CNF.serialize φ
    constructor
    · rintro ⟨C, φ, h⟩
      cases C with
      | nil => simp [CNF.serializeClause] at h
      | cons ℓ C =>
        exact ⟨ℓ.1, ℓ.2, C, φ, by simpa [CNF.serializeClause, CNF.serializeLit,
          List.replicate_succ, List.append_assoc] using h⟩
    · rintro ⟨v, b, C, φ, rfl⟩
      exact ⟨(v, b) :: C, φ, by simp [CNF.serializeClause, CNF.serializeLit,
        List.replicate_succ, List.append_assoc]⟩
  · change (∃ v b C φ, false :: x = List.replicate v true ++ [false, b] ++
      CNF.serializeClause C ++ CNF.serialize φ) ↔
        ∃ b C φ, x = b :: (CNF.serializeClause C ++ CNF.serialize φ)
    constructor
    · rintro ⟨v, b, C, φ, h⟩
      cases v with
      | zero => exact ⟨b, C, φ, by simpa [List.append_assoc] using h⟩
      | succ v => simp [List.replicate_succ] at h
    · rintro ⟨b, C, φ, rfl⟩; exact ⟨0, b, C, φ, by simp⟩
  · change (∃ v b C φ, true :: x = List.replicate v true ++ [false, b] ++
      CNF.serializeClause C ++ CNF.serialize φ) ↔
        ∃ v b C φ, x = List.replicate v true ++ [false, b] ++
          CNF.serializeClause C ++ CNF.serialize φ
    constructor
    · rintro ⟨v, b, C, φ, h⟩
      cases v with
      | zero => simp at h
      | succ v => exact ⟨v, b, C, φ, by simpa [List.replicate_succ] using h⟩
    · rintro ⟨v, b, C, φ, rfl⟩
      exact ⟨v + 1, b, C, φ, by simp [List.replicate_succ]⟩
  · change (∃ b C φ, false :: x = b :: (CNF.serializeClause C ++ CNF.serialize φ)) ↔
      ∃ C φ, x = CNF.serializeClause C ++ CNF.serialize φ
    simp
  · change (∃ b C φ, true :: x = b :: (CNF.serializeClause C ++ CNF.serialize φ)) ↔
      ∃ C φ, x = CNF.serializeClause C ++ CNF.serialize φ
    simp
  all_goals simp [satSyntaxSuffix, satSyntaxStep]

/-- At end of input, exactly the exact-end grammar state accepts. -/
private lemma satSyntaxSuffix_nil (q : Fin 6) : satSyntaxSuffix q [] ↔ q = 4 := by
  fin_cases q <;> simp [satSyntaxSuffix, CNF.serialize, CNF.serializeClause,
    List.append_eq_nil_iff]

/-- The complete finite-state scan recognizes precisely the residual grammar. -/
private lemma satSyntaxSuffix_run (q : Fin 6) (x : List Bool) :
    satSyntaxSuffix q x ↔ x.foldl satSyntaxStep q = 4 := by
  induction x generalizing q with
  | nil => exact satSyntaxSuffix_nil q
  | cons b x ih => rw [satSyntaxSuffix_cons, List.foldl_cons, ← ih]

/-- Boolean result of the complete syntax pass. -/
private def satSyntax (x : List Bool) : Bool := decide (x.foldl satSyntaxStep 0 = 4)

/-- The machine grammar and the audited parser agree on every string, including
empty input, unfinished literals, and trailing garbage.

**Proof sketch.** The residual-language invariant identifies scan acceptance
with the range of serialization. Successful parsing reconstructs its entire
input, and the existing parser round trip proves the converse. -/
private lemma satSyntax_spec (x : List Bool) : satSyntax x = (CNF.parse x).isSome := by
  apply Bool.eq_iff_iff.mpr
  simp only [satSyntax, decide_eq_true_eq]
  rw [← satSyntaxSuffix_run]
  change (∃ φ, x = CNF.serialize φ) ↔ (CNF.parse x).isSome = true
  constructor
  · rintro ⟨φ, rfl⟩; simp [CNF.parse_serialize]
  · intro h
    cases hp : CNF.parse x with
    | none => simp [hp] at h
    | some φ => exact ⟨φ, sat_parse_repr hp⟩

/-- One-way finite-state scanners use no work tapes and emit only the final
verdict, after inspecting the right boundary. -/
private def satScanTM {S : Type} [Fintype S] [DecidableEq S]
    (step : S → Bool → S) (start : S) (accept : S → Bool) : FinTM Bool where
  k := 0
  State := S
  tm := {
    q₀ := start
    tr := fun q inp _ => match inp with
      | some b => ⟨.pos, Fin.elim0, none, some (step q b)⟩
      | none => ⟨0, Fin.elim0, some (accept q), none⟩ }

/-- Scanner configuration just before input symbol `i`, with empty output. -/
private def satScanCfg {S : Type} (x : List Bool) (q : S) (i : ℕ)
    (hi : i ≤ x.length) : Cfg 0 Bool S x :=
  ⟨some q, ⟨i + 1, by omega⟩, Fin.elim0, Fin.elim0, []⟩

/-- One real scanner step consumes one input symbol silently. -/
private lemma satScan_step {S : Type} [Fintype S] [DecidableEq S]
    (step : S → Bool → S) (start : S) (accept : S → Bool)
    (x : List Bool) (q : S) (i : ℕ) (hi : i < x.length) :
    (satScanTM step start accept).tm.step (satScanCfg x q i (by omega)) =
      satScanCfg x (step q x[i]) (i + 1) (by omega) := by
  have hin := inputSymbolInner (cfg := satScanCfg x q i (by omega)) i
    (by simp [satScanCfg, Nat.add_comm]) hi
  unfold MultiTapeTM.step
  change (((satScanTM step start accept).tm.tr q _ _).apply _) = _
  rw [hin]
  apply Cfg.ext_zero_tapes
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [satScanCfg] <;> omega)
  · rfl

/-- A suffix scan consumes every remaining bit and then emits one verdict.

**Proof sketch.** Induct on the suffix. The empty case reads the right blank;
the nonempty case is one silent step followed by the induction hypothesis.
The initial output is empty and no earlier step emits. -/
private lemma satScan_run {S : Type} [Fintype S] [DecidableEq S]
    (step : S → Bool → S) (start : S) (accept : S → Bool)
    (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest) (q : S),
      ((satScanTM step start accept).tm.runFrom
        (satScanCfg x q pre.length (by simp [hx])) (rest.length + 1)).state = none ∧
      ((satScanTM step start accept).tm.runFrom
        (satScanCfg x q pre.length (by simp [hx])) (rest.length + 1)).output =
          [accept (rest.foldl step q)] := by
  induction rest with
  | nil =>
    intro pre hx q
    subst x
    simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, satScanTM,
      satScanCfg, Cfg.inputSymbol, Action.apply]
  | cons b rest ih =>
    intro pre hx q
    have hi : pre.length < x.length := by simp [hx]
    have hget : x[pre.length] = b := by simp [hx]
    have hs := satScan_step step start accept x q pre.length hi
    rw [hget] at hs
    simp only [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    rw [hs]
    simpa only [List.length_append, List.length_singleton, List.foldl_cons] using
      ih (pre ++ [b]) (by simpa [List.append_assoc] using hx) (step q b)

/-- Every such scanner has the exact `n+1` bound. -/
private lemma satScan_computes {S : Type} [Fintype S] [DecidableEq S]
    (step : S → Bool → S) (start : S) (accept : S → Bool) :
    (satScanTM step start accept).ComputesFunInTime
      (fun x => [accept (x.foldl step start)]) (fun n => n + 1) := by
  intro x
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  have hinit : (satScanTM step start accept).tm.initCfg x =
      satScanCfg x start 0 (Nat.zero_le _) := Cfg.ext_zero_tapes rfl rfl rfl
  rw [hinit]
  exact satScan_run step start accept x x [] rfl start

/-- The complete CNF syntax pass is realized by an actual finite machine.
The result concerns every input, not merely serialized formulas. -/
private lemma satSyntax_poly : PolyTimeComputable (fun x => [satSyntax x]) := by
  refine ⟨satScanTM satSyntaxStep 0 (fun q => decide (q = 4)), 1, 1, ?_⟩
  simpa only [Nat.pow_one, Nat.one_mul, satSyntax] using
    satScan_computes satSyntaxStep 0 (fun q => decide (q = 4))

/-- Administrative states, or a streaming phase (formula, clause, index,
polarity, rewind) with formula/clause truth bits and a doubled-bit skip flag. -/
private abbrev SatEvalControl := Fin 4 ⊕ (Fin 5 × Bool × Bool × Bool)

/-- A semantic phase, with the input poised at a doubled bit unless skipping. -/
private def satEvalQ (q : Fin 5) (a c skip : Bool) : SatEvalControl :=
  .inr (q, a, c, skip)

/-- Administrative evaluation actions preserve all tape contents and move only
the input head and the captured-certificate head. -/
private def satEvalAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option SatEvalControl) : Action (M.k + 1) Bool (M.State ⊕ SatEvalControl) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q.map Sum.inr⟩

/-- Capture the certificate extractor, rewind, and evaluate a previously
validated doubled formula. No physical output occurs before the verdict.
Unary index walks and their rewinds take linear time in the literal encoding.
[AB09, Theorem 2.10, membership] -/
private def satEvalTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ SatEvalControl
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun s inp work => match s with
    | .inl q => captureAction Sum.inl (.inr (.inl 0))
        (M.tm.tr q inp fun i => work i.castSucc)
    | .inr (.inl q) => match q.val with
      | 0 => FinTM.controlAction .neg (some (.inr (.inl 1)))
      | 1 => match inp with
        | some _ => FinTM.controlAction .neg (some (.inr (.inl 1)))
        | none => FinTM.controlAction .pos (some (.inr (.inl 2)))
      | 2 => satEvalAction M 0 .neg none (some (.inl 3))
      | _ => match work (Fin.last M.k) with
        | some _ => satEvalAction M 0 .neg none (some (.inl 3))
        | none => satEvalAction M 0 .pos none (some (satEvalQ 0 true false false))
    | .inr (.inr (q, a, c, skip)) =>
      if skip then satEvalAction M .pos 0 none (some (satEvalQ q a c false))
      else if q = 4 then
        match work (Fin.last M.k) with
        | some _ => satEvalAction M 0 .neg none (some (satEvalQ 4 a c false))
        | none => satEvalAction M 0 .pos none (some (satEvalQ 1 a c false))
      else match inp with
        | none => satEvalAction M 0 0 (some false) none
        | some b => match q.val with
          | 0 => if b then satEvalAction M .pos 0 none (some (satEvalQ 1 a false true))
            else satEvalAction M 0 0 (some a) none
          | 1 => if b then satEvalAction M .pos 0 none (some (satEvalQ 2 a c true))
            else satEvalAction M .pos 0 none (some (satEvalQ 0 (a && c) false true))
          | 2 => if b then satEvalAction M .pos .pos none (some (satEvalQ 2 a c true))
            else satEvalAction M .pos 0 none (some (satEvalQ 3 a c true))
          | _ => satEvalAction M .pos 0 none
              (some (satEvalQ 4 a (c || decide (work (Fin.last M.k) = some b)) true)) }

/-- The saved extractor bank and the certificate buffer during evaluation. -/
private def satEvalCfg (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q : SatEvalControl)
    (i : ℕ) (hi : i ≤ w.length) (j : ℤ) : Cfg (M.k + 1) Bool (satEvalTM M).State w :=
  ⟨some (.inr q), ⟨i + 1, by omega⟩,
    fun t => if h : t.val < M.k then saved.workTapes ⟨t, h⟩ else FinTM.bufferTape u,
    fun t => if h : t.val < M.k then saved.workTapePos ⟨t, h⟩ else j, []⟩

/-- The input read does not depend on the saved extractor bank. -/
private lemma satEvalCfg_input (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q : SatEvalControl)
    (i : ℕ) (hi : i ≤ w.length) (j : ℤ) :
    (satEvalCfg M saved u q i hi j).inputSymbol = w[i]? :=
  FinTM.inputSymbol_at _ i hi rfl

/-- The last work head reads exactly the immutable certificate buffer. -/
private lemma satEvalCfg_work (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q : SatEvalControl)
    (i : ℕ) (hi : i ≤ w.length) (j : ℤ) :
    (satEvalCfg M saved u q i hi j).workTapeSymbols (Fin.last M.k) =
      FinTM.bufferTape u j := by
  simp [satEvalCfg, Cfg.workTapeSymbols]

/-- A live administrative action preserves both the saved bank and output. -/
private lemma satEvalAction_apply (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q q' : SatEvalControl)
    (i i' : ℕ) (hi : i ≤ w.length) (hi' : i' ≤ w.length) (j j' : ℤ)
    (m d : SignType)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (w.length + 2)) m = ⟨i' + 1, by omega⟩)
    (hd : j + d.cast = j') :
    (satEvalAction M m d none (some q')).apply (satEvalCfg M saved u q i hi j) =
      satEvalCfg M saved u q' i' hi' j' := by
  refine Cfg.ext rfl hm rfl ?_ rfl
  funext t
  by_cases ht : t.val < M.k
  · simp [satEvalAction, satEvalCfg, Action.apply, ht]
  · simpa [satEvalAction, satEvalCfg, Action.apply, ht] using hd

/-- The second bit of a doubled input symbol is skipped silently. -/
private lemma satEval_skip (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q : Fin 5) (a c : Bool)
    (i : ℕ) (hi : i < w.length) (j : ℤ) :
    (satEvalTM M).tm.step (satEvalCfg M saved u (satEvalQ q a c true) i (by omega) j) =
      satEvalCfg M saved u (satEvalQ q a c false) (i + 1) (by omega) j := by
  unfold MultiTapeTM.step
  change (satEvalAction M .pos 0 none (some (satEvalQ q a c false))).apply _ = _
  exact satEvalAction_apply M saved u _ _ i (i + 1) (by omega) (by omega)
    j j .pos 0 (moveInputPos_pos_of_ne_right _ (by simp <;> omega)) (by simp)

/-- A local semantic transition followed by its skip consumes a doubled bit.
The last work head moves only on the first of the two physical transitions.

**Proof sketch.** Apply the semantic transition with the stated input and work-head move, then apply the
silent skip. The two native positions remain inside the doubled input. -/
private lemma satEval_double (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool)
    (q q' : Fin 5) (a c a' c' b : Bool) (i : ℕ) (hi : i + 2 ≤ w.length)
    (j j' : ℤ) (d : SignType) (hd : j + d.cast = j')
    (hin : w[i]? = some b)
    (htr : (satEvalTM M).tm.tr (.inr (satEvalQ q a c false)) (some b)
      (satEvalCfg M saved u (satEvalQ q a c false) i (by omega) j).workTapeSymbols =
        satEvalAction M .pos d none (some (satEvalQ q' a' c' true))) :
    (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ q a c false) i (by omega) j) 2 =
        satEvalCfg M saved u (satEvalQ q' a' c' false) (i + 2) hi j' := by
  have hs : (satEvalTM M).tm.step
      (satEvalCfg M saved u (satEvalQ q a c false) i (by omega) j) =
        satEvalCfg M saved u (satEvalQ q' a' c' true) (i + 1) (by omega) j' := by
    unfold MultiTapeTM.step
    change ((satEvalTM M).tm.tr (.inr (satEvalQ q a c false)) _ _).apply _ = _
    rw [satEvalCfg_input, hin, htr]
    exact satEvalAction_apply M saved u _ _ i (i + 1) (by omega) (by omega)
      j j' .pos d (moveInputPos_pos_of_ne_right _ (by simp <;> omega)) hd
  change (satEvalTM M).tm.step ((satEvalTM M).tm.step _) = _
  rw [hs, satEval_skip M saved u q' a' c' (i + 1) (by omega) j']

/-- Any left-moving certificate rewind takes exactly `n+1` steps from head
`n-1`, returns to zero, and preserves all native input and output fields.

**Proof sketch.** Induct on `n`. At `-1` the buffer is blank; otherwise its
cell is a certificate bit, so one silent left move exposes the shorter case. -/
private lemma satEval_rewind (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q dest : SatEvalControl)
    (htr : ∀ inp work, (satEvalTM M).tm.tr (.inr q) inp work =
      match work (Fin.last M.k) with
      | some _ => satEvalAction M 0 .neg none (some q)
      | none => satEvalAction M 0 .pos none (some dest))
    (i : ℕ) (hi : i ≤ w.length) (n : ℕ) (hn : n ≤ u.length) :
    (satEvalTM M).tm.runFrom (satEvalCfg M saved u q i hi ((n : ℤ) - 1)) (n + 1) =
      satEvalCfg M saved u dest i hi 0 := by
  induction n with
  | zero =>
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((satEvalTM M).tm.tr (.inr q) _ _).apply _ = _
    rw [htr, satEvalCfg_work]
    simp only [Int.natCast_zero, zero_sub, FinTM.bufferTape_left]
    exact satEvalAction_apply M saved u q dest i i hi hi (-1) 0 0 .pos
      (moveInputPos_zero _) (by simp)
  | succ n ih =>
    have hw : FinTM.bufferTape u (((n + 1 : ℕ) : ℤ) - 1) = some u[n] := by
      simp [FinTM.bufferTape, List.getElem?_eq_getElem (by omega : n < u.length)]
    have hs : (satEvalTM M).tm.step
        (satEvalCfg M saved u q i hi (((n + 1 : ℕ) : ℤ) - 1)) =
          satEvalCfg M saved u q i hi ((n : ℤ) - 1) := by
      unfold MultiTapeTM.step
      change ((satEvalTM M).tm.tr (.inr q) _ _).apply _ = _
      rw [htr, satEvalCfg_work, hw]
      exact satEvalAction_apply M saved u q q i i hi hi _ _ 0 .neg
        (moveInputPos_zero _) (by simp [SignType.cast] <;> omega)
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]

/-- The native pairing prefix doubles every formula bit. -/
private def satBits (x : List Bool) : List Bool := x.flatMap fun b => [b, b]

/-- Doubled data has exactly twice the native length. -/
private lemma satBits_length (x : List Bool) : (satBits x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [satBits, List.flatMap_cons] at * <;> omega

/-- A unary index scan advances the certificate head once per remaining one.
The first one of a literal is consumed by the clause state, so this scan's
count is the variable index, not its successor. -/
private lemma satEval_index (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (a c : Bool)
    (n : ℕ) : ∀ pre rest (hw : w = pre ++ satBits (List.replicate n true) ++ rest) (j : ℤ),
    (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 2 a c false) pre.length (by simp [hw]) j) (2 * n) =
        satEvalCfg M saved u (satEvalQ 2 a c false) (pre.length + 2 * n)
          (by simp only [hw, List.length_append, satBits_length, List.length_replicate] <;> omega)
          (j + n) := by
  induction n with
  | zero => intros; simp [MultiTapeTM.runFrom_zero]
  | succ n ih =>
    intro pre rest hw j
    have hw' : w = (pre ++ [true, true]) ++ satBits (List.replicate n true) ++ rest := by
      simpa [satBits, List.replicate_succ, List.append_assoc] using hw
    have hi : pre.length + 2 ≤ w.length := by simp [hw']
    have hs := satEval_double M saved u 2 2 a c a c true pre.length hi j (j + 1)
      .pos (by simp) (by simp [hw', List.append_assoc]) (by rfl)
    conv_lhs => rw [show 2 * (n + 1) = 2 + 2 * n by omega, MultiTapeTM.runFrom_add, hs]
    have hr := ih (pre ++ [true, true]) rest hw' (j + 1)
    simpa [Nat.mul_add, add_assoc, add_comm, add_left_comm] using hr

/-- A literal walk and its rewind take exactly `3v+8` transitions, return the
certificate head to zero, and update only the clause truth bit.

**Proof sketch.** Consume the first doubled one, walk the remaining `v`
ones, read the terminator and polarity, and rewind `v+1` occupied cells.
The certificate-length hypothesis guarantees the compared cell is present. -/
private lemma satEval_literal (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (a c b : Bool) (v : ℕ)
    (hv : v < u.length) (pre rest : List Bool)
    (hw : w = pre ++ satBits (CNF.serializeLit (v, b)) ++ rest) :
    (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 1 a c false) pre.length (by simp [hw]) 0) (3 * v + 8) =
      satEvalCfg M saved u (satEvalQ 1 a (c || (satAssignment u v == b)) false)
        (pre.length + 2 * (v + 3))
        (by simp [hw, satBits_length, CNF.serializeLit] <;> omega) 0 := by
  let p₁ := pre ++ [true, true]
  let p₂ := p₁ ++ satBits (List.replicate v true)
  let p₃ := p₂ ++ [false, false]
  let p₄ := p₃ ++ [b, b]
  have hw₁ : w = p₁ ++ satBits (List.replicate v true) ++ [false, false, b, b] ++ rest := by
    simpa [p₁, satBits, CNF.serializeLit, List.replicate_succ, List.append_assoc] using hw
  have hw₂ : w = p₂ ++ [false, false, b, b] ++ rest := hw₁
  have hw₃ : w = p₃ ++ [b, b] ++ rest := by simpa [p₃, List.append_assoc] using hw₂
  have hw₄ : w = p₄ ++ rest := by simpa [p₄, List.append_assoc] using hw₃
  have h₁ := satEval_double M saved u 1 2 a c a c true pre.length
    (by simp [hw₁, p₁] <;> omega) 0 0 0 (by simp)
    (by simp [hw₁, p₁, List.append_assoc]) (by rfl)
  have h₂ := satEval_index M saved u a c v p₁ ([false, false, b, b] ++ rest)
    (by simpa [List.append_assoc] using hw₁) 0
  have h₃ := satEval_double M saved u 2 3 a c a c false p₂.length
    (by simp [hw₂]) (v : ℤ) v 0 (by simp)
    (by simp [hw₂, List.append_assoc]) (by rfl)
  have hread : FinTM.bufferTape u (v : ℤ) = some (satAssignment u v) := by
    simp only [FinTM.bufferTape_nat, satAssignment, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hv, Option.getD_some]
  have h₄ := satEval_double M saved u 3 4 a c a (c || (satAssignment u v == b)) b p₃.length
    (by simp [hw₃]) (v : ℤ) v 0 (by simp) (by simp [hw₃, List.append_assoc]) (by
      simp only [satEvalTM, satEvalQ, Bool.false_eq_true, ↓reduceIte]
      rw [satEvalCfg_work, hread]
      cases h : satAssignment u v <;> cases b <;> rfl)
  have h₅ := satEval_rewind M saved u (satEvalQ 4 a (c || (satAssignment u v == b)) false)
    (satEvalQ 1 a (c || (satAssignment u v == b)) false) (by intros; rfl)
    p₄.length (by simp [hw₄]) (v + 1) (by omega)
  have hl₂ : p₂.length = pre.length + 2 + 2 * v := by simp [p₂, p₁, satBits_length] <;> omega
  have hl₃ : p₃.length = pre.length + 2 + 2 * v + 2 := by simp [p₃, hl₂]
  have hl₄ : p₄.length = pre.length + 2 + 2 * v + 2 + 2 := by simp [p₄, hl₃]
  have hh₂ : (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 2 a c false) (pre.length + 2) (by simp [hw₁, p₁] <;> omega) 0)
        (2 * v) = satEvalCfg M saved u (satEvalQ 2 a c false) p₂.length (by simp [hw₂]) v := by
    simpa [p₁, hl₂] using h₂
  have hh₃ : (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 2 a c false) p₂.length (by simp [hw₂]) v) 2 =
        satEvalCfg M saved u (satEvalQ 3 a c false) p₃.length (by simp [hw₃]) v := by
    simpa [p₃] using h₃
  have hh₄ : (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 3 a c false) p₃.length (by simp [hw₃]) v) 2 =
        satEvalCfg M saved u (satEvalQ 4 a (c || (satAssignment u v == b)) false)
          p₄.length (by simp [hw₄]) v := by
    simpa [p₄] using h₄
  have hh₅ : (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 4 a (c || (satAssignment u v == b)) false)
        p₄.length (by simp [hw₄]) v) (v + 2) =
        satEvalCfg M saved u (satEvalQ 1 a (c || (satAssignment u v == b)) false)
          p₄.length (by simp [hw₄]) 0 := by simpa using h₅
  conv_lhs => rw [show 3 * v + 8 = 2 + (2 * v + (2 + (2 + (v + 2)))) by omega,
    MultiTapeTM.runFrom_add, h₁, MultiTapeTM.runFrom_add, hh₂,
    MultiTapeTM.runFrom_add, hh₃, MultiTapeTM.runFrom_add, hh₄, hh₅]
  congr 1
  omega

/-- A clause pass returns to formula control with its accumulated truth bit.
No verdict is emitted by this pass, even for an empty or false clause.

**Proof sketch.** Induct on literals, composing the exact literal walk with
the tail pass. The closing zero takes two physical transitions. Sum the
literal bounds against three times their unary serialization lengths. -/
private lemma satEval_clause (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (C : CNF.Clause ℕ)
    (hvars : ∀ ℓ ∈ C, ℓ.1 < u.length) :
    ∀ pre rest (hw : w = pre ++ satBits (CNF.serializeClause C) ++ rest) (a c : Bool),
    ∃ t ≤ 3 * (CNF.serializeClause C).length,
      (satEvalTM M).tm.runFrom
        (satEvalCfg M saved u (satEvalQ 1 a c false) pre.length (by simp [hw]) 0) t =
      satEvalCfg M saved u
        (satEvalQ 0 (a && (c || CNF.Clause.eval (satAssignment u) C)) false false)
        (pre.length + 2 * (CNF.serializeClause C).length)
        (by simp only [hw, List.length_append, satBits_length] <;> omega) 0 := by
  induction C with
  | nil =>
    intro pre rest hw a c
    refine ⟨2, by simp [CNF.serializeClause], ?_⟩
    have h := satEval_double M saved u 1 0 a c (a && c) false false pre.length
      (by simp [hw, CNF.serializeClause, satBits]) 0 0 0 (by simp)
      (by simp [hw, CNF.serializeClause, satBits]) (by rfl)
    simpa [CNF.serializeClause, CNF.Clause.eval_nil] using h
  | cons ℓ C ih =>
    intro pre rest hw a c
    have hv := hvars ℓ List.mem_cons_self
    have htvars : ∀ d ∈ C, d.1 < u.length := fun d hd => hvars d (List.mem_cons_of_mem ℓ hd)
    let pre' := pre ++ satBits (CNF.serializeLit ℓ)
    have hw' : w = pre' ++ satBits (CNF.serializeClause C) ++ rest := by
      simpa [pre', satBits, CNF.serializeClause, List.append_assoc] using hw
    have hl : pre'.length = pre.length + 2 * (ℓ.1 + 3) := by
      simp [pre', satBits_length, CNF.serializeLit] <;> omega
    have hs := satEval_literal M saved u a c ℓ.2 ℓ.1 hv pre
      (satBits (CNF.serializeClause C) ++ rest)
      (by simpa [pre', List.append_assoc] using hw')
    obtain ⟨t, ht, hr⟩ := ih htvars pre' rest hw' a (c || (satAssignment u ℓ.1 == ℓ.2))
    have hlen : (CNF.serializeClause (ℓ :: C)).length =
        ℓ.1 + 3 + (CNF.serializeClause C).length := by
      simp [CNF.serializeClause, CNF.serializeLit] <;> omega
    refine ⟨3 * ℓ.1 + 8 + t, by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hs]
    simpa only [hl, hlen, Nat.mul_add, Nat.add_assoc, CNF.Clause.eval_cons, Bool.or_assoc] using hr

/-- The streaming evaluation pass computes the conjunction of all clauses.

**Proof sketch.** Induct on clauses. Each clause starts with its marker and
runs the silent clause pass; conjunction is accumulated in finite control.
Only the final formula terminator emits. The native formula length pays for
all unary walks and rewinds, including empty formulas and empty clauses. -/
private lemma satEval_formula (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (φ : CNF ℕ)
    (hvars : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < u.length) :
    ∀ pre rest (hw : w = pre ++ satBits (CNF.serialize φ) ++ rest) (a : Bool),
    ∃ t ≤ 3 * (CNF.serialize φ).length,
      ((satEvalTM M).tm.runFrom
        (satEvalCfg M saved u (satEvalQ 0 a false false) pre.length (by simp [hw]) 0) t).state = none ∧
      ((satEvalTM M).tm.runFrom
        (satEvalCfg M saved u (satEvalQ 0 a false false) pre.length (by simp [hw]) 0) t).output =
          [a && φ.eval (satAssignment u)] := by
  induction φ with
  | nil =>
    intro pre rest hw a
    refine ⟨1, by simp [CNF.serialize], ?_⟩
    have hin : (satEvalCfg M saved u (satEvalQ 0 a false false)
        pre.length (by simp [hw]) 0).inputSymbol = some false := by
      rw [satEvalCfg_input]
      simp [hw, CNF.serialize, satBits]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
      MultiTapeTM.step, satEvalCfg, satEvalQ] at hin ⊢
    rw [hin]
    simp [satEvalTM, satEvalAction, satEvalQ, CNF.eval_nil]
  | cons C φ ih =>
    intro pre rest hw a
    have hcvars : ∀ ℓ ∈ C, ℓ.1 < u.length := hvars C List.mem_cons_self
    have htvars : ∀ D ∈ φ, ∀ ℓ ∈ D, ℓ.1 < u.length :=
      fun D hD => hvars D (List.mem_cons_of_mem C hD)
    let pre₁ := pre ++ [true, true]
    let pre₂ := pre₁ ++ satBits (CNF.serializeClause C)
    have hw₁ : w = pre₁ ++ satBits (CNF.serializeClause C) ++ satBits (CNF.serialize φ) ++ rest := by
      simpa [pre₁, satBits, CNF.serialize, List.append_assoc] using hw
    have hw₂ : w = pre₂ ++ satBits (CNF.serialize φ) ++ rest := hw₁
    have h₁ := satEval_double M saved u 0 1 a false a false true pre.length
      (by simp [hw₁, pre₁]) 0 0 0 (by simp)
      (by simp [hw₁, pre₁, List.append_assoc]) (by rfl)
    obtain ⟨s, hs, hc⟩ := satEval_clause M saved u C hcvars pre₁
      (satBits (CNF.serialize φ) ++ rest) (by simpa [List.append_assoc] using hw₁) a false
    have hp₁ : pre₁.length = pre.length + 2 := by simp [pre₁]
    have hp₂ : pre₂.length = pre.length + 2 + 2 * (CNF.serializeClause C).length := by
      change (pre₁ ++ satBits (CNF.serializeClause C)).length = _
      rw [List.length_append, hp₁, satBits_length]
    have hc' : (satEvalTM M).tm.runFrom
        (satEvalCfg M saved u (satEvalQ 1 a false false) (pre.length + 2)
          (by simp [hw₁, pre₁]) 0) s =
        satEvalCfg M saved u (satEvalQ 0 (a && CNF.Clause.eval (satAssignment u) C) false false)
          pre₂.length (by simp [hw₂]) 0 := by
      simpa only [hp₁, hp₂, Bool.false_or] using hc
    obtain ⟨t, ht, hr⟩ := ih htvars pre₂ rest hw₂ (a && CNF.Clause.eval (satAssignment u) C)
    have hlen : (CNF.serialize (C :: φ)).length =
        1 + (CNF.serializeClause C).length + (CNF.serialize φ).length := by
      simp [CNF.serialize, CNF.serializeClause] <;> omega
    refine ⟨2 + (s + t), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, h₁, MultiTapeTM.runFrom_add, hc']
    simpa only [CNF.eval_cons, Bool.and_assoc] using hr

/-- Select the actual first halting transition, retaining its final emission. -/
private lemma sat_first_halt (M : FinTM Bool) (x y : List Bool) (T : ℕ)
    (h : M.ComputesInTime x y T) :
    ∃ t ≤ T, (∀ r < t, (M.tm.runFrom (M.tm.initCfg x) r).state ≠ none) ∧
      (M.tm.runFrom (M.tm.initCfg x) t).state = none ∧
      (M.tm.runFrom (M.tm.initCfg x) t).output = y := by
  classical
  have hh := (FinTM.computesInTime_iff _ _ _ _).mp h
  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T, hh.1⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hh.1
  have hs : (M.tm.runFrom (M.tm.initCfg x) t).state = none := Nat.find_spec hex
  have he := M.tm.runFrom_add (M.tm.initCfg x) t (T - t)
  rw [Nat.add_sub_of_le ht, MultiTapeTM.runFrom_of_halt _ hs] at he
  exact ⟨t, ht, fun r hr => Nat.find_min hex hr, hs, by rw [← he]; exact hh.2⟩

/-- Capture and both rewinds establish the evaluator's empty-output seam.

**Proof sketch.** Capture through the extractor's first halt (including a
halting emission), rewind the native input using the audited contract, then
rewind the immutable certificate buffer. Only the final evaluator emits. -/
private lemma satEval_start (M : FinTM Bool) (w u : List Bool) (T : ℕ)
    (hM : M.ComputesInTime w u T) :
    ∃ (saved : Cfg M.k Bool M.State w) (s : ℕ), s ≤ T + w.length + u.length + 5 ∧
      (satEvalTM M).tm.runFrom ((satEvalTM M).tm.initCfg w) s =
        satEvalCfg M saved u (satEvalQ 0 true false false) 0 (Nat.zero_le _) 0 := by
  obtain ⟨t, ht, hlive, hhalt, hout⟩ := sat_first_halt M w u T hM
  let saved := M.tm.runFrom (M.tm.initCfg w) t
  let captured := captureCfg (Sum.inl : M.State → (satEvalTM M).State)
    (.inr (.inl 0)) [] [] saved
  have hinit : (satEvalTM M).tm.initCfg w =
      captureCfg (Sum.inl : M.State → (satEvalTM M).State)
        (.inr (.inl 0)) [] [] (M.tm.initCfg w) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i z
      simp [captureCfg, MultiTapeTM.initCfg, Cfg.init, FinTM.bufferTape]
    · funext i
      simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (satEvalTM M).tm.runFrom ((satEvalTM M).tm.initCfg w) t = captured := by
    rw [hinit]
    exact capture_run M.tm (satEvalTM M).tm Sum.inl (.inr (.inl 0))
      (by intros; rfl) [] [] (M.tm.initCfg w) t hlive
  have hstate : captured.state = some (.inr (.inl 0)) := by
    simp only [captured, captureCfg, saved, hhalt, Option.map_none, Option.getD_none]
  obtain ⟨r, hr, hrew⟩ := FinTM.timed_rewind (satEvalTM M).tm (.inr (.inl 0))
    (.inr (.inl 1)) (some (.inr (.inl 2))) (by intros; rfl) (by intros; rfl)
    captured hstate
  have hafter : {captured with state := some (.inr (.inl 2)), inputPos := 1} =
      satEvalCfg M saved u (.inl 2) 0 (Nat.zero_le _) u.length := by
    simp only [captured, captureCfg, saved, hout, List.nil_append, satEvalCfg]
    exact Cfg.ext rfl (by apply Fin.ext; simp) rfl rfl rfl
  rw [hafter] at hrew
  have hleft : (satEvalTM M).tm.step
      (satEvalCfg M saved u (.inl 2) 0 (Nat.zero_le _) u.length) =
        satEvalCfg M saved u (.inl 3) 0 (Nat.zero_le _) ((u.length : ℤ) - 1) := by
    unfold MultiTapeTM.step
    change (satEvalAction M 0 .neg none (some (.inl 3))).apply _ = _
    exact satEvalAction_apply M saved u _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
      _ _ 0 .neg (moveInputPos_zero _) (by simp [SignType.cast]; omega)
  have htape := satEval_rewind M saved u (.inl 3) (satEvalQ 0 true false false)
    (by intros; rfl) 0 (Nat.zero_le _) u.length (Nat.le_refl _)
  refine ⟨saved, t + r + (u.length + 2), ?_, ?_⟩
  · have hp := captured.inputPos.isLt
    omega
  · have hprefix : (satEvalTM M).tm.runFrom ((satEvalTM M).tm.initCfg w) (t + r) =
        satEvalCfg M saved u (.inl 2) 0 (Nat.zero_le _) u.length := by
      rw [MultiTapeTM.runFrom_add, hcap, hrew]
    rw [MultiTapeTM.runFrom_add, hprefix, MultiTapeTM.runFrom_succ_eq_step, hleft, htape]

/-- One uniform finite evaluator works for every well-formed paired formula
and certificate covering its variables. Its full capture/startup/evaluation
cost is linear in the native paired-input length.

**Proof sketch.** Choose the catalog certificate extractor once. Capture its first halting run, establish
the evaluation seam, and run the formula pass. Its variable bound makes every assignment
lookup defined; combine the linear bounds. -/
private lemma satEval_computes : ∃ (E : FinTM Bool) (A : ℕ),
    ∀ (φ : CNF ℕ) (u : List Bool), (∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < u.length) →
      E.ComputesInTime (pairEncode (CNF.serialize φ) u) [φ.eval (satAssignment u)]
        (A * ((pairEncode (CNF.serialize φ) u).length + 1)) := by
  obtain ⟨M, B, hM⟩ := FinTM.computesFunInTime_pairSnd
  refine ⟨satEvalTM M, B + 6, ?_⟩
  intro φ u hv
  let w := pairEncode (CNF.serialize φ) u
  have hsource : M.ComputesInTime w u (B * (w.length + 1)) := by
    simpa only [w, pairDecode_pairEncode, Option.map_some, Option.getD_some] using hM w
  obtain ⟨saved, s, hs, hstart⟩ := satEval_start M w u (B * (w.length + 1)) hsource
  have hw : w = [] ++ satBits (CNF.serialize φ) ++ ([false, true] ++ u) := by
    simp [w, pairEncode, satBits, List.append_assoc]
  obtain ⟨t, ht, hhalt, hout⟩ := satEval_formula M saved u φ hv [] ([false, true] ++ u) hw true
  have hbase : (satEvalTM M).ComputesInTime w [φ.eval (satAssignment u)] (s + t) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hhalt, by simpa only [Bool.true_and] using hout⟩
  apply hbase.mono
  have hwlen : w.length = 2 * (CNF.serialize φ).length + 2 + u.length := by
    change (satBits (CNF.serialize φ) ++ [false, true] ++ u).length = _
    simp [satBits_length] <;> omega
  change s + t ≤ (B + 6) * (w.length + 1)
  simp only [Nat.add_mul]
  omega

/-- The catalog split emits an encoded pair, or an empty failure result. -/
private def satSplit (z : List Bool) : List Bool :=
  match solveSplit 1 1 z.length with
  | some i => pairEncode (z.take i) (z.drop i)
  | none => []

/-- Instance and certificate projections are guarded independently of their
empty-word defaults. -/
private def satInstance (z : List Bool) : List Bool :=
  ((pairDecode (satSplit z)).map Prod.fst).getD []

/-- The recovered certificate region. -/
private def satWitness (z : List Bool) : List Bool :=
  ((pairDecode (satSplit z)).map Prod.snd).getD []

/-- Exact split success; in particular this is false at every even length. -/
private def satSplitValid (z : List Bool) : Bool := (pairDecode (satSplit z)).isSome

/-- Full syntax validation runs only after successful split recovery. -/
private def satGood (z : List Bool) : Bool := satSplitValid z && satSyntax (satInstance z)

/-- Safe evaluator input: malformed formulas are replaced by the empty formula
before the evaluator runs. Thus no semantic rejection can precede validation. -/
private def satSafe (z : List Bool) : List Bool :=
  if satGood z then satSplit z else pairEncode (CNF.serialize []) []

/-- Evaluation result after the syntax pass; the fallback evaluates to true. -/
private def satSafeValue (z : List Bool) : Bool :=
  if satGood z then (CNF.decode (satInstance z)).eval (satAssignment (satWitness z)) else true

/-- Every actual literal lies below the existing formula variable bound.
This only exposes the defining maximum; finite-assignment evaluation uses the
already proved `eval_congr_of_lt_numVars`. -/
private lemma sat_literal_lt_numVars (φ : CNF ℕ) (C : CNF.Clause ℕ)
    (ℓ : Std.Sat.Literal ℕ) (hC : C ∈ φ) (hℓ : ℓ ∈ C) : ℓ.1 < φ.numVars := by
  apply Nat.lt_of_succ_le
  exact List.le_max_of_le
    (List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨ℓ, hℓ, rfl⟩⟩) (Nat.le_refl _)

/-- Every safe request is a serialized formula with a covering certificate.
The conclusion holds also on failed splits and failed parses.

**Proof sketch.** A successful split gives an odd length and a witness longer than every decoded variable
index. Successful syntax reconstructs the serialization. In either failed-guard case,
the safe pair contains the empty formula, whose evaluation is true. -/
private lemma satSafe_spec (z : List Bool) :
    ∃ (φ : CNF ℕ) (u : List Bool), satSafe z = pairEncode (CNF.serialize φ) u ∧
      (∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < u.length) ∧
      φ.eval (satAssignment u) = satSafeValue z := by
  by_cases hg : satGood z = true
  · cases hs : solveSplit 1 1 z.length with
    | none => simp [satGood, satSplitValid, satSplit, hs, pairDecode] at hg
    | some i =>
      have hsyntax : (CNF.parse (z.take i)).isSome = true := by
        simpa [satGood, satSplitValid, satInstance, satSplit, hs,
          pairDecode_pairEncode, satSyntax_spec] using hg
      cases hp : CNF.parse (z.take i) with
      | none => simp [hp] at hsyntax
      | some φ =>
        have hdecode : CNF.decode (z.take i) = φ := by simp [CNF.decode, hp]
        have hi := sat_split_some z.length i hs
        have hlen : (z.drop i).length = (z.take i).length + 1 := by
          simp only [List.length_drop, List.length_take]; omega
        have hvars : φ.numVars ≤ (z.take i).length := by
          rw [← hdecode]; exact CNF.numVars_decode_le _
        refine ⟨φ, z.drop i, ?_, ?_, ?_⟩
        · simp only [satSafe, hg, ↓reduceIte, satSplit, hs, sat_parse_repr hp]
        · intro C hC ℓ hℓ
          have hv := sat_literal_lt_numVars φ C ℓ hC hℓ
          omega
        · simp [satSafeValue, hg, satInstance, satWitness, satSplit, hs,
            pairDecode_pairEncode, hdecode]
  · refine ⟨[], [], ?_, ?_, ?_⟩
    · simp [satSafe, hg]
    · simp
    · simp [satSafeValue, hg]

/-- Split recovery, projection, grammar validation, and safe request assembly
are all realized by the audited catalog and the complete syntax scanner. -/
private lemma sat_pipeline_poly :
    PolyTimeComputable (fun z => [satSplitValid z]) ∧
    PolyTimeComputable satInstance ∧
    PolyTimeComputable (fun z => [satSyntax (satInstance z)]) ∧
    PolyTimeComputable satSafe := by
  obtain ⟨M, A, hM⟩ := FinTM.computesFunInTime_splitSolve 1 1
  have hs : PolyTimeComputable satSplit := ⟨M, A, 3, hM⟩
  have hv : PolyTimeComputable (fun z => [satSplitValid z]) :=
    (polyTimeComputable_of_linear FinTM.computesFunInTime_pairValid).comp hs
  have hx : PolyTimeComputable satInstance :=
    (polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst).comp hs
  have hp : PolyTimeComputable (fun z => [satSyntax (satInstance z)]) := satSyntax_poly.comp hx
  exact ⟨hv, hx, hp, polyTimeComputable_ite (polyTimeComputable_and hv hp) hs (polyTimeComputable_const _)⟩

/-- The evaluator is polynomial on all safe requests.

**Proof sketch.** Use the evaluator only on the serialized inputs certified by
`satSafe_spec`. The request emitter's own output bound majorizes their lengths;
the original-input composition contract preserves the budget's argument. -/
private lemma satSafeValue_poly : PolyTimeComputable (fun z => [satSafeValue z]) := by
  obtain ⟨E, A, hE⟩ := satEval_computes
  obtain ⟨M, C, e, hM⟩ := sat_pipeline_poly.2.2.2
  have heval (z : List Bool) : E.ComputesInTime (satSafe z) [satSafeValue z]
      (A * (C * (z.length + 1) ^ e + 1)) := by
    obtain ⟨φ, u, hrequest, hvars, hvalue⟩ := satSafe_spec z
    have h := hE φ u hvars
    rw [← hrequest, hvalue] at h
    have hlen : (satSafe z).length ≤ C * (z.length + 1) ^ e := by
      have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hM z)).2
      simpa only [hout] using M.tm.output_length_le z (C * (z.length + 1) ^ e)
    exact h.mono (Nat.mul_le_mul_left A (by omega))
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M E satSafe (fun z => [satSafeValue z])
    (fun n => C * (n + 1) ^ e) (fun n => A * (C * (n + 1) ^ e + 1)) hM heval
  refine ⟨N, 2 * C + A * (C + 1) + 2, e, fun z => (hN z).mono ?_⟩
  have hp : 1 ≤ (z.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have ha : A ≤ A * (z.length + 1) ^ e := by
    simpa using Nat.mul_le_mul_left A hp
  dsimp only
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  omega

/-- The SAT verifier rejects failed splits and otherwise uses the safe
evaluation pipeline. Failed parses take its accepting fallback branch. -/
private lemma satVerdict_false_poly : PolyTimeComputable (fun z => [satVerdict false z]) := by
  have h := polyTimeComputable_ite sat_pipeline_poly.1 satSafeValue_poly (polyTimeComputable_const [false])
  convert h using 1
  funext z
  cases hs : solveSplit 1 1 z.length with
  | none => simp [satVerdict, satSplitValid, satSplit, hs, pairDecode]
  | some i =>
    cases hp : CNF.parse (z.take i) <;>
      simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode,
        satSafeValue, satGood, satInstance, satWitness, satSyntax_spec, hp, CNF.decode, CNF.fallback]

/-- A computed singleton Boolean verdict decides its verifier language. -/
private lemma satVerifier_of_poly (three : Bool)
    (h : PolyTimeComputable (fun z => [satVerdict three z])) : satVerifier three ∈ P := by
  obtain ⟨M, C, e, hM⟩ := h
  apply mem_P_iff.mpr
  refine ⟨C, e, M, fun z => ?_⟩
  have ho : [satVerdict three z] =
      [MultiTapeTM.indicator (satVerifier three : Set (List Bool)) z] := by
    simp [satVerifier, MultiTapeTM.indicator]
  simpa only [ho] using hM z

/-- **`SAT ∈ NP`** [AB09, Theorem 2.10, membership]: the satisfying assignment
is the certificate.

**Proof sketch.** Certificate parameters `(C, c) = (1, 1)`: length exactly
`(n + 1)` bits. A certificate `u` encodes the assignment `a_u = fun v => u.getD v
false`; by `Std.Sat.CNF.numVars_decode_le` the decoded formula mentions only
variables `< n`, and `Complexity.eval_congr_of_lt_numVars` makes the first
`numVars` bits decisive — so `x` is satisfiable iff some length-`(n+1)`
certificate `u` makes `(CNF.decode x).eval a_u = true` (forward: truncate a
satisfying assignment to `n + 1` bits; backward: `a_u` itself). The verifier
language is `V = {x ++ u : |u| = |x| + 1 ∧ (CNF.decode x).eval a_u = true}`;
`V ∈ P` by a machine with the named fill obligations: (i) unique-split recovery
— on input `y` of length `m`, the split `n + (n + 1) = m` forces `m` odd and
`n = (m - 1) / 2`, **rejecting explicitly on even `m`** (the round-3 pattern of
`Complexity.mem_NP_iff_exists_length_le`); (ii) the **parsing machine** for the
LL(1) grammar of `Std.Sat.CNF.parse` (run-length counting over unary indices;
on parse failure continue with the fallback, i.e. accept — the empty formula
evaluates `true`); (iii) the **evaluation machine**: stream the clauses; for a
literal `(v, b)`, walk to position `v` of the certificate region (the unary
index makes the walk linear) and compare with `b`; a clause with no satisfied
literal rejects the formula, exhausting all clauses accepts; (iv) the verdict
`[true]`/`[false]` with buffered output (the standing isolation obligation).
Budget: polynomial in `m`; conclude with `Complexity.mem_P_of_dtime_le`, and
`SAT ∈ NP` with `(1, 1, V)`. -/
theorem SAT_mem_NP : SAT ∈ NP := by
  refine ⟨1, 1, satVerifier false, satVerifier_of_poly false satVerdict_false_poly, ?_⟩
  intro x
  simpa only [Nat.pow_one, Nat.one_mul] using sat_verifier_equiv x

/-- Width scanning stores a saturated counter in finite control. -/
private def satWidthCap (n : ℕ) : Fin 4 := ⟨min n 3, by omega⟩

/-- A separate width pass, run only after the complete syntax pass. The
fourth literal clears the flag; scanning continues without emitting. -/
private def satWidthStep (s : Fin 6 × Fin 4 × Bool) (b : Bool) : Fin 6 × Fin 4 × Bool :=
  let (q, c, good) := s
  match q.val with
  | 0 => (satSyntaxStep q b, 0, good)
  | 1 => if b then (2, satWidthCap (c.val + 1), good && decide (c.val < 3))
      else (0, 0, good)
  | _ => (satSyntaxStep q b, c, good)

/-- Unary index bits do not increment the literal counter. -/
private lemma satWidth_index (n : ℕ) (c : Fin 4) (good : Bool) :
    (List.replicate n true).foldl satWidthStep (2, c, good) = (2, c, good) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, satWidthStep, satSyntaxStep] using ih

/-- A complete literal increments the width counter exactly once, independently
of its variable index and polarity. -/
private lemma satWidth_literal (ℓ : Std.Sat.Literal ℕ) (c : Fin 4) (good : Bool) :
    (CNF.serializeLit ℓ).foldl satWidthStep (1, c, good) =
      (1, satWidthCap (c.val + 1), good && decide (c.val < 3)) := by
  simp only [CNF.serializeLit, List.replicate_succ, List.cons_append, List.foldl_cons]
  change (List.replicate ℓ.1 true ++ [false, ℓ.2]).foldl satWidthStep
    (2, satWidthCap (c.val + 1), good && decide (c.val < 3)) = _
  rw [List.foldl_append, satWidth_index]
  rfl

/-- The separate width pass counts literal occurrences, including repetitions.

**Proof sketch.** Induct on literals. Saturation at three plus a persistent
overflow flag is equivalent to the exact inequality for the total width.
The clause terminator resets the counter without resetting the flag. -/
private lemma satWidth_clause (C : CNF.Clause ℕ) (c : Fin 4) (good : Bool) :
    (CNF.serializeClause C).foldl satWidthStep (1, c, good) =
      (0, 0, good && decide (c.val + C.length ≤ 3)) := by
  induction C generalizing c good with
  | nil =>
    have hc : c.val ≤ 3 := by omega
    simp [CNF.serializeClause, satWidthStep, hc]
  | cons ℓ C ih =>
    have hs : CNF.serializeClause (ℓ :: C) = CNF.serializeLit ℓ ++ CNF.serializeClause C := by
      simp [CNF.serializeClause, List.append_assoc]
    rw [hs, List.foldl_append, satWidth_literal, ih]
    have he : (decide (c.val < 3) && decide ((satWidthCap (c.val + 1)).val + C.length ≤ 3)) =
        decide (c.val + (ℓ :: C).length ≤ 3) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq, satWidthCap, List.length_cons]
      have hc := c.isLt
      omega
    rw [Bool.and_assoc, he]

/-- Every clause is checked; the empty formula passes vacuously. -/
private lemma satWidth_formula (φ : CNF ℕ) (good : Bool) :
    (CNF.serialize φ).foldl satWidthStep (0, 0, good) = (4, 0, good && satWidth φ) := by
  induction φ generalizing good with
  | nil => simp [CNF.serialize, satWidthStep, satSyntaxStep, satWidth]
  | cons C φ ih =>
    have hs : CNF.serialize (C :: φ) = true :: (CNF.serializeClause C ++ CNF.serialize φ) := by
      simp [CNF.serialize, List.append_assoc]
    rw [hs, List.foldl_cons]
    change (CNF.serializeClause C ++ CNF.serialize φ).foldl satWidthStep (1, 0, good) = _
    rw [List.foldl_append, satWidth_clause, ih]
    simp [satWidth, Bool.and_assoc]

/-- The final flag of the independent width pass. -/
private def satWidthScan (x : List Bool) : Bool := (x.foldl satWidthStep (0, 0, true)).2.2

/-- On valid syntax the scan computes exactly the width predicate. -/
private lemma satWidthScan_serialize (φ : CNF ℕ) : satWidthScan (CNF.serialize φ) = satWidth φ := by
  simp [satWidthScan, satWidth_formula]

/-- The width pass is a real finite machine, with no work tapes and `n+1` time. -/
private lemma satWidthScan_poly : PolyTimeComputable (fun x => [satWidthScan x]) := by
  refine ⟨satScanTM satWidthStep (0, 0, true) (fun s => s.2.2), 1, 1, ?_⟩
  simpa only [Nat.pow_one, Nat.one_mul, satWidthScan] using
    satScan_computes satWidthStep (0, 0, true) (fun s => s.2.2)

/-- The 3SAT machine validates the entire syntax before running the width pass,
and runs the evaluation pass only after width success.

**Proof sketch.** Compose the split validity, complete syntax, width, and evaluation machines through
nested conditionals. Split failure rejects; syntax failure accepts the empty fallback;
only successfully parsed inputs reach the width scan. -/
private lemma satVerdict_true_poly : PolyTimeComputable (fun z => [satVerdict true z]) := by
  have hw : PolyTimeComputable (fun z => [satWidthScan (satInstance z)]) :=
    satWidthScan_poly.comp sat_pipeline_poly.2.1
  have hsem := polyTimeComputable_and hw satSafeValue_poly
  have hparse := polyTimeComputable_ite sat_pipeline_poly.2.2.1 hsem (polyTimeComputable_const [true])
  have h := polyTimeComputable_ite sat_pipeline_poly.1 hparse (polyTimeComputable_const [false])
  convert h using 1
  funext z
  cases hs : solveSplit 1 1 z.length with
  | none => simp [satVerdict, satSplitValid, satSplit, hs, pairDecode]
  | some i =>
    cases hp : CNF.parse (z.take i) with
    | none =>
      simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode,
        satSafeValue, satGood, satInstance, satWitness, satSyntax_spec, hp,
        CNF.decode, CNF.fallback, satWidth]
    | some φ =>
      have hx := sat_parse_repr hp
      simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode,
        satSafeValue, satGood, satInstance, satWitness, satSyntax_spec, hx,
        CNF.parse_serialize, CNF.decode_serialize, satWidthScan_serialize]

/-- **`3SAT ∈ NP`** [AB09, Theorem 2.10, membership].

**Proof sketch.** The `Complexity.SAT_mem_NP` verifier with one more pass:
after parsing, additionally scan each clause counting literals to at most
three, rejecting a wider clause (so the verifier decides membership of the
decoded formula in the 3CNF fragment before evaluating). The fallback formula
has no clauses and passes the width check, keeping non-well-formed strings on
the member side, as `Complexity.SAT3` requires. Same parameters `(1, 1)`, same
budget shape. -/
theorem SAT3_mem_NP : SAT3 ∈ NP := by
  refine ⟨1, 1, satVerifier true, satVerifier_of_poly true satVerdict_true_poly, ?_⟩
  intro x
  simpa only [Nat.pow_one, Nat.one_mul] using sat3_verifier_equiv x

/-- Clause evaluation is unchanged when every occurring variable agrees. -/
private lemma satClause_congr (C : CNF.Clause ℕ) (a b : ℕ → Bool)
    (h : ∀ ℓ ∈ C, a ℓ.1 = b ℓ.1) : CNF.Clause.eval a C = CNF.Clause.eval b C := by
  apply CNF.Clause.eval_congr
  intro v hv
  rcases hv with hv | hv
  · exact h (v, false) hv
  · exact h (v, true) hv

/-- Split a nonempty clause into the audited chain, threading the first unused
variable. Each recursive call drops one original literal from the tail.
[AB09, §2.3.5, proof of Lemma 2.14] -/
private def satChain (head : Std.Sat.Literal ℕ) : CNF.Clause ℕ → ℕ → CNF ℕ × ℕ
  | b :: c :: d :: rest, n =>
      let next := satChain (n, false) (c :: d :: rest) (n + 1)
      ([head, b, (n, true)] :: next.1, next.2)
  | rest, n => ([head :: rest], n)

/-- Clause splitting preserves the empty clause, which must remain false. -/
private def satSplitClause (C : CNF.Clause ℕ) (n : ℕ) : CNF ℕ × ℕ :=
  match C with
  | [] => ([[]], n)
  | head :: rest => satChain head rest n

/-- The allocator never moves backwards. -/
private lemma satChain_cursor (head : Std.Sat.Literal ℕ) (rest : CNF.Clause ℕ) (n : ℕ) :
    n ≤ (satChain head rest n).2 := by
  induction rest generalizing head n with
  | nil => exact Nat.le_refl _
  | cons b rest ih =>
    cases rest with
    | nil => exact Nat.le_refl _
    | cons c rest =>
      cases rest with
      | nil => exact Nat.le_refl _
      | cons d rest => exact Nat.le_trans (Nat.le_succ n) (ih (n, false) (n + 1))

/-- Every emitted chain clause has at most three literals. -/
private lemma satChain_width (head : Std.Sat.Literal ℕ) (rest : CNF.Clause ℕ) (n : ℕ) :
    (satChain head rest n).1.WidthAtMost 3 := by
  induction rest generalizing head n with
  | nil => simp [satChain, CNF.WidthAtMost]
  | cons b rest ih =>
    cases rest with
    | nil => simp [satChain, CNF.WidthAtMost]
    | cons c rest =>
      cases rest with
      | nil => simp [satChain, CNF.WidthAtMost]
      | cons d rest =>
        have ht := ih (n, false) (n + 1)
        simpa only [satChain, CNF.WidthAtMost, List.mem_cons, List.length_cons,
          List.length_nil, forall_eq_or_imp, Nat.reduceAdd, Nat.le_refl, true_and] using ht

/-- Projecting a satisfying chain assignment satisfies the original clause.
No freshness hypothesis is needed in this direction.

**Proof sketch.** Induct on the splitting. If neither first literal is true,
the first link forces its fresh positive literal, so the recursively satisfied
tail must be satisfied by an original literal rather than the fresh negation. -/
private lemma satChain_sound (head : Std.Sat.Literal ℕ) (rest : CNF.Clause ℕ) (n : ℕ)
    (a : ℕ → Bool) (h : (satChain head rest n).1.eval a = true) :
    CNF.Clause.eval a (head :: rest) = true := by
  induction rest generalizing head n with
  | nil => simpa [satChain] using h
  | cons b rest ih =>
    cases rest with
    | nil => simpa [satChain] using h
    | cons c rest =>
      cases rest with
      | nil => simpa [satChain] using h
      | cons d rest =>
        have hh : CNF.Clause.eval a [head, b, (n, true)] = true ∧
            (satChain (n, false) (c :: d :: rest) (n + 1)).1.eval a = true := by
          simpa only [satChain, CNF.eval_cons, Bool.and_eq_true] using h
        have ht := ih (n, false) (n + 1) hh.2
        have hfirst := hh.1
        clear h hh ih
        cases hn : a n <;> simp_all [CNF.Clause.eval_cons, CNF.Clause.eval_nil] <;> aesop

/-- One splitting step extends the assignment at precisely the fresh index.
Its value is the truth of the remaining tail, as in the audited sketch.

**Proof sketch.** Update the fresh index to the tail clause truth value. All original literals have
smaller indices and keep their values. Case analysis on the tail value proves both
emitted clauses. -/
private lemma satChain_extend_step (head b : Std.Sat.Literal ℕ) (tail : CNF.Clause ℕ)
    (n : ℕ) (a : ℕ → Bool) (hvars : ∀ ℓ ∈ head :: b :: tail, ℓ.1 < n)
    (hsat : CNF.Clause.eval a (head :: b :: tail) = true) :
    ∃ a' : ℕ → Bool, (∀ v < n, a' v = a v) ∧
      CNF.Clause.eval a' [head, b, (n, true)] = true ∧
      CNF.Clause.eval a' ((n, false) :: tail) = true := by
  let a' := Function.update a n (CNF.Clause.eval a tail)
  have hfix : ∀ v < n, a' v = a v := by
    intro v hv
    exact Function.update_of_ne (by omega : v ≠ n) _ _
  have hhead := hfix head.1 (hvars head (by simp))
  have hb := hfix b.1 (hvars b (by simp))
  have hn : a' n = CNF.Clause.eval a tail := by simp [a']
  have htail : CNF.Clause.eval a' tail = CNF.Clause.eval a tail := by
    apply satClause_congr
    intro ℓ hℓ
    exact hfix ℓ.1 (hvars ℓ (by simp [hℓ]))
  refine ⟨a', hfix, ?_, ?_⟩
  · simpa [CNF.Clause.eval_cons, CNF.Clause.eval_nil, hhead, hb, hn] using hsat
  · simp only [CNF.Clause.eval_cons, hn, htail]
    cases CNF.Clause.eval a tail <;> rfl

/-- A satisfying original clause extends to a satisfying chain assignment,
with every previously allocated variable preserved.

**Proof sketch.** Set the next fresh variable to the tail's truth value. Apply
induction to the clause beginning with its negation, with the cursor increased
by one. That extension preserves the three variables in the emitted link. -/
private lemma satChain_complete (head : Std.Sat.Literal ℕ) (rest : CNF.Clause ℕ) (n : ℕ)
    (a : ℕ → Bool) (hvars : ∀ ℓ ∈ head :: rest, ℓ.1 < n)
    (hsat : CNF.Clause.eval a (head :: rest) = true) :
    ∃ a' : ℕ → Bool, (∀ v < n, a' v = a v) ∧ (satChain head rest n).1.eval a' = true := by
  induction rest generalizing head n a with
  | nil => exact ⟨a, fun _ _ => rfl, by simpa [satChain] using hsat⟩
  | cons b rest ih =>
    cases rest with
    | nil => exact ⟨a, fun _ _ => rfl, by simpa [satChain] using hsat⟩
    | cons c rest =>
      cases rest with
      | nil => exact ⟨a, fun _ _ => rfl, by simpa [satChain] using hsat⟩
      | cons d rest =>
        obtain ⟨a₁, hfix, hfirst, htail⟩ := satChain_extend_step head b (c :: d :: rest) n a hvars hsat
        have hnext : ∀ ℓ ∈ (n, false) :: c :: d :: rest, ℓ.1 < n + 1 := by
          intro ℓ hℓ
          rcases List.mem_cons.mp hℓ with rfl | hℓ
          · simp
          · have hv := hvars ℓ (List.mem_cons_of_mem head (List.mem_cons_of_mem b hℓ))
            omega
        obtain ⟨a₂, hfix₂, hsat₂⟩ := ih (n, false) (n + 1) a₁ hnext htail
        refine ⟨a₂, fun v hv => (hfix₂ v (by omega)).trans (hfix v hv), ?_⟩
        have heq : CNF.Clause.eval a₂ [head, b, (n, true)] =
            CNF.Clause.eval a₁ [head, b, (n, true)] := by
          apply satClause_congr
          intro ℓ hℓ
          apply hfix₂
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
          have hhead := hvars head (by simp)
          have hb := hvars b (by simp)
          rcases hℓ with rfl | rfl | rfl <;> (try dsimp only) <;> omega
        simp only [satChain, CNF.eval_cons, heq, hfirst, hsat₂, Bool.true_and]

/-- Every variable in the chain is below its returned fresh-variable cursor.

**Proof sketch.** Induct on the remaining literals. Each new link uses only two original indices and the
current fresh index; the recursive cursor is at least its starting value, so all are
below the returned cursor. -/
private lemma satChain_vars (head : Std.Sat.Literal ℕ) (rest : CNF.Clause ℕ) (n : ℕ)
    (hvars : ∀ ℓ ∈ head :: rest, ℓ.1 < n) :
    ∀ D ∈ (satChain head rest n).1, ∀ ℓ ∈ D, ℓ.1 < (satChain head rest n).2 := by
  induction rest generalizing head n with
  | nil => simpa only [satChain, List.mem_singleton, forall_eq] using hvars
  | cons b rest ih =>
    cases rest with
    | nil => simpa only [satChain, List.mem_singleton, forall_eq] using hvars
    | cons c rest =>
      cases rest with
      | nil => simpa only [satChain, List.mem_singleton, forall_eq] using hvars
      | cons d rest =>
        have hnext : ∀ ℓ ∈ (n, false) :: c :: d :: rest, ℓ.1 < n + 1 := by
          intro ℓ hℓ
          rcases List.mem_cons.mp hℓ with rfl | hℓ
          · simp
          · have hv := hvars ℓ (List.mem_cons_of_mem head (List.mem_cons_of_mem b hℓ)); omega
        have hr := ih (n, false) (n + 1) hnext
        have hn := satChain_cursor (n, false) (c :: d :: rest) (n + 1)
        intro D hD ℓ hℓ
        simp only [satChain, List.mem_cons] at hD
        rcases hD with rfl | hD
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
          have hhead := hvars head (by simp)
          have hb := hvars b (by simp)
          rcases hℓ with rfl | rfl | rfl <;> dsimp only [satChain] <;> omega
        · exact hr D hD ℓ hℓ

/-- The clause allocator is monotone, also on the empty clause. -/
private lemma satSplitClause_cursor (C : CNF.Clause ℕ) (n : ℕ) :
    n ≤ (satSplitClause C n).2 := by
  cases C with
  | nil => exact Nat.le_refl _
  | cons head rest => exact satChain_cursor head rest n

/-- Splitting a clause always produces 3CNF. -/
private lemma satSplitClause_width (C : CNF.Clause ℕ) (n : ℕ) :
    (satSplitClause C n).1.WidthAtMost 3 := by
  cases C with
  | nil => simp [satSplitClause, CNF.WidthAtMost]
  | cons head rest => exact satChain_width head rest n

/-- The returned cursor bounds all output variables of a split clause. -/
private lemma satSplitClause_vars (C : CNF.Clause ℕ) (n : ℕ)
    (hvars : ∀ ℓ ∈ C, ℓ.1 < n) :
    ∀ D ∈ (satSplitClause C n).1, ∀ ℓ ∈ D, ℓ.1 < (satSplitClause C n).2 := by
  cases C with
  | nil => simp [satSplitClause]
  | cons head rest => exact satChain_vars head rest n hvars

/-- Every satisfying output assignment satisfies the original clause. -/
private lemma satSplitClause_sound (C : CNF.Clause ℕ) (n : ℕ) (a : ℕ → Bool)
    (h : (satSplitClause C n).1.eval a = true) : CNF.Clause.eval a C = true := by
  cases C with
  | nil => simpa [satSplitClause] using h
  | cons head rest => exact satChain_sound head rest n a h

/-- Every satisfying clause assignment extends while preserving earlier indices. -/
private lemma satSplitClause_complete (C : CNF.Clause ℕ) (n : ℕ) (a : ℕ → Bool)
    (hvars : ∀ ℓ ∈ C, ℓ.1 < n) (hsat : CNF.Clause.eval a C = true) :
    ∃ a', (∀ v < n, a' v = a v) ∧ (satSplitClause C n).1.eval a' = true := by
  cases C with
  | nil => simp at hsat
  | cons head rest => exact satChain_complete head rest n a hvars hsat

/-- Transform clauses in order, threading one global fresh-variable cursor.
[AB09, §2.3.5, proof of Lemma 2.14] -/
private def satTransformFrom : CNF ℕ → ℕ → CNF ℕ × ℕ
  | [], n => ([], n)
  | C :: φ, n =>
      let first := satSplitClause C n
      let tail := satTransformFrom φ first.2
      (first.1 ++ tail.1, tail.2)

/-- A literal-wise bound gives the existing maximum-based variable bound. -/
private lemma sat_numVars_le (φ : CNF ℕ) (n : ℕ)
    (hvars : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < n) : φ.numVars ≤ n := by
  apply List.max_le_of_forall_le
  intro v hv
  obtain ⟨C, hC, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hv
  exact Nat.succ_le_of_lt (hvars C hC ℓ hℓ)

/-- The formula transform is always in the 3CNF fragment. -/
private lemma satTransformFrom_width (φ : CNF ℕ) (n : ℕ) :
    (satTransformFrom φ n).1.WidthAtMost 3 := by
  induction φ generalizing n with
  | nil => simp [satTransformFrom, CNF.WidthAtMost]
  | cons C φ ih =>
    intro D hD
    rcases List.mem_append.mp hD with hD | hD
    · exact satSplitClause_width C n D hD
    · exact ih (satSplitClause C n).2 D hD

/-- Soundness composes across all clause chains with the same assignment. -/
private lemma satTransformFrom_sound (φ : CNF ℕ) (n : ℕ) (a : ℕ → Bool)
    (h : (satTransformFrom φ n).1.eval a = true) : φ.eval a = true := by
  induction φ generalizing n with
  | nil => rfl
  | cons C φ ih =>
    have hh : (satSplitClause C n).1.eval a = true ∧
        (satTransformFrom φ (satSplitClause C n).2).1.eval a = true := by
      simpa only [satTransformFrom, CNF.eval_append, Bool.and_eq_true] using h
    exact Bool.and_eq_true_iff.mpr ⟨satSplitClause_sound C n a hh.1, ih _ hh.2⟩

/-- Completeness threads extensions through the globally fresh cursor.

**Proof sketch.** Extend over the first clause, then over the remaining
formula. The second extension preserves the first chain because all its
variables lie below its returned cursor. Both preservation steps use the
existing `eval_congr_of_lt_numVars` theorem. -/
private lemma satTransformFrom_complete (φ : CNF ℕ) (n : ℕ) (a : ℕ → Bool)
    (hvars : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < n) (hsat : φ.eval a = true) :
    ∃ a', (∀ v < n, a' v = a v) ∧ (satTransformFrom φ n).1.eval a' = true := by
  induction φ generalizing n a with
  | nil => exact ⟨a, fun _ _ => rfl, rfl⟩
  | cons C φ ih =>
    have hh := Bool.and_eq_true_iff.mp hsat
    have hcvars : ∀ ℓ ∈ C, ℓ.1 < n := hvars C List.mem_cons_self
    have htvars : ∀ D ∈ φ, ∀ ℓ ∈ D, ℓ.1 < n :=
      fun D hD => hvars D (List.mem_cons_of_mem C hD)
    obtain ⟨a₁, hfix, hfirst⟩ := satSplitClause_complete C n a hcvars hh.1
    have hn := satSplitClause_cursor C n
    have htail : CNF.eval a₁ φ = true := by
      rw [eval_congr_of_lt_numVars (a := a₁) (b := a)
        (fun v hv => hfix v (Nat.lt_of_lt_of_le hv (sat_numVars_le φ n htvars)))]
      exact hh.2
    obtain ⟨a₂, hfix₂, hrest⟩ := ih (satSplitClause C n).2 a₁
      (fun D hD ℓ hℓ => Nat.lt_of_lt_of_le (htvars D hD ℓ hℓ) hn) htail
    refine ⟨a₂, fun v hv => (hfix₂ v (Nat.lt_of_lt_of_le hv hn)).trans (hfix v hv), ?_⟩
    have hfirst₂ : (satSplitClause C n).1.eval a₂ = true := by
      rw [eval_congr_of_lt_numVars (a := a₂) (b := a₁)
        (fun v hv => hfix₂ v (Nat.lt_of_lt_of_le hv
          (sat_numVars_le _ _ (satSplitClause_vars C n hcvars))))]
      exact hfirst
    simp only [satTransformFrom, CNF.eval_append, hfirst₂, hrest, Bool.true_and]

/-- The clause transform starts allocating at precisely `numVars`, as required
by the audited reduction sketch. -/
private def satTransform (φ : CNF ℕ) : CNF ℕ := (satTransformFrom φ φ.numVars).1

/-- Equisatisfiability of the formula-level transform, in both directions.
[AB09, Lemma 2.14] -/
private lemma satTransform_equisat (φ : CNF ℕ) : (satTransform φ).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, satTransformFrom_sound φ φ.numVars a ha⟩
  · rintro ⟨a, ha⟩
    obtain ⟨a', _, h⟩ := satTransformFrom_complete φ φ.numVars a
      (fun C hC ℓ hℓ => sat_literal_lt_numVars φ C ℓ hC hℓ) ha
    exact ⟨a', h⟩

/-- The full string-level reduction, including the prescribed malformed-input
fallback. [AB09, Lemma 2.14] -/
private def satReduction (x : List Bool) : List Bool := CNF.serialize (satTransform (CNF.decode x))

/-- Reduction correctness is quantified over every string, without a
well-formedness hypothesis. The empty fallback is fixed by the transform. -/
private lemma satReduction_correct (x : List Bool) : x ∈ SAT ↔ satReduction x ∈ SAT3 := by
  change (CNF.decode x).Satisfiable ↔
    (CNF.decode (satReduction x)).WidthAtMost 3 ∧ (CNF.decode (satReduction x)).Satisfiable
  rw [satReduction, CNF.decode_serialize, satTransform_equisat]
  exact (and_iff_right (satTransformFrom_width (CNF.decode x) (CNF.decode x).numVars)).symm

/-- Failed parsing maps to the serialization of the unchanged empty formula. -/
private lemma satReduction_fallback (x : List Bool) (h : CNF.parse x = none) :
    satReduction x = CNF.serialize [] := by
  simp [satReduction, CNF.decode, h, CNF.fallback, satTransform, satTransformFrom]

/-- Every clause's serialization has room for all its literal occurrences. -/
private lemma sat_clause_measure (C : CNF.Clause ℕ) : C.length + 1 ≤ (CNF.serializeClause C).length := by
  induction C with
  | nil => simp [CNF.serializeClause]
  | cons ℓ C ih => simp [CNF.serializeClause, CNF.serializeLit] at *; omega

/-- Two-tape actions for the reduction: the first tape is a unary fresh
cursor, the second a temporary literal buffer. -/
private def satRedAction (m : SignType) (w₀ w₁ : Option (Option Bool))
    (d₀ d₁ : SignType) (out : Option Bool) (q : Option (Fin 35)) :
    Action 2 Bool (Fin 35) :=
  ⟨m, fun i => if i = 0 then (w₀, d₀) else (w₁, d₁), out, q⟩

/-- A candidate clause-splitting transducer on previously validated CNF words.
States 2--6 compute the maximum unary literal length silently. States 7--8
rewind the native input; states 9--34 are the proposed streaming serializer.
The buffer's permanent left marker is installed by states 0--1.

**Partial-delivery frontier.** `satRed_start` verifies initialization, the
maximum pass, and rewind. The streaming states still need their correctness
and time proofs; this definition is not a `PolyTimeComputable` witness. -/
private def satRedTM : FinTM Bool where
  k := 2
  State := Fin 35
  tm := {
    q₀ := 0
    tr := fun q inp work =>
      let a := satRedAction
      match q.val with
      | 0 => a 0 none none 0 .neg none (some 1)
      | 1 => a 0 none (some (some false)) 0 .pos none (some 2)
      | 2 => if inp = some true then a .pos none none 0 0 none (some 3)
        else a 0 none none 0 0 none (some 7)
      | 3 => if inp = some true then a .pos (some (some true)) none .pos 0 none (some 4)
        else a .pos none none 0 0 none (some 2)
      | 4 => if inp = some true then a .pos (some (some true)) none .pos 0 none (some 4)
        else a .pos none none .neg 0 none (some 6)
      | 5 => a .pos none none 0 0 none (some 3)
      | 6 => if (work 0).isSome then a 0 none none .neg 0 none (some 6)
        else a 0 none none .pos 0 none (some 5)
      | 7 => a .neg none none 0 0 none (some 8)
      | 8 => if inp.isSome then a .neg none none 0 0 none (some 8)
        else a .pos none none 0 0 none (some 9)
      | 9 => if inp = some true then a .pos none none 0 0 (some true) (some 10)
        else a 0 none none 0 0 (some false) none
      | 10 => if inp = some true then a .pos none none 0 0 (some true) (some 11)
        else a .pos none none 0 0 (some false) (some 9)
      | 11 => if inp = some true then a .pos none none 0 0 (some true) (some 11)
        else a .pos none none 0 0 (some false) (some 12)
      | 12 => a .pos none none 0 0 inp (some 13)
      | 13 => if inp = some true then a .pos none none 0 0 (some true) (some 14)
        else a .pos none none 0 0 (some false) (some 9)
      | 14 => if inp = some true then a .pos none none 0 0 (some true) (some 14)
        else a .pos none none 0 0 (some false) (some 15)
      | 15 => a .pos none none 0 0 inp (some 16)
      | 16 => if inp = some true then a .pos none (some (some true)) 0 .pos none (some 17)
        else a .pos none none 0 0 (some false) (some 9)
      | 17 => if inp = some true then a .pos none (some (some true)) 0 .pos none (some 17)
        else a .pos none (some (some false)) 0 .pos none (some 18)
      | 18 => a .pos none (some inp) 0 .neg none (some 19)
      | 19 => a 0 none none 0 .neg none (some 20)
      | 20 => if work 1 = some true then a 0 none none 0 .neg none (some 20)
        else a 0 none none 0 .pos none (some 21)
      | 21 => if inp = some true then a 0 none none 0 0 none (some 22)
        else a 0 none none 0 0 none (some 33)
      | 22 => if (work 0).isSome then a 0 none none .pos 0 (some true) (some 22)
        else a 0 none none 0 0 (some true) (some 23)
      | 23 => a 0 none none 0 0 (some false) (some 24)
      | 24 => a 0 none none 0 0 (some true) (some 25)
      | 25 => a 0 none none 0 0 (some false) (some 26)
      | 26 => a 0 none none 0 0 (some true) (some 27)
      | 27 => a 0 none none .neg 0 none (some 28)
      | 28 => if (work 0).isSome then a 0 none none .neg 0 none (some 28)
        else a 0 none none .pos 0 none (some 29)
      | 29 => if (work 0).isSome then a 0 none none .pos 0 (some true) (some 29)
        else a 0 (some (some true)) none 0 0 (some true) (some 30)
      | 30 => a 0 none none 0 0 (some false) (some 31)
      | 31 => a 0 none none .neg 0 (some false) (some 32)
      | 32 => if (work 0).isSome then a 0 none none .neg 0 none (some 32)
        else a 0 none none .pos 0 none (some 33)
      | 33 => match work 1 with
        | some b => a 0 none (some none) 0 .pos (some b) (some 33)
        | none => a 0 none none 0 .neg none (some 34)
      | _ => if (work 1).isSome then a 0 none none 0 .pos none (some 16)
        else a 0 none none 0 .neg none (some 34) }

/-- Canonical unary counter tape; its length is the next unused variable. -/
private def satRedCounter (n : ℕ) : ℤ → Option Bool := FinTM.bufferTape (List.replicate n true)

/-- Buffer cells before `cut` have been erased; the permanent marker at -1
allows return even after the payload has been completely erased. -/
private def satRedBuffer (word : List Bool) (cut : ℕ) (z : ℤ) : Option Bool :=
  if z = -1 then some false else if (cut : ℤ) ≤ z then FinTM.bufferTape word z else none

/-- A canonical frame exposes both tape heads and the accumulated output. -/
private def satRedCfg (x : List Bool) (q : Option (Fin 35)) (i : ℕ) (hi : i ≤ x.length)
    (n : ℕ) (buf : ℤ → Option Bool) (a b : ℤ) (out : List Bool) : Cfg 2 Bool (Fin 35) x :=
  ⟨q, ⟨i + 1, by omega⟩, (fun t => if t = 0 then satRedCounter n else buf),
    (fun t => if t = 0 then a else b), out⟩

/-- The canonical native input position reads the corresponding list cell. -/
private lemma satRedCfg_input (x : List Bool) (q : Option (Fin 35))
    (i : ℕ) (hi : i ≤ x.length) (n : ℕ) (buf : ℤ → Option Bool) (a b : ℤ) (out : List Bool) :
    (satRedCfg x q i hi n buf a b out).inputSymbol = x[i]? :=
  FinTM.inputSymbol_at _ i hi rfl

/-- The first tape's occupied cells are exactly its unary prefix. -/
private lemma satRedCounter_read (n j : ℕ) :
    satRedCounter n j = if j < n then some true else none := by
  simp [satRedCounter, FinTM.bufferTape_nat, List.getElem?_replicate]

/-- The counter's left boundary is blank. -/
private lemma satRedCounter_left (n : ℕ) : satRedCounter n (-1) = none := by
  simp [satRedCounter, FinTM.bufferTape_left]

/-- Writing within the current prefix preserves it; writing its right blank
extends the maximum by one. -/
private lemma satRedCounter_write (n j : ℕ) (hj : j ≤ n) :
    Function.update (satRedCounter n) (j : ℤ) (some true) = satRedCounter (max n (j + 1)) := by
  by_cases h : j < n
  · rw [max_eq_left (by omega)]
    exact Function.update_eq_self_iff.mpr (by simp [satRedCounter_read, h])
  · have he : j = n := by omega
    subst j
    simpa [satRedCounter, List.replicate_succ', max_eq_right (Nat.le_succ n)] using
      (FinTM.bufferTape_append (List.replicate n true) true).symm

/-- Frame-level action calculus keeps output append and both tape updates
explicit; it is shared by the maximum pass and the streaming serializer.

**Proof sketch.** Compare all five configuration fields. Split the two work-tape cases, substitute the
prescribed tape updates and integer head movements, and use the explicit output-append
equation. -/
private lemma satRedAction_apply (x : List Bool) (q q' : Option (Fin 35))
    (i i' : ℕ) (hi : i ≤ x.length) (hi' : i' ≤ x.length) (n n' : ℕ)
    (buf buf' : ℤ → Option Bool) (a b a' b' : ℤ) (out out' : List Bool)
    (m : SignType) (w₀ w₁ : Option (Option Bool)) (d₀ d₁ : SignType) (emit : Option Bool)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨i' + 1, by omega⟩)
    (h₀ : (match w₀ with
      | none => satRedCounter n
      | some c => Function.update (satRedCounter n) a c) = satRedCounter n')
    (h₁ : (match w₁ with | none => buf | some c => Function.update buf b c) = buf')
    (ha : a + d₀.cast = a') (hb : b + d₁.cast = b')
    (ho : out ++ emit.toList = out') :
    (satRedAction m w₀ w₁ d₀ d₁ emit q').apply (satRedCfg x q i hi n buf a b out) =
      satRedCfg x q' i' hi' n' buf' a' b' out' := by
  refine Cfg.ext rfl hm ?_ ?_ ho
  · funext t
    fin_cases t
    · cases w₀ <;> simpa [satRedAction, satRedCfg, Action.apply] using h₀
    · cases w₁ <;> simpa [satRedAction, satRedCfg, Action.apply] using h₁
  · funext t
    fin_cases t
    · simpa [satRedAction, satRedCfg, Action.apply] using ha
    · simpa [satRedAction, satRedCfg, Action.apply] using hb

/-- A silent transition with no writes changes only control and head positions. -/
private lemma satRed_move (x : List Bool) (q q' : Fin 35)
    (i i' : ℕ) (hi : i ≤ x.length) (hi' : i' ≤ x.length) (n : ℕ)
    (buf : ℤ → Option Bool) (a b a' b' : ℤ) (out : List Bool)
    (m d₀ d₁ : SignType)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨i' + 1, by omega⟩)
    (ha : a + d₀.cast = a') (hb : b + d₁.cast = b')
    (ht : satRedTM.tm.tr q (x[i]?) (fun t : Fin 2 => if t = 0 then satRedCounter n a else buf b) =
      satRedAction m none none d₀ d₁ none (some q')) :
    satRedTM.tm.step (satRedCfg x (some q) i hi n buf a b out) =
      satRedCfg x (some q') i' hi' n buf a' b' out := by
  unfold MultiTapeTM.step
  change (satRedTM.tm.tr q _ _).apply _ = _
  rw [satRedCfg_input]
  have hw : (satRedCfg x (some q) i hi n buf a b out).workTapeSymbols =
      (fun t => if t = 0 then satRedCounter n a else buf b) := by
    funext t
    fin_cases t <;> rfl
  rw [hw, ht]
  exact satRedAction_apply x (some q) (some q') i i' hi hi' n n buf buf a b a' b' out out
    m none none d₀ d₁ none hm rfl rfl ha hb (by simp)

/-- A single machine transition is the one-step run. -/
private lemma satRed_one {x : List Bool} (cfg : Cfg 2 Bool (Fin 35) x) :
    satRedTM.tm.runFrom cfg 1 = satRedTM.tm.step cfg := by
  rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

/-- Counter rewinds take exactly `r+1` silent transitions, including the
left blank, and apply to each of the three return phases.

**Proof sketch.** Induct on the distance to the left boundary. An occupied counter cell gives one silent
left move; at the blank cell -1, the final right move enters the return state at head
zero. -/
private lemma satRed_counterBack (x : List Bool) (q dest : Fin 35)
    (htr : ∀ (inp : Option Bool) (work : Fin 2 → Option Bool), satRedTM.tm.tr q inp work =
      if (work 0).isSome then satRedAction 0 none none .neg 0 none (some q)
      else satRedAction 0 none none .pos 0 none (some dest))
    (i : ℕ) (hi : i ≤ x.length) (n r : ℕ) (hr : r ≤ n)
    (buf : ℤ → Option Bool) (b : ℤ) (out : List Bool) :
    satRedTM.tm.runFrom (satRedCfg x (some q) i hi n buf ((r : ℤ) - 1) b out) (r + 1) =
      satRedCfg x (some dest) i hi n buf 0 b out := by
  induction r with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply satRed_move x q dest i i hi hi n buf (-1) b 0 b out 0 .pos 0
      (moveInputPos_zero _) (by simp) (by simp)
    rw [htr]
    simp [satRedCounter_left]
  | succ r ih =>
    have hs : satRedTM.tm.step
        (satRedCfg x (some q) i hi n buf (((r + 1 : ℕ) : ℤ) - 1) b out) =
        satRedCfg x (some q) i hi n buf ((r : ℤ) - 1) b out := by
      apply satRed_move x q q i i hi hi n buf _ b _ b out 0 .neg 0
        (moveInputPos_zero _) (by simp <;> omega) (by simp)
      rw [htr]
      have he : (((r + 1 : ℕ) : ℤ) - 1) = r := by omega
      simp [he, satRedCounter_read, show r < n by omega]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]

/-- The maximum pass consumes a unary run, extending precisely to the
maximum of the old prefix and the visited position.

**Proof sketch.** Induct on the unary run. Writing the next occupied cell or right blank changes the
counter length to the corresponding maximum. Compose the one-step update with the
shorter run and reassociate the maxima. -/
private lemma satRed_maxOnes (x : List Bool) (v : ℕ) :
    ∀ pre rest (hx : x = pre ++ List.replicate v true ++ rest)
      (n j : ℕ) (hj : j ≤ n) (buf : ℤ → Option Bool) (b : ℤ) (out : List Bool),
    satRedTM.tm.runFrom
      (satRedCfg x (some 4) pre.length (by simp [hx]) n buf j b out) v =
      satRedCfg x (some 4) (pre.length + v) (by simp [hx])
        (max n (j + v)) buf (j + v) b out := by
  induction v with
  | zero => intros; simp [MultiTapeTM.runFrom_zero, max_eq_left, *]
  | succ v ih =>
    intro pre rest hx n j hj buf b out
    have hx' : x = (pre ++ [true]) ++ List.replicate v true ++ rest := by
      simpa [List.replicate_succ, List.append_assoc] using hx
    have hs : satRedTM.tm.step
        (satRedCfg x (some 4) pre.length (by simp [hx]) n buf j b out) =
        satRedCfg x (some 4) (pre.length + 1) (by simp [hx'])
          (max n (j + 1)) buf (j + 1) b out := by
      unfold MultiTapeTM.step
      change (satRedTM.tm.tr (4 : Fin 35) _ _).apply _ = _
      rw [satRedCfg_input, show x[pre.length]? = some true by simp [hx', List.append_assoc]]
      change (satRedAction .pos (some (some true)) none .pos 0 none (some 4)).apply _ = _
      exact satRedAction_apply x (some 4) (some 4) _ _ _ _ n (max n (j + 1))
        buf buf j b (j + 1) b out out .pos (some (some true)) none .pos 0 none
        (moveInputPos_pos_of_ne_right _ (by simp [hx'] <;> omega))
        (satRedCounter_write n j hj) rfl (by simp) (by simp) (by simp)
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    have h := ih (pre ++ [true]) rest hx' (max n (j + 1)) (j + 1) (Nat.le_max_right _ _)
      buf b out
    have he : max (max n (j + 1)) (j + 1 + v) = max n (j + (v + 1)) := by omega
    simpa [he, Nat.add_assoc, add_assoc, add_comm, add_left_comm] using h

/-- One literal in the maximum pass takes `2v+5` transitions, records the
maximum of the prior bound and `v+1`, and restores the counter head.

**Proof sketch.** Consume the first unary bit, scan the remaining index bits, and consume the zero
separator. Rewind the counter before skipping polarity. The five phases cost one, v,
one, v+2, and one steps. -/
private lemma satRed_maxLiteral (x : List Bool) (v : ℕ) (pol : Bool)
    (pre rest : List Bool) (hx : x = pre ++ CNF.serializeLit (v, pol) ++ rest)
    (n : ℕ) (buf : ℤ → Option Bool) (b : ℤ) (out : List Bool) :
    satRedTM.tm.runFrom
      (satRedCfg x (some 3) pre.length (by simp [hx]) n buf 0 b out) (2 * v + 5) =
      satRedCfg x (some 3) (pre.length + (v + 3))
        (by simp [hx, CNF.serializeLit] <;> omega) (max n (v + 1)) buf 0 b out := by
  let p₁ := pre ++ [true]
  let p₂ := p₁ ++ List.replicate v true
  let p₃ := p₂ ++ [false]
  have hx₁ : x = p₁ ++ List.replicate v true ++ [false, pol] ++ rest := by
    simpa [p₁, CNF.serializeLit, List.replicate_succ, List.append_assoc] using hx
  have hx₂ : x = p₂ ++ [false, pol] ++ rest := hx₁
  have hx₃ : x = p₃ ++ [pol] ++ rest := by simpa [p₃, List.append_assoc] using hx₂
  have h₁ : satRedTM.tm.step
      (satRedCfg x (some 3) pre.length (by simp [hx]) n buf 0 b out) =
      satRedCfg x (some 4) p₁.length (by simp [hx₁]) (max n 1) buf 1 b out := by
    unfold MultiTapeTM.step
    change (satRedTM.tm.tr (3 : Fin 35) _ _).apply _ = _
    rw [satRedCfg_input, show x[pre.length]? = some true by simp [hx₁, p₁, List.append_assoc]]
    change (satRedAction .pos (some (some true)) none .pos 0 none (some 4)).apply _ = _
    exact satRedAction_apply x (some 3) (some 4) _ _ _ _ n (max n 1)
      buf buf 0 b 1 b out out .pos (some (some true)) none .pos 0 none
      (by
        simp only [p₁, List.length_append, List.length_singleton]
        exact moveInputPos_pos_of_ne_right _ (by simp [hx₁, p₁]))
      (satRedCounter_write n 0 (Nat.zero_le _)) rfl (by simp) (by simp) (by simp)
  have h₂ := satRed_maxOnes x v p₁ ([false, pol] ++ rest)
    (by simpa [List.append_assoc] using hx₁) (max n 1) 1 (Nat.le_max_right _ _) buf b out
  have he : max (max n 1) (1 + v) = max n (v + 1) := by omega
  have hh₂ : satRedTM.tm.runFrom
      (satRedCfg x (some 4) p₁.length (by simp [hx₁]) (max n 1) buf 1 b out) v =
      satRedCfg x (some 4) p₂.length (by simp [hx₂]) (max n (v + 1)) buf (v + 1) b out := by
    simpa [p₂, he, Nat.add_comm, Int.add_comm] using h₂
  have h₃ : satRedTM.tm.step
      (satRedCfg x (some 4) p₂.length (by simp [hx₂]) (max n (v + 1)) buf (v + 1) b out) =
      satRedCfg x (some 6) p₃.length (by simp [hx₃]) (max n (v + 1)) buf v b out := by
    apply satRed_move x 4 6 _ _ _ _ _ buf _ b _ b out .pos .neg 0
      (by
        simp only [p₃, List.length_append, List.length_singleton]
        exact moveInputPos_pos_of_ne_right _ (by simp [hx₂]))
      (by simp <;> omega) (by simp)
    simp [satRedTM, show x[p₂.length]? = some false by simp [hx₂, List.append_assoc]]
  have h₄ := satRed_counterBack x 6 5 (by intros; rfl) p₃.length (by simp [hx₃])
    (max n (v + 1)) (v + 1) (Nat.le_max_right _ _) buf b out
  have hh₄ : satRedTM.tm.runFrom
      (satRedCfg x (some 6) p₃.length (by simp [hx₃]) (max n (v + 1)) buf v b out) (v + 2) =
      satRedCfg x (some 5) p₃.length (by simp [hx₃]) (max n (v + 1)) buf 0 b out := by
    simpa using h₄
  have h₅ : satRedTM.tm.step
      (satRedCfg x (some 5) p₃.length (by simp [hx₃]) (max n (v + 1)) buf 0 b out) =
      satRedCfg x (some 3) (pre.length + (v + 3)) (by simp [hx, CNF.serializeLit] <;> omega)
        (max n (v + 1)) buf 0 b out := by
    apply satRed_move x 5 3 _ _ _ _ _ buf _ b _ b out .pos 0 0
      (by
        have hp : p₃.length = pre.length + v + 2 := by simp [p₃, p₂, p₁] <;> omega
        have hm := moveInputPos_pos_of_ne_right
          (⟨p₃.length + 1, by simp [hx₃] <;> omega⟩ : Fin (x.length + 2)) (by simp [hx₃])
        simpa only [hp, Nat.add_assoc] using hm)
      (by simp) (by simp)
    rfl
  rw [← satRed_one] at h₁
  rw [← satRed_one] at h₃
  rw [← satRed_one] at h₅
  conv_lhs => rw [show 2 * v + 5 = 1 + (v + (1 + ((v + 2) + 1))) by omega,
    MultiTapeTM.runFrom_add, h₁, MultiTapeTM.runFrom_add, hh₂,
    MultiTapeTM.runFrom_add, h₃, MultiTapeTM.runFrom_add, hh₄, h₅]

/-- Maximum folding distributes over list concatenation. -/
private lemma sat_foldMax_append (a b : List ℕ) :
    (a ++ b).foldr max 0 = max (a.foldr max 0) (b.foldr max 0) := by
  induction a with
  | nil => simp
  | cons v a ih => simp [ih, max_assoc]

/-- Clause maximum used by the scanner invariant. -/
private def satClauseVars (C : CNF.Clause ℕ) : ℕ := (C.map fun ℓ => ℓ.1 + 1).foldr max 0

/-- The scanner's clause accumulator agrees with the frozen variable bound. -/
private lemma sat_numVars_cons (C : CNF.Clause ℕ) (φ : CNF ℕ) :
    CNF.numVars (C :: φ) = max (satClauseVars C) φ.numVars := by
  simp only [CNF.numVars, List.flatMap_cons, sat_foldMax_append, satClauseVars]

/-- A complete clause maximum pass is silent, linear in its serialization,
and returns both work heads to their entry positions.

**Proof sketch.** Induct on literals, composing the literal maximum pass and the shorter clause pass. A
zero terminator returns to formula control. Each literal cost is bounded by twice its
serialized length. -/
private lemma satRed_maxClause (x : List Bool) (C : CNF.Clause ℕ) :
    ∀ pre rest (hx : x = pre ++ CNF.serializeClause C ++ rest)
      (n : ℕ) (buf : ℤ → Option Bool) (b : ℤ) (out : List Bool),
    ∃ t ≤ 2 * (CNF.serializeClause C).length,
      satRedTM.tm.runFrom
        (satRedCfg x (some 3) pre.length (by simp [hx]) n buf 0 b out) t =
      satRedCfg x (some 2) (pre.length + (CNF.serializeClause C).length)
        (by simp [hx]) (max n (satClauseVars C)) buf 0 b out := by
  induction C with
  | nil =>
    intro pre rest hx n buf b out
    refine ⟨1, by simp [CNF.serializeClause], ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [CNF.serializeClause, List.flatMap_nil, List.nil_append, List.length_singleton,
      satClauseVars, List.map_nil, List.foldr_nil, Nat.max_zero]
    apply satRed_move x 3 2 _ _ _ _ _ buf _ b _ b out .pos 0 0
      (moveInputPos_pos_of_ne_right _ (by simp [hx, CNF.serializeClause]))
      (by simp) (by simp)
    simp [satRedTM, show x[pre.length]? = some false by simp [hx, CNF.serializeClause]]
  | cons ℓ C ih =>
    intro pre rest hx n buf b out
    let pre' := pre ++ CNF.serializeLit ℓ
    have hx' : x = pre' ++ CNF.serializeClause C ++ rest := by
      simpa [pre', CNF.serializeClause, List.append_assoc] using hx
    have hp : pre'.length = pre.length + (ℓ.1 + 3) := by
      simp [pre', CNF.serializeLit] <;> omega
    have hs := satRed_maxLiteral x ℓ.1 ℓ.2 pre (CNF.serializeClause C ++ rest)
      (by simpa [pre', List.append_assoc] using hx') n buf b out
    obtain ⟨t, ht, hr⟩ := ih pre' rest hx' (max n (ℓ.1 + 1)) buf b out
    have hl : (CNF.serializeClause (ℓ :: C)).length =
        ℓ.1 + 3 + (CNF.serializeClause C).length := by
      simp [CNF.serializeClause, CNF.serializeLit] <;> omega
    refine ⟨2 * ℓ.1 + 5 + t, by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hs]
    simpa only [hp, hl, satClauseVars, List.map_cons, List.foldr_cons,
      max_assoc, Nat.add_assoc] using hr

/-- The silent maximum pass over a whole formula reaches the rewind seam
with exactly `numVars` (or the larger incoming bound) on the first tape.

**Proof sketch.** Induct on clauses. Consume the clause marker, run the clause maximum pass, and recurse
on the remaining formula. Maximum folding identifies the accumulated tape length with
the frozen variable bound. -/
private lemma satRed_maxFormula (x : List Bool) (φ : CNF ℕ) :
    ∀ pre rest (hx : x = pre ++ CNF.serialize φ ++ rest)
      (n : ℕ) (buf : ℤ → Option Bool) (b : ℤ) (out : List Bool),
    ∃ t ≤ 2 * (CNF.serialize φ).length,
      satRedTM.tm.runFrom
        (satRedCfg x (some 2) pre.length (by simp [hx]) n buf 0 b out) t =
      satRedCfg x (some 7) (pre.length + (CNF.serialize φ).length - 1)
        (by simp only [hx, List.length_append] <;> omega) (max n φ.numVars) buf 0 b out := by
  induction φ with
  | nil =>
    intro pre rest hx n buf b out
    refine ⟨1, by simp [CNF.serialize], ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [CNF.serialize, List.flatMap_nil, List.nil_append, List.length_singleton,
      Nat.add_sub_cancel, CNF.numVars, List.foldr_nil, Nat.max_zero]
    apply satRed_move x 2 7 _ _ _ _ _ buf _ b _ b out 0 0 0
      (moveInputPos_zero _) (by simp) (by simp)
    simp [satRedTM, show x[pre.length]? = some false by simp [hx, CNF.serialize]]
  | cons C φ ih =>
    intro pre rest hx n buf b out
    let p₁ := pre ++ [true]
    let p₂ := p₁ ++ CNF.serializeClause C
    have hx₁ : x = p₁ ++ CNF.serializeClause C ++ CNF.serialize φ ++ rest := by
      simpa [p₁, CNF.serialize, List.append_assoc] using hx
    have hx₂ : x = p₂ ++ CNF.serialize φ ++ rest := hx₁
    have hs : satRedTM.tm.step
        (satRedCfg x (some 2) pre.length (by simp [hx]) n buf 0 b out) =
        satRedCfg x (some 3) p₁.length (by simp [hx₁]) n buf 0 b out := by
      apply satRed_move x 2 3 _ _ _ _ _ buf _ b _ b out .pos 0 0
        (by
          simp only [p₁, List.length_append, List.length_singleton]
          exact moveInputPos_pos_of_ne_right _ (by simp [hx₁, p₁]))
        (by simp) (by simp)
      simp [satRedTM, show x[pre.length]? = some true by simp [hx₁, p₁, List.append_assoc]]
    obtain ⟨s, hsbound, hsrun⟩ := satRed_maxClause x C p₁ (CNF.serialize φ ++ rest)
      (by simpa [List.append_assoc] using hx₁) n buf b out
    obtain ⟨t, ht, hr⟩ := ih p₂ rest hx₂ (max n (satClauseVars C)) buf b out
    have hp₂ : p₂.length = p₁.length + (CNF.serializeClause C).length := by simp [p₂]
    have hl : (CNF.serialize (C :: φ)).length =
        1 + (CNF.serializeClause C).length + (CNF.serialize φ).length := by
      simp [CNF.serialize, CNF.serializeClause] <;> omega
    refine ⟨1 + (s + t), by omega, ?_⟩
    rw [← satRed_one] at hs
    rw [MultiTapeTM.runFrom_add, hs, MultiTapeTM.runFrom_add, hsrun]
    have hn : max (max n (satClauseVars C)) (CNF.numVars φ) =
        max n (CNF.numVars (C :: φ)) := by rw [sat_numVars_cons, max_assoc]
    have hi : p₂.length + (CNF.serialize φ).length - 1 =
        pre.length + (CNF.serialize (C :: φ)).length - 1 := by
      simp only [p₂, p₁, List.length_append, List.length_singleton]
      omega
    have hi' : p₁.length + (CNF.serializeClause C).length + (CNF.serialize φ).length - 1 =
        pre.length + (CNF.serialize (C :: φ)).length - 1 := by simpa only [hp₂] using hi
    simpa only [hp₂, hi', hn] using hr

/-- The empty literal buffer has just its permanent left marker. -/
private lemma satRedBuffer_empty : satRedBuffer [] 0 =
    Function.update (fun _ : ℤ => (none : Option Bool)) (-1) (some false) := by
  funext z
  by_cases hz : z = -1
  · subst z; simp [satRedBuffer]
  · simp [satRedBuffer, hz, Function.update_of_ne hz, FinTM.bufferTape]

/-- Installing the buffer marker requires exactly two silent transitions.

**Proof sketch.** The first transition moves the buffer head to -1. The second writes the permanent false
marker and returns to zero, preserving the empty counter and empty output. -/
private lemma satRed_init (x : List Bool) :
    satRedTM.tm.runFrom (satRedTM.tm.initCfg x) 2 =
      satRedCfg x (some 2) 0 (Nat.zero_le _) 0 (satRedBuffer [] 0) 0 0 [] := by
  have hz : satRedCounter 0 = fun _ => none := by
    funext z; simp [satRedCounter, FinTM.bufferTape]
  have hinit : satRedTM.tm.initCfg x =
      satRedCfg x (some 0) 0 (Nat.zero_le _) 0 (fun _ => none) 0 0 [] := by
    apply Cfg.ext <;> simp [satRedTM, satRedCfg, hz]
  have h₁ : satRedTM.tm.step
      (satRedCfg x (some 0) 0 (Nat.zero_le _) 0 (fun _ => none) 0 0 []) =
      satRedCfg x (some 1) 0 (Nat.zero_le _) 0 (fun _ => none) 0 (-1) [] := by
    apply satRed_move x 0 1 0 0 _ _ 0 (fun _ => none) 0 0 0 (-1) [] 0 0 .neg
      (moveInputPos_zero _) (by simp) (by simp)
    rfl
  have h₂ : satRedTM.tm.step
      (satRedCfg x (some 1) 0 (Nat.zero_le _) 0 (fun _ => none) 0 (-1) []) =
      satRedCfg x (some 2) 0 (Nat.zero_le _) 0 (satRedBuffer [] 0) 0 0 [] := by
    unfold MultiTapeTM.step
    change (satRedAction 0 none (some (some false)) 0 .pos none (some 2)).apply _ = _
    exact satRedAction_apply x (some 1) (some 2) 0 0 _ _ 0 0 (fun _ => none)
      (satRedBuffer [] 0) 0 (-1) 0 0 [] [] 0 none (some (some false)) 0 .pos none
      (moveInputPos_zero _) rfl satRedBuffer_empty.symm (by simp) (by simp) (by simp)
  rw [hinit, MultiTapeTM.runFrom_succ_eq_step, h₁, satRed_one, h₂]

/-- The maximum pass and native rewind establish the streaming seam with
exactly `numVars` in unary, empty output, and both work heads at zero.

**Proof sketch.** Install the literal-buffer marker, run the complete silent
maximum scan, then use the audited native rewind contract. The bound is
linear in the serialized formula length and also covers the empty formula. -/
private lemma satRed_start (φ : CNF ℕ) :
    ∃ t ≤ 3 * (CNF.serialize φ).length + 5,
      satRedTM.tm.runFrom (satRedTM.tm.initCfg (CNF.serialize φ)) t =
      satRedCfg (CNF.serialize φ) (some 9) 0 (Nat.zero_le _) φ.numVars
        (satRedBuffer [] 0) 0 0 [] := by
  let x := CNF.serialize φ
  obtain ⟨s, hs, hr⟩ := satRed_maxFormula x φ [] [] (by simp [x])
    0 (satRedBuffer [] 0) 0 []
  have hr' : satRedTM.tm.runFrom
      (satRedCfg x (some 2) 0 (Nat.zero_le _) 0 (satRedBuffer [] 0) 0 0 []) s =
      satRedCfg x (some 7) (x.length - 1) (Nat.sub_le _ _) φ.numVars
        (satRedBuffer [] 0) 0 0 [] := by simpa [x] using hr
  let cfg := satRedCfg x (some 7) (x.length - 1) (Nat.sub_le _ _) φ.numVars
    (satRedBuffer [] 0) 0 0 []
  obtain ⟨r, hb, hrew⟩ := FinTM.timed_rewind satRedTM.tm (7 : Fin 35) (8 : Fin 35) (some (9 : Fin 35))
    (by
      intro inp work
      simp [satRedTM, satRedAction, FinTM.controlAction])
    (by
      intro inp work
      cases inp <;> simp [satRedTM, satRedAction, FinTM.controlAction]) cfg rfl
  have he : {cfg with state := some 9, inputPos := 1} =
      satRedCfg x (some 9) 0 (Nat.zero_le _) φ.numVars (satRedBuffer [] 0) 0 0 [] := by
    exact Cfg.ext rfl rfl rfl rfl rfl
  rw [he] at hrew
  refine ⟨2 + (s + r), by dsimp only [cfg, satRedCfg, x] at hb; omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, satRed_init, MultiTapeTM.runFrom_add, hr']
  exact hrew

/-! **E3 continuation B: normalized streaming schedule.** The persistent state
contains only a fresh-variable cursor, the consumed input length, and one of
five grammar phases (formula, first literal, second literal, tail, finished).
The input head is reconstructed from the length on every round; no buffer or
marker is part of this state. The following word-level schedule is the one
fixed by emitter-infra round 2, finding 5. -/

/-- The three fields carried across a normalized emitter seam. -/
private structure SatStreamState where
  fresh : ℕ
  used : ℕ
  phase : Fin 5
  deriving DecidableEq

/-- A literal parser round trip, proved locally because the encoding module's
corresponding helper is private. -/
private lemma satStream_parseLit (l : Std.Sat.Literal ℕ) (r : List Bool) :
    CNF.parseLit (CNF.serializeLit l ++ r) = some (l, r) := by
  have ht (n : ℕ) : CNF.takeTrues (List.replicate n true ++ false :: l.2 :: r) =
      (n, false :: l.2 :: r) := by
    induction n with
    | zero => rfl
    | succ n ih => simpa [List.replicate_succ, CNF.takeTrues, ih]
  simp [CNF.serializeLit, List.append_assoc, CNF.parseLit, ht]

/-- One validated grammar round: consume a marker or a complete literal,
perform the tail lookahead, and return its output chunk and new state.
Finished states are absorbing. At an exhausted formula input the round emits the fallback terminator;
other local parse failures terminate silently. Complete validation selects
the fallback state before any round starts. -/
private def satStreamRound (x : List Bool) (s : SatStreamState) :
    SatStreamState × List Bool :=
  if s.phase = 4 then (s, []) else
  match x.drop s.used with
  | [] => (⟨s.fresh, s.used, 4⟩, [false])
  | false :: _ =>
      (⟨s.fresh, s.used + 1, if s.phase = 0 then 4 else 0⟩, [false])
  | true :: r =>
      if s.phase = 0 then (⟨s.fresh, s.used + 1, 1⟩, [true]) else
      match CNF.parseLit (true :: r) with
      | none => (⟨s.fresh, s.used, 4⟩, [])
      | some (l, rest) =>
          if s.phase = 3 ∧ rest.head? = some true then
            (⟨s.fresh + 1, s.used + (CNF.serializeLit l).length, 3⟩,
             CNF.serializeLit (s.fresh, true) ++ [false, true] ++
               CNF.serializeLit (s.fresh, false) ++ CNF.serializeLit l)
          else
            (⟨s.fresh, s.used + (CNF.serializeLit l).length,
                if s.phase = 1 then 2 else 3⟩, CNF.serializeLit l)

/-- Execute a prescribed number of normalized rounds, concatenating chunks
in their emission order. This is a pure schedule, not a time-computability claim. -/
private def satStreamRun (x : List Bool) : ℕ → SatStreamState → SatStreamState × List Bool
  | 0, s => (s, [])
  | k + 1, s =>
      let a := satStreamRound x s
      let b := satStreamRun x k a.1
      (b.1, a.2 ++ b.2)

/-- Splitting the round count composes endpoints and concatenates outputs.
**Proof sketch.** Induct on the first segment length; associativity of word
concatenation identifies the two ways of grouping the emitted chunks. -/
private lemma satStreamRun_add (x : List Bool) (m n : ℕ) (s : SatStreamState) :
    satStreamRun x (m + n) s =
      let a := satStreamRun x m s
      let b := satStreamRun x n a.1
      (b.1, a.2 ++ b.2) := by
  induction m generalizing s with
  | zero => simp [satStreamRun]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [satStreamRun, ih, List.append_assoc]

/-- Padding after the formula terminator contributes no further output. -/
private lemma satStreamRun_finished (x : List Bool) (k j p : ℕ) :
    satStreamRun x k ⟨j, p, 4⟩ = (⟨j, p, 4⟩, []) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [satStreamRun, satStreamRound, ih]

/-- The output still pending after the first two literals, together with the
final fresh cursor. A tail link closes one clause and opens the next.
[AB09, §2.3.5, proof of Lemma 2.14] -/
private def satStreamTail : CNF.Clause ℕ → ℕ → List Bool × ℕ
  | [], j => ([false], j)
  | [l], j => (CNF.serializeLit l ++ [false], j)
  | l :: d :: rest, j =>
      let t := satStreamTail (d :: rest) (j + 1)
      (CNF.serializeLit (j, true) ++ [false, true] ++
        CNF.serializeLit (j, false) ++ CNF.serializeLit l ++ t.1, t.2)

/-- The initial clause marker is handled by the formula phase; this is the
rest of the clause's emitted serialization, including its final terminator. -/
private def satStreamClause (C : CNF.Clause ℕ) (j : ℕ) : List Bool × ℕ :=
  match C with
  | [] => ([false], j)
  | [a] => (CNF.serializeLit a ++ [false], j)
  | a :: b :: rest =>
      let t := satStreamTail rest j
      (CNF.serializeLit a ++ CNF.serializeLit b ++ t.1, t.2)

/-- The tail fragments are exactly the serialization of the banked chain
recurrence after its first two literals, with the same allocated cursor.
**Proof sketch.** If at most one tail literal remains, the original clause
has width at most three. Otherwise both recurrences allocate the same fresh
variable, emit the same link, and recurse on the same shorter tail. -/
private lemma satStreamTail_chain (a b : Std.Sat.Literal ℕ) (C : CNF.Clause ℕ) (j : ℕ) :
    (satChain a (b :: C) j).1.flatMap (fun D => true :: CNF.serializeClause D) =
      true :: (CNF.serializeLit a ++ CNF.serializeLit b ++ (satStreamTail C j).1) ∧
    (satChain a (b :: C) j).2 = (satStreamTail C j).2 := by
  induction C generalizing a b j with
  | nil => simp [satChain, satStreamTail, CNF.serializeClause, List.append_assoc]
  | cons c C ih =>
    cases C with
    | nil => simp [satChain, satStreamTail, CNF.serializeClause, List.append_assoc]
    | cons d C =>
      obtain ⟨ho, hj⟩ := ih (j, false) c (j + 1)
      simp only [CNF.serializeClause] at ho
      constructor
      · simp only [satChain, List.flatMap_cons, CNF.serializeClause, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, ho, satStreamTail]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      · exact hj

/-- The clause-level schedule realizes `satSplitClause` exactly, including
the empty clause and all widths at most three. -/
private lemma satStreamClause_split (C : CNF.Clause ℕ) (j : ℕ) :
    (satSplitClause C j).1.flatMap (fun D => true :: CNF.serializeClause D) =
      true :: (satStreamClause C j).1 ∧
    (satSplitClause C j).2 = (satStreamClause C j).2 := by
  cases C with
  | nil => simp [satSplitClause, satStreamClause, CNF.serializeClause]
  | cons a C =>
    cases C with
    | nil => simp [satSplitClause, satChain, satStreamClause, CNF.serializeClause]
    | cons b C => exact satStreamTail_chain a b C j

/-- Re-finding the consumed prefix exposes a clause or formula terminator. -/
private lemma satStreamRound_false (x pre rest : List Bool) (j : ℕ) (q : Fin 5)
    (hq : q ≠ 4) (hx : x = pre ++ false :: rest) :
    satStreamRound x ⟨j, pre.length, q⟩ =
      (⟨j, pre.length + 1, if q = 0 then 4 else 0⟩, [false]) := by
  simp [satStreamRound, hq, hx]

/-- Re-finding the prefix exposes the next clause marker at formula level. -/
private lemma satStreamRound_marker (x pre rest : List Bool) (j : ℕ)
    (hx : x = pre ++ true :: rest) :
    satStreamRound x ⟨j, pre.length, 0⟩ = (⟨j, pre.length + 1, 1⟩, [true]) := by
  simp [satStreamRound, hx]

/-- A complete literal and its lookahead are read within one round, so the
literal buffer never occurs in a persistent seam. -/
private lemma satStreamRound_literal (x pre rest : List Bool) (j : ℕ) (q : Fin 5)
    (hq0 : q ≠ 0) (hq4 : q ≠ 4) (l : Std.Sat.Literal ℕ)
    (hx : x = pre ++ CNF.serializeLit l ++ rest) :
    satStreamRound x ⟨j, pre.length, q⟩ =
      if q = 3 ∧ rest.head? = some true then
        (⟨j + 1, pre.length + (CNF.serializeLit l).length, 3⟩,
         CNF.serializeLit (j, true) ++ [false, true] ++
           CNF.serializeLit (j, false) ++ CNF.serializeLit l)
      else
        (⟨j, pre.length + (CNF.serializeLit l).length, if q = 1 then 2 else 3⟩,
          CNF.serializeLit l) := by
  have hd : x.drop pre.length = CNF.serializeLit l ++ rest := by
    simp [hx, List.append_assoc]
  have hh : ∃ r, CNF.serializeLit l ++ rest = true :: r := by
    exact ⟨List.replicate l.1 true ++ [false, l.2] ++ rest,
      by simp [CNF.serializeLit, List.replicate_succ, List.append_assoc]⟩
  obtain ⟨r, hr⟩ := hh
  have hp := satStream_parseLit l rest
  rw [hr] at hp
  simp only [satStreamRound, hq4, ↓reduceIte, hd, hr, hq0, hp]

/-- Tail phase consumes exactly one round per remaining literal and one for
the clause terminator. Every tail link allocates precisely the banked cursor.
**Proof sketch.** Induct on the remaining literals. The empty case consumes
the terminator. The singleton case copies the last literal. With a nonempty
lookahead, the first round emits the fresh positive/negative link, and the
induction hypothesis handles the shorter tail at the incremented cursor. -/
private lemma satStreamRun_tail (C : CNF.Clause ℕ) (x : List Bool) :
    ∀ pre rest j, x = pre ++ CNF.serializeClause C ++ rest →
      satStreamRun x (C.length + 1) ⟨j, pre.length, 3⟩ =
        (⟨(satStreamTail C j).2, pre.length + (CNF.serializeClause C).length, 0⟩,
          (satStreamTail C j).1) := by
  induction C with
  | nil =>
    intro pre rest j hx
    have h := satStreamRound_false x pre rest j 3 (by decide) (by simpa [CNF.serializeClause] using hx)
    simpa [satStreamRun, CNF.serializeClause, satStreamTail] using h
  | cons l C ih =>
    intro pre rest j hx
    let pre' := pre ++ CNF.serializeLit l
    have hx' : x = pre' ++ CNF.serializeClause C ++ rest := by
      simpa [pre', CNF.serializeClause, List.append_assoc] using hx
    have hp : pre'.length = pre.length + (CNF.serializeLit l).length := by simp [pre']
    have hs := satStreamRound_literal x pre (CNF.serializeClause C ++ rest) j 3
      (by decide) (by decide) l (by simpa [CNF.serializeClause, List.append_assoc] using hx)
    cases C with
    | nil =>
      have ht := ih pre' rest j hx'
      simp only [List.length_nil, Nat.zero_add] at ht
      simp only [CNF.serializeClause, List.flatMap_nil, List.nil_append,
        List.singleton_append, List.head?_cons, Bool.false_eq_true, Option.some.injEq,
        and_false, ↓reduceIte, show (3 : Fin 5) ≠ 1 by decide] at hs
      simp only [List.length_cons, List.length_nil] at ht ⊢
      rw [satStreamRun, hs]
      simp only
      rw [← hp, ht]
      simp [satStreamTail, CNF.serializeClause, hp, List.append_assoc, Nat.add_assoc]
    | cons d C =>
      have ht := ih pre' rest (j + 1) hx'
      simp only [List.length_cons, Nat.add_assoc, Nat.reduceAdd] at ht
      have hh : (CNF.serializeClause (d :: C) ++ rest).head? = some true := by
        simp [CNF.serializeClause, CNF.serializeLit, List.replicate_succ, List.append_assoc]
      simp only [hh, and_self, ↓reduceIte] at hs
      simp only [List.length_cons] at ⊢
      rw [satStreamRun, hs]
      simp only
      rw [← hp, ht]
      simp [satStreamTail, CNF.serializeClause, hp, List.append_assoc, Nat.add_assoc]

/-- A whole clause body takes one round per literal and a final terminator
round, starting in first-literal control and returning to formula control.
**Proof sketch.** Handle zero and one literal directly. Otherwise the first
two rounds copy the first two literals, then invoke the tail induction. -/
private lemma satStreamRun_clause (C : CNF.Clause ℕ) (x pre rest : List Bool) (j : ℕ)
    (hx : x = pre ++ CNF.serializeClause C ++ rest) :
    satStreamRun x (C.length + 1) ⟨j, pre.length, 1⟩ =
      (⟨(satStreamClause C j).2, pre.length + (CNF.serializeClause C).length, 0⟩,
        (satStreamClause C j).1) := by
  cases C with
  | nil =>
    have h := satStreamRound_false x pre rest j 1 (by decide) (by simpa [CNF.serializeClause] using hx)
    simpa [satStreamRun, CNF.serializeClause, satStreamClause] using h
  | cons a C =>
    let pre₁ := pre ++ CNF.serializeLit a
    have h₁ := satStreamRound_literal x pre (CNF.serializeClause C ++ rest) j 1
      (by decide) (by decide) a (by simpa [CNF.serializeClause, List.append_assoc] using hx)
    simp only [show (1 : Fin 5) ≠ 3 by decide, false_and, ↓reduceIte] at h₁
    have hp₁ : pre₁.length = pre.length + (CNF.serializeLit a).length := by simp [pre₁]
    have hx₁ : x = pre₁ ++ CNF.serializeClause C ++ rest := by
      simpa [pre₁, CNF.serializeClause, List.append_assoc] using hx
    cases C with
    | nil =>
      have h₂ := satStreamRound_false x pre₁ rest j 2 (by decide)
        (by simpa [CNF.serializeClause] using hx₁)
      simp only [List.length_cons, List.length_nil]
      rw [satStreamRun, h₁]
      simp only
      rw [← hp₁, satStreamRun, h₂]
      simp [satStreamRun, satStreamClause, CNF.serializeClause, hp₁, List.append_assoc, Nat.add_assoc]
    | cons b C =>
      let pre₂ := pre₁ ++ CNF.serializeLit b
      have hp₂ : pre₂.length = pre₁.length + (CNF.serializeLit b).length := by simp [pre₂]
      have h₂ := satStreamRound_literal x pre₁ (CNF.serializeClause C ++ rest) j 2
        (by decide) (by decide) b (by simpa [CNF.serializeClause, List.append_assoc] using hx₁)
      simp only [show (2 : Fin 5) ≠ 3 by decide, false_and, ↓reduceIte,
        show (2 : Fin 5) ≠ 1 by decide] at h₂
      have ht := satStreamRun_tail C x pre₂ rest j
        (by simpa [pre₂, CNF.serializeClause, List.append_assoc] using hx₁)
      simp only [List.length_cons]
      rw [satStreamRun, h₁]
      simp only
      rw [← hp₁, satStreamRun, h₂]
      simp only
      rw [← hp₂, ht]
      simp [satStreamClause, CNF.serializeClause, hp₂, hp₁, List.append_assoc, Nat.add_assoc]

/-- The exact number of nonfinished rounds: two markers per clause, one
round per original literal, and one final formula terminator. -/
private def satStreamCount (φ : CNF ℕ) : ℕ :=
  (φ.map fun C => C.length + 2).sum + 1

/-- The complete validated schedule emits exactly the banked transform and
threads exactly its final fresh-variable cursor.
**Proof sketch.** Induct on clauses. Emit the opening marker, run the proved
clause schedule, then run the remaining formula at its updated cursor.
The formula terminator enters the absorbing finished phase. -/
private lemma satStreamRun_formula (φ : CNF ℕ) (x : List Bool) :
    ∀ pre rest j, x = pre ++ CNF.serialize φ ++ rest →
      satStreamRun x (satStreamCount φ) ⟨j, pre.length, 0⟩ =
        (⟨(satTransformFrom φ j).2, pre.length + (CNF.serialize φ).length, 4⟩,
          CNF.serialize (satTransformFrom φ j).1) := by
  induction φ with
  | nil =>
    intro pre rest j hx
    have h := satStreamRound_false x pre rest j 0 (by decide) (by simpa [CNF.serialize] using hx)
    simpa [satStreamRun, satStreamCount, CNF.serialize, satTransformFrom] using h
  | cons C φ ih =>
    intro pre rest j hx
    let pre₁ := pre ++ [true]
    let pre₂ := pre₁ ++ CNF.serializeClause C
    have hp₁ : pre₁.length = pre.length + 1 := by simp [pre₁]
    have hp₂ : pre₂.length = pre₁.length + (CNF.serializeClause C).length := by simp [pre₂]
    have hx₁ : x = pre₁ ++ CNF.serializeClause C ++ (CNF.serialize φ ++ rest) := by
      simpa [pre₁, CNF.serialize, List.append_assoc] using hx
    have hx₂ : x = pre₂ ++ CNF.serialize φ ++ rest := by
      simpa [pre₂, List.append_assoc] using hx₁
    have h₁ := satStreamRound_marker x pre (CNF.serializeClause C ++ CNF.serialize φ ++ rest) j
      (by simpa [pre₁, List.append_assoc] using hx₁)
    have h₂ := satStreamRun_clause C x pre₁ (CNF.serialize φ ++ rest) j hx₁
    have ht := ih pre₂ rest (satStreamClause C j).2 hx₂
    have hc : satStreamCount (C :: φ) = 1 + ((C.length + 1) + satStreamCount φ) := by
      simp [satStreamCount]; omega
    rw [hc, Nat.add_comm 1, satStreamRun, h₁]
    simp only
    rw [← hp₁, satStreamRun_add, h₂]
    simp only
    rw [← hp₂, ht]
    obtain ⟨ho, hj⟩ := satStreamClause_split C j
    simp only [satTransformFrom, hj]
    congr 1
    · congr 1
      simp [CNF.serialize, hp₂, hp₁, Nat.add_assoc] <;> omega
    · simp only [CNF.serialize, List.flatMap_append, ho, List.cons_append,
        List.nil_append, List.append_assoc]

/-- Every nonfinished round consumes at least one input bit; the concrete
count is bounded even for empty clauses and the empty formula. -/
private lemma satStreamCount_le (φ : CNF ℕ) :
    satStreamCount φ ≤ (CNF.serialize φ).length := by
  induction φ with
  | nil => simp [satStreamCount, CNF.serialize]
  | cons C φ ih =>
    have hc := sat_clause_measure C
    have hlen : (CNF.serialize (C :: φ)).length =
        1 + (CNF.serializeClause C).length + (CNF.serialize φ).length := by
      simp [CNF.serialize]; omega
    simp only [satStreamCount, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- `R(n)=n` supplies `n+1` rounds. After the exact semantic schedule finishes,
all remaining rounds are empty; hence the extra final round is harmless. -/
private lemma satStreamRun_serialize (φ : CNF ℕ) :
    (satStreamRun (CNF.serialize φ) ((CNF.serialize φ).length + 1)
      ⟨φ.numVars, 0, 0⟩).2 = CNF.serialize (satTransform φ) := by
  have h := satStreamRun_formula φ (CNF.serialize φ) [] [] φ.numVars (by simp)
  have hc := satStreamCount_le φ
  rw [show (CNF.serialize φ).length + 1 = satStreamCount φ +
      ((CNF.serialize φ).length + 1 - satStreamCount φ) by omega, satStreamRun_add]
  simp only [List.length_nil, Nat.zero_add, List.append_nil] at h
  rw [h]
  simp only
  rw [satStreamRun_finished]
  simp [satTransform]

/-- The scheduler's output is precisely the range-indexed concatenation
required by the emitting-loop contract. -/
private lemma satStreamRun_output (x : List Bool) (k : ℕ) (s : SatStreamState) :
    (satStreamRun x k s).2 = (List.range k).flatMap
      (fun i => (satStreamRound x ((fun s => (satStreamRound x s).1)^[i] s)).2) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [satStreamRun, ih, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map, Function.comp_apply, Function.iterate_zero_apply,
      Function.iterate_succ_apply]

/-- Pair-encoded seam word: unary fresh cursor, unary consumed length, and a
bounded unary phase tag. It contains no round-local literal buffer. -/
private def satStreamWord (s : SatStreamState) : List Bool :=
  pairEncode (List.replicate s.fresh true)
    (pairEncode (List.replicate s.used true) (List.replicate s.phase.val true))

/-- Total projections for private paired state words. Malformed words have
empty default components; invariants use only the encoded image. -/
private def satStreamFst (w : List Bool) : List Bool :=
  ((pairDecode w).map Prod.fst).getD []

/-- Second component of a private paired word, with the same empty default. -/
private def satStreamSnd (w : List Bool) : List Bool :=
  ((pairDecode w).map Prod.snd).getD []

/-- Decode the bounded control tag modulo five. The modulus only totalizes
malformed words and is the identity on all reachable tags. -/
private def satStreamRead (w : List Bool) : SatStreamState :=
  ⟨(satStreamFst w).length, (satStreamFst (satStreamSnd w)).length,
    ⟨(satStreamSnd (satStreamSnd w)).length % 5, Nat.mod_lt _ (by decide)⟩⟩

/-- The paired representation preserves all three fields exactly. -/
private lemma satStreamRead_word (s : SatStreamState) : satStreamRead (satStreamWord s) = s := by
  cases s with
  | mk j p q =>
    simp [satStreamRead, satStreamWord, satStreamFst, satStreamSnd,
      pairDecode_pairEncode, Nat.mod_eq_of_lt q.isLt]

/-- The state representation has linear size in its two unary counters. -/
private lemma satStreamWord_length (s : SatStreamState) :
    (satStreamWord s).length = 2 * s.fresh + 2 * s.used + s.phase.val + 4 := by
  simp only [satStreamWord, pairEncode, List.length_append, List.length_replicate]
  simp [List.length_flatMap, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.mul_comm] <;> omega

/-- A length-only invariant: offsets remain inside the native input, and at
most one fresh variable is allocated per consumed bit. -/
private def satStreamBound (x : List Bool) (s : SatStreamState) : Prop :=
  s.used ≤ x.length ∧ s.fresh ≤ x.length + s.used

/-- Every round preserves the invariant, including malformed local inputs.
**Proof sketch.** A marker consumes one bit without allocation. A successful
literal parse reconstructs the suffix, so its serialized length fits inside
the unread input; that length is at least three and pays for a possible
single allocation. Finished and local-failure cases preserve the counters. -/
private lemma satStreamRound_bound (x : List Bool) (s : SatStreamState)
    (hs : satStreamBound x s) : satStreamBound x (satStreamRound x s).1 := by
  rcases hs with ⟨hp, hj⟩
  unfold satStreamRound
  split
  · exact ⟨hp, hj⟩
  · cases hd : x.drop s.used with
    | nil => exact ⟨hp, hj⟩
    | cons b r =>
      have hl := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at hl
      cases b with
      | false => dsimp only [satStreamBound]; exact ⟨by omega, by omega⟩
      | true =>
        simp only
        split
        · dsimp only [satStreamBound]; exact ⟨by omega, by omega⟩
        · cases hparse : CNF.parseLit (true :: r) with
          | none => exact ⟨hp, hj⟩
          | some lr =>
            rcases lr with ⟨l, rest⟩
            have he := congrArg List.length (sat_parseLit_repr hparse)
            have hpos : 0 < (CNF.serializeLit l).length := by simp [CNF.serializeLit]
            simp only [List.length_cons, List.length_append] at he
            simp only
            split <;> dsimp only [satStreamBound] <;> exact ⟨by omega, by omega⟩

/-- Reachable cursors are at most twice the original input length, and the
whole state word has length at most `6n+8`. -/
private lemma satStreamBound_size (x : List Bool) (s : SatStreamState)
    (hs : satStreamBound x s) :
    s.fresh ≤ 2 * x.length ∧ (satStreamWord s).length ≤ 6 * x.length + 8 := by
  have hq := s.phase.isLt
  rw [satStreamWord_length]
  rcases hs with ⟨hp, hj⟩
  constructor <;> omega

/-- Complete validation selects the startup state before emission. A failed
parse starts at the right boundary in formula control; its first round emits
only the fallback terminator and then becomes finished, even at input length zero. -/
private def satStreamStart (x : List Bool) : SatStreamState :=
  if satSyntax x then ⟨(CNF.decode x).numVars, 0, 0⟩ else ⟨0, x.length, 0⟩

/-- Both the valid and fallback startup states satisfy the loop invariant. -/
private lemma satStreamStart_bound (x : List Bool) : satStreamBound x (satStreamStart x) := by
  unfold satStreamStart
  split
  · exact ⟨Nat.zero_le _, by simpa using CNF.numVars_decode_le x⟩
  · exact ⟨Nat.le_refl _, Nat.zero_le _⟩

/-- Failed whole-string validation produces exactly `[false]`; no prefix of
the malformed string is emitted. This includes trailing-data failures. -/
private lemma satStreamRun_fallback (x : List Bool) (k : ℕ) :
    (satStreamRun x (k + 1) ⟨0, x.length, 0⟩).2 = [false] := by
  simp [satStreamRun, satStreamRound, satStreamRun_finished]

/-- Exact output identity on every string, before any machine-computability
claim: complete validation plus the normalized schedule is `satReduction`.
**Proof sketch.** A successful parser reconstructs the entire serialized
formula and invokes the formula induction. A failed parse selects the
right-boundary fallback state, whose only nonempty chunk is `[false]`. -/
private lemma satStreamRun_correct (x : List Bool) :
    (satStreamRun x (x.length + 1) (satStreamStart x)).2 = satReduction x := by
  cases hp : CNF.parse x with
  | none =>
    have hs : satSyntax x = false := by simp [satSyntax_spec, hp]
    rw [satStreamStart, hs]
    simpa [satReduction_fallback x hp] using satStreamRun_fallback x x.length
  | some φ =>
    have hx := sat_parse_repr hp
    have hd : CNF.decode x = φ := by simp [CNF.decode, hp]
    have hs : satSyntax x = true := by simp [satSyntax_spec, hp]
    simp only [satStreamStart, hs, ↓reduceIte, satReduction, hd]
    rw [hx]
    exact satStreamRun_serialize φ

/-- Encoded next-state function consumed by the audited emitter interface. -/
private def satStreamStep (x w : List Bool) : List Bool :=
  satStreamWord (satStreamRound x (satStreamRead w)).1

/-- Encoded chunk function consumed by the audited emitter interface. -/
private def satStreamEmit (x w : List Bool) : List Bool :=
  (satStreamRound x (satStreamRead w)).2

/-- The loop invariant includes canonical encoding and its original-input
length bound; arbitrary malformed state words are not admitted as seams. -/
private def satStreamInv (x w : List Bool) : Prop :=
  ∃ s, w = satStreamWord s ∧ satStreamBound x s

/-- The encoded invariant holds at startup. -/
private lemma satStreamInv_start (x : List Bool) :
    satStreamInv x (satStreamWord (satStreamStart x)) :=
  ⟨_, rfl, satStreamStart_bound x⟩

/-- The encoded invariant is closed under every loop step. -/
private lemma satStreamInv_step (x w : List Bool) (h : satStreamInv x w) :
    satStreamInv x (satStreamStep x w) := by
  rcases h with ⟨s, rfl, hs⟩
  refine ⟨(satStreamRound x s).1, ?_, satStreamRound_bound x s hs⟩
  simp [satStreamStep, satStreamRead_word]

/-- Encoded and structured iteration have the same orbit. -/
private lemma satStreamStep_iterate (x : List Bool) (s : SatStreamState) (k : ℕ) :
    (satStreamStep x)^[k] (satStreamWord s) =
      satStreamWord ((fun s => (satStreamRound x s).1)^[k] s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp [satStreamStep, satStreamRead_word]

/-- The exact expression returned by `exists_emitLoopTM`, with `R n = n`,
is the desired all-string reduction. This discharges the output-identity
obligation independently of the remaining native-machine realization. -/
private lemma satStream_output_identity (x : List Bool) :
    (List.range (x.length + 1)).flatMap (fun i =>
      satStreamEmit x ((satStreamStep x)^[i] (satStreamWord (satStreamStart x)))) =
        satReduction x := by
  simp only [satStreamStep_iterate, satStreamEmit, satStreamRead_word]
  rw [← satStreamRun_output]
  exact satStreamRun_correct x

/-- Administrative action for retaining a computed word beside its input.
The completed source bank is untouched; only the capture head may move. -/
private def satPairAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option (Fin 8)) : Action (M.k + 1) Bool (M.State ⊕ Fin 8) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q.map Sum.inr⟩

/-- Capture `f x`, rewind both heads, replay its bits twice, emit the pairing
separator, then copy native `x`. Thus the output is `pairEncode (f x) x`.
This private data-retaining combinator supplies the two-field round arguments. -/
private def satPairTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ Fin 8
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
    | .inl q => captureAction Sum.inl (.inr 0)
        (M.tm.tr q inp (fun i => work (Fin.castSucc i)))
    | .inr q => match q.val with
      | 0 => FinTM.controlAction .neg (some (.inr 1))
      | 1 => if inp.isSome then FinTM.controlAction .neg (some (.inr 1))
        else FinTM.controlAction .pos (some (.inr 2))
      | 2 => satPairAction M 0 .neg none (some 3)
      | 3 => if (work (Fin.last M.k)).isSome then satPairAction M 0 .neg none (some 3)
        else satPairAction M 0 .pos none (some 4)
      | 4 => match work (Fin.last M.k) with
        | some b => satPairAction M 0 0 (some b) (some 5)
        | none => satPairAction M 0 0 (some false) (some 6)
      | 5 => satPairAction M 0 .pos (work (Fin.last M.k)) (some 4)
      | 6 => satPairAction M 0 0 (some true) (some 7)
      | _ => match inp with
        | some b => satPairAction M .pos 0 (some b) (some 7)
        | none => satPairAction M 0 0 none none }

/-- Saved source scratch and its immutable captured word during pairing. -/
private def satPairCfg (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u : List Bool) (q : Option (Fin 8))
    (i : ℕ) (hi : i ≤ x.length) (j : ℤ) (out : List Bool) :
    Cfg (M.k + 1) Bool (satPairTM M).State x :=
  ⟨q.map Sum.inr, ⟨i + 1, by omega⟩,
    fun t => if h : t.val < M.k then saved.workTapes ⟨t, h⟩ else FinTM.bufferTape u,
    fun t => if h : t.val < M.k then saved.workTapePos ⟨t, h⟩ else j, out⟩

/-- Pairing reads native input at the displayed offset. -/
private lemma satPairCfg_input (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u : List Bool) (q : Option (Fin 8))
    (i : ℕ) (hi : i ≤ x.length) (j : ℤ) (out : List Bool) :
    (satPairCfg M saved u q i hi j out).inputSymbol = x[i]? :=
  FinTM.inputSymbol_at _ i hi rfl

/-- Pairing's last work head reads the captured word. -/
private lemma satPairCfg_work (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u : List Bool) (q : Option (Fin 8))
    (i : ℕ) (hi : i ≤ x.length) (j : ℤ) (out : List Bool) :
    (satPairCfg M saved u q i hi j out).workTapeSymbols (Fin.last M.k) =
      FinTM.bufferTape u j := by simp [satPairCfg, Cfg.workTapeSymbols]

/-- Pairing administration changes only the displayed positions and output. -/
private lemma satPairAction_apply (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u : List Bool) (q q' : Option (Fin 8))
    (i i' : ℕ) (hi : i ≤ x.length) (hi' : i' ≤ x.length) (j j' : ℤ)
    (m d : SignType) (b : Option Bool) (out : List Bool)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨i' + 1, by omega⟩)
    (hd : j + d.cast = j') :
    (satPairAction M m d b q').apply (satPairCfg M saved u q i hi j out) =
      satPairCfg M saved u q' i' hi' j' (out ++ b.toList) := by
  refine Cfg.ext rfl hm rfl ?_ rfl
  funext t
  by_cases ht : t.val < M.k
  · simp [satPairAction, satPairCfg, Action.apply, ht]
  · simpa [satPairAction, satPairCfg, Action.apply, ht] using hd

/-- Rewind the captured word from its last occupied cell to the origin.
**Proof sketch.** Induct on the occupied prefix to the left of the head.
Each occupied cell moves left; the blank at `-1` moves right into replay. -/
private lemma satPair_rewind (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u : List Bool) (n : ℕ) (hn : n ≤ u.length) :
    (satPairTM M).tm.runFrom
      (satPairCfg M saved u (some 3) 0 (Nat.zero_le _) ((n : ℤ) - 1) []) (n + 1) =
        satPairCfg M saved u (some 4) 0 (Nat.zero_le _) 0 [] := by
  induction n with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((satPairTM M).tm.tr (.inr 3) _ _).apply _ = _
    simp only [satPairTM]
    rw [satPairCfg_work]
    simp only [Int.natCast_zero, zero_sub, FinTM.bufferTape_left, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact satPairAction_apply M saved u _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
      (-1) 0 0 .pos none [] (moveInputPos_zero _) (by simp)
  | succ n ih =>
    have hw : FinTM.bufferTape u (((n + 1 : ℕ) : ℤ) - 1) = some u[n] := by
      simp [FinTM.bufferTape, List.getElem?_eq_getElem (by omega : n < u.length)]
    have hs : (satPairTM M).tm.step
        (satPairCfg M saved u (some 3) 0 (Nat.zero_le _) (((n + 1 : ℕ) : ℤ) - 1) []) =
        satPairCfg M saved u (some 3) 0 (Nat.zero_le _) ((n : ℤ) - 1) [] := by
      unfold MultiTapeTM.step
      change ((satPairTM M).tm.tr (.inr 3) _ _).apply _ = _
      simp only [satPairTM]
      rw [satPairCfg_work, hw]
      exact satPairAction_apply M saved u _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
        _ _ 0 .neg none [] (moveInputPos_zero _) (by simp; omega)
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]

/-- Capture through the actual first halt, including a halting emission, then
rewind native input and the captured word. All startup output is suppressed.
**Proof sketch.** Use the audited capture correspondence and native rewind;
the last tape then rewinds across precisely the captured output length. -/
private lemma satPair_start (M : FinTM Bool) (x u : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x u T) :
    ∃ (saved : Cfg M.k Bool M.State x) (s : ℕ), s ≤ T + x.length + u.length + 5 ∧
      (satPairTM M).tm.runFrom ((satPairTM M).tm.initCfg x) s =
        satPairCfg M saved u (some 4) 0 (Nat.zero_le _) 0 [] := by
  obtain ⟨t, ht, hlive, hhalt, hout⟩ := sat_first_halt M x u T hM
  let saved := M.tm.runFrom (M.tm.initCfg x) t
  let captured := captureCfg (Sum.inl : M.State → (satPairTM M).State) (.inr 0) [] [] saved
  have hinit : (satPairTM M).tm.initCfg x =
      captureCfg (Sum.inl : M.State → (satPairTM M).State) (.inr 0) [] [] (M.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i z; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init, FinTM.bufferTape]
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (satPairTM M).tm.runFrom ((satPairTM M).tm.initCfg x) t = captured := by
    rw [hinit]
    exact capture_run M.tm (satPairTM M).tm Sum.inl (.inr 0) (by intros; rfl)
      [] [] (M.tm.initCfg x) t hlive
  have hstate : captured.state = some (.inr 0) := by
    simp only [captured, captureCfg, saved, hhalt, Option.map_none, Option.getD_none]
  obtain ⟨r, hr, hrew⟩ := FinTM.timed_rewind (satPairTM M).tm (.inr 0) (.inr 1)
    (some (.inr 2)) (by intros; rfl) (by intro inp work; cases inp <;> rfl) captured hstate
  have he : {captured with state := some (.inr 2), inputPos := 1} =
      satPairCfg M saved u (some 2) 0 (Nat.zero_le _) u.length [] := by
    simp only [captured, captureCfg, saved, hout, List.nil_append, satPairCfg, Option.map_some]
    exact Cfg.ext rfl (by apply Fin.ext; simp) rfl rfl rfl
  rw [he] at hrew
  have hs : (satPairTM M).tm.step (satPairCfg M saved u (some 2) 0 (Nat.zero_le _) u.length []) =
      satPairCfg M saved u (some 3) 0 (Nat.zero_le _) ((u.length : ℤ) - 1) [] := by
    change (satPairAction M 0 .neg none (some 3)).apply _ = _
    exact satPairAction_apply M saved u _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
      _ _ 0 .neg none [] (moveInputPos_zero _) (by simp; omega)
  refine ⟨saved, t + r + (u.length + 2), ?_, ?_⟩
  · have hp := captured.inputPos.isLt; omega
  · have hpre : (satPairTM M).tm.runFrom ((satPairTM M).tm.initCfg x) (t + r) =
        satPairCfg M saved u (some 2) 0 (Nat.zero_le _) u.length [] := by
      rw [MultiTapeTM.runFrom_add, hcap, hrew]
    rw [MultiTapeTM.runFrom_add, hpre, MultiTapeTM.runFrom_succ_eq_step, hs,
      satPair_rewind M saved u u.length (Nat.le_refl _)]

/-- Replay the captured suffix twice bit by bit and append the pairing
separator. The source bank and native input head remain fixed.
**Proof sketch.** Each occupied capture cell takes two transitions and one
head move. The blank after the word triggers the two fixed separator bits. -/
private lemma satPair_replay (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u rest : List Bool) :
    ∀ pre out, u = pre ++ rest →
      (satPairTM M).tm.runFrom
        (satPairCfg M saved u (some 4) 0 (Nat.zero_le _) pre.length out) (2 * rest.length + 2) =
          satPairCfg M saved u (some 7) 0 (Nat.zero_le _) u.length
            (out ++ satBits rest ++ [false, true]) := by
  induction rest with
  | nil =>
    intro pre out hu
    have he : u = pre := by simpa using hu
    clear hu
    subst u
    have h₁ : (satPairTM M).tm.step
        (satPairCfg M saved pre (some 4) 0 (Nat.zero_le _) pre.length out) =
        satPairCfg M saved pre (some 6) 0 (Nat.zero_le _) pre.length (out ++ [false]) := by
      unfold MultiTapeTM.step
      change ((satPairTM M).tm.tr (.inr 4) _ _).apply _ = _
      simp only [satPairTM]
      rw [satPairCfg_work]
      simp only [FinTM.bufferTape_nat, List.getElem?_length]
      exact satPairAction_apply M saved pre _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
        _ _ 0 0 (some false) out (moveInputPos_zero _) (by simp)
    have h₂ : (satPairTM M).tm.step
        (satPairCfg M saved pre (some 6) 0 (Nat.zero_le _) pre.length (out ++ [false])) =
        satPairCfg M saved pre (some 7) 0 (Nat.zero_le _) pre.length ((out ++ [false]) ++ [true]) := by
      exact satPairAction_apply M saved pre _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
        _ _ 0 0 (some true) _ (moveInputPos_zero _) (by simp)
    change (satPairTM M).tm.step ((satPairTM M).tm.step _) = _
    rw [h₁, h₂]
    simp [satBits, List.append_assoc]
  | cons b rest ih =>
    intro pre out hu
    have hw : FinTM.bufferTape u (pre.length : ℤ) = some b := by simp [hu]
    have h₁ : (satPairTM M).tm.step
        (satPairCfg M saved u (some 4) 0 (Nat.zero_le _) pre.length out) =
        satPairCfg M saved u (some 5) 0 (Nat.zero_le _) pre.length (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((satPairTM M).tm.tr (.inr 4) _ _).apply _ = _
      simp only [satPairTM]
      rw [satPairCfg_work, hw]
      exact satPairAction_apply M saved u _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
        _ _ 0 0 (some b) out (moveInputPos_zero _) (by simp)
    have h₂ : (satPairTM M).tm.step
        (satPairCfg M saved u (some 5) 0 (Nat.zero_le _) pre.length (out ++ [b])) =
        satPairCfg M saved u (some 4) 0 (Nat.zero_le _) (pre ++ [b]).length (out ++ [b, b]) := by
      unfold MultiTapeTM.step
      change ((satPairTM M).tm.tr (.inr 5) _ _).apply _ = _
      simp only [satPairTM]
      rw [satPairCfg_work, hw]
      simpa [List.append_assoc] using satPairAction_apply M saved u (some 5) (some 4)
        0 0 (Nat.zero_le _) (Nat.zero_le _) (pre.length : ℤ) ((pre ++ [b]).length : ℤ)
        0 .pos (some b) (out ++ [b]) (moveInputPos_zero _) (by simp)
    rw [show 2 * (b :: rest).length + 2 = (2 * rest.length + 2) + 1 + 1 by simp; omega,
      MultiTapeTM.runFrom_succ_eq_step, h₁, MultiTapeTM.runFrom_succ_eq_step, h₂]
    simpa [satBits, List.append_assoc] using ih (pre ++ [b]) (out ++ [b, b])
      (by simpa [List.append_assoc] using hu)

/-- Native suffix copying emits every bit and halts on the right blank.
**Proof sketch.** Induct on the remaining native suffix. Work tapes and heads
are unchanged, including the completed source bank and its captured result. -/
private lemma satPair_copy (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u rest : List Bool) :
    ∀ pre out (hx : x = pre ++ rest),
      (satPairTM M).tm.runFrom
        (satPairCfg M saved u (some 7) pre.length (by simp [hx]) u.length out) (rest.length + 1) =
          satPairCfg M saved u none x.length (Nat.le_refl _) u.length (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    have hl : x.length = pre.length := by simp [hx]
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((satPairTM M).tm.tr (.inr 7) _ _).apply _ = _
    simp only [satPairTM]
    rw [satPairCfg_input, show x[pre.length]? = none by simp [hx]]
    have ha := satPairAction_apply M saved u (some 7) none pre.length pre.length
      (by omega) (by omega) (u.length : ℤ) (u.length : ℤ) 0 0 none out
      (moveInputPos_zero _) (by simp)
    simpa only [hl, Option.toList_none, List.append_nil] using ha
  | cons b rest ih =>
    intro pre out hx
    have hs : (satPairTM M).tm.step
        (satPairCfg M saved u (some 7) pre.length (by simp [hx]) u.length out) =
        satPairCfg M saved u (some 7) (pre ++ [b]).length (by simp [hx]) u.length (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((satPairTM M).tm.tr (.inr 7) _ _).apply _ = _
      simp only [satPairTM]
      rw [satPairCfg_input]
      rw [show x[pre.length]? = some b by simp [hx]]
      exact satPairAction_apply M saved u (some 7) (some 7) pre.length (pre ++ [b]).length
        (by simp [hx]) (by simp [hx]) (u.length : ℤ) (u.length : ℤ) .pos 0 (some b) out (by
          simpa using moveInputPos_pos_of_ne_right (⟨pre.length + 1, by simp [hx] <;> omega⟩ : Fin (x.length + 2))
            (by simp [hx] <;> omega)) (by simp)
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa [List.append_assoc] using ih (pre ++ [b]) (out ++ [b])
      (by simpa [List.append_assoc] using hx)

/-- Retaining a computed result next to its original input has a uniform
polynomial overhead; the capture output length is paid by the source time. -/
private lemma satPair_computes (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    (satPairTM M).ComputesFunInTime (fun x => pairEncode (f x) x)
      (fun n => 4 * T n + 2 * n + 8) := by
  intro x
  obtain ⟨saved, s, hs, hstart⟩ := satPair_start M x (f x) (T x.length) (hM x)
  have hrep := satPair_replay M saved (f x) (f x) [] [] (by simp)
  have hcopy := satPair_copy M saved (f x) x [] (satBits (f x) ++ [false, true]) (by simp)
  simp only [List.length_nil, Int.natCast_zero, List.nil_append] at hrep hcopy
  have ht : (f x).length ≤ T x.length := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
    simpa only [ho] using M.tm.output_length_le x (T x.length)
  have hc : (satPairTM M).ComputesInTime x (pairEncode (f x) x)
      (s + (2 * (f x).length + 2) + (x.length + 1)) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add _ s (2 * (f x).length + 2), hstart, hrep, hcopy]
    exact ⟨rfl, rfl⟩
  exact hc.mono (by dsimp only; omega)

/-- Polynomial-time functions can retain their computed value and the
original input as a pair. -/
private lemma sat_pt_pair_input {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    PolyTimeComputable (fun x => pairEncode (f x) x) := by
  obtain ⟨M, C, e, hM⟩ := hf
  refine ⟨satPairTM M, 4 * C + 10, e + 1, fun x => (satPair_computes M f _ hM x).mono ?_⟩
  have he : (x.length + 1) ^ e ≤ (x.length + 1) ^ (e + 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have h1 : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)
  have ht := Nat.mul_le_mul_left (4 * C) he
  dsimp only
  calc
    _ = 4 * C * (x.length + 1) ^ e + 2 * x.length + 8 := by ring
    _ ≤ 4 * C * (x.length + 1) ^ (e + 1) + 10 * (x.length + 1) ^ (e + 1) := by omega
    _ = _ := by ring

/-- Mapping a paired payload by a polynomial-time function preserves
polynomial time, by the audited data-retaining catalog constructor. -/
private lemma sat_pt_mapSnd {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun z => match pairDecode z with
      | some (a, b) => pairEncode a (g b)
      | none => []) := by
  obtain ⟨M, C, e, hM⟩ := hg
  obtain ⟨N, K, hN⟩ := FinTM.computesFunInTime_pairMapSnd hM
    (by intro a b hab; exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) e))
  refine ⟨N, K * (C + 1), e + 1, fun x => (hN x).mono ?_⟩
  have he : (x.length + 1) ^ e ≤ (x.length + 1) ^ (e + 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have h1 : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)
  calc
    _ ≤ K * ((C + 1) * (x.length + 1) ^ (e + 1)) := by
      apply Nat.mul_le_mul_left
      calc
        _ ≤ (x.length + 1) ^ (e + 1) + C * (x.length + 1) ^ (e + 1) :=
          Nat.add_le_add h1 (Nat.mul_le_mul_left C he)
        _ = _ := by ring
    _ = _ := by ring

/-- Independently computed fields can be paired without losing the original
input needed by the second computation. -/
private lemma sat_pt_pair {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => pairEncode (f x) (g x)) := by
  simpa only [Function.comp_def, pairDecode_pairEncode] using
    (sat_pt_mapSnd hg).comp (sat_pt_pair_input hf)

/-- Independently computed word fragments can be concatenated in polynomial time. -/
private lemma sat_pt_append {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => f x ++ g x) := by
  simpa only [Function.comp_def, pairDecode_pairEncode] using
    (sat_pt_linear _ FinTM.computesFunInTime_pairConcat).comp (sat_pt_pair hf hg)

/-- Pure semantics for a finite one-way word transducer with at most one
emitted bit per input bit and one optional final bit. -/
private def satMapWord {S : Type} (next : S → Bool → S)
    (emit : S → Bool → Option Bool) (finish : S → Option Bool) : S → List Bool → List Bool
  | q, [] => (finish q).toList
  | q, b :: r => (emit q b).toList ++ satMapWord next emit finish (next q b) r

/-- Finite one-way transducer for local word operations used by round-field
assembly. It uses no work tapes and always halts at the right boundary. -/
private def satMapTM {S : Type} [Fintype S] [DecidableEq S]
    (next : S → Bool → S) (emit : S → Bool → Option Bool)
    (finish : S → Option Bool) (start : S) : FinTM Bool where
  k := 0
  State := S
  tm := {
    q₀ := start
    tr := fun q inp _ => match inp with
      | some b => ⟨.pos, Fin.elim0, emit q b, some (next q b)⟩
      | none => ⟨0, Fin.elim0, finish q, none⟩ }

/-- Scanner frame with an explicit already-emitted prefix. -/
private def satMapCfg {S : Type} (x : List Bool) (q : S) (i : ℕ)
    (hi : i ≤ x.length) (out : List Bool) : Cfg 0 Bool S x :=
  ⟨some q, ⟨i + 1, by omega⟩, Fin.elim0, Fin.elim0, out⟩

/-- The finite transducer implements its recursive word semantics exactly.
**Proof sketch.** Induct on the unread suffix. An input bit performs one
transition and appends its optional emission; the right blank performs the
final transition, including its optional last bit. -/
private lemma satMap_run {S : Type} [Fintype S] [DecidableEq S]
    (next : S → Bool → S) (emit : S → Bool → Option Bool)
    (finish : S → Option Bool) (start : S) (x rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) q out,
      ((satMapTM next emit finish start).tm.runFrom
        (satMapCfg x q pre.length (by simp [hx]) out) (rest.length + 1)).state = none ∧
      ((satMapTM next emit finish start).tm.runFrom
        (satMapCfg x q pre.length (by simp [hx]) out) (rest.length + 1)).output =
          out ++ satMapWord next emit finish q rest := by
  induction rest with
  | nil =>
    intro pre hx q out
    simp only [List.append_nil] at hx
    subst x
    simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, satMapTM,
      satMapCfg, Cfg.inputSymbol, Action.apply, satMapWord]
  | cons b rest ih =>
    intro pre hx q out
    have hs : (satMapTM next emit finish start).tm.step
        (satMapCfg x q pre.length (by simp [hx]) out) =
        satMapCfg x (next q b) (pre ++ [b]).length (by simp [hx]) (out ++ (emit q b).toList) := by
      have hin : (satMapCfg x q pre.length (by simp [hx]) out).inputSymbol = some b := by
        rw [FinTM.inputSymbol_at _ pre.length (by simp [hx]) rfl]
        simp [hx]
      unfold MultiTapeTM.step
      change (((satMapTM next emit finish start).tm.tr q _ _).apply _) = _
      rw [hin]
      refine Cfg.ext_zero_tapes rfl ?_ rfl
      simpa using moveInputPos_pos_of_ne_right
        (⟨pre.length + 1, by simp [hx] <;> omega⟩ : Fin (x.length + 2)) (by simp [hx] <;> omega)
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [satMapWord, List.append_assoc] using
      ih (pre ++ [b]) (by simpa [List.append_assoc] using hx) (next q b) (out ++ (emit q b).toList)

/-- Every finite mapper has the exact input-length-plus-one time bound. -/
private lemma satMap_poly {S : Type} [Fintype S] [DecidableEq S]
    (next : S → Bool → S) (emit : S → Bool → Option Bool)
    (finish : S → Option Bool) (start : S) :
    PolyTimeComputable (satMapWord next emit finish start) := by
  refine ⟨satMapTM next emit finish start, 1, 1, fun x => ?_⟩
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  have hi : (satMapTM next emit finish start).tm.initCfg x =
      satMapCfg x start 0 (Nat.zero_le _) [] := Cfg.ext_zero_tapes rfl rfl rfl
  simpa only [Nat.pow_one, Nat.one_mul, hi, List.length_nil, List.nil_append] using
    satMap_run next emit finish start x x [] (by simp) start []

/-- Replacing every bit by `true` computes the exact unary input length. -/
private lemma sat_pt_unaryLength : PolyTimeComputable (fun x => List.replicate x.length true) := by
  have h := satMap_poly (S := Unit) (fun _ _ => ()) (fun _ _ => some true) (fun _ => none) ()
  have he (x : List Bool) :
      satMapWord (fun (_ : Unit) _ => ()) (fun _ _ => some true) (fun _ => none) () x =
        List.replicate x.length true := by
    induction x with
    | nil => rfl
    | cons b r ih => simpa [satMapWord, List.replicate_succ] using congrArg (true :: ·) ih
  convert h using 1
  funext x
  exact (he x).symm

/-- Removing the first bit is a two-state finite transduction. -/
private lemma sat_pt_tail : PolyTimeComputable List.tail := by
  let emit (q b : Bool) : Option Bool := if q then some b else none
  have h := satMap_poly (fun (_ : Bool) _ => true) emit (fun _ => none) false
  have hc (x : List Bool) : satMapWord (fun (_ : Bool) _ => true) emit (fun _ => none) true x = x := by
    induction x with
    | nil => rfl
    | cons b r ih => simp [satMapWord, emit, ih]
  have he (x : List Bool) : satMapWord (fun (_ : Bool) _ => true) emit (fun _ => none) false x = x.tail := by
    cases x <;> simp [satMapWord, emit, hc]
  convert h using 1
  funext x
  exact (he x).symm

/-- Extracting at most the first bit is also a two-state finite transduction. -/
private lemma sat_pt_head : PolyTimeComputable (fun x => x.take 1) := by
  let emit (q b : Bool) : Option Bool := if q then none else some b
  have h := satMap_poly (fun (_ : Bool) _ => true) emit (fun _ => none) false
  have hc (x : List Bool) : satMapWord (fun (_ : Bool) _ => true) emit (fun _ => none) true x = [] := by
    induction x with
    | nil => rfl
    | cons b r ih => simp [satMapWord, emit, ih]
  have he (x : List Bool) : satMapWord (fun (_ : Bool) _ => true) emit (fun _ => none) false x = x.take 1 := by
    cases x <;> simp [satMapWord, emit, hc]
  convert h using 1
  funext x
  exact (he x).symm

/-- Equality to a fixed control word is decided by the public finite-word
comparison constructor, after any polynomial field computation. -/
private lemma sat_pt_eq {f : List Bool → List Bool} (hf : PolyTimeComputable f) (w : List Bool) :
    PolyTimeComputable (fun x => [decide (f x = w)]) := by
  have he : PolyTimeComputable (fun x => if x = w then [true] else [false]) :=
    sat_pt_linear _ (FinTM.computesFunInTime_ifEq w [true] [false])
  convert he.comp hf using 1
  funext x
  by_cases h : f x = w <;> simp [Function.comp_def, h]

/-- Changing a machine only beyond a guarded stopping point preserves its
entire prefix run. This helper does not assume an eventual halt. -/
private lemma sat_run_agree {k : ℕ} {S : Type} {x : List Bool}
    (A B : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
    (h : ∀ i < t, B.step (A.runFrom c i) = A.step (A.runFrom c i)) :
    B.runFrom c t = A.runFrom c t := by
  have hi : ∀ i ≤ t, B.runFrom c i = A.runFrom c i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hit
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), h i (by omega),
        MultiTapeTM.runFrom_succ_eq_step']
  exact hi t (Nat.le_refl _)

/-- The banked maximum pass has no earlier visit to its streaming entry:
state 9 necessarily emits a bit, whereas the proved endpoint is silent.
**Proof sketch.** If state 9 occurred earlier, the next output would have
positive length. Output-prefix monotonicity would make the silent endpoint
impossible. This justifies intercepting state 9 without redoing the maximum pass. -/
private lemma satRed_start_guard (x : List Bool) (t : ℕ)
    (ho : (satRedTM.tm.runFrom (satRedTM.tm.initCfg x) t).output = []) :
    ∀ i < t, (satRedTM.tm.runFrom (satRedTM.tm.initCfg x) i).state ≠ some (9 : Fin 35) := by
  intro i hi hstate
  have hp := (satRedTM.tm.output_prefix (satRedTM.tm.initCfg x) (show i + 1 ≤ t by omega)).length_le
  rw [ho, List.length_nil, MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output,
    List.length_append] at hp
  have he : (satRedTM.tm.outputSymbol (satRedTM.tm.runFrom (satRedTM.tm.initCfg x) i)).toList.length = 1 := by
    simp only [MultiTapeTM.outputSymbol, hstate]
    simp only [satRedTM]
    split <;> rfl
  rw [he] at hp
  omega

/-- Intercept the proved maximum-pass endpoint and emit its unary cursor.
The earlier banked transition table is used verbatim. Its local buffer marker
is harmless inside this function computation and is erased by a later clean
call; it is never claimed to be a canonical persistent seam. -/
private def satMaxTM : FinTM Bool where
  k := 2
  State := Fin 35
  tm := {
    q₀ := satRedTM.tm.q₀
    tr := fun q inp work =>
      if q = 9 then
        if (work 0).isSome then satRedAction 0 none none .pos 0 (some true) (some 9)
        else satRedAction 0 none none 0 0 none none
      else satRedTM.tm.tr q inp work }

/-- Interception preserves the exact proved initialization and maximum pass. -/
private lemma satMax_start (φ : CNF ℕ) :
    ∃ t ≤ 3 * (CNF.serialize φ).length + 5,
      satMaxTM.tm.runFrom (satMaxTM.tm.initCfg (CNF.serialize φ)) t =
        satRedCfg (CNF.serialize φ) (some 9) 0 (Nat.zero_le _) φ.numVars
          (satRedBuffer [] 0) 0 0 [] := by
  obtain ⟨t, ht, hr⟩ := satRed_start φ
  have hg := satRed_start_guard (CNF.serialize φ) t (by rw [hr]; rfl)
  refine ⟨t, ht, ?_⟩
  have he := sat_run_agree satRedTM.tm satMaxTM.tm (satRedTM.tm.initCfg (CNF.serialize φ)) t (by
    intro i hi
    unfold MultiTapeTM.step
    cases hq : (satRedTM.tm.runFrom (satRedTM.tm.initCfg (CNF.serialize φ)) i).state with
    | none => rfl
    | some q =>
      have hq9 : q ≠ (9 : Fin 35) := by intro h; subst q; exact hg i hi hq
      simp [satMaxTM, hq9])
  exact he.trans hr

/-- Exactly `r` output transitions copy the first `r` unary cursor cells.
No native input or auxiliary buffer movement occurs during replay. -/
private lemma satMax_prefix (x : List Bool) (n : ℕ) (buf : ℤ → Option Bool) :
    ∀ r, r ≤ n → satMaxTM.tm.runFrom
      (satRedCfg x (some 9) 0 (Nat.zero_le _) n buf 0 0 []) r =
        satRedCfg x (some 9) 0 (Nat.zero_le _) n buf r 0 (List.replicate r true) := by
  intro r
  induction r with
  | zero => intro _; rfl
  | succ r ih =>
    intro hr
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (satRedCfg x (some 9) 0 (Nat.zero_le _) n buf r 0
        (List.replicate r true)).workTapeSymbols 0 = some true := by
      simp [satRedCfg, Cfg.workTapeSymbols, satRedCounter_read, show r < n by omega]
    unfold MultiTapeTM.step
    change (satMaxTM.tm.tr (9 : Fin 35) _ _).apply _ = _
    simp only [satMaxTM, ↓reduceIte, hw, Option.isSome_some]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
    · funext i z
      by_cases hi : i = 0 <;> simp [satRedAction, satRedCfg, Action.apply, hi]
    · funext i
      simp [satRedAction, satRedCfg, Action.apply]
      split <;> simp [SignType.cast]
    · simp [satRedAction, satRedCfg, Action.apply, List.replicate_succ', List.append_assoc]

/-- The first blank after the copied cursor halts without an extra bit. -/
private lemma satMax_finish (x : List Bool) (n : ℕ) (buf : ℤ → Option Bool) :
    satMaxTM.tm.runFrom (satRedCfg x (some 9) 0 (Nat.zero_le _) n buf 0 0 []) (n + 1) =
      satRedCfg x none 0 (Nat.zero_le _) n buf n 0 (List.replicate n true) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', satMax_prefix x n buf n (Nat.le_refl _)]
  have hw : (satRedCfg x (some 9) 0 (Nat.zero_le _) n buf n 0
      (List.replicate n true)).workTapeSymbols 0 = none := by
    simp [satRedCfg, Cfg.workTapeSymbols, satRedCounter_read]
  unfold MultiTapeTM.step
  change (satMaxTM.tm.tr (9 : Fin 35) _ _).apply _ = _
  simp only [satMaxTM, ↓reduceIte, hw, Option.isSome_none, Bool.false_eq_true]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z; simp [satRedAction, satRedCfg, Action.apply]
  · funext i; simp [satRedAction, satRedCfg, Action.apply]
  · simp [satRedAction, satRedCfg, Action.apply]

/-- The intercepted maximum pass computes the exact unary variable bound on
serialized formulas in linear time, using the existing maximum invariant. -/
private lemma satMax_computes (φ : CNF ℕ) :
    satMaxTM.ComputesInTime (CNF.serialize φ) (List.replicate φ.numVars true)
      (4 * (CNF.serialize φ).length + 6) := by
  obtain ⟨t, ht, hs⟩ := satMax_start φ
  have hn : φ.numVars ≤ (CNF.serialize φ).length := by
    simpa only [CNF.decode_serialize] using CNF.numVars_decode_le (CNF.serialize φ)
  have hc : satMaxTM.ComputesInTime (CNF.serialize φ) (List.replicate φ.numVars true)
      (t + (φ.numVars + 1)) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hs, satMax_finish]
    exact ⟨rfl, rfl⟩
  exact hc.mono (by omega)

/-- Canonicalization uses the full syntax test; invalid strings become the
serialization of the fixed empty-formula fallback. -/
private def satStreamCanonical (x : List Bool) : List Bool :=
  if satSyntax x then x else [false]

/-- The guard implements `serialize ∘ decode` on every input, including
trailing-data failures; it is an actual polynomial-time computation. -/
private lemma satStreamCanonical_spec (x : List Bool) :
    satStreamCanonical x = CNF.serialize (CNF.decode x) := by
  cases hp : CNF.parse x with
  | none => simp [satStreamCanonical, satSyntax_spec, CNF.decode, hp, CNF.fallback, CNF.serialize]
  | some φ => simp [satStreamCanonical, satSyntax_spec, CNF.decode, hp, sat_parse_repr hp, CNF.parse_serialize]

/-- The canonicalizer is a captured conditional over the proved full scanner. -/
private lemma satStreamCanonical_poly : PolyTimeComputable satStreamCanonical :=
  sat_pt_cond satSyntax_poly polyTimeComputable_id (sat_pt_const [false])

/-- The exact unary fresh cursor is polynomial-time computable on all strings.
**Proof sketch.** Canonicalize before running the intercepted maximum pass.
The canonical word has length at most `n+1`; compose on that certified image,
so no behavior of the maximum machine on malformed input is assumed. -/
private lemma sat_pt_numVars : PolyTimeComputable (fun x => List.replicate (CNF.decode x).numVars true) := by
  obtain ⟨M, C, e, hM⟩ := satStreamCanonical_poly
  have hu (x : List Bool) : satMaxTM.ComputesInTime (satStreamCanonical x)
      (List.replicate (CNF.decode x).numVars true) (4 * (x.length + 1) + 6) := by
    rw [satStreamCanonical_spec]
    apply (satMax_computes (CNF.decode x)).mono
    have hl : (CNF.serialize (CNF.decode x)).length ≤ x.length + 1 := by
      rw [← satStreamCanonical_spec]
      unfold satStreamCanonical
      split <;> simp <;> omega
    omega
  obtain ⟨N, hN⟩ := sat_comp_on_image M satMaxTM satStreamCanonical
    (fun x => List.replicate (CNF.decode x).numVars true)
    (fun n => C * (n + 1) ^ e) (fun n => 4 * (n + 1) + 6) hM hu
  refine ⟨N, 2 * C + 12, e + 1, fun x => (hN x).mono ?_⟩
  have he := Nat.mul_le_mul_left (2 * C)
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show e ≤ e + 1 by omega))
  have h1 : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)
  simp only [Nat.succ_eq_add_one] at he
  dsimp only
  calc
    _ = 2 * C * (x.length + 1) ^ e + 4 * (x.length + 1) + 8 := by ring
    _ ≤ 2 * C * (x.length + 1) ^ (e + 1) + 12 * (x.length + 1) ^ (e + 1) := by omega
    _ = _ := by ring

/-- The entire encoded startup word, including the invalid-input offset,
is computable before any clause emission. -/
private lemma satStreamStart_poly : PolyTimeComputable (fun x => satStreamWord (satStreamStart x)) := by
  have hv := sat_pt_pair sat_pt_numVars (sat_pt_pair (sat_pt_const []) (sat_pt_const []))
  have hf := sat_pt_pair (sat_pt_const []) (sat_pt_pair sat_pt_unaryLength (sat_pt_const []))
  have h := sat_pt_cond satSyntax_poly hv hf
  convert h using 1
  funext x
  cases hs : satSyntax x <;> simp [satStreamStart, satStreamWord, hs]

/-- A nonnegative native offset clamped at the right boundary. -/
private def satStreamPos (x : List Bool) (i : ℕ) : Fin (x.length + 2) :=
  ⟨min i x.length + 1, by omega⟩

/-- The clamped offset reads the ordinary optional list entry. -/
private lemma satStreamPos_read {k : ℕ} {S : Type} (x : List Bool)
    (c : Cfg k Bool S x) (i : ℕ) (hi : c.inputPos = satStreamPos x i) :
    c.inputSymbol = x[i]? := by
  rw [FinTM.inputSymbol_at c (min i x.length) (Nat.min_le_right _ _) (by simp [hi, satStreamPos])]
  by_cases h : i ≤ x.length
  · simp [Nat.min_eq_left h]
  · simp [Nat.min_eq_right (by omega : x.length ≤ i), List.getElem?_eq_none (by omega : x.length ≤ i)]

/-- Advancing a clamped offset agrees with an actual right-moving transition,
including repeated requests beyond the native right boundary. -/
private lemma satStreamPos_succ (x : List Bool) (i : ℕ) :
    moveInputPos (satStreamPos x i) .pos = satStreamPos x (i + 1) := by
  by_cases h : i < x.length
  · have he := moveInputPos_pos_of_ne_right (satStreamPos x i)
      (by simp [satStreamPos, Nat.min_eq_left (Nat.le_of_lt h)]; omega)
    rw [he]
    apply Fin.ext
    simp [satStreamPos, Nat.min_eq_left (Nat.le_of_lt h), Nat.min_eq_left (by omega : i + 1 ≤ x.length)]
  · have he : satStreamPos x i = ⟨x.length + 1, by omega⟩ := by
      apply Fin.ext; simp [satStreamPos, Nat.min_eq_right (by omega : x.length ≤ i)]
    rw [he, SignType.pos_eq_one, moveInputPos_rightBoundary]
    apply Fin.ext
    simp [satStreamPos, Nat.min_eq_right (by omega : x.length ≤ i + 1)]

/-- One-tape actions for a length-controlled native suffix extraction. -/
private def satDropAction (m d : SignType) (write : Option (Option Bool))
    (out : Option Bool) (q : Option (Fin 6)) : Action 1 Bool (Fin 6) :=
  ⟨m, fun _ => (write, d), out, q⟩

/-- On `pairEncode u x`, count the doubled prefix on a unary tape, rewind
that tape, skip exactly `|u|` native payload positions with clamping, then
copy the remaining suffix. No output precedes recognition of the separator. -/
private def satDropTM : FinTM Bool where
  k := 1
  State := Fin 6
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match inp with
        | some b => satDropAction .pos 0 none none (some (if b then 1 else 2))
        | none => satDropAction 0 0 none none none
      | 1 => if inp = some true then satDropAction .pos .pos (some (some true)) none (some 0)
        else satDropAction 0 0 none none none
      | 2 => if inp = some false then satDropAction .pos .pos (some (some true)) none (some 0)
        else if inp = some true then satDropAction .pos .neg none none (some 3)
        else satDropAction 0 0 none none none
      | 3 => if (work 0).isSome then satDropAction 0 .neg none none (some 3)
        else satDropAction 0 .pos none none (some 4)
      | 4 => if (work 0).isSome then satDropAction .pos .pos none none (some 4)
        else satDropAction 0 0 none none (some 5)
      | _ => match inp with
        | some b => satDropAction .pos 0 none (some b) (some 5)
        | none => satDropAction 0 0 none none none }

/-- Counter, counter head, clamped native offset, and emitted prefix. -/
private def satDropCfg (x : List Bool) (q : Option (Fin 6)) (i n : ℕ)
    (h : ℤ) (out : List Bool) : Cfg 1 Bool (Fin 6) x :=
  ⟨q, satStreamPos x i, fun _ => satRedCounter n, fun _ => h, out⟩

/-- A silent dropper action preserves the counter and makes its stated moves. -/
private lemma satDrop_move (x : List Bool) (q q' : Option (Fin 6)) (i i' n : ℕ)
    (h h' : ℤ) (m d : SignType) (b : Option Bool) (out : List Bool)
    (hm : moveInputPos (satStreamPos x i) m = satStreamPos x i') (hd : h + d.cast = h') :
    (satDropAction m d none b q').apply (satDropCfg x q i n h out) =
      satDropCfg x q' i' n h' (out ++ b.toList) := by
  refine Cfg.ext rfl hm rfl ?_ rfl
  funext t
  simpa [satDropAction, satDropCfg, Action.apply] using hd

/-- Writing the counter's right blank appends exactly one unary cell. -/
private lemma satDrop_write (x : List Bool) (q : Option (Fin 6)) (i n : ℕ) :
    (satDropAction .pos .pos (some (some true)) none (some 0)).apply
      (satDropCfg x q i n n []) = satDropCfg x (some 0) (i + 1) (n + 1) (n + 1) [] := by
  refine Cfg.ext rfl (satStreamPos_succ x i) ?_ ?_ rfl
  · funext t z
    simpa [satDropAction, satDropCfg, Action.apply, Nat.max_eq_right (Nat.le_succ n)] using
      congrFun (satRedCounter_write n n (Nat.le_refl _)) z
  · funext t; simp [satDropAction, satDropCfg, Action.apply, SignType.cast]

/-- Each aligned doubled data bit contributes one counter cell in two steps. -/
private lemma satDrop_double (x pre rest : List Bool) (b : Bool) (n : ℕ)
    (hx : x = pre ++ b :: b :: rest) :
    satDropTM.tm.runFrom (satDropCfg x (some 0) pre.length n n []) 2 =
      satDropCfg x (some 0) (pre.length + 2) (n + 1) (n + 1) [] := by
  have hread (q : Option (Fin 6)) (h : ℤ) (j : ℕ) :
      (satDropCfg x q j n h []).inputSymbol = x[j]? := satStreamPos_read x _ j rfl
  have h₁ : satDropTM.tm.step (satDropCfg x (some 0) pre.length n n []) =
      satDropCfg x (some (if b then 1 else 2)) (pre.length + 1) n n [] := by
    unfold MultiTapeTM.step
    change (satDropTM.tm.tr (0 : Fin 6) _ _).apply _ = _
    simp only [satDropTM, hread]
    rw [show x[pre.length]? = some b by simp [hx]]
    exact satDrop_move x _ _ _ _ n _ _ .pos 0 none [] (satStreamPos_succ x _) (by simp)
  have h₂ : satDropTM.tm.step
      (satDropCfg x (some (if b then 1 else 2)) (pre.length + 1) n n []) =
      satDropCfg x (some 0) (pre.length + 2) (n + 1) (n + 1) [] := by
    have hr : x[pre.length + 1]? = some b := by simp [hx]
    cases b <;> unfold MultiTapeTM.step <;>
      simp only [Bool.false_eq_true, ↓reduceIte, satDropTM, hread, hr]
    all_goals exact satDrop_write x _ (pre.length + 1) n
  change satDropTM.tm.step (satDropTM.tm.step _) = _
  rw [h₁, h₂]

/-- The doubled first component is parsed into an exact unary length counter.
**Proof sketch.** Induct on the remaining prefix data, retaining the already
counted prefix. Each aligned pair uses the two-transition lemma. -/
private lemma satDrop_parse (u v : List Bool) :
    ∀ r pre, u = pre ++ r →
      satDropTM.tm.runFrom
        (satDropCfg (pairEncode u v) (some 0) (2 * pre.length) pre.length pre.length []) (2 * r.length) =
          satDropCfg (pairEncode u v) (some 0) (2 * u.length) u.length u.length [] := by
  intro r
  induction r with
  | nil => intro pre hu; simp [hu, MultiTapeTM.runFrom_zero]
  | cons b r ih =>
    intro pre hu
    have hh : pairEncode u v = satBits pre ++ b :: b :: (satBits r ++ [false, true] ++ v) := by
      simp [hu, pairEncode, satBits, List.append_assoc]
    have hs := satDrop_double (pairEncode u v) (satBits pre) (satBits r ++ [false, true] ++ v) b pre.length hh
    simp only [satBits_length] at hs
    rw [show 2 * (b :: r).length = 2 + 2 * r.length by simp; omega,
      MultiTapeTM.runFrom_add, hs]
    have ht := ih (pre ++ [b]) (by simpa [List.append_assoc] using hu)
    simpa [List.length_append, List.length_singleton, Nat.mul_add, Nat.add_assoc] using ht

/-- The aligned `01` separator starts a leftward counter rewind while placing
the native head at the first payload bit. -/
private lemma satDrop_separator (u v : List Bool) :
    satDropTM.tm.runFrom (satDropCfg (pairEncode u v) (some 0) (2 * u.length) u.length u.length []) 2 =
      satDropCfg (pairEncode u v) (some 3) (2 * u.length + 2) u.length ((u.length : ℤ) - 1) [] := by
  have hl : (satBits u).length = 2 * u.length := satBits_length u
  have hr₀ : (pairEncode u v)[2 * u.length]? = some false := by
    rw [← hl]; simp [pairEncode, satBits]
  have hr₁ : (pairEncode u v)[2 * u.length + 1]? = some true := by
    rw [← hl]; simp [pairEncode, satBits]
  have hi (q : Option (Fin 6)) (p : ℕ) (h : ℤ) :
      (satDropCfg (pairEncode u v) q p u.length h []).inputSymbol = (pairEncode u v)[p]? :=
    satStreamPos_read _ _ _ rfl
  have hs : satDropTM.tm.step
      (satDropCfg (pairEncode u v) (some 0) (2 * u.length) u.length u.length []) =
      satDropCfg (pairEncode u v) (some 2) (2 * u.length + 1) u.length u.length [] := by
    unfold MultiTapeTM.step
    change (satDropTM.tm.tr (0 : Fin 6) _ _).apply _ = _
    simp only [satDropTM, hi, hr₀, Bool.false_eq_true, ↓reduceIte]
    exact satDrop_move _ _ _ _ _ _ _ _ .pos 0 none [] (satStreamPos_succ _ _) (by simp)
  change satDropTM.tm.step (satDropTM.tm.step _) = _
  rw [hs]
  unfold MultiTapeTM.step
  change (satDropTM.tm.tr (2 : Fin 6) _ _).apply _ = _
  simp only [satDropTM, hi, hr₁, Option.some.injEq, Bool.true_eq_false, ↓reduceIte]
  exact satDrop_move _ _ _ _ _ _ _ _ .pos .neg none [] (satStreamPos_succ _ _) (by simp; omega)

/-- Counter rewind restores its head without disturbing the payload head. -/
private lemma satDrop_rewind (x : List Bool) (p n : ℕ) :
    ∀ r, r ≤ n → satDropTM.tm.runFrom
      (satDropCfg x (some 3) p n ((r : ℤ) - 1) []) (r + 1) = satDropCfg x (some 4) p n 0 [] := by
  intro r
  induction r with
  | zero =>
    intro _
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (satDropTM.tm.tr (3 : Fin 6) _ _).apply _ = _
    have hw : (satDropCfg x (some 3) p n ((0 : ℤ) - 1) []).workTapeSymbols 0 = none := by
      simp [satDropCfg, Cfg.workTapeSymbols, satRedCounter_left]
    simp only [satDropTM, hw, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact satDrop_move _ _ _ _ _ _ _ _ 0 .pos none [] (moveInputPos_zero _) (by simp)
  | succ r ih =>
    intro hr
    have hw : (satDropCfg x (some 3) p n (((r + 1 : ℕ) : ℤ) - 1) []).workTapeSymbols 0 = some true := by
      have he : (((r + 1 : ℕ) : ℤ) - 1) = r := by omega
      simp [satDropCfg, Cfg.workTapeSymbols, he, satRedCounter_read, show r < n by omega]
    have hs : satDropTM.tm.step (satDropCfg x (some 3) p n (((r + 1 : ℕ) : ℤ) - 1) []) =
        satDropCfg x (some 3) p n ((r : ℤ) - 1) [] := by
      unfold MultiTapeTM.step
      change (satDropTM.tm.tr (3 : Fin 6) _ _).apply _ = _
      simp only [satDropTM, hw, Option.isSome_some, ↓reduceIte]
      exact satDrop_move _ _ _ _ _ _ _ _ 0 .neg none [] (moveInputPos_zero _) (by simp; omega)
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]

/-- The unary counter moves the payload head by its stored length. Native
clamping makes this total even when the stored length exceeds the payload. -/
private lemma satDrop_skip (x : List Bool) (p n : ℕ) :
    ∀ r, r ≤ n → satDropTM.tm.runFrom (satDropCfg x (some 4) p n 0 []) r =
      satDropCfg x (some 4) (p + r) n r [] := by
  intro r
  induction r with
  | zero => intro _; simp [MultiTapeTM.runFrom_zero]
  | succ r ih =>
    intro hr
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (satDropCfg x (some 4) (p + r) n r []).workTapeSymbols 0 = some true := by
      simp [satDropCfg, Cfg.workTapeSymbols, satRedCounter_read, show r < n by omega]
    unfold MultiTapeTM.step
    change (satDropTM.tm.tr (4 : Fin 6) _ _).apply _ = _
    simp only [satDropTM, hw, Option.isSome_some, ↓reduceIte]
    simpa only [Nat.add_assoc] using satDrop_move x (some 4) (some 4) (p + r) (p + r + 1)
      n (r : ℤ) ((r + 1 : ℕ) : ℤ) .pos .pos none [] (satStreamPos_succ _ _) (by simp)

/-- Counter exhaustion dispatches to the native copy phase without moving
past the first unconsumed payload bit. -/
private lemma satDrop_dispatch (x : List Bool) (p n : ℕ) :
    satDropTM.tm.step (satDropCfg x (some 4) p n n []) = satDropCfg x (some 5) p n n [] := by
  have hw : (satDropCfg x (some 4) p n n []).workTapeSymbols 0 = none := by
    simp [satDropCfg, Cfg.workTapeSymbols, satRedCounter_read]
  unfold MultiTapeTM.step
  change (satDropTM.tm.tr (4 : Fin 6) _ _).apply _ = _
  simp only [satDropTM, hw, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  exact satDrop_move _ _ _ _ _ _ _ _ 0 0 none [] (moveInputPos_zero _) (by simp)

/-- The dropper copies exactly the remaining native suffix and then halts. -/
private lemma satDrop_copy (x rest : List Bool) (n : ℕ) :
    ∀ pre out, x = pre ++ rest →
      satDropTM.tm.runFrom (satDropCfg x (some 5) pre.length n n out) (rest.length + 1) =
        satDropCfg x none x.length n n (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    have he : x = pre := by simpa using hx
    clear hx
    subst x
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (satDropTM.tm.tr (5 : Fin 6) _ _).apply _ = _
    have hin : (satDropCfg pre (some 5) pre.length n n out).inputSymbol = none := by
      rw [satStreamPos_read _ _ _ rfl]; simp
    simp only [satDropTM, hin]
    simpa using satDrop_move _ _ _ _ _ _ _ _ 0 0 none out (moveInputPos_zero _) (by simp)
  | cons b rest ih =>
    intro pre out hx
    have hs : satDropTM.tm.step (satDropCfg x (some 5) pre.length n n out) =
        satDropCfg x (some 5) (pre ++ [b]).length n n (out ++ [b]) := by
      unfold MultiTapeTM.step
      change (satDropTM.tm.tr (5 : Fin 6) _ _).apply _ = _
      have hin : (satDropCfg x (some 5) pre.length n n out).inputSymbol = some b := by
        rw [satStreamPos_read _ _ _ rfl]; simp [hx]
      simp only [satDropTM, hin]
      simpa using satDrop_move x (some 5) (some 5) pre.length (pre.length + 1)
        n (n : ℤ) (n : ℤ) .pos 0 (some b) out (satStreamPos_succ _ _) (by simp)
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa [List.append_assoc] using ih (pre ++ [b]) (out ++ [b])
      (by simpa [List.append_assoc] using hx)

/-- Uniform linear-time suffix extraction from a valid length/data pair.
**Proof sketch.** Parse the doubled prefix, recognize the separator, rewind
its unary counter, and advance once per counter cell. Clamping equates that
endpoint to the split at `min |u| |v|`. Copy the remaining suffix; all earlier
stages are silent, and their lengths sum to the displayed linear envelope. -/
private lemma satDrop_computes (u v : List Bool) :
    satDropTM.ComputesInTime (pairEncode u v) (v.drop u.length)
      (3 * ((pairEncode u v).length + 1)) := by
  let x := pairEncode u v
  let p := 2 * u.length + 2
  let pre := satBits u ++ [false, true] ++ v.take u.length
  have hx : x = pre ++ v.drop u.length := by
    simp [x, pre, pairEncode, satBits, List.append_assoc]
  have hxlen : x.length = p + v.length := by
    change (satBits u ++ [false, true] ++ v).length = _
    simp [p, satBits_length] <;> omega
  have hpre : pre.length = p + min u.length v.length := by simp [pre, p, satBits_length]; omega
  have hpos : satStreamPos x (p + u.length) = satStreamPos x pre.length := by
    apply Fin.ext
    simp only [satStreamPos, hxlen, hpre]
    by_cases h : u.length ≤ v.length
    · simp [Nat.min_eq_left h, Nat.min_eq_left (Nat.add_le_add_left h p)]
    · simp [Nat.min_eq_right (by omega : v.length ≤ u.length),
        Nat.min_eq_right (by omega : p + v.length ≤ p + u.length)]
  have hinit : satDropTM.tm.initCfg x = satDropCfg x (some 0) 0 0 0 [] := by
    refine Cfg.ext rfl ?_ ?_ rfl rfl
    · apply Fin.ext; simp [satDropCfg, satStreamPos, MultiTapeTM.initCfg, Cfg.init]
    · funext i z; simp [satDropCfg, satRedCounter, MultiTapeTM.initCfg, Cfg.init, FinTM.bufferTape]
  have hparse := satDrop_parse u v u [] (by simp)
  simp only [List.length_nil, Nat.mul_zero, Int.natCast_zero] at hparse
  have hstart : satDropTM.tm.runFrom (satDropTM.tm.initCfg x)
      (2 * u.length + 2 + (u.length + 1) + u.length + 1) =
        satDropCfg x (some 5) pre.length u.length u.length [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_add _ (2 * u.length + 2) (u.length + 1),
      MultiTapeTM.runFrom_add _ (2 * u.length) 2, hinit, hparse,
      satDrop_separator, satDrop_rewind _ _ _ u.length (Nat.le_refl _),
      satDrop_skip _ _ _ u.length (Nat.le_refl _), satDrop_dispatch]
    exact Cfg.ext rfl hpos rfl rfl rfl
  have hcopy := satDrop_copy x (v.drop u.length) u.length pre [] hx
  have hc : satDropTM.ComputesInTime x (v.drop u.length)
      (2 * u.length + 2 + (u.length + 1) + u.length + 1 + ((v.drop u.length).length + 1)) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hcopy]
    exact ⟨rfl, rfl⟩
  apply hc.mono
  change _ ≤ 3 * (x.length + 1)
  rw [hxlen, List.length_drop]
  dsimp only [p]
  omega

/-- Both total field projections are polynomial-time catalog operations. -/
private lemma sat_pt_fields : PolyTimeComputable satStreamFst ∧ PolyTimeComputable satStreamSnd :=
  ⟨sat_pt_linear _ FinTM.computesFunInTime_pairFst,
    sat_pt_linear _ FinTM.computesFunInTime_pairSnd⟩

/-- Suffix extraction is polynomial on every word, with malformed pair
inputs interpreted through the two empty-default projections.
**Proof sketch.** Re-encode the two projections, then use the native dropper
only on that valid-pair image. The re-encoder's proved output bound pays for
the linear dropper run and gives a polynomial original-input envelope. -/
private lemma sat_pt_drop : PolyTimeComputable
    (fun z => (satStreamSnd z).drop (satStreamFst z).length) := by
  let f (z : List Bool) := pairEncode (satStreamFst z) (satStreamSnd z)
  obtain ⟨M, C, e, hM⟩ := sat_pt_pair sat_pt_fields.1 sat_pt_fields.2
  have hlen (z : List Bool) : (f z).length ≤ C * (z.length + 1) ^ e := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM z)).2
    simpa only [ho, f] using M.tm.output_length_le z (C * (z.length + 1) ^ e)
  have hu (z : List Bool) : satDropTM.ComputesInTime (f z)
      ((satStreamSnd z).drop (satStreamFst z).length) (3 * (C * (z.length + 1) ^ e + 1)) :=
    (satDrop_computes _ _).mono (Nat.mul_le_mul_left 3 (Nat.add_le_add_right (hlen z) 1))
  obtain ⟨N, hN⟩ := sat_comp_on_image M satDropTM f
    (fun z => (satStreamSnd z).drop (satStreamFst z).length)
    (fun n => C * (n + 1) ^ e) (fun n => 3 * (C * (n + 1) ^ e + 1)) hM hu
  refine ⟨N, 5 * C + 5, e, fun z => (hN z).mono ?_⟩
  have h1 : 1 ≤ (z.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  dsimp only
  calc
    _ = 5 * C * (z.length + 1) ^ e + 5 := by ring
    _ ≤ 5 * C * (z.length + 1) ^ e + 5 * (z.length + 1) ^ e := by omega
    _ = _ := by ring

/-- The unary-token catalog agrees with the literal serializer's delimiter;
the polarity bit remains the first bit of the returned suffix. -/
private lemma satToken_literal (l : Std.Sat.Literal ℕ) (r : List Bool) :
    unaryTokenSplit (CNF.serializeLit l ++ r) =
      (List.replicate (l.1 + 1) true ++ [false], l.2 :: r) := by
  have ht (k : ℕ) : unaryTokenSplit (List.replicate k true ++ false :: l.2 :: r) =
      (List.replicate k true ++ [false], l.2 :: r) := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, unaryTokenSplit, ih]
  simpa [CNF.serializeLit, List.append_assoc] using ht (l.1 + 1)

/-- The token splitter removes just the first delimiter after the true run;
the residual true-run suffix never starts with another true. -/
private lemma satToken_shape (x : List Bool) :
    unaryTokenSplit x =
      (List.replicate (CNF.takeTrues x).1 true ++ (CNF.takeTrues x).2.take 1,
        (CNF.takeTrues x).2.tail) ∧ (CNF.takeTrues x).2.head? ≠ some true := by
  induction x with
  | nil => simp [unaryTokenSplit, CNF.takeTrues]
  | cons b x ih =>
    cases b with
    | false => simp [unaryTokenSplit, CNF.takeTrues]
    | true => simpa [unaryTokenSplit, CNF.takeTrues, ih.1, List.replicate_succ] using ih.2

/-- At a literal marker, a failed literal parse means the token splitter has
no polarity bit. This keeps the total round implementation faithful even on
locally malformed state/input combinations. -/
private lemma satToken_failure (r : List Bool) (hp : CNF.parseLit (true :: r) = none) :
    (unaryTokenSplit (true :: r)).2 = [] := by
  have hs := satToken_shape r
  have ht := (satToken_shape (true :: r)).1
  cases he : CNF.takeTrues r with
  | mk k tail =>
    simp only [he] at hs
    cases tail with
    | nil => simp [ht, CNF.takeTrues, he]
    | cons b rest =>
      cases b with
      | true => exact False.elim (hs.2 rfl)
      | false =>
        cases rest with
        | nil => simp [ht, CNF.takeTrues, he]
        | cons c rest => simp [CNF.parseLit, CNF.takeTrues, he] at hp

/-- Round requests pair the persistent state with a fresh copy of native
input. These projections are read-only word operations. -/
private def satReqFresh (z : List Bool) := satStreamFst (satStreamFst z)
private def satReqUsed (z : List Bool) := satStreamFst (satStreamSnd (satStreamFst z))
private def satReqPhase (z : List Bool) := satStreamSnd (satStreamSnd (satStreamFst z))
private def satReqRest (z : List Bool) := (satStreamSnd z).drop (satReqUsed z).length
private def satReqPol (z : List Bool) := (unaryTokenSplit (satReqRest z)).2
private def satReqLit (z : List Bool) :=
  (unaryTokenSplit (satReqRest z)).1 ++ (satReqPol z).take 1
private def satReqLink (z : List Bool) : Bool :=
  decide (satReqPhase z = List.replicate 3 true) && decide ((satReqPol z).tail.take 1 = [true])

/-- Pair the three canonical fields without any round-local scratch. -/
private def satReqPack (j p : List Bool) (q : ℕ) : List Bool :=
  pairEncode j (pairEncode p (List.replicate q true))

/-- The one larger tail chunk is the audited positive link, two clause
markers, negative link, and the consumed original literal, in that order. -/
private def satReqFragment (z : List Bool) : List Bool :=
  (true :: satReqFresh z) ++ [false, true] ++ [false, true] ++
    (true :: satReqFresh z) ++ [false, false] ++ satReqLit z

/-- A total straight-line word implementation of the round's emitted chunk.
Validation of a complete formula belongs to startup; these local tests only
implement the grammar phase and complete-literal lookahead. -/
private def satReqEmit (z : List Bool) : List Bool :=
  if satReqPhase z = List.replicate 4 true then [] else
  if (satReqRest z).take 1 = [] then [false] else
  if (satReqRest z).take 1 = [false] then [false] else
  if satReqPhase z = [] then [true] else
  if satReqPol z = [] then [] else
  if satReqLink z then satReqFragment z else satReqLit z

/-- The same local tests install the next encoded state. Offset advancement
uses the entire literal length; a fresh allocation happens only on a tail link. -/
private def satReqStep (z : List Bool) : List Bool :=
  let j := satReqFresh z
  let p := satReqUsed z
  let p' := p ++ List.replicate (satReqLit z).length true
  if satReqPhase z = List.replicate 4 true then satStreamFst z else
  if (satReqRest z).take 1 = [] then satReqPack j p 4 else
  if (satReqRest z).take 1 = [false] then
    if satReqPhase z = [] then satReqPack j (p ++ [true]) 4 else satReqPack j (p ++ [true]) 0
  else if satReqPhase z = [] then satReqPack j (p ++ [true]) 1 else
  if satReqPol z = [] then satReqPack j p 4 else
  if satReqLink z then satReqPack (j ++ [true]) p' 3 else
  if satReqPhase z = [true] then satReqPack j p' 2 else satReqPack j p' 3

/-- First-bit word equality and optional-head equality coincide. -/
private lemma sat_take_one_true (x : List Bool) : x.take 1 = [true] ↔ x.head? = some true := by
  cases x <;> simp

/-- Every field of a canonical round request is recovered exactly. -/
private lemma satReq_fields (x : List Bool) (s : SatStreamState) :
    satReqFresh (pairEncode (satStreamWord s) x) = List.replicate s.fresh true ∧
    satReqUsed (pairEncode (satStreamWord s) x) = List.replicate s.used true ∧
    satReqPhase (pairEncode (satStreamWord s) x) = List.replicate s.phase.val true ∧
    satReqRest (pairEncode (satStreamWord s) x) = x.drop s.used := by
  simp [satReqFresh, satReqUsed, satReqPhase, satReqRest, satStreamWord,
    satStreamFst, satStreamSnd, pairDecode_pairEncode]

/-- The word program implements exactly the normalized round, on every
canonical state (not only reachable states).
**Proof sketch.** Split by the phase and the next input item. For a literal,
the token round trip identifies the buffered word and lookahead; if parsing
fails there is no polarity bit. Unary concatenation implements counter
addition. The tail-link branch is precisely the prescribed chunk table. -/
private lemma satReq_round (x : List Bool) (s : SatStreamState) :
    satReqStep (pairEncode (satStreamWord s) x) = satStreamWord (satStreamRound x s).1 ∧
    satReqEmit (pairEncode (satStreamWord s) x) = (satStreamRound x s).2 := by
  obtain ⟨hj, hu, hq, hr⟩ := satReq_fields x s
  cases s with
  | mk j p q =>
    dsimp only at hj hu hq hr
    by_cases h4 : q = 4
    · subst q
      simp [satReqStep, satReqEmit, satReqPhase, satStreamFst, satStreamSnd,
        satStreamWord, pairDecode_pairEncode, satStreamRound]
    · cases hd : x.drop p with
      | nil =>
        simp only [satReqStep, satReqEmit, hj, hu, hq, hr, hd]
        fin_cases q <;> simp_all [satReqPack, satStreamWord, satStreamRound,
          satReqFresh, satReqUsed, satReqPhase, satReqRest, satStreamFst, satStreamSnd,
          pairDecode_pairEncode, List.drop_eq_nil_of_le]
      | cons b r =>
        cases b with
        | false =>
          fin_cases q <;> simp_all [satReqStep, satReqEmit, satReqPack, satStreamWord,
            satStreamRound, List.replicate_succ', List.replicate_succ]
        | true =>
          by_cases h0 : q = 0
          · subst q
            simp only [satReqStep, satReqEmit, hj, hu, hq, hr, hd]
            simp [satReqPack, satStreamWord, satStreamRound, hd, List.replicate_succ']
          · cases hp : CNF.parseLit (true :: r) with
            | none =>
              have hpol : satReqPol (pairEncode (satStreamWord ⟨j, p, q⟩) x) = [] := by
                simp only [satReqPol, hr, hd]
                exact satToken_failure r hp
              fin_cases q <;> simp_all [satReqStep, satReqEmit, satReqPack, satStreamWord, satStreamRound]
            | some lr =>
              rcases lr with ⟨l, rest⟩
              have hrepr := sat_parseLit_repr hp
              have htok := satToken_literal l rest
              rw [← hrepr] at htok
              have hpol : satReqPol (pairEncode (satStreamWord ⟨j, p, q⟩) x) = l.2 :: rest := by
                simp [satReqPol, hr, hd, htok]
              have hlit : satReqLit (pairEncode (satStreamWord ⟨j, p, q⟩) x) = CNF.serializeLit l := by
                simp [satReqLit, hr, hd, htok, hpol, CNF.serializeLit]
              by_cases hnext : rest.head? = some true <;>
                fin_cases q <;> simp_all [satReqStep, satReqEmit, satReqPack, satReqLink, satReqFragment,
                satStreamWord, satStreamRound, sat_take_one_true, List.replicate_add,
                CNF.serializeLit, List.replicate_succ, List.append_assoc] <;>
                rw [← List.replicate_succ', List.replicate_succ]

/-- All read-only request fields and the literal token are polynomial-time
computations, using the audited splitter and the proved native suffix reader. -/
private lemma satReq_fields_poly :
    PolyTimeComputable satReqFresh ∧ PolyTimeComputable satReqUsed ∧
    PolyTimeComputable satReqPhase ∧ PolyTimeComputable satReqRest ∧
    PolyTimeComputable satReqPol ∧ PolyTimeComputable satReqLit := by
  have hj : PolyTimeComputable satReqFresh := sat_pt_fields.1.comp sat_pt_fields.1
  have hu : PolyTimeComputable satReqUsed := sat_pt_fields.1.comp (sat_pt_fields.2.comp sat_pt_fields.1)
  have hq : PolyTimeComputable satReqPhase := sat_pt_fields.2.comp (sat_pt_fields.2.comp sat_pt_fields.1)
  have hr : PolyTimeComputable satReqRest := by
    simpa only [Function.comp_def, satStreamFst, satStreamSnd, pairDecode_pairEncode,
      Option.map_some, Option.getD_some, satReqRest] using
      sat_pt_drop.comp (sat_pt_pair hu sat_pt_fields.2)
  have ht : PolyTimeComputable (fun z => pairEncode (unaryTokenSplit (satReqRest z)).1
      (unaryTokenSplit (satReqRest z)).2) :=
    (sat_pt_linear _ FinTM.computesFunInTime_unaryToken).comp hr
  have hp : PolyTimeComputable satReqPol := by
    simpa only [Function.comp_def, satStreamSnd, pairDecode_pairEncode, Option.map_some,
      Option.getD_some, satReqPol] using sat_pt_fields.2.comp ht
  have hf : PolyTimeComputable (fun z => (unaryTokenSplit (satReqRest z)).1) := by
    simpa only [Function.comp_def, satStreamFst, pairDecode_pairEncode, Option.map_some,
      Option.getD_some] using sat_pt_fields.1.comp ht
  exact ⟨hj, hu, hq, hr, hp, sat_pt_append hf (sat_pt_head.comp hp)⟩

/-- Canonical field packing preserves polynomial time for every fixed tag. -/
private lemma sat_pt_pack {j p : List Bool → List Bool} (hj : PolyTimeComputable j)
    (hp : PolyTimeComputable p) (q : ℕ) : PolyTimeComputable (fun z => satReqPack (j z) (p z) q) :=
  sat_pt_pair hj (sat_pt_pair hp (sat_pt_const _))

/-- The Boolean tail-link decision is a conjunction of two finite-word tests. -/
private lemma satReqLink_poly : PolyTimeComputable (fun z => [satReqLink z]) := by
  obtain ⟨_, _, hq, _, hp, _⟩ := satReq_fields_poly
  exact sat_pt_and (sat_pt_eq hq _) (sat_pt_eq (sat_pt_head.comp (sat_pt_tail.comp hp)) [true])

/-- The tail fragment is built by a fixed number of polynomial concatenations. -/
private lemma satReqFragment_poly : PolyTimeComputable satReqFragment := by
  obtain ⟨hj, _, _, _, _, hl⟩ := satReq_fields_poly
  have hvar : PolyTimeComputable (fun z => true :: satReqFresh z) :=
    (sat_pt_linear _ (FinTM.computesFunInTime_prepend [true])).comp hj
  exact sat_pt_append (sat_pt_append (sat_pt_append
    (sat_pt_append (sat_pt_append hvar (sat_pt_const [false, true]))
      (sat_pt_const [false, true])) hvar) (sat_pt_const [false, false])) hl

/-- The per-round output chunk has an actual polynomial-time finite-machine
witness, including empty finished chunks and the invalid-input fallback. -/
private lemma satReqEmit_poly : PolyTimeComputable satReqEmit := by
  obtain ⟨_, _, hq, hr, hp, hl⟩ := satReq_fields_poly
  have hh := sat_pt_head.comp hr
  have h := sat_pt_cond (sat_pt_eq hq (List.replicate 4 true)) (sat_pt_const [])
    (sat_pt_cond (sat_pt_eq hh []) (sat_pt_const [false])
      (sat_pt_cond (sat_pt_eq hh [false]) (sat_pt_const [false])
        (sat_pt_cond (sat_pt_eq hq []) (sat_pt_const [true])
          (sat_pt_cond (sat_pt_eq hp []) (sat_pt_const [])
            (sat_pt_cond satReqLink_poly satReqFragment_poly hl)))))
  simpa only [satReqEmit, Function.comp_def, decide_eq_true_eq] using h

/-- The next persistent state also has an actual polynomial-time witness;
all branch tests are computed and captured on the original round request. -/
private lemma satReqStep_poly : PolyTimeComputable satReqStep := by
  obtain ⟨hj, hu, hq, hr, hp, hl⟩ := satReq_fields_poly
  have hu1 := sat_pt_append hu (sat_pt_const [true])
  have hj1 := sat_pt_append hj (sat_pt_const [true])
  have hul := sat_pt_append hu (sat_pt_unaryLength.comp hl)
  have hh := sat_pt_head.comp hr
  have h := sat_pt_cond (sat_pt_eq hq (List.replicate 4 true)) sat_pt_fields.1
    (sat_pt_cond (sat_pt_eq hh []) (sat_pt_pack hj hu 4)
      (sat_pt_cond (sat_pt_eq hh [false])
        (sat_pt_cond (sat_pt_eq hq []) (sat_pt_pack hj hu1 4) (sat_pt_pack hj hu1 0))
        (sat_pt_cond (sat_pt_eq hq []) (sat_pt_pack hj hu1 1)
          (sat_pt_cond (sat_pt_eq hp []) (sat_pt_pack hj hu 4)
            (sat_pt_cond satReqLink_poly (sat_pt_pack hj1 hul 3)
              (sat_pt_cond (sat_pt_eq hq [true]) (sat_pt_pack hj hul 2) (sat_pt_pack hj hul 3)))))))
  simpa only [satReqStep, Function.comp_def, decide_eq_true_eq] using h

/-- A marker-free administrative pass appends the native input to tape zero,
then rewinds both heads. It is used to form a round request and at startup.
The only occupied tape is the data tape; no origin marker is introduced. -/
private def satAppendTM : FinTM Bool where
  k := 1
  State := Fin 5
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => if (work 0).isSome then ⟨0, fun _ => (none, .pos), none, some 0⟩
        else ⟨0, fun _ => (none, 0), none, some 1⟩
      | 1 => match inp with
        | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 1⟩
        | none => ⟨0, fun _ => (none, .neg), none, some 2⟩
      | 2 => if (work 0).isSome then ⟨0, fun _ => (none, .neg), none, some 2⟩
        else ⟨0, fun _ => (none, .pos), none, some 3⟩
      | 3 => FinTM.controlAction .neg (some 4)
      | _ => match inp with
        | some _ => FinTM.controlAction .neg (some 4)
        | none => FinTM.controlAction .pos none }

/-- The appender's complete configuration, with no hidden scratch. -/
private def satAppendCfg (x : List Bool) (q : Option (Fin 5))
    (i : Fin (x.length + 2)) (w : List Bool) (h : ℤ) : Cfg 1 Bool (Fin 5) x :=
  ⟨q, i, fun _ => FinTM.bufferTape w, fun _ => h, []⟩

/-- Seek the first blank after a known word, without moving the native head.
**Proof sketch.** Each occupied cell advances once; the right blank dispatches
in one further transition. -/
private lemma satAppend_seek (x w rest : List Bool) :
    ∀ pre, w = pre ++ rest → satAppendTM.tm.runFrom
      (satAppendCfg x (some 0) 1 w pre.length) (rest.length + 1) =
        satAppendCfg x (some 1) 1 w w.length := by
  induction rest with
  | nil =>
    intro pre hw
    have he : w = pre := by simpa using hw
    subst w
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (satAppendTM.tm.tr (0 : Fin 5) _ _).apply _ = _
    simp [satAppendTM, satAppendCfg, Cfg.workTapeSymbols, Action.apply]
  | cons b rest ih =>
    intro pre hw
    have hs : satAppendTM.tm.step (satAppendCfg x (some 0) 1 w pre.length) =
        satAppendCfg x (some 0) 1 w (pre ++ [b]).length := by
      unfold MultiTapeTM.step
      change (satAppendTM.tm.tr (0 : Fin 5) _ _).apply _ = _
      have hr : (satAppendCfg x (some 0) 1 w pre.length).workTapeSymbols 0 = some b := by
        simp [satAppendCfg, Cfg.workTapeSymbols, hw]
      simp only [satAppendTM]
      rw [hr]
      simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg, add_assoc]
    rw [show (b :: rest).length + 1 = (rest.length + 1) + 1 by simp,
      MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (pre ++ [b]) (by simpa [List.append_assoc] using hw)

/-- Native copying appends at the right blank and enters the work-tape rewind.
**Proof sketch.** The append lemma identifies the full infinite tape after
each write; clamped native positions advance through the remaining suffix. -/
private lemma satAppend_copy (x w rest : List Bool) :
    ∀ pre, x = pre ++ rest → satAppendTM.tm.runFrom
      (satAppendCfg x (some 1) (satStreamPos x pre.length) (w ++ pre) (w ++ pre).length)
      (rest.length + 1) =
        satAppendCfg x (some 2) (satStreamPos x x.length) (w ++ x) ((w ++ x).length - 1) := by
  induction rest with
  | nil =>
    intro pre hx
    have he : x = pre := by simpa using hx
    clear hx
    subst x
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    have hr := satStreamPos_read pre (satAppendCfg pre (some 1)
      (satStreamPos pre pre.length) (w ++ pre) (w ++ pre).length) pre.length rfl
    unfold MultiTapeTM.step
    change (satAppendTM.tm.tr (1 : Fin 5) _ _).apply _ = _
    simp only [satAppendTM, hr, List.getElem?_length]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i
    simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg, add_assoc]
  | cons b rest ih =>
    intro pre hx
    have hs : satAppendTM.tm.step
        (satAppendCfg x (some 1) (satStreamPos x pre.length) (w ++ pre) (w ++ pre).length) =
        satAppendCfg x (some 1) (satStreamPos x (pre ++ [b]).length)
          (w ++ (pre ++ [b])) (w ++ (pre ++ [b])).length := by
      have hr : (satAppendCfg x (some 1) (satStreamPos x pre.length)
          (w ++ pre) (w ++ pre).length).inputSymbol = some b := by
        rw [satStreamPos_read x _ pre.length rfl]
        simp [hx]
      unfold MultiTapeTM.step
      change (satAppendTM.tm.tr (1 : Fin 5) _ _).apply _ = _
      simp only [satAppendTM, hr, List.getElem?_cons_zero]
      refine Cfg.ext rfl ?_ ?_ ?_ rfl
      · simpa using satStreamPos_succ x pre.length
      · funext i
        simpa [satAppendCfg, Action.apply, List.append_assoc] using
          (FinTM.bufferTape_append (w ++ pre) b).symm
      · funext i; simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg, add_assoc]
    rw [show (b :: rest).length + 1 = (rest.length + 1) + 1 by simp,
      MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (pre ++ [b]) (by simpa [List.append_assoc] using hx)

/-- Rewind exactly the occupied prefix, using its left blank only locally.
**Proof sketch.** Induction on the number of cells to the left of the head;
the blank at minus one is never written, and the final head is zero. -/
private lemma satAppend_rewind (x w : List Bool) (i : Fin (x.length + 2)) :
    ∀ r, r ≤ w.length → satAppendTM.tm.runFrom
      (satAppendCfg x (some 2) i w ((r : ℤ) - 1)) (r + 1) =
        satAppendCfg x (some 3) i w 0 := by
  intro r
  induction r with
  | zero =>
    intro _
    simp only [Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (satAppendTM.tm.tr (2 : Fin 5) _ _).apply _ = _
    have hr : (satAppendCfg x (some 2) i w ((0 : ℤ) - 1)).workTapeSymbols 0 = none := by
      simp [satAppendCfg, Cfg.workTapeSymbols, FinTM.bufferTape]
    simp only [satAppendTM]
    simp only [Nat.cast_zero]
    rw [hr]
    simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg, add_assoc]
  | succ r ih =>
    intro hr
    have hs : satAppendTM.tm.step (satAppendCfg x (some 2) i w (((r + 1 : ℕ) : ℤ) - 1)) =
        satAppendCfg x (some 2) i w ((r : ℤ) - 1) := by
      have hw : ((satAppendCfg x (some 2) i w (((r + 1 : ℕ) : ℤ) - 1)).workTapeSymbols 0).isSome = true := by
        simp [satAppendCfg, Cfg.workTapeSymbols, FinTM.bufferTape_nat, List.getElem?_eq_getElem (by omega : r < w.length)]
      unfold MultiTapeTM.step
      change (satAppendTM.tm.tr (2 : Fin 5) _ _).apply _ = _
      simp only [satAppendTM]
      rw [hw]
      simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg, add_assoc]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- A padded halting run can be cut at its first halt without changing any
endpoint field. This is the local instance of the engine's minimal-halt
argument: use `Nat.find` and the absorbing-halt law. -/
private lemma sat_call_first_halt {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧ (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, fun v hv => Nat.find_min h hv, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hu]

/-- The appender has a full clean return, in linear time in the native input
and existing word. Both input and work heads return to their canonical origins.
**Proof sketch.** Compose seek, copy, work rewind, and the audited native
rewind. Choose the first halt so forwarding wrappers may use the run directly. -/
private lemma satAppend_clean (x w : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 2 * w.length + 3 * x.length + 6 ∧
      (∀ v < t, ¬(satAppendTM.tm.runFrom
        (Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 w)) v).Halted) ∧
      satAppendTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 w)) t =
        { Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 (w ++ x)) with state := none } := by
  have hs := satAppend_seek x w w [] (by simp)
  have hc := satAppend_copy x w x [] (by simp)
  have hr := satAppend_rewind x (w ++ x) (satStreamPos x x.length) (w ++ x).length (Nat.le_refl _)
  obtain ⟨r, hb, hn⟩ := FinTM.timed_rewind satAppendTM.tm (3 : Fin 5) (4 : Fin 5) none
    (by intros; rfl) (by intro inp work; cases inp <;> rfl)
    (satAppendCfg x (some 3) (satStreamPos x x.length) (w ++ x) 0) rfl
  have hi : Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 w) = satAppendCfg x (some 0) 1 w 0 := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i; fin_cases i; rfl
  have he : satAppendTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 w))
      (w.length + 1 + (x.length + 1) + ((w ++ x).length + 1) + r) =
      { Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 (w ++ x)) with state := none } := by
    rw [hi, MultiTapeTM.runFrom_add _ _ r,
      MultiTapeTM.runFrom_add _ _ ((w ++ x).length + 1),
      MultiTapeTM.runFrom_add _ (w.length + 1) (x.length + 1)]
    simp only [List.length_nil, Nat.cast_zero] at hs
    rw [hs]
    have hp : satStreamPos x 0 = 1 := by apply Fin.ext; simp [satStreamPos]
    simp only [List.length_nil, List.append_nil, hp] at hc
    rw [hc, hr, hn]
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i; fin_cases i; rfl
  obtain ⟨u, hu, hut, hg, heq⟩ := sat_call_first_halt satAppendTM.tm
    (Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 w)) _ (by simp [Cfg.ofWords])
    (by rw [he])
  refine ⟨u, hu, ?_, hg, heq.trans he⟩
  simp only [satAppendCfg, satStreamPos, Nat.min_self] at hb
  simp only [List.length_append] at hut
  omega

/-- Pad a callable module into a shared bank, keeping unused tapes stationary. -/
private def satPadAction {k K : ℕ} {S : Type} (a : Action k Bool S) : Action K Bool S :=
  ⟨a.inputTape, fun i => if h : i.val < k then a.workTapes ⟨i.val, h⟩ else (none, 0),
    a.output, a.state⟩

/-- All modules share tape zero; a positive source bank is padded on the right. -/
private def satPadTM (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K) : FinTM Bool where
  k := K
  State := M.State
  tm := { q₀ := M.tm.q₀
          tr := fun q inp work => satPadAction (M.tm.tr q inp
            (fun i => work ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)) }

/-- Configuration embedding for the shared bank; the padding is genuinely blank. -/
private def satPadCfg {k K : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Cfg K Bool S x :=
  ⟨c.state, c.inputPos,
    fun i => if h : i.val < k then c.workTapes ⟨i.val, h⟩ else fun _ => none,
    fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩

/-- Padding commutes with a transition, including writes at arbitrary cells.
**Proof sketch.** Split each work index by membership in the source bank;
the inactive branch neither writes nor moves. -/
private lemma satPad_apply {k K : ℕ} {S : Type} {x : List Bool}
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    (satPadAction (K := K) a).apply (satPadCfg c) = satPadCfg (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases h : i.val < k <;> simp [satPadAction, satPadCfg, Action.apply, h]
  · funext i
    by_cases h : i.val < k <;> simp [satPadAction, satPadCfg, Action.apply, h]

/-- The padded source observes exactly its original work symbols. -/
private lemma satPad_run (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K)
    {x : List Bool} (c : Cfg M.k Bool M.State x) (t : ℕ) :
    (satPadTM M K hk).tm.runFrom (satPadCfg c) t = satPadCfg (M.tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro c
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, satPadCfg, hs]
  | some q =>
    have hw : (fun i : Fin M.k => (satPadCfg (K := K) c).workTapeSymbols
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i; simp [satPadCfg, Cfg.workTapeSymbols, i.isLt]
    have hstate : (satPadCfg (K := K) c).state = some q := hs
    simp only [MultiTapeTM.step, hstate, hs]
    change (satPadAction (M.tm.tr q c.inputSymbol _)).apply _ = _
    rw [hw]
    exact satPad_apply _ _

/-- Positive tape count makes the padded seam the same canonical state word. -/
private lemma satPad_seam {k K : ℕ} {S : Type} {x : List Bool}
    (hk : 0 < k) (q : S) (w out : List Bool) :
    satPadCfg (K := K) ({Cfg.ofWords (input := x) q (stateWord k w) with output := out}) =
      {Cfg.ofWords (input := x) q (stateWord K w) with output := out} := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : i.val < k
    · simp [satPadCfg, Cfg.ofWords, stateWord, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [satPadCfg, Cfg.ofWords, stateWord, hi, hn, FinTM.bufferTape]
  · funext i
    by_cases hi : i.val < k <;> simp [satPadCfg, Cfg.ofWords, hi]

/-- Convert a first-positive-exit module into a halting source for `emit_run`.
The Boolean release flag ensures even an entry equal to exit executes once. -/
private def satStopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
  k := C.k
  State := Bool × C.State
  tm := { q₀ := (false, entry)
          tr := fun q inp work =>
            if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
            else {C.tm.tr q.2 inp work with state := (C.tm.tr q.2 inp work).state.map (true, ·)} }

/-- Release-flag embedding preserves all physical fields of a call. -/
private def satStopCfg {k : ℕ} {S : Type} {x : List Bool}
    (b : Bool) (c : Cfg k Bool S x) : Cfg k Bool (Bool × S) x :=
  ⟨c.state.map (b, ·), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- Before the designated positive exit, the stopped source takes the same
physical step as the module and raises the release flag. -/
private lemma satStop_step (C : FinTM Bool) (entry exit : C.State)
    {x : List Bool} (b : Bool) (c : Cfg C.k Bool C.State x)
    (hlive : c.state ≠ none) (hg : b = true → c.state ≠ some exit) :
    (satStopTM C entry exit).tm.step (satStopCfg b c) = satStopCfg true (C.tm.step c) := by
  cases hs : c.state with
  | none => exact False.elim (hlive hs)
  | some q =>
    have hq : ¬(b = true ∧ q = exit) := by
      rintro ⟨hb, rfl⟩; exact hg hb hs
    simp only [MultiTapeTM.step, satStopCfg, hs, Option.map_some]
    simp only [satStopTM, hq, ↓reduceIte]
    rfl

/-- Live endpoints force every earlier module state to be live. -/
private lemma sat_live_prefix {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom c t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom c u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom c t = tm.runFrom c u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- Stop a clean call one silent step after its certified first positive exit.
**Proof sketch.** Induct on prefixes, keeping the release flag false only at
time zero. The supplied guard prevents early stopping; a final silent halt
retains every canonical seam field and every emitted bit. -/
private lemma satStop_clean (C : FinTM Bool) (entry exit : C.State)
    (x arg result out : List Bool) (t : ℕ) (ht : 0 < t)
    (hg : ∀ v, 0 < v → v < t → (C.tm.runFrom
      (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit)
    (he : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      {Cfg.ofWords exit (stateWord C.k result) with output := out}) :
    (satStopTM C entry exit).tm.runFrom
      (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1) =
      {Cfg.ofWords (true, exit) (stateWord C.k result) with state := none, output := out} := by
  let c := Cfg.ofWords (input := x) entry (stateWord C.k arg)
  have hl := sat_live_prefix C.tm c t (by rw [show C.tm.runFrom c t = _ from he]; simp [Cfg.ofWords])
  have hp : ∀ v, v ≤ t → (satStopTM C entry exit).tm.runFrom (satStopCfg false c) v =
      satStopCfg (decide (v ≠ 0)) (C.tm.runFrom c v) := by
    intro v
    induction v with
    | zero => intro _; rfl
    | succ v ih =>
      intro hv
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        satStop_step C entry exit _ _ (hl v (by omega)) (by
          intro hn
          exact hg v (Nat.pos_of_ne_zero (of_decide_eq_true hn)) (by omega)),
        MultiTapeTM.runFrom_succ_eq_step']
      rfl
  have hi : Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg) = satStopCfg false c := rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step', hp t (Nat.le_refl _)]
  have hflag : decide (t ≠ 0) = true := by simp [Nat.ne_of_gt ht]
  rw [hflag, show C.tm.runFrom c t = _ from he]
  simp [MultiTapeTM.step, satStopTM, satStopCfg, Cfg.ofWords, FinTM.controlAction, Action.apply]

/-- Six finite modules form the streaming body: startup append and install,
then the recurring pack, append, emit, and install calls. -/
private abbrev SatHostState (M : Fin 6 → FinTM Bool) := Unit ⊕ (Σ i, (M i).State)

/-- A module's return destination; startup install and step install return to
the unique loop anchor. The other calls continue to the next finite module. -/
private def satHostNext (i : Fin 6) : Option (Fin 6) :=
  if i = 0 then some 1 else if i = 2 then some 3 else if i = 3 then some 4
  else if i = 4 then some 5 else none

/-- A named entry state inside the finite body. -/
private def satHostEntry (M : Fin 6 → FinTM Bool) (i : Fin 6) : SatHostState M :=
  .inr ⟨i, (M i).tm.q₀⟩

/-- Resolve a finite module's return, with no additional tape operation. -/
private def satHostRet (M : Fin 6 → FinTM Bool) (i : Fin 6) : SatHostState M :=
  match satHostNext i with
  | some j => satHostEntry M j
  | none => .inl ()

/-- The actual finite controller. All modules use the same padded work bank,
so the clean-call contracts restore scratch before each next call. `emitAction`
forwards the halting transition as well as ordinary transitions. -/
private def satHostTM (M : Fin 6 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) : FinTM Bool where
  k := K
  State := SatHostState M
  tm := {
    q₀ := satHostEntry M 0
    tr := fun q inp work => match q with
      | .inl _ => FinTM.controlAction 0 (some (satHostEntry M 2))
      | .inr ⟨i, s⟩ => emitAction (fun s => .inr ⟨i, s⟩) (satHostRet M i)
          ((satPadTM (M i) K (hk i)).tm.tr s inp work) }

/-- Forwarding a padded clean configuration produces the host's canonical
seam with precisely the supplied output prefix. Positive tape count is used
only to identify the real tape-zero word. -/
private lemma satHost_seam (M : Fin 6 → FinTM Bool) (K : ℕ) (i : Fin 6)
    (hp : 0 < (M i).k) (x w pre out : List Bool) (q : (M i).State)
    (state : Option (M i).State) :
    emitCfg (fun s => (Sum.inr ⟨i, s⟩ : SatHostState M)) (satHostRet M i) pre
      (satPadCfg (K := K) {Cfg.ofWords (input := x) q (stateWord (M i).k w)
        with state := state, output := out}) =
      {Cfg.ofWords (((state.map (fun s => (Sum.inr ⟨i, s⟩ : SatHostState M))).getD (satHostRet M i)))
        (stateWord K w) with output := pre ++ out} := by
  have h := satPad_seam (K := K) (x := x) hp q w out
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapes) h
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapePos) h

/-- Run one clean module inside the body, forwarding exactly its output.
**Proof sketch.** Padding preserves the source run. The audited `emit_run`
then transfers every live prefix and the halting endpoint; live prefixes
always remain in that module's state summand, hence cannot hit the anchor. -/
private lemma satHost_call (M : Fin 6 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (i : Fin 6) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
    (q : (M i).State) (t : ℕ)
    (hg : ∀ v < t, ¬((M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
    (he : (M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
      {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
    (∀ v < t, ((satHostTM M K hk).tm.runFrom
      {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} v).state
        ≠ some (.inl ())) ∧
    (satHostTM M K hk).tm.runFrom
      {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} t =
      {Cfg.ofWords (satHostRet M i) (stateWord K result) with output := pre ++ out} := by
  let c := Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)
  let emb : (M i).State → SatHostState M := fun s => .inr ⟨i, s⟩
  have hinit : emitCfg emb (satHostRet M i) pre (satPadCfg (K := K) c) =
      {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} := by
    simpa [emb, c, satHostEntry] using
      satHost_seam M K i hp x arg pre [] (M i).tm.q₀ (some (M i).tm.q₀)
  have hrun (v : ℕ) (hv : v ≤ t) :
      (satHostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} v =
        emitCfg emb (satHostRet M i) pre (satPadCfg ((M i).tm.runFrom c v)) := by
    rw [← hinit]
    rw [emit_run (satPadTM (M i) K (hk i)).tm (satHostTM M K hk).tm emb (satHostRet M i)
      (by intros; rfl) pre _ v (by
        intro u hu
        rw [satPad_run]
        exact hg u (by omega))]
    rw [satPad_run]
  constructor
  · intro v hv
    rw [hrun v (Nat.le_of_lt hv)]
    have hl := hg v hv
    cases hs : ((M i).tm.runFrom c v).state with
    | none => exact False.elim (hl hs)
    | some s => simp [emitCfg, satPadCfg, hs, emb]
  · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
    exact satHost_seam M K i hp x result pre out q none

/-- Joining two guarded segments preserves the first-return guard when the
intermediate seam is also outside the anchor. -/
private lemma sat_guard_add {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
    (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
    (he : tm.runFrom c a = d)
    (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
    ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
  intro v hv
  by_cases h : v < a
  · exact ha v h
  · have hva : a ≤ v := by omega
    rw [← Nat.add_sub_of_le hva, MultiTapeTM.runFrom_add, he]
    exact hb (v - a) (by omega)

/-- Uniform clean-module contract: a first halt with a prescribed replacement
word and emitted chunk, over every untouched native input. -/
private def SatClean (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) : Prop :=
  0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
    (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
    M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
      {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}

/-- Turn a clean-call bridge contract into the uniform first-halting form.
**Proof sketch.** The release wrapper stops one step after the positive exit;
minimal-halt cutting retains its entire clean configuration. -/
private lemma satClean_stop (C : FinTM Bool) (entry exit : C.State)
    (result emit : List Bool → List Bool) (B : ℕ → ℕ) (hk : 0 < C.k)
    (h : ∀ x arg : List Bool, ∃ t ≤ B arg.length, 0 < t ∧
      (∀ v, 0 < v → v < t → (C.tm.runFrom
        (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit) ∧
      C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
        {Cfg.ofWords exit (stateWord C.k (result arg)) with output := emit arg}) :
    SatClean (satStopTM C entry exit) result emit (fun n => B n + 1) := by
  refine ⟨hk, fun x arg => ?_⟩
  obtain ⟨t, hb, ht, hg, he⟩ := h x arg
  have hs := satStop_clean C entry exit x arg (result arg) (emit arg) t ht hg he
  obtain ⟨u, hu, hut, hguard, hend⟩ := sat_call_first_halt (satStopTM C entry exit).tm
    (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1)
    (by simp [Cfg.ofWords]) (by rw [hs])
  refine ⟨u, hu, by dsimp only; omega, hguard, ?_⟩
  simpa only [satStopTM, Cfg.ofWords] using hend.trans hs

/-- The bridge overhead is bounded by one monomial of degree one higher.
**Proof sketch.** Output length is bounded by source time; `n+1` and both
source-time terms fit the larger power. The last unit pays for stopping. -/
private lemma sat_bridge_bound (c A d n len : ℕ) (hlen : len ≤ A * (n + 1) ^ d) :
    c * (A * (n + 1) ^ d + n + len + 1) + 1 ≤
      (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1) := by
  have hd := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + 1 by omega))
  simp only [Nat.succ_eq_add_one] at hd
  have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ d + 1 by omega)
  have h1 : 1 ≤ (n + 1) ^ (d + 1) := by omega
  calc
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, two_mul]
      omega
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + (n + 1) ^ (d + 1) := Nat.add_le_add_left h1 _
    _ = _ := by ring

/-- Every polynomial word computation has a clean first-halting install
module with a polynomial budget on the argument length. -/
private lemma satClean_install {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, SatClean M f (fun _ => []) (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_installCallTM F f _ hF
  -- The bridge's result length depends on the word, so enlarge it pointwise
  -- to source time before putting it in the uniform argument-length budget.
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := satClean_stop C entry exit f (fun _ => [])
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      refine ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, ?_⟩
      exact he)
  refine ⟨satStopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (sat_bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- The emit-mode counterpart preserves the argument and forwards the exact
computed chunk. Its polynomial budget includes cleanup and the final halt. -/
private lemma satClean_emit {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, SatClean M id f (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_emitCallTM F f _ hF
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := satClean_stop C entry exit id f
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      exact ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, he⟩)
  refine ⟨satStopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (sat_bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- Pairing length, used to charge every request to the original input. -/
private lemma satPair_length (u v : List Bool) :
    (pairEncode u v).length = 2 * u.length + v.length + 2 := by
  simp [pairEncode, List.length_flatMap, Nat.mul_comm] <;> omega

/-- Every polynomial on a linearly bounded request fits the common power. -/
private lemma sat_request_budget (A d D n m : ℕ) (hd : d ≤ D)
    (hm : m + 1 ≤ 32 * (n + 1)) :
    A * (m + 1) ^ d ≤ A * (32 * (n + 1)) ^ D := by
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left hm d).trans
    (Nat.pow_le_pow_right (by omega) hd)

/-- Specialize a clean module to one call site in the finite host. -/
private lemma satHost_clean (M : Fin 6 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (i : Fin 6) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : SatClean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ((satHostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl ())) ∧
      (satHostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (satHostRet M i) (stateWord K (f arg)) with output := pre ++ g arg} := by
  obtain ⟨t, hp, ht, hg, he⟩ := h.2 x arg
  obtain ⟨hguard, hend⟩ := satHost_call M K hk i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
  exact ⟨t, hp, ht, hguard, hend⟩

/-- The full normalized emitter is polynomial-time computable.
**Proof sketch.** Build four clean modules for startup, request packing, chunk
emission, and next-state installation. The marker-free appender supplies the
native input at startup and in every round. Their finite tagged host has one
anchor, a validated startup seam, and positive first-return rounds with only
the canonical state word left on tape zero. Request sizes are linear in the
original input, so one common polynomial bounds all calls and cleanup. Invoke
`exists_emitLoopTM` with `R n = n`, then use the exact chunk-table identity. -/
private lemma satReduction_poly : PolyTimeComputable satReduction := by
  obtain ⟨S, aS, dS, hS⟩ := satClean_install satStreamStart_poly
  obtain ⟨P, aP, dP, hP⟩ := satClean_install
    (sat_pt_pair polyTimeComputable_id (sat_pt_const []))
  obtain ⟨E, aE, dE, hE⟩ := satClean_emit satReqEmit_poly
  obtain ⟨I, aI, dI, hI⟩ := satClean_install satReqStep_poly
  obtain ⟨F, aF, hF⟩ := FinTM.computesFunInTime_lengthBits
  let M : Fin 6 → FinTM Bool := fun i => match i.val with
    | 0 => satAppendTM | 1 => S | 2 => P | 3 => satAppendTM | 4 => E | _ => I
  let K := 1 + S.k + P.k + E.k + I.k
  have hk : ∀ i, (M i).k ≤ K := by
    intro i; fin_cases i <;> simp [M, K, satAppendTM] <;> omega
  let H := satHostTM M K hk
  let anchor : H.State := .inl ()
  let D := dS + dP + dE + dI + 1
  let A := aS + aP + aE + aI + aF + 200
  let pow (n : ℕ) := (32 * (n + 1)) ^ D
  let T (n : ℕ) := A * pow n
  have hpow (n : ℕ) : n + 1 ≤ pow n := by
    have h := Nat.pow_le_pow_right (show 0 < 32 * (n + 1) by omega) (show 1 ≤ D by dsimp [D]; omega)
    simp only [Nat.pow_one] at h
    exact (by omega : n + 1 ≤ 32 * (n + 1)).trans h
  have hret0 : satHostRet M 0 = satHostEntry M 1 := rfl
  have hret1 : satHostRet M 1 = anchor := rfl
  have hret2 : satHostRet M 2 = satHostEntry M 3 := rfl
  have hret3 : satHostRet M 3 = satHostEntry M 4 := rfl
  have hret4 : satHostRet M 4 = satHostEntry M 5 := rfl
  have hret5 : satHostRet M 5 = anchor := rfl
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ v < t, (H.tm.runFrom (H.tm.initCfg x) v).state ≠ some anchor) ∧
      H.tm.runFrom (H.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord H.k (satStreamWord (satStreamStart x))) := by
    intro x
    obtain ⟨ta, hapos, hat, hag, hae⟩ := satAppend_clean x []
    have hac := satHost_call M K hk 0 (by simp [M, satAppendTM]) x [] x [] []
      (0 : Fin 5) ta hag (by simpa using hae)
    obtain ⟨haGuard, haEnd⟩ := hac
    have hi : H.tm.initCfg x = Cfg.ofWords (satHostEntry M 0) (stateWord K []) := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i z; simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord, FinTM.bufferTape]
    change H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 0) (stateWord K [])) ta =
      Cfg.ofWords (satHostRet M 0) (stateWord K x) at haEnd
    rw [hret0] at haEnd
    obtain ⟨ts, hspos, hst, hsGuard, hsEnd⟩ := satHost_clean M K hk 1
      (fun x => satStreamWord (satStreamStart x)) (fun _ => [])
      (fun n => aS * (n + 1) ^ dS) (by simpa [M] using hS) x x []
    change H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 1) (stateWord K x)) ts =
      Cfg.ofWords (satHostRet M 1) (stateWord K (satStreamWord (satStreamStart x))) at hsEnd
    rw [hret1] at hsEnd
    have hsB := sat_request_budget aS dS D x.length x.length (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    refine ⟨ta + ts, ?_, ?_, ?_⟩
    · dsimp only [T, A, pow]
      simp only [List.length_nil] at hat
      simp only [Nat.add_mul, Nat.mul_one]
      dsimp only [pow] at hp
      omega
    · rw [hi]
      exact sat_guard_add H.tm anchor _ _ ta ts haGuard haEnd hsGuard
    · rw [hi, MultiTapeTM.runFrom_add, haEnd, hsEnd]
      rfl
  have hround : ∀ x w : List Bool, satStreamInv x w → ∃ t, 0 < t ∧ t ≤ T x.length ∧
      (∀ v, 0 < v → v < t → (H.tm.runFrom
        (Cfg.ofWords (input := x) anchor (stateWord H.k w)) v).state ≠ some anchor) ∧
      H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t =
        {Cfg.ofWords anchor (stateWord H.k (satStreamStep x w)) with output := satStreamEmit x w} := by
    intro x w hw
    obtain ⟨s, rfl, hb⟩ := hw
    let w := satStreamWord s
    let packed := pairEncode w []
    let req := pairEncode w x
    have hwlen : w.length ≤ 6 * x.length + 8 := (satStreamBound_size x s hb).2
    have hplen : packed.length = 2 * w.length + 2 := by simp [packed, satPair_length]
    have hrlen : req.length = 2 * w.length + x.length + 2 := satPair_length w x
    have hpa : packed ++ x = req := by simp [packed, req, pairEncode, List.append_assoc]
    have hstep : satReqStep req = satStreamStep x w := by
      simpa [req, w, satStreamStep, satStreamRead_word] using (satReq_round x s).1
    have hemit : satReqEmit req = satStreamEmit x w := by
      simpa [req, w, satStreamEmit, satStreamRead_word] using (satReq_round x s).2
    have hdispatch : H.tm.step (Cfg.ofWords (input := x) anchor (stateWord K w)) =
        Cfg.ofWords (satHostEntry M 2) (stateWord K w) := by
      change (FinTM.controlAction 0 (some (satHostEntry M 2))).apply _ = _
      simp [FinTM.controlAction, Action.apply, Cfg.ofWords]
      exact ⟨rfl, rfl⟩
    obtain ⟨tp, hppos, hpt, hpGuard, hpEnd⟩ := satHost_clean M K hk 2
      (fun w => pairEncode w []) (fun _ => []) (fun n => aP * (n + 1) ^ dP)
      (by simpa [M, id_eq] using hP) x w []
    change H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 2) (stateWord K w)) tp =
      Cfg.ofWords (satHostRet M 2) (stateWord K packed) at hpEnd
    rw [hret2] at hpEnd
    obtain ⟨ta, hapos, hat, hag, hae⟩ := satAppend_clean x packed
    obtain ⟨haGuard, haEnd⟩ := satHost_call M K hk 3 (by simp [M, satAppendTM])
      x packed req [] [] (0 : Fin 5) ta hag (by simpa [hpa] using hae)
    change H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 3) (stateWord K packed)) ta =
      Cfg.ofWords (satHostRet M 3) (stateWord K req) at haEnd
    rw [hret3] at haEnd
    obtain ⟨te, hepos, het, heGuard, heEnd⟩ := satHost_clean M K hk 4 id satReqEmit
      (fun n => aE * (n + 1) ^ dE) (by simpa [M] using hE) x req []
    change H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 4) (stateWord K req)) te =
      {Cfg.ofWords (satHostRet M 4) (stateWord K req) with output := satReqEmit req} at heEnd
    rw [hret4] at heEnd
    obtain ⟨ti, hipos, hit, hiGuard, hiEnd⟩ := satHost_clean M K hk 5 satReqStep (fun _ => [])
      (fun n => aI * (n + 1) ^ dI) (by simpa [M] using hI) x req (satReqEmit req)
    change H.tm.runFrom
      {Cfg.ofWords (input := x) (satHostEntry M 5) (stateWord K req) with output := satReqEmit req} ti =
      {Cfg.ofWords (satHostRet M 5) (stateWord K (satReqStep req)) with output := satReqEmit req ++ []} at hiEnd
    rw [List.append_nil, hret5] at hiEnd
    have hpB := sat_request_budget aP dP D x.length w.length (by dsimp [D]; omega) (by omega)
    have heB := sat_request_budget aE dE D x.length req.length (by dsimp [D]; omega) (by omega)
    have hiB := sat_request_budget aI dI D x.length req.length (by dsimp [D]; omega) (by omega)
    have hpow' := hpow x.length
    have hpAE : H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 2) (stateWord K w))
        (tp + ta) = Cfg.ofWords (satHostEntry M 4) (stateWord K req) := by
      rw [MultiTapeTM.runFrom_add, hpEnd, haEnd]
    have hpAguard := sat_guard_add H.tm anchor _ _ tp ta hpGuard hpEnd haGuard
    have hpAEguard := sat_guard_add H.tm anchor _ _ (tp + ta) te hpAguard hpAE heGuard
    have hpAEE : H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 2) (stateWord K w))
        (tp + ta + te) = {Cfg.ofWords (satHostEntry M 5) (stateWord K req) with output := satReqEmit req} := by
      rw [MultiTapeTM.runFrom_add, hpAE, heEnd]
    have hguard := sat_guard_add H.tm anchor _ _ (tp + ta + te) ti hpAEguard hpAEE hiGuard
    refine ⟨(tp + ta + te + ti) + 1, by omega, ?_, ?_, ?_⟩
    · dsimp only [T, A, pow]
      simp only [Nat.add_mul]
      dsimp only [pow] at hpow'
      omega
    · intro v hv hvt
      have hvform : v = (v - 1) + 1 := by omega
      change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord K w)) v).state ≠ some anchor
      rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdispatch]
      exact hguard (v - 1) (by omega)
    · change H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord K w))
        ((tp + ta + te + ti) + 1) = _
      rw [MultiTapeTM.runFrom_succ_eq_step, hdispatch, MultiTapeTM.runFrom_add, hpAEE, hiEnd]
      rw [hstep, hemit]
      rfl
  have hFuel : F.ComputesFunInTime (fun x => Nat.bits x.length) T := by
    intro x
    apply (hF x).mono
    have hp := Nat.mul_le_mul_left aF (hpow x.length)
    dsimp only [T, A]
    simp only [Nat.add_mul]
    omega
  obtain ⟨L, c, hL⟩ := FinTM.exists_emitLoopTM H F anchor satStreamInv satStreamStep satStreamEmit
    (fun x => satStreamWord (satStreamStart x)) id T hFuel satStreamInv_start satStreamInv_step hstart hround
  refine ⟨L, 2 * c * (A * 32 ^ D + 1), D + 1, fun x => ?_⟩
  have hcalc : c * (T x.length + 1) * (x.length + 2) ≤
      (2 * c * (A * 32 ^ D + 1)) * (x.length + 1) ^ (D + 1) := by
    have h1 : 1 ≤ (x.length + 1) ^ D := Nat.one_le_pow _ _ (by omega)
    have hb : T x.length + 1 ≤ (A * 32 ^ D + 1) * (x.length + 1) ^ D := by
      dsimp only [T, pow]
      simp only [Nat.mul_pow, Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc]
      omega
    calc
      _ ≤ (c * ((A * 32 ^ D + 1) * (x.length + 1) ^ D)) * (2 * (x.length + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left c hb) (by omega)
      _ = _ := by rw [Nat.pow_succ]; ring
  have hout := (hL x).mono hcalc
  simpa only [id_eq, satStream_output_identity] using hout

/-- **`SAT ≤ₚ 3SAT`** [AB09, Lemma 2.14]: clause splitting with fresh
variables.

**Proof sketch.** The formula-level transform `t : CNF ℕ → CNF ℕ` maps each
clause of width `> 3` to a chain: `C = ℓ₁ ∨ ℓ₂ ∨ rest` becomes
`(ℓ₁ ∨ ℓ₂ ∨ z) ∧ t(¬z ∨ rest)` with `z` a fresh variable, recursively until
width `≤ 3` ([AB09, §2.3.5]); clauses of width `≤ 3` pass through. Fresh
variables are allocated from `φ.numVars` upward by a running counter, so
freshness is by construction (indices `≥ numVars` are unmentioned —
`Complexity.eval_congr_of_lt_numVars`'s bound). **Equisatisfiability**, the
mathematical content, by induction on the splitting: forward, a satisfying
assignment extends to the fresh variables by giving each `z` the value "the
tail `rest` is satisfied" (if `ℓ₁ ∨ ℓ₂` already holds, `z := false` keeps the
second clause on its `¬z` disjunct — [AB09]'s case analysis); backward, a
satisfying assignment of the image restricted to the original variables
satisfies `C`, since from `(ℓ₁ ∨ ℓ₂ ∨ z)` and inductively `¬z ∨ rest` either
some original literal holds or the chain walks to one. Width and size: every
output clause has width `≤ 3`, and the output has at most `|C| - 2` chain
links per clause — total size linear in the input size, fresh indices at most
`numVars + Σ widths`. **The string-level reduction** is
`f = Std.Sat.CNF.serialize ∘ t ∘ Std.Sat.CNF.decode`, with
`Complexity.PolyTimeComputable f` by the named machine obligations: the parsing
machine (shared with `Complexity.SAT_mem_NP`), the streaming transform (a
clause buffer, a width counter, and the fresh-variable counter whose unary
serialization stays linear in the output position), and the serializer;
output length polynomial in `|x|`. **Correctness for every string**:
well-formed `x` by `Std.Sat.CNF.decode_serialize` and equisatisfiability
(width of `t φ` is `≤ 3` by construction); non-well-formed `x` decodes to the
fallback `[]`, which `t` fixes, so `f x = Std.Sat.CNF.serialize []` — and both
sides of `x ∈ SAT ↔ f x ∈ SAT3` are true (the fallback and the empty formula
are satisfiable and 3CNF). Conclude with the definition
`Complexity.PolyTimeReducible`. -/
theorem SAT_reducible_SAT3 : SAT ≤ₚ SAT3 := by
  exact ⟨satReduction, satReduction_poly, satReduction_correct⟩

end Complexity

```


## ===== audits/logs/ch3-p31-sweep.log =====

```
P3.1 GATE SWEEP at commit edea2663748fe2b1e47636094b95744ed50148f0 (edea2663), branch complexity/arora-barak-ch3-4, started 2026-10-08 17:50:45
== TCSlib/Complexity/TuringMachine/OracleFinite
== TCSlib/Complexity/TuringMachine/OracleNondeterministic
TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean:278:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/ClassOracle/Classes
TCSlib/Complexity/ClassOracle/Classes.lean:108:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassOracle/Classes.lean:121:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassOracle/Classes.lean:142:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassOracle/Classes.lean:150:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassOracle/Classes.lean:160:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassOracle/Classes.lean:181:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/ClassOracle/SATOracle
TCSlib/Complexity/ClassOracle/SATOracle.lean:49:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassOracle/SATOracle.lean:57:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassOracle/SATOracle.lean:65:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/ClassOracle
P31_SWEEP_DONE

```


## ===== audits/logs/ch34-p31-p41-stylelint.log =====

```
INFO  TCSlib/Complexity/ClassOracle/Classes.lean    184 lines; 10 public / 0 private declarations
INFO  TCSlib/Complexity/ClassOracle/SATOracle.lean  68 lines; 3 public / 0 private declarations

style_lint: 0 FAIL, 0 WARN over 2 files
INFO  TCSlib/Complexity/SpaceComplexity/Basic.lean                161 lines; 10 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean          460 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Constructible.lean        82 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean       495 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean    246 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Examples.lean             63 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean         416 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Inclusions.lean           96 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean         307 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean      93 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean    333 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean      285 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean      551 lines; 30 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean        226 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean         176 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Call.lean        360 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean  495 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean       438 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean  508 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean     266 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean     358 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean        455 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean     479 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean      423 lines; 29 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean         333 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean       376 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean      662 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean      662 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean    445 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean  571 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Program.lean     347 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean         564 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/NSPACE.lean               114 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean         86 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean        319 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean            217 lines; 11 public / 0 private declarations

style_lint: 0 FAIL, 0 WARN over 35 files
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

```
