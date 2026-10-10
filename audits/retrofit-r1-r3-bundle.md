# External audit pack — chapter-1/2 retrofit, epoch R1 boundary, round 3

Round 2 (`audits/retrofit-r1-r2-pack.md`, findings verbatim in
`audits/retrofit-r1-r2-findings.md`) **closed R1-1, R1-3, and R1-4**
(full bidirectional reconstruction with recomputed blobs; the E1
statements proven identical up to renaming; the errata confirmed) and
held the gate on the ledger: **R2-1** (inconsistent arithmetic, no single
inclusion rule, missing sources) and **R2-2** (debt: the relocation
family's "reimplementation" classification refuted — byte-identical
across the three files — and the H3 copies omitted, with no named cleanup
owner/window). This round audits the ledger rebuild and the human
acknowledgment. The gate closes on zero blockers and majors; debt majors
close only by human acknowledgment — **which has now been given**.

## Disposition table (verify each)

| Round-2 finding | Disposition |
|---|---|
| R2-1 (major: ledger arithmetic and convention) | **Rebuilt** (`audits/duplication-ledger.md`, attached): one primary inclusion rule (expanded correspondence membership, strengthened counterparts included symmetrically; strict normalized-twin counts stated secondarily where they differ), every family enumerated once per file, your independently computed figures adopted verbatim — Loop **104/212 = 49.1%** (87 + 4 relocation originals + 13 H3 copies), Primitives **150/272 = 55.1%** (146 + 4), Hardness **4/549**, Catalog **264/423 = 62.4%** (150 + 95 + 17 + 2; strict 259 = 61.2%), Wrappers **17/29 = 58.6%**; your span-rule line counts (2,009 / 3,162 / 73-per-file) adopted with the rule stated; deleted-original/dead-twin labels downgraded to 12.2c dispositions requiring the Catalog reference graph. The previously missing sources are attached: **the complete pinned `Build/Catalog.lean` and `Build/Wrappers.lean`**, plus the A2/F2A agent reports whose declared-copy inventories the correspondences cite. Recompute the totals and fractions; flag any member the rule still misses. |
| R2-2 (major, debt: the relocation family and H3 copies) | **Accounted and acknowledged.** The ledger now counts the three-file relocation family once per file (12 members in all) under its correct classification — verbatim copies, pre-policy legacy, disclosed at their batches but mischaracterized by the round-1 ledger — and the 13 H3 copies in Loop's row (originals not double-counted; the `_init` near-copy noted, uncounted). **The human acknowledgment is on record** (the user, 2026-10-09, via the plan's decision log and the ledger's acknowledgment table): cleanup owner — **retrofit batch RB4** over all three files, collapsing the H3 copies via the proved §13 Z5 agreement transfer and replacing the relocation family via the proved Z1-rider selected-tape exports plus Z5; window — **after the A-S1 fill gate closes** (Z5 and the rider are proved as of vhost-f1). Verify the acknowledgment names family, owner, and window as the governance requires, and that D-R2/D-R3 are carried without renewed approval, per your own round-2 guidance. |
| R2-3 (minor: delta wording) | **Fixed**: eleven dead originals plus one live original eliminated by replacement; the epoch-wide 76 + 7 distinction retained. |
| R2-4 — R2-11 (closed and no-findings rows) | Carried as recorded; nothing in this round's delta touches sources — the only changed artifacts are the ledger, the plan's decision log, and this pack. |

## Brief for the auditor

1. Verify the rebuilt ledger against the attached sources and
   correspondences: recompute at least the Catalog 264 partition (now
   fully attachable: count the `f2_*`/`a2_*`/`catalog_redirect*` members
   in the attached `Catalog.lean` against the attached inventories and
   agent reports) and the Wrappers 17/29 row; re-check the Loop/
   Primitives/Hardness member arithmetic you supplied; confirm the
   inclusion rule is applied symmetrically this time.
2. Verify the acknowledgment chain for R2-2 (ledger table + the plan's
   decision-log row) meets the template's debt disposition: named family,
   named owner, named window, human attribution.
3. Report in the standard table; findings verbatim into
   `audits/retrofit-r1-r3-findings.md`; the gate closes on zero blockers
   and majors, which retires epoch R1 and arms both 12.2c and RB4.

## Repository-side attestations

As rounds 1-2, unchanged (replays, axiom prints, lint, checksums,
bundles, shim exclusions, merge trail). This round's delta is
documentation only; no Lean source changed.

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
| **A-S2 round 2 FAILED on the repair's own cascade contracts; repaired** (2026-10-09: **1 blocker / 0 majors / 1 minor** — `audits/zone-infra-r2-findings.md` verbatim; the round-1 operational repair ACCEPTED, the old Z4 major CLOSED at sketch level). **A-S2-R2-1**: both new cascade contracts omitted the **top-left receiving room** — at `ℓ=1, j=0` with `L₀` full the guarded move is the identity and the conclusions are false (`2 = 3`); the auditor supplied the necessity argument, the weaker/stronger hypothesis split, the two-pass induction under the shared repair, and the classical-invariant implication showing no textbook pre-state is excluded. Repaired in `Zone.lean`: `zoneCascadeRight_lengths` gains the **necessary** `+2^j` room hypothesis; `zoneSide_cascadeRight` gains the auditor's weaker `+2^(j-1)` form (one-pass boundary recorded in the docstring); regressions `zoneCascadeRight_zero` and `zoneCascadeRight_blocked` added; sketches adopt the round-2 schedule analysis verbatim. Zone.lean 647 lines, 24 sorry warnings, exit 0, lint 0 FAIL. **A-S2-R2-2 acknowledged**: the auditor's inventory is canonical (Zone 20 defs / 18 sorried / 22 terms / 8 capacity holes in 4 defs; tranche 26/23/27/3 incl. the unchanged `alphabet_reduction_spaceUsed` row). Round-3 pack follows | Recorded |
| **Retrofit-R1 round 2: R1-1/R1-3/R1-4 CLOSED, gate still open on the ledger** (2026-10-09: **0 blockers / 2 majors / 1 minor / 8 notes** — `audits/retrofit-r1-r2-findings.md` verbatim). Closed: full bidirectional reconstruction with recomputed blob hashes; the **E1 statement comparison settled** — the deleted private and `Turing.eq_pairEncode_of_pairDecode` are the identical quantified proposition up to renaming; the errata confirmed independently. Open: **R2-1** — the ledger's arithmetic was inconsistent (summands 261 vs printed 249; Primitives partition 147 of 150; asymmetric inclusion rule); **R2-2 (debt)** — the ledger's "design-harvest reimplementation" claim REFUTED: the four relocation declarations are **byte-identical across Loop/Primitives/Hardness** after identifier substitution (one family, two verbatim copies, 73 lines per file), and the 13 exact Loop-internal H3 copies were omitted; the relocation family has no named cleanup owner/window (D-R2's 12.2c excludes Hardness). **Ledger REBUILT** (`audits/duplication-ledger.md`): one expanded-correspondence rule, strict-twin counts secondary, the auditor's figures adopted (Loop 104/212 = 49.1%, Primitives 150/272 = 55.1%, Hardness 4/549, Catalog 264/423 = 62.4%, Wrappers 17/29), the R2-3 wording fixed (eleven dead + one replaced). **Proposed acknowledgment, PENDING THE USER per the governance**: a retrofit batch **RB4** (Loop + Primitives + Hardness) as owner — collapsing the H3 copies via the proved Z5 and the relocation family via the proved Z1-rider exports + Z5 — window: after the A-S1 fill gate closes. Round-3 pack issues on that acknowledgment | Recorded |
| **RB4 ACKNOWLEDGED (user, 2026-10-09)** — the R2-2 debt disposition: owner = retrofit batch **RB4** over `Build/Loop.lean` + `Build/Primitives.lean` + `CookLevin/Hardness.lean`, collapsing the 13 H3 copies via the proved Z5 and replacing the three-file relocation family via the proved Z1-rider exports + Z5; window = **after the A-S1 fill gate closes**. Recorded in `audits/duplication-ledger.md`'s acknowledgment table; the retrofit-r1 round-3 pack issues with the rebuilt ledger and the attached `Catalog.lean`/`Wrappers.lean` sources | Decided |

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

## ===== audits/retrofit-r1-pack.md =====

```
# External audit pack — chapter-1/2 retrofit, epoch R1 boundary

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4d).
Epoch R1 = the three conservative retrofit batches, integrated and merged:
RB1 (`Build/Loop.lean`, PR #10), RB2 (`Build/Primitives.lean`, PR #9, plus
the maintainer's E1-resolution commit approved by the user's merge), RB3
(`CookLevin/Hardness.lean`, PR #10). This is the epoch-boundary audit the
workflow and the duplication governance require (`workflow.md` §4; audit
template failure mode 5). The gate closes on zero blockers and zero
majors; a debt major closes only by explicit human acknowledgment.

Audited at commit `c43f3a53` (branch `complexity/arora-barak-ch3-4`; the
tree also carries the out-of-scope §13 statement work — `Build/Zone.lean`,
`Codes2Tape.lean`, `Build/VirtualInput.lean`, the `Simulation`/`Embed`/
`Robustness` additions — which has its own gates and is **not** this
audit's object). **Every change is kernel-checked** (maintainer replay
evidence below); the audit object is the retrofit's **discipline**: that
deletions deleted only dead material, that public surfaces are
byte-identical, that every replacement is the strict simplification its
brief claimed, and that the epoch's duplication ledger is honest.

## Brief for the auditor

1. **Re-verify the freezes from the patches.** The three attached patch
   series are the complete change (plus the maintainer's E1 commit, whose
   diff is quoted below). Verify: every removed line lies inside a deleted
   `private` declaration (with its docstring), an authorized comment
   block, or a named re-pointed use line inside a `private` proof body —
   with exactly **one** exception, the E1 line (item 3). The public
   declarations of all three files must be reconstructible byte-for-byte
   from base `5588628c`; the maintainer's declaration-level comparisons
   attested 18/18, 9/9 (8 + `stateWord`), and 5/5 — re-establish
   independently.
2. **Audit the deletions as deletions of dead code**: 62 (Primitives) +
   8 (Loop) + 6 (Hardness) + the 2 Encoding-duplicate privates + the H4
   pair + `clCompute_comp`/`clBuffer_append_bit`/`clA5_pt_unaryLength`/
   `catalogPair_length`. The compile is the base safety argument (a live
   deletion fails loudly); your added value is the converse check — flag
   any deleted declaration that a *pending* consumer (the §4d plan, the
   12.2c dedup maps, the §13 layer) expected to survive.
3. **The E1 exception (human-approved).** RB2's agent correctly escalated:
   `catalogPair_inverse`'s last use sat in the public proof body of
   `computesFunInTime_stripLast`, which the batch freeze forbids touching.
   The maintainer's commit swapped that one line,
   `rw [catalogPair_inverse x u v hd]` →
   `rw [Turing.eq_pairEncode_of_pairDecode x u v hd]`, and deleted the
   private duplicate; the user approved by merging. Verify: the two lemmas
   are statement-identical (the public one is attached in context via the
   patch), the theorem's statement/signature/docstring are untouched, and
   the governance trail (escalation → flagged commit → human merge) is
   complete. This is the first exercise of the duplication policy's
   human-approval loop — report any gap in the trail as a major.
4. **Audit the three citations as strict simplifications**:
   (a) Loop's H4 — the forwarding lockstep now cites the public
   `Turing.emit_run` + `leftCfg_run` through a padded source (the glue is
   quoted in the RB1 report; `emLoopForwardCfg` the *definition* was
   retained because frame proofs consume it — verify that retention is
   right, not an oversight); (b) Hardness's `clFreshTM` — now literally
   `seamCompTM clWipeTM.tm 2 clReadTM.tm (.inl none)` with `clFresh_run`
   citing `seamCompTM_run_ofCfg`, the first §12 consumer outside `Build/`
   (verify the citation carries the displaced stream head through the
   general-configuration seam, and that the sanctioned `Build.Seam` import
   is the only import change in the epoch); (c) the Hardness swaps
   (`bufferedCompTM_computesInTime`, `bufferTape_append`,
   `clNative_fill true` — all 13 use sites are enumerated in the RB3
   report; verify the enumeration against the patch).
5. **The epoch duplication ledger** (failure mode 5, cumulative): all
   three deliveries declared "new copies: none", and the epoch's net
   effect on copied material is strictly negative (dead copies deleted;
   one cross-file duplicate pair collapsed by E1; the Loop↔Catalog and
   Primitives↔Catalog twin inventories untouched and still queued for
   12.2c). Verify no patch introduces a copy, and record the per-file
   totals: Loop 5,713 → 5,515, Primitives 7,636 → 6,374, Hardness
   8,904 → 8,725 (net **−1,639 lines, −85 privates** across the epoch).
6. **Verify the recorded errata**: the retrofit inventory's "two strict
   Encoding swaps" missed the public-body use that became E1 (now in the
   plan's decision log); the backlog's generated-kernel-artifact count
   corrects to 12, located in `Nondeterminism`/`EXP`/`SAT`, none in
   Hardness; Hardness's private count was 553, not ~538.
7. Report anything the epoch misstates, in the standard table and
   severity scale.

## Repository-side attestations (verify or challenge)

* Integration: `git am -3`, Codex authorship preserved on all seven agent
  commits; side-branch + PR discipline per the user's rule (PR #9 merged
  by the user with the flagged E1 commit; PR #10 merged by the user).
* Replays (per batch, on the side branches): RB1 — Loop + **Catalog** (the
  heavy importer) + the `TuringMachine` facade, exit 0 / 0 errors /
  0 sorries; RB2 — Primitives + facade likewise; RB3 — Hardness + the
  `CookLevin` facade likewise (logs
  `audits/logs/retrofit-rb{1,2,3}-integration-sweep.log`).
* Independent axiom prints: 8/8 (Loop — seven at the standard triple,
  `stateWord` axiom-free), 18/18 and 5/5 (standard triple), no `sorryAx`
  anywhere (`audits/logs/retrofit-rb{1,2,3}-axioms.log`).
* Style lint: 0 FAIL on every batch; the surviving size WARNs are the
  recorded retrofit/12.2c program.
* Delivery integrity: checksums verified on all three zips; bundles verify
  against the recorded base `5588628c`; RB2's and RB3's environment-shim C
  files **excluded** per the standing instruction (not compiled, not run,
  unreferenced by the patches; RB1's delivery carried none).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md` (failure mode 5 in force);
findings verbatim into `audits/retrofit-r1-findings.md`; the epoch gate
closes on zero blockers and majors, which completes the conservative
retrofit and arms the promoted 12.2c window (its precondition — the
shrunken `Build/` files — is now met).
```

## ===== audits/retrofit-r1-findings.md =====

```
**Retrofit epoch R1 — external audit findings**

**Verdict: gate remains open — 0 blockers, 2 majors, 2 minors, 8 notes.** The majors concern missing evidence for expressly required audit checks. I found no unauthorized change in the supplied patches and no mathematical counterexample. The recorded human decisions are credited; this report does not request renewed approval of already acknowledged debt or of E1.

Audit target: `c43f3a53`, relative to the recorded base `5588628cbbddea9546f616907364b608e15557fd`. Evidence: the supplied pack and its 20 attachments only. Bundle SHA-256, independently computed: `3d0a0f7415f22caa60ff21a9c11747eef2f786c4b0bfd8e5c36140c221c4200e`.

I accepted the commissioned premise that the changes are kernel-checked. I did not re-audit tactic correctness, access repository development history, or modify Lean sources. I parsed all 46 unified-diff hunks, checked their old/new line counts and inter-patch context consistency, independently enumerated the removals and additions, and tracked line positions through all seven agent commits and the maintainer's E1 diff.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R1-1 | major | Audit pack §1/§3 · source reconstruction and `catalogPair_inverse` replacement | The packet does not supply the evidence needed for the requested full source reconstruction or literal comparison with the public Encoding lemma. | None of the three complete Lean source files is attached, at either the base or final revision. More specifically, the pack says the public `Turing.eq_pairEncode_of_pairDecode` is attached “in context via the patch,” but the E1 patch contains only the deleted private declaration and the replacement invocation. No attachment contains the public declaration. A successful rewrite at four call sites does not establish equality of the complete universally quantified statements. The change-boundary freeze check below succeeds, but full declaration-byte comparisons and blob rehashes cannot be independently reproduced from these excerpts. | Supply one complete pinned source state for each of the three files, so the patches reconstruct the other states, and the exact public Encoding declaration with its namespace/variable context. Then repeat the byte comparisons and the E1 statement comparison. No additional public-body permission is needed. |
| R1-2 | major | `workflow.md` §4 · epoch cumulative duplication ledger | The delivered ledger reports the change in duplication, but does not provide the required cumulative copied-material totals and fractions. | “New copies: none” is verified. The 5,713/7,636/8,904 line counts are total file sizes, not copied-material counts. The attached inventories give historical twin counts, selected approximate family sizes, and provenance descriptions; they do not give a reconciled final per-file copied-material numerator, denominator, and fraction. The 95 Loop and 150 Primitives twin maps are baseline inventories, and some originals have now been deleted. The complete twin sources/maps needed to independently verify the remaining provenance are absent. | Add a final per-file cumulative ledger, with named families/counterparts, exact counting convention, non-overlapping copied-material totals and fractions, and retained/deleted dispositions for the historical maps. Carry forward the recorded D-R2/D-R3 approvals and schedules. For any accumulated debt not covered by those decisions, the template's required disposition is **human acknowledgment required**, naming where and when it will be resolved. This finding does not demand fresh approval of already accepted families. |
| R1-3 | minor | Audit pack §2/§5 · deletion total | The epoch removes **83**, not 85, private declarations. | The patches remove 10 from Loop, 64 from Primitives including E1, and 9 from Hardness; they introduce no declarations. Thus `10 + 64 + 9 = 83`. The prose list also mentions `catalogPair_length` twice: within the two Encoding duplicates and again at its end. The line reduction of 1,639 is correct. | Record the pack erratum in the resolutions: **−1,639 lines, −83 privates**. Count `catalogPair_length` once. |
| R1-4 | minor | Audit pack §1 and plan §4d · public-freeze bookkeeping | The public inventory and post-E1 byte-identity wording need correction. | Loop has **8** publics including `stateWord`, not 9; the attached axiom log has exactly those eight names. Primitives has 18 and Hardness 5. Before E1 all 18 Primitives public bodies are unchanged; after E1 exactly one body contains the explicitly authorized identifier substitution. The plan's merged-RB2 row nevertheless says “18/18 publics byte-identical” without this qualification. | State the inventory as Loop 8 / Primitives 18 / Hardness 5. Distinguish unchanged signatures/statements/docstrings for all 31 from unchanged complete declaration text for 30, with the sole approved E1 body substitution. Preserve the historical pre-E1 agent attestation as such. |
| R1-5 | note — no findings | Three patch series · ownership, authorized boundaries, additions | The supplied changes obey the amended scope. | Every source path is one of the three owned files. All seven agent patches retain Codex authorship. All 83 removed declaration heads are private. Other edits are the named comments, the H4 consumer derivation, the RB2 private uses, the RB3 replacements including `clFreshTM`, and E1. No public head/signature is edited, no declaration is added, and the only import addition is `Build.Seam` in Hardness. | None. Full reconstruction remains subject to R1-1. |
| R1-6 | note — no findings | Deleted private families · pending consumers | No supplied pending-consumer obligation requires a removed original to survive. | The 76 initial dead-code targets match the three briefs exactly. The seven other removed lemmas are replaced at their current uses. Plan §4d explicitly orders deletion before 12.2c and requires the dead Catalog twins to be dropped later. The live `emCall*`, H3, Primitives F25a/F27a/F26, and Hardness relocation/reader/wipe families are retained. The §13 plan names `bufferedSecondCfg`/`a2_mapVirtual` as virtual-input precedents; neither is deleted here. | None for the supplied plan and inventories. Retain historical provenance in the later twin-disposition ledger; do not interpret an old twin map as a requirement to preserve dead originals. |
| R1-7 | note — no findings | `Build/Loop.lean` · H4 | The forwarding replacement is a strict simplification, and retaining `emLoopForwardCfg` is justified. | Two local lockstep lemmas, totaling 52 lines with their comments/separators, disappear. Their two-line caller becomes 19 lines citing `leftCfg_run` and `Turing.emit_run`, for a net reduction of 35. Padding and configuration commutation are local glue, not a new lockstep induction. `emLoopForwardCfg` is still in the retained consumer's statement and in the new commutation fact, so deleting it would require additional changes. | None. |
| R1-8 | note — no findings | `CookLevin/Hardness.lean` · `clFreshTM`, `clFresh_run` | The general-configuration seam citation preserves the displaced stream head. | The machine becomes exactly `seamCompTM clWipeTM.tm 2 clReadTM.tm (.inl none)`. The wipe endpoint is reused with only the control state changed; its stream cursor remains `pre.length`. The new proof passes `he`, `rfl`, and the strict pre-return exclusion `hf`, then invokes `clRead_run` at that cursor. There is no replacement by native initialization or a zero-head `Cfg.ofWords` seam. `clFresh_idle` and `clFresh_first` are unchanged. | None. |
| R1-9 | note — no findings | `CookLevin/Hardness.lean` · three strict swaps | All 13 reported replacement sites match the patches, including the final line numbers. | Two composition uses, one buffer-append use, and ten unary-length uses are present exactly as enumerated below. Composition retains the old time envelope through the output-length bound and monotonicity. The buffer equality is cited in the needed symmetric direction. Unary-length uses share the existing `clNative_fill true`. Task 2 reduces the file by 32 lines. | None. |
| R1-10 | note — no findings | RB2 report → `7224d118` → plan §4d · E1 approval trail | The governance trail is complete **as recorded in the packet**. | RB2 explicitly escalates the frozen public use and retains both it and the private lemma. The maintainer diff is labeled “needs your approval by merge.” The plan records PR #9 merged by the user and explicitly associates that merge with approval of `7224d118`. The E1 diff starts at RB2's final blob label `406229db` and changes exactly the escalated public line. | None for the recorded approval. The source-comparison gap is R1-1. This is verification of the attached decision trail, not independent authentication of a GitHub merge event. |
| R1-11 | note — no findings | Recorded errata · Encoding use, generated artifacts, Hardness count | The recorded corrections agree with the attached evidence at its stated level. | The public E1 use is visible in the patch and acknowledged in the plan. Hardness's inventory counts `361 + 186 + 4 + 1 + 1 = 553` privates and independently records `618 − 65 = 553`. The generated-artifact list has 1 in Nondeterminism, 1 in EXP, and 3 plus a 7-member family in SAT: 12 total, none assigned to Hardness. | None. The artifact-location claim is inventory evidence; those modules and their kernel inventory are not attached for a fresh enumeration. |
| R1-12 | note — no findings | Axiom logs and delivery scope | The attached axiom prints agree with the stated public inventory and contain no admission axiom. | There are 8 + 18 + 5 = 31 entries: `stateWord` is axiom-free; the remaining 30 list only `propext`, `Classical.choice`, and `Quot.sound`. No patch references or modifies an environment shim. The separate integration sweeps, lint runs, zip checksums, and merge placement are maintainer attestations, not independently replayed checks in this audit. | None under the commissioned kernel-checked premise. |

**Re-established patch boundaries and size ledger.**

These numbers are computed from the hunks. Starting absolute sizes/private totals are taken from the supplied baseline inventories; the deltas are independently counted.

| File | Lines before | Lines after | Line delta | Privates before | Privates after | Private delta |
|---|---:|---:|---:|---:|---:|---:|
| Loop | 5,713 | 5,515 | −198 | 214 | 204 | −10 |
| Primitives, including E1 | 7,636 | 6,374 | −1,262 | 318 | 254 | −64 |
| Hardness | 8,904 | 8,725 | −179 | 553 | 544 | −9 |
| Total | 22,253 | 20,614 | **−1,639** | 1,085 | 1,002 | **−83** |

The per-commit line arithmetic is:

- Loop: `5,713 + 2 − 165 = 5,550`; `5,550 + 19 − 54 = 5,515`.
- Primitives: `7,636 − 1,222 = 6,414`; `6,414 + 28 − 44 = 6,398`; E1 gives `6,398 + 1 − 25 = 6,374`.
- Hardness: `8,904 + 2 − 126 = 8,780`; `8,780 + 24 − 56 = 8,748`; `8,748 + 4 − 27 = 8,725`.
- Combined: `198 + 1,262 + 179 = 1,639`; `10 + 64 + 9 = 83`.

The recorded patch-index chains are internally consistent:

| File | Index chain printed in the patches |
|---|---|
| Loop | `c33e04c1 → 3e99b317 → dbb41eae` |
| Primitives | `3d969bdf → c1f48adb → 406229db → bf6244f1` |
| Hardness | `a27121c6 → 262e84fc → 830e1c3c → c63b4e7c` |

These are **not independently recomputed blob hashes**. I propagated the supplied text and line identities through the hunks without inventing missing text. The patches leave 5,458 base lines of Loop, 6,220 of Primitives, and 8,561 of Hardness unavailable. Thus they support an exhaustive classification of the supplied edits, but not the stronger claim that complete source files or complete public declaration bytes were recovered and rehashed.

For the freeze check, every removal block was classified against the binding briefs. Entire declaration removals start at the declarations' own docstrings and end before the next retained declaration. The sole partial-docstring removal adjacent to a deletion is the expressly authorized `clCount_width` sentence. The module/section comment hunks in Primitives do not edit `computesFunInTime_incFixed`, despite that theorem's name occurring in a diff hunk header. The following surviving declarations contain the substantive edits:

| File | Authorized retained material changed |
|---|---|
| Loop | One sentence in `loopHost_contracts`; the body of `emLoopHost_body_forward` |
| Primitives, agent patches | The three named comment regions; one use in `catalogPayload_length`; two use lines in `pairMap_computes` |
| Primitives, E1 | One use line in the public `computesFunInTime_stripLast` proof |
| Hardness | One sentence in `clCount_width`; `clCopy_write`; `clQueryCode_machine`; `clNative_image`; the ten enumerated unary-length uses; the body of `clFreshTM`; the proof body of `clFresh_run`; the sanctioned import |

Taking the pack's completeness assertion for the patch series as given, no other public text is changed. This independently supports the **relative freeze**: Loop 8/8 and Hardness 5/5 unchanged; Primitives 18/18 unchanged before E1, and 17/18 complete bodies unchanged after E1 with all 18 signatures, statements, and docstrings unchanged. The optional `splitSolve` stretch was not performed.

**Deletion accounting and future-consumer check.**

| Group | Independently enumerated removal count | Disposition |
|---|---:|---|
| Loop initial dead targets | 8 | Exactly `loop_silent_prefix`, `loopDebitTM`, `loopDebitCfg`, `loopBorrow_step`, `loopBorrow_run`, `loopBorrow_rewind`, `loopBorrow_correct`, `loopBody_capture` |
| Loop H4 proof pair | 2 | `emLoop_forward_apply`, `emLoop_forward_run`; replaced in the retained consumer |
| Primitives F24a/F24b/F24c/F24d/F24e/F24f | 59 | `6 + 13 + 18 + 11 + 9 + 2`; exact name set agrees with the brief |
| Primitives split orphans | 3 | `splitFind_none`, `splitCount_firstHalt`, `splitPrepare_first` |
| Primitives Encoding duplicates | 2 | `catalogPair_length` in the agent series; `catalogPair_inverse` in E1 |
| Hardness initial dead targets | 6 | Exactly `clRefClockTM`, `clRefClockCfg`, `clCount_first`, `clRefCountTM`, `clRefCount_first`, `clReadFields` |
| Hardness replaced lemmas | 3 | `clCompute_comp`, `clBuffer_append_bit`, `clA5_pt_unaryLength` |

The correct distinction is **76 already-dead declarations plus 7 eliminated by replacement**, not 83 declarations all dead in the baseline. Existing consumers of the latter seven are redirected as part of the changes.

The pending-program check does not rely on private visibility alone: a future harvest could still need a private's source. Here the supplied plans explicitly request these deletions, retain the needed live templates, and schedule removal of the corresponding dead Catalog copies. In particular, the old `emitterBank*` relocation target is superseded and deliberately deleted; its historical mention is not an instruction to preserve it for §13. H3's agreement-transfer consumer and the `emCall*` clean-call templates survive. Primitives' compare, erase, relocation, and split-controller material scheduled for later work survives. Hardness's live parallel bank and its noncanonical wipe/read/relocation infrastructure survive.

The full §13 design document and complete counterpart sources are not among these 20 attachments. I therefore do not extend this conclusion to unprovided consumer specifications or claim to have independently recomputed Catalog's liveness graph.

**Replacement reasoning.**

For H4, the added tape is inactive under `leftAction 1 id`. `leftCfg_run` supplies the entire padded trajectory, including its unchanged extra tape and head. Mapping the source state by the identity preserves the source liveness premise at every strict-prefix time. The local `Cfg.ext` fact commutes padding with `emitCfg`, and the transition agreement commutes padding with `emitAction`. Applying the public `emit_run` then gives exactly the retained consumer's endpoint, including the final action's optional emission. No stronger liveness requirement at the final time is introduced. At time zero both sides remain the same padded, prefix-adjusted initial configuration. The actual global lockstep proof and induction have been removed.

For `clFresh_run`, the wipe retains the stream word `pre ++ pairEncode w tail`, its cursor `pre.length`, and native input position `p`, while clearing the target and returning its target head to zero. The seam's single dispatch changes control only. The second phase therefore starts at the exact empty-target `clReadCfg` used by `clRead_run`, even when `pre` is nonempty. The returned stream cursor is `pre.length + 2 * w.length + 2`, with the new target word `w` and target head zero. The duration remains `a + 1 + (3 * w.length + 3)`, under the existing bound `2 * old.length + 3 * w.length + 6`. Empty `old`, empty `w`, and nonzero stream cursors require no new hypothesis. The general configuration contract is essential to this simplification. Task 3 removes 24 lines from the construction/proof and adds the one import, for a net reduction of 23.

The composition swaps remove a 22-line helper and add only output-length/monotonicity glue at its two callers. The useful inequality is the existing consequence of the first completed computation: `y.length ≤ a`, where `a` is that computation's time allowance. It is used to retain the old `2 * a + b + 2` allowance after citing the public composition row. `clNative_image` already contains the intermediate-length estimate for its polynomial envelope. No output-independent bound for the second machine is asserted: its contract is still used on the first machine's actual output. The exact public composition declaration is not reproduced in this packet, so this is an audit of the supplied replacement and its kernel-checked use, not an independent restatement of that library declaration.

**All 13 Hardness use sites, independently located after the complete RB3 series:**

| Removed helper | Retained caller | Final line |
|---|---|---:|
| `clBuffer_append_bit` | `clCopy_write` | 1,636 |
| `clCompute_comp` | `clQueryCode_machine` | 4,984 |
| `clCompute_comp` | `clNative_image` | 5,145 |
| `clA5_pt_unaryLength` | `clA5Drop_native` | 6,833 |
| `clA5_pt_unaryLength` | `clA5Field_native` | 6,901 |
| `clA5_pt_unaryLength` | `clA5StoredRound_native`, header field | 7,012 |
| `clA5_pt_unaryLength` | `clA5StoredRound_native`, header tail | 7,013 |
| `clA5_pt_unaryLength` | `clA5Next_native` | 7,029 |
| `clA5_pt_unaryLength` | `clA5Sizes_native`, header field | 7,570 |
| `clA5_pt_unaryLength` | `clA5Sizes_native`, header tail | 7,571 |
| `clA5_pt_unaryLength` | `clA5Cursor_native` | 7,933 |
| `clA5_pt_unaryLength` | `clA5Indices_native` | 7,955 |
| `clA5_pt_unaryLength` | `clA5Fragment_native` | 8,032 |

**E1 and the residual ledger.**

The deleted private's complete proposition is supplied:

```lean
private lemma catalogPair_inverse (x : List Bool) :
    ∀ a v, pairDecode x = some (a, v) → x = pairEncode a v
```

Its four previous code uses are accounted for: one in `catalogPayload_length`, two in `pairMap_computes`, and the last in the public `computesFunInTime_stripLast`. RB2 replaces the first three and leaves the fourth frozen. E1 then replaces the fourth and removes the 24-line declaration block. This is the declared exception, not an unreported agent violation. What remains missing is the other declaration required for the exact statement comparison.

The existing acknowledgment is substantive: D-R2 explicitly commissions 12.2c immediately after the retrofit, names the 150/95 historical twin families and Wrappers copies, and calls for one implementation with time and space contracts. D-R3 commissions the agreement-transfer machinery for Loop H3. These decisions should be carried into the resolutions; there is no reason to ask the human to approve those same families again.

Nevertheless, a current cumulative ledger cannot simply call the old maps “untouched.” All 95 original Loop core declarations had Catalog counterparts; 8 originals have now been deleted, leaving **87 original-side members** of that historical correspondence. Catalog's copies were not edited. The three deleted Primitives split orphans likewise had entries in the baseline twin families; other Encoding-copy dispositions also need to be reconciled against the actual map. The rewritten Primitives comment continues to disclose an additional live cross-file relocation harvest from Loop's `emCall` family. None of these facts is evidence of a new copy; all are reasons to supply the required final accounting rather than substitute a net-negative line delta for it.

Glossary: `a` and `b` are the first and second computation time allowances in the composition discussion; `y` is the intermediate word. In the seam discussion, `pre` is the stream prefix, `old` the previous target word, `w` the field being read, `tail` the following stream suffix, `p` the native input-head position, and `a` the wipe duration. These are the corresponding source declarations' variables.
```

## ===== audits/retrofit-r1-r2-pack.md =====

```
# External audit pack — chapter-1/2 retrofit, epoch R1 boundary, round 2

Round 1 (`audits/retrofit-r1-pack.md`, findings verbatim in
`audits/retrofit-r1-findings.md`) returned **0 blockers, 2 majors, 2
minors, 8 notes** — no code defect; both majors are evidence-packaging
gaps, both supplied here. Audited at commit `fb721402` (the three retrofit
target files are byte-identical there to the post-merge state your round-1
report analyzed; the tree's other changes are the out-of-scope §13
surface). The gate closes on zero blockers and zero majors; debt majors
close only by human acknowledgment.

## Disposition table (verify each)

| Round-1 finding | Disposition |
|---|---|
| R1-1 (major: no complete sources; the public Encoding lemma absent) | **Supplied.** The three complete **final** source files are attached in full (`Build/Loop.lean` 5,515, `Build/Primitives.lean` 6,374, `CookLevin/Hardness.lean` 8,725), together with the three patch series — reverse-apply them to reconstruct the base `5588628c` states and redo the full byte comparisons and blob arithmetic. `Encoding.lean` is attached in full: the public `Turing.eq_pairEncode_of_pairDecode` (line 231, with its namespace and variable context) against the deleted private's quoted proposition — perform the literal statement comparison the E1 approval assumed. |
| R1-2 (major: no cumulative duplication ledger) | **Supplied**: the standing `audits/duplication-ledger.md` (attached) — the counting convention (twin-map membership per the retrofit inventories), per-file original-/copy-side totals and declaration fractions, approximate twin-block lines, the epoch delta (0 new copies; 245 → 233 original-side members; one pair collapsed by the approved E1), and the disposition column carrying the recorded D-R2/D-R3 acknowledgments and the 12.2c schedule. Headline honesty: `Build/Catalog.lean` stands at **59% copied material by declarations** — acknowledged debt with a named resolution window, per your proposed fix no fresh approval is requested. Verify the ledger's arithmetic against the attached inventories and sources; flag any family the convention misses. |
| R1-3 (minor: −83, not −85; double-listed `catalogPair_length`) | **Erratum acknowledged** in the plan's decision log: −1,639 lines, **−83** private declarations (76 dead + 7 eliminated by replacement, your distinction adopted); `catalogPair_length` counted once. Shipped round-1 pack stays verbatim. |
| R1-4 (minor: Loop public count; post-E1 freeze wording) | **Erratum acknowledged**: Loop 8 / Primitives 18 / Hardness 5 publics; all 31 signatures/statements/docstrings unchanged; 30/31 complete declaration texts unchanged, with the one authorized E1 proof-body substitution; the agents' 18/18 attestation preserved as the historical pre-E1 statement. |
| R1-5 — R1-12 (notes) | Carried as recorded; your "76 dead + 7 replaced" accounting, the H4/`clFreshTM`/swap verifications, the E1 trail verification, and the evidence-boundary distinctions are adopted into the resolutions at close. |

## Brief for the auditor

1. Reconstruct the three base files from the attached finals and patch
   series; re-establish the public-declaration byte comparisons you could
   not complete in round 1 (Loop 8/8, Hardness 5/5, Primitives 18/18
   pre-E1 and 17/18 complete bodies post-E1 with the authorized line).
2. Perform the literal E1 statement comparison: the deleted
   `catalogPair_inverse` proposition against the attached public
   `Turing.eq_pairEncode_of_pairDecode`, in context.
3. Verify `audits/duplication-ledger.md`: the convention's fit to the
   attached inventories, the per-file counts and fractions (recompute at
   least the Loop 87 and Primitives 146 original-side figures and the
   Catalog partition), the epoch delta, and the acknowledgment state. If
   any accumulated debt lacks a named owner and window, that is a debt
   major requiring human acknowledgment.
4. Report in the standard table; the gate closes on zero blockers and
   majors.

## Repository-side attestations

As the round-1 pack, unchanged: the per-batch replays, independent axiom
prints (8 + 18 + 5, no `sorryAx`), lint, checksums, bundle verifications,
shim exclusions, and the side-branch/PR merge trail.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md` (failure mode 5 in force);
findings verbatim into `audits/retrofit-r1-r2-findings.md`.
```

## ===== audits/retrofit-r1-r2-findings.md =====

```
**Retrofit epoch R1 — round-2 external audit findings**

**Verdict: gate remains open — 0 blockers, 2 majors, 1 minor, 8 notes.** R1-1 is closed. R1-2 is not closed: the new ledger has inconsistent arithmetic and omits demonstrable copies. R1-3 and R1-4 are closed by the recorded errata, independently confirmed below. No Lean statement defect or unauthorized public change was found.

Target: the packet’s `fb721402` snapshot, relative to its recorded base `5588628c`. Evidence: this supplied bundle only, including its 16 attachments. Independently computed bundle SHA-256: `6902983404d5563980943e2795d21fb786acc563b5dcec31cf3e4c96ddd0b819`.

I reconstructed every intermediate target-file state, replayed all 46 hunks in both directions without offsets or fuzzy matching, recomputed the Git blob hashes, and compared the complete public declarations and their attached documentation. I also enumerated declarations with comments excluded, checked the dead sets against references from surviving declarations, reconstructed inventory membership, and compared the omitted duplicate families directly. Kernel checking is the commissioned premise; I did not rerun Lean or independently authenticate repository commits or merge events.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | **major** | `audits/duplication-ledger.md:10–18, 30–34` · counting convention and Catalog partition; R1-2 | The cumulative ledger still has no consistent, independently verifiable Catalog total. | The printed summands total **261**, not 249. Its Primitives partition accounts for only `143 + 3 + 1 = 147` of the historical 150 counterparts, omitting the three strengthened split-closure counterparts. Conversely, the Loop count includes its two strengthened counterparts despite the stated byte-level rule. Keeping all historical correspondence members gives a **conditional** total of 264, not 249; strict normalized twins give a different total. Catalog and Wrappers sources, the full pair manifest, and the cited A2/F2A reports are absent. Thus 423, the dead/sole-owner labels, the Wrappers denominator, and the Catalog line estimate cannot be independently reconstructed. | Define one inclusion rule; enumerate each distinct member and counterpart, including strengthened, deleted-original, and internal pairs; regenerate totals and fractions. Supply the pinned Catalog/Wrappers sources or an auditable complete correspondence with the necessary source evidence. Do not repair this by changing 249 to 261 alone. Existing D-R2 acknowledgment remains credited. |
| R2-2 | **major — debt / incomplete accounting** | Ledger `:19–24, 30–35, 44–48` · relocation family and Loop H3 | The excluded relocation “reimplementations” include exact copies, and the Loop row omits known internal copies. The packet does not establish a cleanup owner/window for the full relocation family. | After only the four corresponding identifier substitutions, **all four complete relocation declarations, including docstrings, are byte-identical** across Loop, Primitives, and Hardness; the exact map is below. This directly refutes “not byte-level copies,” Primitives’ zero copy-side count, and Hardness’s zero cross-file count. Separately, 13 H3 declarations equal their Loop originals after renaming and comment/whitespace normalization; the fourteenth has one extra simp entry. D-R3 acknowledges H3, but acknowledgment does not remove its members from the current ledger. D-R1 commissions prerequisite exports; D-R2 explicitly leaves Hardness outside 12.2c. Neither supplies an explicit cleanup assignment/window for all three copies of this relocation family. | Include these families and count each declaration once per file. Carry forward D-R2/D-R3 without renewed approval. For the omitted relocation debt, provide an existing acknowledgment that covers the exact family and names its cleanup owner/window; otherwise **human acknowledgment required**, with that owner/window. Do not label exact copies as non-copy design harvest. |
| R2-3 | **minor** | Ledger `:37–42` · epoch delta | The phrase “twelve dead originals deleted” is false. | The twelve removed historical-map members are eight dead Loop declarations, three dead Primitives split orphans, and the **live** `catalogPair_inverse`, removed after replacing its uses. The count `245 − 12 = 233` is correct. | Say **eleven dead originals plus one original eliminated by replacement**. Retain the independently verified epoch-wide distinction, 76 dead + 7 replaced. |
| R2-4 | note — no findings | Three complete finals and patch series · R1-1 reconstruction | The source-reconstruction part of R1-1 is fully repaired. | All 46 hunks reverse-apply exactly; forward replay recovers the attached finals byte-for-byte. Every old/new patch-index hash matches recomputation, including the full RB2 hashes. All eight Loop and five Hardness complete public declarations are unchanged. Primitives is 18/18 unchanged before E1 and 17/18 afterward. | Close this part of R1-1. |
| R2-5 | note — no findings | `catalogPair_inverse` / `Turing.eq_pairEncode_of_pairDecode` · R1-1 E1 comparison | The universally quantified statements are identical up to bound-variable renaming and binder presentation. | The common type is displayed below. Namespace inspection finds the same `Turing.pairDecode` and `Turing.pairEncode`, with no extra section variables, typeclass requirements, or assumptions. E1 changes exactly the one invocation in `computesFunInTime_stripLast`; its statement and documentation are unchanged. | Close the remaining part of R1-1. No additional E1 approval is needed. |
| R2-6 | note — no findings | Plan §4d decision log · R1-3/R1-4 | Both recorded errata are correct. | Independently counted: 83 removed privates and 1,639 removed lines; `catalogPair_length` occurs once among the removals. The public inventory is 8 + 18 + 5 = 31. All 31 statements/docstrings and 30 complete declaration texts are unchanged; the exception is precisely E1. The later decision-log entry qualifies the historical 18/18 attestation. | Close R1-3 and R1-4; preserve the historical pack with its explicit correction. |
| R2-7 | note — no findings | Three batches · R1-5/R1-6 | Ownership, deletion boundaries, and retained pending-consumer material remain compliant. | No declaration is added. All 83 removed declarations are private. For the first-patch dead sets, no surviving declaration references any of the 8/62/6 removed names after comment stripping. The seven further removals have their consumers redirected. The live `emCall`, H3, compare/erase/relocation, and Hardness reader/wipe families remain. Only `Build.Seam` is added to imports. | Carry R1-5/R1-6 as no findings. |
| R2-8 | note — no findings | Loop H4 · R1-7 | The forwarding replacement remains a strict simplification. | The two local lockstep lemmas disappear; the retained caller cites `leftCfg_run` and `Turing.emit_run` with local padding/configuration glue. This patch removes 35 net lines. `emLoopForwardCfg` remains used by the caller’s statement and the commutation fact. | Carry R1-7 as no findings. |
| R2-9 | note — no findings | Hardness `clFresh*` and strict swaps · R1-8/R1-9 | The seam preserves the displaced stream head, and the reported replacement sites are exact. | `clFreshTM.tm` is the stated `seamCompTM`; the `run_ofCfg` call passes the wipe endpoint and first-return cut directly to the reader at the retained cursor. `clFresh_idle` and `clFresh_first` are byte-identical. The replacement patch has exactly 2 composition citations, 1 buffer-append citation, and 10 `clNative_fill true` citations. | Carry R1-8/R1-9 as no findings. |
| R2-10 | note — no findings | E1 trail; D-R2/D-R3 · R1-10 | The recorded E1 approval and existing debt acknowledgments remain valid evidence at the packet’s stated level. | The flagged `7224d118` diff joins the agent’s `406229db` state exactly; the plan explicitly associates its approval with the user’s PR #9 merge. D-R2 names the historical Catalog/Primitives/Loop/Wrappers debt and promotes 12.2c to the next window after the retrofit. D-R3 commissions Z5 for H3. | Carry these acknowledgments forward. R2-2 concerns omitted accounting and the additional family’s cleanup disposition, not renewed approval of these decisions. |
| R2-11 | note — no findings | Evidence boundaries · R1-11/R1-12 | Historical kernel/artifact attestations are carried at their original evidentiary level. | The reconstructed Hardness baseline independently contains 553 privates. The artifact-location correction and the clean 31-entry axiom audit remain recorded in the inventories/prior findings; the underlying artifact modules and axiom logs are not attached here. No patch touches or references an environment shim. | Carry R1-11/R1-12 without claiming a new kernel/log replay. |

**Reconstruction and freeze evidence.**

The following are independently recomputed Git blob hashes, abbreviated here to the lengths used in the patch headers. The association with the named repository commits remains packet metadata.

| File | Recomputed blob sequence | Line counts at those states | Private counts at those states |
|---|---|---|---|
| Loop | `c33e04c1 → 3e99b317 → dbb41eae` | `5713 → 5550 → 5515` | `214 → 206 → 204` |
| Primitives | `3d969bdf → c1f48adb → 406229db → bf6244f1` | `7636 → 6414 → 6398 → 6374` | `318 → 256 → 255 → 254` |
| Hardness | `a27121c6 → 262e84fc → 830e1c3c → c63b4e7c` | `8904 → 8780 → 8748 → 8725` | `553 → 547 → 544 → 544` |

The independently verified epoch arithmetic is:

```text
Lines:    (5713 − 5515) + (7636 − 6374) + (8904 − 8725)
        = 198 + 1262 + 179 = 1639.
Privates: (214 − 204) + (318 − 254) + (553 − 544)
        = 10 + 64 + 9 = 83.
Dead:     8 + 62 + 6 = 76.
Replaced: 2 + 2 + 3 = 7.
```

The complete declaration comparison includes attached docstrings and intervening closure comments. The sole changed public line is:

```diff
-          rw [catalogPair_inverse x u v hd]
+          rw [Turing.eq_pairEncode_of_pairDecode x u v hd]
```

**Literal E1 statement comparison.**

The deleted private lies in `namespace Turing.FinTM`; the public theorem lies in `namespace Turing`. Expanding their explicit/curried binders and renaming the public theorem’s `z, a, b` to `x, a, v` yields the same type:

```lean
∀ (x a v : List Bool),
  Turing.pairDecode x = some (a, v) → x = Turing.pairEncode a v
```

This is equality of the quantified proposition, not merely evidence that a particular rewrite succeeds. The source spellings and proofs need not be byte-identical.

**Independent ledger recomputation.**

I enumerated the 95 Loop core members from the inventory’s F1–F15 member lists and checked their presence in both reconstructed states. For Primitives, F01–F10 contribute 80; F13–F22 contribute 69; `catalogPair_inverse` contributes 1, giving 150. All 150 names exist in the reconstructed baseline. Intersecting these historical maps with the final declarations gives:

| Historical map | Baseline members | Removed members | Surviving originals | Final file declarations | Fraction |
|---|---:|---|---:|---:|---:|
| Loop → Catalog | 95 | Six standalone debit declarations, `loop_silent_prefix`, `loopBody_capture` | `95 − 8 = 87` | `204 + 8 = 212` | `100 × 87 / 212 = 41.0377%` |
| Primitives → Catalog | 150 | `splitFind_none`, `splitCount_firstHalt`, `splitPrepare_first`, `catalogPair_inverse` | `150 − 4 = 146` | `254 + 18 = 272` | `100 × 146 / 272 = 53.6765%` |

Thus 87, 146, their rounded 41%/54%, and `245 → 233` are correct **for the expanded historical maps**. They are not complete cumulative per-file totals and are not strict byte-twin totals. The inventories explicitly exclude from exact matching two Loop counterparts (`loopHost_prepare`, `loopHost_contracts`) and three Primitives counterparts (`splitSolve_of_body`, `splitSolve_source`, `splitSolve_closed`). Strict normalized surviving-original counts would instead be 85 and 143.

The Catalog arithmetic exposes the inconsistency step by step:

```text
Printed partition: 143 + 3 + 1 + 87 + 8 + 17 + 2 = 261.
Printed numerator: 249 = 143 + 87 + 17 + 2.
Difference:        261 − 249 = 12.
```

The omitted 12 are precisely the printed `3 + 1 + 8` historical-copy categories. Additionally, the Primitives partition should contain all 150 historical members under the expanded convention, whereas its `143 + 3 + 1` contains only 147.

Assuming the packet’s remaining source counts and disjointness claims, the two consistent alternatives would be:

```text
Expanded historical correspondences:
  150 + 95 + 17 + 2 = 264; 100 × 264 / 423 = 62.4113%.
Strict normalized historical twins:
  147 + 93 + 17 + 2 = 259; 100 × 259 / 423 = 61.2293%.
```

These are **conditional reconciliations, not certified Catalog totals**: the Catalog/Wrappers sources and the complete internal/copy-side maps are missing. The source evidence is also insufficient to decide whether the three orphan counterparts are live sole owners or dead, or whether the inverse counterpart is dead. Those labels require the Catalog reference graph. Wrappers’ “small” supplies neither a denominator nor a reproducible fraction. The approximately 6,000/450 line claims likewise remain attestations.

For the attached original-side blocks, an explicit span count—attached docstring and intervening closure note through the last code line, excluding separating blank/module-note blocks—gives **2,009 lines for the 87 Loop members** and **3,162 for the 146 Primitives members**. Different block-attribution conventions can change these counts; the ledger should state the rule that produces its approximate 2,350/3,300 figures.

**Omitted families verified from the full sources.**

Every row of this map is identical across its three files after replacing the four family identifiers consistently. Even whitespace and docstrings then match.

| Loop declaration | Primitives declaration | Hardness declaration |
|---|---|---|
| `emCallAction` | `emitterP2Action` | `clSlotAction` |
| `emCallCfg` | `emitterP2Cfg` | `clSlotCfg` |
| `emCall_apply` | `emitterP2_apply` | `clSlot_apply` |
| `emCall_relocate_run` | `emitterP2_relocate_run` | `clSlot_run` |

The blocks occupy Loop lines 3520–3595, Primitives 4699–4774, and Hardness 1803–1878: **73 declaration/docstring lines per file**, excluding the three inter-declaration blank lines. This is one four-declaration family with two later copies, not three unrelated reimplementations.

H3’s exact normalized copies have suffixes `fuel_capture`, `input_rewind`, `fuel_rewind`, `fuel_copy`, `fuel_return`, `fuel_setup`, `prepare`, `release`, `borrow_step`, `borrow_run`, `borrow_rewind`, `borrow`, and `reject`, mapping `loopHost_*` to `emLoopHost_*`. The `init` pair differs only by the added `loopHost` simp entry. The H3 originals already belong to the 87-member core map and must not be counted again; the copied declarations are additional members.

Keeping the ledger’s expanded-map convention and adding **only** the omitted exact families verified above gives these lower bounds:

| File | Distinct members after these corrections | Fraction |
|---|---:|---:|
| Loop | `87 + 4 + 13 = 104` | `100 × 104 / 212 = 49.0566%` |
| Primitives | `146 + 4 = 150` | `100 × 150 / 272 = 55.1471%` |
| Hardness | At least 4 | `100 × 4 / 549 = 0.7286%` |

The alternative strict-normalized counts would start at 102/212 and 147/272 for Loop and Primitives. Neither version counts the near-copy H3 `init`, other semantic reimplementations, or unseen counterpart material. These lower bounds demonstrate why the current ledger cannot be accepted as complete.

D-R2’s scheduled Catalog deduplication and D-R3’s H3 acknowledgment are substantive and remain accepted. The repair needed is accurate current accounting plus a documented cleanup disposition for the omitted relocation family. No source changes, renewed E1 permission, or renewed approval of already accepted Catalog/H3 debt are required by this report.

Glossary: In the common Lean type, `x` is the encoded Boolean list, and `a` and `v` are its decoded components. Other identifiers are existing source declarations or recorded audit labels.
```

## ===== audits/duplication-ledger.md =====

```
# Cumulative duplication ledger

The standing per-file accounting of copied proved material that
`workflow.md` §4 requires at every epoch boundary. Created as the
retrofit-R1 round-1 repair (R1-2); **rebuilt at round 2** (R2-1/R2-2 of
`audits/retrofit-r1-r2-findings.md`): the first version's arithmetic was
inconsistent (summands 261 against a printed 249), its inclusion rule was
applied asymmetrically, and it **misclassified an exact three-file copy
family as "design-harvest reimplementation"** — the round-2 auditor
proved the four relocation declarations byte-identical across `Loop`,
`Primitives`, and `Hardness` after consistent identifier substitution,
and found the 13 exact Loop-internal H3 copies omitted. This version
adopts one inclusion rule, enumerates every family, and uses the
auditor's independently computed figures wherever they exist.

## Counting convention (one rule)

**Primary rule — expanded correspondence membership**: a declaration is a
ledger member iff it belongs to a *recorded cross-declaration
correspondence* — the retrofit inventories' twin maps **including their
strengthened-counterpart rows**, the A2/F2A reports' declared copies, and
the round-2 audit's verified relocation and H3 families. Each member is
counted **once per file it inhabits**. (Secondary, where it differs: the
*strict normalized-byte-twin* count excludes the five strengthened
counterparts — Loop's `loopHost_prepare`/`loopHost_contracts`,
Primitives' `splitSolve_of_body`/`_source`/`_closed` — and H3's one
near-copy `_init` pair.) Fractions are members over the file's total
declarations. Line figures use the round-2 audit's span rule — attached
docstring and intervening closure note through the last code line,
excluding separating blank/module-note blocks — with the auditor's
computed values where available and estimates under the same rule marked
`≈`.

## State after retrofit epoch R1 (the merged PRs #9/#10)

| File | Total decls | Original-side members | Copy-side members | All members | Fraction | Lines in member blocks |
|---|---:|---:|---:|---:|---:|---:|
| `Build/Loop.lean` | 212 | 87 →Catalog (of the historical 95; strict 85) + 4 relocation originals (`emCallAction`/`emCallCfg`/`emCall_apply`/`emCall_relocate_run`, the batch-L source of the three-file family) | 13 H3 exact copies (`emLoopHost_*`; their `loopHost_*` originals are already in the 87 and are not double-counted; the `_init` near-copy noted, uncounted) | **104** | **49.1%** | 2,009 (auditor) + 73 + ≈512 |
| `Build/Primitives.lean` | 272 | 146 →Catalog (of the historical 150; strict 143) | 4 relocation copies (`emitterP2Action`/`emitterP2Cfg`/`emitterP2_apply`/`emitterP2_relocate_run` — **byte-identical to Loop's after identifier substitution**, round-2 verified) | **150** | **55.1%** | 3,162 (auditor) + 73 |
| `CookLevin/Hardness.lean` | 549 | 0 | 4 relocation copies (`clSlotAction`/`clSlotCfg`/`clSlot_apply`/`clSlot_run` — likewise byte-identical) | **4** | **0.73%** | 73 |
| `Build/Catalog.lean` | 423 | 0 | 150 Primitives-sourced + 95 Loop-sourced + 17 Wrappers-sourced (10 `f2_timed*`, 7 `catalog_redirect*`) + 2 in-file `a2_` duplicates of `f2_` sum facts | **264** | **62.4%** (strict: 259, 61.2%) | ≈6,000 |
| `Build/Wrappers.lean` | 29 (10 pub + 19 priv) | 17 | 0 | **17** | **58.6%** | ≈450 |
| `Build/Embed.lean`, `Build/Seam.lean`, `Build/VirtualInput.lean`, `Build/Zone.lean`, `Simulation.lean`, `Codes2Tape.lean` | — | 0 | 0 | 0 | 0% | 0 |

Copy-side counts deliberately include copies whose originals were deleted
in R1 (the copies persist; deletion of an original does not shrink the
copy side). The Loop inventory's recorded dispositions — the 8 dead
Loop-twin copies in Catalog (`f2_loop_silent_prefix`,
`f2_loopBody_capture`, the six `f2_loopDebit*`/`f2_loopBorrow*`) and the
orphans' dead twins — are **dispositions for 12.2c, not subtractions
here**; sole-owner/dead labels require Catalog's reference graph and are
settled at that window. Internal near-duplicates flagged by the
inventories but outside the rule (`clCountTape ≡ bufferTape`, the H3
`_init` pair) are noted, uncounted.

**Epoch R1 delta**: new copies **0**; the historical maps lost **eleven
dead originals plus one live original eliminated by replacement**
(`catalogPair_inverse`, the human-approved E1) — 245 → 233 surviving
→Catalog originals (R2-3 wording); net −1,639 lines, −83 private
declarations (76 dead + 7 replaced).

## Acknowledgment and disposition state

| Debt family | Acknowledgment | Cleanup owner and window |
|---|---|---|
| Catalog's 264 copy-side members (↔ Primitives/Loop/Wrappers + in-file) | **D-R2** (user, 2026-10-09) | the **12.2c** per-theme refactor, promoted to the next window after R1; precondition (shrunken `Build/` files) met |
| Loop's 13 H3 copies (+1 near-copy) | **D-R3** (user, 2026-10-09) commissioned the collapse mechanism — §13 Z5, **now proved** (vhost-f1) | **ACKNOWLEDGED (user, 2026-10-09): retrofit batch RB4** (Loop), consuming Z5, window: after the A-S1 fill gate closes |
| The three-file relocation family (4 decls × 3 files; pre-policy legacy, disclosed at its batches as "private harvest" but verbatim in fact) | **the user, 2026-10-09** (the round-2 audit's R2-2 disposition) | **ACKNOWLEDGED (user, 2026-10-09): the same RB4** (all three files), replacing the family with the R1 selected-tape exports (D-R1, proved) + Z5 agreement transfer, per the inventories' own analysis of what unlocks it |

Any new copy in a future delivery enters through the per-delivery ledger
and the one-fifth escalation rule of `workflow.md` §4.
```

## ===== audits/retrofit-inventory/loop.md =====

```
# Retrofit inventory — `Build/Loop.lean` (commissioned report, verbatim)

*Maintainer provenance note: produced 2026-10-09 by a commissioned read-only
inventory agent at HEAD `af3952a3` (file unchanged since earlier that day);
source-text liveness analysis (token matching with comments stripped,
transitive closure from the public declarations) — no kernel walker run.
Feeds plan §4d. The report follows verbatim.*

---

# Retrofit inventory: privates in `TCSlib/Complexity/TuringMachine/Build/Loop.lean`

**Bottom line.** Only two families can be acted on under the strict-simplification bar:
- **8 dead declarations** (about 160 lines).
- **One 3-declaration family (H4).** It re-derives a forwarding lemma the file avoided because it was unproved at the time. That lemma, `Turing.emit_run` in Wrappers, is now proved.

The other 87 declarations whose role matches R1, R2 or the catalog have to be left alone. They all fail on structure:
- the hosts are single, hand-built transition tables (not composites);
- the decision/find loop runs the body again every round, which R2 cannot express;
- the phase boundaries are not `Cfg.ofWords`-shaped.

## How the inventory was built

- Every declaration was taken from the source with a Python regex over `^(private )?(noncomputable )?(def|theorem|lemma|abbrev|structure|inductive|instance) <name>`. Two docstring lines that start with the word "lemma" (5497, 5506) were excluded.
- **Result: 222 declarations = 214 private + 8 public.** `grep -c '^private '` gives 215; the extra hit is the docstring line 2703, not a declaration.
- A partition of the 214 into 33 families was checked by script: every private appears exactly once.
- References were computed by token matching on bodies with comments stripped, then taken transitively from the 8 publics.
- Catalog copies were matched by name (`f2_<name>`, `a2_<name>`) and compared text-for-text after removing the prefix.

## 1. Public declarations and file layout

| # | Line | Public declaration | Role | Privates reached (transitively) |
|---|---|---|---|---|
| 1 | 122 | `Turing.stateWord` | Seam word assignment: state on tape 0, other tapes blank | 0 |
| 2 | 140 | `Turing.loop_run` | Frozen summation lemma (empty-output terminal); nothing in the file uses it | 0 |
| 3 | 2392 | `Turing.FinTM.exists_loopCfgTM` | Configuration-level loop: startup, per-round accept-or-advance segments, halted `[false]` terminal | 85 |
| 4 | 2519 | `exists_loopTM` | Decision loop, budget `c(T+1)(R+2)` (proved via #3 and `loop_halted_run`) | 86 |
| 5 | 2633 | `exists_loopFindTM` | Find loop: first accepting payload, or `[]` | 86 |
| 6 | 5508 | `exists_emitLoopTM` | Emitting loop: concatenation of per-round chunks | 82 |
| 7 | 5645 | `exists_installCallTM` | Clean call, install mode: `Cfg.ofWords` seam to `Cfg.ofWords` seam, first return, `0 < C.k` | 91 |
| 8 | 5691 | `exists_emitCallTM` | Clean call, emit mode: argument kept, `f arg` sent to output | 91 |

The privates form three independent clusters:
- **Core decision/find loop**: 95 privates. #3–#5 use all except the 8 dead ones; #6 shares 54 of them.
- **`emCall*`**: 91 privates, used only by #7 and #8. They use no core privates.
- **`emLoop*`**: 28 privates, used only by #6.

**File layout**
- 1–14: header, imports (Convention, Wrappers, Composition, Mathlib).
- 16–116: module docstring.
- 118–177: `namespace Turing` (`stateWord`, `loop_run`).
- 179–5713: `namespace Turing.FinTM`.
  - 181–322: run/trace utilities.
  - 324–437: debit arithmetic and buffer helpers.
  - 439–563: standalone debit machine (dead).
  - 565–717: stop-at-anchor body wrapper.
  - 719–836: host state and controller (`loopHost`).
  - 838–2187: host phase lemmas.
  - 2188–2359: `loopHost_bound` and `loopHost_contracts`.
  - 2361–2697: publics #3–#5 and the two summation lemmas.
  - 2699–4605: `/-! ### Clean-call phase machinery` (`emCall*`; stray sub-comment at 3356).
  - 4607–5595: `/-! ### Forwarding loop controller` (`emLoop*`) and #6.
  - 5597–5711: publics #7 and #8.

## 2. Private families

Line counts include docstrings. All families have 16 or fewer members, so every member is listed.

### Core loop — 95 privates, lines 181–2614

**F1. Run/trace utilities** — 9 members, 181–322, about 134 lines.
- Members: `loop_live_prefix` 182, `loop_silent_prefix` 193, `loop_first_halt` 207, `loop_orbit_inv` 230, `loop_fuel_width` 240, `loop_input_move_le` 247, `loop_input_run_le` 261, `loop_output_length_le` 277, `loop_rewind_bounded` 294.
- Role: generic run facts — live prefix, first-halt cut, orbit invariant, fuel width, input/output displacement bounds, bounded input rewind.
- **KEEP** (8). `loop_silent_prefix` is **DEAD**.
- Not replaceable: §12 has no lemmas of this kind. `loop_rewind_bounded` already wraps the public `rewind_scan`; `loop_fuel_width` cites the public `output_length_le`.

**F2. Fixed-width debit arithmetic** — 10 members, 324–411, about 79 lines.
- Members: `loopDebit` 326, `loopBorrowPos` 332, `loopBorrowPos_le` 337, `loopDebit_length` 343, `loopValue` 349, `loopValue_bits` 354, `loopDebit_value` 365, `loopDebit_success` 379, `loopDebit_iterate_length` 390, `loopDebit_iterate_value` 400.
- **KEEP.** The catalog has `incFixed`/`incrementTM` (increment) but no decrement.

**F3. Buffer read/write helpers** — 2 members, 413–437.
- Members: `loopBuffer_read` 414, `loopBuffer_write` 422.
- **KEEP.**

**F4. Standalone one-tape debit machine** — 6 members, 439–563, about 125 lines.
- Members: `loopDebitTM` 443, `loopDebitCfg` 459, `loopBorrow_step` 466, `loopBorrow_run` 492, `loopBorrow_rewind` 517, `loopBorrow_correct` 551.
- Its own docstring says it "privately re-derives the counter template".
- **DEAD.** The members refer only to each other. `loopBorrow_correct` has no referrers; its only other mention is the historical docstring at 2205. The host performs the borrow itself in F13.

**F5. Stop-at-anchor body wrapper** — 6 members, 565–717, about 148 lines.
- Members: `loopBodyTM` 569, `loopBodyCfg` 592, `loopBody_stop` 604, `loopBody_step` 622, `loopBody_run` 669, `loopBody_capture` 697.
- Role: a release bit forces one action at the anchor; the next anchor entry halts the body; a one-cell flag tape records "returned to anchor" versus "genuine halt".
- **Role matches R2 (`seamReleaseTM` plus exit dispatch) → LEAVE** (5 members).
- `loopBody_capture` is **DEAD**: no referrers, superseded by `loopHost_body_capture` through `loopBodySource`.

**F6. Host state and controller definitions** — 3 members, 719–836.
- Members: `LoopHostState` 720, `loopControlAction` 739, `loopHost` 763 (14-phase controller).
- **KEEP.**

**F7. Relocation and capture glue (R1-shaped)** — 12 members, about 116 lines.
- Members: `loopFuelSource` 724, `loopBodySource` 732, `loopHost_body_capture` 840, `loopHost_fuel_capture` 854, `loopHost_init` 866, `loopFuelCfg` 1076, `loopFuel_run` 1085, `loopFuel_init` 1098, `loopFuelCaptured` 1368, `loopBodyPadded` 1486, `loopCall` 1496, `loopBodySource_run` 1506.
- Role: move the fuel machine onto the right tape block and the stopped body onto the left block (public `rightAction`/`leftAction`, `rightCfg_run`/`leftCfg_run` from Simulation.lean), with output captured via the public `captureAction`/`capture_run`.
- **Role matches R1 → LEAVE.**

**F7b. Relocated layout versus controller frame identities** — 4 members, about 152 lines.
- Members: `loopFuelCaptured_frame` 1387, `loopReady_call` 1562, `loopCall_frame` 1679, `loopCall_reframe` 1706.
- Role: tape-block bookkeeping that matches relocated configurations against `loopFrame`.
- **Role matches R1 (`embedSilentCfg` frame parameters) → LEAVE.**

**F8. Controller frame algebra** — 9 members, about 115 lines.
- Members: `loopControl_idle` 875, `loopFrame` 900, `loopWrite` 920, `loopControl_apply` 927, `loopFrame_payload` 1115, `loopFrame_counter` 1125, `loopFrame_flag` 1881, `loopFlag_clear` 1890, `loopControl_payload` 1019.
- **KEEP.**

**F9. Payload replay (find mode)** — 7 members, about 173 lines.
- Members: `loopReplayTM` 963, `loopReplayCfg` 973, `loopReplay_step` 979, `loopReplay_run` 1003, `loopHost_replay` 1039, `loopHost_payload_rewind` 1973, `loopHost_frame_replay` 2026.
- **KEEP.** No catalog row emits a tape's contents to the output. `loopHost_replay` already relocates with a single `rightCfg_run` citation.

**F10. Fuel setup, phases 0–3 (capture tape to counter)** — 9 members, 1133–1365, about 225 lines.
- Members: `loopHost_fuel_rewind` 1137, `loopCopyTape` 1187, `loopCopy_read` 1191, `loopCopy_erase` 1196, `loopCopy_initial` 1209, `loopCopy_final` 1217, `loopHost_fuel_copy` 1231, `loopHost_fuel_return` 1282, `loopHost_fuel_setup` 1337.
- **Role matches the catalog's `transferTM` → LEAVE.**

**F11. Startup, prepare, release** — 5 members, about 116 lines.
- Members: `loopHost_input_rewind` 883, `loopHost_prepare` 1446, `loopReady` 1375, `loopHost_release` 1601, `loopHost_start` 1632.
- **KEEP.** Borderline: this is a linear chain of phases (R2-shaped), but its boundaries are not canonical, so it would be LEAVE anyway.

**F12. Body-call returns** — 2 members, 1515–1675.
- Members: `loopHost_anchor_return` 1521, `loopHost_halt_return` 1652.
- **Role matches R2 (first-return cut) → LEAVE.**

**F13. In-host borrow and reject** — 5 members, 1736–1967, about 213 lines.
- Members: `loopHost_borrow_step` 1738, `loopHost_borrow_run` 1776, `loopHost_borrow_rewind` 1809, `loopHost_borrow` 1859, `loopHost_reject` 1901.
- **KEEP** (debit logic).

**F14. Accept, round, bound, contracts** — 4 members, 2056–2359, about 302 lines.
- Members: `loopHost_accept` 2061, `loopHost_round` 2127, `loopHost_bound` 2190, `loopHost_contracts` 2214.
- **KEEP.** These are the implementation behind #3–#5.

**F15. Summation** — 2 members.
- Members: `loop_halted_run` 2445 (used by #4), `loop_find_run` 2584 (used by #5).
- **KEEP.** R2 provides no summation over loop rounds.

### Clean call (`emCall*`) — 91 privates, lines 2707–4605

**G1. Captured evaluation on a virtual input** — 6 members, 2707–2835.
- Members: `emCallIdleTM` 2709, `emCallEvalTM` 2717, `emCallEvalCfg` 2730, `emCall_eval_run` 2741, `emCall_eval_initial` 2767, `emCall_eval_first` 2800.
- **KEEP.** The virtual input comes from `bufferedCompTM`'s second phase. Embed.lean's own header puts this out of R1's scope (R1 does not "alter the source input word").

**G2. Marked-interval cleaner** — 12 members, 2837–3067, about 220 lines.
- Members: `emCallInterval` 2839, `emCallCleared` 2844, `emCall_cleared_step` 2848, `emCallClearTM` 2862, `emCallClearCfg` 2881, `emCall_clear_left` 2890, `emCall_cleared_zero` 2939, `emCall_cleared_all` 2946, `emCall_clear_scan` 2958, `emCall_origin_erase` 2985, `emCall_clear_origin` 3000, `emCall_clear_run` 3033.
- **Role matches the catalog's `clearTM` → LEAVE.**

**G3. Visited-interval tracker** — 16 members, 3069–3358, about 275 lines.
- Members: `emCallSpan` 3071, `emCall_span_extend` 3076, `emCallSlots` 3089, `emCallTrackTM` 3096, `emCallTrackCfg` 3118, `emCallTrackMid` 3127, `emCall_track_action` 3137, `emCall_track_stamp` 3174, `emCallLo` 3200, `emCallHi` 3206, `emCall_track_extent` 3213, `emCall_track_support` 3235, `emCall_span_zero` 3263, `emCall_track_initial` 3275, `emCall_track_run` 3302, `emCall_track_computes` 3348.
- **KEEP.** R1's space lemmas are proof-level statements, not marker tapes written by a machine.

**G4. Tracker-to-cleaner bridge and first-entry cut** — 4 members, 3360–3466.
- Members: `emCall_span_interval` 3362, `emCall_track_clearable` 3377, `emCall_first_entry` 3415, `emCall_clear_first` 3439.
- **KEEP.** `seamCompTM` takes a cut as a hypothesis; nothing in §12 produces one.

**G5. Right-boundary normalizer** — 9 members, 3468–3639, about 164 lines.
- Members: `emCallRightTM` 3471, `emCallRightCfg` 3487, `emCall_right_step` 3494, `emCall_right_run` 3507, `emCallRightScan` 3520, `emCall_right_scan` 3529, `emCall_right_finish` 3571, `emCall_right_endpoint` 3601, `emCall_right_computes` 3627.
- **KEEP, borderline.** The `.inl` branch is `embedEmitRetTM` with the identity selection (halt-to-live), followed by an input-head scan. Rebuilding it as R1′ plus `seamCompTM` adds a dispatch step and is a rewrite, not a simplification.

**G6. Prepared-evaluation composite** — 1 member: `emCall_prepared_eval_first` 3651.
- **KEEP.**

**G7. Generic relocation core** — 4 members, 3683–3758, about 73 lines.
- Members: `emCallAction` 3685, `emCallCfg` 3694, `emCall_apply` 3705, `emCall_relocate_run` 3722.
- This is the R1 core in disguise: a partial inverse `select` plays the role of `embedSlot`; `emCall_apply` corresponds to `embedSilent_apply`; `emCall_relocate_run` corresponds to `embedEmitTM_runFrom`, plus a state embedding and a guard.
- **Role matches R1 → LEAVE.**

**G8. Two-tape finalizer** — 8 members, 3760–4040, about 274 lines.
- Members: `emCallFinishTM` 3763, `emCallFinishCfg` 3794, `emCall_erase_last` 3801, `emCall_finish_arg` 3815, `emCall_finish_rewind` 3864, `emCall_finish_transfer` 3903, `emCall_finish_erase` 3953, `emCall_finish_run` 3994.
- **Role matches the catalog's `clearTM`/`transferTM` → LEAVE.**

**G9a. Layout and selection algebra** — 13 members, 4052–4222, about 135 lines.
- Members: `emCallTripleIndex` 4053, `emCallTripleSelect` 4064, `emCall_triple_inverse` 4072, `emCallPairIndex` 4080, `emCallPairSelect` 4085, `emCall_pair_inverse` 4092, `emCallLayout` 4123, `emCall_layout_cases` 4130, `emCall_layout_triple` 4157, `emCall_layout_pair` 4185, `emCall_triple_pair` 4193, `emCall_triple_other` 4203, `emCall_pair_triple` 4217.
- These play the role of R1's `embedSlot_selected`/`embedSlot_unselected`, but those are **private** in Embed.lean, so they could not be cited even in principle.
- **Role matches R1 → LEAVE.**

**G9b. Frame transport identities** — 8 members, 4224–4497, about 183 lines.
- Members: `emCallFrame` 4226, `emCallBankFrame` 4234, `emCall_bank_initial` 4249, `emCall_bank_final` 4287, `emCall_prepare_initial` 4382, `emCall_prepare_final` 4395, `emCall_finish_initial` 4451, `emCall_finish_final` 4478.
- **Role matches R1 → LEAVE.**

**G9c. Controller and phase sequencing** — 10 members, 4042–4605, about 216 lines.
- Members: `emCallSource` 4044, `emCallState` 4049, `emCallTM` 4101, `emCall_bank_step` 4331, `emCall_banks_run` 4362, `emCall_prepare_run` 4422, `emCall_finalize_run` 4501, `emCall_complete` 4532, `emCall_exit_fixed` 4560, `emCall_first` 4581.
- Each phase ends with a silent dispatch (`controlAction 0`), which is `seamCompTM`'s dispatch step.
- **Role matches R2 → LEAVE.** `emCall_exit_fixed`/`emCall_first` supply the public first-return clause and stay regardless.

### Forwarding loop (`emLoop*`) — 28 privates, lines 4609–5466

**H1. Output-prefix commutation** — 2 members: `emLoop_step_prefix` 4611, `emLoop_run_prefix` 4630.
- **KEEP.**

**H2. Forwarding host definition** — 1 member: `emLoopHost` 4643.
- Its body branch uses `emitAction`; every other state falls through to `loopHost.tr`.
- **KEEP.**

**H3. Verbatim re-proofs of `loopHost` phase lemmas** — 14 members, 4657–5181, about 512 lines.
- Members: `emLoopHost_fuel_capture` 4658, `_init` 4670, `_input_rewind` 4680, `_fuel_rewind` 4699, `_fuel_copy` 4754, `_fuel_return` 4805, `_fuel_setup` 4860, `_prepare` 4896, `_release` 4939, `_borrow_step` 4967, `_borrow_run` 5005, `_borrow_rewind` 5038, `_borrow` 5088, `_reject` 5115.
- Scripted diff: 13 are byte-identical to their `loopHost_*` counterparts after renaming `emLoopHost`→`loopHost`. `_init` differs only by one extra simp lemma.
- **KEEP for this retrofit** — no §12 facility removes them. See the out-of-scope notes at the end.

**H4. Local re-derivation of `emit_run`** — 3 members, 5183–5240, about 56 lines.
- Members: `emLoopForwardCfg` 5185, `emLoop_forward_apply` 5192, `emLoop_forward_run` 5210.
- Its docstring (line 5206) says it was "proved locally so this batch does not depend on the concurrent `Turing.emit_run` admission". `Turing.emit_run` (Wrappers.lean:273) is now proved; Wrappers.lean has 0 sorries.
- **REPLACE (actionable).** Borderline on the facility: what replaces it is R1's exported precursor `emit_run` plus Simulation's `leftCfg_run`, not `embedEmitTM` itself. Details in section 3.

**H5. Forwarding call and round** — 7 members, 5242–5419, about 172 lines.
- Members: `emLoopCall` 5244, `emLoopCall_frame` 5255, `emLoopHost_body_forward` 5275, `emLoopHost_anchor_return` 5294, `emLoopCall_empty` 5332, `emLoopHost_start` 5346, `emLoopHost_round` 5370.
- **KEEP.** `emLoopHost_body_forward` becomes a direct `emit_run` citation if H4 is done. `emLoopHost_anchor_return` is a 36-line near-copy of `loopHost_anchor_return` (forward instead of capture).

**H6. Prefix summation** — 1 member: `emLoop_sum` 5427.
- **KEEP.**

### Dead-candidate evidence

`grep -nw` shows the declaration and nothing else for `loop_silent_prefix` (193) and `loopBody_capture` (697). The F4 names appear only inside lines 443–563, plus the docstring mention of `loopBorrow_correct` at 2205. The reachability computation puts all 8 outside the closure of every public declaration.

## 3. What would replace each REPLACE-role family, and why most must stay

Facts that block the replacements, checked against the sources:
- **R1 only describes its own machine.** It has lockstep lemmas for `embedSilentTM`/`embedEmitTM ι M` and the returning forms, but no "any host whose table agrees with the embedded action" lemma (the `hagree` form that `capture_run`/`emit_run` have).
- **The hosts are monolithic.** `loopHost` and `emCallTM` are single hand-built transition tables, not composites.
- **R2 has no way to start inside phase 2.** Every Seam theorem starts from `c₀.mapState Sum.inl`. `exists_loopCfgTM`'s per-round segments start at `cfg i`, inside the looping phase.
- **R2 has no back-edge.** `seamCompTM` is a one-shot sequential composite; the loop re-enters the body every round.
- **Catalog routines are canonical-only.** `transferTM_run`, `clearTM_run` and the rest are stated only from `Cfg.ofWords` with heads at the origin.

| Family | Would-be facility | Boundaries canonical? | Verdict |
|---|---|---|---|
| F7 (12) | R1 `embedSilentTM`/`embedSilentRetTM` | No: fuel residue kept, capture head at word end | LEAVE. Already one- to three-line citations of public Simulation/Wrappers lemmas; citing R1 means redefining `loopHost` as a composite |
| F7b (4) | R1 `embedSilentCfg` frame parameters | No | LEAVE (only pays off after an R1/R2 rebuild of the host) |
| G7 (4), G9a (13), G9b (8) | R1 `embedEmitTM`, `embedSlot` | Internal boundaries are not: data with holes, arbitrary heads | LEAVE. Needs an agreement lemma R1 lacks, a state embedding, and a guard; `embedSlot` is private. **Strongest R1 candidate** if R1 ever exports an agreeing-host lockstep |
| F5 (5), F12 (2) | R2 `seamReleaseTM` plus exit dispatch | — | LEAVE. Release must be re-armed every round by the controller (phases 6 and 9 dispatch to `(anchor, true)`), plus the halt-kind flag tape |
| G9c (10) | R2 `seamCompTM_*_ofCfg` | Outer entry yes; internal boundaries and emit-mode exit (`with output := …`) no | LEAVE. The bank loop runs over `Fin (M.k+1)` inside one state space, while R2 composes exactly two machines |
| F10 (9) | Catalog `transferTM` (3\|w\|+3) | No: capture head starts at \|w\|, arbitrary residue; copies and erases in one forward pass | LEAVE |
| G2 (12) | Catalog `clearTM` (2\|w\|+2) | No: data with holes, cells at negative positions (`lo ≤ 0`), head anywhere, marker tapes | LEAVE |
| G8 (8) | Catalog `clearTM` + `transferTM` | No: both heads enter at the right blanks; emit mode replays to output, which no catalog row does | LEAVE |
| **H4 (3)** | `Turing.emit_run` (Wrappers E2, R1's precursor) + `leftCfg_run` | General configurations — no canonical boundary needed | **REPLACE.** Glue: a padded source `P.tr = leftAction 1 id (loopBodySource.tr …)`; `emitAction ∘ leftAction 1 id = leftAction 1 id ∘ emitAction` (closes by `simp` with `Option.map_id`); one `Cfg.ext` showing `emitCfg ∘ leftCfg = leftCfg ∘ emitCfg`; the liveness guard comes from `leftCfg_run`. About 15–25 lines replacing 56. Needs build confirmation |

## 4. Catalog copies (input for 12.2c — all KEEP here)

- **All 95 core privates (lines 181–2614) have Catalog copies. None of the 91 `emCall*` or 28 `emLoop*` privates do.**
- **94 are copied as `f2_<name>`.** They sit in Catalog.lean roughly between 5571 (`f2_loop_live_prefix`) and 7823 (`f2_loop_find_run`). Examples: `f2_LoopHostState` 6109, `f2_loopHost` 6152, `f2_loopHost_contracts` 7637.
  - 92 are byte-identical after removing the prefix.
  - 2 are strengthened with head-position bounds:
    - `f2_loopHost_prepare` 6835 (↔ `loopHost_prepare` 1446) adds `∀ i, -(T) ≤ c.workTapePos i ≤ T`, proved via `head_steps`.
    - `f2_loopHost_contracts` 7637 (↔ `loopHost_contracts` 2214) adds per-round and terminal head bounds, using `f2_loopCall_heads`.
    - So the Loop originals are weaker special cases of these.
- **1 is copied as `a2_loop_halted_run`** (Catalog 10667 ↔ `loop_halted_run` 2445, identical).
- **Catalog-only analogues with no Loop counterpart:**
  - `f2_loopCall_heads` 7588, `f2_exists_loopFind_space` 7935;
  - `a2_loop_prepare` 10426, `a2_loop_start_prefix` 10510 and `a2_loop_round` 10539 — space-ledger variants of `loopHost_prepare`, `loopHost_start` and `loopHost_round`, built over `f2_loopHost`.
- **The 8 dead declarations were copied too and are dead in Catalog as well.** `f2_loop_silent_prefix` and `f2_loopBody_capture` each occur once; `f2_loopBorrow_correct` occurs twice (the declaration at 5940 and a docstring at 7628). 12.2c can drop them on both sides.

## 5. Summary

| Classification | Count | Families | Estimated line impact in Loop.lean |
|---|---|---|---|
| DEAD-CANDIDATE | 8 | F4 (6), `loop_silent_prefix`, `loopBody_capture` | about −160 (192–200, 439–563, 692–717), plus fixing the docstring sentence at 2205 |
| REPLACE, actionable | 3 | H4 | about −30 to −40 net (56 lines out, 15–25 in); borderline because the facility is `emit_run` |
| REPLACE-R1 role → LEAVE | 41 | F7 12, F7b 4, G7 4, G9a 13, G9b 8 | 0 (about 660 lines; replacing them is a host rebuild) |
| REPLACE-R2 role → LEAVE | 17 | F5 5, F12 2, G9c 10 | 0 |
| REPLACE-CATALOG role → LEAVE | 29 | F10 9, G2 12, G8 8 | 0 |
| KEEP | 116 | F1 8, F2, F3, F6, F8, F9, F11, F13, F14, F15, G1, G3–G6, H1–H3, H5, H6 | 0 |
| **Total** | **214** | | **about −190 to −200 under the strict bar** |

Of the 116 KEEP, 95 are the core loop (all with Catalog copies, see section 4).

## Out of scope, but noticed

- **The largest duplication in the file is internal, not §12.** H3's 14 lemmas (about 512 lines, plus the 36-line near-copy `emLoopHost_anchor_return`) repeat `loopHost`'s phase lemmas, because `emLoopHost` agrees with `loopHost` on every non-body state. A machine-agreement transfer lemma would collapse them. That is a separate decision from this retrofit.
- **Stale status headers.** Embed.lean, Seam.lean and Catalog.lean still say "statement skeleton / all sorried", but `grep -c sorry` returns 0 for all three.
```

## ===== audits/retrofit-inventory/primitives.md =====

```
# Retrofit inventory — `Build/Primitives.lean` (commissioned report, verbatim)

*Maintainer provenance note: produced 2026-10-09 by a commissioned read-only
inventory agent at HEAD `af3952a3`; source-text liveness analysis (token
matching with comments stripped, transitive closure from the public
declarations) — no Lean build run. Feeds plan §4d. The report follows
verbatim.*

---

# Retrofit inventory: `Build/Primitives.lean` (all 318 private declarations)

**File:** `/Users/seyoonr/phd_experiments/tcslib/TCSlib/Complexity/TuringMachine/Build/Primitives.lean`. I read it at HEAD `af3952a3`. The file was last changed in `84b79daf`, and its working tree is clean.

**How the inventory was built.** I enumerated every declaration from the source text. There are 336 in total: 318 private and 18 public, with zero `sorry`s (the word "admitted" appears only in comments).
- References between declarations are token matches over the source with comments removed, so a name mentioned only in a docstring does not count as a use.
- Liveness is the transitive closure from the 18 public theorems.
- The 6 private `instance`s have no textual uses. They are still live, because `FinTM` has `[Fintype State]` and `[DecidableEq State]` fields (`TuringMachine/Finite.lean:128-136`).
- Token matching can only overstate liveness, never understate it, so the DEAD set below is sound.
- I did not run a Lean build; this is a source-text analysis.

---

## 0. Main findings (read these first)

1. **The "engine room" premise does not hold at the import level.**
   - `Build/Catalog.lean` does not import Primitives. It imports only `Mathlib.Data.Nat.Size`, `Mathlib.Tactic.DeriveFintype`, `Build.Loop` and `Encoding`.
   - Instead it holds its own copies of these privates, under an `f2_` prefix. `Catalog.lean:1305-1307` says these are "F2 local witness copies from Composition.lean and Build/Primitives.lean", unchanged except for the prefix.
   - **150 Primitives privates have an `f2_` twin in Catalog.** 147 are identical once the prefix, whitespace and comments are ignored. The other 3 (`splitSolve_of_body`, `splitSolve_source`, `splitSolve_closed`) differ only in that the Catalog versions add a space bound.
   - So `pairDupTM`, `pairValidTM`, `pairExtractTM`, `scanCfg` and the rest are the *originals* of code that is now duplicated. Catalog's public rows rest on `f2_pairDupTM` and friends, not on these.
2. **The named R1 target `emitterBank*` is dead code.** It is not referenced by any public theorem. Deleting it is strictly simpler than rewriting it against R1. 62 privates (about 1,227 lines) are dead in total: 59 leftover components from the earlier emitter batch, plus 3 orphan lemmas from the split-search section.
3. **Two clean catalog replacements exist, both at canonical `Cfg.ofWords` seams:**
   - `emitterCompare*` (8 privates) → `Turing.compareTM`
   - `emitterP2Erase*` (6 privates) → `Turing.clearTM`
4. **R1 cannot replace the live `emitterP2*` relocation layer from Embed's public API alone.**
   - Every frame lemma needs to know what the transported configuration holds on the *selected* tapes.
   - Embed exports no lemma about selected tapes: `embedSlot` and `embedSlot_selected` are private (`Embed.lean:124-151`), and the public `embedEmitTM_frame` covers only unselected tapes.
   - The host is also a single product controller, not a standalone `embedEmitTM ι M`.
   - Classification: LEAVE.
5. **R2 cannot replace either body controller.**
   - `seamCompTM` has exactly one exit state and one entry state; no branching combinator exists.
   - Both bodies branch at two points, and each round starts and ends at the same anchor.
   - Classification: LEAVE.
6. **Two exact duplicates of public `Encoding.lean` lemmas** are already within Primitives' imports:
   - `catalogPair_inverse` ≡ `Turing.eq_pairEncode_of_pairDecode` (`Encoding.lean:231`)
   - `catalogPair_length` ≡ `Turing.length_pairEncode` (`Encoding.lean:192`)
   - These are not §12 replacements, but swapping in the public lemma is strictly simpler.

---

## 1. Public surface and file structure

### 1a. The 18 public declarations

All live in `namespace Turing.FinTM` and all have the shape `∃ M c, M.ComputesFunInTime f T`. "Twin" means Catalog has a `_spaceUsed` row whose first part states the identical time contract.

| # | Declaration (line) | Role | Catalog twin |
|---|---|---|---|
| 1 | `computesFunInTime_prepend` (2122) | P3: computes `w ++ x` | yes |
| 2 | `computesFunInTime_lengthBits` (2137) | P4: `Nat.bits` of the input length, via `Complexity.timeConstructible_id` (no privates) | yes |
| 3 | `computesFunInTime_polyUnary` (2159) | P5 unary: `replicate (C(n+1)^e) true` | yes |
| 4 | `computesFunInTime_polyBits` (2183) | P5 binary: built from rows 3 and 2 (no privates) | yes |
| 5 | `computesFunInTime_pairEncodeFixed` (2220) | P6 encoder: a special case of row 1 | yes |
| 6 | `computesFunInTime_pairFst` (2235) | P6 extractor, first component | yes |
| 7 | `computesFunInTime_pairSnd` (2254) | P6 extractor, second component | yes |
| 8 | `computesFunInTime_pairValid` (2271) | P6 validity test | yes |
| 9 | `computesFunInTime_pairConcat` (2287) | P13 | yes |
| 10 | `computesFunInTime_pairDup` (2308) | P14 | yes |
| 11 | `computesFunInTime_pairMapSnd` (2747) | threaded map | yes, but needs extra space hypotheses `hgs`/`hSg` |
| 12 | `computesFunInTime_pairLenCheck` (2783) | P8, threaded form | yes |
| 13 | `computesFunInTime_stripLast` (2844) | marker strip, threaded form | yes |
| 14 | `computesFunInTime_splitSolve` (4393) | P15 split search | yes |
| 15 | `computesFunInTime_incFixed` (4414) | P9 fixed-width increment | yes |
| 16 | `computesFunInTime_splitSolveWith` (7399) | E4′ width-parametric split search | none (space rows deferred, decision 12.3) |
| 17 | `computesFunInTime_unaryToken` (7553) | stream row | none |
| 18 | `computesFunInTime_appendBit` (7622) | stream row | none |

### 1b. Section map

- **L1–121:** imports, module docstring (L67–110 carry a stale "admitted" status), and the batch-P4 closure note. `namespace` opens at L123.
- **L125–982:** P3 prefix, zero-tape scan kit, P14 duplicate, P9 increment, P6 validity, and the shared P6/P13 extractor.
- **L980–1408:** P5 unary polynomial generator.
- **L1409–1757:** P8 length checker (`pairCountTM`) and the input-rewind helper.
- **L1758–2110:** marker-strip machinery, pair-grammar lemmas, payload composition.
- **L2112–2312:** public rows 1–10.
- **L2313–2913:** threaded map (`pairMapTM`), then public rows 11–13.
- **L2914–4418:** split-search body and closure, then public rows 14–15.
- **L4419–5955:** emitter batch P. This holds the E4′ loop bridge and the earlier batch's components, which are now mostly dead.
- **L5956–7409:** emitter P2: relocation layer, phase machines, tape layout, body controller, closure, then public row 16.
- **L7410–7635:** stream machines and public rows 17–18. `end` at L7636.

---

## 2. Private declarations by family

Notation:
- Line ranges include docstrings; "interleaved" means the family is split across the given ranges.
- "Reached by" names the public rows whose proofs depend on the family (abbreviations: pre = prepend, pEF = pairEncodeFixed, sS = splitSolve, sSW = splitSolveWith, and so on).
- **DUP-f2** means a byte-identical `f2_` copy exists in `Catalog.lean`.

### A. Original machines for the catalog rows (the brief's "engine room")

| Family | # | Lines (~) | Role | Reached by | Class |
|---|---|---|---|---|---|
| F01 prefix | 5 | 129–211 (~83) | Emit a fixed word, then copy the input (no work tapes) | pre, pEF, sS (constant source) | KEEP, DUP-f2 |
| F02 scan kit | 7 | 212–268, 371–440, 553–567 | Input-scan configurations and copy/scan invariants (no work tapes) | 11 rows, including the stream rows | KEEP, DUP-f2 |
| F03 pairDup | 3 | 270–370 (~101) | P14 machine | dup | KEEP, DUP-f2 |
| F04 incFixed | 3 | 442–552 (~111) | P9 string-function machine | inc | KEEP, DUP-f2. **Borderline:** Catalog's `incrementTM` increments a tape word in place; it is not an input→output machine, so it cannot replace this |
| F05 pairValid | 4 | 569–663 (~95) | Validity scanner | val | KEEP, DUP-f2 |
| F06 pairExtract | 12 | 664–982 (~319) | Shared buffered parser | fst, snd, cat, map, lenC, strip | KEEP, DUP-f2 (also needed by the non-projectable `pairMapSnd`) |
| F07 polyUnary | 20 | 983–1408 (~426) | P5 nested-loop generator | pU, pB, lenC, sS (`catalogPolyTape` also sSW) | KEEP, DUP-f2 |
| F08 pairLenCheck | 11 | 1409–1757, excluding 1649–1677 (~320) | Capture, rewind, parse, count down | lenC | KEEP, DUP-f2. Already uses the public W1 `captureAction`/`capture_run`; the later phases read input and emit, so R1's `embedSilentRetTM` would not be simpler |
| F09 input rewind | 1 | 1649–1677 | Rewind the input head (built on public `rewind_scan`) | map, lenC, sS, sSW | KEEP, DUP-f2. No catalog routine moves the input head |
| F10 stripLast | 14 | 1758–2061, interleaved (~280) | Copy, trim and replay, plus a true-bit scanner | strip (`catalogBuffer_erase` also sSW) | KEEP, DUP-f2 |
| F11 pair grammar | 4 | 2013–2110, 2658–2664 (~80) | List lemmas and payload composition | map, strip | 2 swap to public Encoding lemmas (finding 6); 2 KEEP (no twin) |
| F12 pairMap | 14 | 2313–2731 (~413) | Threaded-map controller | map | KEEP. No twin (Catalog uses a different `a2_` implementation); not projectable (§3) |
| F13 split orbit | 9 | 2914–3005 (~92) | Candidate step, orbit, `find?` bridge, bounds | sS; 4 members also sSW | KEEP, DUP-f2 (1 member dead) |
| F14 split position/scratch | 5 | 3006–3050 | Saturated input position; partially cleared scratch tape | sS, sSW | KEEP, DUP-f2 |
| F15 split restore | 9 | 3051–3222, 3355–3403 (~222) | Append to candidate, clear all scratch tapes in parallel, rewind; first-entry cut | sS, sSW (P2 advance phase) | KEEP, DUP-f2. **Borderline:** the parallel k-tape clear is fused with the append and the rewind; `clearTM` is single-tape and §12 has no k-fold seam composition |
| F16 split counted simulation | 7 | 3224–3324, 3404–3438 (~137) | Run the source on tapes 1..k; each emitted bit advances the input head instead of printing | sS | **LEAVE (R1-shaped)**: R1 offers only "capture to a tape" or "forward to output", not this emission mode. DUP-f2; 1 member dead |
| F17 `splitPoly_loop_end` | 1 | 3326–3354 | Generator loop endpoint | sS | KEEP, DUP-f2 |
| F18 split prepare | 8 | 3439–3584 (~146) | Write unary length copies to all scratch tapes in parallel | sS | KEEP, DUP-f2 (1 member dead) |
| F19 split glue | 6 | 3585–3652, 3754–3767, 4048–4075 (~106) | Anchor-exclusion traces; state-embedding lockstep and cut | sS; the four `splitSafe*` also sSW | **LEAVE (R2-shaped)**, DUP-f2 |
| F20 split body | 12 | 3654–4206, interleaved (~356) | Multi-phase round controller | sS | KEEP, DUP-f2 (this is where R2 would have to apply; see §4) |
| F21 split emit | 6 | 3667–3686, 3911–4046 (~154) | Emit the native split (doubling and copying, input → output) | sS, sSW | KEEP, DUP-f2 |
| F22 split closure | 6 | 4201–4366 (~166) | Close via the public `exists_loopFindTM` | sS | KEEP; Catalog twins differ only by the added space bound |

Members:
- **F01:** `catalogPrefixTM`, `catalogPrefixCfg`, `catalogPrefixTM_emit`, `catalogPrefixTM_copy`, `catalogPrefixTM_computes`.
- **F02:** `scanCfg`, `scanCfg_read`, `scanCopy_run`, `scanCopy_finish`, `scanCopy_suffix`, `scanTrues_run`, `scanStep_right`.
- **F03:** `pairDupTM`, `pairDup_double`, `pairDup_computes`.
- **F04:** `incFixed_cases`, `incFixedTM`, `incFixed_computes`.
- **F05:** `pairValidTM`, `pairValid_block`, `pairValid_run`, `pairValid_computes`.
- **F06:** `pairExtractTM`, `extractCfg`, `extractCfg_read`, `extract_first`, `extract_block`, `extract_rewind`, `extract_replay`, `extract_replay_finish`, `extract_suffix`, `extract_finish`, `extract_run`, `pairExtract_computes`.
- **F07 (20):** `CatalogPolyControl`, `catalogPolyControlFintype`, `catalogPolyControlDecidableEq`, `catalogPolyTape`, `catalogPolyMove`, `catalogPolyUnaryTM`, `catalogPolyCfg`, `catalogPolyMove_apply`, `catalogPoly_emit`, `catalogPoly_rewind`, `catalogPoly_advance`, `catalogPolyCost`, `catalogPoly_loop`, `catalogPolyTape_write`, `catalogPolyCost_le`, `catalogPolyCopyCfg`, `catalogPoly_copy`, `catalogPoly_setup`, `catalogPoly_start`, `catalogPoly_unary_computes`.
- **F08:** `lenAction`, `pairCountTM`, `lenCfg`, `lenCfg_read`, `lenAction_apply`, `lenSuffix_run`, `lenParse_first`, `lenParse_block`, `lenParse_run`, `lenStart`, `pairCount_computes`.
- **F09:** `catalogRewind`.
- **F10:** `rawStripTM`, `stripCfg`, `catalogBuffer_erase`, `rawStrip_copy`, `rawStrip_rewind`, `rawStrip_replay`, `rawStrip_finish`, `rawStrip_erase`, `rawStrip_trim`, `rawStrip_computes`, `anyTrueTM`, `anyTrue_run`, `anyTrue_computes`, `catalogMarker_cases`.
- **F11:** `catalogPair_inverse` and `catalogPair_length` (swap to public lemmas); `catalogPayload_length` and `catalogPayload_computes` (KEEP; the latter uses the public `bufferedCompTM`, `bufferedComp_start`, `bufferedSecondCfg_run`).
- **F12:** `mapAction`, `pairMapTM`, `mapCfg`, `mapAction_apply`, `mapBuffer_rewind`, `mapStart`, `mapCfg_read`, `mapParse_first`, `mapParse_block`, `mapValidate`, `mapPrefix_replay`, `mapPayload_replay`, `mapPayload_finish`, `pairMap_computes`.
- **F13:** `splitStep`, `splitAccept`, `splitStep_inv`, `splitStep_orbit`, `catalogFind_congr`, `splitFind_eq`, `splitFind_none` (DEAD), `splitLoop_result`, `splitLoop_bound`.
- **F14:** `splitPos`, `splitPos_read`, `splitPos_succ`, `splitScratch`, `splitScratch_erase`.
- **F15:** `splitRestoreTM`, `splitRestoreScan`, `splitRestore_scan`, `splitRestoreClean`, `splitRestore_append`, `splitRestore_rewind`, `splitRestore_run`, `catalogFirstEntry`, `splitRestore_first`.
- **F16:** `splitCountAction`, `splitCountCfg`, `splitCount_over`, `splitCount_apply`, `splitCount_run`, `splitCount_accept`, `splitCount_firstHalt` (DEAD).
- **F17:** `splitPoly_loop_end`.
- **F18:** `splitPrepareTM`, `splitPrepareScan`, `splitPrepare_scan`, `splitPrepareReady`, `splitPrepare_extra`, `splitPrepare_rewind`, `splitPrepare_run`, `splitPrepare_first` (DEAD).
- **F19:** `splitSafe`, `splitSafe_add`, `splitEmbed_cut`, `splitEmbed_run`, `splitSafe_one`, `splitSafe_join`.
- **F20:** `splitRewindTM`, `SplitBodyState`, `splitBodyStateFintype`, `splitBodyStateDecidableEq`, `splitBodyTM`, `splitBank`, `splitBody_start`, `splitBody_prepare`, `splitBody_count`, `splitBody_rewind`, `splitBody_restore`, `splitBody_round`.
- **F21:** `splitEmitTM`, `splitEmitCfg`, `splitEmit_double`, `splitEmit_separator`, `splitEmit_suffix`, `splitEmit_run`.
- **F22:** `splitSolve_of_body`, `splitSource_poly`, `splitSource_constant`, `splitBody_envelope`, `splitSolve_source`, `splitSolve_closed`.

### B. Emitter batch P (L4419–5955)

| Family | # | Lines (~) | Role | Class |
|---|---|---|---|---|
| F23 emitterSplit | 5 | 4441–4549 (~109) | Loop bridge for the width-parametric search, via public `exists_loopFindTM` and `computesFunInTime_lengthBits` | KEEP (sSW) |
| F24a eval | 6 | 4550–4679 (~130) | Captured evaluator built on `bufferedCompTM` | **DEAD** |
| F24b clear | 13 | 4822–5054, 5448–5481 (~266) | Interval cleaner for visited cells | **DEAD** |
| F24c track | 18 | 5054–5390 (~337) | Visited-interval tracker | **DEAD** |
| F24d bank | 11 | 5493–5690 (~198) | Whole-bank simultaneous cleaner | **DEAD** (this is the backlog's named R1 target) |
| F24e right | 9 | 5691–5863 (~173) | Halt-to-live return adapter | **DEAD** |
| F24f eval closers | 2 | 5864–5960 (~74) | Ends of the old evaluation chain | **DEAD** |
| F25a compare | 8 | 4680–4821, 5415–5447 (~175) | Two-tape whole-word comparison, heads restored, verdict kept in control state | **REPLACE-CATALOG** (`Turing.compareTM`) |
| F25b first entry | 1 | 5391–5414 | Cut a run at its least visit to a stopping state | KEEP. In-file generalization of `catalogFirstEntry`; no public §12 equivalent |
| F25c width arithmetic | 3 | 5482–5491, 5906–5928 | `Nat.bits` injectivity, the width equation, the evaluation budget | KEEP (the public `LogProg.bits_injective` lives in SpaceComplexity, outside Primitives' imports) |

Members:
- **F23:** `emitterSplitAccept`, `emitterSplit_find`, `emitterSplit_result`, `emitterSplit_loop_bound`, `emitterSplit_of_body`.
- **F24a:** `emitterIdleTM`, `emitterEvalTM`, `emitterEvalCfg`, `emitter_eval_run`, `emitter_eval_initial`, `emitter_eval_first`.
- **F24b:** `emitterInterval`, `emitterCleared`, `emitter_cleared_step`, `emitterClearTM`, `emitterClearCfg`, `emitter_clear_left`, `emitter_cleared_zero`, `emitter_cleared_all`, `emitter_clear_scan`, `emitter_origin_erase`, `emitter_clear_origin`, `emitter_clear_run`, `emitter_clear_first`.
- **F24c (18):** `emitterSpan`, `emitter_span_extend`, `emitterSlots`, `emitterTrackTM`, `emitterTrackCfg`, `emitterTrackMid`, `emitter_track_action`, `emitter_track_stamp`, `emitterLo`, `emitterHi`, `emitter_track_extent`, `emitter_track_support`, `emitter_span_zero`, `emitter_track_initial`, `emitter_track_run`, `emitter_track_computes`, `emitter_span_interval`, `emitter_track_clearable`.
- **F24d:** `emitterBankSymbols`, `emitterBankPart`, `emitterBankTM`, `emitterBankCfg`, `emitterBank_part`, `emitterBank_step`, `emitterBank_run`, `emitterClear_fixed`, `emitterBank_clear`, `emitterBank_fixed`, `emitterBank_first`.
- **F24e:** `emitterRightTM`, `emitterRightCfg`, `emitter_right_step`, `emitter_right_run`, `emitterRightScan`, `emitter_right_scan`, `emitter_right_finish`, `emitter_right_endpoint`, `emitter_right_computes`.
- **F24f:** `emitter_prepared_eval_first`, `emitter_width_eval_first`.
- **F25a:** `emitter_take_succ_eq`, `emitterCompareTM`, `emitterCompareCfg`, `emitter_compare_nonblank`, `emitter_compare_scan`, `emitter_compare_rewind`, `emitter_compare_run`, `emitter_compare_first`.
- **F25b:** `emitter_first_entry`.
- **F25c:** `emitter_bits_injective`, `emitter_binary_check`, `emitter_width_budget`.

### C. Emitter P2 (L5956–7409) and the stream machines

| Family | # | Lines (~) | Role | Class |
|---|---|---|---|---|
| F26a P2 relocation | 4 | 5961–6037 (~77) | Move an action or configuration onto selected host tapes, map its states, step-by-step lockstep | **LEAVE (R1-shaped)** |
| F26b P2 layout | 24 | 6513–6734 (~222) | Tape layout (candidate, width bank, length bank), tape selections and their inverses, frame identities | **LEAVE (R1-shaped)** |
| F27a P2 erase | 6 | 6038–6150 (~113) | Clear one word on one tape at a canonical seam | **REPLACE-CATALOG** (`Turing.clearTM`) |
| F27b P2 prepare | 8 | 6151–6433 (~276) | Copy the candidate, copy the input suffix, set the past-end flag, rewind | KEEP. The candidate copy (copyTM-like) is interleaved with input motion and the flag, so it cannot be split at canonical seams |
| F28 P2 glue | 6 | 6328–7210, interleaved (~121) | Concatenating phases, dispatch steps, execute-first calls | **LEAVE (R2-shaped)** |
| F29 P2 body | 20 | 6735–7378 (~609) | 11-phase controller, the round theorem, closure (uses the public `exists_installCallTM`) | KEEP (R2 note in §4) |
| F30 stream | 7 | 7410–7612 (~169) | Unary-token and append-bit machines (no work tapes) | KEEP (no catalog row; P16–P18 space rows deferred) |

Members:
- **F26a:** `emitterP2Action`, `emitterP2Cfg`, `emitterP2_apply`, `emitterP2_relocate_run`.
- **F26b (24):** `emitterP2Words`, `emitterP2LeftIndex`, `emitterP2LeftSelect`, `emitterP2RightIndex`, `emitterP2RightSelect`, `emitterP2_left_inverse`, `emitterP2_right_inverse`, `emitterP2_left_frame`, `emitterP2_right_frame`, `emitterP2_words_clean`, `emitterP2OneSelect`, `emitterP2_one_inverse`, `emitterP2_one_frame`, `emitterP2SmallIndex`, `emitterP2SmallSelect`, `emitterP2_small_inverse`, `emitterP2_small_frame`, `emitterP2PairIndex`, `emitterP2PairSelect`, `emitterP2_pair_inverse`, `emitterP2_pair_frame`, `emitterP2_update_left`, `emitterP2_update_right`, `emitterP2_update_candidate`.
- **F27a:** `emitterP2EraseTM`, `emitterP2EraseCfg`, `emitterP2_erase_scan`, `emitterP2_erase_back`, `emitterP2_erase_run`, `emitterP2_erase_first`.
- **F27b:** `emitterP2PrepareTM`, `emitterP2PrepareCfg`, `emitterP2_prepare_candidate`, `emitterP2_prepare_suffix`, `emitterP2_prepare_rewind_candidate`, `emitterP2_prepare_rewind_suffix`, `emitterP2_prepare_run`, `emitterP2_prepare_first`.
- **F28:** `emitterP2_join`, `emitterP2_segment`, `emitterP2_call_segment`, `emitterP2_control`, `emitterP2_after`, `emitterP2_strict_join`.
- **F29 (20):** `EmitterP2State`, `emitterP2StateFintype`, `emitterP2StateDecidableEq`, `emitterP2BodyTM`, `emitterP2_body_start`, `emitterP2_body_prepare`, `emitterP2_body_width`, `emitterP2_body_length`, `emitterP2_body_compare`, `emitterP2_body_erase_left`, `emitterP2_body_erase_right`, `emitterP2_advance_initial`, `emitterP2_stateWord_one`, `emitterP2_body_advance`, `emitterP2_emit_initial`, `emitterP2_body_emit`, `emitterP2_body_test`, `emitterP2_body_finish`, `emitterP2_body_round`, `emitterP2_closed`.
- **F30:** `emitterTokenTM`, `emitterToken_double`, `emitterToken_separator`, `emitterToken_run`, `emitterToken_length`, `emitterAppendTM`, `emitterAppend_run`.

The prefix count matches the brief's "~77": 10 names start with `emitterBank` and 67 with `emitterP2`, plus `EmitterP2State`. By role, though, only the 28 in F26 are relocation code; the rest are phase machines, glue and the body controller.

### Evidence for the DEAD set (62)

These declarations have no references from any other declaration in the file:
- `emitter_eval_initial`, `emitter_clear_first`, `emitterBank_first`, `emitter_width_eval_first`
- `splitFind_none`, `splitCount_firstHalt`, `splitPrepare_first`

Every other DEAD member is referenced only from inside the dead set. For example:
- `emitterClearTM` is used only by `emitterClearCfg`, the `emitter_clear_*` lemmas, the `emitterBank*` members and `emitterClear_fixed`.
- `emitterTrackTM` is used only by the `emitter_track_*` lemmas and the two eval closers.
- `emitter_eval_first` is used only by `emitter_prepared_eval_first`.

These are private, so no other file can use them. Mentions elsewhere are docstring-only (`Embed.lean:31,65,187,619`; `CookLevin/Hardness.lean:1262`). This matches `audits/emitter-fill-findings.md:193`: "The predecessor's unused bank helpers remain proved components". The 3 split orphans likely have dead `f2_` twins in Catalog too; I did not check that file's liveness.

---

## 3. What "engine room" means here

The originals the brief names (F01–F10, F13–F22) are KEEP under the brief's rule. But none of them carries weight for the catalog: they are live only because Primitives' own public rows use them. That opens two ways to remove the duplication:

**(a) Project the rows from Catalog now.**
- The first part of each `_spaceUsed` row is statement-identical to Primitives' row for: prepend, polyUnary, pairFst, pairSnd, pairValid, pairConcat, pairDup, pairLenCheck, stripLast, splitSolve and incFixed.
- Each of those 11 proofs becomes a 2–3-line projection from its twin.
- This frees **100 privates (~2,402 lines)**. 47 twins stay live, because `pairMapSnd`, `splitSolveWith` and the stream rows still need them: the scan core, F06, `catalogPolyTape`, `catalogRewind`, `catalogBuffer_erase`, `catalogPair_inverse`, and the split orbit/position/restore/emit/safe pieces.
- It needs `import TCSlib.Complexity.TuringMachine.Build.Catalog` in Primitives. That creates no import cycle, and none of Catalog's public names (`transferTM`, `copyTM`, `clearTM`, `compareTM`, `incrementTM`, `SweepPhase`, `FlagPhase`, `capture_visitedByTapeHead`) is defined anywhere else.
- `pairMapSnd` cannot be projected: Catalog's row needs a space bound for an arbitrary machine, and the only time-to-space lemma (`f2_space_of_time`) is private to Catalog.

**(b) Or wait for the planned per-theme split** and remove the duplication then.

There is also an option independent of Catalog. `computesFunInTime_splitSolve` follows from `computesFunInTime_splitSolveWith` plus `computesFunInTime_polyBits`, because `solveSplitWith (fun i => C*(i+1)^e)` unfolds to `solveSplit C e` by definition (`Convention.lean:125-133`). The only work is the bound `c(n+1)(b(n+2)^(e+1)+n+2) ≤ K(n+1)^(e+2)`. This frees 38 privates (~909 lines): all of F16–F18, F20, F22 and parts of F13. Those 38 are a subset of the 100 in option (a).

---

## 4. The REPLACE-* candidates and their seams

**REPLACE-CATALOG F25a → `Turing.compareTM 2 0 1`. Seam is canonical.**
- Start and end match exactly: `emitterCompareCfg w u v 1 0 true 0` is the configuration `Cfg.ofWords .run ![u,v]` (input head at 1, work heads at 0, empty output), and the endpoint is `Cfg.ofWords (.done (decide (u = v))) ![u,v]`. The only call site uses input position 1 (`emitterP2_body_compare`).
- Cost fits: `compareTM_run` gives `T ≤ 2·min+2 ≤ 2(max+1)`, and its first-return cut `∀ t<T, ∀ v, state ≠ done v` has exactly the shape needed.
- The positivity fact `0 < t` that `_first` provides is thrown away by its caller.
- Glue:
  - change `EmitterP2State.compare` to carry a `FlagPhase` state;
  - update the `emitterP2BodyTM` compare case;
  - restate `emitterP2_pair_frame` with a `Cfg.ofWords` source;
  - update the state literals in body_compare, body_test and body_round.

**REPLACE-CATALOG F27a → `Turing.clearTM 1 0`. Seam is canonical.**
- `emitterP2EraseCfg w u 0 0` already *is* `Cfg.ofWords 0 (fun _ => u)` by definition; `emitterP2_body_erase_left` uses `change` to that form.
- `clearTM_run` gives `T ≤ 2|u|+2`, the cut, and the endpoint `Cfg.ofWords .done (update w 0 [])`. One lemma is needed: on `Fin 1`, updating every entry to `[]` gives the all-`[]` function.
- Glue: `eraseLeft`/`eraseRight` carry a `SweepPhase` state; the two body cases change; two `hframe` lemmas are restated.
- `catalogBuffer_erase` stays live through F10.
- This also removes the stale `emitterP2EraseCfg` docstring already flagged in the backlog.

**R1 candidates.**
- **F26a/F26b (28): LEAVE.** These are what Embed's own docstring calls the generic form of `embedEmitCfg`. But:
  - (i) there is no public lemma for selected tapes, so none of the frame identities used by the 7 body phase lemmas can be re-proved;
  - (ii) the host is a product controller, so a state-embedding lockstep lemma (the job of `emitterP2_relocate_run`/`splitEmbed_run`) is still needed on top of `embedEmitTM_runFrom`;
  - (iii) switching to `Fin m ↪ Fin (k+l+1)` trades the left-inverse proofs for injectivity proofs one for one, so nothing is saved.
  - Point (i) would go away with an additive public lemma in `Embed.lean` (selected-tape projections of `embedEmitCfg`, or an `ofWords` transport lemma). That changes Embed's public surface, not Primitives', so it is your call.
- **F16 (6 live): LEAVE.** Its emission mode is not one R1 offers.
- **F24d: delete, do not port** (dead).

**R2 candidates.**
- **F19 + F28 (12) and the two body controllers F20/F29: LEAVE.**
- `splitBodyTM` branches after its rewind phase (to emit or to restore). Its count and rewind seams are not canonical (the input head is at `splitPos`, and the rewind starts from an arbitrary configuration). Each round starts and ends at the same anchor. Rebuilding it would need `seamCompTM_run_ofCfg` plus `seamReleaseTM` plus a branching combinator that does not exist.
- `emitterP2BodyTM` has canonical seams throughout (`Cfg.ofWords … (emitterP2Words …)`). But it branches twice (at the end of prepare on the `over` flag, and at the end of eraseRight on `ok`), carries the verdict in its state through both erase phases, and runs its execute-first calls inside the product controller. `emitterP2_call_segment` is in fact the case Seam.lean cites as the motivation for `seamReleaseTM`, but that adapter wraps a whole standalone machine, so it is not a drop-in replacement.

**Other borderline cases (all KEEP).**
- `catalogBuffer_erase` duplicates the public `bufferTape_erase_last` (`SpaceComplexity/Machines/FragDec.lean:96`), which is outside Primitives' imports; importing it would invert the layering.
- `emitter_first_entry` is an in-file generalization of `catalogFirstEntry`. Once F25a and F27a are replaced, each has one remaining caller, so they could be merged.
- The comment blocks at L67–110, L4419–4439 and L5956–5959 describe now-dead families and an "admitted" status that no longer holds; they need comment-only edits.

---

## 5. Summary

| Class | Privates | ~Lines (docstring-inclusive) | Notes |
|---|---|---|---|
| DEAD-CANDIDATE | 62 | 1,227 | 59 from the earlier emitter batch (F24a–f), 3 split orphans |
| REPLACE-CATALOG | 14 | 288 removed, about +15–30 glue | `compareTM`, `clearTM`; canonical seams; needs the Catalog import |
| REPLACE (public Encoding lemma, not §12) | 2 | 30 | `eq_pairEncode_of_pairDecode`, `length_pairEncode` |
| REPLACE-R1 | 0 | — | 34 R1-shaped privates are LEAVE (F26: 28; F16: 6) |
| REPLACE-R2 | 0 | — | 12 R2-shaped privates are LEAVE (F19, F28) |
| LEAVE (R-shaped, simplification bar fails) | 46 | 642 (415 R1-shaped + 227 R2-shaped) | — |
| KEEP | 194 | 4,775 | 134 of these have `f2_` twins (DUP-f2); 60 do not |
| **Total** | **318** | **≈6,962 private** | Public declarations ≈547 lines; header ≈122 |

**Estimated impact:**
- **Conservative pass** (DEAD + REPLACE-CATALOG + the two Encoding swaps): −78 privates, about −1,520 lines net. The file goes from 7,636 to about 6,100 lines.
- **Adding option (a)** (project 11 rows from Catalog): a further −100 privates and about −2,370 lines net. That leaves 140 privates in a file of about 3,700 lines.
- **Or, instead of (a)**, the splitSolve-via-splitSolveWith route: −38 privates (~909 lines), with no new import.

All counts and lines are computed from the source text. Line spans include each declaration's docstring; module-note blocks between declarations are attributed to the declaration before them.
```

## ===== audits/retrofit-inventory/hardness.md =====

```
# Retrofit inventory — `CookLevin/Hardness.lean` (commissioned report, verbatim)

*Maintainer provenance note: produced 2026-10-09 by a commissioned read-only
inventory agent at HEAD `36bb6255`; source-text liveness analysis (comment
stripping, reference graph by token matching, reachability from the public
theorems) — the kernel walker was not run. Feeds plan §4d. The report follows
verbatim.*

---

# Hardness.lean private-declaration inventory and retrofit plan

**File:** `/Users/seyoonr/phd_experiments/tcslib/TCSlib/Complexity/CookLevin/Hardness.lean` (8,904 lines, branch `complexity/arora-barak-ch3-4`, HEAD `36bb6255`). Nothing was modified.

**Method.** I stripped all comments from the source, detected every top-level declaration, and built a reference graph by token-matching against the file's own declaration names. Liveness is reachability from the 5 public theorems. Every private is assigned to exactly one family (the script reported 0 unassigned). I could not build or run the kernel walker, so "dead" here means dead in the source text.

## Headline findings

1. **The file has 553 privates, not ~538.** That is 618 at A5 close minus 65 deleted at E5. By kind: 361 lemma, 186 def, 4 abbrev, 1 structure (`CLFieldCode`), 1 inductive (`CLTemplateKind`).
2. **Under the strict-simplification bar, very little can be replaced today.** Only 5 privates pass now: `clFresh*` via R2, plus `clCompute_comp` via the public composition row. 63 more are R1/R2/catalog-shaped but blocked.
3. **The main blocker is a gap in R1's public API.** `Build/Embed.lean` exports no lemma giving the contents or head of a *selected* tape in `embedEmitCfg` / `embedSilentCfg`. The facts that would provide this, `embedSlot_selected` and `embedSlot_unselected`, are private (Embed.lean:128, :142). The public `embedEmitTM_frame` covers only unselected tapes, and `embedEmitTM_visitedByTapeHead` gives only visited sets.
   - Every frame-identification lemma in Hardness needs those fields. `clSlotCfg` alone occurs 93 times.
   - So no R1 consumer in this file can be proved from the public API.
   - The fix belongs in Embed.lean, not here: add public `embedEmitCfg` (and silent-flavor) field lemmas for selected tapes.
   - No file in TCSlib uses `embed*`, `seam*`, `transferTM`, `copyTM`, `clearTM`, `compareTM` or `incrementTM` yet. Hardness would be the first consumer.
4. **Two library docstrings overclaim what they generalize.**
   - Embed.lean says R1 is the "generic form" of `clBank*`. It is not: `clBankTM` is a *simultaneous product* of l counters (`State := Fin l → Option (Fin 4)`, cost 2W+2 regardless of l). R1 relocates one routine.
   - Catalog.lean says its copy and compare rows promote the `clCopy*` / `clCmp*` shapes. They match in cost only:
     - `clCopyTM` appends `pairEncode w []` (doubled bits plus `01`) at the record head, not at the origin.
     - `clCmpTM` tests a four-word binary cross-sum `a+b = c+d`, not two-word equality.

## 1. Public surface and file structure

**Public declarations (5):**

| Decl | Lines | Role |
|---|---|---|
| `NPHard.polyTimeReducible` | 76–85 | Hardness transfers forward along `≤ₚ` (this is the fifth theorem) |
| `SAT_NPHard` | 8752–8880 | [AB09, Lemma 2.11]; proof is `clA5Reduction hL` |
| `SAT_NPComplete` | 8882–8887 | `⟨SAT_mem_NP, SAT_NPHard⟩` |
| `SAT3_NPHard` | 8889–8896 | `SAT_NPHard.polyTimeReducible SAT_reducible_SAT3` |
| `SAT3_NPComplete` | 8898–8902 | `⟨SAT3_mem_NP, SAT3_NPHard⟩` |

**Phases.** Batch boundaries are confirmed from `audits/ch2-epoch4-agent-reports/batchA*.md` (counts at batch close: 77, 52, 150, 176, 163).

| Phase | Lines | Privates now | Contents |
|---|---|---|---|
| Header, module doc, first public | 1–86 | 0 | |
| A: snapshot encoding and pure layer | 87–605 | 48 | emission algebra 94–180; packing, verifier, budget 182–236; Claim-2.13 templates, product snapshot code, six-family tableau 238–533; cursor orbit and `clEmitter_of_body` 522–605 |
| A2: native preparation, reference simulation of the oblivious verifier | 606–1259 | 38 | NP verifier 609–620; function adapters 622–689; fill 691–751; header 753–790; reference simulator 792–893; dead clock runner 895–918; binary counter 920–1258 |
| A3: trajectory (tracker, recorder, comparator, reader) | 1260–3333 | 133 | bank 1260–1434; tracking 1436–1707; copier 1709–1917; slot relocation 1919–1999; row copier 2001–2216; pure counts 2218–2298; recorder 2299–2772; comparator 2774–3084; fields and reader 3105–3332 |
| A4: packed-records producer | 3334–6262 | 171 | utilities 3334–3378; wipe 3380–3509; fresh 3511–3584; row loader 3586–3815; input copier 3817–3939; prepare 3941–4053; header layout 4055–4159; record host 4161–4289; matcher 4291–4693; last-visit 4695–4783; replay 4785–4883; composition, output, prepared 4884–5063; query 5065–5163; outputs and budgets 5164–5547; search and visit rows 5549–5795; repeat host and size envelopes 5796–6160; packed producer 6162–6261 |
| A5: controller | 6263–6773 | — | halt, pad and stop adapters; cyclic 5-module host; clean contracts and startup |
| A5: output identity | 6775–8339 | (139 for 6263–8339) | word toolkit; stored data, cursor, fuel, round; `clA5Output_of_nativeChunk` 7356; bounded decode; fragment and emit selector; `clA5OutputIdentity` 8333 |
| A5: equisatisfiability | 8340–8750 | 24 | ends with `clA5Reduction` 8740–8750 |
| Public theorems | 8752–8904 | 0 | |

## 2. All 553 privates by role family

Line totals include each declaration's docstring.

**KEEP (Cook–Levin-specific): 260 decls, 3,292 lines**

| Fam | # | Lines | Members / role |
|---|---|---|---|
| A | 10 | 94–180 | `clLastRound`, `clGroups`, `clGroups_length`, `clFragment`, `clFragment_append`, `clChunk`, `clChunks_before`, `clChunks_serialize`, `clGroups_index`, `clGroups_serialize`. Ordered emission algebra. |
| B | 3 | 191, 216, 612 | `clObliviousVerifier`, `clLoop_polyBound`, `clNPVerifier`. Verifier normalization and budget. |
| C | 35 | 184–533 | e.g. `clPack`, `clTemplate*`, `CLFieldCode`, `clFieldCode`, `clSymbol*`, `clBlockEncode`, `clStateSlice`/`clInputSlice`/`clWorkSlice`, `clBlock_*`, `clBlockDecode*`, `CLTemplateKind`, `clPredicate`, `clWire`, `clGroup`, `clInputGroup`, `clWorkGroup`, `clTableauGroups`, `clTableau`, `clTableau_chunks`, `clPrev_spec`, `clCursor_orbit`. Snapshot code, templates, tableau. |
| D | 1 | 543–605 | `clEmitter_of_body`. Already cites public `exists_emitLoopTM`. |
| E | 5 | 625–689 | `clNative_linear`, `clNative_map`, `clNative_pair`, `clNative_append`, `clNative_unary`. Already thin wrappers over catalog rows. |
| G | 2 | 758–790 | `clPrepHeader`, `clPrepHeader_native` |
| H | 3 | 796–893 | `clRefCfg`, `clRefAction`, `clRef_apply`. Virtual-input reference simulation (stage s2). |
| K1 | 9 | 1439–1508 | `clMoves`, `clPositions`, `clMoves_correct`, `clSelect`, `clAdvance`, `clSigned`, `clSigned_advance`, `clAdvance_bound`, `clSigned_eq`. Pure movement arithmetic. |
| P | 13 | 2221–2298, 3088, 3319 | `clElapsed_width`, `clTag`, `clTag_valid`, `clMove_inj`, `clMoves_tag`, `clCounts`, `clCounts_succ`, `clCounts_bound`, `clCounts_positions`, `clRecFields`, `clRecords`, `clCounts_schedule`, `clRecords_length` |
| S1 | 4 | 3105–3129 | `clFields`, `clPair_append`, `clFields_append`, `clRowPrefix_fields`. Field-format specification. |
| AA | 11 | 4057–4159 | `clNative_fields`, `clHeaderTail`, `clHeaderField`, their `_native` lemmas, `clRecWords`, `clHeaderKeep`, `clHeaderLayout`, `clHeaderLayout_native`, `clHeaderLayout_exact`, `clRecordArgument_native` |
| AC2 | 7 | 4294–4693 | `clMatchWords`, `clRows`, `clRows_add`, `clRows_split`, `clRows_records`, `clMatchFlag`, `clMatchFlag_schedule` |
| AD | 8 | 4697–4783 | `clVisitCode`, `clLastCode`, `clLastCode_native` (already cites `stripLast`), `clLastMarker_step`, `clLastIndex`, `clLastIndex_marker`, `clLastIndex_max`, `clLastCode_prev` |
| AH | 22 | 5067–5547 | e.g. `clQueryWords`, `clQueryFlagsTM`, `clQueryFlags_compute`, `clQueryCode_machine`, `clRecordOutputTM`, `clRecordOutput_compute`/`_quadratic`, `clNative_image`, `clRecords_native`, `clCountOutputTM`, `clQuery_budget`. Producer assembly and ledgers. |
| AI | 16 | 5551–5795 | e.g. `clSearchTarget`, `clSearch_native`, `clPrev_native`, `clVisitRow*`, `clNative_cleanCall` (cites `exists_installCallTM`), `clVisitStep*`, `clVisitRows` |
| AK | 5 | 6037–6105 | `clFields_size`, `clVisitCode_size`, `clVisitRow_size`, `clVisitRows_size`, `clVisitState_size` |
| AL | 6 | 6164–6261 | `clProducerHorizon`, `clProducerClock_native`, `clVisitRows_native`, `clPackedRecords`, `clPackedRecords_native`, `clPackedRecords_machine` |
| AP | 11 | 6536–6773 | `CLA5Clean`, `clA5_bridge_bound`, `clA5Clean_install`, `clA5Clean_emit`, `clA5Copy_clean`, `clA5Packed_install`, `clA5Pack`, `clA5Cursor_install`, `clA5Modules`, `clA5Modules_bound`, `clA5Startup` |
| AS | 65 | 7116–8342 | e.g. `clA5Template_native`, `clA5Group_native`, `clA5Stored*`, `clA5Next*`, `clA5Fuel`, `clA5Round`, `clA5Output_of_nativeChunk`, `clA5Tail_*`, `clA5Field_*`, `clA5Count*`, `clA5InputPos*`, `clA5Visit*`, `clA5InputFragment*`, `clA5WorkFragment*`, `clA5GroupAt*`, `clA5Cursor*`, index decls, `clA5WorkChoice*`, `clA5Fragment*`, `clA5Emit*`, `clA5OutputIdentity`. Emission selector and output identity. |
| AT | 24 | 8345–8750 | e.g. `clA5Block`, `clA5Meaning`, `clA5Group_eval`, `clA5Tableau_eval`, `clA5Reconstruct`, `clA5Certificate`, `clA5Run_output`, `clA5NoFalse`, `clA5Decider_accept`, `clA5TraceAssignment`, `clA5Sound`, `clA5Complete`, `clA5Equisat`, `clA5Reduction`. Equisatisfiability. |

**LEAVE (looks like §12 machinery but fails the bar, or has no §12 counterpart): 219 decls, 3,764 lines**

| Fam | # | Lines | Members / why it fails |
|---|---|---|---|
| F | 3 | 693–751 | `clFillTM`, `clFill_run`, `clNative_fill`. No catalog row computes `replicate \|x\| b`. Confirmed LIVE. |
| I | 19 | 921–1258 | e.g. `clCountInc`, `clCountTM`, `clCountTape`, `clCountCfg`, `clCount_carry`, `clCount_rewind`, `clCount_run`, `clCount_idle`, `clCountTape_eq`, `clCount_width`. Different semantics from `incrementTM`: `clCountInc` extends the word on overflow (Nat.bits successor, `clCountInc_bits`), while `incrementTM` is fixed-width and wraps. |
| J | 11 | 1264–1434 | `clBankPart`, `clBankTM`, `clBankCfg`, `clBank_part`, `clBank_step`, `clBank_run`, `clBankStart`, `clBank_component`, `clBank_finish`, `clBank_idle`, `clBank_first`. Parallel product, not R1. Running the counters in sequence would change the 2W+2 ledger that `clTrack_round` and `clRec_cost_bound` depend on. |
| K2 | 6 | 1513–1707 | `clTrackTM`, `clTrackCfg`, `clTrack_source`, `clTrack_frame`, `clTrack_dispatch`, `clTrack_round`. The round loops back to its own anchor. |
| L | 12 | 1711–1917 | `clBuffer_append_bit`, `clTwo`, `clCopyTM`, `clCopyCfg`, `clCopy_write`, `clCopy_pair`, `clCopy_forward`, `clCopy_separator`, `clCopy_rewind`, `clCopy_run`, `clCopy_idle`, `clCopy_first`. Doubled-bit append at the record head, not `copyTM` semantics. |
| O | 10 | 2017–2216 | `clRowTM`, `clRowCfg`, `clRow_frame`, `clRow_field`, `clRowPrefix`, `clRow_prefix_run`, `clRow_stored`, `clRow_idle`, `clRow_first`, `clRowPrefix_length`. Indexed loop over l fields. |
| Q | 15 | 2301–2772 | `clRecState`, `clRecTM`, `clRecCfg`, `clRec_row_frame`, `clRec_row_inactive`, `clRec_copy`, `clRec_tick`, `clRec_stop`, `clRec_track_frame`, `clRec_track_inactive`, `clRec_advance`, `clRec_prefix`, `clRec_complete`, `clRec_prepared`, `clRec_cost_bound`. Five-phase controller with a cycle; seams are non-canonical (record head at its length, clock head at t, virtual-input buffer head at inputPos−1). |
| R | 27 | 2775–3084 | e.g. `clBit`, `clNum`, `clNum_bits`, `clAddColumn`, `clCmpUpdate`, `clCmpOrbit`, `clCmpVerdict`, `clCmpTM`, `clCmpCfg`, `clCmp_forward`, `clCmp_rewind`, `clCmp_run`, `clCmp_first`. Four-word cross-sum test, not equality. |
| S2 | 7 | 3145–3314 | `clReadTM`, `clReadCfg`, `clRead_pair`, `clRead_forward`, `clRead_separator`, `clRead_rewind`, `clRead_run`. Reads at a stream cursor; the catalog's pair rows are function-level only. |
| T | 1 | 3337–3363 | `clFirst`. Generic first-return cut; no public counterpart. |
| W | 11 | 3601–3815 | `clLoadTM`, `clLoadCfg`, `clLoad_frame`, `clLoad_field`, `clLoadWords`, `clLoadWords_step`, `clLoad_split`, `clLoad_prefix`, `clLoad_complete`, `clLoad_idle`, `clLoad_first`. Indexed loop. |
| Y | 7 | 3819–3939 | `clInputTM`, `clInputCfg`, `clInput_forward`, `clInput_backward`, `clInput_run`, `clInput_idle`, `clInput_first`. Copies input to a tape; there is no catalog counterpart (candidate for promotion). |
| AC1 | 14 | 4334–4679 | `clMatchState`, `clMatchTM`, `clMatchCfg`, `clMatch_tick`, `clMatch_stop`, `clMatch_load_frame`, `clMatch_load`, `clMatch_cmp_frame`, `clMatch_commit`, `clMatch_compare`, `clMatch_round`, `clPriorRow`, `clMatch_prefix`, `clMatch_complete`. Cyclic search loop. |
| AE | 6 | 4787–4883, 5364 | `clReplayTM`, `clReplayCfg`, `clReplay_back`, `clReplay_forward`, `clReplay_run`, `clReplay_from`. No counterpart (promotion candidate). |
| AJ | 12 | 5798–6160 | `clRepeatTM`, `clRepeatCfg`, `clRepeat_frame`, `clRepeat_call`, `clRepeat_round`, `clRepeat_complete`, `clRepeatWords`, `clRepeat_initial`, `clRepeatOutputTM`, `clRepeatOutput_compute`, `clRepeat_budget`, `clRepeatArgument_native`. The iteration count N(x) depends on the data; `exists_loopTM` / `exists_loopFindTM` need binary fuel R(\|x\|) that depends only on input length. |
| AN | 7 | 6271–6560 | `clA5_call_first_halt`, `clA5StopTM`, `clA5StopCfg`, `clA5Stop_step`, `clA5_live_prefix`, `clA5Stop_clean`, `clA5Clean_stop`. Converts a live exit into a halt for the `emit_run` host. `seamReleaseTM` is the analog, but the host has a cycle. |
| AO | 10 | 6339–6635 | `clA5Pad_seam`, `CLA5HostState`, `clA5HostNext`, `clA5HostEntry`, `clA5HostRet`, `clA5HostTM`, `clA5Host_seam`, `clA5Host_call`, `clA5_guard_add`, `clA5Host_clean`. The host cycles 3→4→anchor; R2 has no cycle combinator. |
| AQ | 39 | 6776–8292 | e.g. `clA5_pt_const`, `clA5_pt_cond`, `clA5_pt_eq` (these 3 already wrap catalog rows), `clA5MapTM`, `clA5Map_run`, `clA5_pt_tail`, `clA5_pt_head`, `clA5Iter_native`, `clA5Drop_native`, `clA5Div_native`, `clA5Mod_native`, `clA5Decode*`, `clA5EqNum_native`. Finite transducers and unary arithmetic; no catalog rows exist. |
| AR | 2 | 7430–7527 | `clA5CompareTM`, `clA5Compare_compute`. Halting-verdict wrapper around the cross-sum comparator. |

**REPLACE: passes the bar today (5 decls, 92 lines)**

| Fam | Members | Facility |
|---|---|---|
| V (3513–3584) | `clFreshTM`, `clFresh_run`, `clFresh_idle`, `clFresh_first` | R2 `seamCompTM` + `seamCompTM_run_ofCfg` |
| AF (4887–4901) | `clCompute_comp` | `FinTM.bufferedCompTM_computesInTime` (Composition.lean:355) |

**REPLACE: flagged LEAVE because blocked (63 decls, 854 lines)**

| Fam | # | Lines | Members | Facility |
|---|---|---|---|---|
| M | 7 | 1581, 1926–1999, 2588, 3367 | `clLeft_until`, `clSlotAction`, `clSlotCfg`, `clSlot_apply`, `clSlot_run`, `clSlot_release`, `clMap_run` | R1 |
| N | 27 | 2003–4905 | e.g. `clRowIndex`/`Select`/`_inverse`, `clRecTrack*`, `clRecRow*`, `clRecClockIndex`, `clLeft_ne_right`, `clRight_ne_left`, `clLoadIndex`/`Select`/`_inverse`, `clPrepareIndex`/`Select`, `clRecordSelect`/`Index`/`_inverse`, `clMatchLoad*`, `clMatchCmp*`, `clOneSelect` | R1 `Fin m ↪ Fin k` embeddings |
| AM | 5 | 6289–6336 | `clA5PadAction`, `clA5PadTM`, `clA5PadCfg`, `clA5Pad_apply`, `clA5Pad_run` | R1 `embedEmitTM` |
| U | 8 | 3382–3509 | `clErase_last`, `clWipeTM`, `clWipeCfg`, `clWipe_forward`, `clWipe_backward`, `clWipe_run`, `clWipe_idle`, `clWipe_first` | Catalog `clearTM` |
| Z | 5 | 3949–4053 | `clPrepareTM`, `clPrepare_start`, `clPrepare_complete`, `clPrepare_idle`, `clPrepare_first` | R2 + R1 |
| AB | 4 | 4178–4289 | `clRecordTM`, `clRecordCfg`, `clRecord_prepare_frame`, `clRecord_complete` | R2 + R1 |
| AG | 7 | 4909–5063, 5382 | `clOutputTM`, `clOutput_compute`, `clPreparedTM`, `clPreparedCfg`, `clPrepared_run`, `clPrepared_idle`, `clOutputAt_compute` | R2 + R1 |

**DEAD-CANDIDATE: 6 decls, 118 lines.** Evidence is from the comment-stripped source.

| Decl | Defined | Only references |
|---|---|---|
| `clRefClockTM` | 899 | 916 (inside `clRefClockCfg`) |
| `clRefClockCfg` | 914 | none |
| `clCount_first` | 1151 | 1218 (inside `clRefCount_first`) |
| `clRefCountTM` | 1188 | 1209, 1213, 1219 (inside `clRefCount_first`) |
| `clRefCount_first` | 1205 | none in code; one docstring mention at 1242 (`clCount_width`) |
| `clReadFields` | 3133 | 3137 (its own recursion) |

- These form three closed clusters. Nothing that a public theorem reaches cites any of them.
- E5 kept the first four as "kernel-dead, demoted on textual grounds" (`audits/evidence/ch2-epoch34/e5-dedup-inventory.md:218-223`). The only textual citations are inside the cluster and the docstring.
- `clRefClockCfg` and `clReadFields` appear in neither E5 list. That is a gap in the E5 record; re-run the kernel walker before deleting them.

**Prior guidance, checked against the source:**
- `clFill*` is LIVE. Path: `SAT_NPHard → clA5Reduction → clA5OutputIdentity → clA5Output_of_nativeChunk → clA5Fuel → clPackedRecords_native → clPrepHeader_native → clNative_fill → clFillTM`. `clNative_fill` is also used by `clVisitRow_native`.
- `clCertificateCall` and `clTrack_schedule` were dead at source and are already deleted (E5 inventory lines 154 and 214; zero hits anywhere in TCSlib).
- The "11 generated kernel artifacts" are **absent from Hardness.lean**. Its certified kernel surface is exactly the 5 source publics (`kernel-surface-inventory.md:111-117`), and the file has no `deriving`, `instance` or attributes.
  - The artifacts live in Nondeterminism (`stepWith.eq_1`), EXP (`solveSplitWith.eq_1`) and SAT (`WidthAtMost`/`fallback`/`numVars.eq_1` plus the 7-member `instDecidableEqSatStreamState` family).
  - The inventory implies 8+7 = 15 artifacts before E5 and 5+7 = 12 after, not 11. Worth flagging to whoever owns that count.
- The known "~82 classic-family" prefix count is exactly 82 (clCount 28, clCmp 20, clBank 11, clCopy 10, clRead 8, clSlot 5). By role it is mixed: the `clCount*` prefix includes 5 pure-spec decls, 3 output-assembly decls and 1 dead decl.

## 3. Facility mapping and seam analysis for each REPLACE family

- **V `clFresh*` → R2 (passes).**
  - `clFreshTM` already has `seamCompTM`'s shape, up to unfolding: state `Fin 3 ⊕ clReadTM.State`, dispatch `FinTM.controlAction 0 (some (.inr entry))`, left branch `Action.mapState Sum.inl`.
  - Hardness's `.mapState Sum.inl` / `.mapState Sum.inr` seams match the R2′ `seamCompTM_run_ofCfg` statement exactly. The stream head is displaced, which the general-configuration variant handles.
  - No glue is needed. Saves about 20 lines; `clMap_run` call sites drop from 9 to 7. `clFresh_idle` / `clFresh_first` stay, because `clRead_run` has no first-return cut.
- **AF `clCompute_comp` → composition row (passes).** It is canonical at the function level: `bufferedCompTM_computesInTime` plus `output_length_le` and `mono`. Saves about 15 lines.
- **M / N → R1 (LEAVE).**
  - The seams are fine: R1 frames are general.
  - Blocker 1 is the missing selected-tape field lemmas described above.
  - Blocker 2: all 13 `clSlot_run` sites are *guarded* agreement inside multi-phase or cyclic hosts, while R1's transformers are closed and unguarded. `clMap_run` would have to be re-proved on its own as the glue.
  - Once the Embed API exists: drop the 4 core decls and turn the 27 index/select decls into about 9 embeddings, roughly −160 lines. `clSlot_release` and `clLeft_until` stay; `clLeft_until` is a guarded version of the public `FinTM.leftCfg_run`.
- **AM A5 padding → R1 (LEAVE).** The seams are canonical (`Cfg.ofWords` / `stateWord`), but the glue lemma `clA5Pad_seam` needs selected-tape fields, so it hits the same blocker. With the API: about −40 lines.
- **U wipe → catalog `clearTM` (LEAVE).**
  - The semantics and cost (2\|w\|+2, with a built-in first-return cut) match.
  - The seam is non-canonical: the stream tape's head sits at cursor s, and `clearTM_run` is stated only at `Cfg.ofWords`. Fixing that needs the R1 embedding, which is blocked.
  - The input head p is generic but is always 1 at external call sites (`clLoadCfg x 1`, 3969–4452), so p would have to be specialized to 1.
  - Switching to `SweepPhase` states would change about 40 literal states (`.inl 0`, …) in 3949–5063.
  - With the API: about −90 lines.
- **Z / AB / AG → R2 + R1 (LEAVE).**
  - The gluing matches R2′. The relocated phase does not: clInput onto the last tape, clRecTM, A onto the first A.k tapes, replay onto tape i.
  - Without R1, each relocated phase needs a standalone `clSlotAction` machine, and the endpoint shape changes into `(clSlotCfg … id …).mapState Sum.inr`. That ripples into the consumers of `clPreparedCfg` / `clRecordCfg`, so the net gain is about zero.
  - With the API: about −40 to −60 lines.

**Simplifications outside §12, all strict:**
- `clBuffer_append_bit` (1711, one use at 1757) is `(FinTM.bufferTape_append w b).symm`.
- `clA5_pt_unaryLength` (6896, 10 uses) duplicates `clNative_fill true`.
- `clCountTape` duplicates `FinTM.bufferTape` (that is exactly what `clCountTape_eq` proves).

**Already compliant:** Hardness already cites 13 catalog function rows, `exists_emitLoopTM`, `exists_installCallTM`, `exists_emitCallTM`, `emit_run` / `emitAction` and `bufferedCompTM`.

## 4. Summary

| Class | Decls | Lines (blocks) |
|---|---|---|
| KEEP | 260 | 3,292 |
| LEAVE | 219 | 3,764 |
| REPLACE, passes now (V R2, AF composition) | 5 | 92 |
| REPLACE, flagged LEAVE (R1 M+N+AM 39; CATALOG U 8; R2 Z+AB+AG 16) | 63 | 854 |
| DEAD | 6 | 118 |
| **Total** | **553** | **8,120** |

**Line impact:**
- Doable now: −9 decls (6 dead, `clCompute_comp`, `clBuffer_append_bit`, `clA5_pt_unaryLength`), about −170 lines.
- Possible only after Embed.lean exports selected-tape lemmas: about −34 more decls, about −300 to −350 more lines.
- Even the best case removes only about 6% of the file.

**Suggested two-batch split.** Run them in order; the public surface (76–85 and 8752–8902) stays byte-identical throughout.

- **Batch 1, lines 1–3818** (A, A2, A3, and A4 up to the end of `clLoad_first`):
  - Delete X (895–918, 1147–1239 cluster, 3131–3143) and fix the `clCount_width` docstring at 1241–1243.
  - Replace `clBuffer_append_bit`.
  - Apply R2 to `clFresh` (3511–3584). Its state type is unchanged, so the downstream literals stay valid.
  - If the Embed API has landed: migrate M, N and U (decls ≤3818) and the 5 `clSlot_run` sites at 2074, 2452, 2636, 3375, 3657. Keep `clSlot_run` alive for batch 2. U's `SweepPhase` ripple reaches 3949–5063, so either update those literals here or defer U to batch 2.
- **Batch 2, lines 3819–8904** (rest of A4, A5, equisatisfiability):
  - Replace `clCompute_comp` (users at 5160, 5314).
  - Rename `clA5_pt_unaryLength` to `clNative_fill true`.
  - If the Embed API has landed: Z/AB/AG, N (decls >3818), AM, and the remaining 8 `clSlot_run` sites (3971, 4271, 4446, 4532, 4962, 5032, 5418, 5881). Then delete the `clSlot` core.

**Prerequisite outside this file:** public selected-tape field lemmas for `embedEmitCfg` / `embedSilentCfg` in `TCSlib/Complexity/TuringMachine/Build/Embed.lean`. Without them, every R1 item in this plan stays LEAVE.
```

## ===== audits/routine-f1-agent-reports/batchF2A-REPORT.md =====

```
# F2 / Batch A — partial delivery, 17 of 19 targets

**This is not a zero-sorry completion.** It invokes ground rule 7 (continuation budget) of the supplied brief. The first 17 targets in the prescribed risk order are proved and checked. Exactly two original `sorry` bodies remain, and no new private helper is admitted.

## Repository and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required starting branch: `complexity/arora-barak-ch3-4`.
- Recorded base: `ead9abf1cf0d5441da438d22399a9e9b9257fdf5`.
- Working/delivery branch: `fill/s12-f2-A`.
- Delivery commit: `e2cf86eafbb9af925a29963802453e9ead638bbd`.
- Only changed tracked path: `TCSlib/Complexity/TuringMachine/Build/Catalog.lean`.
- No push, PR, rebase, or `lake build` was performed.
- All 72 original source declarations retain their order. All original signatures, docstrings, imports, option headers, and non-target bodies (including all F1 helpers/proofs) are unchanged. The proof bodies of 17 targets and 306 new private source declarations are the only changes.

## Exact remaining frontier

1. `Turing.FinTM.exists_loopTM_spaceUsed` — unchanged original `sorry`, risk-order item 18. The six-step ledger in the brief is still owed. The local copies of the received loop controller and its phase contracts are now available as `f2_loopHost`, `f2_loopHost_body_capture`, `f2_loopHost_prepare`, `f2_loopHost_round`, and their companion declarations. `f2_loopHost_contracts`, `f2_segment_heads`, and `f2_seamed_space` already prove the reusable-seam time-window space argument used by split search. They do **not** constitute a claim that the required `hstartSpace` / `hroundSpace` / `hFspace` ledger has been discharged. Continue by bounding source body positions from the space hypotheses, projecting those positions through each captured call, retaining the fuel bank bound, and combining the fixed-width counter/capture and flag intervals. No multiply-by-round-count space argument is acceptable.
2. `Turing.FinTM.computesFunInTime_pairMapSnd_spaceUsed` — unchanged original `sorry`, risk-order item 19, still last. No new forwarding controller has been installed. The named construction obligations remain: validating buffer stage; encoded-prefix emission stage; forwarding payload simulation with both virtual-input boundary clamps, including empty payload; their seam; malformed-input rejection; coefficient-one source-bank trajectory containment; and halted-tail bounds. Do not reuse the refuted captured-output `pairMapTM` witness.

New private helpers remaining `sorry`: **none**. The axiom log prints all 19 targets; exactly the two entries above contain `sorryAx`.

## Verification

- Stock Lean `4.25.0` (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`), as pinned in `lean-toolchain`.
- Mathlib pin: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; manifest unchanged.
- Setup used `lake exe cache get` only. The final cache retrieval obtained and decompressed all 7506 requested files.
- Ran the prescribed 65-module order. Its first facade attempt reported the anticipated missing `Build/Embed.olean`. Individually checked `Build/Embed`, `Build/Seam`, `NDCodes`, `Formulas/QBF`, and `Formulas/QBFEncoding`, then resumed from the facade through the final module. All resumed checks passed. Supplemental bootstrap output can contain tool-output truncation markers; the final owned-file/facade evidence is in `final-sweep.log`.
- Final edited-file check: `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Catalog`, exit 0, fresh `.olean`, **0 error diagnostics and 2 documented sorry warnings**.
- Final facade: `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine`, exit 0, fresh `.olean`, **0 errors and 0 local sorry warnings**. A facade import does not erase the two documented Catalog admissions.
- All 17 completed target axiom footprints are exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. Both remaining targets have `sorryAx`, as expected for this partial. See `axioms.log` and `verification/axioms.lean`.
- Statement/body/order freeze audit: PASS; see `verification/owned-file-audit.json`.
- `git diff --check`: PASS.
- Scoped campaign style checker: 0 FAIL, 1 WARN (9404-line file). The supplied brief explicitly forbids splitting this owned file; reopening inaccessible private witnesses and retaining all F1 material accounts for the size. No public helper surface was added.

### Environment note

This execution environment could not resolve the stock binaries' `/proc/<current numeric pid>/exe` lookup. An external `LD_PRELOAD` shim maps only that exact self-process path to `/proc/self/exe`, leaving other calls unchanged. `environment/self_exe.c` is included for reproducibility; it was compiled outside the repository. It does not alter Lean proof terms, the kernel, toolchain sources, or repository files. The Lean checks used the stock pinned binary with this path shim. No `native_decide`, proof axiom, unsafe proof escape, or additional admission was introduced.

## Per-target audit route and proved bound

The quotations below are the matching rows of `audits/routine-infra-findings.md`, “Catalog Part 2: 21/21”. They remain binding together with the later R4/R5 repairs and answer-5 ledger. Bounds below concern the same chosen machine in both conjuncts, at every horizon.

### 1. `computesFunInTime_id_spaceUsed` — PROVED

> **Supported, same witness family.** Identity has linear time and a constant whole-run work-space bound, with the same existential machine in both clauses. The original `idTM` has zero work tapes, hence space exactly zero at all times.

Witness `f2_idTM`; time `n+1`, work space exactly `0` at every horizon. Chosen `c=1`.

### 2. `computesFunInTime_const_spaceUsed` — PROVED

> **Supported, same witness family.** A fixed output word has linear-in-input time allowance and constant work space. The original zero-work-tape finite emission chain satisfies both, with the constant chosen after the fixed word.

Witness `f2_constTM w`; fixed emission chain, time `(w.length+1)(n+1)`, work space exactly `0`.

### 3. `computesFunInTime_prepend_spaceUsed` — PROVED

> **Supported, same witness family.** Prepending the fixed word has linear time and constant whole-run work space. The actual `catalogPrefixTM` has zero work tapes, a stronger property than the sketch's no-work-head-movement claim.

Witness `f2_catalogPrefixTM w`; time `(w.length+1)(n+1)`, work space exactly `0`.

### 4. `computesFunInTime_pairEncodeFixed_spaceUsed` — PROVED

> **Supported, same witness family.** Pairing a fixed first component with the input takes linear time and constant work space. The fixed doubled prefix plus separator is exactly a prepend instance, so zero work tapes suffice.

Prepend the doubled fixed prefix and separator. Both clauses use the same zero-work-tape witness; the prepend constant covers time and space.

### 5. `computesFunInTime_pairValid_spaceUsed` — PROVED

> **Supported, same witness family.** Emit a singleton grammar-validity bit in linear time and constant work space. `pairValidTM` has no work tapes; alignment and the pending bit live in finite control.

Witness `f2_pairValidTM`; time `n+1`, work space exactly `0`, `c=1`.

### 6. `computesFunInTime_pairDup_spaceUsed` — PROVED

> **Supported, same witness family.** Emit `pairEncode x x` in linear time with constant work space. `pairDupTM` rereads the bounded read-only input and has zero work tapes.

Witness `f2_pairDupTM`; time `4(n+1)`, work space exactly `0`, `c=4`.

### 7. `computesFunInTime_incFixed_spaceUsed` — PROVED

> **Supported, same witness family.** Emit the same-width successor, or `[]` on overflow, in linear time and constant work space. This is the original zero-work-tape transducer using input scans and a finite carry flag, not the new in-place work-tape routine.

Witness `f2_incFixedTM`; time `3(n+1)`, work space exactly `0`, `c=3`.

### 8. `computesFunInTime_pairFst_spaceUsed` — PROVED

> **Supported, same witness family.** Emit the decoded first component, or empty output on parse failure, in linear time and linear work space. The actual parser buffers at most half the original input before replay; malformed input may leave a partial buffer but never a larger visited span.

Witness `f2_pairExtractTM true false`; received sharp time `5(n+1)`. All-time visited sets are contained in the stopped prefix, of at most `5(n+1)+1` cells on its one tape. Both stated clauses use `c=6`.

### 9. `computesFunInTime_pairSnd_spaceUsed` — PROVED

> **Supported, same witness family.** Emit the decoded second component, or empty output on parse failure, with the same bounds. The shared `pairExtractTM false true` still buffers the first component and traverses that buffer before copying the suffix; those visits remain linear in input length.

Witness `f2_pairExtractTM false true`; the same sharp-time/visited-prefix argument, including malformed inputs, gives `c=6` for time and linear space.

### 10. `computesFunInTime_pairConcat_spaceUsed` — PROVED

> **Supported, same witness family.** On a valid pair emit the concatenated components, otherwise `[]`, with linear time and work space. `pairExtractTM true true` uses the same bounded prefix buffer, then streams the second component.

Witness `f2_pairExtractTM true true`; the same grammar-validating buffer and stopped-prefix argument gives `c=6`.

### 11. `computesFunInTime_polyUnary_spaceUsed` — PROVED

> **Supported, same witness family.** Unary `C(n+1)^e` is emitted within `c(n+1)^(e+1)` time and `c(n+1)` work space. For positive exponent, the fixed number of loop tapes each holds a side-length `n+1` bank and revisits it; output is uncharged physical output. Exponent zero uses the fixed emission chain.

Exponent zero uses the constant family. For `e=d+1`, the received nested-loop generator uses `d+1` banks. `f2_polyHeads`, `f2_poly_step`, and `f2_poly_space` contain every trajectory in a fixed interval and prove space `5(d+1)(n+1)`; the coefficient `C+10(d+1)+4` covers both clauses.

### 12. `computesFunInTime_polyBits_spaceUsed` — PROVED

> **Supported with the R5 case split.** Binary polynomial value has the old time allowance and work space at most `c(C(n+1)^e+1)`. For positive coefficient and exponent, the unary intermediate, linear loop banks, and binary counter all fit that value bound. A zero coefficient requires the constant-empty family; exponent zero is another fixed-value instance.

R5 is implemented before the buffered route: `C=0` and `e=0` use constant-output machines. For positive `C,e`, compose the received unary generator with the direct counter. The sharper generator time is degree `e`, so the stopped all-time footprint is bounded by a constant times `C(n+1)^e+1`. The frozen degree `e+1` time clause is retained.

### 13. `computesFunInTime_lengthBits_spaceUsed` — PROVED

> **Supported by a direct construction; original witness's sharp space unchecked.** The machine must output binary input length in linear time using `O(Nat.size n+1)` visited cells. A variable-width binary counter can return its head after each carry and advance the input once per increment; the sum of carry lengths is bounded by `∑_{j≥1} floor(n/2^j)≤n`, so total time is linear, and the counter occupies only its bit width plus boundary cells. The attached old proof delegates to `Complexity.timeConstructible_id`; its source is not attached, so that particular witness is not certified here.

Direct variable-width counter `f2_counterTM`, with `c=5`: time `5(n+1)`, space `5(Nat.size n+1)`. The potential identity for carries gives the linear counting budget; `f2_counter_count_space`, `f2_counter_heads`, and `f2_counter_space` include intermediate carries, output, and the stationary tail. No use of the existential sharp witness `timeConstructible_id`.

### 14. `computesFunInTime_pairLenCheck_spaceUsed` — PROVED

> **Supported, same witness family.** Decide the original first-component polynomial length test, rejecting malformed pairs, with time `c(n+1)^(e+1)` and space `c((n+1)^e+n+1)`. The parser/composition banks have linear spans and the captured unary output has length at most `C(n+1)^e`; the fixed coefficient `C` is absorbed in `c`. This bound deliberately keeps the linear term, including `C=0` and `e=0`.

The received `f2_pairCountTM` captures a generator composed with the received first-component extractor. `f2_unary_sharp` and the grammar length bound give actual time `K((n+1)^e+n+1)`; the stopped all-time trajectory therefore fits the stated space envelope. One enlarged coefficient gives the frozen degree `e+1` time clause and space `c((n+1)^e+n+1)`.

### 15. `computesFunInTime_stripLast_spaceUsed` — PROVED

> **Supported, same witness family; R8 corrects its description.** On a valid pair, strip the second component before its last `true` and re-encode the pair; reject if no such marker exists. The guard's extraction/composition uses linear banks, `rawStripTM` buffers the original input once, and the timed conditional keeps these disjoint finite banks; their total span is linear. The quadratic time contract is retained even though the attached construction proves a stronger intermediate bound.

The received raw buffer, guard, composition, and timed-conditional family are assembled in `f2_strip_linear`. Its actual bound is `a(n+1)`, before the original quadratic weakening. `f2_space_of_time` then proves linear all-time space for that same machine. The target uses `c=a+M.k(a+1)`.

### 16. `computesFunInTime_splitSolve_spaceUsed` — PROVED

> **Supported, same witness family at the requested loose bound.** The least valid split, or empty failure, keeps time degree `e+2` while using space degree `e+1`. Each actual source/body segment has time `O((n+1)^(e+1))`, hence at most that many head moves per tape from its origin; canonical round returns confine the union of reused spans to a fixed multiple of that bound. Fuel and the accepted output buffer also fit it, and the result-bearing loop reuses its banks rather than allocating a new bank per candidate.

The received source, prepare/count/restore/emit body, and result-bearing loop are reopened locally. `f2_loopHost_contracts` additionally exposes bounded canonical seams and a bounded exhaustion terminal. `f2_segment_heads` confines all rounds and halted tails to one fixed interval; `f2_seamed_space` includes startup. Instantiation by `f2_splitSolve_of_body` retains time degree `e+2` and space degree `e+1`, with no factor for the number of candidates in space.

### 17. `computesFunInTime_cond_spaceUsed` — PROVED

> **Supported, same witness family.** A conditional retains the old time clause and uses at most `sD(n)+max(s₁(n),s₂(n))+c` work space. The attached timed controller keeps the decider bank, the selected branch bank, and idle branch-origin cells disjoint; only one output bit is captured from the decider. Input rewind is uncharged input-head motion, and no monotonicity is needed because both branches see the same input.

Witness `f2_timedCondTM D M₁ M₂`. `f2_cond_ledger` gives a decider-source prefix and a selected-branch prefix at every host horizon; back/read and rewind only repeat endpoints. `f2_branch_space` counts the unselected origins exactly and `f2_cond_space` charges two capture-head cells. `c=7+M₁.k+M₂.k` covers time and the exact coefficient-one bound `sD(n)+max(s₁(n),s₂(n))+c`.

### 18. `exists_loopTM_spaceUsed` — PENDING

> `Loop:2519` | None: `c(T n+1)(R n+2)` | Add `S,hFspace,hstartSpace,hroundSpace`; `space ≤ c(S n+T n+1)`

No proved export in this partial. Target bound remains `c(S(n)+T(n)+1)` with the inherited time clause; see the exact frontier above.

### 19. `computesFunInTime_pairMapSnd_spaceUsed` — PENDING

> **Supported as an existential target, but not by the documented old witness (R4).** It retains the original linear-plus-`Tg` time and adds `Sg(n)+c(n+1)` space, assuming monotonicity of both budgets and all-time payload space. A controller can first validate and buffer the pair, output the encoded first component, and simulate `Mg` on a buffered second component while forwarding its output. Source work-head trajectories remain unchanged, giving coefficient 1 on `Sg`, and the input buffer/administration costs only `O(n+1)`; this construction must replace the capture-all-output sketch.

No proved controller in this partial. Target bound remains `Sg(n)+c(n+1)` with time `c(n+1+Tg(n))`; see the exact frontier above.

## Proof-route details for audit

`f2_space_of_time` is an actual all-time trajectory proof: every later head position is identified with the halted endpoint, the entire visited image is included in the finite time-prefix image, that image has at most `T+1` positions per tape, and the finite tape sum is taken. It is used only where a sharper received time bound already fits the required space envelope (extractors, positive polynomial bits, length checker, and raw stripping). It does not infer an all-time bound from a final configuration alone. The direct counter, reusable unary banks, split-search seams, and conditional source banks have their separate trajectory invariants.

Private copies of received witnesses consistently use the `f2_` prefix. The transition tables are copied from the received Composition, Primitives, Wrappers, Loop, and explicit direct-counter implementation; they are not replacements commissioned outside the brief. Only local proof interfaces are strengthened where the space evidence needs additional data. The counter copies the explicit implementation and its amortized arithmetic, without using the opaque `timeConstructible_id` existential. The only commissioned new controller is the final forwarding summit, which is explicitly not yet constructed.

R5 is discharged in `computesFunInTime_polyBits_spaceUsed`: the `C=0` and `e=0` branches use the constant-output family before the positive buffered route. The linear administrative term is retained for the length checker, including these boundary cases. R8 is reflected by `f2_strip_linear`; its quadratic public time allowance is merely weakening of the actual linear intermediate.

For split search, the result-bearing loop is needed. `f2_exists_loopFind_space` uses the received finding host and its canonical seams, not the decision-only loop theorem. Completed fuel head positions are bounded at the first halt; all other canonical seam heads are zero. Each actual bounded segment therefore lies in a common interval. Accepted payload capture and replay are included in that segment's proved duration, and the terminal's stationary suffix is explicitly covered. Thus the number of candidates multiplies time but never the space interval.

For W3, `f2_cond_ledger` supplies finite source-prefix indices at every host time. The decider-bank image is contained in its source image up to its time budget, and the selected-branch image in its source image up to the host horizon. `f2_branch_space` adds exactly the idle branch's origin cells. The capture bank visits only positions zero and one, and native input rewind is uncharged.

## Requested shared lemmas

No shared-file change is required to use this partial. Useful future projections, currently private here, are `f2_rewind_heads`, `f2_cond_ledger` / `f2_cond_space`, and the canonical-seam head clauses of `f2_loopHost_contracts`. They are requests for later serial integration only; no source outside the owned file was edited, including the queued Wrappers projection.

## Escalations

None: no frozen statement is claimed unprovable. This is a continuation-budget frontier, not a repaired or weakened specification.

## New private declaration inventory

Every new source declaration is listed below in file order. Compiler-generated constructors, recursors, and derived instance internals inherit the private scope of their listed source declaration. All listed lemmas have checked proofs; none is admitted.

| # | Kind | Name |
|---:|---|---|
| 1 | def | `f2_idTM` |
| 2 | lemma | `f2_idTM_run` |
| 3 | def | `f2_constTM` |
| 4 | def | `f2_catalogPrefixTM` |
| 5 | def | `f2_catalogPrefixCfg` |
| 6 | lemma | `f2_catalogPrefixTM_emit` |
| 7 | lemma | `f2_catalogPrefixTM_copy` |
| 8 | lemma | `f2_catalogPrefixTM_computes` |
| 9 | def | `f2_scanCfg` |
| 10 | lemma | `f2_scanCfg_read` |
| 11 | lemma | `f2_scanCopy_run` |
| 12 | lemma | `f2_scanCopy_finish` |
| 13 | def | `f2_pairDupTM` |
| 14 | lemma | `f2_pairDup_double` |
| 15 | lemma | `f2_pairDup_computes` |
| 16 | lemma | `f2_scanCopy_suffix` |
| 17 | lemma | `f2_scanTrues_run` |
| 18 | lemma | `f2_incFixed_cases` |
| 19 | def | `f2_incFixedTM` |
| 20 | lemma | `f2_incFixed_computes` |
| 21 | lemma | `f2_scanStep_right` |
| 22 | def | `f2_pairValidTM` |
| 23 | lemma | `f2_pairValid_block` |
| 24 | lemma | `f2_pairValid_run` |
| 25 | lemma | `f2_pairValid_computes` |
| 26 | def | `f2_pairExtractTM` |
| 27 | def | `f2_extractCfg` |
| 28 | lemma | `f2_extractCfg_read` |
| 29 | lemma | `f2_extract_first` |
| 30 | lemma | `f2_extract_block` |
| 31 | lemma | `f2_extract_rewind` |
| 32 | lemma | `f2_extract_replay` |
| 33 | lemma | `f2_extract_replay_finish` |
| 34 | lemma | `f2_extract_suffix` |
| 35 | lemma | `f2_extract_finish` |
| 36 | lemma | `f2_extract_run` |
| 37 | lemma | `f2_pairExtract_computes` |
| 38 | inductive | `f2_CatalogPolyControl` |
| 39 | instance | `f2_catalogPolyControlFintype` |
| 40 | instance | `f2_catalogPolyControlDecidableEq` |
| 41 | def | `f2_catalogPolyTape` |
| 42 | def | `f2_catalogPolyMove` |
| 43 | def | `f2_catalogPolyUnaryTM` |
| 44 | def | `f2_catalogPolyCfg` |
| 45 | lemma | `f2_catalogPolyMove_apply` |
| 46 | lemma | `f2_catalogPoly_emit` |
| 47 | lemma | `f2_catalogPoly_rewind` |
| 48 | lemma | `f2_catalogPoly_advance` |
| 49 | def | `f2_catalogPolyCost` |
| 50 | lemma | `f2_catalogPoly_loop` |
| 51 | lemma | `f2_catalogPolyTape_write` |
| 52 | lemma | `f2_catalogPolyCost_le` |
| 53 | def | `f2_catalogPolyCopyCfg` |
| 54 | lemma | `f2_catalogPoly_copy` |
| 55 | lemma | `f2_catalogPoly_setup` |
| 56 | lemma | `f2_catalogPoly_start` |
| 57 | lemma | `f2_catalogPoly_unary_computes` |
| 58 | def | `f2_polyHeads` |
| 59 | lemma | `f2_polyHeads_bounds` |
| 60 | lemma | `f2_poly_step` |
| 61 | lemma | `f2_head_steps` |
| 62 | lemma | `f2_poly_space` |
| 63 | def | `f2_counterInc` |
| 64 | def | `f2_counterCarry` |
| 65 | lemma | `f2_counterInc_potential` |
| 66 | lemma | `f2_counterInc_bits` |
| 67 | lemma | `f2_counterInc_length` |
| 68 | def | `f2_counterBump` |
| 69 | def | `f2_counterTM` |
| 70 | def | `f2_counterTape` |
| 71 | def | `f2_counterCfg` |
| 72 | lemma | `f2_counterTape_read` |
| 73 | lemma | `f2_counterTape_write` |
| 74 | lemma | `f2_counter_carry_step` |
| 75 | lemma | `f2_counter_carry` |
| 76 | lemma | `f2_counter_rewind` |
| 77 | lemma | `f2_counter_start` |
| 78 | lemma | `f2_counter_increment` |
| 79 | lemma | `f2_counter_count` |
| 80 | lemma | `f2_counter_emit_run` |
| 81 | lemma | `f2_counter_emit` |
| 82 | lemma | `f2_counter_computes` |
| 83 | lemma | `f2_counter_count_space` |
| 84 | lemma | `f2_counter_heads` |
| 85 | lemma | `f2_counter_space` |
| 86 | def | `f2_lenAction` |
| 87 | def | `f2_pairCountTM` |
| 88 | def | `f2_lenCfg` |
| 89 | lemma | `f2_lenCfg_read` |
| 90 | lemma | `f2_lenAction_apply` |
| 91 | lemma | `f2_lenSuffix_run` |
| 92 | lemma | `f2_lenParse_first` |
| 93 | lemma | `f2_lenParse_block` |
| 94 | lemma | `f2_lenParse_run` |
| 95 | lemma | `f2_catalogRewind` |
| 96 | lemma | `f2_lenStart` |
| 97 | lemma | `f2_pairCount_computes` |
| 98 | lemma | `f2_catalogPair_inverse` |
| 99 | lemma | `f2_space_of_time` |
| 100 | lemma | `f2_unary_sharp` |
| 101 | lemma | `f2_first_length` |
| 102 | def | `f2_rawStripTM` |
| 103 | def | `f2_stripCfg` |
| 104 | lemma | `f2_catalogBuffer_erase` |
| 105 | lemma | `f2_rawStrip_copy` |
| 106 | lemma | `f2_rawStrip_rewind` |
| 107 | lemma | `f2_rawStrip_replay` |
| 108 | lemma | `f2_rawStrip_finish` |
| 109 | lemma | `f2_rawStrip_erase` |
| 110 | lemma | `f2_rawStrip_trim` |
| 111 | lemma | `f2_rawStrip_computes` |
| 112 | def | `f2_anyTrueTM` |
| 113 | lemma | `f2_anyTrue_run` |
| 114 | lemma | `f2_anyTrue_computes` |
| 115 | lemma | `f2_catalogMarker_cases` |
| 116 | lemma | `f2_strip_linear` |
| 117 | lemma | `f2_loop_live_prefix` |
| 118 | lemma | `f2_loop_silent_prefix` |
| 119 | lemma | `f2_loop_first_halt` |
| 120 | lemma | `f2_loop_orbit_inv` |
| 121 | lemma | `f2_loop_fuel_width` |
| 122 | lemma | `f2_loop_input_move_le` |
| 123 | lemma | `f2_loop_input_run_le` |
| 124 | lemma | `f2_loop_output_length_le` |
| 125 | lemma | `f2_loop_rewind_bounded` |
| 126 | def | `f2_loopDebit` |
| 127 | def | `f2_loopBorrowPos` |
| 128 | lemma | `f2_loopBorrowPos_le` |
| 129 | lemma | `f2_loopDebit_length` |
| 130 | def | `f2_loopValue` |
| 131 | lemma | `f2_loopValue_bits` |
| 132 | lemma | `f2_loopDebit_value` |
| 133 | lemma | `f2_loopDebit_success` |
| 134 | lemma | `f2_loopDebit_iterate_length` |
| 135 | lemma | `f2_loopDebit_iterate_value` |
| 136 | lemma | `f2_loopBuffer_read` |
| 137 | lemma | `f2_loopBuffer_write` |
| 138 | def | `f2_loopDebitTM` |
| 139 | def | `f2_loopDebitCfg` |
| 140 | lemma | `f2_loopBorrow_step` |
| 141 | lemma | `f2_loopBorrow_run` |
| 142 | lemma | `f2_loopBorrow_rewind` |
| 143 | lemma | `f2_loopBorrow_correct` |
| 144 | def | `f2_loopBodyTM` |
| 145 | def | `f2_loopBodyCfg` |
| 146 | lemma | `f2_loopBody_stop` |
| 147 | lemma | `f2_loopBody_step` |
| 148 | lemma | `f2_loopBody_run` |
| 149 | lemma | `f2_loopBody_capture` |
| 150 | abbrev | `f2_LoopHostState` |
| 151 | def | `f2_loopFuelSource` |
| 152 | def | `f2_loopBodySource` |
| 153 | def | `f2_loopControlAction` |
| 154 | def | `f2_loopHost` |
| 155 | lemma | `f2_loopHost_body_capture` |
| 156 | lemma | `f2_loopHost_fuel_capture` |
| 157 | lemma | `f2_loopHost_init` |
| 158 | lemma | `f2_loopControl_idle` |
| 159 | lemma | `f2_loopHost_input_rewind` |
| 160 | def | `f2_loopFrame` |
| 161 | def | `f2_loopWrite` |
| 162 | lemma | `f2_loopControl_apply` |
| 163 | def | `f2_loopReplayTM` |
| 164 | def | `f2_loopReplayCfg` |
| 165 | lemma | `f2_loopReplay_step` |
| 166 | lemma | `f2_loopReplay_run` |
| 167 | lemma | `f2_loopControl_payload` |
| 168 | lemma | `f2_loopHost_replay` |
| 169 | def | `f2_loopFuelCfg` |
| 170 | lemma | `f2_loopFuel_run` |
| 171 | lemma | `f2_loopFuel_init` |
| 172 | lemma | `f2_loopFrame_payload` |
| 173 | lemma | `f2_loopFrame_counter` |
| 174 | lemma | `f2_loopHost_fuel_rewind` |
| 175 | def | `f2_loopCopyTape` |
| 176 | lemma | `f2_loopCopy_read` |
| 177 | lemma | `f2_loopCopy_erase` |
| 178 | lemma | `f2_loopCopy_initial` |
| 179 | lemma | `f2_loopCopy_final` |
| 180 | lemma | `f2_loopHost_fuel_copy` |
| 181 | lemma | `f2_loopHost_fuel_return` |
| 182 | lemma | `f2_loopHost_fuel_setup` |
| 183 | def | `f2_loopFuelCaptured` |
| 184 | def | `f2_loopReady` |
| 185 | lemma | `f2_loopFuelCaptured_frame` |
| 186 | lemma | `f2_loopHost_prepare` |
| 187 | def | `f2_loopBodyPadded` |
| 188 | def | `f2_loopCall` |
| 189 | lemma | `f2_loopBodySource_run` |
| 190 | lemma | `f2_loopHost_anchor_return` |
| 191 | lemma | `f2_loopReady_call` |
| 192 | lemma | `f2_loopHost_release` |
| 193 | lemma | `f2_loopHost_start` |
| 194 | lemma | `f2_loopHost_halt_return` |
| 195 | lemma | `f2_loopCall_frame` |
| 196 | lemma | `f2_loopCall_reframe` |
| 197 | lemma | `f2_loopHost_borrow_step` |
| 198 | lemma | `f2_loopHost_borrow_run` |
| 199 | lemma | `f2_loopHost_borrow_rewind` |
| 200 | lemma | `f2_loopHost_borrow` |
| 201 | lemma | `f2_loopFrame_flag` |
| 202 | lemma | `f2_loopFlag_clear` |
| 203 | lemma | `f2_loopHost_reject` |
| 204 | lemma | `f2_loopHost_payload_rewind` |
| 205 | lemma | `f2_loopHost_frame_replay` |
| 206 | lemma | `f2_loopHost_accept` |
| 207 | lemma | `f2_loopHost_round` |
| 208 | lemma | `f2_loopCall_heads` |
| 209 | def | `f2_loopHost_bound` |
| 210 | lemma | `f2_loopHost_contracts` |
| 211 | lemma | `f2_loop_find_run` |
| 212 | lemma | `f2_segment_heads` |
| 213 | lemma | `f2_space_radius` |
| 214 | lemma | `f2_seamed_space` |
| 215 | lemma | `f2_exists_loopFind_space` |
| 216 | def | `f2_splitStep` |
| 217 | def | `f2_splitAccept` |
| 218 | lemma | `f2_splitStep_inv` |
| 219 | lemma | `f2_splitStep_orbit` |
| 220 | lemma | `f2_catalogFind_congr` |
| 221 | lemma | `f2_splitFind_eq` |
| 222 | lemma | `f2_splitFind_none` |
| 223 | lemma | `f2_splitLoop_result` |
| 224 | lemma | `f2_splitLoop_bound` |
| 225 | def | `f2_splitPos` |
| 226 | lemma | `f2_splitPos_read` |
| 227 | lemma | `f2_splitPos_succ` |
| 228 | def | `f2_splitScratch` |
| 229 | lemma | `f2_splitScratch_erase` |
| 230 | def | `f2_splitRestoreTM` |
| 231 | def | `f2_splitRestoreScan` |
| 232 | lemma | `f2_splitRestore_scan` |
| 233 | def | `f2_splitRestoreClean` |
| 234 | lemma | `f2_splitRestore_append` |
| 235 | lemma | `f2_splitRestore_rewind` |
| 236 | lemma | `f2_splitRestore_run` |
| 237 | def | `f2_splitCountAction` |
| 238 | def | `f2_splitCountCfg` |
| 239 | lemma | `f2_splitCount_over` |
| 240 | lemma | `f2_splitCount_apply` |
| 241 | lemma | `f2_splitCount_run` |
| 242 | lemma | `f2_splitPoly_loop_end` |
| 243 | lemma | `f2_catalogFirstEntry` |
| 244 | lemma | `f2_splitRestore_first` |
| 245 | lemma | `f2_splitCount_accept` |
| 246 | lemma | `f2_splitCount_firstHalt` |
| 247 | def | `f2_splitPrepareTM` |
| 248 | def | `f2_splitPrepareScan` |
| 249 | lemma | `f2_splitPrepare_scan` |
| 250 | def | `f2_splitPrepareReady` |
| 251 | lemma | `f2_splitPrepare_extra` |
| 252 | lemma | `f2_splitPrepare_rewind` |
| 253 | lemma | `f2_splitPrepare_run` |
| 254 | lemma | `f2_splitPrepare_first` |
| 255 | def | `f2_splitSafe` |
| 256 | lemma | `f2_splitSafe_add` |
| 257 | lemma | `f2_splitEmbed_cut` |
| 258 | def | `f2_splitRewindTM` |
| 259 | def | `f2_splitEmitTM` |
| 260 | inductive | `f2_SplitBodyState` |
| 261 | instance | `f2_splitBodyStateFintype` |
| 262 | instance | `f2_splitBodyStateDecidableEq` |
| 263 | def | `f2_splitBodyTM` |
| 264 | def | `f2_splitBank` |
| 265 | lemma | `f2_splitBody_start` |
| 266 | lemma | `f2_splitEmbed_run` |
| 267 | lemma | `f2_splitBody_prepare` |
| 268 | lemma | `f2_splitBody_count` |
| 269 | lemma | `f2_splitBody_rewind` |
| 270 | lemma | `f2_splitBody_restore` |
| 271 | def | `f2_splitEmitCfg` |
| 272 | lemma | `f2_splitEmit_double` |
| 273 | lemma | `f2_splitEmit_separator` |
| 274 | lemma | `f2_splitEmit_suffix` |
| 275 | lemma | `f2_splitEmit_run` |
| 276 | lemma | `f2_splitSafe_one` |
| 277 | lemma | `f2_splitSafe_join` |
| 278 | lemma | `f2_splitBody_round` |
| 279 | lemma | `f2_splitSolve_of_body` |
| 280 | lemma | `f2_splitSource_poly` |
| 281 | lemma | `f2_splitSource_constant` |
| 282 | lemma | `f2_splitBody_envelope` |
| 283 | lemma | `f2_splitSolve_source` |
| 284 | lemma | `f2_splitSolve_closed` |
| 285 | def | `f2_timedPadTM` |
| 286 | def | `f2_timedCondTM` |
| 287 | def | `f2_timedBranchCfg` |
| 288 | def | `f2_timedControlCfg` |
| 289 | lemma | `f2_timed_capture` |
| 290 | lemma | `f2_timed_control_init` |
| 291 | lemma | `f2_timed_branch_run` |
| 292 | def | `f2_timedReadyCfg` |
| 293 | lemma | `f2_timed_read` |
| 294 | lemma | `f2_timed_start` |
| 295 | lemma | `f2_cond_time` |
| 296 | lemma | `f2_rewind_scan_heads` |
| 297 | lemma | `f2_rewind_heads` |
| 298 | def | `f2_finSumEquiv` |
| 299 | lemma | `f2_sum_add` |
| 300 | lemma | `f2_branch_space` |
| 301 | def | `f2_condHeads` |
| 302 | lemma | `f2_control_heads` |
| 303 | lemma | `f2_branch_heads` |
| 304 | lemma | `f2_read_heads` |
| 305 | lemma | `f2_cond_ledger` |
| 306 | lemma | `f2_cond_space` |

## Final sweep tail

```text
PASS TCSlib/Complexity/ClassNP/Transducer
CHECK TCSlib/Complexity/ClassNP/CounterProgPolyTime
PASS TCSlib/Complexity/ClassNP/CounterProgPolyTime
CHECK TCSlib/Complexity/ClassNP/PClosure
PASS TCSlib/Complexity/ClassNP/PClosure
CHECK TCSlib/Complexity/ClassNP/ExpPoly
PASS TCSlib/Complexity/ClassNP/ExpPoly
CHECK TCSlib/Complexity/ClassNP
PASS TCSlib/Complexity/ClassNP

FINAL SUMMARY
Catalog: PASS, exit 0, fresh .olean, 0 errors, 2 documented sorry warnings.
TuringMachine facade: PASS, exit 0, fresh .olean, 0 errors, 0 local sorry warnings.
Remaining bootstrap modules: PASS.
Completed target axiom prints: 17/17 standard triple only; 0 sorryAx.
Unfinished target axiom prints: exactly 2 with sorryAx; this is a partial delivery.
```

## Package contents and application

- `REPORT.md`: this report, explicit remaining frontier, matching audit rows, and complete helper inventory.
- `TCSlib/Complexity/TuringMachine/Build/Catalog.lean`: full modified source.
- `patches/0001-Fill-17-catalog-space-rows-retain-loop-and-forwardin.patch`: format-patch against the recorded base, preserving the agent author.
- `fill-s12-f2-A.bundle`: incremental Git bundle containing branch `fill/s12-f2-A`; it requires the recorded base commit.
- `final-sweep.log`, `axioms.log`, and `verification/`: final evidence and supplemental bootstrap/freeze/style records.
- `environment/self_exe.c`: external execution-environment compatibility shim source.
- `SHA256SUMS`: SHA-256 of every other packaged file, using paths relative to the archive root.

Apply the patch with `git am` from the recorded base, or import the bundle in a repository containing that base. Package verification checks that applying the patch to the base index reconstructs the exact delivery tree and that the bundle is valid. No remote write is part of this delivery.
```

## ===== audits/retrofit-r1-agent-reports/rb2-REPORT.md =====

```
# Retrofit RB2 report

**Status: partial delivery under the brief's escalation rule.** Task 1 and Task 3
are complete. Task 2's length swap is complete; the inverse swap is complete at
all three private use sites, but its declaration and one frozen public use must
remain. Task 4 was not attempted. No admissions were introduced.

## Base and commit series

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Source branch: `complexity/arora-barak-ch3-4`.
- Recorded base: `5588628cbbddea9546f616907364b608e15557fd`.
- Working branch: `fill/retrofit-rb2`.
- The brief was issued at `ff012d28ca3131452161669e1d7efe389b75ba2e`;
  the cloned branch was at the recorded base. The owned source is byte-identical
  between these two commits. No rebase, push, or PR was performed.
- Only `TCSlib/Complexity/TuringMachine/Build/Primitives.lean` is changed in the commit series. Reports and evidence are
  delivery artifacts outside the repository.

```text
f2d1ad365091f7a6ce75708d0f97187e513fbfbd Retrofit RB2: delete 62 dead emitter and split-search privates
de1036e6a3eddd870ba99b16ee069558d86b7113 Retrofit RB2: reuse Encoding lemmas within freeze and refresh status notes
```

## Task 1: 62/62 deletions confirmed

Commit 1 deletes every listed private and its own docstring. The fresh Lean
check succeeds after deletion; no member required restoration and no unexpected
referencer was found. All other declarations, including the six private
instances, are byte-identical. Exactly 1,222 source lines were removed.

- **F24a eval (6):** `emitterIdleTM`, `emitterEvalTM`, `emitterEvalCfg`, `emitter_eval_run`, `emitter_eval_initial`, `emitter_eval_first`.
- **F24b clear (13):** `emitterInterval`, `emitterCleared`, `emitter_cleared_step`, `emitterClearTM`, `emitterClearCfg`, `emitter_clear_left`, `emitter_cleared_zero`, `emitter_cleared_all`, `emitter_clear_scan`, `emitter_origin_erase`, `emitter_clear_origin`, `emitter_clear_run`, `emitter_clear_first`.
- **F24c track (18):** `emitterSpan`, `emitter_span_extend`, `emitterSlots`, `emitterTrackTM`, `emitterTrackCfg`, `emitterTrackMid`, `emitter_track_action`, `emitter_track_stamp`, `emitterLo`, `emitterHi`, `emitter_track_extent`, `emitter_track_support`, `emitter_span_zero`, `emitter_track_initial`, `emitter_track_run`, `emitter_track_computes`, `emitter_span_interval`, `emitter_track_clearable`.
- **F24d bank (11):** `emitterBankSymbols`, `emitterBankPart`, `emitterBankTM`, `emitterBankCfg`, `emitterBank_part`, `emitterBank_step`, `emitterBank_run`, `emitterClear_fixed`, `emitterBank_clear`, `emitterBank_fixed`, `emitterBank_first`.
- **F24e right (9):** `emitterRightTM`, `emitterRightCfg`, `emitter_right_step`, `emitter_right_run`, `emitterRightScan`, `emitter_right_scan`, `emitter_right_finish`, `emitter_right_endpoint`, `emitter_right_computes`.
- **F24f eval closers (2):** `emitter_prepared_eval_first`, `emitter_width_eval_first`.
- **Split orphans (3):** `splitFind_none`, `splitCount_firstHalt`, `splitPrepare_first`.

## Task 2: Encoding replacements and escalation

`catalogPair_length` and its docstring are deleted. Its one use is repointed to
`Turing.length_pairEncode`. All three private uses of `catalogPair_inverse` are
repointed to `Turing.eq_pairEncode_of_pairDecode`.

| Containing private declaration | Final source line | Repointed use |
|---|---:|---|
| `catalogPayload_length` | 2068 | `have hx := Turing.eq_pairEncode_of_pairDecode x a b hd` |
| `pairMap_computes` | 2701 | `(by simpa using Turing.eq_pairEncode_of_pairDecode x a b hd)` |
| `pairMap_computes` | 2721 | `rw [Turing.eq_pairEncode_of_pairDecode x a b hd, Turing.length_pairEncode]` |

**Escalation RB2-E1 — conflicting requirements.** The task requests deletion of
`catalogPair_inverse`, but binding ground rule 1 requires every public proof
body to remain byte-identical, except for the optional `splitSolve` change.
The public proof of `computesFunInTime_stripLast` contains this live reference
at original line 2880 / final line 2872:

```lean
          rw [catalogPair_inverse x u v hd]
```

The public Encoding theorem has the same explicit argument shape, so replacing
that line with the following would complete the use-site swap, but would
violate the public-body freeze:

```lean
          rw [Turing.eq_pairEncode_of_pairDecode x u v hd]
```

Following the escalation rule, that line and the complete original
`catalogPair_inverse` declaration/docstring (final line 2014) are
retained unchanged. It has exactly this one remaining code use. Completing
Task 2 requires an explicit exception for this public-body identifier change;
then the retained private can be deleted. No compatibility alias, new private,
notation, signature change, or import was introduced to work around the freeze.

## Task 3: exactly the three authorized comment blocks

Only the named module-note region (original lines 67–110) and the section notes
at original lines 4419–4439 and 5956–5959 were rewritten. The module-note region
now reads:

```text
**Implementation note (batch P).** The first eleven targets in the batch
brief's fill order and the four continuation targets `pairLenCheck`,
`stripLast`, `pairMapSnd`, and `splitSolve` are proved. The original spec-phase
prose above and on the contracts is retained as the audit record. The length
counter is obtained from the public `Complexity.timeConstructible_id`, whose
proved machine implements precisely the sketched amortized counter. The three
extractors share one private buffered parser, so suffix-only extraction also
buffers and replays silently before copying the suffix; its linear envelope
is unchanged. The fixed-width incrementer adapts the enumerator's carry
semantics to two native-input scans, validating before physical emission.


**Implementation note (batch P2).** The threaded length checker, marker stripper,
threaded map, and split search are proved. The length checker composes the existing
buffered first extractor with the unary generator, captures the result with
`capture_run`, then reparses and counts down on the native payload. Malformed
inputs emit only `[false]`. The marker stripper first guards on a valid
extracted suffix containing a true bit; the successful branch buffers the
whole original encoding, erases its final marker/false-run, and replays the
retained encoding. The guard is complete before any physical output. Both
routes reuse the in-file parser/scan invariant patterns and proved public
wrappers. `catalogPayload_computes` supplies a proved relocated-simulation
component for the threaded map, with its time evaluated at the actual suffix
length; the retained-prefix/captured-output controller is proved below.


**Implementation note (batch P3).** The threaded map is proved.
`pairMapTM` captures `catalogPayload_computes` on the original physical input,
rewinds the capture and input, validates without emission, then replays the
original encoded prefix and captured result. `pairMap_computes` bounds this
controller by `4 * (T n + n + 3)` and the public theorem uses coefficient 40.
All original contract docstrings are retained as the audit record.

The split-search theorem is proved. Its private components include the unary
orbit/search bridges and
`splitSolve_of_body`, which closes the public result only when supplied the
actual startup and round contracts; a candidate-preserving unary-bank
preparer; a counted source-simulation correspondence; the generator's exact
loop endpoint; and a scratch-restoration controller with a positive first
return and no earlier visit to its return state. The combined `splitBodyTM`
and `splitBody_round` assemble these components and prove `hround`.
```

The two section notes now read:

```lean
/-! Emitter implementation. The append-bit and unary-token contracts are
proved below with coefficients one and three. The width-parametric split
contract is proved by the native `emitterP2*` controller.

The `emitterSplit*` layer generalizes the in-file loop closure without any
monotonicity assumption on the width function. The `emitterCompare*` family
is reimplemented in this file from the A-continuation's `e3c*` templates in
`ClassNP/Nondeterminism.lean` at base d7b5b6f94d28df8095165dd4dfe82fd09ba0d414.
Those originals are unchanged and are not cited as imported privates. The
native accepting emitter is `splitEmitTM`/`splitEmit_run`. The controller below
discharges `emitterSplit_of_body`'s literal configuration and strict-interior
anchor contracts. -/
```

```lean
/-! **Emitter P2 implementation.** The controller below proves the
width-parametric split contract. Its generic relocation layer is reimplemented
from batch L's `emCall` family in `Build/Loop.lean`, per the private-harvest
policy. It preserves inactive storage and follows observed returns, including
the mandatory first action when entry equals exit. -/
```

All surviving declaration docstrings and all other comments are unchanged.

## Task 4 and scope

**Not attempted.** This stretch is optional and the brief allows it only after
Tasks 1–3 are delivery-ready. The mandatory inverse swap remains escalated.
No new proof route or constant was introduced; `computesFunInTime_splitSolve`
is byte-identical, including its proof body. No additional private was deleted.
The complete F25a `emitterCompare*` and F27a `emitterP2Erase*` families are
unchanged. No import changed; Primitives does not import Catalog.

## Freeze, duplication, and size

- **Duplication ledger: new copies: none.** The existing inverse-lemma copy
  remains solely because of RB2-E1; it was not changed or copied elsewhere.
- New private declarations: **0**.
- Public declarations: **18 before / 18 after**, in the same order, with each
  complete declaration (docstring, signature, statement, and proof body)
  byte-identical. Six private instances are also byte-identical.
- Private declarations: **318 before / 256 after commit 1 / 255 final**.
- Source lines: **7,636 before / 6,414 after commit 1 / 6,398 final**.
- Comment/string-stripped source has zero `sorry`, `admit`, `axiom`, or
  `native_decide` tokens, both before and after.
- Source SHA-256, base: `72bf7361024c351f3ad9e1ba61106a8376638612769205d50f904184a340205d`.
- Source SHA-256, final: `f04e55a189047d1b061cd0ce4993df84c7959cf0e254f37ac9c9ff339aa5f68f`.
- Repository diff paths: exactly `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`. Final working tree: clean.

## Verification

Pinned Lean is v4.25.0, release commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib is
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
No `lake build` command was run.

The initial cache setup encountered unsupported archive ownership restoration;
it was retried with `TAR_OPTIONS=--no-same-owner`. The full-mathlib download was
stopped after 759 successful files and narrowed to the exact mathlib imports
of the bootstrap dependency closure. The successful `lake exe cache get`
invocation downloaded 847 additional required archives and unpacked all 969
needed module archives. Setup did not change dependency revisions or tracked
repository files. Setup logs and the exact root list are included.

All 65 modules in `scripts/ab_ch1_module_order.txt` were successfully elaborated
in the listed order into a fresh local olean tree, with exit 0 and zero error
diagnostics. The first runner became unavailable after 50 successful checks,
without a completed `Hardness` result or olean. The sweep resumed at that
unfinished module; none of the 50 completed checks was repeated. From that
point, an external launcher selects the stock Lean binary's `-j 1` option.
This changes worker count only; the repository check script is unchanged.
One additional baseline finding is the pre-existing admission in
`TuringMachine/CounterProgRun.lean`, `Complexity.CounterProg.sim_run_of_regs_le`
(declaration at line 343, `sorry` at line 346). The repository check exited 0
and produced a fresh olean, but the extra zero-sorry wrapper initially flagged
it. After confirming the unchanged source, the module was rechecked as an
explicit out-of-scope baseline admission. The raw log preserves both attempts
and the original wrapper failure; its two warning occurrences concern this
same existing declaration. Every other module on the 65-item list is
zero-sorry. No such exception is allowed for the owned file or final checks.
The current facades additionally require six modules absent from
that older order list: `Build/Embed`, `Build/Seam`, `Build/Catalog`, `NDCodes`,
`Formulas/QBF`, and `Formulas/QBFEncoding`. These were compiled just before
their first use, with separate supplemental logs. The latter three each have
one existing out-of-scope chapter-3/4 admission. Thus the complete bootstrap
dependency closure has four existing admitted declarations, including the
counter-program row. None is new, none is in Primitives, and none occurs in
any of the 18 checked public axiom footprints. These are baseline facts, not
retrofit admissions or edits.

The changed file was checked before and after each commit. The initial second
post-commit runner ended without a completed result or olean; the exact same
committed source was rechecked in an isolated invocation. The interrupted log
is retained as `evidence/task23-postcommit-interrupted.log`. The completed
checks are:

```text
task1-precommit: PASS TCSlib/Complexity/TuringMachine/Build/Primitives: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=91.9
task1-postcommit: PASS TCSlib/Complexity/TuringMachine/Build/Primitives: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=129.4
task23-precommit: PASS TCSlib/Complexity/TuringMachine/Build/Primitives: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=117.9
task23-postcommit: PASS TCSlib/Complexity/TuringMachine/Build/Primitives: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=117.3
```

The final required sweep uses the final post-commit Primitives check as its
first check, immediately followed by the TuringMachine facade check. No source
changed between them. Both produced fresh oleans with zero errors and zero
sorry warnings; the full combined log is included:

```text
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6217:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6220:6: warning: 'simp [MultiTapeTM.step, emitterTokenTM, Action.apply, scanCfg, List.append_assoc]' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6220:6: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Primitives.lean:6271:63: warning: This simp argument is unused:
  List.append_assoc

Hint: Omit it from the simp argument list.
  simp [emitterTokenTM, Action.apply, scanCfg, pairEncode, L̵i̵s̵t̵.̵a̵p̵p̵e̵n̵d̵_̵a̵s̵s̵o̵c̵,̵ ̵hlen]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
PASS TCSlib/Complexity/TuringMachine/Build/Primitives: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=117.3

$ bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine: exit=0, errors=0, sorry_warnings=0, fresh_olean=True, seconds=9.3
```

Style lint command:
`python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`.
Result: **style_lint: 0 FAIL, 3 WARN over 7 files**. The three inherited size warnings concern files outside
the allowed splitting scope; this retrofit reduces Primitives by 1,238 lines.

All 18 final axiom footprints are identical to their separately printed
baseline footprints and use only the permitted standard axioms; no `sorryAx`:

```text
'Turing.FinTM.computesFunInTime_prepend' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_lengthBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyUnary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_polyBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairEncodeFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairFst' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairSnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairConcat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairDup' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairMapSnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairLenCheck' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_stripLast' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolve' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_incFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_splitSolveWith' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_unaryToken' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_appendBit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The environment needs a self-executable lookup compatibility shim: stock
processes cannot resolve `/proc/<their numeric pid>/exe`, while
`/proc/self/exe` works. The external `LD_PRELOAD` shim only maps that exact
current-process path to `/proc/self/exe`. Its source is supplied in
`evidence/environment/self_exe.c`. It changes no kernel, proof term, toolchain
source, repository source, or axiom. It is unnecessary on a normal system.

## Archive contents and integration

The archive contains `REPORT.md`, the full modified source under its repository
path, two ordered `git format-patch` patches, an incremental git bundle against
the recorded base, `final-sweep.log`, `axioms.log`, supplemental verification
evidence, and `SHA256SUMS`. Apply the two patches to the recorded base, in
order, or fetch the supplied bundle. The bundle requires that base commit.
RB2-E1 remains an explicit uncompleted mandatory item; this archive does not
claim full completion of Tasks 1–3.
```

## ===== audits/vhost-agent-reports/f1-REPORT.md =====

```
# vhost-f1 — completed proof fill

## Delivery and base

- Result: **11/11 target statements filled**, with no remaining admitted proof in either owned file.
- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Source branch: `complexity/arora-barak-ch3-4`.
- Recorded base: `44d25413044aed185a83ece08f7c29d0446d38ce`.
- The brief cites `756657d0b45f41f2a5e93f976f3189ce99080772`; the recorded base is its immediate successor, the commit issuing this fill brief. No rebase occurred.
- Working branch: `fill/vhost-f1`.
- Delivery commit: `50f846477261689db83c4f4e629c9dad93a7ca96`.
- No push or pull request; no `lake build`.

The archive has a flat layout. `Simulation.lean` is the full replacement for
`TCSlib/Complexity/TuringMachine/Simulation.lean`; `VirtualInput.lean` is the full
replacement for `TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean`.
The format-patch series and incremental git bundle are against the recorded base.
`SHA256SUMS` covers every other archive member.

## Filled statements and binding proof routes

| Statement | Implemented route |
|---|---|
| `MultiTapeTM.step_eq_of_agreeOn` | Split halted/live control; use equality of the complete transition action on the guarded state. |
| `MultiTapeTM.runFrom_eq_of_agreeOn` | Induct on the horizon with the strict-prefix guard; cite the one-step transfer. |
| `vhostEmitTM_step` | Adapt the `bufferedSecondCfg_step` template to buffer plus bank, retaining the output prefix. Cite the existing buffer-read and virtual-movement lemmas; preserve the halting action's writes and emission. |
| `vhostEmitTM_runFrom` | Chain the step contract and valid arrival tags by induction, citing the iteration identities. |
| `vhostEmitTM_visitedByTapeHead_bank` | Project the all-time run identity and identify the two finite images. |
| `vhostEmitTM_visitedByTapeHead_buffer` | Project the buffer head and identify the finite image of source input positions minus one. |
| `vhostCfg_buffer_head_mem` | Project the run identity and use the source input position's `Fin` bounds. |
| `vhostEmitTM_spaceUsed_le` | Split off the buffer tape; identify the bank sum exactly with source space and bound buffer visits by the prescribed interval. |
| `vhostEmitTM_emitting_halt` | Cite the step contract, substitute the halting/emitting action, and associate output concatenation. |
| `vhostSilentTM_runFrom` | Compose `embedSilentTM_runFrom` with `vhostEmitTM_runFrom`; no additional simulation induction. |
| `vhostSilentTM_spaceUsed_le` | Cite selected-tape equality and the capture-growth bound from `Embed`; sum the selected bank and sole capture tape, then apply the forwarding space bound. |

The forwarding step proof consumes `bufferTape_inputSymbol` and
`virtualMove_correct` at `c.mapState (fun _ => ())`: these existing lemmas use
`S : Type`, whereas the frozen target allows `S : Type*`. Mapping only the control
to `Unit` leaves the input position and input read definitionally unchanged. No
signature restriction or duplicate input lemma was introduced.

The imported surface does not expose `Fin.sum_univ_succ`/`Fin.sum_univ_add`.
The forwarding sum uses `Fin.addCases`, `Finset.sum_bij`, and
`Finset.sum_erase_add` to implement the same buffer/bank split without changing
imports. The silent sum uses the analogous selected/capture partition. All
space coefficients and horizons are unchanged.

## Declaration inventory and freeze

Exactly one new declaration, private in `VirtualInput.lean`:

- `Turing.vhostSilent_layout`: for every silent-host tape index, membership in
  the `Fin.castAddEmb 1` range is equivalent to value below `1 + m`, and
  nonmembership is equivalent to equality with `vhostCap m`. Both silent proofs
  use it to discharge capture disjointness; the space proof also uses its
  completeness to exclude any unaccounted ambient tape. It includes `m = 0`.

`Simulation.lean` adds no declarations. No declarations were removed.
Optional exports: **none**.
Requested shared lemmas: **none**; the sole helper is specific to this layout.
Docstring appendices to existing declarations: **none**. The new helper has its
own statement and proof sketch.

The byte-level freeze check replaces only the eleven filled bodies with their
original `sorry` bodies and removes the one new private helper; the resulting
files are byte-identical to the base. Thus all existing statements, definitions,
imports, options, attributes, docstrings, and non-target proofs are unchanged.
`freeze.log` records the checks. The patch application was checked against the
base using a temporary git index and reproduced the exact delivery commit tree;
the bundle also verifies (`packaging.log`). The diff touches only the two owned files;
`Build/Loop.lean`, `CookLevin/Hardness.lean`, and all other files are untouched.

## Duplication ledger

**new copies: none**.

The new host proofs adapt the binding buffered-host template and cite its shared
read/movement facts and the existing run algebra. Neither silent contract
reimplements the embedding simulation. No existing proved declaration was copied
into a new private declaration.

## Verification

- Lean: **4.25.0**, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, matching the manifest.
- `lake exe cache get` completed successfully. The pinned local toolchain and
  dependency files were initially copied into this task's own directory from an
  existing local setup. A process-local executable-path compatibility shim was
  needed in this runtime; it does not change Lean or any proof source.
- The prescribed 65-module bootstrap was run in order, with supplemental checks
  for the current facade imports and the Build infrastructure. During initial
  cache extraction, three concurrent checks exited with a bus error; affected
  checks were retried after cache setup completed. No source was changed to
  address these environment failures. An early facade check preceded the
  `UnaryTape` bootstrap; it was rerun after bootstrap completion. That failed
  attempt is preserved separately in `verification-retries.log`;
  `final-sweep.log` contains the five successful fresh checks in order.
  Out-of-scope baseline admissions were left untouched.
- Final checks use `scripts/lean_check_tree.sh`, which removes the old target
  `.olean` before elaboration and requires a fresh one. All five final modules
  pass with zero errors and zero sorry warnings, in the required order.

Final sweep summary (full diagnostics in `final-sweep.log`):

```text
PASS TCSlib/Complexity/TuringMachine/Simulation: errors=0; sorry_warnings=0; fresh_olean=yes
PASS TCSlib/Complexity/TuringMachine/Build/Embed: errors=0; sorry_warnings=0; fresh_olean=yes
PASS TCSlib/Complexity/TuringMachine/Build/VirtualInput: errors=0; sorry_warnings=0; fresh_olean=yes
PASS TCSlib/Complexity/TuringMachine/Build/Catalog: errors=0; sorry_warnings=0; fresh_olean=yes
PASS TCSlib/Complexity/TuringMachine: errors=0; sorry_warnings=0; fresh_olean=yes
FINAL: 5/5 PASS; 0 errors; 0 sorry warnings; all five oleans freshly produced.
```

All eleven axiom prints, from the final fresh tree (`axioms.log`):

```text
'Turing.MultiTapeTM.step_eq_of_agreeOn' depends on axioms: [propext, Quot.sound]
'Turing.MultiTapeTM.runFrom_eq_of_agreeOn' depends on axioms: [propext, Quot.sound]
'Turing.vhostEmitTM_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostEmitTM_runFrom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostEmitTM_visitedByTapeHead_bank' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostEmitTM_visitedByTapeHead_buffer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostCfg_buffer_head_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostEmitTM_spaceUsed_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostEmitTM_emitting_halt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostSilentTM_runFrom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostSilentTM_spaceUsed_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every footprint is a subset of `[propext, Classical.choice, Quot.sound]`; none
contains `sorryAx` or any additional axiom.

Style lint, one directory per invocation:

- `TCSlib/Complexity/TuringMachine/Build`: **0 FAIL**, 3 inherited file-size WARNs.
- `TCSlib/Complexity/TuringMachine`: **0 FAIL**, 10 file-size WARNs.

`Simulation.lean` is now 1,014 lines. Its existing size deviation is justified in
`AroraBarakChapters3-4Plan.md`, decision-log row **A-S1 spec layer LANDED**:
decision 13.5 locates Z5 beside the lockstep infrastructure, and a split belongs
to the queued D7 window. This fill adds nine lines net to that file and does not
split it. `VirtualInput.lean` is 506 lines. Full lint output is included in
`style-build.log` and `style-machine.log`.

## Completion checklist

- [x] 11/11 frozen target statements filled.
- [x] Base commit and the sole new private declaration recorded.
- [x] Optional exports and requested shared lemmas recorded as none.
- [x] Duplication ledger: new copies none.
- [x] Five final checks: zero errors, zero sorry warnings, fresh oleans.
- [x] Eleven axiom prints: only the permitted standard axioms, no `sorryAx`.
- [x] Both style checks: zero FAIL.
- [x] Diff restricted to the two owned files.
- [x] Full sources, patch series, git bundle, logs, and checksums included.

No remaining proof frontier or escalation.
```

## ===== TCSlib/Complexity/TuringMachine/Build/Catalog.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: catalog promotions and space annotations (R3)

The R3 increment of the machine-construction library
(`machine-library-design.md` §12): the remaining audited A-chain tape
routines promoted as public machines with exact time **and** space costs,
plus the space retro-annotation of the existing catalog and control
surface. Per frozen decision 12.2 this lives in a **new** file — the new
rows and the space lemmas for the old rows both — keeping
`Build/Primitives.lean` byte-identical; the later refactor toward a
per-theme layout is a recorded backlog item.

**Status: statement skeleton (§12 statement phase).** The five routine
machines and their two phase alphabets are real definitions (TM1-style
labelled control, the catalog's house idiom); every contract is sorried,
each with a proof sketch naming its fill obligations.

## Part 1 — new promotions (seam routines)

Configuration-level routines at the `Turing.Cfg.ofWords` seam of
`TCSlib.Complexity.TuringMachine.Build.Convention`, entering at their
start anchor with heads at the origin and exiting at a **live** anchor
(first-return cut included in each contract), so they compose under
`Turing.seamCompTM`. These are D6-style promotions of the audited 4A
privates — the A3 chain proved `3|w| + 3` copy and `2|w| + 2` clear,
matching the external prior art's catalog to within one step
(independent convergence, 2026-10-06 survey; [Bon26], the
transfer/clear/copy routine catalog):

* `Turing.transferTM` — move a word from tape `src` to tape `dst`
  (source erased), within `3|w| + 3`.
* `Turing.copyTM` — copy a word from tape `src` to tape `dst` (source
  kept), within `3|w| + 3`.
* `Turing.clearTM` — blank the word on one tape, within `2|w| + 2`.
* `Turing.compareTM` — word equality of two tapes, verdict in the exit
  anchor, tapes restored, within `2·min(|u|,|v|) + 2`.
* `Turing.incrementTM` — in-place little-endian fixed-width increment
  (`Turing.incFixed`), success/overflow in the exit anchor, within
  `2|w| + 2`; on overflow the word wraps to all-`false`.

Each routine carries per-tape space statements
(`Turing.MultiTapeTM.spaceUsedByTape`): the touched tapes visit at most
the word interval plus the two boundary blanks, and every other tape
stays at its origin singleton.

## Part 2 — space retro-annotation

Per frozen decision 12.3, the existing catalog rows (P1–P15 as realized)
and the control combinators W1–W3 and L receive `spaceUsed` theorems in
this increment, with no signature changes and no edits to the home files:
each annotation restates the audited row's existential contract joined
with a space clause on the same witness, so the audited statement surface
is untouched (additive growth). The emitter combinators (E1/E2/E3′/E4′ —
`exists_emitLoopTM`, `emit_run`/`exists_emitCallTM`, the stream rows
P16–P18, `splitSolveWith`) stay lazy until a space consumer appears.

## Main definitions

* `Turing.SweepPhase`, `Turing.FlagPhase` — the two phase alphabets.
* `Turing.transferTM`, `Turing.copyTM`, `Turing.clearTM`,
  `Turing.compareTM`, `Turing.incrementTM`.

## Main results

All sorried (statement phase): the five routines' run and per-tape space
contracts (`*_run`, `*_spaceUsedByTape`); the catalog space rows
`Turing.FinTM.computesFunInTime_*_spaceUsed` (P1–P15 as realized,
including the threaded-map row with its payload space hypothesis); and
the control-layer rows `Turing.capture_visitedByTapeHead` (W1),
`Turing.FinTM.redirectTM_spaceUsedByTape` (W2),
`Turing.FinTM.computesFunInTime_cond_spaceUsed` (W3), and
`Turing.FinTM.exists_loopTM_spaceUsed` (L).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2–§1.4: the routines are the
  folklore tape subroutines of the textbook's simulation arguments;
  Definition 4.1: the visited-cells space measure the annotations use.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model — TM2-style keyed stacks there, `FinTM`
  tapes with heads here): the transfer/clear/copy/compare routine catalog
  and its exact-cost discipline.
-/

namespace Turing

/-- Phase alphabet of the sweep-shaped routines (`Turing.transferTM`,
`Turing.copyTM`, `Turing.clearTM`): a forward pass over the stored word,
a return pass to the origin, and the live exit anchor. -/
inductive SweepPhase where
  /-- the forward pass over the stored word -/
  | sweep
  /-- the return pass back to the origin -/
  | rewind
  /-- the live exit anchor -/
  | done
deriving DecidableEq, Fintype

/-- Phase alphabet of the verdict-bearing routines (`Turing.compareTM`,
`Turing.incrementTM`): a forward working pass, a return pass carrying the
verdict, and a pair of live exit anchors indexed by the verdict. -/
inductive FlagPhase where
  /-- the forward working pass -/
  | run
  /-- the return pass, carrying the verdict -/
  | rewind (flag : Bool)
  /-- the live exit anchors, one per verdict -/
  | done (flag : Bool)
deriving DecidableEq, Fintype

variable {k : ℕ} {x : List Bool}

/-- **R3, transfer** (design §12; [Bon26]). Move the word stored on tape
`src` to tape `dst`: a forward pass copies cell by cell (both heads in
lockstep), the turn at the source's right blank starts the return pass,
which erases the source on the way back, and the overshoot to the left
blank steps right into the live `done` anchor with both heads at the
origin. -/
def transferTM (k : ℕ) (src dst : Fin k) : MultiTapeTM k Bool SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = dst then (some (some b), SignType.pos)
            else if j = src then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
    | .rewind =>
      match w src with
      | some _ =>
        ⟨0, fun j => if j = src then (some none, SignType.neg)
            else if j = dst then (none, SignType.neg) else (none, 0),
          none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.pos)
            else (none, 0), none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **R3, copy** (design §12; [Bon26]; the A3 chain's `3|w| + 3` row).
Copy the word stored on tape `src` onto tape `dst`, keeping the source:
the same two-pass sweep as `Turing.transferTM` without the erasure on the
return pass. -/
def copyTM (k : ℕ) (src dst : Fin k) : MultiTapeTM k Bool SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w src with
      | some b =>
        ⟨0, fun j => if j = dst then (some (some b), SignType.pos)
            else if j = src then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
    | .rewind =>
      match w src with
      | some _ =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.neg)
            else (none, 0), none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = src ∨ j = dst then (none, SignType.pos)
            else (none, 0), none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **R3, clear** (design §12; [Bon26]; P12's engine, the A3 chain's
`2|w| + 2` row, and the frozen §3 scratch discipline's supporting
primitive). Blank the word on tape `i`: a forward pass to the right blank,
then a return pass erasing each cell, with the left-blank overshoot
stepping right into the live `done` anchor at the origin. -/
def clearTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool SweepPhase where
  q₀ := .sweep
  tr := fun q _ w =>
    match q with
    | .sweep =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some .sweep⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some .rewind⟩
    | .rewind =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (some none, SignType.neg) else (none, 0),
          none, some .rewind⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some .done⟩
    | .done => ⟨0, fun _ => (none, 0), none, some .done⟩

/-- **R3, compare** (design §12; [Bon26]; the 4A chain's `clCmp*` shape).
Test the words on tapes `fst` and `snd` for equality, read-only: a
lockstep forward scan compares cell by cell — the first mismatch (a
differing pair, or one word ending early) selects the `false` verdict, a
simultaneous double blank selects `true` — then a return pass guided by
`fst`'s intact content carries the verdict to the live `done` anchor with
both heads at the origin and both words untouched. -/
def compareTM (k : ℕ) (fst snd : Fin k) : MultiTapeTM k Bool FlagPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w fst, w snd with
      | some a, some b =>
        if a = b then
          ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.pos)
              else (none, 0), none, some .run⟩
        else
          ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
              else (none, 0), none, some (.rewind false)⟩
      | none, none =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind true)⟩
      | _, _ =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind false)⟩
    | .rewind v =>
      match w fst with
      | some _ =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.neg)
            else (none, 0), none, some (.rewind v)⟩
      | none =>
        ⟨0, fun j => if j = fst ∨ j = snd then (none, SignType.pos)
            else (none, 0), none, some (.done v)⟩
    | .done v => ⟨0, fun _ => (none, 0), none, some (.done v)⟩

/-- **R3, increment** (design §12; [Bon26]; the enumerator's
`enumCarryTM` discipline in place, cf. the string-function row
`Turing.FinTM.computesFunInTime_incFixed`). In-place little-endian
fixed-width binary increment on tape `i`: the carry pass flips `true`
cells to `false` moving right; the first `false` flips to `true` and
selects the success verdict; running off the width (all `true`) selects
the overflow verdict, leaving the wrapped all-`false` word — the
enumerator's counter convention. The return pass carries the verdict to
the live `done` anchor at the origin. -/
def incrementTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool FlagPhase where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w i with
      | some true =>
        ⟨0, fun j => if j = i then (some (some false), SignType.pos)
            else (none, 0), none, some .run⟩
      | some false =>
        ⟨0, fun j => if j = i then (some (some true), SignType.neg)
            else (none, 0), none, some (.rewind true)⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some (.rewind false)⟩
    | .rewind v =>
      match w i with
      | some _ =>
        ⟨0, fun j => if j = i then (none, SignType.neg) else (none, 0),
          none, some (.rewind v)⟩
      | none =>
        ⟨0, fun j => if j = i then (none, SignType.pos) else (none, 0),
          none, some (.done v)⟩
    | .done v => ⟨0, fun _ => (none, 0), none, some (.done v)⟩

/-- Configuration at a scan position, with explicit words and head positions. -/
private def catalogCfg {S : Type*} (q : S) (w : Fin k → List Bool)
    (heads : Fin k → ℤ) : Cfg k Bool S x :=
  { Cfg.ofWords q w with workTapePos := heads }

/-- The chronological trace of a forward scan, left turn, return, and entry.
The return index is the number of nonblank cells still to erase or cross. -/
private def catalogTrace {S : Type*} (F R : ℕ → Cfg k Bool S x)
    (D : Cfg k Bool S x) (L t : ℕ) : Cfg k Bool S x :=
  if t ≤ L then F t else if t ≤ 2 * L + 1 then R (2 * L + 1 - t) else D

/-- Local transition equations determine the complete trace, including all
stationary steps after the exit. **Proof sketch.** Induct on elapsed time;
split at the forward endpoint, return endpoint, and stationary tail. -/
private lemma catalog_trace_run {S : Type*} (M : MultiTapeTM k Bool S)
    (F R : ℕ → Cfg k Bool S x) (D : Cfg k Bool S x) (L : ℕ)
    (hF : ∀ r < L, M.step (F r) = F (r + 1))
    (hturn : M.step (F L) = R L)
    (hR : ∀ r < L, M.step (R (r + 1)) = R r)
    (hentry : M.step (R 0) = D) (hD : M.step D = D) (t : ℕ) :
    M.runFrom (F 0) t = catalogTrace F R D L t := by
  induction t with
  | zero => simp [catalogTrace]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    by_cases h₁ : t < L
    · simpa [catalogTrace, show t ≤ L by omega, show t + 1 ≤ L by omega]
        using hF t h₁
    · by_cases h₂ : t = L
      · subst t
        simpa [catalogTrace, show ¬L + 1 ≤ L by omega,
          show L + 1 ≤ 2 * L + 1 by omega, show 2 * L + 1 - (L + 1) = L by omega]
          using hturn
      · by_cases h₃ : t < 2 * L + 1
        · have he : 2 * L + 1 - t = (2 * L - t) + 1 := by omega
          simpa [catalogTrace, show ¬t ≤ L by omega, show ¬t + 1 ≤ L by omega,
            show t ≤ 2 * L + 1 by omega, show t + 1 ≤ 2 * L + 1 by omega,
            he, show 2 * L + 1 - (t + 1) = 2 * L - t by omega]
            using hR (2 * L - t) (by omega)
        · by_cases h₄ : t = 2 * L + 1
          · subst t
            simpa [catalogTrace, show ¬2 * L + 1 ≤ L by omega,
              show ¬2 * L + 1 + 1 ≤ L by omega] using hentry
          · simpa [catalogTrace, show ¬t ≤ L by omega,
              show ¬t + 1 ≤ L by omega, show ¬t ≤ 2 * L + 1 by omega,
              show ¬t + 1 ≤ 2 * L + 1 by omega] using hD

/-- A head confined to the inclusive interval from minus one to `L` visits
at most `L+2` cells. -/
private lemma catalog_space_bound {S : Type*} (M : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) (L t : ℕ) (i : Fin k)
    (h : ∀ u, -1 ≤ (M.runFrom c u).workTapePos i ∧
      (M.runFrom c u).workTapePos i ≤ (L : ℤ)) :
    M.spaceUsedByTape c t i ≤ L + 2 := by
  have hs : M.visitedByTapeHead c t i ⊆ Finset.Icc (-1 : ℤ) (L : ℤ) := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_Icc.mpr (h u)
  exact (Finset.card_le_card hs).trans (by rw [Int.card_Icc]; omega)

/-- A head stationary at zero has exactly its origin singleton as visited set. -/
private lemma catalog_space_one {S : Type*} (M : MultiTapeTM k Bool S)
    (c : Cfg k Bool S x) (t : ℕ) (i : Fin k)
    (h : ∀ u, (M.runFrom c u).workTapePos i = 0) :
    M.spaceUsedByTape c t i = 1 := by
  simp only [MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead, h]
  rw [Finset.image_const Finset.nonempty_range_add_one]
  rfl

/-- Erasing the last cell of a prefix shortens that prefix by one.
**Proof sketch.** Read the last cell, earlier cells, and outside cells separately. -/
private lemma catalog_erase_take (w : List Bool) (r : ℕ) (hr : r < w.length) :
    Function.update (FinTM.bufferTape (w.take (r + 1))) (r : ℤ) none =
      FinTM.bufferTape (w.take r) := by
  funext z
  by_cases hz : z = (r : ℤ)
  · subst z
    simp [FinTM.bufferTape, List.getElem?_eq_none]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · simp only [FinTM.bufferTape, if_pos h0]
      by_cases hzr : z.toNat < r
      · simp [List.getElem?_take, hzr, show z.toNat < r + 1 by omega]
      · have hzr' : r + 1 ≤ z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by simp; omega)]
    · simp [FinTM.bufferTape, h0]

/-- Appending the next original bit extends a copied prefix by one. -/
private lemma catalog_write_take (w : List Bool) (r : ℕ) (hr : r < w.length) :
    Function.update (FinTM.bufferTape (w.take r)) (r : ℤ) (some w[r]) =
      FinTM.bufferTape (w.take (r + 1)) := by
  rw [List.take_succ_eq_append_getElem hr]
  simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hr)] using
    (FinTM.bufferTape_append (w.take r) w[r]).symm

/-- Clear's forward phase has intact words; the return phase retains exactly
the unerased prefix below and at the head. -/
private def catalogClearF (i : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .sweep w (fun j => if j = i then (r : ℤ) else 0)

/-- Clear's return index counts the remaining unerased cells. -/
private def catalogClearR (i : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .rewind (Function.update w i ((w i).take r))
    (fun j => if j = i then (r : ℤ) - 1 else 0)

/-- Clear's exact phase invariant. **Proof sketch.** During the scan the
word is intact. The turn reads its right blank. Each return transition erases
just the last remaining cell; the final left blank makes the right-entry. -/
private lemma catalog_clear_trace (i : Fin k) (w : Fin k → List Bool) (t : ℕ) :
    (clearTM k i).runFrom (Cfg.ofWords (input := x) .sweep w) t =
      catalogTrace (catalogClearF i w) (catalogClearR i w)
        (Cfg.ofWords .done (Function.update w i [])) (w i).length t := by
  have h0 : catalogClearF (x := x) i w 0 = Cfg.ofWords .sweep w := by
    apply Cfg.ext <;> simp [catalogClearF, catalogCfg, Cfg.ofWords]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    have hs : (catalogClearF (x := x) i w r).workTapeSymbols i = some (w i)[r] := by
      simp [catalogClearF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        FinTM.bufferTape_nat, List.getElem?_eq_getElem hr]
    change ((clearTM k i).tr .sweep _ _).apply _ = _
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · have hs : (catalogClearF (x := x) i w (w i).length).workTapeSymbols i = none := by
      simp [catalogClearF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
    change ((clearTM k i).tr .sweep _ _).apply _ = _
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hj : j = i <;> simp [hj]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogClearR (x := x) i w (r + 1)).workTapeSymbols i =
        some (w i)[r] := by
      simp [catalogClearR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        show (r + 1 : ℕ) - (1 : ℤ) = (r : ℤ) by omega,
        List.getElem?_take, List.getElem?_eq_getElem hr]
    change ((clearTM k i).tr .rewind _ _).apply _ = _
    simp only [clearTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hj : j = i
      · subst j
        simpa [show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using
          catalog_erase_take (w i) r hr
      · simp [hj]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, clearTM, catalogClearR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, clearTM, Cfg.ofWords, Action.apply]

/-- Copy and transfer share the forward phase: the destination holds the copied
prefix and the source remains intact, with both heads at its end. -/
private def catalogCopyF (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .sweep (Function.update w dst ((w src).take r))
    (fun j => if j = src ∨ j = dst then (r : ℤ) else 0)

/-- During copy's return the words are complete and unchanged. -/
private def catalogCopyR (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .rewind (Function.update w dst (w src))
    (fun j => if j = src ∨ j = dst then (r : ℤ) - 1 else 0)

/-- During transfer's return the source retains exactly the unerased prefix. -/
private def catalogTransferR (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool SweepPhase x :=
  catalogCfg .rewind (Function.update (Function.update w src ((w src).take r)) dst (w src))
    (fun j => if j = src ∨ j = dst then (r : ℤ) - 1 else 0)

/-- The common forward transition copies exactly the next source bit. -/
private lemma catalog_copy_forward (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (r : ℕ) (hr : r < (w src).length) :
    (copyTM k src dst).step (catalogCopyF (x := x) src dst w r) =
      catalogCopyF src dst w (r + 1) := by
  have hs : (catalogCopyF (x := x) src dst w r).workTapeSymbols src =
      some (w src)[r] := by
    simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
      List.getElem?_eq_getElem hr]
  change ((copyTM k src dst).tr .sweep _ _).apply _ = _
  simp only [copyTM, hs]
  apply Cfg.ext <;> simp [Action.apply, catalogCopyF, catalogCfg, Cfg.ofWords]
  · funext j
    by_cases hj : j = dst
    · subst j
      simpa using catalog_write_take (w src) r hr
    · by_cases hs : j = src <;> simp [hj, hs, hne, Ne.symm hne]
  · funext j
    by_cases hd : j = dst <;> by_cases hs : j = src <;>
      simp [hd, hs, hne, SignType.cast] <;> omega

/-- Copy's exact phase invariant, including the stationary exit. -/
private lemma catalog_copy_trace (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (copyTM k src dst).runFrom (Cfg.ofWords (input := x) .sweep w) t =
      catalogTrace (catalogCopyF src dst w) (catalogCopyR src dst w)
        (Cfg.ofWords .done (Function.update w dst (w src))) (w src).length t := by
  have h0 : catalogCopyF (x := x) src dst w 0 = Cfg.ofWords .sweep w := by
    apply Cfg.ext <;> simp [catalogCopyF, catalogCfg, Cfg.ofWords]
    funext j
    by_cases hj : j = dst
    · subst j; simp [hdst]
    · simp [hj]
  rw [← h0]
  apply catalog_trace_run
  · exact catalog_copy_forward src dst hne w
  · have hs : (catalogCopyF (x := x) src dst w (w src).length).workTapeSymbols src =
        none := by
      simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne]
    change ((copyTM k src dst).tr .sweep _ _).apply _ = _
    simp only [copyTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogCopyR (x := x) src dst w (r + 1)).workTapeSymbols src =
        some (w src)[r] := by
      simp [catalogCopyR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
        List.getElem?_eq_getElem hr]
    change ((copyTM k src dst).tr .rewind _ _).apply _ = _
    simp only [copyTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogCopyR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, copyTM, catalogCopyR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, hne, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, copyTM, Cfg.ofWords, Action.apply]

/-- Transfer's exact phase invariant. The forward transitions are copy's;
on return, erasure is behind the head, leaving every cell still to read intact. -/
private lemma catalog_transfer_trace (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (transferTM k src dst).runFrom (Cfg.ofWords (input := x) .sweep w) t =
      catalogTrace (catalogCopyF src dst w) (catalogTransferR src dst w)
        (Cfg.ofWords .done (Function.update (Function.update w src []) dst (w src)))
        (w src).length t := by
  have h0 : catalogCopyF (x := x) src dst w 0 = Cfg.ofWords .sweep w := by
    apply Cfg.ext <;> simp [catalogCopyF, catalogCfg, Cfg.ofWords]
    funext j
    by_cases hj : j = dst
    · subst j; simp [hdst]
    · simp [hj]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    exact catalog_copy_forward src dst hne w r hr
  · have hs : (catalogCopyF (x := x) src dst w (w src).length).workTapeSymbols src =
        none := by
      simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne]
    change ((transferTM k src dst).tr .sweep _ _).apply _ = _
    simp only [transferTM, hs]
    apply Cfg.ext <;>
      simp [Action.apply, catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hd : j = dst <;> by_cases hs : j = src <;> simp [hd, hs]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogTransferR (x := x) src dst w (r + 1)).workTapeSymbols src =
        some (w src)[r] := by
      simp [catalogTransferR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
        List.getElem?_take, List.getElem?_eq_getElem hr]
    change ((transferTM k src dst).tr .rewind _ _).apply _ = _
    simp only [transferTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogTransferR, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hs : j = src
      · subst j
        simpa [hne, show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using
          catalog_erase_take (w src) r hr
      · by_cases hd : j = dst
        · subst j; simp [hne, Ne.symm hne]
        · simp [hs, hd]
    · funext j
      by_cases hs : j = src <;> by_cases hd : j = dst <;>
        simp [hs, hd, hne, Ne.symm hne, SignType.cast] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, transferTM, catalogTransferR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, hne, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, transferTM, Cfg.ofWords, Action.apply]

/-- The first unequal or terminating cells occur after a common nonblank
prefix, and equality at those terminating cells is precisely word equality.
**Proof sketch.** Remove equal leading bits recursively; unequal bits or either
empty list stop immediately. This also covers aliased physical tape indices. -/
private lemma catalog_compare_stop (u v : List Bool) :
    ∃ d ≤ min u.length v.length,
      (∀ r < d, ∃ b, u[r]? = some b ∧ v[r]? = some b) ∧
      (¬∃ b, u[d]? = some b ∧ v[d]? = some b) ∧
      (u[d]? = v[d]? ↔ u = v) := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact ⟨0, by simp, by simp, by simp, by simp⟩
    | cons b v => exact ⟨0, by simp, by simp, by simp, by simp⟩
  | cons a u ih =>
    cases v with
    | nil => exact ⟨0, by simp, by simp, by simp, by simp⟩
    | cons b v =>
      by_cases hab : a = b
      · subst b
        obtain ⟨d, hd, hp, hs, he⟩ := ih v
        refine ⟨d + 1, by simpa using hd, ?_, ?_, ?_⟩
        · intro r hr
          cases r with
          | zero => exact ⟨a, rfl, rfl⟩
          | succ r => simpa using hp r (by omega)
        · simpa using hs
        · simpa using he
      · refine ⟨0, by simp, by simp, ?_, ?_⟩
        · simpa [eq_comm] using hab
        · simp [hab]

/-- Comparison's forward configuration retains every word and advances the
selected physical heads once each, including when the two indices coincide. -/
private def catalogCompareF (fst snd : Fin k) (w : Fin k → List Bool) (r : ℕ) :
    Cfg k Bool FlagPhase x :=
  catalogCfg .run w (fun j => if j = fst ∨ j = snd then (r : ℤ) else 0)

/-- Comparison's return configuration carries the verdict without changing words. -/
private def catalogCompareR (fst snd : Fin k) (w : Fin k → List Bool)
    (v : Bool) (r : ℕ) : Cfg k Bool FlagPhase x :=
  catalogCfg (.rewind v) w
    (fun j => if j = fst ∨ j = snd then (r : ℤ) - 1 else 0)

/-- Comparison's exact configuration invariant, at a first differing or blank
position. **Proof sketch.** The common-prefix condition supplies every forward
read and every first-tape return read. The stopping condition determines the
turn and verdict. The heads then return from `d-1` through `-1` to zero. -/
private lemma catalog_compare_trace (fst snd : Fin k) (w : Fin k → List Bool)
    (d : ℕ) (hd : d ≤ min (w fst).length (w snd).length)
    (hp : ∀ r < d, ∃ b, (w fst)[r]? = some b ∧ (w snd)[r]? = some b)
    (hs : ¬∃ b, (w fst)[d]? = some b ∧ (w snd)[d]? = some b)
    (he : ((w fst)[d]? = (w snd)[d]?) ↔ w fst = w snd) (t : ℕ) :
    (compareTM k fst snd).runFrom (Cfg.ofWords (input := x) .run w) t =
      catalogTrace (catalogCompareF fst snd w)
        (catalogCompareR fst snd w (decide (w fst = w snd)))
        (Cfg.ofWords (.done (decide (w fst = w snd))) w) d t := by
  have h0 : catalogCompareF (x := x) fst snd w 0 = Cfg.ofWords .run w := by
    apply Cfg.ext <;> simp [catalogCompareF, catalogCfg, Cfg.ofWords]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    obtain ⟨b, hf, hg⟩ := hp r hr
    have hsf : (catalogCompareF (x := x) fst snd w r).workTapeSymbols fst = some b := by
      simpa [catalogCompareF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols] using hf
    have hsg : (catalogCompareF (x := x) fst snd w r).workTapeSymbols snd = some b := by
      simpa [catalogCompareF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols] using hg
    change ((compareTM k fst snd).tr .run _ _).apply _ = _
    simp only [compareTM, hsf, hsg, ↓reduceIte]
    apply Cfg.ext <;> simp [Action.apply, catalogCompareF, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · have hread : (catalogCompareF (x := x) fst snd w d).workTapeSymbols =
        fun j => FinTM.bufferTape (w j) (if j = fst ∨ j = snd then (d : ℤ) else 0) := rfl
    have ht : (compareTM k fst snd).tr .run
        (catalogCompareF (x := x) fst snd w d).inputSymbol
        (catalogCompareF (x := x) fst snd w d).workTapeSymbols =
        ⟨0, (fun j => if j = fst ∨ j = snd then (none, SignType.neg) else (none, 0)),
          none, some (.rewind (decide (w fst = w snd)))⟩ := by
      simp only [compareTM, hread, if_pos (Or.inl rfl : fst = fst ∨ fst = snd),
        if_pos (Or.inr rfl : snd = fst ∨ snd = snd), FinTM.bufferTape_nat]
      cases hf : (w fst)[d]? with
      | none =>
        cases hg : (w snd)[d]? with
        | none =>
          have heq : w fst = w snd := he.mp (by rw [hf, hg])
          simp [hf, hg, heq]
        | some b =>
          have hneq : w fst ≠ w snd := by
            intro h
            have h' := he.mpr h
            simp only [hf, hg, reduceCtorEq] at h'
          simp [hf, hg, hneq]
      | some a =>
        cases hg : (w snd)[d]? with
        | none =>
          have hneq : w fst ≠ w snd := by
            intro h
            have h' := he.mpr h
            simp only [hf, hg, reduceCtorEq] at h'
          simp [hf, hg, hneq]
        | some b =>
          have hab : a ≠ b := by
            intro h
            subst b
            exact hs ⟨a, hf, hg⟩
          have hneq : w fst ≠ w snd := by
            intro h
            have h' := he.mpr h
            exact hab (by simpa only [hf, hg, Option.some.injEq] using h')
          simp [hf, hg, hab, hneq]
    change ((compareTM k fst snd).tr .run _ _).apply _ = _
    rw [ht]
    apply Cfg.ext <;> simp [Action.apply, catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    obtain ⟨b, hf, _⟩ := hp r hr
    have hread : (catalogCompareR (x := x) fst snd w (decide (w fst = w snd))
        (r + 1)).workTapeSymbols fst = some b := by
      simpa [catalogCompareR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using hf
    change ((compareTM k fst snd).tr (.rewind _) _ _).apply _ = _
    simp only [compareTM, hread]
    apply Cfg.ext <;> simp [Action.apply, catalogCompareR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, compareTM, catalogCompareR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, compareTM, Cfg.ofWords, Action.apply]

/-- A word consists of its leading true bits followed by either a first false
bit and its tail, or no remaining bits. -/
private lemma catalog_increment_split (w : List Bool) :
    ∃ p : ℕ, ∃ tail : Option (List Bool),
      w = List.replicate p true ++ tail.elim [] (false :: ·) := by
  induction w with
  | nil => exact ⟨0, none, rfl⟩
  | cons b w ih =>
    cases b with
    | false => exact ⟨0, some w, rfl⟩
    | true =>
      obtain ⟨p, tail, hw⟩ := ih
      exact ⟨p + 1, tail, by simp [List.replicate_succ, hw]⟩

/-- Fixed-width increment flips the leading true prefix and the first false;
an absent first false gives overflow. -/
private lemma catalog_increment_value (p : ℕ) (tail : Option (List Bool)) :
    incFixed (List.replicate p true ++ tail.elim [] (false :: ·)) =
      tail.map (fun v => List.replicate p false ++ true :: v) := by
  induction p with
  | zero => cases tail <;> rfl
  | succ p ih =>
    simp only [List.replicate_succ, List.cons_append, incFixed, ih]
    cases tail <;> rfl

/-- Changing the cell immediately after a prefix changes exactly that bit.
**Proof sketch.** At the selected cell use list indexing at the prefix length;
elsewhere, the suffix and prefix lookups are unchanged. -/
private lemma catalog_write_middle (pre rest : List Bool) (a b : Bool) :
    Function.update (FinTM.bufferTape (pre ++ a :: rest)) (pre.length : ℤ) (some b) =
      FinTM.bufferTape (pre ++ b :: rest) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [FinTM.bufferTape]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · simp only [FinTM.bufferTape, if_pos h0, List.getElem?_append]
      by_cases hlt : z.toNat < pre.length
      · simp [hlt]
      · have he : z.toNat - pre.length = (z.toNat - pre.length - 1) + 1 := by omega
        simp only [if_neg hlt]
        rw [he]
        rfl
    · simp [FinTM.bufferTape, h0]

/-- Increment's carry configuration: the first `r` bits have been reset, the
remaining true prefix and stopping suffix are intact, and the head is at `r`. -/
private def catalogIncF (i : Fin k) (w : Fin k → List Bool) (p : ℕ)
    (tail : Option (List Bool)) (r : ℕ) : Cfg k Bool FlagPhase x :=
  catalogCfg .run (Function.update w i
    (List.replicate r false ++ List.replicate (p - r) true ++ tail.elim [] (false :: ·)))
    (fun j => if j = i then (r : ℤ) else 0)

/-- Increment's return configuration holds the complete updated or wrapped
word and carries the success bit, with the head immediately before cell `r`. -/
private def catalogIncR (i : Fin k) (w : Fin k → List Bool) (p : ℕ)
    (tail : Option (List Bool)) (r : ℕ) : Cfg k Bool FlagPhase x :=
  catalogCfg (.rewind tail.isSome)
    (Function.update w i (List.replicate p false ++ tail.elim [] (true :: ·)))
    (fun j => if j = i then (r : ℤ) - 1 else 0)

/-- Increment's exact phase invariant. **Proof sketch.** Each carry step resets
one true bit; the first false is changed on the left-turn itself, so cell `p+1`
is not visited. With no false, the right blank turns without writing. Both cases
return over the reset prefix and enter the live exit after exactly `2p+2` steps. -/
private lemma catalog_increment_trace (i : Fin k) (w : Fin k → List Bool)
    (p : ℕ) (tail : Option (List Bool))
    (hw : w i = List.replicate p true ++ tail.elim [] (false :: ·)) (t : ℕ) :
    (incrementTM k i).runFrom (Cfg.ofWords (input := x) .run w) t =
      catalogTrace (catalogIncF i w p tail) (catalogIncR i w p tail)
        (Cfg.ofWords (.done tail.isSome)
          (Function.update w i (List.replicate p false ++ tail.elim [] (true :: ·)))) p t := by
  have h0 : catalogIncF (x := x) i w p tail 0 = Cfg.ofWords .run w := by
    apply Cfg.ext <;> simp [catalogIncF, catalogCfg, Cfg.ofWords, ← hw]
  rw [← h0]
  apply catalog_trace_run
  · intro r hr
    have hpr : p - r = (p - (r + 1)) + 1 := by omega
    have hs : (catalogIncF (x := x) i w p tail r).workTapeSymbols i = some true := by
      simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        hpr, List.replicate_succ, List.append_assoc]
    change ((incrementTM k i).tr .run _ _).apply _ = _
    simp only [incrementTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogCfg, Cfg.ofWords]
    · funext j
      by_cases hj : j = i
      · subst j
        have hh := catalog_write_middle (List.replicate r false)
          (List.replicate (p - (r + 1)) true ++ tail.elim [] (false :: ·)) true false
        simp only [ite_true, Function.update_self]
        rw [hpr, List.replicate_succ, List.cons_append]
        simpa only [List.length_replicate, List.replicate_succ',
          List.append_assoc, List.singleton_append] using hh
      · simp [hj]
    · funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · cases tail with
    | none =>
      have hs : (catalogIncF (x := x) i w p none p).workTapeSymbols i = none := by
        simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
      change ((incrementTM k i).tr .run _ _).apply _ = _
      simp only [incrementTM, hs]
      apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      all_goals
        funext j
        split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
    | some v =>
      have hs : (catalogIncF (x := x) i w p (some v) p).workTapeSymbols i = some false := by
        simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
      change ((incrementTM k i).tr .run _ _).apply _ = _
      simp only [incrementTM, hs]
      apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      · funext j
        by_cases hj : j = i
        · subst j
          simpa using catalog_write_middle (List.replicate p false) v false true
        · simp [hj]
      · funext j
        split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
  · intro r hr
    have hs : (catalogIncR (x := x) i w p tail (r + 1)).workTapeSymbols i = some false := by
      simp [catalogIncR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
        List.getElem?_append, hr]
    change ((incrementTM k i).tr (.rewind _) _ _).apply _ = _
    simp only [incrementTM, hs]
    apply Cfg.ext <;> simp [Action.apply, catalogIncR, catalogCfg, Cfg.ofWords]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, incrementTM, catalogIncR, catalogCfg, Cfg.ofWords,
        Cfg.workTapeSymbols, Action.apply]
    all_goals
      funext j
      split_ifs <;> simp_all [SignType.cast]
  · apply Cfg.ext <;>
      simp [MultiTapeTM.step, incrementTM, Cfg.ofWords, Action.apply]

/-- **Transfer, the run contract** (spec, fill pending — design §12 R3;
[Bon26]). From the seam with word `w src` on the source and a blank
destination, the routine reaches — within `3|w src| + 3` steps and
without visiting the exit anchor earlier — the seam whose source is blank
and whose destination holds the word, everything else untouched.

**Proof sketch.** Two phase invariants. *Sweep*, time `p ≤ |w|`: heads of
`src`/`dst` at `p`, `dst` holding the copied prefix, `src` intact; the
turn at the right blank enters *rewind*. *Rewind*, positions `|w| - 1`
down to `-1`: `src` erased above the head, `dst` complete; the left-blank
overshoot steps right into `done` at the origin at time `2|w| + 2`
(` ≤ 3|w| + 3`). The cut holds because `done` only appears after the
overshoot. -/
theorem transferTM_run (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) :
    ∃ T ≤ 3 * (w src).length + 3,
      (∀ t < T, ((transferTM k src dst).runFrom
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t).state
          ≠ some SweepPhase.done) ∧
      (transferTM k src dst).runFrom
          (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
        Cfg.ofWords SweepPhase.done
          (Function.update (Function.update w src []) dst (w src)) := by
  refine ⟨2 * (w src).length + 2, by omega, ?_, ?_⟩
  · intro t ht
    rw [catalog_transfer_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_transfer_trace src dst hne w hdst]
    simp [catalogTrace, show ¬2 * (w src).length + 2 ≤ (w src).length by omega]

/-- **Transfer, per-tape space** (spec, fill pending — design §12 R3).
The two touched tapes visit at most the word interval plus the two
boundary blanks — `|w src| + 2` cells, from the `-1` overshoot to the
right blank at `|w src|` — and every other tape never leaves its origin.

**Proof sketch.** Head-movement count of the phases: both touched heads
walk `0 → |w src| → -1 → 0` in unit steps, so their trajectories lie in
`[-1, |w src|]` (`Finset.Icc`, cardinality `|w src| + 2`); all other
action components are `(none, 0)`, so those trajectories are constant and
the visited set is the origin singleton. -/
theorem transferTM_spaceUsedByTape (k : ℕ) (src dst : Fin k)
    (hne : src ≠ dst) (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (transferTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t src
      ≤ (w src).length + 2 ∧
    (transferTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t dst
      ≤ (w src).length + 2 ∧
    ∀ j : Fin k, j ≠ src → j ≠ dst →
      (transferTM k src dst).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  have hb (j : Fin k) : (transferTM k src dst).spaceUsedByTape
      (Cfg.ofWords (input := x) .sweep w) t j ≤ (w src).length + 2 := by
    apply catalog_space_bound
    intro u
    rw [catalog_transfer_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨hb src, hb dst, ?_⟩
  intro j hs hd
  apply catalog_space_one
  intro u
  rw [catalog_transfer_trace src dst hne w hdst]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords, hs, hd]

/-- **Copy, the run contract** (spec, fill pending — design §12 R3;
[Bon26]; the A3 `3|w| + 3` row). From the seam with word `w src` on the
source and a blank destination, the routine reaches — within
`3|w src| + 3` steps and without visiting the exit anchor earlier — the
seam where both tapes hold the word.

**Proof sketch.** As `transferTM_run` without the erasure clause: sweep
copies the prefix in lockstep, rewind returns both heads guided by the
intact source, the overshoot enters `done` at time `2|w| + 2`. -/
theorem copyTM_run (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) :
    ∃ T ≤ 3 * (w src).length + 3,
      (∀ t < T, ((copyTM k src dst).runFrom
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t).state
          ≠ some SweepPhase.done) ∧
      (copyTM k src dst).runFrom
          (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
        Cfg.ofWords SweepPhase.done (Function.update w dst (w src)) := by
  refine ⟨2 * (w src).length + 2, by omega, ?_, ?_⟩
  · intro t ht
    rw [catalog_copy_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_copy_trace src dst hne w hdst]
    simp [catalogTrace, show ¬2 * (w src).length + 2 ≤ (w src).length by omega]

/-- **Copy, per-tape space** (spec, fill pending — design §12 R3). As the
transfer routine: the two touched tapes visit at most `|w src| + 2` cells
(the word interval plus both boundary blanks), every other tape exactly
its origin singleton.

**Proof sketch.** Identical head-movement count to
`transferTM_spaceUsedByTape`: both touched heads walk
`0 → |w src| → -1 → 0`; all other tapes receive `(none, 0)` throughout. -/
theorem copyTM_spaceUsedByTape (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
    (copyTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t src
      ≤ (w src).length + 2 ∧
    (copyTM k src dst).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t dst
      ≤ (w src).length + 2 ∧
    ∀ j : Fin k, j ≠ src → j ≠ dst →
      (copyTM k src dst).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  have hb (j : Fin k) : (copyTM k src dst).spaceUsedByTape
      (Cfg.ofWords (input := x) .sweep w) t j ≤ (w src).length + 2 := by
    apply catalog_space_bound
    intro u
    rw [catalog_copy_trace src dst hne w hdst]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨hb src, hb dst, ?_⟩
  intro j hs hd
  apply catalog_space_one
  intro u
  rw [catalog_copy_trace src dst hne w hdst]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords, hs, hd]

/-- **Clear, the run contract** (spec, fill pending — design §12 R3;
[Bon26]; the A3 `2|w| + 2` row, P12's engine). From the seam with word
`w i` on tape `i`, the routine reaches — within `2|w i| + 2` steps and
without visiting the exit anchor earlier — the seam with tape `i` blank,
everything else untouched.

**Proof sketch.** Sweep walks right over the intact word to the right
blank (`|w i| + 1` steps including the turn), rewind erases on the way
back and overshoots to `-1`, the final step enters `done` at the origin:
exactly `2|w i| + 2` steps, matching the stated budget on the nose. -/
theorem clearTM_run (k : ℕ) (i : Fin k) (w : Fin k → List Bool) :
    ∃ T ≤ 2 * (w i).length + 2,
      (∀ t < T, ((clearTM k i).runFrom
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t).state
          ≠ some SweepPhase.done) ∧
      (clearTM k i).runFrom
          (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
        Cfg.ofWords SweepPhase.done (Function.update w i []) := by
  refine ⟨2 * (w i).length + 2, le_rfl, ?_, ?_⟩
  · intro t ht
    rw [catalog_clear_trace]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_clear_trace]
    simp [catalogTrace, show ¬2 * (w i).length + 2 ≤ (w i).length by omega]

/-- **Clear, per-tape space** (spec, fill pending — design §12 R3). Tape
`i` visits at most `|w i| + 2` cells (the word interval plus both
boundary blanks); every other tape exactly its origin singleton.

**Proof sketch.** The single touched head walks `0 → |w i| → -1 → 0` in
unit steps, so its trajectory lies in `[-1, |w i|]`; every other tape's
action is `(none, 0)` in every phase. -/
theorem clearTM_spaceUsedByTape (k : ℕ) (i : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (clearTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) SweepPhase.sweep w) t i
      ≤ (w i).length + 2 ∧
    ∀ j : Fin k, j ≠ i →
      (clearTM k i).spaceUsedByTape
          (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
  constructor
  · apply catalog_space_bound
    intro u
    rw [catalog_clear_trace]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords] <;> omega
  · intro j hj
    apply catalog_space_one
    intro u
    rw [catalog_clear_trace]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords, hj]

/-- **Compare, the run contract** (spec, fill pending — design §12 R3;
[Bon26]). From the seam, the routine reaches — within
`2·min(|w fst|, |w snd|) + 2` steps and without visiting either exit
anchor earlier — the seam carrying the equality verdict
`decide (w fst = w snd)` in its anchor, with every tape (the compared two
included) byte-identical to the entry.

**Proof sketch.** The lockstep scan maintains "prefixes below the heads
agree"; it ends at the first disagreeing position or the double blank,
at depth at most `min + 1`. List equality is exactly "no disagreement
and simultaneous blank". The return pass is guided by `fst`'s intact
content — sound because the scan depth never exceeds `|w fst| + 1`, so
the first blank met moving left is the `-1` overshoot. Both passes have
the same length, giving `2·min + 2` worst case. -/
theorem compareTM_run (k : ℕ) (fst snd : Fin k) (w : Fin k → List Bool) :
    ∃ T ≤ 2 * min (w fst).length (w snd).length + 2,
      (∀ t < T, ∀ v : Bool, ((compareTM k fst snd).runFrom
        (Cfg.ofWords (input := x) FlagPhase.run w) t).state
          ≠ some (FlagPhase.done v)) ∧
      (compareTM k fst snd).runFrom
          (Cfg.ofWords (input := x) FlagPhase.run w) T =
        Cfg.ofWords (FlagPhase.done (decide (w fst = w snd))) w := by
  obtain ⟨d, hd, hp, hs, he⟩ := catalog_compare_stop (w fst) (w snd)
  refine ⟨2 * d + 2, by omega, ?_, ?_⟩
  · intro t ht v
    rw [catalog_compare_trace fst snd w d hd hp hs he]
    simp only [catalogTrace]
    split_ifs <;> simp_all [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords]
    omega
  · rw [catalog_compare_trace fst snd w d hd hp hs he]
    simp [catalogTrace, show ¬2 * d + 2 ≤ d by omega]

/-- **Compare, per-tape space** (spec, fill pending — design §12 R3). The
two compared tapes visit at most `min(|w fst|, |w snd|) + 2` cells (the
scanned interval plus both boundary cells); every other tape exactly its
origin singleton.

**Proof sketch.** Exact position counting, uniformly over mismatches,
equal words, and unequal lengths (round-1 finding 6 — the earlier
`[-1, min + 1]` interval argument did not cover equal inputs): with `d`
the first differing position or the first position where a word ends
(`d ≤ min`), the scan turns at `d`, the return pass overshoots to `-1`,
and both touched trajectories are exactly the integers of `[-1, d]` —
`d + 2 ≤ min + 2` visited cells in every case, aliased indices included;
untouched tapes receive `(none, 0)` throughout. -/
theorem compareTM_spaceUsedByTape (k : ℕ) (fst snd : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (compareTM k fst snd).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t fst
      ≤ min (w fst).length (w snd).length + 2 ∧
    (compareTM k fst snd).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t snd
      ≤ min (w fst).length (w snd).length + 2 ∧
    ∀ j : Fin k, j ≠ fst → j ≠ snd →
      (compareTM k fst snd).spaceUsedByTape
          (Cfg.ofWords (input := x) FlagPhase.run w) t j = 1 := by
  obtain ⟨d, hd, hp, hs, he⟩ := catalog_compare_stop (w fst) (w snd)
  have hb (j : Fin k) : (compareTM k fst snd).spaceUsedByTape
      (Cfg.ofWords (input := x) .run w) t j ≤ d + 2 := by
    apply catalog_space_bound
    intro u
    rw [catalog_compare_trace fst snd w d hd hp hs he]
    simp only [catalogTrace]
    split_ifs <;> simp only [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords] <;>
      (try split_ifs) <;> omega
  refine ⟨(hb fst).trans (by omega), (hb snd).trans (by omega), ?_⟩
  intro j hf hg
  apply catalog_space_one
  intro u
  rw [catalog_compare_trace fst snd w d hd hp hs he]
  simp only [catalogTrace]
  split_ifs <;> simp [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords, hf, hg]

/-- **Increment, the success contract** (spec, fill pending — design §12
R3). If the word on tape `i` has a successor at its width
(`Turing.incFixed (w i) = some v`), the routine reaches — within
`2|w i| + 2` steps and without visiting either exit anchor earlier — the
seam carrying the success verdict and the incremented word `v` in place.

**Proof sketch.** The carry pass flips the maximal `true`-prefix to
`false` and the first `false` to `true`, which is exactly
`Turing.incFixed`'s recursion. With `p` the first `false` position, the
machine takes `p` carry steps, one left-turn/write step, `p` rewind
steps, and one right-entry step — **exactly `2p + 2 ≤ 2|w i|` steps**,
visited interval `[-1, p]`; it never visits `p + 1` on success, and
`[false]` returns in two steps (round-1 finding 7 corrected the earlier
mixed count). The looser public `2|w i| + 2` is deliberate slack. -/
theorem incrementTM_run_succ (k : ℕ) (i : Fin k) (w : Fin k → List Bool)
    (v : List Bool) (hv : incFixed (w i) = some v) :
    ∃ T ≤ 2 * (w i).length + 2,
      (∀ t < T, ∀ b : Bool, ((incrementTM k i).runFrom
        (Cfg.ofWords (input := x) FlagPhase.run w) t).state
          ≠ some (FlagPhase.done b)) ∧
      (incrementTM k i).runFrom
          (Cfg.ofWords (input := x) FlagPhase.run w) T =
        Cfg.ofWords (FlagPhase.done true) (Function.update w i v) := by
  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
  rw [hw, catalog_increment_value] at hv
  cases tail with
  | none => simp at hv
  | some tail =>
    have hv' : v = List.replicate p false ++ true :: tail := by simpa using hv.symm
    have hp : p < (w i).length := by simp [hw]
    refine ⟨2 * p + 2, by omega, ?_, ?_⟩
    · intro t ht b
      rw [catalog_increment_trace i w p (some tail) hw]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      omega
    · rw [catalog_increment_trace i w p (some tail) hw]
      simp [catalogTrace, show ¬2 * p + 2 ≤ p by omega, hv']

/-- **Increment, the overflow contract** (spec, fill pending — design §12
R3). If the word on tape `i` is all `true` (`Turing.incFixed (w i) =
none`), the routine reaches — within `2|w i| + 2` steps and without
visiting either exit anchor earlier — the seam carrying the overflow
verdict and the wrapped all-`false` word, the enumerator's counter
convention.

**Proof sketch.** The carry pass flips every cell and falls off the width
at the right blank (`|w i| + 1` steps), the return pass over the written
`false` word overshoots to `-1` and enters `done false` at the origin:
exactly `2|w i| + 2` steps. -/
theorem incrementTM_run_overflow (k : ℕ) (i : Fin k)
    (w : Fin k → List Bool) (hv : incFixed (w i) = none) :
    ∃ T ≤ 2 * (w i).length + 2,
      (∀ t < T, ∀ b : Bool, ((incrementTM k i).runFrom
        (Cfg.ofWords (input := x) FlagPhase.run w) t).state
          ≠ some (FlagPhase.done b)) ∧
      (incrementTM k i).runFrom
          (Cfg.ofWords (input := x) FlagPhase.run w) T =
        Cfg.ofWords (FlagPhase.done false)
          (Function.update w i (List.replicate (w i).length false)) := by
  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
  rw [hw, catalog_increment_value] at hv
  cases tail with
  | some tail => simp at hv
  | none =>
    have hp : (w i).length = p := by simp [hw]
    refine ⟨2 * p + 2, by omega, ?_, ?_⟩
    · intro t ht b
      rw [catalog_increment_trace i w p none hw]
      simp only [catalogTrace]
      split_ifs <;> simp_all [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
      omega
    · rw [catalog_increment_trace i w p none hw]
      simp [catalogTrace, show ¬2 * p + 2 ≤ p by omega, hp]

/-- **Increment, per-tape space** (spec, fill pending — design §12 R3).
Tape `i` visits at most `|w i| + 2` cells; every other tape exactly its
origin singleton.

**Proof sketch.** The carry head walks right to at most the right blank
at `|w i|`, back to the `-1` overshoot, and home: trajectory inside
`[-1, |w i|]`; other tapes receive `(none, 0)` in every phase. -/
theorem incrementTM_spaceUsedByTape (k : ℕ) (i : Fin k)
    (w : Fin k → List Bool) (t : ℕ) :
    (incrementTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) FlagPhase.run w) t i
      ≤ (w i).length + 2 ∧
    ∀ j : Fin k, j ≠ i →
      (incrementTM k i).spaceUsedByTape
          (Cfg.ofWords (input := x) FlagPhase.run w) t j = 1 := by
  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
  have hp : p ≤ (w i).length := by simp [hw]
  constructor
  · have hb : (incrementTM k i).spaceUsedByTape
        (Cfg.ofWords (input := x) .run w) t i ≤ p + 2 := by
      apply catalog_space_bound
      intro u
      rw [catalog_increment_trace i w p tail hw]
      simp only [catalogTrace]
      split_ifs <;> simp [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords] <;> omega
    omega
  · intro j hj
    apply catalog_space_one
    intro u
    rw [catalog_increment_trace i w p tail hw]
    simp only [catalogTrace]
    split_ifs <;> simp [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords, hj]

/-- **W1 space row** (spec, fill pending — design §12 R3, decision 12.3).
Under the hypotheses of `Turing.capture_run`, the host's source-bank
tapes visit exactly the source's cells — per-tape, on the nose — and the
capture tape's space usage is bounded by the output recorded in the
window plus one.

**Proof sketch.** `Turing.capture_run` makes the host trajectory on tape
`i.castSucc` pointwise equal to the source's on tape `i`, so the visited
images and their cardinalities agree. The capture head sits at
`|pre ++ output-so-far|`, which is nondecreasing (one cell per recorded
emission, `Turing.MultiTapeTM.output_prefix`), so its visited set is an
integer interval of length the output growth plus one. -/
theorem capture_visitedByTapeHead {k : ℕ} {S H : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → H) (ret : H)
    (hagree : ∀ (s : S) (inp : Option Bool) (w : Fin (k + 1) → Option Bool),
      host.tr (emb s) inp w =
        captureAction emb ret (tm.tr s inp fun i => w i.castSucc))
    (pre out₀ : List Bool) (c₀ : Cfg k Bool S x) (t : ℕ)
    (hlive : ∀ t' < t, ¬(tm.runFrom c₀ t').Halted) :
    (∀ i : Fin k,
      host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t i.castSucc
        = tm.visitedByTapeHead c₀ t i ∧
      host.spaceUsedByTape (captureCfg emb ret pre out₀ c₀) t i.castSucc
        = tm.spaceUsedByTape c₀ t i) ∧
    host.spaceUsedByTape (captureCfg emb ret pre out₀ c₀) t (Fin.last k)
      ≤ (tm.runFrom c₀ t).output.length - c₀.output.length + 1 := by
  have hr (u : ℕ) (hu : u ≤ t) :=
    capture_run tm host emb ret hagree pre out₀ c₀ u
      (fun v hv => hlive v (by omega))
  constructor
  · intro i
    have he : host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t i.castSucc =
        tm.visitedByTapeHead c₀ t i := by
      unfold MultiTapeTM.visitedByTapeHead
      apply Finset.image_congr
      intro u hu
      dsimp only
      rw [hr u (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hu))]
      simp [captureCfg, i.isLt]
    exact ⟨he, congrArg Finset.card he⟩
  · have hmono {u v : ℕ} (huv : u ≤ v) :
        (tm.runFrom c₀ u).output.length ≤ (tm.runFrom c₀ v).output.length :=
      (tm.output_prefix c₀ huv).length_le
    have hbound : c₀.output.length ≤ (tm.runFrom c₀ t).output.length :=
      hmono (Nat.zero_le t)
    have hsub : host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t (Fin.last k) ⊆
        Finset.Icc ((pre.length + c₀.output.length : ℕ) : ℤ)
          ((pre.length + (tm.runFrom c₀ t).output.length : ℕ) : ℤ) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      have hut : u ≤ t := by have := Finset.mem_range.mp hu; omega
      rw [hr u hut]
      simp only [captureCfg, Fin.val_last, lt_self_iff_false, ↓reduceDIte,
        List.length_append, Finset.mem_Icc]
      have hlo := hmono (Nat.zero_le u)
      have hhi := hmono hut
      simp only [MultiTapeTM.runFrom_zero] at hlo
      constructor <;> omega
    exact (Finset.card_le_card hsub).trans (by
      rw [Int.card_Icc]
      omega)

end Turing

namespace Turing.FinTM

/- F2 local witness copies from Composition.lean and Build/Primitives.lean.
Their transition tables and time proofs are unchanged except for the f2_ prefix;
local copies keep the frozen source modules and their private interfaces intact. -/

/-- The one-state copy machine: emits each input bit moving right, and halts on the
boundary blank. -/
private def f2_idTM : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ =>
        match inp with
        | some b => ⟨SignType.pos, fun i => i.elim0, some b, some ()⟩
        | none => ⟨SignType.zero, fun i => i.elim0, none, none⟩ }

/-- Run invariant of the copy machine: after `t ≤ n` steps it is live, its input head
sits at position `t + 1`, and it has emitted exactly the first `t` input bits. -/
private lemma f2_idTM_run (x : List Bool) : ∀ t, t ≤ x.length →
    (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).state = some () ∧
    (((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).inputPos : ℕ) = t + 1) ∧
    (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).output = x.take t := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨rfl, ?_, rfl⟩
    simp [MultiTapeTM.runFrom]
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hpos, hout⟩ := ih (Nat.le_of_succ_le ht)
    have hrun1 : f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) (t + 1) =
        (f2_idTM.tm.tr () (some (x[t]'(by omega)))
          ((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).workTapeSymbols)).apply
          (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      dsimp only
      rw [inputSymbolInner (p := t) (by omega) (by omega)]
    refine ⟨?_, ?_, ?_⟩
    · rw [hrun1]
      simp [f2_idTM, Action.apply]
    · rw [hrun1]
      simp only [f2_idTM, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      show ((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) t).inputPos : ℕ) + 1 = t + 2
      omega
    · rw [hrun1]
      simp only [f2_idTM, Action.apply]
      rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- The zero-work-tape machine whose states form the emission chain for `w`. -/
private def f2_constTM (w : List Bool) : FinTM Bool where
  k := 0
  State := Fin (w.length + 1)
  tm := { q₀ := 0, tr := fun i _ _ => emitAction w id i }

/-- Emit the fixed prefix, then copy the input verbatim. No work tape is needed;
the last finite state is the copy state. -/
private def f2_catalogPrefixTM (w : List Bool) : FinTM Bool where
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
private def f2_catalogPrefixCfg (w x : List Bool) (q : Option (Fin (w.length + 1)))
    (p : Fin (x.length + 2)) (out : List Bool) : Cfg 0 Bool (Fin (w.length + 1)) x :=
  ⟨q, p, fun i => i.elim0, fun i => i.elim0, out⟩

/-- After `i` prefix steps exactly the first `i` fixed bits have been emitted,
and the input head has not moved. -/
private lemma f2_catalogPrefixTM_emit (w x : List Bool) : ∀ i (hi : i ≤ w.length),
    (f2_catalogPrefixTM w).tm.runFrom ((f2_catalogPrefixTM w).tm.initCfg x) i =
      f2_catalogPrefixCfg w x (some ⟨i, by omega⟩) 1 (w.take i) := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext_zero_tapes <;> simp [f2_catalogPrefixCfg, f2_catalogPrefixTM]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hlt : i < w.length := by omega
    simp only [MultiTapeTM.step, f2_catalogPrefixCfg, f2_catalogPrefixTM, dif_pos hlt, Action.apply]
    apply Cfg.ext_zero_tapes
    · rfl
    · simp
    · rw [List.take_succ, List.getElem?_eq_getElem hlt]

/-- The copy phase emits one input bit per step and preserves the fixed prefix. -/
private lemma f2_catalogPrefixTM_copy (w x : List Bool) : ∀ i (hi : i ≤ x.length),
    (f2_catalogPrefixTM w).tm.runFrom
      (f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩) 1 w) i =
      f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i) := by
  intro i
  induction i with
  | zero => intro hi; simp [f2_catalogPrefixCfg]
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hsym : (f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩)
        ⟨i + 1, by omega⟩ (w ++ x.take i)).inputSymbol = some (x[i]'(by omega)) :=
      inputSymbolInner i (by simp only [f2_catalogPrefixCfg]; omega) (by omega)
    change ((f2_catalogPrefixTM w).tm.tr ⟨w.length, by omega⟩
      (f2_catalogPrefixCfg w x (some ⟨w.length, by omega⟩) ⟨i + 1, by omega⟩
        (w ++ x.take i)).inputSymbol _).apply _ = _
    rw [hsym]
    simp only [f2_catalogPrefixTM, Nat.lt_irrefl, ↓reduceDIte, Action.apply, f2_catalogPrefixCfg]
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
private lemma f2_catalogPrefixTM_computes (w : List Bool) :
    (f2_catalogPrefixTM w).ComputesFunInTime (fun x => w ++ x) (fun n => w.length + n + 1) := by
  intro x
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  dsimp only
  rw [show w.length + x.length + 1 = w.length + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, f2_catalogPrefixTM_emit w x w.length (Nat.le_refl _)]
  simp only [List.take_length]
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_catalogPrefixTM_copy w x x.length (Nat.le_refl _)]
  simp [f2_catalogPrefixTM, f2_catalogPrefixCfg, MultiTapeTM.step, Cfg.inputSymbol, Fin.ext_iff, Action.apply]


/-- A zero-work-tape configuration indexed by the number of input bits passed. -/
private def f2_scanCfg {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) : Cfg 0 Bool S x :=
  ⟨q, ⟨i + 1, by omega⟩, fun j => j.elim0, fun j => j.elim0, out⟩

/-- Reading at the indexed input position returns the optional list entry. -/
private lemma f2_scanCfg_read {S : Type} (x : List Bool) (q : Option S)
    (i : ℕ) (hi : i ≤ x.length) (out : List Bool) :
    (f2_scanCfg x q i hi out).inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [List.getElem?_eq_getElem h]
    exact inputSymbolInner i (by simp [f2_scanCfg]; omega) h
  · have he : i = x.length := by omega
    subst i
    simp [f2_scanCfg, Cfg.inputSymbol, Fin.ext_iff]

/-- A copy state emits the next `j` input bits after an arbitrary output prefix.
**Proof sketch.** Induct on the number of copied cells; each transition appends
the scanned bit and moves right. The indexed configuration keeps the boundary
case separate from the actual bit-reading steps. -/
private lemma f2_scanCopy_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) : ∀ j (hj : j ≤ x.length),
    tm.runFrom (f2_scanCfg x (some q) 0 (by omega) out) j =
      f2_scanCfg x (some q) j hj (out ++ x.take j) := by
  intro j
  induction j with
  | zero => intro hj; simp [f2_scanCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    change (tm.tr q (f2_scanCfg x (some q) j (by omega) (out ++ x.take j)).inputSymbol
      _).apply _ = _
    rw [htr, f2_scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
    · simp only [Action.apply, f2_scanCfg, Option.toList_some, List.take_succ,
        List.getElem?_eq_getElem (by omega : j < x.length), List.append_assoc]

/-- After copying the entire input, the right-blank transition halts silently. -/
private lemma f2_scanCopy_finish {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x out : List Bool) :
    tm.runFrom (f2_scanCfg x (some q) 0 (by omega) out) (x.length + 1) =
      f2_scanCfg x none x.length (by omega) (out ++ x) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_scanCopy_run tm q htr x out _ (by omega)]
  unfold MultiTapeTM.step
  change (tm.tr q (f2_scanCfg x (some q) x.length (by omega)
    (out ++ x.take x.length)).inputSymbol _).apply _ = _
  rw [htr, f2_scanCfg_read]
  apply Cfg.ext_zero_tapes <;> simp [Action.apply, f2_scanCfg]

/-- Duplicate the input into the self-delimiting pair: double on the first
pass, rewind silently after emitting the separator's first bit, then emit its
second bit and copy. Every input is legal, so no validation buffer is needed. -/
private def f2_pairDupTM : FinTM Bool where
  k := 0
  State := Fin 5
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some b => ⟨0, fun j => j.elim0, some b, some 1⟩
          | none => ⟨.neg, fun j => j.elim0, some false, some 2⟩
        | 1 => ⟨.pos, fun j => j.elim0, inp, some 0⟩
        | 2 => match inp with
          | some _ => controlAction .neg (some 2)
          | none => controlAction .pos (some 3)
        | 3 => ⟨0, fun j => j.elim0, some true, some 4⟩
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 4⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- Every two first-pass transitions emit one doubled input bit.
**Proof sketch.** The first transition emits while staying at the scanned
cell, and the second emits that same bit and advances. Induction concatenates
these two-step blocks, leaving the right blank for the separator transition. -/
private lemma f2_pairDup_double (x : List Bool) : ∀ j (hj : j ≤ x.length),
    f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x) (2 * j) =
      f2_scanCfg x (some (0 : Fin 5)) j hj ((x.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext_zero_tapes <;> simp [f2_scanCfg, f2_pairDupTM]
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread := f2_scanCfg_read x (some (0 : Fin 5)) j (by omega)
      ((x.take j).flatMap fun b => [b, b])
    rw [List.getElem?_eq_getElem (by omega)] at hread
    have hfirst : f2_pairDupTM.tm.step
        (f2_scanCfg x (some (0 : Fin 5)) j (by omega) ((x.take j).flatMap fun b => [b, b])) =
        f2_scanCfg x (some (1 : Fin 5)) j (by omega)
          (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change (f2_pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
      rw [hread]
      apply Cfg.ext_zero_tapes <;> simp [f2_pairDupTM, Action.apply, f2_scanCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change (f2_pairDupTM.tm.tr (1 : Fin 5) _ _).apply _ = _
    rw [f2_scanCfg_read, List.getElem?_eq_getElem (by omega)]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
    · change (((x.take j).flatMap fun b => [b, b]) ++ [x[j]'(by omega)]) ++
        [x[j]'(by omega)] = (x.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < x.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- The two passes and rewind take exactly `4|x|+4` transitions.
**Proof sketch.** Doubling costs `2|x|`, emitting the first separator bit
costs one, rewind and dispatch cost `|x|+1`, the second separator bit costs
one, and copying with its final blank test costs `|x|+1`. -/
private lemma f2_pairDup_computes (x : List Bool) :
    f2_pairDupTM.ComputesInTime x (pairEncode x x) (4 * (x.length + 1)) := by
  let pre := x.flatMap fun b => [b, b]
  let c : Cfg 0 Bool (Fin 5) x :=
    ⟨some 2, ⟨x.length, by omega⟩, fun j => j.elim0, fun j => j.elim0, pre ++ [false]⟩
  have hsep : f2_pairDupTM.tm.step (f2_scanCfg x (some (0 : Fin 5)) x.length (by omega) pre) = c := by
    unfold MultiTapeTM.step
    change (f2_pairDupTM.tm.tr (0 : Fin 5) _ _).apply _ = _
    rw [f2_scanCfg_read]
    apply Cfg.ext_zero_tapes
    · simp [f2_pairDupTM, c]
    · simpa [f2_pairDupTM, Action.apply, f2_scanCfg, c] using
        moveInputPos_neg_of_ne_left (⟨x.length + 1, by omega⟩ : Fin (x.length + 2))
          (by simp [Fin.ext_iff])
    · simp [f2_pairDupTM, Action.apply, f2_scanCfg, c]
  have hr := rewind_scan f2_pairDupTM.tm (2 : Fin 5) (some (3 : Fin 5)) (fun _ _ => rfl) c rfl (by simp [c])
  have hemit : f2_pairDupTM.tm.step {c with state := some (3 : Fin 5), inputPos := 1} =
      f2_scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    apply Cfg.ext_zero_tapes <;>
      simp [MultiTapeTM.step, f2_pairDupTM, c, f2_scanCfg, Action.apply, List.append_assoc]
  have h1 : f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x) (2 * x.length + 1) = c := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_pairDup_double x x.length (by omega)]
    simpa only [List.take_length] using hsep
  have h2 : f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1)) =
      {c with state := some (3 : Fin 5), inputPos := 1} := by
    rw [MultiTapeTM.runFrom_add, h1]
    exact hr
  have h3 : f2_pairDupTM.tm.runFrom (f2_pairDupTM.tm.initCfg x)
      (2 * x.length + 1 + (x.length + 1) + 1) =
      f2_scanCfg x (some (4 : Fin 5)) 0 (by omega) (pre ++ [false, true]) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', h2, hemit]
  apply (computesInTime_iff _ _ _ _).mpr
  rw [show 4 * (x.length + 1) = (2 * x.length + 1 + (x.length + 1) + 1) +
    (x.length + 1) by omega, MultiTapeTM.runFrom_add, h3,
    f2_scanCopy_finish f2_pairDupTM.tm (4 : Fin 5) (fun _ _ => rfl)]
  exact ⟨rfl, rfl⟩

/-- Copy a suffix from an already-positioned input head, preserving prior output.
**Proof sketch.** Induct on the suffix. A nonempty suffix emits its first bit
and shifts the prefix/suffix boundary by one. The empty suffix reads the right
blank and halts without another emission. -/
private lemma f2_scanCopy_suffix {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (htr : ∀ inp work, tm.tr q inp work = match inp with
      | some b => ⟨.pos, fun j => j.elim0, some b, some q⟩
      | none => ⟨0, fun j => j.elim0, none, none⟩)
    (x rest : List Bool) : ∀ pre out (hx : x = pre ++ rest),
    tm.runFrom (f2_scanCfg x (some q) pre.length (by simp [hx]) out) (rest.length + 1) =
      f2_scanCfg x none x.length (by omega) (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    subst x
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (tm.tr q _ _).apply _ = _
    rw [htr, f2_scanCfg_read]
    apply Cfg.ext_zero_tapes <;> simp [Action.apply, f2_scanCfg]
  | cons b rest ih =>
    intro pre out hx
    have hlen : pre.length < x.length := by simp [hx]
    have hread : x[pre.length]? = some b := by simp [hx]
    have hs : tm.step (f2_scanCfg x (some q) pre.length (by omega) out) =
        f2_scanCfg x (some q) (pre ++ [b]).length (by simp [hx]) (out ++ [b]) := by
      unfold MultiTapeTM.step
      change (tm.tr q _ _).apply _ = _
      rw [htr, f2_scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [f2_scanCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by omega⟩ : Fin (x.length + 2)) (by simp; omega)
      · rfl
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- A true-prefix scan either remains silent or emits one false per true.
**Proof sketch.** Induct on the prefix length. Taking a shorter prefix gives
the induction hypothesis, and the last entry of the longer prefix identifies
the symbol read by the next transition. -/
private lemma f2_scanTrues_run {S : Type} (tm : MultiTapeTM 0 Bool S) (q : S)
    (emit : Bool)
    (htr : ∀ work, tm.tr q (some true) work =
      ⟨.pos, fun j => j.elim0, if emit then some false else none, some q⟩)
    (x : List Bool) : ∀ j (hj : j ≤ x.length),
    x.take j = List.replicate j true →
    tm.runFrom (f2_scanCfg x (some q) 0 (by omega) []) j =
      f2_scanCfg x (some q) j hj (if emit then List.replicate j false else []) := by
  intro j
  induction j with
  | zero => intro hj hp; cases emit <;> rfl
  | succ j ih =>
    intro hj hp
    have hshort : x.take j = List.replicate j true := by
      have h := congrArg (List.take j) hp
      simpa only [List.take_take, List.take_replicate, Nat.min_eq_left (by omega : j ≤ j + 1)] using h
    have hb : x[j]? = some true := by
      have h := congrArg (fun w : List Bool => w[j]?) hp
      simpa [List.getElem?_take, Nat.lt_succ_self] using h
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega) hshort]
    unfold MultiTapeTM.step
    change (tm.tr q _ _).apply _ = _
    rw [f2_scanCfg_read, hb, htr]
    apply Cfg.ext_zero_tapes
    · rfl
    · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
    · cases emit <;> simp [Action.apply, f2_scanCfg, List.replicate_succ']

/-- Either every input bit is true (overflow), or its first false splits off
the carry prefix and determines the exact incremented word. -/
private lemma f2_incFixed_cases (x : List Bool) :
    (x = List.replicate x.length true ∧ incFixed x = none) ∨
      ∃ j rest, x = List.replicate j true ++ false :: rest ∧
        incFixed x = some (List.replicate j false ++ true :: rest) := by
  induction x with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons b x ih =>
    cases b with
    | false => exact Or.inr ⟨0, x, rfl, rfl⟩
    | true =>
      rcases ih with ⟨hx, hinc⟩ | ⟨j, rest, hx, hinc⟩
      · exact Or.inl ⟨by simpa only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and] using hx, by simp [incFixed, hinc]⟩
      · exact Or.inr ⟨j + 1, rest, by simp [hx, List.replicate_succ],
          by simp [incFixed, hinc, List.replicate_succ]⟩

/-- Detect a nonoverflowing word silently, rewind, then perform the carry
while emitting. This is the enumerator's carry discipline adapted to native
input and append-only output; unlike the in-place harvest, it validates first. -/
private def f2_incFixedTM : FinTM Bool where
  k := 0
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp _ => match q.val with
        | 0 => match inp with
          | some true => ⟨.pos, fun j => j.elim0, none, some 0⟩
          | some false => controlAction .neg (some 1)
          | none => controlAction 0 none
        | 1 => match inp with
          | some _ => controlAction .neg (some 1)
          | none => controlAction .pos (some 2)
        | 2 => match inp with
          | some true => ⟨.pos, fun j => j.elim0, some false, some 2⟩
          | some false => ⟨.pos, fun j => j.elim0, some true, some 3⟩
          | none => controlAction 0 none
        | _ => match inp with
          | some b => ⟨.pos, fun j => j.elim0, some b, some 3⟩
          | none => ⟨0, fun j => j.elim0, none, none⟩ }

/-- Fixed-width increment is computed within `3(|x|+1)` steps, with no output
on overflow, including the empty word.
**Proof sketch.** The all-true case scans and halts silently. Otherwise let
`j` be the first false's index. Detection plus rewind costs `2j+2`; carry
emission and suffix copy cost `|x|+1`. Since `j < |x|`, the advertised
linear envelope covers the whole run. -/
private lemma f2_incFixed_computes (x : List Bool) :
    f2_incFixedTM.ComputesInTime x ((incFixed x).getD []) (3 * (x.length + 1)) := by
  rcases f2_incFixed_cases x with ⟨hx, hinc⟩ | ⟨j, rest, hx, hinc⟩
  · have hr := f2_scanTrues_run f2_incFixedTM.tm (0 : Fin 4) false (fun _ => rfl)
      x x.length (by omega) (by simpa using hx)
    have hh : f2_incFixedTM.ComputesInTime x [] (x.length + 1) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_succ_eq_step', show f2_incFixedTM.tm.initCfg x =
        f2_scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [f2_incFixedTM, f2_scanCfg], hr]
      unfold MultiTapeTM.step
      change ((f2_incFixedTM.tm.tr (0 : Fin 4) _ _).apply _).state = none ∧ _
      rw [f2_scanCfg_read]
      simp [f2_incFixedTM, controlAction, Action.apply, f2_scanCfg]
    simpa only [hinc, Option.getD_none] using hh.mono (by omega)
  · have hj : j < x.length := by simp [hx]
    have hpre : x.take j = List.replicate j true := by simp [hx]
    have hread : x[j]? = some false := by simp [hx]
    let c : Cfg 0 Bool (Fin 4) x :=
      ⟨some 1, ⟨j, by omega⟩, fun i => i.elim0, fun i => i.elim0, []⟩
    have hdet : f2_incFixedTM.tm.runFrom (f2_incFixedTM.tm.initCfg x) (j + 1) = c := by
      rw [MultiTapeTM.runFrom_succ_eq_step', show f2_incFixedTM.tm.initCfg x =
        f2_scanCfg x (some (0 : Fin 4)) 0 (by omega) [] from
          by apply Cfg.ext_zero_tapes <;> simp [f2_incFixedTM, f2_scanCfg],
        f2_scanTrues_run f2_incFixedTM.tm (0 : Fin 4) false (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (f2_incFixedTM.tm.tr (0 : Fin 4) _ _).apply _ = _
      rw [f2_scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · simpa [f2_incFixedTM, controlAction, Action.apply, f2_scanCfg, c] using
          moveInputPos_neg_of_ne_left (⟨j + 1, by omega⟩ : Fin (x.length + 2))
            (by simp [Fin.ext_iff])
      · rfl
    have hrew : f2_incFixedTM.tm.runFrom (f2_incFixedTM.tm.initCfg x) (j + 1 + (j + 1)) =
        f2_scanCfg x (some (2 : Fin 4)) 0 (by omega) [] := by
      rw [MultiTapeTM.runFrom_add, hdet]
      exact rewind_scan f2_incFixedTM.tm (1 : Fin 4) (some (2 : Fin 4))
        (fun _ _ => rfl) c rfl (by simp [c]; omega)
    have hemit : f2_incFixedTM.tm.runFrom (f2_scanCfg x (some (2 : Fin 4)) 0 (by omega) [])
        (j + 1) = f2_scanCfg x (some (3 : Fin 4)) (j + 1) (by omega)
          (List.replicate j false ++ [true]) := by
      rw [MultiTapeTM.runFrom_succ_eq_step',
        f2_scanTrues_run f2_incFixedTM.tm (2 : Fin 4) true (fun _ => rfl) x j (by omega) hpre]
      unfold MultiTapeTM.step
      change (f2_incFixedTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      rw [f2_scanCfg_read, hread]
      apply Cfg.ext_zero_tapes
      · rfl
      · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
      · rfl
    have hcopy := f2_scanCopy_suffix f2_incFixedTM.tm (3 : Fin 4) (fun _ _ => rfl)
      x rest (List.replicate j true ++ [false]) (List.replicate j false ++ [true])
      (by simpa [List.append_assoc] using hx)
    have hh : f2_incFixedTM.ComputesInTime x (List.replicate j false ++ true :: rest)
        ((j + 1 + (j + 1)) + ((j + 1) + (rest.length + 1))) := by
      apply (computesInTime_iff _ _ _ _).mpr
      rw [MultiTapeTM.runFrom_add, hrew, MultiTapeTM.runFrom_add, hemit]
      simp only [List.length_append, List.length_replicate, List.length_singleton] at hcopy
      rw [hcopy]
      exact ⟨rfl, by simp [f2_scanCfg, List.append_assoc]⟩
    have hlen : x.length = j + 1 + rest.length := by simp [hx]; omega
    simpa only [hinc, Option.getD_some] using hh.mono (by omega)

/-- A right-moving zero-tape transition advances the indexed configuration
and appends exactly its optional emission. -/
private lemma f2_scanStep_right {S : Type} (tm : MultiTapeTM 0 Bool S)
    (x : List Bool) (q : S) (q' : Option S) (i : ℕ) (hi : i < x.length)
    (out : List Bool) (emit : Option Bool)
    (htr : ∀ work, tm.tr q x[i]? work = ⟨.pos, fun j => j.elim0, emit, q'⟩) :
    tm.step (f2_scanCfg x (some q) i (by omega) out) =
      f2_scanCfg x q' (i + 1) (by omega) (out ++ emit.toList) := by
  unfold MultiTapeTM.step
  change (tm.tr q _ _).apply _ = _
  rw [f2_scanCfg_read, htr]
  apply Cfg.ext_zero_tapes
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [f2_scanCfg]; omega)
  · rfl

/-- Scan aligned pairs of bits, retaining just the first bit of the current
block. Only a terminal verdict transition emits output. -/
private def f2_pairValidTM : FinTM Bool where
  k := 0
  State := Option Bool
  tm :=
    { q₀ := none
      tr := fun q inp _ => match q, inp with
        | none, some b => ⟨.pos, fun j => j.elim0, none, some (some b)⟩
        | some b, some c =>
          if b = c then ⟨.pos, fun j => j.elim0, none, some none⟩
          else ⟨.pos, fun j => j.elim0, some (!b && c), none⟩
        | _, none => ⟨0, fun j => j.elim0, some false, none⟩ }

/-- One aligned block either continues silently or halts with its verdict. -/
private lemma f2_pairValid_block (x pre rest : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    f2_pairValidTM.tm.runFrom (f2_scanCfg x (some none) pre.length (by simp [hx]) []) 2 =
      if b = c then f2_scanCfg x (some none) (pre.length + 2) (by simp [hx]) []
      else f2_scanCfg x none (pre.length + 2) (by simp [hx]) [!b && c] := by
  have h1 := f2_scanStep_right f2_pairValidTM.tm x none (some (some b)) pre.length
    (by simp [hx]) [] none (by intro work; simp [hx, f2_pairValidTM])
  have h2 := f2_scanStep_right f2_pairValidTM.tm x (some b)
    (if b = c then some none else none) (pre.length + 1) (by simp [hx])
    [] (if b = c then none else some (!b && c)) (by
      intro work
      have hr : x[pre.length + 1]? = some c := by simp [hx]
      rw [hr]
      by_cases h : b = c <;> simp [f2_pairValidTM, h])
  change f2_pairValidTM.tm.step (f2_pairValidTM.tm.step _) = _
  rw [h1]
  simp only [Option.toList_none, List.append_nil]
  rw [h2]
  by_cases h : b = c <;> simp [h]

/-- The validity scanner halts within one more than the unprocessed length.
**Proof sketch.** Induct in aligned two-bit blocks. The empty and singleton
cases fail on a boundary blank. Equal-bit blocks invoke the induction
hypothesis silently; `01` succeeds and `10` fails immediately, independently
of the suffix. Thus no verdict is emitted before validity is decided. -/
private lemma f2_pairValid_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (f2_pairValidTM.tm.runFrom
        (f2_scanCfg x (some none) pre.length (by simp [hx]) []) t).state = none ∧
      (f2_pairValidTM.tm.runFrom
        (f2_scanCfg x (some none) pre.length (by simp [hx]) []) t).output =
          [(pairDecode rest).isSome] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((f2_pairValidTM.tm.tr none _ _).apply _).state = none ∧ _
    rw [f2_scanCfg_read]
    simp [hx, f2_pairValidTM, Action.apply, f2_scanCfg, pairDecode]
  | singleton b =>
    intro pre hx
    have h1 := f2_scanStep_right f2_pairValidTM.tm x none (some (some b)) pre.length
      (by simp [hx]) [] none (by intro work; simp [hx, f2_pairValidTM])
    refine ⟨2, by simp, ?_⟩
    change (f2_pairValidTM.tm.step (f2_pairValidTM.tm.step _)).state = none ∧
      (f2_pairValidTM.tm.step (f2_pairValidTM.tm.step _)).output = _
    rw [h1]
    unfold MultiTapeTM.step
    change ((f2_pairValidTM.tm.tr (some b) _ _).apply _).state = none ∧ _
    rw [f2_scanCfg_read]
    cases b <;> simp [hx, f2_pairValidTM, Action.apply, f2_scanCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, f2_pairValid_block x pre rest b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> simpa [pairDecode] using ho
    · refine ⟨2, by simp, ?_⟩
      rw [f2_pairValid_block x pre rest b c hx, if_neg h]
      cases b <;> cases c <;> simp_all [f2_scanCfg, pairDecode]

/-- The validity test starts with an empty aligned prefix and uses the
linear envelope `|x|+1`. -/
private lemma f2_pairValid_computes (x : List Bool) :
    f2_pairValidTM.ComputesInTime x [(pairDecode x).isSome] (x.length + 1) := by
  obtain ⟨t, ht, hs, ho⟩ := f2_pairValid_run x x [] rfl
  have hinit : f2_pairValidTM.tm.initCfg x = f2_scanCfg x (some none) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> simp [f2_pairValidTM, f2_scanCfg]
  have h : f2_pairValidTM.ComputesInTime x [(pairDecode x).isSome] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact h.mono ht


/-- A shared extractor buffers the decoded prefix, validates the separator,
rewinds and replays the buffer, then optionally copies the suffix. The two
flags select the first component, the second, or their concatenation. -/
private def f2_pairExtractTM (first second : Bool) : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Fin 3
  tm :=
    { q₀ := .inl none
      tr := fun q inp work => match q with
        | .inl none => match inp with
          | some b => ⟨.pos, fun _ => (none, 0), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, 0), none, none⟩
        | .inl (some b) => match inp with
          | none => ⟨0, fun _ => (none, 0), none, none⟩
          | some c =>
            if b = c then
              ⟨.pos, fun _ => (some (some b), .pos), none, some (.inl none)⟩
            else if b then ⟨.pos, fun _ => (none, 0), none, none⟩
            else ⟨.pos, fun _ => (none, .neg), none, some (.inr 0)⟩
        | .inr q => match q.val with
          | 0 => match work 0 with
            | some _ => ⟨0, fun _ => (none, .neg), none, some (.inr 0)⟩
            | none => ⟨0, fun _ => (none, .pos), none, some (.inr 1)⟩
          | 1 => match work 0 with
            | some b => ⟨0, fun _ => (none, .pos), if first then some b else none, some (.inr 1)⟩
            | none => ⟨0, fun _ => (none, 0), none, some (.inr 2)⟩
          | _ => if second then match inp with
              | some b => ⟨.pos, fun _ => (none, 0), some b, some (.inr 2)⟩
              | none => ⟨0, fun _ => (none, 0), none, none⟩
            else ⟨0, fun _ => (none, 0), none, none⟩ }

/-- The shared extractor's one-buffer configurations. -/
private def f2_extractCfg (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    Cfg 1 Bool (Option Bool ⊕ Fin 3) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape a, fun _ => z, out⟩

/-- The extractor reads the indexed input entry independently of its buffer. -/
private lemma f2_extractCfg_read (x : List Bool) (q : Option (Option Bool ⊕ Fin 3))
    (i : ℕ) (hi : i ≤ x.length) (a : List Bool) (z : ℤ) (out : List Bool) :
    (f2_extractCfg x q i hi a z out).inputSymbol = x[i]? :=
  f2_scanCfg_read x q i hi out

/-- Reading the first half of an aligned block preserves the buffer silently. -/
private lemma f2_extract_first (first second : Bool) (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    (f2_pairExtractTM first second).tm.step
      (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) =
      f2_extractCfg x (some (.inl (some b))) (pre.length + 1) (by simp [hx]) a a.length [] := by
  unfold MultiTapeTM.step
  change ((f2_pairExtractTM first second).tm.tr (.inl none) _ _).apply _ = _
  rw [f2_extractCfg_read]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [f2_extractCfg, hx])
  · funext i; simp [f2_pairExtractTM, Action.apply, f2_extractCfg]

/-- Equal-bit blocks append one decoded bit; `01` begins replay and `10`
halts silently. In particular, neither transition emits physical output. -/
private lemma f2_extract_block (first second : Bool) (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) 2 =
      if b = c then f2_extractCfg x (some (.inl none)) (pre.length + 2) (by simp [hx])
          (a ++ [b]) (a ++ [b]).length []
      else if b then f2_extractCfg x none (pre.length + 2) (by simp [hx]) a a.length []
      else f2_extractCfg x (some (.inr 0)) (pre.length + 2) (by simp [hx]) a (a.length - 1) [] := by
  change (f2_pairExtractTM first second).tm.step ((f2_pairExtractTM first second).tm.step _) = _
  rw [f2_extract_first first second x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change ((f2_pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _ = _
  rw [f2_extractCfg_read]
  have hr : x[pre.length + 1]? = some c := by simp [hx]
  rw [hr]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ := by
    exact moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases c <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals refine Cfg.ext rfl hm ?_ ?_ rfl
  all_goals first
    | rfl
    | (funext i; exact (bufferTape_append a _).symm)
    | (funext i; simp [f2_pairExtractTM, Action.apply, f2_extractCfg])

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma f2_extract_rewind (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) []) (j + 1) =
      f2_extractCfg x (some (.inr 1)) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (f2_pairExtractTM first second).tm.step
        (f2_extractCfg x (some (.inr 0)) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        f2_extractCfg x (some (.inr 0)) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay reads the buffered word once; the first-component flag decides
whether those reads emit. At the right blank the controller starts the suffix.
**Proof sketch.** Induct on the number of replayed cells. Each live step
preserves the tape and appends either its bit or nothing. -/
private lemma f2_extract_replay (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j (_hj : j ≤ a.length),
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 1)) i hi a 0 []) j =
      f2_extractCfg x (some (.inr 1)) i hi a j (if first then a.take j else []) := by
  intro j
  induction j with
  | zero => intro hj; cases first <;> rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change (if first then a.take j else []) ++
        (if first then some (a[j]'(by omega)) else none).toList =
          (if first then a.take (j + 1) else [])
      have ht : a.take j ++ [a[j]'(by omega)] = a.take (j + 1) := by
        rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
        rfl
      cases first with
      | false => rfl
      | true => exact ht

/-- Replay's right-blank test dispatches to the suffix state silently. -/
private lemma f2_extract_replay_finish (first second : Bool) (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) :
    (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 1)) i hi a 0 []) (a.length + 1) =
      f2_extractCfg x (some (.inr 2)) i hi a a.length (if first then a else []) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_extract_replay first second x a i hi _ (by omega)]
  unfold MultiTapeTM.step
  simp only [f2_pairExtractTM, f2_extractCfg, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_length, List.take_length]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext k; simp [Action.apply]
  · simp [Action.apply]

/-- With suffix copying enabled, the final phase emits the remaining input.
**Proof sketch.** The input prefix grows by one at each emitting transition;
the buffer and its head remain fixed. A right-blank test supplies the final
halting step. This is the one-buffer version of the private suffix-copy lemma. -/
private lemma f2_extract_suffix (first : Bool) (x rest a : List Bool) :
    ∀ pre out (hx : x = pre ++ rest),
    (f2_pairExtractTM first true).tm.runFrom
      (f2_extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out)
        (rest.length + 1) =
      f2_extractCfg x none x.length (by omega) a a.length (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    simp only [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((f2_pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
    rw [f2_extractCfg_read]
    have hr : x[pre.length]? = none := by simp [hx]
    rw [hr]
    refine Cfg.ext rfl ?_ rfl ?_ ?_
    · simp [f2_pairExtractTM, Action.apply, f2_extractCfg, hx]
    · funext k; simp [f2_pairExtractTM, Action.apply, f2_extractCfg]
    · simp [f2_pairExtractTM, Action.apply, f2_extractCfg]
  | cons b rest ih =>
    intro pre out hx
    have hs : (f2_pairExtractTM first true).tm.step
        (f2_extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length out) =
        f2_extractCfg x (some (.inr 2)) (pre ++ [b]).length (by simp [hx])
          a a.length (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((f2_pairExtractTM first true).tm.tr (.inr 2) _ _).apply _ = _
      rw [f2_extractCfg_read]
      have hr : x[pre.length]? = some b := by simp [hx]
      rw [hr]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa [f2_extractCfg] using moveInputPos_pos_of_ne_right
          (⟨pre.length + 1, by simp [hx]; omega⟩ : Fin (x.length + 2)) (by simp [hx])
      · funext k; simp [f2_pairExtractTM, Action.apply, f2_extractCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hx)

/-- Once validation succeeds, rewind, replay, and optional suffix copying
cost at most `2|a|+|rest|+3` steps.
**Proof sketch.** The rewind costs `|a|+1`, and replay plus dispatch costs
`|a|+1`. Disabled suffix copying halts in one step; enabled copying uses
`|rest|+1`. Only these postvalidation phases emit output. -/
private lemma f2_extract_finish (first second : Bool) (x pre rest a : List Bool)
    (hx : x = pre ++ rest) :
    ∃ t ≤ 2 * a.length + rest.length + 3,
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).state = none ∧
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) []) t).output =
          (if first then a else []) ++ (if second then rest else []) := by
  have hp : (f2_pairExtractTM first second).tm.runFrom
      (f2_extractCfg x (some (.inr 0)) pre.length (by simp [hx]) a (a.length - 1) [])
        ((a.length + 1) + (a.length + 1)) =
      f2_extractCfg x (some (.inr 2)) pre.length (by simp [hx]) a a.length (if first then a else []) := by
    rw [MultiTapeTM.runFrom_add, f2_extract_rewind first second x a _ _ _ (by omega),
      f2_extract_replay_finish]
  cases second with
  | false =>
    refine ⟨(a.length + 1) + (a.length + 1) + 1, by omega, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', hp]
    simp [MultiTapeTM.step, f2_pairExtractTM, f2_extractCfg, Action.apply]
  | true =>
    refine ⟨((a.length + 1) + (a.length + 1)) + (rest.length + 1), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hp, f2_extract_suffix first x rest a pre _ hx]
    exact ⟨rfl, rfl⟩

/-- The silent aligned parser either rejects or validates and invokes replay.
**Proof sketch.** Induct over aligned two-bit blocks while carrying the
already-decoded buffer. A doubled bit costs two steps and enlarges the buffer
by one; the linear potential `3|rest|+2|a|+5` pays for both effects. Missing
and forbidden separators halt silently. At `01`, apply the validated finish
ledger. The result includes the previously buffered prefix only on success. -/
private lemma f2_extract_run (first second : Bool) (x rest : List Bool) :
    ∀ pre a (hx : x = pre ++ rest),
    ∃ t ≤ 3 * rest.length + 2 * a.length + 5,
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).state = none ∧
      ((f2_pairExtractTM first second).tm.runFrom
        (f2_extractCfg x (some (.inl none)) pre.length (by simp [hx]) a a.length []) t).output =
          match pairDecode rest with
          | some (b, c) => (if first then a ++ b else []) ++ (if second then c else [])
          | none => [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx
    refine ⟨1, by omega, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((f2_pairExtractTM first second).tm.tr (.inl none) _ _).apply _).state = none ∧ _
    rw [f2_extractCfg_read]
    simp [hx, f2_pairExtractTM, Action.apply, f2_extractCfg, pairDecode]
  | singleton b =>
    intro pre a hx
    refine ⟨2, by simp, ?_⟩
    change ((f2_pairExtractTM first second).tm.step ((f2_pairExtractTM first second).tm.step _)).state = none ∧
      ((f2_pairExtractTM first second).tm.step ((f2_pairExtractTM first second).tm.step _)).output = _
    rw [f2_extract_first first second x pre [] a b hx]
    unfold MultiTapeTM.step
    change (((f2_pairExtractTM first second).tm.tr (.inl (some b)) _ _).apply _).state = none ∧ _
    rw [f2_extractCfg_read]
    cases b <;> simp [hx, f2_pairExtractTM, Action.apply, f2_extractCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b]) (a ++ [b]) (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, f2_extract_block first second x pre rest a b b hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, List.length_nil] using hs
      · cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd, List.append_assoc] using ho
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := f2_extract_finish first second x (pre ++ [false, true]) rest a
          (by simpa [List.append_assoc] using hx)
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, f2_extract_block first second x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [f2_extract_block first second x pre rest a true false hx]
        simp [f2_extractCfg, pairDecode]
      · exact False.elim (h rfl)

/-- The three extractor modes share the uniform linear envelope `5(|x|+1)`.
The initial buffer and decoded prefix are empty. -/
private lemma f2_pairExtract_computes (first second : Bool) (x : List Bool) :
    (f2_pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) (5 * (x.length + 1)) := by
  obtain ⟨t, ht, hs, ho⟩ := f2_extract_run first second x x [] [] rfl
  have hinit : (f2_pairExtractTM first second).tm.initCfg x =
      f2_extractCfg x (some (.inl none)) 0 (by omega) [] 0 [] := by
    apply Cfg.ext <;> simp [f2_pairExtractTM, f2_extractCfg, MultiTapeTM.initCfg, Cfg.init]
  have hh : (f2_pairExtractTM first second).ComputesInTime x
      (match pairDecode x with
        | some (a, b) => (if first then a else []) ++ (if second then b else [])
        | none => []) t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, by simpa using ho⟩
  exact hh.mono (by simp only [List.length_nil] at ht; omega)


/-- Control for copying the side length, nested unary loops, and constant emission. -/
private inductive f2_CatalogPolyControl (c C : ℕ) where
  | copy | setup
  | loop (i : Fin (c + 1))
  | rewind (i : Fin (c + 1))
  | advance (i : Fin (c + 2))
  | emit (j : Fin (C + 1))

/-- Enumerate the control through a finite sum representation, privately. -/
private instance f2_catalogPolyControlFintype (c C : ℕ) : Fintype (f2_CatalogPolyControl c C) :=
  derive_fintype% _

/-- Compare control states through the same finite sum representation, privately. -/
private instance f2_catalogPolyControlDecidableEq (c C : ℕ) : DecidableEq (f2_CatalogPolyControl c C) :=
  (proxy_equiv% (f2_CatalogPolyControl c C)).symm.decidableEq

/-- A unary word of length `q`, surrounded by blanks. -/
private def f2_catalogPolyTape (q : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < q then some true else none

/-- Move just the selected work head, preserving every tape. -/
private def f2_catalogPolyMove {c C : ℕ} (i : Fin (c + 1)) (d : SignType)
    (s : f2_CatalogPolyControl c C) : Action (c + 1) Bool (f2_CatalogPolyControl c C) :=
  ⟨0, fun j => (none, if j = i then d else 0), none, some s⟩

/-- Finite machine emitting `C` symbols at each point of a `(c+1)`-dimensional
box. The unary loop tapes are copied in parallel; rewinding a completed inner
loop costs its side length, charged to the iterations that just completed. -/
private def f2_catalogPolyUnaryTM (c C : ℕ) : FinTM Bool where
  k := c + 1
  State := f2_CatalogPolyControl c C
  tm := {
    q₀ := .copy
    tr := fun s inp w => match s with
      | .copy => match inp with
        | some _ => ⟨.pos, fun _ => (some (some true), .pos), none, some .copy⟩
        | none => ⟨0, fun _ => (some (some true), .neg), none, some .setup⟩
      | .setup =>
        if w 0 = none then
          ⟨0, fun _ => (none, .pos), none, some (.loop (Fin.last c))⟩
        else ⟨0, fun _ => (none, .neg), none, some .setup⟩
      | .loop i =>
        if w i = none then f2_catalogPolyMove i .neg (.rewind i)
        else ⟨0, fun _ => (none, 0), none,
          some (if h : i.val = 0 then .emit ⟨C, Nat.lt_succ_self C⟩
            else .loop ⟨i.val - 1, by omega⟩)⟩
      | .rewind i =>
        if w i = none then f2_catalogPolyMove i .pos (.advance ⟨i.val + 1, by omega⟩)
        else f2_catalogPolyMove i .neg (.rewind i)
      | .advance i =>
        if h : i.val < c + 1 then f2_catalogPolyMove ⟨i.val, h⟩ .pos (.loop ⟨i.val, h⟩)
        else ⟨0, fun _ => (none, 0), none, none⟩
      | .emit j =>
        if h : j.val = 0 then ⟨0, fun _ => (none, 0), none, some (.advance 0)⟩
        else ⟨0, fun _ => (none, 0), some true,
          some (.emit ⟨j.val - 1, by omega⟩)⟩ }

/-- A loop configuration, with all unary tapes installed and arbitrary head positions. -/
private def f2_catalogPolyCfg {c C : ℕ} (x : List Bool) (q : ℕ)
    (s : f2_CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool) :
    Cfg (c + 1) Bool (f2_CatalogPolyControl c C) x :=
  ⟨some s, ⟨x.length + 1, by omega⟩, fun _ => f2_catalogPolyTape q, h, o⟩

/-- Applying a head-only action updates exactly the selected head. -/
private lemma f2_catalogPolyMove_apply {c C : ℕ} (x : List Bool) (q : ℕ)
    (s s' : f2_CatalogPolyControl c C) (h : Fin (c + 1) → ℤ) (o : List Bool)
    (i : Fin (c + 1)) (d : SignType) :
    (f2_catalogPolyMove i d s').apply (f2_catalogPolyCfg x q s h o) =
      f2_catalogPolyCfg x q s' (Function.update h i (h i + d.cast)) o := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · rfl
  · funext j
    by_cases hj : j = i <;> simp [f2_catalogPolyMove, f2_catalogPolyCfg, Action.apply, hj]
  · simp [f2_catalogPolyMove, f2_catalogPolyCfg, Action.apply]

/-- The finite emission chain appends exactly its remaining number of true bits. -/
private lemma f2_catalogPoly_emit {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) : ∀ j (hj : j ≤ C) (o : List Bool),
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q (.emit ⟨j, by omega⟩) h o) (j + 1) =
      f2_catalogPolyCfg x q (.advance 0) h (o ++ List.replicate j true) := by
  intro j
  induction j with
  | zero =>
    intro hj o
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;> simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Action.apply]
  | succ j ih =>
    intro hj o
    have hs : (f2_catalogPolyUnaryTM c C).tm.step
        (f2_catalogPolyCfg x q (.emit ⟨j + 1, by omega⟩) h o) =
        f2_catalogPolyCfg x q (.emit ⟨j, by omega⟩) h (o ++ [true]) := by
      apply Cfg.ext <;> simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Action.apply]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]
    simp [List.replicate_succ, List.append_assoc]

/-- Rewinding crosses a unary prefix and its left boundary, restoring head zero.
The other loop heads and the accumulated output remain unchanged. -/
private lemma f2_catalogPoly_rewind {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    ∀ j (_hj : j ≤ q),
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o) (j + 1) =
      f2_catalogPolyCfg x q (.advance ⟨i.val + 1, by omega⟩) (Function.update h i 0) o := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change ((if _ then _ else _) : Action (c + 1) Bool (f2_CatalogPolyControl c C)).apply _ = _
    simp only [Cfg.workTapeSymbols, f2_catalogPolyCfg, Function.update_self,
      Nat.cast_zero, zero_sub, f2_catalogPolyTape, show ¬(0 ≤ (-1 : ℤ) ∧ (-1 : ℤ) < q) by omega,
      ↓reduceIte]
    simpa [f2_catalogPolyCfg] using f2_catalogPolyMove_apply x q (.rewind i)
      (.advance ⟨i.val + 1, by omega⟩) (Function.update h i (-1)) o i .pos
  | succ j ih =>
    intro hj
    have hs : (f2_catalogPolyUnaryTM c C).tm.step
        (f2_catalogPolyCfg x q (.rewind i) (Function.update h i ((j + 1 : ℕ) - 1 : ℤ)) o) =
        f2_catalogPolyCfg x q (.rewind i) (Function.update h i ((j : ℤ) - 1)) o := by
      change ((if _ then _ else _) : Action (c + 1) Bool (f2_CatalogPolyControl c C)).apply _ = _
      simp only [Cfg.workTapeSymbols, f2_catalogPolyCfg, Function.update_self,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, f2_catalogPolyTape,
        if_pos (show 0 ≤ (j : ℤ) ∧ (j : ℤ) < q by omega),
        reduceCtorEq, ↓reduceIte]
      simpa [f2_catalogPolyCfg, sub_eq_add_neg] using f2_catalogPolyMove_apply x q (.rewind i)
        (.rewind i) (Function.update h i (j : ℤ)) o i .neg
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Returning from an inner loop advances the next outer loop by one cell. -/
private lemma f2_catalogPoly_advance {c C : ℕ} (x : List Bool) (q : ℕ)
    (h : Fin (c + 1) → ℤ) (o : List Bool) (i : Fin (c + 1)) :
    (f2_catalogPolyUnaryTM c C).tm.step
      (f2_catalogPolyCfg x q (.advance ⟨i.val, by omega⟩) h o) =
      f2_catalogPolyCfg x q (.loop i) (Function.update h i (h i + 1)) o := by
  simp only [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, i.isLt, ↓reduceDIte]
  simpa [f2_catalogPolyCfg] using f2_catalogPolyMove_apply x q
    (.advance ⟨i.val, by omega⟩) (.loop i) h o i .pos

/-- Exact time for a full nest of unary loops, with `r` loop levels. -/
private def f2_catalogPolyCost (q C : ℕ) : ℕ → ℕ
  | 0 => C + 1
  | r + 1 => q * (f2_catalogPolyCost q C r + 2) + q + 2

/-- A loop at level `i` executes its remaining iterations, resets its head,
and returns to its parent with exactly `C*q^i` new symbols per iteration.

**Proof sketch.** Induct on the nesting level, then on the number of remaining
iterations. At level zero the body is the finite emission chain. At higher
levels it is a complete inner loop. Each body has one dispatch and one parent
advance; after the final iteration the unary rewind restores the head to zero.
The invariant leaves all outer heads arbitrary, making recursive calls composable. -/
private lemma f2_catalogPoly_loop {c C : ℕ} (x : List Bool) (q : ℕ) (_hq : 0 < q) :
    ∀ i (hi : i < c + 1) (h : Fin (c + 1) → ℤ)
      (_hh : ∀ k, k.val ≤ i → h k = 0) (o : List Bool) (r j : ℕ), j + r = q →
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
      (r * (f2_catalogPolyCost q C i + 2) + q + 2) =
      f2_catalogPolyCfg x q (.advance ⟨i + 1, by omega⟩) h
        (o ++ List.replicate (r * (C * q ^ i)) true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi h hh o r
    have hbody (j : ℕ) (hj : j < q) (o : List Bool) :
        (f2_catalogPolyUnaryTM c C).tm.runFrom
          (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (j : ℤ)) o)
          (f2_catalogPolyCost q C i + 2) =
        f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((j : ℤ) + 1))
          (o ++ List.replicate (C * q ^ i) true) := by
      let h' := Function.update h ⟨i, hi⟩ (j : ℤ)
      have hread : (f2_catalogPolyCfg (C := C) x q (.loop ⟨i, hi⟩) h' o).workTapeSymbols ⟨i, hi⟩ =
          some true := by simp [h', f2_catalogPolyCfg, Cfg.workTapeSymbols, f2_catalogPolyTape, hj]
      have hs : (f2_catalogPolyUnaryTM c C).tm.step (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) =
          f2_catalogPolyCfg x q (if hz : i = 0 then .emit ⟨C, by omega⟩
            else .loop ⟨i - 1, by omega⟩) h' o := by
        unfold MultiTapeTM.step
        change ((f2_catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [f2_catalogPolyUnaryTM, hread, reduceCtorEq, ↓reduceIte]
        apply Cfg.ext <;> simp [f2_catalogPolyCfg, Action.apply]
      by_cases hz : i = 0
      · subst i
        simp only [↓reduceDIte] at hs
        change (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop 0) h' o) _ = _
        rw [show f2_catalogPolyCost q C 0 + 2 = 1 + (C + 1) + 1 by simp [f2_catalogPolyCost]; omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop 0) h' o) 1 =
            f2_catalogPolyCfg x q (.emit ⟨C, by omega⟩) h' o by simpa using hs,
          f2_catalogPoly_emit x q h' C (le_refl C),
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using f2_catalogPoly_advance (C := C) x q h'
          (o ++ List.replicate C true) (⟨0, hi⟩ : Fin (c + 1))
      · have hlow : ∀ k : Fin (c + 1), k.val ≤ i - 1 → h' k = 0 := by
          intro k hk
          have hne : k ≠ ⟨i, hi⟩ := by intro he; have := congrArg Fin.val he; simp at this; omega
          simp only [h', Function.update_of_ne hne]
          exact hh k (by omega)
        have hinner := ih (i - 1) (by omega) (by omega) h' hlow o q 0 (by omega)
        have hupdate : Function.update h' ⟨i - 1, by omega⟩ 0 = h' := by
          rw [← hlow ⟨i - 1, by omega⟩ (le_refl _)]
          exact Function.update_eq_self _ _
        have hi' : i - 1 + 1 = i := by omega
        have hout : q * (C * q ^ (i - 1)) = C * q ^ i := by
          calc
            q * (C * q ^ (i - 1)) = C * (q ^ (i - 1) * q) := by ring
            _ = C * q ^ i := by simp only [← Nat.pow_succ, Nat.succ_eq_add_one, hi']
        simp only [dif_neg hz] at hs
        simp only [Nat.cast_zero] at hinner
        rw [hupdate] at hinner
        have hinner' : (f2_catalogPolyUnaryTM c C).tm.runFrom
            (f2_catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o) (f2_catalogPolyCost q C i) =
            f2_catalogPolyCfg x q (.advance ⟨i, by omega⟩) h'
              (o ++ List.replicate (C * q ^ i) true) := by
          have hcost : q * (f2_catalogPolyCost q C (i - 1) + 2) + q + 2 =
              f2_catalogPolyCost q C i := by
            calc
              _ = f2_catalogPolyCost q C (i - 1 + 1) := rfl
              _ = f2_catalogPolyCost q C i := by rw [hi']
          simpa only [hcost, hi', hout] using hinner
        change (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) _ = _
        rw [show f2_catalogPolyCost q C i + 2 = 1 + f2_catalogPolyCost q C i + 1 by omega,
          MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
          show (f2_catalogPolyUnaryTM c C).tm.runFrom (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) h' o) 1 =
            f2_catalogPolyCfg x q (.loop ⟨i - 1, by omega⟩) h' o by simpa using hs,
          hinner', MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
        simpa [h'] using f2_catalogPoly_advance (C := C) x q h'
          (o ++ List.replicate (C * q ^ i) true) (⟨i, hi⟩ : Fin (c + 1))
    induction r generalizing o with
    | zero =>
      intro j hj
      have hj' : j = q := by omega
      subst j
      have hs : (f2_catalogPolyUnaryTM c C).tm.step
          (f2_catalogPolyCfg x q (.loop ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o) =
          f2_catalogPolyCfg x q (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ ((q : ℤ) - 1)) o := by
        unfold MultiTapeTM.step
        change ((f2_catalogPolyUnaryTM c C).tm.tr (.loop ⟨i, hi⟩) _ _).apply _ = _
        simp only [f2_catalogPolyUnaryTM, Cfg.workTapeSymbols, f2_catalogPolyCfg, Function.update_self,
          f2_catalogPolyTape, lt_self_iff_false, and_false, ↓reduceIte]
        simpa [f2_catalogPolyCfg, sub_eq_add_neg] using f2_catalogPolyMove_apply x q (.loop ⟨i, hi⟩)
          (.rewind ⟨i, hi⟩) (Function.update h ⟨i, hi⟩ (q : ℤ)) o ⟨i, hi⟩ .neg
      simp only [Nat.zero_mul, Nat.zero_add, List.replicate_zero, List.append_nil]
      rw [MultiTapeTM.runFrom_succ_eq_step, hs, f2_catalogPoly_rewind x q h o ⟨i, hi⟩ q (le_refl q)]
      rw [← hh ⟨i, hi⟩ (le_refl _), Function.update_eq_self]
    | succ r ihr =>
      intro j hj
      have hjq : j < q := by omega
      rw [show (r + 1) * (f2_catalogPolyCost q C i + 2) + q + 2 =
          (f2_catalogPolyCost q C i + 2) + (r * (f2_catalogPolyCost q C i + 2) + q + 2) by ring,
        MultiTapeTM.runFrom_add, hbody j hjq]
      have hr := ihr (o ++ List.replicate (C * q ^ i) true) (j + 1) (by omega)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      rw [hr, List.append_assoc, ← List.replicate_add]
      congr 3
      ring

/-- Writing at the first blank extends a unary tape by exactly one cell. -/
private lemma f2_catalogPolyTape_write (q : ℕ) :
    Function.update (f2_catalogPolyTape q) (q : ℤ) (some true) = f2_catalogPolyTape (q + 1) := by
  funext z
  by_cases hz : z = (q : ℤ)
  · subst z
    simp [f2_catalogPolyTape]
  · rw [Function.update_of_ne hz]
    unfold f2_catalogPolyTape
    have he : (0 ≤ z ∧ z < (q : ℤ)) ↔ (0 ≤ z ∧ z < ((q + 1 : ℕ) : ℤ)) := by omega
    simp only [he]

/-- The full loop costs at most a constant times the number of box points.
Each level's rewinds are charged to its `q` completed body iterations. -/
private lemma f2_catalogPolyCost_le (q C : ℕ) (hq : 0 < q) : ∀ r,
    f2_catalogPolyCost q C r ≤ (C + 1 + 5 * r) * q ^ r := by
  intro r
  induction r with
  | zero => simp [f2_catalogPolyCost]
  | succ r ih =>
    have hqpow : q ≤ q ^ (r + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hq (show 1 ≤ r + 1 by omega)
    have hpos : 1 ≤ q ^ (r + 1) := Nat.one_le_pow _ _ hq
    calc
      f2_catalogPolyCost q C (r + 1) = q * (f2_catalogPolyCost q C r + 2) + q + 2 := rfl
      _ ≤ q * ((C + 1 + 5 * r) * q ^ r + 2) + q + 2 :=
        Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left q (Nat.add_le_add_right ih 2)) q) 2
      _ = (C + 1 + 5 * r) * q ^ (r + 1) + 3 * q + 2 := by rw [Nat.pow_succ]; ring
      _ ≤ (C + 1 + 5 * r) * q ^ (r + 1) + 5 * q ^ (r + 1) := by omega
      _ = (C + 1 + 5 * (r + 1)) * q ^ (r + 1) := by ring

/-- Configurations while copying the input length to every unary loop tape. -/
private def f2_catalogPolyCopyCfg (c C : ℕ) (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (c + 1) Bool (f2_CatalogPolyControl c C) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩, fun _ => f2_catalogPolyTape i, fun _ => i, []⟩

/-- One input scan copies its length, in unary, onto every loop tape at once. -/
private lemma f2_catalogPoly_copy (c C : ℕ) (x : List Bool) : ∀ i (hi : i ≤ x.length),
    (f2_catalogPolyUnaryTM c C).tm.runFrom ((f2_catalogPolyUnaryTM c C).tm.initCfg x) i =
      f2_catalogPolyCopyCfg c C x i hi := by
  intro i
  induction i with
  | zero =>
    intro hi
    apply Cfg.ext
    · rfl
    · rfl
    · funext k z
      simp [MultiTapeTM.initCfg, Cfg.init, f2_catalogPolyCopyCfg, f2_catalogPolyTape,
        show ¬(0 ≤ z ∧ z < (0 : ℤ)) by omega]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (f2_catalogPolyCopyCfg c C x i (by omega)).inputSymbol = some x[i] :=
      inputSymbolInner i (by simp [f2_catalogPolyCopyCfg, Nat.add_comm]) (by omega)
    unfold MultiTapeTM.step
    change ((f2_catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 1 + 1
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    · funext k
      exact f2_catalogPolyTape_write i
    · funext k
      simp [f2_catalogPolyUnaryTM, f2_catalogPolyCopyCfg, Action.apply, Nat.add_comm]
    · rfl

/-- The startup rewind moves all synchronized heads left, then enters the outermost loop. -/
private lemma f2_catalogPoly_setup (c C : ℕ) (x : List Bool) (q : ℕ) : ∀ j (_hj : j ≤ q),
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) []) (j + 1) =
      f2_catalogPolyCfg x q (.loop (Fin.last c)) (fun _ => 0) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Cfg.workTapeSymbols, f2_catalogPolyTape, Action.apply]
  | succ j ih =>
    intro hj
    have hs : (f2_catalogPolyUnaryTM c C).tm.step
        (f2_catalogPolyCfg x q .setup (fun _ => ((j + 1 : ℕ) : ℤ) - 1) []) =
        f2_catalogPolyCfg x q .setup (fun _ => (j : ℤ) - 1) [] := by
      apply Cfg.ext <;>
        simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Cfg.workTapeSymbols, f2_catalogPolyTape,
          show (j : ℤ) < q by omega, Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Startup installs side length `|x|+1` and puts every loop head at zero.
The final extra unary cell handles empty input without a special case. -/
private lemma f2_catalogPoly_start (c C : ℕ) (x : List Bool) :
    (f2_catalogPolyUnaryTM c C).tm.runFrom ((f2_catalogPolyUnaryTM c C).tm.initCfg x)
      (2 * (x.length + 1)) =
      f2_catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [] := by
  have hs : (f2_catalogPolyUnaryTM c C).tm.step
      (f2_catalogPolyCopyCfg c C x x.length (le_refl _)) =
      f2_catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    have hin : (f2_catalogPolyCopyCfg c C x x.length (le_refl _)).inputSymbol = none := by
      simp [f2_catalogPolyCopyCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change ((f2_catalogPolyUnaryTM c C).tm.tr .copy _ _).apply _ = _
    rw [hin]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · funext k
      exact f2_catalogPolyTape_write x.length
    · funext k
      simp [f2_catalogPolyUnaryTM, f2_catalogPolyCopyCfg, f2_catalogPolyCfg, Action.apply, sub_eq_add_neg]
    · rfl
  have hpre : (f2_catalogPolyUnaryTM c C).tm.runFrom ((f2_catalogPolyUnaryTM c C).tm.initCfg x)
      (x.length + 1) =
      f2_catalogPolyCfg x (x.length + 1) .setup (fun _ => (x.length : ℤ) - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_catalogPoly_copy c C x x.length (le_refl _), hs]
  rw [show 2 * (x.length + 1) = (x.length + 1) + (x.length + 1) by omega,
    MultiTapeTM.runFrom_add, hpre]
  exact f2_catalogPoly_setup c C x (x.length + 1) x.length (by omega)

/-- The explicit generator computes the exact unary catalogPolynomial in linear time
in its number of box points. This includes coefficient zero and empty input.

**Proof sketch.** Startup costs `2(n+1)`. The full outer loop emits
`C(n+1)^(c+1)` symbols and costs at most `(C+1+5(c+1))(n+1)^(c+1)`.
One final transition halts; `n+1 ≤ (n+1)^(c+1)` absorbs startup. -/
private lemma f2_catalogPoly_unary_computes (c C : ℕ) :
    (f2_catalogPolyUnaryTM c C).ComputesFunInTime
      (fun x => List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (fun n => (C + 5 * (c + 1) + 4) * (n + 1) ^ (c + 1)) := by
  intro x
  have hl := f2_catalogPoly_loop (c := c) (C := C) x (x.length + 1) (Nat.succ_pos _) c (by omega)
    (fun _ => 0) (by simp) [] (x.length + 1) 0 (by omega)
  have hout : (x.length + 1) * (C * (x.length + 1) ^ c) =
      C * (x.length + 1) ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg x (x.length + 1) (.loop (Fin.last c)) (fun _ => 0) [])
      (f2_catalogPolyCost (x.length + 1) C (c + 1)) =
      f2_catalogPolyCfg x (x.length + 1) (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * (x.length + 1) ^ (c + 1)) true) := by
    simpa [f2_catalogPolyCost, hout] using hl
  have hbase : (f2_catalogPolyUnaryTM c C).ComputesInTime x
      (List.replicate (C * (x.length + 1) ^ (c + 1)) true)
      (2 * (x.length + 1) + f2_catalogPolyCost (x.length + 1) C (c + 1) + 1) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, f2_catalogPoly_start, hloop]
    simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, f2_catalogPolyCfg, Action.apply]
  apply hbase.mono
  have hp : x.length + 1 ≤ (x.length + 1) ^ (c + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
      (show 1 ≤ c + 1 by omega)
  have hpos : 1 ≤ (x.length + 1) ^ (c + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc
    _ ≤ 2 * (x.length + 1) +
        (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left
        (f2_catalogPolyCost_le (x.length + 1) C (Nat.succ_pos _) (c + 1)) _) 1
    _ ≤ (C + 1 + 5 * (c + 1)) * (x.length + 1) ^ (c + 1) +
        3 * (x.length + 1) ^ (c + 1) := by omega
    _ = _ := by ring



/-- After initialization each loop bank remains a fixed unary interval. The
active loop head may scan its right blank; the active rewind head may scan its
left blank; all other active indices stay strictly inside the installed bank. -/
private def f2_polyHeads {d C : ℕ} (q : ℕ)
    (s : Option (f2_CatalogPolyControl d C)) (h : Fin (d + 1) → ℤ) : Prop :=
  match s with
  | none => ∀ j, -1 ≤ h j ∧ h j ≤ q
  | some (.loop i) => ∀ j, 0 ≤ h j ∧ h j ≤ q ∧ (j ≠ i → h j < q)
  | some (.rewind i) => ∀ j, -1 ≤ h j ∧ h j < q ∧ (j ≠ i → 0 ≤ h j)
  | some (.advance _) | some (.emit _) => ∀ j, 0 ≤ h j ∧ h j < q
  | _ => False

/-- The loop-phase invariant implies the common closed head interval. -/
private lemma f2_polyHeads_bounds {d C q : ℕ}
    {s : Option (f2_CatalogPolyControl d C)} {h : Fin (d + 1) → ℤ}
    (hp : f2_polyHeads q s h) (j : Fin (d + 1)) :
    -1 ≤ h j ∧ h j ≤ q := by
  cases s with
  | none => exact hp j
  | some s =>
    cases s <;> simp only [f2_polyHeads] at hp
    all_goals first | contradiction | (have := hp j; omega)

/-- The nested-loop transitions preserve the installed unary words and the
phase-specific head intervals, independently of output length or round count.
**Proof sketch.** Only initialization writes. A loop's right move can reach its
right blank but no farther; a rewind turns on the left blank at minus one.
Advance changes one index, and emission changes no work head. -/
private lemma f2_poly_step {d C q : ℕ} {x : List Bool} (hq : 0 < q)
    (c : Cfg (d + 1) Bool (f2_CatalogPolyControl d C) x)
    (hw : c.workTapes = fun _ => f2_catalogPolyTape q)
    (hp : f2_polyHeads q c.state c.workTapePos) :
    ((f2_catalogPolyUnaryTM d C).tm.step c).workTapes =
        (fun _ => f2_catalogPolyTape q) ∧
      f2_polyHeads q ((f2_catalogPolyUnaryTM d C).tm.step c).state
        ((f2_catalogPolyUnaryTM d C).tm.step c).workTapePos := by
  have hr (i : Fin (d + 1)) : c.workTapeSymbols i =
      if 0 ≤ c.workTapePos i ∧ c.workTapePos i < q then some true else none := by
    simp only [Cfg.workTapeSymbols, hw, f2_catalogPolyTape]
  cases hs : c.state with
  | none => simpa only [MultiTapeTM.step, hs] using And.intro hw hp
  | some s =>
    simp only [hs] at hp
    cases s with
    | copy => exact False.elim hp
    | setup => exact False.elim hp
    | loop i =>
      dsimp only [f2_polyHeads] at hp
      by_cases hblank : c.workTapeSymbols i = none
      · constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            ↓reduceIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = i
          · subst j
            simp only [↓reduceIte, SignType.cast]
            omega
          · simp only [he, ↓reduceIte, SignType.cast]
            have := hj.2.2 he
            omega
      · have hi : c.workTapePos i < q := by
          rw [hr] at hblank
          split at hblank <;> simp_all
        have hall (j : Fin (d + 1)) : 0 ≤ c.workTapePos j ∧ c.workTapePos j < q := by
          have hj := hp j
          by_cases he : j = i
          · simpa [he] using And.intro (hp i).1 hi
          · exact ⟨hj.1, hj.2.2 he⟩
        constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank, ↓reduceIte,
            Action.apply]
          split <;> simp only [f2_polyHeads, SignType.cast, add_zero]
          · exact hall
          · intro j
            have := hall j
            exact ⟨this.1, le_of_lt this.2, fun _ => this.2⟩
    | rewind i =>
      dsimp only [f2_polyHeads] at hp
      by_cases hblank : c.workTapeSymbols i = none
      · have hi : c.workTapePos i = -1 := by
          have hlo := (hp i).1
          have hhi := (hp i).2.1
          rw [hr] at hblank
          have hn : ¬(0 ≤ c.workTapePos i ∧ c.workTapePos i < q) := by
            simpa only [ite_eq_right_iff, Option.some_ne_none, imp_false] using hblank
          omega
        constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            ↓reduceIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = i
          · subst j
            simp only [↓reduceIte, SignType.cast]
            omega
          · simp only [he, ↓reduceIte, SignType.cast, add_zero]
            exact ⟨hj.2.2 he, hj.2.1⟩
      · have hi : 0 ≤ c.workTapePos i := by
          rw [hr] at hblank
          split at hblank <;> simp_all
        constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hblank,
            ↓reduceIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = i
          · subst j
            simp only [↓reduceIte, SignType.cast]
            omega
          · simp only [he, ↓reduceIte, SignType.cast, add_zero]
            exact hj
    | advance i =>
      dsimp only [f2_polyHeads] at hp
      by_cases hi : i.val < d + 1
      · constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi,
            f2_catalogPolyMove, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi,
            ↓reduceDIte, f2_catalogPolyMove, Action.apply, f2_polyHeads]
          intro j
          have hj := hp j
          by_cases he : j = ⟨i.val, hi⟩
          · simp only [he, ↓reduceIte, SignType.cast]
            simp only [he] at hj
            omega
          · simp only [he, ↓reduceIte, SignType.cast, add_zero]
            exact ⟨hj.1, le_of_lt hj.2, fun _ => hj.2⟩
      · constructor
        · simpa [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi, Action.apply] using hw
        · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, hi, ↓reduceDIte,
            Action.apply, f2_polyHeads, SignType.cast, add_zero]
          intro j
          have := hp j
          omega
    | emit j =>
      constructor
      · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM]
        split <;> simpa only [Action.apply] using hw
      · simp only [MultiTapeTM.step, hs, f2_catalogPolyUnaryTM, Action.apply]
        split <;> simpa only [f2_polyHeads, SignType.cast, add_zero] using hp

/-- A work head lies within the number of elapsed steps of its starting cell.
This is a trajectory bound obtained by adding the one-step movement bounds. -/
private lemma f2_head_steps {k : ℕ} {S : Type} {x : List Bool}
    (M : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) (i : Fin k) :
    c.workTapePos i - (t : ℤ) ≤ (M.runFrom c t).workTapePos i ∧
      (M.runFrom c t).workTapePos i ≤ c.workTapePos i + (t : ℤ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hs := abs_le.mp (M.workTapePos_step_le (M.runFrom c t) i)
    rw [MultiTapeTM.runFrom_succ_eq_step']
    push_cast
    constructor <;> omega

/-- The generator's all-time work space is linear in the input length.
**Proof sketch.** Startup lasts `2(n+1)` steps from the origin, so its entire
trajectory fits the interval of that radius. The preserved loop invariant
confines every later head to `[-1,n+1]`, including after halt. Contain the
inclusive visited images in the larger fixed interval and sum its cardinality;
the number of loop iterations never appears in this bound. -/
private lemma f2_poly_space (d C : ℕ) (x : List Bool) (t : ℕ) :
    (f2_catalogPolyUnaryTM d C).tm.spaceUsed
      ((f2_catalogPolyUnaryTM d C).tm.initCfg x) t ≤
        (5 * (d + 1)) * (x.length + 1) := by
  let M := (f2_catalogPolyUnaryTM d C).tm
  let c := f2_catalogPolyCfg (c := d) (C := C) x (x.length + 1)
    (.loop (Fin.last d)) (fun _ => 0) []
  have hinv (u : ℕ) : (M.runFrom c u).workTapes =
      (fun _ => f2_catalogPolyTape (x.length + 1)) ∧
      f2_polyHeads (x.length + 1) (M.runFrom c u).state (M.runFrom c u).workTapePos := by
    induction u with
    | zero =>
      refine ⟨rfl, ?_⟩
      simp [c, f2_catalogPolyCfg, f2_polyHeads]
      omega
    | succ u ih =>
      rw [MultiTapeTM.runFrom_succ_eq_step']
      exact f2_poly_step (Nat.succ_pos _) _ ih.1 ih.2
  have hpos (u : ℕ) (i : Fin (d + 1)) :
      -(2 * (x.length + 1) : ℤ) ≤ (M.runFrom (M.initCfg x) u).workTapePos i ∧
        (M.runFrom (M.initCfg x) u).workTapePos i ≤ (2 * (x.length + 1) : ℤ) := by
    by_cases hu : u ≤ 2 * (x.length + 1)
    · have h := f2_head_steps M (M.initCfg x) u i
      change 0 - (u : ℤ) ≤ _ ∧ _ ≤ 0 + (u : ℤ) at h
      constructor <;> omega
    · rw [show u = 2 * (x.length + 1) + (u - 2 * (x.length + 1)) by omega,
        MultiTapeTM.runFrom_add, f2_catalogPoly_start]
      have h := f2_polyHeads_bounds (hinv (u - 2 * (x.length + 1))).2 i
      dsimp only [c, M] at h
      constructor <;> omega
  have hcard (i : Fin (d + 1)) : M.spaceUsedByTape (M.initCfg x) t i ≤
      5 * (x.length + 1) := by
    have hsub : M.visitedByTapeHead (M.initCfg x) t i ⊆
        Finset.Icc (-(2 * (x.length + 1) : ℤ)) (2 * (x.length + 1) : ℤ) := by
      intro z hz
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (hpos u i)
    exact (Finset.card_le_card hsub).trans (by rw [Int.card_Icc]; omega)
  change M.spaceUsed (M.initCfg x) t ≤ _
  unfold MultiTapeTM.spaceUsed
  calc
    _ ≤ ∑ _i : Fin (d + 1), 5 * (x.length + 1) :=
      Finset.sum_le_sum (fun i _ => hcard i)
    _ = _ := by simp; ring

/-- Increment a little-endian binary word, extending it on overflow. -/
private def f2_counterInc : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: f2_counterInc bs

/-- The number of initial true bits cleared by an increment. -/
private def f2_counterCarry : List Bool → ℕ
  | true :: bs => f2_counterCarry bs + 1
  | _ => 0

/-- Each cleared true bit decreases the potential by one; the final write adds one.
This is the local accounting identity behind the amortized bound. -/
private lemma f2_counterInc_potential (bs : List Bool) :
    (f2_counterInc bs).count true + f2_counterCarry bs = bs.count true + 1 := by
  induction bs with
  | nil => simp [f2_counterInc, f2_counterCarry]
  | cons b bs ih =>
    cases b with
    | false => simp [f2_counterInc, f2_counterCarry]
    | true => simp [f2_counterInc, f2_counterCarry]; omega

/-- The list increment is exactly successor in `Nat.bits`, including overflow.
**Proof sketch.** Binary induction: a low zero becomes one without a carry; a
low one becomes zero and applies the induction hypothesis to the high part. -/
private lemma f2_counterInc_bits (n : ℕ) : f2_counterInc n.bits = (n + 1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [f2_counterInc]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false =>
      change true :: n.bits = (2 * n + 1).bits
      exact (Nat.bit1_bits n).symm
    | true =>
      simp only [f2_counterInc, ih]
      have he : Nat.bit true n + 1 = 2 * (n + 1) := by simp [Nat.bit_val]; omega
      rw [he, Nat.bit0_bits _ (by omega)]

/-- An increment grows the word by at most one cell, and all cleared cells lie
within the incremented word. -/
private lemma f2_counterInc_length (bs : List Bool) :
    (f2_counterInc bs).length ≤ bs.length + 1 ∧
      f2_counterCarry bs ≤ (f2_counterInc bs).length := by
  induction bs with
  | nil => simp [f2_counterInc, f2_counterCarry]
  | cons b bs ih =>
    cases b <;> simp only [f2_counterInc, f2_counterCarry, List.length_cons] <;> omega

/-- One carry transition, with the first transition also advancing the input. -/
private def f2_counterBump (d : SignType) (w : Option Bool) : Action 1 Bool (Fin 4) :=
  if w = some true then
    ⟨d, fun _ => (some (some false), .pos), none, some 1⟩
  else ⟨d, fun _ => (some (some true), .neg), none, some 2⟩

/-- The audit's four-state counter: count = 0, carry = 1, rewind = 2, emit = 3.
[AB09, §1.3 examples], implemented by the phase-1 reaudit's transition table. -/
private def f2_counterTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm :=
    { q₀ := 0
      tr := fun q inp work =>
        if q = 0 then
          match inp with
          | none => ⟨.zero, fun _ => (none, .zero), none, some 3⟩
          | some _ => f2_counterBump .pos (work 0)
        else if q = 1 then f2_counterBump .zero (work 0)
        else if q = 2 then
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .pos), none, some 0⟩
          | some _ => ⟨.zero, fun _ => (none, .neg), none, some 2⟩
        else
          match work 0 with
          | none => ⟨.zero, fun _ => (none, .zero), none, none⟩
          | some b => ⟨.zero, fun _ => (none, .pos), some b, some 3⟩ }

/-- A finite word on nonnegative cells, with a blank at every other cell. -/
private def f2_counterTape (bs : List Bool) (z : ℤ) : Option Bool :=
  if z < 0 then none else bs[z.toNat]?

/-- Canonical configurations for carry, rewind, count, and emission invariants. -/
private def f2_counterCfg (x : List Bool) (q : Fin 4) (p : Fin (x.length + 2))
    (z : ℤ) (bs out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨some q, p, fun _ => f2_counterTape bs, fun _ => z, out⟩

/-- Reading after a prefix gives the head of the remaining word (blank if empty). -/
private lemma f2_counterTape_read (pre bs : List Bool) :
    f2_counterTape (pre ++ bs) pre.length = bs.head? := by
  simp only [f2_counterTape, if_neg (by omega : ¬(pre.length : ℤ) < 0), Int.toNat_natCast,
    List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Replace the first suffix bit, or extend the word if the suffix is empty.
**Proof sketch.** At the write position use the updated value. Before that
position both tapes read the unchanged prefix; afterwards both read the old tail.
Negative cells remain blank. -/
private lemma f2_counterTape_write (pre bs : List Bool) (b : Bool) :
    Function.update (f2_counterTape (pre ++ bs)) (pre.length : ℤ) (some b) =
      f2_counterTape (pre ++ b :: bs.tail) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z
    simp [f2_counterTape_read]
  · rw [Function.update_of_ne hz]
    unfold f2_counterTape
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
private lemma f2_counter_carry_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    f2_counterTM.tm.step (f2_counterCfg x 1 p pre.length (pre ++ bs) []) =
      if bs.head? = some true then
        f2_counterCfg x 1 p (pre.length + 1) (pre ++ false :: bs.tail) []
      else f2_counterCfg x 2 p (pre.length - 1) (pre ++ true :: bs.tail) [] := by
  unfold MultiTapeTM.step
  change (f2_counterTM.tm.tr (1 : Fin 4) _ _).apply _ = _
  simp only [f2_counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (f2_counterBump .zero (f2_counterTape (pre ++ bs) pre.length)).apply _ = _
  rw [f2_counterTape_read]
  unfold f2_counterBump
  by_cases h : bs.head? = some true <;> simp only [h, ↓reduceIte]
  all_goals
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext j; exact f2_counterTape_write pre bs _
    · funext j; simp [Action.apply, f2_counterCfg, sub_eq_add_neg]
    · rfl

/-- A carry flips precisely the initial true bits, then writes the final true bit.
**Proof sketch.** Induct on the suffix. The empty suffix and a leading false bit
finish in one step. A leading true bit is replaced by false and included in the
prefix before invoking the induction hypothesis on the tail. -/
private lemma f2_counter_carry (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ pre : List Bool,
    f2_counterTM.tm.runFrom (f2_counterCfg x 1 p pre.length (pre ++ bs) [])
        (f2_counterCarry bs + 1) =
      f2_counterCfg x 2 p ((pre.length : ℤ) + f2_counterCarry bs - 1)
        (pre ++ f2_counterInc bs) [] := by
  induction bs with
  | nil =>
    intro pre
    simp only [f2_counterCarry, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero, f2_counter_carry_step]
    simp [f2_counterInc]
  | cons b bs ih =>
    intro pre
    cases b with
    | false =>
      simp only [f2_counterCarry, MultiTapeTM.runFrom_succ_eq_step,
        MultiTapeTM.runFrom_zero, f2_counter_carry_step]
      simp [f2_counterInc]
    | true =>
      simp only [f2_counterCarry, MultiTapeTM.runFrom_succ_eq_step, f2_counter_carry_step,
        List.head?_cons, List.tail_cons, ↓reduceIte]
      have h := ih (pre ++ [false])
      rw [MultiTapeTM.runFrom_succ_eq_step] at h
      simpa [f2_counterInc, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using h

/-- Rewind crosses the written prefix, detects the untouched blank at `-1`, and
returns to cell zero in the count state.
**Proof sketch.** Induct on the number of written cells still to cross.
Each bit causes one left move; at `-1` one right move ends the rewind. -/
private lemma f2_counter_rewind (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ j (_hj : j ≤ bs.length),
    f2_counterTM.tm.runFrom (f2_counterCfg x 2 p ((j : ℤ) - 1) bs []) (j + 1) =
      f2_counterCfg x 0 p 0 bs [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply Cfg.ext <;>
      simp [MultiTapeTM.step, f2_counterTM, f2_counterCfg, Cfg.workTapeSymbols,
        f2_counterTape, Action.apply]
  | succ j ih =>
    intro hj
    have hw : (f2_counterCfg x 2 p (j : ℤ) bs []).workTapeSymbols 0 = some bs[j] := by
      simp only [f2_counterCfg, Cfg.workTapeSymbols, f2_counterTape,
        if_neg (by omega : ¬(j : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    have hs : f2_counterTM.tm.step (f2_counterCfg x 2 p (j : ℤ) bs []) =
        f2_counterCfg x 2 p ((j : ℤ) - 1) bs [] := by
      unfold MultiTapeTM.step
      change (f2_counterTM.tm.tr (2 : Fin 4) _ _).apply _ = _
      simp only [f2_counterTM, show (2 : Fin 4) ≠ 0 from by decide,
        show (2 : Fin 4) ≠ 1 from by decide, ↓reduceIte, hw]
      apply Cfg.ext
      · rfl
      · exact moveInputPos_zero p
      · rfl
      · funext k; simp [Action.apply, f2_counterCfg, sub_eq_add_neg]
      · rfl
    have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
    rw [he, MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The first carry transition also consumes exactly one input symbol. -/
private lemma f2_counter_start (x : List Bool) (i : ℕ) (hi : i < x.length) (bs : List Bool) :
    f2_counterTM.tm.step (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []) =
      f2_counterTM.tm.step (f2_counterCfg x 1 ⟨i + 2, by omega⟩ 0 bs []) := by
  have hs : (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs []).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [f2_counterCfg]; omega) hi
  unfold MultiTapeTM.step
  change (f2_counterTM.tm.tr (0 : Fin 4) _ _).apply _ =
    (f2_counterTM.tm.tr (1 : Fin 4) _ _).apply _
  rw [hs]
  simp only [f2_counterTM, show (1 : Fin 4) ≠ 0 from by decide, ↓reduceIte]
  change (f2_counterBump .pos (f2_counterTape bs 0)).apply _ =
    (f2_counterBump .zero (f2_counterTape bs 0)).apply _
  unfold f2_counterBump
  by_cases h : f2_counterTape bs 0 = some true <;> simp only [h, ↓reduceIte]
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
private lemma f2_counter_increment (x : List Bool) (i : ℕ) (hi : i < x.length)
    (bs : List Bool) :
    f2_counterTM.tm.runFrom (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
        (2 * f2_counterCarry bs + 2) =
      f2_counterCfg x 0 ⟨i + 2, by omega⟩ 0 (f2_counterInc bs) [] := by
  have hc : f2_counterTM.tm.runFrom (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 bs [])
      (f2_counterCarry bs + 1) =
      f2_counterCfg x 2 ⟨i + 2, by omega⟩ ((f2_counterCarry bs : ℤ) - 1) (f2_counterInc bs) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step, f2_counter_start x i hi,
      ← MultiTapeTM.runFrom_succ_eq_step]
    simpa only [List.length_nil, Nat.cast_zero, zero_add, List.nil_append] using
      f2_counter_carry x ⟨i + 2, by omega⟩ bs []
  rw [show 2 * f2_counterCarry bs + 2 = (f2_counterCarry bs + 1) + (f2_counterCarry bs + 1) by omega,
    MultiTapeTM.runFrom_add, hc]
  exact f2_counter_rewind x ⟨i + 2, by omega⟩ (f2_counterInc bs) (f2_counterCarry bs)
    (f2_counterInc_length bs).2

/-- The counting invariant carries a nonnegative potential of twice the popcount.
**Proof sketch.** Initially both elapsed time and potential are zero. An increment
with `r` cleared bits costs `2r + 2` steps and changes the potential by `2 - 2r`.
Thus elapsed time plus potential increases by exactly four per input symbol.
The semantic invariant records the exact canonical binary word and head positions. -/
private lemma f2_counter_count (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) t =
        f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_⟩
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp [MultiTapeTM.initCfg, f2_counterCfg, f2_counterTape]
    · rfl
    · rfl
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc⟩ := ih (by omega)
    refine ⟨t + 2 * f2_counterCarry i.bits + 2, ?_, ?_⟩
    · have hp := f2_counterInc_potential i.bits
      rw [f2_counterInc_bits] at hp
      omega
    · rw [show t + 2 * f2_counterCarry i.bits + 2 = t + (2 * f2_counterCarry i.bits + 2) by omega,
        MultiTapeTM.runFrom_add, hc, f2_counter_increment x i (by omega), f2_counterInc_bits]

/-- The emit phase appends exactly the stored prefix, one bit per step.
**Proof sketch.** Induct on the emitted length, using the nonblank cell at each
index below the word length; the tape contents and input position never change. -/
private lemma f2_counter_emit_run (x : List Bool) (p : Fin (x.length + 2))
    (bs : List Bool) : ∀ i (_hi : i ≤ bs.length),
    f2_counterTM.tm.runFrom (f2_counterCfg x 3 p 0 bs []) i =
      f2_counterCfg x 3 p i bs (bs.take i) := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (f2_counterCfg x 3 p i bs (bs.take i)).workTapeSymbols 0 = some bs[i] := by
      simp only [f2_counterCfg, Cfg.workTapeSymbols, f2_counterTape,
        if_neg (by omega : ¬(i : ℤ) < 0), Int.toNat_natCast]
      exact List.getElem?_eq_getElem (by omega)
    unfold MultiTapeTM.step
    change (f2_counterTM.tm.tr (3 : Fin 4) _ _).apply _ = _
    simp only [f2_counterTM, show (3 : Fin 4) ≠ 0 from by decide,
      show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
      ↓reduceIte, hw]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · rfl
    · funext j; simp [Action.apply, f2_counterCfg]
    · simp only [Action.apply, f2_counterCfg]
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]

/-- At the first blank after the stored word, emission halts without extra output. -/
private lemma f2_counter_emit (x : List Bool) (p : Fin (x.length + 2)) (bs : List Bool) :
    let c := f2_counterTM.tm.runFrom (f2_counterCfg x 3 p 0 bs []) (bs.length + 1)
    c.state = none ∧ c.output = bs := by
  have hw : (f2_counterCfg x 3 p bs.length bs (bs.take bs.length)).workTapeSymbols 0 =
      none := by
    simp only [f2_counterCfg, Cfg.workTapeSymbols, f2_counterTape,
      if_neg (by omega : ¬(bs.length : ℤ) < 0), Int.toNat_natCast]
    exact List.getElem?_eq_none (le_refl _)
  dsimp only
  rw [MultiTapeTM.runFrom_succ_eq_step', f2_counter_emit_run x p bs bs.length (le_refl _)]
  unfold MultiTapeTM.step
  change ((f2_counterTM.tm.tr (3 : Fin 4) _ _).apply _).state = none ∧ _
  simp only [f2_counterTM, show (3 : Fin 4) ≠ 0 from by decide,
    show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    ↓reduceIte, hw]
  simp [Action.apply, f2_counterCfg]

/-- The direct variable-width counter outputs the input length in at most
five times one plus that length. Its complete time proof is copied from the
explicit counter construction in ClassP/TimeConstructible.lean; no existential
witness or sharp space property of timeConstructible_id is assumed. -/
private lemma f2_counter_computes : f2_counterTM.ComputesFunInTime
    (fun x => Nat.bits x.length) (fun n => 5 * (n + 1)) := by
  intro x
  obtain ⟨t, ht, hc⟩ := f2_counter_count x x.length (le_refl _)
  have hs : f2_counterTM.tm.step
      (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) =
      f2_counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    have hin : (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol =
        none := by simp [Cfg.inputSymbol, f2_counterCfg]
    unfold MultiTapeTM.step
    change (f2_counterTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [f2_counterTM, Action.apply, f2_counterCfg]
  have hstart : f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) (t + 1) =
      f2_counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hs]
  have he := f2_counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits
  have hbase : f2_counterTM.ComputesInTime x x.length.bits
      ((t + 1) + (x.length.bits.length + 1)) := by
    refine ⟨_, ?_, ?_, rfl⟩
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.1
    · rw [MultiTapeTM.runFrom_add, hstart]; exact he.2
  apply hbase.mono
  have hl := Turing.length_bits_le_self x.length
  change (t + 1) + (x.length.bits.length + 1) ≤ 5 * (x.length + 1)
  omega

/-- The counting invariant also covers every suspended increment's head
trajectory. Each increment returns to the origin, and its carry length is
bounded by the final input length's binary width.
**Proof sketch.** Reuse the exact `2*carry+2` increment ledger and popcount
potential. Split each prefix at the preceding return; in the current increment
apply the unit-step trajectory bound from the origin. Binary width is monotone. -/
private lemma f2_counter_count_space (x : List Bool) : ∀ i (hi : i ≤ x.length),
    ∃ t, t + 2 * i.bits.count true ≤ 4 * i ∧
      f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) t =
        f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits [] ∧
      ∀ u ≤ t, ∀ j : Fin 1,
        -(2 * (Nat.size x.length + 1) : ℤ) ≤
          (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ∧
        (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ≤
          (2 * (Nat.size x.length + 1) : ℤ) := by
  intro i
  induction i with
  | zero =>
    intro hi
    refine ⟨0, by simp, ?_, ?_⟩
    · apply Cfg.ext
      · rfl
      · rfl
      · funext j z
        simp [MultiTapeTM.initCfg, f2_counterCfg, f2_counterTape]
      · rfl
      · rfl
    · intro u hu j
      have : u = 0 := by omega
      subst u
      simp [MultiTapeTM.initCfg, Cfg.init]
      omega
  | succ i ih =>
    intro hi
    obtain ⟨t, ht, hc, hb⟩ := ih (by omega)
    refine ⟨t + (2 * f2_counterCarry i.bits + 2), ?_, ?_, ?_⟩
    · have hp := f2_counterInc_potential i.bits
      rw [f2_counterInc_bits] at hp
      omega
    · rw [MultiTapeTM.runFrom_add, hc,
        f2_counter_increment x i (by omega), f2_counterInc_bits]
    · intro u hu j
      by_cases hut : u ≤ t
      · exact hb u hut j
      · rw [show u = t + (u - t) by omega, MultiTapeTM.runFrom_add, hc]
        have hp := f2_head_steps f2_counterTM.tm
          (f2_counterCfg x 0 ⟨i + 1, by omega⟩ 0 i.bits []) (u - t) j
        have hcarry := (f2_counterInc_length i.bits).2
        rw [f2_counterInc_bits, Nat.size_eq_bits_len] at hcarry
        have hwidth := Nat.size_le_size hi
        change 0 - ((u - t : ℕ) : ℤ) ≤ _ ∧ _ ≤ 0 + ((u - t : ℕ) : ℤ) at hp
        constructor <;> omega

/-- All prefixes of the direct counter, including its stationary halted tail,
fit a fixed interval whose radius is twice one plus the final binary width.
Counting rounds return their heads to zero; final emission traverses just the
stored binary word. -/
private lemma f2_counter_heads (x : List Bool) (u : ℕ) (j : Fin 1) :
    -(2 * (Nat.size x.length + 1) : ℤ) ≤
      (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ∧
    (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) u).workTapePos j ≤
      (2 * (Nat.size x.length + 1) : ℤ) := by
  obtain ⟨t, _, hc, hb⟩ := f2_counter_count_space x x.length (le_refl _)
  let c := f2_counterCfg x 3 ⟨x.length + 1, by omega⟩ 0 x.length.bits []
  have hs : f2_counterTM.tm.step
      (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []) = c := by
    have hin : (f2_counterCfg x 0 ⟨x.length + 1, by omega⟩ 0 x.length.bits []).inputSymbol =
        none := by simp [Cfg.inputSymbol, f2_counterCfg]
    unfold MultiTapeTM.step
    change (f2_counterTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [c, f2_counterTM, Action.apply, f2_counterCfg]
  have hstart : f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) (t + 1) = c := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hc, hs]
  let T := t + 1 + (x.length.bits.length + 1)
  have hhalt : (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) T).state = none := by
    rw [show T = (t + 1) + (x.length.bits.length + 1) from rfl,
      MultiTapeTM.runFrom_add, hstart]
    exact (f2_counter_emit x ⟨x.length + 1, by omega⟩ x.length.bits).1
  have hpre (v : ℕ) (hv : v ≤ T) :
      -(2 * (Nat.size x.length + 1) : ℤ) ≤
        (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) v).workTapePos j ∧
      (f2_counterTM.tm.runFrom (f2_counterTM.tm.initCfg x) v).workTapePos j ≤
        (2 * (Nat.size x.length + 1) : ℤ) := by
    by_cases hvt : v ≤ t
    · exact hb v hvt j
    · rw [show v = (t + 1) + (v - (t + 1)) by omega,
        MultiTapeTM.runFrom_add, hstart]
      have hp := f2_head_steps f2_counterTM.tm c (v - (t + 1)) j
      change 0 - ((v - (t + 1) : ℕ) : ℤ) ≤ _ ∧ _ ≤ 0 + ((v - (t + 1) : ℕ) : ℤ) at hp
      have hlen := Nat.size_eq_bits_len x.length
      dsimp only [T] at hv
      constructor <;> omega
  by_cases hu : u ≤ T
  · exact hpre u hu
  · rw [show u = T + (u - T) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hhalt]
    exact hpre T (le_refl _)

/-- Taking the cardinality of the counter's inclusive trajectory interval
and summing over its single tape gives a logarithmic all-time space bound. -/
private lemma f2_counter_space (x : List Bool) (t : ℕ) :
    f2_counterTM.tm.spaceUsed (f2_counterTM.tm.initCfg x) t ≤
      5 * (Nat.size x.length + 1) := by
  have hcard (j : Fin 1) :
      f2_counterTM.tm.spaceUsedByTape (f2_counterTM.tm.initCfg x) t j ≤
        5 * (Nat.size x.length + 1) := by
    have hsub : f2_counterTM.tm.visitedByTapeHead (f2_counterTM.tm.initCfg x) t j ⊆
        Finset.Icc (-(2 * (Nat.size x.length + 1) : ℤ))
          (2 * (Nat.size x.length + 1) : ℤ) := by
      intro z hz
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (f2_counter_heads x u j)
    exact (Finset.card_le_card hsub).trans (by rw [Int.card_Icc]; omega)
  simpa [MultiTapeTM.spaceUsed] using hcard 0

/-- Administrative actions for the captured length checker move only the
input and final (countdown) head. No tape is written. -/
private def f2_lenAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option (M.State ⊕ (Fin 4 ⊕ Option Bool))) :
    Action (M.k + 1) Bool (M.State ⊕ (Fin 4 ⊕ Option Bool)) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q⟩

/-- Capture a total generator, rewind the physical input, validate its pair
syntax, then compare the suffix length with the captured word's length.
Only the final comparison or rejection transition emits a verdict. -/
private def f2_pairCountTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ (Fin 4 ⊕ Option Bool)
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
      | .inl s => captureAction Sum.inl (.inr (.inl 0))
          (M.tm.tr s inp fun i => work i.castSucc)
      | .inr (.inl q) => match q.val with
        | 0 => f2_lenAction M 0 .neg none (some (.inr (.inl 1)))
        | 1 => controlAction .neg (some (.inr (.inl 2)))
        | 2 => match inp with
          | some _ => controlAction .neg (some (.inr (.inl 2)))
          | none => controlAction .pos (some (.inr (.inr none)))
        | _ => match inp with
          | none => f2_lenAction M 0 0 (some true) none
          | some _ => match work (Fin.last M.k) with
            | none => f2_lenAction M 0 0 (some false) none
            | some _ => f2_lenAction M .pos .neg none (some (.inr (.inl 3)))
      | .inr (.inr none) => match inp with
        | none => f2_lenAction M 0 0 (some false) none
        | some b => f2_lenAction M .pos 0 none (some (.inr (.inr (some b))))
      | .inr (.inr (some b)) => match inp with
        | none => f2_lenAction M 0 0 (some false) none
        | some d => if b = d then f2_lenAction M .pos 0 none (some (.inr (.inr none)))
          else if b then f2_lenAction M 0 0 (some false) none
          else f2_lenAction M .pos 0 none (some (.inr (.inl 3))) }

/-- Checker configurations retain the completed generator bank and its
captured output; `r` is the number of still available countdown cells. -/
private def f2_lenCfg (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (f2_pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    Cfg (M.k + 1) Bool (f2_pairCountTM M).State x :=
  { captureCfg (fun s : M.State => (Sum.inl s : (f2_pairCountTM M).State))
      (.inr (.inl 0)) [] [] c with
    state := q
    inputPos := ⟨i + 1, by omega⟩
    workTapePos := fun j => if h : j.val < M.k then c.workTapePos ⟨j, h⟩
      else (r : ℤ) - 1 }

/-- The checker's input read is independent of the saved generator bank. -/
private lemma f2_lenCfg_read (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : Option (f2_pairCountTM M).State) (i : ℕ) (hi : i ≤ x.length) (r : ℕ) :
    (f2_lenCfg M c q i hi r).inputSymbol = x[i]? :=
  inputSymbol_at _ i hi rfl

/-- A stationary or forward administrative action preserves all work tapes;
its last-head movement subtracts one precisely when consuming a cell. -/
private lemma f2_lenAction_apply (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (q q' : Option (f2_pairCountTM M).State)
    (i j r s : ℕ) (hi : i ≤ x.length) (hj : j ≤ x.length)
    (m d : SignType) (b : Option Bool)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨j + 1, by omega⟩)
    (hd : (r : ℤ) - 1 + d.cast = (s : ℤ) - 1) :
    (f2_lenAction M m d b q').apply (f2_lenCfg M c q i hi r) =
      {f2_lenCfg M c q' j hj s with output := b.toList} := by
  refine Cfg.ext rfl hm ?_ ?_ rfl
  · rfl
  · funext k
    by_cases hk : k.val < M.k
    · simp [f2_lenAction, f2_lenCfg, Action.apply, hk]
    · simpa [f2_lenAction, f2_lenCfg, Action.apply, hk] using hd

/-- Suffix comparison consumes one captured cell per input bit and emits one
verdict at termination. Empty suffixes succeed even with an empty counter.
**Proof sketch.** Induct on the suffix. A zero counter rejects a nonempty
suffix immediately; otherwise one silent step decrements both lengths. -/
private lemma f2_lenSuffix_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).state = none ∧
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) r) t).output =
          [decide (rest.length ≤ r)] := by
  induction rest with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((f2_pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
    rw [f2_lenCfg_read]
    simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Action.apply]
  | cons b rest ih =>
    intro pre hx r hr
    cases r with
    | zero =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change (((f2_pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _).state = none ∧ _
      rw [f2_lenCfg_read]
      simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Cfg.workTapeSymbols,
        bufferTape_left, Action.apply]
    | succ r =>
      have hs : (f2_pairCountTM M).tm.step
          (f2_lenCfg M c (some (.inr (.inl 3))) pre.length (by simp [hx]) (r + 1)) =
          f2_lenCfg M c (some (.inr (.inl 3))) (pre.length + 1) (by simp [hx]) r := by
        unfold MultiTapeTM.step
        change ((f2_pairCountTM M).tm.tr (.inr (.inl 3)) _ _).apply _ = _
        rw [f2_lenCfg_read]
        have hin : x[pre.length]? = some b := by simp [hx]
        have hw : (f2_lenCfg M c (some (.inr (.inl 3))) pre.length
            (by simp [hx]) (r + 1)).workTapeSymbols (Fin.last M.k) =
              some (c.output[r]'(by omega)) := by
          simp [f2_lenCfg, captureCfg, Cfg.workTapeSymbols, bufferTape,
            List.getElem?_eq_getElem (by omega : r < c.output.length)]
        simp only [f2_pairCountTM, hin, hw]
        exact f2_lenAction_apply M c _ _ pre.length (pre.length + 1) (r + 1) r
          (by simp [hx]) (by simp [hx]) .pos .neg none
          (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast]; omega)
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [b]) (by simpa [List.append_assoc] using hx)
        r (by omega)
      refine ⟨1 + t, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add]
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      rw [hs]
      simpa using And.intro hh ho

/-- The first half of an aligned block changes only finite control and the
input position; countdown cells remain untouched during validation. -/
private lemma f2_lenParse_first (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b : Bool) (r : ℕ)
    (hx : x = pre ++ b :: rest) :
    (f2_pairCountTM M).tm.step
      (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) =
      f2_lenCfg M c (some (.inr (.inr (some b)))) (pre.length + 1) (by simp [hx]) r := by
  unfold MultiTapeTM.step
  change ((f2_pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _ = _
  rw [f2_lenCfg_read]
  have hin : x[pre.length]? = some b := by simp [hx]
  simp only [f2_pairCountTM, hin]
  exact f2_lenAction_apply M c _ _ pre.length (pre.length + 1) r r
    (by simp [hx]) (by simp [hx]) .pos 0 none
    (moveInputPos_pos_of_ne_right _ (by simp [hx])) (by simp [SignType.cast])

/-- Two parser steps either advance over a doubled bit, enter the suffix
comparison at `01`, or reject `10`. Nothing is emitted on a valid block. -/
private lemma f2_lenParse_block (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (pre rest : List Bool) (b d : Bool) (r : ℕ)
    (hx : x = pre ++ b :: d :: rest) :
    (f2_pairCountTM M).tm.runFrom
      (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) 2 =
      if b = d then f2_lenCfg M c (some (.inr (.inr none)))
          (pre.length + 2) (by simp [hx]) r
      else if b then {f2_lenCfg M c none (pre.length + 1) (by simp [hx]) r with output := [false]}
      else f2_lenCfg M c (some (.inr (.inl 3))) (pre.length + 2) (by simp [hx]) r := by
  change (f2_pairCountTM M).tm.step ((f2_pairCountTM M).tm.step _) = _
  rw [f2_lenParse_first M c pre (d :: rest) b r hx]
  unfold MultiTapeTM.step
  change ((f2_pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _ = _
  rw [f2_lenCfg_read]
  have hin : x[pre.length + 1]? = some d := by simp [hx]
  rw [hin]
  have hm : moveInputPos (⟨pre.length + 1 + 1, by simp [hx]⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 2 + 1, by simp [hx]; omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases d <;>
    simp only [f2_pairCountTM, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals first
    | exact f2_lenAction_apply M c _ _ (pre.length + 1) (pre.length + 2) r r
        (by simp [hx]) (by simp [hx]) .pos 0 none hm (by simp [SignType.cast])
    | exact f2_lenAction_apply M c _ _ (pre.length + 1) (pre.length + 1) r r
        (by simp [hx]) (by simp [hx]) 0 0 (some false)
        (moveInputPos_zero _) (by simp [SignType.cast])

/-- Aligned validation followed by countdown comparison decides the payload
bound in at most one more than the unread input length.
**Proof sketch.** Induct over two-bit blocks, using the existing parser's
same grammar and induction pattern. Equal-bit blocks preserve the counter;
`01` invokes suffix comparison; malformed endings and `10` reject. -/
private lemma f2_lenParse_run (M : FinTM Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) r, r ≤ c.output.length →
    ∃ t ≤ rest.length + 1,
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).state = none ∧
      ((f2_pairCountTM M).tm.runFrom
        (f2_lenCfg M c (some (.inr (.inr none))) pre.length (by simp [hx]) r) t).output =
          [match pairDecode rest with
            | some (_, b) => decide (b.length ≤ r)
            | none => false] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre hx r hr
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((f2_pairCountTM M).tm.tr (.inr (.inr none)) _ _).apply _).state = none ∧ _
    rw [f2_lenCfg_read]
    simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Action.apply, pairDecode]
  | singleton b =>
    intro pre hx r hr
    refine ⟨2, by simp, ?_⟩
    change ((f2_pairCountTM M).tm.step ((f2_pairCountTM M).tm.step _)).state = none ∧
      ((f2_pairCountTM M).tm.step ((f2_pairCountTM M).tm.step _)).output = _
    rw [f2_lenParse_first M c pre [] b r hx]
    unfold MultiTapeTM.step
    change (((f2_pairCountTM M).tm.tr (.inr (.inr (some b))) _ _).apply _).state = none ∧ _
    rw [f2_lenCfg_read]
    cases b <;> simp [hx, f2_pairCountTM, f2_lenAction, f2_lenCfg, captureCfg, Action.apply, pairDecode]
  | cons_cons b d rest ih _ =>
    intro pre hx r hr
    by_cases h : b = d
    · subst d
      obtain ⟨t, ht, hs, ho⟩ := ih (pre ++ [b, b])
        (by simpa [List.append_assoc] using hx) r hr
      refine ⟨2 + t, by simp only [List.length_cons] at *; omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, f2_lenParse_block M c pre rest b b r hx, if_pos rfl]
      simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
      refine ⟨hs, ?_⟩
      cases b <;> cases hd : pairDecode rest with
        | none => simpa [pairDecode, hd] using ho
        | some p => cases p; simpa [pairDecode, hd] using ho
    · cases b <;> cases d
      · exact False.elim (h rfl)
      · obtain ⟨t, ht, hs, ho⟩ := f2_lenSuffix_run M c rest (pre ++ [false, true])
          (by simpa [List.append_assoc] using hx) r hr
        refine ⟨2 + t, by simp only [List.length_cons]; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, f2_lenParse_block M c pre rest false true r hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [List.length_append, List.length_cons, List.length_nil] at hs ho
        exact ⟨hs, by simpa [pairDecode] using ho⟩
      · refine ⟨2, by simp, ?_⟩
        rw [f2_lenParse_block M c pre rest true false r hx]
        simp [f2_lenCfg, pairDecode]
      · exact False.elim (h rfl)

/-- Quantitative input rewind, adapted from the wrapper controller's proved
`timed_rewind` pattern using the public `rewind_scan` interface.
**Proof sketch.** One mandatory left move is followed by exactly the new
position plus one scan steps. Work tapes and output are preserved. -/
private lemma f2_catalogRewind {k : ℕ} {S : Type} {x : List Bool}
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

/-- A completed generator is captured without physical output, then its
last cell and the first physical input cell are exposed for comparison.
**Proof sketch.** Use the least source halting time to discharge `capture_run`'s
liveness guard. One step moves the capture head left; quantitative rewind
restores the input head while preserving the completed generator bank. -/
private lemma f2_lenStart (M : FinTM Bool) (x w : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x w T) :
    ∃ t ≤ T + x.length + 4, ∃ c : Cfg M.k Bool M.State x,
      c.output = w ∧
      (f2_pairCountTM M).tm.runFrom ((f2_pairCountTM M).tm.initCfg x) t =
        f2_lenCfg M c (some (.inr (.inr none))) 0 (by omega) c.output.length := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hM).1⟩
  let t := Nat.find hh
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hM).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : M.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = w := hc.output_unique hM
  let emb : M.State → (f2_pairCountTM M).State := Sum.inl
  let ret : (f2_pairCountTM M).State := .inr (.inl 0)
  have hinit : (f2_pairCountTM M).tm.initCfg x = captureCfg emb ret [] [] (M.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (f2_pairCountTM M).tm.runFrom ((f2_pairCountTM M).tm.initCfg x) t =
      captureCfg emb ret [] [] c := by
    rw [hinit]
    exact capture_run M.tm (f2_pairCountTM M).tm emb ret (fun _ _ _ => rfl)
      [] [] _ t (fun s hst => Nat.find_min hh hst)
  let ready : Cfg (M.k + 1) Bool (f2_pairCountTM M).State x :=
    {f2_lenCfg M c (some (.inr (.inl 1))) 0 (by omega) c.output.length with
      inputPos := c.inputPos}
  have hback : (f2_pairCountTM M).tm.step (captureCfg emb ret [] [] c) = ready := by
    have hstate : (captureCfg emb ret [] [] c).state = some ret := by simp [captureCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i
      by_cases hi : i.val < M.k <;>
        simp [f2_pairCountTM, ret, f2_lenAction, Action.apply, captureCfg, ready, f2_lenCfg, hi,
          sub_eq_add_neg]
    · rfl
  obtain ⟨r, hrle, hr⟩ := f2_catalogRewind (f2_pairCountTM M).tm
    (.inr (.inl 1)) (.inr (.inl 2)) (some (.inr (.inr none)))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) ready rfl
  refine ⟨t + 1 + r, ?_, c, ho, ?_⟩
  · change r ≤ c.inputPos.val + 2 at hrle
    have := c.inputPos.isLt
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    rw [hback, hr]
    rfl

/-- The captured checker compares a valid pair's payload with the length of
the generator's output, and rejects every malformed input.
**Proof sketch.** Compose the silent capture/rewind prefix with the aligned
parser and countdown ledger, then absorb the two linear scans. -/
private lemma f2_pairCount_computes {M : FinTM Bool} {g : List Bool → List Bool}
    {T : ℕ → ℕ} (hM : M.ComputesFunInTime g T) :
    (f2_pairCountTM M).ComputesFunInTime
      (fun x => [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false]) (fun n => T n + 2 * n + 5) := by
  intro x
  obtain ⟨t, ht, c, ho, hstart⟩ := f2_lenStart M x (g x) (T x.length) (hM x)
  obtain ⟨r, hr, hs, hout⟩ := f2_lenParse_run M c x [] rfl c.output.length (le_refl _)
  have hc : (f2_pairCountTM M).ComputesInTime x
      [match pairDecode x with
        | some (_, b) => decide (b.length ≤ (g x).length)
        | none => false] (t + r) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, by simpa only [ho] using hout⟩
  exact hc.mono (by dsimp only; omega)

/-- A successful aligned parse reconstructs the input's exact encoding.
**Proof sketch.** Induct over two-bit blocks: equal bits prepend one decoded
bit; the separator exposes the entire remaining suffix. -/
private lemma f2_catalogPair_inverse (x : List Bool) :
    ∀ a v, pairDecode x = some (a, v) → x = pairEncode a v := by
  induction x using List.twoStepInduction with
  | nil => intro a v h; simp [pairDecode] at h
  | singleton b => intro a v h; cases b <;> simp [pairDecode] at h
  | cons_cons b d rest ih _ =>
    intro a v h
    cases b <;> cases d
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
      rcases p with ⟨u, w⟩
      cases he
      rw [ih u w hp]
      rfl
    · cases h; rfl
    · simp [pairDecode] at h
    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
      rcases p with ⟨u, w⟩
      cases he
      rw [ih u w hp]
      rfl

/-- Every all-time head position of a halted computation already occurs before
its time bound. Taking the image of that finite prefix gives at most `T+1`
cells per tape, including the initial cell.
**Proof sketch.** For a later time, split the run at `T` and use halt absorption;
for an earlier time use the same time index. Take cardinalities and sum. -/
private lemma f2_space_of_time {M : FinTM Bool} {x y : List Bool} {T : ℕ}
    (h : M.ComputesInTime x y T) (t : ℕ) :
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (T + 1) := by
  have hh := ((computesInTime_iff _ _ _ _).mp h).1
  have hsub (i : Fin M.k) :
      M.tm.visitedByTapeHead (M.tm.initCfg x) t i ⊆
        M.tm.visitedByTapeHead (M.tm.initCfg x) T i := by
    intro z hz
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
    by_cases hu : u ≤ T
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (by omega), rfl⟩
    · have hr : M.tm.runFrom (M.tm.initCfg x) u =
          M.tm.runFrom (M.tm.initCfg x) T := by
        rw [show u = T + (u - T) by omega, MultiTapeTM.runFrom_add,
          MultiTapeTM.runFrom_of_halt _ hh]
      exact Finset.mem_image.mpr ⟨T, Finset.mem_range.mpr (by omega),
        congrArg (fun c => c.workTapePos i) hr.symm⟩
  calc
    _ ≤ ∑ _i : Fin M.k, (T + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.card_le_card (hsub i)).trans (by
        unfold MultiTapeTM.visitedByTapeHead
        exact (Finset.card_image_le).trans (by rw [Finset.card_range]))
    _ = _ := by simp

/-- **P1 space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.computesFunInTime_id`). The copy machine runs in
constant work-tape space: one witness does the whole job on its input and
output heads alone.

**Proof sketch.** The existing witness `idTM` has no work tapes, so every
`spaceUsed` value is `0`; re-exhibit it and join the audited time
contract with the constant bound. -/
theorem computesFunInTime_id_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime id (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_idTM, 1, ?_, ?_⟩
  · intro x
    obtain ⟨hstate, hpos, hout⟩ := f2_idTM_run x x.length (le_refl _)
    have h0 : (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length).inputPos ≠ 0 := by
      intro h
      rw [h] at hpos
      simp at hpos
    have hsym : (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length).inputSymbol = none := by
      unfold Cfg.inputSymbol
      rw [dif_neg h0, dif_pos (by omega)]
    have hrun1 : f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) (x.length + 1) =
        (f2_idTM.tm.tr () none
          ((f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length).workTapeSymbols)).apply
          (f2_idTM.tm.runFrom (f2_idTM.tm.initCfg x) x.length) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      dsimp only
      rw [hsym]
    have hbase : f2_idTM.ComputesInTime x x (x.length + 1) := by
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hrun1]
        simp [f2_idTM, Action.apply]
      · rw [hrun1]
        simp only [f2_idTM, Action.apply]
        rw [hout]
        simp
    exact hbase.mono (le_of_eq (one_mul _).symm)
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P2 space row** (spec, fill pending — design §12 R3; annotates
`Turing.FinTM.computesFunInTime_const`). The fixed-word emission chain
runs in constant work-tape space.

**Proof sketch.** The existing witness `constTM w` is a zero-work-tape
emission chain, so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_const_spaceUsed (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun _ => w) (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_constTM w, w.length + 1, ?_, ?_⟩
  · intro x
    obtain ⟨hs, ho⟩ := emit_halts (f2_constTM w).tm w id (fun _ _ _ => rfl)
      ((f2_constTM w).tm.initCfg x) rfl
    have hbase : (f2_constTM w).ComputesInTime x w (w.length + 1) := by
      exact ⟨_, hs, by simpa only [MultiTapeTM.initCfg, Cfg.init, List.nil_append] using ho, rfl⟩
    exact hbase.mono (Nat.le_mul_of_pos_right _ (by omega))
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P3 space row** (spec, fill pending — design §12 R3; annotates
`Turing.FinTM.computesFunInTime_prepend`). Prepending a fixed word runs
in constant work-tape space: an emission chain followed by the input
copy scan never moves a work head.

**Proof sketch.** The existing witness `catalogPrefixTM` has no work-tape
movement (head-movement count zero on every phase), so each visited set
is the origin singleton and the total is the tape count, a machine
constant absorbed into `c`. -/
theorem computesFunInTime_prepend_spaceUsed (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => w ++ x) (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_catalogPrefixTM w, w.length + 1, ?_, ?_⟩
  · intro x
    apply (f2_catalogPrefixTM_computes w x).mono
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P4 space row** (spec, fill pending — design §12 R3; annotates
`Turing.FinTM.computesFunInTime_lengthBits`). The binary length counter
runs in logarithmic work-tape space: the counter word has `Nat.size n`
bits and the scan never leaves its interval (the sharp clause the
chapter-4 campaign consumes).

**Proof sketch.** The witness drives an in-place binary counter on one
work tape (the `Turing.incFixed` carry discipline): its head stays within
the counter interval `[-1, Nat.size n + 1]`, whose visit count the carry
head-movement bounds; constants absorb the boundary cells. -/
theorem computesFunInTime_lengthBits_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits x.length)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (Nat.size x.length + 1) := by
  exact ⟨f2_counterTM, 5, f2_counter_computes, f2_counter_space⟩

/-- **P5 space row, unary clause** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_polyUnary`). The unary
polynomial generator runs in linear work-tape space: each of its `e`
nested loop tapes holds a unary counter of side `n + 1`.

**Proof sketch.** Head-movement count per loop tape: installed by one
input scan and bounded by the box side `n + 1`, revisited in place
across iterations — per-tape visited sets lie in `[-1, n + 1]`, and the
tape count depends only on `e`, absorbed into `c`. -/
theorem computesFunInTime_polyUnary_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  cases e with
  | zero =>
    obtain ⟨M, c, ht, hs⟩ := computesFunInTime_const_spaceUsed (List.replicate C true)
    refine ⟨M, c, by simpa using ht, ?_⟩
    intro x t
    exact (hs x t).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  | succ d =>
    refine ⟨f2_catalogPolyUnaryTM d C, C + 10 * (d + 1) + 4, ?_, ?_⟩
    · intro x
      apply (f2_catalogPoly_unary_computes d C x).mono
      apply Nat.mul_le_mul
      · omega
      · exact Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    · intro x t
      exact (f2_poly_space d C x t).trans
        (Nat.mul_le_mul_right (x.length + 1) (by omega))

/-- **P5 space row, binary clause** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_polyBits`). The binary
polynomial evaluator runs in linear work-tape space: it is the unary
generator buffered into the length counter, and the buffer tape holds
the unary intermediate — the linear clause is the witness family's
honest bound (a logarithmic-space evaluator would be a new machine, out
of this increment's scope; recorded as a deviation from the sharpest
conceivable form).

**Proof sketch.** Split on the coefficient and exponent (round-1
finding 5 — the unqualified buffered-generator route fails at `C = 0`,
where the old generator still initializes length-`n + 1` unary banks
against a constant bound): for `C = 0`, and likewise for `e = 0`, the
witness is the constant-output family (zero work tapes, constant
space); for `C > 0` and `e > 0`, where `n + 1 ≤ C·(n+1)^e`, the buffered
composition's buffer holds the unary intermediate of length
`C·(n+1)^e`, the generator's banks are linear, and the counter is
logarithmic — all inside the stated value-linear bound. -/
theorem computesFunInTime_polyBits_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e))
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (C * (x.length + 1) ^ e + 1) := by
  by_cases hC : C = 0
  · subst C
    obtain ⟨M, c, ht, hs⟩ := computesFunInTime_const_spaceUsed (Nat.bits 0)
    refine ⟨M, c, ?_, ?_⟩
    · intro x
      simpa only [Nat.zero_mul] using (ht x).mono
        (Nat.mul_le_mul_left c (by
          simpa only [Nat.pow_one] using
            Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)))
    · simpa using hs
  · cases e with
    | zero =>
      obtain ⟨M, c, ht, hs⟩ := computesFunInTime_const_spaceUsed (Nat.bits C)
      refine ⟨M, c, by simpa using ht, ?_⟩
      intro x t
      simpa using (hs x t).trans (Nat.le_mul_of_pos_right c (Nat.succ_pos C))
    | succ d =>
      let A := C + 5 * (d + 1) + 4
      let K := A + 6 * C + 7
      let M := bufferedCompTM (f2_catalogPolyUnaryTM d C) f2_counterTM
      have ht : M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ (d + 1)))
          (fun n => K * (n + 1) ^ (d + 1)) := by
        intro x
        have h := bufferedCompTM_computesInTime
          (f2_catalogPolyUnaryTM d C) f2_counterTM
          (f2_catalogPoly_unary_computes d C x)
          (f2_counter_computes (List.replicate (C * (x.length + 1) ^ (d + 1)) true))
        simp only [List.length_replicate] at h
        apply h.mono
        have hp := Nat.one_le_pow (d + 1) (x.length + 1) (Nat.succ_pos _)
        change A * (x.length + 1) ^ (d + 1) + C * (x.length + 1) ^ (d + 1) + 2 +
          5 * (C * (x.length + 1) ^ (d + 1) + 1) ≤ K * (x.length + 1) ^ (d + 1)
        have hseven := Nat.mul_le_mul_left 7 hp
        calc
          _ = (A + 6 * C) * (x.length + 1) ^ (d + 1) + 7 := by ring
          _ ≤ (A + 6 * C) * (x.length + 1) ^ (d + 1) +
              7 * (x.length + 1) ^ (d + 1) := Nat.add_le_add_left hseven _
          _ = _ := by dsimp only [K]; ring
      refine ⟨M, M.k * (K + 1) + K, ?_, ?_⟩
      · intro x
        apply (ht x).mono
        exact Nat.mul_le_mul (by omega)
          (Nat.pow_le_pow_right (Nat.succ_pos _) (by omega))
      · intro x t
        have h := f2_space_of_time (ht x) t
        have hp : (x.length + 1) ^ (d + 1) ≤ C * (x.length + 1) ^ (d + 1) :=
          Nat.le_mul_of_pos_left _ (by omega)
        have hb : K * (x.length + 1) ^ (d + 1) + 1 ≤
            (K + 1) * (C * (x.length + 1) ^ (d + 1) + 1) := by
          have hh := Nat.mul_le_mul_left K hp
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
          omega
        exact h.trans ((Nat.mul_le_mul_left M.k hb).trans (by
          rw [← Nat.mul_assoc]
          exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))

/-- **P6 space row, fixed-first-component encoder** (spec, fill pending —
design §12 R3; annotates `Turing.FinTM.computesFunInTime_pairEncodeFixed`).
Pairing with a fixed first component runs in constant work-tape space: it
is the prepend row at the doubled fixed word.

**Proof sketch.** Same witness route as
`computesFunInTime_prepend_spaceUsed` at the word
`(α doubled) ++ [false, true]`: no work-head movement at all. -/
theorem computesFunInTime_pairEncodeFixed_spaceUsed (α : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode α x)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  simpa only [pairEncode] using
    computesFunInTime_prepend_spaceUsed ((α.flatMap fun b => [b, b]) ++ [false, true])

/-- **P6 space row, first extraction** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairFst`). The
first-component extractor runs in linear work-tape space: the aligned
scan buffers the undoubled prefix before any emission.

**Proof sketch.** The witness's single work tape holds the undoubled
prefix, of length at most half the input; its head walks the buffer
forward once and replays it once, so the visited set lies in
`[-1, n + 1]`. -/
theorem computesFunInTime_pairFst_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.fst).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  refine ⟨f2_pairExtractTM true false, 6, ?_, ?_⟩
  · intro x
    have h := (f2_pairExtract_computes true false x).mono
      (show 5 * (x.length + 1) ≤ 6 * (x.length + 1) by omega)
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some p => cases p; simpa [hd] using h
  · intro x t
    have h := f2_space_of_time (f2_pairExtract_computes true false x) t
    change _ ≤ 1 * (5 * (x.length + 1) + 1) at h
    omega

/-- **P6 space row, second extraction** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairSnd`). The
second-component extractor runs in linear work-tape space (it shares the
buffered parser with the first extractor).

**Proof sketch.** As `computesFunInTime_pairFst_spaceUsed`: one buffer
tape of at most the input length, walked forward and replayed once. -/
theorem computesFunInTime_pairSnd_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.snd).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  refine ⟨f2_pairExtractTM false true, 6, ?_, ?_⟩
  · intro x
    have h := (f2_pairExtract_computes false true x).mono
      (show 5 * (x.length + 1) ≤ 6 * (x.length + 1) by omega)
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some p => cases p; simpa [hd] using h
  · intro x t
    have h := f2_space_of_time (f2_pairExtract_computes false true x) t
    change _ ≤ 1 * (5 * (x.length + 1) + 1) at h
    omega

/-- **P6 space row, validity test** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_pairValid`). The grammar
validity test runs in constant work-tape space: alignment is finite
control, nothing is buffered.

**Proof sketch.** The existing witness `pairValidTM` has no work tapes
(`k = 0`), so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_pairValid_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => [(pairDecode x).isSome])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_pairValidTM, 1, ?_, ?_⟩
  · intro x
    simpa using f2_pairValid_computes x
  · intro x t
    rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
    omega

/-- **P13 space row, pair to concatenation** (spec, fill pending — design
§12 R3; annotates `Turing.FinTM.computesFunInTime_pairConcat`). The
concatenation extractor runs in linear work-tape space.

**Proof sketch.** The shared buffered parser again: one buffer tape
holding the undoubled prefix, walked forward and replayed once before
the suffix copy. -/
theorem computesFunInTime_pairConcat_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => a ++ b
          | none => [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  refine ⟨f2_pairExtractTM true true, 6, ?_, ?_⟩
  · intro x
    have h := (f2_pairExtract_computes true true x).mono
      (show 5 * (x.length + 1) ≤ 6 * (x.length + 1) by omega)
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some p => cases p; simpa [hd] using h
  · intro x t
    have h := f2_space_of_time (f2_pairExtract_computes true true x) t
    change _ ≤ 1 * (5 * (x.length + 1) + 1) at h
    omega

/-- **P14 space row, pair duplication** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_pairDup`). The duplication
encoder runs in constant work-tape space: both passes re-read the input
tape, nothing is buffered.

**Proof sketch.** The existing witness `pairDupTM` has no work tapes
(`k = 0`), so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_pairDup_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => pairEncode x x)
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_pairDupTM, 4, f2_pairDup_computes, ?_⟩
  intro x t
  rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
  omega

/-- The unary generator's received time proof has the sharper degree `e`;
only the fixed-output case needs the separate linear allowance. -/
private lemma f2_unary_sharp (C e : ℕ) :
    ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime (fun x => List.replicate (C * (x.length + 1) ^ e) true)
        (fun n => a * ((n + 1) ^ e + n + 1)) := by
  cases e with
  | zero =>
    obtain ⟨M, a, ht, _⟩ := computesFunInTime_const_spaceUsed (List.replicate C true)
    refine ⟨M, a, ?_⟩
    intro x
    simpa only [Nat.pow_zero, Nat.mul_one] using
      (ht x).mono (Nat.mul_le_mul_left a (by omega : x.length + 1 ≤ 1 + x.length + 1))
  | succ d =>
    refine ⟨f2_catalogPolyUnaryTM d C, C + 5 * (d + 1) + 4, ?_⟩
    intro x
    exact (f2_catalogPoly_unary_computes d C x).mono
      (Nat.mul_le_mul_left _ (by omega))

/-- The decoded first component is no longer than the original encoding;
a malformed encoding extracts the empty word. -/
private lemma f2_first_length (x : List Bool) :
    (((pairDecode x).map Prod.fst).getD []).length ≤ x.length := by
  cases hd : pairDecode x with
  | none => simp
  | some ab =>
    rcases ab with ⟨a, b⟩
    simp only [Option.map_some, Option.getD_some]
    rw [f2_catalogPair_inverse x a b hd, length_pairEncode]
    omega

/-- **P8 space row, threaded length check** (spec, fill pending — design
§12 R3; annotates `Turing.FinTM.computesFunInTime_pairLenCheck`). The
threaded length checker's space is dominated by the unary polynomial
bank `C·(|a|+1)^e` it counts down against, plus the linear parse
buffers.

**Proof sketch.** Head-movement count per stage: the extractor buffers at
most `n` cells, the unary generator's bank holds `C·(|a|+1)^e ≤
C·(n+1)^e` cells, and the countdown walks that bank in place; boundary
cells and the stage count go into `c`. -/
theorem computesFunInTime_pairLenCheck_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => [match pairDecode x with
          | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ e)
          | none => false])
        (fun n => c * (n + 1) ^ (e + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ c * ((x.length + 1) ^ e + x.length + 1) := by
  obtain ⟨U, a, hU⟩ := f2_unary_sharp C e
  let G := bufferedCompTM (f2_pairExtractTM true false) U
  have hF : (f2_pairExtractTM true false).ComputesFunInTime
      (fun x => ((pairDecode x).map Prod.fst).getD []) (fun n => 5 * (n + 1)) := by
    intro x
    have h := f2_pairExtract_computes true false x
    cases hd : pairDecode x with
    | none => simpa [hd] using h
    | some ab => cases ab; simpa [hd] using h
  have hG : G.ComputesFunInTime
      (fun x => List.replicate (C * ((((pairDecode x).map Prod.fst).getD []).length + 1) ^ e) true)
      (fun n => (a + 8) * ((n + 1) ^ e + n + 1)) := by
    intro x
    have hlen := f2_first_length x
    have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) e
    have hu := (hU (((pairDecode x).map Prod.fst).getD [])).mono
      (Nat.mul_le_mul_left a (Nat.add_le_add_right (Nat.add_le_add hpow hlen) 1))
    have h := bufferedCompTM_computesInTime _ _ (hF x) hu
    apply h.mono
    have hp := Nat.one_le_pow e (x.length + 1) (Nat.succ_pos _)
    simp only [Nat.add_mul]
    omega
  let M := f2_pairCountTM G
  let K := a + 13
  have ht : M.ComputesFunInTime
      (fun x => [match pairDecode x with
        | some (u, v) => decide (v.length ≤ C * (u.length + 1) ^ e)
        | none => false])
      (fun n => K * ((n + 1) ^ e + n + 1)) := by
    intro x
    have h := f2_pairCount_computes hG x
    have htime : (a + 8) * ((x.length + 1) ^ e + x.length + 1) + 2 * x.length + 5 ≤
        K * ((x.length + 1) ^ e + x.length + 1) := by
      dsimp only [K]
      simp only [Nat.add_mul]
      omega
    have h' := h.mono htime
    cases hd : pairDecode x with
    | none => simpa [hd] using h'
    | some uv => cases uv; simpa [hd] using h'
  refine ⟨M, 2 * K + M.k * (K + 1), ?_, ?_⟩
  · intro x
    apply (ht x).mono
    have hp : (x.length + 1) ^ e ≤ (x.length + 1) ^ (e + 1) :=
      Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have hn : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := by
      simpa only [Nat.pow_one] using
        Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)
    calc
      K * ((x.length + 1) ^ e + x.length + 1) ≤
          K * (2 * (x.length + 1) ^ (e + 1)) := Nat.mul_le_mul_left _ (by omega)
      _ = (2 * K) * (x.length + 1) ^ (e + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · intro x t
    have h := f2_space_of_time (ht x) t
    have hb : K * ((x.length + 1) ^ e + x.length + 1) + 1 ≤
        (K + 1) * ((x.length + 1) ^ e + x.length + 1) := by
      calc
        _ ≤ K * ((x.length + 1) ^ e + x.length + 1) +
            ((x.length + 1) ^ e + x.length + 1) := by omega
        _ = _ := by ring
    exact h.trans ((Nat.mul_le_mul_left M.k hb).trans (by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))

/- Local copies of the received raw-strip and guard witnesses. -/
/-- Copy the physical input, erase its final false-run and last true, rewind,
then replay. An all-false input halts silently during the reverse scan. -/
private def f2_rawStripTM : FinTM Bool where
  k := 1
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match inp with
        | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
        | none => ⟨0, fun _ => (none, .neg), none, some 1⟩
      | 1 => match work 0 with
        | none => ⟨0, fun _ => (none, 0), none, none⟩
        | some b => ⟨0, fun _ => (some none, .neg), none, some (if b then 2 else 1)⟩
      | 2 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some 2⟩
        | none => ⟨0, fun _ => (none, .pos), none, some 3⟩
      | _ => match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some 3⟩
        | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Raw-strip configurations expose the indexed input and a contiguous buffer. -/
private def f2_stripCfg (x : List Bool) (q : Option (Fin 4)) (i : ℕ) (hi : i ≤ x.length)
    (w : List Bool) (h : ℤ) (out : List Bool) : Cfg 1 Bool (Fin 4) x :=
  ⟨q, ⟨i + 1, by omega⟩, fun _ => bufferTape w, fun _ => h, out⟩

/-- Erasing the last written cell restores exactly the shorter buffer. -/
private lemma f2_catalogBuffer_erase (w : List Bool) (b : Bool) :
    Function.update (bufferTape (w ++ [b])) (w.length : ℤ) none = bufferTape w := by
  rw [bufferTape_append, Function.update_idem]
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z; simp
  · simp [Function.update_of_ne hz]

/-- The forward copy is silent and installs exactly the scanned input prefix.
**Proof sketch.** One input step appends the next bit at the buffer's right
blank; the input and work heads both advance once. -/
private lemma f2_rawStrip_copy (x : List Bool) : ∀ j (hj : j ≤ x.length),
    f2_rawStripTM.tm.runFrom (f2_rawStripTM.tm.initCfg x) j =
      f2_stripCfg x (some 0) j hj (x.take j) j [] := by
  intro j
  induction j with
  | zero => intro hj; apply Cfg.ext <;> simp [f2_rawStripTM, f2_stripCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hin : (f2_stripCfg x (some 0) j (by omega) (x.take j) j []).inputSymbol =
        some (x[j]'(by omega)) := inputSymbolInner j (by simp [f2_stripCfg]; omega) (by omega)
    unfold MultiTapeTM.step
    change (f2_rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    refine Cfg.ext rfl (moveInputPos_pos_of_ne_right _ (by simp [f2_stripCfg]; omega)) ?_ ?_ rfl
    · funext k
      change Function.update (bufferTape (x.take j)) (j : ℤ) (some (x[j]'(by omega))) =
        bufferTape (x.take (j + 1))
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      simpa only [List.length_take, Nat.min_eq_left (by omega : j ≤ x.length)] using
        (bufferTape_append (x.take j) (x[j]'(by omega))).symm
    · funext k; simp [f2_rawStripTM, f2_stripCfg, Action.apply]

/-- Rewinding the validated buffer from cell `j-1` takes `j+1` transitions.
**Proof sketch.** At the left blank, move right and enter replay. Otherwise
read a buffer cell, move left, and invoke the induction hypothesis. -/
private lemma f2_rawStrip_rewind (x a : List Bool)
    (i : ℕ) (hi : i ≤ x.length) : ∀ j, j ≤ a.length →
    f2_rawStripTM.tm.runFrom
      (f2_stripCfg x (some 2) i hi a ((j : ℤ) - 1) []) (j + 1) =
      f2_stripCfg x (some 3) i hi a 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, Nat.cast_zero,
      zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext k; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : f2_rawStripTM.tm.step
        (f2_stripCfg x (some 2) i hi a (((j + 1 : ℕ) : ℤ) - 1) []) =
        f2_stripCfg x (some 2) i hi a ((j : ℤ) - 1) [] := by
      have hz : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < a.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext k; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Replay appends exactly the visited buffer prefix and preserves its tape.
**Proof sketch.** The same replay invariant as the shared extractor: induct
on the number of visited cells and use the next-prefix equation for lists. -/
private lemma f2_rawStrip_replay (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∀ j (_hj : j ≤ a.length),
    f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 3) i hi a 0 []) j =
      f2_stripCfg x (some 3) i hi a j (a.take j) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    unfold MultiTapeTM.step
    simp only [f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, bufferTape_nat,
      List.getElem?_eq_getElem (by omega : j < a.length)]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
    · funext k; simp [Action.apply]
    · change a.take j ++ [a[j]'(by omega)] = a.take (j + 1)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega)]
      rfl

/-- Rewind followed by replay halts with exactly the retained buffer.
**Proof sketch.** The rewind costs `|a|+1`; replay and its final blank test
cost another `|a|+1`, and no earlier phase has emitted anything. -/
private lemma f2_rawStrip_finish (x a : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).state = none ∧
    (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 2) i hi a (a.length - 1) [])
      (2 * (a.length + 1))).output = a := by
  have htime : 2 * (a.length + 1) = (a.length + 1) + (a.length + 1) := by omega
  rw [htime, MultiTapeTM.runFrom_add, f2_rawStrip_rewind x a i hi a.length (le_refl _),
    MultiTapeTM.runFrom_succ_eq_step', f2_rawStrip_replay x a i hi a.length (le_refl _)]
  simp [MultiTapeTM.step, f2_rawStripTM, f2_stripCfg, Cfg.workTapeSymbols, Action.apply]

/-- The reverse phase erases the last cell and moves left, branching to
replay preparation precisely when the erased bit is true. -/
private lemma f2_rawStrip_erase (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) (b : Bool) :
    f2_rawStripTM.tm.step
      (f2_stripCfg x (some 1) i hi (w ++ [b]) ((w ++ [b]).length - 1) []) =
      f2_stripCfg x (some (if b then 2 else 1)) i hi w (w.length - 1) [] := by
  have hz : (((w ++ [b]).length : ℕ) : ℤ) - 1 = w.length := by simp
  rw [hz]
  unfold MultiTapeTM.step
  simp only [f2_stripCfg, f2_rawStripTM, Cfg.workTapeSymbols, bufferTape_nat,
    List.getElem?_append_right (by omega : w.length ≤ w.length), Nat.sub_self,
    List.getElem?_cons_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext k; exact f2_catalogBuffer_erase w b
  · funext k; simp [Action.apply, sub_eq_add_neg]

/-- Reverse erasure implements `splitAtLastTrue` exactly, including rejection
of every all-false word.
**Proof sketch.** Induct from the right. A final false is erased and the
induction continues. A final true is erased and the retained prefix is
rewound and replayed. These are exactly the `reverse.dropWhile` equations. -/
private lemma f2_rawStrip_trim (x w : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    ∃ t ≤ 3 * (w.length + 1),
      (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 1) i hi w (w.length - 1) []) t).state = none ∧
      (f2_rawStripTM.tm.runFrom (f2_stripCfg x (some 1) i hi w (w.length - 1) []) t).output =
        (splitAtLastTrue w).getD [] := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, f2_rawStripTM, f2_stripCfg,
      Cfg.workTapeSymbols, Action.apply, splitAtLastTrue]
  | append_singleton w b ih =>
    cases b with
    | false =>
      obtain ⟨t, ht, hs, ho⟩ := ih
      refine ⟨t + 1, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_rawStrip_erase]
      exact ⟨hs, by simpa [splitAtLastTrue] using ho⟩
    | true =>
      refine ⟨2 * (w.length + 1) + 1,
        by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_rawStrip_erase]
      simpa [splitAtLastTrue] using f2_rawStrip_finish x w i hi

/-- Raw marker stripping runs in linear time, with physical output delayed
until the last true has been located and removed.
**Proof sketch.** Copy in `|x|+1` steps, including the right-blank turn;
the reverse/replay ledger uses at most another `3(|x|+1)` steps. -/
private lemma f2_rawStrip_computes : f2_rawStripTM.ComputesFunInTime
    (fun x => (splitAtLastTrue x).getD []) (fun n => 4 * (n + 1)) := by
  intro x
  have hstart : f2_rawStripTM.tm.runFrom (f2_rawStripTM.tm.initCfg x) (x.length + 1) =
      f2_stripCfg x (some 1) x.length (le_refl _) x (x.length - 1) [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_rawStrip_copy x x.length (le_refl _)]
    have hin : (f2_stripCfg x (some 0) x.length (le_refl _) (x.take x.length) x.length []).inputSymbol =
        none := by simp [f2_stripCfg, Cfg.inputSymbol]
    unfold MultiTapeTM.step
    change (f2_rawStripTM.tm.tr (0 : Fin 4) _ _).apply _ = _
    rw [hin]
    apply Cfg.ext <;> simp [f2_rawStripTM, f2_stripCfg, Action.apply, sub_eq_add_neg]
  obtain ⟨t, ht, hs, ho⟩ := f2_rawStrip_trim x x x.length (le_refl _)
  have hc : f2_rawStripTM.ComputesInTime x ((splitAtLastTrue x).getD []) (x.length + 1 + t) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hs, ho⟩
  exact hc.mono (by dsimp only; omega)

/-- A finite scanner emits whether its input contains a true bit. -/
private def f2_anyTrueTM : FinTM Bool where
  k := 0
  State := Unit
  tm := {
    q₀ := ()
    tr := fun _ inp _ => match inp with
      | some false => ⟨.pos, fun i => i.elim0, none, some ()⟩
      | some true => ⟨0, fun i => i.elim0, some true, none⟩
      | none => ⟨0, fun i => i.elim0, some false, none⟩ }

/-- The marker-existence scan halts within one more than the remaining length.
**Proof sketch.** False bits advance silently; a true or the right boundary
emits the corresponding verdict and halts. -/
private lemma f2_anyTrue_run (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest),
    ∃ t ≤ rest.length + 1,
      (f2_anyTrueTM.tm.runFrom (f2_scanCfg x (some ()) pre.length (by simp [hx]) []) t).state = none ∧
      (f2_anyTrueTM.tm.runFrom (f2_scanCfg x (some ()) pre.length (by simp [hx]) []) t).output =
        [rest.any id] := by
  induction rest with
  | nil =>
    intro pre hx
    refine ⟨1, by simp, ?_⟩
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((f2_anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
    rw [f2_scanCfg_read]
    simp [hx, f2_anyTrueTM, Action.apply, f2_scanCfg]
  | cons b rest ih =>
    intro pre hx
    cases b with
    | true =>
      refine ⟨1, by simp, ?_⟩
      simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
      unfold MultiTapeTM.step
      change ((f2_anyTrueTM.tm.tr () _ _).apply _).state = none ∧ _
      rw [f2_scanCfg_read]
      simp [hx, f2_anyTrueTM, Action.apply, f2_scanCfg]
    | false =>
      have hs := f2_scanStep_right f2_anyTrueTM.tm x () (some ()) pre.length (by simp [hx]) [] none
        (by intro work; simp [hx, f2_anyTrueTM])
      obtain ⟨t, ht, hh, ho⟩ := ih (pre ++ [false]) (by simpa [List.append_assoc] using hx)
      refine ⟨t + 1, by simp only [List.length_cons]; omega, ?_⟩
      rw [MultiTapeTM.runFrom_succ_eq_step, hs]
      simpa using And.intro hh ho

/-- The true-bit scanner starts at the first input cell and uses a linear bound. -/
private lemma f2_anyTrue_computes : f2_anyTrueTM.ComputesFunInTime
    (fun x => [x.any id]) (fun n => n + 1) := by
  intro x
  obtain ⟨t, ht, hs, ho⟩ := f2_anyTrue_run x x [] rfl
  have hinit : f2_anyTrueTM.tm.initCfg x = f2_scanCfg x (some ()) 0 (by omega) [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  have hc : f2_anyTrueTM.ComputesInTime x [x.any id] t := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [hinit]
    exact ⟨hs, ho⟩
  exact hc.mono ht

/-- Marker absence is exactly the false verdict; a present marker can be
stripped after any fixed prefix without disturbing that prefix.
**Proof sketch.** Right induction follows `reverse.dropWhile`: append-false
preserves the previous result, and append-true selects the whole old word. -/
private lemma f2_catalogMarker_cases (v : List Bool) :
    (v.any id = false ∧ splitAtLastTrue v = none) ∨
      ∃ u, v.any id = true ∧ splitAtLastTrue v = some u ∧
        ∀ pre, splitAtLastTrue (pre ++ v) = some (pre ++ u) := by
  induction v using List.reverseRecOn with
  | nil => left; simp [splitAtLastTrue]
  | append_singleton v b ih =>
    cases b with
    | false =>
      rcases ih with ⟨ha, hs⟩ | ⟨u, ha, hs, hp⟩
      · left; simpa [splitAtLastTrue] using And.intro ha hs
      · right
        refine ⟨u, by simpa using ha, by simpa [splitAtLastTrue] using hs, ?_⟩
        intro pre
        simpa [splitAtLastTrue, List.append_assoc] using hp pre
    | true =>
      right
      refine ⟨v, by simp, by simp [splitAtLastTrue], ?_⟩
      intro pre
      simp [splitAtLastTrue]

private lemma f2_strip_linear :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => match pairDecode x with
          | some (a, v) =>
            match splitAtLastTrue v with
            | some u => pairEncode a u
            | none => []
          | none => [])
        fun n => c * (n + 1) := by
  obtain ⟨S, a, hS, _⟩ := computesFunInTime_pairSnd_spaceUsed
  obtain ⟨D, b, hD⟩ := computesFunInTime_comp hS f2_anyTrue_computes
    (by intro m n h; exact Nat.add_le_add_right h 1)
  have hD' : D.ComputesFunInTime
      (fun x => [((pairDecode x).map Prod.snd |>.getD []).any id])
      (fun n => b * (a * (n + 1) + (a * (n + 1) + 1) + 1)) := by
    simpa only [Function.comp_apply] using hD
  obtain ⟨E, c, hE, _⟩ := computesFunInTime_const_spaceUsed ([] : List Bool)
  obtain ⟨M, d, hM⟩ := computesFunInTime_cond hD' f2_rawStrip_computes hE
  refine ⟨M, d * (2 * b * (a + 1) + (4 + c) + 1), fun x => ?_⟩
  have hh : M.ComputesInTime x
      (match pairDecode x with
        | some (u, v) => match splitAtLastTrue v with
          | some w => pairEncode u w
          | none => []
        | none => [])
      (d * (b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) +
        max (4 * (x.length + 1)) (c * (x.length + 1)) + 1)) := by
    have hm := hM x
    cases hd : pairDecode x with
    | none => simpa [hd] using hm
    | some uv =>
      rcases uv with ⟨u, v⟩
      rcases f2_catalogMarker_cases v with ⟨ha, hs⟩ | ⟨w, ha, hs, hp⟩
      · simpa [hd, ha, hs] using hm
      · have hx : splitAtLastTrue x = some (pairEncode u w) := by
          rw [f2_catalogPair_inverse x u v hd]
          exact hp _
        simpa [hd, ha, hs, hx] using hm
  apply hh.mono
  have hbase : a * (x.length + 1) + 1 ≤ (a + 1) * (x.length + 1) := by
    simp only [Nat.add_mul, Nat.one_mul]; omega
  have hg : b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) ≤
      (2 * b * (a + 1)) * (x.length + 1) := by
    calc
      _ = (2 * b) * (a * (x.length + 1) + 1) := by ring
      _ ≤ (2 * b) * ((a + 1) * (x.length + 1)) := Nat.mul_le_mul_left _ hbase
      _ = _ := by ring
  have hm : max (4 * (x.length + 1)) (c * (x.length + 1)) ≤
      (4 + c) * (x.length + 1) := by
    apply max_le
    · exact Nat.mul_le_mul_right _ (by omega)
    · exact Nat.mul_le_mul_right _ (by omega)
  have hb : b * (a * (x.length + 1) + (a * (x.length + 1) + 1) + 1) +
      max (4 * (x.length + 1)) (c * (x.length + 1)) + 1 ≤
      (2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1) := by
    calc
      _ ≤ (2 * b * (a + 1)) * (x.length + 1) +
          (4 + c) * (x.length + 1) + (x.length + 1) :=
        Nat.add_le_add (Nat.add_le_add hg hm) (by omega)
      _ = _ := by ring
  calc
    _ ≤ d * ((2 * b * (a + 1) + (4 + c) + 1) * (x.length + 1)) := Nat.mul_le_mul_left d hb
    _ = _ := by ring

/-- **P9 space row, marker stripping** (spec, fill pending — design §12
R3; annotates `Turing.FinTM.computesFunInTime_stripLast`). The marker
stripper runs in linear work-tape space: the raw buffer and the guard
banks are each linear, and the quadratic **time** contract is deliberate
slack over the construction's actual linear-derived bound (round-1
finding/note 8 — the attached witness proves a linear intermediate
before weakening; no replay story is needed).

**Proof sketch.** The witness's guard/extraction banks and the raw-strip
buffer are each at most linear (`O(n + 1)` cells); the timed conditional
keeps them disjoint; every head stays inside linear intervals, and the
retained `(n+1)²` time clause is slack, not a resource actually spent on
space. -/
theorem computesFunInTime_stripLast_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun x => match pairDecode x with
          | some (a, v) =>
            match splitAtLastTrue v with
            | some u => pairEncode a u
            | none => []
          | none => [])
        (fun n => c * (n + 1) ^ 2) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) := by
  obtain ⟨M, a, hM⟩ := f2_strip_linear
  refine ⟨M, a + M.k * (a + 1), ?_, ?_⟩
  · intro x
    apply (hM x).mono
    have hn : x.length + 1 ≤ (x.length + 1) ^ 2 := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos x.length)
        (show 1 ≤ 2 by omega)
    exact (Nat.mul_le_mul_left a hn).trans
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · intro x t
    have h := f2_space_of_time (hM x) t
    have hb : a * (x.length + 1) + 1 ≤ (a + 1) * (x.length + 1) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    exact h.trans ((Nat.mul_le_mul_left M.k hb).trans (by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))

/-- **P11 space row, fixed-width increment** (spec, fill pending — design
§12 R3; annotates `Turing.FinTM.computesFunInTime_incFixed`; the
string-function counterpart of `Turing.incrementTM`). The incrementer
runs in constant work-tape space: it validates and emits from two native
input scans with the carry resident in control.

**Proof sketch.** The existing witness `incFixedTM` has no work tapes
(`k = 0`), so `spaceUsed` is identically `0`. -/
theorem computesFunInTime_incFixed_spaceUsed :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => (incFixed x).getD [])
        (fun n => c * (n + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c := by
  refine ⟨f2_incFixedTM, 3, f2_incFixed_computes, ?_⟩
  intro x t
  rw [MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl]
  omega

/-- Control of the forwarding map: silent pair validation and buffering,
separate buffer rewinds, doubled-prefix emission, and clamped virtual input. -/
private inductive a2_MapState (Q : Type) where
  | parse (pending : Option Bool)
  | copyB | backB | backA | emitA | emitAgain (b : Bool) | separator
  | run (q : Q) (tag : Bool)
  deriving DecidableEq

private instance a2_mapStateFintype (Q : Type) [Fintype Q] : Fintype (a2_MapState Q) :=
  derive_fintype% _

/-- Administration touches only the two input buffers, and never a payload tape. -/
private def a2_mapAct (M : FinTM Bool) (inp : SignType)
    (a b : Option (Option Bool) × SignType) (out : Option Bool)
    (next : Option (a2_MapState M.State)) : Action (1 + (1 + M.k)) Bool (a2_MapState M.State) :=
  ⟨inp, tapeBlocks (fun _ => a) b (fun _ => (none, 0)), out, next⟩

/-- The commissioned forwarding controller. The two buffers contain the
components, never the payload output. In setup mode the payload entry is a
stationary live seam, used only to certify its first arrival. In forwarding
mode each payload step has exactly its original work actions and emission;
`virtualMove` clamps both virtual-input boundaries, including empty input. -/
private def a2_mapTM (M : FinTM Bool) (forward : Bool) : FinTM Bool where
  k := 1 + (1 + M.k)
  State := a2_MapState M.State
  tm := {
    q₀ := .parse none
    tr := fun q inp work =>
      let act := a2_mapAct M
      let first := work (Fin.castAdd (1 + M.k) (0 : Fin 1))
      let second := work (Fin.natAdd 1 (Fin.castAdd M.k (0 : Fin 1)))
      match q with
      | .parse none => match inp with
        | none => act 0 (none, 0) (none, 0) none none
        | some b => act .pos (none, 0) (none, 0) none (some (.parse (some b)))
      | .parse (some b) => match inp with
        | none => act 0 (none, 0) (none, 0) none none
        | some d => if b = d then
            act .pos (some (some b), .pos) (none, 0) none (some (.parse none))
          else if b then act .pos (none, 0) (none, 0) none none
          else act .pos (none, .neg) (none, 0) none (some .copyB)
      | .copyB => match inp with
        | some b => act .pos (none, 0) (some (some b), .pos) none (some .copyB)
        | none => act 0 (none, 0) (none, .neg) none (some .backB)
      | .backB => match second with
        | some _ => act 0 (none, 0) (none, .neg) none (some .backB)
        | none => act 0 (none, 0) (none, .pos) none (some .backA)
      | .backA => match first with
        | some _ => act 0 (none, .neg) (none, 0) none (some .backA)
        | none => act 0 (none, .pos) (none, 0) none (some .emitA)
      | .emitA => match first with
        | some b => act 0 (none, 0) (none, 0) (some b) (some (.emitAgain b))
        | none => act 0 (none, 0) (none, 0) (some false) (some .separator)
      | .emitAgain b => act 0 (none, .pos) (none, 0) (some b) (some .emitA)
      | .separator => act 0 (none, 0) (none, 0) (some true) (some (.run M.tm.q₀ true))
      | .run q b => if forward then
          let a := M.tm.tr q second (fun i => work (Fin.natAdd 1 (Fin.natAdd 1 i)))
          let m := virtualMove b second a.inputTape
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, m) a.workTapes,
            a.output, a.state.map (fun q => .run q (virtualNextTag b m))⟩
        else controlAction 0 (some (.run q b)) }

/-- Administrative configurations have two buffered words and an untouched
blank payload bank. The physical output is explicit. -/
private def a2_mapCfg (M : FinTM Bool) (x : List Bool) (q : Option (a2_MapState M.State))
    (p : Fin (x.length + 2)) (a b : List Bool) (ha hb : ℤ) (out : List Bool) :
    Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x where
  state := q
  inputPos := p
  workTapes := tapeBlocks (fun _ => bufferTape a) (bufferTape b) (fun _ _ => none)
  workTapePos := tapeBlocks (fun _ => ha) hb (fun _ => 0)
  output := out

/-- The forwarding configuration retains the physical input, first buffer,
and already emitted prefix; the second buffer is the source's virtual input. -/
private def a2_mapVirtual (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (tag : Bool) (p : Fin (x.length + 2))
    (a pre : List Bool) : Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x where
  state := c.state.map (fun q => .run q tag)
  inputPos := p
  workTapes := tapeBlocks (fun _ => bufferTape a) (bufferTape y) c.workTapes
  workTapePos := tapeBlocks (fun _ => (a.length : ℤ)) ((c.inputPos.val : ℤ) - 1) c.workTapePos
  output := pre ++ c.output

/-- The parser reads its native input independently of both buffers. -/
private lemma a2_mapCfg_read (M : FinTM Bool) (x : List Bool) (q : Option (a2_MapState M.State))
    (i : ℕ) (hi : i ≤ x.length) (a b : List Bool) (ha hb : ℤ) (out : List Bool) :
    (a2_mapCfg M x q ⟨i + 1, by omega⟩ a b ha hb out).inputSymbol = x[i]? :=
  inputSymbol_at _ i hi rfl

/-- Administrative actions with no writes only change the two buffer heads,
control, input position, and the physical output. -/
private lemma a2_map_move (M : FinTM Bool) (x : List Bool)
    (q q' : Option (a2_MapState M.State)) (p : Fin (x.length + 2))
    (a b : List Bool) (ha hb : ℤ) (out : List Bool)
    (mi ma mb : SignType) (emit : Option Bool) :
    (a2_mapAct M mi (none, ma) (none, mb) emit q').apply
      (a2_mapCfg M x q p a b ha hb out) =
      a2_mapCfg M x q' (moveInputPos p mi) a b (ha + ma.cast) (hb + mb.cast)
        (out ++ emit.toList) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [a2_mapAct, a2_mapCfg, Action.apply]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [a2_mapAct, a2_mapCfg, Action.apply]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [a2_mapAct, a2_mapCfg, Action.apply]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
        simp [a2_mapAct, a2_mapCfg, Action.apply]

/-- Reading the first half of an aligned block changes only finite control
and the native input head. No physical output is emitted. -/
private lemma a2_map_first (M : FinTM Bool) (x pre rest a : List Bool) (b : Bool)
    (hx : x = pre ++ b :: rest) :
    (a2_mapTM M false).tm.step
      (a2_mapCfg M x (some (.parse none)) ⟨pre.length + 1, by simp [hx] <;> omega⟩
        a [] a.length 0 []) =
      a2_mapCfg M x (some (.parse (some b))) ⟨pre.length + 2, by simp [hx] <;> omega⟩
        a [] a.length 0 [] := by
  unfold MultiTapeTM.step
  change ((a2_mapTM M false).tm.tr (.parse none) _ _).apply _ = _
  rw [a2_mapCfg_read M x _ pre.length (by simp [hx])]
  have hr : x[pre.length]? = some b := by simp [hx]
  rw [hr]
  change (a2_mapAct M .pos (none, 0) (none, 0) none _).apply _ = _
  rw [a2_map_move]
  simp only [SignType.cast, add_zero, Option.toList_none,
    List.append_nil]
  congr 1
  exact moveInputPos_pos_of_ne_right _ (by simp [hx])

/-- Doubled blocks append one bit to the first buffer. `01` starts suffix
buffering; `10` rejects before emitting. Both missing-bit cases are handled
by the surrounding parser induction. -/
private lemma a2_map_block (M : FinTM Bool) (x pre rest a : List Bool) (b c : Bool)
    (hx : x = pre ++ b :: c :: rest) :
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some (.parse none)) ⟨pre.length + 1, by simp [hx] <;> omega⟩
        a [] a.length 0 []) 2 =
      if b = c then a2_mapCfg M x (some (.parse none))
        ⟨pre.length + 3, by simp [hx] <;> omega⟩ (a ++ [b]) [] (a ++ [b]).length 0 []
      else if b then a2_mapCfg M x none
        ⟨pre.length + 3, by simp [hx] <;> omega⟩ a [] a.length 0 []
      else a2_mapCfg M x (some .copyB)
        ⟨pre.length + 3, by simp [hx] <;> omega⟩ a [] (a.length - 1) 0 [] := by
  change (a2_mapTM M false).tm.step ((a2_mapTM M false).tm.step _) = _
  rw [a2_map_first M x pre (c :: rest) a b hx]
  unfold MultiTapeTM.step
  change ((a2_mapTM M false).tm.tr (.parse (some b)) _ _).apply _ = _
  rw [a2_mapCfg_read M x _ (pre.length + 1) (by simp [hx])]
  have hr : x[pre.length + 1]? = some c := by simp [hx]
  rw [hr]
  have hm : moveInputPos (⟨pre.length + 2, by simp [hx] <;> omega⟩ : Fin (x.length + 2)) .pos =
      ⟨pre.length + 3, by simp [hx] <;> omega⟩ :=
    moveInputPos_pos_of_ne_right _ (by simp [hx])
  cases b <;> cases c <;> simp only [a2_mapTM, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals refine Cfg.ext rfl hm ?_ ?_ rfl
  all_goals first
    | (funext i
       refine Fin.addCases (fun j => ?_) (fun j => ?_) i
       · simpa only [a2_mapAct, a2_mapCfg, Action.apply, tapeBlocks_left] using (bufferTape_append a _).symm
       · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
           simp [a2_mapAct, a2_mapCfg, Action.apply])
    | (funext i
       refine Fin.addCases (fun j => ?_) (fun j => ?_) i
       · simp [a2_mapAct, a2_mapCfg, Action.apply, sub_eq_add_neg]
       · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
           simp [a2_mapAct, a2_mapCfg, Action.apply])

/-- After validation, the complete suffix is buffered silently. Its right
blank is turned left exactly once, including when the suffix is empty. -/
private lemma a2_map_suffix (M : FinTM Bool) (x rest a : List Bool) :
    ∀ pre b (hx : x = pre ++ rest),
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some .copyB) ⟨pre.length + 1, by simp [hx] <;> omega⟩
        a b (a.length - 1) b.length []) (rest.length + 1) =
      a2_mapCfg M x (some .backB) ⟨x.length + 1, by omega⟩
        a (b ++ rest) (a.length - 1) ((b ++ rest).length - 1) [] := by
  induction rest with
  | nil =>
    intro pre b hx
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((a2_mapTM M false).tm.tr .copyB _ _).apply _ = _
    rw [a2_mapCfg_read M x _ pre.length (by simp [hx])]
    have hr : x[pre.length]? = none := by simp [hx]
    rw [hr]
    change (a2_mapAct M 0 (none, 0) (none, .neg) none _).apply _ = _
    rw [a2_map_move]
    simp [hx, sub_eq_add_neg]
  | cons d rest ih =>
    intro pre b hx
    have hs : (a2_mapTM M false).tm.step
        (a2_mapCfg M x (some .copyB) ⟨pre.length + 1, by simp [hx] <;> omega⟩
          a b (a.length - 1) b.length []) =
        a2_mapCfg M x (some .copyB) ⟨(pre ++ [d]).length + 1, by simp [hx] <;> omega⟩
          a (b ++ [d]) (a.length - 1) (b ++ [d]).length [] := by
      unfold MultiTapeTM.step
      change ((a2_mapTM M false).tm.tr .copyB _ _).apply _ = _
      rw [a2_mapCfg_read M x _ pre.length (by simp [hx])]
      have hr : x[pre.length]? = some d := by simp [hx]
      rw [hr]
      refine Cfg.ext rfl ?_ ?_ ?_ rfl
      · simpa only [List.length_append, List.length_singleton] using
          moveInputPos_pos_of_ne_right
            (⟨pre.length + 1, by simp [hx] <;> omega⟩ : Fin (x.length + 2)) (by simp [hx])
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp [a2_mapTM, a2_mapAct, a2_mapCfg, Action.apply]
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simpa only [a2_mapTM, a2_mapAct, a2_mapCfg, Action.apply, tapeBlocks_buffer] using
              (bufferTape_append b d).symm
          · simp [a2_mapTM, a2_mapAct, a2_mapCfg, Action.apply]
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp [a2_mapTM, a2_mapAct, a2_mapCfg, Action.apply]
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
            simp [a2_mapTM, a2_mapAct, a2_mapCfg, Action.apply]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [d]) (b ++ [d]) (by simpa [List.append_assoc] using hx)

/-- Rewind the second buffer to zero, preserving the first buffer and the
blank payload bank. The left-blank step is present even at width zero. -/
private lemma a2_map_backB (M : FinTM Bool) (x a b : List Bool)
    (p : Fin (x.length + 2)) : ∀ j, j ≤ b.length →
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some .backB) p a b (a.length - 1) ((j : ℤ) - 1) []) (j + 1) =
      a2_mapCfg M x (some .backA) p a b (a.length - 1) 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_buffer,
      Nat.cast_zero, zero_sub, bufferTape_left]
    change (a2_mapAct M 0 (none, 0) (none, .pos) none _).apply
      (a2_mapCfg M x (some .backB) p a b (a.length - 1) (-1) []) = _
    rw [a2_map_move]
    simp [a2_mapCfg]
  | succ j ih =>
    intro hj
    have hr : bufferTape b (((j + 1 : ℕ) : ℤ) - 1) = some b[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hs : (a2_mapTM M false).tm.step
        (a2_mapCfg M x (some .backB) p a b (a.length - 1) (((j + 1 : ℕ) : ℤ) - 1) []) =
        a2_mapCfg M x (some .backB) p a b (a.length - 1) ((j : ℤ) - 1) [] := by
      unfold MultiTapeTM.step
      simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_buffer, hr]
      change (a2_mapAct M 0 (none, 0) (none, .neg) none _).apply
        (a2_mapCfg M x (some .backB) p a b (a.length - 1) (((j + 1 : ℕ) : ℤ) - 1) []) = _
      rw [a2_map_move]
      simp [a2_mapCfg, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- The corresponding first-buffer rewind, leaving virtual input at zero. -/
private lemma a2_map_backA (M : FinTM Bool) (x a b : List Bool)
    (p : Fin (x.length + 2)) : ∀ j, j ≤ a.length →
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some .backA) p a b ((j : ℤ) - 1) 0 []) (j + 1) =
      a2_mapCfg M x (some .emitA) p a b 0 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_left,
      Nat.cast_zero, zero_sub, bufferTape_left]
    change (a2_mapAct M 0 (none, .pos) (none, 0) none _).apply
      (a2_mapCfg M x (some .backA) p a b (-1) 0 []) = _
    rw [a2_map_move]
    simp [a2_mapCfg]
  | succ j ih =>
    intro hj
    have hr : bufferTape a (((j + 1 : ℕ) : ℤ) - 1) = some a[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hs : (a2_mapTM M false).tm.step
        (a2_mapCfg M x (some .backA) p a b (((j + 1 : ℕ) : ℤ) - 1) 0 []) =
        a2_mapCfg M x (some .backA) p a b ((j : ℤ) - 1) 0 [] := by
      unfold MultiTapeTM.step
      simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_left, hr]
      change (a2_mapAct M 0 (none, .neg) (none, 0) none _).apply
        (a2_mapCfg M x (some .backA) p a b (((j + 1 : ℕ) : ℤ) - 1) 0 []) = _
      rw [a2_map_move]
      simp [a2_mapCfg, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Emit each retained first-component bit twice, then `01`, and enter the
payload seam. The second buffer and payload bank are unchanged.
**Proof sketch.** Each nonblank first-buffer cell takes two emission steps;
the second advances the head. At the right blank, two further transitions
emit the delimiter and enter the source's start state with right-arrival tag. -/
private lemma a2_map_emit (M : FinTM Bool) (x a b rest : List Bool)
    (p : Fin (x.length + 2)) : ∀ pre out, a = pre ++ rest →
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some .emitA) p a b pre.length 0 out) (2 * rest.length + 2) =
      a2_mapCfg M x (some (.run M.tm.q₀ true)) p a b a.length 0
        (out ++ rest.flatMap (fun d => [d, d]) ++ [false, true]) := by
  induction rest with
  | nil =>
    intro pre out he
    simp only [List.append_nil] at he
    subst a
    have hs : (a2_mapTM M false).tm.step
        (a2_mapCfg M x (some .emitA) p pre b pre.length 0 out) =
        a2_mapCfg M x (some .separator) p pre b pre.length 0 (out ++ [false]) := by
      unfold MultiTapeTM.step
      simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_left,
        bufferTape_nat, List.getElem?_length]
      change (a2_mapAct M 0 (none, 0) (none, 0) (some false) _).apply
        (a2_mapCfg M x (some .emitA) p pre b pre.length 0 out) = _
      rw [a2_map_move]
      simp [a2_mapCfg]
    change (a2_mapTM M false).tm.step ((a2_mapTM M false).tm.step _) = _
    rw [hs]
    change (a2_mapAct M 0 (none, 0) (none, 0) (some true) _).apply _ = _
    rw [a2_map_move]
    simp [List.append_assoc]
  | cons d rest ih =>
    intro pre out he
    have hr : bufferTape a pre.length = some d := by simp [he]
    have hs : (a2_mapTM M false).tm.runFrom
        (a2_mapCfg M x (some .emitA) p a b pre.length 0 out) 2 =
        a2_mapCfg M x (some .emitA) p a b (pre ++ [d]).length 0 (out ++ [d, d]) := by
      change (a2_mapTM M false).tm.step ((a2_mapTM M false).tm.step _) = _
      have hfirst : (a2_mapTM M false).tm.step
          (a2_mapCfg M x (some .emitA) p a b pre.length 0 out) =
          a2_mapCfg M x (some (.emitAgain d)) p a b pre.length 0 (out ++ [d]) := by
        unfold MultiTapeTM.step
        simp only [a2_mapTM, a2_mapCfg, Cfg.workTapeSymbols, tapeBlocks_left, hr]
        change (a2_mapAct M 0 (none, 0) (none, 0) (some d) _).apply
          (a2_mapCfg M x (some .emitA) p a b pre.length 0 out) = _
        rw [a2_map_move]
        simp [a2_mapCfg]
      rw [hfirst]
      change (a2_mapAct M 0 (none, .pos) (none, 0) (some d) _).apply _ = _
      rw [a2_map_move]
      simp [List.append_assoc]
    rw [show 2 * (d :: rest).length + 2 = 2 + (2 * rest.length + 2) by simp; omega,
      MultiTapeTM.runFrom_add, hs]
    simpa only [List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append] using
      ih (pre ++ [d]) (out ++ [d, d]) (by simpa [List.append_assoc] using he)

/-- Successful suffix buffering, two rewinds, and encoded-prefix emission
reach the initialized payload seam within `3|a|+2|b|+5` transitions. -/
private lemma a2_map_finish (M : FinTM Bool) (x pre a b : List Bool)
    (hx : x = pre ++ b) :
    (a2_mapTM M false).tm.runFrom
      (a2_mapCfg M x (some .copyB) ⟨pre.length + 1, by simp [hx] <;> omega⟩
        a [] (a.length - 1) 0 []) (3 * a.length + 2 * b.length + 5) =
      a2_mapVirtual M (M.tm.initCfg b) true ⟨x.length + 1, by omega⟩ a (pairEncode a []) := by
  rw [show 3 * a.length + 2 * b.length + 5 =
      ((b.length + 1) + (b.length + 1) + (a.length + 1)) + (2 * a.length + 2) by omega,
    MultiTapeTM.runFrom_add (a := (b.length + 1) + (b.length + 1) + (a.length + 1)) (b := 2 * a.length + 2),
    MultiTapeTM.runFrom_add (a := (b.length + 1) + (b.length + 1)) (b := a.length + 1),
    MultiTapeTM.runFrom_add (a := b.length + 1) (b := b.length + 1)]
  have hcopy := a2_map_suffix M x b a pre [] hx
  simp only [List.nil_append, List.length_nil, Nat.cast_zero] at hcopy
  rw [hcopy]
  rw [a2_map_backB M x a b _ _ (le_refl _), a2_map_backA M x a b _ _ (le_refl _)]
  have he := a2_map_emit M x a b a (⟨x.length + 1, by omega⟩) [] [] (by simp)
  simp only [List.length_nil, Nat.cast_zero, List.nil_append] at he
  rw [he]
  refine Cfg.ext rfl rfl rfl ?_ ?_
  · funext i
    simp [a2_mapCfg, a2_mapVirtual, MultiTapeTM.initCfg, Cfg.init]
  · simp [a2_mapCfg, a2_mapVirtual, MultiTapeTM.initCfg, Cfg.init, pairEncode]

/-- The validating setup either halts silently on malformed input or reaches
exactly the required payload seam with the encoded first component emitted.
**Proof sketch.** Induct on aligned pairs. Equal bits add one buffered bit;
`10`, a missing bit, or a missing delimiter reject. At `01`, buffer the entire
suffix and apply the rewind/emission ledger. No payload transition is used. -/
private lemma a2_map_parse (M : FinTM Bool) (x rest : List Bool) :
    ∀ pre a (hx : x = pre ++ rest), ∃ t ≤ 3 * rest.length + 3 * a.length + 5,
      match pairDecode rest with
      | some (d, b) => (a2_mapTM M false).tm.runFrom
          (a2_mapCfg M x (some (.parse none)) ⟨pre.length + 1, by simp [hx] <;> omega⟩
            a [] a.length 0 []) t =
          a2_mapVirtual M (M.tm.initCfg b) true ⟨x.length + 1, by omega⟩
            (a ++ d) (pairEncode (a ++ d) [])
      | none =>
          ((a2_mapTM M false).tm.runFrom
            (a2_mapCfg M x (some (.parse none)) ⟨pre.length + 1, by simp [hx] <;> omega⟩
              a [] a.length 0 []) t).state = none ∧
          ((a2_mapTM M false).tm.runFrom
            (a2_mapCfg M x (some (.parse none)) ⟨pre.length + 1, by simp [hx] <;> omega⟩
              a [] a.length 0 []) t).output = [] := by
  induction rest using List.twoStepInduction with
  | nil =>
    intro pre a hx
    refine ⟨1, by simp, ?_⟩
    simp only [pairDecode, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (((a2_mapTM M false).tm.tr (.parse none) _ _).apply _).state = none ∧ _
    rw [a2_mapCfg_read M x _ pre.length (by simp [hx])]
    simp [hx, a2_mapTM, a2_mapAct, Action.apply, a2_mapCfg]
  | singleton b =>
    intro pre a hx
    refine ⟨2, by simp, ?_⟩
    have hd : pairDecode [b] = none := by cases b <;> rfl
    rw [hd]
    change ((a2_mapTM M false).tm.step ((a2_mapTM M false).tm.step _)).state = none ∧
      ((a2_mapTM M false).tm.step ((a2_mapTM M false).tm.step _)).output = []
    rw [a2_map_first M x pre [] a b hx]
    unfold MultiTapeTM.step
    change (((a2_mapTM M false).tm.tr (.parse (some b)) _ _).apply _).state = none ∧ _
    rw [a2_mapCfg_read M x _ (pre.length + 1) (by simp [hx])]
    cases b <;> simp [hx, a2_mapTM, a2_mapAct, Action.apply, a2_mapCfg, pairDecode]
  | cons_cons b c rest ih _ =>
    intro pre a hx
    by_cases h : b = c
    · subst c
      obtain ⟨t, ht, he⟩ := ih (pre ++ [b, b]) (a ++ [b])
        (by simpa [List.append_assoc] using hx)
      refine ⟨2 + t, by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega, ?_⟩
      have hr := a2_map_block M x pre rest a b b hx
      simp only [if_pos rfl] at hr
      simp only [List.length_append, List.length_cons, List.length_nil] at he
      cases b <;> cases hd : pairDecode rest with
      | none =>
        simp only [pairDecode, hd] at he ⊢
        rw [MultiTapeTM.runFrom_add, hr]
        simpa [List.append_assoc, Nat.add_assoc] using he
      | some p =>
        rcases p with ⟨d, v⟩
        simp only [pairDecode, hd] at he ⊢
        rw [MultiTapeTM.runFrom_add, hr]
        simpa [List.append_assoc, Nat.add_assoc] using he
    · cases b <;> cases c
      · exact False.elim (h rfl)
      · refine ⟨2 + (3 * a.length + 2 * rest.length + 5), by simp only [List.length_cons]; omega, ?_⟩
        simp only [pairDecode, List.append_nil]
        rw [MultiTapeTM.runFrom_add, a2_map_block M x pre rest a false true hx]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simpa only [List.length_append, List.length_cons, List.length_nil] using
          a2_map_finish M x (pre ++ [false, true]) a rest (by simpa [List.append_assoc] using hx)
      · refine ⟨2, by simp, ?_⟩
        rw [a2_map_block M x pre rest a true false hx]
        simp [a2_mapCfg, pairDecode]
      · exact False.elim (h rfl)

/-- Starting with empty buffers gives a uniform linear setup budget on every
input, including malformed encodings. -/
private lemma a2_map_setup (M : FinTM Bool) (x : List Bool) :
    ∃ t ≤ 5 * (x.length + 1),
      match pairDecode x with
      | some (a, b) => (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t =
          a2_mapVirtual M (M.tm.initCfg b) true ⟨x.length + 1, by omega⟩ a (pairEncode a [])
      | none => ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t).state = none ∧
          ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t).output = [] := by
  obtain ⟨t, ht, he⟩ := a2_map_parse M x x [] [] rfl
  have hi : (a2_mapTM M false).tm.initCfg x =
      a2_mapCfg M x (some (.parse none)) ⟨1, by omega⟩ [] [] 0 0 [] := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [a2_mapCfg, MultiTapeTM.initCfg, Cfg.init]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [a2_mapCfg, MultiTapeTM.initCfg, Cfg.init]
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp [a2_mapCfg, MultiTapeTM.initCfg, Cfg.init]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
          simp [a2_mapCfg, MultiTapeTM.initCfg, Cfg.init]
  refine ⟨t, by simp only [List.length_nil, mul_zero, add_zero] at ht; omega, ?_⟩
  rw [hi]
  simpa only [List.nil_append, List.length_nil, Nat.cast_zero] using he

/-- One forwarded payload step has exactly the source work actions and
emission. `virtualMove_correct` proves both boundary clamps and preserves
its arrival tag, without a nonempty-input assumption. -/
private lemma a2_mapVirtual_step (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (tag : Bool) (hb : VirtualTag c.inputPos tag)
    (p : Fin (x.length + 2)) (a pre : List Bool) :
    ∃ tag', VirtualTag (M.tm.step c).inputPos tag' ∧
      (a2_mapTM M true).tm.step (a2_mapVirtual M c tag p a pre) =
        a2_mapVirtual M (M.tm.step c) tag' p a pre := by
  cases hq : c.state with
  | none =>
    refine ⟨tag, ?_, ?_⟩
    · simpa only [MultiTapeTM.step_of_halt hq] using hb
    · rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt]
      simp [a2_mapVirtual, hq]
  | some q =>
    let act := M.tm.tr q c.inputSymbol c.workTapeSymbols
    let mv := virtualMove tag c.inputSymbol act.inputTape
    have hm := virtualMove_correct c tag hb act.inputTape
    have hc : M.tm.step c = act.apply c := by simp only [MultiTapeTM.step, hq, act]
    refine ⟨virtualNextTag tag mv, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · have hs : (a2_mapVirtual M c tag p a pre).state = some (.run q tag) := by
        simp [a2_mapVirtual, hq]
      have hv : (a2_mapVirtual M c tag p a pre).workTapeSymbols
          (Fin.natAdd 1 (Fin.castAdd M.k (0 : Fin 1))) = c.inputSymbol := by
        simp [a2_mapVirtual, Cfg.workTapeSymbols, bufferTape_inputSymbol]
      have hr : (fun i => (a2_mapVirtual M c tag p a pre).workTapeSymbols
          (Fin.natAdd 1 (Fin.natAdd 1 i))) = c.workTapeSymbols := by
        funext i
        simp [a2_mapVirtual, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only [a2_mapTM]
      rw [hv, hr, hq]
      change (Action.apply _ _) = a2_mapVirtual M (act.apply c) _ p a pre
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp [a2_mapVirtual, Action.apply, act]
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
            simp [a2_mapVirtual, Action.apply, act]
      · funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simp [a2_mapVirtual, Action.apply, act]
        · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
          · simpa only [a2_mapVirtual, Action.apply, tapeBlocks_buffer, ↓reduceIte] using hm.1
          · simp [a2_mapVirtual, Action.apply, act]
      · exact List.append_assoc pre c.output act.output.toList

/-- Payload forwarding preserves its entire source trajectory at all times,
including the final halting action and the stationary halted tail. -/
private lemma a2_mapVirtual_run (M : FinTM Bool) {x y : List Bool}
    (c : Cfg M.k Bool M.State y) (tag : Bool) (hb : VirtualTag c.inputPos tag)
    (p : Fin (x.length + 2)) (a pre : List Bool) (t : ℕ) :
    ∃ tag', VirtualTag (M.tm.runFrom c t).inputPos tag' ∧
      (a2_mapTM M true).tm.runFrom (a2_mapVirtual M c tag p a pre) t =
        a2_mapVirtual M (M.tm.runFrom c t) tag' p a pre := by
  induction t with
  | zero => exact ⟨tag, hb, rfl⟩
  | succ t ih =>
    obtain ⟨b, hb, he⟩ := ih
    obtain ⟨d, hd, hs⟩ := a2_mapVirtual_step M _ b hb p a pre
    refine ⟨d, ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hd
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, hs, MultiTapeTM.runFrom_succ_eq_step']

/-- A setup configuration is at the payload seam if its control is a
payload state; this includes the source start state on empty virtual input. -/
private def a2_mapEntered (M : FinTM Bool) {x : List Bool}
    (c : Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x) : Prop :=
  ∃ q tag, c.state = some (.run q tag)

/-- Setup mode freezes every field once it reaches a payload state. -/
private lemma a2_mapSetup_stationary (M : FinTM Bool) {x : List Bool}
    (c : Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x)
    (h : a2_mapEntered M c) (t : ℕ) : (a2_mapTM M false).tm.runFrom c t = c := by
  obtain ⟨q, tag, hs⟩ := h
  have he : (a2_mapTM M false).tm.step c = c := by
    simp only [MultiTapeTM.step, hs, a2_mapTM, Bool.false_eq_true, ↓reduceIte,
      controlAction_apply, moveInputPos_zero]
    cases c
    simp_all
  induction t with
  | zero => rfl
  | succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih, he]

/-- Before the payload seam the operational and setup transition tables
coincide, on all configurations rather than just well-formed buffers. -/
private lemma a2_mapSetup_step (M : FinTM Bool) {x : List Bool}
    (c : Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x)
    (h : ¬a2_mapEntered M c) :
    (a2_mapTM M true).tm.step c = (a2_mapTM M false).tm.step c := by
  cases hs : c.state with
  | none => simp only [MultiTapeTM.step, hs]
  | some q =>
    cases q with
    | run q tag => exact (h ⟨q, tag, hs⟩).elim
    | parse pending => cases pending <;> simp only [MultiTapeTM.step, hs, a2_mapTM]
    | _ => simp only [MultiTapeTM.step, hs, a2_mapTM]

/-- Transfer an entire setup prefix through the final entry action. -/
private lemma a2_mapSetup_run (M : FinTM Bool) (x : List Bool) (t : ℕ)
    (h : ∀ u < t, ¬a2_mapEntered M
      ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) u)) :
    (a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) t =
      (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun u hu => h u (by omega)),
      a2_mapSetup_step M _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Every setup action leaves each payload work head fixed. -/
private lemma a2_mapSetup_head_step (M : FinTM Bool) {x : List Bool}
    (c : Cfg (1 + (1 + M.k)) Bool (a2_MapState M.State) x) (i : Fin M.k) :
    ((a2_mapTM M false).tm.step c).workTapePos (Fin.natAdd 1 (Fin.natAdd 1 i)) =
      c.workTapePos (Fin.natAdd 1 (Fin.natAdd 1 i)) := by
  have ha (q : a2_MapState M.State) (inp : Option Bool)
      (work : Fin (1 + (1 + M.k)) → Option Bool) :
      ((a2_mapTM M false).tm.tr q inp work).workTapes (Fin.natAdd 1 (Fin.natAdd 1 i)) =
        (none, 0) := by
    cases q with
    | parse pending =>
      cases pending with
      | none => cases inp <;> simp [a2_mapTM, a2_mapAct]
      | some b =>
        cases inp with
        | none => simp [a2_mapTM, a2_mapAct]
        | some d =>
          by_cases he : b = d
          · simp [a2_mapTM, he, a2_mapAct]
          · cases b <;> simp [a2_mapTM, he, a2_mapAct]
    | copyB => cases inp <;> simp [a2_mapTM, a2_mapAct]
    | backB =>
      cases h : work (Fin.natAdd 1 (Fin.castAdd M.k (0 : Fin 1))) <;>
        simp only [a2_mapTM, h, a2_mapAct, tapeBlocks_right]
    | backA =>
      cases h : work (Fin.castAdd (1 + M.k) (0 : Fin 1)) <;>
        simp only [a2_mapTM, h, a2_mapAct, tapeBlocks_right]
    | emitA =>
      cases h : work (Fin.castAdd (1 + M.k) (0 : Fin 1)) <;>
        simp only [a2_mapTM, h, a2_mapAct, tapeBlocks_right]
    | emitAgain b => simp [a2_mapTM, a2_mapAct]
    | separator => simp [a2_mapTM, a2_mapAct]
    | run q tag => rfl
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => rfl
  | some q => simp only [Action.apply, ha]; simp

/-- The payload bank stays at its initial origin throughout setup, with no
condition on grammar validity, buffer widths, or elapsed time. -/
private lemma a2_mapSetup_heads (M : FinTM Bool) (x : List Bool) (t : ℕ) (i : Fin M.k) :
    ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t).workTapePos
      (Fin.natAdd 1 (Fin.natAdd 1 i)) = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', a2_mapSetup_head_step, ih]

/-- Choose the first payload entry, then transfer every prefix to the
operational host. The stationary setup seam identifies this first entry
with the complete validating/buffering/emission endpoint, so no payload
work is hidden in the administrative time bound. -/
private lemma a2_map_launch (M : FinTM Bool) (x a b : List Bool)
    (hd : pairDecode x = some (a, b)) :
    ∃ u ≤ 5 * (x.length + 1),
      (a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u =
        a2_mapVirtual M (M.tm.initCfg b) true ⟨x.length + 1, by omega⟩ a (pairEncode a []) ∧
      ∀ v ≤ u, (a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) v =
        (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v := by
  classical
  obtain ⟨t, ht, he⟩ := a2_map_setup M x
  simp only [hd] at he
  have hex : ∃ u, a2_mapEntered M
      ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) u) := by
    refine ⟨t, M.tm.q₀, true, ?_⟩
    rw [he]
    rfl
  let u := Nat.find hex
  have hu : u ≤ t := Nat.find_min' hex (by rw [he]; exact ⟨M.tm.q₀, true, rfl⟩)
  have hg : ∀ v < u, ¬a2_mapEntered M
      ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v) :=
    fun v hv => Nat.find_min hex hv
  have hprefix (v : ℕ) (hv : v ≤ u) := a2_mapSetup_run M x v
    (fun w hw => hg w (by omega))
  refine ⟨u, hu.trans ht, ?_, hprefix⟩
  rw [hprefix u (le_refl _)]
  have hs := a2_mapSetup_stationary M _ (Nat.find_spec hex) (t - u)
  have hh : (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) t =
      (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) u := by
    rw [show t = u + (t - u) by omega, MultiTapeTM.runFrom_add]
    exact hs
  rw [← hh, he]

/-- A malformed encoding never reaches a payload state, since such a setup
state would remain live forever. Hence its entire operational trajectory
agrees with setup, including the silent halt and every later time. -/
private lemma a2_map_reject (M : FinTM Bool) (x : List Bool)
    (hd : pairDecode x = none) :
    ∃ u ≤ 5 * (x.length + 1),
      ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).state = none ∧
      ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).output = [] ∧
      ∀ v, (a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) v =
        (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v := by
  obtain ⟨u, hu, he⟩ := a2_map_setup M x
  simp only [hd] at he
  have hn (v : ℕ) : ¬a2_mapEntered M
      ((a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v) := by
    intro hv
    obtain ⟨q, tag, hq⟩ := hv
    by_cases h : v ≤ u
    · have hrun : (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) u =
          (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v := by
        rw [show u = v + (u - v) by omega, MultiTapeTM.runFrom_add]
        exact a2_mapSetup_stationary M _ ⟨q, tag, hq⟩ _
      have hh := he.1
      rw [hrun, hq] at hh
      contradiction
    · have hh : (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) v =
          (a2_mapTM M false).tm.runFrom ((a2_mapTM M false).tm.initCfg x) u := by
        rw [show v = u + (v - u) by omega, MultiTapeTM.runFrom_add,
          MultiTapeTM.runFrom_of_halt _ he.1]
      rw [hh, he.1] at hq
      contradiction
  have heq (v : ℕ) := a2_mapSetup_run M x v (fun w _ => hn w)
  refine ⟨u, hu, ?_, ?_, heq⟩ <;> rw [heq u]
  · exact he.1
  · exact he.2

/-- Explicit equivalence between a disjoint pair of banks and their concatenation. -/
private def a2_mapSumEquiv (a b : ℕ) : Fin a ⊕ Fin b ≃ Fin (a + b) where
  toFun := Sum.elim (Fin.castAdd b) (Fin.natAdd a)
  invFun := fun i => if h : (i : ℕ) < a then Sum.inl ⟨i, h⟩
    else Sum.inr ⟨i - a, by have := i.isLt; omega⟩
  left_inv := by
    intro i
    cases i with
    | inl i => simp [i.isLt]
    | inr i =>
      simp only [Sum.elim_inr, Fin.coe_natAdd, not_lt.mpr (Nat.le_add_right _ _), ↓reduceDIte]
      congr 1
      apply Fin.ext
      simp
  right_inv := by
    intro i
    dsimp only
    split
    · rfl
    · apply Fin.ext
      dsimp only [Sum.elim_inr, Fin.coe_natAdd]
      omega

/-- Sum a finite tape bank by its two disjoint blocks. -/
private lemma a2_map_sum {a b : ℕ} (f : Fin (a + b) → ℕ) :
    (∑ i : Fin (a + b), f i) =
      (∑ i : Fin a, f (Fin.castAdd b i)) + ∑ i : Fin b, f (Fin.natAdd a i) := by
  rw [Fintype.sum_equiv (a2_mapSumEquiv a b).symm f (fun i => f ((a2_mapSumEquiv a b).toFun i))]
  · exact Finset.sum_disjSum Finset.univ Finset.univ _
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]

/-- Count the two administrative tapes by fixed integer intervals, and the
payload bank by containment in one source trajectory. No coefficient is
introduced on the source-bank sum. -/
private lemma a2_map_space (M : FinTM Bool) (x y : List Bool) (t D S : ℕ)
    (hfirst : ∀ u ≤ t, -(D : ℤ) ≤
        ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos
          (Fin.castAdd (1 + M.k) (0 : Fin 1)) ∧
      ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos
          (Fin.castAdd (1 + M.k) (0 : Fin 1)) ≤ D)
    (hsecond : ∀ u ≤ t, -(D : ℤ) ≤
        ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos
          (Fin.natAdd 1 (Fin.castAdd M.k (0 : Fin 1))) ∧
      ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos
          (Fin.natAdd 1 (Fin.castAdd M.k (0 : Fin 1))) ≤ D)
    (hsource : ∀ i, (a2_mapTM M true).tm.visitedByTapeHead ((a2_mapTM M true).tm.initCfg x) t
        (Fin.natAdd 1 (Fin.natAdd 1 i)) ⊆ M.tm.visitedByTapeHead (M.tm.initCfg y) t i)
    (hs : M.tm.spaceUsed (M.tm.initCfg y) t ≤ S) :
    (a2_mapTM M true).tm.spaceUsed ((a2_mapTM M true).tm.initCfg x) t ≤ S + 2 * (2 * D + 1) := by
  have hc (i : Fin (1 + (1 + M.k)))
      (h : ∀ u ≤ t, -(D : ℤ) ≤
          ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos i ∧
        ((a2_mapTM M true).tm.runFrom ((a2_mapTM M true).tm.initCfg x) u).workTapePos i ≤ D) :
      (a2_mapTM M true).tm.spaceUsedByTape ((a2_mapTM M true).tm.initCfg x) t i ≤ 2 * D + 1 := by
    have hsub : (a2_mapTM M true).tm.visitedByTapeHead ((a2_mapTM M true).tm.initCfg x) t i ⊆
        Finset.Icc (-(D : ℤ)) (D : ℤ) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (h u (by have := Finset.mem_range.mp hu; omega))
    exact (Finset.card_le_card hsub).trans (by rw [Int.card_Icc]; omega)
  have ha := hc _ hfirst
  have hb := hc _ hsecond
  have hp : (∑ i : Fin M.k, (a2_mapTM M true).tm.spaceUsedByTape
      ((a2_mapTM M true).tm.initCfg x) t (Fin.natAdd 1 (Fin.natAdd 1 i))) ≤ S := by
    exact (Finset.sum_le_sum (fun i _ => Finset.card_le_card (hsource i))).trans hs
  change (∑ i : Fin (1 + (1 + M.k)),
    (a2_mapTM M true).tm.spaceUsedByTape ((a2_mapTM M true).tm.initCfg x) t i) ≤ _
  rw [a2_map_sum, a2_map_sum]
  simp only [Fintype.sum_unique]
  simp only [show (default : Fin 1) = 0 from Subsingleton.elim _ _]
  omega

/-- **Threaded-map space row** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_pairMapSnd`, the round-2
catalog addition). Given a payload machine with its own space bound
`Sg` (monotone, since the payload runs on the second component, which is
no longer than the whole input), the threaded-map controller's space is
the payload's plus linear administration. **The witness is a new
forwarding controller, not the received captured-payload machine**
(round-1 finding 4, the witness-honesty refutation: `pairMapTM`'s
capture tape visits `|g b| + 1` cells — the unary-square payload defeats
any linear administrative claim about it; output length is not bounded
by the payload's work space).

**Proof sketch.** The commissioned controller: validate and buffer the
input pair (`O(n + 1)` cells), emit the encoded first component, then
simulate `Mg` on the buffered second component **forwarding its output**
(the E2/`embedEmitTM` discipline — emissions go to the physical output,
never to a work bank), leaving the payload's work-head trajectories
unchanged — coefficient `1` on `Sg` — plus the linear buffer and
administration; the `Monotone Sg` hypothesis transports the payload
bound from `|b|` to `n`. Named construction obligations for the brief:
the validating buffer stage, the forwarding payload stage, and their
seam. -/
theorem computesFunInTime_pairMapSnd_spaceUsed {Mg : FinTM Bool}
    {g : List Bool → List Bool} {Tg : ℕ → ℕ} (Sg : ℕ → ℕ)
    (hg : Mg.ComputesFunInTime g Tg) (hTg : Monotone Tg)
    (hgs : ∀ (y : List Bool) (t : ℕ),
      Mg.tm.spaceUsed (Mg.tm.initCfg y) t ≤ Sg y.length)
    (hSg : Monotone Sg) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun z => match pairDecode z with
          | some (a, b) => pairEncode a (g b)
          | none => [])
        (fun n => c * (n + 1 + Tg n)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ Sg x.length + c * (x.length + 1) := by
  let M := a2_mapTM Mg true
  refine ⟨M, 22, ?_, ?_⟩
  · intro x
    cases hd : pairDecode x with
    | none =>
      obtain ⟨u, hu, hh, ho, _⟩ := a2_map_reject Mg x hd
      have ht : M.ComputesInTime x [] u := ⟨_, hh, ho, rfl⟩
      simpa only [hd] using ht.mono (show u ≤ 22 * (x.length + 1 + Tg x.length) by omega)
    | some ab =>
      rcases ab with ⟨a, b⟩
      obtain ⟨u, hu, hinit, _⟩ := a2_map_launch Mg x a b hd
      have hlen : b.length ≤ x.length := by
        have h := congrArg List.length (eq_pairEncode_of_pairDecode x a b hd)
        rw [length_pairEncode] at h
        omega
      obtain ⟨tag, _, hr⟩ := a2_mapVirtual_run Mg (x := x) (Mg.tm.initCfg b) true
        (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init])
        (⟨x.length + 1, by omega⟩) a (pairEncode a []) (Tg b.length)
      obtain ⟨space, hh, ho, _⟩ := hg b
      have hrun : M.tm.runFrom (M.tm.initCfg x) (u + Tg b.length) =
          a2_mapVirtual Mg (Mg.tm.runFrom (Mg.tm.initCfg b) (Tg b.length)) tag
            ⟨x.length + 1, by omega⟩ a (pairEncode a []) := by
        rw [MultiTapeTM.runFrom_add, hinit]
        exact hr
      have ht : M.ComputesInTime x (pairEncode a (g b)) (u + Tg b.length) := by
        refine ⟨_, ?_, ?_, rfl⟩
        · rw [hrun]
          change Option.map (fun q => a2_MapState.run q tag)
            (Mg.tm.runFrom (Mg.tm.initCfg b) (Tg b.length)).state = none
          rw [hh]
          rfl
        · rw [hrun]
          change pairEncode a [] ++
            (Mg.tm.runFrom (Mg.tm.initCfg b) (Tg b.length)).output = pairEncode a (g b)
          rw [ho]
          simp [pairEncode, List.append_assoc]
      have hT := hTg hlen
      simpa only [hd] using ht.mono
        (show u + Tg b.length ≤ 22 * (x.length + 1 + Tg x.length) by omega)
  · intro x t
    let D := 5 * (x.length + 1)
    have hshort (v : ℕ) (hv : v ≤ D) (i : Fin M.k) :
        -(D : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) v).workTapePos i ∧
        (M.tm.runFrom (M.tm.initCfg x) v).workTapePos i ≤ D := by
      have h := f2_head_steps M.tm (M.tm.initCfg x) v i
      rw [show (M.tm.initCfg x).workTapePos i = 0 from rfl, zero_sub, zero_add] at h
      constructor <;> omega
    cases hd : pairDecode x with
    | none =>
      obtain ⟨u, hu, hh, _, heq⟩ := a2_map_reject Mg x hd
      have hheads (v : ℕ) (i : Fin M.k) :
          -(D : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) v).workTapePos i ∧
          (M.tm.runFrom (M.tm.initCfg x) v).workTapePos i ≤ D := by
        by_cases hv : v ≤ u
        · exact hshort v (hv.trans hu) i
        · rw [show v = u + (v - u) by omega, MultiTapeTM.runFrom_add,
            MultiTapeTM.runFrom_of_halt _ hh]
          exact hshort u hu i
      have hp (i : Fin Mg.k) : M.tm.visitedByTapeHead (M.tm.initCfg x) t
          (Fin.natAdd 1 (Fin.natAdd 1 i)) ⊆ Mg.tm.visitedByTapeHead (Mg.tm.initCfg x) t i := by
        intro z hz
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
        change ((a2_mapTM Mg true).tm.runFrom _ v).workTapePos _ ∈ _
        rw [heq v, a2_mapSetup_heads]
        exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
      have hs := a2_map_space Mg x x t D (Sg x.length)
        (fun v _ => hheads v _) (fun v _ => hheads v _) hp (hgs x t)
      change M.tm.spaceUsed (M.tm.initCfg x) t ≤ _ at hs
      dsimp only [D] at hs
      omega
    | some ab =>
      rcases ab with ⟨a, b⟩
      obtain ⟨u, hu, hinit, hprefix⟩ := a2_map_launch Mg x a b hd
      have hlen : a.length ≤ x.length ∧ b.length ≤ x.length := by
        have h := congrArg List.length (eq_pairEncode_of_pairDecode x a b hd)
        rw [length_pairEncode] at h
        omega
      have hrun (v : ℕ) : ∃ tag,
          M.tm.runFrom (M.tm.initCfg x) (u + v) =
            a2_mapVirtual Mg (Mg.tm.runFrom (Mg.tm.initCfg b) v) tag
              ⟨x.length + 1, by omega⟩ a (pairEncode a []) := by
        obtain ⟨tag, _, he⟩ := a2_mapVirtual_run Mg (x := x) (Mg.tm.initCfg b) true
          (by simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init])
          (⟨x.length + 1, by omega⟩) a (pairEncode a []) v
        refine ⟨tag, ?_⟩
        rw [MultiTapeTM.runFrom_add, hinit]
        exact he
      have ha (v : ℕ) : -(D : ℤ) ≤
          (M.tm.runFrom (M.tm.initCfg x) v).workTapePos (Fin.castAdd (1 + Mg.k) (0 : Fin 1)) ∧
          (M.tm.runFrom (M.tm.initCfg x) v).workTapePos (Fin.castAdd (1 + Mg.k) (0 : Fin 1)) ≤ D := by
        by_cases hv : v ≤ u
        · exact hshort v (hv.trans hu) _
        · obtain ⟨tag, he⟩ := hrun (v - u)
          rw [show v = u + (v - u) by omega, he]
          simp only [a2_mapVirtual, tapeBlocks_left]
          dsimp only [D]
          constructor <;> omega
      have hb (v : ℕ) : -(D : ℤ) ≤
          (M.tm.runFrom (M.tm.initCfg x) v).workTapePos (Fin.natAdd 1 (Fin.castAdd Mg.k (0 : Fin 1))) ∧
          (M.tm.runFrom (M.tm.initCfg x) v).workTapePos (Fin.natAdd 1 (Fin.castAdd Mg.k (0 : Fin 1))) ≤ D := by
        by_cases hv : v ≤ u
        · exact hshort v (hv.trans hu) _
        · obtain ⟨tag, he⟩ := hrun (v - u)
          rw [show v = u + (v - u) by omega, he]
          simp only [a2_mapVirtual, tapeBlocks_buffer]
          have hp := (Mg.tm.runFrom (Mg.tm.initCfg b) (v - u)).inputPos.isLt
          dsimp only [D]
          constructor <;> omega
      -- Each payload-bank head is either still at its source origin or is
      -- exactly a source position at a time no greater than this horizon.
      have hp (i : Fin Mg.k) : M.tm.visitedByTapeHead (M.tm.initCfg x) t
          (Fin.natAdd 1 (Fin.natAdd 1 i)) ⊆ Mg.tm.visitedByTapeHead (Mg.tm.initCfg b) t i := by
        intro z hz
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
        have hvt : v ≤ t := by have := Finset.mem_range.mp hv; omega
        by_cases hvu : v ≤ u
        · change ((a2_mapTM Mg true).tm.runFrom _ v).workTapePos _ ∈ _
          rw [hprefix v hvu, a2_mapSetup_heads]
          exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩
        · obtain ⟨tag, he⟩ := hrun (v - u)
          change (M.tm.runFrom (M.tm.initCfg x) v).workTapePos _ ∈ _
          rw [show v = u + (v - u) by omega, he]
          simp only [a2_mapVirtual, tapeBlocks_right]
          exact Finset.mem_image.mpr ⟨v - u, Finset.mem_range.mpr (by omega), rfl⟩
      have hs := a2_map_space Mg x b t D (Sg x.length)
        (fun v _ => ha v) (fun v _ => hb v) hp ((hgs b t).trans (hSg hlen.2))
      change M.tm.spaceUsed (M.tm.initCfg x) t ≤ _ at hs
      dsimp only [D] at hs
      omega

/-- A live endpoint rules out a halt anywhere in its preceding run. -/
private lemma f2_loop_live_prefix {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom cfg t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom cfg u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom cfg t = tm.runFrom cfg u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- An empty final output forces every earlier output to be empty. -/
private lemma f2_loop_silent_prefix {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom cfg t).output = []) :
    ∀ u ≤ t, (tm.runFrom cfg u).output = [] := by
  intro u hu
  have hp := tm.output_prefix cfg hu
  rw [ht] at hp
  simpa using hp

/-- Replace a possibly padded halting-time witness by its first halt,
retaining the entire endpoint configuration.
**Proof sketch.** Choose the least halting time. Minimality supplies the
strict liveness guard; the absorbing-halt law identifies its endpoint
with the original, possibly later, witness. -/
private lemma f2_loop_first_halt {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧
      (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      (tm.runFrom cfg u).state = none ∧ tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, ?_, hu, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · intro v hv
    exact Nat.find_min h hv
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hu]

/-- The declared invariant holds at each orbit word, including unreachable
rounds after an earlier acceptance. -/
private lemma f2_loop_orbit_inv (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool) (s0 : List Bool → List Bool)
    (hInv0 : ∀ x, Inv x (s0 x))
    (hInvStep : ∀ x s, Inv x s → Inv x (stepF x s)) (x : List Bool) (i : ℕ) :
    Inv x ((stepF x)^[i] (s0 x)) := by
  induction i with
  | zero => exact hInv0 x
  | succ i ih => rw [Function.iterate_succ_apply']; exact hInvStep x _ ih

/-- The fuel run bounds the fixed counter width on each actual input. -/
private lemma f2_loop_fuel_width (F : FinTM Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    (Nat.bits (R x.length)).length ≤ T x.length := by
  obtain ⟨s, hhalt, hout, hspace⟩ := hF x
  simpa only [hout] using F.tm.output_length_le x (T x.length)

/-- One native input-head move increases its position by at most one. -/
private lemma f2_loop_input_move_le {n : ℕ} (p : Fin (n + 2)) (m : SignType) :
    (moveInputPos p m).val ≤ p.val + 1 := by
  cases m with
  | zero => simp
  | neg => rw [moveInputPos_neg_val]; omega
  | pos =>
    by_cases hp : p.val = n + 1
    · have he : p = ⟨n + 1, by omega⟩ := Fin.ext hp
      rw [he]
      simp only [SignType.pos_eq_one, moveInputPos_rightBoundary]
      omega
    · rw [moveInputPos_pos_of_ne_right p hp]

/-- Input displacement is bounded by elapsed time, even for sublinear budgets. -/
private lemma f2_loop_input_run_le {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) :
    (tm.runFrom c t).inputPos.val ≤ c.inputPos.val + t := by
  have stepBound (d : Cfg k Bool S x) : (tm.step d).inputPos.val ≤ d.inputPos.val + 1 := by
    cases hd : d.state with
    | none => simp [MultiTapeTM.step, hd]
    | some q =>
      simpa only [MultiTapeTM.step, hd, Action.apply] using
        f2_loop_input_move_le d.inputPos (tm.tr q d.inputSymbol d.workTapeSymbols).inputTape
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (stepBound _).trans (by omega)

/-- A run appends at most one output bit per step, from any seam configuration. -/
private lemma f2_loop_output_length_le {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ) :
    (tm.runFrom c t).output.length ≤ c.output.length + t := by
  have stepBound (d : Cfg k Bool S x) : (tm.step d).output.length ≤ d.output.length + 1 := by
    rw [MultiTapeTM.step_output, List.length_append]
    cases tm.outputSymbol d <;> simp
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (stepBound _).trans (by omega)

/-- The input rewind has a bound in its starting position, so it can be
charged to the preceding run without scanning the entire input.
**Proof sketch.** Take the mandatory first left move and apply the proved
`rewind_scan` at the resulting position. Its exact scan time is position
plus one; the first left move never increases position. -/
private lemma f2_loop_rewind_bounded {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some start) :
    ∃ t ≤ cfg.inputPos.val + 2,
      tm.runFrom cfg t = {cfg with state := dest, inputPos := 1} := by
  have hstep : tm.step cfg =
      {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
    unfold MultiTapeTM.step
    rw [hs]
    dsimp only
    rw [hstart, controlAction_apply]
  let c := tm.step cfg
  have hc : c.state = some scan := by simp only [c, hstep]
  have hp : c.inputPos.val ≤ x.length := by
    simp only [c, hstep, moveInputPos_neg_val]
    have := cfg.inputPos.isLt
    omega
  refine ⟨1 + (c.inputPos.val + 1), ?_, ?_⟩
  · simp only [c, hstep, moveInputPos_neg_val]
    omega
  · rw [MultiTapeTM.runFrom_add]
    have hfirst : tm.runFrom cfg 1 = c := rfl
    rw [hfirst, rewind_scan tm scan dest hscan c hc hp]
    simp only [c, hstep]

/-- Fixed-width little-endian decrement and its success flag. Underflow
sets the existing cells to true and returns false, without extending the word. -/
private def f2_loopDebit : List Bool → List Bool × Bool
  | [] => ([], false)
  | true :: bs => (false :: bs, true)
  | false :: bs => (true :: (f2_loopDebit bs).1, (f2_loopDebit bs).2)

/-- Number of low zero bits traversed by a borrow. -/
private def f2_loopBorrowPos : List Bool → ℕ
  | false :: bs => f2_loopBorrowPos bs + 1
  | _ => 0

/-- The borrow scan cannot cross more cells than the fixed width. -/
private lemma f2_loopBorrowPos_le (u : List Bool) : f2_loopBorrowPos u ≤ u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp only [f2_loopBorrowPos, List.length_cons] <;> omega

/-- Both successful decrements and underflow preserve the counter width. -/
private lemma f2_loopDebit_length (u : List Bool) : (f2_loopDebit u).1.length = u.length := by
  induction u with
  | nil => rfl
  | cons b u ih => cases b <;> simp [f2_loopDebit, ih]

/-- Little-endian counter value; high zero cells contribute nothing. -/
private def f2_loopValue : List Bool → ℕ
  | [] => 0
  | b :: bs => 2 * f2_loopValue bs + if b then 1 else 0

/-- The fuel machine's binary word has its declared numerical value. -/
private lemma f2_loopValue_bits (n : ℕ) : f2_loopValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [f2_loopValue]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b <;> simp [f2_loopValue, ih, Nat.bit_val]

/-- A successful debit reduces value by one; underflow occurs only at zero.
**Proof sketch.** A low one is cleared immediately. A low zero becomes one
while the inductive debit reduces the higher part; doubling that equation
gives the successor equation for the full word. -/
private lemma f2_loopDebit_value (u : List Bool) :
    if (f2_loopDebit u).2 then f2_loopValue (f2_loopDebit u).1 + 1 = f2_loopValue u
    else f2_loopValue u = 0 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    cases b with
    | true => simp [f2_loopDebit, f2_loopValue]
    | false =>
      cases h : (f2_loopDebit u).2 <;>
        simp only [f2_loopDebit, h, Bool.false_eq_true, ↓reduceIte,
          f2_loopValue, Nat.add_zero] at ih ⊢ <;> omega

/-- The borrow returns success exactly for positive counter values. -/
private lemma f2_loopDebit_success (u : List Bool) :
    (f2_loopDebit u).2 = true ↔ 0 < f2_loopValue u := by
  have h := f2_loopDebit_value u
  cases hb : (f2_loopDebit u).2
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    simp [h]
  · simp only [hb, ↓reduceIte] at h
    simp only [true_iff]
    omega

/-- Iterating debit retains the original fixed width at every index. -/
private lemma f2_loopDebit_iterate_length (u : List Bool) (i : ℕ) :
    ((fun w => (f2_loopDebit w).1)^[i] u).length = u.length := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', f2_loopDebit_length, ih]

/-- Before exhaustion, the counter after `i` debits has value `R-i`.
**Proof sketch.** Start from the fuel word's value. Before the last debit
the induction hypothesis gives a positive value, so the success equation
reduces it by exactly one. No representation is shortened. -/
private lemma f2_loopDebit_iterate_value (R i : ℕ) (hi : i ≤ R) :
    f2_loopValue ((fun w => (f2_loopDebit w).1)^[i] R.bits) = R - i := by
  induction i with
  | zero => simpa using f2_loopValue_bits R
  | succ i ih =>
    have hv := ih (by omega)
    have hs : (f2_loopDebit ((fun w => (f2_loopDebit w).1)^[i] R.bits)).2 = true :=
      (f2_loopDebit_success _).2 (by omega)
    have hd := f2_loopDebit_value ((fun w => (f2_loopDebit w).1)^[i] R.bits)
    simp only [hs, ↓reduceIte] at hd
    rw [Function.iterate_succ_apply']
    omega

/-- Read the first bit of a suffix, with the empty suffix represented by blank. -/
private lemma f2_loopBuffer_read (pre bs : List Bool) :
    bufferTape (pre ++ bs) pre.length = bs.head? := by
  simp only [bufferTape_nat, List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases bs <;> rfl

/-- Writing at the start of a nonempty suffix preserves the prefix and width.
**Proof sketch.** At the write position use the new bit. Before and after
that position both tapes read the same unchanged entries. -/
private lemma f2_loopBuffer_write (pre bs : List Bool) (old new : Bool) :
    Function.update (bufferTape (pre ++ old :: bs)) (pre.length : ℤ) (some new) =
      bufferTape (pre ++ new :: bs) := by
  funext z
  by_cases hz : z = (pre.length : ℤ)
  · subst z; simp
  · rw [Function.update_of_ne hz]
    unfold bufferTape
    by_cases hn : 0 ≤ z
    · simp only [if_pos hn]
      by_cases hl : z.toNat < pre.length
      · rw [List.getElem?_append_left hl, List.getElem?_append_left hl]
      · have hg : pre.length < z.toNat := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        simp only [List.getElem?_cons, if_neg (by omega : z.toNat - pre.length ≠ 0)]
    · simp only [if_neg hn]

/-- One-tape fixed-width decrement, followed by a rewind. The live states are
borrow (`inl none`), rewind with success flag (`inl (some b)`), and return
(`inr b`). No transition emits physical output. Return states wait for a
surrounding controller. This privately re-derives the counter template. -/
private def f2_loopDebitTM : FinTM Bool where
  k := 1
  State := Option Bool ⊕ Bool
  tm :=
    { q₀ := .inl none
      tr := fun q _ work => match q with
        | .inl none => match work 0 with
          | some false => ⟨0, fun _ => (some (some true), .pos), none, some (.inl none)⟩
          | some true => ⟨0, fun _ => (some (some false), .neg), none, some (.inl (some true))⟩
          | none => ⟨0, fun _ => (none, .neg), none, some (.inl (some false))⟩
        | .inl (some b) => match work 0 with
          | some _ => ⟨0, fun _ => (none, .neg), none, some (.inl (some b))⟩
          | none => ⟨0, fun _ => (none, .pos), none, some (.inr b)⟩
        | .inr b => controlAction 0 (some (.inr b)) }

/-- A candidate on the borrow tape, with arbitrary native input-head position. -/
private def f2_loopDebitCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Bool ⊕ Bool) (z : ℤ) (u : List Bool) :
    Cfg f2_loopDebitTM.k Bool f2_loopDebitTM.State x :=
  ⟨some q, p, fun _ => bufferTape u, fun _ => z, []⟩

/-- One borrow transition writes only inside the fixed-width word, or detects
the right blank without writing to it. -/
private lemma f2_loopBorrow_step (x : List Bool) (p : Fin (x.length + 2))
    (pre bs : List Bool) :
    f2_loopDebitTM.tm.step (f2_loopDebitCfg x p (.inl none) pre.length (pre ++ bs)) =
      match bs with
      | [] => f2_loopDebitCfg x p (.inl (some false)) (pre.length - 1) pre
      | true :: us => f2_loopDebitCfg x p (.inl (some true)) (pre.length - 1) (pre ++ false :: us)
      | false :: us => f2_loopDebitCfg x p (.inl none) (pre.length + 1) (pre ++ true :: us) := by
  unfold MultiTapeTM.step
  change (f2_loopDebitTM.tm.tr (.inl none) _ _).apply _ = _
  simp only [f2_loopDebitTM, f2_loopDebitCfg, Cfg.workTapeSymbols, f2_loopBuffer_read]
  cases bs with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    · simp
    · funext i; simp [Action.apply, sub_eq_add_neg]
  | cons b bs =>
    cases b <;> refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
    all_goals first
      | (funext i; exact f2_loopBuffer_write pre bs _ _)
      | (funext i; simp [Action.apply, sub_eq_add_neg])

/-- The borrow phase takes one step beyond the leading false prefix, including
one blank test on underflow.
**Proof sketch.** Induct on the remaining candidate. Each false bit is set
and added to the processed prefix. A true bit or the right blank starts
rewind without changing the width. -/
private lemma f2_loopBorrow_run (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) : ∀ pre : List Bool,
    f2_loopDebitTM.tm.runFrom (f2_loopDebitCfg x p (.inl none) pre.length (pre ++ u))
        (f2_loopBorrowPos u + 1) =
      f2_loopDebitCfg x p (.inl (some (f2_loopDebit u).2))
        ((pre.length : ℤ) + f2_loopBorrowPos u - 1) (pre ++ (f2_loopDebit u).1) := by
  induction u with
  | nil =>
    intro pre
    simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
      f2_loopBorrow_step x p pre []
  | cons b u ih =>
    intro pre
    cases b with
    | true =>
      simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
        f2_loopBorrow_step x p pre (true :: u)
    | false =>
      simp only [f2_loopBorrowPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_loopBorrow_step]
      simpa [f2_loopDebit, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])

/-- Rewind over `j` known candidate cells to the left blank, then return at
cell zero in exactly `j+1` steps, retaining the candidate and success flag. -/
private lemma f2_loopBorrow_rewind (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) (b : Bool) : ∀ j, j ≤ u.length →
    f2_loopDebitTM.tm.runFrom (f2_loopDebitCfg x p (.inl (some b)) ((j : ℤ) - 1) u)
        (j + 1) = f2_loopDebitCfg x p (.inr b) 0 u := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [Nat.cast_zero, zero_sub]
    unfold MultiTapeTM.step
    simp only [f2_loopDebitTM, f2_loopDebitCfg, Cfg.workTapeSymbols, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hstep : f2_loopDebitTM.tm.step
        (f2_loopDebitCfg x p (.inl (some b)) ((j + 1 : ℕ) - 1) u) =
          f2_loopDebitCfg x p (.inl (some b)) ((j : ℤ) - 1) u := by
      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      rw [hz]
      unfold MultiTapeTM.step
      simp only [f2_loopDebitTM, f2_loopDebitCfg, Cfg.workTapeSymbols, bufferTape_nat,
        List.getElem?_eq_getElem (by omega : j < u.length)]
      refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [hstep]
    exact ih (by omega)

/-- A complete fixed-width decrement and rewind costs `2j+2 ≤ 2|u|+2`,
where `j` is the leading false-prefix length. It returns live at cell zero,
retains the input head, and emits nothing. Width zero returns underflow only
when this subroutine is called, so enumeration can process `[]` first. -/
private lemma f2_loopBorrow_correct (x : List Bool) (p : Fin (x.length + 2))
    (u : List Bool) :
    2 * f2_loopBorrowPos u + 2 ≤ 2 * u.length + 2 ∧
      f2_loopDebitTM.tm.runFrom (f2_loopDebitCfg x p (.inl none) 0 u)
          (2 * f2_loopBorrowPos u + 2) =
        f2_loopDebitCfg x p (.inr (f2_loopDebit u).2) 0 (f2_loopDebit u).1 := by
  refine ⟨by have := f2_loopBorrowPos_le u; omega, ?_⟩
  have hr := f2_loopBorrow_run x p u []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * f2_loopBorrowPos u + 2 = (f2_loopBorrowPos u + 1) + (f2_loopBorrowPos u + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact f2_loopBorrow_rewind x p (f2_loopDebit u).1 (f2_loopDebit u).2 _
    (by rw [f2_loopDebit_length]; exact f2_loopBorrowPos_le u)

/-- Stop the body at the next anchor entry, distinguishing that return from
a genuine source halt on an extra one-cell flag tape. A true release bit
forces one source action, even at the anchor; every source successor clears
the release bit. The body's full output is retained for subsequent capture. -/
private def f2_loopBodyTM (body : FinTM Bool) (anchor : body.State) : FinTM Bool where
  k := body.k + 1
  State := body.State × Bool
  tm :=
    { q₀ := (body.tm.q₀, false)
      tr := fun q inp work =>
        if q.1 = anchor ∧ q.2 = false then
          { inputTape := 0
            workTapes := fun i =>
              if (i : ℕ) < body.k then (none, 0) else (some (some false), 0)
            output := none
            state := none }
        else
          let a := body.tm.tr q.1 inp (fun i => work i.castSucc)
          { inputTape := a.inputTape
            workTapes := fun i =>
              if h : (i : ℕ) < body.k then a.workTapes ⟨i, h⟩
              else (if a.state = none then some (some true) else none, 0)
            output := a.output
            state := a.state.map (fun s => (s, false)) } }

/-- Embed a source configuration with its release bit and the one-cell
halt-kind flag. The flag head stays at the origin throughout a body call. -/
private def f2_loopBodyCfg (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (flag : Option Bool) :
    Cfg (f2_loopBodyTM body anchor).k Bool (f2_loopBodyTM body anchor).State x where
  state := c.state.map (fun s => (s, release))
  inputPos := c.inputPos
  workTapes := fun i => if h : (i : ℕ) < body.k then c.workTapes ⟨i, h⟩
    else fun z => if z = 0 then flag else none
  workTapePos := fun i => if h : (i : ℕ) < body.k then c.workTapePos ⟨i, h⟩ else 0
  output := c.output

/-- At an unreleased anchor the stop wrapper takes one silent step and
records rejection, without changing the body's configuration data. -/
private lemma f2_loopBody_stop (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (hc : c.state = some anchor) (flag : Option Bool) :
    (f2_loopBodyTM body anchor).tm.step (f2_loopBodyCfg body anchor c false flag) =
      f2_loopBodyCfg body anchor {c with state := none} false (some false) := by
  unfold MultiTapeTM.step
  simp only [f2_loopBodyCfg, hc, Option.map_some, f2_loopBodyTM, and_self, ↓reduceIte]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z
    by_cases hi : (i : ℕ) < body.k
    · simp [Action.apply, hi]
    · simp only [Action.apply, hi, ↓reduceIte]
      by_cases hz : z = 0 <;> simp [hz, hi, Function.update]
  · funext i
    by_cases hi : (i : ℕ) < body.k <;> simp [Action.apply, hi]
  · simp [Action.apply]

/-- Away from an unreleased anchor, the wrapper executes exactly one body
action and records a true flag precisely on a genuine halting transition. -/
private lemma f2_loopBody_step (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (q : body.State) (release : Bool)
    (flag : Option Bool) (hc : c.state = some q)
    (hgo : ¬(q = anchor ∧ release = false)) :
    (f2_loopBodyTM body anchor).tm.step (f2_loopBodyCfg body anchor c release flag) =
      f2_loopBodyCfg body anchor (body.tm.step c) false
        (if (body.tm.step c).state = none then some true else flag) := by
  let a := body.tm.tr q c.inputSymbol c.workTapeSymbols
  have hb : body.tm.step c = a.apply c := by simp only [MultiTapeTM.step, hc, a]
  rw [hb]
  unfold MultiTapeTM.step
  simp only [f2_loopBodyCfg, hc, Option.map_some, f2_loopBodyTM, hgo, ↓reduceIte]
  have hr : (fun i : Fin body.k =>
      (f2_loopBodyCfg body anchor c release flag).workTapeSymbols i.castSucc) =
        c.workTapeSymbols := by
    funext i
    simp [f2_loopBodyCfg, Cfg.workTapeSymbols, i.isLt]
  change (let a' : Action body.k Bool body.State :=
            body.tm.tr q c.inputSymbol (fun i : Fin body.k =>
              (f2_loopBodyCfg body anchor c release flag).workTapeSymbols i.castSucc);
    ({
      inputTape := a'.inputTape
      workTapes := fun i => if h : (i : ℕ) < body.k then a'.workTapes ⟨i, h⟩
        else (if a'.state = none then some (some true) else none, 0)
      output := a'.output
      state := a'.state.map (fun s => (s, false)) } :
        Action (body.k + 1) Bool (body.State × Bool))).apply _ = _
  rw [hr]
  dsimp only
  dsimp only [a] at *
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : (i : ℕ) < body.k
    · simp [Action.apply, hi]
    · by_cases ha : (body.tm.tr q c.inputSymbol c.workTapeSymbols).state = none
      · simp only [Action.apply, hi, ↓reduceDIte, ha, ↓reduceIte]
        by_cases hz : z = 0 <;> simp [hz, hi, Function.update]
      · simp [Action.apply, hi, ha]
  · funext i
    by_cases hi : (i : ℕ) < body.k <;> simp [Action.apply, hi]

/-- Up to the first halt or anchor return, the stop wrapper simulates the
body exactly. The release flag is consumed by the first action.
**Proof sketch.** Induct on elapsed time. Strict liveness supplies a source
state; the no-anchor condition, except for the released first action,
enables the one-step lemma. Its flag update records a halting emission's
transition without discarding that emission. -/
private lemma f2_loopBody_run (body : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (hc : c.state ≠ none)
    (t : ℕ) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none) t =
      f2_loopBodyCfg body anchor (body.tm.runFrom c t) (if t = 0 then release else false)
        (if (body.tm.runFrom c t).state = none then some true else none) := by
  induction t with
  | zero => simp [hc]
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    rw [ih (fun u hu => hlive u (by omega)) (fun u hu => hanchor u (by omega))]
    have ht := hlive t (by omega)
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp ht
    have hgo : ¬(q = anchor ∧ (if t = 0 then release else false) = false) := by
      rcases hanchor t (by omega) with ⟨hz, hr⟩ | hn
      · simp [hz, hr]
      · rintro ⟨rfl, _⟩
        exact hn hq
    rw [if_neg ht, f2_loopBody_step body anchor _ q _ none hq hgo]
    simp only [Nat.succ_ne_zero, ↓reduceIte, MultiTapeTM.runFrom_succ_eq_step']

/-- W1 captures the stopped body's complete trace in any agreeing controller.
This includes an output bit emitted by the halting transition.
**Proof sketch.** The preceding simulation gives strict liveness of the
stop wrapper before the endpoint. Apply the audited capture contract with
the supplied controller as host, then substitute the simulated endpoint. -/
private lemma f2_loopBody_capture (body : FinTM Bool) (anchor : body.State)
    {H : Type*} {x : List Bool} (host : MultiTapeTM (body.k + 1 + 1) Bool H)
    (emb : body.State × Bool → H) (ret : H)
    (hagree : ∀ s inp work, host.tr (emb s) inp work =
      captureAction emb ret ((f2_loopBodyTM body anchor).tm.tr s inp fun i => work i.castSucc))
    (c : Cfg body.k Bool body.State x) (release : Bool) (hc : c.state ≠ none)
    (t : ℕ) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    host.runFrom (captureCfg emb ret [] [] (f2_loopBodyCfg body anchor c release none)) t =
      captureCfg emb ret [] []
        (f2_loopBodyCfg body anchor (body.tm.runFrom c t) (if t = 0 then release else false)
          (if (body.tm.runFrom c t).state = none then some true else none)) := by
  have hguard : ∀ u < t,
      ¬((f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none) u).Halted := by
    intro u hu
    rw [f2_loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, f2_loopBodyCfg] using hlive u hu
  rw [capture_run (f2_loopBodyTM body anchor).tm host emb ret hagree [] [] _ t hguard,
    f2_loopBody_run body anchor c release hc t hlive hanchor]

/-- Disjoint finite control for fuel, body calls, and fourteen controller phases. -/
private abbrev f2_LoopHostState (body F : FinTM Bool) :=
  F.State ⊕ ((Bool × (body.State × Bool)) ⊕ Fin 14)

/-- Relocate the fuel machine past the untouched body, flag, and counter tapes. -/
private def f2_loopFuelSource (body F : FinTM Bool) :
    MultiTapeTM (body.k + 1 + (1 + F.k)) Bool F.State where
  q₀ := F.tm.q₀
  tr := fun q inp work =>
    rightAction (body.k + 1) id (rightAction 1 id
      (F.tm.tr q inp fun i => work (Fin.natAdd (body.k + 1) (Fin.natAdd 1 i))))

/-- Extend the stopped body with a preserved counter and the fuel-phase residue. -/
private def f2_loopBodySource (body F : FinTM Bool) (anchor : body.State) :
    MultiTapeTM (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) where
  q₀ := (body.tm.q₀, false)
  tr := fun q inp work => leftAction (1 + F.k) id
    ((f2_loopBodyTM body anchor).tm.tr q inp fun i => work (Fin.castAdd (1 + F.k) i))

/-- A controller action touches only the flag, counter, and capture tapes. -/
private def f2_loopControlAction (body F : FinTM Bool) (inp : SignType)
    (flag : Option (Option Bool)) (counter payload : Option (Option Bool) × SignType)
    (out : Option Bool) (next : Option (f2_LoopHostState body F)) :
    Action (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) where
  inputTape := inp
  workTapes := fun i =>
    if (i : ℕ) = body.k then (flag, 0)
    else if (i : ℕ) = body.k + 1 then counter
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then payload
    else (none, 0)
  output := out
  state := next

/-- Concrete loop controller, with fixed-verdict and payload-replay modes.
Fuel is captured, rewound, copied into the fixed-width counter while the
capture tape is cleared, and both heads are rewound together. Two further
phases rewind the native input before starting the body. Body startup and
active rounds have disjoint return states; only an active rejection debits.
The release bit forces one body action before another anchor is recognized.

Control phases: 0/1 fuel rewind; 2 counter copy; 3 counter/capture rewind;
4/5 input rewind; 6 startup return; 7 round return; 8 borrow; 9/10 successful
and underflow rewinds; 11 exhaustion; 12/13 payload rewind and replay.
The fuel work tapes are never cleared or reused after the fuel phase. -/
private def f2_loopHost (body F : FinTM Bool) (anchor : body.State) (findMode : Bool) :
    FinTM Bool where
  k := body.k + 1 + (1 + F.k) + 1
  State := f2_LoopHostState body F
  tm :=
    { q₀ := .inl F.tm.q₀
      tr := fun q inp work =>
        let ctrl (j : Fin 14) : f2_LoopHostState body F := .inr (.inr j)
        let call (startup : Bool) (s : body.State × Bool) : f2_LoopHostState body F :=
          .inr (.inl (startup, s))
        let flag : Fin (body.k + 1 + (1 + F.k) + 1) := ⟨body.k, by omega⟩
        let counter : Fin (body.k + 1 + (1 + F.k) + 1) := ⟨body.k + 1, by omega⟩
        let payload := Fin.last (body.k + 1 + (1 + F.k))
        let act := f2_loopControlAction body F
        match q with
        | .inl s => captureAction Sum.inl (ctrl 0)
            ((f2_loopFuelSource body F).tr s inp fun i => work i.castSucc)
        | .inr (.inl (startup, s)) =>
            captureAction (call startup) (ctrl (if startup then 6 else 7))
              ((f2_loopBodySource body F anchor).tr s inp fun i => work i.castSucc)
        | .inr (.inr phase) =>
            if phase = 0 then act 0 none (none, 0) (none, .neg) none (some (ctrl 1))
            else if phase = 1 then
              match work payload with
              | some _ => act 0 none (none, 0) (none, .neg) none (some (ctrl 1))
              | none => act 0 none (none, 0) (none, .pos) none (some (ctrl 2))
            else if phase = 2 then
              match work payload with
              | some b => act 0 none (some (some b), .pos) (some none, .pos) none
                  (some (ctrl 2))
              | none => act 0 none (none, .neg) (none, .neg) none (some (ctrl 3))
            else if phase = 3 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, .neg) none (some (ctrl 3))
              | none => act 0 none (none, .pos) (none, .pos) none (some (ctrl 4))
            else if phase = 4 then act .neg none (none, 0) (none, 0) none (some (ctrl 5))
            else if phase = 5 then
              match inp with
              | some _ => act .neg none (none, 0) (none, 0) none (some (ctrl 5))
              | none => act .pos none (none, 0) (none, 0) none
                  (some (call true (body.tm.q₀, false)))
            else if phase = 6 then act 0 (some none) (none, 0) (none, 0) none
              (some (call false (anchor, true)))
            else if phase = 7 then
              if work flag = some true then
                if findMode then act 0 none (none, 0) (none, .neg) none (some (ctrl 12))
                else act 0 none (none, 0) (none, 0) (some true) none
              else act 0 (some none) (none, 0) (none, 0) none (some (ctrl 8))
            else if phase = 8 then
              match work counter with
              | some false => act 0 none (some (some true), .pos) (none, 0) none
                  (some (ctrl 8))
              | some true => act 0 none (some (some false), .neg) (none, 0) none
                  (some (ctrl 9))
              | none => act 0 none (none, .neg) (none, 0) none (some (ctrl 10))
            else if phase = 9 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, 0) none (some (ctrl 9))
              | none => act 0 none (none, .pos) (none, 0) none
                  (some (call false (anchor, true)))
            else if phase = 10 then
              match work counter with
              | some _ => act 0 none (none, .neg) (none, 0) none (some (ctrl 10))
              | none => act 0 none (none, .pos) (none, 0) none (some (ctrl 11))
            else if phase = 11 then
              act 0 none (none, 0) (none, 0) (if findMode then none else some false) none
            else if phase = 12 then
              match work payload with
              | some _ => act 0 none (none, 0) (none, .neg) none (some (ctrl 12))
              | none => act 0 none (none, 0) (none, .pos) none (some (ctrl 13))
            else
              match work payload with
              | some b => act 0 none (none, 0) (none, .pos) (some b) (some (ctrl 13))
              | none => act 0 none (none, 0) (none, 0) none none }

/-- The concrete host's body states agree with W1 on the entire source table;
startup and active calls return to distinct controller phases. -/
private lemma f2_loopHost_body_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x) (t : ℕ)
    (hlive : ∀ u < t, ¬((f2_loopBodySource body F anchor).runFrom c u).Halted) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
          (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] [] c) t =
      captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
        (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] []
        ((f2_loopBodySource body F anchor).runFrom c t) := by
  exact capture_run (f2_loopBodySource body F anchor) (f2_loopHost body F anchor findMode).tm
    _ _ (by intro s inp work; rfl) [] [] c t hlive

/-- The fuel states capture all fuel emissions directly in the concrete host. -/
private lemma f2_loopHost_fuel_capture (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (c : Cfg (body.k + 1 + (1 + F.k)) Bool F.State x) (t : ℕ)
    (hlive : ∀ u < t, ¬((f2_loopFuelSource body F).runFrom c u).Halted) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] c) t =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((f2_loopFuelSource body F).runFrom c t) := by
  exact capture_run (f2_loopFuelSource body F) (f2_loopHost body F anchor findMode).tm
    _ _ (by intro s inp work; rfl) [] [] c t hlive

/-- The fuel capture starts at the host's genuine blank initial configuration. -/
private lemma f2_loopHost_init (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) :
    (f2_loopHost body F anchor findMode).tm.initCfg x =
      captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] []
        ((f2_loopFuelSource body F).initCfg x) := by
  rw [initCfg_ofWords, initCfg_ofWords]
  simp [Cfg.ofWords, captureCfg, f2_loopHost, f2_loopFuelSource]

/-- With no track operations, a controller action is the standard input-only action. -/
private lemma f2_loopControl_idle (body F : FinTM Bool) (inp : SignType)
    (next : Option (f2_LoopHostState body F)) :
    f2_loopControlAction body F inp none (none, 0) (none, 0) none next =
      controlAction inp next := by
  simp [f2_loopControlAction, controlAction]

/-- Host phases 4 and 5 rewind the native input in bounded time, retaining
all tapes, heads, and output, then dispatch to genuine body startup. -/
private lemma f2_loopHost_input_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (cfg : Cfg (f2_loopHost body F anchor findMode).k Bool (f2_loopHost body F anchor findMode).State x)
    (hs : cfg.state = some (.inr (.inr (4 : Fin 14)))) :
    ∃ t ≤ cfg.inputPos.val + 2,
      (f2_loopHost body F anchor findMode).tm.runFrom cfg t =
        {cfg with state := some (.inr (.inl (true, (body.tm.q₀, false)))), inputPos := 1} := by
  apply f2_loop_rewind_bounded (f2_loopHost body F anchor findMode).tm
    (.inr (.inr 4)) (.inr (.inr 5)) (.some (.inr (.inl (true, (body.tm.q₀, false)))))
    ?_ ?_ cfg hs
  · intro inp work
    exact f2_loopControl_idle body F .neg _
  · intro inp work
    cases inp <;> exact f2_loopControl_idle body F _ _

/-- A controller configuration with arbitrary preserved body/fuel residue.
Only the flag, counter, and capture tracks are replaced by the parameters. -/
private def f2_loopFrame (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x where
  state := q
  inputPos := p
  workTapes := fun i =>
    if (i : ℕ) = body.k then flag
    else if (i : ℕ) = body.k + 1 then counter
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then payload
    else base.workTapes i
  workTapePos := fun i =>
    if (i : ℕ) = body.k then 0
    else if (i : ℕ) = body.k + 1 then ch
    else if (i : ℕ) = body.k + 1 + (1 + F.k) then ph
    else base.workTapePos i
  output := out

/-- Optional writes update exactly their current cell. -/
private def f2_loopWrite (tape : ℤ → Option Bool) (head : ℤ) :
    Option (Option Bool) → ℤ → Option Bool
  | none => tape
  | some symbol => Function.update tape head symbol

/-- Controller actions preserve the inactive frame and perform precisely
the three declared track operations. -/
private lemma f2_loopControl_apply (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool)
    (inp : SignType) (fw : Option (Option Bool))
    (ca pa : Option (Option Bool) × SignType) (emit : Option Bool)
    (next : Option (f2_LoopHostState body F)) :
    (f2_loopControlAction body F inp fw ca pa emit next).apply
        (f2_loopFrame body F base q p flag counter payload ch ph out) =
      f2_loopFrame body F base next (moveInputPos p inp)
        (f2_loopWrite flag 0 fw) (f2_loopWrite counter ch ca.1) (f2_loopWrite payload ph pa.1)
        (ch + ca.2) (ph + pa.2) (out ++ emit.toList) := by
  have hcf : body.k + 1 ≠ body.k := by omega
  have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
  have hpc : body.k + 1 + (1 + F.k) ≠ body.k + 1 := by omega
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hf : (i : ℕ) = body.k
    · simp only [Action.apply, f2_loopControlAction, f2_loopFrame, hf, ↓reduceIte]
      cases fw <;> rfl
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp only [Action.apply, f2_loopControlAction, f2_loopFrame, hc, hcf, ↓reduceIte]
        cases ca.1 <;> rfl
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · simp only [Action.apply, f2_loopControlAction, f2_loopFrame, hp, hpf, hpc, ↓reduceIte]
          cases pa.1 <;> rfl
        · simp [Action.apply, f2_loopControlAction, f2_loopFrame, hf, hc, hp]
  · funext i
    by_cases hf : (i : ℕ) = body.k
    · simp [Action.apply, f2_loopControlAction, f2_loopFrame, hf]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [Action.apply, f2_loopControlAction, f2_loopFrame, hc]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k) <;>
          simp [Action.apply, f2_loopControlAction, f2_loopFrame, hf, hc, hp, hpf]

/-- One-tape payload replay: emit each stored bit, then halt on the right blank. -/
private def f2_loopReplayTM : FinTM Bool where
  k := 1
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ _ work => match work 0 with
        | some b => ⟨0, fun _ => (none, .pos), some b, some ()⟩
        | none => ⟨0, fun _ => (none, 0), none, none⟩ }

/-- Replay configuration with arbitrary input position and output prefix. -/
private def f2_loopReplayCfg (x : List Bool) (p : Fin (x.length + 2))
    (q : Option Unit) (z : ℤ) (word out : List Bool) : Cfg 1 Bool Unit x :=
  ⟨q, p, fun _ => bufferTape word, fun _ => z, out⟩

/-- A replay step emits the current bit without modifying the captured word;
at the right blank it halts without an additional bit. -/
private lemma f2_loopReplay_step (x : List Bool) (p : Fin (x.length + 2))
    (pre rest out : List Bool) :
    f2_loopReplayTM.tm.step (f2_loopReplayCfg x p (some ()) pre.length (pre ++ rest) out) =
      match rest with
      | [] => f2_loopReplayCfg x p none pre.length pre out
      | b :: bs => f2_loopReplayCfg x p (some ()) (pre.length + 1) (pre ++ b :: bs) (out ++ [b]) := by
  unfold MultiTapeTM.step
  change (f2_loopReplayTM.tm.tr () _ _).apply _ = _
  simp only [f2_loopReplayTM, f2_loopReplayCfg, Cfg.workTapeSymbols, f2_loopBuffer_read]
  cases rest with
  | nil =>
    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ ?_
    · simp
    · funext i; simp [Action.apply]
    · simp [Action.apply]
  | cons b rest =>
    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
    funext i; simp [Action.apply]

/-- Replay emits exactly the remaining payload in its length plus one steps,
including an empty payload.
**Proof sketch.** Induct on the unprocessed suffix. The step lemma emits
one bit and moves the frontier; the empty suffix supplies the final blank
test. Concatenation associativity preserves the exact output order. -/
private lemma f2_loopReplay_run (x : List Bool) (p : Fin (x.length + 2))
    (rest : List Bool) : ∀ pre out : List Bool,
    f2_loopReplayTM.tm.runFrom (f2_loopReplayCfg x p (some ()) pre.length (pre ++ rest) out)
        (rest.length + 1) =
      f2_loopReplayCfg x p none (pre ++ rest).length (pre ++ rest) (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out
    simpa [MultiTapeTM.runFrom_succ_eq_step] using f2_loopReplay_step x p pre [] out
  | cons b rest ih =>
    intro pre out
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step, f2_loopReplay_step]
    simpa [List.append_assoc, List.length_append, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_assoc, add_comm, add_left_comm] using ih (pre ++ [b]) (out ++ [b])

/-- A payload-only controller action is the right-block action extension. -/
private lemma f2_loopControl_payload (body F : FinTM Bool) (d : SignType)
    (out : Option Bool) (next : Option (f2_LoopHostState body F)) :
    f2_loopControlAction body F 0 none (none, 0) (none, d) out next =
      rightAction (body.k + 1 + (1 + F.k)) id
        (⟨0, fun _ : Fin 1 => (none, d), out, next⟩ : Action 1 Bool (f2_LoopHostState body F)) := by
  simp only [f2_loopControlAction, rightAction, Option.map_id]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    have hj : (j : ℕ) ≠ body.k + 1 + (1 + F.k) := Nat.ne_of_lt j.isLt
    simp [hj]
  · intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
    simp [hf]

/-- Phase 13 replays the captured payload in the actual host, preserving
the arbitrary completed body/fuel tapes. -/
private lemma f2_loopHost_replay (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (x : List Bool) (p : Fin (x.length + 2)) (word out : List Bool)
    (tapes : Fin (body.k + 1 + (1 + F.k)) → ℤ → Option Bool)
    (heads : Fin (body.k + 1 + (1 + F.k)) → ℤ) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
          (f2_loopReplayCfg x p (some ()) 0 word out) tapes heads) (word.length + 1) =
      rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
        (f2_loopReplayCfg x p none word.length word (out ++ word)) tapes heads := by
  have htr : ∀ q inp work,
      (f2_loopHost body F anchor findMode).tm.tr (.inr (.inr (13 : Fin 14))) inp work =
        rightAction (body.k + 1 + (1 + F.k))
          (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
          (f2_loopReplayTM.tm.tr q inp fun i => work (Fin.natAdd (body.k + 1 + (1 + F.k)) i)) := by
    intro q inp work
    cases q
    change (match work (Fin.last (body.k + 1 + (1 + F.k))) with
      | some b => f2_loopControlAction body F 0 none (none, 0) (none, .pos) (some b)
          (some (.inr (.inr 13)))
      | none => f2_loopControlAction body F 0 none (none, 0) (none, 0) none none) = _
    cases hw : work (Fin.last (body.k + 1 + (1 + F.k)))
    · simpa only [f2_loopReplayTM, show Fin.natAdd (body.k + 1 + (1 + F.k)) (0 : Fin 1) =
          Fin.last (body.k + 1 + (1 + F.k)) from rfl, hw] using
        f2_loopControl_payload body F 0 none none
    · simpa only [f2_loopReplayTM, show Fin.natAdd (body.k + 1 + (1 + F.k)) (0 : Fin 1) =
          Fin.last (body.k + 1 + (1 + F.k)) from rfl, hw] using
        f2_loopControl_payload body F .pos _ _
  refine (rightCfg_run (k := body.k + 1 + (1 + F.k)) (l := 1)
    f2_loopReplayTM.tm (f2_loopHost body F anchor findMode).tm
    (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14))) htr
    (f2_loopReplayCfg x p (some ()) 0 word out) tapes heads (word.length + 1)).trans ?_
  have hr := f2_loopReplay_run x p word [] out
  simpa using congrArg
    (fun c => rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14))) c tapes heads) hr

/-- The fuel configuration on its relocated block, with the body, flag, and
counter still blank. The completed fuel residue is retained by this embedding. -/
private def f2_loopFuelCfg (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k)) Bool F.State x :=
  rightCfg id (rightCfg id c (fun (_ : Fin 1) _ => none) (fun _ => 0))
    (fun (_ : Fin (body.k + 1)) _ => none) (fun _ => 0)

/-- Relocating fuel through the counter and body blocks preserves every run.
**Proof sketch.** Apply the right-block simulation twice. Each inactive block
has its own blank tapes and origin heads, retained throughout the source run. -/
private lemma f2_loopFuel_run (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (t : ℕ) :
    (f2_loopFuelSource body F).runFrom (f2_loopFuelCfg body F c) t =
      f2_loopFuelCfg body F (F.tm.runFrom c t) := by
  let pad : MultiTapeTM (1 + F.k) Bool F.State :=
    { q₀ := F.tm.q₀
      tr := fun q inp work => rightAction 1 id
        (F.tm.tr q inp (fun i => work (Fin.natAdd 1 i))) }
  unfold f2_loopFuelCfg
  rw [rightCfg_run pad (f2_loopFuelSource body F) id (fun _ _ _ => rfl),
    rightCfg_run F.tm pad id (fun _ _ _ => rfl)]

/-- The relocated fuel source begins at its genuine blank configuration. -/
private lemma f2_loopFuel_init (body F : FinTM Bool) (x : List Bool) :
    (f2_loopFuelSource body F).initCfg x = f2_loopFuelCfg body F (F.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro k <;>
        simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro k <;>
        simp [f2_loopFuelCfg, rightCfg, MultiTapeTM.initCfg, Cfg.init]

/-- The capture track of a frame reads precisely its parameterized tape. -/
private lemma f2_loopFrame_payload (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (f2_loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        (Fin.last (body.k + 1 + (1 + F.k))) = payload ph := by
  have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
  simp [f2_loopFrame, Cfg.workTapeSymbols, hf]

/-- The counter track of a frame reads precisely its parameterized tape. -/
private lemma f2_loopFrame_counter (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (f2_loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        ⟨body.k + 1, by omega⟩ = counter ch := by
  simp [f2_loopFrame, Cfg.workTapeSymbols]

/-- Fuel-rewind phase 1 scans to the left blank and returns at the origin.
**Proof sketch.** Induct on the number of stored cells to the left. At zero,
the head is on the left blank; otherwise its cell is nonblank and the left
move reduces that number. All other tracks and the native input are retained. -/
private lemma f2_loopHost_fuel_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool)
    (ch : ℤ) (word out : List Bool) : ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out) (j + 1) =
      f2_loopFrame body F base (some (.inr (.inr 2))) p flag counter
        (bufferTape word) ch 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
        (bufferTape word) ch ((0 : ℤ) - 1) out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
          (some (.inr (.inr 1)))
      | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
          (some (.inr (.inr 2)))).apply _ = _
    rw [f2_loopFrame_payload]
    simp only [zero_sub, bufferTape_left]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out) =
        f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 1))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
            (some (.inr (.inr 1)))
        | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
            (some (.inr (.inr 2)))).apply _ = _
      rw [f2_loopFrame_payload]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- During fuel copying, the processed prefix of the capture tape is blank. -/
private def f2_loopCopyTape (pre rest : List Bool) (z : ℤ) : Option Bool :=
  if z < pre.length then none else bufferTape (pre ++ rest) z

/-- The copying frontier reads the first bit of the remaining suffix. -/
private lemma f2_loopCopy_read (pre rest : List Bool) :
    f2_loopCopyTape pre rest pre.length = rest.head? := by
  simp only [f2_loopCopyTape, lt_self_iff_false, ↓reduceIte, f2_loopBuffer_read]

/-- Clearing one fuel cell extends the already-cleared prefix by that bit. -/
private lemma f2_loopCopy_erase (pre rest : List Bool) (b : Bool) :
    Function.update (f2_loopCopyTape pre (b :: rest)) (pre.length : ℤ) none =
      f2_loopCopyTape (pre ++ [b]) rest := by
  funext z
  by_cases hz : z = pre.length
  · subst z; simp [f2_loopCopyTape]
  · rw [Function.update_of_ne hz]
    have hlt : z < (pre.length : ℤ) ↔ z < ((pre ++ [b]).length : ℤ) := by
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      omega
    simp only [f2_loopCopyTape, hlt, List.append_assoc, List.singleton_append]

/-- Before copying begins the capture tape is the original fuel buffer. -/
private lemma f2_loopCopy_initial (word : List Bool) :
    f2_loopCopyTape [] word = bufferTape word := by
  funext z
  by_cases hz : z < 0
  · simp [f2_loopCopyTape, bufferTape, hz, show ¬0 ≤ z by omega]
  · simp [f2_loopCopyTape, hz]

/-- After copying ends the capture tape is completely blank. -/
private lemma f2_loopCopy_final (word : List Bool) :
    f2_loopCopyTape word [] = bufferTape [] := by
  funext z
  by_cases hz : z < word.length
  · simp [f2_loopCopyTape, hz]
  · have hn : 0 ≤ z := by omega
    simp [f2_loopCopyTape, hz, bufferTape, hn]

/-- Phase 2 copies the remaining fuel bits to the counter, clearing each
captured bit, then starts the synchronized rewind.
**Proof sketch.** Induct on the uncopied suffix. A nonempty suffix writes
its head at the counter's right blank, clears the corresponding payload
cell, and advances both heads. The empty suffix detects the right blank
and moves both heads left once, including when the original word is empty. -/
private lemma f2_loopHost_fuel_copy (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (out : List Bool)
    (rest : List Bool) : ∀ pre,
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (f2_loopCopyTape pre rest) pre.length pre.length out) (rest.length + 1) =
      f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape (pre ++ rest))
        (bufferTape []) ((pre ++ rest).length - 1) ((pre ++ rest).length - 1) out := by
  induction rest with
  | nil =>
    intro pre
    rw [List.length_nil, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
        (f2_loopCopyTape pre []) pre.length pre.length out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some b => f2_loopControlAction body F 0 none (some (some b), .pos)
          (some none, .pos) none (some (.inr (.inr 2)))
      | none => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))).apply _ = _
    rw [f2_loopFrame_payload, f2_loopCopy_read]
    dsimp only [List.head?]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite, f2_loopCopy_final, sub_eq_add_neg]
  | cons b rest ih =>
    intro pre
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (f2_loopCopyTape pre (b :: rest)) pre.length pre.length out) =
        f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape (pre ++ [b]))
          (f2_loopCopyTape (pre ++ [b]) rest) (pre ++ [b]).length (pre ++ [b]).length out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 2))) p flag (bufferTape pre)
          (f2_loopCopyTape pre (b :: rest)) pre.length pre.length out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some bit => f2_loopControlAction body F 0 none (some (some bit), .pos)
            (some none, .pos) none (some (.inr (.inr 2)))
        | none => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))).apply _ = _
      rw [f2_loopFrame_payload, f2_loopCopy_read]
      dsimp only [List.head?]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, f2_loopCopy_erase, bufferTape_append]
    rw [hs]
    simpa [List.append_assoc] using ih (pre ++ [b])

/-- Phase 3 rewinds counter and cleared capture heads together.
**Proof sketch.** Induct on the number of counter cells to the left. Both
heads take the same moves; only the counter is read, so the already-cleared
capture tape stays blank. The final left-blank test moves both heads to zero. -/
private lemma f2_loopHost_fuel_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out) (j + 1) =
      f2_loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
        (bufferTape []) ((0 : ℤ) - 1) ((0 : ℤ) - 1) out).workTapeSymbols
          ⟨body.k + 1, by omega⟩ with
      | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
          (some (.inr (.inr 3)))
      | none => f2_loopControlAction body F 0 none (none, .pos) (none, .pos) none
          (some (.inr (.inr 4)))).apply _ = _
    rw [f2_loopFrame_counter]
    simp only [zero_sub, bufferTape_left]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out) =
        f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) ((j : ℤ) - 1) ((j : ℤ) - 1) out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 3))) p flag (bufferTape word)
          (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            ⟨body.k + 1, by omega⟩ with
        | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, .neg) none
            (some (.inr (.inr 3)))
        | none => f2_loopControlAction body F 0 none (none, .pos) (none, .pos) none
            (some (.inr (.inr 4)))).apply _ = _
      rw [f2_loopFrame_counter]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Fuel setup phases 0--3 copy the complete fuel word to the counter,
clear the capture track, and return both heads to zero in exactly `3|word|+4`
steps. This includes the empty word, with no counter debit.
**Proof sketch.** Compose the mandatory left move, the fuel rewind, the
copy/clear scan, and the synchronized rewind. Their costs are respectively
one and three copies of the word length plus one. -/
private lemma f2_loopHost_fuel_setup (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag : ℤ → Option Bool) (word out : List Bool) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
          (bufferTape word) 0 word.length out) (3 * word.length + 4) =
      f2_loopFrame body F base (some (.inr (.inr 4))) p flag (bufferTape word)
        (bufferTape []) 0 0 out := by
  have hs : (f2_loopHost body F anchor findMode).tm.step
      (f2_loopFrame body F base (some (.inr (.inr 0))) p flag (bufferTape [])
        (bufferTape word) 0 word.length out) =
      f2_loopFrame body F base (some (.inr (.inr 1))) p flag (bufferTape [])
        (bufferTape word) 0 ((word.length : ℤ) - 1) out := by
    change (f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
      (some (.inr (.inr 1)))).apply _ = _
    rw [f2_loopControl_apply]
    simp [f2_loopWrite, sub_eq_add_neg]
  rw [show 3 * word.length + 4 =
      ((word.length + 1) + (word.length + 1) + (word.length + 1)) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hs]
  rw [MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add (a := word.length + 1) (b := word.length + 1),
    f2_loopHost_fuel_rewind body F anchor findMode base p flag (bufferTape []) 0 word out
      word.length (le_refl _)]
  have hc := f2_loopHost_fuel_copy body F anchor findMode base p flag out word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, f2_loopCopy_initial] at hc
  rw [hc, f2_loopHost_fuel_return body F anchor findMode base p flag word out
    word.length (le_refl _)]

/-- The host's captured fuel endpoint, retaining all completed fuel residue. -/
private def f2_loopFuelCaptured (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x :=
  captureCfg Sum.inl (Sum.inr (Sum.inr (0 : Fin 14))) [] [] (f2_loopFuelCfg body F c)

/-- The prepared startup configuration: fuel copied, capture blank, input
and active heads at their origins, and completed fuel work retained. -/
private def f2_loopReady (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x :=
  f2_loopFrame body F (f2_loopFuelCaptured body F c)
    (some (.inr (.inl (true, (body.tm.q₀, false))))) 1
    (bufferTape []) (bufferTape c.output) (bufferTape []) 0 0 []

/-- At a genuine fuel halt the capture endpoint has the frame expected by
phase 0, with the flag and counter still blank.
**Proof sketch.** Split the physical tape index into capture, body/flag,
counter, and fuel blocks. The three active controller tracks agree with
their explicit parameters; every inactive track is retained from the base. -/
private lemma f2_loopFuelCaptured_frame (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (hc : c.state = none) :
    f2_loopFuelCaptured body F c =
      f2_loopFrame body F (f2_loopFuelCaptured body F c) (some (.inr (.inr 0))) c.inputPos
        (bufferTape []) (bufferTape []) (bufferTape c.output) 0 c.output.length [] := by
  refine Cfg.ext ?_ rfl ?_ ?_ rfl
  · simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, hc]
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, hf]
    · intro j
      have hj : (j : ℕ) ≠ body.k + 1 + (1 + F.k) := Nat.ne_of_lt j.isLt
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hbc : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 := by omega
          have hbp : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 + (1 + F.k) := by omega
          simp [f2_loopFrame, hbf, Nat.ne_of_lt b.isLt]
  · funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, hf]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [f2_loopFuelCaptured, captureCfg, f2_loopFuelCfg, rightCfg, f2_loopFrame, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hbc : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 := by omega
          have hbp : body.k + 1 + (1 + (b : ℕ)) ≠ body.k + 1 + (1 + F.k) := by omega
          simp [f2_loopFrame, hbf, Nat.ne_of_lt b.isLt]

/-- Fuel execution, setup, and input rewind reach prepared body startup
within `5*T+7` steps, retaining the actual fuel endpoint.
**Proof sketch.** Replace the supplied padded fuel run by its first halt,
relocate it twice, and capture it in the actual host. Setup costs `3L+4`,
where `L ≤ T`; the input rewind costs at most the first run's displacement
plus two, hence at most `T+3`. No bound in the input length is used. -/
private lemma f2_loopHost_prepare (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T) (x : List Bool) :
    ∃ (c : Cfg F.k Bool F.State x) (t : ℕ),
      c.state = none ∧ c.output = Nat.bits (R x.length) ∧ t ≤ 5 * T x.length + 7 ∧
      (f2_loopHost body F anchor findMode).tm.runFrom
        ((f2_loopHost body F anchor findMode).tm.initCfg x) t = f2_loopReady body F c ∧
      ∀ i, -(T x.length : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ T x.length := by
  obtain ⟨space, hhalt, hout, hspace⟩ := hF x
  obtain ⟨u, hu, hut, hlive, huh, hue⟩ :=
    f2_loop_first_halt F.tm (F.tm.initCfg x) (T x.length) (by simp [MultiTapeTM.initCfg, Cfg.init]) hhalt
  let c := F.tm.runFrom (F.tm.initCfg x) u
  have hc : c.state = none := huh
  have ho : c.output = Nat.bits (R x.length) := by dsimp only [c]; rw [hue]; exact hout
  have hcap : (f2_loopHost body F anchor findMode).tm.runFrom
      ((f2_loopHost body F anchor findMode).tm.initCfg x) u = f2_loopFuelCaptured body F c := by
    rw [f2_loopHost_init, f2_loopFuel_init]
    rw [f2_loopHost_fuel_capture]
    · rw [f2_loopFuel_run]; rfl
    · intro v hv
      rw [f2_loopFuel_run]
      simpa [Cfg.Halted, f2_loopFuelCfg, rightCfg] using hlive v hv
  let prepared := f2_loopFrame body F (f2_loopFuelCaptured body F c)
    (some (.inr (.inr 4))) c.inputPos (bufferTape []) (bufferTape c.output)
    (bufferTape []) 0 0 []
  have hsetup : (f2_loopHost body F anchor findMode).tm.runFrom
      (f2_loopFuelCaptured body F c) (3 * c.output.length + 4) = prepared := by
    conv_lhs => arg 1; rw [f2_loopFuelCaptured_frame body F c hc]
    exact f2_loopHost_fuel_setup body F anchor findMode _ _ _ _ _
  obtain ⟨v, hv, hrew⟩ := f2_loopHost_input_rewind body F anchor findMode prepared rfl
  have hw : c.output.length ≤ T x.length := by rw [ho]; exact f2_loop_fuel_width F R T hF x
  have hp : c.inputPos.val ≤ 1 + u := f2_loop_input_run_le F.tm (F.tm.initCfg x) u
  refine ⟨c, u + (3 * c.output.length + 4) + v, hc, ho, ?_, ?_, ?_⟩
  · change v ≤ c.inputPos.val + 2 at hv
    omega
  · rw [MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_add (a := u) (b := 3 * c.output.length + 4), hcap, hsetup, hrew]
    rfl

  · intro i
    have h := f2_head_steps F.tm (F.tm.initCfg x) u i
    have hh : -(u : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ u := by
      simpa [c, MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords] using h
    omega

/-- The stopped body's padded source configuration, preserving the counter
word and the complete fuel residue through every call. -/
private def f2_loopBodyPadded (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (flag : Option Bool)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x :=
  leftCfg id (f2_loopBodyCfg body anchor c release flag)
    (Fin.addCases (fun (_ : Fin 1) => bufferTape word) fuel.workTapes)
    (Fin.addCases (fun (_ : Fin 1) => 0) fuel.workTapePos)

/-- A body call viewed inside the concrete capturing host. A halted stopped
body is represented by the corresponding startup/active return phase. -/
private def f2_loopCall (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
    (startup : Bool) (c : Cfg body.k Bool body.State x) (release : Bool)
    (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x :=
  captureCfg (fun s => Sum.inr (Sum.inl (startup, s)))
    (Sum.inr (Sum.inr (if startup then 6 else 7 : Fin 14))) [] []
    (f2_loopBodyPadded body F anchor c release flag word fuel)

/-- The padded body source simulates the stopped body with arbitrary inactive
counter and fuel tracks. -/
private lemma f2_loopBodySource_run (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool}
    (c : Cfg (body.k + 1) Bool (body.State × Bool) x)
    (tapes : Fin (1 + F.k) → ℤ → Option Bool) (heads : Fin (1 + F.k) → ℤ) (t : ℕ) :
    (f2_loopBodySource body F anchor).runFrom (leftCfg id c tapes heads) t =
      leftCfg id ((f2_loopBodyTM body anchor).tm.runFrom c t) tapes heads :=
  leftCfg_run (f2_loopBodyTM body anchor).tm (f2_loopBodySource body F anchor)
    id (fun _ _ _ => rfl) c tapes heads t

/-- A live anchor endpoint is captured after one additional stop step.
The exact endpoint keeps every inactive tape and carries the false stop flag.
**Proof sketch.** The live endpoint rules out earlier halts. Use the source
wrapper simulation up to that endpoint, take its silent anchor-stop step,
and lift the resulting run through the padded source and actual host capture.
The guard at time zero is supplied by the release bit for active calls. -/
private lemma f2_loopHost_anchor_return (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hend : (body.tm.runFrom c t).state = some anchor)
    (hreleased : t = 0 → release = false)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor startup c release none word fuel) (t + 1) =
      f2_loopCall body F anchor startup {body.tm.runFrom c t with state := none}
        false (some false) word fuel := by
  have hlive : ∀ u ≤ t, (body.tm.runFrom c u).state ≠ none :=
    f2_loop_live_prefix body.tm c t (by rw [hend]; simp)
  have hc : c.state ≠ none := by simpa using hlive 0 (Nat.zero_le _)
  have hr : (f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none) t =
      f2_loopBodyCfg body anchor (body.tm.runFrom c t) false none := by
    rw [f2_loopBody_run body anchor c release hc t
      (fun u hu => hlive u (by omega)) hanchor]
    have hn := hlive t (le_refl _)
    rw [if_neg hn]
    by_cases ht : t = 0
    · rw [if_pos ht, hreleased ht]
    · rw [if_neg ht]
  have hstop : (f2_loopBodyTM body anchor).tm.runFrom (f2_loopBodyCfg body anchor c release none)
      (t + 1) =
      f2_loopBodyCfg body anchor {body.tm.runFrom c t with state := none} false (some false) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hr, f2_loopBody_stop body anchor _ hend]
  unfold f2_loopCall f2_loopBodyPadded
  rw [f2_loopHost_body_capture]
  · rw [f2_loopBodySource_run, hstop]
  · intro u hu
    rw [f2_loopBodySource_run, f2_loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, leftCfg, f2_loopBodyCfg] using hlive u (by omega)

/-- Prepared fuel startup is the canonical captured body call on blank body
tapes; the counter and fuel residue are exactly the padded inactive block.
**Proof sketch.** Compare the four physical tape blocks. The input head and
all active heads are at their origins; only the completed fuel bank has
arbitrary contents and head positions. -/
private lemma f2_loopReady_call (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (fuel : Cfg F.k Bool F.State x) :
    f2_loopReady body F fuel =
      f2_loopCall body F anchor true (body.tm.initCfg x) false none fuel.output fuel := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    refine Fin.lastCases ?_ ?_ i
    · have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
      simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
        f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, hf]
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro a
        have ha : (a : ℕ) < body.k + 1 + (1 + F.k) := by omega
        have han : (a : ℕ) ≠ body.k + 1 := by omega
        have hap : (a : ℕ) ≠ body.k + 1 + (1 + F.k) := by omega
        simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
          f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, f2_loopFuelCaptured, f2_loopFuelCfg,
          rightCfg, ha, han, hap, Fin.addCases, a.isLt]
      · intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          have hb : b = 0 := Subsingleton.elim _ _
          subst b
          simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
            f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, Fin.addCases]
        · intro b
          have hbf : body.k + 1 + (1 + (b : ℕ)) ≠ body.k := by omega
          have hb : (b : ℕ) < F.k := b.isLt
          simp [f2_loopReady, f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg,
            f2_loopBodyCfg, MultiTapeTM.initCfg, Cfg.init, f2_loopFuelCaptured, f2_loopFuelCfg,
            rightCfg, hbf, hb, Nat.ne_of_lt hb, Fin.addCases]

/-- Phase 6 clears startup's false flag and releases the first anchor for
free. It changes no body, counter, or fuel data.
**Proof sketch.** The captured stopped body is in phase 6. Its sole write
clears the flag's origin cell. Comparing tape blocks identifies the result
with the active released call on the same body data. -/
private lemma f2_loopHost_release (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    (f2_loopHost body F anchor findMode).tm.step
        (f2_loopCall body F anchor true {c with state := none} false (some false) word fuel) =
      f2_loopCall body F anchor false {c with state := some anchor} true none word fuel := by
  change (f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
    (some (.inr (.inl (false, (anchor, true)))))).apply _ = _
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z
    by_cases hf : (i : ℕ) = body.k
    · have hi : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
        leftCfg, f2_loopBodyCfg, hf, hi, Fin.addCases, Function.update]
    · by_cases hb : (i : ℕ) < body.k + 1
      · have hi : (i : ℕ) < body.k := by omega
        simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
          leftCfg, f2_loopBodyCfg, hf, Fin.addCases, hb, hi]
      · simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
          leftCfg, f2_loopBodyCfg, hf, Fin.addCases, hb]
  · funext i
    by_cases hf : (i : ℕ) = body.k <;>
      simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg, f2_loopBodyPadded,
        leftCfg, f2_loopBodyCfg, hf]
  · simp [Action.apply, f2_loopControlAction, f2_loopCall, captureCfg]

/-- Genuine body startup reaches the released first candidate in at most
its source startup time plus two host steps.
**Proof sketch.** When the startup time is positive, the no-anchor prefix is
captured without a premature stop; a zero-time startup already occupies the
anchor (the no-anchor premise is vacuous) and takes the two administrative
steps directly. In either case the anchor endpoint yields the false flag;
one stop step and phase 6's flag-clear step release the initial candidate. -/
private lemma f2_loopHost_start (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (s : List Bool) (t : ℕ)
    (fuel : Cfg F.k Bool F.State x)
    (hguard : ∀ u < t, (body.tm.runFrom (body.tm.initCfg x) u).state ≠ some anchor)
    (hend : body.tm.runFrom (body.tm.initCfg x) t = Cfg.ofWords anchor (stateWord body.k s)) :
    (f2_loopHost body F anchor findMode).tm.runFrom (f2_loopReady body F fuel) (t + 2) =
      f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
        true none fuel.output fuel := by
  rw [f2_loopReady_call body F anchor, show t + 2 = (t + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step']
  rw [f2_loopHost_anchor_return body F anchor findMode true (body.tm.initCfg x) false t
    fuel.output fuel (by rw [hend]; rfl) (fun _ => rfl) (fun u hu => Or.inr (hguard u hu))]
  rw [hend, f2_loopHost_release body F anchor findMode _ _ _]
  rfl

/-- A genuine first halt returns to phase 7 with the true stop flag and the
entire source output captured, including its halting emission.
**Proof sketch.** Simulate the released body through its first halting action.
Strict liveness permits actual-host capture throughout; the positive duration
consumes the release bit and the halting action sets the true flag. -/
private lemma f2_loopHost_halt_return (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (t : ℕ) (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (ht : 0 < t) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u, 0 < u → u < t → (body.tm.runFrom c u).state ≠ some anchor)
    (hend : (body.tm.runFrom c t).state = none) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false c true none word fuel) t =
      f2_loopCall body F anchor false (body.tm.runFrom c t) false (some true) word fuel := by
  have hc : c.state ≠ none := by simpa using hlive 0 ht
  have hg : ∀ u < t, (u = 0 ∧ true = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor := by
    intro u hu
    by_cases hz : u = 0
    · exact Or.inl ⟨hz, rfl⟩
    · exact Or.inr (hanchor u (by omega) hu)
  unfold f2_loopCall f2_loopBodyPadded
  rw [f2_loopHost_body_capture]
  · rw [f2_loopBodySource_run, f2_loopBody_run body anchor c true hc t hlive hg]
    simp [hend, Nat.ne_of_gt ht]
  · intro u hu
    rw [f2_loopBodySource_run, f2_loopBody_run body anchor c true hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hg v (by omega))]
    simpa [Cfg.Halted, leftCfg, f2_loopBodyCfg] using hlive u hu

/-- A captured body call has the explicit flag, counter, and payload tracks
used by the controller frame, with arbitrary inactive body and fuel residue. -/
private lemma f2_loopCall_frame (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (startup : Bool) (c : Cfg body.k Bool body.State x)
    (release : Bool) (flag : Option Bool) (word : List Bool) (fuel : Cfg F.k Bool F.State x) :
    f2_loopCall body F anchor startup c release flag word fuel =
      f2_loopFrame body F (f2_loopCall body F anchor startup c release flag word fuel)
        (f2_loopCall body F anchor startup c release flag word fuel).state c.inputPos
        (fun z => if z = 0 then flag else none) (bufferTape word) (bufferTape c.output)
        0 c.output.length [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    by_cases hf : (i : ℕ) = body.k
    · have hlt : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
        hf, hlt, Fin.addCases]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
          hc, Fin.addCases]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
          simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hp, hpf]
        · simp [f2_loopFrame, hf, hc, hp]

/-- Reframing a body call changes precisely its control, flag, and counter.
**Proof sketch.** The source configuration changes only in state. Thus all
inactive body and fuel data coincide; compare the three explicitly replaced
tracks and retain every other physical tape and head. -/
private lemma f2_loopCall_reframe (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (c : Cfg body.k Bool body.State x)
    (startup startup' release release' : Bool) (flag flag' : Option Bool)
    (word word' : List Bool) (fuel : Cfg F.k Bool F.State x) (q : Option body.State) :
    f2_loopFrame body F (f2_loopCall body F anchor startup c release flag word fuel)
        (f2_loopCall body F anchor startup' {c with state := q} release' flag' word' fuel).state
        c.inputPos (fun z => if z = 0 then flag' else none) (bufferTape word')
        (bufferTape c.output) 0 c.output.length [] =
      f2_loopCall body F anchor startup' {c with state := q} release' flag' word' fuel := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  all_goals
    funext i
    by_cases hf : (i : ℕ) = body.k
    · have hlt : body.k < body.k + 1 + (1 + F.k) := by omega
      simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
        hf, hlt, Fin.addCases]
    · by_cases hc : (i : ℕ) = body.k + 1
      · simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
          hc, Fin.addCases]
      · by_cases hp : (i : ℕ) = body.k + 1 + (1 + F.k)
        · have hpf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
          simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hp, hpf]
        · by_cases hb : (i : ℕ) < body.k + 1
          · have hi : (i : ℕ) < body.k := by omega
            simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
              hf, hc, hp, Fin.addCases, hb, hi]
          · have hn : (i : ℕ) - (body.k + 1) ≠ 0 := by omega
            simp [f2_loopFrame, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg,
              hf, hc, hp, Fin.addCases, hb, hn]

/-- One actual-host borrow step changes only the counter, recording success
or underflow in the rewind phase. -/
private lemma f2_loopHost_borrow_step (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (pre rest : List Bool) :
    (f2_loopHost body F anchor findMode).tm.step
      (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
        (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []) =
      match rest with
      | [] => f2_loopFrame body F base (some (.inr (.inr 10))) p (bufferTape [])
          (bufferTape pre) (bufferTape []) (pre.length - 1) 0 []
      | true :: us => f2_loopFrame body F base (some (.inr (.inr 9))) p (bufferTape [])
          (bufferTape (pre ++ false :: us)) (bufferTape []) (pre.length - 1) 0 []
      | false :: us => f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ true :: us)) (bufferTape []) (pre.length + 1) 0 [] := by
  change (match (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
      (bufferTape (pre ++ rest)) (bufferTape []) pre.length 0 []).workTapeSymbols
        ⟨body.k + 1, by omega⟩ with
    | some false => f2_loopControlAction body F 0 none (some (some true), .pos) (none, 0)
        none (some (.inr (.inr 8)))
    | some true => f2_loopControlAction body F 0 none (some (some false), .neg) (none, 0)
        none (some (.inr (.inr 9)))
    | none => f2_loopControlAction body F 0 none (none, .neg) (none, 0) none
        (some (.inr (.inr 10)))).apply _ = _
  rw [f2_loopFrame_counter, f2_loopBuffer_read]
  cases rest with
  | nil =>
    simp only [List.head?]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite, sub_eq_add_neg]
  | cons b rest =>
    cases b <;> simp only [List.head?]
    all_goals rw [f2_loopControl_apply]; simp [f2_loopWrite, f2_loopBuffer_write, sub_eq_add_neg]

/-- The actual host performs the borrow scan in the standalone scan's exact
time, preserving all non-counter tracks.
**Proof sketch.** Induct on the remaining word. Each false bit advances the
processed prefix. A true bit or the right blank starts the appropriate
rewind phase; no cell outside the original counter width is written. -/
private lemma f2_loopHost_borrow_run (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) : ∀ pre,
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape (pre ++ word)) (bufferTape []) pre.length 0 [])
        (f2_loopBorrowPos word + 1) =
      f2_loopFrame body F base (some (.inr (.inr (if (f2_loopDebit word).2 then 9 else 10)))) p
        (bufferTape []) (bufferTape (pre ++ (f2_loopDebit word).1)) (bufferTape [])
        ((pre.length : ℤ) + f2_loopBorrowPos word - 1) 0 [] := by
  induction word with
  | nil =>
    intro pre
    simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
      f2_loopHost_borrow_step body F anchor findMode base p pre []
  | cons b word ih =>
    intro pre
    cases b with
    | true =>
      simpa [f2_loopBorrowPos, f2_loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
        f2_loopHost_borrow_step body F anchor findMode base p pre (true :: word)
    | false =>
      simp only [f2_loopBorrowPos]
      rw [MultiTapeTM.runFrom_succ_eq_step, f2_loopHost_borrow_step]
      simpa [f2_loopDebit, List.append_assoc, Nat.cast_add, Nat.cast_one,
        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])

/-- The host's success/underflow rewind returns the counter head to zero.
Success releases the next anchor; underflow enters phase 11 without yet
emitting. Both paths retain all inactive residue.
**Proof sketch.** Induct on the number of counter cells to the left. The
left-blank test dispatches according to the stored success bit. -/
private lemma f2_loopHost_borrow_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) (success : Bool) :
    ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 []) (j + 1) =
      f2_loopFrame body F base
        (some (if success then .inr (.inl (false, (anchor, true))) else .inr (.inr 11))) p
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    cases success <;>
      (change (match (f2_loopFrame body F base _ p (bufferTape []) (bufferTape word)
          (bufferTape []) ((0 : ℤ) - 1) 0 []).workTapeSymbols ⟨body.k + 1, by omega⟩ with
        | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, 0) none _
        | none => f2_loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
    all_goals
      rw [f2_loopFrame_counter]
      simp only [zero_sub, bufferTape_left]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []) =
        f2_loopFrame body F base (some (.inr (.inr (if success then 9 else 10)))) p
          (bufferTape []) (bufferTape word) (bufferTape []) ((j : ℤ) - 1) 0 [] := by
      cases success <;>
        (change (match (f2_loopFrame body F base _ p (bufferTape []) (bufferTape word)
            (bufferTape []) (((j + 1 : ℕ) : ℤ) - 1) 0 []).workTapeSymbols
              ⟨body.k + 1, by omega⟩ with
          | some _ => f2_loopControlAction body F 0 none (none, .neg) (none, 0) none _
          | none => f2_loopControlAction body F 0 none (none, .pos) (none, 0) none _).apply _ = _)
      all_goals
        rw [f2_loopFrame_counter, show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
          bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
        rw [f2_loopControl_apply]
        simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- The complete actual-host counter operation has the fixed-width
worst-case bound `2|word|+2`, covering underflow and width zero. -/
private lemma f2_loopHost_borrow (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (word : List Bool) :
    2 * f2_loopBorrowPos word + 2 ≤ 2 * word.length + 2 ∧
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 8))) p (bufferTape [])
          (bufferTape word) (bufferTape []) 0 0 []) (2 * f2_loopBorrowPos word + 2) =
      f2_loopFrame body F base
        (some (if (f2_loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) p
        (bufferTape []) (bufferTape (f2_loopDebit word).1) (bufferTape []) 0 0 [] := by
  refine ⟨by have := f2_loopBorrowPos_le word; omega, ?_⟩
  have hr := f2_loopHost_borrow_run body F anchor findMode base p word []
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
  rw [show 2 * f2_loopBorrowPos word + 2 =
      (f2_loopBorrowPos word + 1) + (f2_loopBorrowPos word + 1) by omega,
    MultiTapeTM.runFrom_add, hr]
  exact f2_loopHost_borrow_rewind body F anchor findMode base p (f2_loopDebit word).1
    (f2_loopDebit word).2 _ (by rw [f2_loopDebit_length]; exact f2_loopBorrowPos_le word)

/-- The flag read is at its fixed origin, independently of inactive residue. -/
private lemma f2_loopFrame_flag (body F : FinTM Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (q : Option (f2_LoopHostState body F)) (p : Fin (x.length + 2))
    (flag counter payload : ℤ → Option Bool) (ch ph : ℤ) (out : List Bool) :
    (f2_loopFrame body F base q p flag counter payload ch ph out).workTapeSymbols
        ⟨body.k, by omega⟩ = flag 0 := by
  simp [f2_loopFrame, Cfg.workTapeSymbols]

/-- Clearing the only flag cell leaves a completely blank flag tape. -/
private lemma f2_loopFlag_clear (flag : Option Bool) :
    f2_loopWrite (fun z : ℤ => if z = 0 then flag else none) 0 (some none) = bufferTape [] := by
  funext z
  by_cases hz : z = 0 <;> simp [f2_loopWrite, Function.update, hz]

/-- A rejecting stopped call clears its flag, debits in worst-case width
time, and either releases the next anchor or emits exhaustion and halts.
Underflow and its emission are included in this same segment.
**Proof sketch.** Phase 7 clears the false flag in one step. The proved host
borrow takes `2j+2` steps. Success is the reframed next body seam; underflow
takes one additional phase-11 step, for at most `2|word|+4` steps in total. -/
private lemma f2_loopHost_reject (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x)
    (hc : c.state = none) (ho : c.output = []) :
    ∃ t ≤ 2 * word.length + 4,
      if (f2_loopDebit word).2 then
        (f2_loopHost body F anchor findMode).tm.runFrom
            (f2_loopCall body F anchor false c false (some false) word fuel) t =
          f2_loopCall body F anchor false {c with state := some anchor} true none (f2_loopDebit word).1 fuel
      else
        ((f2_loopHost body F anchor findMode).tm.runFrom
          (f2_loopCall body F anchor false c false (some false) word fuel) t).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom
          (f2_loopCall body F anchor false c false (some false) word fuel) t).output =
            (if findMode then [] else [false]) := by
  let base := f2_loopCall body F anchor false c false (some false) word fuel
  have hs : base.state = some (.inr (.inr (7 : Fin 14))) := by
    simp [base, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hc]
  have hf : base = f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos
      (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 [] := by
    have h := f2_loopCall_frame body F anchor false c false (some false) word fuel
    have hstate : (f2_loopCall body F anchor false c false (some false) word fuel).state =
        some (.inr (.inr (7 : Fin 14))) := hs
    simpa only [hstate, ho, List.length_nil, Nat.cast_zero] using h
  have hstep : (f2_loopHost body F anchor findMode).tm.step base =
      f2_loopFrame body F base (some (.inr (.inr 8))) c.inputPos
        (bufferTape []) (bufferTape word) (bufferTape []) 0 0 [] := by
    conv_lhs => arg 1; rw [hf]
    change (if (f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos
        (fun z => if z = 0 then some false else none) (bufferTape word) (bufferTape []) 0 0 []).workTapeSymbols
          ⟨body.k, by omega⟩ = some true then _
      else f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
        (some (.inr (.inr 8)))).apply _ = _
    rw [f2_loopFrame_flag]
    change (f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
      (some (.inr (.inr 8)))).apply _ = _
    rw [f2_loopControl_apply, f2_loopFlag_clear]
    simp [f2_loopWrite]
  have hrun : (f2_loopHost body F anchor findMode).tm.runFrom base (2 * f2_loopBorrowPos word + 3) =
      f2_loopFrame body F base
        (some (if (f2_loopDebit word).2 then .inr (.inl (false, (anchor, true)))
          else .inr (.inr 11))) c.inputPos
        (bufferTape []) (bufferTape (f2_loopDebit word).1) (bufferTape []) 0 0 [] := by
    rw [show 2 * f2_loopBorrowPos word + 3 = (2 * f2_loopBorrowPos word + 2) + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact (f2_loopHost_borrow body F anchor findMode base c.inputPos word).2
  have hw := f2_loopBorrowPos_le word
  by_cases hb : (f2_loopDebit word).2 = true
  · refine ⟨2 * f2_loopBorrowPos word + 3, by omega, ?_⟩
    simp only [hb, if_true] at hrun ⊢
    rw [hrun]
    have h := f2_loopCall_reframe body F anchor c false false false true (some false) none
      word (f2_loopDebit word).1 fuel (some anchor)
    simpa [base, f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, ho] using h
  · refine ⟨2 * f2_loopBorrowPos word + 4, by omega, ?_⟩
    simp only [hb] at hrun ⊢
    have hh : (f2_loopHost body F anchor findMode).tm.runFrom base (2 * f2_loopBorrowPos word + 4) =
        f2_loopFrame body F base none c.inputPos (bufferTape []) (bufferTape (f2_loopDebit word).1)
          (bufferTape []) 0 0 (if findMode then [] else [false]) := by
      rw [show 2 * f2_loopBorrowPos word + 4 = (2 * f2_loopBorrowPos word + 3) + 1 by omega,
        MultiTapeTM.runFrom_succ_eq_step', hrun]
      change (f2_loopControlAction body F 0 none (none, 0) (none, 0)
        (if findMode then none else some false) none).apply _ = _
      rw [f2_loopControl_apply]
      cases findMode <;> simp [f2_loopWrite]
    rw [hh]
    exact ⟨rfl, rfl⟩

/-- Accepting-payload phase 12 scans to the left blank and returns at the origin.
**Proof sketch.** Induct on the number of stored cells to the left. At zero,
the head is on the left blank; otherwise its cell is nonblank and the left
move reduces that number. All other tracks and the native input are retained. -/
private lemma f2_loopHost_payload_rewind (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool)
    (ch : ℤ) (word out : List Bool) : ∀ j, j ≤ word.length →
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out) (j + 1) =
      f2_loopFrame body F base (some (.inr (.inr 13))) p flag counter
        (bufferTape word) ch 0 out := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    change (match (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
        (bufferTape word) ch ((0 : ℤ) - 1) out).workTapeSymbols
          (Fin.last (body.k + 1 + (1 + F.k))) with
      | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
          (some (.inr (.inr 12)))
      | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
          (some (.inr (.inr 13)))).apply _ = _
    rw [f2_loopFrame_payload]
    simp only [zero_sub, bufferTape_left]
    rw [f2_loopControl_apply]
    simp [f2_loopWrite]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hs : (f2_loopHost body F anchor findMode).tm.step
        (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out) =
        f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch ((j : ℤ) - 1) out := by
      change (match (f2_loopFrame body F base (some (.inr (.inr 12))) p flag counter
          (bufferTape word) ch (((j + 1 : ℕ) : ℤ) - 1) out).workTapeSymbols
            (Fin.last (body.k + 1 + (1 + F.k))) with
        | some _ => f2_loopControlAction body F 0 none (none, 0) (none, .neg) none
            (some (.inr (.inr 12)))
        | none => f2_loopControlAction body F 0 none (none, 0) (none, .pos) none
            (some (.inr (.inr 13)))).apply _ = _
      rw [f2_loopFrame_payload]
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega : j < word.length)]
      rw [f2_loopControl_apply]
      simp [f2_loopWrite, sub_eq_add_neg]
    rw [hs]
    exact ih (by omega)

/-- Phase 13 replays a framed payload, retaining arbitrary inactive tracks.
**Proof sketch.** Express the frame as the right-block replay configuration
using its own inactive tape and head projections, then apply the already
proved actual-host replay correspondence. -/
private lemma f2_loopHost_frame_replay (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool}
    (base : Cfg (body.k + 1 + (1 + F.k) + 1) Bool (f2_LoopHostState body F) x)
    (p : Fin (x.length + 2)) (flag counter : ℤ → Option Bool) (ch : ℤ) (word : List Bool) :
    let c := f2_loopFrame body F base (some (.inr (.inr 13))) p flag counter (bufferTape word) ch 0 []
    ((f2_loopHost body F anchor findMode).tm.runFrom c (word.length + 1)).state = none ∧
    ((f2_loopHost body F anchor findMode).tm.runFrom c (word.length + 1)).output = word := by
  dsimp only
  let c := f2_loopFrame body F base (some (.inr (.inr 13))) p flag counter (bufferTape word) ch 0 []
  let tapes := fun i : Fin (body.k + 1 + (1 + F.k)) => c.workTapes i.castSucc
  let heads := fun i : Fin (body.k + 1 + (1 + F.k)) => c.workTapePos i.castSucc
  have he : c = rightCfg (fun _ : Unit => Sum.inr (Sum.inr (13 : Fin 14)))
      (f2_loopReplayCfg x p (some ()) 0 word []) tapes heads := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    all_goals
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [rightCfg, Fin.addCases_left, tapes, heads]
        congr 1
      · intro j
        have hj : j = 0 := Subsingleton.elim _ _
        subst j
        have hf : body.k + 1 + (1 + F.k) ≠ body.k := by omega
        simp [c, rightCfg, f2_loopReplayCfg, f2_loopFrame, hf]
  change ((f2_loopHost body F anchor findMode).tm.runFrom c _).state = _ ∧
    ((f2_loopHost body F anchor findMode).tm.runFrom c _).output = _
  rw [he, f2_loopHost_replay]
  exact ⟨rfl, rfl⟩

/-- An accepting stopped call emits its fixed verdict or replays its full
captured payload, including the empty payload, within `2|output|+3` steps.
**Proof sketch.** The true stop flag dispatches acceptance independently of
payload length. Decision mode emits immediately. Find mode takes one left
move, the length-plus-one rewind, and the length-plus-one replay. -/
private lemma f2_loopHost_accept (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (c : Cfg body.k Bool body.State x)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (hc : c.state = none) :
    ∃ t ≤ 2 * c.output.length + 3,
      ((f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false c false (some true) word fuel) t).state = none ∧
      ((f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false c false (some true) word fuel) t).output =
          (if findMode then c.output else [true]) := by
  let base := f2_loopCall body F anchor false c false (some true) word fuel
  let flag := fun z : ℤ => if z = 0 then some true else none
  have hf : base = f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos flag
      (bufferTape word) (bufferTape c.output) 0 c.output.length [] := by
    have hstate : (f2_loopCall body F anchor false c false (some true) word fuel).state =
        some (.inr (.inr (7 : Fin 14))) := by
      simp [f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, hc]
    simpa only [hstate] using f2_loopCall_frame body F anchor false c false (some true) word fuel
  have hstep : (f2_loopHost body F anchor findMode).tm.step base =
      if findMode then
        f2_loopFrame body F base (some (.inr (.inr 12))) c.inputPos flag
          (bufferTape word) (bufferTape c.output) 0 (c.output.length - 1) []
      else f2_loopFrame body F base none c.inputPos flag
        (bufferTape word) (bufferTape c.output) 0 c.output.length [true] := by
    conv_lhs => arg 1; rw [hf]
    change (if (f2_loopFrame body F base (some (.inr (.inr 7))) c.inputPos flag
        (bufferTape word) (bufferTape c.output) 0 c.output.length []).workTapeSymbols
          ⟨body.k, by omega⟩ = some true then _
      else f2_loopControlAction body F 0 (some none) (none, 0) (none, 0) none
        (some (.inr (.inr 8)))).apply _ = _
    rw [f2_loopFrame_flag]
    change (if findMode then
      f2_loopControlAction body F 0 none (none, 0) (none, .neg) none (some (.inr (.inr 12)))
      else f2_loopControlAction body F 0 none (none, 0) (none, 0) (some true) none).apply _ = _
    cases findMode <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [f2_loopControl_apply] <;> simp [f2_loopWrite, sub_eq_add_neg]
  cases findMode with
  | false =>
    refine ⟨1, by omega, ?_⟩
    change ((f2_loopHost body F anchor false).tm.step base).state = none ∧
      ((f2_loopHost body F anchor false).tm.step base).output = [true]
    rw [hstep]
    exact ⟨rfl, rfl⟩
  | true =>
    refine ⟨2 * c.output.length + 3, le_refl _, ?_⟩
    have hrun : (f2_loopHost body F anchor true).tm.runFrom base (2 * c.output.length + 3) =
        (f2_loopHost body F anchor true).tm.runFrom
          (f2_loopFrame body F base (some (.inr (.inr 13))) c.inputPos flag
            (bufferTape word) (bufferTape c.output) 0 0 []) (c.output.length + 1) := by
      rw [show 2 * c.output.length + 3 =
          ((c.output.length + 1) + (c.output.length + 1)) + 1 by omega,
        MultiTapeTM.runFrom_succ_eq_step, hstep]
      simp only [if_true]
      rw [MultiTapeTM.runFrom_add, f2_loopHost_payload_rewind body F anchor true base
        c.inputPos flag (bufferTape word) 0 c.output [] c.output.length (le_refl _)]
    change ((f2_loopHost body F anchor true).tm.runFrom base _).state = _ ∧
      ((f2_loopHost body F anchor true).tm.runFrom base _).output = _
    rw [hrun]
    exact f2_loopHost_frame_replay body F anchor true base c.inputPos flag (bufferTape word) 0 c.output

/-- One body round plus all controller work has a uniform local bound.
Acceptance returns the exact payload/verdict; rejection either reaches the
decremented next seam or finishes underflow within the same segment.
**Proof sketch.** For acceptance, replace a padded endpoint by its first
halt, capture every emission, and use the accepting dispatch bound. At most
one symbol is emitted per source step. For rejection, the live seam supplies
the anchor-stop capture; append the complete width-bounded counter dispatch. -/
private lemma f2_loopHost_round (body F : FinTM Bool) (anchor : body.State)
    (findMode : Bool) {x : List Bool} (s next payload : List Bool) (accepted : Bool)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (t : ℕ) (ht : 0 < t)
    (hanchor : ∀ u, 0 < u → u < t →
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) u).state ≠ some anchor)
    (hend : if accepted then
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state = none ∧
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output = payload
      else body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
        Cfg.ofWords anchor (stateWord body.k next)) :
    ∃ v ≤ 3 * t + 2 * word.length + 5,
      let start := f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel
      if accepted then
        ((f2_loopHost body F anchor findMode).tm.runFrom start v).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom start v).output =
          (if findMode then payload else [true])
      else if (f2_loopDebit word).2 then
        (f2_loopHost body F anchor findMode).tm.runFrom start v =
          f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k next))
            true none (f2_loopDebit word).1 fuel
      else ((f2_loopHost body F anchor findMode).tm.runFrom start v).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom start v).output =
          (if findMode then [] else [false]) := by
  dsimp only
  let start := Cfg.ofWords (input := x) anchor (stateWord body.k s)
  by_cases ha : accepted = true
  · simp only [ha, if_true] at hend ⊢
    obtain ⟨u, hu, hut, hlive, hhalt, he⟩ := f2_loop_first_halt body.tm start t (by simp [start, Cfg.ofWords]) hend.1
    have hcap := f2_loopHost_halt_return body F anchor findMode start u word fuel hu hlive
      (fun v hv hvu => hanchor v hv (by omega)) hhalt
    obtain ⟨v, hv, hstop, hout⟩ := f2_loopHost_accept body F anchor findMode (body.tm.runFrom start u) word fuel hhalt
    have hw : (body.tm.runFrom start u).output.length ≤ u := by
      simpa [start, Cfg.ofWords] using f2_loop_output_length_le body.tm start u
    refine ⟨u + v, by omega, ?_⟩
    change ((f2_loopHost body F anchor findMode).tm.runFrom
      (f2_loopCall body F anchor false start true none word fuel) (u + v)).state = _ ∧ _
    rw [MultiTapeTM.runFrom_add, hcap]
    refine ⟨hstop, ?_⟩
    rw [hout, he, hend.2]
  · simp only [ha] at hend ⊢
    have hguard : ∀ u < t, (u = 0 ∧ true = true) ∨ (body.tm.runFrom start u).state ≠ some anchor := by
      intro u hu
      by_cases hz : u = 0
      · exact Or.inl ⟨hz, rfl⟩
      · exact Or.inr (hanchor u (by omega) hu)
    have hcap := f2_loopHost_anchor_return body F anchor findMode false start true t word fuel
      (by rw [hend]; rfl)
      (by intro hz; omega) hguard
    change (f2_loopHost body F anchor findMode).tm.runFrom _ (t + 1) = _ at hcap
    have hr : body.tm.runFrom start t = Cfg.ofWords anchor (stateWord body.k next) := hend
    rw [hr] at hcap
    obtain ⟨v, hv, hfinish⟩ := f2_loopHost_reject body F anchor findMode
      {Cfg.ofWords (input := x) anchor (stateWord body.k next) with state := none} word fuel rfl rfl
    refine ⟨(t + 1) + v, by omega, ?_⟩
    change (if (f2_loopDebit word).2 then
      (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor false start true none word fuel) ((t + 1) + v) = _
      else _)
    rw [MultiTapeTM.runFrom_add, hcap]
    exact hfinish

/-- At a canonical call, only the retained fuel bank can be displaced.
All body, flag, counter and capture heads are at zero. -/
private lemma f2_loopCall_heads (body F : FinTM Bool) (anchor : body.State)
    (x s word : List Bool) (fuel : Cfg F.k Bool F.State x) (B : ℕ)
    (hf : ∀ i, -(B : ℤ) ≤ fuel.workTapePos i ∧ fuel.workTapePos i ≤ B) :
    ∀ i, -(B : ℤ) ≤ (f2_loopCall body F anchor false
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos i ∧
      (f2_loopCall body F anchor false
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos i ≤ B := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [f2_loopCall, captureCfg, f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, Cfg.ofWords]
  · simp only [f2_loopCall, captureCfg, Fin.coe_castSucc, dif_pos j.isLt]
    change -(B : ℤ) ≤ (f2_loopBodyPadded body F anchor
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos j ∧
      (f2_loopBodyPadded body F anchor
        (Cfg.ofWords anchor (stateWord body.k s)) true none word fuel).workTapePos j ≤ B
    simp only [f2_loopBodyPadded, leftCfg]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [Fin.addCases_left, f2_loopBodyCfg, Cfg.ofWords]
    · simp only [Fin.addCases_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.addCases_left]
        omega
      · simpa only [Fin.addCases_right] using hf j

/-- The audit's fixed maximum for the received phase budgets. -/
private def f2_loopHost_bound : ℕ := max 1 (max 9 (3 + 2 + 5))

/-- Configuration contracts for the concrete controller in both output modes.
**Continuation frontier: unproved.** The public corollaries below are conditional
on this one machine-construction obligation; this is not a closed batch.

**Proof sketch.** Run the relocated fuel source to its first halt using
`f2_loopHost_fuel_capture`. Phases 0--5 copy and retain its binary fuel, clear
the capture tape, and rewind the two work heads and the input head. Run
startup with `f2_loopHost_body_capture`; phase 6 clears the flag and releases
the initial seam without a debit. Define each candidate seam using the
iterated body word and `f2_loopDebit` word, retaining the fuel work residue.
`f2_loop_orbit_inv` supplies every local body premise. The body simulation and
first-halt lemmas identify the first stop; W1 preserves its full payload.
Phase 7 either emits/replays that payload or starts the width-bounded
borrow. `f2_loopBorrow_correct` is the standalone counter template to be
lifted into phases 8--10. Final zero underflow and phase 11 belong to the
last rejecting segment. If the last candidate accepts, choose any halted
false/empty terminal. Sum the phase constants with the audit's maximum
ledger. The missing proof is precisely the controller-level lifting and
assembly of these phase contracts, including startup and replay bounds. -/
/- Batch L2 closure: the preceding continuation docstring is retained as
historical evidence. Its listed obligations are discharged below by the phase
lemmas and the canonical family; there is no remaining construction admission. -/
private lemma f2_loopHost_contracts (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (out : List Bool → List Bool → List Bool) (findMode : Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = out x s
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ c : ℕ, ∀ x : List Bool,
      ∃ (cfg : ℕ → Cfg (f2_loopHost body F anchor findMode).k Bool
          (f2_loopHost body F anchor findMode).State x) (startup : ℕ),
        startup ≤ c * (T x.length + 1) ∧
        (f2_loopHost body F anchor findMode).tm.runFrom
          ((f2_loopHost body F anchor findMode).tm.initCfg x) startup = cfg 0 ∧
        (∀ i ≤ R x.length, (cfg i).output = []) ∧
        (cfg (R x.length + 1)).state = none ∧
        (cfg (R x.length + 1)).output = (if findMode then [] else [false]) ∧
        (∀ i ≤ R x.length, ∃ t ≤ c * (T x.length + 1),
          if acceptF x ((stepF x)^[i] (s0 x)) then
            ((f2_loopHost body F anchor findMode).tm.runFrom (cfg i) t).state = none ∧
            ((f2_loopHost body F anchor findMode).tm.runFrom (cfg i) t).output =
              (if findMode then out x ((stepF x)^[i] (s0 x)) else [true])
          else (f2_loopHost body F anchor findMode).tm.runFrom (cfg i) t = cfg (i + 1)) ∧
        (∀ i ≤ R x.length, ∀ j,
          -(T x.length : ℤ) ≤ (cfg i).workTapePos j ∧
          (cfg i).workTapePos j ≤ T x.length) ∧
        (∀ j, -((T x.length + c * (T x.length + 1) : ℕ) : ℤ) ≤
          (cfg (R x.length + 1)).workTapePos j ∧
          (cfg (R x.length + 1)).workTapePos j ≤
            (T x.length + c * (T x.length + 1) : ℕ)) := by
  classical
  refine ⟨f2_loopHost_bound, ?_⟩
  intro x
  obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare, hfuel⟩ :=
    f2_loopHost_prepare body F anchor findMode R T hF x
  obtain ⟨btime, hbt, hbguard, hbend⟩ := hstart x
  let words (i : ℕ) := (fun w => (f2_loopDebit w).1)^[i] (Nat.bits (R x.length))
  let orbit (i : ℕ) := (stepF x)^[i] (s0 x)
  let candidate (i : ℕ) := f2_loopCall body F anchor false
    (Cfg.ofWords (input := x) anchor (stateWord body.k (orbit i))) true none (words i) fuel
  have hheads (i : ℕ) (j) :
      -(T x.length : ℤ) ≤ (candidate i).workTapePos j ∧
      (candidate i).workTapePos j ≤ T x.length :=
    f2_loopCall_heads body F anchor x (orbit i) (words i) fuel (T x.length) hfuel j
  have hwidth (i : ℕ) : (words i).length ≤ T x.length := by
    dsimp only [words]
    rw [f2_loopDebit_iterate_length]
    exact f2_loop_fuel_width F R T hF x
  have hsuccess (i : ℕ) (hi : i ≤ R x.length) :
      (f2_loopDebit (words i)).2 = true ↔ i < R x.length := by
    rw [f2_loopDebit_success]
    dsimp only [words]
    rw [f2_loopDebit_iterate_value _ _ hi]
    omega
  -- Each specified seam has its own local contract, including unreachable
  -- seams following an earlier accepting candidate.
  have hlocal : ∀ i ≤ R x.length, ∃ t ≤ f2_loopHost_bound * (T x.length + 1),
      if acceptF x (orbit i) then
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).output =
          (if findMode then out x (orbit i) else [true])
      else if i < R x.length then
        (f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t = candidate (i + 1)
      else
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) t).output =
          (if findMode then [] else [false]) := by
    intro i hi
    obtain ⟨t, htpos, ht, hguard, hend⟩ := hround x (orbit i)
      (f2_loop_orbit_inv Inv stepF s0 hInv0 hInvStep x i)
    obtain ⟨v, hv, hsegment⟩ := f2_loopHost_round body F anchor findMode
      (orbit i) (stepF x (orbit i)) (out x (orbit i)) (acceptF x (orbit i))
      (words i) fuel t htpos hguard hend
    refine ⟨v, ?_, ?_⟩
    · have hw := hwidth i
      change v ≤ 10 * (T x.length + 1)
      omega
    · simpa only [candidate, words, orbit, Function.iterate_succ_apply', hsuccess i hi] using hsegment
  -- Fix one segment witness per seam so the last rejecting segment's actual
  -- endpoint, including underflow and emission, is the chosen terminal.
  let time (i : ℕ) := if hi : i ≤ R x.length then (hlocal i hi).choose else 0
  have htime (i : ℕ) (hi : i ≤ R x.length) :
      time i ≤ f2_loopHost_bound * (T x.length + 1) ∧
      if acceptF x (orbit i) then
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).output =
          (if findMode then out x (orbit i) else [true])
      else if i < R x.length then
        (f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i) = candidate (i + 1)
      else
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).state = none ∧
        ((f2_loopHost body F anchor findMode).tm.runFrom (candidate i) (time i)).output =
          (if findMode then [] else [false]) := by
    simpa only [time, dif_pos hi] using (hlocal i hi).choose_spec
  have hlast := htime (R x.length) (le_refl _)
  let terminal := if acceptF x (orbit (R x.length)) then
      {candidate (R x.length + 1) with state := none, output := if findMode then [] else [false]}
    else (f2_loopHost body F anchor findMode).tm.runFrom (candidate (R x.length))
      (time (R x.length))
  have hterminal : terminal.state = none ∧ terminal.output = (if findMode then [] else [false]) := by
    dsimp only [terminal]
    split
    · exact ⟨rfl, rfl⟩
    · rename_i ha
      simpa only [ha, Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl] using hlast.2
  have hterminalheads (j) :
      -((T x.length + f2_loopHost_bound * (T x.length + 1) : ℕ) : ℤ) ≤
        terminal.workTapePos j ∧
      terminal.workTapePos j ≤ (T x.length + f2_loopHost_bound * (T x.length + 1) : ℕ) := by
    dsimp only [terminal]
    split
    · have h := hheads (R x.length + 1) j
      dsimp only
      omega
    · have hd := f2_head_steps (f2_loopHost body F anchor findMode).tm
        (candidate (R x.length)) (time (R x.length)) j
      have hs := hheads (R x.length) j
      have ht := (htime (R x.length) (le_refl _)).1
      omega
  let cfg (i : ℕ) := if i ≤ R x.length then candidate i else terminal
  have hcfg (i : ℕ) (hi : i ≤ R x.length) : cfg i = candidate i := if_pos hi
  refine ⟨cfg, ftime + (btime + 2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ftime + (btime + 2) ≤ 10 * (T x.length + 1)
    omega
  · rw [hcfg 0 (Nat.zero_le _), MultiTapeTM.runFrom_add, hprepare,
      f2_loopHost_start body F anchor findMode (s0 x) btime fuel hbguard hbend]
    simp only [candidate, words, orbit, Function.iterate_zero_apply, hfo]
  · intro i hi
    rw [hcfg i hi]
    rfl
  · simpa only [cfg, if_neg (by omega : ¬R x.length + 1 ≤ R x.length)] using hterminal.1
  · simpa only [cfg, if_neg (by omega : ¬R x.length + 1 ≤ R x.length)] using hterminal.2
  · intro i hi
    have h := htime i hi
    refine ⟨time i, h.1, ?_⟩
    rw [hcfg i hi]
    change (if acceptF x (orbit i) then _ else _)
    by_cases ha : acceptF x (orbit i) = true
    · simp only [ha, if_true] at h ⊢
      simpa only [orbit] using h.2
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hlt : i < R x.length
      · rw [hcfg (i + 1) (by omega)]
        simpa only [if_pos hlt] using h.2
      · have he : i = R x.length := by omega
        subst i
        rw [show cfg (R x.length + 1) = terminal from if_neg (by omega)]
        simp only [terminal, ha, Bool.false_eq_true, ↓reduceIte]

  · intro i hi j
    rw [hcfg i hi]
    exact hheads i j
  · intro j
    rw [show cfg (R x.length + 1) = terminal from if_neg (by omega)]
    exact hterminalheads j

/-- The first accepting segment returns its own payload; an already-halted
empty-output terminal supplies exhaustion.
**Proof sketch.** Induct on the ordered candidate range. Acceptance at its
head terminates immediately. Otherwise compose the advance with the shifted
induction hypothesis; `find?_map` shifts the selected index back by one.
Thus the payload is tied to the least accepting candidate, including when
that payload is empty. -/
private lemma f2_loop_find_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (payload : ℕ → List Bool) (B N : ℕ)
    (hend : (cfg N).state = none ∧ (cfg N).output = [])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = payload j
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ N * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output =
        (match (List.range N).find? accept with | some i => payload i | none => []) := by
  induction N generalizing cfg accept payload with
  | zero => exact ⟨0, by simp, by simpa using hend⟩
  | succ N ih =>
    obtain ⟨t, ht, hc⟩ := hround 0 (by omega)
    by_cases hb : accept 0 = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · exact Nat.le_mul_of_pos_left B (by omega)
      · simpa [List.range_succ_eq_map, hb] using hc.2
    · simp only [hb] at hc
      obtain ⟨s, hs, hhalt, hout⟩ := ih
        (fun j => cfg (j + 1)) (fun j => accept (j + 1))
        (fun j => payload (j + 1)) hend (fun j hj => hround (j + 1) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc, hout, List.range_succ_eq_map]
        simp only [List.find?_cons_of_neg hb, List.find?_map, Function.comp_def]
        cases (List.range N).find? (fun j => accept (j + 1)) <;> rfl

/-- Uniform seam positions and segment lengths confine the complete loop,
including an accepting halt and all stationary later times. No round count
occurs in the interval: every next segment restarts at a bounded seam. -/
private lemma f2_segment_heads {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x) (N B H : ℕ)
    (hseam : ∀ j < N, ∀ i, -(H : ℤ) ≤ (cfg j).workTapePos i ∧
      (cfg j).workTapePos i ≤ H)
    (hend : (cfg N).state = none)
    (hterminal : ∀ i, -((H + B : ℕ) : ℤ) ≤ (cfg N).workTapePos i ∧
      (cfg N).workTapePos i ≤ (H + B : ℕ))
    (hsegment : ∀ j < N, ∃ u ≤ B,
      (tm.runFrom (cfg j) u).state = none ∨ tm.runFrom (cfg j) u = cfg (j + 1)) :
    ∀ t i, -((H + B : ℕ) : ℤ) ≤ (tm.runFrom (cfg 0) t).workTapePos i ∧
      (tm.runFrom (cfg 0) t).workTapePos i ≤ (H + B : ℕ) := by
  induction N generalizing cfg with
  | zero =>
    intro t i
    rw [MultiTapeTM.runFrom_of_halt _ hend]
    exact hterminal i
  | succ N ih =>
    intro t i
    obtain ⟨u, hu, he⟩ := hsegment 0 (by omega)
    have hs := hseam 0 (by omega) i
    have hp (v : ℕ) (hv : v ≤ B) :
        -((H + B : ℕ) : ℤ) ≤ (tm.runFrom (cfg 0) v).workTapePos i ∧
        (tm.runFrom (cfg 0) v).workTapePos i ≤ (H + B : ℕ) := by
      have hh := f2_head_steps tm (cfg 0) v i
      omega
    by_cases ht : t ≤ u
    · exact hp t (ht.trans hu)
    · rw [show t = u + (t - u) by omega, MultiTapeTM.runFrom_add]
      rcases he with he | he
      · rw [MultiTapeTM.runFrom_of_halt _ he]
        exact hp u hu
      · rw [he]
        exact ih (fun j => cfg (j + 1))
          (fun j hj => hseam (j + 1) (by omega)) hend hterminal
          (fun j hj => hsegment (j + 1) (by omega)) (t - u) i

/-- Convert an all-time, origin-centred trajectory bound to total space.
The inclusive interval contains every head position at every prefix. -/
private lemma f2_space_radius (M : FinTM Bool) (x : List Bool) (B : ℕ)
    (h : ∀ t i, -(B : ℤ) ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
      (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ≤ B) (t : ℕ) :
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (2 * B + 1) := by
  have hc (i : Fin M.k) : M.tm.spaceUsedByTape (M.tm.initCfg x) t i ≤ 2 * B + 1 := by
    have hs : M.tm.visitedByTapeHead (M.tm.initCfg x) t i ⊆
        Finset.Icc (-(B : ℤ)) (B : ℤ) := by
      intro z hz
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_Icc.mpr (h u i)
    exact (Finset.card_le_card hs).trans (by rw [Int.card_Icc]; omega)
  unfold MultiTapeTM.spaceUsed
  calc
    _ ≤ ∑ _i : Fin M.k, (2 * B + 1) := Finset.sum_le_sum (fun i _ => hc i)
    _ = _ := by simp

/-- A bounded startup followed by reusable seams has all-time space linear
in the common segment budget, independently of the number of rounds. -/
private lemma f2_seamed_space (M : FinTM Bool) (x : List Bool)
    (cfg : ℕ → Cfg M.k Bool M.State x) (N B H startup : ℕ)
    (hstart : startup ≤ B) (hinit : M.tm.runFrom (M.tm.initCfg x) startup = cfg 0)
    (hseam : ∀ j < N, ∀ i, -(H : ℤ) ≤ (cfg j).workTapePos i ∧
      (cfg j).workTapePos i ≤ H)
    (hend : (cfg N).state = none)
    (hterminal : ∀ i, -((H + B : ℕ) : ℤ) ≤ (cfg N).workTapePos i ∧
      (cfg N).workTapePos i ≤ (H + B : ℕ))
    (hsegment : ∀ j < N, ∃ u ≤ B,
      (M.tm.runFrom (cfg j) u).state = none ∨ M.tm.runFrom (cfg j) u = cfg (j + 1))
    (t : ℕ) : M.tm.spaceUsed (M.tm.initCfg x) t ≤ M.k * (2 * (H + B) + 1) := by
  apply f2_space_radius M x (H + B) _ t
  intro u i
  by_cases hu : u ≤ startup
  · have hp := f2_head_steps M.tm (M.tm.initCfg x) u i
    rw [show (M.tm.initCfg x).workTapePos i = 0 from rfl, zero_sub, zero_add] at hp
    omega
  · rw [show u = startup + (u - startup) by omega, MultiTapeTM.runFrom_add, hinit]
    exact f2_segment_heads M.tm cfg N B H hseam hend hterminal hsegment (u - startup) i

/-- The received result-bearing loop, retaining its reusable-seam space bound. -/
private lemma f2_exists_loopFind_space (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (out : List Bool → List Bool → List Bool)
    (s0 : List Bool → List Bool) (R T : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = out x s
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s))) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => match (List.range (R x.length + 1)).find?
            (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
          | some i => out x ((stepF x)^[i] (s0 x))
          | none => [])
        (fun n => c * (T n + 1) * (R n + 2)) ∧
      ∀ x t, E.tm.spaceUsed (E.tm.initCfg x) t ≤ c * (T x.length + 1) := by
  obtain ⟨c, hc⟩ := f2_loopHost_contracts body F anchor Inv stepF acceptF out true s0 R T
    hF hInv0 hInvStep hstart hround
  let E := f2_loopHost body F anchor true
  have ht : E.ComputesFunInTime
      (fun x => match (List.range (R x.length + 1)).find?
          (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
        | some i => out x ((stepF x)^[i] (s0 x))
        | none => []) (fun n => c * (T n + 1) * (R n + 2)) := by
    intro x
    obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments, hheads, hterminal⟩ := hc x
    obtain ⟨t, ht, hhalt, houtput⟩ := f2_loop_find_run E.tm cfg
      (fun i => acceptF x ((stepF x)^[i] (s0 x)))
      (fun i => out x ((stepF x)^[i] (s0 x))) (c * (T x.length + 1)) (R x.length + 1)
      ⟨hend, by simpa using hout⟩
      (fun j hj => by simpa using hsegments j (by omega))
    have hrun := E.tm.runFrom_add (E.tm.initCfg x) startup t
    rw [hinit] at hrun
    have hcompute : E.ComputesInTime x
        (match (List.range (R x.length + 1)).find?
            (fun i => acceptF x ((stepF x)^[i] (s0 x))) with
          | some i => out x ((stepF x)^[i] (s0 x))
          | none => []) (startup + t) := by
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hrun]; exact hhalt
      · rw [hrun]; exact houtput
    apply hcompute.mono
    calc startup + t ≤ c * (T x.length + 1) +
          (R x.length + 1) * (c * (T x.length + 1)) := Nat.add_le_add hs ht
      _ = c * (T x.length + 1) * (R x.length + 2) := by
        rw [Nat.mul_comm (R x.length + 1)]
        simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two]
        omega

  let K := E.k * (2 * (c + 1) + 1)
  refine ⟨E, c + K, ?_, ?_⟩
  · intro x
    exact (ht x).mono (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  · intro x t
    obtain ⟨cfg, startup, hs, hinit, _, hend, _, hsegments, hheads, hterminal⟩ := hc x
    have h := f2_seamed_space E x cfg (R x.length + 1) (c * (T x.length + 1))
      (T x.length) startup hs hinit (fun j hj => hheads j (by omega)) hend hterminal
      (by
        intro j hj
        obtain ⟨u, hu, he⟩ := hsegments j (by omega)
        refine ⟨u, hu, ?_⟩
        split at he
        · exact Or.inl he.1
        · exact Or.inr he) t
    have hb : 2 * (T x.length + c * (T x.length + 1)) + 1 ≤
        (2 * (c + 1) + 1) * (T x.length + 1) := by
      have he : (2 * (c + 1) + 1) * (T x.length + 1) =
          2 * (T x.length + c * (T x.length + 1)) + T x.length + 3 := by ring
      omega
    calc
      _ ≤ E.k * ((2 * (c + 1) + 1) * (T x.length + 1)) :=
        h.trans (Nat.mul_le_mul_left _ hb)
      _ = K * (T x.length + 1) := by dsimp [K]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- The audited split-search step preserves every existing candidate bit;
at the one-past-end state it stalls. -/
private def f2_splitStep (w s : List Bool) : List Bool :=
  if s.length ≤ w.length then s ++ [true] else s

/-- Split-search acceptance is the exact padding length equation. -/
private def f2_splitAccept (C e : ℕ) (w s : List Bool) : Bool :=
  decide (s.length + C * (s.length + 1) ^ e = w.length)

/-- The length invariant is closed even on arbitrary candidate bit patterns. -/
private lemma f2_splitStep_inv (w s : List Bool) (hs : s.length ≤ w.length + 1) :
    (f2_splitStep w s).length ≤ w.length + 1 := by
  unfold f2_splitStep
  split <;> simp_all <;> omega

/-- All orbit points tested by the loop are precisely the unary candidates.
**Proof sketch.** Before fuel is exhausted the current length is the iteration
index, so the step appends one true. The extra one-past-end state is included. -/
private lemma f2_splitStep_orbit (w : List Bool) : ∀ i, i ≤ w.length + 1 →
    (f2_splitStep w)^[i] [] = List.replicate i true := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega)]
    simp only [f2_splitStep, List.length_replicate, if_pos (by omega : i ≤ w.length)]
    exact (List.replicate_succ').symm

/-- Extensional equality of search predicates on the searched list preserves
both the least-success index and failure. -/
private lemma f2_catalogFind_congr {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ a ∈ xs, p a = q a) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.find?_cons, h a (by simp)]
    rw [ih (fun b hb => h b (by simp [hb]))]

/-- The orbit predicate and `solveSplit` use the same finite search, including
its unsuccessful branch. The Boolean equality is converted explicitly. -/
private lemma f2_splitFind_eq (C e : ℕ) (w : List Bool) :
    (List.range (w.length + 1)).find?
      (fun i => f2_splitAccept C e w ((f2_splitStep w)^[i] [])) = solveSplit C e w.length := by
  apply f2_catalogFind_congr
  intro i hi
  have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
  rw [f2_splitStep_orbit w i (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [f2_splitAccept, List.length_replicate, decide_eq_true_eq, beq_iff_eq]

/-- Failed split search is equivalent to rejecting every candidate within fuel. -/
private lemma f2_splitFind_none (C e : ℕ) (w : List Bool) :
    solveSplit C e w.length = none ↔
      ∀ i ≤ w.length, f2_splitAccept C e w ((f2_splitStep w)^[i] []) = false := by
  rw [← f2_splitFind_eq, List.find?_eq_none]
  simp only [List.mem_range, Nat.lt_succ_iff, Bool.not_eq_true]

/-- Each successful orbit payload is exactly the split at the returned index;
exhaustion returns the same empty word on both sides. -/
private lemma f2_splitLoop_result (C e : ℕ) (w : List Bool) :
    (match (List.range (w.length + 1)).find?
        (fun i => f2_splitAccept C e w ((f2_splitStep w)^[i] [])) with
      | some i => pairEncode (w.take ((f2_splitStep w)^[i] []).length)
          (w.drop ((f2_splitStep w)^[i] []).length)
      | none => []) =
    (match solveSplit C e w.length with
      | some i => pairEncode (w.take i) (w.drop i)
      | none => []) := by
  rw [f2_splitFind_eq]
  cases hs : solveSplit C e w.length with
  | none => rfl
  | some i =>
    have hi := List.mem_of_find?_eq_some hs
    have hi' : i ≤ w.length := by simpa only [List.mem_range, Nat.lt_succ_iff] using hi
    simp only [f2_splitStep_orbit w i (by omega), List.length_replicate]

/-- The loop overhead raises the body's polynomial exponent by exactly one.
**Proof sketch.** Bound the additive one by `(n+1)^(e+1)` and the factor `n+2`
by `2(n+1)`, then combine powers. This includes `n=0` and `e=0`. -/
private lemma f2_splitLoop_bound (c A e n : ℕ) :
    c * (A * (n + 1) ^ (e + 1) + 1) * (n + 2) ≤
      (2 * c * (A + 1)) * (n + 1) ^ (e + 2) := by
  have hp : 1 ≤ (n + 1) ^ (e + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hfirst : A * (n + 1) ^ (e + 1) + 1 ≤ (A + 1) * (n + 1) ^ (e + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    _ ≤ c * ((A + 1) * (n + 1) ^ (e + 1)) * (2 * (n + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c hfirst) (by omega)
    _ = _ := by rw [show e + 2 = (e + 1) + 1 by omega, Nat.pow_succ]; ring

/-- A physical input position after consuming a unary count, saturated at the
right boundary. -/
private def f2_splitPos (w : List Bool) (j : ℕ) : Fin (w.length + 2) :=
  ⟨min j w.length + 1, by omega⟩

/-- A saturated countdown read is blank exactly after all input bits. -/
private lemma f2_splitPos_read {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = f2_splitPos w j) :
    cfg.inputSymbol = if h : j < w.length then some (w[j]'h) else none := by
  by_cases hj : j < w.length
  · rw [dif_pos hj]
    exact inputSymbolInner j
      (by simp [hp, f2_splitPos, Nat.min_eq_left (by omega : j ≤ w.length), Nat.add_comm]) hj
  · rw [dif_neg hj]
    simp [Cfg.inputSymbol, hp, f2_splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]

/-- A forward move increments a saturated unary countdown position. -/
private lemma f2_splitPos_succ (w : List Bool) (j : ℕ) :
    moveInputPos (f2_splitPos w j) .pos = f2_splitPos w (j + 1) := by
  by_cases hj : j < w.length
  · rw [moveInputPos_pos_of_ne_right _ (by simp [f2_splitPos] <;> omega)]
    apply Fin.ext
    simp only [f2_splitPos, Fin.val_mk]
    omega
  · have he : f2_splitPos w j = ⟨w.length + 1, by omega⟩ := by
      apply Fin.ext
      simp [f2_splitPos, Nat.min_eq_right (by omega : w.length ≤ j)]
    rw [he, SignType.pos_eq_one, moveInputPos_rightBoundary]
    apply Fin.ext
    simp [f2_splitPos, Nat.min_eq_right (by omega : w.length ≤ j + 1)]

/-- A partially cleared unary scratch word, with its remaining suffix exposed. -/
private def f2_splitScratch (q j : ℕ) (z : ℤ) : Option Bool :=
  if (j : ℤ) ≤ z ∧ z < q then some true else none

/-- Clearing the exposed scratch cell advances the cleared prefix by one. -/
private lemma f2_splitScratch_erase (q j : ℕ) :
    Function.update (f2_splitScratch q j) (j : ℤ) none = f2_splitScratch q (j + 1) := by
  funext z
  by_cases hz : z = (j : ℤ)
  · subst z; simp [f2_splitScratch]
  · rw [Function.update_of_ne hz]
    have he : ((j : ℤ) ≤ z ∧ z < q) ↔ (((j + 1 : ℕ) : ℤ) ≤ z ∧ z < q) := by omega
    simp only [f2_splitScratch, he]

/-- The rejection cleanup preserves all candidate bits, appends only within
the input-length range, clears every unary scratch tape, and restores heads.
State 4 is an absorbing return seam, suitable for a first-return embedding. -/
private def f2_splitRestoreTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 5 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some _ => ⟨.pos, Fin.cases (none, .pos) (fun _ => (some none, .pos)),
            none, some (0, q.2 || inp.isNone)⟩
        | none => ⟨0, Fin.cases (if q.2 then (none, .neg) else (some (some true), .neg))
            (fun _ => (some none, .neg)), none, some (1, false)⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some (1, false)⟩
        | none => ⟨0, fun _ => (none, .pos), none, some (2, false)⟩
      | 2 => controlAction .neg (some (3, false))
      | 3 => match inp with
        | some _ => controlAction .neg (some (3, false))
        | none => controlAction .pos (some (4, false))
      | _ => controlAction 0 (some (4, false)) }

/-- The clearing scan has consumed `j` candidate cells and erased exactly that
prefix on each scratch tape; the physical input tracks the same count. -/
private def f2_splitRestoreScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (f2_splitRestoreTM k).State w :=
  ⟨some (0, decide (w.length < j)), f2_splitPos w j,
    Fin.cases (bufferTape s) (fun _ => f2_splitScratch (s.length + 1) j), fun _ => j, []⟩

/-- The silent cleanup scans each candidate bit once, including false bits.
**Proof sketch.** Each transition preserves tape 0, clears one cell on every
scratch tape, and advances all heads. The overflow flag records precisely
whether more candidate cells than native input cells have been consumed. -/
private lemma f2_splitRestore_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) j =
      f2_splitRestoreScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (f2_splitRestoreScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [f2_splitRestoreScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    have hin := f2_splitPos_read w (f2_splitRestoreScan k w s j) j rfl
    unfold MultiTapeTM.step
    change ((f2_splitRestoreTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [f2_splitRestoreTM, hw]
    refine Cfg.ext ?_ (f2_splitPos_succ w j) ?_ ?_ rfl
    · change some (0, decide (w.length < j) ||
        (f2_splitRestoreScan k w s j).inputSymbol.isNone) = some (0, decide (w.length < j + 1))
      rw [hin]
      by_cases hjn : j < w.length
      · simp [hjn, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
      · simp [hjn, show w.length < j + 1 by omega]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact f2_splitScratch_erase _ _
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitRestoreScan]

/-- A cleaned configuration has only the candidate on tape zero; all work
heads are synchronized and the physical output is empty. -/
private def f2_splitRestoreClean (k : ℕ) (w s : List Bool)
    (q : (f2_splitRestoreTM k).State) (p : Fin (w.length + 2)) (h : ℤ) :
    Cfg (k + 1) Bool (f2_splitRestoreTM k).State w :=
  ⟨some q, p, Fin.cases (bufferTape s) (fun _ => fun _ => none), fun _ => h, []⟩

/-- The end-of-scan step clears the final extra scratch cell and appends to
tape 0 exactly when the old candidate length is at most the input length. -/
private lemma f2_splitRestore_append (k : ℕ) (w s : List Bool) :
    (f2_splitRestoreTM k).tm.step (f2_splitRestoreScan k w s s.length) =
      f2_splitRestoreClean k w (f2_splitStep w s) (1, false)
        (f2_splitPos w s.length) (s.length - 1) := by
  have hw : (f2_splitRestoreScan k w s s.length).workTapeSymbols 0 = none := by
    simp [f2_splitRestoreScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((f2_splitRestoreTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [f2_splitRestoreTM, hw]
  by_cases hs : s.length ≤ w.length
  · have hflag : decide (w.length < s.length) = false := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa [Action.apply, f2_splitRestoreClean, f2_splitStep, hs] using (bufferTape_append s true).symm
      · change Function.update (f2_splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [f2_splitScratch_erase]
        funext z
        simp [f2_splitRestoreClean, f2_splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitRestoreScan, f2_splitRestoreClean, sub_eq_add_neg]
  · have hflag : decide (w.length < s.length) = true := by simp; omega
    rw [hflag]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [Action.apply, f2_splitRestoreScan, f2_splitRestoreClean, f2_splitStep, hs]
      · change Function.update (f2_splitScratch (s.length + 1) s.length) (s.length : ℤ) none = _
        rw [f2_splitScratch_erase]
        funext z
        simp [f2_splitRestoreClean, f2_splitScratch]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitRestoreScan, f2_splitRestoreClean, sub_eq_add_neg]

/-- Candidate-guided rewind restores every head, including heads on tapes
that have already been cleared. No candidate bit is altered. -/
private lemma f2_splitRestore_rewind (k : ℕ) (w s : List Bool) (p : Fin (w.length + 2)) :
    ∀ j, j ≤ s.length →
      (f2_splitRestoreTM k).tm.runFrom
        (f2_splitRestoreClean k w s (1, false) p ((j : ℤ) - 1)) (j + 1) =
        f2_splitRestoreClean k w s (2, false) p 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, f2_splitRestoreClean, f2_splitRestoreTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, f2_splitRestoreScan]
  | succ j ih =>
    intro hj
    have hs : (f2_splitRestoreTM k).tm.step
        (f2_splitRestoreClean k w s (1, false) p (((j + 1 : ℕ) : ℤ) - 1)) =
        f2_splitRestoreClean k w s (1, false) p ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, f2_splitRestoreClean, f2_splitRestoreTM, Cfg.workTapeSymbols,
        Fin.cases_zero, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- Complete rejection cleanup restores exactly the audited state-word seam.
It works for arbitrary candidate bits, and its one-past-end stall is silent.
**Proof sketch.** Scan and erase `|s|` cells, handle the final scratch cell,
rewind synchronized heads along the preserved candidate, then rewind input.
The cost is at most `2|s|+|w|+5`, and every transition is silent. -/
private lemma f2_splitRestore_run (k : ℕ) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (f2_splitStep w s)) := by
  have hlen : s.length ≤ (f2_splitStep w s).length := by
    unfold f2_splitStep
    split <;> simp
  obtain ⟨r, hr, he⟩ := f2_catalogRewind (f2_splitRestoreTM k).tm (2, false) (3, false)
    (some (4, false)) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (f2_splitRestoreClean k w (f2_splitStep w s) (2, false) (f2_splitPos w s.length) 0) rfl
  have hp : (f2_splitPos w s.length).val ≤ w.length + 1 := by simp [f2_splitPos] <;> omega
  have hfirst : (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) (s.length + 1) =
      f2_splitRestoreClean k w (f2_splitStep w s) (1, false) (f2_splitPos w s.length) (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_splitRestore_scan k w s _ (le_refl _),
      f2_splitRestore_append]
  refine ⟨(s.length + 1) + (s.length + 1) + r, ?_, ?_⟩
  · change r ≤ (f2_splitPos w s.length).val + 2 at hr
    omega
  · rw [MultiTapeTM.runFrom_add _ _ r,
      MultiTapeTM.runFrom_add _ (s.length + 1) (s.length + 1),
      hfirst, f2_splitRestore_rewind k w (f2_splitStep w s) _ _ hlen, he]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitRestoreClean, Cfg.ofWords, stateWord]
    · rfl
    · rfl

/-- Replace source emissions by native-input consumption. Tape zero retains
the candidate; the source bank occupies successor-indexed tapes. A finite
flag remembers consumption past the native right boundary. -/
private def f2_splitCountAction {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (over : Bool) (inp : Option Bool) (a : Action k Bool S) : Action (k + 1) Bool H :=
  let over' := over || (a.output.isSome && inp.isNone)
  ⟨if a.output.isSome then .pos else 0, Fin.cases (none, 0) a.workTapes, none,
    some (match a.state with | some q => emb q over' | none => ret over')⟩

/-- Source configurations use an empty virtual input and arbitrary initialized
work tapes. Their output length is consumed after the candidate's length. -/
private def f2_splitCountCfg {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) : Cfg (k + 1) Bool H w :=
  let over := decide (w.length < s.length + c.output.length)
  ⟨some (match c.state with | some q => emb q over | none => ret over),
    f2_splitPos w (s.length + c.output.length), Fin.cases (bufferTape s) c.workTapes,
    Fin.cases 0 c.workTapePos, []⟩

/-- Consuming one additional symbol updates the saturation flag exactly. -/
private lemma f2_splitCount_over {k : ℕ} {S : Type} (w : List Bool)
    (cfg : Cfg k Bool S w) (j : ℕ) (hp : cfg.inputPos = f2_splitPos w j) :
    (decide (w.length < j) || cfg.inputSymbol.isNone) = decide (w.length < j + 1) := by
  rw [f2_splitPos_read w cfg j hp]
  by_cases hj : j < w.length
  · simp [hj, show ¬w.length < j by omega, show ¬w.length < j + 1 by omega]
  · simp [hj, show w.length < j + 1 by omega]

/-- One transformed step consumes exactly its optional source emission,
preserves the candidate, and reproduces all source-bank writes and moves.
**Proof sketch.** Split on the optional output and on tape zero versus source
tapes. The one-emission case is precisely the saturated-position increment
and overflow update; the zero-emission case leaves both unchanged. -/
private lemma f2_splitCount_apply {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) (a : Action k Bool S) :
    (f2_splitCountAction emb ret (decide (w.length < s.length + c.output.length))
      (f2_splitCountCfg emb ret w s c).inputSymbol a).apply (f2_splitCountCfg emb ret w s c) =
      f2_splitCountCfg emb ret w s (a.apply c) := by
  have hflag := f2_splitCount_over w (f2_splitCountCfg emb ret w s c)
    (s.length + c.output.length) rfl
  cases ho : a.output with
  | none =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simp [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho]
    · simpa [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho] using
        moveInputPos_zero (f2_splitPos w (s.length + c.output.length))
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitCountAction, f2_splitCountCfg, Action.apply]
  | some b =>
    refine Cfg.ext ?_ ?_ ?_ ?_ rfl
    · simpa [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        congrArg (fun flag => some (match a.state with | some q => emb q flag | none => ret flag)) hflag
    · simpa [f2_splitCountAction, f2_splitCountCfg, Action.apply, ho, Nat.add_assoc] using
        f2_splitPos_succ w (s.length + c.output.length)
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;> rfl
    · funext i; refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitCountAction, f2_splitCountCfg, Action.apply]

/-- A counted source run follows the original work-bank computation exactly,
including a final emitting halt, while consuming its output on native input.
**Proof sketch.** Empty virtual input always reads blank. Apply the one-step
correspondence through the source's first halt, as in `capture_run`; the
physical output stays empty throughout. -/
private lemma f2_splitCount_run {k : ℕ} {S H : Type}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → Bool → H) (ret : Bool → H)
    (hagree : ∀ q over inp work, host.tr (emb q over) inp work =
      f2_splitCountAction emb ret over inp (tm.tr q none (fun i => work i.succ)))
    (w s : List Bool) (c : Cfg k Bool S []) (t : ℕ)
    (hlive : ∀ j < t, ¬(tm.runFrom c j).Halted) :
    host.runFrom (f2_splitCountCfg emb ret w s c) t =
      f2_splitCountCfg emb ret w s (tm.runFrom c t) := by
  have hstep (d : Cfg k Bool S []) (hs : ¬d.Halted) :
      host.step (f2_splitCountCfg emb ret w s d) = f2_splitCountCfg emb ret w s (tm.step d) := by
    cases hq : d.state with
    | none => exact False.elim (hs hq)
    | some q =>
      have hstate : (f2_splitCountCfg emb ret w s d).state =
          some (emb q (decide (w.length < s.length + d.output.length))) := by
        simp [f2_splitCountCfg, hq]
      have hsource : d.inputSymbol = none := by
        unfold Cfg.inputSymbol
        split_ifs with h₀ h₁
        · rfl
        · rfl
        · have hp := d.inputPos.isLt
          simp only [Fin.ext_iff, Fin.val_zero] at h₀
          simp only [List.length_nil] at hp
          simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff, Fin.val_one] at h₁
          omega
      have hwork : (fun i => (f2_splitCountCfg emb ret w s d).workTapeSymbols i.succ) =
          d.workTapeSymbols := by
        funext i; simp [f2_splitCountCfg, Cfg.workTapeSymbols]
      simp only [MultiTapeTM.step, hstate, hq]
      rw [hagree, hwork, hsource]
      exact f2_splitCount_apply emb ret w s d _
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
      hstep _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- The in-file generator's loop phase ends with every unary scratch head
back at zero, ready for the restoration controller. The source input is empty;
its loop side length is supplied by the initialized work tapes.
**Proof sketch.** Run the existing exact nested-loop invariant over the full
box and then take the final halting transition. No fresh generator proof is
assumed, and the zero coefficient is included. -/
private lemma f2_splitPoly_loop_end (c C q : ℕ) (hq : 0 < q) :
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (f2_catalogPolyCost q C (c + 1) + 1) =
      {f2_catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) with state := none} := by
  have hl := f2_catalogPoly_loop (c := c) (C := C) [] q hq c (by omega)
    (fun _ => 0) (by simp) [] q 0 (by omega)
  have hout : q * (C * q ^ c) = C * q ^ (c + 1) := by rw [Nat.pow_succ]; ring
  have hloop : (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_catalogPolyCfg (C := C) [] q (.loop (Fin.last c)) (fun _ => 0) [])
      (f2_catalogPolyCost q C (c + 1)) =
      f2_catalogPolyCfg (C := C) [] q (.advance (Fin.last (c + 1))) (fun _ => 0)
        (List.replicate (C * q ^ (c + 1)) true) := by
    simpa [f2_catalogPolyCost, hout] using hl
  rw [MultiTapeTM.runFrom_succ_eq_step', hloop]
  simp only [MultiTapeTM.step, f2_catalogPolyCfg, f2_catalogPolyUnaryTM, Fin.val_last,
    Nat.lt_irrefl, ↓reduceDIte]
  refine Cfg.ext rfl ?_ rfl ?_ ?_
  · rfl
  · funext i; simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, Action.apply, f2_catalogPolyCfg]
  · simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, Action.apply, f2_catalogPolyCfg]

/-- A run reaching an absorbing control state has a least such entry, and its
configuration at that first entry is already the final configuration.
**Proof sketch.** Choose the least hit. Absorption makes its entire suffix
constant, so the bounded endpoint identifies the first-hit configuration. -/
private lemma f2_catalogFirstEntry {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (q : S) (c d : Cfg k Bool S w) (T : ℕ)
    (hfix : ∀ z : Cfg k Bool S w, z.state = some q → tm.step z = z)
    (hd : d.state = some q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, (∀ j < t, (tm.runFrom c j).state ≠ some q) ∧ tm.runFrom c t = d := by
  classical
  have hh : ∃ t, (tm.runFrom c t).state = some q := ⟨T, by rw [hT, hd]⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
  have hs : (tm.runFrom c t).state = some q := Nat.find_spec hh
  refine ⟨t, ht, fun j hj => Nat.find_min hh hj, ?_⟩
  have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
    Function.iterate_fixed (hfix _ hs) _
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, hconst] at he
  exact he.symm

/-- The cleanup's return seam is absorbing, so its exact restoration can be
exported with positive duration and no earlier return-state visit. -/
private lemma f2_splitRestore_first (k : ℕ) (w s : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 2 * s.length + w.length + 5 ∧
      (∀ j < t, ((f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) j).state
        ≠ some (4, false)) ∧
      (f2_splitRestoreTM k).tm.runFrom (f2_splitRestoreScan k w s 0) t =
        Cfg.ofWords (4, false) (stateWord (k + 1) (f2_splitStep w s)) := by
  obtain ⟨T, hTle, hT⟩ := f2_splitRestore_run k w s
  have hfix (z : Cfg (k + 1) Bool (f2_splitRestoreTM k).State w)
      (hz : z.state = some (4, false)) : (f2_splitRestoreTM k).tm.step z = z := by
    unfold MultiTapeTM.step
    rw [hz]
    change (controlAction 0 (some (4, false))).apply z = z
    rw [controlAction_apply, moveInputPos_zero]
    cases z
    simp_all
  obtain ⟨t, ht, hi, he⟩ := f2_catalogFirstEntry (f2_splitRestoreTM k).tm (4, false)
    (f2_splitRestoreScan k w s 0) _ T hfix rfl hT
  refine ⟨t, ?_, ht.trans hTle, hi, he⟩
  by_contra h
  have ht0 : t = 0 := by omega
  have hstate := congrArg Cfg.state he
  simp only [ht0, MultiTapeTM.runFrom_zero, f2_splitRestoreScan, Cfg.ofWords,
    Option.some.injEq, Prod.mk.injEq] at hstate
  have hf := congrArg (fun q : (f2_splitRestoreTM k).State => q.1.val) hstate
  norm_num at hf

/-- Native countdown acceptance is exactly equality of the consumed length
and the original input length; overflow and short counts both reject. -/
private lemma f2_splitCount_accept {k : ℕ} {S H : Type} (emb : S → Bool → H) (ret : Bool → H)
    (w s : List Bool) (c : Cfg k Bool S []) :
    (!decide (w.length < s.length + c.output.length) &&
      (f2_splitCountCfg emb ret w s c).inputSymbol.isNone) =
        decide (s.length + c.output.length = w.length) := by
  rw [f2_splitPos_read w (f2_splitCountCfg emb ret w s c) (s.length + c.output.length) rfl]
  by_cases hlt : s.length + c.output.length < w.length
  · simp [hlt, show ¬s.length + c.output.length = w.length by omega]
  · by_cases he : s.length + c.output.length = w.length
    · simp [he]
    · simp [hlt, he, show w.length < s.length + c.output.length by omega]

/-- The counted simulation can be stopped at the source's first halt without
losing the exact initialized-bank endpoint. This removes any padded halted
tail from a source time bound before entering the next controller phase. -/
private lemma f2_splitCount_firstHalt {k : ℕ} {S H : Type}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
    (emb : S → Bool → H) (ret : Bool → H)
    (hagree : ∀ q over inp work, host.tr (emb q over) inp work =
      f2_splitCountAction emb ret over inp (tm.tr q none (fun i => work i.succ)))
    (w s : List Bool) (c d : Cfg k Bool S []) (T : ℕ)
    (hd : d.state = none) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (f2_splitCountCfg emb ret w s c) t = f2_splitCountCfg emb ret w s d := by
  classical
  have hh : ∃ t, (tm.runFrom c t).state = none := ⟨T, by rw [hT, hd]⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
  have hs : (tm.runFrom c t).state = none := Nat.find_spec hh
  have he := tm.runFrom_add c t (T - t)
  rw [Nat.add_sub_of_le ht, hT, tm.runFrom_of_halt _ hs] at he
  refine ⟨t, ht, ?_⟩
  rw [f2_splitCount_run tm host emb ret hagree w s c t (fun j hj => Nat.find_min hh hj), ← he]

/-- Prepare the polynomial loop bank by copying the candidate's length to all
scratch tapes in parallel, adding the extra side-length cell, and rewinding
all work heads along the untouched candidate. State 2 is the return seam. -/
private def f2_splitPrepareTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 3 × Bool
  tm := {
    q₀ := (0, false)
    tr := fun q inp work => match q.1.val with
      | 0 => match work 0 with
        | some _ => ⟨.pos, Fin.cases (none, .pos) (fun _ => (some (some true), .pos)),
            none, some (0, q.2 || inp.isNone)⟩
        | none => ⟨0, Fin.cases (none, .neg) (fun _ => (some (some true), .neg)),
            none, some (1, q.2)⟩
      | 1 => match work 0 with
        | some _ => ⟨0, fun _ => (none, .neg), none, some (1, q.2)⟩
        | none => ⟨0, fun _ => (none, .pos), none, some (2, q.2)⟩
      | _ => controlAction 0 (some (2, q.2)) }

/-- During preparation, every scratch tape contains the length scanned so far. -/
private def f2_splitPrepareScan (k : ℕ) (w s : List Bool) (j : ℕ) :
    Cfg (k + 1) Bool (f2_splitPrepareTM k).State w :=
  ⟨some (0, decide (w.length < j)), f2_splitPos w j,
    Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape j), fun _ => j, []⟩

/-- Preparation copies a unary side length without reading or changing any
candidate bit value. The same induction covers a candidate past native EOF. -/
private lemma f2_splitPrepare_scan (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (f2_splitPrepareTM k).tm.runFrom (f2_splitPrepareScan k w s 0) j =
      f2_splitPrepareScan k w s j := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (f2_splitPrepareScan k w s j).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [f2_splitPrepareScan, Cfg.workTapeSymbols,
        List.getElem?_eq_getElem (by omega : j < s.length)]
    unfold MultiTapeTM.step
    change ((f2_splitPrepareTM k).tm.tr (0, decide (w.length < j)) _ _).apply _ = _
    simp only [f2_splitPrepareTM, hw]
    refine Cfg.ext ?_ (f2_splitPos_succ w j) ?_ ?_ rfl
    · exact congrArg (fun over => some (0, over))
        (f2_splitCount_over w (f2_splitPrepareScan k w s j) j rfl)
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact f2_catalogPolyTape_write j
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Action.apply, f2_splitPrepareScan]

/-- Prepared scratch tapes have side length `|s|+1`, with synchronized heads;
the overflow flag records the candidate's length alone. -/
private def f2_splitPrepareReady (k : ℕ) (w s : List Bool)
    (q : Fin 3) (h : ℤ) : Cfg (k + 1) Bool (f2_splitPrepareTM k).State w :=
  ⟨some (q, decide (w.length < s.length)), f2_splitPos w s.length,
    Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape (s.length + 1)), fun _ => h, []⟩

/-- Adding the extra side-length cell handles the empty candidate uniformly. -/
private lemma f2_splitPrepare_extra (k : ℕ) (w s : List Bool) :
    (f2_splitPrepareTM k).tm.step (f2_splitPrepareScan k w s s.length) =
      f2_splitPrepareReady k w s 1 (s.length - 1) := by
  have hw : (f2_splitPrepareScan k w s s.length).workTapeSymbols 0 = none := by
    simp [f2_splitPrepareScan, Cfg.workTapeSymbols]
  unfold MultiTapeTM.step
  change ((f2_splitPrepareTM k).tm.tr (0, decide (w.length < s.length)) _ _).apply _ = _
  simp only [f2_splitPrepareTM, hw]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact f2_catalogPolyTape_write s.length
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i <;>
      simp [Action.apply, f2_splitPrepareScan, f2_splitPrepareReady, sub_eq_add_neg]

/-- Rewind the synchronized bank along the preserved candidate; each scratch
tape retains its extra cell even though the rewind uses the candidate length. -/
private lemma f2_splitPrepare_rewind (k : ℕ) (w s : List Bool) : ∀ j, j ≤ s.length →
    (f2_splitPrepareTM k).tm.runFrom (f2_splitPrepareReady k w s 1 ((j : ℤ) - 1)) (j + 1) =
      f2_splitPrepareReady k w s 2 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, f2_splitPrepareReady, f2_splitPrepareTM, Cfg.workTapeSymbols,
      Fin.cases_zero, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply]
  | succ j ih =>
    intro hj
    have hs : (f2_splitPrepareTM k).tm.step (f2_splitPrepareReady k w s 1 (((j + 1 : ℕ) : ℤ) - 1)) =
        f2_splitPrepareReady k w s 1 ((j : ℤ) - 1) := by
      have he : (((j + 1 : ℕ) : ℤ) - 1) = j := by omega
      rw [he]
      simp only [MultiTapeTM.step, f2_splitPrepareReady, f2_splitPrepareTM, Cfg.workTapeSymbols,
        Fin.cases_zero, bufferTape_nat, List.getElem?_eq_getElem (by omega : j < s.length)]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- From the audited state-word seam, preparation takes exactly `2(|s|+1)`
silent steps and initializes every loop head at zero. -/
private lemma f2_splitPrepare_run (k : ℕ) (w s : List Bool) :
    (f2_splitPrepareTM k).tm.runFrom
      (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) (2 * (s.length + 1)) =
      f2_splitPrepareReady k w s 2 0 := by
  have hinit : Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s) =
      f2_splitPrepareScan k w s 0 := by
    refine Cfg.ext (by simp [f2_splitPrepareScan, Cfg.ofWords]) ?_ ?_ rfl rfl
    · simp [f2_splitPrepareScan, Cfg.ofWords, f2_splitPos]
    · funext i
      refine Fin.cases ?_ (fun i => ?_) i <;>
        simp [f2_splitPrepareScan, Cfg.ofWords, stateWord]
      funext z
      simp [f2_catalogPolyTape]
  have hfirst : (f2_splitPrepareTM k).tm.runFrom (f2_splitPrepareScan k w s 0) (s.length + 1) =
      f2_splitPrepareReady k w s 1 (s.length - 1) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', f2_splitPrepare_scan k w s _ (le_refl _), f2_splitPrepare_extra]
  rw [hinit, show 2 * (s.length + 1) = (s.length + 1) + (s.length + 1) by omega,
    MultiTapeTM.runFrom_add, hfirst, f2_splitPrepare_rewind k w s s.length (le_refl _)]

/-- Preparation can be exposed at its first return-state entry, with no
premature visit and without changing its exact initialized-bank endpoint. -/
private lemma f2_splitPrepare_first (k : ℕ) (w s : List Bool) :
    ∃ t ≤ 2 * (s.length + 1),
      (∀ j < t, ((f2_splitPrepareTM k).tm.runFrom
        (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) j).state ≠
          some (2, decide (w.length < s.length))) ∧
      (f2_splitPrepareTM k).tm.runFrom
        (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) t =
          f2_splitPrepareReady k w s 2 0 := by
  apply f2_catalogFirstEntry (f2_splitPrepareTM k).tm (2, decide (w.length < s.length))
  · intro z hz
    unfold MultiTapeTM.step
    rw [hz]
    change (controlAction 0 (some (2, decide (w.length < s.length)))).apply z = z
    rw [controlAction_apply, moveInputPos_zero]
    cases z
    simp_all
  · rfl
  · exact f2_splitPrepare_run k w s

/-- A phase trace excludes the round anchor even at its two endpoints. -/
private def f2_splitSafe {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (t : ℕ) : Prop :=
  ∀ j ≤ t, (tm.runFrom c j).state ≠ some anchor

/-- Safe traces concatenate at their literal configuration seam. -/
private lemma f2_splitSafe_add {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (u v : ℕ)
    (hu : f2_splitSafe tm anchor c u) (hv : f2_splitSafe tm anchor (tm.runFrom c u) v) :
    f2_splitSafe tm anchor c (u + v) := by
  intro j hj
  by_cases h : j ≤ u
  · exact hu j h
  · have he : j = u + (j - u) := by omega
    rw [he, MultiTapeTM.runFrom_add]
    exact hv (j - u) (by omega)

/-- Cut an absorbing source phase at its first terminal control state and
embed the entire prefix into a disjoint host phase.
**Proof sketch.** Take the least terminal visit. Absorption identifies its
configuration with the known endpoint. Induct on the prefix length using
transition agreement only before that visit; every mapped control state,
including a halted state, is different from the host anchor. -/
private lemma f2_splitEmbed_cut {k : ℕ} {S H : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H)
    (emb : S → H) (anchor : H) (stop : S → Prop) [DecidablePred stop]
    (haway : ∀ q, emb q ≠ anchor)
    (hfix : ∀ c : Cfg k Bool S w, (∃ q, c.state = some q ∧ stop q) → tm.step c = c)
    (hagree : ∀ q, ¬stop q → ∀ inp work,
      host.tr (emb q) inp work = (tm.tr q inp work).mapState emb)
    (c d : Cfg k Bool S w) (T : ℕ)
    (hd : ∃ q, d.state = some q ∧ stop q) (hT : tm.runFrom c T = d) :
    ∃ t ≤ T, host.runFrom (c.mapState emb) t = d.mapState emb ∧
      f2_splitSafe host anchor (c.mapState emb) t := by
  classical
  have hex : ∃ t, ∃ q, (tm.runFrom c t).state = some q ∧ stop q :=
    ⟨T, by rw [hT]; exact hd⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex (by rw [hT]; exact hd)
  have he : tm.runFrom c t = d := by
    have hh := tm.runFrom_add c t (T - t)
    have hconst : tm.runFrom (tm.runFrom c t) (T - t) = tm.runFrom c t :=
      Function.iterate_fixed (hfix _ (Nat.find_spec hex)) _
    rw [Nat.add_sub_of_le ht, hT, hconst] at hh
    exact hh.symm
  have hp : ∀ j ≤ t, host.runFrom (c.mapState emb) j = (tm.runFrom c j).mapState emb := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih =>
      intro hj
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        MultiTapeTM.runFrom_succ_eq_step']
      let z := tm.runFrom c j
      change host.step (z.mapState emb) = (tm.step z).mapState emb
      cases hz : z.state with
      | none => simp [MultiTapeTM.step, Cfg.mapState, hz]
      | some q =>
        have hn : ¬stop q := fun hq => Nat.find_min hex (by omega) ⟨q, hz, hq⟩
        simp only [MultiTapeTM.step, Cfg.mapState, hz, Option.map_some]
        rw [hagree q hn]
        rfl
  refine ⟨t, ht, by rw [hp t (le_refl _), he], ?_⟩
  intro j hj
  rw [hp j hj]
  cases hs : (tm.runFrom c j).state with
  | none => simp [Cfg.mapState, hs]
  | some q => simpa [Cfg.mapState, hs] using haway q

/-- A standalone native-input rewind, with an absorbing return at state two. -/
private def f2_splitRewindTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 3
  tm := {
    q₀ := 0
    tr := fun q inp _ => match q.val with
      | 0 => controlAction .neg (some 1)
      | 1 => match inp with
        | some _ => controlAction .neg (some 1)
        | none => controlAction .pos (some 2)
      | _ => controlAction 0 (some 2) }

/-- Emit a native-input split, using tape zero only as a length counter.
The first two states double native bits, state two completes the separator,
and state three copies the native suffix. No candidate bit is emitted. -/
private def f2_splitEmitTM (k : ℕ) : FinTM Bool where
  k := k + 1
  State := Fin 4
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match work 0 with
        | none => ⟨0, fun _ => (none, 0), some false, some 2⟩
        | some _ => ⟨0, fun _ => (none, 0), inp, some 1⟩
      | 1 => ⟨.pos, Fin.cases (none, .pos) (fun _ => (none, 0)), inp, some 0⟩
      | 2 => ⟨0, fun _ => (none, 0), some true, some 3⟩
      | _ => match inp with
        | some b => ⟨.pos, fun _ => (none, 0), some b, some 3⟩
        | none => controlAction 0 none }

/-- Each subroutine has its own finite control phase; only cleanup can
return to the anchor. The acceptance bit survives the native-input rewind. -/
private inductive f2_SplitBodyState (S : Type) where
  | anchor
  | prepare (q : Fin 3 × Bool)
  | count (q : S) (over : Bool)
  | check (over : Bool)
  | rewind (accept : Bool) (q : Fin 3)
  | restore (q : Fin 5 × Bool)
  | emit (q : Fin 4)

private instance f2_splitBodyStateFintype (S : Type) [Fintype S] :
    Fintype (f2_SplitBodyState S) := derive_fintype% _

/-- Equality of controller states compares only matching phases and their
finite payloads. Keep the instance private, including its generated helpers. -/
private instance f2_splitBodyStateDecidableEq (S : Type) [DecidableEq S] :
    DecidableEq (f2_SplitBodyState S) := by
  intro a b
  cases a <;> cases b
  all_goals try (solve | apply isFalse; intro h; cases h)
  · exact isTrue rfl
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.prepare.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.count.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.check.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.rewind.injEq _ _ _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.restore.injEq _ _)))
  · exact decidable_of_iff _ (Iff.symm (iff_of_eq (f2_SplitBodyState.emit.injEq _ _)))

/-- Combined round controller. The polynomial source starts on the prepared
bank, and its emissions are counted against native input without physical
output. Every seam transition is explicit, including the final anchor return. -/
private def f2_splitBodyTM (M : FinTM Bool) (start : M.State) : FinTM Bool where
  k := M.k + 1
  State := f2_SplitBodyState M.State
  tm := {
    q₀ := .anchor
    tr := fun q inp work => match q with
      | .anchor => controlAction 0 (some (.prepare (0, false)))
      | .prepare p =>
        if p.1 = 2 then controlAction 0 (some (.count start p.2))
        else ((f2_splitPrepareTM M.k).tm.tr p inp work).mapState .prepare
      | .count q over => f2_splitCountAction .count .check over inp
          (M.tm.tr q none (fun i => work i.succ))
      | .check over => controlAction 0 (some (.rewind (!over && inp.isNone) 0))
      | .rewind ok p =>
        if p = 2 then controlAction 0 (some (if ok then .emit 0 else .restore (0, false)))
        else ((f2_splitRewindTM M.k).tm.tr p inp work).mapState (.rewind ok)
      | .restore p =>
        if p = (4, false) then controlAction 0 (some .anchor)
        else ((f2_splitRestoreTM M.k).tm.tr p inp work).mapState .restore
      | .emit p => ((f2_splitEmitTM M.k).tm.tr p inp work).mapState .emit }

/-- The source bank has the candidate's successor length on each tape and
all heads at zero; its virtual input is empty. -/
private def f2_splitBank (M : FinTM Bool) (s : List Bool)
    (q : Option M.State) (out : List Bool) : Cfg M.k Bool M.State [] :=
  ⟨q, 1, fun _ => f2_catalogPolyTape (s.length + 1), fun _ => 0, out⟩

/-- The genuine initial configuration is the empty-candidate anchor seam;
there is no unproved startup work hidden in a zero-time witness. -/
private lemma f2_splitBody_start (M : FinTM Bool) (start : M.State) (w : List Bool) :
    (f2_splitBodyTM M start).tm.initCfg w =
      Cfg.ofWords .anchor (stateWord (M.k + 1) []) := by
  rw [initCfg_ofWords]
  congr 1
  funext i
  simp [stateWord]

/-- A complete source embedding commutes with every step, including halt. -/
private lemma f2_splitEmbed_run {k : ℕ} {S H : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM k Bool H) (emb : S → H)
    (hagree : ∀ q inp work, host.tr (emb q) inp work = (tm.tr q inp work).mapState emb)
    (c : Cfg k Bool S w) (t : ℕ) :
    host.runFrom (c.mapState emb) t = (tm.runFrom c t).mapState emb := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro z
  cases hs : z.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rw [hagree]
    rfl

/-- Preparation reaches its first return with the exact counted-source bank.
Every configuration of the embedded preparation is outside the anchor phase.
**Proof sketch.** Cut the absorbing source at its first return, map its full
configuration into the preparation phase, then take the explicit dispatch.
Check the source-bank seam field by field, including the native head and flag. -/
private lemma f2_splitBody_prepare (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * (s.length + 1),
      (f2_splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
          f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s
            (f2_splitBank M s (some start) []) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor
        (Cfg.ofWords (input := w) (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) := by
  obtain ⟨t, ht, he, hsafe⟩ := f2_splitEmbed_cut (f2_splitPrepareTM M.k).tm
    (f2_splitBodyTM M start).tm f2_SplitBodyState.prepare .anchor (fun q => q.1 = 2)
    (by intro q; simp)
    (by
      rintro z ⟨⟨q, over⟩, hz, hq⟩
      change q = 2 at hq
      subst q
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2, over))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [f2_splitBodyTM, hq])
    (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s))
    (f2_splitPrepareReady M.k w s 2 0) (2 * (s.length + 1))
    ⟨_, rfl, rfl⟩ (f2_splitPrepare_run M.k w s)
  have hstep : (f2_splitBodyTM M start).tm.step
      ((f2_splitPrepareReady M.k w s 2 0).mapState f2_SplitBodyState.prepare) =
      f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s
        (f2_splitBank M s (some start) []) := by
    simp only [MultiTapeTM.step, Cfg.mapState, f2_splitPrepareReady, Option.map_some,
      f2_splitBodyTM, ↓reduceIte]
    refine Cfg.ext ?_ ?_ rfl ?_ rfl
    · simp [Action.apply, controlAction, f2_splitCountCfg, f2_splitBank]
    · simp [Action.apply, controlAction, f2_splitCountCfg, f2_splitBank]
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [Action.apply, controlAction, f2_splitCountCfg, f2_splitBank]
  have hinit : (Cfg.ofWords (input := w) (0, false) (stateWord (M.k + 1) s)).mapState
      (f2_SplitBodyState.prepare (S := M.State)) = Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s) := rfl
  rw [hinit] at he hsafe
  have hend : (f2_splitBodyTM M start).tm.runFrom
      (Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)) (t + 1) =
      f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s
        (f2_splitBank M s (some start) []) := by
    rw [MultiTapeTM.runFrom_succ_eq_step', he, hstep]
  refine ⟨t, ht, hend, ?_⟩
  intro j hj
  by_cases hjt : j ≤ t
  · exact hsafe j hjt
  · have hj' : j = t + 1 := by omega
    rw [hj', hend]
    simp [f2_splitCountCfg, f2_splitBank]

/-- Counted evaluation reaches its first source halt; every prefix remains
in a count or check state and therefore cannot revisit the round anchor.
**Proof sketch.** Choose the least source halt and remove its constant halted
suffix. Apply the counted correspondence to every prefix through that halt;
its control image is disjoint from the anchor, including the return state. -/
private lemma f2_splitBody_count (M : FinTM Bool) (start : M.State) (w s : List Bool)
    (out : List Bool) (T : ℕ)
    (hT : M.tm.runFrom (f2_splitBank M s (some start) []) T = f2_splitBank M s none out) :
    ∃ t ≤ T, (f2_splitBodyTM M start).tm.runFrom
      (f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s (some start) [])) t =
      f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s none out) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor
        (f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s (some start) [])) t := by
  classical
  let c := f2_splitBank M s (some start) []
  let d := f2_splitBank M s none out
  have hh : ∃ t, (M.tm.runFrom c t).state = none := ⟨T, by rw [hT]; rfl⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh (by rw [hT]; rfl)
  have he : M.tm.runFrom c t = d := by
    have h := M.tm.runFrom_add c t (T - t)
    rw [Nat.add_sub_of_le ht, hT, M.tm.runFrom_of_halt _ (Nat.find_spec hh)] at h
    exact h.symm
  have hp (j : ℕ) (hj : j ≤ t) := f2_splitCount_run M.tm (f2_splitBodyTM M start).tm
    f2_SplitBodyState.count f2_SplitBodyState.check (fun _ _ _ _ => rfl) w s c j
    (fun l hl => Nat.find_min hh (by omega))
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hp t (le_refl _), he]
  · intro j hj
    rw [hp j hj]
    cases hq : (M.tm.runFrom c j).state <;> simp [f2_splitCountCfg, hq]

/-- Rewind preserves the exact source bank and physical output. Its terminal
state is cut before dispatch to the accepting emitter or rejecting cleanup.
**Proof sketch.** Use the quantitative native rewind, then cut its absorbing
return and embed that prefix while retaining the acceptance bit in control. -/
private lemma f2_splitBody_rewind (M : FinTM Bool) (start : M.State) (w : List Bool)
    (ok : Bool) (c : Cfg (M.k + 1) Bool (Fin 3) w)
    (hc : c.state = some 0) :
    ∃ t ≤ c.inputPos.val + 2,
      (f2_splitBodyTM M start).tm.runFrom (c.mapState (f2_SplitBodyState.rewind ok)) t =
        ({c with state := some (2 : Fin 3), inputPos := 1}).mapState (f2_SplitBodyState.rewind ok) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor (c.mapState (f2_SplitBodyState.rewind ok)) t := by
  obtain ⟨T, hT, he⟩ := f2_catalogRewind (f2_splitRewindTM M.k).tm (0 : Fin 3) (1 : Fin 3) (some (2 : Fin 3))
    (fun _ _ => rfl) (fun _ _ => rfl) c hc
  obtain ⟨t, ht, hend, hsafe⟩ := f2_splitEmbed_cut (f2_splitRewindTM M.k).tm
    (f2_splitBodyTM M start).tm (f2_SplitBodyState.rewind ok) .anchor (fun q => q = (2 : Fin 3))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (2 : Fin 3))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [f2_splitBodyTM, hq])
    c {c with state := some (2 : Fin 3), inputPos := 1} T ⟨(2 : Fin 3), rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Rejection cleanup is embedded up to its absorbing return, so its exact
restoration and the no-anchor property hold simultaneously in the body.
**Proof sketch.** Apply the exact restoration run and cut at its absorbing
false-flag return. Its host control remains in the restore phase; the final
transition to the anchor is accounted for separately by the round proof. -/
private lemma f2_splitBody_restore (M : FinTM Bool) (start : M.State) (w s : List Bool) :
    ∃ t ≤ 2 * s.length + w.length + 5,
      (f2_splitBodyTM M start).tm.runFrom
        ((f2_splitRestoreScan M.k w s 0).mapState f2_SplitBodyState.restore) t =
        Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (f2_splitStep w s)) ∧
      f2_splitSafe (f2_splitBodyTM M start).tm .anchor
        ((f2_splitRestoreScan M.k w s 0).mapState f2_SplitBodyState.restore) t := by
  obtain ⟨T, hT, he⟩ := f2_splitRestore_run M.k w s
  obtain ⟨t, ht, hend, hsafe⟩ := f2_splitEmbed_cut (f2_splitRestoreTM M.k).tm
    (f2_splitBodyTM M start).tm f2_SplitBodyState.restore .anchor (fun q => q = (4, false))
    (by intro q; simp)
    (by
      rintro z ⟨q, hz, rfl⟩
      simp only [MultiTapeTM.step, hz]
      change (controlAction 0 (some (4, false))).apply z = z
      rw [controlAction_apply, moveInputPos_zero]
      cases z; simp_all)
    (by intro q hq inp work; simp [f2_splitBodyTM, hq])
    (f2_splitRestoreScan M.k w s 0)
    (Cfg.ofWords (4, false) (stateWord (M.k + 1) (f2_splitStep w s))) T
    ⟨_, rfl, rfl⟩ he
  exact ⟨t, ht.trans hT, hend, hsafe⟩

/-- Emitter configurations preserve the initialized scratch bank and use the
candidate head only to count the doubled native prefix. -/
private def f2_splitEmitCfg (k : ℕ) (w s : List Bool) (q : Option (Fin 4))
    (j h : ℕ) (out : List Bool) : Cfg (k + 1) Bool (Fin 4) w :=
  ⟨q, f2_splitPos w j, Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape (s.length + 1)),
    Fin.cases (h : ℤ) (fun _ => 0), out⟩

/-- Two transitions emit two copies of the current native bit and advance
both the native head and the candidate counter. Arbitrary candidate bit
values are read only for their presence.
**Proof sketch.** Induct on the number of doubled cells. The two transitions
read the same native bit, emit it twice, and only then advance both heads. -/
private lemma f2_splitEmit_double (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    ∀ j, j ≤ s.length → (f2_splitEmitTM k).tm.runFrom
      (f2_splitEmitCfg k w s (some 0) 0 0 []) (2 * j) =
      f2_splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b]) := by
  intro j
  induction j with
  | zero => intro hj; rfl
  | succ j ih =>
    intro hj
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hread (q : Fin 4) (out : List Bool) :
        (f2_splitEmitCfg k w s (some q) j j out).inputSymbol = some (w[j]'(by omega)) := by
      rw [f2_splitPos_read w _ j rfl, dif_pos (by omega)]
    have hwork : (f2_splitEmitCfg k w s (some 0) j j
        ((w.take j).flatMap fun b => [b, b])).workTapeSymbols 0 = some (s[j]'(by omega)) := by
      simp [f2_splitEmitCfg, Cfg.workTapeSymbols, List.getElem?_eq_getElem (by omega : j < s.length)]
    have hfirst : (f2_splitEmitTM k).tm.step
        (f2_splitEmitCfg k w s (some 0) j j ((w.take j).flatMap fun b => [b, b])) =
        f2_splitEmitCfg k w s (some 1) j j
          (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) := by
      unfold MultiTapeTM.step
      change ((f2_splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
      simp only [f2_splitEmitTM, hwork, hread]
      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
      funext i; simp [Action.apply, f2_splitEmitCfg]
    rw [hfirst]
    unfold MultiTapeTM.step
    change ((f2_splitEmitTM k).tm.tr (1 : Fin 4) _ _).apply _ = _
    simp only [f2_splitEmitTM, hread]
    refine Cfg.ext rfl (f2_splitPos_succ w j) ?_ ?_ ?_
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    · funext i
      refine Fin.cases ?_ (fun l => ?_) i <;> simp [Action.apply, f2_splitEmitCfg]
    · change (((w.take j).flatMap fun b => [b, b]) ++ [w[j]'(by omega)]) ++
          [w[j]'(by omega)] = (w.take (j + 1)).flatMap fun b => [b, b]
      simp only [List.take_succ, List.getElem?_eq_getElem (by omega : j < w.length),
        Option.toList_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Once the counter is exhausted, emit the two separator bits without
moving the native head away from the beginning of the suffix. -/
private lemma f2_splitEmit_separator (k : ℕ) (w s : List Bool) (out : List Bool) :
    (f2_splitEmitTM k).tm.runFrom (f2_splitEmitCfg k w s (some 0) s.length s.length out) 2 =
      f2_splitEmitCfg k w s (some 3) s.length s.length (out ++ [false, true]) := by
  have hwork : (f2_splitEmitCfg k w s (some 0) s.length s.length out).workTapeSymbols 0 = none := by
    simp [f2_splitEmitCfg, Cfg.workTapeSymbols]
  have hf : (f2_splitEmitTM k).tm.step (f2_splitEmitCfg k w s (some 0) s.length s.length out) =
      f2_splitEmitCfg k w s (some 2) s.length s.length (out ++ [false]) := by
    unfold MultiTapeTM.step
    change ((f2_splitEmitTM k).tm.tr (0 : Fin 4) _ _).apply _ = _
    simp only [f2_splitEmitTM, hwork]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i; simp [Action.apply, f2_splitEmitCfg]
  rw [show 2 = 1 + 1 by omega, MultiTapeTM.runFrom_succ_eq_step,
    show (f2_splitEmitTM k).tm.step _ = _ from hf, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.runFrom_zero]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ ?_
  · funext i; simp [MultiTapeTM.step, f2_splitEmitTM, Action.apply, f2_splitEmitCfg]
  · simp [MultiTapeTM.step, f2_splitEmitTM, Action.apply, f2_splitEmitCfg, List.append_assoc]

/-- The suffix-copy phase preserves all work tapes and copies native bits
verbatim, including the empty suffix and its final blank-reading halt.
**Proof sketch.** Induct on the remaining suffix while allowing arbitrary
already-copied prefix and output. The nonempty case copies one native bit;
the empty case reads the right blank and halts without an extra emission. -/
private lemma f2_splitEmit_suffix (k : ℕ) (w s rest : List Bool) :
    ∀ pre out h, w = pre ++ rest → (f2_splitEmitTM k).tm.runFrom
      (f2_splitEmitCfg k w s (some 3) pre.length h out) (rest.length + 1) =
      f2_splitEmitCfg k w s none w.length h (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out h hw
    have he : w = pre := by simpa using hw
    clear hw
    subst w
    simp only [List.append_nil, List.length_nil, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    have hr := f2_splitPos_read pre (f2_splitEmitCfg k pre s (some 3) pre.length h out) pre.length rfl
    simp only [Nat.lt_irrefl, ↓reduceDIte] at hr
    unfold MultiTapeTM.step
    change ((f2_splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
    rw [hr]
    simp [f2_splitEmitTM, controlAction, f2_splitEmitCfg]
  | cons b rest ih =>
    intro pre out h hw
    have hread : (f2_splitEmitCfg k w s (some 3) pre.length h out).inputSymbol = some b := by
      rw [f2_splitPos_read w _ pre.length rfl]
      simp [hw]
    have hstep : (f2_splitEmitTM k).tm.step (f2_splitEmitCfg k w s (some 3) pre.length h out) =
        f2_splitEmitCfg k w s (some 3) (pre ++ [b]).length h (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((f2_splitEmitTM k).tm.tr (3 : Fin 4) _ _).apply _ = _
      rw [hread]
      refine Cfg.ext rfl ?_ rfl ?_ rfl
      · simpa only [List.length_append, List.length_singleton] using f2_splitPos_succ w pre.length
      · funext i; simp [f2_splitEmitTM, Action.apply, f2_splitEmitCfg]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (pre ++ [b]) (out ++ [b]) h (by simpa [List.append_assoc] using hw)

/-- The accepting emitter produces exactly the encoded native split in
`|s|+|w|+3` steps. Its candidate may contain any bit pattern.
**Proof sketch.** Double exactly the native prefix counted by the candidate,
emit the separator, and copy the remaining native suffix. Concatenate the
three exact runs and cancel the prefix length in the time expression. -/
private lemma f2_splitEmit_run (k : ℕ) (w s : List Bool) (hs : s.length ≤ w.length) :
    (f2_splitEmitTM k).tm.runFrom (f2_splitEmitCfg k w s (some 0) 0 0 [])
      (s.length + w.length + 3) =
      f2_splitEmitCfg k w s none w.length s.length
        (pairEncode (w.take s.length) (w.drop s.length)) := by
  have ht : s.length + w.length + 3 =
      2 * s.length + 2 + ((w.drop s.length).length + 1) := by
    simp only [List.length_drop]; omega
  rw [ht, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add _ (2 * s.length) 2,
    f2_splitEmit_double k w s hs _ (le_refl _), f2_splitEmit_separator]
  have h := f2_splitEmit_suffix k w s (w.drop s.length) (w.take s.length)
    (((w.take s.length).flatMap fun b => [b, b]) ++ [false, true]) s.length
    (List.take_append_drop s.length w).symm
  simpa [List.length_take, Nat.min_eq_left hs, pairEncode] using h

/-- A single transition is safe when both its endpoints exclude the anchor. -/
private lemma f2_splitSafe_one {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S w)
    (he : tm.step c = d) (hc : c.state ≠ some anchor) (hd : d.state ≠ some anchor) :
    tm.runFrom c 1 = d ∧ f2_splitSafe tm anchor c 1 := by
  refine ⟨he, ?_⟩
  intro j hj
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · exact hc
  · change (tm.step c).state ≠ _
    rw [he]; exact hd

/-- Concatenate two safe exact phase runs. -/
private lemma f2_splitSafe_join {k : ℕ} {S : Type} {w : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d f : Cfg k Bool S w) (u v : ℕ)
    (h1 : tm.runFrom c u = d) (hs1 : f2_splitSafe tm anchor c u)
    (h2 : tm.runFrom d v = f) (hs2 : f2_splitSafe tm anchor d v) :
    tm.runFrom c (u + v) = f ∧ f2_splitSafe tm anchor c (u + v) := by
  refine ⟨by rw [MultiTapeTM.runFrom_add, h1, h2], ?_⟩
  apply f2_splitSafe_add tm anchor c u v hs1
  rw [h1]; exact hs2

/-- A completed source gives a complete body round, including acceptance,
rejection, positive duration, and anchor exclusion over every strict interior
step. The bound explicitly includes all dispatches, rewinds, and emission.
**Proof sketch.** Depart the anchor in one step. Concatenate safe preparation,
counting, decision, and rewind traces. Equality accepts and emits native
slices. Inequality dispatches to the exact scratch restoration, followed by
one explicit return to the anchor. All intermediate states belong to disjoint
phases; the only anchor step is the final rejecting transition. -/
private lemma f2_splitBody_round (M : FinTM Bool) (start : M.State) (w s out : List Bool)
    (T : ℕ) (hT : M.tm.runFrom (f2_splitBank M s (some start) []) T = f2_splitBank M s none out) :
    ∃ t, 0 < t ∧ t ≤ T + 5 * s.length + 3 * w.length + 20 ∧
      (∀ j, 0 < j → j < t →
        ((f2_splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) j).state ≠ some .anchor) ∧
      if decide (s.length + out.length = w.length) then
        ((f2_splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).state = none ∧
        ((f2_splitBodyTM M start).tm.runFrom
          (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
      else (f2_splitBodyTM M start).tm.runFrom
        (Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) s)) t =
          Cfg.ofWords .anchor (stateWord (M.k + 1) (f2_splitStep w s)) := by
  let tm := (f2_splitBodyTM M start).tm
  let z : Cfg (M.k + 1) Bool (f2_SplitBodyState M.State) w :=
    Cfg.ofWords .anchor (stateWord (M.k + 1) s)
  let p : Cfg (M.k + 1) Bool (f2_SplitBodyState M.State) w :=
    Cfg.ofWords (.prepare (0, false)) (stateWord (M.k + 1) s)
  let d := f2_splitCountCfg f2_SplitBodyState.count f2_SplitBodyState.check w s (f2_splitBank M s none out)
  let ok := decide (s.length + out.length = w.length)
  let c : Cfg (M.k + 1) Bool (Fin 3) w :=
    ⟨some 0, f2_splitPos w (s.length + out.length),
      Fin.cases (bufferTape s) (fun _ => f2_catalogPolyTape (s.length + 1)),
      Fin.cases 0 (fun _ => 0), []⟩
  let r : Cfg (M.k + 1) Bool (f2_SplitBodyState M.State) w :=
    ({c with state := some (2 : Fin 3), inputPos := 1} : Cfg (M.k + 1) Bool (Fin 3) w).mapState
    (f2_SplitBodyState.rewind (S := M.State) ok)
  have hdepart : tm.runFrom z 1 = p := by
    change (controlAction 0 (some (.prepare (0, false)))).apply z = p
    rw [controlAction_apply, moveInputPos_zero]
    rfl
  obtain ⟨a, ha, hprep, hpreps⟩ := f2_splitBody_prepare M start w s
  obtain ⟨b, hb, hcount, hcounts⟩ := f2_splitBody_count M start w s out T hT
  obtain ⟨h1, hs1⟩ := f2_splitSafe_join tm .anchor p _ d (a + 1) b hprep hpreps hcount hcounts
  have hcheck : tm.step d = c.mapState (f2_SplitBodyState.rewind ok) := by
    unfold MultiTapeTM.step
    change (controlAction 0 (some (.rewind
      (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) 0))).apply d = _
    rw [controlAction_apply, moveInputPos_zero]
    have hok := f2_splitCount_accept f2_SplitBodyState.count f2_SplitBodyState.check w s
      (f2_splitBank M s none out)
    change (!decide (w.length < s.length + out.length) && d.inputSymbol.isNone) = ok at hok
    rw [hok]
    rfl
  obtain ⟨hcheck', hchecks⟩ := f2_splitSafe_one tm .anchor d _ hcheck
    (by simp [d, f2_splitCountCfg, f2_splitBank]) (by simp [c, Cfg.mapState])
  obtain ⟨h2, hs2⟩ := f2_splitSafe_join tm .anchor p d _ (a + 1 + b) 1 h1 hs1 hcheck' hchecks
  obtain ⟨v, hv, hrew, hrews⟩ := f2_splitBody_rewind M start w ok c rfl
  obtain ⟨h3, hs3⟩ := f2_splitSafe_join tm .anchor p _ r (a + 1 + b + 1) v h2 hs2 hrew hrews
  have hv' : v ≤ w.length + 3 := by
    have hp : c.inputPos.val ≤ w.length + 1 := by simp [c, f2_splitPos]
    omega
  by_cases hok : s.length + out.length = w.length
  · have hs : s.length ≤ w.length := by omega
    let ec := f2_splitEmitCfg M.k w s (some 0) 0 0 []
    let ed := f2_splitEmitCfg M.k w s none w.length s.length
      (pairEncode (w.take s.length) (w.drop s.length))
    have hdispatch : tm.step r = ec.mapState f2_SplitBodyState.emit := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, f2_splitBodyTM, ↓reduceIte, ok, hok, decide_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext rfl ?_ rfl rfl rfl
      simp [ec, f2_splitEmitCfg, f2_splitPos]
    obtain ⟨hd, hds⟩ := f2_splitSafe_one tm .anchor r _ hdispatch
      (by simp [r, Cfg.mapState]) (by simp [ec, Cfg.mapState, f2_splitEmitCfg])
    obtain ⟨h4, hs4⟩ := f2_splitSafe_join tm .anchor p r _ (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    have hemit : tm.runFrom (ec.mapState f2_SplitBodyState.emit) (s.length + w.length + 3) =
        ed.mapState f2_SplitBodyState.emit := by
      rw [f2_splitEmbed_run (f2_splitEmitTM M.k).tm tm f2_SplitBodyState.emit (fun _ _ _ => rfl)]
      exact congrArg (Cfg.mapState f2_SplitBodyState.emit) (f2_splitEmit_run M.k w s hs)
    have hemits : f2_splitSafe tm .anchor (ec.mapState f2_SplitBodyState.emit) (s.length + w.length + 3) := by
      intro j hj
      rw [f2_splitEmbed_run (f2_splitEmitTM M.k).tm tm f2_SplitBodyState.emit (fun _ _ _ => rfl)]
      cases hq : ((f2_splitEmitTM M.k).tm.runFrom ec j).state <;> simp [Cfg.mapState, hq]
    obtain ⟨h5, hs5⟩ := f2_splitSafe_join tm .anchor p _ _ (a + 1 + b + 1 + v + 1)
      (s.length + w.length + 3) h4 hs4 hemit hemits
    let u := a + 1 + b + 1 + v + 1 + (s.length + w.length + 3)
    have hend : tm.runFrom z (1 + u) = ed.mapState f2_SplitBodyState.emit := by
      rw [MultiTapeTM.runFrom_add, hdepart]; exact h5
    refine ⟨1 + u, by omega, by dsimp [u]; omega, ?_, ?_⟩
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hs5 (j - 1) (by dsimp [u] at hjt; omega)
    · simp only [hok, decide_true, ↓reduceIte]
      change (tm.runFrom z (1 + u)).state = none ∧ _
      rw [hend]
      exact ⟨rfl, rfl⟩
  · let rc := (f2_splitRestoreScan M.k w s 0).mapState (f2_SplitBodyState.restore (S := M.State))
    have hdispatch : tm.step r = rc := by
      simp only [r, c, Cfg.mapState, Option.map_some, MultiTapeTM.step,
        tm, f2_splitBodyTM, ↓reduceIte, ok, hok, decide_false, Bool.false_eq_true]
      rw [controlAction_apply, moveInputPos_zero]
      refine Cfg.ext ?_ ?_ ?_ ?_ rfl
      · simp [rc, f2_splitRestoreScan, Cfg.mapState]
      · simp [rc, f2_splitRestoreScan, Cfg.mapState, f2_splitPos]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i
        · rfl
        · funext z; simp [rc, f2_splitRestoreScan, Cfg.mapState, f2_splitScratch, f2_catalogPolyTape]
      · funext i
        refine Fin.cases ?_ (fun l => ?_) i <;> rfl
    obtain ⟨hd, hds⟩ := f2_splitSafe_one tm .anchor r rc hdispatch
      (by simp [r, Cfg.mapState]) (by simp [rc, Cfg.mapState, f2_splitRestoreScan])
    obtain ⟨h4, hs4⟩ := f2_splitSafe_join tm .anchor p r rc (a + 1 + b + 1 + v) 1 h3 hs3 hd hds
    obtain ⟨l, hl, hrest, hrests⟩ := f2_splitBody_restore M start w s
    obtain ⟨h5, hs5⟩ := f2_splitSafe_join tm .anchor p rc _ (a + 1 + b + 1 + v + 1) l h4 hs4 hrest hrests
    let u := a + 1 + b + 1 + v + 1 + l
    have hreturn : tm.step (Cfg.ofWords (.restore (4, false)) (stateWord (M.k + 1) (f2_splitStep w s))) =
        Cfg.ofWords (input := w) .anchor (stateWord (M.k + 1) (f2_splitStep w s)) := by
      change (controlAction 0 (some (f2_SplitBodyState.anchor (S := M.State)))).apply _ = _
      rw [controlAction_apply, moveInputPos_zero]
      rfl
    refine ⟨1 + u + 1, by omega, by dsimp [u]; omega, ?_, ?_⟩
    · intro j hj hjt
      change (tm.runFrom z j).state ≠ _
      rw [show j = 1 + (j - 1) by omega, MultiTapeTM.runFrom_add, hdepart]
      exact hs5 (j - 1) (by dsimp [u] at hjt; omega)
    · simp only [hok, decide_false, Bool.false_eq_true, ↓reduceIte]
      change tm.runFrom z (1 + u + 1) = _
      rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add, hdepart, h5, hreturn]

/-- Given the concrete startup and round contracts, the audited loop supplies
the frozen split-search result and exponent. No body contract is assumed as an
axiom: both are explicit arguments, including the positive silent stall.
**Proof sketch.** Enlarge the body coefficient to cover the existing binary
length machine, instantiate the proved loop, identify its unary orbit and
finite search, then apply the checked exponent calculation. -/
private lemma f2_splitSolve_of_body (C e : ℕ) (body : FinTM Bool) (anchor : body.State)
    (A : ℕ)
    (hstart : ∀ w : List Bool, ∃ t ≤ A * (w.length + 1) ^ (e + 1),
      (∀ t' < t, (body.tm.runFrom (body.tm.initCfg w) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg w) t =
        Cfg.ofWords anchor (stateWord body.k []))
    (hround : ∀ (w s : List Bool), s.length ≤ w.length + 1 →
      ∃ t, 0 < t ∧ t ≤ A * (w.length + 1) ^ (e + 1) ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t').state
            ≠ some anchor) ∧
        if f2_splitAccept C e w s then
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).state = none ∧
          (body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t).output =
            pairEncode (w.take s.length) (w.drop s.length)
        else
          body.tm.runFrom (Cfg.ofWords (input := w) anchor (stateWord body.k s)) t =
            Cfg.ofWords anchor (stateWord body.k (f2_splitStep w s))) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  obtain ⟨F, a, hF, _⟩ := computesFunInTime_lengthBits_spaceUsed
  have hn (n : ℕ) : n + 1 ≤ (n + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ e + 1 by omega)
  have hbody (n : ℕ) : A * (n + 1) ^ (e + 1) ≤ (A + a) * (n + 1) ^ (e + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hF' : F.ComputesFunInTime (fun w => Nat.bits w.length)
      (fun n => (A + a) * (n + 1) ^ (e + 1)) := by
    intro w
    apply (hF w).mono
    exact (Nat.mul_le_mul_left a (hn w.length)).trans (Nat.mul_le_mul_right _ (by omega))
  obtain ⟨M, c, hM, hspace⟩ := f2_exists_loopFind_space body F anchor
    (fun w s => s.length ≤ w.length + 1) f2_splitStep (f2_splitAccept C e)
    (fun w s => pairEncode (w.take s.length) (w.drop s.length)) (fun _ => [])
    id (fun n => (A + a) * (n + 1) ^ (e + 1)) hF'
    (by intro w; simp) f2_splitStep_inv
    (by
      intro w
      obtain ⟨t, ht, hi, hh⟩ := hstart w
      exact ⟨t, ht.trans (hbody w.length), hi, hh⟩)
    (by
      intro w s hs
      obtain ⟨t, htpos, ht, hi, hh⟩ := hround w s hs
      exact ⟨t, htpos, ht.trans (hbody w.length), hi, hh⟩)
  refine ⟨M, 2 * c * (A + a + 1), ?_, ?_⟩
  · intro w
    have hm := hM w
    dsimp only [id_eq] at hm
    convert hm.mono (f2_splitLoop_bound c (A + a) e w.length) using 1
    exact (f2_splitLoop_result C e w).symm

  · intro x t
    have h := hspace x t
    have hp : 1 ≤ (x.length + 1) ^ (e + 1) := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have hb : (A + a) * (x.length + 1) ^ (e + 1) + 1 ≤
        (A + a + 1) * (x.length + 1) ^ (e + 1) := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    calc
      _ ≤ c * ((A + a + 1) * (x.length + 1) ^ (e + 1)) :=
        h.trans (Nat.mul_le_mul_left c hb)
      _ = (c * (A + a + 1)) * (x.length + 1) ^ (e + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _
        (Nat.mul_le_mul_right _ (by omega : c ≤ 2 * c))

/-- The positive-exponent source is the already proved nested-loop phase,
started on the prepared bank rather than rerunning input initialization. -/
private lemma f2_splitSource_poly (c C : ℕ) (s : List Bool) :
    (f2_catalogPolyUnaryTM c C).tm.runFrom
      (f2_splitBank (f2_catalogPolyUnaryTM c C) s (some (.loop (Fin.last c))) [])
      (f2_catalogPolyCost (s.length + 1) C (c + 1) + 1) =
      f2_splitBank (f2_catalogPolyUnaryTM c C) s none
        (List.replicate (C * (s.length + 1) ^ (c + 1)) true) := by
  simpa [f2_splitBank, f2_catalogPolyCfg] using f2_splitPoly_loop_end c C (s.length + 1) (by omega)

/-- Exponent zero uses the fixed prefix source on empty virtual input, with
no scratch tapes. Its last blank-reading step is included in the bound. -/
private lemma f2_splitSource_constant (C : ℕ) (s : List Bool) :
    (f2_catalogPrefixTM (List.replicate C true)).tm.runFrom
      (f2_splitBank (f2_catalogPrefixTM (List.replicate C true)) s (some (0 : Fin ((List.replicate C true).length + 1))) []) (C + 1) =
      f2_splitBank (f2_catalogPrefixTM (List.replicate C true)) s none (List.replicate C true) := by
  have hi : f2_splitBank (f2_catalogPrefixTM (List.replicate C true)) s (some (0 : Fin ((List.replicate C true).length + 1))) [] =
      (f2_catalogPrefixTM (List.replicate C true)).tm.initCfg [] := by
    apply Cfg.ext_zero_tapes <;> rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step']
  have he := f2_catalogPrefixTM_emit (List.replicate C true) [] C (by simp)
  rw [he]
  simp only [List.take_replicate, Nat.min_self]
  apply Cfg.ext_zero_tapes <;>
    simp [MultiTapeTM.step, f2_catalogPrefixTM, f2_catalogPrefixCfg, Cfg.inputSymbol,
      Fin.ext_iff, Action.apply, f2_splitBank]

/-- The invariant bounds every candidate, including the one-past-end stall,
inside one common body envelope. The factor `2^e` covers the prepared side
length `|s|+1 ≤ 2(|w|+1)` without increasing the exponent.
**Proof sketch.** Bound the source by its proved box cost, compare the two
side lengths, and absorb all linear controller overhead into forty copies of
the positive polynomial envelope. -/
private lemma f2_splitBody_envelope (C e l n T : ℕ) (hl : l ≤ n + 1)
    (hT : T ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    T + 5 * l + 3 * n + 20 ≤
      ((C + 1 + 5 * e) * 2 ^ e + 40) * (n + 1) ^ (e + 1) := by
  have hp : (l + 1) ^ e ≤ 2 ^ e * (n + 1) ^ (e + 1) := by
    calc
      (l + 1) ^ e ≤ (2 * (n + 1)) ^ e := Nat.pow_le_pow_left (by omega) e
      _ = 2 ^ e * (n + 1) ^ e := Nat.mul_pow _ _ _
      _ ≤ 2 ^ e * (n + 1) ^ (e + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hmul := Nat.mul_le_mul_left (C + 1 + 5 * e) hp
  have hn : n + 1 ≤ (n + 1) ^ (e + 1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (Nat.succ_pos n)
      (show 1 ≤ e + 1 by omega)
  have hlin : 5 * l + 3 * n + 21 ≤ 40 * (n + 1) ^ (e + 1) := by omega
  calc
    T + 5 * l + 3 * n + 20 ≤
        (C + 1 + 5 * e) * (2 ^ e * (n + 1) ^ (e + 1)) +
          40 * (n + 1) ^ (e + 1) := by omega
    _ = _ := by ring

/-- Instantiate the completed controller with an exact unary-output source.
The source assumption is discharged below separately for zero and positive
exponents; startup and the full body round have already been constructed.
**Proof sketch.** Supply the exact zero-time startup and constructed round to
the existing loop closure. The common envelope bounds the actual phase times,
and the source's unary-output length identifies the checked acceptance test. -/
private lemma f2_splitSolve_source (C e : ℕ) (M : FinTM Bool) (start : M.State)
    (B : ℕ → ℕ)
    (hsource : ∀ s : List Bool, M.tm.runFrom (f2_splitBank M s (some start) []) (B s.length) =
      f2_splitBank M s none (List.replicate (C * (s.length + 1) ^ e) true))
    (hbound : ∀ l, B l ≤ (C + 1 + 5 * e) * (l + 1) ^ e + 1) :
    ∃ (N : FinTM Bool) (c : ℕ),
      N.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => []) (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ x t, N.tm.spaceUsed (N.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  apply f2_splitSolve_of_body C e (f2_splitBodyTM M start) .anchor
    ((C + 1 + 5 * e) * 2 ^ e + 40)
  · intro w
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · intro j hj; omega
    · exact f2_splitBody_start M start w
  · intro w s hs
    obtain ⟨t, htpos, ht, hsafe, hend⟩ := f2_splitBody_round M start w s
      (List.replicate (C * (s.length + 1) ^ e) true) (B s.length) (hsource s)
    refine ⟨t, htpos, ht.trans (f2_splitBody_envelope C e s.length w.length (B s.length)
      hs (hbound s.length)), hsafe, ?_⟩
    simpa only [f2_splitAccept, List.length_replicate] using hend

/-- Close the two exponent cases privately, so compiler-generated proof
helpers also remain private. Both cases instantiate the concrete body and
its proved round contract through the exact source interfaces. -/
private lemma f2_splitSolve_closed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  cases e with
  | zero =>
    apply f2_splitSolve_source C 0 (f2_catalogPrefixTM (List.replicate C true))
      (0 : Fin ((List.replicate C true).length + 1)) (fun _ => C + 1)
    · intro s
      simpa using f2_splitSource_constant C s
    · intro l; simp
  | succ e =>
    apply f2_splitSolve_source C (e + 1) (f2_catalogPolyUnaryTM e C) (.loop (Fin.last e))
      (fun l => f2_catalogPolyCost (l + 1) C (e + 1) + 1)
    · exact f2_splitSource_poly e C
    · intro l
      exact Nat.add_le_add_right (f2_catalogPolyCost_le (l + 1) C (by omega) (e + 1)) 1

/-- **P15 space row, split search** (spec, fill pending — design §12 R3;
annotates `Turing.FinTM.computesFunInTime_splitSolve`). The padding
split search runs in space one polynomial degree below its time: per
candidate it rebuilds unary banks of size at most `C·(n+1)^e` in place,
and candidates reuse the same banks.

**Proof sketch.** Head-movement count of the loop body's phases: the
candidate banks and the generator's output bank are rebuilt in place
every round (the round seam restores heads to the origin), so the
per-tape visited sets are intervals of length at most the largest bank,
`C·(n+1)^e` cells plus linear administration; the round count multiplies
time, not space. -/
theorem computesFunInTime_splitSolve_spaceUsed (C e : ℕ) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime
        (fun w => match solveSplit C e w.length with
          | some i => pairEncode (w.take i) (w.drop i)
          | none => [])
        (fun n => c * (n + 1) ^ (e + 2)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
  exact f2_splitSolve_closed C e

/- Local copies of the W2 correspondence from Build/Wrappers.lean.
The originals are private; the all-time trajectory is needed for the space row. -/
/-- Map a source state and its last-emission register to simulation, halt,
or the stationary live loop. An empty register never matches a bit. -/
private def catalog_redirectState {S : Type} (haltOn : Bool) (q : Option S)
    (r : Option Bool) : Option ((S × Option Bool) ⊕ Unit) :=
  match q with
  | some s => some (.inl (s, r))
  | none => if r = some haltOn then none else some (.inr ())

/-- Suppress physical emission, updating the register before the halt test. -/
private def catalog_redirectAction {k : ℕ} {S : Type} (haltOn : Bool)
    (a : Action k Bool S) (r : Option Bool) : Action k Bool ((S × Option Bool) ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, none, catalog_redirectState haltOn a.state (a.output.or r)⟩

/-- The source tapes and input head are unchanged; its last emitted bit is
remembered in control and the physical output is empty. -/
private def catalog_redirectCfg (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : Cfg (redirectTM M haltOn).k Bool
      (redirectTM M haltOn).State x :=
  ⟨catalog_redirectState haltOn c.state c.output.getLast?, c.inputPos,
    c.workTapes, c.workTapePos, []⟩

/-- The stationary live loop is fixed by every subsequent transition. -/
private lemma catalog_redirect_loop (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg (redirectTM M haltOn).k Bool (redirectTM M haltOn).State x)
    (hs : c.state = some (.inr ())) (t : ℕ) :
    (redirectTM M haltOn).tm.runFrom c t = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    apply Cfg.ext <;> simp [MultiTapeTM.step, hs, redirectTM, Action.apply]

/-- Capture and application commute because the last entry of an appended
singleton is the new bit, while no emission leaves the old register intact. -/
private lemma catalog_redirect_apply (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (a : Action M.k Bool M.State) :
    (catalog_redirectAction haltOn a c.output.getLast?).apply (catalog_redirectCfg M haltOn c) =
      catalog_redirectCfg M haltOn (a.apply c) := by
  have hlast : (c.output ++ a.output.toList).getLast? = a.output.or c.output.getLast? := by
    cases a.output <;> simp
  refine Cfg.ext ?_ rfl rfl rfl rfl
  dsimp only [catalog_redirectCfg, catalog_redirectAction, Action.apply]
  rw [hlast]

/-- The correspondence also holds after a source halt: a matching result
is absorbed as halted, and a mismatching result is absorbed in the live loop.
This adapts `acceptCfg_step` in the HALT reduction to an optional register. -/
private lemma catalog_redirect_step (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    (redirectTM M haltOn).tm.step (catalog_redirectCfg M haltOn c) =
      catalog_redirectCfg M haltOn (M.tm.step c) := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs]
    by_cases hr : c.output.getLast? = some haltOn
    · exact MultiTapeTM.step_of_halt (by simp [catalog_redirectCfg, catalog_redirectState, hs, hr])
    · exact catalog_redirect_loop M haltOn (catalog_redirectCfg M haltOn c)
        (by simp [catalog_redirectCfg, catalog_redirectState, hs, hr]) 1
  | some q =>
    have hi : (catalog_redirectCfg M haltOn c).inputSymbol = c.inputSymbol := rfl
    have hw : (catalog_redirectCfg M haltOn c).workTapeSymbols = c.workTapeSymbols := rfl
    have hstate : (catalog_redirectCfg M haltOn c).state = some (.inl (q, c.output.getLast?)) := by
      simp only [catalog_redirectCfg, catalog_redirectState, hs]
    simp only [MultiTapeTM.step, hstate, hs]
    rw [hi, hw]
    have htr : (redirectTM M haltOn).tm.tr (.inl (q, c.output.getLast?))
        c.inputSymbol c.workTapeSymbols =
        catalog_redirectAction haltOn (M.tm.tr q c.inputSymbol c.workTapeSymbols) c.output.getLast? := by
      cases hq : (M.tm.tr q c.inputSymbol c.workTapeSymbols).state <;>
        cases ho : (M.tm.tr q c.inputSymbol c.workTapeSymbols).output <;>
          simp [redirectTM, catalog_redirectAction, catalog_redirectState, hq, ho]
    rw [htr]
    exact catalog_redirect_apply M haltOn c _

/-- Initialized runs commute with redirection at every time, including
after a source halt. This is the last-emission invariant for both clauses. -/
private lemma catalog_redirect_run (M : FinTM Bool) (haltOn : Bool) (x : List Bool) (t : ℕ) :
    (redirectTM M haltOn).tm.runFrom ((redirectTM M haltOn).tm.initCfg x) t =
      catalog_redirectCfg M haltOn (M.tm.runFrom (M.tm.initCfg x) t) := by
  have hi : (redirectTM M haltOn).tm.initCfg x = catalog_redirectCfg M haltOn (M.tm.initCfg x) := rfl
  rw [hi]
  exact MultiTapeTM.runFrom_comm_of_step (catalog_redirectCfg M haltOn) (catalog_redirect_step M haltOn)
    (M.tm.initCfg x) t


/-- **W2 space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.redirectTM` beside its
`redirectTM_computes`/`redirectTM_live` contract pair). Redirection costs
no space, per tape and exactly: the redirected machine's tape actions are
the source's verbatim, before and after the source halt.

**Proof sketch.** `redirect_run`'s configuration correspondence preserves
work tapes and heads at every time (the live loop is stationary and the
simulation phase copies the source's tape actions), so the two head
trajectories coincide pointwise and the visited images agree. -/
theorem redirectTM_spaceUsedByTape (M : FinTM Bool) (haltOn : Bool)
    (x : List Bool) (t : ℕ) (i : Fin M.k) :
    (redirectTM M haltOn).tm.spaceUsedByTape
        ((redirectTM M haltOn).tm.initCfg x) t i
      = M.tm.spaceUsedByTape (M.tm.initCfg x) t i := by
  unfold MultiTapeTM.spaceUsedByTape MultiTapeTM.visitedByTapeHead
  congr 1
  apply Finset.image_congr
  intro u _
  dsimp only
  rw [catalog_redirect_run]
  rfl

/-- Pad the decider with the fresh branch tapes. The added tapes are idle,
so the public left-block simulation supplies its complete run invariant. -/
private def f2_timedPadTM (D : FinTM Bool) (r : ℕ) : MultiTapeTM (D.k + r) Bool D.State where
  q₀ := D.tm.q₀
  tr q inp work := leftAction r id (D.tm.tr q inp (fun i => work (Fin.castAdd r i)))

/-- The conditional controller captures the decider on the last tape,
steps back to read its singleton verdict, rewinds the physical input, then
runs the selected branch on its untouched tape bank. In the administrative
states, the first Boolean distinguishes back/read and the second distinguishes
rewind-start/scan. The branch transition table is independent of its selector. -/
private def f2_timedCondTM (D M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := (D.k + (M₁.k + M₂.k)) + 1
  State := D.State ⊕ (Bool ⊕ ((Bool × Bool) ⊕ (M₁.State ⊕ M₂.State)))
  tm :=
    { q₀ := .inl D.tm.q₀
      tr := fun q inp work => match q with
        | .inl q => captureAction Sum.inl (.inr (.inl false))
            ((f2_timedPadTM D (M₁.k + M₂.k)).tr q inp (fun i => work i.castSucc))
        | .inr (.inl false) =>
          ⟨0, (fun i => if (i : ℕ) < D.k + (M₁.k + M₂.k) then (none, 0)
            else (none, .neg)), none, some (.inr (.inl true))⟩
        | .inr (.inl true) => controlAction 0
            (some (.inr (.inr (.inl ((work (Fin.last _)).getD false, false)))))
        | .inr (.inr (.inl (b, false))) =>
            controlAction .neg (some (.inr (.inr (.inl (b, true)))))
        | .inr (.inr (.inl (b, true))) => match inp with
          | some _ => controlAction .neg (some (.inr (.inr (.inl (b, true)))))
          | none => controlAction .pos
              (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
        | .inr (.inr (.inr q)) => leftAction 1 id
            (rightAction D.k (fun s => .inr (.inr (.inr s)))
              ((branchTM M₁ M₂ false).tm.tr q inp
                (fun i => work (Fin.natAdd D.k i).castSucc))) }

/-- The branch configuration retains the decider's finished work and the
captured verdict; its own state, input head, work tapes, and output are exact. -/
private def f2_timedBranchCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) :
    Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x :=
  leftCfg id (rightCfg (fun s => .inr (.inr (.inr s))) c tapes heads)
    (fun (_ : Fin 1) => bufferTape [b]) (fun _ => 0)

/-- The decider's configuration inside its padded, captured simulation.
Both branch tape banks are blank throughout this phase. -/
private def f2_timedControlCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) :
    Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x :=
  captureCfg Sum.inl (.inr (.inl false)) [] []
    (leftCfg id c (fun (_ : Fin (M₁.k + M₂.k)) _ => none) (fun _ => 0))

/-- The capture contract, instantiated on the padded decider, gives the
entire controller phase through its first halt. -/
private lemma f2_timed_capture (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (t : ℕ)
    (hlive : ∀ s < t, ¬(D.tm.runFrom c s).Halted) :
    (f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedControlCfg D M₁ M₂ c) t =
      f2_timedControlCfg D M₁ M₂ (D.tm.runFrom c t) := by
  have hpad (u : ℕ) := leftCfg_run D.tm (f2_timedPadTM D (M₁.k + M₂.k)) id
    (fun _ _ _ => rfl) c (fun _ _ => none) (fun _ => 0) u
  have h := capture_run (f2_timedPadTM D (M₁.k + M₂.k)) (f2_timedCondTM D M₁ M₂).tm
    Sum.inl (.inr (.inl false)) (fun _ _ _ => rfl) [] []
    (leftCfg id c (fun _ _ => none) (fun _ => 0)) t (fun s hs => by
      unfold Cfg.Halted
      rw [hpad s]
      simpa only [leftCfg, Option.map_id] using hlive s hs)
  simpa only [hpad t] using h

/-- The host's genuine initial configuration is the captured, padded
initial configuration: all three work-tape blocks are blank. -/
private lemma f2_timed_control_init (D M₁ M₂ : FinTM Bool) (x : List Bool) :
    (f2_timedCondTM D M₁ M₂).tm.initCfg x =
      f2_timedControlCfg D M₁ M₂ (D.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : (i : ℕ) < D.k + (M₁.k + M₂.k)
    · simp only [f2_timedControlCfg, captureCfg, leftCfg, MultiTapeTM.initCfg,
        Cfg.init, dif_pos hi]
      exact (Fin.addCases (fun _ => by simp) (fun _ => by simp) ⟨i, hi⟩)
    · simp [f2_timedControlCfg, captureCfg, leftCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) < D.k + (M₁.k + M₂.k)
    · simp only [f2_timedControlCfg, captureCfg, leftCfg, MultiTapeTM.initCfg,
        Cfg.init, dif_pos hi]
      exact (Fin.addCases (fun _ => by simp) (fun _ => by simp) ⟨i, hi⟩)
    · simp [f2_timedControlCfg, captureCfg, leftCfg, hi]

/-- Once dispatched, the selected branch runs in lockstep while the old
decider tapes and singleton capture tape remain idle.
**Proof sketch.** The branch action is a right-block embedding followed by
a left-block embedding; compose their application lemmas, then iterate. -/
private lemma f2_timed_branch_run (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) (t : ℕ) :
    (f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedBranchCfg D M₁ M₂ c tapes heads b) t =
      f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.runFrom c t) tapes heads b := by
  apply MultiTapeTM.runFrom_comm_of_step (fun c => f2_timedBranchCfg D M₁ M₂ c tapes heads b)
  intro d
  cases hs : d.state with
  | none =>
    simp only [MultiTapeTM.step, f2_timedBranchCfg, leftCfg, rightCfg, hs, Option.map_none]
  | some q =>
    have hstate : (f2_timedBranchCfg D M₁ M₂ d tapes heads b).state =
        some (.inr (.inr (.inr q))) := by
      simp only [f2_timedBranchCfg, leftCfg, rightCfg, hs, Option.map_some, id_eq]
    have hi : (f2_timedBranchCfg D M₁ M₂ d tapes heads b).inputSymbol = d.inputSymbol := rfl
    have hw : (fun i => (f2_timedBranchCfg D M₁ M₂ d tapes heads b).workTapeSymbols
        (Fin.natAdd D.k i).castSucc) = d.workTapeSymbols := by
      funext i
      simp only [f2_timedBranchCfg, leftCfg, rightCfg, Cfg.workTapeSymbols,
        Fin.castSucc, Fin.addCases_left, Fin.addCases_right]
    simp only [MultiTapeTM.step, hstate, hs]
    dsimp only [f2_timedCondTM]
    let emb : (M₁.State ⊕ M₂.State) → (f2_timedCondTM D M₁ M₂).State :=
      fun s => .inr (.inr (.inr s))
    change (leftAction 1 id (rightAction D.k emb
      ((branchTM M₁ M₂ b).tm.tr q d.inputSymbol
        (fun i => (f2_timedBranchCfg D M₁ M₂ d tapes heads b).workTapeSymbols
          (Fin.natAdd D.k i).castSucc)))).apply
        (leftCfg id (rightCfg emb d tapes heads)
          (fun (_ : Fin 1) => bufferTape [b]) (fun _ => 0)) = _
    erw [hw, leftCfg_apply, rightCfg_apply]
    rfl

/-- After reading the verdict, all branch data are initialized; only the
input head still needs rewinding. The capture head is back at cell zero. -/
private def f2_timedReadyCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) :
    Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x :=
  { f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) c.workTapes c.workTapePos b with
    state := some (.inr (.inr (.inl (b, false))))
    inputPos := c.inputPos }

/-- Two silent transitions move the capture head left and read the completed
singleton verdict, without touching the input or either work bank.
**Proof sketch.** The final capture head is one past the singleton, hence at
one. Moving it left exposes exactly its bit at zero; the next transition
records that bit in the rewind state. -/
private lemma f2_timed_read (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) (hs : c.state = none) (ho : c.output = [b]) :
    (f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedControlCfg D M₁ M₂ c) 2 =
      f2_timedReadyCfg D M₁ M₂ c b := by
  let ready := f2_timedReadyCfg D M₁ M₂ c b
  have hback : (f2_timedCondTM D M₁ M₂).tm.step (f2_timedControlCfg D M₁ M₂ c) =
      {ready with state := some (.inr (.inl true))} := by
    have hstate : (f2_timedControlCfg D M₁ M₂ c).state = some (.inr (.inl false)) := by
      simp [f2_timedControlCfg, captureCfg, leftCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, j.isLt]
        refine Fin.addCases ?_ ?_ j <;> intro z <;> simp
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, ho]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, j.isLt]
        refine Fin.addCases ?_ ?_ j <;> intro z <;> simp
      · intro j
        simp [f2_timedCondTM, Action.apply, f2_timedControlCfg, captureCfg, leftCfg,
          f2_timedReadyCfg, f2_timedBranchCfg, rightCfg, ready, ho]
  have hread : (f2_timedCondTM D M₁ M₂).tm.step
      {ready with state := some (.inr (.inl true))} = ready := by
    have hsym : ({ready with state := some (.inr (.inl true))} :
        Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x).workTapeSymbols
        (Fin.last _) = some b := by
      change (f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x)
        c.workTapes c.workTapePos b).workTapeSymbols
          (Fin.natAdd (D.k + (M₁.k + M₂.k)) (0 : Fin 1)) = some b
      simp [f2_timedBranchCfg, leftCfg, rightCfg, Cfg.workTapeSymbols, bufferTape]
    unfold MultiTapeTM.step
    dsimp only
    change ((controlAction 0 (some (.inr (.inr (.inl
      ((({ready with state := some (.inr (.inl true))} :
        Cfg (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State x).workTapeSymbols
        (Fin.last _)).getD false, false)))))) :
          Action (f2_timedCondTM D M₁ M₂).k Bool (f2_timedCondTM D M₁ M₂).State).apply _ = _
    rw [hsym, controlAction_apply]
    simp only [Option.getD_some, moveInputPos_zero]
    rfl
  change (f2_timedCondTM D M₁ M₂).tm.step
    ((f2_timedCondTM D M₁ M₂).tm.step (f2_timedControlCfg D M₁ M₂ c)) = _
  rw [hback, hread]

/-- A singleton-output decider reaches the selected branch's genuine
initial configuration in at most twice its budget plus five steps.
**Proof sketch.** Choose the first source halt, which is within the supplied
budget. Capture until that halt, read the singleton in two steps, and rewind
in at most the current input position plus two. The head-position bound
charges this rewind to the decider's elapsed steps, not the input length. -/
private lemma f2_timed_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    ∃ a ≤ 2 * T + 5, ∃ (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) a =
        f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads b := by
  classical
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hD).1⟩
  let t := Nat.find hh
  let c := D.tm.runFrom (D.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hD).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = [b] := hc.output_unique hD
  have hcap : (f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) t =
      f2_timedControlCfg D M₁ M₂ c := by
    rw [f2_timed_control_init]
    exact f2_timed_capture D M₁ M₂ _ t (fun s hst => Nat.find_min hh hst)
  obtain ⟨r, hrle, hr⟩ := timed_rewind (f2_timedCondTM D M₁ M₂).tm
    (.inr (.inr (.inl (b, false)))) (.inr (.inr (.inl (b, true))))
    (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (f2_timedReadyCfg D M₁ M₂ c b) rfl
  refine ⟨t + 2 + r, ?_, c.workTapes, c.workTapePos, ?_⟩
  · have hp : c.inputPos.val ≤ 1 + t := by
      simpa only [MultiTapeTM.initCfg, Cfg.init, Fin.val_one] using
        MultiTapeTM.timed_input_bound (tm := D.tm) (D.tm.initCfg x) t
    change r ≤ c.inputPos.val + 2 at hrle
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap,
      f2_timed_read D M₁ M₂ c b hs ho, hr]
    rfl

private lemma f2_cond_time {D M₁ M₂ : FinTM Bool} {p : List Bool → Bool}
    {f₁ f₂ : List Bool → List Bool} {T₀ T₁ T₂ : ℕ → ℕ}
    (hD : D.ComputesFunInTime (fun x => [p x]) T₀)
    (h₁ : M₁.ComputesFunInTime f₁ T₁) (h₂ : M₂.ComputesFunInTime f₂ T₂) :
    (f2_timedCondTM D M₁ M₂).ComputesFunInTime
      (fun x => if p x then f₁ x else f₂ x)
      (fun n => 5 * (T₀ n + max (T₁ n) (T₂ n) + 1)) := by
  intro x
  let B := max (T₁ x.length) (T₂ x.length)
  have hb : (branchTM M₁ M₂ (p x)).ComputesInTime x
      (if p x then f₁ x else f₂ x) B := by
    apply (branchTM_computes M₁ M₂ (p x) x _ B).mpr
    cases hp : p x with
    | false => exact (h₂ x).mono (Nat.le_max_right _ _)
    | true => exact (h₁ x).mono (Nat.le_max_left _ _)
  obtain ⟨a, ha, tapes, heads, hstart⟩ :=
    f2_timed_start D M₁ M₂ x (p x) (T₀ x.length) (hD x)
  have hc : (f2_timedCondTM D M₁ M₂).ComputesInTime x
      (if p x then f₁ x else f₂ x) (a + B) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, f2_timed_branch_run]
    obtain ⟨hs, ho⟩ := (computesInTime_iff _ _ _ _).mp hb
    exact ⟨by simpa only [f2_timedBranchCfg, leftCfg, rightCfg, Option.map_eq_none_iff] using hs, ho⟩
  -- The controller prefix and selected branch fit one uniform coefficient.
  apply hc.mono
  dsimp only [B] at *
  omega

/-- A native input rewind keeps every work head fixed at every prefix,
including its dispatch step. -/
private lemma f2_rewind_scan_heads {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (scan : S) (dest : Option S)
    (htr : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest) :
    ∀ (j : ℕ) (cfg : Cfg k Bool S x), cfg.state = some scan →
      cfg.inputPos.val = j → j ≤ x.length →
      ∀ u ≤ j + 1, (tm.runFrom cfg u).workTapePos = cfg.workTapePos := by
  intro j
  induction j with
  | zero =>
    intro cfg hs hj hp u hu
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with rfl | rfl
    · rfl
    · have hz : cfg.inputPos = 0 := Fin.ext hj
      have hi : cfg.inputSymbol = none := by simp [Cfg.inputSymbol, hz]
      change (tm.step cfg).workTapePos = _
      simp only [MultiTapeTM.step, hs, htr, hi, controlAction_apply]
  | succ j ih =>
    intro cfg hs hj hp u hu
    cases u with
    | zero => rfl
    | succ u =>
      have hi : cfg.inputSymbol = some (x[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      have he : tm.step cfg =
          {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
        simp only [MultiTapeTM.step, hs, htr, hi, controlAction_apply]
      rw [MultiTapeTM.runFrom_succ_eq_step, he]
      apply ih _ rfl _ (by omega) u (by omega)
      simp only [moveInputPos_neg_val]
      omega

/-- The bounded rewind with the prefix work-head equality retained. -/
private lemma f2_rewind_heads {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work = match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (c : Cfg k Bool S x) (hs : c.state = some start) :
    ∃ r ≤ c.inputPos.val + 2,
      tm.runFrom c r = {c with state := dest, inputPos := 1} ∧
      ∀ u ≤ r, (tm.runFrom c u).workTapePos = c.workTapePos := by
  have hstep : tm.step c =
      {c with state := some scan, inputPos := moveInputPos c.inputPos .neg} := by
    simp only [MultiTapeTM.step, hs, hstart, controlAction_apply]
  have hp : (moveInputPos c.inputPos .neg).val ≤ x.length := by
    rw [moveInputPos_neg_val]
    have := c.inputPos.isLt
    omega
  refine ⟨1 + ((moveInputPos c.inputPos .neg).val + 1), ?_, ?_, ?_⟩
  · rw [moveInputPos_neg_val]; omega
  · rw [MultiTapeTM.runFrom_add]
    change tm.runFrom (tm.step c) _ = _
    rw [hstep, rewind_scan tm scan dest hscan _ rfl hp]
  · intro u hu
    cases u with
    | zero => rfl
    | succ u =>
      rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact f2_rewind_scan_heads tm scan dest hscan (moveInputPos c.inputPos .neg).val _ rfl rfl hp u (by omega)

/-- Explicit equivalence between a disjoint pair of banks and their concatenation. -/
private def f2_finSumEquiv (a b : ℕ) : Fin a ⊕ Fin b ≃ Fin (a + b) where
  toFun := Sum.elim (Fin.castAdd b) (Fin.natAdd a)
  invFun := fun i => if h : (i : ℕ) < a then Sum.inl ⟨i, h⟩
    else Sum.inr ⟨i - a, by have := i.isLt; omega⟩
  left_inv := by
    intro i
    cases i with
    | inl i => simp [i.isLt]
    | inr i =>
      simp only [Sum.elim_inr, Fin.coe_natAdd, not_lt.mpr (Nat.le_add_right _ _), ↓reduceDIte]
      congr 1
      apply Fin.ext
      simp
  right_inv := by
    intro i
    dsimp only
    split
    · rfl
    · apply Fin.ext
      dsimp only [Sum.elim_inr, Fin.coe_natAdd]
      omega

/-- Sum a finite tape bank by its two disjoint blocks. -/
private lemma f2_sum_add {a b : ℕ} (f : Fin (a + b) → ℕ) :
    (∑ i : Fin (a + b), f i) =
      (∑ i : Fin a, f (Fin.castAdd b i)) + ∑ i : Fin b, f (Fin.natAdd a i) := by
  rw [Fintype.sum_equiv (f2_finSumEquiv a b).symm f (fun i => f ((f2_finSumEquiv a b).toFun i))]
  · exact Finset.sum_disjSum Finset.univ Finset.univ _
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]

/-- Disjoint branch banks give exact selected-space plus idle origins. -/
private lemma f2_branch_space (M₁ M₂ : FinTM Bool) (b : Bool) (x : List Bool) (t : ℕ) :
    (branchTM M₁ M₂ b).tm.spaceUsed ((branchTM M₁ M₂ b).tm.initCfg x) t =
      if b then M₁.tm.spaceUsed (M₁.tm.initCfg x) t + M₂.k
      else M₂.tm.spaceUsed (M₂.tm.initCfg x) t + M₁.k := by
  cases b with
  | false =>
    have hi : (branchTM M₁ M₂ false).tm.initCfg x =
        rightCfg Sum.inr (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
    have hr (u : ℕ) := rightCfg_run M₂.tm (branchTM M₁ M₂ false).tm Sum.inr
      (fun _ _ _ => rfl) (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) u
    simp only [Bool.false_eq_true, ↓reduceIte, MultiTapeTM.spaceUsed]
    change (∑ i : Fin (M₁.k + M₂.k),
      (branchTM M₁ M₂ false).tm.spaceUsedByTape ((branchTM M₁ M₂ false).tm.initCfg x) t i) = _
    rw [f2_sum_add (a := M₁.k) (b := M₂.k)]
    simp only [MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead]
    simp only [hi]
    simp only [hr]
    simp only [rightCfg, Fin.addCases_left, Fin.addCases_right]
    simp [Finset.image_const Finset.nonempty_range_add_one, Nat.add_comm]
  | true =>
    have hi : (branchTM M₁ M₂ true).tm.initCfg x =
        leftCfg Sum.inl (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
      · funext i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
    have hr (u : ℕ) := leftCfg_run M₁.tm (branchTM M₁ M₂ true).tm Sum.inl
      (fun _ _ _ => rfl) (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) u
    simp only [↓reduceIte, MultiTapeTM.spaceUsed]
    change (∑ i : Fin (M₁.k + M₂.k),
      (branchTM M₁ M₂ true).tm.spaceUsedByTape ((branchTM M₁ M₂ true).tm.initCfg x) t i) = _
    rw [f2_sum_add (a := M₁.k) (b := M₂.k)]
    simp only [MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead]
    simp only [hi]
    simp only [hr]
    simp only [leftCfg, Fin.addCases_left, Fin.addCases_right]
    simp [Finset.image_const Finset.nonempty_range_add_one]

/-- Head layout of the timed controller, with one scalar capture position. -/
private def f2_condHeads (D M₁ M₂ : FinTM Bool) (d : Fin D.k → ℤ)
    (b : Fin (M₁.k + M₂.k) → ℤ) (z : ℤ) :
    Fin ((D.k + (M₁.k + M₂.k)) + 1) → ℤ :=
  Fin.addCases (Fin.addCases d b) (fun _ => z)

/-- The captured decider has its source positions, idle branches, and a
capture head at its output length. -/
private lemma f2_control_heads (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) :
    (f2_timedControlCfg D M₁ M₂ c).workTapePos =
      f2_condHeads D M₁ M₂ c.workTapePos (fun _ => 0) c.output.length := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [f2_timedControlCfg, captureCfg, leftCfg, f2_condHeads, j.isLt]
  · simp [f2_timedControlCfg, captureCfg, leftCfg, f2_condHeads]

/-- A dispatched branch keeps the completed decider's heads and the
capture head fixed while simulating precisely its selected bank. -/
private lemma f2_branch_heads (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) :
    (f2_timedBranchCfg D M₁ M₂ c tapes heads b).workTapePos =
      f2_condHeads D M₁ M₂ heads c.workTapePos 0 := rfl

/-- The mandatory back/read pair preserves both machine banks and moves
only the singleton capture head from one to zero. -/
private lemma f2_read_heads (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) (hs : c.state = none) (ho : c.output = [b]) :
    ∀ u ≤ 2, ∃ z : ℤ, 0 ≤ z ∧ z ≤ 1 ∧
      ((f2_timedCondTM D M₁ M₂).tm.runFrom (f2_timedControlCfg D M₁ M₂ c) u).workTapePos =
        f2_condHeads D M₁ M₂ c.workTapePos (fun _ => 0) z := by
  intro u hu
  have hu : u = 0 ∨ u = 1 ∨ u = 2 := by omega
  rcases hu with rfl | rfl | rfl
  · refine ⟨1, by omega, by omega, ?_⟩
    simpa [ho] using f2_control_heads D M₁ M₂ c
  · refine ⟨0, by omega, by omega, ?_⟩
    have hstate : (f2_timedControlCfg D M₁ M₂ c).state = some (.inr (.inl false)) := by
      simp [f2_timedControlCfg, captureCfg, leftCfg, hs]
    change ((f2_timedCondTM D M₁ M₂).tm.step (f2_timedControlCfg D M₁ M₂ c)).workTapePos = _
    simp only [MultiTapeTM.step, hstate]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [f2_timedCondTM, Action.apply, f2_control_heads, f2_condHeads, j.isLt]
    · simp [f2_timedCondTM, Action.apply, f2_control_heads, f2_condHeads, ho]
  · refine ⟨0, by omega, by omega, ?_⟩
    rw [f2_timed_read D M₁ M₂ c b hs ho]
    rfl

/-- The whole timed conditional has two unchanged source trajectories:
a decider prefix, then a branch prefix. The administrative stages repeat
endpoints; only the capture head has positions zero or one. -/
private lemma f2_cond_ledger (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    ∀ u, ∃ v ≤ T, ∃ w ≤ u, ∃ z : ℤ, 0 ≤ z ∧ z ≤ 1 ∧
      ((f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) u).workTapePos =
        f2_condHeads D M₁ M₂ (D.tm.runFrom (D.tm.initCfg x) v).workTapePos
          ((branchTM M₁ M₂ b).tm.runFrom ((branchTM M₁ M₂ b).tm.initCfg x) w).workTapePos z := by
  classical
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hD).1⟩
  let d := Nat.find hh
  let c := D.tm.runFrom (D.tm.initCfg x) d
  have hd : d ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hD).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x c.output d := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = [b] := hc.output_unique hD
  have hcap (u : ℕ) (hu : u ≤ d) :
      (f2_timedCondTM D M₁ M₂).tm.runFrom ((f2_timedCondTM D M₁ M₂).tm.initCfg x) u =
        f2_timedControlCfg D M₁ M₂ (D.tm.runFrom (D.tm.initCfg x) u) := by
    rw [f2_timed_control_init]
    exact f2_timed_capture D M₁ M₂ _ u (fun s hsu => Nat.find_min hh (by omega))
  obtain ⟨r, hrle, hr, hrheads⟩ := f2_rewind_heads (f2_timedCondTM D M₁ M₂).tm
    (.inr (.inr (.inl (b, false)))) (.inr (.inr (.inl (b, true))))
    (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (f2_timedReadyCfg D M₁ M₂ c b) rfl
  have hstart : (f2_timedCondTM D M₁ M₂).tm.runFrom
      ((f2_timedCondTM D M₁ M₂).tm.initCfg x) (d + 2 + r) =
      f2_timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x)
        c.workTapes c.workTapePos b := by
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap d (le_refl _),
      f2_timed_read D M₁ M₂ c b hs ho, hr]
    rfl
  intro u
  by_cases hu : u ≤ d
  · refine ⟨u, hu.trans hd, 0, Nat.zero_le _,
      (D.tm.runFrom (D.tm.initCfg x) u).output.length, by omega, ?_, ?_⟩
    · have hp := (D.tm.output_prefix (D.tm.initCfg x) hu).length_le
      change (D.tm.runFrom (D.tm.initCfg x) u).output.length ≤ c.output.length at hp
      rw [ho] at hp
      simp only [List.length_singleton] at hp
      exact_mod_cast hp
    · rw [hcap u hu, f2_control_heads]
      rfl
  · refine ⟨d, hd, ?_⟩
    by_cases hread : u ≤ d + 2
    · obtain ⟨z, hz0, hz1, he⟩ := f2_read_heads D M₁ M₂ c b hs ho (u - d) (by omega)
      refine ⟨0, Nat.zero_le _, z, hz0, hz1, ?_⟩
      rw [show u = d + (u - d) by omega, MultiTapeTM.runFrom_add, hcap d (le_refl _)]
      exact he
    · by_cases hrew : u ≤ d + 2 + r
      · refine ⟨0, Nat.zero_le _, 0, by omega, by omega, ?_⟩
        rw [show u = d + 2 + (u - (d + 2)) by omega, MultiTapeTM.runFrom_add,
          MultiTapeTM.runFrom_add, hcap d (le_refl _), f2_timed_read D M₁ M₂ c b hs ho,
          hrheads _ (by omega)]
        rfl
      · refine ⟨u - (d + 2 + r), by omega, 0, by omega, by omega, ?_⟩
        rw [show u = d + 2 + r + (u - (d + 2 + r)) by omega,
          MultiTapeTM.runFrom_add, hstart, f2_timed_branch_run, f2_branch_heads]
        simp only [Nat.add_sub_cancel_left]
        rfl

/-- Cardinalities of the disjoint source banks, with the singleton verdict
occupying at most its two head positions. -/
private lemma f2_cond_space (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T t : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    (f2_timedCondTM D M₁ M₂).tm.spaceUsed ((f2_timedCondTM D M₁ M₂).tm.initCfg x) t ≤
      D.tm.spaceUsed (D.tm.initCfg x) T +
        (branchTM M₁ M₂ b).tm.spaceUsed ((branchTM M₁ M₂ b).tm.initCfg x) t + 2 := by
  let M := f2_timedCondTM D M₁ M₂
  let B := branchTM M₁ M₂ b
  have hDcard (i : Fin D.k) :
      M.tm.spaceUsedByTape (M.tm.initCfg x) t ((Fin.castAdd (M₁.k + M₂.k) i).castSucc) ≤
        D.tm.spaceUsedByTape (D.tm.initCfg x) T i := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v, hv, w, hw, z, hz0, hz1, he⟩ := f2_cond_ledger D M₁ M₂ x b T hD u
    apply Finset.mem_image.mpr
    refine ⟨v, Finset.mem_range.mpr (by omega), ?_⟩
    change _ = ((f2_timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _
    rw [he]
    simp [f2_condHeads, Fin.castSucc]
  have hBcard (i : Fin (M₁.k + M₂.k)) :
      M.tm.spaceUsedByTape (M.tm.initCfg x) t ((Fin.natAdd D.k i).castSucc) ≤
        B.tm.spaceUsedByTape (B.tm.initCfg x) t i := by
    apply Finset.card_le_card
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨v, hv, w, hw, z, hz0, hz1, he⟩ := f2_cond_ledger D M₁ M₂ x b T hD u
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_range.mpr (by have := Finset.mem_range.mp hu; omega), ?_⟩
    change _ = ((f2_timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _
    rw [he]
    simp [f2_condHeads, Fin.castSucc, B]
  have hcap : M.tm.spaceUsedByTape (M.tm.initCfg x) t (Fin.last _) ≤ 2 := by
    have hsub : M.tm.visitedByTapeHead (M.tm.initCfg x) t (Fin.last _) ⊆ Finset.Icc (0 : ℤ) 1 := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨v, hv, w, hw, z, hz0, hz1, he⟩ := f2_cond_ledger D M₁ M₂ x b T hD u
      change ((f2_timedCondTM D M₁ M₂).tm.runFrom _ u).workTapePos _ ∈ _
      rw [he]
      simpa [f2_condHeads, Fin.last, Fin.addCases] using Finset.mem_Icc.mpr ⟨hz0, hz1⟩
    exact (Finset.card_le_card hsub).trans (by decide)
  change (∑ i : Fin ((D.k + (M₁.k + M₂.k)) + 1), M.tm.spaceUsedByTape (M.tm.initCfg x) t i) ≤ _
  rw [f2_sum_add, f2_sum_add]
  simp only [Fintype.sum_unique]
  exact Nat.add_le_add (Nat.add_le_add
    (Finset.sum_le_sum (fun i _ => hDcard i))
    (Finset.sum_le_sum (fun i _ => hBcard i))) hcap

/-- **W3 space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.computesFunInTime_cond`). Given space bounds for
the decider and both branches, the conditional controller's space is the
decider's plus the selected branch's **max** — the unselected branch's
bank is idle (origin singletons) — plus a machine constant for the
capture tape and the idle banks' origin cells.

**Proof sketch.** The controller's tape banks are disjoint: the decider
bank is only touched in the capture phase (bounded by `sD` through the
W1 lockstep), the selected branch bank only after dispatch (bounded by
its own hypothesis on the same input `x` — no monotonicity needed), the
unselected bank and the capture tape contribute one cell per tape plus
the singleton verdict; sum the three groups. -/
theorem computesFunInTime_cond_spaceUsed {D M₁ M₂ : FinTM Bool}
    {p : List Bool → Bool} {f₁ f₂ : List Bool → List Bool}
    {T₀ T₁ T₂ : ℕ → ℕ} (sD s₁ s₂ : ℕ → ℕ)
    (hD : D.ComputesFunInTime (fun x => [p x]) T₀)
    (h₁ : M₁.ComputesFunInTime f₁ T₁) (h₂ : M₂.ComputesFunInTime f₂ T₂)
    (hsD : ∀ (x : List Bool) (t : ℕ),
      D.tm.spaceUsed (D.tm.initCfg x) t ≤ sD x.length)
    (hs₁ : ∀ (x : List Bool) (t : ℕ),
      M₁.tm.spaceUsed (M₁.tm.initCfg x) t ≤ s₁ x.length)
    (hs₂ : ∀ (x : List Bool) (t : ℕ),
      M₂.tm.spaceUsed (M₂.tm.initCfg x) t ≤ s₂ x.length) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => if p x then f₁ x else f₂ x)
        (fun n => c * (T₀ n + max (T₁ n) (T₂ n) + 1)) ∧
      ∀ (x : List Bool) (t : ℕ),
        M.tm.spaceUsed (M.tm.initCfg x) t
          ≤ sD x.length + max (s₁ x.length) (s₂ x.length) + c := by
  refine ⟨f2_timedCondTM D M₁ M₂, 7 + M₁.k + M₂.k, ?_, ?_⟩
  · intro x
    exact (f2_cond_time hD h₁ h₂ x).mono (Nat.mul_le_mul_right _ (by omega))
  · intro x t
    have h := f2_cond_space D M₁ M₂ x (p x) (T₀ x.length) t (hD x)
    rw [f2_branch_space] at h
    have hd := hsD x (T₀ x.length)
    have h1 := hs₁ x t
    have h2 := hs₂ x t
    have hm1 := Nat.le_max_left (s₁ x.length) (s₂ x.length)
    have hm2 := Nat.le_max_right (s₁ x.length) (s₂ x.length)
    split at h <;> omega

/-- A unit-step head starting at zero visits every integer between zero and
its endpoint. Thus a bound on total visited space bounds its displacement.
**Proof sketch.** Induct on time to put the intervening integer interval in
the visited set: a unit step adds at most its new endpoint. Take interval
cardinalities and use the inclusion of this tape's space in total space. -/
private lemma a2_source_radius {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) (c : Cfg k Bool Q x) (t B : ℕ)
    (hc : ∀ i, c.workTapePos i = 0) (hb : tm.spaceUsed c t ≤ B) (i : Fin k) :
    -(B : ℤ) ≤ (tm.runFrom c t).workTapePos i ∧
      (tm.runFrom c t).workTapePos i ≤ B := by
  have hinter (u : ℕ) : Finset.Icc (min 0 ((tm.runFrom c u).workTapePos i))
      (max 0 ((tm.runFrom c u).workTapePos i)) ⊆ tm.visitedByTapeHead c u i := by
    induction u with
    | zero =>
      intro z hz
      simp only [MultiTapeTM.runFrom_zero, hc, min_self, max_self,
        Finset.mem_Icc] at hz
      have hz0 : z = 0 := by omega
      subst z
      exact Finset.mem_image.mpr ⟨0, by simp, by simpa using hc i⟩
    | succ u ih =>
      intro z hz
      have hd := tm.workTapePos_step_le (tm.runFrom c u) i
      rw [abs_le] at hd
      rw [← MultiTapeTM.runFrom_succ_eq_step'] at hd
      by_cases hp : z ∈ Finset.Icc (min 0 ((tm.runFrom c u).workTapePos i))
          (max 0 ((tm.runFrom c u).workTapePos i))
      · obtain ⟨v, hv, he⟩ := Finset.mem_image.mp (ih hp)
        exact Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr
          (by have := Finset.mem_range.mp hv; omega), he⟩
      · simp only [Finset.mem_Icc] at hz hp
        have he : (tm.runFrom c (u + 1)).workTapePos i = z := by omega
        exact Finset.mem_image.mpr ⟨u + 1, by simp, he⟩
  have hcard := Finset.card_le_card (hinter t)
  rw [Int.card_Icc] at hcard
  have htotal := tm.spaceUsedByTape_le_spaceUsed c t i
  change (tm.visitedByTapeHead c t i).card ≤ tm.spaceUsed c t at htotal
  omega

/-- All physical heads lie in one fixed origin-centred integer interval. -/
private def a2_heads {k : ℕ} {Q : Type} {x : List Bool}
    (c : Cfg k Bool Q x) (B : ℕ) : Prop :=
  ∀ i, -(B : ℤ) ≤ c.workTapePos i ∧ c.workTapePos i ≤ B

/-- Enlarging the common interval preserves a head bound. -/
private lemma a2_heads_mono {k : ℕ} {Q : Type} {x : List Bool}
    {c : Cfg k Bool Q x} {A B : ℕ} (h : a2_heads c A) (hle : A ≤ B) :
    a2_heads c B := by
  intro i
  have := h i
  constructor <;> omega

/-- A short administrative segment enlarges its starting interval by at
most its duration, including every intermediate work-head position. -/
private lemma a2_heads_steps {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) (c : Cfg k Bool Q x) (A B t : ℕ)
    (h : a2_heads c A) (ht : t ≤ B) : a2_heads (tm.runFrom c t) (A + B) := by
  intro i
  have hs := h i
  have hm := f2_head_steps tm c t i
  constructor <;> omega

/-- Concatenating two bounded traces reuses their common interval. -/
private lemma a2_heads_join {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) (c : Cfg k Bool Q x) (a b B : ℕ)
    (ha : ∀ u ≤ a, a2_heads (tm.runFrom c u) B)
    (hb : ∀ u ≤ b, a2_heads (tm.runFrom (tm.runFrom c a) u) B) :
    ∀ u ≤ a + b, a2_heads (tm.runFrom c u) B := by
  intro u hu
  by_cases h : u ≤ a
  · exact ha u h
  · rw [show u = a + (u - a) by omega, MultiTapeTM.runFrom_add]
    exact hb (u - a) (by omega)

/-- After a halting endpoint, every later head is that same endpoint head. -/
private lemma a2_heads_halted {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) (c : Cfg k Bool Q x) (a B : ℕ)
    (hh : (tm.runFrom c a).state = none)
    (ha : ∀ u ≤ a, a2_heads (tm.runFrom c u) B) :
    ∀ u, a2_heads (tm.runFrom c u) B := by
  intro u
  by_cases h : u ≤ a
  · exact ha u h
  · rw [show u = a + (u - a) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ hh]
    exact ha a (le_refl _)

/-- Project a captured body call onto its body, stationary flag, fixed
counter origin, retained fuel bank, and current output-length head. -/
private lemma a2_call_heads (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (startup : Bool) (c : Cfg body.k Bool body.State x)
    (release : Bool) (flag : Option Bool) (word : List Bool)
    (fuel : Cfg F.k Bool F.State x) (B : ℕ)
    (hb : a2_heads c B) (hf : a2_heads fuel B) (ho : c.output.length ≤ B) :
    a2_heads (f2_loopCall body F anchor startup c release flag word fuel) B := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [f2_loopCall, captureCfg, Fin.val_last, lt_self_iff_false, ↓reduceDIte,
      f2_loopBodyPadded, leftCfg, f2_loopBodyCfg, List.nil_append]
    constructor <;> omega
  · simp only [f2_loopCall, captureCfg, Fin.coe_castSucc, dif_pos j.isLt]
    change -(B : ℤ) ≤ (f2_loopBodyPadded body F anchor c release flag word fuel).workTapePos j ∧
      (f2_loopBodyPadded body F anchor c release flag word fuel).workTapePos j ≤ B
    simp only [f2_loopBodyPadded, leftCfg]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.addCases_left, f2_loopBodyCfg]
      split
      · exact hb _
      · constructor <;> omega
    · simp only [Fin.addCases_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.addCases_left]; constructor <;> omega
      · simpa only [Fin.addCases_right] using hf j

/-- Fuel capture preserves its source heads, leaves the other banks at
zero, and places its last head at the current fuel output length. -/
private lemma a2_fuel_heads (body F : FinTM Bool) {x : List Bool}
    (c : Cfg F.k Bool F.State x) (B : ℕ)
    (hf : a2_heads c B) (ho : c.output.length ≤ B) :
    a2_heads (f2_loopFuelCaptured body F c) B := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [f2_loopFuelCaptured, captureCfg, Fin.val_last, lt_self_iff_false,
      ↓reduceDIte, f2_loopFuelCfg, rightCfg, List.nil_append]
    constructor <;> omega
  · simp only [f2_loopFuelCaptured, captureCfg, Fin.coe_castSucc, dif_pos j.isLt]
    change -(B : ℤ) ≤ (f2_loopFuelCfg body F c).workTapePos j ∧
      (f2_loopFuelCfg body F c).workTapePos j ≤ B
    simp only [f2_loopFuelCfg, rightCfg]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp only [Fin.addCases_left]; constructor <;> omega
    · simp only [Fin.addCases_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.addCases_left]; constructor <;> omega
      · simpa only [Fin.addCases_right] using hf j

/-- Every prefix of a captured body call is the same prefix of its source,
with the release bit consumed once and the halt flag set on the last action. -/
private lemma a2_call_run (body F : FinTM Bool) (anchor : body.State)
    (findMode startup : Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (hc : c.state ≠ none)
    (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor) :
    (f2_loopHost body F anchor findMode).tm.runFrom
        (f2_loopCall body F anchor startup c release none word fuel) t =
      f2_loopCall body F anchor startup (body.tm.runFrom c t)
        (if t = 0 then release else false)
        (if (body.tm.runFrom c t).state = none then some true else none) word fuel := by
  unfold f2_loopCall f2_loopBodyPadded
  rw [f2_loopHost_body_capture]
  · rw [f2_loopBodySource_run, f2_loopBody_run body anchor c release hc t hlive hanchor]
  · intro u hu
    rw [f2_loopBodySource_run, f2_loopBody_run body anchor c release hc u
      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
    simpa [Cfg.Halted, leftCfg, f2_loopBodyCfg] using hlive u hu

/-- Budgeted source space bounds all captured-call prefixes. Empty final
output gives no capture growth; a singleton final verdict gives at most one
cell of growth, including a verdict emitted by the halting action. -/
private lemma a2_call_prefix (body F : FinTM Bool) (anchor : body.State)
    (startup : Bool) {x : List Bool}
    (c : Cfg body.k Bool body.State x) (release : Bool) (t B : ℕ)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (hc : c.state ≠ none)
    (hzero : ∀ i, c.workTapePos i = 0)
    (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
      (body.tm.runFrom c u).state ≠ some anchor)
    (hspace : ∀ u ≤ t, body.tm.spaceUsed c u ≤ B)
    (hf : a2_heads fuel B) (hout : (body.tm.runFrom c t).output.length ≤ B) :
    ∀ u ≤ t, a2_heads ((f2_loopHost body F anchor false).tm.runFrom
      (f2_loopCall body F anchor startup c release none word fuel) u) B := by
  intro u hu
  rw [a2_call_run body F anchor false startup c release u word fuel hc
    (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
  exact a2_call_heads body F anchor startup _ _ _ word fuel B
    (a2_source_radius body.tm c u B hzero (hspace u hu)) hf
    (((body.tm.output_prefix c hu).length_le).trans hout)

/-- Fuel capture and installation have a width-bounded space ledger.
The fuel source is charged to its space hypothesis; the three installation
scans cost `3*width+4`, and the possibly long input rewind moves no work head.
**Proof sketch.** Capture to the first halt, project the source heads and
output lengths at every prefix, then concatenate the setup and input-only
rewind traces. Retain the source endpoint's `B` bound for all later calls. -/
private lemma a2_loop_prepare (body F : FinTM Bool) (anchor : body.State)
    (R T S : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hspace : ∀ x t, F.tm.spaceUsed (F.tm.initCfg x) t ≤ S x.length)
    (x : List Bool) :
    ∃ (c : Cfg F.k Bool F.State x) (t : ℕ),
      c.state = none ∧ c.output = Nat.bits (R x.length) ∧ t ≤ 5 * T x.length + 7 ∧
      (f2_loopHost body F anchor false).tm.runFrom
        ((f2_loopHost body F anchor false).tm.initCfg x) t = f2_loopReady body F c ∧
      a2_heads c (S x.length) ∧
      ∀ u ≤ t, a2_heads ((f2_loopHost body F anchor false).tm.runFrom
        ((f2_loopHost body F anchor false).tm.initCfg x) u)
        (S x.length + 4 * (Nat.bits (R x.length)).length + 4) := by
  obtain ⟨space, hhalt, hout, _⟩ := hF x
  obtain ⟨u, hu, hut, hlive, huh, hue⟩ :=
    f2_loop_first_halt F.tm (F.tm.initCfg x) (T x.length)
      (by simp [MultiTapeTM.initCfg, Cfg.init]) hhalt
  let c := F.tm.runFrom (F.tm.initCfg x) u
  have hc : c.state = none := huh
  have ho : c.output = Nat.bits (R x.length) := by dsimp only [c]; rw [hue]; exact hout
  have hcap (v : ℕ) (hv : v ≤ u) : (f2_loopHost body F anchor false).tm.runFrom
      ((f2_loopHost body F anchor false).tm.initCfg x) v =
        f2_loopFuelCaptured body F (F.tm.runFrom (F.tm.initCfg x) v) := by
    rw [f2_loopHost_init, f2_loopFuel_init, f2_loopHost_fuel_capture]
    · rw [f2_loopFuel_run]; rfl
    · intro w hw
      rw [f2_loopFuel_run]
      simpa [Cfg.Halted, f2_loopFuelCfg, rightCfg] using hlive w (by omega)
  have hs (v : ℕ) : a2_heads (F.tm.runFrom (F.tm.initCfg x) v) (S x.length) :=
    a2_source_radius F.tm (F.tm.initCfg x) v _ (fun _ => rfl) (hspace x v)
  have hpref (v : ℕ) (hv : v ≤ u) : a2_heads
      ((f2_loopHost body F anchor false).tm.runFrom
        ((f2_loopHost body F anchor false).tm.initCfg x) v)
      (S x.length + c.output.length) := by
    rw [hcap v hv]
    apply a2_fuel_heads
    · exact a2_heads_mono (hs v) (by omega)
    · have := (F.tm.output_prefix (F.tm.initCfg x) hv).length_le
      change (F.tm.runFrom (F.tm.initCfg x) v).output.length ≤ c.output.length at this
      omega
  let prepared := f2_loopFrame body F (f2_loopFuelCaptured body F c)
    (some (.inr (.inr 4))) c.inputPos (bufferTape []) (bufferTape c.output)
    (bufferTape []) 0 0 []
  have hsetup : (f2_loopHost body F anchor false).tm.runFrom
      (f2_loopFuelCaptured body F c) (3 * c.output.length + 4) = prepared := by
    conv_lhs => arg 1; rw [f2_loopFuelCaptured_frame body F c hc]
    exact f2_loopHost_fuel_setup body F anchor false _ _ _ _ _
  obtain ⟨v, hv, hrew, hrewheads⟩ := f2_rewind_heads
    (f2_loopHost body F anchor false).tm (.inr (.inr 4)) (.inr (.inr 5))
    (.some (.inr (.inl (true, (body.tm.q₀, false)))))
    (fun _ _ => f2_loopControl_idle body F .neg _)
    (fun inp _ => by cases inp <;> exact f2_loopControl_idle body F _ _) prepared rfl
  have hw : c.output.length ≤ T x.length := by rw [ho]; exact f2_loop_fuel_width F R T hF x
  have hi : c.inputPos.val ≤ 1 + u := f2_loop_input_run_le F.tm (F.tm.initCfg x) u
  have hinstall (w : ℕ) (hw : w ≤ 3 * c.output.length + 4) :
      a2_heads ((f2_loopHost body F anchor false).tm.runFrom
        (f2_loopFuelCaptured body F c) w) (S x.length + 4 * c.output.length + 4) := by
    have hb := hpref u (le_refl _)
    rw [hcap u (le_refl _)] at hb
    have hh := a2_heads_steps (f2_loopHost body F anchor false).tm
      (f2_loopFuelCaptured body F c) _ (3 * c.output.length + 4) w hb hw
    convert hh using 1 <;> omega
  refine ⟨c, u + (3 * c.output.length + 4) + v, hc, ho, ?_, ?_, hs u, ?_⟩
  · change v ≤ c.inputPos.val + 2 at hv
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
      hcap u (le_refl _), hsetup, hrew]
    rfl
  · rw [← ho]
    apply a2_heads_join
    · apply a2_heads_join
      · intro w hw
        exact a2_heads_mono (hpref w hw) (by omega)
      · rw [hcap u (le_refl _)]
        exact hinstall
    · rw [MultiTapeTM.runFrom_add, hcap u (le_refl _), hsetup]
      intro w hw i
      rw [hrewheads w hw]
      have hh := hinstall (3 * c.output.length + 4) (le_refl _)
      rw [hsetup] at hh
      exact hh i

/-- Startup uses its space hypothesis only up to the supplied first anchor;
the silent stop and release add two bounded administrative steps. -/
private lemma a2_loop_start_prefix (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (s : List Bool) (t B : ℕ) (fuel : Cfg F.k Bool F.State x)
    (hguard : ∀ u < t, (body.tm.runFrom (body.tm.initCfg x) u).state ≠ some anchor)
    (hend : body.tm.runFrom (body.tm.initCfg x) t = Cfg.ofWords anchor (stateWord body.k s))
    (hs : ∀ u ≤ t, body.tm.spaceUsed (body.tm.initCfg x) u ≤ B)
    (hf : a2_heads fuel B) :
    ∀ u ≤ t + 2, a2_heads ((f2_loopHost body F anchor false).tm.runFrom
      (f2_loopReady body F fuel) u) (B + 2) := by
  rw [f2_loopReady_call body F anchor]
  have hl := f2_loop_live_prefix body.tm (body.tm.initCfg x) t
    (by rw [hend]; simp [Cfg.ofWords])
  have hp := a2_call_prefix body F anchor true (body.tm.initCfg x) false t B
    fuel.output fuel (by simp [MultiTapeTM.initCfg, Cfg.init]) (fun _ => rfl)
    (fun u hu => hl u (by omega)) (fun u hu => Or.inr (hguard u hu)) hs hf
    (by rw [hend]; simp [Cfg.ofWords])
  apply a2_heads_join
  · intro u hu
    exact a2_heads_mono (hp u hu) (by omega)
  · intro u hu
    exact a2_heads_steps _ _ B 2 u (hp t (le_refl _)) hu

/-- A decision round has a single fixed space interval, independent of its
index. The source bank uses the budgeted source hypothesis, the retained
fuel bank starts within the same bound, and debit administration is charged
only to the unchanged counter width.
**Proof sketch.** At acceptance use the actual first halt; append-only output
bounds capture by one. At rejection the source endpoint is silent and has
origin heads. The stop plus the received borrow/rewind/underflow segment
costs at most `2*width+5`. Concatenate prefix bounds, including both endings. -/
private lemma a2_loop_round (body F : FinTM Bool) (anchor : body.State)
    {x : List Bool} (s next : List Bool) (accepted : Bool)
    (word : List Bool) (fuel : Cfg F.k Bool F.State x) (t B : ℕ) (ht : 0 < t)
    (hanchor : ∀ u, 0 < u → u < t →
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) u).state ≠ some anchor)
    (hend : if accepted then
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state = none ∧
      (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output = [true]
      else body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
        Cfg.ofWords anchor (stateWord body.k next))
    (hspace : ∀ u ≤ t, body.tm.spaceUsed
      (Cfg.ofWords (input := x) anchor (stateWord body.k s)) u ≤ B)
    (hf : a2_heads fuel B) :
    ∃ v,
      (∀ u ≤ v, a2_heads ((f2_loopHost body F anchor false).tm.runFrom
        (f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
          true none word fuel) u) (B + 2 * word.length + 6)) ∧
      ((f2_loopHost body F anchor false).tm.runFrom
        (f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
          true none word fuel) v).state = none ∨
      ∃ v, (f2_loopDebit word).2 = true ∧
        (∀ u ≤ v, a2_heads ((f2_loopHost body F anchor false).tm.runFrom
          (f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
            true none word fuel) u) (B + 2 * word.length + 6)) ∧
        (f2_loopHost body F anchor false).tm.runFrom
          (f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k s))
            true none word fuel) v =
          f2_loopCall body F anchor false (Cfg.ofWords anchor (stateWord body.k next))
            true none (f2_loopDebit word).1 fuel := by
  let start := Cfg.ofWords (input := x) anchor (stateWord body.k s)
  have hzero (i) : start.workTapePos i = 0 := rfl
  have hc : start.state ≠ none := by simp [start, Cfg.ofWords]
  have hg : ∀ u < t, (u = 0 ∧ true = true) ∨ (body.tm.runFrom start u).state ≠ some anchor := by
    intro u hu
    by_cases hz : u = 0
    · exact Or.inl ⟨hz, rfl⟩
    · exact Or.inr (hanchor u (by omega) hu)
  by_cases ha : accepted = true
  · simp only [ha, if_true] at hend
    obtain ⟨u, hu, hut, hlive, hhalt, he⟩ := f2_loop_first_halt body.tm start t hc hend.1
    have hcap := f2_loopHost_halt_return body F anchor false start u word fuel hu hlive
      (fun v hv hvu => hanchor v hv (by omega)) hhalt
    obtain ⟨v, hv, hstop, _⟩ := f2_loopHost_accept body F anchor false
      (body.tm.runFrom start u) word fuel hhalt
    have ho : (body.tm.runFrom start u).output = [true] := by rw [he]; exact hend.2
    have hv5 : v ≤ 5 := by simpa [ho] using hv
    have hp := a2_call_prefix body F anchor false start true u (B + 1) word fuel hc hzero
      hlive (fun w hw => hg w (by omega))
      (fun w hw => (hspace w (by omega)).trans (by omega))
      (a2_heads_mono hf (by omega)) (by simp [ho])
    refine ⟨u + v, ?_⟩
    left
    constructor
    · apply a2_heads_join
      · intro w hw
        exact a2_heads_mono (hp w hw) (by omega)
      · intro w hw
        exact a2_heads_mono (a2_heads_steps _ _ (B + 1) 5 w
          (hp u (le_refl _)) (by omega)) (by omega)
    · rw [MultiTapeTM.runFrom_add, hcap]
      exact hstop
  · simp only [ha] at hend
    have hl := f2_loop_live_prefix body.tm start t (by rw [hend]; simp [Cfg.ofWords])
    have hp := a2_call_prefix body F anchor false start true t B word fuel hc hzero
      (fun w hw => hl w (by omega)) hg hspace hf (by rw [hend]; simp [Cfg.ofWords])
    have hcap := f2_loopHost_anchor_return body F anchor false false start true t word fuel
      (by rw [hend]; rfl) (by intro hz; omega) hg
    rw [show body.tm.runFrom start t = Cfg.ofWords anchor (stateWord body.k next) from hend] at hcap
    obtain ⟨v, hv, hfinish⟩ := f2_loopHost_reject body F anchor false
      {Cfg.ofWords (input := x) anchor (stateWord body.k next) with state := none}
      word fuel rfl rfl
    have hpall : ∀ u ≤ (t + 1) + v, a2_heads
        ((f2_loopHost body F anchor false).tm.runFrom
          (f2_loopCall body F anchor false start true none word fuel) u)
        (B + 2 * word.length + 6) := by
      rw [show (t + 1) + v = t + (1 + v) by omega]
      apply a2_heads_join
      · intro w hw
        exact a2_heads_mono (hp w hw) (by omega)
      · intro w hw
        exact a2_heads_mono (a2_heads_steps _ _ B (2 * word.length + 5) w
          (hp t (le_refl _)) (by omega)) (by omega)
    refine ⟨(t + 1) + v, ?_⟩
    by_cases hd : (f2_loopDebit word).2 = true
    · right
      refine ⟨(t + 1) + v, hd, hpall, ?_⟩
      rw [MultiTapeTM.runFrom_add, hcap]
      simpa only [hd, if_true] using hfinish
    · left
      refine ⟨hpall, ?_⟩
      rw [MultiTapeTM.runFrom_add, hcap]
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at hfinish
      exact hfinish.1

/-- A finite chain of returning or halting segments reuses one interval.
The last segment must halt; every earlier halt supplies a stationary tail.
The interval is never multiplied by the number of segments. -/
private lemma a2_segments {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) (cfg : ℕ → Cfg k Bool Q x) (N B : ℕ)
    (hN : 0 < N)
    (hround : ∀ i < N, ∃ u,
      (∀ v ≤ u, a2_heads (tm.runFrom (cfg i) v) B) ∧
      ((tm.runFrom (cfg i) u).state = none ∨
        i + 1 < N ∧ tm.runFrom (cfg i) u = cfg (i + 1))) :
    ∀ t, a2_heads (tm.runFrom (cfg 0) t) B := by
  induction N generalizing cfg with
  | zero => omega
  | succ N ih =>
    obtain ⟨u, hp, he⟩ := hround 0 (by omega)
    intro t
    by_cases ht : t ≤ u
    · exact hp t ht
    · rw [show t = u + (t - u) by omega, MultiTapeTM.runFrom_add]
      rcases he with hh | ⟨hn, hr⟩
      · rw [MultiTapeTM.runFrom_of_halt _ hh]
        exact hp u (le_refl _)
      · rw [hr]
        exact ih (fun i => cfg (i + 1)) (by omega)
          (fun i hi => by
            obtain ⟨v, hv, he⟩ := hround (i + 1) (by omega)
            refine ⟨v, hv, ?_⟩
            rcases he with hh | ⟨hj, hr⟩
            · exact Or.inl hh
            · exact Or.inr ⟨by omega, hr⟩) (t - u)

/-- Sum the received decision segments, with an already halted false terminal.
**Proof sketch.** Induct on the candidate count; acceptance stops, while a
rejection composes the next segment and shifts the Boolean list test. -/
private lemma a2_loop_halted_run {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : ℕ → Cfg k Bool S x)
    (accept : ℕ → Bool) (B N : ℕ)
    (hend : (cfg N).state = none ∧ (cfg N).output = [false])
    (hround : ∀ j < N, ∃ t ≤ B,
      if accept j then
        (tm.runFrom (cfg j) t).state = none ∧
          (tm.runFrom (cfg j) t).output = [true]
      else tm.runFrom (cfg j) t = cfg (j + 1)) :
    ∃ t ≤ N * B, (tm.runFrom (cfg 0) t).state = none ∧
      (tm.runFrom (cfg 0) t).output = [(List.range N).any accept] := by
  induction N generalizing cfg accept with
  | zero => exact ⟨0, by simp, by simpa using hend⟩
  | succ N ih =>
    obtain ⟨t, ht, hc⟩ := hround 0 (by omega)
    have hany : (List.range (N + 1)).any accept =
        (accept 0 || (List.range N).any (fun j => accept (j + 1))) := by
      simp [List.range_succ_eq_map, List.any_map, Function.comp_def]
    by_cases hb : accept 0 = true
    · simp only [hb, ↓reduceIte] at hc
      refine ⟨t, ht.trans ?_, hc.1, ?_⟩
      · exact Nat.le_mul_of_pos_left B (by omega)
      · simpa [hany, hb] using hc.2
    · simp only [hb] at hc
      obtain ⟨s, hs, hhalt, hout⟩ := ih
        (fun j => cfg (j + 1)) (fun j => accept (j + 1)) hend
        (fun j hj => hround (j + 1) (by omega))
      refine ⟨t + s, ?_, ?_, ?_⟩
      · rw [Nat.succ_mul]; omega
      · rw [MultiTapeTM.runFrom_add, hc]; exact hhalt
      · rw [MultiTapeTM.runFrom_add, hc]
        simpa [hany, hb] using hout

/-- **L space row** (spec, fill pending — design §12 R3, decision 12.3;
annotates `Turing.FinTM.exists_loopTM`; the `exists_loopCfgTM` and
`exists_loopFindTM` siblings inherit the same host at fill time). Same
hypotheses as the decision loop, plus space bounds for the fuel machine
and for the body — from its initial configuration and from every
admissible seam, within the round budget. Conclusion: the loop host also
runs within a constant multiple of `S n + T n + 1` work-tape cells. The
key point is that space does **not** scale with the round count `R`:
rounds restart from seams with heads at the origin, so their footprints
overlap instead of accumulating.

**Proof sketch.** Per tape, each round's visited set is an interval
containing the seam origin (heads move by unit steps from the origin) of
cardinality at most `S n`, so the union over all rounds lies in
`[-(S n), S n]` — at most `2·S n + 1` cells, not `R·S n`. The counter
tape holds the fuel word, of length at most `T n`
(`Turing.MultiTapeTM.output_length_le` on the fuel machine), walked in
place by the debits; the capture tape records one verdict per round and
is rewound with the round, staying within a constant; the fuel machine's
own banks are bounded by `hFspace`. Sum the groups and absorb tape
counts into `c`.  **Scope note (round-1 note R10)**: this row annotates the
decision-loop export (`Turing.exists_loopTM`) only; the configuration- and
result-bearing siblings (`exists_loopCfgTM`, `exists_loopFindTM`) carry no
exported space clause here — same-witness conjunctions for them are a
recorded future addition, commissioned when a consumer needs them, not an
implied theorem. -/
theorem exists_loopTM_spaceUsed (body F : FinTM Bool) (anchor : body.State)
    (Inv : List Bool → List Bool → Prop)
    (stepF : List Bool → List Bool → List Bool)
    (acceptF : List Bool → List Bool → Bool)
    (s0 : List Bool → List Bool) (R T S : ℕ → ℕ)
    (hF : F.ComputesFunInTime (fun x => Nat.bits (R x.length)) T)
    (hInv0 : ∀ x : List Bool, Inv x (s0 x))
    (hInvStep : ∀ (x s : List Bool), Inv x s → Inv x (stepF x s))
    (hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t,
        (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord body.k (s0 x)))
    (hround : ∀ (x s : List Bool), Inv x s →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
              ≠ some anchor) ∧
        if acceptF x s then
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).state
              = none ∧
          (body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t).output
              = [true]
        else
          body.tm.runFrom
            (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
              Cfg.ofWords anchor (stateWord body.k (stepF x s)))
    (hFspace : ∀ (x : List Bool) (t : ℕ),
      F.tm.spaceUsed (F.tm.initCfg x) t ≤ S x.length)
    (hstartSpace : ∀ (x : List Bool) (t : ℕ), t ≤ T x.length →
      body.tm.spaceUsed (body.tm.initCfg x) t ≤ S x.length)
    (hroundSpace : ∀ (x s : List Bool), Inv x s →
      ∀ t ≤ T x.length,
        body.tm.spaceUsed
          (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t
            ≤ S x.length) :
    ∃ (E : FinTM Bool) (c : ℕ),
      E.ComputesFunInTime
        (fun x => [(List.range (R x.length + 1)).any
          fun i => acceptF x ((stepF x)^[i] (s0 x))])
        (fun n => c * (T n + 1) * (R n + 2)) ∧
      ∀ (x : List Bool) (t : ℕ),
        E.tm.spaceUsed (E.tm.initCfg x) t
          ≤ c * (S x.length + T x.length + 1) := by
  obtain ⟨c, hc⟩ := f2_loopHost_contracts body F anchor Inv stepF acceptF
    (fun _ _ => [true]) false s0 R T hF hInv0 hInvStep hstart hround
  let E := f2_loopHost body F anchor false
  have htime : E.ComputesFunInTime
      (fun x => [(List.range (R x.length + 1)).any
        fun i => acceptF x ((stepF x)^[i] (s0 x))])
      (fun n => c * (T n + 1) * (R n + 2)) := by
    intro x
    obtain ⟨cfg, startup, hs, hinit, _, hend, hout, hsegments, _, _⟩ := hc x
    obtain ⟨t, ht, hhalt, houtput⟩ := a2_loop_halted_run E.tm cfg
      (fun i => acceptF x ((stepF x)^[i] (s0 x))) (c * (T x.length + 1))
      (R x.length + 1) ⟨hend, by simpa using hout⟩
      (fun j hj => by simpa using hsegments j (by omega))
    have hrun := E.tm.runFrom_add (E.tm.initCfg x) startup t
    rw [hinit] at hrun
    have hcompute : E.ComputesInTime x
        [(List.range (R x.length + 1)).any
          (fun i => acceptF x ((stepF x)^[i] (s0 x)))] (startup + t) := by
      refine ⟨_, ?_, ?_, rfl⟩
      · rw [hrun]; exact hhalt
      · rw [hrun]; exact houtput
    apply hcompute.mono
    calc startup + t ≤ c * (T x.length + 1) +
          (R x.length + 1) * (c * (T x.length + 1)) := Nat.add_le_add hs ht
      _ = c * (T x.length + 1) * (R x.length + 2) := by ring
  refine ⟨E, c + 19 * E.k, ?_, ?_⟩
  · intro x
    exact (htime x).mono (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  · intro x t
    -- Fuel: capture has its source's space bound and its actual output width.
    obtain ⟨fuel, ftime, hfh, hfo, hft, hprepare, hfuel, hprepareSpace⟩ :=
      a2_loop_prepare body F anchor R T S hF hFspace x
    obtain ⟨btime, hbt, hbguard, hbend⟩ := hstart x
    let words (i : ℕ) := (fun w => (f2_loopDebit w).1)^[i] (Nat.bits (R x.length))
    let orbit (i : ℕ) := (stepF x)^[i] (s0 x)
    let cfg (i : ℕ) := f2_loopCall body F anchor false
      (Cfg.ofWords (input := x) anchor (stateWord body.k (orbit i))) true none (words i) fuel
    let B := S x.length + 4 * (Nat.bits (R x.length)).length + 8
    have hwidth (i : ℕ) : (words i).length = (Nat.bits (R x.length)).length :=
      f2_loopDebit_iterate_length _ _
    have hsuccess (i : ℕ) (hi : i ≤ R x.length) :
        (f2_loopDebit (words i)).2 = true ↔ i < R x.length := by
      rw [f2_loopDebit_success]
      dsimp only [words]
      rw [f2_loopDebit_iterate_value _ _ hi]
      omega
    -- Every admissible source call starts at zero. Its captured prefixes
    -- are bounded before the common, fixed-width administrative allowance.
    have hlocal : ∀ i < R x.length + 1, ∃ u,
        (∀ v ≤ u, a2_heads (E.tm.runFrom (cfg i) v) B) ∧
        ((E.tm.runFrom (cfg i) u).state = none ∨
          i + 1 < R x.length + 1 ∧ E.tm.runFrom (cfg i) u = cfg (i + 1)) := by
      intro i hi
      have hinv := f2_loop_orbit_inv Inv stepF s0 hInv0 hInvStep x i
      obtain ⟨u, hup, hut, hguard, hend⟩ := hround x (orbit i) hinv
      obtain ⟨v, he⟩ := a2_loop_round body F anchor (orbit i) (stepF x (orbit i))
        (acceptF x (orbit i)) (words i) fuel u (S x.length) hup hguard hend
        (fun w hw => hroundSpace x (orbit i) hinv w (hw.trans hut)) hfuel
      have hbound : S x.length + 2 * (words i).length + 6 ≤ B := by
        rw [hwidth]
        dsimp [B]
        omega
      rcases he with ⟨hp, hh⟩ | ⟨v', hd, hp, he⟩
      · exact ⟨v, fun w hw => a2_heads_mono (hp w hw) hbound, Or.inl hh⟩
      · refine ⟨v', fun w hw => a2_heads_mono (hp w hw) hbound,
          Or.inr ⟨by have := (hsuccess i (by omega)).mp hd; omega, ?_⟩⟩
        simpa only [cfg, words, orbit, Function.iterate_succ_apply'] using he
    have hrounds := a2_segments E.tm cfg (R x.length + 1) B (by omega) hlocal
    -- Startup has no captured output, and its stop/release is two steps.
    have hinit : E.tm.runFrom (E.tm.initCfg x) (ftime + (btime + 2)) = cfg 0 := by
      rw [MultiTapeTM.runFrom_add, hprepare,
        f2_loopHost_start body F anchor false (s0 x) btime fuel hbguard hbend]
      simp only [cfg, words, orbit, Function.iterate_zero_apply, hfo]
    have hstartup : ∀ u ≤ ftime + (btime + 2),
        a2_heads (E.tm.runFrom (E.tm.initCfg x) u) B := by
      apply a2_heads_join
      · intro u hu
        exact a2_heads_mono (hprepareSpace u hu) (by dsimp [B]; omega)
      · rw [hprepare]
        intro u hu
        exact a2_heads_mono (a2_loop_start_prefix body F anchor (s0 x) btime
          (S x.length) fuel hbguard hbend
          (fun v hv => hstartSpace x v (hv.trans hbt)) hfuel u hu)
          (by dsimp [B]; omega)
    -- Reuse the same interval over every round and every halted tail.
    have hall : ∀ u, a2_heads (E.tm.runFrom (E.tm.initCfg x) u) B := by
      intro u
      by_cases hu : u ≤ ftime + (btime + 2)
      · exact hstartup u hu
      · rw [show u = (ftime + (btime + 2)) + (u - (ftime + (btime + 2))) by omega,
          MultiTapeTM.runFrom_add, hinit]
        exact hrounds _
    have hs := f2_space_radius E x B hall t
    have hw := f2_loop_fuel_width F R T hF x
    have hb : 2 * B + 1 ≤ 19 * (S x.length + T x.length + 1) := by
      dsimp only [B]
      omega
    calc
      E.tm.spaceUsed (E.tm.initCfg x) t ≤ E.k * (2 * B + 1) := hs
      _ ≤ E.k * (19 * (S x.length + T x.length + 1)) := Nat.mul_le_mul_left _ hb
      _ = (19 * E.k) * (S x.length + T x.length + 1) := by ring
      _ ≤ (c + 19 * E.k) * (S x.length + T x.length + 1) :=
        Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Build/Wrappers.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.Composition

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: wrappers

The output-isolation layer of the machine-construction library
(`machine-library-design.md` §5, W1–W3): the capture/silence discipline
written once, consolidating its four private incarnations
(`universalCaptureTM` in the universal-machine development, the Chapter-2
enumerator's `enumCaptureTM`, the HALT batch's `acceptTM`, and the private
engine inside `TCSlib.Complexity.TuringMachine.Composition.exists_cond`).
The obligation list is the one the phase-1 and phase-4 audits tabulated:
every source emission is captured, **including an emission on the halting
transition**; the wrapper's physical output stays untouched; the completed
source configuration is preserved at the return.

**Status: proved.** The two action/configuration transformers and the
derived machine are real definitions; the four contract theorems are
proved (filled from the existing private proofs in the library fill
batches; gates closed). New Chapter-1 surface, audited in the shared
infrastructure round.

## Design

* **W1 (capture)** is *host-parametric*: rather than a closed wrapper
  machine, `Turing.captureAction` transforms one source action into a host
  action (source tapes untouched, emission appended to the last tape,
  silence, halt redirected to a designated return state), and
  `Turing.capture_run` says that **any** host machine agreeing with the
  transformed table on an embedded copy of the source states simulates the
  source in lockstep with its output captured on the last tape. Consumers
  (the loop fill, HALT-style control modifications, the Chapter-2
  continuations) embed the source into *their* controller state type and
  inherit the whole induction. The capture tape holds the full output
  word (tape-capture core, frozen design decision 9.3); reading one bit
  off it is the register corollary, derived at fill time.
* **W2 (halt-redirect)** is the `acceptTM` pattern as a closed
  transformation `Turing.FinTM.redirectTM`: simulate a machine silently
  while remembering the last emitted bit, halt exactly when the source
  halts with the designated bit, and otherwise enter a one-state
  stationary live loop.
* **W3 (timed branch)** is the quantitative form of
  `Turing.FinTM.exists_comp_partial`'s sibling
  `Turing.FinTM.exists_cond`: deciding which branch runs costs the
  decider's budget, and the branch runs on the *same* physical input, so
  no monotonicity hypothesis is needed.

## Main declarations

* `Turing.captureAction`, `Turing.captureCfg` — the W1 transformers.
* `Turing.capture_run` — the W1 lockstep/capture/silence contract.
* `Turing.FinTM.redirectTM` — the W2 transformation.
* `Turing.FinTM.redirectTM_computes`, `Turing.FinTM.redirectTM_live` — the
  W2 contract pair.
* `Turing.FinTM.computesFunInTime_cond` — the W3 timed branch.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; the capture discipline is the
  output-isolation folklore every simulation argument of §1.4–§1.7 uses.)

**Implementation note (batch W).** All four contracts are now proved; the
original spec-phase descriptions above and in their docstrings are retained.
The conditional controller instantiates `capture_run` on a padded decider,
reads its singleton output, and uses a quantitative refinement of
`rewind_from_any`. Its branch-start prefix is at most twice the decider's
budget plus five, yielding the uniform multiplier `5` in the frozen bound.

**Maintainer note (D6 promotion).** Batch W's two shared-lemma promotion
requests are executed: `timed_input_bound` is now the public
`Turing.MultiTapeTM.timed_input_bound` in `Deterministic.lean` (generalized
from `Bool` to an arbitrary symbol type; the proof was symbol-free), and
`timed_rewind` is the public `Turing.FinTM.timed_rewind` in
`Simulation.lean`, verbatim. The private copies formerly here are removed;
the two call sites below consume the public lemmas.

**Implementation note (emitter batch W).** `emit_run` is now proved by the
private action identity `emit_apply` and the guarded induction used by
`capture_run`. A halting action forwards its optional final emission on
the same transition that transfers control to the live return state.
-/

namespace Turing

variable {k : ℕ} {S H : Type*}

/-- W1 action transformer. Transform one source action into a host action
over one extra tape: the source's input move and work-tape actions are kept
on the first `k` tapes; the source's emission, **if any**, is written on
the last tape with a right move (so the capture tape accumulates the output
word from the origin); the host emits nothing; a live source successor is
embedded via `emb`, and a halting source action transfers control to the
designated return state `ret` — on the very transition that may carry the
final emission, which is therefore captured like any other. -/
def captureAction (emb : S → H) (ret : H) (a : Action k Bool S) :
    Action (k + 1) Bool H where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < k then a.workTapes ⟨i, h⟩
    else
      match a.output with
      | some b => (some (some b), SignType.pos)
      | none => (none, SignType.zero)
  output := none
  state := some ((a.state.map emb).getD ret)

/-- W1 configuration correspondence. A source configuration `c`, viewed
inside a host with one extra tape: source state embedded (a halted source
sits at the return state `ret`), same input head, source work tapes on the
first `k` tapes, and the capture tape holding `pre ++ c.output` — the
emissions captured so far after a pre-existing prefix — with its head one
past that word. The host's own physical output is the untouched `out₀`. -/
def captureCfg {input : List Bool} (emb : S → H) (ret : H)
    (pre out₀ : List Bool) (c : Cfg k Bool S input) :
    Cfg (k + 1) Bool H input where
  state := some ((c.state.map emb).getD ret)
  inputPos := c.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < k then c.workTapes ⟨i, h⟩
    else FinTM.bufferTape (pre ++ c.output)
  workTapePos := fun i =>
    if h : (i : ℕ) < k then c.workTapePos ⟨i, h⟩
    else ((pre ++ c.output).length : ℤ)
  output := out₀

/-- Applying a captured action preserves the source fields and appends its
optional emission to the buffer. The write uses the old head before moving.
**Proof sketch.** Split the tape index at the source tape count. Source tapes
are unchanged by the embedding; on the final tape use `bufferTape_append`
for an emission and the stationary no-write action otherwise. -/
private lemma capture_apply {input : List Bool} (emb : S → H) (ret : H)
    (pre out₀ : List Bool) (c : Cfg k Bool S input) (a : Action k Bool S) :
    (captureAction emb ret a).apply (captureCfg emb ret pre out₀ c) =
      captureCfg emb ret pre out₀ (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp [captureAction, captureCfg, Action.apply, hi]
    · cases ho : a.output <;>
        simp [captureAction, captureCfg, Action.apply, hi, ho,
          ← List.append_assoc, FinTM.bufferTape_append]
  · funext i
    by_cases hi : (i : ℕ) < k
    · simp [captureAction, captureCfg, Action.apply, hi]
    · cases ho : a.output <;>
        simp [captureAction, captureCfg, Action.apply, hi, ho, Nat.cast_add,
          add_assoc]
  · simp [captureAction, captureCfg, Action.apply]

/-- **W1, the capture contract** (spec, fill pending — harvested from the
four private incarnations). If a host machine's transition table agrees, on
an embedded copy of the source's states, with the capture-transformed
source table, then the host run from a capture configuration *is* the
capture image of the source run, for as long as the source has not halted
before the time in question. Taking `t` to be the source's halting time
instantiates the return clause: the host sits at `ret` with the completed
source configuration preserved, the full source output (halting emission
included) on the capture tape, and the host output still `out₀`; taking
`t` below it gives live lockstep.

**Proof sketch.** Induction on `t`. One host step from a live capture image
applies the transformed action: the first `k` tapes and the input head
update exactly as the source's (`Turing.Action.apply` componentwise); the
capture tape appends the emitted bit, which is
`Turing.FinTM.bufferTape_append` at head `|pre ++ c.output|`; silence keeps
the host output at `out₀`; and the successor state is the embedded source
successor, or `ret` on the halting transition. -/
theorem capture_run {input : List Bool} (tm : MultiTapeTM k Bool S)
    (host : MultiTapeTM (k + 1) Bool H) (emb : S → H) (ret : H)
    (hagree : ∀ (s : S) (inp : Option Bool) (w : Fin (k + 1) → Option Bool),
      host.tr (emb s) inp w =
        captureAction emb ret (tm.tr s inp fun i => w i.castSucc))
    (pre out₀ : List Bool) (c₀ : Cfg k Bool S input) (t : ℕ)
    (hlive : ∀ t' < t, ¬(tm.runFrom c₀ t').Halted) :
    host.runFrom (captureCfg emb ret pre out₀ c₀) t =
      captureCfg emb ret pre out₀ (tm.runFrom c₀ t) := by
  have hstep (c : Cfg k Bool S input) (hs : ¬c.Halted) :
      host.step (captureCfg emb ret pre out₀ c) =
        captureCfg emb ret pre out₀ (tm.step c) := by
    cases hq : c.state with
    | none => exact False.elim (hs hq)
    | some q =>
      have hstate : (captureCfg emb ret pre out₀ c).state = some (emb q) := by
        simp [captureCfg, hq]
      have hinput : (captureCfg emb ret pre out₀ c).inputSymbol = c.inputSymbol := rfl
      have hwork : (fun i => (captureCfg emb ret pre out₀ c).workTapeSymbols
          i.castSucc) = c.workTapeSymbols := by
        funext i
        simp [captureCfg, Cfg.workTapeSymbols, i.isLt]
      simp only [MultiTapeTM.step, hstate, hq]
      rw [hagree, hinput, hwork]
      exact capture_apply emb ret pre out₀ c _
  -- The guard supplies a genuine source step, including at the final halt.
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => hlive s (by omega)),
      hstep _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- **E2 action transformer** (design §11): the forwarding dual
of `Turing.captureAction`. Transform one source action into a host action
over the **same** tapes: input move and work-tape actions are kept
verbatim; the source's emission, **if any, is forwarded as the host's
physical emission** — including an emission on the halting transition; a
live source successor is embedded via `emb`, and a halting source action
transfers control to the designated live return state `ret`. This is what
lets a proved transducer serve as one emission stage of a larger host.
Customers: the forwarding loop-host variant behind `exists_emitLoopTM`,
and `exists_emitCallTM`'s module. Construction: a record map, no
machine content. -/
def emitAction (emb : S → H) (ret : H) (a : Action k Bool S) :
    Action k Bool H where
  inputTape := a.inputTape
  workTapes := a.workTapes
  output := a.output
  state := some ((a.state.map emb).getD ret)

/-- **E2 configuration correspondence** (design §11): a source
configuration `c`, viewed inside the host — state embedded (a halted source
appears at the live return state `ret`), tapes, heads, and input position
verbatim, and the host's physical output equal to the host's prior output
`pre` followed by everything the source has emitted. It deliberately does
**not** normalize the source's terminal tapes or heads: clean returns are
the separate bridge contracts' job (`exists_installCallTM`,
`exists_emitCallTM` — emitter-infra round-1 audit, finding 1). Customers:
`emit_run`'s statement and the bridge fills. Construction: a record map,
no machine content. -/
def emitCfg {input : List Bool} (emb : S → H) (ret : H)
    (pre : List Bool) (c : Cfg k Bool S input) :
    Cfg k Bool H input where
  state := some ((c.state.map emb).getD ret)
  inputPos := c.inputPos
  workTapes := c.workTapes
  workTapePos := c.workTapePos
  output := pre ++ c.output

/-- Applying a forwarded action preserves the source fields and appends its
optional emission after the host prefix, including when that action halts.
**Proof sketch.** The state, input head, work tapes, and work heads agree
definitionally; the physical output equality is append associativity. -/
private lemma emit_apply {input : List Bool} (emb : S → H) (ret : H)
    (pre : List Bool) (c : Cfg k Bool S input) (a : Action k Bool S) :
    (emitAction emb ret a).apply (emitCfg emb ret pre c) =
      emitCfg emb ret pre (a.apply c) := by
  refine Cfg.ext rfl rfl rfl rfl ?_
  exact List.append_assoc pre c.output a.output.toList

/-- **E2, the forwarding wrapper** (spec, fill pending — design §11;
customers: the emitting loop's per-round chunk calls, the Cook-Levin
clause-group emission (4A), 3B-cont's fresh-literal chains). Any host
machine agreeing with the transformed table on an embedded copy of the
source states runs the source in lockstep while **appending the source's
output to the host's physical output**, the exact dual of
`Turing.capture_run`: source tapes verbatim, the halting transition's
emission forwarded like any other, and the host landing in the live
return state at the source's halt.

**Construction sketch.** Mirror `capture_run`: one `emitAction`-apply
lemma (source fields preserved; the optional emission appended to the
host output after `pre`), then induction over the guarded run, the guard
supplying a genuine source step including at the final halt. -/
theorem emit_run {input : List Bool} (tm : MultiTapeTM k Bool S)
    (host : MultiTapeTM k Bool H) (emb : S → H) (ret : H)
    (hagree : ∀ (s : S) (inp : Option Bool) (w : Fin k → Option Bool),
      host.tr (emb s) inp w = emitAction emb ret (tm.tr s inp w))
    (pre : List Bool) (c₀ : Cfg k Bool S input) (t : ℕ)
    (hlive : ∀ t' < t, ¬(tm.runFrom c₀ t').Halted) :
    host.runFrom (emitCfg emb ret pre c₀) t =
      emitCfg emb ret pre (tm.runFrom c₀ t) := by
  have hstep (c : Cfg k Bool S input) (hs : ¬c.Halted) :
      host.step (emitCfg emb ret pre c) =
        emitCfg emb ret pre (tm.step c) := by
    cases hq : c.state with
    | none => exact False.elim (hs hq)
    | some q =>
      have hstate : (emitCfg emb ret pre c).state = some (emb q) := by
        simp [emitCfg, hq]
      have hinput : (emitCfg emb ret pre c).inputSymbol = c.inputSymbol := rfl
      have hwork : (emitCfg emb ret pre c).workTapeSymbols = c.workTapeSymbols := rfl
      simp only [MultiTapeTM.step, hstate, hq]
      rw [hagree, hinput, hwork]
      exact emit_apply emb ret pre c _
  -- The guard supplies a genuine source step, including at the final halt.
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => hlive s (by omega)),
      hstep _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

end Turing

namespace Turing.FinTM

/-- W2 transformation: the `acceptTM` control-modification pattern. Simulate
`M` with its output suppressed while a finite register remembers the **last**
emitted bit (`none` before any emission) — updated *before* the halt test, so
a bit emitted on the halting transition counts. When the source halts, halt
if the remembered bit is `haltOn`; otherwise enter the one-state stationary
live loop. Tape count unchanged. -/
def redirectTM (M : FinTM Bool) (haltOn : Bool) : FinTM Bool where
  k := M.k
  State := (M.State × Option Bool) ⊕ Unit
  tm :=
    { q₀ := Sum.inl (M.tm.q₀, none)
      tr := fun q inp work =>
        match q with
        | Sum.inl (s, r) =>
          let a := M.tm.tr s inp work
          let r' := match a.output with
            | some b => some b
            | none => r
          { inputTape := a.inputTape
            workTapes := a.workTapes
            output := none
            state := match a.state with
              | some s' => some (Sum.inl (s', r'))
              | none => if r' = some haltOn then none else some (Sum.inr ()) }
        | Sum.inr () =>
          { inputTape := SignType.zero
            workTapes := fun _ => (none, SignType.zero)
            output := none
            state := some (Sum.inr ()) } }

/-- Map a source state and its last-emission register to simulation, halt,
or the stationary live loop. An empty register never matches a bit. -/
private def redirectState {S : Type} (haltOn : Bool) (q : Option S)
    (r : Option Bool) : Option ((S × Option Bool) ⊕ Unit) :=
  match q with
  | some s => some (.inl (s, r))
  | none => if r = some haltOn then none else some (.inr ())

/-- Suppress physical emission, updating the register before the halt test. -/
private def redirectAction {k : ℕ} {S : Type} (haltOn : Bool)
    (a : Action k Bool S) (r : Option Bool) : Action k Bool ((S × Option Bool) ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, none, redirectState haltOn a.state (a.output.or r)⟩

/-- The source tapes and input head are unchanged; its last emitted bit is
remembered in control and the physical output is empty. -/
private def redirectCfg (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) : Cfg (redirectTM M haltOn).k Bool
      (redirectTM M haltOn).State x :=
  ⟨redirectState haltOn c.state c.output.getLast?, c.inputPos,
    c.workTapes, c.workTapePos, []⟩

/-- The stationary live loop is fixed by every subsequent transition. -/
private lemma redirect_loop (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg (redirectTM M haltOn).k Bool (redirectTM M haltOn).State x)
    (hs : c.state = some (.inr ())) (t : ℕ) :
    (redirectTM M haltOn).tm.runFrom c t = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
    apply Cfg.ext <;> simp [MultiTapeTM.step, hs, redirectTM, Action.apply]

/-- Capture and application commute because the last entry of an appended
singleton is the new bit, while no emission leaves the old register intact. -/
private lemma redirect_apply (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) (a : Action M.k Bool M.State) :
    (redirectAction haltOn a c.output.getLast?).apply (redirectCfg M haltOn c) =
      redirectCfg M haltOn (a.apply c) := by
  have hlast : (c.output ++ a.output.toList).getLast? = a.output.or c.output.getLast? := by
    cases a.output <;> simp
  refine Cfg.ext ?_ rfl rfl rfl rfl
  dsimp only [redirectCfg, redirectAction, Action.apply]
  rw [hlast]

/-- The correspondence also holds after a source halt: a matching result
is absorbed as halted, and a mismatching result is absorbed in the live loop.
This adapts `acceptCfg_step` in the HALT reduction to an optional register. -/
private lemma redirect_step (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
    (c : Cfg M.k Bool M.State x) :
    (redirectTM M haltOn).tm.step (redirectCfg M haltOn c) =
      redirectCfg M haltOn (M.tm.step c) := by
  cases hs : c.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs]
    by_cases hr : c.output.getLast? = some haltOn
    · exact MultiTapeTM.step_of_halt (by simp [redirectCfg, redirectState, hs, hr])
    · exact redirect_loop M haltOn (redirectCfg M haltOn c)
        (by simp [redirectCfg, redirectState, hs, hr]) 1
  | some q =>
    have hi : (redirectCfg M haltOn c).inputSymbol = c.inputSymbol := rfl
    have hw : (redirectCfg M haltOn c).workTapeSymbols = c.workTapeSymbols := rfl
    have hstate : (redirectCfg M haltOn c).state = some (.inl (q, c.output.getLast?)) := by
      simp only [redirectCfg, redirectState, hs]
    simp only [MultiTapeTM.step, hstate, hs]
    rw [hi, hw]
    have htr : (redirectTM M haltOn).tm.tr (.inl (q, c.output.getLast?))
        c.inputSymbol c.workTapeSymbols =
        redirectAction haltOn (M.tm.tr q c.inputSymbol c.workTapeSymbols) c.output.getLast? := by
      cases hq : (M.tm.tr q c.inputSymbol c.workTapeSymbols).state <;>
        cases ho : (M.tm.tr q c.inputSymbol c.workTapeSymbols).output <;>
          simp [redirectTM, redirectAction, redirectState, hq, ho]
    rw [htr]
    exact redirect_apply M haltOn c _

/-- Initialized runs commute with redirection at every time, including
after a source halt. This is the last-emission invariant for both clauses. -/
private lemma redirect_run (M : FinTM Bool) (haltOn : Bool) (x : List Bool) (t : ℕ) :
    (redirectTM M haltOn).tm.runFrom ((redirectTM M haltOn).tm.initCfg x) t =
      redirectCfg M haltOn (M.tm.runFrom (M.tm.initCfg x) t) := by
  have hi : (redirectTM M haltOn).tm.initCfg x = redirectCfg M haltOn (M.tm.initCfg x) := rfl
  rw [hi]
  exact MultiTapeTM.runFrom_comm_of_step (redirectCfg M haltOn) (redirect_step M haltOn)
    (M.tm.initCfg x) t

/-- **W2, the halting clause** (spec, fill pending — harvested from the
HALT batch's `acceptTM_halts_iff`). If `M` completes output `w` on `x`
within `t` steps and the last bit of `w` is the designated bit, the
redirected machine halts on `x` within the same budget with **empty**
output (everything was suppressed).

**Proof sketch.** Lockstep correspondence between `M`'s run and the
redirected run, carrying "register = last emitted bit so far"; at `M`'s
halting transition the register equals `w`'s last bit, so the redirect
halts there. -/
theorem redirectTM_computes {M : FinTM Bool} {haltOn : Bool}
    {x w : List Bool} {t : ℕ} (hM : M.ComputesInTime x w t)
    (hlast : w.getLast? = some haltOn) :
    (redirectTM M haltOn).ComputesInTime x [] t := by
  obtain ⟨hs, hout⟩ := (computesInTime_iff M x w t).mp hM
  apply (computesInTime_iff _ x [] t).mpr
  rw [redirect_run]
  exact ⟨by simp only [redirectCfg, hs, hout, redirectState, hlast, ite_true], rfl⟩

/-- **W2, the live clause** (spec, fill pending). If `M` completes output
`w` on `x` and `w`'s last bit is *not* the designated bit (in particular if
`w = []`), the redirected machine never halts on `x`: at the source's
halting transition it enters the stationary live loop, which is fixed under
every further step.

**Proof sketch.** Lockstep with the register invariant (register = last
emission so far) up to the source's halting transition; there the register
differs from the designated bit, so control enters the stationary live
state, which every further step fixes (two-line induction). -/
theorem redirectTM_live {M : FinTM Bool} {haltOn : Bool}
    {x w : List Bool} {t : ℕ} (hM : M.ComputesInTime x w t)
    (hlast : w.getLast? ≠ some haltOn) :
    ∀ u : ℕ, ¬((redirectTM M haltOn).tm.runFrom
      ((redirectTM M haltOn).tm.initCfg x) u).Halted := by
  intro u hhalt
  rw [redirect_run] at hhalt
  change redirectState haltOn (M.tm.runFrom (M.tm.initCfg x) u).state
    (M.tm.runFrom (M.tm.initCfg x) u).output.getLast? = none at hhalt
  -- A redirected halt forces a genuine source halt with the matching register.
  have hs : (M.tm.runFrom (M.tm.initCfg x) u).state = none := by
    cases h : (M.tm.runFrom (M.tm.initCfg x) u).state with
    | none => rfl
    | some q => simp only [redirectState, h, reduceCtorEq] at hhalt
  have hc : M.ComputesInTime x (M.tm.runFrom (M.tm.initCfg x) u).output u :=
    (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have hout := hc.output_unique hM
  rw [hs, hout] at hhalt
  simp only [redirectState, if_neg hlast, Option.some_ne_none] at hhalt

/-- Pad the decider with the fresh branch tapes. The added tapes are idle,
so the public left-block simulation supplies its complete run invariant. -/
private def timedPadTM (D : FinTM Bool) (r : ℕ) : MultiTapeTM (D.k + r) Bool D.State where
  q₀ := D.tm.q₀
  tr q inp work := leftAction r id (D.tm.tr q inp (fun i => work (Fin.castAdd r i)))

/-- The conditional controller captures the decider on the last tape,
steps back to read its singleton verdict, rewinds the physical input, then
runs the selected branch on its untouched tape bank. In the administrative
states, the first Boolean distinguishes back/read and the second distinguishes
rewind-start/scan. The branch transition table is independent of its selector. -/
private def timedCondTM (D M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := (D.k + (M₁.k + M₂.k)) + 1
  State := D.State ⊕ (Bool ⊕ ((Bool × Bool) ⊕ (M₁.State ⊕ M₂.State)))
  tm :=
    { q₀ := .inl D.tm.q₀
      tr := fun q inp work => match q with
        | .inl q => captureAction Sum.inl (.inr (.inl false))
            ((timedPadTM D (M₁.k + M₂.k)).tr q inp (fun i => work i.castSucc))
        | .inr (.inl false) =>
          ⟨0, (fun i => if (i : ℕ) < D.k + (M₁.k + M₂.k) then (none, 0)
            else (none, .neg)), none, some (.inr (.inl true))⟩
        | .inr (.inl true) => controlAction 0
            (some (.inr (.inr (.inl ((work (Fin.last _)).getD false, false)))))
        | .inr (.inr (.inl (b, false))) =>
            controlAction .neg (some (.inr (.inr (.inl (b, true)))))
        | .inr (.inr (.inl (b, true))) => match inp with
          | some _ => controlAction .neg (some (.inr (.inr (.inl (b, true)))))
          | none => controlAction .pos
              (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
        | .inr (.inr (.inr q)) => leftAction 1 id
            (rightAction D.k (fun s => .inr (.inr (.inr s)))
              ((branchTM M₁ M₂ false).tm.tr q inp
                (fun i => work (Fin.natAdd D.k i).castSucc))) }

/-- The branch configuration retains the decider's finished work and the
captured verdict; its own state, input head, work tapes, and output are exact. -/
private def timedBranchCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) :
    Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x :=
  leftCfg id (rightCfg (fun s => .inr (.inr (.inr s))) c tapes heads)
    (fun (_ : Fin 1) => bufferTape [b]) (fun _ => 0)

/-- The decider's configuration inside its padded, captured simulation.
Both branch tape banks are blank throughout this phase. -/
private def timedControlCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) :
    Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x :=
  captureCfg Sum.inl (.inr (.inl false)) [] []
    (leftCfg id c (fun (_ : Fin (M₁.k + M₂.k)) _ => none) (fun _ => 0))

/-- The capture contract, instantiated on the padded decider, gives the
entire controller phase through its first halt. -/
private lemma timed_capture (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (t : ℕ)
    (hlive : ∀ s < t, ¬(D.tm.runFrom c s).Halted) :
    (timedCondTM D M₁ M₂).tm.runFrom (timedControlCfg D M₁ M₂ c) t =
      timedControlCfg D M₁ M₂ (D.tm.runFrom c t) := by
  have hpad (u : ℕ) := leftCfg_run D.tm (timedPadTM D (M₁.k + M₂.k)) id
    (fun _ _ _ => rfl) c (fun _ _ => none) (fun _ => 0) u
  have h := capture_run (timedPadTM D (M₁.k + M₂.k)) (timedCondTM D M₁ M₂).tm
    Sum.inl (.inr (.inl false)) (fun _ _ _ => rfl) [] []
    (leftCfg id c (fun _ _ => none) (fun _ => 0)) t (fun s hs => by
      unfold Cfg.Halted
      rw [hpad s]
      simpa only [leftCfg, Option.map_id] using hlive s hs)
  simpa only [hpad t] using h

/-- The host's genuine initial configuration is the captured, padded
initial configuration: all three work-tape blocks are blank. -/
private lemma timed_control_init (D M₁ M₂ : FinTM Bool) (x : List Bool) :
    (timedCondTM D M₁ M₂).tm.initCfg x =
      timedControlCfg D M₁ M₂ (D.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases hi : (i : ℕ) < D.k + (M₁.k + M₂.k)
    · simp only [timedControlCfg, captureCfg, leftCfg, MultiTapeTM.initCfg,
        Cfg.init, dif_pos hi]
      exact (Fin.addCases (fun _ => by simp) (fun _ => by simp) ⟨i, hi⟩)
    · simp [timedControlCfg, captureCfg, leftCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) < D.k + (M₁.k + M₂.k)
    · simp only [timedControlCfg, captureCfg, leftCfg, MultiTapeTM.initCfg,
        Cfg.init, dif_pos hi]
      exact (Fin.addCases (fun _ => by simp) (fun _ => by simp) ⟨i, hi⟩)
    · simp [timedControlCfg, captureCfg, leftCfg, hi]

/-- Once dispatched, the selected branch runs in lockstep while the old
decider tapes and singleton capture tape remain idle.
**Proof sketch.** The branch action is a right-block embedding followed by
a left-block embedding; compose their application lemmas, then iterate. -/
private lemma timed_branch_run (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg (M₁.k + M₂.k) Bool (M₁.State ⊕ M₂.State) x)
    (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ) (b : Bool) (t : ℕ) :
    (timedCondTM D M₁ M₂).tm.runFrom (timedBranchCfg D M₁ M₂ c tapes heads b) t =
      timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.runFrom c t) tapes heads b := by
  apply MultiTapeTM.runFrom_comm_of_step (fun c => timedBranchCfg D M₁ M₂ c tapes heads b)
  intro d
  cases hs : d.state with
  | none =>
    simp only [MultiTapeTM.step, timedBranchCfg, leftCfg, rightCfg, hs, Option.map_none]
  | some q =>
    have hstate : (timedBranchCfg D M₁ M₂ d tapes heads b).state =
        some (.inr (.inr (.inr q))) := by
      simp only [timedBranchCfg, leftCfg, rightCfg, hs, Option.map_some, id_eq]
    have hi : (timedBranchCfg D M₁ M₂ d tapes heads b).inputSymbol = d.inputSymbol := rfl
    have hw : (fun i => (timedBranchCfg D M₁ M₂ d tapes heads b).workTapeSymbols
        (Fin.natAdd D.k i).castSucc) = d.workTapeSymbols := by
      funext i
      simp only [timedBranchCfg, leftCfg, rightCfg, Cfg.workTapeSymbols,
        Fin.castSucc, Fin.addCases_left, Fin.addCases_right]
    simp only [MultiTapeTM.step, hstate, hs]
    dsimp only [timedCondTM]
    let emb : (M₁.State ⊕ M₂.State) → (timedCondTM D M₁ M₂).State :=
      fun s => .inr (.inr (.inr s))
    change (leftAction 1 id (rightAction D.k emb
      ((branchTM M₁ M₂ b).tm.tr q d.inputSymbol
        (fun i => (timedBranchCfg D M₁ M₂ d tapes heads b).workTapeSymbols
          (Fin.natAdd D.k i).castSucc)))).apply
        (leftCfg id (rightCfg emb d tapes heads)
          (fun (_ : Fin 1) => bufferTape [b]) (fun _ => 0)) = _
    erw [hw, leftCfg_apply, rightCfg_apply]
    rfl

/-- After reading the verdict, all branch data are initialized; only the
input head still needs rewinding. The capture head is back at cell zero. -/
private def timedReadyCfg (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) :
    Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x :=
  { timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) c.workTapes c.workTapePos b with
    state := some (.inr (.inr (.inl (b, false))))
    inputPos := c.inputPos }

/-- Two silent transitions move the capture head left and read the completed
singleton verdict, without touching the input or either work bank.
**Proof sketch.** The final capture head is one past the singleton, hence at
one. Moving it left exposes exactly its bit at zero; the next transition
records that bit in the rewind state. -/
private lemma timed_read (D M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg D.k Bool D.State x) (b : Bool) (hs : c.state = none) (ho : c.output = [b]) :
    (timedCondTM D M₁ M₂).tm.runFrom (timedControlCfg D M₁ M₂ c) 2 =
      timedReadyCfg D M₁ M₂ c b := by
  let ready := timedReadyCfg D M₁ M₂ c b
  have hback : (timedCondTM D M₁ M₂).tm.step (timedControlCfg D M₁ M₂ c) =
      {ready with state := some (.inr (.inl true))} := by
    have hstate : (timedControlCfg D M₁ M₂ c).state = some (.inr (.inl false)) := by
      simp [timedControlCfg, captureCfg, leftCfg, hs]
    simp only [MultiTapeTM.step, hstate]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [timedCondTM, Action.apply, timedControlCfg, captureCfg, leftCfg,
          timedReadyCfg, timedBranchCfg, rightCfg, ready, j.isLt]
        refine Fin.addCases ?_ ?_ j <;> intro z <;> simp
      · intro j
        simp [timedCondTM, Action.apply, timedControlCfg, captureCfg, leftCfg,
          timedReadyCfg, timedBranchCfg, rightCfg, ready, ho]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [timedCondTM, Action.apply, timedControlCfg, captureCfg, leftCfg,
          timedReadyCfg, timedBranchCfg, rightCfg, ready, j.isLt]
        refine Fin.addCases ?_ ?_ j <;> intro z <;> simp
      · intro j
        simp [timedCondTM, Action.apply, timedControlCfg, captureCfg, leftCfg,
          timedReadyCfg, timedBranchCfg, rightCfg, ready, ho]
  have hread : (timedCondTM D M₁ M₂).tm.step
      {ready with state := some (.inr (.inl true))} = ready := by
    have hsym : ({ready with state := some (.inr (.inl true))} :
        Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x).workTapeSymbols
        (Fin.last _) = some b := by
      change (timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x)
        c.workTapes c.workTapePos b).workTapeSymbols
          (Fin.natAdd (D.k + (M₁.k + M₂.k)) (0 : Fin 1)) = some b
      simp [timedBranchCfg, leftCfg, rightCfg, Cfg.workTapeSymbols, bufferTape]
    unfold MultiTapeTM.step
    dsimp only
    change ((controlAction 0 (some (.inr (.inr (.inl
      ((({ready with state := some (.inr (.inl true))} :
        Cfg (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State x).workTapeSymbols
        (Fin.last _)).getD false, false)))))) :
          Action (timedCondTM D M₁ M₂).k Bool (timedCondTM D M₁ M₂).State).apply _ = _
    rw [hsym, controlAction_apply]
    simp only [Option.getD_some, moveInputPos_zero]
    rfl
  change (timedCondTM D M₁ M₂).tm.step
    ((timedCondTM D M₁ M₂).tm.step (timedControlCfg D M₁ M₂ c)) = _
  rw [hback, hread]

/-- A singleton-output decider reaches the selected branch's genuine
initial configuration in at most twice its budget plus five steps.
**Proof sketch.** Choose the first source halt, which is within the supplied
budget. Capture until that halt, read the singleton in two steps, and rewind
in at most the current input position plus two. The head-position bound
charges this rewind to the decider's elapsed steps, not the input length. -/
private lemma timed_start (D M₁ M₂ : FinTM Bool) (x : List Bool) (b : Bool) (T : ℕ)
    (hD : D.ComputesInTime x [b] T) :
    ∃ a ≤ 2 * T + 5, ∃ (tapes : Fin D.k → ℤ → Option Bool) (heads : Fin D.k → ℤ),
      (timedCondTM D M₁ M₂).tm.runFrom ((timedCondTM D M₁ M₂).tm.initCfg x) a =
        timedBranchCfg D M₁ M₂ ((branchTM M₁ M₂ b).tm.initCfg x) tapes heads b := by
  classical
  have hh : ∃ t, (D.tm.runFrom (D.tm.initCfg x) t).state = none :=
    ⟨T, ((computesInTime_iff _ _ _ _).mp hD).1⟩
  let t := Nat.find hh
  let c := D.tm.runFrom (D.tm.initCfg x) t
  have ht : t ≤ T := Nat.find_min' hh ((computesInTime_iff _ _ _ _).mp hD).1
  have hs : c.state = none := Nat.find_spec hh
  have hc : D.ComputesInTime x c.output t := (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = [b] := hc.output_unique hD
  have hcap : (timedCondTM D M₁ M₂).tm.runFrom ((timedCondTM D M₁ M₂).tm.initCfg x) t =
      timedControlCfg D M₁ M₂ c := by
    rw [timed_control_init]
    exact timed_capture D M₁ M₂ _ t (fun s hst => Nat.find_min hh hst)
  obtain ⟨r, hrle, hr⟩ := timed_rewind (timedCondTM D M₁ M₂).tm
    (.inr (.inr (.inl (b, false)))) (.inr (.inr (.inl (b, true))))
    (some (.inr (.inr (.inr (branchTM M₁ M₂ b).tm.q₀))))
    (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl)
    (timedReadyCfg D M₁ M₂ c b) rfl
  refine ⟨t + 2 + r, ?_, c.workTapes, c.workTapePos, ?_⟩
  · have hp : c.inputPos.val ≤ 1 + t := by
      simpa only [MultiTapeTM.initCfg, Cfg.init, Fin.val_one] using
        MultiTapeTM.timed_input_bound (tm := D.tm) (D.tm.initCfg x) t
    change r ≤ c.inputPos.val + 2 at hrle
    omega
  · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hcap,
      timed_read D M₁ M₂ c b hs ho, hr]
    rfl

/-- **W3, the timed branch** (spec, fill pending): the quantitative form of
`Turing.FinTM.exists_cond`. If a decider machine computes the test bit
within `T₀` and each branch computes its function within `T₁`, `T₂`, the
conditional function is computable within a constant multiple of
`T₀ + max T₁ T₂ + 1`. No monotonicity hypothesis: the selected branch runs
on the *same* physical input.

**Proof sketch.** Run the decider through the W1 capture discipline (its
verdict on the capture tape, physical output silent), rewind per the
`Turing.FinTM.rewind_from_any` scan, then dispatch on the captured bit into
the two-machine branch union (`Turing.FinTM.branchTM`), which runs the
selected branch from its genuine initial configuration on the shared input.
Constant overhead per phase is absorbed into `c`. -/
theorem computesFunInTime_cond {D M₁ M₂ : FinTM Bool} {p : List Bool → Bool}
    {f₁ f₂ : List Bool → List Bool} {T₀ T₁ T₂ : ℕ → ℕ}
    (hD : D.ComputesFunInTime (fun x => [p x]) T₀)
    (h₁ : M₁.ComputesFunInTime f₁ T₁) (h₂ : M₂.ComputesFunInTime f₂ T₂) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => if p x then f₁ x else f₂ x)
        (fun n => c * (T₀ n + max (T₁ n) (T₂ n) + 1)) := by
  refine ⟨timedCondTM D M₁ M₂, 5, fun x => ?_⟩
  let B := max (T₁ x.length) (T₂ x.length)
  have hb : (branchTM M₁ M₂ (p x)).ComputesInTime x
      (if p x then f₁ x else f₂ x) B := by
    apply (branchTM_computes M₁ M₂ (p x) x _ B).mpr
    cases hp : p x with
    | false => exact (h₂ x).mono (Nat.le_max_right _ _)
    | true => exact (h₁ x).mono (Nat.le_max_left _ _)
  obtain ⟨a, ha, tapes, heads, hstart⟩ :=
    timed_start D M₁ M₂ x (p x) (T₀ x.length) (hD x)
  have hc : (timedCondTM D M₁ M₂).ComputesInTime x
      (if p x then f₁ x else f₂ x) (a + B) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, timed_branch_run]
    obtain ⟨hs, ho⟩ := (computesInTime_iff _ _ _ _).mp hb
    exact ⟨by simpa only [timedBranchCfg, leftCfg, rightCfg, Option.map_eq_none_iff] using hs, ho⟩
  -- The controller prefix and selected branch fit one uniform coefficient.
  apply hc.mono
  dsimp only [B] at *
  omega

end Turing.FinTM
```
