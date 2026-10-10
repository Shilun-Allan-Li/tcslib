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
| **A-S2 statement gate CLOSED** (round 3, 2026-10-09: **PASS, 0 blockers / 0 majors / 1 minor** — `audits/zone-infra-r3-findings.md` verbatim; loop summary `audits/zone-infra-resolutions.md`). The amended cascade contracts and both regressions verified true as literally stated — the auditor supplied the complete two-pass induction, the necessity and classical-invariant arguments, six boundary traces (incl. the intended word/length hypothesis separation and the repaired former dead end), and ~74,500 finite-model instances. Minor swept: the round-3 pack's inventory erratum acknowledged — **the auditor's counts are canonical** (Zone 20 sorried / 24 terms / 38 explicit; tranche 25 sorried / 29 terms / 50 explicit). All auditor analyses and grammar numbers adopted as binding fill routes; sanity exports offered as optional permanent lemmas. **Three-round lesson recorded**: both blockers were maintainer hypothesis omissions on data-moving contracts — the pre-ship boundary check ("what breaks at full/empty without each hypothesis?") is now mandatory maintainer practice for every spec layer | Recorded |
| **Retrofit-R1 round 3: R2-2/R2-3 CLOSED (the RB4 acknowledgment accepted); gate held on ledger completeness; reconciliation COMPLETED** (2026-10-09: **0 blockers / 1 major / 2 minors / 5 notes** — `audits/retrofit-r1-r3-findings.md` verbatim). R3-1: the Catalog row missed the ledger's own union rule — the 2 in-file originals, the 3 declared Composition copies, and the 20-member counter block. **Maintainer reconciliation, declaration by declaration with normalized comparison**: 19 counter members identical to `TimeConstructible.lean`'s originals, `f2_counter_computes` a near-copy of `timeConstructible_id`'s proof body, the 3 Composition copies identical; the remaining 29 F2A entries confirmed as new space material, not copies. **Catalog: 289/423 = 68.3%** (strict 283 = 66.9%); new original-side rows `TimeConstructible.lean` 20/21 and `Composition.lean` 3/19; Wrappers lines corrected to the auditor's 297. Minors: the A2 report attached in round 4; the span-rule estimate replaced. **Round-4 pack out** with the three sources attached for independent reproduction | Recorded |
| **A-S1 fill gate CLOSED — tranche A-S1 COMPLETE end to end** (round 1, 2026-10-09: **PASS, 0 blockers / 0 majors / 1 minor**, no debt finding — `audits/vhost-f1-findings.md` verbatim; loop summary `audits/vhost-f1-resolutions.md`). The auditor re-derived `vhostSilent_layout`'s partition arithmetic, checked all eleven proofs body-by-body against the binding routes (pointwise visited equalities, coefficient-one sums, the two silent contracts as pure two-layer citations, the strict-prefix agreement guards), verified both declared techniques benign (the `Unit` mapping definitionally inert; both `sum_bij` partitions surjective), and re-established the freeze with reverse/forward blob reconstruction isolating the header refresh as doc-only. Minor swept: pack line-count erratum (delivery 506 / post-refresh 508). **Z1 + Z5 are proved public infrastructure; the RB4 window ("after the A-S1 fill gate closes") is now OPEN.** Duplicate re-downloads of the zone-r3 and retrofit-r1-r3 findings verified byte-identical and removed | Recorded |
| **A-S2 fill briefs + RB4 brief issued; ARM proposal page published** (2026-10-09, base `8f13d74e`): `briefs/zone-f1-batch{A,B,C}.md` — ZF-A (`Zone.lean`, 20 targets incl. the two shift-machine rows; the three rounds' inductions, layout arithmetic, and machine-row implementation notes embedded verbatim as binding routes), ZF-B (`Codes2Tape.lean`, 2 scheme builds; the grammar numbers binding — record 13, guard `351·(n+1)`, min 354; axiom discipline bars any route through `NDCodes`'s sorried existence), ZF-C (the Z4 trio; the `sweepTM` refutation kept as a binding regression, the demand-grown witness + retraction route embedded; the reuse-not-copy screen explicit). `briefs/retrofit-rb4.md` — the acknowledged debt discharge (H3 via Z5; the three-file relocation family via the rider exports + Z5 under the vhost audit's transport-first composition plan; one disclosed local copy at most; side-branch + PR integration). All four batches file-disjoint and parallel; deliveries `zone-f1-{A,B,C}.zip`, `retrofit-rb4.zip`. **`arm-extensions-proposal.md`** added at the repo root — the colleague-facing sync page for Jason (the three extensions, the `CounterProg` input question, the two provenance questions) | Recorded |
| **Retrofit-R1 round 4: the reconciliation VERIFIED; two public correspondences found; the screen completed** (2026-10-09: **0 blockers / 1 major / 2 minors / 7 notes** — `audits/retrofit-r1-r4-findings.md` verbatim). Closed: R3-1's named omissions, R3-2 (the A2 report reconciled: 45 = 2 + 1 + 42), the Wrappers estimate. Open: **R4-1** — `computesFunInTime_id`/`_const`'s Composition time proofs are reproduced verbatim inside Catalog's `_spaceUsed` time conjuncts; the census must include them and the remaining public targets must be screened. **Maintainer screen executed** (normalized containment, ≥60-char segments, method in the ledger): exactly the auditor's two hits; **all 16 screened Primitives rows distinct**. Ledger finalized: **Catalog 291/423 = 68.8% expanded / 283 = 66.9% strict; Composition 5/19 = 26.3%; TimeConstructible 20/21** with the round-4 measured spans throughout (expanded union 6,267 lines) and the R4-2 decomposition fix (306 = 150+94+10+3+20+2+27; the acknowledgment label 264 → 291). **Round-5 pack out** with the four sources attached for screen reproduction | Recorded |
| **PR #11 merged: the a-gupte ch7 tree + shared block-query P-closure join the campaign branch** (user decisions 2026-10-10). Cross-fork coordination PR from `a-gupte:complexity/arora-barak-ch7` (head `d4503768`), both branches forked from the same main commit `4aea7cfd` — the merge imports zero main commits and touches no campaign-owned file (purely additive; the one conflict, the `TuringMachine.lean` facade doc bullet, resolved by union). Pre-merge screens: new-public-name intersection across the two branches EMPTY (215 vs 319); the loop hosts ch7 consumes (`exists_emitLoopTM`/`exists_emitCallTM`/`exists_installCallTM`) statement-identical between main and this branch post-retrofit; no unexpected files. **Decisions**: (1) ch7 lives on this branch so the modular TM/circuit infra evolves in one place; (2) the `PClosure.lean` extension (one import + `mem_P_of_blockAny`/`_blockMajority`/`_blockXorAny`) accepted IN PLACE on the Z1-rider precedent — **consumption embargo**: no freeze claims on `PClosure.lean` and no ch3-4 code cites the block stack or the EmitIter hosts until the block-stack gate closes; (3) **pinned audit surface for the ch7-side (Aparna) round**: the six post-gate commits `c4114867..d4503768` — `PolyTimeBlockLoop/Tests/Majority`, `EmitIterEmbed/Body`, the `PClosure` extension (~2,900 lines; their ch7-phase1 gate at `76fe2f46` covered the 13-module surface incl. `CounterProgInput`/`PolyTimePrefix`/`PairEncode`, NOT these) — a statement gate + fill verification on the MERGED tree under `audits/TEMPLATE.md`; (4) EmitIter `padAction`/`embedCfg`-vs-§12-Embed harmonization and the shared-primitive naming DEFERRED TO 12.2c (rename window closes when the block-stack audit pack is cut). **Verification at merge**: 48-module sweep (23 main-side bootstrap deps + the 19 new/extended modules + the Expanders/Randomized/ClassNP/TuringMachine facades; `CircuitComplexity`/root facades out of scope — untouched ~100-module main-side closures); lint: 7 missing public docstrings REPAIRED by maintainer (comment-only, flagged for the block-stack audit; `resMatrix_apply`, `blockCount_le`, `weakAdv_pos`/`_le_sixth`/`_ge`, `measurable_coordIndicator`/`integrable_coordIndicator`), and `Randomized/Classes.lean` 1,265 lines > 1000 justified here: the audited ch7 Tier-B class core, gated as one surface at ch7-phase1; any split belongs to the ch7 campaign. `CounterProgInput` flagged for the Jason ARM sync (CounterProg input conventions must not fork) | Recorded |

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
