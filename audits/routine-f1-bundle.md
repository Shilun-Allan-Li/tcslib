# External audit pack — machine-routine layer (§12), epoch F1 fill gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4c), the
§12 fill campaign's first epoch. The statement gate closed in three rounds
(`audits/routine-infra-resolutions.md`); this round audits the **fills**:
37 of the 56 audited-true statements proved by three parallel batch agents
(plan §4c: F1A `Build/Embed.lean` 13/13, F1B `Build/Seam.lean` 11/11,
F1C `Build/Catalog.lean` Part 1 + W1/W2 13/13). Epoch gates follow the
statement-gate rule: the gate closes on a round with zero blockers and zero
majors (`workflow.md` §4).

Audited at commit `bf1b6d04` (branch `complexity/arora-barak-ch3-4`). The
fills are the three attached patch series (Codex-authored, integrated by
`git am -3` as `d20ab758`, `a5012741`, `2f67e910`); the agents' own
`REPORT.md`s are attached verbatim. **Every proof is kernel-checked** — the
maintainer's replay evidence is below — so this audit's object is not
correctness of the checked terms but the **surface**: the sixty new private
declarations (A 14, B 13, C 33 — blind-restate each against its role), the
honesty of the helper statements (a vacuous or subtly weakened private
lemma misleads every later fill that imitates it), fidelity of the proofs
to the binding inherited contracts, and the handful of declared anomalies
below.

## Brief for the auditor

1. **Blind-restate all sixty new private declarations** from their bodies
   (the reports' role tables are claims to check, not ground truth): A's
   `embedSlot_selected`/`embedSlot_unselected` glue pair, the four
   `*_apply`/`*_step` transports, the `embedReturn*` encodings and
   `embedThroughHalt` core, `embedReturn_visited`; B's `seamComp_step_*`,
   `seam_stationary_apply`, `seamComp_dispatch`, the `seamComp_left`/
   `seamComp_right` lockstep identities (they must be exactly the round-2
   report's two displayed full-configuration identities), the general
   cores, `seam_ofWords_mapState`; C's `catalogCfg`/`catalogTrace`
   configuration-trace family and the per-routine invariants.
2. **Check contract fidelity**: A's returning-run proofs against the
   round-3 five-step plan (positive time; component check; live-prefix
   induction; last step; first-visit exclusion) and the visited equalities
   proved **without** the through-halt contracts (the binding independence);
   B's canonical theorems derived as instances of the general cores with
   **no independent lockstep proof** and the visited containment with **no
   phase-two endpoint hypothesis**; C's budgets landing on the exact
   movement table (`2L+2`, `2d+2`, `2p+2`; intervals `[-1,·]`), W1's
   per-prefix `capture_run` application including the terminal emission,
   W2's trajectory agreement with no output or termination hypothesis.
3. **Assess the declared anomalies**: (i) A's two unused-`hcap` warnings —
   the frozen signatures keep the hypothesis while the private transports
   hold without it; is the exported capture interpretation still the one
   the statement advertises, and is keeping the premise the right call?
   (ii) A's two flagged **Fill appendix** docstring additions — appendices
   only, no audited sketch text altered? (iii) C's requested shared lemma
   (a public `redirectTM` head-trajectory projection) — right shape for
   the natural-home queue? (iv) The three deliveries' environment-shim C
   files were **excluded** (not compiled, not run, not integrated,
   unreferenced by the patches) — flag if any integrated artifact
   nonetheless depends on anything outside the Lean sources.
4. Report anything the fills newly misstate — in the standard table and
   severity scale. Statement bodies were frozen; verify no signature,
   definition, or F2-row drift against the attached patches (the
   maintainer's mechanical check found removals only at `sorry` bodies).

## Repository-side attestations (verify or challenge)

* Freeze (maintainer, mechanical): across all three patches, every removed
  line is a `sorry` body except A's two flagged appendix re-terminations;
  each patch touches only its owned file; C's 19 epoch-F2 statements remain
  sorried and byte-identical.
* Fresh replay (`audits/logs/routine-f1-integration-sweep.log`, revision
  recorded at start: `bf1b6d04`'s parent set, re-run post-integration):
  the three modules plus the `TuringMachine` facade, 0 `error:` lines,
  fresh `.olean`s, **exactly 19** `declaration uses 'sorry'` warnings, all
  in `Catalog.lean`'s F2 rows. `Embed.lean` and `Seam.lean` are
  **zero-sorry**.
* Independent axiom prints (`audits/logs/routine-f1-axioms.log`, generated
  by the maintainer, not the agents): all **37** filled theorems at most
  `[propext, Classical.choice, Quot.sound]` (several proper subsets);
  `sorryAx` appears nowhere.
* Style lint (`audits/logs/routine-f1-stylelint.log`): 0 FAIL;
  size WARNs only (Catalog now 1851 lines — the queued per-theme split,
  backlog §2 decision 12.2(c), is the recorded justification; Embed 931
  and Seam 696 exceed the 600 target as INFO).
* Delivery integrity: `SHA256SUMS` verified 15/12/14 files OK; each zip's
  bundle verifies against its recorded base `42d524b6`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/routine-f1-findings.md`; the epoch gate closes on zero blockers and
majors, after which epoch F2 (the 19 Catalog space rows) dispatches.


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
| F1B | `Build/Seam.lean` | 11 | The **general-configuration trio first** (`_ofCfg` run / first-return / visited — the round-2/3 reports verify the lockstep decomposition and the `(Cfg.ofWords q w).mapState f = Cfg.ofWords (f q) w` identity), then the four canonical statements **as instances**, the two additive and one max space corollaries by projection, and the release pair (fresh-step equation + `Sum.inr` lockstep) |
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
| **P3.2 gate CLOSED** (round 2, 2026-10-09: **PASS, 0 blockers / 0 majors / 2 minors / 1 note** — `audits/ch3-p32-r2-findings.md` verbatim; loop summary `audits/ch3-p32-resolutions.md`). Both round-1 counterconstructions verified to violate the new `UniformMachineCode` clauses; `exists_uniformMachineCode` confirmed true by the auditor's independent polynomial construction over the concrete grammar (adopted into the sketch — minor R2-1: the received compiler route is arbitrary-time, no received polynomial ledger is claimed); "four-coordinate pairing" wording (R2-2). Carried: the fill-gate axiom-closure check for the choice-over-sorried-existence chain. **Natural-home promotions into the P3.1 files unblocked** | Recorded |
| **P3.3 gate CLOSED** (round 2, 2026-10-09: **PASS, 0 blockers / 0 majors / 2 minors / 2 notes** — `audits/ch3-p33-r2-findings.md` verbatim; loop summary `audits/ch3-p33-resolutions.md`). Both round-1 majors closed (fixed-code repetition; the concrete O(n) capped locator, no monotonicity needed). Minors swept: the ladder pinned (`ℓ₀ := 2` seed, the source formula authoritative — round-2 pack paraphrase acknowledged as an offset erratum) and the clock-allowance split stated with the interpreter prefix-bound obligation; the stage-bottom comparison attributed to the square (note 3). **Facade rewiring**: `NDCodes` joins `TuringMachine.lean`, `NTimeHierarchy` joins `Diagonalization.lean` (P3.2+P3.3 both closed), the root's two temporary imports removed; `Robustness/Bidirectional` added to the scratch tree (facade sweep gap). **Every drafted phase of the chapter-3/4 statement program is now gated closed except the §12 routine layer**; P3.4 (Ladner) remains the sole undrafted phase | Recorded |
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
**major** = statement is fixable but materially misleading as is; **minor** = edge case
or naming/attribution defect; **note** = observation, no change required.
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
```


## ===== audits/routine-infra-resolutions.md =====

```
# Machine-routine layer (§12) — audit loop resolutions

**Gate: CLOSED (round 3, 2026-10-09).** Three rounds:

| Round | Verdict | Findings files |
|---|---|---|
| 1 | FAIL — 0 blockers, 4 majors, 3 minors, 3 notes | `audits/routine-infra-findings.md` |
| 2 | FAIL — 1 blocker, 0 majors, 0 minors, 1 note | `audits/routine-infra-r2-findings.md` |
| 3 | **PASS — 0 blockers, 0 majors, 1 minor, 0 notes** | `audits/routine-infra-r3-findings.md` |

## The loop

* **Round 1** (audited surface: the 47-statement skeleton of
  `Build/{Embed,Seam,Catalog}.lean`) found no counterexample to any of the
  47 sorried conclusions but four interface majors: the closed embeddings
  cannot express the halt-to-live return (R1 — the final halting emission
  is lost to the halt or to premature seam dispatch, formal trace
  supplied); the seam theorems were canonical-`Cfg.ofWords`-only (R2); the
  first-return cut excluded positive entry-equals-exit calls (R3); and
  `pairMapSnd`'s documented witness was refuted — its capture tape visits
  output-length cells (R4). Repairs added **three definitions and nine
  sorried contracts** (the returning embeddings
  `embedSilentRetTM`/`embedEmitRetTM` with through-halt run and visited
  contracts; the general-configuration seam theorems
  `seamCompTM_{run,firstReturn,visitedByTapeHead}_ofCfg`; the
  `seamReleaseTM` adapter with first-return and visited contracts),
  commissioned the forwarding `pairMapSnd` controller, and corrected the
  `polyBits`/`compare`/`increment` sketches (R5-R7) plus the
  R8/R9/R10 descriptions. 47 → 56 sorried statements.
* **Round 2** accepted seven of the nine new contracts, every round-1
  disposition, and the S7/S8/S9 replays — but found both through-halt
  contracts **false at `T = 0`** for an initially halted configuration
  (the handover projection demands `none = some (Sum.inr ())`). Repair:
  `(hc : c.state ≠ none)` on both.
* **Round 3**: PASS. The auditor replayed the counterexample against the
  amendment (no instance exists), proved the full positive-time induction
  through the final step, verified consumers discharge `hc` at every
  advertised live seam, and confirmed byte-identity of everything else
  down to blob hashes.

## Minor, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| R3-1 | The handover docstring's equivalence is now stated under **both** first-halt hypotheses (`hc ↔ 0 < T` needs `hhalt` forward and `hlive 0` backward); the round-3 pack's `hhalt`-only phrasing is acknowledged below |

## Pack errata, acknowledged (shipped packs are never edited)

* Round-2 pack: the new-contract subdivision read "six run/first-return
  plus three visited-set"; the correct split is **five and four**
  (round-2 note R2-2).
* Round-3 pack: the brief repeated the `hhalt`-only equivalence
  qualification corrected by R3-1.

## Carried into the fill briefs

* The round-2/round-3 positive-time through-halt induction (step 3's
  component check, the `Option.elim` successor equations, the last-step
  case) — effectively a proof plan for both `_run` contracts.
* The commissioned `pairMapSnd` forwarding controller with the
  coefficient-one payload ledger (round-2's R4 calculation); the
  `polyBits` case split; the exact `compare`/`increment` counts.
* Round-1's S1-S12 sanity list (S7/S8/S9 already replayed by the
  auditors); the loop-row sibling contracts (R10) and the zone/virtual
  input consumer layers (R9) as commissioned future work.
* `Catalog.lean` at 1012 lines: justified by the queued per-theme split
  (backlog §2, decision 12.2 option (c)).

## Consequences

* **Every statement gate of the chapters-3-4 campaign is now CLOSED**:
  P0, P3.1, P3.2, P3.3, P4.1, P4.2, P4.3, P4.4, and §12.
* The §12 freeze lifts: `Build/{Embed,Seam,Catalog}.lean` join the
  `TuringMachine.lean` facade and the root's temporary imports are
  removed (the closing commit).
* The P4.1-carried `NP ⊆ PSPACE` hard dependency and the P4.2/P4.3
  fill-engine references now rest on a **closed** §12 surface.
* Statement-freeze baseline: the closing commit.
```


## ===== audits/routine-infra-r3-findings.md =====

```
# Machine-routine layer (§12), round 3: repair audit

**Verdict: PASS — 0 blockers, 0 majors, 1 minor, 0 notes.** The statement gate meets its zero-blocker/zero-major criterion. Both through-halt contracts are repaired. Round-2 R2-1 and the remaining round-1 R1 obligation are closed at statement level. The sole new finding is a documentation qualification; no further theorem hypothesis or conclusion change is needed.

Audited packet: `routine-infra-r3-bundle.md`, reported commit `2b82cbb3932438a3c6cda77d992d2fc4018d9923`, branch `complexity/arora-barak-ch3-4`. Audit date: 2026-10-09. Independently computed SHA-256:

```text
bb6514407d11a4a72b9dd4ad6d20a7acffd01a564fe3d369afbb49f30248d89b
```

Scope: the 38-line repair diff, both amended contracts, their use at live seams, and preservation of the previous dispositions. References below use extracted attachment line numbers. This is a mathematical statement audit, not a kernel-checked proof fill. No source files were changed.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R3-1 | minor | `Build/Embed.lean:478` · docstring of `embedSilentRetTM_run`; opening pack repeats the qualification | The equivalence between `hc` and `0 < T` needs both existing first-halt hypotheses, not `hhalt` alone. | For an initially halted `c` and `T = 1`, absorption gives `hhalt`, and `0 < T` holds, but `hc` fails. This example violates `hlive` at zero, so it does **not** refute either amended contract. The forward implication uses `hhalt`; the reverse uses `hlive 0`. | Replace “under `hhalt`” with “under `hlive` and `hhalt`” in the source docstring. Acknowledge the same qualification for the shipped pack without editing it. |

**Replay and positive-time proof.** Both amended declarations retain exactly their old conclusions: transported lockstep at all times before `T`, the complete transported configuration with a live return anchor at `T`, and exclusion of that anchor before `T`. The suppressing contract retains `hcap`; forwarding needs no capture-tape condition.

1. **The old counterexample is excluded.** Reuse round 2's choices: `m = 0`, `k = 1`, `S = Unit`, empty input, the empty injection, `cap = 0`, and

   ```lean
   c := { M.initCfg [] with state := none }
   T := 0
   ```

   The capture condition holds. The hypothesis `hlive` is vacuous and `hhalt` follows from `runFrom_zero`. But the new premise reduces to

   \[
   \mathrm{hc}:\quad \mathrm{none}\ne\mathrm{none},
   \]

   which is impossible. Neither amended theorem can be instantiated. The old state-projection contradiction remains a valid diagnosis of the old statement, but is no longer a counterexample to the new one.

2. **Positive time follows, and the equivalence is precise.** For a live `c`,

   \[
   T=0
   \Longrightarrow
   c.\mathrm{state}=(M.\mathrm{runFrom}\ c\ 0).\mathrm{state}
   =\mathrm{none}\quad(\mathrm{hhalt}),
   \]

   contradicting `hc`. Since `T` is natural, `0 < T`. Conversely,

   \[
   0<T
   \Longrightarrow
   (M.\mathrm{runFrom}\ c\ 0).\mathrm{state}\ne\mathrm{none}
   \quad(\mathrm{hlive}\ 0)
   \Longrightarrow c.\mathrm{state}\ne\mathrm{none}.
   \]

   Thus, under **both** `hlive` and `hhalt`,

   \[
   c.\mathrm{state}\ne\mathrm{none}\quad\Longleftrightarrow\quad 0<T.
   \]

3. **The same action is executed completely.** Fix either flavor. Write `E` for its configuration transport with the stated parameters fixed, and `R` for its returning machine. From any live source configuration `c`, the definitions give

   \[
   \begin{aligned}
   &R.\mathrm{step}\bigl((E(c)).\mathrm{mapState}\ \mathrm{Sum.inl}\bigr)\\
   &\quad=\left\{E(M.\mathrm{step}\ c)\ \mathrm{with}\
   \mathrm{state}:=\mathrm{some}\!\left(
   (M.\mathrm{step}\ c).\mathrm{state}.\mathrm{elim}
   \ (\mathrm{Sum.inr}())\ \mathrm{Sum.inl}\right)\right\}.
   \end{aligned}
   \]

   Here is the component check. Injectivity of `ι` gives `embedSlot ι (ι i) = some i`; the transported selected tapes and heads therefore supply exactly the source's work symbols. The input position also agrees. Consequently both machines select the same source action. `embedActionCore` copies its input movement and every selected work-tape write and movement. Other frame tapes receive no write or movement. In the suppressing case, `hcap` keeps capture outside the selected bank: no emission leaves capture unchanged, while emission of a bit appends that bit at the old word length, by `bufferTape_append`; physical output remains `out₀`. In the forwarding case, output becomes `pre ++` the new source output, by list-append associativity. `Action.apply` performs these effects regardless of whether the successor is halted. Only the successor control differs, exactly as displayed.

4. **Induct up to the last live time.** At zero, `runFrom_zero` gives the required transported equality. If `t + 1 < T`, `hlive` makes the source live at both `t` and `t + 1`. Apply step 3 to the configuration at time `t`: its successor is `some q` for a source state `q`, and `Option.elim` sends it to `Sum.inl q`. The induction hypothesis and `runFrom_succ_eq_step'` yield

   \[
   R.\mathrm{runFrom}\bigl((E(c)).\mathrm{mapState}\ \mathrm{Sum.inl}\bigr)\ t
   =\bigl(E(M.\mathrm{runFrom}\ c\ t)\bigr).\mathrm{mapState}\ \mathrm{Sum.inl}
   \qquad(t<T).
   \]

5. **Execute the final step.** Since `0 < T`, the predecessor satisfies `T - 1 < T` and `(T - 1) + 1 = T`. The source is live there by `hlive`, so step 3 applies. Its successor is `none` by `hhalt`, hence `Option.elim` now selects `Sum.inr ()`. This proves exactly

   \[
   R.\mathrm{runFrom}\bigl((E(c)).\mathrm{mapState}\ \mathrm{Sum.inl}\bigr)\ T
   =\{E(M.\mathrm{runFrom}\ c\ T)\ \mathrm{with}\
      \mathrm{state}:=\mathrm{some}(\mathrm{Sum.inr}())\}.
   \]

   At every earlier time, step 4 and `hlive` put control in `some (Sum.inl q)`, distinct from `some (Sum.inr ())`. This proves the first-visit clause. These are all three conjuncts of each amended contract. The round-2 positive-time argument applies unchanged; no additional premise is needed.

The smallest positive case, S8, still has `T = 1`: a live, one-state source emits `true` and halts. With silent capture prefix `[false]` and physical output `[true]`, the return configuration has capture word `[false,true]`, capture head `2`, physical output `[true]`, and state `some (Sum.inr ())`. Forwarding with prefix `[false]` gives physical output `[false,true]` at the same live anchor. A final selected-tape write and head movement also survive by step 3. A final action with no emission works identically, leaving the capture head or physical output unchanged.

**Consumers and unchanged contracts.** The new premise is discharged by the supplied live launch configurations:

\[
\begin{aligned}
(M.\mathrm{initCfg}\ x).\mathrm{state}&=\mathrm{some}(M.q_0),\\
(\mathrm{Cfg.ofWords}\ q\ w).\mathrm{state}&=\mathrm{some}(q),\\
c_1.\mathrm{state}=\mathrm{some}(\mathrm{exit})
&\Longrightarrow
(c_1.\mathrm{mapState}(\mathrm{fun}\ \_\Rightarrow\mathrm{entry})).\mathrm{state}
=\mathrm{some}(\mathrm{entry}).
\end{aligned}
\]

Similarly, the release adapter assumes `c.state = some anchor` and starts its transported configuration at a live fresh state. Tape residue, displaced heads, and accumulated output do not affect these equations. Thus the added premise excludes only the unsupported initially halted launch; it imposes no extra condition on the advertised live-seam consumers.

| Unchanged round-2 contract(s) | Why the repair causes no regression |
|---|---|
| `embedSilentRetTM_visitedByTapeHead`, `embedEmitRetTM_visitedByTapeHead` | Compare the returning and closed **host** machines directly. While their controls correspond, their non-control actions agree; after the first host halt, the closed machine is absorbed and the returning anchor idles. Initially halted starts leave both machines fixed. This proof needs neither `hc` nor `hcap`, and also covers nonhalting runs. It does not depend on applying a through-halt theorem to an initially halted source. |
| `seamCompTM_run_ofCfg` | The full transported return and first-visit cut proved above still supply its phase-one hypotheses; stationary dispatch still costs exactly one step. |
| `seamCompTM_firstReturn_ofCfg` | Left/right state separation and the second-phase cut are unchanged. |
| `seamCompTM_visitedByTapeHead_ofCfg` | The two run segments and stationary dispatch are unchanged, hence so is the union containment. |
| `seamReleaseTM_firstReturn`, `seamReleaseTM_visitedByTapeHead` | Their definitions, live-start hypotheses, and execute-first arguments are byte-identical. S7's positive self-return remains valid. |

S9's arbitrary-frame, output-carrying composition is unaffected. Round-1 R2–R10 retain their accepted round-2 dispositions; R1 now closes. Round-2 R2-2 is addressed by the acknowledged pack erratum: **five run/first-return contracts and four visited-set contracts**, totaling nine.

**Integrity and evidence limits.** I independently obtained the round-2 packet and verified its SHA-256 as `fc7afcb8a469914c4b6a672348769329cfe708c013c64cfbb957481aadb2a3cf`, then compared the extracted files directly.

| Check | Result |
|---|---|
| Complete §12 source change | Exactly the supplied 38-line diff: two `hc` insertions and one docstring paragraph edit. All machine definitions and theorem conclusions are unchanged; the other 54 theorem declarations are unchanged. |
| Diff blob identities | Old `Embed.lean`: `e1d69d240310e4d080d9640dfe8faf0223b90798`; new: `b44c447984dcc5e6e91636986aeacb862f1024af`. Both match the diff's index prefixes. |
| Frozen context | All ten other attached Lean files, including `Seam.lean` and `Catalog.lean`, are byte-identical to round 2. The design document, policy, workflow, audit template, and round-1 report are also byte-identical. |
| Inventory | The theorem-name lists are unchanged. Exactly **56** sorried declarations: **Embed 13 + Seam 11 + Catalog 32**. |
| Supplied elaboration log | Header names the reported commit; 56 sorry warnings and zero `error:` lines. Every warning line points to the corresponding attached theorem declaration. |
| Supplied style log | Zero FAIL lines and nine WARN lines, agreeing with its summary. |

“Nothing else moved” holds for the §12 source and frozen Lean context. The broader campaign plan additionally appends four status rows recording repair batches and other gate closures; this is administrative context, not an unreported §12 source change.

No fresh Lean build was possible: `lean` and `lake` are unavailable, and the packet is not a complete checkout. The supplied logs were checked for internal consistency; fresh `.olean` production and the repository's commit association were not independently reproduced. This limitation does not affect the direct source comparison or the mathematical repair argument.

**Notation glossary.** `E` denotes the chosen configuration transport (`embedSilentCfg` or `embedEmitCfg`) with all non-configuration parameters fixed; `R` denotes its matching returning machine (`embedSilentRetTM` or `embedEmitRetTM`). All other symbols are the source declarations' parameters, state constructors, fields, and operations; `q` is a live source state in the induction.
```


## ===== audits/routine-f1-agent-reports/batchA-REPORT.md =====

```
# §12 F1 Batch A — proof-fill report

**Complete: 13/13 targets proved.** No admitted helper or admitted dependency.
Only `TCSlib/Complexity/TuringMachine/Build/Embed.lean` changed in the git series.
No push or PR was made.

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Base branch: `complexity/arora-barak-ch3-4`.
Base commit: `42d524b665f1fc856fe6f60a27a7d7ecced91b71`.
Working branch: `fill/s12-f1-A`.
Delivered commit: `6983c4e7657871cec5f47b0f23978f94250586dd`.

The followed brief is `briefs/routine-f1-batchA.md` from this base. The base
is the brief-publication commit immediately after its cited `f7f4f0f7`;
no rebase occurred. The three audit reports and resolutions were read.

## Target completion, in the required fill order

| Order | Target in namespace `Turing` | Result |
|---:|---|---|
| 1 | `embedSilentTM_runFrom` | Proved |
| 2 | `embedSilentTM_frame` | Proved |
| 3 | `embedSilentTM_visitedByTapeHead` | Proved |
| 4 | `embedSilentTM_visitedByTapeHead_frame` | Proved |
| 5 | `embedSilentTM_spaceUsedByTape_cap` | Proved |
| 6 | `embedEmitTM_runFrom` | Proved |
| 7 | `embedEmitTM_frame` | Proved |
| 8 | `embedEmitTM_visitedByTapeHead` | Proved |
| 9 | `embedEmitTM_visitedByTapeHead_frame` | Proved |
| 10 | `embedSilentRetTM_run` | Proved |
| 11 | `embedEmitRetTM_run` | Proved |
| 12 | `embedSilentRetTM_visitedByTapeHead` | Proved |
| 13 | `embedEmitRetTM_visitedByTapeHead` | Proved |

The first nine proofs use the two inverse-selection lemmas and the two
componentwise action/step commutations. The capture bound uses output
monotonicity to contain the head trajectory in the integer interval between
its initial and final positions, then takes the interval cardinality.

The two returning-run proofs instantiate `embedThroughHalt`, which follows
the binding audit plan: derive positive time, induct over the live prefix,
execute the final source action from the predecessor time, and exclude the
right anchor at all earlier times. `embedSilentRet_step` and
`embedEmitRet_step` identify the audit's complete-action component check;
`embedReturnAction` and `embedReturnCfg_live` expose the optional-successor
cases without changing any non-control field.

The last two proofs use `embedReturn_visited` directly. They do **not**
depend on either returning-run contract. This helper compares the host
machines, treats initially halted starts separately, and imposes no source
termination or capture-separation hypothesis. The one-step S8 observations
for both flavors also check using only `rfl`; see `SanityCheck.lean` and
`sanity.log`.

## Every new source declaration

All 14 additions to `Embed.lean` are `private`; 12 are lemmas and 2 are definitions.
There are no new public declarations, instances, axioms, or removals.

| Private declaration | Role |
|---|---|
| `embedSlot_selected` | Unique inverse on a selected tape. |
| `embedSlot_unselected` | No inverse outside the selected bank. |
| `embedSilent_apply` | Silent action transport, component by component, including buffer append. |
| `embedSilent_step` | Source reads and complete silent step commutation. |
| `embedEmit_apply` | Forwarding action transport and output append associativity. |
| `embedEmit_step` | Source reads and complete forwarding step commutation. |
| `embedReturnAction` | Private action encoding that changes only the successor control. |
| `embedReturnCfg` | Private configuration encoding that changes only the control. |
| `embedReturnCfg_live` | Agreement of the return encoding with left state mapping at a live state. |
| `embedReturn_step` | Direct closed-host/returning-host one-step comparison, including stationary halt/anchor. |
| `embedSilentRet_step` | Audit step 3 for the silent returning transport. |
| `embedThroughHalt` | Audit positive-time argument, live-prefix induction, last step, and first-visit exclusion. |
| `embedEmitRet_step` | Audit step 3 for the forwarding returning transport. |
| `embedReturn_visited` | All-time direct host comparison of visited sets; initially halted starts handled separately. |

The separate `SanityCheck.lean` contains three private test fixtures
(`emitHalt`, `emptyBank`, `silentStart`) and two anonymous `example`s.
These are not repository changes or public library declarations.

**Requested shared lemmas:** none. **Escalations:** none.

## Freeze and documentation

`freeze-check.json` records a comment-stripped comparison with the base:
all 21 original declarations remain in their original order; all signatures
are unchanged; all eight original definitions, including the two original
private definitions, are unchanged. The only modified theorem bodies are
the 13 commissioned targets. Imports and options are unchanged.

Two permitted proof-sketch appendices were added: the capture bound's
interval-containment shortcut, and the returning silent visited-set proof's
independence from the through-halt contracts. No attribution was edited.
Existing skeleton-status wording was retained under the brief's freeze.
The file stays a single coherent cluster because this batch's exclusive
ownership forbids moving helpers into other modules.

## Verification

- Final `Embed` check: exit 0; a fresh `.olean`; zero `error:` diagnostics;
  zero `declaration uses 'sorry'` warnings. See `sweep.log`.
- All 13 final `#print axioms` results are in `axioms.log`, generated by
  `AxiomCheck.lean` against the fresh tree. Every footprint is a subset of
  `[propext, Classical.choice, Quot.sound]`; `sorryAx` never appears.
- S8 definitional checks: exit 0, no diagnostics (`sanity.log`).
- Frozen-surface comparison: passed. `git diff --check`: passed.
- The patch was independently applied to the recorded base file and
  reproduced the final source byte-for-byte. The incremental git bundle
  verifies and records the base as its prerequisite (`bundle-verify.log`).
- The bootstrap completed all 65 listed modules after checking the six
  additional imports described below. The continuation has zero errors.
  The final fresh Turing-machine facade check exited 0 with no diagnostics;
  its command and status are appended to `sweep.log`.

The only final source warnings are unused `hcap` parameters in
`embedSilentTM_runFrom` and `embedSilentRetTM_run`. Their audited signatures
are preserved. The private transport equations actually hold even when
capture is selected: both definitions then give selected-tape behavior
priority and ignore capture. The off-bank premise remains essential to
the exported capture-tape interpretation and space bound, where it is used.

Final per-file log tail:

```text
warning: unused variable `hcap` (embedSilentTM_runFrom)
warning: unused variable `hcap` (embedSilentRetTM_run)
Exit status: 0
Command: bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine
Exit status: 0
```

## Environment and reproducibility

Lean is the unmodified official 4.25.0 release
(`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`); mathlib is the pinned
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
The standard `lake exe cache get` setup failed during its optional
ProofWidgets release fetch. Subsequent setup called the pinned cache
library's download/unpack functions for the required imports, without
editing dependency sources. No campaign `lake build` was issued.

This execution environment permits `/proc/self/exe` but rejects the
numerical spelling of the current process's executable path. A small
runtime path-compatibility shim maps only that exact own-process spelling
to `/proc/self/exe`. It changes no Lean code, kernel operation, source,
proof, or imported declaration. Normal environments do not need it.

The prescribed 65-module bootstrap list predates six imports. The first
pass additionally checked `Build/Embed`, `Build/Seam`, `Build/Catalog`, and
`NDCodes` before the Turing-machine facade, which passed. It subsequently
stopped at the separate `Formulas` facade because `QBF.olean` was missing.
The continuation checks the unchanged `QBF` and `QBFEncoding` modules,
then resumes at `Formulas`. The original missing-dependency diagnostic is
retained in `bootstrap.log`; continuation evidence is in
`bootstrap-resume.log`. No dependency source was changed. All repository
checks use `scripts/lean_check_tree.sh` and direct Lean checks.

To integrate with the recorded base available:

```sh
git am -3 patches/*.patch
```

Then use the repository check script on `Build/Embed` and the facade,
and run `AxiomCheck.lean` against that fresh olean tree. `changes.bundle`
is an alternative git transport with the same single source commit.
`SHA256SUMS` covers every delivered file except the checksum manifest itself.
```


## ===== audits/routine-f1-agent-reports/batchB-REPORT.md =====

```
# §12 F1 Batch B — seam composition and release

**Complete: 11/11 targets filled.** No new admissions, axioms, public declarations, or statement changes. Delivery is the flat `fill-s12-f1-B.zip`; no push or pull request was made, and `lake build` was never run.

## Provenance and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested starting branch: `complexity/arora-barak-ch3-4`.
- Recorded base: `42d524b665f1fc856fe6f60a27a7d7ecced91b71` (the commit adding the matching `briefs/routine-f1-batchB.md`; its parent is the brief's issuance commit `f7f4f0f7`).
- Working branch: `fill/s12-f1-B`; no rebase.
- Delivery commit: `4938f0fe9610c724d6c011f44013307ac285303a`.
- Only changed repository file: `TCSlib/Complexity/TuringMachine/Build/Seam.lean`.
- Full source: 696 lines, 36,665 bytes. The coherent shared decomposition stays in the sole owned file.
- Instructions read: the matching Batch B brief, repository policy/workflow, all three routine-infrastructure audit reports, and their resolutions.

## Proof order and discharge map

The general-configuration trio was filled first, then the canonical instances, additive/max space corollaries, and release contracts, in the brief's order. To preserve the public declaration order (which places canonical statements before the general ones), the general proofs live in private cores. Each general public theorem is a wrapper around its core; the canonical theorem specializes that same core using `seam_ofWords_mapState`. No canonical theorem has an independent lockstep proof.

| Target | Discharging proof |
|---|---|
| `seamCompTM_run_ofCfg` | `seamComp_run_general`: left lockstep, one exact dispatch, right lockstep, then the phase-two endpoint |
| `seamCompTM_firstReturn_ofCfg` | `seamComp_firstReturn_general`: left/right constructor separation and the transported phase-two cut |
| `seamCompTM_visitedByTapeHead_ofCfg` | `seamComp_visited_general`: split each image witness at dispatch; no phase-two endpoint hypothesis |
| `seamCompTM_run` | Canonical instance of `seamComp_run_general` |
| `seamCompTM_firstReturn` | Canonical instance of `seamComp_firstReturn_general` |
| `seamCompTM_visitedByTapeHead` | Canonical instance of `seamComp_visited_general` |
| `seamCompTM_spaceUsedByTape_le_add` | Cardinality monotonicity and the union-cardinality inequality |
| `seamCompTM_spaceUsed_le_add` | Sum the per-tape inequality |
| `seamCompTM_spaceUsedByTape_le_max` | Each phase visits its initial origin; the idle singleton is contained in the other phase's set |
| `seamReleaseTM_firstReturn` | Execute the fresh step, transport every positive-time run, and exclude time zero by constructor disjointness |
| `seamReleaseTM_visitedByTapeHead` | Pointwise head equality at zero and every positive time, then equality of finite images |

The two full-configuration trajectory identities required by the inherited audit contract are exactly `seamComp_left` and `seamComp_right`. Dispatch preserves every non-control field of an arbitrary configuration. The right lockstep and release lockstep include halting and post-halt times. Thus the audit's S7 execute-first return and S9 displaced-head/nonempty-output cases are instances of the proved contracts; no canonical-seam assumption was added to a general theorem.

## New declarations

All 13 are private lemmas; none remains admitted:

1. `seamComp_step_left` — one-step left correspondence away from the exit.
2. `seamComp_step_right` — unconditional one-step right correspondence.
3. `seam_stationary_apply` — a stationary, silent, write-free action changes only control.
4. `seamComp_dispatch` — dispatch on an arbitrary live exit configuration.
5. `seamComp_left` — inclusive left-prefix run correspondence under the cut.
6. `seamComp_right` — right run correspondence at every offset after dispatch.
7. `seamComp_run_general` — the shared general endpoint proof.
8. `seamComp_firstReturn_general` — the shared general exclusion proof; endpoint hypotheses are unnecessary for this exclusion alone.
9. `seamComp_visited_general` — the shared general visited-set containment.
10. `seam_ofWords_mapState` — canonical state mapping, proved by reflexivity.
11. `seamRelease_fresh_step` — the fresh state executes the source anchor's action.
12. `seamRelease_step_right` — one-step correspondence in the right copy.
13. `seamRelease_run_pos` — source-run correspondence at every positive time.

Requested shared lemmas: **none**. Escalations: **none**. Remaining targets/frontier: **none**. No existing docstring or attribution was edited; new helper docstrings explain their proof steps.

## Verification

All checks completed successfully on 2026-10-09 UTC.

| Gate | Result |
|---|---|
| Prescribed 65-module bootstrap | Exit 0; zero errors; one untouched pre-existing admission in `CounterProgRun.lean:343` |
| Five additional facade dependencies | Exit 0; zero errors; 48 untouched pre-existing admissions (Embed 13, Catalog 32, NDCodes 1, QBF 1, QBFEncoding 1) |
| Final owned-file check | Exit 0; fresh nonempty olean; zero errors; zero sorry warnings |
| Final TuringMachine facade check | Exit 0; fresh nonempty olean; zero errors |
| All eleven axiom prints on the final fresh tree | Four footprints `[propext, Quot.sound]`; seven `[propext, Classical.choice, Quot.sound]`; no `sorryAx` |
| Incremental git bundle | `git bundle verify` succeeds |

Final sweep log tail:

```text
PASS TCSlib/Complexity/TuringMachine/Build/Seam: exit 0, fresh nonempty olean
CHECK TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine: exit 0, fresh nonempty olean
```

The five remaining diagnostics in the owned file are only unused-variable warnings for redundant hypotheses in frozen signatures: canonical `firstReturn.h₂`, canonical `visitedByTapeHead.h₂`, general `firstReturn.h₂` and `firstReturn.hq`, and release `firstReturn.hc'`. They are not admissions or errors. Existing module/docstring labels mentioning the statement-skeleton phase were retained under the brief's docstring freeze.

The statement-preservation check (`freeze-check.log`) confirms byte-identical public theorem signatures and machine definitions, unchanged public declaration inventory/order, preservation of all 15 original comments/docstrings, unchanged imports/options/namespace variables, and exactly one changed repository path. `git diff --check` passes.

## Environment and reproduction

Lean is the pinned official **4.25.0**, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib is pinned at `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

This environment exposes executable discovery at `/proc/self/exe`; Lean's numeric self-PID path did not work. The included `app_path.c` is a narrow runtime compatibility shim: it maps only this process's own executable-path lookup to `/proc/self/exe` and passes every other `readlink` call through unchanged. It changes no Lean executable, kernel, source, proof term, or compiler option. Build it with `gcc -shared -fPIC app_path.c -ldl -o app_path.so`, then set `LD_PRELOAD` to that shared object's absolute path if reproducing in this same environment. Ordinary hosts do not need it.

The authorized `lake exe cache get` setup was narrowed to the 32 external Mathlib roots used by the bootstrap/import closure after the full-cache attempt was interrupted; it completed successfully and unpacked 969 cached modules. No dependency source, manifest, checker script, or toolchain source was modified.

The supplied 65-module bootstrap order predates six imports now wired into its facades: `Build/Embed`, `Build/Seam`, `Build/Catalog`, `NDCodes`, `Formulas/QBF`, and `Formulas/QBFEncoding`. The owned module was checked during proof iteration; the other five unchanged modules were checked separately before their importing facades. This supplements the prescribed order without changing it. Their pre-existing admissions remain untouched and are not dependencies of the eleven completed proofs, as the axiom prints confirm.

## Archive and integration

- `Seam.lean`: full modified source, to place at the owned repository path above.
- `0001-Fill-section-12-seam-composition-and-release-proofs.patch`: one-commit `git format-patch` series against the recorded base; integrate with `git am -3`.
- `fill-s12-f1-B.bundle`: verified incremental bundle; its prerequisite is the recorded base, and its `HEAD` is the delivery commit.
- `sweep.log`, `axioms.log`, and `Axioms.lean`: final checks and reproducible axiom-print program.
- `bootstrap.log`, `bootstrap-extra.log`: prerequisite elaboration evidence.
- `freeze-check.log`, `bundle-verify.log`, and `app_path.c`: preservation, bundle, and environment evidence.
- `REPORT.md` and `SHA256SUMS`: this report and checksums of every other archive member.

All archive members are at the ZIP root. Verify with `sha256sum -c SHA256SUMS` after extraction. The archive contains no generated Lean binaries or dependency trees.
```


## ===== audits/routine-f1-agent-reports/batchC-REPORT.md =====

```
# §12 Epoch F1, Batch C — complete delivery

**13/13 assigned theorems proved.** Exactly 19 F2 statements remain sorried and byte-identical. No partial frontier and no new admitted helpers.

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Source branch: `complexity/arora-barak-ch3-4`.
Working branch: `fill/s12-f1-C`.
Base: `42d524b665f1fc856fe6f60a27a7d7ecced91b71`.
Delivery commit: `4daaf8767c1b275cdf6a19dbec4ecee6dd513d83`.
Source SHA-256: `9d896306befa195f88dc2900c62cda20090ae787b527872c49da49d5239e57aa`.

Only `TCSlib/Complexity/TuringMachine/Build/Catalog.lean` changed. No push, PR, rebase, or `lake build` was performed. The brief used was the self-contained repository copy `briefs/routine-f1-batchC.md`; the three audit reports, resolutions, policy, and workflow were read. Original definitions, signatures, docstrings, imports, and option headers are preserved; no docstring appendices were added.

## Filled declarations

1. `Turing.transferTM_run`
2. `Turing.transferTM_spaceUsedByTape`
3. `Turing.copyTM_run`
4. `Turing.copyTM_spaceUsedByTape`
5. `Turing.clearTM_run`
6. `Turing.clearTM_spaceUsedByTape`
7. `Turing.compareTM_run`
8. `Turing.compareTM_spaceUsedByTape`
9. `Turing.incrementTM_run_succ`
10. `Turing.incrementTM_run_overflow`
11. `Turing.incrementTM_spaceUsedByTape`
12. `Turing.capture_visitedByTapeHead`
13. `Turing.FinTM.redirectTM_spaceUsedByTape`

## Exact movement ledger

| Routine/case | Forward | Turn | Return | Right-entry | Exact first exit used by the proof | Public bound | Final touched interval |
|---|---:|---:|---:|---:|---|---|---|
| transfer | L | 1 | L | 1 | 2L+2 | 3L+3 (slack) | integers [−1,L], L+2 cells, both tapes |
| copy | L | 1 | L | 1 | 2L+2 | 3L+3 (slack) | integers [−1,L], L+2 cells, both tapes |
| clear | L | 1 | L | 1 | 2L+2 | 2L+2 | integers [−1,L], L+2 cells |
| compare | d | 1 | d | 1 | 2d+2 | 2 min(lengths)+2 | integers [−1,d], d+2 cells |
| increment, success | p | 1 | p | 1 | 2p+2 ≤ 2L | 2L+2 (slack) | integers [−1,p], p+2 cells |
| increment, overflow | L | 1 | L | 1 | 2L+2 | 2L+2 | integers [−1,L], L+2 cells |

Each private routine trace is a full configuration equality at every natural time. The forward configurations visit every nonnegative cell up to the scan depth; the zero-index return configuration visits −1; all intermediate positions lie between these extremes; the completed configuration is stationary at zero. Thus the exact intervals in the table follow directly from those proved traces. The formal public space proofs apply interval containment and `Int.card_Icc`, or the stationary-singleton lemma. The public run proofs choose the displayed exact time and prove exclusion of every requested exit before it.

Empty transfer/copy/clear and width-zero overflow have the trace 0, −1, 0 and return in two steps. A successful increment of `[false]` also returns in two steps without visiting cell 1. Comparison uses a disjunction for physical tape selection and therefore handles self-comparison with one movement per step; the stopping lemma also covers both proper-prefix orientations, equal words, and immediate mismatch.

W1 applies `capture_run` separately at each prefix of the supplied horizon. Output-prefix monotonicity places the capture head between its initial and final recorded lengths, giving exactly the requested output-growth bound; the terminal halting emission is included. W2 uses all-time trajectory agreement, including a source halt followed by either redirected halt or its stationary live loop. No output or termination hypothesis was introduced.

## New private declarations

- `catalogCfg`: Canonical input/output fields, specified words, and explicit work-head positions.
- `catalogTrace`: Forward phase, return phase, and stationary completed configuration as a function of time.
- `catalog_trace_run`: Induction turning the five local transition obligations into the complete all-time trace.
- `catalog_space_bound`: Visited-image containment in the integer interval from −1 to the scan depth, then cardinality.
- `catalog_space_one`: A stationary head visits exactly one cell.
- `catalog_erase_take`: Erasing the last cell of a stored prefix shortens that prefix by one.
- `catalog_write_take`: Writing the next source bit extends the destination prefix by one.
- `catalogClearF`: Clear forward configuration: intact word and advancing head.
- `catalogClearR`: Clear return configuration: unerased prefix and returning head.
- `catalog_clear_trace`: Clear phase invariant and exact all-time configuration trace.
- `catalogCopyF`: Shared transfer/copy forward configuration: intact source and copied destination prefix.
- `catalogCopyR`: Copy return configuration: both complete words and returning heads.
- `catalogTransferR`: Transfer return configuration: unerased source prefix, complete destination, returning heads.
- `catalog_copy_forward`: The common forward transition copies the next bit.
- `catalog_copy_trace`: Copy phase invariant and exact all-time configuration trace.
- `catalog_transfer_trace`: Transfer phase invariant and exact all-time configuration trace.
- `catalog_compare_stop`: Existence of the first differing or terminating position, common nonblank prefix, and correct verdict.
- `catalogCompareF`: Read-only comparison scan with one move per selected physical tape.
- `catalogCompareR`: Read-only comparison return carrying its verdict.
- `catalog_compare_trace`: Comparison phase invariant and exact all-time configuration trace.
- `catalog_increment_split`: Decomposition into leading true bits and either a first false with its tail or no suffix.
- `catalog_increment_value`: The value of incFixed on that decomposition, including overflow.
- `catalog_write_middle`: Changing the bit immediately after a prefix preserves all other cells.
- `catalogIncF`: Increment carry configuration: reset prefix, remaining true prefix, untouched stopping suffix.
- `catalogIncR`: Increment return configuration: complete updated/wrapped word and verdict.
- `catalog_increment_trace`: Increment phase invariant and exact all-time configuration trace.
- `catalog_redirectState`: Local copy of Wrappers.redirectState, translating live/halted source control and last-emission register.
- `catalog_redirectAction`: Local copy of Wrappers.redirectAction, retaining tape actions while suppressing output.
- `catalog_redirectCfg`: Local copy of Wrappers.redirectCfg, preserving source tapes and heads.
- `catalog_redirect_loop`: Local copy of Wrappers.redirect_loop, proving the live loop is stationary.
- `catalog_redirect_apply`: Local copy of Wrappers.redirect_apply, transporting a complete source action.
- `catalog_redirect_step`: Local copy of Wrappers.redirect_step, including both post-halt cases.
- `catalog_redirect_run`: Local copy of Wrappers.redirect_run, all-time initialized configuration correspondence.

The seven `catalog_redirect*` declarations are local copies of the already-proved private correspondence in `Build/Wrappers.lean`, with their names consistently prefixed. No foreign private declaration is referenced. All helpers are in the owned module; there are no new public declarations.

## Frozen F2 inventory

All nineteen declarations below retain their original statement, docstring, and `by sorry` body byte-for-byte. Their line offsets necessarily change when proofs are inserted; their order and contents do not.

- `Turing.FinTM.computesFunInTime_id_spaceUsed`
- `Turing.FinTM.computesFunInTime_const_spaceUsed`
- `Turing.FinTM.computesFunInTime_prepend_spaceUsed`
- `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed`
- `Turing.FinTM.computesFunInTime_polyUnary_spaceUsed`
- `Turing.FinTM.computesFunInTime_polyBits_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairEncodeFixed_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairFst_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairSnd_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairValid_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairConcat_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairDup_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairLenCheck_spaceUsed`
- `Turing.FinTM.computesFunInTime_stripLast_spaceUsed`
- `Turing.FinTM.computesFunInTime_incFixed_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairMapSnd_spaceUsed`
- `Turing.FinTM.computesFunInTime_splitSolve_spaceUsed`
- `Turing.FinTM.computesFunInTime_cond_spaceUsed`
- `Turing.FinTM.exists_loopTM_spaceUsed`

`evidence/freeze.json` records the inventory and source hash. The comparison checked all 32 original theorem signatures and docstrings, all original definitions, the nineteen complete F2 declarations, and the one-file change scope. `git diff --check` passed. Replaying the format-patch on the exact base produced the identical Git tree; see `evidence/patch-replay.log`. The bundle was verified and declares the recorded base as its prerequisite.

## Verification

Pinned Lean: 4.25.0, compiler commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
Pinned mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

- `final-sweep.log`: fresh owned-module check, exit 0, zero `error:` diagnostics, exactly **19** `declaration uses 'sorry'` warnings; then the requested TuringMachine facade check, exit 0 and zero errors.
- `axioms.log`: all thirteen requested axiom prints, each exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or other axiom.
- `evidence/bootstrap.log`: the prescribed module-order bootstrap, completed through all 65 entries (exit 0 after the documented prerequisite recoveries). Its initial Oracle attempt lacked a mathlib cache object; after targeted cache recovery, the sweep resumed at Oracle. This historical setup error is retained in the raw log. A later Formulas facade attempt required its newer QBF imports; those unchanged modules were checked and the sweep resumed at Formulas. These two recovered setup diagnostics are retained in the raw log. The final owned-module/facade gate is recorded separately above.
- The current facade additionally imports `Build/Embed`, `Build/Seam`, and `NDCodes`; the Formulas facade additionally imports `QBF` and `QBFEncoding`. These five modules are absent from the 65-entry bootstrap list. They were checked as unchanged prerequisites; `evidence/facade-dependencies.log` retains their expected out-of-scope admissions.
- Non-sorry simplifier/unused-tactic lint warnings are present; none is an elaboration error. No warning suppression was added.

Environment setup required `TAR_OPTIONS=--no-same-owner` for archive extraction. In this runtime, `/proc/self/exe` works but the numeric virtual-PID executable path does not. `environment/self_exe.c` normalizes only the executing process's own numeric executable lookup to `/proc/self/exe`; it leaves all other filesystem calls alone. The stock Lean executable, kernel, and libraries are unchanged. It was built with `cc -shared -fPIC environment/self_exe.c -o self_exe.so -ldl` and supplied using `LD_PRELOAD` for the checks. Ordinary Linux environments need no such compatibility helper. The cache download's shared temporary-file cleanup also failed once; an isolated targeted cache successfully supplied all required mathlib dependencies before checks.

The owned file is 1,851 lines. The existing §12 per-theme split deferral and this batch’s one-file ownership require the phase helpers to remain here; no other file was split or changed.

**Final sweep log tail:**

```text
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1757:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1802:8: warning: declaration uses 'sorry'
EXIT 0; ERROR_DIAGNOSTICS 0; SORRY_WARNINGS 19
FRESH_OLEAN .lake/tcslib-check-oleans/TCSlib/Complexity/TuringMachine/Build/Catalog.olean 3362832 bytes
RUN bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine
EXIT 0; ERROR_DIAGNOSTICS 0; SORRY_WARNINGS 0
FRESH_OLEAN .lake/tcslib-check-oleans/TCSlib/Complexity/TuringMachine.olean 45168 bytes
PASS: Catalog 19 expected F2 sorry warnings; facade clean.
```

## Requested shared lemmas

A public initialized head-trajectory correspondence for `redirectTM` would let later consumers avoid the seven local copies:

```lean
((redirectTM M haltOn).tm.runFrom ((redirectTM M haltOn).tm.initCfg x) t).workTapePos
  = (M.tm.runFrom (M.tm.initCfg x) t).workTapePos
```

The local `catalog_redirect_run` proves a stronger full-configuration correspondence and supplies this equality by projection. No shared-file change is needed for this delivery.

**Escalations: none.** All assigned statements are proved as frozen.

**Notation:** L is the touched word's length; d is comparison's first differing or terminating-blank position; p is the first false position in a successful increment. These are the brief's ledger variables.
```


## ===== audits/evidence/routine-f1-batchA.patch =====

```
From 6983c4e7657871cec5f47b0f23978f94250586dd Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Fri, 9 Oct 2026 13:39:18 +0800
Subject: [PATCH] Fill the thirteen audited bank-embedding contracts

---
 .../Complexity/TuringMachine/Build/Embed.lean | 374 +++++++++++++++++-
 1 file changed, 359 insertions(+), 15 deletions(-)

diff --git a/TCSlib/Complexity/TuringMachine/Build/Embed.lean b/TCSlib/Complexity/TuringMachine/Build/Embed.lean
index 75dc9507..db10abdc 100644
--- a/TCSlib/Complexity/TuringMachine/Build/Embed.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/Embed.lean
@@ -124,6 +124,29 @@ sends to host tape `j`, or `none` when `j` is unselected. Injectivity of
 private def embedSlot (ι : Fin m ↪ Fin k) (j : Fin k) : Option (Fin m) :=
   (List.finRange m).find? fun i => decide (ι i = j)
 
+/-- Searching at a selected tape returns its unique source index. -/
+private lemma embedSlot_selected (ι : Fin m ↪ Fin k) (i : Fin m) :
+    embedSlot ι (ι i) = some i := by
+  unfold embedSlot
+  cases hs : (List.finRange m).find? (fun j => decide (ι j = ι i)) with
+  | none =>
+    have hn := List.find?_eq_none.mp hs i (by simp)
+    simp at hn
+  | some j =>
+    have hj := List.find?_some hs
+    have hji : j = i := ι.injective (of_decide_eq_true hj)
+    subst j
+    rfl
+
+/-- Searching outside the selected bank returns no source index. -/
+private lemma embedSlot_unselected (ι : Fin m ↪ Fin k) (j : Fin k)
+    (hj : j ∉ Set.range ι) : embedSlot ι j = none := by
+  unfold embedSlot
+  rw [List.find?_eq_none]
+  intro i _
+  simp only [decide_eq_true_eq]
+  exact fun hij => hj ⟨i, hij⟩
+
 /-- The shared private core of the two embedding transformers (frozen
 decision 12.4): transport one source action along `ι`, keeping the input
 move and the successor state, performing the source's tape-`i` action on
@@ -228,6 +251,61 @@ def embedEmitTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S) :
   tr := fun q inp w =>
     embedActionCore ι none (M.tr q inp fun i => w (ι i))
 
+/-- Applying the silent core commutes with configuration transport.
+**Proof sketch.** Selected tapes perform the source action. Off-bank tapes
+are stationary, except that capture appends the emitted bit at the old
+word length. Input movement and successor control are copied verbatim. -/
+private lemma embedSilent_apply (ι : Fin m ↪ Fin k) (cap : Fin k)
+    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
+    (pre out₀ : List Bool) (c : Cfg m Bool S x) (a : Action m Bool S) :
+    (embedActionCore ι (some cap) a).apply
+        (embedSilentCfg ι cap tapes heads pre out₀ c) =
+      embedSilentCfg ι cap tapes heads pre out₀ (a.apply c) := by
+  refine Cfg.ext rfl rfl ?_ ?_ ?_
+  · funext j
+    cases hs : embedSlot ι j with
+    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
+    | none =>
+      by_cases hj : j = cap
+      · subst j
+        cases ho : a.output <;>
+          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
+            ← List.append_assoc, FinTM.bufferTape_append]
+      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
+  · funext j
+    cases hs : embedSlot ι j with
+    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
+    | none =>
+      by_cases hj : j = cap
+      · subst j
+        cases ho : a.output <;>
+          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
+            Nat.cast_add, add_assoc]
+      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
+  · simp [embedActionCore, embedSilentCfg, Action.apply]
+
+/-- The silent host reads the source action and executes all its effects
+in one step; halted configurations remain fixed on both sides. -/
+private lemma embedSilent_step (ι : Fin m ↪ Fin k) (cap : Fin k)
+    (M : MultiTapeTM m Bool S)
+    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
+    (pre out₀ : List Bool) (c : Cfg m Bool S x) :
+    (embedSilentTM ι cap M).step (embedSilentCfg ι cap tapes heads pre out₀ c) =
+      embedSilentCfg ι cap tapes heads pre out₀ (M.step c) := by
+  unfold MultiTapeTM.step
+  cases hs : c.state with
+  | none => simp [embedSilentCfg, hs]
+  | some q =>
+    rw [show (embedSilentCfg ι cap tapes heads pre out₀ c).state = some q from hs]
+    dsimp only
+    have hr : (fun i => (embedSilentCfg ι cap tapes heads pre out₀ c).workTapeSymbols
+        (ι i)) = c.workTapeSymbols := by
+      funext i
+      simp [Cfg.workTapeSymbols, embedSilentCfg, embedSlot_selected]
+    change (embedActionCore ι (some cap) (M.tr q c.inputSymbol _)).apply _ = _
+    rw [hr]
+    exact embedSilent_apply ι cap tapes heads pre out₀ c _
+
 /-- **R1 lockstep, suppressing flavor** (spec, fill pending — design §12;
 [Bon26], `rename_executes`). The transported run *is* the transport of the
 source run, at every time and with the step count preserved exactly: `t`
@@ -255,7 +333,9 @@ theorem embedSilentTM_runFrom (ι : Fin m ↪ Fin k) (cap : Fin k)
     (embedSilentTM ι cap M).runFrom
         (embedSilentCfg ι cap tapes heads pre out₀ c) t =
       embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c t) := by
-  sorry
+  exact MultiTapeTM.runFrom_comm_of_step
+    (embedSilentCfg ι cap tapes heads pre out₀)
+    (embedSilent_step ι cap M tapes heads pre out₀) c t
 
 /-- **R1 frame, suppressing flavor** (spec, fill pending — design §12).
 Along the whole transported run, every host tape outside the selected bank
@@ -284,7 +364,10 @@ theorem embedSilentTM_frame (ι : Fin m ↪ Fin k) (cap : Fin k)
       = (M.runFrom c t).inputPos ∧
     ((embedSilentTM ι cap M).runFrom
         (embedSilentCfg ι cap tapes heads pre out₀ c) t).output = out₀ := by
-  sorry
+  rw [embedSilentTM_runFrom ι cap hcap]
+  refine ⟨?_, rfl, rfl⟩
+  intro j hj hjc
+  simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]
 
 /-- **R1 space, suppressing flavor, selected tapes** (spec, fill pending —
 design §12: "cells visited on host tape `ι i` equal cells visited on
@@ -308,7 +391,15 @@ theorem embedSilentTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
     (embedSilentTM ι cap M).spaceUsedByTape
         (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
       = M.spaceUsedByTape c t i := by
-  sorry
+  have hv : (embedSilentTM ι cap M).visitedByTapeHead
+      (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i) =
+      M.visitedByTapeHead c t i := by
+    unfold MultiTapeTM.visitedByTapeHead
+    congr 1
+    funext u
+    rw [embedSilentTM_runFrom ι cap hcap]
+    simp [embedSilentCfg, embedSlot_selected]
+  exact ⟨hv, congrArg Finset.card hv⟩
 
 /-- **R1 space, suppressing flavor, unselected tapes** (spec, fill
 pending — design §12: "unselected tapes visit nothing new"). A host tape
@@ -328,7 +419,14 @@ theorem embedSilentTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
         (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} ∧
     (embedSilentTM ι cap M).spaceUsedByTape
         (embedSilentCfg ι cap tapes heads pre out₀ c) t j = 1 := by
-  sorry
+  have hv : (embedSilentTM ι cap M).visitedByTapeHead
+      (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} := by
+    unfold MultiTapeTM.visitedByTapeHead
+    simp_rw [embedSilentTM_runFrom ι cap hcap]
+    simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]
+    exact Finset.image_const ⟨0, by simp⟩ _
+  refine ⟨hv, ?_⟩
+  simp [MultiTapeTM.spaceUsedByTape, hv]
 
 /-- **R1 space, suppressing flavor, the capture tape** (spec, fill
 pending — design §12; every unselected tape is accounted for, the capture
@@ -342,7 +440,10 @@ recorded emission.
 increments bounded by one emission per step; the visited set is therefore
 the integer interval from the initial head to the final one, of
 cardinality the output growth plus one
-(`Turing.MultiTapeTM.output_prefix` gives the monotone growth). -/
+(`Turing.MultiTapeTM.output_prefix` gives the monotone growth).
+
+**Fill appendix.** For the stated upper bound, the formal proof only
+needs containment in this interval, followed by its cardinality. -/
 theorem embedSilentTM_spaceUsedByTape_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
     (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
     (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
@@ -350,7 +451,68 @@ theorem embedSilentTM_spaceUsedByTape_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
     (embedSilentTM ι cap M).spaceUsedByTape
         (embedSilentCfg ι cap tapes heads pre out₀ c) t cap
       ≤ (M.runFrom c t).output.length - c.output.length + 1 := by
-  sorry
+  have hgrowth : c.output.length ≤ (M.runFrom c t).output.length := by
+    simpa using (M.output_prefix c (Nat.zero_le t)).length_le
+  have hsub : (embedSilentTM ι cap M).visitedByTapeHead
+      (embedSilentCfg ι cap tapes heads pre out₀ c) t cap ⊆
+      Finset.Icc ((pre ++ c.output).length : ℤ)
+        ((pre ++ (M.runFrom c t).output).length : ℤ) := by
+    intro z hz
+    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
+    have hut : u ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
+    have hlo : c.output.length ≤ (M.runFrom c u).output.length := by
+      simpa using (M.output_prefix c (Nat.zero_le u)).length_le
+    have hhi := (M.output_prefix c hut).length_le
+    rw [embedSilentTM_runFrom ι cap hcap]
+    simp only [embedSilentCfg, embedSlot_unselected ι cap hcap, ↓reduceIte,
+      Finset.mem_Icc, List.length_append, Nat.cast_add]
+    constructor <;> omega
+  calc
+    _ ≤ (Finset.Icc ((pre ++ c.output).length : ℤ)
+        ((pre ++ (M.runFrom c t).output).length : ℤ)).card :=
+      Finset.card_le_card hsub
+    _ = (M.runFrom c t).output.length - c.output.length + 1 := by
+      rw [Int.card_Icc]
+      simp only [List.length_append, Nat.cast_add]
+      omega
+
+/-- Applying the forwarding core commutes with configuration transport:
+selected tapes update identically, the frame stays fixed, and appending
+the optional emission associates with the existing output prefix. -/
+private lemma embedEmit_apply (ι : Fin m ↪ Fin k)
+    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
+    (pre : List Bool) (c : Cfg m Bool S x) (a : Action m Bool S) :
+    (embedActionCore ι none a).apply (embedEmitCfg ι tapes heads pre c) =
+      embedEmitCfg ι tapes heads pre (a.apply c) := by
+  refine Cfg.ext rfl rfl ?_ ?_ ?_
+  · funext j
+    cases hs : embedSlot ι j <;>
+      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
+  · funext j
+    cases hs : embedSlot ι j <;>
+      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
+  · simp [embedActionCore, embedEmitCfg, Action.apply, List.append_assoc]
+
+/-- The forwarding host reads the same source action and executes it
+completely in one step, including an emission on a halting transition. -/
+private lemma embedEmit_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
+    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
+    (pre : List Bool) (c : Cfg m Bool S x) :
+    (embedEmitTM ι M).step (embedEmitCfg ι tapes heads pre c) =
+      embedEmitCfg ι tapes heads pre (M.step c) := by
+  unfold MultiTapeTM.step
+  cases hs : c.state with
+  | none => simp [embedEmitCfg, hs]
+  | some q =>
+    rw [show (embedEmitCfg ι tapes heads pre c).state = some q from hs]
+    dsimp only
+    have hr : (fun i => (embedEmitCfg ι tapes heads pre c).workTapeSymbols
+        (ι i)) = c.workTapeSymbols := by
+      funext i
+      simp [Cfg.workTapeSymbols, embedEmitCfg, embedSlot_selected]
+    change (embedActionCore ι none (M.tr q c.inputSymbol _)).apply _ = _
+    rw [hr]
+    exact embedEmit_apply ι tapes heads pre c _
 
 /-- **R1 lockstep, forwarding flavor** (spec, fill pending — design §12;
 [Bon26], `rename_executes`). The transported run is the transport of the
@@ -367,7 +529,8 @@ theorem embedEmitTM_runFrom (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
     (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
     (embedEmitTM ι M).runFrom (embedEmitCfg ι tapes heads pre c) t =
       embedEmitCfg ι tapes heads pre (M.runFrom c t) := by
-  sorry
+  exact MultiTapeTM.runFrom_comm_of_step (embedEmitCfg ι tapes heads pre)
+    (embedEmit_step ι M tapes heads pre) c t
 
 /-- **R1 frame, forwarding flavor** (spec, fill pending — design §12).
 Along the whole transported run, every host tape outside the selected
@@ -391,7 +554,10 @@ theorem embedEmitTM_frame (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
     ((embedEmitTM ι M).runFrom
         (embedEmitCfg ι tapes heads pre c) t).output
       = pre ++ (M.runFrom c t).output := by
-  sorry
+  rw [embedEmitTM_runFrom]
+  refine ⟨?_, rfl, rfl⟩
+  intro j hj
+  simp [embedEmitCfg, embedSlot_unselected ι j hj]
 
 /-- **R1 space, forwarding flavor, selected tapes** (spec, fill pending —
 design §12). The visited set of host tape `ι i` up to time `t` is exactly
@@ -410,7 +576,15 @@ theorem embedEmitTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
     (embedEmitTM ι M).spaceUsedByTape
         (embedEmitCfg ι tapes heads pre c) t (ι i)
       = M.spaceUsedByTape c t i := by
-  sorry
+  have hv : (embedEmitTM ι M).visitedByTapeHead
+      (embedEmitCfg ι tapes heads pre c) t (ι i) =
+      M.visitedByTapeHead c t i := by
+    unfold MultiTapeTM.visitedByTapeHead
+    congr 1
+    funext u
+    rw [embedEmitTM_runFrom]
+    simp [embedEmitCfg, embedSlot_selected]
+  exact ⟨hv, congrArg Finset.card hv⟩
 
 /-- **R1 space, forwarding flavor, unselected tapes** (spec, fill
 pending — design §12). A host tape outside the selected bank visits
@@ -428,7 +602,14 @@ theorem embedEmitTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
         (embedEmitCfg ι tapes heads pre c) t j = {heads j} ∧
     (embedEmitTM ι M).spaceUsedByTape
         (embedEmitCfg ι tapes heads pre c) t j = 1 := by
-  sorry
+  have hv : (embedEmitTM ι M).visitedByTapeHead
+      (embedEmitCfg ι tapes heads pre c) t j = {heads j} := by
+    unfold MultiTapeTM.visitedByTapeHead
+    simp_rw [embedEmitTM_runFrom]
+    simp only [embedEmitCfg, embedSlot_unselected ι j hj]
+    exact Finset.image_const ⟨0, by simp⟩ _
+  refine ⟨hv, ?_⟩
+  simp [MultiTapeTM.spaceUsedByTape, hv]
 
 /-- **R1′, the returning suppressing embedding** (round-1 repair R1). As
 `Turing.embedSilentTM`, on states `S ⊕ Unit`: live source states run the
@@ -466,6 +647,120 @@ def embedEmitRetTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S) :
         some (a.state.elim (Sum.inr ()) Sum.inl)⟩
     | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩
 
+/-- Replace an action's optional successor by the live return encoding,
+without changing any input, work-tape, or output effect. -/
+private def embedReturnAction (a : Action k Bool S) : Action k Bool (S ⊕ Unit) :=
+  ⟨a.inputTape, a.workTapes, a.output, some (a.state.elim (Sum.inr ()) Sum.inl)⟩
+
+/-- Encode a closed host configuration with live left states and a live
+right return anchor, preserving all four non-control fields. -/
+private def embedReturnCfg (c : Cfg k Bool S x) : Cfg k Bool (S ⊕ Unit) x :=
+  { c with state := some (c.state.elim (Sum.inr ()) Sum.inl) }
+
+/-- At a live configuration, the return encoding is ordinary left state
+mapping; at a halt it instead uses the live right anchor. -/
+private lemma embedReturnCfg_live (c : Cfg k Bool S x) (hc : c.state ≠ none) :
+    embedReturnCfg c = c.mapState Sum.inl := by
+  cases hs : c.state with
+  | none => exact (hc hs).elim
+  | some q => simp [embedReturnCfg, Cfg.mapState, hs]
+
+/-- Direct comparison of a closed host step with a returning host step.
+**Proof sketch.** At a live left state, both hosts execute the same action
+and only the successor encoding differs. At a closed halt, the returning
+anchor's idle action preserves every non-control field, just as absorption
+does on the closed side. No property of a source embedding is needed. -/
+private lemma embedReturn_step (N : MultiTapeTM k Bool S)
+    (R : MultiTapeTM k Bool (S ⊕ Unit))
+    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
+      embedReturnAction (N.tr q inp work))
+    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
+      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
+    (c : Cfg k Bool S x) :
+    R.step (embedReturnCfg c) = embedReturnCfg (N.step c) := by
+  unfold MultiTapeTM.step
+  cases hs : c.state with
+  | none => simp [embedReturnCfg, hs, hidle, Action.apply]
+  | some q =>
+    rw [show (embedReturnCfg c).state = some (Sum.inl q) by
+      simp [embedReturnCfg, hs]]
+    dsimp only
+    have hin : (embedReturnCfg c).inputSymbol = c.inputSymbol := rfl
+    have hw : (embedReturnCfg c).workTapeSymbols = c.workTapeSymbols := rfl
+    rw [hin, hw, hleft]
+    rfl
+
+/-- The silent returning step executes the entire transported source
+action, then encodes its successor as a live left state or return anchor. -/
+private lemma embedSilentRet_step (ι : Fin m ↪ Fin k) (cap : Fin k)
+    (M : MultiTapeTM m Bool S)
+    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
+    (pre out₀ : List Bool) (c : Cfg m Bool S x) (hc : c.state ≠ none) :
+    (embedSilentRetTM ι cap M).step
+        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) =
+      embedReturnCfg (embedSilentCfg ι cap tapes heads pre out₀ (M.step c)) := by
+  have h := embedReturn_step (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
+    (fun _ _ _ => rfl) (fun _ _ => rfl)
+    (embedSilentCfg ι cap tapes heads pre out₀ c)
+  rw [embedReturnCfg_live (embedSilentCfg ι cap tapes heads pre out₀ c) hc,
+    embedSilent_step] at h
+  exact h
+
+/-- A live-step transport reaches the return anchor exactly at a positive
+first halt, with all transported data intact.
+**Proof sketch.** The initially live state and terminal halt imply positive
+time. Induct over the strict live prefix, where the successor encoding is
+ordinary left mapping. Execute the step from the last live configuration
+separately; its halted successor encodes the return anchor. Earlier states
+are left constructors, so none is the right anchor. -/
+private lemma embedThroughHalt (M : MultiTapeTM m Bool S)
+    (R : MultiTapeTM k Bool (S ⊕ Unit))
+    (E : Cfg m Bool S x → Cfg k Bool S x)
+    (hstate : ∀ d, (E d).state = d.state)
+    (hstep : ∀ d, d.state ≠ none →
+      R.step ((E d).mapState Sum.inl) = embedReturnCfg (E (M.step d)))
+    (c : Cfg m Bool S x) (T : ℕ) (hc : c.state ≠ none)
+    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
+    (hhalt : (M.runFrom c T).state = none) :
+    (∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
+      (E (M.runFrom c t)).mapState Sum.inl) ∧
+    R.runFrom ((E c).mapState Sum.inl) T =
+      { E (M.runFrom c T) with state := some (Sum.inr ()) } ∧
+    ∀ t < T, (R.runFrom ((E c).mapState Sum.inl) t).state ≠
+      some (Sum.inr ()) := by
+  have hT : 0 < T := by
+    by_contra hn
+    have hz : T = 0 := by omega
+    subst T
+    exact hc (by simpa using hhalt)
+  have hrun : ∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
+      (E (M.runFrom c t)).mapState Sum.inl := by
+    intro t
+    induction t with
+    | zero => intro _; rfl
+    | succ t ih =>
+      intro ht
+      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
+        hstep _ (hlive t (by omega)), ← MultiTapeTM.runFrom_succ_eq_step']
+      apply embedReturnCfg_live
+      rw [hstate]
+      exact hlive _ ht
+  refine ⟨hrun, ?_, ?_⟩
+  · have hlast : T - 1 + 1 = T := by omega
+    calc
+      R.runFrom ((E c).mapState Sum.inl) T =
+          R.step (R.runFrom ((E c).mapState Sum.inl) (T - 1)) :=
+        (congrArg (R.runFrom ((E c).mapState Sum.inl)) hlast).symm.trans
+          MultiTapeTM.runFrom_succ_eq_step'
+      _ = embedReturnCfg (E (M.runFrom c T)) := by
+        rw [hrun _ (by omega), hstep _ (hlive _ (by omega)),
+          ← MultiTapeTM.runFrom_succ_eq_step', hlast]
+      _ = _ := by simp [embedReturnCfg, hstate, hhalt]
+  · intro t ht
+    rw [hrun t ht]
+    simp only [Cfg.mapState, hstate]
+    cases (M.runFrom c t).state <;> simp
+
 /-- **R1′ through-halt contract, suppressing flavor** (spec, fill pending —
 round-1 repair R1): if the source first halts at time `T`, the returning
 embedding runs in `Sum.inl`-lockstep through every live time and, at `T`,
@@ -511,7 +806,21 @@ theorem embedSilentRetTM_run (ι : Fin m ↪ Fin k) (cap : Fin k)
       ((embedSilentRetTM ι cap M).runFrom
           ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl)
           t).state ≠ some (Sum.inr ()) := by
-  sorry
+  exact embedThroughHalt M (embedSilentRetTM ι cap M)
+    (embedSilentCfg ι cap tapes heads pre out₀) (fun _ => rfl)
+    (embedSilentRet_step ι cap M tapes heads pre out₀) c T hc hlive hhalt
+
+/-- The forwarding returning step preserves the complete source action,
+including its final emission, and changes only the successor encoding. -/
+private lemma embedEmitRet_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
+    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
+    (pre : List Bool) (c : Cfg m Bool S x) (hc : c.state ≠ none) :
+    (embedEmitRetTM ι M).step ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) =
+      embedReturnCfg (embedEmitCfg ι tapes heads pre (M.step c)) := by
+  have h := embedReturn_step (embedEmitTM ι M) (embedEmitRetTM ι M)
+    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c)
+  rw [embedReturnCfg_live (embedEmitCfg ι tapes heads pre c) hc, embedEmit_step] at h
+  exact h
 
 /-- **R1′ through-halt contract, forwarding flavor** (spec, fill pending —
 round-1 repair R1): as `Turing.embedSilentRetTM_run` with the final
@@ -544,7 +853,35 @@ theorem embedEmitRetTM_run (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
       ((embedEmitRetTM ι M).runFrom
           ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t).state ≠
         some (Sum.inr ()) := by
-  sorry
+  exact embedThroughHalt M (embedEmitRetTM ι M)
+    (embedEmitCfg ι tapes heads pre) (fun _ => rfl)
+    (embedEmitRet_step ι M tapes heads pre) c T hc hlive hhalt
+
+/-- Direct host comparison preserves every visited-head set, from any
+initial configuration and for every finite horizon.
+**Proof sketch.** Initially halted configurations stay halted on both
+sides. From a live start, iterate the direct step comparison under the
+return encoding, whose head positions are unchanged. Equality of the
+head trajectories gives equality of their finite images. This uses no
+termination hypothesis, source simulation, or capture-tape separation. -/
+private lemma embedReturn_visited (N : MultiTapeTM k Bool S)
+    (R : MultiTapeTM k Bool (S ⊕ Unit))
+    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
+      embedReturnAction (N.tr q inp work))
+    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
+      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
+    (c : Cfg k Bool S x) (t : ℕ) (j : Fin k) :
+    R.visitedByTapeHead (c.mapState Sum.inl) t j = N.visitedByTapeHead c t j := by
+  unfold MultiTapeTM.visitedByTapeHead
+  congr 1
+  funext u
+  by_cases hc : c.state = none
+  · rw [R.runFrom_of_halt _ (by simp [Cfg.mapState, hc]), N.runFrom_of_halt _ hc]
+    rfl
+  · have hrun := MultiTapeTM.runFrom_comm_of_step embedReturnCfg
+      (embedReturn_step N R hleft hidle) c u
+    rw [embedReturnCfg_live c hc] at hrun
+    exact congrArg (fun d => d.workTapePos j) hrun
 
 /-- **R1′ space, suppressing flavor** (spec, fill pending — round-1 repair
 R1): at every time and on every tape, the returning embedding's visited set
@@ -555,7 +892,11 @@ at the live anchor while the other sits halted, both stationary.
 **Proof sketch.** For `t` up to the first source halt, both machines apply
 identical tape actions (`embedSilentRetTM_run`'s lockstep and the halting
 step's shared core); beyond it, the anchor's idle action and the halted
-absorption are both stationary, freezing both visited sets. -/
+absorption are both stationary, freezing both visited sets.
+
+**Fill appendix.** The direct host comparison `embedReturn_visited`
+handles initially halted and live starts separately. It uses neither
+through-halt contract nor a capture-separation hypothesis. -/
 theorem embedSilentRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
     (M : MultiTapeTM m Bool S)
     (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
@@ -564,7 +905,9 @@ theorem embedSilentRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
         ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t j =
       (embedSilentTM ι cap M).visitedByTapeHead
         (embedSilentCfg ι cap tapes heads pre out₀ c) t j := by
-  sorry
+  exact embedReturn_visited (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
+    (fun _ _ _ => rfl) (fun _ _ => rfl)
+    (embedSilentCfg ι cap tapes heads pre out₀ c) t j
 
 /-- **R1′ space, forwarding flavor** (spec, fill pending — round-1 repair
 R1): the forwarding analogue of
@@ -582,6 +925,7 @@ theorem embedEmitRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
         ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t j =
       (embedEmitTM ι M).visitedByTapeHead
         (embedEmitCfg ι tapes heads pre c) t j := by
-  sorry
+  exact embedReturn_visited (embedEmitTM ι M) (embedEmitRetTM ι M)
+    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c) t j
 
 end Turing
-- 
2.51.1
```


## ===== audits/evidence/routine-f1-batchB.patch =====

```
From 4938f0fe9610c724d6c011f44013307ac285303a Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Fri, 9 Oct 2026 13:38:59 +0800
Subject: [PATCH] Fill section-12 seam composition and release proofs

---
 .../Complexity/TuringMachine/Build/Seam.lean  | 264 +++++++++++++++++-
 1 file changed, 253 insertions(+), 11 deletions(-)

diff --git a/TCSlib/Complexity/TuringMachine/Build/Seam.lean b/TCSlib/Complexity/TuringMachine/Build/Seam.lean
index ef9ebc4b..8d88eac9 100644
--- a/TCSlib/Complexity/TuringMachine/Build/Seam.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/Seam.lean
@@ -123,6 +123,163 @@ def seamCompTM [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
       let a := M₂.tr s inp w
       ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩
 
+/-- Away from the exit, one left step is exactly the state-mapped source step,
+including the absorbing halted case. -/
+private lemma seamComp_step_left [DecidableEq S₁]
+    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
+    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
+    (c : Cfg k Bool S₁ x) (hc : c.state ≠ some exit) :
+    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inl) =
+      (M₁.step c).mapState Sum.inl := by
+  cases hs : c.state with
+  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
+  | some q =>
+    have hq : q ≠ exit := fun h => hc (hs.trans (congrArg some h))
+    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
+    dsimp only [seamCompTM]
+    rw [if_neg hq]
+    rfl
+
+/-- Right steps commute with state mapping, even after a source halt. -/
+private lemma seamComp_step_right [DecidableEq S₁]
+    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
+    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂) (c : Cfg k Bool S₂ x) :
+    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inr) =
+      (M₂.step c).mapState Sum.inr := by
+  cases hs : c.state with
+  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
+  | some q =>
+    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
+    rfl
+
+/-- A stationary, silent, write-free action changes only the control field. -/
+private lemma seam_stationary_apply (c : Cfg k Bool S₁ x) (q : S₁) :
+    (Action.mk 0 (fun _ => (none, 0)) none (some q)).apply c =
+      { c with state := some q } := by
+  simp [Action.apply]
+
+/-- Dispatch preserves all data of an arbitrary live exit configuration. -/
+private lemma seamComp_dispatch [DecidableEq S₁]
+    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
+    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
+    (c : Cfg k Bool S₁ x) (hc : c.state = some exit) :
+    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inl) =
+      (c.mapState fun _ => entry).mapState Sum.inr := by
+  unfold MultiTapeTM.step
+  simp only [Cfg.mapState, hc, Option.map_some]
+  dsimp only [seamCompTM]
+  rw [if_pos rfl, seam_stationary_apply]
+
+/-- The whole left trajectory agrees through the exit time.
+**Proof sketch.** Induct on the time; the cut licenses the left-step
+identity at every predecessor strictly before the endpoint. -/
+private lemma seamComp_left [DecidableEq S₁]
+    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
+    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
+    {c : Cfg k Bool S₁ x} {T : ℕ}
+    (hcut : ∀ t < T, (M₁.runFrom c t).state ≠ some exit)
+    (t : ℕ) (ht : t ≤ T) :
+    (seamCompTM M₁ exit M₂ entry).runFrom (c.mapState Sum.inl) t =
+      (M₁.runFrom c t).mapState Sum.inl := by
+  induction t with
+  | zero => rfl
+  | succ t ih =>
+    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
+      seamComp_step_left M₁ exit M₂ entry _ (hcut t (by omega)),
+      MultiTapeTM.runFrom_succ_eq_step']
+
+/-- After the one-step dispatch, the entire right trajectory agrees.
+**Proof sketch.** Split the run at the dispatch, use left lockstep and
+the exit equation, then iterate the unconditional right-step identity. -/
+private lemma seamComp_right [DecidableEq S₁]
+    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
+    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
+    {c₀ c₁ : Cfg k Bool S₁ x} {T₁ : ℕ}
+    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
+    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (t : ℕ) :
+    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
+        (T₁ + 1 + t) =
+      (M₂.runFrom (c₁.mapState fun _ => entry) t).mapState Sum.inr := by
+  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step',
+    seamComp_left M₁ exit M₂ entry hcut T₁ le_rfl, h₁,
+    seamComp_dispatch M₁ exit M₂ entry c₁ hexit]
+  exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
+    (seamComp_step_right M₁ exit M₂ entry) _ t
+
+/-- General endpoint composition, shared by the frozen public forms. -/
+private lemma seamComp_run_general [DecidableEq S₁]
+    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
+    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
+    {c₀ c₁ : Cfg k Bool S₁ x} {c₃ : Cfg k Bool S₂ x} {T₁ T₂ : ℕ}
+    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
+    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
+    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) :
+    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
+        (T₁ + 1 + T₂) = c₃.mapState Sum.inr :=
+  (seamComp_right M₁ exit M₂ entry h₁ hexit hcut T₂).trans
+    (congrArg (Cfg.mapState Sum.inr) h₂)
+
+/-- The right final anchor is absent before the total time.
+**Proof sketch.** Through the left endpoint, constructor disjointness
+excludes the anchor. Afterwards, right lockstep transports the phase-two
+cut at the time remaining after dispatch. -/
+private lemma seamComp_firstReturn_general [DecidableEq S₁]
+    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
+    (M₂ : MultiTapeTM k Bool S₂) (entry q₂ : S₂)
+    {c₀ c₁ : Cfg k Bool S₁ x} {T₁ T₂ : ℕ}
+    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
+    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
+    (hcut₂ : ∀ t < T₂,
+      (M₂.runFrom (c₁.mapState fun _ => entry) t).state ≠ some q₂) :
+    ∀ t < T₁ + 1 + T₂,
+      ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
+        some (Sum.inr q₂) := by
+  intro t ht
+  by_cases hleft : t ≤ T₁
+  · rw [seamComp_left M₁ exit M₂ entry hcut t hleft]
+    cases (M₁.runFrom c₀ t).state <;> simp [Cfg.mapState]
+  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
+    rw [htime, seamComp_right M₁ exit M₂ entry h₁ hexit hcut]
+    intro heq
+    apply hcut₂ (t - (T₁ + 1)) (by omega)
+    change Option.map Sum.inr
+      (M₂.runFrom (c₁.mapState fun _ => entry) (t - (T₁ + 1))).state =
+        some (Sum.inr q₂) at heq
+    obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp heq
+    exact hq.trans (congrArg some (Sum.inr.inj heq))
+
+/-- Every visited position belongs to one of the two exact run segments.
+**Proof sketch.** A time at most the left duration uses left lockstep.
+Every later time is dispatch time plus a unique nonnegative offset, at
+most the right duration; right lockstep supplies its image witness. -/
+private lemma seamComp_visited_general [DecidableEq S₁]
+    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
+    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
+    {c₀ c₁ : Cfg k Bool S₁ x} {T₁ T₂ : ℕ}
+    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
+    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (i : Fin k) :
+    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead (c₀.mapState Sum.inl)
+        (T₁ + 1 + T₂) i ⊆
+      M₁.visitedByTapeHead c₀ T₁ i ∪
+        M₂.visitedByTapeHead (c₁.mapState fun _ => entry) T₂ i := by
+  intro z hz
+  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
+  have ht' := Finset.mem_range.mp ht
+  by_cases hleft : t ≤ T₁
+  · rw [seamComp_left M₁ exit M₂ entry hcut t hleft]
+    apply Finset.mem_union_left
+    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
+  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
+    rw [htime, seamComp_right M₁ exit M₂ entry h₁ hexit hcut]
+    apply Finset.mem_union_right
+    exact Finset.mem_image.mpr
+      ⟨t - (T₁ + 1), Finset.mem_range.mpr (by omega), rfl⟩
+
+/-- State mapping of a canonical seam changes only its anchor. -/
+private lemma seam_ofWords_mapState {S₃ : Type*} (f : S₁ → S₃)
+    (q : S₁) (w : Fin k → List Bool) :
+    (Cfg.ofWords (input := x) q w).mapState f = Cfg.ofWords (f q) w := rfl
+
 /-- **R2, seam-to-seam composition** (spec, fill pending — design §12;
 [Bon26], `executes_in_sum`). If `M₁` carries the seam
 `Cfg.ofWords start w₀` to the seam `Cfg.ofWords exit w₁` in exactly `T₁`
@@ -159,7 +316,12 @@ theorem seamCompTM_run [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
     (seamCompTM M₁ exit M₂ entry).runFrom
         (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) =
       Cfg.ofWords (Sum.inr q₂) w₂ := by
-  sorry
+  have h₂' : M₂.runFrom
+      ((Cfg.ofWords (input := x) exit w₁).mapState fun _ => entry) T₂ =
+        Cfg.ofWords q₂ w₂ := by
+    simpa only [seam_ofWords_mapState] using h₂
+  simpa only [seam_ofWords_mapState] using
+    seamComp_run_general M₁ exit M₂ entry h₁ rfl hcut h₂'
 
 /-- **R2, the inherited first-return cut** (spec, fill pending — design
 §12). Under the hypotheses of `seamCompTM_run`, if additionally `M₂` does
@@ -190,7 +352,12 @@ theorem seamCompTM_firstReturn [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S
       ((seamCompTM M₁ exit M₂ entry).runFrom
           (Cfg.ofWords (input := x) (Sum.inl start) w₀) t).state ≠
         some (Sum.inr q₂) := by
-  sorry
+  have hcut₂' : ∀ t < T₂,
+      (M₂.runFrom ((Cfg.ofWords (input := x) exit w₁).mapState fun _ => entry)
+        t).state ≠ some q₂ := by
+    simpa only [seam_ofWords_mapState] using hcut₂
+  simpa only [seam_ofWords_mapState] using
+    seamComp_firstReturn_general M₁ exit M₂ entry q₂ h₁ rfl hcut hcut₂'
 
 /-- **R2 space, the per-tape headline** (spec, fill pending — design §12,
 frozen decision 12.1: the sharp per-tape form). On every work tape `i`,
@@ -223,7 +390,8 @@ theorem seamCompTM_visitedByTapeHead [DecidableEq S₁]
         (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ⊆
       M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i ∪
         M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i := by
-  sorry
+  simpa only [seam_ofWords_mapState] using
+    seamComp_visited_general (T₂ := T₂) M₁ exit M₂ entry h₁ rfl hcut i
 
 /-- **R2 space, the per-tape sum corollary** (spec, fill pending — design
 §12, decision 12.1). On every work tape, the composite's space usage is
@@ -245,7 +413,9 @@ theorem seamCompTM_spaceUsedByTape_le_add [DecidableEq S₁]
         (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ≤
       M₁.spaceUsedByTape (Cfg.ofWords (input := x) start w₀) T₁ i +
         M₂.spaceUsedByTape (Cfg.ofWords (input := x) entry w₁) T₂ i := by
-  sorry
+  exact (Finset.card_le_card
+    (seamCompTM_visitedByTapeHead M₁ exit M₂ entry start q₂ w₀ w₁ w₂
+      T₁ T₂ h₁ hcut h₂ i)).trans (Finset.card_union_le _ _)
 
 /-- **R2 space, the total sum corollary** (spec, fill pending — design
 §12). The composite's total space usage is at most the sum of the
@@ -267,7 +437,11 @@ theorem seamCompTM_spaceUsed_le_add [DecidableEq S₁]
         (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) ≤
       M₁.spaceUsed (Cfg.ofWords (input := x) start w₀) T₁ +
         M₂.spaceUsed (Cfg.ofWords (input := x) entry w₁) T₂ := by
-  sorry
+  unfold MultiTapeTM.spaceUsed
+  rw [← Finset.sum_add_distrib]
+  exact Finset.sum_le_sum fun i _ =>
+    seamCompTM_spaceUsedByTape_le_add M₁ exit M₂ entry start q₂ w₀ w₁ w₂
+      T₁ T₂ h₁ hcut h₂ i
 
 /-- **R2 space, the max corollary for disjointly-owned tapes** (spec, fill
 pending — design §12, frozen decision 12.1: the sharpest available form).
@@ -301,7 +475,21 @@ theorem seamCompTM_spaceUsedByTape_le_max [DecidableEq S₁]
         (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ≤
       max (M₁.spaceUsedByTape (Cfg.ofWords (input := x) start w₀) T₁ i)
         (M₂.spaceUsedByTape (Cfg.ofWords (input := x) entry w₁) T₂ i) := by
-  sorry
+  have hzero₁ : (0 : ℤ) ∈
+      M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i :=
+    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ T₁), rfl⟩
+  have hzero₂ : (0 : ℤ) ∈
+      M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i :=
+    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ T₂), rfl⟩
+  have hsub := seamCompTM_visitedByTapeHead M₁ exit M₂ entry start q₂
+    w₀ w₁ w₂ T₁ T₂ h₁ hcut h₂ i
+  rcases hown with hown | hown
+  · rw [hown, Finset.union_eq_right.mpr
+      (Finset.singleton_subset_iff.mpr hzero₂)] at hsub
+    exact (Finset.card_le_card hsub).trans (le_max_right _ _)
+  · rw [hown, Finset.union_eq_left.mpr
+      (Finset.singleton_subset_iff.mpr hzero₁)] at hsub
+    exact (Finset.card_le_card hsub).trans (le_max_left _ _)
 
 /-- **R2′, general-configuration seam-to-seam composition** (spec, fill
 pending — round-1 repair R2): the `Cfg.ofWords` restriction of
@@ -335,7 +523,7 @@ theorem seamCompTM_run_ofCfg [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
     (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
         (T₁ + 1 + T₂) =
       c₃.mapState Sum.inr := by
-  sorry
+  exact seamComp_run_general M₁ exit M₂ entry h₁ hexit hcut h₂
 
 /-- **R2′, the general inherited first-return cut** (spec, fill pending —
 round-1 repair R2): under the hypotheses of
@@ -359,7 +547,7 @@ theorem seamCompTM_firstReturn_ofCfg [DecidableEq S₁]
     ∀ t < T₁ + 1 + T₂,
       ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
         some (Sum.inr q₂) := by
-  sorry
+  exact seamComp_firstReturn_general M₁ exit M₂ entry q₂ h₁ hexit hcut hcut₂
 
 /-- **R2′ space, the general per-tape headline** (spec, fill pending —
 round-1 repair R2): under the hypotheses of `Turing.seamCompTM_run_ofCfg`,
@@ -381,7 +569,7 @@ theorem seamCompTM_visitedByTapeHead_ofCfg [DecidableEq S₁]
         (T₁ + 1 + T₂) i ⊆
       M₁.visitedByTapeHead c₀ T₁ i ∪
         M₂.visitedByTapeHead (c₁.mapState fun _ => entry) T₂ i := by
-  sorry
+  exact seamComp_visited_general M₁ exit M₂ entry h₁ hexit hcut i
 
 variable {S : Type*}
 
@@ -408,6 +596,40 @@ def seamReleaseTM (M : MultiTapeTM k Bool S) (anchor : S) :
       let a := M.tr s inp w
       ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩
 
+/-- The fresh state executes the anchor action without a dispatch step. -/
+private lemma seamRelease_fresh_step (M : MultiTapeTM k Bool S) (anchor : S)
+    (c : Cfg k Bool S x) (hc : c.state = some anchor) :
+    (seamReleaseTM M anchor).step (c.mapState fun _ => Sum.inl ()) =
+      (M.step c).mapState Sum.inr := by
+  simp only [MultiTapeTM.step, Cfg.mapState, hc, Option.map_some]
+  rfl
+
+/-- In the right copy, release steps commute with state mapping. -/
+private lemma seamRelease_step_right (M : MultiTapeTM k Bool S) (anchor : S)
+    (c : Cfg k Bool S x) :
+    (seamReleaseTM M anchor).step (c.mapState Sum.inr) =
+      (M.step c).mapState Sum.inr := by
+  cases hs : c.state with
+  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
+  | some q =>
+    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
+    rfl
+
+/-- At every positive time, release runs are the right-mapped source runs.
+**Proof sketch.** Execute the fresh step once, then iterate the right-step
+identity. This also covers a source that halts or never returns. -/
+private lemma seamRelease_run_pos (M : MultiTapeTM k Bool S) (anchor : S)
+    (c : Cfg k Bool S x) (hc : c.state = some anchor) (t : ℕ) (ht : 0 < t) :
+    (seamReleaseTM M anchor).runFrom (c.mapState fun _ => Sum.inl ()) t =
+      (M.runFrom c t).mapState Sum.inr := by
+  cases t with
+  | zero => omega
+  | succ t =>
+    rw [MultiTapeTM.runFrom_succ_eq_step, seamRelease_fresh_step M anchor c hc,
+      MultiTapeTM.runFrom_succ_eq_step]
+    exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
+      (seamRelease_step_right M anchor) _ t
+
 /-- **R3′, the positive first return through the adapter** (spec, fill
 pending — round-1 repair R3): if `M`, started at its anchor, first
 re-visits the anchor at a strictly positive time `T`, then the adapter,
@@ -433,7 +655,19 @@ theorem seamReleaseTM_firstReturn (M : MultiTapeTM k Bool S) (anchor : S)
         ((seamReleaseTM M anchor).runFrom
             (c.mapState fun _ => Sum.inl ()) t).state ≠
           some (Sum.inr anchor) := by
-  sorry
+  constructor
+  · rw [seamRelease_run_pos M anchor c hc T hT, h]
+  · intro t ht
+    by_cases htpos : 0 < t
+    · rw [seamRelease_run_pos M anchor c hc t htpos]
+      intro heq
+      apply hcut t htpos ht
+      change Option.map Sum.inr (M.runFrom c t).state =
+        some (Sum.inr anchor) at heq
+      obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp heq
+      exact hq.trans (congrArg some (Sum.inr.inj heq))
+    · have htzero : t = 0 := by omega
+      simp [htzero, Cfg.mapState, hc]
 
 /-- **R3′ space** (spec, fill pending — round-1 repair R3): the adapter's
 visited sets equal `M`'s at every time and on every tape — the trajectories
@@ -449,6 +683,14 @@ theorem seamReleaseTM_visitedByTapeHead (M : MultiTapeTM k Bool S)
     (seamReleaseTM M anchor).visitedByTapeHead
         (c.mapState fun _ => Sum.inl ()) t i =
       M.visitedByTapeHead c t i := by
-  sorry
+  unfold MultiTapeTM.visitedByTapeHead
+  apply Finset.image_congr
+  intro s _
+  dsimp only
+  by_cases hs : s = 0
+  · subst s
+    rfl
+  · rw [seamRelease_run_pos M anchor c hc s (Nat.pos_of_ne_zero hs)]
+    rfl
 
 end Turing
-- 
2.51.1
```


## ===== audits/evidence/routine-f1-batchC.patch =====

```
From 4daaf8767c1b275cdf6a19dbec4ecee6dd513d83 Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Fri, 9 Oct 2026 13:40:52 +0800
Subject: [PATCH] Prove the thirteen epoch-F1 catalog and wrapper contracts

---
 .../TuringMachine/Build/Catalog.lean          | 865 +++++++++++++++++-
 1 file changed, 852 insertions(+), 13 deletions(-)

diff --git a/TCSlib/Complexity/TuringMachine/Build/Catalog.lean b/TCSlib/Complexity/TuringMachine/Build/Catalog.lean
index 3b6303a6..b239b408 100644
--- a/TCSlib/Complexity/TuringMachine/Build/Catalog.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/Catalog.lean
@@ -282,6 +282,592 @@ def incrementTM (k : ℕ) (i : Fin k) : MultiTapeTM k Bool FlagPhase where
           none, some (.done v)⟩
     | .done v => ⟨0, fun _ => (none, 0), none, some (.done v)⟩
 
+/-- Configuration at a scan position, with explicit words and head positions. -/
+private def catalogCfg {S : Type*} (q : S) (w : Fin k → List Bool)
+    (heads : Fin k → ℤ) : Cfg k Bool S x :=
+  { Cfg.ofWords q w with workTapePos := heads }
+
+/-- The chronological trace of a forward scan, left turn, return, and entry.
+The return index is the number of nonblank cells still to erase or cross. -/
+private def catalogTrace {S : Type*} (F R : ℕ → Cfg k Bool S x)
+    (D : Cfg k Bool S x) (L t : ℕ) : Cfg k Bool S x :=
+  if t ≤ L then F t else if t ≤ 2 * L + 1 then R (2 * L + 1 - t) else D
+
+/-- Local transition equations determine the complete trace, including all
+stationary steps after the exit. **Proof sketch.** Induct on elapsed time;
+split at the forward endpoint, return endpoint, and stationary tail. -/
+private lemma catalog_trace_run {S : Type*} (M : MultiTapeTM k Bool S)
+    (F R : ℕ → Cfg k Bool S x) (D : Cfg k Bool S x) (L : ℕ)
+    (hF : ∀ r < L, M.step (F r) = F (r + 1))
+    (hturn : M.step (F L) = R L)
+    (hR : ∀ r < L, M.step (R (r + 1)) = R r)
+    (hentry : M.step (R 0) = D) (hD : M.step D = D) (t : ℕ) :
+    M.runFrom (F 0) t = catalogTrace F R D L t := by
+  induction t with
+  | zero => simp [catalogTrace]
+  | succ t ih =>
+    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
+    by_cases h₁ : t < L
+    · simpa [catalogTrace, show t ≤ L by omega, show t + 1 ≤ L by omega]
+        using hF t h₁
+    · by_cases h₂ : t = L
+      · subst t
+        simpa [catalogTrace, show ¬L + 1 ≤ L by omega,
+          show L + 1 ≤ 2 * L + 1 by omega, show 2 * L + 1 - (L + 1) = L by omega]
+          using hturn
+      · by_cases h₃ : t < 2 * L + 1
+        · have he : 2 * L + 1 - t = (2 * L - t) + 1 := by omega
+          simpa [catalogTrace, show ¬t ≤ L by omega, show ¬t + 1 ≤ L by omega,
+            show t ≤ 2 * L + 1 by omega, show t + 1 ≤ 2 * L + 1 by omega,
+            he, show 2 * L + 1 - (t + 1) = 2 * L - t by omega]
+            using hR (2 * L - t) (by omega)
+        · by_cases h₄ : t = 2 * L + 1
+          · subst t
+            simpa [catalogTrace, show ¬2 * L + 1 ≤ L by omega,
+              show ¬2 * L + 1 + 1 ≤ L by omega] using hentry
+          · simpa [catalogTrace, show ¬t ≤ L by omega,
+              show ¬t + 1 ≤ L by omega, show ¬t ≤ 2 * L + 1 by omega,
+              show ¬t + 1 ≤ 2 * L + 1 by omega] using hD
+
+/-- A head confined to the inclusive interval from minus one to `L` visits
+at most `L+2` cells. -/
+private lemma catalog_space_bound {S : Type*} (M : MultiTapeTM k Bool S)
+    (c : Cfg k Bool S x) (L t : ℕ) (i : Fin k)
+    (h : ∀ u, -1 ≤ (M.runFrom c u).workTapePos i ∧
+      (M.runFrom c u).workTapePos i ≤ (L : ℤ)) :
+    M.spaceUsedByTape c t i ≤ L + 2 := by
+  have hs : M.visitedByTapeHead c t i ⊆ Finset.Icc (-1 : ℤ) (L : ℤ) := by
+    intro z hz
+    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
+    exact Finset.mem_Icc.mpr (h u)
+  exact (Finset.card_le_card hs).trans (by rw [Int.card_Icc]; omega)
+
+/-- A head stationary at zero has exactly its origin singleton as visited set. -/
+private lemma catalog_space_one {S : Type*} (M : MultiTapeTM k Bool S)
+    (c : Cfg k Bool S x) (t : ℕ) (i : Fin k)
+    (h : ∀ u, (M.runFrom c u).workTapePos i = 0) :
+    M.spaceUsedByTape c t i = 1 := by
+  simp only [MultiTapeTM.spaceUsedByTape, MultiTapeTM.visitedByTapeHead, h]
+  rw [Finset.image_const Finset.nonempty_range_add_one]
+  rfl
+
+/-- Erasing the last cell of a prefix shortens that prefix by one.
+**Proof sketch.** Read the last cell, earlier cells, and outside cells separately. -/
+private lemma catalog_erase_take (w : List Bool) (r : ℕ) (hr : r < w.length) :
+    Function.update (FinTM.bufferTape (w.take (r + 1))) (r : ℤ) none =
+      FinTM.bufferTape (w.take r) := by
+  funext z
+  by_cases hz : z = (r : ℤ)
+  · subst z
+    simp [FinTM.bufferTape, List.getElem?_eq_none]
+  · rw [Function.update_of_ne hz]
+    by_cases h0 : 0 ≤ z
+    · simp only [FinTM.bufferTape, if_pos h0]
+      by_cases hzr : z.toNat < r
+      · simp [List.getElem?_take, hzr, show z.toNat < r + 1 by omega]
+      · have hzr' : r + 1 ≤ z.toNat := by omega
+        rw [List.getElem?_eq_none (by simp; omega),
+          List.getElem?_eq_none (by simp; omega)]
+    · simp [FinTM.bufferTape, h0]
+
+/-- Appending the next original bit extends a copied prefix by one. -/
+private lemma catalog_write_take (w : List Bool) (r : ℕ) (hr : r < w.length) :
+    Function.update (FinTM.bufferTape (w.take r)) (r : ℤ) (some w[r]) =
+      FinTM.bufferTape (w.take (r + 1)) := by
+  rw [List.take_succ_eq_append_getElem hr]
+  simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hr)] using
+    (FinTM.bufferTape_append (w.take r) w[r]).symm
+
+/-- Clear's forward phase has intact words; the return phase retains exactly
+the unerased prefix below and at the head. -/
+private def catalogClearF (i : Fin k) (w : Fin k → List Bool) (r : ℕ) :
+    Cfg k Bool SweepPhase x :=
+  catalogCfg .sweep w (fun j => if j = i then (r : ℤ) else 0)
+
+/-- Clear's return index counts the remaining unerased cells. -/
+private def catalogClearR (i : Fin k) (w : Fin k → List Bool) (r : ℕ) :
+    Cfg k Bool SweepPhase x :=
+  catalogCfg .rewind (Function.update w i ((w i).take r))
+    (fun j => if j = i then (r : ℤ) - 1 else 0)
+
+/-- Clear's exact phase invariant. **Proof sketch.** During the scan the
+word is intact. The turn reads its right blank. Each return transition erases
+just the last remaining cell; the final left blank makes the right-entry. -/
+private lemma catalog_clear_trace (i : Fin k) (w : Fin k → List Bool) (t : ℕ) :
+    (clearTM k i).runFrom (Cfg.ofWords (input := x) .sweep w) t =
+      catalogTrace (catalogClearF i w) (catalogClearR i w)
+        (Cfg.ofWords .done (Function.update w i [])) (w i).length t := by
+  have h0 : catalogClearF (x := x) i w 0 = Cfg.ofWords .sweep w := by
+    apply Cfg.ext <;> simp [catalogClearF, catalogCfg, Cfg.ofWords]
+  rw [← h0]
+  apply catalog_trace_run
+  · intro r hr
+    have hs : (catalogClearF (x := x) i w r).workTapeSymbols i = some (w i)[r] := by
+      simp [catalogClearF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
+        FinTM.bufferTape_nat, List.getElem?_eq_getElem hr]
+    change ((clearTM k i).tr .sweep _ _).apply _ = _
+    simp only [clearTM, hs]
+    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogCfg, Cfg.ofWords]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
+  · have hs : (catalogClearF (x := x) i w (w i).length).workTapeSymbols i = none := by
+      simp [catalogClearF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
+    change ((clearTM k i).tr .sweep _ _).apply _ = _
+    simp only [clearTM, hs]
+    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
+    · funext j
+      by_cases hj : j = i <;> simp [hj]
+    · funext j
+      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
+  · intro r hr
+    have hs : (catalogClearR (x := x) i w (r + 1)).workTapeSymbols i =
+        some (w i)[r] := by
+      simp [catalogClearR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
+        show (r + 1 : ℕ) - (1 : ℤ) = (r : ℤ) by omega,
+        List.getElem?_take, List.getElem?_eq_getElem hr]
+    change ((clearTM k i).tr .rewind _ _).apply _ = _
+    simp only [clearTM, hs]
+    apply Cfg.ext <;> simp [Action.apply, catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
+    · funext j
+      by_cases hj : j = i
+      · subst j
+        simpa [show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using
+          catalog_erase_take (w i) r hr
+      · simp [hj]
+    · funext j
+      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
+  · apply Cfg.ext <;>
+      simp [MultiTapeTM.step, clearTM, catalogClearR, catalogCfg, Cfg.ofWords,
+        Cfg.workTapeSymbols, Action.apply]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast]
+  · apply Cfg.ext <;>
+      simp [MultiTapeTM.step, clearTM, Cfg.ofWords, Action.apply]
+
+/-- Copy and transfer share the forward phase: the destination holds the copied
+prefix and the source remains intact, with both heads at its end. -/
+private def catalogCopyF (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
+    Cfg k Bool SweepPhase x :=
+  catalogCfg .sweep (Function.update w dst ((w src).take r))
+    (fun j => if j = src ∨ j = dst then (r : ℤ) else 0)
+
+/-- During copy's return the words are complete and unchanged. -/
+private def catalogCopyR (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
+    Cfg k Bool SweepPhase x :=
+  catalogCfg .rewind (Function.update w dst (w src))
+    (fun j => if j = src ∨ j = dst then (r : ℤ) - 1 else 0)
+
+/-- During transfer's return the source retains exactly the unerased prefix. -/
+private def catalogTransferR (src dst : Fin k) (w : Fin k → List Bool) (r : ℕ) :
+    Cfg k Bool SweepPhase x :=
+  catalogCfg .rewind (Function.update (Function.update w src ((w src).take r)) dst (w src))
+    (fun j => if j = src ∨ j = dst then (r : ℤ) - 1 else 0)
+
+/-- The common forward transition copies exactly the next source bit. -/
+private lemma catalog_copy_forward (src dst : Fin k) (hne : src ≠ dst)
+    (w : Fin k → List Bool) (r : ℕ) (hr : r < (w src).length) :
+    (copyTM k src dst).step (catalogCopyF (x := x) src dst w r) =
+      catalogCopyF src dst w (r + 1) := by
+  have hs : (catalogCopyF (x := x) src dst w r).workTapeSymbols src =
+      some (w src)[r] := by
+    simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
+      List.getElem?_eq_getElem hr]
+  change ((copyTM k src dst).tr .sweep _ _).apply _ = _
+  simp only [copyTM, hs]
+  apply Cfg.ext <;> simp [Action.apply, catalogCopyF, catalogCfg, Cfg.ofWords]
+  · funext j
+    by_cases hj : j = dst
+    · subst j
+      simpa using catalog_write_take (w src) r hr
+    · by_cases hs : j = src <;> simp [hj, hs, hne, Ne.symm hne]
+  · funext j
+    by_cases hd : j = dst <;> by_cases hs : j = src <;>
+      simp [hd, hs, hne, SignType.cast] <;> omega
+
+/-- Copy's exact phase invariant, including the stationary exit. -/
+private lemma catalog_copy_trace (src dst : Fin k) (hne : src ≠ dst)
+    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
+    (copyTM k src dst).runFrom (Cfg.ofWords (input := x) .sweep w) t =
+      catalogTrace (catalogCopyF src dst w) (catalogCopyR src dst w)
+        (Cfg.ofWords .done (Function.update w dst (w src))) (w src).length t := by
+  have h0 : catalogCopyF (x := x) src dst w 0 = Cfg.ofWords .sweep w := by
+    apply Cfg.ext <;> simp [catalogCopyF, catalogCfg, Cfg.ofWords]
+    funext j
+    by_cases hj : j = dst
+    · subst j; simp [hdst]
+    · simp [hj]
+  rw [← h0]
+  apply catalog_trace_run
+  · exact catalog_copy_forward src dst hne w
+  · have hs : (catalogCopyF (x := x) src dst w (w src).length).workTapeSymbols src =
+        none := by
+      simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne]
+    change ((copyTM k src dst).tr .sweep _ _).apply _ = _
+    simp only [copyTM, hs]
+    apply Cfg.ext <;> simp [Action.apply, catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
+  · intro r hr
+    have hs : (catalogCopyR (x := x) src dst w (r + 1)).workTapeSymbols src =
+        some (w src)[r] := by
+      simp [catalogCopyR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
+        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
+        List.getElem?_eq_getElem hr]
+    change ((copyTM k src dst).tr .rewind _ _).apply _ = _
+    simp only [copyTM, hs]
+    apply Cfg.ext <;> simp [Action.apply, catalogCopyR, catalogCfg, Cfg.ofWords]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
+  · apply Cfg.ext <;>
+      simp [MultiTapeTM.step, copyTM, catalogCopyR, catalogCfg, Cfg.ofWords,
+        Cfg.workTapeSymbols, hne, Action.apply]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast]
+  · apply Cfg.ext <;>
+      simp [MultiTapeTM.step, copyTM, Cfg.ofWords, Action.apply]
+
+/-- Transfer's exact phase invariant. The forward transitions are copy's;
+on return, erasure is behind the head, leaving every cell still to read intact. -/
+private lemma catalog_transfer_trace (src dst : Fin k) (hne : src ≠ dst)
+    (w : Fin k → List Bool) (hdst : w dst = []) (t : ℕ) :
+    (transferTM k src dst).runFrom (Cfg.ofWords (input := x) .sweep w) t =
+      catalogTrace (catalogCopyF src dst w) (catalogTransferR src dst w)
+        (Cfg.ofWords .done (Function.update (Function.update w src []) dst (w src)))
+        (w src).length t := by
+  have h0 : catalogCopyF (x := x) src dst w 0 = Cfg.ofWords .sweep w := by
+    apply Cfg.ext <;> simp [catalogCopyF, catalogCfg, Cfg.ofWords]
+    funext j
+    by_cases hj : j = dst
+    · subst j; simp [hdst]
+    · simp [hj]
+  rw [← h0]
+  apply catalog_trace_run
+  · intro r hr
+    exact catalog_copy_forward src dst hne w r hr
+  · have hs : (catalogCopyF (x := x) src dst w (w src).length).workTapeSymbols src =
+        none := by
+      simp [catalogCopyF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne]
+    change ((transferTM k src dst).tr .sweep _ _).apply _ = _
+    simp only [transferTM, hs]
+    apply Cfg.ext <;>
+      simp [Action.apply, catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords]
+    · funext j
+      by_cases hd : j = dst <;> by_cases hs : j = src <;> simp [hd, hs]
+    · funext j
+      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
+  · intro r hr
+    have hs : (catalogTransferR (x := x) src dst w (r + 1)).workTapeSymbols src =
+        some (w src)[r] := by
+      simp [catalogTransferR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
+        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
+        List.getElem?_take, List.getElem?_eq_getElem hr]
+    change ((transferTM k src dst).tr .rewind _ _).apply _ = _
+    simp only [transferTM, hs]
+    apply Cfg.ext <;> simp [Action.apply, catalogTransferR, catalogCfg, Cfg.ofWords]
+    · funext j
+      by_cases hs : j = src
+      · subst j
+        simpa [hne, show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using
+          catalog_erase_take (w src) r hr
+      · by_cases hd : j = dst
+        · subst j; simp [hne, Ne.symm hne]
+        · simp [hs, hd]
+    · funext j
+      by_cases hs : j = src <;> by_cases hd : j = dst <;>
+        simp [hs, hd, hne, Ne.symm hne, SignType.cast] <;> omega
+  · apply Cfg.ext <;>
+      simp [MultiTapeTM.step, transferTM, catalogTransferR, catalogCfg, Cfg.ofWords,
+        Cfg.workTapeSymbols, hne, Action.apply]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast]
+  · apply Cfg.ext <;>
+      simp [MultiTapeTM.step, transferTM, Cfg.ofWords, Action.apply]
+
+/-- The first unequal or terminating cells occur after a common nonblank
+prefix, and equality at those terminating cells is precisely word equality.
+**Proof sketch.** Remove equal leading bits recursively; unequal bits or either
+empty list stop immediately. This also covers aliased physical tape indices. -/
+private lemma catalog_compare_stop (u v : List Bool) :
+    ∃ d ≤ min u.length v.length,
+      (∀ r < d, ∃ b, u[r]? = some b ∧ v[r]? = some b) ∧
+      (¬∃ b, u[d]? = some b ∧ v[d]? = some b) ∧
+      (u[d]? = v[d]? ↔ u = v) := by
+  induction u generalizing v with
+  | nil =>
+    cases v with
+    | nil => exact ⟨0, by simp, by simp, by simp, by simp⟩
+    | cons b v => exact ⟨0, by simp, by simp, by simp, by simp⟩
+  | cons a u ih =>
+    cases v with
+    | nil => exact ⟨0, by simp, by simp, by simp, by simp⟩
+    | cons b v =>
+      by_cases hab : a = b
+      · subst b
+        obtain ⟨d, hd, hp, hs, he⟩ := ih v
+        refine ⟨d + 1, by simpa using hd, ?_, ?_, ?_⟩
+        · intro r hr
+          cases r with
+          | zero => exact ⟨a, rfl, rfl⟩
+          | succ r => simpa using hp r (by omega)
+        · simpa using hs
+        · simpa using he
+      · refine ⟨0, by simp, by simp, ?_, ?_⟩
+        · simpa [eq_comm] using hab
+        · simp [hab]
+
+/-- Comparison's forward configuration retains every word and advances the
+selected physical heads once each, including when the two indices coincide. -/
+private def catalogCompareF (fst snd : Fin k) (w : Fin k → List Bool) (r : ℕ) :
+    Cfg k Bool FlagPhase x :=
+  catalogCfg .run w (fun j => if j = fst ∨ j = snd then (r : ℤ) else 0)
+
+/-- Comparison's return configuration carries the verdict without changing words. -/
+private def catalogCompareR (fst snd : Fin k) (w : Fin k → List Bool)
+    (v : Bool) (r : ℕ) : Cfg k Bool FlagPhase x :=
+  catalogCfg (.rewind v) w
+    (fun j => if j = fst ∨ j = snd then (r : ℤ) - 1 else 0)
+
+/-- Comparison's exact configuration invariant, at a first differing or blank
+position. **Proof sketch.** The common-prefix condition supplies every forward
+read and every first-tape return read. The stopping condition determines the
+turn and verdict. The heads then return from `d-1` through `-1` to zero. -/
+private lemma catalog_compare_trace (fst snd : Fin k) (w : Fin k → List Bool)
+    (d : ℕ) (hd : d ≤ min (w fst).length (w snd).length)
+    (hp : ∀ r < d, ∃ b, (w fst)[r]? = some b ∧ (w snd)[r]? = some b)
+    (hs : ¬∃ b, (w fst)[d]? = some b ∧ (w snd)[d]? = some b)
+    (he : ((w fst)[d]? = (w snd)[d]?) ↔ w fst = w snd) (t : ℕ) :
+    (compareTM k fst snd).runFrom (Cfg.ofWords (input := x) .run w) t =
+      catalogTrace (catalogCompareF fst snd w)
+        (catalogCompareR fst snd w (decide (w fst = w snd)))
+        (Cfg.ofWords (.done (decide (w fst = w snd))) w) d t := by
+  have h0 : catalogCompareF (x := x) fst snd w 0 = Cfg.ofWords .run w := by
+    apply Cfg.ext <;> simp [catalogCompareF, catalogCfg, Cfg.ofWords]
+  rw [← h0]
+  apply catalog_trace_run
+  · intro r hr
+    obtain ⟨b, hf, hg⟩ := hp r hr
+    have hsf : (catalogCompareF (x := x) fst snd w r).workTapeSymbols fst = some b := by
+      simpa [catalogCompareF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols] using hf
+    have hsg : (catalogCompareF (x := x) fst snd w r).workTapeSymbols snd = some b := by
+      simpa [catalogCompareF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols] using hg
+    change ((compareTM k fst snd).tr .run _ _).apply _ = _
+    simp only [compareTM, hsf, hsg, ↓reduceIte]
+    apply Cfg.ext <;> simp [Action.apply, catalogCompareF, catalogCfg, Cfg.ofWords]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
+  · have hread : (catalogCompareF (x := x) fst snd w d).workTapeSymbols =
+        fun j => FinTM.bufferTape (w j) (if j = fst ∨ j = snd then (d : ℤ) else 0) := rfl
+    have ht : (compareTM k fst snd).tr .run
+        (catalogCompareF (x := x) fst snd w d).inputSymbol
+        (catalogCompareF (x := x) fst snd w d).workTapeSymbols =
+        ⟨0, (fun j => if j = fst ∨ j = snd then (none, SignType.neg) else (none, 0)),
+          none, some (.rewind (decide (w fst = w snd)))⟩ := by
+      simp only [compareTM, hread, if_pos (Or.inl rfl : fst = fst ∨ fst = snd),
+        if_pos (Or.inr rfl : snd = fst ∨ snd = snd), FinTM.bufferTape_nat]
+      cases hf : (w fst)[d]? with
+      | none =>
+        cases hg : (w snd)[d]? with
+        | none =>
+          have heq : w fst = w snd := he.mp (by rw [hf, hg])
+          simp [hf, hg, heq]
+        | some b =>
+          have hneq : w fst ≠ w snd := by
+            intro h
+            have h' := he.mpr h
+            simp only [hf, hg, reduceCtorEq] at h'
+          simp [hf, hg, hneq]
+      | some a =>
+        cases hg : (w snd)[d]? with
+        | none =>
+          have hneq : w fst ≠ w snd := by
+            intro h
+            have h' := he.mpr h
+            simp only [hf, hg, reduceCtorEq] at h'
+          simp [hf, hg, hneq]
+        | some b =>
+          have hab : a ≠ b := by
+            intro h
+            subst b
+            exact hs ⟨a, hf, hg⟩
+          have hneq : w fst ≠ w snd := by
+            intro h
+            have h' := he.mpr h
+            exact hab (by simpa only [hf, hg, Option.some.injEq] using h')
+          simp [hf, hg, hab, hneq]
+    change ((compareTM k fst snd).tr .run _ _).apply _ = _
+    rw [ht]
+    apply Cfg.ext <;> simp [Action.apply, catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
+  · intro r hr
+    obtain ⟨b, hf, _⟩ := hp r hr
+    have hread : (catalogCompareR (x := x) fst snd w (decide (w fst = w snd))
+        (r + 1)).workTapeSymbols fst = some b := by
+      simpa [catalogCompareR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
+        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega] using hf
+    change ((compareTM k fst snd).tr (.rewind _) _ _).apply _ = _
+    simp only [compareTM, hread]
+    apply Cfg.ext <;> simp [Action.apply, catalogCompareR, catalogCfg, Cfg.ofWords]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
+  · apply Cfg.ext <;>
+      simp [MultiTapeTM.step, compareTM, catalogCompareR, catalogCfg, Cfg.ofWords,
+        Cfg.workTapeSymbols, Action.apply]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast]
+  · apply Cfg.ext <;>
+      simp [MultiTapeTM.step, compareTM, Cfg.ofWords, Action.apply]
+
+/-- A word consists of its leading true bits followed by either a first false
+bit and its tail, or no remaining bits. -/
+private lemma catalog_increment_split (w : List Bool) :
+    ∃ p : ℕ, ∃ tail : Option (List Bool),
+      w = List.replicate p true ++ tail.elim [] (false :: ·) := by
+  induction w with
+  | nil => exact ⟨0, none, rfl⟩
+  | cons b w ih =>
+    cases b with
+    | false => exact ⟨0, some w, rfl⟩
+    | true =>
+      obtain ⟨p, tail, hw⟩ := ih
+      exact ⟨p + 1, tail, by simp [List.replicate_succ, hw]⟩
+
+/-- Fixed-width increment flips the leading true prefix and the first false;
+an absent first false gives overflow. -/
+private lemma catalog_increment_value (p : ℕ) (tail : Option (List Bool)) :
+    incFixed (List.replicate p true ++ tail.elim [] (false :: ·)) =
+      tail.map (fun v => List.replicate p false ++ true :: v) := by
+  induction p with
+  | zero => cases tail <;> rfl
+  | succ p ih =>
+    simp only [List.replicate_succ, List.cons_append, incFixed, ih]
+    cases tail <;> rfl
+
+/-- Changing the cell immediately after a prefix changes exactly that bit.
+**Proof sketch.** At the selected cell use list indexing at the prefix length;
+elsewhere, the suffix and prefix lookups are unchanged. -/
+private lemma catalog_write_middle (pre rest : List Bool) (a b : Bool) :
+    Function.update (FinTM.bufferTape (pre ++ a :: rest)) (pre.length : ℤ) (some b) =
+      FinTM.bufferTape (pre ++ b :: rest) := by
+  funext z
+  by_cases hz : z = (pre.length : ℤ)
+  · subst z
+    simp [FinTM.bufferTape]
+  · rw [Function.update_of_ne hz]
+    by_cases h0 : 0 ≤ z
+    · simp only [FinTM.bufferTape, if_pos h0, List.getElem?_append]
+      by_cases hlt : z.toNat < pre.length
+      · simp [hlt]
+      · have he : z.toNat - pre.length = (z.toNat - pre.length - 1) + 1 := by omega
+        simp only [if_neg hlt]
+        rw [he]
+        rfl
+    · simp [FinTM.bufferTape, h0]
+
+/-- Increment's carry configuration: the first `r` bits have been reset, the
+remaining true prefix and stopping suffix are intact, and the head is at `r`. -/
+private def catalogIncF (i : Fin k) (w : Fin k → List Bool) (p : ℕ)
+    (tail : Option (List Bool)) (r : ℕ) : Cfg k Bool FlagPhase x :=
+  catalogCfg .run (Function.update w i
+    (List.replicate r false ++ List.replicate (p - r) true ++ tail.elim [] (false :: ·)))
+    (fun j => if j = i then (r : ℤ) else 0)
+
+/-- Increment's return configuration holds the complete updated or wrapped
+word and carries the success bit, with the head immediately before cell `r`. -/
+private def catalogIncR (i : Fin k) (w : Fin k → List Bool) (p : ℕ)
+    (tail : Option (List Bool)) (r : ℕ) : Cfg k Bool FlagPhase x :=
+  catalogCfg (.rewind tail.isSome)
+    (Function.update w i (List.replicate p false ++ tail.elim [] (true :: ·)))
+    (fun j => if j = i then (r : ℤ) - 1 else 0)
+
+/-- Increment's exact phase invariant. **Proof sketch.** Each carry step resets
+one true bit; the first false is changed on the left-turn itself, so cell `p+1`
+is not visited. With no false, the right blank turns without writing. Both cases
+return over the reset prefix and enter the live exit after exactly `2p+2` steps. -/
+private lemma catalog_increment_trace (i : Fin k) (w : Fin k → List Bool)
+    (p : ℕ) (tail : Option (List Bool))
+    (hw : w i = List.replicate p true ++ tail.elim [] (false :: ·)) (t : ℕ) :
+    (incrementTM k i).runFrom (Cfg.ofWords (input := x) .run w) t =
+      catalogTrace (catalogIncF i w p tail) (catalogIncR i w p tail)
+        (Cfg.ofWords (.done tail.isSome)
+          (Function.update w i (List.replicate p false ++ tail.elim [] (true :: ·)))) p t := by
+  have h0 : catalogIncF (x := x) i w p tail 0 = Cfg.ofWords .run w := by
+    apply Cfg.ext <;> simp [catalogIncF, catalogCfg, Cfg.ofWords, ← hw]
+  rw [← h0]
+  apply catalog_trace_run
+  · intro r hr
+    have hpr : p - r = (p - (r + 1)) + 1 := by omega
+    have hs : (catalogIncF (x := x) i w p tail r).workTapeSymbols i = some true := by
+      simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
+        hpr, List.replicate_succ, List.append_assoc]
+    change ((incrementTM k i).tr .run _ _).apply _ = _
+    simp only [incrementTM, hs]
+    apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogCfg, Cfg.ofWords]
+    · funext j
+      by_cases hj : j = i
+      · subst j
+        have hh := catalog_write_middle (List.replicate r false)
+          (List.replicate (p - (r + 1)) true ++ tail.elim [] (false :: ·)) true false
+        simp only [ite_true, Function.update_self]
+        rw [hpr, List.replicate_succ, List.cons_append]
+        simpa only [List.length_replicate, List.replicate_succ',
+          List.append_assoc, List.singleton_append] using hh
+      · simp [hj]
+    · funext j
+      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
+  · cases tail with
+    | none =>
+      have hs : (catalogIncF (x := x) i w p none p).workTapeSymbols i = none := by
+        simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
+      change ((incrementTM k i).tr .run _ _).apply _ = _
+      simp only [incrementTM, hs]
+      apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
+      all_goals
+        funext j
+        split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
+    | some v =>
+      have hs : (catalogIncF (x := x) i w p (some v) p).workTapeSymbols i = some false := by
+        simp [catalogIncF, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols]
+      change ((incrementTM k i).tr .run _ _).apply _ = _
+      simp only [incrementTM, hs]
+      apply Cfg.ext <;> simp [Action.apply, catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
+      · funext j
+        by_cases hj : j = i
+        · subst j
+          simpa using catalog_write_middle (List.replicate p false) v false true
+        · simp [hj]
+      · funext j
+        split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg]
+  · intro r hr
+    have hs : (catalogIncR (x := x) i w p tail (r + 1)).workTapeSymbols i = some false := by
+      simp [catalogIncR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
+        show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
+        List.getElem?_append, hr]
+    change ((incrementTM k i).tr (.rewind _) _ _).apply _ = _
+    simp only [incrementTM, hs]
+    apply Cfg.ext <;> simp [Action.apply, catalogIncR, catalogCfg, Cfg.ofWords]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast, sub_eq_add_neg] <;> omega
+  · apply Cfg.ext <;>
+      simp [MultiTapeTM.step, incrementTM, catalogIncR, catalogCfg, Cfg.ofWords,
+        Cfg.workTapeSymbols, Action.apply]
+    all_goals
+      funext j
+      split_ifs <;> simp_all [SignType.cast]
+  · apply Cfg.ext <;>
+      simp [MultiTapeTM.step, incrementTM, Cfg.ofWords, Action.apply]
+
 /-- **Transfer, the run contract** (spec, fill pending — design §12 R3;
 [Bon26]). From the seam with word `w src` on the source and a blank
 destination, the routine reaches — within `3|w src| + 3` steps and
@@ -305,7 +891,14 @@ theorem transferTM_run (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
           (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
         Cfg.ofWords SweepPhase.done
           (Function.update (Function.update w src []) dst (w src)) := by
-  sorry
+  refine ⟨2 * (w src).length + 2, by omega, ?_, ?_⟩
+  · intro t ht
+    rw [catalog_transfer_trace src dst hne w hdst]
+    simp only [catalogTrace]
+    split_ifs <;> simp_all [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords]
+    omega
+  · rw [catalog_transfer_trace src dst hne w hdst]
+    simp [catalogTrace, show ¬2 * (w src).length + 2 ≤ (w src).length by omega]
 
 /-- **Transfer, per-tape space** (spec, fill pending — design §12 R3).
 The two touched tapes visit at most the word interval plus the two
@@ -328,7 +921,21 @@ theorem transferTM_spaceUsedByTape (k : ℕ) (src dst : Fin k)
     ∀ j : Fin k, j ≠ src → j ≠ dst →
       (transferTM k src dst).spaceUsedByTape
           (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
-  sorry
+  have hb (j : Fin k) : (transferTM k src dst).spaceUsedByTape
+      (Cfg.ofWords (input := x) .sweep w) t j ≤ (w src).length + 2 := by
+    apply catalog_space_bound
+    intro u
+    rw [catalog_transfer_trace src dst hne w hdst]
+    simp only [catalogTrace]
+    split_ifs <;> simp only [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords] <;>
+      (try split_ifs) <;> omega
+  refine ⟨hb src, hb dst, ?_⟩
+  intro j hs hd
+  apply catalog_space_one
+  intro u
+  rw [catalog_transfer_trace src dst hne w hdst]
+  simp only [catalogTrace]
+  split_ifs <;> simp [catalogCopyF, catalogTransferR, catalogCfg, Cfg.ofWords, hs, hd]
 
 /-- **Copy, the run contract** (spec, fill pending — design §12 R3;
 [Bon26]; the A3 `3|w| + 3` row). From the seam with word `w src` on the
@@ -348,7 +955,14 @@ theorem copyTM_run (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
       (copyTM k src dst).runFrom
           (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
         Cfg.ofWords SweepPhase.done (Function.update w dst (w src)) := by
-  sorry
+  refine ⟨2 * (w src).length + 2, by omega, ?_, ?_⟩
+  · intro t ht
+    rw [catalog_copy_trace src dst hne w hdst]
+    simp only [catalogTrace]
+    split_ifs <;> simp_all [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords]
+    omega
+  · rw [catalog_copy_trace src dst hne w hdst]
+    simp [catalogTrace, show ¬2 * (w src).length + 2 ≤ (w src).length by omega]
 
 /-- **Copy, per-tape space** (spec, fill pending — design §12 R3). As the
 transfer routine: the two touched tapes visit at most `|w src| + 2` cells
@@ -369,7 +983,21 @@ theorem copyTM_spaceUsedByTape (k : ℕ) (src dst : Fin k) (hne : src ≠ dst)
     ∀ j : Fin k, j ≠ src → j ≠ dst →
       (copyTM k src dst).spaceUsedByTape
           (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
-  sorry
+  have hb (j : Fin k) : (copyTM k src dst).spaceUsedByTape
+      (Cfg.ofWords (input := x) .sweep w) t j ≤ (w src).length + 2 := by
+    apply catalog_space_bound
+    intro u
+    rw [catalog_copy_trace src dst hne w hdst]
+    simp only [catalogTrace]
+    split_ifs <;> simp only [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords] <;>
+      (try split_ifs) <;> omega
+  refine ⟨hb src, hb dst, ?_⟩
+  intro j hs hd
+  apply catalog_space_one
+  intro u
+  rw [catalog_copy_trace src dst hne w hdst]
+  simp only [catalogTrace]
+  split_ifs <;> simp [catalogCopyF, catalogCopyR, catalogCfg, Cfg.ofWords, hs, hd]
 
 /-- **Clear, the run contract** (spec, fill pending — design §12 R3;
 [Bon26]; the A3 `2|w| + 2` row, P12's engine). From the seam with word
@@ -389,7 +1017,14 @@ theorem clearTM_run (k : ℕ) (i : Fin k) (w : Fin k → List Bool) :
       (clearTM k i).runFrom
           (Cfg.ofWords (input := x) SweepPhase.sweep w) T =
         Cfg.ofWords SweepPhase.done (Function.update w i []) := by
-  sorry
+  refine ⟨2 * (w i).length + 2, le_rfl, ?_, ?_⟩
+  · intro t ht
+    rw [catalog_clear_trace]
+    simp only [catalogTrace]
+    split_ifs <;> simp_all [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords]
+    omega
+  · rw [catalog_clear_trace]
+    simp [catalogTrace, show ¬2 * (w i).length + 2 ≤ (w i).length by omega]
 
 /-- **Clear, per-tape space** (spec, fill pending — design §12 R3). Tape
 `i` visits at most `|w i| + 2` cells (the word interval plus both
@@ -406,7 +1041,18 @@ theorem clearTM_spaceUsedByTape (k : ℕ) (i : Fin k)
     ∀ j : Fin k, j ≠ i →
       (clearTM k i).spaceUsedByTape
           (Cfg.ofWords (input := x) SweepPhase.sweep w) t j = 1 := by
-  sorry
+  constructor
+  · apply catalog_space_bound
+    intro u
+    rw [catalog_clear_trace]
+    simp only [catalogTrace]
+    split_ifs <;> simp [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords] <;> omega
+  · intro j hj
+    apply catalog_space_one
+    intro u
+    rw [catalog_clear_trace]
+    simp only [catalogTrace]
+    split_ifs <;> simp [catalogClearF, catalogClearR, catalogCfg, Cfg.ofWords, hj]
 
 /-- **Compare, the run contract** (spec, fill pending — design §12 R3;
 [Bon26]). From the seam, the routine reaches — within
@@ -430,7 +1076,15 @@ theorem compareTM_run (k : ℕ) (fst snd : Fin k) (w : Fin k → List Bool) :
       (compareTM k fst snd).runFrom
           (Cfg.ofWords (input := x) FlagPhase.run w) T =
         Cfg.ofWords (FlagPhase.done (decide (w fst = w snd))) w := by
-  sorry
+  obtain ⟨d, hd, hp, hs, he⟩ := catalog_compare_stop (w fst) (w snd)
+  refine ⟨2 * d + 2, by omega, ?_, ?_⟩
+  · intro t ht v
+    rw [catalog_compare_trace fst snd w d hd hp hs he]
+    simp only [catalogTrace]
+    split_ifs <;> simp_all [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords]
+    omega
+  · rw [catalog_compare_trace fst snd w d hd hp hs he]
+    simp [catalogTrace, show ¬2 * d + 2 ≤ d by omega]
 
 /-- **Compare, per-tape space** (spec, fill pending — design §12 R3). The
 two compared tapes visit at most `min(|w fst|, |w snd|) + 2` cells (the
@@ -456,7 +1110,22 @@ theorem compareTM_spaceUsedByTape (k : ℕ) (fst snd : Fin k)
     ∀ j : Fin k, j ≠ fst → j ≠ snd →
       (compareTM k fst snd).spaceUsedByTape
           (Cfg.ofWords (input := x) FlagPhase.run w) t j = 1 := by
-  sorry
+  obtain ⟨d, hd, hp, hs, he⟩ := catalog_compare_stop (w fst) (w snd)
+  have hb (j : Fin k) : (compareTM k fst snd).spaceUsedByTape
+      (Cfg.ofWords (input := x) .run w) t j ≤ d + 2 := by
+    apply catalog_space_bound
+    intro u
+    rw [catalog_compare_trace fst snd w d hd hp hs he]
+    simp only [catalogTrace]
+    split_ifs <;> simp only [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords] <;>
+      (try split_ifs) <;> omega
+  refine ⟨(hb fst).trans (by omega), (hb snd).trans (by omega), ?_⟩
+  intro j hf hg
+  apply catalog_space_one
+  intro u
+  rw [catalog_compare_trace fst snd w d hd hp hs he]
+  simp only [catalogTrace]
+  split_ifs <;> simp [catalogCompareF, catalogCompareR, catalogCfg, Cfg.ofWords, hf, hg]
 
 /-- **Increment, the success contract** (spec, fill pending — design §12
 R3). If the word on tape `i` has a successor at its width
@@ -481,7 +1150,21 @@ theorem incrementTM_run_succ (k : ℕ) (i : Fin k) (w : Fin k → List Bool)
       (incrementTM k i).runFrom
           (Cfg.ofWords (input := x) FlagPhase.run w) T =
         Cfg.ofWords (FlagPhase.done true) (Function.update w i v) := by
-  sorry
+  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
+  rw [hw, catalog_increment_value] at hv
+  cases tail with
+  | none => simp at hv
+  | some tail =>
+    have hv' : v = List.replicate p false ++ true :: tail := by simpa using hv.symm
+    have hp : p < (w i).length := by simp [hw]
+    refine ⟨2 * p + 2, by omega, ?_, ?_⟩
+    · intro t ht b
+      rw [catalog_increment_trace i w p (some tail) hw]
+      simp only [catalogTrace]
+      split_ifs <;> simp_all [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
+      omega
+    · rw [catalog_increment_trace i w p (some tail) hw]
+      simp [catalogTrace, show ¬2 * p + 2 ≤ p by omega, hv']
 
 /-- **Increment, the overflow contract** (spec, fill pending — design §12
 R3). If the word on tape `i` is all `true` (`Turing.incFixed (w i) =
@@ -504,7 +1187,20 @@ theorem incrementTM_run_overflow (k : ℕ) (i : Fin k)
           (Cfg.ofWords (input := x) FlagPhase.run w) T =
         Cfg.ofWords (FlagPhase.done false)
           (Function.update w i (List.replicate (w i).length false)) := by
-  sorry
+  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
+  rw [hw, catalog_increment_value] at hv
+  cases tail with
+  | some tail => simp at hv
+  | none =>
+    have hp : (w i).length = p := by simp [hw]
+    refine ⟨2 * p + 2, by omega, ?_, ?_⟩
+    · intro t ht b
+      rw [catalog_increment_trace i w p none hw]
+      simp only [catalogTrace]
+      split_ifs <;> simp_all [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords]
+      omega
+    · rw [catalog_increment_trace i w p none hw]
+      simp [catalogTrace, show ¬2 * p + 2 ≤ p by omega, hp]
 
 /-- **Increment, per-tape space** (spec, fill pending — design §12 R3).
 Tape `i` visits at most `|w i| + 2` cells; every other tape exactly its
@@ -521,7 +1217,23 @@ theorem incrementTM_spaceUsedByTape (k : ℕ) (i : Fin k)
     ∀ j : Fin k, j ≠ i →
       (incrementTM k i).spaceUsedByTape
           (Cfg.ofWords (input := x) FlagPhase.run w) t j = 1 := by
-  sorry
+  obtain ⟨p, tail, hw⟩ := catalog_increment_split (w i)
+  have hp : p ≤ (w i).length := by simp [hw]
+  constructor
+  · have hb : (incrementTM k i).spaceUsedByTape
+        (Cfg.ofWords (input := x) .run w) t i ≤ p + 2 := by
+      apply catalog_space_bound
+      intro u
+      rw [catalog_increment_trace i w p tail hw]
+      simp only [catalogTrace]
+      split_ifs <;> simp [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords] <;> omega
+    omega
+  · intro j hj
+    apply catalog_space_one
+    intro u
+    rw [catalog_increment_trace i w p tail hw]
+    simp only [catalogTrace]
+    split_ifs <;> simp [catalogIncF, catalogIncR, catalogCfg, Cfg.ofWords, hj]
 
 /-- **W1 space row** (spec, fill pending — design §12 R3, decision 12.3).
 Under the hypotheses of `Turing.capture_run`, the host's source-bank
@@ -550,7 +1262,41 @@ theorem capture_visitedByTapeHead {k : ℕ} {S H : Type*} {x : List Bool}
         = tm.spaceUsedByTape c₀ t i) ∧
     host.spaceUsedByTape (captureCfg emb ret pre out₀ c₀) t (Fin.last k)
       ≤ (tm.runFrom c₀ t).output.length - c₀.output.length + 1 := by
-  sorry
+  have hr (u : ℕ) (hu : u ≤ t) :=
+    capture_run tm host emb ret hagree pre out₀ c₀ u
+      (fun v hv => hlive v (by omega))
+  constructor
+  · intro i
+    have he : host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t i.castSucc =
+        tm.visitedByTapeHead c₀ t i := by
+      unfold MultiTapeTM.visitedByTapeHead
+      apply Finset.image_congr
+      intro u hu
+      dsimp only
+      rw [hr u (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hu))]
+      simp [captureCfg, i.isLt]
+    exact ⟨he, congrArg Finset.card he⟩
+  · have hmono {u v : ℕ} (huv : u ≤ v) :
+        (tm.runFrom c₀ u).output.length ≤ (tm.runFrom c₀ v).output.length :=
+      (tm.output_prefix c₀ huv).length_le
+    have hbound : c₀.output.length ≤ (tm.runFrom c₀ t).output.length :=
+      hmono (Nat.zero_le t)
+    have hsub : host.visitedByTapeHead (captureCfg emb ret pre out₀ c₀) t (Fin.last k) ⊆
+        Finset.Icc ((pre.length + c₀.output.length : ℕ) : ℤ)
+          ((pre.length + (tm.runFrom c₀ t).output.length : ℕ) : ℤ) := by
+      intro z hz
+      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
+      have hut : u ≤ t := by have := Finset.mem_range.mp hu; omega
+      rw [hr u hut]
+      simp only [captureCfg, Fin.val_last, lt_self_iff_false, ↓reduceDIte,
+        List.length_append, Finset.mem_Icc]
+      have hlo := hmono (Nat.zero_le u)
+      have hhi := hmono hut
+      simp only [MultiTapeTM.runFrom_zero] at hlo
+      constructor <;> omega
+    exact (Finset.card_le_card hsub).trans (by
+      rw [Int.card_Icc]
+      omega)
 
 end Turing
 
@@ -885,6 +1631,93 @@ theorem computesFunInTime_splitSolve_spaceUsed (C e : ℕ) :
         M.tm.spaceUsed (M.tm.initCfg x) t ≤ c * (x.length + 1) ^ (e + 1) := by
   sorry
 
+/- Local copies of the W2 correspondence from Build/Wrappers.lean.
+The originals are private; the all-time trajectory is needed for the space row. -/
+/-- Map a source state and its last-emission register to simulation, halt,
+or the stationary live loop. An empty register never matches a bit. -/
+private def catalog_redirectState {S : Type} (haltOn : Bool) (q : Option S)
+    (r : Option Bool) : Option ((S × Option Bool) ⊕ Unit) :=
+  match q with
+  | some s => some (.inl (s, r))
+  | none => if r = some haltOn then none else some (.inr ())
+
+/-- Suppress physical emission, updating the register before the halt test. -/
+private def catalog_redirectAction {k : ℕ} {S : Type} (haltOn : Bool)
+    (a : Action k Bool S) (r : Option Bool) : Action k Bool ((S × Option Bool) ⊕ Unit) :=
+  ⟨a.inputTape, a.workTapes, none, catalog_redirectState haltOn a.state (a.output.or r)⟩
+
+/-- The source tapes and input head are unchanged; its last emitted bit is
+remembered in control and the physical output is empty. -/
+private def catalog_redirectCfg (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
+    (c : Cfg M.k Bool M.State x) : Cfg (redirectTM M haltOn).k Bool
+      (redirectTM M haltOn).State x :=
+  ⟨catalog_redirectState haltOn c.state c.output.getLast?, c.inputPos,
+    c.workTapes, c.workTapePos, []⟩
+
+/-- The stationary live loop is fixed by every subsequent transition. -/
+private lemma catalog_redirect_loop (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
+    (c : Cfg (redirectTM M haltOn).k Bool (redirectTM M haltOn).State x)
+    (hs : c.state = some (.inr ())) (t : ℕ) :
+    (redirectTM M haltOn).tm.runFrom c t = c := by
+  induction t with
+  | zero => rfl
+  | succ t ih =>
+    rw [MultiTapeTM.runFrom_succ_eq_step', ih]
+    apply Cfg.ext <;> simp [MultiTapeTM.step, hs, redirectTM, Action.apply]
+
+/-- Capture and application commute because the last entry of an appended
+singleton is the new bit, while no emission leaves the old register intact. -/
+private lemma catalog_redirect_apply (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
+    (c : Cfg M.k Bool M.State x) (a : Action M.k Bool M.State) :
+    (catalog_redirectAction haltOn a c.output.getLast?).apply (catalog_redirectCfg M haltOn c) =
+      catalog_redirectCfg M haltOn (a.apply c) := by
+  have hlast : (c.output ++ a.output.toList).getLast? = a.output.or c.output.getLast? := by
+    cases a.output <;> simp
+  refine Cfg.ext ?_ rfl rfl rfl rfl
+  dsimp only [catalog_redirectCfg, catalog_redirectAction, Action.apply]
+  rw [hlast]
+
+/-- The correspondence also holds after a source halt: a matching result
+is absorbed as halted, and a mismatching result is absorbed in the live loop.
+This adapts `acceptCfg_step` in the HALT reduction to an optional register. -/
+private lemma catalog_redirect_step (M : FinTM Bool) (haltOn : Bool) {x : List Bool}
+    (c : Cfg M.k Bool M.State x) :
+    (redirectTM M haltOn).tm.step (catalog_redirectCfg M haltOn c) =
+      catalog_redirectCfg M haltOn (M.tm.step c) := by
+  cases hs : c.state with
+  | none =>
+    rw [MultiTapeTM.step_of_halt hs]
+    by_cases hr : c.output.getLast? = some haltOn
+    · exact MultiTapeTM.step_of_halt (by simp [catalog_redirectCfg, catalog_redirectState, hs, hr])
+    · exact catalog_redirect_loop M haltOn (catalog_redirectCfg M haltOn c)
+        (by simp [catalog_redirectCfg, catalog_redirectState, hs, hr]) 1
+  | some q =>
+    have hi : (catalog_redirectCfg M haltOn c).inputSymbol = c.inputSymbol := rfl
+    have hw : (catalog_redirectCfg M haltOn c).workTapeSymbols = c.workTapeSymbols := rfl
+    have hstate : (catalog_redirectCfg M haltOn c).state = some (.inl (q, c.output.getLast?)) := by
+      simp only [catalog_redirectCfg, catalog_redirectState, hs]
+    simp only [MultiTapeTM.step, hstate, hs]
+    rw [hi, hw]
+    have htr : (redirectTM M haltOn).tm.tr (.inl (q, c.output.getLast?))
+        c.inputSymbol c.workTapeSymbols =
+        catalog_redirectAction haltOn (M.tm.tr q c.inputSymbol c.workTapeSymbols) c.output.getLast? := by
+      cases hq : (M.tm.tr q c.inputSymbol c.workTapeSymbols).state <;>
+        cases ho : (M.tm.tr q c.inputSymbol c.workTapeSymbols).output <;>
+          simp [redirectTM, catalog_redirectAction, catalog_redirectState, hq, ho]
+    rw [htr]
+    exact catalog_redirect_apply M haltOn c _
+
+/-- Initialized runs commute with redirection at every time, including
+after a source halt. This is the last-emission invariant for both clauses. -/
+private lemma catalog_redirect_run (M : FinTM Bool) (haltOn : Bool) (x : List Bool) (t : ℕ) :
+    (redirectTM M haltOn).tm.runFrom ((redirectTM M haltOn).tm.initCfg x) t =
+      catalog_redirectCfg M haltOn (M.tm.runFrom (M.tm.initCfg x) t) := by
+  have hi : (redirectTM M haltOn).tm.initCfg x = catalog_redirectCfg M haltOn (M.tm.initCfg x) := rfl
+  rw [hi]
+  exact MultiTapeTM.runFrom_comm_of_step (catalog_redirectCfg M haltOn) (catalog_redirect_step M haltOn)
+    (M.tm.initCfg x) t
+
+
 /-- **W2 space row** (spec, fill pending — design §12 R3, decision 12.3;
 annotates `Turing.FinTM.redirectTM` beside its
 `redirectTM_computes`/`redirectTM_live` contract pair). Redirection costs
@@ -900,7 +1733,13 @@ theorem redirectTM_spaceUsedByTape (M : FinTM Bool) (haltOn : Bool)
     (redirectTM M haltOn).tm.spaceUsedByTape
         ((redirectTM M haltOn).tm.initCfg x) t i
       = M.tm.spaceUsedByTape (M.tm.initCfg x) t i := by
-  sorry
+  unfold MultiTapeTM.spaceUsedByTape MultiTapeTM.visitedByTapeHead
+  congr 1
+  apply Finset.image_congr
+  intro u _
+  dsimp only
+  rw [catalog_redirect_run]
+  rfl
 
 /-- **W3 space row** (spec, fill pending — design §12 R3, decision 12.3;
 annotates `Turing.FinTM.computesFunInTime_cond`). Given space bounds for
-- 
2.51.1
```


## ===== TCSlib/Complexity/TuringMachine/Build/Embed.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: bank embedding (R1)

The general tape-embedding layer of the machine-construction library
(`machine-library-design.md` §12, R1): a verified routine on its own
`m`-tape set runs on any injectively selected subset of a `k`-tape host's
work tapes, cost unchanged, everything else framed. This is the §5
deferral promoted — the design deferred the general form "until a third
site needs it", and the third, fourth, and fifth sites have arrived (the
chapter-1/2 retrofit families, the Hennie–Stearns conversion, the
two-work-tape universal machine). **Scope, stated precisely** (round-1
note R9): `ι` selects whole distinct physical tapes with coordinates
intact — it does not multiplex several virtual tapes onto zones of one
physical tape, shrink the tape count, or alter the source input word; the
Hennie–Stearns and universal-machine consumers get their zone/virtual-input
representation layers separately, with this module supplying only the
fixed-physical-bank routine relocation. It is the generic form of the private
`emitterBank*`/`emitterP2*` relocation families of
`TCSlib.Complexity.TuringMachine.Build.Primitives`, of the 4A chain's
`clBank*`/`clSlot*` families, and of the retained-tape disciplines that
`Build/Loop.lean` and `Build/Wrappers.lean` carry internally.

**Status: statement skeleton (§12 statement phase).** The transformers and
configuration transports below are real definitions; every contract is
sorried, each with a proof sketch naming its fill obligations.

## Design

Per frozen decision 12.4 there are **two named transformers over one
shared private core** (`embedActionCore`), so each spec stays crisp and a
consumer cites whichever fits:

* `Turing.embedSilentTM` — the W1/capture flavor: the embedded routine's
  emissions are recorded on a designated host work tape `cap` outside the
  selected bank, and the host's physical output stays silent.
* `Turing.embedEmitTM` — the E2/forwarding flavor: emissions pass to the
  host's physical output verbatim.

The two **closed** transformers preserve the source state type and map
the source halt to the host halt; their lockstep is unguarded, holding at
every time with the step count preserved exactly. The round-1 audit
(finding R1) refuted the earlier claim that live-return dispatch could be
left to the seam combinator: a source whose final transition emits and
halts loses that emission either way — the closed embedding is halted
after it, and a seam exit at the sole live state dispatches *before* it.
The **returning** flavors below repair this with an explicit halt-to-live
adapter built into the action core: `Turing.embedSilentRetTM` and
`Turing.embedEmitRetTM` run the source on states `S ⊕ Unit`, execute every
source action **through the halting transition** — the final emission
included — and land in the live return anchor `Sum.inr ()`, which a seam
then consumes as its left exit (`Turing.captureAction`'s and
`Turing.emitterRightTM`'s halt-to-live discipline, now exported).
`Turing.captureAction`/`Turing.capture_run` and
`Turing.emitAction`/`Turing.emit_run` are the fixed-shape precursors
(last-tape capture, identity selection); their statements are untouched.

## Main definitions

* `Turing.embedSilentCfg`, `Turing.embedEmitCfg` — a source configuration
  transported along `ι : Fin m ↪ Fin k`, with the unselected host tapes
  carried as frame parameters.
* `Turing.embedSilentTM`, `Turing.embedEmitTM` — the two closed machine
  transformers.
* `Turing.embedSilentRetTM`, `Turing.embedEmitRetTM` — the two returning
  transformers (round-1 repair R1): source halts land in the live return
  anchor `Sum.inr ()`, with the halting transition executed in full.

## Main results

All sorried (statement phase):

* `Turing.embedSilentTM_runFrom`, `Turing.embedEmitTM_runFrom` — lockstep:
  the transported run is the transport of the source run, same step count.
* `Turing.embedSilentTM_frame`, `Turing.embedEmitTM_frame` — tapes outside
  `Set.range ι` byte-identical with heads unmoved, input position tracking
  the source, output per flavor.
* `Turing.embedSilentTM_visitedByTapeHead`,
  `Turing.embedEmitTM_visitedByTapeHead` (and `_frame` companions),
  `Turing.embedSilentTM_spaceUsedByTape_cap` — per-tape space: host tape
  `ι i` visits exactly the source's tape-`i` cells, unselected tapes visit
  nothing new, and the capture tape is bounded by the recorded output.
* `Turing.embedSilentRetTM_run`, `Turing.embedEmitRetTM_run` — the
  through-halt contracts: live lockstep, then the handover at the source's
  first halt, final emission and source residue preserved, with the return
  anchor reached first exactly there.
* `Turing.embedSilentRetTM_visitedByTapeHead`,
  `Turing.embedEmitRetTM_visitedByTapeHead` — the returning flavors visit
  exactly what the closed flavors visit, at every time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; tape-subset simulations are the
  folklore of the §1.3/§1.7 robustness and simulation arguments.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model — TM2-style keyed stacks there, `FinTM`
  tapes with heads here): the bank-embedding shape is `StackRename`'s
  `rename_executes`.
-/

namespace Turing

variable {m k : ℕ} {S : Type*} {x : List Bool}

/-- The partial inverse of the tape selection: the source index that `ι`
sends to host tape `j`, or `none` when `j` is unselected. Injectivity of
`ι` makes the first `List.find?` hit the unique preimage. -/
private def embedSlot (ι : Fin m ↪ Fin k) (j : Fin k) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide (ι i = j)

/-- Searching at a selected tape returns its unique source index. -/
private lemma embedSlot_selected (ι : Fin m ↪ Fin k) (i : Fin m) :
    embedSlot ι (ι i) = some i := by
  unfold embedSlot
  cases hs : (List.finRange m).find? (fun j => decide (ι j = ι i)) with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp)
    simp at hn
  | some j =>
    have hj := List.find?_some hs
    have hji : j = i := ι.injective (of_decide_eq_true hj)
    subst j
    rfl

/-- Searching outside the selected bank returns no source index. -/
private lemma embedSlot_unselected (ι : Fin m ↪ Fin k) (j : Fin k)
    (hj : j ∉ Set.range ι) : embedSlot ι j = none := by
  unfold embedSlot
  rw [List.find?_eq_none]
  intro i _
  simp only [decide_eq_true_eq]
  exact fun hij => hj ⟨i, hij⟩

/-- The shared private core of the two embedding transformers (frozen
decision 12.4): transport one source action along `ι`, keeping the input
move and the successor state, performing the source's tape-`i` action on
host tape `ι i`, and leaving every unselected tape stationary and
unwritten — except that an emission is handled per the mode `sink`:
`sink = some cap` records it on host tape `cap` with a right move (the
capture discipline of `Turing.captureAction`) and keeps the host output
silent, while `sink = none` forwards it as the host's physical emission
(the discipline of `Turing.emitAction`). -/
private def embedActionCore (ι : Fin m ↪ Fin k) (sink : Option (Fin k))
    (a : Action m Bool S) : Action k Bool S where
  inputTape := a.inputTape
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => a.workTapes i
    | none =>
      match sink with
      | some cap =>
        if j = cap then
          match a.output with
          | some b => (some (some b), SignType.pos)
          | none => (none, 0)
        else (none, 0)
      | none => (none, 0)
  output :=
    match sink with
    | some _ => none
    | none => a.output
  state := a.state

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, suppressing flavor: same control state and input position,
source tape `i` sitting on host tape `ι i` (content and head), the
designated capture tape `cap` holding `pre ++ c.output` — the emissions
recorded so far after a pre-existing prefix — with its head one past that
word, every other unselected tape holding the ambient frame `tapes j` with
its head at `heads j`, and the host's physical output the untouched
`out₀`. Generic form of the `emitterBank*`/`clBank*` configuration
correspondences; for a source of `m` tapes in a host of `m + 1` with the
last tape selected as capture, it degenerates to `Turing.captureCfg` up to
the state embedding (round-1 restatement note: the specialization enlarges
the tape count by one — it is not `m = k`). [Bon26] -/
def embedSilentCfg (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) : Cfg k Bool S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none =>
      if j = cap then FinTM.bufferTape (pre ++ c.output) else tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none =>
      if j = cap then ((pre ++ c.output).length : ℤ) else heads j
  output := out₀

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, forwarding flavor: same control state and input position,
source tape `i` on host tape `ι i`, every unselected tape holding the
ambient frame, and the host's physical output equal to the host's prior
output `pre` followed by everything the source has emitted. Generic form
of the `emitterP2*` relocation correspondences; at `ι = id` it is
`Turing.emitCfg` up to the state embedding. [Bon26] -/
def embedEmitCfg (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) : Cfg k Bool S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none => tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none => heads j
  output := pre ++ c.output

/-- **R1, the suppressing embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, recording every emission on the designated host work tape `cap`
(intended outside `Set.range ι`) and emitting nothing physically — the
W1/capture flavor. States are preserved and the source halt is the host
halt; live return dispatch is the seam combinator's job. -/
def embedSilentTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S) : MultiTapeTM k Bool S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι (some cap) (M.tr q inp fun i => w (ι i))

/-- **R1, the forwarding embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, with every emission passed to the host's physical output verbatim —
the E2 flavor. States are preserved and the source halt is the host
halt. -/
def embedEmitTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S) :
    MultiTapeTM k Bool S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι none (M.tr q inp fun i => w (ι i))

/-- Applying the silent core commutes with configuration transport.
**Proof sketch.** Selected tapes perform the source action. Off-bank tapes
are stationary, except that capture appends the emitted bit at the old
word length. Input movement and successor control are copied verbatim. -/
private lemma embedSilent_apply (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (a : Action m Bool S) :
    (embedActionCore ι (some cap) a).apply
        (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            ← List.append_assoc, FinTM.bufferTape_append]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            Nat.cast_add, add_assoc]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · simp [embedActionCore, embedSilentCfg, Action.apply]

/-- The silent host reads the source action and executes all its effects
in one step; halted configurations remain fixed on both sides. -/
private lemma embedSilent_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) :
    (embedSilentTM ι cap M).step (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedSilentCfg, hs]
  | some q =>
    rw [show (embedSilentCfg ι cap tapes heads pre out₀ c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedSilentCfg ι cap tapes heads pre out₀ c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedSilentCfg, embedSlot_selected]
    change (embedActionCore ι (some cap) (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedSilent_apply ι cap tapes heads pre out₀ c _

/-- **R1 lockstep, suppressing flavor** (spec, fill pending — design §12;
[Bon26], `rename_executes`). The transported run *is* the transport of the
source run, at every time and with the step count preserved exactly: `t`
host steps simulate `t` source steps. No liveness guard is needed — the
transformer preserves states, so a halted source transports to a halted
host and both runs stall together.

**Proof sketch.** One-step commutation plus
`Turing.MultiTapeTM.runFrom_comm_of_step`. For the step: a halted source
makes both sides the identity. For a live source state, the host reads the
source symbols through `ι` (the transport puts source tape `i` at `ι i`),
so the host applies `embedActionCore` of the very action the source
applies; componentwise, selected tapes update as the source's
(`Turing.Action.apply` through the `embedSlot` inverse, whose two
equations `embedSlot ι (ι i) = some i` and `embedSlot ι j = none` off the
range are the `List.find?` glue obligations), unselected tapes receive the
stationary no-write action, the capture tape appends the optional emission
at head `|pre ++ c.output|` (`Turing.FinTM.bufferTape_append`, exactly as
in `capture_apply`), silence keeps the output at `out₀`, and the states
agree. -/
theorem embedSilentTM_runFrom (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t =
      embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step
    (embedSilentCfg ι cap tapes heads pre out₀)
    (embedSilent_step ι cap M tapes heads pre out₀) c t

/-- **R1 frame, suppressing flavor** (spec, fill pending — design §12).
Along the whole transported run, every host tape outside the selected bank
and distinct from the capture tape is byte-identical to its ambient frame
with its head unmoved; the input position tracks the source's; and the
host's physical output stays `out₀` (output silence).

**Proof sketch.** Project the lockstep equation
`embedSilentTM_runFrom` componentwise: the transport's `workTapes`/
`workTapePos` at an unselected `j ≠ cap` are the frame parameters by the
`embedSlot` off-range equation, its `inputPos` is the source's, and its
`output` is `out₀` by definition. -/
theorem embedSilentTM_frame (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι → j ≠ cap →
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapes j
        = tapes j ∧
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapePos j
        = heads j) ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).output = out₀ := by
  rw [embedSilentTM_runFrom ι cap hcap]
  refine ⟨?_, rfl, rfl⟩
  intro j hj hjc
  simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]

/-- **R1 space, suppressing flavor, selected tapes** (spec, fill pending —
design §12: "cells visited on host tape `ι i` equal cells visited on
source tape `i`"). The visited set of host tape `ι i` up to time `t` is
exactly the source's visited set of tape `i`, so the per-tape space
agrees on the nose.

**Proof sketch.** Both visited sets are images of `Finset.range (t + 1)`
under the respective head trajectories
(`Turing.MultiTapeTM.visitedByTapeHead`), and the lockstep equation
`embedSilentTM_runFrom` makes the trajectories pointwise equal at `ι i`
via the transport's `workTapePos` clause and `embedSlot ι (ι i) = some i`.
The cardinality clause is `congrArg Finset.card`. -/
theorem embedSilentTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) (i : Fin m) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, suppressing flavor, unselected tapes** (spec, fill
pending — design §12: "unselected tapes visit nothing new"). A host tape
outside the selected bank and distinct from the capture tape visits
exactly the singleton of its initial head position, so its space usage is
one cell.

**Proof sketch.** By `embedSilentTM_frame` the head of such a tape never
moves, so the trajectory image collapses to `{heads j}`; the cardinality
clause is `Finset.card_singleton`. -/
theorem embedSilentTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (cap : Fin k) (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) (hjc : j ≠ cap) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = 1 := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1 space, suppressing flavor, the capture tape** (spec, fill
pending — design §12; every unselected tape is accounted for, the capture
tape included). The capture tape's space usage up to time `t` is bounded
by the number of emissions recorded in that window plus one: the head
starts one past `pre ++ c.output` and advances right exactly once per
recorded emission.

**Proof sketch.** By lockstep the capture head position at time `t'` is
`|pre| + |(M.runFrom c t').output|`, which is nondecreasing in `t'` with
increments bounded by one emission per step; the visited set is therefore
the integer interval from the initial head to the final one, of
cardinality the output growth plus one
(`Turing.MultiTapeTM.output_prefix` gives the monotone growth).

**Fill appendix.** For the stated upper bound, the formal proof only
needs containment in this interval, followed by its cardinality. -/
theorem embedSilentTM_spaceUsedByTape_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t cap
      ≤ (M.runFrom c t).output.length - c.output.length + 1 := by
  have hgrowth : c.output.length ≤ (M.runFrom c t).output.length := by
    simpa using (M.output_prefix c (Nat.zero_le t)).length_le
  have hsub : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t cap ⊆
      Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    have hut : u ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
    have hlo : c.output.length ≤ (M.runFrom c u).output.length := by
      simpa using (M.output_prefix c (Nat.zero_le u)).length_le
    have hhi := (M.output_prefix c hut).length_le
    rw [embedSilentTM_runFrom ι cap hcap]
    simp only [embedSilentCfg, embedSlot_unselected ι cap hcap, ↓reduceIte,
      Finset.mem_Icc, List.length_append, Nat.cast_add]
    constructor <;> omega
  calc
    _ ≤ (Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ)).card :=
      Finset.card_le_card hsub
    _ = (M.runFrom c t).output.length - c.output.length + 1 := by
      rw [Int.card_Icc]
      simp only [List.length_append, Nat.cast_add]
      omega

/-- Applying the forwarding core commutes with configuration transport:
selected tapes update identically, the frame stays fixed, and appending
the optional emission associates with the existing output prefix. -/
private lemma embedEmit_apply (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (a : Action m Bool S) :
    (embedActionCore ι none a).apply (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · simp [embedActionCore, embedEmitCfg, Action.apply, List.append_assoc]

/-- The forwarding host reads the same source action and executes it
completely in one step, including an emission on a halting transition. -/
private lemma embedEmit_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) :
    (embedEmitTM ι M).step (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedEmitCfg, hs]
  | some q =>
    rw [show (embedEmitCfg ι tapes heads pre c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedEmitCfg ι tapes heads pre c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedEmitCfg, embedSlot_selected]
    change (embedActionCore ι none (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedEmit_apply ι tapes heads pre c _

/-- **R1 lockstep, forwarding flavor** (spec, fill pending — design §12;
[Bon26], `rename_executes`). The transported run is the transport of the
source run, at every time and with the step count preserved exactly;
emissions are forwarded, so the host's output is `pre` followed by the
source's output at every instant (through the transport).

**Proof sketch.** As `embedSilentTM_runFrom`, with the capture clause
replaced by the output clause: the one-step commutation appends the
optional emission after `pre` (associativity of `++`, exactly as in
`emit_apply`), and `Turing.MultiTapeTM.runFrom_comm_of_step` iterates. -/
theorem embedEmitTM_runFrom (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (embedEmitTM ι M).runFrom (embedEmitCfg ι tapes heads pre c) t =
      embedEmitCfg ι tapes heads pre (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step (embedEmitCfg ι tapes heads pre)
    (embedEmit_step ι M tapes heads pre) c t

/-- **R1 frame, forwarding flavor** (spec, fill pending — design §12).
Along the whole transported run, every host tape outside the selected
bank is byte-identical to its ambient frame with its head unmoved, the
input position tracks the source's, and the host's physical output is
`pre` followed by the source's output so far.

**Proof sketch.** Project `embedEmitTM_runFrom` componentwise, as in the
suppressing flavor; the output clause is the transport's definition. -/
theorem embedEmitTM_frame (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι →
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapes j = tapes j ∧
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapePos j = heads j) ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).output
      = pre ++ (M.runFrom c t).output := by
  rw [embedEmitTM_runFrom]
  refine ⟨?_, rfl, rfl⟩
  intro j hj
  simp [embedEmitCfg, embedSlot_unselected ι j hj]

/-- **R1 space, forwarding flavor, selected tapes** (spec, fill pending —
design §12). The visited set of host tape `ι i` up to time `t` is exactly
the source's visited set of tape `i`; per-tape space agrees on the nose.

**Proof sketch.** As `embedSilentTM_visitedByTapeHead`: pointwise equal
head trajectories from `embedEmitTM_runFrom`, then image and
cardinality. -/
theorem embedEmitTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) (i : Fin m) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedEmitTM_runFrom]
    simp [embedEmitCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, forwarding flavor, unselected tapes** (spec, fill
pending — design §12). A host tape outside the selected bank visits
exactly the singleton of its initial head position; its space usage is
one cell.

**Proof sketch.** By `embedEmitTM_frame` the head never moves; collapse
the trajectory image to `{heads j}` and take cardinalities. -/
theorem embedEmitTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j = {heads j} ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t j = 1 := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedEmitTM_runFrom]
    simp only [embedEmitCfg, embedSlot_unselected ι j hj]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1′, the returning suppressing embedding** (round-1 repair R1). As
`Turing.embedSilentTM`, on states `S ⊕ Unit`: live source states run the
capture-flavored core, but a source action whose successor is `none` lands
in the **live return anchor** `Sum.inr ()` — the halting transition is
executed in full, its emission recorded on `cap`, before control arrives at
the anchor (the `Turing.captureAction`/`Turing.emitterRightTM` halt-to-live
discipline, exported). The anchor itself idles (stationary, silent, live),
which is exactly what a seam combinator overrides as its left exit. -/
def embedSilentRetTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S) : MultiTapeTM k Bool (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι (some cap) a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- **R1′, the returning forwarding embedding** (round-1 repair R1). As
`Turing.embedEmitTM`, on states `S ⊕ Unit`, with source halts landing in
the live return anchor `Sum.inr ()` after the halting transition — its
forwarded emission included — has executed in full. -/
def embedEmitRetTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S) :
    MultiTapeTM k Bool (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι none a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- Replace an action's optional successor by the live return encoding,
without changing any input, work-tape, or output effect. -/
private def embedReturnAction (a : Action k Bool S) : Action k Bool (S ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, a.output, some (a.state.elim (Sum.inr ()) Sum.inl)⟩

/-- Encode a closed host configuration with live left states and a live
right return anchor, preserving all four non-control fields. -/
private def embedReturnCfg (c : Cfg k Bool S x) : Cfg k Bool (S ⊕ Unit) x :=
  { c with state := some (c.state.elim (Sum.inr ()) Sum.inl) }

/-- At a live configuration, the return encoding is ordinary left state
mapping; at a halt it instead uses the live right anchor. -/
private lemma embedReturnCfg_live (c : Cfg k Bool S x) (hc : c.state ≠ none) :
    embedReturnCfg c = c.mapState Sum.inl := by
  cases hs : c.state with
  | none => exact (hc hs).elim
  | some q => simp [embedReturnCfg, Cfg.mapState, hs]

/-- Direct comparison of a closed host step with a returning host step.
**Proof sketch.** At a live left state, both hosts execute the same action
and only the successor encoding differs. At a closed halt, the returning
anchor's idle action preserves every non-control field, just as absorption
does on the closed side. No property of a source embedding is needed. -/
private lemma embedReturn_step (N : MultiTapeTM k Bool S)
    (R : MultiTapeTM k Bool (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Bool S x) :
    R.step (embedReturnCfg c) = embedReturnCfg (N.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedReturnCfg, hs, hidle, Action.apply]
  | some q =>
    rw [show (embedReturnCfg c).state = some (Sum.inl q) by
      simp [embedReturnCfg, hs]]
    dsimp only
    have hin : (embedReturnCfg c).inputSymbol = c.inputSymbol := rfl
    have hw : (embedReturnCfg c).workTapeSymbols = c.workTapeSymbols := rfl
    rw [hin, hw, hleft]
    rfl

/-- The silent returning step executes the entire transported source
action, then encodes its successor as a live left state or return anchor. -/
private lemma embedSilentRet_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (hc : c.state ≠ none) :
    (embedSilentRetTM ι cap M).step
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) =
      embedReturnCfg (embedSilentCfg ι cap tapes heads pre out₀ (M.step c)) := by
  have h := embedReturn_step (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c)
  rw [embedReturnCfg_live (embedSilentCfg ι cap tapes heads pre out₀ c) hc,
    embedSilent_step] at h
  exact h

/-- A live-step transport reaches the return anchor exactly at a positive
first halt, with all transported data intact.
**Proof sketch.** The initially live state and terminal halt imply positive
time. Induct over the strict live prefix, where the successor encoding is
ordinary left mapping. Execute the step from the last live configuration
separately; its halted successor encodes the return anchor. Earlier states
are left constructors, so none is the right anchor. -/
private lemma embedThroughHalt (M : MultiTapeTM m Bool S)
    (R : MultiTapeTM k Bool (S ⊕ Unit))
    (E : Cfg m Bool S x → Cfg k Bool S x)
    (hstate : ∀ d, (E d).state = d.state)
    (hstep : ∀ d, d.state ≠ none →
      R.step ((E d).mapState Sum.inl) = embedReturnCfg (E (M.step d)))
    (c : Cfg m Bool S x) (T : ℕ) (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl) ∧
    R.runFrom ((E c).mapState Sum.inl) T =
      { E (M.runFrom c T) with state := some (Sum.inr ()) } ∧
    ∀ t < T, (R.runFrom ((E c).mapState Sum.inl) t).state ≠
      some (Sum.inr ()) := by
  have hT : 0 < T := by
    by_contra hn
    have hz : T = 0 := by omega
    subst T
    exact hc (by simpa using hhalt)
  have hrun : ∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        hstep _ (hlive t (by omega)), ← MultiTapeTM.runFrom_succ_eq_step']
      apply embedReturnCfg_live
      rw [hstate]
      exact hlive _ ht
  refine ⟨hrun, ?_, ?_⟩
  · have hlast : T - 1 + 1 = T := by omega
    calc
      R.runFrom ((E c).mapState Sum.inl) T =
          R.step (R.runFrom ((E c).mapState Sum.inl) (T - 1)) :=
        (congrArg (R.runFrom ((E c).mapState Sum.inl)) hlast).symm.trans
          MultiTapeTM.runFrom_succ_eq_step'
      _ = embedReturnCfg (E (M.runFrom c T)) := by
        rw [hrun _ (by omega), hstep _ (hlive _ (by omega)),
          ← MultiTapeTM.runFrom_succ_eq_step', hlast]
      _ = _ := by simp [embedReturnCfg, hstate, hhalt]
  · intro t ht
    rw [hrun t ht]
    simp only [Cfg.mapState, hstate]
    cases (M.runFrom c t).state <;> simp

/-- **R1′ through-halt contract, suppressing flavor** (spec, fill pending —
round-1 repair R1): if the source first halts at time `T`, the returning
embedding runs in `Sum.inl`-lockstep through every live time and, at `T`,
sits at the **live return anchor** over the completed transport — the
halting transition's emission recorded on `cap`, the source tape residue
preserved on the selected bank, the frame untouched — having visited the
anchor first exactly there. The start must be **live** (`hc` — round-2
blocker: an initially halted `c` at `T = 0` satisfies the other hypotheses
vacuously while the handover state projection would demand
`none = some (Sum.inr ())`; under `hlive` **and** `hhalt` together, `hc` is
equivalent to `0 < T` — the forward direction uses `hhalt`, the reverse
`hlive 0` (round-3 finding 1 sharpened the earlier `hhalt`-only phrasing).
The smallest case is the round-1 counterexample cured: a one-state source
that emits and halts on its first transition lands at time `1` in
`Sum.inr ()` with `pre ++ [b]` on the capture tape (the audit's S8 check).

**Proof sketch.** Live times: the `Sum.inl` branch applies the very core of
`Turing.embedSilentTM`, so `embedSilentTM_runFrom`'s one-step commutation
transports verbatim under `Cfg.mapState Sum.inl` (`Cfg.mapState_apply`).
At the halting step, the source action's tape and capture effects are those
of the closed flavor — `Turing.FinTM.bufferTape_append` records the final
emission — while the successor `Option.elim` lands in `Sum.inr ()` instead
of `none`; the anchor cannot occur earlier because live source states map
into `Sum.inl`. Fill obligations, named: the two `Option.elim` successor
equations; the through-halt step case; the first-visit projection. -/
theorem embedSilentRetTM_run (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t =
        (embedSilentCfg ι cap tapes heads pre out₀
          (M.runFrom c t)).mapState Sum.inl) ∧
    (embedSilentRetTM ι cap M).runFrom
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) T =
      { embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl)
          t).state ≠ some (Sum.inr ()) := by
  exact embedThroughHalt M (embedSilentRetTM ι cap M)
    (embedSilentCfg ι cap tapes heads pre out₀) (fun _ => rfl)
    (embedSilentRet_step ι cap M tapes heads pre out₀) c T hc hlive hhalt

/-- The forwarding returning step preserves the complete source action,
including its final emission, and changes only the successor encoding. -/
private lemma embedEmitRet_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (hc : c.state ≠ none) :
    (embedEmitRetTM ι M).step ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) =
      embedReturnCfg (embedEmitCfg ι tapes heads pre (M.step c)) := by
  have h := embedReturn_step (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c)
  rw [embedReturnCfg_live (embedEmitCfg ι tapes heads pre c) hc, embedEmit_step] at h
  exact h

/-- **R1′ through-halt contract, forwarding flavor** (spec, fill pending —
round-1 repair R1): as `Turing.embedSilentRetTM_run` with the final
emission forwarded to the physical output (`pre ++ (M.runFrom c T).output`
at the anchor).

**Proof sketch.** As `embedSilentRetTM_run`, with the forwarding core: live
times transport under `Cfg.mapState Sum.inl` by `embedEmitTM_runFrom`'s
one-step commutation, the halting step applies the closed forwarding core's
tape and output effects (the final emission appended to the physical
output) with the successor `Option.elim` landing in `Sum.inr ()`, and the
first-visit clause projects from the `Sum.inl` lockstep. Fill obligations,
named: the successor equations; the through-halt step case; the
first-visit projection. -/
theorem embedEmitRetTM_run (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t =
        (embedEmitCfg ι tapes heads pre (M.runFrom c t)).mapState Sum.inl) ∧
    (embedEmitRetTM ι M).runFrom
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) T =
      { embedEmitCfg ι tapes heads pre (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t).state ≠
        some (Sum.inr ()) := by
  exact embedThroughHalt M (embedEmitRetTM ι M)
    (embedEmitCfg ι tapes heads pre) (fun _ => rfl)
    (embedEmitRet_step ι M tapes heads pre) c T hc hlive hhalt

/-- Direct host comparison preserves every visited-head set, from any
initial configuration and for every finite horizon.
**Proof sketch.** Initially halted configurations stay halted on both
sides. From a live start, iterate the direct step comparison under the
return encoding, whose head positions are unchanged. Equality of the
head trajectories gives equality of their finite images. This uses no
termination hypothesis, source simulation, or capture-tape separation. -/
private lemma embedReturn_visited (N : MultiTapeTM k Bool S)
    (R : MultiTapeTM k Bool (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Bool S x) (t : ℕ) (j : Fin k) :
    R.visitedByTapeHead (c.mapState Sum.inl) t j = N.visitedByTapeHead c t j := by
  unfold MultiTapeTM.visitedByTapeHead
  congr 1
  funext u
  by_cases hc : c.state = none
  · rw [R.runFrom_of_halt _ (by simp [Cfg.mapState, hc]), N.runFrom_of_halt _ hc]
    rfl
  · have hrun := MultiTapeTM.runFrom_comm_of_step embedReturnCfg
      (embedReturn_step N R hleft hidle) c u
    rw [embedReturnCfg_live c hc] at hrun
    exact congrArg (fun d => d.workTapePos j) hrun

/-- **R1′ space, suppressing flavor** (spec, fill pending — round-1 repair
R1): at every time and on every tape, the returning embedding's visited set
from the `Sum.inl`-mapped seam equals the closed embedding's from the plain
seam — the trajectories coincide through the halt, and afterwards one idles
at the live anchor while the other sits halted, both stationary.

**Proof sketch.** For `t` up to the first source halt, both machines apply
identical tape actions (`embedSilentRetTM_run`'s lockstep and the halting
step's shared core); beyond it, the anchor's idle action and the halted
absorption are both stationary, freezing both visited sets.

**Fill appendix.** The direct host comparison `embedReturn_visited`
handles initially halted and live starts separately. It uses neither
through-halt contract nor a capture-separation hypothesis. -/
theorem embedSilentRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) (j : Fin k) :
    (embedSilentRetTM ι cap M).visitedByTapeHead
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t j =
      (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j := by
  exact embedReturn_visited (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c) t j

/-- **R1′ space, forwarding flavor** (spec, fill pending — round-1 repair
R1): the forwarding analogue of
`Turing.embedSilentRetTM_visitedByTapeHead`.

**Proof sketch.** As the suppressing flavor: identical tape actions through
the first source halt, then the live idle and the halted absorption are
both stationary, freezing both visited sets — the trajectories coincide at
every time. -/
theorem embedEmitRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) (j : Fin k) :
    (embedEmitRetTM ι M).visitedByTapeHead
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t j =
      (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j := by
  exact embedReturn_visited (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c) t j

end Turing
```


## ===== TCSlib/Complexity/TuringMachine/Build/Seam.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Convention
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: seam composition (R2)

The configuration-level sequencing layer of the machine-construction
library (`machine-library-design.md` §12, R2): sequential composition of
two controllers at the canonical `Turing.Cfg.ofWords` seam of
`TCSlib.Complexity.TuringMachine.Build.Convention`. If `M₁` carries seam
`c₀` to seam `c₁` within `T₁` under a first-return cut, and `M₂` carries
`c₁` to `c₂` within `T₂`, the dispatch-glued composite carries `c₀` to
`c₂` within `T₁ + 1 + T₂` — the explicit constant is `1`, one silent
stationary dispatch step at the seam. This is the generic form of the
per-batch dispatch gluing re-proved in every A-chain and emitter batch,
and it exists at the configuration level precisely because the emitter
round-1 finding stands: *function-level* contracts cannot deliver
clean-return seams, so composing `ComputesFunInTime` contracts can never
replace this combinator.

**Status: statement skeleton (§12 statement phase).** The composite is a
real definition (state-sum dispatch in `Turing.bufferedCompTM`'s style,
kept minimal); every contract is sorried, each with a proof sketch naming
its fill obligations.

## Design

* The glue is a **state sum** `S₁ ⊕ S₂`: left states run `M₁`'s table,
  right states run `M₂`'s, and the designated left anchor `exit` takes one
  stationary, silent, write-free transition to the right anchor `entry`.
  Dispatch-on-anchor (rather than dispatch-on-halt) matches the ABI: seam
  contracts end at a **live** anchor (`Build/Loop.lean`'s `hstart`/
  `hround` shape), and the catalog routines of
  `TCSlib.Complexity.TuringMachine.Build.Catalog` exit at live anchors.
* The space clause is stated in the **sharp per-tape form** (frozen
  decision 12.1): the headline is per-tape containment of visited sets —
  the composite's visited set on every work tape is contained in the
  union of the phases' — which implies both the per-tape sum bound and
  the max bound for disjointly-owned tapes, stated as corollaries.

## Main definitions

* `Turing.seamCompTM` — the dispatch-glued composite of two machines at
  `Turing.Cfg.ofWords` seams.

## Main results

All sorried (statement phase):

* `Turing.seamCompTM_run` — seam-to-seam composition within
  `T₁ + 1 + T₂`.
* `Turing.seamCompTM_firstReturn` — the composite inherits a first-return
  cut at the final anchor, so composites **whose phases satisfy the stated
  cuts** chain (round-1 finding R3: the cut excludes positive
  entry-equals-exit calls — those route through the release adapter below).
* `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_firstReturn_ofCfg`,
  `Turing.seamCompTM_visitedByTapeHead_ofCfg` — the **general-configuration**
  composition (round-1 repair R2): phase two starts from phase one's
  returned configuration with only the control state replaced, so arbitrary
  frames, displaced inactive heads, and accumulated output cross the
  dispatch intact; the canonical `Cfg.ofWords` theorems are its instances.
* `Turing.seamReleaseTM`, `Turing.seamReleaseTM_firstReturn`,
  `Turing.seamReleaseTM_visitedByTapeHead` — the **fresh-entry/release
  adapter** (round-1 repair R3): the entry action executes unconditionally
  from a fresh start state, so a positive call that returns to its own
  anchor becomes seam-consumable.
* `Turing.seamCompTM_visitedByTapeHead` — per-tape visited-set
  containment (the headline space clause, decision 12.1).
* `Turing.seamCompTM_spaceUsedByTape_le_add`,
  `Turing.seamCompTM_spaceUsed_le_add`,
  `Turing.seamCompTM_spaceUsedByTape_le_max` — the sum and
  max-for-disjointly-owned-tapes corollaries.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; phase-sequenced simulations
  are the folklore engine of §1.4–§1.7.)
* [Balbach22] F. Balbach, *The Cook–Levin theorem*, Isabelle AFP entry
  `Cook_Levin`, 2022. (The composition-combinator architecture precedent,
  as in `TCSlib.Complexity.TuringMachine.Composition`.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model): the seam-composition shape is
  `StackRename`'s `executes_in_sum`.
-/

namespace Turing

variable {k : ℕ} {S₁ S₂ : Type*} {x : List Bool}

/-- **R2, the seam composite** (design §12; [Bon26], `executes_in_sum`).
The dispatch-glued sequential composite of `M₁` and `M₂` at
`Turing.Cfg.ofWords` seams: states are the sum `S₁ ⊕ S₂`, left states run
`M₁`'s transition table and right states `M₂`'s (each halting where its
phase halts), except that the designated left anchor `exit` takes one
stationary, silent, write-free dispatch step to the right anchor `entry`.
The composite starts at `M₁`'s initial state; a run launched at a left
seam anchor is the intended use. -/
def seamCompTM [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂) :
    MultiTapeTM k Bool (S₁ ⊕ S₂) where
  q₀ := Sum.inl M₁.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      if s = exit then ⟨0, fun _ => (none, 0), none, some (Sum.inr entry)⟩
      else
        let a := M₁.tr s inp w
        ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inl⟩
    | Sum.inr s =>
      let a := M₂.tr s inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩

/-- Away from the exit, one left step is exactly the state-mapped source step,
including the absorbing halted case. -/
private lemma seamComp_step_left [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (c : Cfg k Bool S₁ x) (hc : c.state ≠ some exit) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inl) =
      (M₁.step c).mapState Sum.inl := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    have hq : q ≠ exit := fun h => hc (hs.trans (congrArg some h))
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    dsimp only [seamCompTM]
    rw [if_neg hq]
    rfl

/-- Right steps commute with state mapping, even after a source halt. -/
private lemma seamComp_step_right [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂) (c : Cfg k Bool S₂ x) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inr) =
      (M₂.step c).mapState Sum.inr := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rfl

/-- A stationary, silent, write-free action changes only the control field. -/
private lemma seam_stationary_apply (c : Cfg k Bool S₁ x) (q : S₁) :
    (Action.mk 0 (fun _ => (none, 0)) none (some q)).apply c =
      { c with state := some q } := by
  simp [Action.apply]

/-- Dispatch preserves all data of an arbitrary live exit configuration. -/
private lemma seamComp_dispatch [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (c : Cfg k Bool S₁ x) (hc : c.state = some exit) :
    (seamCompTM M₁ exit M₂ entry).step (c.mapState Sum.inl) =
      (c.mapState fun _ => entry).mapState Sum.inr := by
  unfold MultiTapeTM.step
  simp only [Cfg.mapState, hc, Option.map_some]
  dsimp only [seamCompTM]
  rw [if_pos rfl, seam_stationary_apply]

/-- The whole left trajectory agrees through the exit time.
**Proof sketch.** Induct on the time; the cut licenses the left-step
identity at every predecessor strictly before the endpoint. -/
private lemma seamComp_left [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c : Cfg k Bool S₁ x} {T : ℕ}
    (hcut : ∀ t < T, (M₁.runFrom c t).state ≠ some exit)
    (t : ℕ) (ht : t ≤ T) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c.mapState Sum.inl) t =
      (M₁.runFrom c t).mapState Sum.inl := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
      seamComp_step_left M₁ exit M₂ entry _ (hcut t (by omega)),
      MultiTapeTM.runFrom_succ_eq_step']

/-- After the one-step dispatch, the entire right trajectory agrees.
**Proof sketch.** Split the run at the dispatch, use left lockstep and
the exit equation, then iterate the unconditional right-step identity. -/
private lemma seamComp_right [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {T₁ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (t : ℕ) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + t) =
      (M₂.runFrom (c₁.mapState fun _ => entry) t).mapState Sum.inr := by
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_succ_eq_step',
    seamComp_left M₁ exit M₂ entry hcut T₁ le_rfl, h₁,
    seamComp_dispatch M₁ exit M₂ entry c₁ hexit]
  exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
    (seamComp_step_right M₁ exit M₂ entry) _ t

/-- General endpoint composition, shared by the frozen public forms. -/
private lemma seamComp_run_general [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {c₃ : Cfg k Bool S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) = c₃.mapState Sum.inr :=
  (seamComp_right M₁ exit M₂ entry h₁ hexit hcut T₂).trans
    (congrArg (Cfg.mapState Sum.inr) h₂)

/-- The right final anchor is absent before the total time.
**Proof sketch.** Through the left endpoint, constructor disjointness
excludes the anchor. Afterwards, right lockstep transports the phase-two
cut at the time remaining after dispatch. -/
private lemma seamComp_firstReturn_general [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry q₂ : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (c₁.mapState fun _ => entry) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
        some (Sum.inr q₂) := by
  intro t ht
  by_cases hleft : t ≤ T₁
  · rw [seamComp_left M₁ exit M₂ entry hcut t hleft]
    cases (M₁.runFrom c₀ t).state <;> simp [Cfg.mapState]
  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
    rw [htime, seamComp_right M₁ exit M₂ entry h₁ hexit hcut]
    intro heq
    apply hcut₂ (t - (T₁ + 1)) (by omega)
    change Option.map Sum.inr
      (M₂.runFrom (c₁.mapState fun _ => entry) (t - (T₁ + 1))).state =
        some (Sum.inr q₂) at heq
    obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp heq
    exact hq.trans (congrArg some (Sum.inr.inj heq))

/-- Every visited position belongs to one of the two exact run segments.
**Proof sketch.** A time at most the left duration uses left lockstep.
Every later time is dispatch time plus a unique nonnegative offset, at
most the right duration; right lockstep supplies its image witness. -/
private lemma seamComp_visited_general [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead c₀ T₁ i ∪
        M₂.visitedByTapeHead (c₁.mapState fun _ => entry) T₂ i := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
  have ht' := Finset.mem_range.mp ht
  by_cases hleft : t ≤ T₁
  · rw [seamComp_left M₁ exit M₂ entry hcut t hleft]
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr (by omega), rfl⟩
  · have htime : t = T₁ + 1 + (t - (T₁ + 1)) := by omega
    rw [htime, seamComp_right M₁ exit M₂ entry h₁ hexit hcut]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨t - (T₁ + 1), Finset.mem_range.mpr (by omega), rfl⟩

/-- State mapping of a canonical seam changes only its anchor. -/
private lemma seam_ofWords_mapState {S₃ : Type*} (f : S₁ → S₃)
    (q : S₁) (w : Fin k → List Bool) :
    (Cfg.ofWords (input := x) q w).mapState f = Cfg.ofWords (f q) w := rfl

/-- **R2, seam-to-seam composition** (spec, fill pending — design §12;
[Bon26], `executes_in_sum`). If `M₁` carries the seam
`Cfg.ofWords start w₀` to the seam `Cfg.ofWords exit w₁` in exactly `T₁`
steps without visiting the anchor `exit` earlier (the first-return cut),
and `M₂` carries `Cfg.ofWords entry w₁` to `Cfg.ofWords q₂ w₂` in exactly
`T₂` steps, then the composite carries the left-mapped first seam to the
right-mapped last seam in exactly `T₁ + 1 + T₂` steps — the explicit
dispatch constant is `1`, not `O(1)`.

**Proof sketch.** Three segments composed with
`Turing.MultiTapeTM.runFrom_add`. (i) *Phase one lockstep*: on left
states other than the anchor, one composite step is the `Sum.inl`-mapped
`M₁` step; the cut guarantees the anchor is not visited before `T₁`, so
induction carries the left-mapped configuration to time `T₁`, where it is
`Cfg.ofWords (Sum.inl exit) w₁`. (ii) *Dispatch*: at the anchor the
composite takes the stationary silent step, and a stationary write-free
action fixes every tape, head, and the output of a seam configuration, so
time `T₁ + 1` is exactly `Cfg.ofWords (Sum.inr entry) w₁`. (iii) *Phase
two lockstep*: on right states one composite step is the
`Sum.inr`-mapped `M₂` step (`Turing.MultiTapeTM.runFrom_comm_of_step`),
carrying the seam to the right-mapped `Cfg.ofWords q₂ w₂` at time
`T₁ + 1 + T₂`. The degenerate case `T₁ = 0` (so `start = exit`,
`w₀ = w₁`) is covered because the dispatch step alone performs the
phase-one handover. -/
theorem seamCompTM_run [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) :
    (seamCompTM M₁ exit M₂ entry).runFrom
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) =
      Cfg.ofWords (Sum.inr q₂) w₂ := by
  have h₂' : M₂.runFrom
      ((Cfg.ofWords (input := x) exit w₁).mapState fun _ => entry) T₂ =
        Cfg.ofWords q₂ w₂ := by
    simpa only [seam_ofWords_mapState] using h₂
  simpa only [seam_ofWords_mapState] using
    seamComp_run_general M₁ exit M₂ entry h₁ rfl hcut h₂'

/-- **R2, the inherited first-return cut** (spec, fill pending — design
§12). Under the hypotheses of `seamCompTM_run`, if additionally `M₂` does
not visit its final anchor `q₂` strictly before `T₂`, then the composite
does not visit `Sum.inr q₂` strictly before `T₁ + 1 + T₂` — so a
composite is itself a seam-to-seam routine and chains under further
`seamCompTM` applications.

**Proof sketch.** Split the window. Before and at `T₁` the composite's
state is a left state (phase-one lockstep of `seamCompTM_run`), never
`Sum.inr q₂` by constructor disjointness. From `T₁ + 1` on, the
composite's state is the `Sum.inr` image of `M₂`'s state at the shifted
time (phase-two lockstep), and `Sum.inr` injectivity turns the `M₂` cut
into the composite cut; a mid-phase `M₂` halt is excluded because halting
absorbs and would contradict `h₂`'s live anchor at `T₂`. -/
theorem seamCompTM_firstReturn [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (Cfg.ofWords (input := x) entry w₁) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom
          (Cfg.ofWords (input := x) (Sum.inl start) w₀) t).state ≠
        some (Sum.inr q₂) := by
  have hcut₂' : ∀ t < T₂,
      (M₂.runFrom ((Cfg.ofWords (input := x) exit w₁).mapState fun _ => entry)
        t).state ≠ some q₂ := by
    simpa only [seam_ofWords_mapState] using hcut₂
  simpa only [seam_ofWords_mapState] using
    seamComp_firstReturn_general M₁ exit M₂ entry q₂ h₁ rfl hcut hcut₂'

/-- **R2 space, the per-tape headline** (spec, fill pending — design §12,
frozen decision 12.1: the sharp per-tape form). On every work tape `i`,
the composite's visited set over the whole composed run is contained in
the union of the two phases' visited sets. This is the statement the sum
and max corollaries below both project from; it is deliberately the
containment itself, since downstream applications may depend on the
sharpness.

**Proof sketch.** Decompose the trajectory by the two lockstep segments
of `seamCompTM_run`: times `0, …, T₁` reproduce `M₁`'s head positions
(phase-one lockstep), time `T₁ + 1` is the dispatch step, which is
stationary — the head sits at the seam origin, already visited by both
phases' initial configurations — and times `T₁ + 1, …, T₁ + 1 + T₂`
reproduce `M₂`'s positions shifted by `T₁ + 1` (phase-two lockstep).
Every trajectory point therefore lies in one of the two phases' images;
conclude by `Finset.image` monotonicity over the split of
`Finset.range`. -/
theorem seamCompTM_visitedByTapeHead [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i ∪
        M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i := by
  simpa only [seam_ofWords_mapState] using
    seamComp_visited_general (T₂ := T₂) M₁ exit M₂ entry h₁ rfl hcut i

/-- **R2 space, the per-tape sum corollary** (spec, fill pending — design
§12, decision 12.1). On every work tape, the composite's space usage is
at most the sum of the phases' space usages on that tape.

**Proof sketch.** `Finset.card_le_card` on
`seamCompTM_visitedByTapeHead`, then `Finset.card_union_le`. -/
theorem seamCompTM_spaceUsedByTape_le_add [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).spaceUsedByTape
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ≤
      M₁.spaceUsedByTape (Cfg.ofWords (input := x) start w₀) T₁ i +
        M₂.spaceUsedByTape (Cfg.ofWords (input := x) entry w₁) T₂ i := by
  exact (Finset.card_le_card
    (seamCompTM_visitedByTapeHead M₁ exit M₂ entry start q₂ w₀ w₁ w₂
      T₁ T₂ h₁ hcut h₂ i)).trans (Finset.card_union_le _ _)

/-- **R2 space, the total sum corollary** (spec, fill pending — design
§12). The composite's total space usage is at most the sum of the
phases' total space usages.

**Proof sketch.** Sum `seamCompTM_spaceUsedByTape_le_add` over all tapes
(`Finset.sum_le_sum`), then distribute the sum over the addition. -/
theorem seamCompTM_spaceUsed_le_add [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) :
    (seamCompTM M₁ exit M₂ entry).spaceUsed
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) ≤
      M₁.spaceUsed (Cfg.ofWords (input := x) start w₀) T₁ +
        M₂.spaceUsed (Cfg.ofWords (input := x) entry w₁) T₂ := by
  unfold MultiTapeTM.spaceUsed
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ =>
    seamCompTM_spaceUsedByTape_le_add M₁ exit M₂ entry start q₂ w₀ w₁ w₂
      T₁ T₂ h₁ hcut h₂ i

/-- **R2 space, the max corollary for disjointly-owned tapes** (spec, fill
pending — design §12, frozen decision 12.1: the sharpest available form).
If one of the two phases is *idle* on tape `i` — its visited set is the
seam-origin singleton `{0}` — then the composite's space usage on `i` is
bounded by the **max** of the phases' usages, not their sum. Under a
tape-ownership discipline (each work tape owned by one phase, the other
phase never moving its head there) this gives per-tape space equal to the
owner's, which is what the chapter-4 consumers depend on.

**Proof sketch.** From `seamCompTM_visitedByTapeHead` the composite's
visited set is contained in the union, and the idle side's singleton
`{0}` is already contained in the other side's visited set — a seam
configuration has every head at the origin, so `0` is in every phase's
visited set at every horizon. The union collapses to the non-idle side's
set; `Finset.card_le_card` and `le_max_left/right` finish. -/
theorem seamCompTM_spaceUsedByTape_le_max [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    (start : S₁) (q₂ : S₂) (w₀ w₁ w₂ : Fin k → List Bool) (T₁ T₂ : ℕ)
    (h₁ : M₁.runFrom (Cfg.ofWords (input := x) start w₀) T₁ =
      Cfg.ofWords exit w₁)
    (hcut : ∀ t < T₁,
      (M₁.runFrom (Cfg.ofWords (input := x) start w₀) t).state ≠ some exit)
    (h₂ : M₂.runFrom (Cfg.ofWords (input := x) entry w₁) T₂ =
      Cfg.ofWords q₂ w₂) (i : Fin k)
    (hown : M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i
        = {0} ∨
      M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i = {0}) :
    (seamCompTM M₁ exit M₂ entry).spaceUsedByTape
        (Cfg.ofWords (input := x) (Sum.inl start) w₀) (T₁ + 1 + T₂) i ≤
      max (M₁.spaceUsedByTape (Cfg.ofWords (input := x) start w₀) T₁ i)
        (M₂.spaceUsedByTape (Cfg.ofWords (input := x) entry w₁) T₂ i) := by
  have hzero₁ : (0 : ℤ) ∈
      M₁.visitedByTapeHead (Cfg.ofWords (input := x) start w₀) T₁ i :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ T₁), rfl⟩
  have hzero₂ : (0 : ℤ) ∈
      M₂.visitedByTapeHead (Cfg.ofWords (input := x) entry w₁) T₂ i :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ T₂), rfl⟩
  have hsub := seamCompTM_visitedByTapeHead M₁ exit M₂ entry start q₂
    w₀ w₁ w₂ T₁ T₂ h₁ hcut h₂ i
  rcases hown with hown | hown
  · rw [hown, Finset.union_eq_right.mpr
      (Finset.singleton_subset_iff.mpr hzero₂)] at hsub
    exact (Finset.card_le_card hsub).trans (le_max_right _ _)
  · rw [hown, Finset.union_eq_left.mpr
      (Finset.singleton_subset_iff.mpr hzero₁)] at hsub
    exact (Finset.card_le_card hsub).trans (le_max_left _ _)

/-- **R2′, general-configuration seam-to-seam composition** (spec, fill
pending — round-1 repair R2): the `Cfg.ofWords` restriction of
`Turing.seamCompTM_run` is lifted. If `M₁` carries an arbitrary
configuration `c₀` to `c₁` in exactly `T₁` steps, first reaching the anchor
`exit` there, and `M₂` carries `c₁` **with only the control state replaced
by `entry`** to `c₃` in `T₂` steps, then the composite carries the
`Sum.inl`-mapped `c₀` to the `Sum.inr`-mapped `c₃` in exactly
`T₁ + 1 + T₂` steps: the dispatch step is stationary, silent, and
write-free, so displaced inactive heads, noncanonical tape contents, the
input position, and **accumulated output** all cross it intact — exactly
the seams the round-1 audit exhibited (`emitterP2_relocate_run`'s arbitrary
frames, `exists_emitCallTM`'s nonempty output) that no `Cfg.ofWords`
endpoint can describe. The canonical `seamCompTM_run` is the
`Cfg.ofWords` instance.

**Proof sketch.** Identical three-segment decomposition to
`seamCompTM_run` — phase-one `Sum.inl` lockstep under the cut, one
dispatch step, phase-two `Sum.inr` lockstep via `Cfg.mapState_apply` —
with the single new observation that a stationary write-free action fixes
**every** field of an arbitrary configuration, not only a canonical one
(`Turing.Action.apply` componentwise). Fill obligations, named: the two
lockstep inductions over `Cfg.mapState`, the dispatch-step field check,
and the `ofWords` specialization recovering the canonical theorem. -/
theorem seamCompTM_run_ofCfg [DecidableEq S₁] (M₁ : MultiTapeTM k Bool S₁)
    (exit : S₁) (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {c₃ : Cfg k Bool S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃) :
    (seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) =
      c₃.mapState Sum.inr := by
  exact seamComp_run_general M₁ exit M₂ entry h₁ hexit hcut h₂

/-- **R2′, the general inherited first-return cut** (spec, fill pending —
round-1 repair R2): under the hypotheses of
`Turing.seamCompTM_run_ofCfg`, if `M₂` first reaches `q₂` at `T₂`, the
composite first reaches `Sum.inr q₂` at `T₁ + 1 + T₂`.

**Proof sketch.** As `seamCompTM_firstReturn`, over the general lockstep
segments: left times produce `Sum.inl` states, right times the
`Sum.inr`-mapped `M₂` states at shifted time, and injectivity of the
constructors transports the cuts. -/
theorem seamCompTM_firstReturn_ofCfg [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂) (q₂ : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {c₃ : Cfg k Bool S₂ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit)
    (h₂ : M₂.runFrom (c₁.mapState fun _ => entry) T₂ = c₃)
    (hq : c₃.state = some q₂)
    (hcut₂ : ∀ t < T₂,
      (M₂.runFrom (c₁.mapState fun _ => entry) t).state ≠ some q₂) :
    ∀ t < T₁ + 1 + T₂,
      ((seamCompTM M₁ exit M₂ entry).runFrom (c₀.mapState Sum.inl) t).state ≠
        some (Sum.inr q₂) := by
  exact seamComp_firstReturn_general M₁ exit M₂ entry q₂ h₁ hexit hcut hcut₂

/-- **R2′ space, the general per-tape headline** (spec, fill pending —
round-1 repair R2): under the hypotheses of `Turing.seamCompTM_run_ofCfg`,
on every work tape the composite's visited set over the composed run is
contained in the union of the two phases' visited sets — the
general-configuration form of `Turing.seamCompTM_visitedByTapeHead`, from
which the canonical corollaries project.

**Proof sketch.** As the canonical headline: the two lockstep segments
reproduce the phases' trajectories, and the dispatch step is stationary at
a point both phases' endpoint/start configurations already visit. -/
theorem seamCompTM_visitedByTapeHead_ofCfg [DecidableEq S₁]
    (M₁ : MultiTapeTM k Bool S₁) (exit : S₁)
    (M₂ : MultiTapeTM k Bool S₂) (entry : S₂)
    {c₀ c₁ : Cfg k Bool S₁ x} {T₁ T₂ : ℕ}
    (h₁ : M₁.runFrom c₀ T₁ = c₁) (hexit : c₁.state = some exit)
    (hcut : ∀ t < T₁, (M₁.runFrom c₀ t).state ≠ some exit) (i : Fin k) :
    (seamCompTM M₁ exit M₂ entry).visitedByTapeHead (c₀.mapState Sum.inl)
        (T₁ + 1 + T₂) i ⊆
      M₁.visitedByTapeHead c₀ T₁ i ∪
        M₂.visitedByTapeHead (c₁.mapState fun _ => entry) T₂ i := by
  exact seamComp_visited_general M₁ exit M₂ entry h₁ hexit hcut i

variable {S : Type*}

/-- **R3′, the fresh-entry/release adapter** (round-1 repair R3). The seam
combinator dispatches at its exit anchor **before** that state's action, so
a positive call that starts and ends at one anchor cannot be cut
(`seamCompTM_firstReturn`'s cut is contradictory at zero — the round-1
finding, witnessed by `exists_installCallTM`/`exists_emitCallTM`'s
strictly-positive interior promises and `emitterP2_call_segment`'s
execute-first discipline). The adapter runs `M` on states `Unit ⊕ S` with a
fresh start `Sum.inl ()` that executes the anchor's action
**unconditionally**, after which control lives in the `Sum.inr` copy — so
the *first re-arrival* at `Sum.inr anchor` is a genuine positive-time
event a seam can consume as its left exit. -/
def seamReleaseTM (M : MultiTapeTM k Bool S) (anchor : S) :
    MultiTapeTM k Bool (Unit ⊕ S) where
  q₀ := Sum.inl ()
  tr := fun q inp w =>
    match q with
    | Sum.inl _ =>
      let a := M.tr anchor inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩
    | Sum.inr s =>
      let a := M.tr s inp w
      ⟨a.inputTape, a.workTapes, a.output, a.state.map Sum.inr⟩

/-- The fresh state executes the anchor action without a dispatch step. -/
private lemma seamRelease_fresh_step (M : MultiTapeTM k Bool S) (anchor : S)
    (c : Cfg k Bool S x) (hc : c.state = some anchor) :
    (seamReleaseTM M anchor).step (c.mapState fun _ => Sum.inl ()) =
      (M.step c).mapState Sum.inr := by
  simp only [MultiTapeTM.step, Cfg.mapState, hc, Option.map_some]
  rfl

/-- In the right copy, release steps commute with state mapping. -/
private lemma seamRelease_step_right (M : MultiTapeTM k Bool S) (anchor : S)
    (c : Cfg k Bool S x) :
    (seamReleaseTM M anchor).step (c.mapState Sum.inr) =
      (M.step c).mapState Sum.inr := by
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, Cfg.mapState, hs]
  | some q =>
    simp only [MultiTapeTM.step, Cfg.mapState, hs, Option.map_some]
    rfl

/-- At every positive time, release runs are the right-mapped source runs.
**Proof sketch.** Execute the fresh step once, then iterate the right-step
identity. This also covers a source that halts or never returns. -/
private lemma seamRelease_run_pos (M : MultiTapeTM k Bool S) (anchor : S)
    (c : Cfg k Bool S x) (hc : c.state = some anchor) (t : ℕ) (ht : 0 < t) :
    (seamReleaseTM M anchor).runFrom (c.mapState fun _ => Sum.inl ()) t =
      (M.runFrom c t).mapState Sum.inr := by
  cases t with
  | zero => omega
  | succ t =>
    rw [MultiTapeTM.runFrom_succ_eq_step, seamRelease_fresh_step M anchor c hc,
      MultiTapeTM.runFrom_succ_eq_step]
    exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)
      (seamRelease_step_right M anchor) _ t

/-- **R3′, the positive first return through the adapter** (spec, fill
pending — round-1 repair R3): if `M`, started at its anchor, first
re-visits the anchor at a strictly positive time `T`, then the adapter,
started at its fresh state over the same configuration, reaches
`Sum.inr anchor` first at exactly `T`, over the `Sum.inr`-transported run.
The audit's S7 check is the smallest case: a two-step write-then-return
call executes both source actions before any seam dispatch can fire.

**Proof sketch.** The fresh step applies the anchor's action verbatim
(`Cfg.mapState_apply` at the constant relabeling), after which every step
is `Sum.inr`-lockstep with `M`'s run; the first-visit clause is the
transported cut, with time zero excluded by the fresh constructor
(`Sum.inl ≠ Sum.inr`). Fill obligations, named: the fresh-step equation,
the lockstep induction, and the cut transport. -/
theorem seamReleaseTM_firstReturn (M : MultiTapeTM k Bool S) (anchor : S)
    {c c' : Cfg k Bool S x} {T : ℕ}
    (hc : c.state = some anchor) (hT : 0 < T) (h : M.runFrom c T = c')
    (hc' : c'.state = some anchor)
    (hcut : ∀ t, 0 < t → t < T → (M.runFrom c t).state ≠ some anchor) :
    (seamReleaseTM M anchor).runFrom (c.mapState fun _ => Sum.inl ()) T =
        c'.mapState Sum.inr ∧
      ∀ t < T,
        ((seamReleaseTM M anchor).runFrom
            (c.mapState fun _ => Sum.inl ()) t).state ≠
          some (Sum.inr anchor) := by
  constructor
  · rw [seamRelease_run_pos M anchor c hc T hT, h]
  · intro t ht
    by_cases htpos : 0 < t
    · rw [seamRelease_run_pos M anchor c hc t htpos]
      intro heq
      apply hcut t htpos ht
      change Option.map Sum.inr (M.runFrom c t).state =
        some (Sum.inr anchor) at heq
      obtain ⟨q, hq, heq⟩ := Option.map_eq_some_iff.mp heq
      exact hq.trans (congrArg some (Sum.inr.inj heq))
    · have htzero : t = 0 := by omega
      simp [htzero, Cfg.mapState, hc]

/-- **R3′ space** (spec, fill pending — round-1 repair R3): the adapter's
visited sets equal `M`'s at every time and on every tape — the trajectories
coincide step for step.

**Proof sketch.** Every adapter step applies the very action `M` applies at
the corresponding state (the fresh step at the anchor, `Sum.inr` steps at
their carried state), so the head trajectories agree; project
`seamReleaseTM_firstReturn`'s lockstep. -/
theorem seamReleaseTM_visitedByTapeHead (M : MultiTapeTM k Bool S)
    (anchor : S) {c : Cfg k Bool S x} (hc : c.state = some anchor)
    (t : ℕ) (i : Fin k) :
    (seamReleaseTM M anchor).visitedByTapeHead
        (c.mapState fun _ => Sum.inl ()) t i =
      M.visitedByTapeHead c t i := by
  unfold MultiTapeTM.visitedByTapeHead
  apply Finset.image_congr
  intro s _
  dsimp only
  by_cases hs : s = 0
  · subst s
    rfl
  · rw [seamRelease_run_pos M anchor c hc s (Nat.pos_of_ne_zero hs)]
    rfl

end Turing
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end Turing.FinTM
```


## ===== TCSlib/Complexity/TuringMachine/Build/Convention.lean =====

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
# Machine-construction library: the calling convention

The vocabulary module of the machine-construction library
(`machine-library-design.md`, design frozen 2026-10-03): the single seam
notion that the library's control combinators speak, plus the pure list/
arithmetic functions that the primitive contracts in
`TCSlib.Complexity.TuringMachine.Build.Primitives` are stated against.

**Status: proved.** This module is fully proved (definitions and two
glue lemmas), and the sibling `Build` modules' contracts stated against
it are now all proved as well (library fill batches and the emitter
increment; zero sorries). The `Build` surface was new Chapter-1 growth,
audited in the shared infrastructure and emitter rounds
(`audits/ch1-infra-*`, `audits/emitter-*`).

## The seam notion

The model already gives *whole* machines a clean boundary: read-only input,
blank work tapes, append-only output, start at `Turing.MultiTapeTM.initCfg`.
The library therefore needs a configuration discipline only where a
construction crosses an *internal* seam — the round boundary of the loop
combinator and the entry of a wrapped subroutine. `Turing.Cfg.ofWords` is
that discipline: control at a designated anchor, input head at its initial
position, every work tape holding one word from the origin
(`Turing.FinTM.bufferTape`) with its head at the origin, output empty. A
loop body's contract is "`ofWords` in, `ofWords` out", and — per the frozen
design decision — the body *restores its own scratch to blank* (its scratch
words are `[]` on both sides of the contract) rather than relying on a
generic clearing pass.

## Main definitions

* `Turing.Cfg.ofWords` — the canonical seam configuration: anchor state,
  input head at 1, work tape `i` holding word `w i` from the origin, heads
  at the origin, empty output.
* `Turing.splitAtLastTrue` — strip a marker suffix: the prefix before the
  last `true`, or `none` if the word is all `false` (the audited marker
  discipline of the Chapter-2 Exercise-2.1 construction).
* `Turing.solveSplit` — least solution `i ≤ n` of the padding length
  equation `i + C·(i+1)^e = n`, or `none` (the split-search discipline of
  the padding constructions).
* `Turing.incFixed` — little-endian fixed-width binary increment with
  explicit overflow (`none`), width preserved (the enumerator's counter
  discipline; width zero overflows immediately).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the k-tape machine model the
  seams are stated over.)
-/

namespace Turing

variable {k : ℕ} {State : Type*}

/-- The canonical seam configuration of the machine-construction library:
control at the anchor state `q`, input head at its initial position `1`,
work tape `i` holding the word `w i` written from the origin
(`Turing.FinTM.bufferTape`), every work head at the origin, and the output
empty. Loop-round and wrapper-entry contracts are stated as equations
between `runFrom` results and `ofWords` configurations; a body that owns
scratch tapes lists them with word `[]` on both sides of its contract
(body-restores-scratch, the frozen design decision 9.2). -/
def Cfg.ofWords {input : List Bool} (q : State) (w : Fin k → List Bool) :
    Cfg k Bool State input :=
  ⟨some q, 1, fun i => FinTM.bufferTape (w i), fun _ => 0, []⟩

/-- A machine's genuine initial configuration is the seam configuration at
its start state with every tape word empty: `Cfg.init` has blank tapes and
`Turing.FinTM.bufferTape [] = fun _ => none`. This is the lemma that lets a
combinator's startup phase begin from a seam rather than from a bespoke
initialization invariant. -/
lemma initCfg_ofWords (tm : MultiTapeTM k Bool State) (x : List Bool) :
    tm.initCfg x = Cfg.ofWords tm.q₀ (fun _ => []) := by
  simp only [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, FinTM.bufferTape_nil]

/-- The seam words of a configuration are read back literally: at a seam,
work tape `i` holds exactly `w i` on cells `0, …, |w i| − 1` and blanks
elsewhere. Unfolds `Cfg.ofWords` for consumers that reason cell-wise. -/
lemma Cfg.ofWords_workTapes {input : List Bool} (q : State)
    (w : Fin k → List Bool) (i : Fin k) :
    (Cfg.ofWords (input := input) q w).workTapes i = FinTM.bufferTape (w i) :=
  rfl

/-- Strip a marker suffix: the prefix of `v` before its **last** `true`, or
`none` when `v` is all `false`. This is the Chapter-2 Exercise-2.1 marker
discipline (split at the last `true`; an all-`false` certificate region is
a rejection), stated once as a pure function so that machine contracts and
the chapter-side semantic lemmas name the same operation. -/
def splitAtLastTrue (v : List Bool) : Option (List Bool) :=
  match v.reverse.dropWhile (fun b => !b) with
  | true :: rest => some rest.reverse
  | _ => none

/-- Least index `i ≤ n` solving the padding length equation
`i + C·(i+1)^e = n`, or `none` when no solution exists. Strict monotonicity
of `i ↦ i + C·(i+1)^e` makes the solution unique; the machine contract
`Turing.FinTM.computesFunInTime_splitSolve` performs this bounded search. -/
def solveSplit (C e n : ℕ) : Option ℕ :=
  (List.range (n + 1)).find? fun i => i + C * (i + 1) ^ e == n

/-- Little-endian fixed-width binary increment with explicit overflow:
`incFixed w` is the successor word of the same length, or `none` when `w`
is all `true` (overflow) — in particular width zero overflows immediately,
matching the enumerator's audited counter discipline. -/
def incFixed : List Bool → Option (List Bool)
  | [] => none
  | false :: rest => some (true :: rest)
  | true :: rest => (incFixed rest).map (false :: ·)

/-- **Emitter-increment vocabulary** (design §11): least
solution `i ≤ n` of the width-parametric split equation `i + f i = n`, or
`none` — the generalization of `Turing.solveSplit` from the hardwired
polynomial family to an arbitrary width function. At
`f = fun i => C * (i + 1) ^ e` this definitionally recovers
`solveSplit C e n`. Customers: the 3A-continuation's exponential padding
equation (through `computesFunInTime_splitSolveWith`) and later padding
arguments. No machine content: `List.range` search, first match. -/
def solveSplitWith (f : ℕ → ℕ) (n : ℕ) : Option ℕ :=
  (List.range (n + 1)).find? fun i => i + f i == n

/-- **Emitter-increment vocabulary** (design §11): split off
the leading unary token — the maximal `true`-prefix together with its
terminating `false` delimiter — returning the token and the remainder. A
word with no delimiter yields the whole word as an unterminated token with
empty remainder; the empty word yields two empty words; a leading `false`
is the length-zero token `[false]`. This operation consumes **unary
tokens** — the shared atom of the serialization grammars (unary indices
with terminators). It does not consume standalone single-bit markers or
polarity bits: `unaryTokenSplit [true, false, true] =
([true, false], [true])`, a terminated unary-one token, not a lone
`true` marker — scanners handle markers and polarity by their own
grammar states (emitter-infra round-1 audit, finding 4). Customers: the
3B continuation's streaming scanner, the Cook-Levin emitter's index
reads (4A), 4B's dual scanner. No machine content: structural recursion
on the word. -/
def unaryTokenSplit : List Bool → List Bool × List Bool
  | [] => ([], [])
  | false :: rest => ([false], rest)
  | true :: rest =>
    let (tok, r) := unaryTokenSplit rest
    (true :: tok, r)

end Turing
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


## ===== audits/logs/routine-f1-integration-sweep.log =====

```
S12 F1 INTEGRATION SWEEP at commit 2f67e910bb3a617d769524bb109bd9573cb1bbea (2f67e910), branch complexity/arora-barak-ch3-4, started 2026-10-09 08:57:41
== TCSlib/Complexity/TuringMachine/Build/Embed
TCSlib/Complexity/TuringMachine/Build/Embed.lean:330:5: warning: unused variable `hcap`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Build/Embed.lean:790:5: warning: unused variable `hcap`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
== TCSlib/Complexity/TuringMachine/Build/Seam
TCSlib/Complexity/TuringMachine/Build/Seam.lean:347:5: warning: unused variable `h₂`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Build/Seam.lean:387:5: warning: unused variable `h₂`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Build/Seam.lean:543:5: warning: unused variable `h₂`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Build/Seam.lean:544:5: warning: unused variable `hq`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Build/Seam.lean:650:5: warning: unused variable `hc'`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
== TCSlib/Complexity/TuringMachine/Build/Catalog
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:356:58: warning: unused variable `hr`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:362:28: warning: This simp argument is unused:
  List.getElem?_eq_none

Hint: Omit it from the simp argument list.
  simp [FinTM.bufferTape,̵ ̵L̵i̵s̵t̵.̵g̵e̵t̵E̵l̵e̵m̵?̵_̵e̵q̵_̵n̵o̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:367:14: warning: This simp argument is unused:
  List.getElem?_take

Hint: Omit it from the simp argument list.
  simp [L̵i̵s̵t̵.̵g̵e̵t̵E̵l̵e̵m̵?̵_̵t̵a̵k̵e̵,̵ ̵hzr, show z.toNat < r + 1 by omega]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:413:45: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp_all [SignType.cast,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:427:8: warning: This simp argument is unused:
  show (r + 1 : ℕ) - (1 : ℤ) = (r : ℤ) by omega

Hint: Omit it from the simp argument list.
  simp [catalogClearR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, s̵h̵o̵w̵ ̵(̵r̵ ̵+̵ ̵1̵ ̵:̵ ̵ℕ̵)̵ ̵-̵ ̵(̵1̵ ̵:̵ ̵ℤ̵)̵ ̵=̵ ̵(̵r̵ ̵:̵ ̵ℤ̵)̵ ̵b̵y̵ ̵o̵m̵e̵g̵a̵,̵List.getElem?_take,
          List.getElem?_eq_getElem hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:428:8: warning: This simp argument is unused:
  List.getElem?_take

Hint: Omit it from the simp argument list.
  simp [catalogClearR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols,
          show (r + 1 : ℕ) - (1 : ℤ) = (r : ℤ) by omega,
  ̵  ̵ ̵ ̵ ̵ ̵ ̵ ̵List.getElem?_t̵a̵k̵e,̵ ̵L̵i̵s̵t̵.̵g̵e̵t̵E̵l̵e̵m̵?̵_̵e̵q_getElem hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:431:42: warning: This simp argument is unused:
  catalogClearF

Hint: Omit it from the simp argument list.
  simp [Action.apply, catalogClearF̵,̵ ̵c̵a̵t̵a̵l̵o̵g̵C̵l̵e̵a̵r̵R, catalogCfg, Cfg.ofWords]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:413:65: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:439:65: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:413:65: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:439:65: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:484:51: warning: This simp argument is unused:
  Ne.symm hne

Hint: Omit it from the simp argument list.
  simp [hj, hs, hne,̵ ̵N̵e̵.̵s̵y̵m̵m̵ ̵h̵n̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:487:44: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:487:44: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:517:8: warning: This simp argument is unused:
  show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega

Hint: Omit it from the simp argument list.
  simp [catalogCopyR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
          s̵h̵o̵w̵ ̵(̵(̵r̵ ̵+̵ ̵1̵ ̵:̵ ̵ℕ̵)̵ ̵:̵ ̵ℤ̵)̵ ̵-̵ ̵1̵ ̵=̵ ̵(̵r̵ ̵:̵ ̵ℤ̵)̵ ̵b̵y̵ ̵o̵m̵e̵g̵a̵,̵
  ̵ ̵ ̵ ̵ ̵ ̵ ̵ ̵ ̵List.getElem?_eq_getElem hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:524:65: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:524:65: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:567:8: warning: This simp argument is unused:
  show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega

Hint: Omit it from the simp argument list.
  simp [catalogTransferR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne, s̵h̵o̵w̵ ̵(̵(̵r̵ ̵+̵ ̵1̵ ̵:̵ ̵ℕ̵)̵ ̵:̵ ̵ℤ̵)̵ ̵-̵ ̵1̵ ̵=̵ ̵(̵r̵ ̵:̵ ̵ℤ̵)̵ ̵b̵y̵ ̵o̵m̵e̵g̵a̵,̵List.getElem?_take,
          List.getElem?_eq_getElem hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:568:8: warning: This simp argument is unused:
  List.getElem?_take

Hint: Omit it from the simp argument list.
  simp [catalogTransferR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, hne,
          show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega,
  ̵  ̵ ̵ ̵ ̵ ̵ ̵ ̵List.getElem?_t̵a̵k̵e,̵ ̵L̵i̵s̵t̵.̵g̵e̵t̵E̵l̵e̵m̵?̵_̵e̵q_getElem hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:578:25: warning: This simp argument is unused:
  hne

Hint: Omit it from the simp argument list.
  simp [h̵n̵e̵,̵ ̵Ne.symm hne]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:641:13: warning: unused variable `hd`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:664:45: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp_all [SignType.cast,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:672:35: warning: This simp argument is unused:
  if_pos (Or.inl rfl : fst = fst ∨ fst = snd)

Hint: Omit it from the simp argument list.
  simp only [compareTM, hread, if_pos (̵O̵r̵.̵i̵n̵l̵ ̵r̵f̵l̵ ̵:̵ ̵f̵s̵t̵ ̵=̵ ̵f̵s̵t̵ ̵∨̵ ̵f̵s̵t̵ ̵=̵ ̵s̵n̵d̵)̵,̵
  ̵ ̵ ̵ ̵ ̵ ̵ ̵ ̵ ̵i̵f̵_̵p̵o̵s̵ ̵(Or.inr rfl : snd = fst ∨ snd = snd),
  ̲  ̲ ̲ ̲ ̲ ̲ ̲ ̲FinTM.bufferTape_nat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:673:8: warning: This simp argument is unused:
  if_pos (Or.inr rfl : snd = fst ∨ snd = snd)

Hint: Omit it from the simp argument list.
  simp only [compareTM, hread, if_pos (Or.inl rfl : fst = fst ∨ fst = snd),
          i̵f̵_̵p̵o̵s̵ ̵(̵O̵r̵.̵i̵n̵r̵ ̵r̵f̵l̵ ̵:̵ ̵s̵n̵d̵ ̵=̵ ̵f̵s̵t̵ ̵∨̵ ̵s̵n̵d̵ ̵=̵ ̵s̵n̵d̵)̵,̵ ̵FinTM.bufferTape_nat]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:673:53: warning: This simp argument is unused:
  FinTM.bufferTape_nat

Hint: Omit it from the simp argument list.
  simp only [compareTM, hread, if_pos (Or.inl rfl : fst = fst ∨ fst = snd),
          if_pos (Or.inr rfl : snd = fst ∨ snd = snd),̵ ̵F̵i̵n̵T̵M̵.̵b̵u̵f̵f̵e̵r̵T̵a̵p̵e̵_̵n̵a̵t̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:679:16: warning: This simp argument is unused:
  hf

Hint: Omit it from the simp argument list.
  simp [hf̵,̵ ̵h̵g, heq]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:664:65: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:721:65: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:664:65: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:721:65: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:827:45: warning: This simp argument is unused:
  sub_eq_add_neg

Hint: Omit it from the simp argument list.
  simp_all [SignType.cast,̵ ̵s̵u̵b̵_̵e̵q̵_̵a̵d̵d̵_̵n̵e̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:854:8: warning: This simp argument is unused:
  show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) by omega

Hint: Omit it from the simp argument list.
  simp [catalogIncR, catalogCfg, Cfg.ofWords, Cfg.workTapeSymbols, s̵h̵o̵w̵ ̵(̵(̵r̵ ̵+̵ ̵1̵ ̵:̵ ̵ℕ̵)̵ ̵:̵ ̵ℤ̵)̵ ̵-̵ ̵1̵ ̵=̵ ̵(̵r̵ ̵:̵ ̵ℤ̵)̵ ̵b̵y̵ ̵o̵m̵e̵g̵a̵,̵List.getElem?_append, hr]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:827:65: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:861:65: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:827:65: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:861:65: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1313:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1326:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1342:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1359:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1376:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1403:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1419:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1436:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1451:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1466:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1481:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1499:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1517:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1542:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1564:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1594:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1623:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1757:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1802:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/TuringMachine
S12_F1_SWEEP_DONE
```


## ===== audits/logs/routine-f1-axioms.log =====

```
'Turing.embedSilentTM_runFrom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.embedSilentTM_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.embedSilentTM_visitedByTapeHead' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.embedSilentTM_visitedByTapeHead_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.embedSilentTM_spaceUsedByTape_cap' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.embedEmitTM_runFrom' depends on axioms: [propext, Quot.sound]
'Turing.embedEmitTM_frame' depends on axioms: [propext, Quot.sound]
'Turing.embedEmitTM_visitedByTapeHead' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.embedEmitTM_visitedByTapeHead_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.embedSilentRetTM_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.embedEmitRetTM_run' depends on axioms: [propext, Quot.sound]
'Turing.embedSilentRetTM_visitedByTapeHead' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.embedEmitRetTM_visitedByTapeHead' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.seamCompTM_run' depends on axioms: [propext, Quot.sound]
'Turing.seamCompTM_firstReturn' depends on axioms: [propext, Quot.sound]
'Turing.seamCompTM_visitedByTapeHead' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.seamCompTM_spaceUsedByTape_le_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.seamCompTM_spaceUsed_le_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.seamCompTM_spaceUsedByTape_le_max' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.seamCompTM_run_ofCfg' depends on axioms: [propext, Quot.sound]
'Turing.seamCompTM_firstReturn_ofCfg' depends on axioms: [propext, Quot.sound]
'Turing.seamCompTM_visitedByTapeHead_ofCfg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.seamReleaseTM_firstReturn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.seamReleaseTM_visitedByTapeHead' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.transferTM_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.transferTM_spaceUsedByTape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.copyTM_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.copyTM_spaceUsedByTape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.clearTM_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.clearTM_spaceUsedByTape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.compareTM_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.compareTM_spaceUsedByTape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.incrementTM_run_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.incrementTM_run_overflow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.incrementTM_spaceUsedByTape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.capture_visitedByTapeHead' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.redirectTM_spaceUsedByTape' depends on axioms: [propext, Classical.choice, Quot.sound]
```


## ===== audits/logs/routine-f1-stylelint.log =====

```
WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  1851 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5713 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7636 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1109 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  1851 lines; 39 public / 33 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean               157 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    931 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    931 lines; 19 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5713 lines; 8 public / 214 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7636 lines; 18 public / 318 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     696 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     696 lines; 13 public / 13 private declarations
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
INFO  TCSlib/Complexity/TuringMachine/NDCodes.lean                        190 lines; 9 public / 0 private declarations
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

style_lint: 0 FAIL, 9 WARN over 39 files
```
