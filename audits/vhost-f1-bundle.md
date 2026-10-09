# External audit pack — zone/virtual-input layer (§13), tranche A-S1 fill gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4b,
track A). The A-S1 statement gate closed in one round
(`audits/vhost-infra-resolutions.md`); this round audits the **fill**: all
11 audited-true statements of the virtual-input half proved by one batch
(brief `briefs/vhost-f1.md`, report attached verbatim), making
`Build/VirtualInput.lean` and the Z5 statements of `Simulation.lean`
zero-sorry. Epoch gates close on zero blockers and zero majors
(`workflow.md` §4); failure-mode-5 rule in force.

Audited at commit `724108dd` (branch `complexity/arora-barak-ch3-4`). The
fill is the attached single-commit patch (Codex-authored, integrated by
`git am -3` as `4ae4e9b2`; a maintainer doc-only commit then refreshed the
module's stale status header). **Every proof is kernel-checked** — the
maintainer's replay evidence is below — so the audit object is the
**surface**: the one new private declaration, fidelity of the eleven
proofs to the statement-gate audit's binding routes (that audit's
findings are attached — its per-statement arguments were the mandated
proof plans), and the two declared technique notes.

## Brief for the auditor

1. **Blind-restate the single new private declaration**,
   `Turing.vhostSilent_layout`, from its body: it must be exactly the
   layout arithmetic the statement-gate audit verified independently
   (range of `Fin.castAddEmb 1` ↔ value below `1 + m`; complement ↔
   `vhostCap m`; `m = 0` included) — no more, no less. Both silent proofs
   and the silent space proof lean on it; a weaker completeness clause
   (an unaccounted ambient tape) would silently weaken the space ledger.
2. **Check proof fidelity to the binding routes** (the attached
   `vhost-infra-findings.md`, section "The eleven sorried statements,
   literally"): in particular — the step proof adapts, not copies, the
   `bufferedSecondCfg_step` template and cites `bufferTape_inputSymbol` +
   `virtualMove_correct`; the visited statements are proved as
   **equalities** via all-time projection; the silent pair performs **no
   third simulation induction** (two-layer citations only); the space
   proofs keep coefficient one at the same horizon with no output-length
   term on the emit side.
3. **Assess the two declared technique notes**: (i) `virtualMove_correct`
   is consumed at `c.mapState (fun _ => ())` to bridge the existing
   lemma's `S : Type` against the target's `S : Type*` — verify the
   control-only mapping leaves the input position and read definitionally
   unchanged and restricts nothing (a silent universe restriction of the
   frozen statements would be a major); (ii) the buffer/bank sum split is
   implemented with `Fin.addCases` + `Finset.sum_bij`/`sum_erase_add`
   because `Fin.sum_univ_add` is outside the import surface — verify no
   import changed and the split is the true partition.
4. **Freeze**: the maintainer's mechanical check found the patch's
   removals to be exactly the eleven `sorry` bodies, the delivered
   sources byte-identical to the integrated files, and the byte-level
   reconstruction (restore the eleven bodies, drop the one helper)
   recovers the base exactly. Re-establish from the attached patch; also
   verify the maintainer's post-fill status-header refresh (quoted in the
   decision log) is doc-only.
5. **Debt screen (failure mode 5)**: the delivery ledger says "new
   copies: none"; verify the eleven proofs cite rather than restate the
   buffered-host facts (the five prior private rebuilds of this pattern
   remain queued for 12.2c and are untouched).
6. Report anything the fill newly misstates — standard table, standard
   severity scale.

## Repository-side attestations (verify or challenge)

* Freeze (maintainer, mechanical): patch removals are exactly the eleven
  `sorry` lines; one declaration added (private); both delivered full
  sources byte-identical to the integrated files; diff touches only the
  two owned files; the bundle verifies against the recorded base
  `44d25413`.
* Fresh replay (`audits/logs/vhost-f1-integration-sweep.log`): the five
  prescribed modules (`Simulation`, `Build/Embed`, `Build/VirtualInput`,
  `Build/Catalog`, the `TuringMachine` facade) all exit 0 — **0 errors,
  0 sorry warnings**, fresh `.olean`s. (The tree's remaining sorries are
  the A-S2 statement surface, out of scope and in its own gate.)
* Independent axiom prints (`audits/logs/vhost-f1-axioms.log`,
  maintainer-generated): all **11** within
  `[propext, Classical.choice, Quot.sound]` — the two Z5 transfers at the
  proper subset `[propext, Quot.sound]` — and `sorryAx` nowhere.
* Style lint: 0 FAIL; `Simulation.lean` at 1,014 lines under its recorded
  justification; `VirtualInput.lean` 506 lines.
* Delivery integrity: `SHA256SUMS` all OK; duplication ledger "new
  copies: none"; the delivery notes a runtime executable-path shim was
  needed in its environment but ships no shim source and the patch
  references none.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/vhost-f1-findings.md`; the gate closes on zero blockers and
majors, which completes tranche A-S1 end to end (statements, gate, fill,
fill gate) and leaves §13 waiting only on the A-S2 loop.

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

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), and the program layers (`LogProg.ARM`,
`CounterProg`) where a register-level description suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

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
fresh sweep; the headline axiom prints; and the **duplication ledger** — every
private copy of existing proved material in the delivery enumerated, with each
touched file's cumulative copied-material count and fraction. If a delivery pushes a
file past **one fifth copied material**, or adds copies to a file that already
received copies in an earlier epoch, the maintainer opens a `backlog.md` §1
human-review item before the epoch's audit pack ships — no discretion. Integration
is `git am -3` from the patch series, preserving the agent's authorship. Large fills that exhaust one agent's budget
continue via a continuation brief to a fresh agent (the `universal` B2 precedent).

**Epoch boundaries**: the maintainer re-runs the full sweep, produces a **drift
attestation** (§6), and prepares the epoch's audit pack with elaboration evidence
and the epoch's **duplication ledger**, which the auditor verifies independently
(audit template failure mode 5); the epoch's gate follows the same
zero-blockers/majors rule as phase gates, and a debt major closes only by explicit
human acknowledgment recorded in the resolutions file.

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

## ===== briefs/vhost-f1.md =====

```
# §13 fill campaign — Tranche A-S1, single batch: the virtual-input layer and the agreement transfer (`Build/VirtualInput.lean` + `Simulation.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/vhost-f1`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `756657d0b45f41f2a5e93f976f3189ce99080772`), and never
  rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `vhost-f1.zip` with `REPORT.md`, both full modified source files, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

You are filling the **11 audited-true statements** of the §13 tranche
A-S1 (the virtual-input layer): 9 in
`TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean` and 2 in
`TCSlib/Complexity/TuringMachine/Simulation.lean`. The statement gate
closed in one round (`audits/vhost-infra-{findings,resolutions}.md` —
read both). **The auditor supplied a complete per-statement mathematical
argument for every target; those arguments are quoted verbatim below and
are the binding proof routes.** The in-repo fill template is the proved
`Turing.FinTM.bufferedSecondCfg_step`/`bufferedSecondCfg_run`
(`Simulation.lean` — the same arbitrary-source-configuration, valid-tag,
existential-arrival-tag, all-horizon shape; your Z1 proofs adapt them with
the inactive first block removed and an output prefix carried along).

Retrofit batches RB1/RB3 run concurrently on `Build/Loop.lean` and
`CookLevin/Hardness.lean` — **you never touch those files**.

## Owned files (modify these and nothing else)

`Build/VirtualInput.lean` — all 9 sorried theorems, suggested order:
1. `vhostEmitTM_step` 2. `vhostEmitTM_runFrom` (the core pair)
3. `vhostEmitTM_visitedByTapeHead_bank`
4. `vhostEmitTM_visitedByTapeHead_buffer` 5. `vhostCfg_buffer_head_mem`
6. `vhostEmitTM_spaceUsed_le` 7. `vhostEmitTM_emitting_halt`
8. `vhostSilentTM_runFrom` 9. `vhostSilentTM_spaceUsed_le` (the two
silent contracts are **two-layer citations** — `embedSilentTM_runFrom`
and the R1 silent space clauses over your targets 2 and 6; perform no
third simulation induction).

`Simulation.lean` — the 2 sorried theorems:
10. `MultiTapeTM.step_eq_of_agreeOn` 11. `MultiTapeTM.runFrom_eq_of_agreeOn`.

## Optional permanent lemmas (audit-adopted; deliver any subset, each flagged)

Public additions sanctioned by the gate close (resolutions, "Adopted"):
(a) `VirtualTag (1 : Fin (y.length + 2)) true` and `q₀`-independence of
`runFrom` (replacing `q₀` with the table fixed changes no run);
(b) injectivity of `fun c => vhostCfg c b p pre` at fixed `b, p, pre` —
do **not** assert joint `(c, b)` injectivity (halted transports forget the
tag); (c) native-head constancy for **arbitrary** host configurations
(`((vhostEmitTM M).runFrom d t).inputPos = d.inputPos`), stated as an
input-position fact, never as a work-tape index; (d) named empty-word
left/right clamp corollaries and a silent emitting-halt projection. List
each delivered one in `REPORT.md` under "Optional exports".

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules; the known baseline admissions are out of scope:
  `CounterProgRun`'s S9 and the chapter-3/4 statement surfaces), then
  check `Build/Embed`, `Build/Seam`, `Build/Catalog`, and
  `Build/VirtualInput` in that order.
- Iterate per edit on the file you changed. Final, in order:
  `Simulation`, `Build/Embed`, `Build/VirtualInput`, `Build/Catalog`,
  then `TCSlib/Complexity/TuringMachine` (the facade) — zero `error:`
  lines and **zero `sorry` warnings in all five**, fresh `.olean`s.
- **Axiom prints**: `#print axioms` for all 11 filled theorems on the
  final fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` — proper subsets fine — and
  no `sorryAx`: this batch has no sanctioned admitted dependency.
- Style lint (one directory per invocation):
  `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  and `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`
  — 0 FAIL (Simulation's 1,005-line WARN is justified in the plan's
  decision log; cite that justification in `REPORT.md`, do not split the
  file).

## Ground rules (binding)

1. **File ownership.** Only the two owned files, and only the 11 targets'
   proofs, `private` helpers, and the flagged optional exports. Shared
   wishes go under "Requested shared lemmas" in `REPORT.md` with a
   `private` local copy. List every new declaration — the epoch audit
   blind-restates them.
2. **Statement freeze.** No renames, re-signatures, restatements, or
   attribution edits anywhere. Docstring sketch appendices allowed,
   flagged.
3. **Duplication governance** (`policy.md`, **Duplication**): zero new
   copies of existing proved material; `REPORT.md` carries the ledger line
   ("new copies: none" expected). In particular, adapt — do not copy —
   the `bufferedSecondCfg` proofs: cite `bufferTape_inputSymbol`,
   `virtualMove_correct`, and the `runFrom` lemmas rather than restating
   them.
4. **Escalation** on anything unprovable as stated: stop, record the
   obstruction, deliver what exists.
5. Docstrings stay; precise imports; keep `set_option` headers.
6. **Continuation budget**: 11 targets over one core. On exhaustion,
   deliver a partial zip whose `REPORT.md` states what is proved, which
   `private` helpers remain `sorry` (allowed **only** in a partial
   delivery, each listed), and the frontier.

## Inherited audit contract (verbatim; binding on the fill)

From `audits/vhost-infra-findings.md`, "The eleven sorried statements,
literally" — the route for each target, in the brief's numbering:

> 1. **`step_eq_of_agreeOn`.** If `c.state = none`, both steps equal `c`.
> Otherwise write `c.state = some q`; `hq` gives `q ∈ Q`, so `h` equates
> the two actions at `c.inputSymbol` and `c.workTapeSymbols`, and applying
> equal actions to the same configuration gives the stated equality.
>
> 2. **`runFrom_eq_of_agreeOn`.** Induct on the number of steps up to the
> requested horizon, with equality at zero because both runs start at `c`.
> At time `u < t`, substitute the already-equal configurations and apply
> the preceding step lemma using `hq u`; if that configuration is halted,
> equality is automatic. No assumption about the control at time `t` is
> needed, and no equality of the two `q₀` fields is needed.
>
> 3. **`vhostEmitTM_step`.** In the halted case take the original tag,
> because source and host configurations are both fixed. In the live case
> the buffer read is the source input read by `bufferTape_inputSymbol`,
> and the bank reads are identical by the transport's fields; choose
> `b' := virtualNextTag b (virtualMove b c.inputSymbol a.inputTape)`,
> where `a` is the source action. `virtualMove_correct` supplies both the
> exact buffer-head equation and validity of `b'`; all other configuration
> fields follow from the action definition and append associativity,
> including when `a.state = none`.
>
> 4. **`vhostEmitTM_runFrom`.** At time zero, use witness `b` and the
> supplied tag hypothesis. For the successor step, apply the step contract
> to the transported source configuration and its valid arrival tag, then
> substitute the source and host iteration identities. This works after a
> halt as well as before it and introduces no nonemptiness or liveness
> premise.
>
> 5. **`vhostEmitTM_visitedByTapeHead_bank`.** Apply the run contract
> separately at every `u ≤ t` and project `workTapePos (vhostBank i)`.
> The resulting head equals `(M.runFrom c u).workTapePos i`, independently
> of the existential arrival tag, so the two images of
> `Finset.range (t+1)` are equal. Thus the statement is equality, not
> merely containment.
>
> 6. **`vhostEmitTM_visitedByTapeHead_buffer`.** The corresponding
> buffer-head projection at each time `u ≤ t` is exactly
> `((M.runFrom c u).inputPos.val : ℤ) - 1`. Substitution into the defining
> finite image gives exactly the stated right-hand side, with both time
> zero and time `t` included.
>
> 7. **`vhostCfg_buffer_head_mem`.** The run identity gives the head as
> the integer source input position minus one. Since that position belongs
> to `Fin (y.length+2)`, its value lies between zero and `y.length+1`, so
> the transported head lies between `-1` and `y.length`, inclusively.
>
> 8. **`vhostEmitTM_spaceUsed_le`.** Split the sum of work-tape
> visited-set cardinalities into tape zero and the bank indexed by
> `Fin m`. The bank equalities give exactly `M.spaceUsed c t`, while the
> buffer equality and interval lemma bound its cardinality by
> `y.length+2`. This yields the printed coefficient one, at the same
> horizon, without any output-length term.
>
> 9. **`vhostEmitTM_emitting_halt`.** The hypotheses say that the action
> applied from the live source configuration has successor `none` and
> emission `some bit`. The host applies that same emission while mapping
> the successor to `none`, so its new output is
> `(pre ++ c.output) ++ [bit]`. Transporting the source step gives
> `pre ++ (c.output ++ [bit])`; append associativity makes these equal to
> the displayed contract, so the final bit is neither dropped nor
> duplicated.
>
> 10. **`vhostSilentTM_runFrom`.** Apply `embedSilentTM_runFrom` with
> source `vhostEmitTM M`, the specified embedding, capture tape, and
> transported starting configuration; the required capture-disjointness
> follows from the layout arithmetic [the unselected set is exactly the
> capture tape]. Substitute `vhostEmitTM_runFrom` and its valid arrival
> tag. The result is precisely `vhostSilentCfg` of the source endpoint,
> with capture prefix `capPre` and physical output `out₀` unchanged; no
> third simulation induction is needed.
>
> 11. **`vhostSilentTM_spaceUsed_le`.** Split the silent host into the
> selected forwarding host and its sole capture tape.
> `embedSilentTM_visitedByTapeHead` gives the selected contribution
> exactly, and `embedSilentTM_spaceUsedByTape_cap` bounds capture by
> source output growth plus one. That quantity is at most the final
> capture-word length plus one, so the forwarding bound gives exactly the
> stated inequality.

Also binding (the audit's layout arithmetic, verify it inside your proofs
of 10-11): for the silent layout,
`j ∈ range (Fin.castAddEmb 1) ↔ j.val < 1 + m`, and the complement is
exactly `vhostCap m` — capture is disjoint from the selected range and
there is no third, ambient case, including `m = 0`.

## Out-of-scope sorries you will see (leave untouched)

`CounterProgRun`'s `sim_run_of_regs_le` (S9, baseline); the chapter-3/4
statement surfaces (`NDCodes`, `Formulas/QBF*`, `Diagonalization/*`,
`ClassOracle/*`, `SpaceComplexity/*`, `ClassPSPACE/*`,
`TuringMachine/Oracle*`, `NondeterministicSpace`). Everything in
`Build/Loop.lean` and `CookLevin/Hardness.lean` (concurrent retrofit
batches own them).

## REPORT.md checklist

- [ ] 11/11 filled (or the partial frontier per ground rule 6).
- [ ] Base commit hash; every new `private` declaration listed; optional
      exports listed (or "none").
- [ ] Duplication ledger: "new copies: none".
- [ ] Final sweep log tail (the five checks, 0 errors / 0 sorries) +
      11 axiom prints (at most the standard triple; no `sorryAx`).
- [ ] Diff touches only the two owned files.

## Known pitfalls at this pin (hard-won)

- `Fin.addCases` on `Fin (1 + m)`: after `cases`/`refine Fin.addCases`,
  `simp [vhostCfg]` exposes the two blocks; the repo's
  `bufferedFirstCfg_init`/`bufferedSecondCfg_step` proofs show the exact
  `Fin.addCases ?_ ?_ i <;> intro j <;> simp [...]` idiom.
- `Option.map` on the control: `c.state.map (fun q => (q, b))` — after
  `cases hq : c.state`, `dsimp only` before rewriting; a halted transport
  has state `none` with no tag to track.
- `virtualMove_correct` consumes `c.inputSymbol`; rewrite the buffer read
  to it via `bufferTape_inputSymbol` **before** introducing the source
  action, as `bufferedSecondCfg_step` does (its `hv` step).
- `Function.update_of_ne` (not `update_noteq`); avoid bare `simp` with
  folded forms; `omega` needs beta-reduced, non-`Fin`-projection goals.
- Visited sets are `Finset.image` over `Finset.range (t + 1)`:
  trajectory equalities give image equalities pointwise
  (`Finset.image_congr`-style); for target 8 use the `Fin.sum_univ_succ`/
  `Fin.addCases` split of `spaceUsed`'s sum, not interval arithmetic.
- For targets 10-11, the R1 lemma names are `embedSilentTM_runFrom`,
  `embedSilentTM_visitedByTapeHead`, `embedSilentTM_spaceUsedByTape_cap`
  (`Build/Embed.lean`); instantiate `hcap` disjointness from the layout
  arithmetic, with `Fin.castAddEmb`'s value-preservation (`Fin.ext`,
  `omega`) closing the range computation.
- The `∃ b'` witnesses chain: never case on the existential tag of a
  previous time except through the lemma's own statement.
```

## ===== audits/vhost-infra-pack.md =====

```
# External audit pack — zone/virtual-input layer (§13), statement gate, tranche A-S1

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4b,
track A; design `machine-library-design.md` §13/§13a). The §13 statement
phase runs in two tranches; this round audits **A-S1, the virtual-input
half**: Z5 (the machine-agreement transfer, `Simulation.lean`, additive),
Z1 (`Build/VirtualInput.lean`, new), and the Z1 rider (four selected-tape
exports in `Build/Embed.lean`, skeleton-time proofs). The zone half
(Z2/Z3/Z4) follows as tranche A-S2 with its own gate. The gate closes on
zero blockers and zero majors (`workflow.md` §3), with the failure-mode-5
rule in force: a debt major closes only by explicit human acknowledgment.

Audited at commit `28a49d69` (branch `complexity/arora-barak-ch3-4`).
**The audit object is the statement surface**: 7 new definitions, 11
`sorry`d contracts (9 in `VirtualInput.lean`, 2 in `Simulation.lean`), and
4 skeleton-time-proved lemmas. The proofs that exist are kernel-checked;
hunt the five failure modes of `audits/TEMPLATE.md` (infidelity,
trivialization, unprovability, missing hypotheses, debt).

## Brief for the auditor

1. **Blind-restate every definition** from its body before reading its
   docstring, and report daylight: `MultiTapeTM.AgreeOn`; `vhostBuffer`/
   `vhostBank`/`vhostCap` (the `1 + m` and `(1 + m) + 1` layouts);
   `vhostCfg` (in particular the buffer-head convention — source input
   position **minus one** — and that a halted source maps to a halted
   host); `vhostEmitTM` (the clamped `virtualMove` discipline, the tag in
   control, the frozen native head, `q₀ = (M.q₀, true)`);
   `vhostSilentTM`/`vhostSilentCfg` (**the layer composing with itself**:
   `embedSilentTM (Fin.castAddEmb 1) (vhostCap m)` over `vhostEmitTM`).
   For the silent pair, verify the composition arithmetic yourself: the
   range of `Fin.castAddEmb 1` on `Fin (1+m)` misses **exactly** the
   capture tape, so the transport's ambient frame parameters
   (`fun _ _ => none`, `fun _ => 0`) are inert — confirm or exhibit a tape
   they touch.
2. **Argue each of the 11 sorried statements true as literally stated**,
   or exhibit the problem. The binding inherited contracts are the A2/F2
   audit clauses (attached `batchF2A2-REPORT.md` and the F2 findings'
   forwarding ledger): both boundary clamps with **no nonempty-`y`
   premise**, halt absorption, the source's halting emission executed
   before the control dies, coefficient-one space on the hosted bank. The
   named fill template is the proved
   `Turing.FinTM.bufferedSecondCfg_step`/`_run` — compare statement shapes
   and flag any weakening (note the visited-set statements claim
   **equality**, not containment).
3. **Adversarial instantiations** (at least eight): `y = []` (boundaries
   adjacent — both clamps, tag at `p.val = 1` forced `true`); `m = 0` (a
   bank-free source: the host is one buffer tape); `t = 0`; an initially
   halted `c`; a source action attempting the outward move at each
   boundary under each tag; the emitting halting step (does
   `vhostEmitTM_emitting_halt`'s output parse `(pre ++ c.output) ++ [bit]`
   match the step identity?); native `x = []` (`p : Fin 2`); nonempty
   `pre`/`capPre`. For Z5: `Q = ∅`, `Q = Set.univ`, a run that halts
   before `t`, machines agreeing nowhere outside `Q`.
4. **Z5 strength check against its named customers** (design §13 Z5;
   evidence attached in `retrofit-inventory/loop.md`): the forwarding loop
   host agrees with the capturing host on every non-body state — is
   `AgreeOn` + `runFrom_eq_of_agreeOn`'s visit hypothesis (`∀ u < t`,
   live states in `Q`) sufficient to collapse the fourteen re-proved phase
   lemmas, and sufficient for the guarded `clSlot_run`-style sites, or do
   those need a per-configuration (not per-state) agreement form? If the
   statement is too weak for the named customers, that is a major.
5. **The four rider lemmas** (`embedSilentCfg_selected_tape`/`_pos`,
   `embedEmitCfg_selected_tape`/`_pos`): skeleton-time proofs, flagged —
   blind-restate them and confirm they are the selected-tape projections
   the three retrofit inventories requested (the D-R1 blocker), and that
   their statements expose nothing beyond the transports' fields.
6. **Space-ledger shapes**: `vhostEmitTM_spaceUsed_le`'s constant
   (`y.length + 2`) and the silent bound's capture term
   (`(capPre ++ (M.runFrom c t).output).length + 1`) — right constants,
   right horizon, coefficient one on `M.spaceUsed`? The intended consumer
   of the silent ledger is the `NP^EXPCOM ⊆ EXP` query simulation; flag a
   shape that consumer cannot use.
7. **Debt screen (failure mode 5)**: this tranche must add **no new
   copies** of existing proved material. The five prior private
   re-derivations (`bufferedCompTM` phase two aside, which is public and
   stays) remain in place pending the recorded 12.2c dedup — verify the
   new file *defines* rather than copies (the transformer is new public
   surface; its contracts cite, not restate, `virtualMove_correct`), and
   verify the maintainer's ledger line below.
8. Report anything the statements misstate, in the standard table and
   severity scale; propose any missing machine-checkable sanity theorem
   (candidates you should weigh: an `initCfg`-free statement that the
   `q₀` tag claim in `vhostEmitTM`'s docstring is actually consumed
   nowhere; a `vhostCfg` injectivity/ext lemma; the emit flavor's
   `visitedByTapeHead` for the *native* input — note the native head is
   frozen by the run identity).

## Known deviations and declared anomalies (verify they are benign)

* The four rider lemmas are **proved at statement time** (rfl-grade at the
  private `embedSlot_selected`), keeping the closed `Embed.lean`
  zero-sorry; precedent: the P3.1/P4.1 skeleton-time proofs.
* `vhostSilentTM` is a **definition by composition**, not a bespoke
  machine; its two contracts are deliberately stated on the composite and
  sketched as two-layer citations. If you judge the composite statements
  underdetermined (e.g. the inert-frame analysis fails), that is a major.
* `Simulation.lean` crosses the size policy line at 1,005 lines; the
  justification (decision 13.5, additive growth, D7 split window) is
  recorded in the plan's decision log.
* The `q₀ := (M.q₀, true)` tag is asserted valid at the canonical start
  position in a docstring; no contract consumes `q₀`. Flag if any
  statement silently depends on it.

## Repository-side attestations (verify or challenge)

* Elaboration: `Simulation`, `Build/Embed`, `Build/VirtualInput` all check
  with exit 0, zero `error:` lines, fresh `.olean`s; exactly **11**
  `declaration uses 'sorry'` warnings (9 + 2); `Embed.lean` remains
  zero-sorry.
* Style lint: 0 FAIL over both directories; the one new WARN
  (`Simulation.lean` size) is justified as above; every `sorry` carries a
  literal **Proof sketch**.
* **Duplication ledger (failure mode 5): new copies — none.** The file
  defines new public surface; the five in-repo precedents are untouched
  and queued for 12.2c.
* Base: the statements were landed in one maintainer commit at
  `28a49d69`; no other file changed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md` (including failure mode 5);
findings verbatim into `audits/vhost-infra-findings.md`; the gate closes
on zero blockers and majors, after which the A-S1 fill epoch dispatches
and tranche A-S2 (the zone half) is drafted.
```

## ===== audits/vhost-infra-findings.md =====

```
# Virtual-input infrastructure: A-S1 statement-gate audit

**Verdict: PASS — 0 blockers, 0 majors, 2 minors.** No new duplication-debt major. The eleven sorried contracts are mathematically true as written, subject to the inherited machine semantics and proved infrastructure. This is a statement audit, not a claim that their missing Lean proofs have been filled or independently kernel-checked.

Audited material: the supplied ten-attachment bundle, labelled commit `28a49d69`, branch `complexity/arora-barak-ch3-4`. Bundle SHA-256:

`b76a53aa8be41c5eb80700e2b5cdb91aa831f367ce213fe51ce6d2eb490bee64`

The source inventory is **8 new definitions, 11 sorried contracts, and 4 skeleton-time-proved lemmas**, not 7 + 11 + 4. All eight definitions were restated from comment-stripped bodies before their declaration docstrings were inspected. The four rider statements received the same treatment.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| A-S1-1 | minor | Audit pack · declaration inventory | The pack counts seven new definitions in total. | `VirtualInput.lean` contains seven `def` declarations: `vhostBuffer`, `vhostBank`, `vhostCfg`, `vhostEmitTM`, `vhostCap`, `vhostSilentTM`, and `vhostSilentCfg`. `Simulation.lean` adds `MultiTapeTM.AgreeOn`, giving eight. Every one was audited. | Record a pack erratum: eight definitions and 23 audited declarations overall. Preserve the shipped pack as required by `workflow.md`. |
| A-S1-2 | minor | `machine-library-design.md` §13, Z1 rider · promised `ofWords` form | The design promises selected-tape projections **and an `ofWords` transport form**; the delivered rider has only the four general projection lemmas. | `Embed.lean:943–973` exports exactly the four projections. They can be specialized to `c := Cfg.ofWords …`; there is no separately named new `ofWords` theorem. Thus the useful field facts are available, but the design's inventory is not synchronized with the delivered surface. | State explicitly that the promised form is supplied by specialization, or add the intended named specialization. If a whole-configuration identity was intended, state it separately with its frame, capture, head, and output parameters. |
| A-S1-3 | note — no findings | `VirtualInput.lean` · all seven definitions and nine contracts | Buffer hosting, both clamps, halting behavior, and output forwarding match the binding inherited behavior. | The head is the **integer** source input position minus one; the buffer receives an outer `none` write, so it is preserved; `virtualMove_correct` supplies the exact movement equation. The final source action is applied even when its successor state is `none`. See the statement checks and adversarial table below. | None required. |
| A-S1-4 | note — no findings | `vhostSilentTM`, `vhostSilentCfg` | The composite has no ambient tape accidentally reset by the default frame. | The embedding has image `{0,…,m}` inside `{0,…,m+1}`. Its complement is exactly `{m+1}`, the capture tape. The selected branch or capture branch handles every tape; the ambient defaults handle none. | None required. |
| A-S1-5 | note — no findings | `Simulation.lean` · `AgreeOn`, `step_eq_of_agreeOn`, `runFrom_eq_of_agreeOn` | The guarded transfer has the correct quantifiers for state-guarded agreement. | Agreement is uniform over reads on the chosen state set, while only live states at times strictly below the horizon must belong to it. A phase may leave the set or halt at the final step. This suffices for the Loop agreement layer and the state guards observed in the supplemental `clSlot_run` source; it is not a replacement for the separate tape/state transport. See customer-strength discussion and provenance limitation below. | None required for the state-agreement contract. A reachable-configuration transfer is a useful further generalization, not required by the observed read-uniform guards. |
| A-S1-6 | note — no findings | `Embed.lean` · four selected-tape rider lemmas | The riders expose only fields of the existing transports. | They identify tape contents and head positions at `ι i`, for arbitrary ambient frame parameters and prefixes. The selected branch takes priority even if `cap` is selected; these field identities therefore need no capture-disjointness hypothesis. Dynamic silent simulation still needs that hypothesis. | None required. The declared skeleton-time proof exception is benign. |
| A-S1-7 | note — no findings | Both space ledgers | Constants, horizons, and the coefficient of source space are correct. | The buffer interval has `y.length + 2` cells. Each bank visited set is equal to the source's at the **same** horizon. The silent wrapper adds only the capture contribution; its existing output-growth bound implies the stated final-word bound. | None required. The current silent bound is sufficient for the named query-decider application. |
| A-S1-8 | note — no findings | New surface · failure mode 5 | No new copied proof families appear in the submitted additions. | The new host is a public transformer using the existing `bufferTape`, `virtualMove`, `virtualNextTag`, and `embedSilentTM`. Its nine contracts are admissions, not copied proofs; the four rider proofs cite the existing selected-slot fact. Z5 adds a predicate and two contracts. The plan explicitly schedules the inherited deduplication for 12.2c. | No new debt acknowledgment required. This does not certify the contents or unchanged status of omitted predecessor files. |
| A-S1-9 | note — evidence limitation | Pack · elaboration, lint, change scope, and customer provenance | Source facts can be checked; all repository execution attestations cannot be independently replayed from this packet. | Independently counted source admissions: 9 in `VirtualInput`, 2 in `Simulation`, 0 in `Embed`; all eleven new admissions have a literal `Proof sketch`. The 1,005-line Simulation size and its justification are present. No build logs, pinned dependency environment, parent diff, Hardness inventory/source, or separate F2 findings file is attached. Limited supplemental customer source was inspected at a different commit, identified below. | Keep these distinctions in the resolutions. Supply pinned customer excerpts and the commit diff/logs if independently replayed provenance or execution verification is required; do not describe this audit as having performed that replay. |

## Blind definition restatements and daylight

The restatements below were recorded before reading the corresponding docstrings. “No daylight” means the body agrees with the declaration prose and the applicable §13 design, including §13a's canonical-layout refinement.

| Definition | Restatement from the body | Comparison |
|---|---|---|
| `MultiTapeTM.AgreeOn M N Q` (`Simulation:970`) | For every control state in `Q`, every input-symbol read, and every tuple of work-symbol reads, the two machines return the same complete action. Initial states and transitions outside `Q` are unrestricted. | No daylight. In particular, this is not merely equality on reads actually seen in one execution. |
| `vhostBuffer m` (`VirtualInput:106`) | Tape index zero of the `1 + m` work tapes. | No daylight. |
| `vhostBank i` (`VirtualInput:110`) | Tape index `1 + i.val`; every source tape gets a distinct nonbuffer slot. | No daylight. |
| `vhostCfg c b p pre` (`VirtualInput:120`) | Map live control `q` to `(q,b)` and preserve `none`; put the native head at `p`; install `bufferTape y` at tape zero with head `(c.inputPos.val : ℤ) - 1`; copy the source bank's contents and heads; set output to `pre ++ c.output`. | No daylight. The definition accepts invalid tags, but every relevant dynamic contract requires `VirtualTag`. A halted transport forgets the tag because its control is `none`. |
| `vhostEmitTM M` (`VirtualInput:138`) | Initial control is `(M.q₀,true)`. Ignore the native input read, read the virtual input from the buffer, and run the source transition on that read and the selected bank reads. Keep native input movement zero; never write the buffer; move its head by the clamped virtual move. Forward the bank operations and optional emission; attach the updated tag to a live successor, preserving a halting successor. | No daylight. All fields of a halting action survive except that there is no live control on which to store the tag. Initializing this machine does not itself load an arbitrary virtual word; the documented setup seam is essential. |
| `vhostCap m` (`VirtualInput:150`) | The last work tape, of value `1 + m`, in the silent host's `(1 + m) + 1` tapes. | No daylight. |
| `vhostSilentTM M` (`VirtualInput:158`) | Apply the existing silent capture embedding to `vhostEmitTM M`, selecting its entire bank by the value-preserving `Fin.castAddEmb 1` and using the added final tape for capture. | No daylight. This is genuinely a composition of existing transformers. |
| `vhostSilentCfg c b p capPre out₀` (`VirtualInput:167`) | Apply the same silent configuration embedding to `vhostCfg c b p []`. Preserve the virtual buffer and source bank, store `bufferTape (capPre ++ c.output)` on the final tape with its head at that word's length, and retain physical output `out₀`. | No daylight. The blank ambient tape and zero ambient head functions are unused, as proved next. |

For the silent layout, for every `j : Fin ((1 + m) + 1)`,

\[
\begin{aligned}
j\in\operatorname{range}(\mathrm{Fin.castAddEmb}\ 1)
&\iff j.val<1+m,\\
j\notin\operatorname{range}(\mathrm{Fin.castAddEmb}\ 1)
&\iff j.val=1+m\\
&\iff j=\mathrm{vhostCap}(m).
\end{aligned}
\]

The first equivalence follows because `castAddEmb` preserves values and its domain is `Fin (1+m)`. The second uses `j.val < (1+m)+1`; the third uses equality of `Fin` values. Thus capture is disjoint from the selected range and there is no third, ambient case. This includes `m = 0`: tape zero is the buffer and tape one is capture.

## The eleven sorried statements, literally

These are mathematical arguments for the statements, not replacement Lean proof scripts. They use the inherited `step` convention: a halted configuration is fixed; a live configuration applies the complete transition action, including writes and optional output, before taking the action's successor state.

1. **`step_eq_of_agreeOn` (`Simulation:981`).** If `c.state = none`, both steps equal `c`. Otherwise write `c.state = some q`; `hq` gives `q ∈ Q`, so `h` equates the two actions at `c.inputSymbol` and `c.workTapeSymbols`, and applying equal actions to the same configuration gives the stated equality.

2. **`runFrom_eq_of_agreeOn` (`Simulation:998`).** Induct on the number of steps up to the requested horizon, with equality at zero because both runs start at `c`. At time `u < t`, substitute the already-equal configurations and apply the preceding step lemma using `hq u`; if that configuration is halted, equality is automatic. No assumption about the control at time `t` is needed, and no equality of the two `q₀` fields is needed.

3. **`vhostEmitTM_step` (`VirtualInput:186`).** In the halted case take the original tag, because source and host configurations are both fixed. In the live case the buffer read is the source input read by `bufferTape_inputSymbol`, and the bank reads are identical by the transport's fields; choose `b' := virtualNextTag b (virtualMove b c.inputSymbol a.inputTape)`, where `a` is the source action. `virtualMove_correct` supplies both the exact buffer-head equation and validity of `b'`; all other configuration fields follow from the action definition and append associativity, including when `a.state = none`.

4. **`vhostEmitTM_runFrom` (`VirtualInput:201`).** At time zero, use witness `b` and the supplied tag hypothesis. For the successor step, apply the step contract to the transported source configuration and its valid arrival tag, then substitute the source and host iteration identities. This works after a halt as well as before it and introduces no nonemptiness or liveness premise.

5. **`vhostEmitTM_visitedByTapeHead_bank` (`VirtualInput:216`).** Apply the run contract separately at every `u ≤ t` and project `workTapePos (vhostBank i)`. The resulting head equals `(M.runFrom c u).workTapePos i`, independently of the existential arrival tag, so the two images of `Finset.range (t+1)` are equal. Thus the statement is equality, not merely containment.

6. **`vhostEmitTM_visitedByTapeHead_buffer` (`VirtualInput:230`).** The corresponding buffer-head projection at each time `u ≤ t` is exactly `((M.runFrom c u).inputPos.val : ℤ) - 1`. Substitution into the defining finite image gives exactly the stated right-hand side, with both time zero and time `t` included.

7. **`vhostCfg_buffer_head_mem` (`VirtualInput:246`).** The run identity gives the head as the integer source input position minus one. Since that position belongs to `Fin (y.length+2)`, its value lies between zero and `y.length+1`, so the transported head lies between `-1` and `y.length`, inclusively.

8. **`vhostEmitTM_spaceUsed_le` (`VirtualInput:262`).** Split the sum of work-tape visited-set cardinalities into tape zero and the bank indexed by `Fin m`. The bank equalities give exactly `M.spaceUsed c t`, while the buffer equality and interval lemma bound its cardinality by `y.length+2`. This yields the printed coefficient one, at the same horizon, without any output-length term.

9. **`vhostEmitTM_emitting_halt` (`VirtualInput:279`).** The hypotheses say that the action applied from the live source configuration has successor `none` and emission `some bit`. The host applies that same emission while mapping the successor to `none`, so its new output is `(pre ++ c.output) ++ [bit]`. Transporting the source step gives `pre ++ (c.output ++ [bit])`; append associativity makes these equal to the displayed contract, so the final bit is neither dropped nor duplicated.

10. **`vhostSilentTM_runFrom` (`VirtualInput:299`).** Apply `embedSilentTM_runFrom` with source `vhostEmitTM M`, the specified embedding, capture tape, and transported starting configuration; the required capture-disjointness follows from the layout arithmetic above. Substitute `vhostEmitTM_runFrom` and its valid arrival tag. The result is precisely `vhostSilentCfg` of the source endpoint, with capture prefix `capPre` and physical output `out₀` unchanged; no third simulation induction is needed.

11. **`vhostSilentTM_spaceUsed_le` (`VirtualInput:315`).** Split the silent host into the selected forwarding host and its sole capture tape. `embedSilentTM_visitedByTapeHead` gives the selected contribution exactly, and `embedSilentTM_spaceUsedByTape_cap` bounds capture by source output growth plus one. That quantity is at most the final capture-word length plus one, so the forwarding bound gives exactly the stated inequality.

The movement equation used in item 3 is literally the inherited one:

\[
(c.inputPos.val:\mathbb Z)-1
+(\mathrm{virtualMove}\ b\ c.inputSymbol\ a.inputTape:\mathbb Z)
=((\mathrm{moveInputPos}\ c.inputPos\ a.inputTape).val:\mathbb Z)-1.
\]

The existing `bufferedSecondCfg_step`/`_run` have the same arbitrary-source-configuration, valid-tag, arbitrary-native-position, existential-arrival-tag, and all-horizon shape. Z1 removes the inactive first block, generalizes to a raw machine, and permits an arbitrary output prefix. It does not weaken their treatment of empty input or halted configurations. Removing the inactive block is the declared canonical-layout choice; R1 supplies relocation/frame extension separately.

## Space calculation and the named consumer

The buffer bound counts **both** blank boundaries:

\[
\#\{-1,0,\ldots,y.length\}=y.length+2.
\]

Consequently,

\[
\begin{aligned}
\mathrm{space}_{\rm emit}(t)
&=M.spaceUsed(c,t)+\#\mathrm{bufferVisits}(t)\\
&\le M.spaceUsed(c,t)+y.length+2.
\end{aligned}
\]

The existing capture theorem is stronger than the newly stated capture allowance. Append-only output gives

\[
\begin{aligned}
\mathrm{space}_{\rm cap}(t)
&\le |(M.runFrom\ c\ t).output|-|c.output|+1\\
&\le |(M.runFrom\ c\ t).output|+1\\
&\le |capPre++(M.runFrom\ c\ t).output|+1.
\end{aligned}
\]

The subtraction is natural-number subtraction, and output monotonicity ensures it is the actual nonnegative growth. Adding the emit bound gives the silent statement. Existing capture-prefix cells need not all be visited during this run; charging their full length is conservative, not an undercount. There are no extra ambient tapes contributing unaccounted initial cells.

For the intended query-decider use in `NP^EXPCOM ⊆ EXP`, take an empty capture prefix and a source run whose complete output is a singleton answer. Every prefix output then has length at most one, so the silent bound is at most

\[
M.spaceUsed(c,t)+y.length+4.
\]

This preserves the source-space coefficient and suffices for that use. Loading/resetting the query buffer and capture tape, and joining repeated query segments, remain consumer obligations; no contract here falsely charges those operations to the lockstep window. This audit verifies the ledger's usable shape, not the separate oracle-class theorem.

## Adversarial instantiations

| Test | Substitution and result |
|---|---|
| Empty virtual input, left boundary | `y=[]`, source position zero, tag `false`, buffer head `-1`. A left request is clamped to zero movement; a right request moves to buffer position zero and sets the tag to `true`. |
| Empty virtual input, right boundary | `y=[]`, source position one, tag necessarily `true`, buffer head zero. A right request is clamped; a left request moves to `-1` and sets the tag to `false`. There is no missing nonempty-word premise. |
| Each boundary under the wrong tag | At the left boundary with tag `true`, a left request escapes to `-2`; at the right boundary with tag `false`, a right request escapes to `y.length+1`. Both are excluded by `hb`. This verifies that the tag hypothesis is necessary rather than redundant. |
| Stationary moves and repeated outward attempts | On a valid boundary tag, clamping produces zero movement, and `virtualNextTag b 0 = b`. Repeated attempts remain clamped. An interior stationary move also preserves either permitted interior tag. |
| Interior tags | For a one-bit word at source position one, both tags satisfy `VirtualTag`. Moving left reaches position zero with tag `false`; moving right reaches position two with tag `true`. Neither interior tag causes spurious clamping because the scanned bit is nonblank. |
| Zero source tapes | `m=0` leaves one emit-host tape, the buffer; the bank equalities have no instances. Silent hosting has exactly buffer and capture, with no hidden ambient tape. Source space is zero. |
| Zero horizon | At `t=0`, choose the original tag. Each existing work tape contributes its initial head singleton; the buffer image also has one element, and capture contributes one visited cell irrespective of the length already stored. Both inequalities hold. |
| Initially halted source | `c.state=none` makes both hosts initially halted. Every subsequent configuration, output, buffer head, bank head, and capture head is fixed. The existential tag can remain the supplied valid tag even though it is not stored in halted control. |
| Emitting halting action | Let `pre=[true,false]`, `c.output=[false]`, and `bit=true`. The host halts with output `[true,false,false,true]`; simultaneous source work writes and head moves are also executed. Every later step fixes this result. |
| Empty native input | `x=[]` gives `p : Fin 2`. Both possible native positions stay fixed because every live host action requests native movement zero, and halted configurations are fixed. Virtual-input behavior is independent of the native read. |
| Nonempty capture prefix and physical output | With `capPre=[false,true]`, `c.output=[false]`, and a new `true` emission, capture becomes `[false,true,false,true]` and its head moves from three to four. The arbitrary physical output `out₀` remains unchanged. |
| Agreement on the empty set | With `Q=∅`, agreement itself is vacuous. For a live start, the visit premise is possible at `t=0` but impossible at any positive horizon because of time zero; for a halted start, every horizon works and both runs are fixed. No false transfer is obtained. |
| Agreement on all states | With `Q=Set.univ`, read-uniform action equality gives equality of runs from any **common configuration**, even when `M.q₀ ≠ N.q₀`. It does not assert equality of their separately initialized configurations. |
| Halting before the horizon | If the common run halts at time `h<t`, the visit condition constrains only its live prefix; all later antecedents asserting a live state are false. The remaining steps are identities for both machines. |
| Disagreement immediately outside the set | Take two states, with `Q` containing only the first. Both machines move from the first to the second silently; at the second one emits `false` and the other emits `true`. Transfer is valid at horizon one, whose final state is outside `Q`; it cannot be applied at horizon two. Strict `< t` is the correct endpoint convention. |
| Read-dependent agreement only on the actual run | Two machines can agree forever on a stationary blank-tape run from one state yet disagree at that same state when the scanned cell is `some true`. This would require a weaker, per-configuration transfer hypothesis; `AgreeOn` deliberately does not cover it. The observed `clSlot_run` guards require agreement for **all** reads, so this is not their obstruction. |

Independent executable checks, using a small mathematical model rather than Lean, passed: 270 valid tag/movement cases for word lengths 0–8; 18 invalid-tag outward counterexamples; 33 tape layouts for `m=0,…,32`; 675 prefix/output/emission append cases; and 9,720 head/output trajectories covering word lengths 0–4, bank sizes 0–2, all period-three movement patterns, initial/early halts, and nonempty prefixes. These finite checks corroborate the arguments; they are not substitutes for the quantified proofs.

## Z5 customer strength

For Loop, choose `Q` to exclude the body-state constructor. The attached inventory says the forwarding table delegates every other state to the capturing table, exactly the all-reads equality required by `AgreeOn`. A non-body segment transfers as soon as its strict-prefix control invariant is supplied. Entry into a body state at the segment's final time is allowed; later execution of that body is not transferred. One-step phase identities use `step_eq_of_agreeOn`; the initial-configuration identity separately uses the two hosts' equal initial-state fields. Thus “collapse fourteen lemmas” includes simple field/projection reductions and shared prefix invariants, not fourteen applications of one endpoint equation without further premises.

The `clSlot_run` signature inspected in supplemental source has

```lean
(good : S → Prop)
(hagree : ∀ q, good q → ∀ inp work,
  host.tr (emb q) inp work =
    clSlotAction select emb (src.tr q inp (fun i => work (index i))))
(hguard : ∀ j < t, ∀ q,
  (src.runFrom c j).state = some q → good q)
```

Its guard is on the control state, and its equality is uniform over `inp` and `work`. The thirteen observed uses have state predicates such as `q ≠ exit`, a component unequal to `none`, exclusion of final constructors, or `True`. They do not introduce a tape-content or head-position guard. Therefore a per-configuration **agreement** hypothesis is unnecessary for those guards.

There is a separate typing issue: `clSlot_run` transports between different tape counts and state types, whereas Z5 equates runs on one carrier. Z5 must be applied **after** tape relocation and state transport produce the reference machine on the host carrier; the compared machines then use the same starting host configuration. It does not, by itself, replace the entire generic `clSlot_run` theorem or establish that transport. For the concrete injective constructor/pair state embeddings, one can extend the renamed source table to the host state type, use the existing unguarded state/block transport and R1 relocation to identify its run, then use Z5 on the image of the good source states. This is the appropriate composition of responsibilities; claiming that `runFrom_eq_of_agreeOn` directly accepts arbitrary `src`, `host`, and `emb` would be incorrect.

The fully generic `clSlot_run` also permits a noninjective `emb`; its complete heterogeneous statement is not a literal specialization of the new API. If preserving that entire private helper's generality becomes a retrofit requirement, a public guarded configuration-transport theorem would be the appropriate additional export. I do not interpret the current design's explicitly same-carrier Z5 contract as promising that stronger transport theorem.

**Evidence boundary:** the packet contains the Loop inventory but not Loop or Hardness source at `28a49d69`, nor the other two retrofit inventories. For the limited customer check, I inspected read-only source snapshots at commit `5588628cbbddea9546f616907364b608e15557fd`, without consulting development history or prior audit findings. The observed Loop constructor and fourteen-family descriptions match the attached inventory; the Hardness snapshot has thirteen `clSlot_run` call sites. This corroborates the customer shape but does not independently establish that those omitted files are unchanged at the audited commit.

Supplemental file SHA-256 values:

- `Build/Loop.lean`: `51842d285e66ff5da13b434f4652b333f43690086416f681165f4ff2267acb78`.
- `CookLevin/Hardness.lean`: `b1332ebc638a2ecd1c438d3f1a1e34a3669e0ae7afad32493d9949cdf2ffc6bb`.

## Rider restatements and declared anomalies

| Rider | Blind restatement |
|---|---|
| `embedSilentCfg_selected_tape` | At host tape `ι i`, the silent transport's entire tape function equals `c.workTapes i`. |
| `embedSilentCfg_selected_pos` | At host tape `ι i`, the silent transport's head equals `c.workTapePos i`. |
| `embedEmitCfg_selected_tape` | At host tape `ι i`, the forwarding transport's entire tape function equals `c.workTapes i`. |
| `embedEmitCfg_selected_pos` | At host tape `ι i`, the forwarding transport's head equals `c.workTapePos i`. |

All parameters in these statements are arbitrary as printed. They expose exactly the selected fields requested by D-R1; they make no claim about a run, time, space, capture disjointness, or canonical input configuration. They are thin public consequences of the existing private selection equation, not new machine-construction proofs. The skeleton-time exception is therefore benign.

The silent definition-by-composition is fully determined, with the required tape disjointness discharged arithmetically. The Simulation size deviation is real—1,005 lines—and its decision-13.5/D7 justification is explicitly recorded in the plan. No new contract consumes a machine's `q₀`: they all concern supplied configurations and `runFrom`; the `true` initial tag is valid at source position one even when the virtual word is empty. There is no hidden initial-configuration correctness assertion.

The new file cites the existing virtual-movement and buffering primitives rather than declaring replacements for them. The public `bufferedCompTM` remains a distinct sequential-composition customer, so retaining it is not new duplication. The plan's 12.2c decision explicitly schedules the inherited private-copy cleanup after the retrofit batches. The attachment set is insufficient to independently count every inherited copy or verify that every omitted predecessor was untouched; no such stronger provenance claim is made here.

## Recommended machine-checkable sanity exports

These are additions to weigh, not blockers for the present statements.

1. **Initial-tag validity and independence from `q₀`.** Export `VirtualTag (1 : Fin (y.length+2)) true`. Separately, prove that replacing a machine's `q₀` while keeping its transition table fixed does not change `runFrom c t`; instantiate this for the host. This is an `initCfg`-free way to express precisely what the current contracts do and do not consume.
2. **Transport injectivity for fixed parameters.** For fixed `b`, `p`, and `pre`, `fun c => vhostCfg c b p pre` is injective: project the bank, cancel the fixed output prefix, recover input position from the buffer head, and recover the optional source state by its first component. Do **not** assert joint injectivity in `(c,b)`: distinct tags give the same transported configuration when `c.state=none`.
3. **Native-head constancy.** For every host configuration `d`, not just a valid transported one, prove `((vhostEmitTM M).runFrom d t).inputPos = d.inputPos`; the transition always requests movement zero. Its finite trajectory image is the singleton `{d.inputPos}`. `visitedByTapeHead` indexes work tapes only, so a native-input version should use this input-position image rather than an invented work-tape index.
4. **Boundary and seam specializations.** Give named empty-word left/right clamp corollaries, and a silent emitting-halt projection showing the capture append and unchanged `out₀`. The general contracts already imply them; named forms would make the inherited regressions easy to preserve during 12.2c.

## Verification scope

Independently checked: attachment count and bundle hash; blind declaration inventory; all eleven literal contract shapes and sketches; four rider statements; layout arithmetic; boundary/halt/prefix cases; exact visited-set and space calculations; observed customer guard quantifiers; and the absence of newly copied proof families in the supplied additions.

Not independently replayed: Lean elaboration, axiom printing, fresh-olean creation, repository style scripts, the parent-to-`28a49d69` diff, or customer source identity at that commit. Source admission counts are not reported as independently reproduced compiler-warning counts. The separate F2 findings are absent, so the binding forwarding clauses were checked against the quoted A2 report, the pack, the design, and the supplied proved buffered-host template.

## Notation glossary

`M`, `N` are machines; `c`, `d` are configurations; `q` is a live control state; `Q` is the agreement set; `t`, `u`, `h` are nonnegative times. `m` is the source work-tape count; `i`, `j` are tape indices where used as such. `x`, `y` are native and virtual input words; `b`, `b'` are boundary tags; `p` is the native input-head position; `a` is the source action. `pre`, `capPre`, `out₀`, and `bit` retain their Lean meanings: physical-output prefix, capture prefix, fixed physical output, and emitted bit. `S`, `H` are source and host state types; `src`, `host`, `good`, `emb`, `index`, and `select` retain the names and roles in the displayed `clSlot_run` signature. `++` is list concatenation, `|w|` is list length, and `#A` is finite-set cardinality. `space_emit`, `space_cap`, and `bufferVisits` abbreviate the emitting host's work space, the silent host's capture-tape space, and the buffer's visited set, respectively, always from the transported starting configuration at the displayed horizon. All other code identifiers have their source meanings.
```

## ===== audits/vhost-infra-resolutions.md =====

```
# Resolutions — zone/virtual-input layer (§13), statement gate, tranche A-S1

Loop summary for the A-S1 external audit (`audits/vhost-infra-pack.md`,
bundle sha256 `b76a53aa…`, audited at `28a49d69`). Findings preserved
verbatim in `audits/vhost-infra-findings.md`.

## Outcome

**Round 1: PASS — 0 blockers, 0 majors, 2 minors (and six explicit
no-findings rows, including the failure-mode-5 debt screen: new copies —
none). The A-S1 statement gate is CLOSED.** The eleven sorried contracts
are confirmed true as literally stated, with the auditor supplying a
complete per-statement mathematical argument (adopted into the fill brief
as the binding routes), blind restatements of all eight definitions and
four rider lemmas with no daylight, the silent-composition layout
arithmetic verified (the unselected set is exactly the capture tape, the
ambient parameters inert, `m = 0` included), sixteen adversarial
instantiation families, and ~10,700 finite model checks corroborating the
clamp/trajectory behavior.

## Disposition of the findings

| # | Severity | Disposition |
|---|---|---|
| A-S1-1 | minor | **Pack erratum acknowledged** (shipped packs stay verbatim): the pack counted seven new definitions; the correct inventory is **eight** (`MultiTapeTM.AgreeOn` included), 23 audited declarations in all. Every one was audited. |
| A-S1-2 | minor | **Swept in the design doc** (`machine-library-design.md` §13b): the rider's promised `ofWords` transport form is supplied by specialization of the four projections; a named whole-configuration identity is commissioned on need at the 12.2c window. |
| A-S1-3 — A-S1-8 | notes | No-findings rows (definitions and contracts faithful; silent composition fully determined; Z5 quantifiers correct; riders thin and benign; space ledgers' constants and coefficient-one shape confirmed sufficient for the `NP^EXPCOM ⊆ EXP` query use; no new debt). No action. |
| A-S1-9 | note | Evidence-boundary note carried verbatim: the audit verified source facts, not repository execution; elaboration/lint/axiom evidence remains the maintainer's. The auditor's supplemental customer check used read-only snapshots at `5588628c` (file hashes recorded in the findings). |

## Adopted and carried

* **The eleven per-statement arguments are the binding fill routes**,
  embedded verbatim in the A-S1 fill brief (`briefs/vhost-f1.md`).
* **The four recommended sanity exports are adopted as optional permanent
  lemmas** of the fill batch: initial-tag validity + `q₀`-independence of
  `runFrom`; fixed-parameter injectivity of `vhostCfg` (joint `(c, b)`
  injectivity explicitly NOT asserted — halted transports forget the tag);
  native-head constancy for arbitrary host configurations (as an
  input-position image, not a work-tape index); named empty-word clamp and
  silent emitting-halt specializations.
* **Z5 composition-of-responsibilities** (binding on retrofit consumers):
  Z5 equates runs on one carrier; heterogeneous `clSlot_run`-style sites
  transport first (R1 + state renaming), then agree. A public guarded
  configuration-transport theorem is a possible later export, not a
  promise of this layer.
* The `q₀ := (M.q₀, true)` docstring claim is consumed by no contract
  (auditor-verified); the optional sanity export makes this checkable.

## Gate state

| Item | State |
|---|---|
| §13 tranche A-S1 (Z5 + Z1 + rider) statement gate | **CLOSED (round 1)** |
| A-S1 fill epoch | brief issued (`briefs/vhost-f1.md`), 11 targets |
| §13 tranche A-S2 (Z2 + Z3 + Z4) | to draft |
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

## ===== audits/evidence/vhost-f1.patch =====

```
From 50f846477261689db83c4f4e629c9dad93a7ca96 Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Fri, 9 Oct 2026 17:21:49 -0300
Subject: [PATCH] Prove virtual-input hosting and guarded agreement transfer

---
 .../TuringMachine/Build/VirtualInput.lean     | 201 +++++++++++++++++-
 .../Complexity/TuringMachine/Simulation.lean  |  13 +-
 2 files changed, 203 insertions(+), 11 deletions(-)

diff --git a/TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean b/TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean
index e1eddb26..31a6e7c4 100644
--- a/TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean
@@ -189,7 +189,47 @@ theorem vhostEmitTM_step (M : MultiTapeTM m Bool S) (c : Cfg m Bool S y)
     ∃ b', FinTM.VirtualTag (M.step c).inputPos b' ∧
       (vhostEmitTM M).step (vhostCfg c b p pre) =
         vhostCfg (M.step c) b' p pre := by
-  sorry
+  cases hq : c.state with
+  | none =>
+    refine ⟨b, ?_, ?_⟩
+    · simpa only [MultiTapeTM.step_of_halt hq] using hb
+    · rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt]
+      simp [vhostCfg, hq]
+  | some q =>
+    have hs : (vhostCfg c b p pre).state = some (q, b) := by
+      simp [vhostCfg, hq]
+    have hv : (vhostCfg c b p pre).workTapeSymbols (vhostBuffer m) =
+        c.inputSymbol := by
+      change FinTM.bufferTape y ((c.inputPos.val : ℤ) - 1) = c.inputSymbol
+      exact FinTM.bufferTape_inputSymbol (c.mapState (fun _ => ()))
+    have hr : (fun i => (vhostCfg c b p pre).workTapeSymbols (vhostBank i)) =
+        c.workTapeSymbols := by
+      funext i
+      simp [vhostCfg, vhostBank, Cfg.workTapeSymbols]
+    let a := M.tr q c.inputSymbol c.workTapeSymbols
+    let mv := FinTM.virtualMove b c.inputSymbol a.inputTape
+    -- The input-only facts specialize through Unit, preserving arbitrary state universes.
+    have hm := FinTM.virtualMove_correct (c.mapState (fun _ => ())) b hb a.inputTape
+    have hc : M.step c = a.apply c := by
+      simp only [MultiTapeTM.step, hq, a]
+    refine ⟨FinTM.virtualNextTag b mv, ?_, ?_⟩
+    · simpa only [hc, Action.apply] using hm.2
+    · unfold MultiTapeTM.step
+      rw [hs]
+      dsimp only [vhostEmitTM]
+      rw [hv, hr, hq]
+      change (Action.apply _ _) = vhostCfg (a.apply c) _ p pre
+      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
+      · funext i
+        refine Fin.addCases ?_ ?_ i <;> intro j <;>
+          simp [vhostCfg, Action.apply, a]
+      · funext i
+        refine Fin.addCases ?_ ?_ i
+        · intro j
+          simpa only [vhostCfg, Action.apply, Fin.addCases_left] using hm.1
+        · intro j
+          simp [vhostCfg, Action.apply, a]
+      · simp only [Action.apply, vhostCfg, List.append_assoc, a]
 
 /-- The forwarding lockstep at every time: one host step per source step,
 with a valid arrival tag at the endpoint. Completed outputs are preserved
@@ -204,7 +244,14 @@ theorem vhostEmitTM_runFrom (M : MultiTapeTM m Bool S) (c : Cfg m Bool S y)
     ∃ b', FinTM.VirtualTag (M.runFrom c t).inputPos b' ∧
       (vhostEmitTM M).runFrom (vhostCfg c b p pre) t =
         vhostCfg (M.runFrom c t) b' p pre := by
-  sorry
+  induction t with
+  | zero => exact ⟨b, hb, rfl⟩
+  | succ t ih =>
+    obtain ⟨b', hb', he⟩ := ih
+    obtain ⟨b'', hb'', he'⟩ := vhostEmitTM_step M _ b' hb' p pre
+    refine ⟨b'', ?_, ?_⟩
+    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hb''
+    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']
 
 /-- Bank tape `i` of the forwarding host visits exactly the cells the
 source's tape `i` visits, at every horizon.
@@ -218,7 +265,12 @@ theorem vhostEmitTM_visitedByTapeHead_bank (M : MultiTapeTM m Bool S)
     (p : Fin (x.length + 2)) (pre : List Bool) (t : ℕ) (i : Fin m) :
     (vhostEmitTM M).visitedByTapeHead (vhostCfg c b p pre) t (vhostBank i) =
       M.visitedByTapeHead c t i := by
-  sorry
+  unfold MultiTapeTM.visitedByTapeHead
+  congr 1
+  funext u
+  obtain ⟨b', _, he⟩ := vhostEmitTM_runFrom M c b hb p pre u
+  rw [he]
+  simp [vhostCfg, vhostBank]
 
 /-- The buffer head's trajectory is exactly the source's input trajectory
 shifted by one: at every horizon, the buffer tape's visited set is the
@@ -233,7 +285,12 @@ theorem vhostEmitTM_visitedByTapeHead_buffer (M : MultiTapeTM m Bool S)
     (vhostEmitTM M).visitedByTapeHead (vhostCfg c b p pre) t (vhostBuffer m) =
       (Finset.range (t + 1)).image
         (fun u => ((M.runFrom c u).inputPos.val : ℤ) - 1) := by
-  sorry
+  unfold MultiTapeTM.visitedByTapeHead
+  congr 1
+  funext u
+  obtain ⟨b', _, he⟩ := vhostEmitTM_runFrom M c b hb p pre u
+  rw [he]
+  simp [vhostCfg, vhostBuffer]
 
 /-- The buffer head stays inside `[-1, y.length]` at every time — the
 permanent form of the two boundary clamps, the empty buffered word
@@ -248,7 +305,11 @@ theorem vhostCfg_buffer_head_mem (M : MultiTapeTM m Bool S)
     (p : Fin (x.length + 2)) (pre : List Bool) (t : ℕ) :
     ((vhostEmitTM M).runFrom (vhostCfg c b p pre) t).workTapePos
         (vhostBuffer m) ∈ Finset.Icc (-1 : ℤ) (y.length : ℤ) := by
-  sorry
+  obtain ⟨b', _, he⟩ := vhostEmitTM_runFrom M c b hb p pre t
+  rw [he]
+  simp only [vhostCfg, vhostBuffer, Fin.addCases_left, Finset.mem_Icc]
+  have hp := (M.runFrom c t).inputPos.isLt
+  constructor <;> omega
 
 /-- The coefficient-one space ledger of the forwarding host: host space is
 at most source space plus the buffer interval. No term depends on the
@@ -264,7 +325,47 @@ theorem vhostEmitTM_spaceUsed_le (M : MultiTapeTM m Bool S)
     (p : Fin (x.length + 2)) (pre : List Bool) (t : ℕ) :
     (vhostEmitTM M).spaceUsed (vhostCfg c b p pre) t ≤
       M.spaceUsed c t + (y.length + 2) := by
-  sorry
+  have hbuffer : (vhostEmitTM M).spaceUsedByTape (vhostCfg c b p pre) t
+      (vhostBuffer m) ≤ y.length + 2 := by
+    calc
+      _ ≤ (Finset.Icc (-1 : ℤ) (y.length : ℤ)).card := by
+        apply Finset.card_le_card
+        intro z hz
+        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
+        exact vhostCfg_buffer_head_mem M c b hb p pre u
+      _ = y.length + 2 := by
+        rw [Int.card_Icc]
+        omega
+  have hbank (i : Fin m) :
+      (vhostEmitTM M).spaceUsedByTape (vhostCfg c b p pre) t (vhostBank i) =
+        M.spaceUsedByTape c t i :=
+    congrArg Finset.card (vhostEmitTM_visitedByTapeHead_bank M c b hb p pre t i)
+  have hsum : M.spaceUsed c t =
+      ∑ j ∈ Finset.univ.erase (vhostBuffer m),
+        (vhostEmitTM M).spaceUsedByTape (vhostCfg c b p pre) t j := by
+    apply Finset.sum_bij (fun i _ => vhostBank i)
+    · intro i _
+      simp [vhostBank, vhostBuffer, Fin.ext_iff]
+    · intro i _ j _ hij
+      apply Fin.ext
+      have hval := congrArg Fin.val hij
+      simpa [vhostBank] using hval
+    · intro j
+      refine Fin.addCases ?_ ?_ j
+      · intro i hi
+        have hi0 : i = 0 := Subsingleton.elim _ _
+        subst i
+        simp [vhostBuffer] at hi
+      · intro i _
+        exact ⟨i, Finset.mem_univ i, rfl⟩
+    · intro i _
+      exact (hbank i).symm
+  calc
+    _ = M.spaceUsed c t +
+        (vhostEmitTM M).spaceUsedByTape (vhostCfg c b p pre) t (vhostBuffer m) := by
+      rw [hsum]
+      exact (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
+    _ ≤ M.spaceUsed c t + (y.length + 2) := by omega
 
 /-- A source halting step that emits is forwarded before the host control
 dies: the emitted bit lands on the host output and the host halts in the
@@ -285,7 +386,39 @@ theorem vhostEmitTM_emitting_halt (M : MultiTapeTM m Bool S)
     ((vhostEmitTM M).step (vhostCfg c b p pre)).state = none ∧
       ((vhostEmitTM M).step (vhostCfg c b p pre)).output =
         pre ++ c.output ++ [bit] := by
-  sorry
+  obtain ⟨b', _, he⟩ := vhostEmitTM_step M c b hb p pre
+  rw [he]
+  simp [vhostCfg, MultiTapeTM.step, hq, ha, ho, List.append_assoc]
+
+/-- The silent selection consists of all indices below the final capture
+tape, and its complement is exactly that tape, including when `m = 0`.
+
+**Proof sketch.** The embedding preserves index values, and every value
+below `1 + m` has a preimage. An unselected index is at least `1 + m` and
+strictly below `(1 + m) + 1`, so it is the capture index. -/
+private theorem vhostSilent_layout (j : Fin ((1 + m) + 1)) :
+    (j ∈ Set.range (Fin.castAddEmb 1 : Fin (1 + m) ↪ Fin ((1 + m) + 1)) ↔
+      j.val < 1 + m) ∧
+    (j ∉ Set.range (Fin.castAddEmb 1 : Fin (1 + m) ↪ Fin ((1 + m) + 1)) ↔
+      j = vhostCap m) := by
+  have hselected :
+      j ∈ Set.range (Fin.castAddEmb 1 : Fin (1 + m) ↪ Fin ((1 + m) + 1)) ↔
+        j.val < 1 + m := by
+    constructor
+    · rintro ⟨i, rfl⟩
+      exact i.isLt
+    · intro hj
+      exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
+  refine ⟨hselected, ?_⟩
+  rw [hselected]
+  constructor
+  · intro hj
+    apply Fin.ext
+    have hlt := j.isLt
+    change j.val = 1 + m + 0
+    omega
+  · rintro rfl
+    simp [vhostCap]
 
 /-- The suppressing lockstep at every time: capture records the source's
 emissions after the prior capture prefix, the physical output stays
@@ -302,7 +435,11 @@ theorem vhostSilentTM_runFrom (M : MultiTapeTM m Bool S) (c : Cfg m Bool S y)
     ∃ b', FinTM.VirtualTag (M.runFrom c t).inputPos b' ∧
       (vhostSilentTM M).runFrom (vhostSilentCfg c b p capPre out₀) t =
         vhostSilentCfg (M.runFrom c t) b' p capPre out₀ := by
-  sorry
+  have hcap := (vhostSilent_layout (vhostCap m)).2.mpr rfl
+  obtain ⟨b', hb', he⟩ := vhostEmitTM_runFrom M c b hb p [] t
+  refine ⟨b', hb', ?_⟩
+  unfold vhostSilentTM vhostSilentCfg
+  rw [embedSilentTM_runFrom _ _ hcap, he]
 
 /-- The suppressing flavor's space ledger: source space, the buffer
 interval, and the capture word — coefficient one on the source term.
@@ -318,6 +455,52 @@ theorem vhostSilentTM_spaceUsed_le (M : MultiTapeTM m Bool S)
     (vhostSilentTM M).spaceUsed (vhostSilentCfg c b p capPre out₀) t ≤
       M.spaceUsed c t + (y.length + 2) +
         ((capPre ++ (M.runFrom c t).output).length + 1) := by
-  sorry
+  have hcap := (vhostSilent_layout (vhostCap m)).2.mpr rfl
+  have hselected (i : Fin (1 + m)) :
+      (vhostSilentTM M).spaceUsedByTape (vhostSilentCfg c b p capPre out₀) t
+          (Fin.castAddEmb 1 i) =
+        (vhostEmitTM M).spaceUsedByTape (vhostCfg c b p []) t i :=
+    (embedSilentTM_visitedByTapeHead (Fin.castAddEmb 1) (vhostCap m) hcap
+      (vhostEmitTM M) (fun _ _ => none) (fun _ => 0) capPre out₀
+      (vhostCfg c b p []) t i).2
+  have hcapture :
+      (vhostSilentTM M).spaceUsedByTape (vhostSilentCfg c b p capPre out₀) t
+          (vhostCap m) ≤ (capPre ++ (M.runFrom c t).output).length + 1 := by
+    have hgrowth := embedSilentTM_spaceUsedByTape_cap (Fin.castAddEmb 1)
+      (vhostCap m) hcap (vhostEmitTM M) (fun _ _ => none) (fun _ => 0)
+      capPre out₀ (vhostCfg c b p []) t
+    obtain ⟨b', _, he⟩ := vhostEmitTM_runFrom M c b hb p [] t
+    rw [he] at hgrowth
+    change (vhostSilentTM M).spaceUsedByTape (vhostSilentCfg c b p capPre out₀) t
+        (vhostCap m) ≤ (M.runFrom c t).output.length - c.output.length + 1 at hgrowth
+    simp only [List.length_append]
+    omega
+  have hsum : (vhostEmitTM M).spaceUsed (vhostCfg c b p []) t =
+      ∑ j ∈ Finset.univ.erase (vhostCap m),
+        (vhostSilentTM M).spaceUsedByTape (vhostSilentCfg c b p capPre out₀) t j := by
+    apply Finset.sum_bij (fun i _ => Fin.castAddEmb 1 i)
+    · intro i _
+      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
+      intro hi
+      exact hcap ⟨i, hi⟩
+    · intro i _ j _ hij
+      exact (Fin.castAddEmb 1).injective hij
+    · intro j hj
+      have hne := (Finset.mem_erase.mp hj).1
+      have hin : j ∈ Set.range (Fin.castAddEmb 1 : Fin (1 + m) ↪
+          Fin ((1 + m) + 1)) := by
+        by_contra hout
+        exact hne ((vhostSilent_layout j).2.mp hout)
+      obtain ⟨i, rfl⟩ := hin
+      exact ⟨i, Finset.mem_univ _, rfl⟩
+    · intro i _
+      exact (hselected i).symm
+  calc
+    _ = (vhostEmitTM M).spaceUsed (vhostCfg c b p []) t +
+        (vhostSilentTM M).spaceUsedByTape (vhostSilentCfg c b p capPre out₀) t
+          (vhostCap m) := by
+      rw [hsum]
+      exact (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
+    _ ≤ _ := Nat.add_le_add (vhostEmitTM_spaceUsed_le M c b hb p [] t) hcapture
 
 end Turing
diff --git a/TCSlib/Complexity/TuringMachine/Simulation.lean b/TCSlib/Complexity/TuringMachine/Simulation.lean
index 0d0233c9..873340ca 100644
--- a/TCSlib/Complexity/TuringMachine/Simulation.lean
+++ b/TCSlib/Complexity/TuringMachine/Simulation.lean
@@ -983,7 +983,11 @@ theorem step_eq_of_agreeOn {k : ℕ} {Symbol State : Type*}
     (h : M.AgreeOn N Q) {input : List Symbol} (c : Cfg k Symbol State input)
     (hq : ∀ q, c.state = some q → q ∈ Q) :
     N.step c = M.step c := by
-  sorry
+  cases hs : c.state with
+  | none => simp only [step_of_halt hs]
+  | some q =>
+    simp only [step, hs]
+    rw [h q (hq q hs)]
 
 /-- A whole run transfers across an agreement: if every control state the
 `M`-run visits strictly before time `t` lies in the agreement set, the two
@@ -1000,6 +1004,11 @@ theorem runFrom_eq_of_agreeOn {k : ℕ} {Symbol State : Type*}
     (h : M.AgreeOn N Q) {input : List Symbol} (c : Cfg k Symbol State input)
     (t : ℕ) (hq : ∀ u < t, ∀ q, (M.runFrom c u).state = some q → q ∈ Q) :
     N.runFrom c t = M.runFrom c t := by
-  sorry
+  induction t with
+  | zero => rfl
+  | succ t ih =>
+    rw [runFrom_succ_eq_step', ih (fun u hu => hq u (by omega)),
+      runFrom_succ_eq_step']
+    exact step_eq_of_agreeOn h _ (hq t (by omega))
 
 end Turing.MultiTapeTM
-- 
2.51.1

```

## ===== TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Build.Embed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: virtual-input hosting (Z1)

The virtual-input layer of the machine-construction library
(`machine-library-design.md` §13, Z1): a verified machine whose *input* is
a designated **buffered word** on a work tape runs inside a host, one host
step per source step, with the buffer read-only, the source's work bank
intact, and the source's input movement realized as the clamped buffer
movement of `Turing.FinTM.virtualMove` under the `VirtualTag` boundary
discipline. This is the pattern the proved corpus has hand-rebuilt five
times — `Turing.FinTM.bufferedCompTM`'s second phase
(`bufferedSecondCfg_step`/`_run`, the public template for the contracts
below), the A2 forwarding controller's `a2_mapVirtual` lockstep and the
F2A `f2_splitCount*` virtual-empty-input hosting (both private in
`Build/Catalog.lean`), the universal interpreter's input discipline, and
the oblivious candidate's `obliviousVisit` transduction — promoted to one
transformer pair.

## Design (decisions 13.4 and 13a, recorded in the design document)

* **Canonical layout, relocation by composition.** The transformer is
  defined on exactly `1 + m` work tapes — the buffer first, the payload
  bank after it. A consumer needing the buffer or bank elsewhere composes
  with the R1 embeddings of `Build/Embed.lean`; relocation is never baked
  in.
* **A silent/emit pair over one core** (the 12.4 shape). The forwarding
  flavor `vhostEmitTM` passes source emissions to the host's physical
  output. The suppressing flavor `vhostSilentTM` is *defined as the layer
  composing with itself*: the R1 capture wrapper `embedSilentTM` applied
  to `vhostEmitTM` at the identity-shaped selection, with one extra
  capture tape appended — so its contracts are instances of the two
  layers' contracts, never a third lockstep.
* **The boundary tag lives in the control state** (`S × Bool`, the
  `a2_MapState.run q tag` precedent): a stationary move preserves the
  tag, so repeated outward attempts at a blank boundary stay clamped,
  with **no nonempty-input premise anywhere** — on an empty buffered word
  the two boundaries are adjacent and the clamps still hold.
* **Setup is the consumer's.** The transformer owns the hosting from a
  loaded buffer onward; parsing, loading, and rewinding the buffer, and
  choosing the seam, belong to the consumer (the A2 controller's parse
  stages are the precedent), seamed with R2.

## Status: proved (A-S1 gate closed round 1; fill epoch vhost-f1)

Every contract below is kernel-checked. The statement gate closed at
`audits/vhost-infra-resolutions.md`; the fill (one batch, 11 targets,
report `audits/vhost-agent-reports/f1-REPORT.md`) followed the gate
audit's per-statement routes, adapting the proved
`Turing.FinTM.bufferedSecondCfg` template. The original proof sketches
are retained on the contracts as the audit record.

## Main definitions and results

* `Turing.vhostCfg` — the configuration transport: a source configuration
  on virtual input `y`, a boundary tag, a frozen native input position,
  and a prior output prefix, viewed inside the `1 + m`-tape host.
* `Turing.vhostEmitTM` — the forwarding transformer.
* `Turing.vhostSilentTM` — the suppressing/capturing transformer, as the
  R1 capture of the forwarding flavor.
* `Turing.vhostEmitTM_runFrom` — the lockstep: one host step per source
  step, at every time, with a valid arrival tag; halted sources are
  absorbed; no halting, liveness, or nonempty-input hypotheses.
* `Turing.vhostEmitTM_visitedByTapeHead_bank` /
  `Turing.vhostEmitTM_visitedByTapeHead_buffer` — the bank tapes visit
  exactly the source's cells; the buffer head's trajectory is exactly the
  source's input trajectory shifted by one.
* `Turing.vhostEmitTM_spaceUsed_le` — the coefficient-one space ledger:
  host space is at most source space plus the buffer interval
  `y.length + 2`.
* `Turing.vhostSilentTM_runFrom` / `Turing.vhostSilentTM_spaceUsed_le` —
  the suppressing flavor's instances.
* Permanent regression lemmas (adopted from the F2 epoch audit):
  `Turing.vhostCfg_buffer_head_mem` (the clamp interval, empty word
  included) and `Turing.vhostEmitTM_emitting_halt` (a source halting
  emission is forwarded before the host control dies).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern
  Approach*, Cambridge University Press, 2009. (§1.2; running a machine
  on a stored word is the folklore of every simulation argument there.)
* In-repo precedents harvested (design §13, Evidence):
  `Turing.FinTM.bufferedCompTM` phase two (`Simulation.lean`, proved);
  `a2_mapVirtual`/`a2_mapVirtual_step`/`a2_mapVirtual_run` and
  `f2_splitCountAction`/`f2_splitCount_run` (`Build/Catalog.lean`,
  proved, private); the audited A2/F2 contracts bind the clamp and
  halt-absorption clauses below.
-/

namespace Turing

variable {m : ℕ} {S : Type*} {x y : List Bool}

/-- The buffer tape of the canonical virtual-input host: the first of its
`1 + m` work tapes. -/
def vhostBuffer (m : ℕ) : Fin (1 + m) := Fin.castAdd m (0 : Fin 1)

/-- The payload-bank tape of the canonical virtual-input host carrying the
source's work tape `i`. -/
def vhostBank (i : Fin m) : Fin (1 + m) := Fin.natAdd 1 i

/-- A source configuration on virtual input `y`, viewed inside the
`1 + m`-tape host over native input `x`: the control carries the source
state and the boundary tag; the native input head sits frozen at `p`; the
buffer holds `y` with its head at the source's input position minus one
(the `Turing.FinTM.bufferTape_inputSymbol` convention); the bank holds the
source's work tapes and heads verbatim; and the host output is the prior
prefix `pre` followed by everything the source has emitted. A halted
source maps to a halted host. -/
def vhostCfg (c : Cfg m Bool S y) (b : Bool) (p : Fin (x.length + 2))
    (pre : List Bool) : Cfg (1 + m) Bool (S × Bool) x where
  state := c.state.map (fun q => (q, b))
  inputPos := p
  workTapes := Fin.addCases (fun _ => FinTM.bufferTape y) c.workTapes
  workTapePos := Fin.addCases (fun _ => (c.inputPos.val : ℤ) - 1) c.workTapePos
  output := pre ++ c.output

/-- **Z1, the forwarding virtual-input transformer** (design §13, decision
13.4). Host the `m`-tape machine `M` on `1 + m` tapes with its input read
from the buffer: each step reads the buffer cell as the source's input
symbol, performs the source's work actions on the bank, realizes the
source's input movement as the clamped buffer movement, forwards the
source's emission physically, never moves the native input head, and
carries the arrival tag in control. The initial tag is `true` (valid at
the canonical start position `1` for every `y`, the empty word included).
Setup — loading `y` onto the buffer and arriving at a `vhostCfg` seam — is
the consumer's, by R2 composition. -/
def vhostEmitTM (M : MultiTapeTM m Bool S) :
    MultiTapeTM (1 + m) Bool (S × Bool) where
  q₀ := (M.q₀, true)
  tr := fun qb _inp w =>
    let v := w (vhostBuffer m)
    let a := M.tr qb.1 v (fun i => w (vhostBank i))
    let mv := FinTM.virtualMove qb.2 v a.inputTape
    ⟨0, Fin.addCases (fun _ => ((none : Option (Option Bool)), mv)) a.workTapes,
      a.output, a.state.map (fun q => (q, FinTM.virtualNextTag qb.2 mv))⟩

/-- The capture tape of the suppressing flavor: the extra last tape of its
`(1 + m) + 1` work tapes. -/
def vhostCap (m : ℕ) : Fin ((1 + m) + 1) := Fin.natAdd (1 + m) (0 : Fin 1)

/-- **Z1, the suppressing virtual-input transformer**: the layer composing
with itself. The R1 capture wrapper runs the forwarding host on the first
`1 + m` tapes of a `(1 + m) + 1`-tape machine, records every emission on
the appended capture tape, and emits nothing physically. Its contracts are
instances of `Turing.embedSilentTM`'s over `Turing.vhostEmitTM`'s — no
third lockstep exists. -/
def vhostSilentTM (M : MultiTapeTM m Bool S) :
    MultiTapeTM ((1 + m) + 1) Bool (S × Bool) :=
  embedSilentTM (Fin.castAddEmb 1) (vhostCap m) (vhostEmitTM M)

/-- The suppressing flavor's configuration transport: the forwarding
transport (with empty inner prefix) viewed through the R1 silent transport
— capture word `capPre` followed by the source's emissions, ambient frame
nowhere (the single unselected tape is the capture tape), physical output
the untouched `out₀`. -/
def vhostSilentCfg (c : Cfg m Bool S y) (b : Bool) (p : Fin (x.length + 2))
    (capPre out₀ : List Bool) : Cfg ((1 + m) + 1) Bool (S × Bool) x :=
  embedSilentCfg (Fin.castAddEmb 1) (vhostCap m) (fun _ _ => none) (fun _ => 0)
    capPre out₀ (vhostCfg c b p [])

/-- One forwarding host step simulates one source step, producing a valid
arrival tag; the statement includes the absorbing halted case and the
empty buffered word, with no liveness or nonemptiness premises.

**Proof sketch.** The template is the proved
`Turing.FinTM.bufferedSecondCfg_step`, with the first block removed and
the output prefix carried along. A halted source is fixed on both sides.
On a live state, buffer reads at the source input position minus one equal
source input reads (`bufferTape_inputSymbol`); `virtualMove_correct`
supplies the buffer-head equation and the new tag; the bank performs the
source's work actions; the emission appends to `pre ++ c.output` by
associativity; the native head and buffer contents are fixed; the
successor control carries the new tag, dying exactly when the source
halts. -/
theorem vhostEmitTM_step (M : MultiTapeTM m Bool S) (c : Cfg m Bool S y)
    (b : Bool) (hb : FinTM.VirtualTag c.inputPos b) (p : Fin (x.length + 2))
    (pre : List Bool) :
    ∃ b', FinTM.VirtualTag (M.step c).inputPos b' ∧
      (vhostEmitTM M).step (vhostCfg c b p pre) =
        vhostCfg (M.step c) b' p pre := by
  cases hq : c.state with
  | none =>
    refine ⟨b, ?_, ?_⟩
    · simpa only [MultiTapeTM.step_of_halt hq] using hb
    · rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt]
      simp [vhostCfg, hq]
  | some q =>
    have hs : (vhostCfg c b p pre).state = some (q, b) := by
      simp [vhostCfg, hq]
    have hv : (vhostCfg c b p pre).workTapeSymbols (vhostBuffer m) =
        c.inputSymbol := by
      change FinTM.bufferTape y ((c.inputPos.val : ℤ) - 1) = c.inputSymbol
      exact FinTM.bufferTape_inputSymbol (c.mapState (fun _ => ()))
    have hr : (fun i => (vhostCfg c b p pre).workTapeSymbols (vhostBank i)) =
        c.workTapeSymbols := by
      funext i
      simp [vhostCfg, vhostBank, Cfg.workTapeSymbols]
    let a := M.tr q c.inputSymbol c.workTapeSymbols
    let mv := FinTM.virtualMove b c.inputSymbol a.inputTape
    -- The input-only facts specialize through Unit, preserving arbitrary state universes.
    have hm := FinTM.virtualMove_correct (c.mapState (fun _ => ())) b hb a.inputTape
    have hc : M.step c = a.apply c := by
      simp only [MultiTapeTM.step, hq, a]
    refine ⟨FinTM.virtualNextTag b mv, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · unfold MultiTapeTM.step
      rw [hs]
      dsimp only [vhostEmitTM]
      rw [hv, hr, hq]
      change (Action.apply _ _) = vhostCfg (a.apply c) _ p pre
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;>
          simp [vhostCfg, Action.apply, a]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j
          simpa only [vhostCfg, Action.apply, Fin.addCases_left] using hm.1
        · intro j
          simp [vhostCfg, Action.apply, a]
      · simp only [Action.apply, vhostCfg, List.append_assoc, a]

/-- The forwarding lockstep at every time: one host step per source step,
with a valid arrival tag at the endpoint. Completed outputs are preserved
and a halted source stays absorbed; `t = 0` and the empty buffered word
are instances, not exceptions.

**Proof sketch.** Induct on `t` and chain `vhostEmitTM_step`, exactly as
`Turing.FinTM.bufferedSecondCfg_run` chains its step lemma. -/
theorem vhostEmitTM_runFrom (M : MultiTapeTM m Bool S) (c : Cfg m Bool S y)
    (b : Bool) (hb : FinTM.VirtualTag c.inputPos b) (p : Fin (x.length + 2))
    (pre : List Bool) (t : ℕ) :
    ∃ b', FinTM.VirtualTag (M.runFrom c t).inputPos b' ∧
      (vhostEmitTM M).runFrom (vhostCfg c b p pre) t =
        vhostCfg (M.runFrom c t) b' p pre := by
  induction t with
  | zero => exact ⟨b, hb, rfl⟩
  | succ t ih =>
    obtain ⟨b', hb', he⟩ := ih
    obtain ⟨b'', hb'', he'⟩ := vhostEmitTM_step M _ b' hb' p pre
    refine ⟨b'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hb''
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']

/-- Bank tape `i` of the forwarding host visits exactly the cells the
source's tape `i` visits, at every horizon.

**Proof sketch.** Project `vhostEmitTM_runFrom` at each time
`u ≤ t` onto the head of `vhostBank i`: the transported configuration
holds the source head verbatim, so the two `Finset.image`s over
`Finset.range (t + 1)` agree pointwise. -/
theorem vhostEmitTM_visitedByTapeHead_bank (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (pre : List Bool) (t : ℕ) (i : Fin m) :
    (vhostEmitTM M).visitedByTapeHead (vhostCfg c b p pre) t (vhostBank i) =
      M.visitedByTapeHead c t i := by
  unfold MultiTapeTM.visitedByTapeHead
  congr 1
  funext u
  obtain ⟨b', _, he⟩ := vhostEmitTM_runFrom M c b hb p pre u
  rw [he]
  simp [vhostCfg, vhostBank]

/-- The buffer head's trajectory is exactly the source's input trajectory
shifted by one: at every horizon, the buffer tape's visited set is the
image of the source's input positions minus one.

**Proof sketch.** Project `vhostEmitTM_runFrom` at each `u ≤ t` onto the
buffer head, which the transport pins at the source input position minus
one. -/
theorem vhostEmitTM_visitedByTapeHead_buffer (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (pre : List Bool) (t : ℕ) :
    (vhostEmitTM M).visitedByTapeHead (vhostCfg c b p pre) t (vhostBuffer m) =
      (Finset.range (t + 1)).image
        (fun u => ((M.runFrom c u).inputPos.val : ℤ) - 1) := by
  unfold MultiTapeTM.visitedByTapeHead
  congr 1
  funext u
  obtain ⟨b', _, he⟩ := vhostEmitTM_runFrom M c b hb p pre u
  rw [he]
  simp [vhostCfg, vhostBuffer]

/-- The buffer head stays inside `[-1, y.length]` at every time — the
permanent form of the two boundary clamps, the empty buffered word
included (there the interval is `[-1, 0]` and outward moves stay put).
Adopted as a permanent regression lemma from the F2 epoch audit.

**Proof sketch.** By `vhostEmitTM_runFrom` the buffer head at time `u` is
the source input position minus one, and input positions inhabit
`Fin (y.length + 2)`. -/
theorem vhostCfg_buffer_head_mem (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (pre : List Bool) (t : ℕ) :
    ((vhostEmitTM M).runFrom (vhostCfg c b p pre) t).workTapePos
        (vhostBuffer m) ∈ Finset.Icc (-1 : ℤ) (y.length : ℤ) := by
  obtain ⟨b', _, he⟩ := vhostEmitTM_runFrom M c b hb p pre t
  rw [he]
  simp only [vhostCfg, vhostBuffer, Fin.addCases_left, Finset.mem_Icc]
  have hp := (M.runFrom c t).inputPos.isLt
  constructor <;> omega

/-- The coefficient-one space ledger of the forwarding host: host space is
at most source space plus the buffer interval. No term depends on the
source's output or on the host horizon beyond the source's own space.

**Proof sketch.** Sum over the `1 + m` tapes: each bank tape's visited set
equals the source's (`vhostEmitTM_visitedByTapeHead_bank`), and the
buffer's visited set lies in the `y.length + 2`-cell interval
(`vhostCfg_buffer_head_mem`), so its cardinality is at most
`y.length + 2`. -/
theorem vhostEmitTM_spaceUsed_le (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (pre : List Bool) (t : ℕ) :
    (vhostEmitTM M).spaceUsed (vhostCfg c b p pre) t ≤
      M.spaceUsed c t + (y.length + 2) := by
  have hbuffer : (vhostEmitTM M).spaceUsedByTape (vhostCfg c b p pre) t
      (vhostBuffer m) ≤ y.length + 2 := by
    calc
      _ ≤ (Finset.Icc (-1 : ℤ) (y.length : ℤ)).card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hz
        exact vhostCfg_buffer_head_mem M c b hb p pre u
      _ = y.length + 2 := by
        rw [Int.card_Icc]
        omega
  have hbank (i : Fin m) :
      (vhostEmitTM M).spaceUsedByTape (vhostCfg c b p pre) t (vhostBank i) =
        M.spaceUsedByTape c t i :=
    congrArg Finset.card (vhostEmitTM_visitedByTapeHead_bank M c b hb p pre t i)
  have hsum : M.spaceUsed c t =
      ∑ j ∈ Finset.univ.erase (vhostBuffer m),
        (vhostEmitTM M).spaceUsedByTape (vhostCfg c b p pre) t j := by
    apply Finset.sum_bij (fun i _ => vhostBank i)
    · intro i _
      simp [vhostBank, vhostBuffer, Fin.ext_iff]
    · intro i _ j _ hij
      apply Fin.ext
      have hval := congrArg Fin.val hij
      simpa [vhostBank] using hval
    · intro j
      refine Fin.addCases ?_ ?_ j
      · intro i hi
        have hi0 : i = 0 := Subsingleton.elim _ _
        subst i
        simp [vhostBuffer] at hi
      · intro i _
        exact ⟨i, Finset.mem_univ i, rfl⟩
    · intro i _
      exact (hbank i).symm
  calc
    _ = M.spaceUsed c t +
        (vhostEmitTM M).spaceUsedByTape (vhostCfg c b p pre) t (vhostBuffer m) := by
      rw [hsum]
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
    _ ≤ M.spaceUsed c t + (y.length + 2) := by omega

/-- A source halting step that emits is forwarded before the host control
dies: the emitted bit lands on the host output and the host halts in the
same step. Adopted as a permanent regression lemma from the F2 epoch audit
(the "closed embeddings lose the final halting emission" lesson, checked
here in the positive).

**Proof sketch.** Instantiate `vhostEmitTM_step` at a live `c` whose
action has `state = none` and `output = some bit`: the transported
successor is the halted source step, whose output is
`pre ++ c.output ++ [bit]` by the step identity. -/
theorem vhostEmitTM_emitting_halt (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (pre : List Bool) (q : S) (bit : Bool)
    (hq : c.state = some q)
    (ha : (M.tr q c.inputSymbol c.workTapeSymbols).state = none)
    (ho : (M.tr q c.inputSymbol c.workTapeSymbols).output = some bit) :
    ((vhostEmitTM M).step (vhostCfg c b p pre)).state = none ∧
      ((vhostEmitTM M).step (vhostCfg c b p pre)).output =
        pre ++ c.output ++ [bit] := by
  obtain ⟨b', _, he⟩ := vhostEmitTM_step M c b hb p pre
  rw [he]
  simp [vhostCfg, MultiTapeTM.step, hq, ha, ho, List.append_assoc]

/-- The silent selection consists of all indices below the final capture
tape, and its complement is exactly that tape, including when `m = 0`.

**Proof sketch.** The embedding preserves index values, and every value
below `1 + m` has a preimage. An unselected index is at least `1 + m` and
strictly below `(1 + m) + 1`, so it is the capture index. -/
private theorem vhostSilent_layout (j : Fin ((1 + m) + 1)) :
    (j ∈ Set.range (Fin.castAddEmb 1 : Fin (1 + m) ↪ Fin ((1 + m) + 1)) ↔
      j.val < 1 + m) ∧
    (j ∉ Set.range (Fin.castAddEmb 1 : Fin (1 + m) ↪ Fin ((1 + m) + 1)) ↔
      j = vhostCap m) := by
  have hselected :
      j ∈ Set.range (Fin.castAddEmb 1 : Fin (1 + m) ↪ Fin ((1 + m) + 1)) ↔
        j.val < 1 + m := by
    constructor
    · rintro ⟨i, rfl⟩
      exact i.isLt
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
  refine ⟨hselected, ?_⟩
  rw [hselected]
  constructor
  · intro hj
    apply Fin.ext
    have hlt := j.isLt
    change j.val = 1 + m + 0
    omega
  · rintro rfl
    simp [vhostCap]

/-- The suppressing lockstep at every time: capture records the source's
emissions after the prior capture prefix, the physical output stays
`out₀`, and the arrival tag stays valid.

**Proof sketch.** Chain the two layers: `vhostEmitTM_runFrom` transports
the source run through the forwarding host, and the R1 silent lockstep
(`embedSilentTM_runFrom`) transports the forwarding host's run through the
capture wrapper; `vhostSilentCfg` is by definition the composite
transport. No third induction is performed. -/
theorem vhostSilentTM_runFrom (M : MultiTapeTM m Bool S) (c : Cfg m Bool S y)
    (b : Bool) (hb : FinTM.VirtualTag c.inputPos b) (p : Fin (x.length + 2))
    (capPre out₀ : List Bool) (t : ℕ) :
    ∃ b', FinTM.VirtualTag (M.runFrom c t).inputPos b' ∧
      (vhostSilentTM M).runFrom (vhostSilentCfg c b p capPre out₀) t =
        vhostSilentCfg (M.runFrom c t) b' p capPre out₀ := by
  have hcap := (vhostSilent_layout (vhostCap m)).2.mpr rfl
  obtain ⟨b', hb', he⟩ := vhostEmitTM_runFrom M c b hb p [] t
  refine ⟨b', hb', ?_⟩
  unfold vhostSilentTM vhostSilentCfg
  rw [embedSilentTM_runFrom _ _ hcap, he]

/-- The suppressing flavor's space ledger: source space, the buffer
interval, and the capture word — coefficient one on the source term.

**Proof sketch.** The R1 silent space clauses give the selected tapes' and
capture tape's contributions over the forwarding host's run; substitute
the forwarding ledger (`vhostEmitTM_spaceUsed_le` tape by tape) for the
selected bank, and bound the capture tape by its final word length plus
one via `bufferTape_append` growth. -/
theorem vhostSilentTM_spaceUsed_le (M : MultiTapeTM m Bool S)
    (c : Cfg m Bool S y) (b : Bool) (hb : FinTM.VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (capPre out₀ : List Bool) (t : ℕ) :
    (vhostSilentTM M).spaceUsed (vhostSilentCfg c b p capPre out₀) t ≤
      M.spaceUsed c t + (y.length + 2) +
        ((capPre ++ (M.runFrom c t).output).length + 1) := by
  have hcap := (vhostSilent_layout (vhostCap m)).2.mpr rfl
  have hselected (i : Fin (1 + m)) :
      (vhostSilentTM M).spaceUsedByTape (vhostSilentCfg c b p capPre out₀) t
          (Fin.castAddEmb 1 i) =
        (vhostEmitTM M).spaceUsedByTape (vhostCfg c b p []) t i :=
    (embedSilentTM_visitedByTapeHead (Fin.castAddEmb 1) (vhostCap m) hcap
      (vhostEmitTM M) (fun _ _ => none) (fun _ => 0) capPre out₀
      (vhostCfg c b p []) t i).2
  have hcapture :
      (vhostSilentTM M).spaceUsedByTape (vhostSilentCfg c b p capPre out₀) t
          (vhostCap m) ≤ (capPre ++ (M.runFrom c t).output).length + 1 := by
    have hgrowth := embedSilentTM_spaceUsedByTape_cap (Fin.castAddEmb 1)
      (vhostCap m) hcap (vhostEmitTM M) (fun _ _ => none) (fun _ => 0)
      capPre out₀ (vhostCfg c b p []) t
    obtain ⟨b', _, he⟩ := vhostEmitTM_runFrom M c b hb p [] t
    rw [he] at hgrowth
    change (vhostSilentTM M).spaceUsedByTape (vhostSilentCfg c b p capPre out₀) t
        (vhostCap m) ≤ (M.runFrom c t).output.length - c.output.length + 1 at hgrowth
    simp only [List.length_append]
    omega
  have hsum : (vhostEmitTM M).spaceUsed (vhostCfg c b p []) t =
      ∑ j ∈ Finset.univ.erase (vhostCap m),
        (vhostSilentTM M).spaceUsedByTape (vhostSilentCfg c b p capPre out₀) t j := by
    apply Finset.sum_bij (fun i _ => Fin.castAddEmb 1 i)
    · intro i _
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hi
      exact hcap ⟨i, hi⟩
    · intro i _ j _ hij
      exact (Fin.castAddEmb 1).injective hij
    · intro j hj
      have hne := (Finset.mem_erase.mp hj).1
      have hin : j ∈ Set.range (Fin.castAddEmb 1 : Fin (1 + m) ↪
          Fin ((1 + m) + 1)) := by
        by_contra hout
        exact hne ((vhostSilent_layout j).2.mp hout)
      obtain ⟨i, rfl⟩ := hin
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · intro i _
      exact (hselected i).symm
  calc
    _ = (vhostEmitTM M).spaceUsed (vhostCfg c b p []) t +
        (vhostSilentTM M).spaceUsedByTape (vhostSilentCfg c b p capPre out₀) t
          (vhostCap m) := by
      rw [hsum]
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm
    _ ≤ _ := Nat.add_le_add (vhostEmitTM_spaceUsed_le M c b hb p [] t) hcapture

end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Simulation.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation gadgets

Generic building blocks for machine constructions, split out of
`TCSlib.Complexity.TuringMachine.Composition` at the epoch-1/epoch-2 boundary
(epoch-1 audit, findings 5 and 11, and the policy file-size standard): the
machines of the composition file, and the heavier constructions of later
epochs, are assembled from these. Everything here is public — it is shared
audited surface — and carries no finiteness assumptions beyond what each
gadget needs.

## Contents

* **Emission chains** (`Turing.FinTM.emitAction`, `emit_run`, `emit_halts`):
  states that write a fixed word to the output, one symbol per step, ignoring
  all reads, then halt.
* **Control actions** (`Turing.FinTM.controlAction`, `controlAction_apply`):
  transitions that only move the input head and change state.
* **Input-head positioning** (`Turing.FinTM.inputSymbol_at`,
  `moveInputPos_neg_val`, `rewind_scan`, `rewind_from_any`): reading at a
  position, the clamped left move, and the audited rewind-to-start procedure
  (one unconditional left move, left while reading a symbol, one right move).
* **Disjoint tape-block embeddings** (`Turing.FinTM.leftAction`/`rightAction`,
  `leftCfg`/`rightCfg`, their `apply`/`step`/`run` lemmas): run a machine on
  the left or right block of a `k + l`-tape machine, in lockstep, with the
  other block's tapes inactive. **Scope note** (epoch-1 audit, finding 11):
  these embeddings preserve the *native* input tape and pass emissions to the
  *real* output — they are not, by themselves, a buffered-composition
  simulator; buffering and virtual-input clamping need their own invariants on
  top.
* **Branch union** (`Turing.FinTM.branchTM`, `branchTM_computes`): two
  machines in disjoint tape and state blocks; the Boolean chooses only the
  initial state.
* **Optional-write normalization** (`Turing.Action.apply_workTapes`): the raw
  action-application identity for work tapes, promoted at the epoch-2/epoch-3
  boundary.
* **Buffered sequential simulator** (`Turing.FinTM.bufferedCompTM`): the
  three-block tape partition, contiguous buffer representation, virtual-input
  reads and clamping invariant, first- and second-phase run correspondence,
  and an exact `|y| + 2` rewind-and-dispatch ledger. These extend the scope of
  the native-input embeddings above without changing their statements.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2-§1.3; the "high-level description"
  convention on p. 14.)
-/

namespace Turing

/-- **Optional-write normalization** (promoted from the epoch-2 fill per the
epoch-2 audit, promotion recommendation 1): applying an action rewrites each
work tape at its head with the proposed write, defaulting to the existing read
when the action declines to write. An explicit `some none` write remains an
erase, while an outer `none` writes back the scanned symbol unchanged. Holds
for every alphabet, state type, action, configuration, and tape index — no
finiteness, liveness, or computation hypothesis. -/
lemma Action.apply_workTapes {k : ℕ} {Symbol State : Type*} {input : List Symbol}
    (a : Action k Symbol State) (c : Cfg k Symbol State input) (i : Fin k) :
    (a.apply c).workTapes i =
      Function.update (c.workTapes i) (c.workTapePos i)
        ((a.workTapes i).1.getD (c.workTapeSymbols i)) := by
  cases hw : (a.workTapes i).1 with
  | none => simp [Action.apply, hw, Cfg.workTapeSymbols]
  | some w => simp [Action.apply, hw]

end Turing

namespace Turing.FinTM

/-- One step of a fixed-word emission chain, with an arbitrary state embedding.
The input and all work tapes are left untouched. -/
def emitAction {k : ℕ} {S : Type} (w : List Bool)
    (e : Fin (w.length + 1) → S) (i : Fin (w.length + 1)) : Action k Bool S :=
  if h : i.val < w.length then
    ⟨0, fun _ => (none, 0), some w[i.val], some (e ⟨i.val + 1, by omega⟩)⟩
  else
    ⟨0, fun _ => (none, 0), none, none⟩

/-- After `t` emission steps the state is the `t`-th chain state and exactly the
first `t` symbols have been appended. The induction uses no tape invariant because
emission transitions ignore all reads. -/
lemma emit_run {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    ∀ t (ht : t ≤ w.length),
      (tm.runFrom cfg t).state = some (e ⟨t, by omega⟩) ∧
      (tm.runFrom cfg t).output = cfg.output ++ w.take t := by
  intro t
  induction t with
  | zero =>
    intro ht
    exact ⟨hs, by simp⟩
  | succ t ih =>
    intro ht
    obtain ⟨hstate, hout⟩ := ih (by omega)
    have hstep : tm.runFrom cfg (t + 1) =
        (emitAction w e ⟨t, by omega⟩).apply (tm.runFrom cfg t) := by
      rw [MultiTapeTM.runFrom_succ_eq_step']
      unfold MultiTapeTM.step
      rw [hstate]
      exact congrArg (fun a => a.apply (tm.runFrom cfg t)) (htr _ _ _)
    rw [hstep]
    simp only [emitAction, dif_pos (show t < w.length by omega), Action.apply]
    refine ⟨True.intro, ?_⟩
    rw [hout, List.take_succ, List.getElem?_eq_getElem (by omega)]
    simp [List.append_assoc]

/-- One further, nonemitting step halts the fixed-word emission chain. -/
lemma emit_halts {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (w : List Bool) (e : Fin (w.length + 1) → S)
    (htr : ∀ i inp work, tm.tr (e i) inp work = emitAction w e i)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some (e 0)) :
    (tm.runFrom cfg (w.length + 1)).state = none ∧
      (tm.runFrom cfg (w.length + 1)).output = cfg.output ++ w := by
  obtain ⟨hstate, hout⟩ := emit_run tm w e htr cfg hs w.length (le_refl _)
  rw [MultiTapeTM.runFrom_succ_eq_step']
  unfold MultiTapeTM.step
  rw [hstate]
  dsimp only
  rw [htr]
  simp [emitAction, Action.apply, hout]


/-- An action that only moves the input head and changes the state. -/
def controlAction {k : ℕ} {S : Type} (m : SignType) (q : Option S) :
    Action k Bool S := ⟨m, fun _ => (none, 0), none, q⟩

/-- Read position `i + 1` as the optional `i`-th input symbol, including the
right boundary. -/
lemma inputSymbol_at {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (i : ℕ) (hi : i ≤ x.length)
    (hp : cfg.inputPos.val = i + 1) : cfg.inputSymbol = x[i]? := by
  by_cases h : i < x.length
  · rw [inputSymbolInner i (by omega) h, List.getElem?_eq_getElem h]
  · have he : i = x.length := by omega
    have hz : cfg.inputPos ≠ 0 := by
      intro hz
      rw [hz] at hp
      simp at hp
    simp only [Cfg.inputSymbol, dif_neg hz, dif_pos (show cfg.inputPos.val = x.length + 1 by omega)]
    simp [he]


/-- Extend an action to the left block of a disjoint tape sum and rename states. -/
def leftAction {k : ℕ} {S S' : Type} (l : ℕ) (f : S → S')
    (a : Action k Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases a.workTapes (fun _ => (none, 0))
  output := a.output
  state := a.state.map f

/-- Extend an action to the right block, leaving the left block untouched. -/
def rightAction {l : ℕ} {S S' : Type} (k : ℕ) (f : S → S')
    (a : Action l Bool S) : Action (k + l) Bool S' where
  inputTape := a.inputTape
  workTapes := Fin.addCases (fun _ => (none, 0)) a.workTapes
  output := a.output
  state := a.state.map f

/-- Embed a configuration in the left tape block, retaining arbitrary inactive
right tapes and head positions. The state renaming preserves halting. -/
def leftCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases c.workTapes tapes
  workTapePos := Fin.addCases c.workTapePos heads
  output := c.output

/-- Embed in the right block, retaining arbitrary inactive left tapes. This is also
used when the left block contains a completed controller's work. -/
def rightCfg {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    Cfg (k + l) Bool S' x where
  state := c.state.map f
  inputPos := c.inputPos
  workTapes := Fin.addCases tapes c.workTapes
  workTapePos := Fin.addCases heads c.workTapePos
  output := c.output

/-- Extending an action commutes with the left configuration embedding. -/
lemma leftCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action k Bool S) (c : Cfg k Bool S x)
    (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    (leftAction l f a).apply (leftCfg f c tapes heads) =
      leftCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [leftAction, leftCfg, Action.apply]

/-- Extending an action commutes with the right configuration embedding. -/
lemma rightCfg_apply {k l : ℕ} {S S' : Type} {x : List Bool} (f : S → S')
    (a : Action l Bool S) (c : Cfg l Bool S x)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    (rightAction k f a).apply (rightCfg f c tapes heads) =
      rightCfg f (a.apply c) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [rightAction, rightCfg, Action.apply]

/-- A machine whose renamed transitions use only the left block simulates one
step exactly, including the absorbing halting configuration. -/
lemma leftCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) :
    tm'.step (leftCfg f c tapes heads) = leftCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [leftCfg, hs]
  | some q =>
    have hs' : (leftCfg f c tapes heads).state = some (f q) := by simp [leftCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (leftCfg f c tapes heads).workTapeSymbols (Fin.castAdd l i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, leftCfg]
    change (leftAction l f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact leftCfg_apply f _ c tapes heads

/-- The right-block version of the one-step correspondence; inactive tapes may
contain arbitrary data from an earlier phase. -/
lemma rightCfg_step {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) :
    tm'.step (rightCfg f c tapes heads) = rightCfg f (tm.step c) tapes heads := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [rightCfg, hs]
  | some q =>
    have hs' : (rightCfg f c tapes heads).state = some (f q) := by simp [rightCfg, hs]
    rw [hs']
    dsimp only
    rw [htr]
    have hr : (fun i => (rightCfg f c tapes heads).workTapeSymbols (Fin.natAdd k i)) =
        c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, rightCfg]
    change (rightAction k f (tm.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact rightCfg_apply f _ c tapes heads

/-- Lift the left-block one-step correspondence to every finite run. -/
lemma leftCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      leftAction l f (tm.tr q inp (fun i => work (Fin.castAdd l i))))
    (c : Cfg k Bool S x) (tapes : Fin l → ℤ → Option Bool) (heads : Fin l → ℤ) (t : ℕ) :
    tm'.runFrom (leftCfg f c tapes heads) t = leftCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => leftCfg f c tapes heads)
    (fun c => leftCfg_step tm tm' f htr c tapes heads) c t

/-- Lift the right-block correspondence to every run, preserving arbitrary
inactive left tapes. This is the fresh-branch lockstep gadget. -/
lemma rightCfg_run {k l : ℕ} {S S' : Type} {x : List Bool}
    (tm : MultiTapeTM l Bool S) (tm' : MultiTapeTM (k + l) Bool S') (f : S → S')
    (htr : ∀ q inp work, tm'.tr (f q) inp work =
      rightAction k f (tm.tr q inp (fun i => work (Fin.natAdd k i))))
    (c : Cfg l Bool S x) (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ) (t : ℕ) :
    tm'.runFrom (rightCfg f c tapes heads) t = rightCfg f (tm.runFrom c t) tapes heads :=
  MultiTapeTM.runFrom_comm_of_step (fun c => rightCfg f c tapes heads)
    (fun c => rightCfg_step tm tm' f htr c tapes heads) c t

/-- Put two machines in disjoint tape and state blocks; the Boolean chooses only
the initial state, while the transition table is independent of that choice. -/
def branchTM (M₁ M₂ : FinTM Bool) (b : Bool) : FinTM Bool where
  k := M₁.k + M₂.k
  State := M₁.State ⊕ M₂.State
  tm :=
    { q₀ := cond b (.inl M₁.tm.q₀) (.inr M₂.tm.q₀)
      tr := fun q inp work => match q with
        | .inl q => leftAction M₂.k Sum.inl
            (M₁.tm.tr q inp (fun i => work (Fin.castAdd M₂.k i)))
        | .inr q => rightAction M₁.k Sum.inr
            (M₂.tm.tr q inp (fun i => work (Fin.natAdd M₁.k i))) }

/-- Each selected branch has exactly its original time and completed output.
The proof embeds its initial blank configuration, then uses lockstep. -/
lemma branchTM_computes (M₁ M₂ : FinTM Bool) (b : Bool) (x w : List Bool) (t : ℕ) :
    (branchTM M₁ M₂ b).ComputesInTime x w t ↔ (cond b M₁ M₂).ComputesInTime x w t := by
  cases b with
  | false =>
    have hi : (branchTM M₁ M₂ false).tm.initCfg x =
        rightCfg Sum.inr (M₂.tm.initCfg x) (fun (_ : Fin M₁.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [rightCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      rightCfg_run M₂.tm (branchTM M₁ M₂ false).tm Sum.inr (fun _ _ _ => rfl)]
    simp only [rightCfg, Option.map_eq_none_iff]
  | true =>
    have hi : (branchTM M₁ M₂ true).tm.initCfg x =
        leftCfg Sum.inl (M₁.tm.initCfg x) (fun (_ : Fin M₂.k) _ => none) (fun _ => 0) := by
      refine Cfg.ext rfl rfl ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
      · funext i
        refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [leftCfg]
    rw [computesInTime_iff, computesInTime_iff, hi,
      leftCfg_run M₁.tm (branchTM M₁ M₂ true).tm Sum.inl (fun _ _ _ => rfl)]
    simp only [leftCfg, Option.map_eq_none_iff]

/-- A control action leaves all work tapes, work heads, and output unchanged. -/
lemma controlAction_apply {k : ℕ} {S : Type} {x : List Bool}
    (cfg : Cfg k Bool S x) (m : SignType) (q : Option S) :
    (controlAction m q).apply cfg =
      {cfg with state := q, inputPos := moveInputPos cfg.inputPos m} := by
  refine Cfg.ext rfl rfl rfl ?_ ?_
  · funext i
    simp [controlAction, Action.apply]
  · simp [controlAction, Action.apply]

/-- The clamped left move always subtracts one from the natural input position. -/
lemma moveInputPos_neg_val {n : ℕ} (pos : Fin (n + 2)) :
    (moveInputPos pos .neg).val = pos.val - 1 := by
  by_cases h : pos = 0
  · subst pos
    simp [SignType.neg_eq_neg_one]
  · rw [moveInputPos_neg_of_ne_left pos h]

/-- Starting at or to the left of the last input symbol, scan left to the left
blank, then move right and dispatch. All other configuration fields are preserved.

**Proof sketch.** Induct on the input-head position. At zero the scanned symbol is
blank, so one right move finishes. At a positive position the input symbol exists;
one left move reduces the position and the induction hypothesis finishes the run. -/
lemma rewind_scan {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (scan : S) (dest : Option S)
    (htr : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest) :
    ∀ (cfg : Cfg k Bool S x), cfg.state = some scan → cfg.inputPos.val ≤ x.length →
      tm.runFrom cfg (cfg.inputPos.val + 1) = {cfg with state := dest, inputPos := 1} := by
  have aux : ∀ (j : ℕ) (cfg : Cfg k Bool S x), cfg.state = some scan →
      cfg.inputPos.val = j → j ≤ x.length →
      tm.runFrom cfg (j + 1) = {cfg with state := dest, inputPos := 1} := by
    intro j
    induction j with
    | zero =>
      intro cfg hs hj _
      have hz : cfg.inputPos = 0 := Fin.ext hj
      have hsym : cfg.inputSymbol = none := by
        unfold Cfg.inputSymbol
        rw [dif_pos hz]
      change tm.step cfg = _
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only
      rw [htr, hsym]
      dsimp only
      rw [controlAction_apply]
      have hm : moveInputPos cfg.inputPos .pos = 1 := by
        apply Fin.ext
        rw [hz, moveInputPos_pos_of_ne_right _ (by simp)]
        simp
      rw [hm]
    | succ j ih =>
      intro cfg hs hj hlen
      have hsym : cfg.inputSymbol = some (x[j]'(by omega)) :=
        inputSymbolInner j (by omega) (by omega)
      have hstep : tm.step cfg =
          {cfg with state := some scan, inputPos := moveInputPos cfg.inputPos .neg} := by
        unfold MultiTapeTM.step
        rw [hs]
        dsimp only
        rw [htr, hsym]
        dsimp only
        rw [controlAction_apply]
      have hp : (moveInputPos cfg.inputPos .neg).val = j := by
        rw [moveInputPos_neg_val]
        omega
      rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
      exact ih _ rfl hp (by omega)
  intro cfg hs hp
  exact aux cfg.inputPos.val cfg hs rfl hp

/-- From any valid input position, take the mandatory first left move and then
scan left. This returns to position `1`, even for an empty input or a start at a
boundary. No work tape or output is changed. -/
lemma rewind_from_any {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (start scan : S) (dest : Option S)
    (hstart : ∀ inp work, tm.tr start inp work = controlAction .neg (some scan))
    (hscan : ∀ inp work, tm.tr scan inp work =
      match inp with
      | some _ => controlAction .neg (some scan)
      | none => controlAction .pos dest)
    (cfg : Cfg k Bool S x) (hs : cfg.state = some start) :
    ∃ t, tm.runFrom cfg t = {cfg with state := dest, inputPos := 1} := by
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
  refine ⟨1 + (c.inputPos.val + 1), ?_⟩
  rw [MultiTapeTM.runFrom_add]
  have hfirst : tm.runFrom cfg 1 = c := rfl
  rw [hfirst, rewind_scan tm scan dest hscan c hc hp]
  simp only [c, hstep]

/-- A quantitative refinement of `rewind_from_any`: its construction takes
at most the current input position plus two steps, preserving all work and output.
**Proof sketch.** The mandatory first left move puts the head at most at the
last input symbol. `rewind_scan` then takes exactly the new position plus one. -/
lemma timed_rewind {k : ℕ} {S : Type} {x : List Bool}
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

/-- Assemble the left work block, one buffer tape, and the right work block.
All three projections use the same nested `Fin.addCases` partition. -/
def tapeBlocks {α : Type} {k l : ℕ} (left : Fin k → α) (buffer : α)
    (right : Fin l → α) : Fin (k + (1 + l)) → α :=
  Fin.addCases left (Fin.addCases (fun _ => buffer) right)

/-- The left projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_left {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin k) :
    tapeBlocks a b c (Fin.castAdd (1 + l) i) = a i := by simp [tapeBlocks]

/-- The buffer projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_buffer {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin 1) :
    tapeBlocks a b c (Fin.natAdd k (Fin.castAdd l i)) = b := by
  simp [tapeBlocks]

/-- The right projection of the three-block tape partition. -/
@[simp] lemma tapeBlocks_right {α : Type} {k l : ℕ} (a : Fin k → α) (b : α)
    (c : Fin l → α) (i : Fin l) :
    tapeBlocks a b c (Fin.natAdd k (Fin.natAdd 1 i)) = c i := by simp [tapeBlocks]

/-- A word stored contiguously from cell zero, blank at every other integer cell. -/
def bufferTape (w : List Bool) (z : ℤ) : Option Bool :=
  if 0 ≤ z then w[z.toNat]? else none

/-- An empty buffer is blank everywhere. -/
@[simp] lemma bufferTape_nil : bufferTape [] = fun _ => none := by
  funext z
  simp [bufferTape]

/-- The buffer cell at any nonnegative natural position reads the corresponding
optional word entry, so position `w.length` is the right blank. -/
@[simp] lemma bufferTape_nat (w : List Bool) (i : ℕ) :
    bufferTape w i = w[i]? := by simp [bufferTape]

/-- Cell minus one is the left blank, including for an empty word. -/
@[simp] lemma bufferTape_left (w : List Bool) : bufferTape w (-1) = none := by
  simp [bufferTape]

/-- Appending one emitted bit changes just the old right-blank cell.

**Proof sketch.** At that cell the appended singleton is read. At a smaller
nonnegative cell, list lookup stays in the old prefix. Larger cells and all
negative cells remain blank. -/
lemma bufferTape_append (w : List Bool) (b : Bool) :
    bufferTape (w ++ [b]) = Function.update (bufferTape w) (w.length : ℤ) (some b) := by
  funext z
  by_cases hz : z = (w.length : ℤ)
  · subst z
    simp [bufferTape]
  · rw [Function.update_of_ne hz]
    by_cases h0 : 0 ≤ z
    · have hne : z.toNat ≠ w.length := by omega
      simp only [bufferTape, if_pos h0, List.getElem?_append]
      split
      · rfl
      · have hgt : w.length < z.toNat := by omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    · simp [bufferTape, h0]

/-- A boundary tag constrains only boundary positions: false at the left blank,
true at the right blank. Interior positions admit either direction-of-arrival tag. -/
def VirtualTag {n : ℕ} (p : Fin (n + 2)) (b : Bool) : Prop :=
  (p.val = 0 → b = false) ∧ (p.val = n + 1 → b = true)

/-- Suppress an outward move at a blank whose boundary is identified by the tag.
The real buffer head otherwise takes the simulated input movement. -/
def virtualMove (b : Bool) (inp : Option Bool) (m : SignType) : SignType :=
  if inp = none ∧ ((b = false ∧ m = .neg) ∨ (b = true ∧ m = .pos)) then 0 else m

/-- Record the last nonstationary buffer movement. A stationary move preserves
its boundary tag, so repeated outward attempts remain clamped. -/
def virtualNextTag (b : Bool) (m : SignType) : Bool :=
  match m with
  | .neg => false
  | .zero => b
  | .pos => true

/-- Buffer reads at virtual position minus one equal native input reads. -/
lemma bufferTape_inputSymbol {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) : bufferTape w ((c.inputPos.val : ℤ) - 1) = c.inputSymbol := by
  by_cases h0 : c.inputPos = 0
  · simp [Cfg.inputSymbol, h0]
  · have hp : 0 < c.inputPos.val := by
      have : c.inputPos.val ≠ 0 := fun h => h0 (Fin.ext h)
      omega
    have he : (c.inputPos.val : ℤ) - 1 = ((c.inputPos.val - 1 : ℕ) : ℤ) := by omega
    rw [he, bufferTape_nat]
    have h := inputSymbol_at c (c.inputPos.val - 1)
      (by have := c.inputPos.isLt; omega) (by omega)
    exact h.symm

/-- The virtual movement and arrival tag exactly implement native clamping.

**Proof sketch.** Split into left boundary, right boundary, and interior. The
buffer is blank exactly at the two boundaries in this range. The tag specifies
which outward direction to suppress. The three movement cases then give the
position equation and preserve the boundary-tag invariant, even on empty input. -/
lemma virtualMove_correct {k : ℕ} {S : Type} {w : List Bool}
    (c : Cfg k Bool S w) (b : Bool) (hb : VirtualTag c.inputPos b) (m : SignType) :
    (c.inputPos.val : ℤ) - 1 + (virtualMove b c.inputSymbol m : ℤ) =
      ((moveInputPos c.inputPos m).val : ℤ) - 1 ∧
    VirtualTag (moveInputPos c.inputPos m)
      (virtualNextTag b (virtualMove b c.inputSymbol m)) := by
  have hp := c.inputPos.isLt
  by_cases h0 : c.inputPos.val = 0
  · have he : c.inputPos = 0 := Fin.ext h0
    have hbf := hb.1 h0
    subst b
    cases m <;>
      simp [virtualMove, virtualNextTag, Cfg.inputSymbol, he, VirtualTag,
        moveInputPos, SignType.zero_eq_zero, SignType.neg_eq_neg_one,
        SignType.pos_eq_one]
  · have hne : c.inputPos ≠ 0 := fun h => h0 (congrArg Fin.val h)
    by_cases hr : c.inputPos.val = w.length + 1
    · have hbt := hb.2 hr
      subst b
      have he : c.inputPos = ⟨w.length + 1, by omega⟩ := Fin.ext hr
      have hs : c.inputSymbol = none := by simp [Cfg.inputSymbol, he]
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | pos =>
        simp [virtualMove, virtualNextTag, hs, he, VirtualTag, SignType.pos_eq_one]
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, hr, SignType.neg_eq_neg_one]
        omega
    · have hs : c.inputSymbol = some (w[c.inputPos.val - 1]'(by omega)) :=
        inputSymbolInner _ (by omega) (by omega)
      cases m with
      | zero =>
        simpa [virtualMove, virtualNextTag, hs, SignType.zero_eq_zero] using
          (And.intro (show (c.inputPos.val : ℤ) - 1 = (c.inputPos.val : ℤ) - 1 from rfl) hb)
      | neg =>
        rw [moveInputPos_neg_of_ne_left _ hne]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.neg_eq_neg_one]
        constructor <;> omega
      | pos =>
        rw [moveInputPos_pos_of_ne_right _ hr]
        simp [virtualMove, virtualNextTag, hs, VirtualTag, SignType.pos_eq_one]

/-- Run the first machine into the middle buffer, rewind it, then run the second
machine with virtual input. The first component's halting state and the rewind
state are live administrative states. Phase two alone can halt or emit output. -/
def bufferedCompTM (M₁ M₂ : FinTM Bool) : FinTM Bool where
  k := M₁.k + (1 + M₂.k)
  State := Option M₁.State ⊕ (Unit ⊕ (M₂.State × Bool))
  tm :=
    { q₀ := .inl (some M₁.tm.q₀)
      tr := fun q inp work => match q with
        | .inl (some q) =>
          let a := M₁.tm.tr q inp (fun i => work (Fin.castAdd (1 + M₂.k) i))
          ⟨a.inputTape, tapeBlocks a.workTapes
            (a.output.map some, if a.output = none then 0 else .pos)
            (fun _ => (none, 0)), none, some (.inl a.state)⟩
        | .inl none =>
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
            none, some (.inr (.inl ()))⟩
        | .inr (.inl ()) =>
          if work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = none then
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .pos) (fun _ => (none, 0)),
              none, some (.inr (.inr (M₂.tm.q₀, true)))⟩
          else
            ⟨0, tapeBlocks (fun _ => (none, 0)) (none, .neg) (fun _ => (none, 0)),
              none, some (.inr (.inl ()))⟩
        | .inr (.inr (q, b)) =>
          let v := work (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1)))
          let a := M₂.tm.tr q v (fun i => work (Fin.natAdd M₁.k (Fin.natAdd 1 i)))
          let m := virtualMove b v a.inputTape
          ⟨0, tapeBlocks (fun _ => (none, 0)) (none, m) a.workTapes,
            a.output, a.state.map (fun q => .inr (.inr (q, virtualNextTag b m)))⟩ }

/-- Embed phase one with its exact emitted prefix on the buffer and the buffer
head on its right blank. The real output and the second work block are empty. -/
def bufferedFirstCfg (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inl c.state)
  inputPos := c.inputPos
  workTapes := tapeBlocks c.workTapes (bufferTape c.output) (fun _ _ => none)
  workTapePos := tapeBlocks c.workTapePos c.output.length (fun _ => 0)
  output := []

/-- The initialized composite is the embedded initialized first machine. -/
lemma bufferedFirstCfg_init (M₁ M₂ : FinTM Bool) (x : List Bool) :
    (bufferedCompTM M₁ M₂).tm.initCfg x = bufferedFirstCfg M₁ M₂ (M₁.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [bufferedFirstCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedFirstCfg, tapeBlocks]

/-- One live first-phase transition preserves the complete buffer invariant,
including an emission on the simulated halting transition.

**Proof sketch.** The first work block and native input move in lockstep. A
nonemitting transition leaves the buffer fixed; an emission updates precisely its
right blank by `bufferTape_append` and moves that head one step. The second block
and real output stay empty, and a simulated halt remains an administrative state. -/
lemma bufferedFirstCfg_step (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedFirstCfg M₁ M₂ (M₁.tm.step c) := by
  unfold MultiTapeTM.step
  cases hq : c.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (bufferedFirstCfg M₁ M₂ c).state = some (.inl (some q)) := by
      simp [bufferedFirstCfg, hq]
    rw [hs']
    dsimp only [bufferedCompTM]
    have hr : (fun i => (bufferedFirstCfg M₁ M₂ c).workTapeSymbols
        (Fin.castAdd (1 + M₂.k) i)) = c.workTapeSymbols := by
      funext i
      simp [bufferedFirstCfg, Cfg.workTapeSymbols]
    have hi : (bufferedFirstCfg M₁ M₂ c).inputSymbol = c.inputSymbol := rfl
    rw [hr, hi]
    let a := M₁.tm.tr q c.inputSymbol c.workTapeSymbols
    change (⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.inl a.state)⟩ :
      Action (M₁.k + (1 + M₂.k)) Bool _).apply _ = bufferedFirstCfg M₁ M₂ (a.apply c)
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedFirstCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;>
            simp [bufferedFirstCfg, Action.apply, ho, bufferTape_append]
        · intro j; simp [bufferedFirstCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedFirstCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [bufferedFirstCfg, Action.apply, ho]
        · intro j; simp [bufferedFirstCfg, Action.apply]
    · simp [bufferedFirstCfg, Action.apply]

/-- First-phase lockstep holds up to and including the first halting transition.
The hypothesis deliberately excludes steps after the simulated halt. -/
lemma bufferedFirstCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (t : ℕ)
    (h : ∀ s, s < t → (M₁.tm.runFrom c s).state ≠ none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) t =
      bufferedFirstCfg M₁ M₂ (M₁.tm.runFrom c t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      bufferedFirstCfg_step M₁ M₂ _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Embed a configuration on virtual input `y` while the physical input remains
`x`. The buffer head represents virtual position minus one. The left block and
native input head retain arbitrary inactive contents from phase one. -/
def bufferedSecondCfg (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (p : Fin (x.length + 2))
    (tapes : Fin M₁.k → ℤ → Option Bool) (heads : Fin M₁.k → ℤ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := c.state.map (fun q => .inr (.inr (q, b)))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) c.workTapes
  workTapePos := tapeBlocks heads ((c.inputPos.val : ℤ) - 1) c.workTapePos
  output := c.output

/-- One second-phase step simulates one native step, with a valid new arrival
tag. The statement includes the absorbing halting case.

**Proof sketch.** Buffer reads agree with virtual input reads. The clamping lemma
proves the head equation and preserves the tag. All second-machine work actions
and emissions are unchanged, while the buffer and first block are read-only. -/
lemma bufferedSecondCfg_step (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) :
    ∃ b', VirtualTag (M₂.tm.step c).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.step (bufferedSecondCfg M₁ M₂ c b p tapes heads) =
        bufferedSecondCfg M₁ M₂ (M₂.tm.step c) b' p tapes heads := by
  cases hq : c.state with
  | none =>
    refine ⟨b, ?_, ?_⟩
    · simpa only [MultiTapeTM.step_of_halt hq] using hb
    · rw [MultiTapeTM.step_of_halt hq, MultiTapeTM.step_of_halt]
      simp [bufferedSecondCfg, hq]
  | some q =>
    let a := M₂.tm.tr q c.inputSymbol c.workTapeSymbols
    let m := virtualMove b c.inputSymbol a.inputTape
    have hm := virtualMove_correct c b hb a.inputTape
    have hc : M₂.tm.step c = a.apply c := by
      simp only [MultiTapeTM.step, hq, a]
    refine ⟨virtualNextTag b m, ?_, ?_⟩
    · simpa only [hc, Action.apply] using hm.2
    · have hs : (bufferedSecondCfg M₁ M₂ c b p tapes heads).state =
          some (.inr (.inr (q, b))) := by simp [bufferedSecondCfg, hq]
      have hv : (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.castAdd M₂.k (0 : Fin 1))) = c.inputSymbol := by
        simp [bufferedSecondCfg, Cfg.workTapeSymbols, bufferTape_inputSymbol]
      have hr : (fun i => (bufferedSecondCfg M₁ M₂ c b p tapes heads).workTapeSymbols
          (Fin.natAdd M₁.k (Fin.natAdd 1 i))) = c.workTapeSymbols := by
        funext i
        simp [bufferedSecondCfg, Cfg.workTapeSymbols]
      unfold MultiTapeTM.step
      rw [hs]
      dsimp only [bufferedCompTM]
      rw [hv, hr, hq]
      change (Action.apply _ _) = bufferedSecondCfg M₁ M₂ (a.apply c) _ p tapes heads
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [bufferedSecondCfg, Action.apply, a]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;>
            simp [bufferedSecondCfg, Action.apply, a]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [bufferedSecondCfg, Action.apply, a]
        · intro j
          refine Fin.addCases ?_ ?_ j
          · intro j
            simpa only [bufferedSecondCfg, Action.apply, tapeBlocks_buffer] using hm.1
          · intro j; simp [bufferedSecondCfg, Action.apply, a]

/-- Every second-phase run has a matching virtual run at the same time and a
valid arrival tag. This preserves completed outputs and absorbing halting. -/
lemma bufferedSecondCfg_run (M₁ M₂ : FinTM Bool) {x y : List Bool}
    (c : Cfg M₂.k Bool M₂.State y) (b : Bool) (hb : VirtualTag c.inputPos b)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (t : ℕ) :
    ∃ b', VirtualTag (M₂.tm.runFrom c t).inputPos b' ∧
      (bufferedCompTM M₁ M₂).tm.runFrom (bufferedSecondCfg M₁ M₂ c b p tapes heads) t =
        bufferedSecondCfg M₁ M₂ (M₂.tm.runFrom c t) b' p tapes heads := by
  induction t with
  | zero => exact ⟨b, hb, rfl⟩
  | succ t ih =>
    obtain ⟨b', hb', he⟩ := ih
    obtain ⟨b'', hb'', he'⟩ := bufferedSecondCfg_step M₁ M₂ _ b' hb' p tapes heads
    refine ⟨b'', ?_, ?_⟩
    · simpa only [MultiTapeTM.runFrom_succ_eq_step'] using hb''
    · rw [MultiTapeTM.runFrom_succ_eq_step', he, he', MultiTapeTM.runFrom_succ_eq_step']

/-- The rewind scan configuration, with buffer head at `j - 1` and all second
machine tapes still blank. The scan state is always live, including at `j = 0`. -/
def bufferedScanCfg (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) (j : ℕ) :
    Cfg (bufferedCompTM M₁ M₂).k Bool (bufferedCompTM M₁ M₂).State x where
  state := some (.inr (.inl ()))
  inputPos := p
  workTapes := tapeBlocks tapes (bufferTape y) (fun _ _ => none)
  workTapePos := tapeBlocks heads ((j : ℤ) - 1) (fun _ => 0)
  output := []

/-- Scanning from virtual position `j ≤ |y|` takes exactly `j + 1` transitions
to reach the second machine's initialized configuration with arrival tag true.

**Proof sketch.** At zero the buffer head is at the left blank, so move right
and dispatch. At successor `j + 1`, cell `j` contains a symbol; one left move
reduces to `j`. For an empty word, dispatch reaches its right blank with the
correct true tag, and its left blank remains one inward move away. -/
lemma bufferedScanCfg_run (M₁ M₂ : FinTM Bool) {x : List Bool} (y : List Bool)
    (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
    (heads : Fin M₁.k → ℤ) : ∀ j, j ≤ y.length →
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedScanCfg M₁ M₂ y p tapes heads j) (j + 1) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero]
    simp only [MultiTapeTM.step, bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols,
      tapeBlocks_buffer, Nat.cast_zero, zero_sub, bufferTape_left]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [bufferedSecondCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedSecondCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;>
          simp [bufferedSecondCfg, Action.apply]
  | succ j ih =>
    intro hj
    have hread : bufferTape y (((j + 1 : ℕ) : ℤ) - 1) = some y[j] := by
      rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega,
        bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedScanCfg M₁ M₂ y p tapes heads (j + 1)) =
        bufferedScanCfg M₁ M₂ y p tapes heads j := by
      simp only [MultiTapeTM.step, bufferedScanCfg, bufferedCompTM, Cfg.workTapeSymbols,
        tapeBlocks_buffer, hread, Option.some_ne_none, if_false]
      refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply]
        · intro j
          refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [Action.apply]
      · funext i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [Action.apply]
        · intro z
          refine Fin.addCases ?_ ?_ z <;> intro z <;> simp [Action.apply, sub_eq_add_neg]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep]
    exact ih (by omega)

/-- From a completed first-phase configuration, rewind and dispatch cost exactly
`|output| + 2` steps. The first move is unconditional from the right blank.

**Proof sketch.** That first left move reaches scan position `|output|`. Apply
the scan invariant for the remaining `|output| + 1` transitions. The real output
stays empty and the native input head and first work block stay fixed. -/
lemma bufferedFirstCfg_rewind (M₁ M₂ : FinTM Bool) {x : List Bool}
    (c : Cfg M₁.k Bool M₁.State x) (hs : c.state = none) :
    (bufferedCompTM M₁ M₂).tm.runFrom (bufferedFirstCfg M₁ M₂ c) (c.output.length + 2) =
      bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg c.output) true c.inputPos c.workTapes c.workTapePos := by
  have hstep : (bufferedCompTM M₁ M₂).tm.step (bufferedFirstCfg M₁ M₂ c) =
      bufferedScanCfg M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos c.output.length := by
    simp only [MultiTapeTM.step, bufferedFirstCfg, hs, bufferedCompTM]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [bufferedScanCfg, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [bufferedScanCfg, Action.apply, sub_eq_add_neg]
  rw [show c.output.length + 2 = (c.output.length + 1) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step, hstep]
  exact bufferedScanCfg_run M₁ M₂ c.output c.inputPos c.workTapes c.workTapePos _ (le_refl _)

/-- Any completed first computation reaches the second phase within
`t₁ + |y| + 2` steps, with a fresh second work block and virtual input `y`.

**Proof sketch.** Choose the first halting time, which is at most `t₁`.
First-phase lockstep reaches its completed configuration, and determinism
identifies the output with `y`. The exact rewind lemma supplies `|y| + 2` more
steps, retaining the first block and parked native input head. -/
lemma bufferedComp_start (M₁ M₂ : FinTM Bool) (x y : List Bool) (t₁ : ℕ)
    (h₁ : M₁.ComputesInTime x y t₁) :
    ∃ (a : ℕ) (p : Fin (x.length + 2)) (tapes : Fin M₁.k → ℤ → Option Bool)
      (heads : Fin M₁.k → ℤ), a ≤ t₁ + y.length + 2 ∧
      (bufferedCompTM M₁ M₂).tm.runFrom ((bufferedCompTM M₁ M₂).tm.initCfg x) a =
        bufferedSecondCfg M₁ M₂ (M₂.tm.initCfg y) true p tapes heads := by
  classical
  have hh : ∃ t, (M₁.tm.runFrom (M₁.tm.initCfg x) t).state = none :=
    ⟨t₁, ((computesInTime_iff M₁ x y t₁).mp h₁).1⟩
  let t := Nat.find hh
  let c := M₁.tm.runFrom (M₁.tm.initCfg x) t
  have hs : c.state = none := Nat.find_spec hh
  have ht : t ≤ t₁ := Nat.find_min' hh ((computesInTime_iff M₁ x y t₁).mp h₁).1
  have hc : M₁.ComputesInTime x c.output t :=
    (computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩
  have ho : c.output = y := hc.output_unique h₁
  refine ⟨t + (y.length + 2), c.inputPos, c.workTapes, c.workTapePos, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, bufferedFirstCfg_init,
    bufferedFirstCfg_run M₁ M₂ _ t (fun s hs => Nat.find_min hh hs)]
  have hf := bufferedFirstCfg_rewind M₁ M₂ c hs
  cases ho
  exact hf

end Turing.FinTM

/-! ### Machine-agreement transfer (§13, Z5)

Two machines over the same tape count and state type whose transition
tables agree on a set of control states run identically for as long as the
run's control stays inside that set. This is the `hagree` genre of
`Turing.capture_run`/`Turing.emit_run` made standalone: those lemmas carry
a per-state agreement hypothesis for one specific wrapper, re-proved ad hoc
at every host; the standalone form transfers whole runs between any two
agreeing tables (design `machine-library-design.md` §13, item Z5; decision
D-R3). First customers: the forwarding loop host of `Build/Loop.lean`
(whose fourteen phase lemmas are verbatim re-proofs of the capturing
host's, since the two tables agree on every non-body state) and the
guarded `clSlot_run` agreement sites of `CookLevin/Hardness.lean`. -/

namespace Turing.MultiTapeTM

/-- The two transition tables agree on every control state in `Q`: from any
such state, both machines take the identical action on identical reads.
Nothing is assumed about states outside `Q`, about `q₀`, or about
halting. -/
def AgreeOn {k : ℕ} {Symbol State : Type*} (M N : MultiTapeTM k Symbol State)
    (Q : Set State) : Prop :=
  ∀ q ∈ Q, ∀ inp work, M.tr q inp work = N.tr q inp work

/-- One step transfers across an agreement: if the configuration's control
state (when live) lies in the agreement set, both machines step it to the
same configuration. Halted configurations step to themselves on both sides.

**Proof sketch.** On `c.state = none` both steps are the identity. On
`c.state = some q` with `q ∈ Q`, unfold `step`: both sides apply the same
action `M.tr q c.inputSymbol c.workTapeSymbols = N.tr q …` to `c`. -/
theorem step_eq_of_agreeOn {k : ℕ} {Symbol State : Type*}
    {M N : MultiTapeTM k Symbol State} {Q : Set State}
    (h : M.AgreeOn N Q) {input : List Symbol} (c : Cfg k Symbol State input)
    (hq : ∀ q, c.state = some q → q ∈ Q) :
    N.step c = M.step c := by
  cases hs : c.state with
  | none => simp only [step_of_halt hs]
  | some q =>
    simp only [step, hs]
    rw [h q (hq q hs)]

/-- A whole run transfers across an agreement: if every control state the
`M`-run visits strictly before time `t` lies in the agreement set, the two
runs coincide at time `t` (and hence at every earlier time, by
instantiating `t`). The endpoint itself may leave the set or halt; no
liveness is assumed, and `t = 0` is the trivial case.

**Proof sketch.** Induct on `t`. The inductive hypothesis transfers the
run at `t`; the visit hypothesis at `u = t` puts its live control in `Q`,
so `step_eq_of_agreeOn` transfers the final step. Halted intermediate
configurations step identically on both sides without the hypothesis. -/
theorem runFrom_eq_of_agreeOn {k : ℕ} {Symbol State : Type*}
    {M N : MultiTapeTM k Symbol State} {Q : Set State}
    (h : M.AgreeOn N Q) {input : List Symbol} (c : Cfg k Symbol State input)
    (t : ℕ) (hq : ∀ u < t, ∀ q, (M.runFrom c u).state = some q → q ∈ Q) :
    N.runFrom c t = M.runFrom c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runFrom_succ_eq_step', ih (fun u hu => hq u (by omega)),
      runFrom_succ_eq_step']
    exact step_eq_of_agreeOn h _ (hq t (by omega))

end Turing.MultiTapeTM
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


/-! ### Selected-tape exports (§13 Z1 rider, decision D-R1)

The retrofit inventories (`audits/retrofit-inventory/`) found, three times
independently, that no old-code R1 consumer can be proved from this file's
public surface: the frame lemmas cover only unselected tapes, and
`embedSlot_selected` is private. These four projections export the
selected-tape fields of the two configuration transports. They are
skeleton-time proofs (statement-phase additions flagged for the A-S1
audit): each is definitional at `embedSlot_selected`. -/

/-- The silent transport holds the source's tape `i` on host tape `ι i`. -/
theorem embedSilentCfg_selected_tape (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes (ι i) =
      c.workTapes i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The silent transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedSilentCfg_selected_pos (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos (ι i) =
      c.workTapePos i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape `i` on host tape
`ι i`. -/
theorem embedEmitCfg_selected_tape (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapes (ι i) = c.workTapes i := by
  simp [embedEmitCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedEmitCfg_selected_pos (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapePos (ι i) = c.workTapePos i := by
  simp [embedEmitCfg, embedSlot_selected]

end Turing
```

## ===== audits/logs/vhost-f1-integration-sweep.log =====

```
VHOST-F1 INTEGRATION SWEEP at b3b99d6d535f2c8513f12f812819ea5292587e34, 2026-10-09 16:33:14
== TCSlib/Complexity/TuringMachine/Simulation
exit_TCSlib/Complexity/TuringMachine/Simulation=0
== TCSlib/Complexity/TuringMachine/Build/Embed
TCSlib/Complexity/TuringMachine/Build/Embed.lean:330:5: warning: unused variable `hcap`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
TCSlib/Complexity/TuringMachine/Build/Embed.lean:790:5: warning: unused variable `hcap`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
exit_TCSlib/Complexity/TuringMachine/Build/Embed=0
== TCSlib/Complexity/TuringMachine/Build/VirtualInput
exit_TCSlib/Complexity/TuringMachine/Build/VirtualInput=0
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
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4741:79: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4741:79: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4739:72: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4784:9: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4784:9: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4776:60: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4776:60: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4761:72: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4764:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4766:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4768:38: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4777:36: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4819:79: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4819:79: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4798:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4817:67: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4829:43: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4858:15: warning: This simp argument is unused:
  List.length_nil

Hint: Omit it from the simp argument list.
  simp only [L̵i̵s̵t̵.̵l̵e̵n̵g̵t̵h̵_̵n̵i̵l̵,̵ ̵Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4893:15: warning: This simp argument is unused:
  List.length_nil

Hint: Omit it from the simp argument list.
  simp only [L̵i̵s̵t̵.̵l̵e̵n̵g̵t̵h̵_̵n̵i̵l̵,̵ ̵Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:4979:65: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:5039:72: warning: This simp argument is unused:
  pairDecode

Hint: Omit it from the simp argument list.
  simp [hx, a2_mapTM, a2_mapAct, Action.apply, a2_mapCfg,̵ ̵p̵a̵i̵r̵D̵e̵c̵o̵d̵e̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:5048:17: warning: This simp argument is unused:
  if_pos rfl

Hint: Omit it from the simp argument list.
  simp only [̵i̵f̵_̵p̵o̵s̵ ̵r̵f̵l̵]̵ ̵at hr

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:5008:76: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:5014:78: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:5017:78: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8047:25: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8047:25: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8146:62: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8294:34: warning: This simp argument is unused:
  f2_splitRestoreScan

Hint: Omit it from the simp argument list.
  simp [Action.apply,̵ ̵f̵2̵_̵s̵p̵l̵i̵t̵R̵e̵s̵t̵o̵r̵e̵S̵c̵a̵n̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8324:85: warning: 'omega' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8324:85: warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8387:6: warning: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8432:52: warning: This simp argument is unused:
  Nat.cast_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, N̵a̵t̵.̵c̵a̵s̵t̵_̵o̵n̵e̵,̵ ̵Fin.ext_iff, Fin.val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8432:66: warning: This simp argument is unused:
  Fin.ext_iff

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.e̵x̵t̵_̵i̵f̵f̵,̵ ̵F̵i̵n̵.̵val_one] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8432:79: warning: This simp argument is unused:
  Fin.val_one

Hint: Omit it from the simp argument list.
  simp only [List.length_nil, Nat.zero_add, Nat.cast_one, Fin.ext_iff,̵ ̵F̵i̵n̵.̵v̵a̵l̵_̵o̵n̵e̵] at h₁

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8472:20: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵f2_catalogPolyUnaryTM, Action.apply, f2_catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8472:38: warning: This simp argument is unused:
  f2_catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, f̵2̵_̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, f2_catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8472:75: warning: This simp argument is unused:
  f2_catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, Action.apply,̵ ̵f̵2̵_̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8473:10: warning: This simp argument is unused:
  MultiTapeTM.step

Hint: Omit it from the simp argument list.
  simp [M̵u̵l̵t̵i̵T̵a̵p̵e̵T̵M̵.̵s̵t̵e̵p̵,̵ ̵f2_catalogPolyUnaryTM, Action.apply, f2_catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8473:28: warning: This simp argument is unused:
  f2_catalogPolyUnaryTM

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, f̵2̵_̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵U̵n̵a̵r̵y̵T̵M̵,̵ ̵Action.apply, f2_catalogPolyCfg]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8473:65: warning: This simp argument is unused:
  f2_catalogPolyCfg

Hint: Omit it from the simp argument list.
  simp [MultiTapeTM.step, f2_catalogPolyUnaryTM, Action.apply,̵ ̵f̵2̵_̵c̵a̵t̵a̵l̵o̵g̵P̵o̵l̵y̵C̵f̵g̵]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:8520:23: warning: This simp argument is unused:
  Prod.mk.injEq

Hint: Omit it from the simp argument list.
  simp only [ht0, MultiTapeTM.runFrom_zero, f2_splitRestoreScan, Cfg.ofWords,
      Option.some.injEq,̵ ̵P̵r̵o̵d̵.̵m̵k̵.̵i̵n̵j̵E̵q̵] at hstate

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:10487:23: warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
exit_TCSlib/Complexity/TuringMachine/Build/Catalog=0
== TCSlib/Complexity/TuringMachine
exit_TCSlib/Complexity/TuringMachine=0
VHOST_F1_SWEEP_DONE
```

## ===== audits/logs/vhost-f1-axioms.log =====

```
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

## ===== audits/logs/vhost-f1-stylelint.log =====

```
WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean       10878 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean          5515 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean    6374 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/TuringMachine/Build/Catalog.lean       10878 lines; 39 public / 384 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean    157 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean         975 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean         975 lines; 23 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean          5515 lines; 8 public / 204 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean    6374 lines; 18 public / 254 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean          696 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean          696 lines; 13 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean  508 lines; 16 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean      739 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean      739 lines; 10 public / 19 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Zone.lean          455 lines; 28 public / 0 private declarations

style_lint: 0 FAIL, 3 WARN over 9 files
```
