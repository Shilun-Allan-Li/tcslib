# External audit pack — Chapter 4, phase P4.3, round 2 (re-audit of the round-1 repairs)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase
P4.3, round 2. Round 1 (`audits/ch4-p43-findings.md`, attached verbatim)
returned **1 blocker, 4 majors, 4 minors, 3 notes**; per `workflow.md` §3 the
gate did not close. This round audits the repairs. The gate closes on zero
blockers and zero majors.

Audited at commit `aa02db41` (branch `complexity/arora-barak-ch3-4`). The
complete repair is the attached diff
(`audits/evidence/ch4-p43-r2-repairs.diff`, the range `200f4693..aa02db41`
restricted to the three repaired files): **one statement changed**
(`exists_adjacency_codec_cnf`, the blocker), **one definition added**
(`Turing.Cfg.InWindow`), and six proof sketches plus the module docstring's
deviations bullet rewritten. Every other declaration of the phase is
byte-identical to the round-1 surface, checkable in the diff.

**Layering update since round 1**: the P4.2 gate is now **CLOSED** (round 1,
PASS — `audits/ch4-p42-resolutions.md`, attached). The restated codec
deliberately factors through that closed surface's vertex quotient
(`Turing.NDTM.coreSum`, the three-valued `Turing.OutSummary`), exactly the
repair direction round 1 proposed; round-1 note 10's cross-filing is
disposed there (no P4.2 defect found). The P4.4 gate also closed; §12
remains under concurrent audit, cited by fill-engine references only.

## Brief for the auditor

You have the round-1 report. For each finding, the table below states the
repair and where it lives; the complete change is the attached diff. Your
deliverables:

1. For **finding 1 (the blocker)**: audit the restated
   `Complexity.exists_adjacency_codec_cnf` as a fresh statement — blind-restate
   it, then check it against your own round-1 repair guidance: the codec's
   injectivity now reaches only the input and the vertex quotient
   (`x = x'` across inputs; `coreSum c = coreSum d` within one input); the
   windowed side condition is the new `Turing.Cfg.InWindow`; the adjacency
   equivalence reads `coreSum (M.tm.step c) = coreSum d`; validity (`φv`)
   characterizes exactly the codec image among length-matching strings;
   acceptance (`φacc`) is halted state plus `accept` summary; cross-input
   pairs are rejected by `φa`; and all three CNFs carry `numVars` and
   **serialized-length** bounds. Is the restatement true, and is it strong
   enough for the hardness route of your round-1 answer 5?
2. For **each major and minor (2-9)**: verify the repair matches your
   proposed fix or say why the deviation is inadequate. Majors 4 and 5
   repaired the *sketches* only — confirm the statements never needed to
   change.
3. Report anything the repairs broke or newly misstate — in particular,
   check the new `Cfg.InWindow` definition and the restated package's
   quantifier structure for fresh defects — in the same findings-table
   format and severity scale as round 1.

Sources as in round 1 ([AB09] §4.2, §4.1.3, Exercise 3.2).

## Scope

| Item | Where |
|---|---|
| Under audit | the attached diff: `ClassPSPACE/TQBF.lean` (the restated codec package, `Turing.Cfg.InWindow`, the rewritten deviations bullet, the membership and hardness sketches), `ClassPSPACE/Games.lean` (the `determined` sketch), `SpaceComplexity/Hierarchy.lean` (the `space_universal` and `space_hierarchy` sketches, the padding clause of `SPACE_linear_ne_NP`, one docstring bullet) |
| Unchanged, re-attached for context | `Formulas/{QBF,QBFEncoding}.lean`, both facades, and every statement of the three repaired files other than the codec package (byte-identity checkable in the diff) |
| Declared, out of scope | the same commit range also contains: the P4.2/P4.4 gate closures (their findings, resolutions, and seven swept docstring minors in `ConfigGraph`/`Logspace/*` — closed gates, attached as context), the phase-P3.3 statement skeleton (`TuringMachine/NDCodes.lean`, `Diagonalization/NTimeHierarchy.lean` — its own future gate), and plan/backlog bookkeeping. Also out of scope: tactic proofs; round-1 notes 11-12 (dispositions below) |

## Per-finding disposition (verify each)

| # | Round-1 finding | Repair |
|---|---|---|
| 1 | **blocker** — fixed-length injective codes on full configurations are impossible (unbounded output; pigeonhole at `n = s = 0`) | Restated over the quotient carrier, per your guidance: `code` is injective **down to `(x, coreSum)`** on `Cfg.InWindow`-windowed configurations; the output enters only through the summary; adjacency compares `coreSum (step c)` with `coreSum d`. Your `c_j` family now has equal codes *required* (all `j ≥ 2` are `dead`-summary with equal cores), and the halted self-loop reads `coreSum (step c) = coreSum c` — consistent, no pigeonhole |
| 2 | **major** — the existential package supplies no uniform construction | The package now declares itself **existence, not an algorithm** (docstring bullet + hardness sketch): the uniform polynomial-time emitter of `φv`/`φa`/`φacc`, the initial-vertex code, and the level scaffolding are **private, named fill obligations of `TQBF_PSPACEHard`** — your proposed option (b) |
| 3 | **major** — unguarded midpoints invent paths through junk codes | The package now carries `φv` with an exact image characterization (both directions, over all length-matching strings) and cross-input rejection; the hardness sketch's recursion guards the midpoint with `Valid` and quantifies an `Accept` target — your `Valid`/`Next`/`Accept` interface |
| 4 | **major** — `space_universal` sketch: window-membership is not a cell count; streamed output cannot be retracted | Sketch rewritten (statement unchanged, as you noted it could be): visited-interval **cardinality** via min/max counters checked including the final configuration (`s = 0` always fails; your `0 → 1` instance counts two cells); the core-count clock with the periodicity argument; **probe silently, then replay** for the output contract; the canonizer cost a finite code-dependent constant, no `O(length α)` claim |
| 5 | **major** — `space_hierarchy` sketch: `∀ α, ∃ Cα` gives no uniform `O(g)` bound | Sketch rewritten (statement unchanged) to your increasing-budget repair: budgets `s = 0, …, g n` over fixed banks, the fixed universal's own heads **hard-capped** in `[-g n, g n]` (uniform in `α`), first-success flip with a three-valued attempt summary, one **fixed code with padded payload**, the **space-preserving one-work-tape normal form named as a fill obligation** (a time-only normal form is not a space ledger), domination at `A := C_α·(c₀ + 2)` through the bundled floors; `f`'s constructibility contributes only its floor |
| 6 | minor — `ψ₀ = adjacency` misses zero-length paths at live vertices | The hardness sketch's base is now `Valid a ∧ Valid b ∧ (a = b ∨ Next (a, b))` |
| 7 | minor — the codec's listed tracks omitted the scanned input | The codec now carries the **input-content track** (plus the one-hot position track), keeping the formulas input-independent; `φa` conjoins content-track equality and reads the scanned bit under the position marker |
| 8 | minor — the literal-occurrence sum misses empty clauses | All three size clauses now bound `(CNF.serialize ·).length` directly (plus `numVars`); the sketch cites the serialization-length equation with clause count explicit |
| 9 | minor — mover-relative game value flips polarity | `determined`'s sketch now fixes the **player-one perspective** (`V h` = player one can force `W = true`; OR at even, AND at odd histories) and extracts both strategies by polarity |
| 10 | note — [P4.2] carrier distinction | Filed to the P4.2 round, which closed with no defect; disposition in `audits/ch4-p42-resolutions.md` (its note 6 carries the bridge obligations) |
| 11 | note — junk-code attribution under the abstract scheme | No change: the abstract `code` makes no per-string attribution, and `space_universal` never needs one; recorded |
| 12 | note — attestation posture | This round attaches the repair diff itself; revision identity and olean freshness remain maintainer attestations, stated to verify or challenge |

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch4-p43-r2-sweep.log`, revision recorded at
  start: `aa02db41`): all seven modules, both facades listed, 0 `error:`
  lines, fresh `.olean`s, exactly **12** `declaration uses 'sorry'` warnings
  (QBF 1, QBFEncoding 1, TQBF 5, Games 1, Hierarchy 4; facades 0) — the
  inventory is unchanged by the repairs (one statement restated in place,
  one definition added).
* Style lint (`audits/logs/ch4-p43-r2-stylelint.log`): `Formulas` 0 FAIL /
  0 WARN over 5 files; `ClassPSPACE` 0 FAIL / 0 WARN over 2 files;
  `SpaceComplexity` 0 FAIL / 0 WARN over 42 files (`Hierarchy.lean`
  included; facades sit outside the per-tree linter, as in round 1).
* Statement-freeze baseline: commit `aa02db41`.
* The repaired surface's new declaration count: 14 definitions + 1
  (`Turing.Cfg.InWindow`) and 12 sorried statements, counts verified
  programmatically against the sweep log.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch4-p43-r2-findings.md`; the gate closes on zero blockers and majors.


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


## ===== audits/ch4-p43-findings.md =====

```
# P4.3 statement-gate audit

**Verdict: FAIL — gate remains open.** **1 blocker, 4 majors, 4 minors, 3 notes.** The blocker is a false statement, `exists_adjacency_codec_cnf`. The majors concern the advertised interfaces and proof sketches, not counterexamples to PSPACE-completeness or the space hierarchy theorem.

Input SHA-256, independently recomputed:

`5a52f3982128502b46dfe4914df2ebbcec22d1a792d0df5373b6d348210e9f1e`

The bundle contains **exactly 30 attachments**. Audited baseline asserted by the pack: `200f4693a40f30302efed75a4e23ac31216172b7`, branch `complexity/arora-barak-ch3-4`. Scope: the seven named P4.3 files, **14 definitions and 12 sorried statements**, with the supplied dependencies as context. I read the in-scope declarations with comments stripped before comparing their docstrings. No source files were changed; no sub-agents were used.

The arguments below are mathematical statement audits, **not completed Lean proofs or a fresh elaboration**. “True” means independently supported by the stated construction, not inferred from `sorryAx` or the false codec lemma. The exact commit comparison and build-artifact claims remain unverified; see finding 12.

## Findings

Paths in this table are relative to `TCSlib/Complexity/`, except for the pack and logs. Line numbers refer to the extracted attachments.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **blocker** | `ClassPSPACE/TQBF.lean:122` · `exists_adjacency_codec_cnf` | Windowed **full** configurations admit fixed-length injective codes and exact-step adjacency. | Set `n = s = 0`, keep the state halted, input position fixed, work heads at zero and tapes blank, and vary `output`. There are infinitely many such configurations but only `2^C` length-`C` codes. Section “Counterexample” gives the finite pigeonhole contradiction. Exact-step correctness alone also forces the impossible injectivity on these halted configurations. | Encode a finite, acceptance-preserving quotient, such as `coreSum`, and change **both** equality clauses accordingly; or explicitly restrict to a suitable bounded-output carrier and prove its closure/adequacy. Merely deleting the injectivity conjunct or invoking `coreCode_inj` does not repair the statement. |
| 2 | **major** | `ClassPSPACE/TQBF.lean:122,193` · adjacency package / `TQBF_PSPACEHard` sketch | The existential package supplies the polynomially emittable objects needed by a Karp reduction. | Its prefix is `∀ M, ∃ C, ∀ n s, ∃ code φ`. It specifies neither a uniform constructor nor a computation bound for `code`, the initial/accepting codes, or `φ`. Polynomial description size does not supply a polynomial-time algorithm selecting descriptions. This defect survives repair of finding 1. | Give a joint uniform construction contract, or name a concrete construction plus private polynomial-time construction/serialization obligations used by hardness. Do not claim that the displayed existential interface alone supplies them. |
| 3 | **major** | `ClassPSPACE/TQBF.lean:128,174` · guarded eval equivalence / midpoint recursion | Correctness on encoded configuration pairs suffices when midpoint blocks quantify over all bit strings. | The theorem says nothing about strings outside the codec image. A two-bit example has valid codes `00,11`, only identity edges between valid codes, but additionally permits `00 → 01 → 11`; all valid-pair checks hold while the midpoint formula invents a path. See question 5. | Supply an efficient validity predicate and restrict existential intermediate vertices, or give a total adjacency contract excluding invalid vertices. Include computable initial and accepting predicates and the quotient-to-run bridge. |
| 4 | **major** | `SpaceComplexity/Hierarchy.lean:77` · `space_universal` sketch | Window overflow and a clock implement the stated exact visited-cell test and tagged output. | At `s = 1`, a one-tape machine can visit positions `0,1` and halt without leaving `[-1,1]`, although it used two cells. At `s = 0`, the initial work-cell visit already exceeds the budget. Also, streamed output cannot be retracted when a later overflow/nonhalting verdict must yield exactly `[false]`. | Track the visited interval and reject when its cardinality exceeds `s`, including initial and final configurations. Probe silently, then on success emit `true` and replay while forwarding output. Budget canonization by a finite code-dependent constant, not the unprovided claim `O(length α)`. The theorem statement can remain unchanged. |
| 5 | **major** | `SpaceComplexity/Hierarchy.lean:132` · `space_hierarchy` sketch | The displayed call to `space_universal` proves one uniform `O(g(n))` bound for the diagonal machine. | `C` may depend on the code parsed from the input; `∀ α, ∃ Cα` does not give `∃ C, ∀ inputs`. Calling with budget proportional to `g(n)` gives a code-dependent multiple of `g(n)`. Padding the code can change that constant, contrary to the attached `CodePrefix` discipline. | Cap the diagonal machine's own simulated workspace uniformly, keep one code fixed, and pad the payload. Question 7 gives a repair using capped calls at increasing budgets; it also avoids assuming a tighter cost for a call made with budget `g(n)`. State the space-preserving normal-form and virtual-input obligations. |
| 6 | minor | `ClassPSPACE/TQBF.lean:177,190` · hardness sketch | `ψ₀ = adjacency` starts the induction “path of length at most `2^i`.” | For a live configuration `c` with `step c ≠ c`, zero-step reachability from `c` to itself is true, but adjacency at `(c,c)` is false. Halted self-loops do not fix this at live vertices. | Set the base to valid equality **or** adjacency, or prove exact-`2^i` reachability and separately pad paths at a halted accepting target. This is also a small omission in the book's displayed induction, not a reason to inherit it. |
| 7 | minor | `ClassPSPACE/TQBF.lean:106` · codec construction sketch | The listed state/head/work tracks suffice for an input-independent adjacency formula `φ`. | The listed tracks omit the input symbols and the scanned-input snapshot. A machine changing state according to its scanned input bit has identical listed tracks on one-bit inputs `false` and `true`, but different successors. The formal `code x c` may depend on `x`; the sketch has not used that allowance. | Include a scanned-symbol snapshot and its consistency checks, or carry the read-only input track in the code; alternatively allow an input-dependent formula. Do not assert linear local-check size until these checks and multi-tape coordination are accounted for. Polynomial size remains sufficient. |
| 8 | minor | `ClassPSPACE/TQBF.lean:138` · CNF size measure | The literal-occurrence bound is, by itself, an adequate serialization-size bound. | For `φ = List.replicate r []`, the stated sum is zero and `numVars = 0`, while `CNF.serialize φ` has length `2r + 1`. Empty clauses cost syntax without contributing literals. | Bound clause count too, bound serialization length directly, or prove a normalization retaining at most one empty clause before emission. See question 4 for the exact length equation. |
| 9 | minor | `ClassPSPACE/Games.lean:84` · `determined` sketch | A value meaning “the mover can force a win for their side” obeys the displayed alternating existential/universal recursion with terminal value `W`. | That recurrence keeps **player one's** perspective fixed. A mover-relative value instead changes polarity as the turn changes; at an odd terminal history, `W = true` still means player one won. | Define the value as “player one can force `W = true`,” use OR at even histories and AND at odd histories, and explicitly construct player two's strategy where the value is false. The theorem itself is true. |
| 10 | note | **[P4.2]** `SpaceComplexity/ConfigGraph.lean:119,127,156` · `coreSum`, `CfgStep`, `coreSum_stepWith` | The finite counted vertices and the raw reachability relation have different carriers. | `coreSum` discards unbounded output information down to three cases; `CfgStep` still relates full configurations. The supplied congruence is the right bridge for acceptance. I found no counterexample to these definitions in this review. | No P4.2 repair requested here. File this distinction with that round; finding 1 is a P4.3 misuse of the finite-counting idea, not an inherited false P4.2 definition. |
| 11 | note | `TimeHierarchy/Diagonal.lean:106` and pack question 6 · abstract `code` / “junk codes” | A particular junk string has a specified parser-fallback meaning. | The attached `code` is a choice of an `EffectiveMachineCode`. Its supplied laws ensure total effective decoding and padded encoding round trips, but do not identify a fallback machine for `[]` or another arbitrary string. | Test arbitrary decoded machines, or supply a theorem identifying the selected concrete scheme before asserting a junk string's exact output. This does not harm `space_universal`. |
| 12 | note | Pack provenance and `audits/logs/ch4-p43-*` | The bundle independently establishes the historical diff, fresh elaboration, fresh oleans, and full facade wiring. | The source inventory and text logs check out, but the audited git objects and build artifacts are not in the bundle. The located older checkout does not contain `200f4693`; no historical equality was inferred from it. The logs contain neither per-module exit statuses nor olean freshness evidence. | Retain these as maintainer attestations; attach the seven-file diff and artifact/exit evidence if independent certification is required. No mathematical gate decision here depends on accepting those claims. |

## Counterexample to the codec statement

Fix any `M : FinTM Bool`. Suppose the claimed witnesses exist. Take the resulting constant `C` and specialize to `n = s = 0` and `x = []`.

For each integer `j` with `0 ≤ j ≤ 2^C`, form the configuration

\[
c_j=\{\mathrm{state}:=\mathrm{none},\quad
\mathrm{inputPos}:=0,\quad
\mathrm{workTapes}:=(\lambda i\,z.\,\mathrm{none}),\quad
\mathrm{workTapePos}:=(\lambda i.\,0),\quad
\mathrm{output}:=\mathrm{replicate}(j,\mathrm{false})\}.
\]

All fields are well typed: the empty input has two allowed input-head positions, and there is no restriction on the output list. For every work tape, the head has absolute position zero and every cell outside the zero-radius window is blank. Thus every pair `c_j,c_k` satisfies all four window hypotheses.

The theorem consequently gives

\[
\operatorname{length}(\mathrm{code}\ []\ c_j)=C(0+0+1)=C,
\]
\[
\mathrm{code}\ []\ c_j=\mathrm{code}\ []\ c_k
\Longrightarrow c_j=c_k
\Longrightarrow j=k,
\]

where the last implication follows by taking output lengths. This is an injection from a set of size `2^C + 1` into the binary words of length `C`, a set of size `2^C`. Therefore

\[
2^C+1\le 2^C,
\]

a contradiction. No assumption about the transition table, constructibility, reachability from the initial configuration, or the formula-size bound is needed.

Deleting the explicit injectivity conjunct does not help. Each `c_j` is halted, so `M.tm.step c_j = c_j`, making the formula true on its code paired with itself. If `code [] c_j = code [] c_k`, the formula has the same assignment on `(c_j,c_k)`; the eval equivalence then gives `step c_j = c_k`, hence again `c_j = c_k`.

An acceptance-oriented repair should make the code factor through `coreSum`, identify equal codes with equal summaries and cores, and compare `coreSum (step c)` with `coreSum d`. The supplied `coreSum_stepWith` then supports lifting quotient paths from the actual initial configuration. Forgetting output entirely would lose the acceptance test; retaining its three-valued summary avoids that problem.

## Blind restatements of all 14 definitions

These restatements were obtained from the declaration bodies before reading their docstrings.

| # | Definition | Literal mathematical meaning and comparison |
|---|---|---|
| D1 | `QBF.Quant` | A two-element datatype with constructors `ex` and `all`. Their logical meaning is supplied by the recursion, not by this datatype alone. |
| D2 | `QBF` | An arbitrary pair of a finite quantifier list and a CNF over natural-number variable indices. There is no closure condition tying the two fields together. This is the declared CNF restriction with open matrices permitted. |
| D3 | `truthAux m qs σ i` | Quantify a Boolean at index `i`, overwrite that coordinate of `σ`, increment `i`, and recurse on the remaining list; an empty list asks whether `m.eval σ = true`. The `ex` branch uses existence and the `all` branch uses universal quantification. Coordinates outside the processed interval retain their original values. |
| D4 | `truth Q` | Apply `truthAux` to `Q.matrix`, starting with `Q.quants`, the constant-false assignment, and index zero. A matrix variable beyond the prefix is therefore fixed to false, not implicitly existentially quantified. |
| D5 | `quantBit` | Map `ex` to `true` and `all` to `false`. |
| D6 | `quantOfBit` | Map `true` to `ex` and `false` to `all`. Both compositions with D5 are identities by two cases. |
| D7 | `encode Q` | Encode the quantifier bits as the doubled first component of `pairEncode`, followed by its aligned `false,true` separator and the CNF serialization. No well-formedness hypothesis is required. |
| D8 | `decode x` | On pair success, decode every prefix bit and total-decode the matrix bytes. On pair failure, return the empty prefix and empty CNF. A malformed matrix after a successful pair parse retains the parsed prefix but replaces the matrix by the empty CNF; its truth is still true. |
| D9 | `PSPACEHard L'` | Every binary language in `PSPACE` has a polynomial-time many-one reduction to `L'`. No membership or decidability condition on `L'` is part of hardness alone. |
| D10 | `PSPACEComplete L'` | The conjunction that `L'` belongs to `PSPACE` and satisfies D9. |
| D11 | `TQBF` | The set of all binary strings whose total-decoded QBF satisfies D4. This is a particular totalized string language, not the convention that all malformed encodings are rejected. |
| D12 | `Game.playOut s₁ s₂ n` | Begin with the empty history and append one chosen bit per recursive step. Player one supplies a move when the current history length is even, and player two when it is odd. The resulting history has length exactly `n`. |
| D13 | `Game.FirstWins n W` | There exists one history-dependent strategy for player one such that every player-two strategy produces a length-`n` play with `W = true`. The winning strategy must be fixed before the opposing strategy is chosen. |
| D14 | `Game.SecondWins n W` | There exists one player-two strategy such that every player-one strategy produces `W = false`. This is the correct opposite outcome, not a second existential witness for `W = true`. |

The definitions implement the declared conventions. The differences in D2, D4, D8, D11 and the binary fixed-depth restriction in D12–D14 are explicit restrictions/totalizations, not hidden changes. CNF matrices and unary variable indices preserve polynomial-time completeness when the construction and serialization obligations are actually supplied. Unbound variables fixed to false do not endanger membership or hardness: membership handles them explicitly, and hardness may output closed formulas.

## All 12 sorried statements

| # | Declaration | True-as-stated assessment and argument |
|---|---|---|
| S1 | `QBF.truth_exPrefix_iff_satisfiable` | **True.** Existential witnesses give a total final assignment satisfying the matrix, so the forward implication needs no coverage hypothesis. Conversely choose the satisfying assignment's bit at each index below `n`; `m.numVars ≤ n` ensures agreement on every mentioned variable. |
| S2 | `QBF.decode_encode` | **True.** Apply `pairDecode_pairEncode`, cancel `quantOfBit ∘ quantBit` pointwise, and use `CNF.decode_serialize`. Equality of the two fields gives equality of QBF structures. |
| S3 | `PSPACE_eq_P_of_pspaceComplete_mem_P` | **True.** Hardness and downward closure of `P` under polynomial-time reductions give `PSPACE ⊆ P`. The reverse inclusion follows from the polynomial-space simulation of polynomial-time deciders; the positive polynomial bounds absorb fixed tape-count overhead. |
| S4 | `exists_adjacency_codec_cnf` | **False.** The finite pigeonhole argument above contradicts both its injectivity demand and, independently, its exact-step equivalence on halted configurations. The proof sketch only describes core data, whereas the conclusion distinguishes full output lists. |
| S5 | `TQBF_mem_PSPACE` | **True; even linear space is attainable.** Validate the entire encoding, then traverse assignments depth first with constant-size information per quantified variable and evaluate the serialized CNF by scans. Invalid syntax returns true through the specified fallback; free variables read false. All work fits in `O(input length + 1)` cells without storing a separate restricted formula at every recursion level. |
| S6 | `TQBF_PSPACEHard` | **True as a language-theoretic statement; the advertised proof interface is inadequate.** A valid, uniformly constructible codec of cores plus output summaries yields a polynomial-width finite graph. Apply the guarded midpoint construction from question 5, then prenex conversion, innermost existential Tseitin variables, and polynomial unary serialization. This independent route does not use S4 as written; findings 1–3 must be repaired before the proposed dependency route can be filled. |
| S7 | `TQBF_PSPACEComplete` | **True.** Conjoin S5 and S6 under the definition of `PSPACEComplete`. Its intended proof remains downstream of the unresolved hardness interface. |
| S8 | `Game.determined` | **True.** Backward evaluation of the finite binary game tree determines whether player one can force `W = true`. If so choose a true-valued child at each relevant even node; otherwise choose a false-valued child at each relevant odd node for player two, extending the strategy arbitrarily on unused histories. |
| S9 | `space_universal` | **True, with the corrected construction in question 6.** Effectivity permits finite code-specific canonization overhead, exact interval accounting tests the simulated budget, and a core-count clock decides whether a bounded run halts. A silent first pass followed by replay realizes the output contract without buffering an arbitrarily long output. |
| S10 | `space_hierarchy` | **True, with a uniform cap and fixed-code padding.** Eventual domination plus positivity gives the non-strict inclusion after absorbing finitely many exceptional lengths. The capped diagonal construction in question 7 separates the classes while using a single `O(g)` bound; only the lower floor, not the computability part of `hf`, is needed. |
| S11 | `LOGSPACE_ssubset_PSPACE` | **True.** Apply S10 to `logSpace` and `n + 1`, using the two supplied constructibility contracts and logarithmic domination proved below. A language separating these two bounds also separates `LOGSPACE` from the larger union `PSPACE`. |
| S12 | `SPACE_linear_ne_NP` | **True.** Under the contrary equality, a polynomially padded version of every quadratic-space language lies in linear space and hence in `NP`. Polynomial-reduction closure of `NP` transfers this back to the original language, collapsing quadratic space into linear space and contradicting S10. |

## Answers to the eight questions

**1. Index threading and accumulated updates.** After the first `j` quantifiers starting at index `i`, the assignment agrees with the chosen bits on `[i,i+j)` and with the original assignment outside that interval. Induction proves this: `Function.update` changes exactly `i+j`, and the recursive call advances to `i+j+1`, so it cannot overwrite a previously chosen coordinate. At the leaf, evaluation therefore uses precisely the prescribed quantified coordinates. In particular,

\[
\mathrm{truth}\langle [],m\rangle
\iff m.\mathrm{eval}(\lambda v.\mathrm{false})=\mathrm{true}.
\]

For a closed matrix, varying the initial assignment changes no mentioned variable at the leaf, so it does not change truth.

**2. Coverage of the existential prefix.** `numVars` is one greater than the maximum mentioned index, or zero if none is mentioned. Thus `m.numVars ≤ n` is precisely coverage by the initial segment `[0,n)`; it is sufficient, though not necessary for every particular matrix. Without it, take `m = [[(0,true)]]`, `n = 0`: the matrix is satisfiable but the QBF is false. Forward extraction of a satisfying assignment works without the hypothesis; backward extraction needs the update-agreement argument. At `n = 0`, coverage forces evaluation to be assignment-independent; `[]` is true and `[[]]` is false. Extra existential quantifiers beyond `numVars` change nothing because Boolean quantification is over a nonempty type and those variables do not occur.

**3. Pair alignment and round trip.** The parser reads pairs from the beginning: equal pairs encode prefix bits; the aligned `false,true` pair ends the prefix. An unaligned occurrence of these bits is not a separator. Both quantifier conversion functions are inverse, so the round trip follows exactly as in S2. A separate injectivity hypothesis is unnecessary; the round trip already proves

\[
\mathrm{encode}(Q)=\mathrm{encode}(R)
\Longrightarrow
\mathrm{decode}(\mathrm{encode}(Q))=
\mathrm{decode}(\mathrm{encode}(R))
\Longrightarrow Q=R.
\]

The semantic correctness consumer only needs this round trip; a polynomial-time consumer additionally needs construction and output-length bounds, which the round trip does not assert. Here “malformed” concerns the serialization grammar: a syntactically valid encoding with free matrix variables instead follows the declared false-assignment convention.

**4. Full adjacency-package reading.** For a fixed machine, one positive `C` must work for **all** natural `n,s`. Only then are a total dependent function `code` and a single CNF `φ` selected. The code length is `C(s+n+1)` even on inputs whose length differs from `n` and on nonwindowed configurations; there is no injectivity or adjacency requirement on those extra cases. For inputs of length `n`, both heads and all nonblank work cells of **each** configuration must lie in the window. Under those four assumptions the package demands injectivity into **full configuration equality**, plus the exact deterministic-step test. Neither reachability nor a bound on output is assumed.

The formula is selected before `x` and therefore is the same for every length-`n` input. This is possible with an appropriate input-carrying code, but is not realized by the fields listed in the sketch (finding 7). A corrected code can use padding to meet the exact length and a constant dummy word outside its guarded domain.

On valid concatenated codes, `φ.numVars ≤ 2C(s+n+1)` puts every mentioned variable inside the concatenation; the `getD ... false` default is never consulted for such variables. This is a sound indexing convention. It does not certify that an arbitrary block quantified later is a valid code.

The literal measure is exactly an occurrence count. The attached serialization obeys

\[
\operatorname{length}(\mathrm{CNF.serialize}\,\varphi)
=1+2\varphi.\mathrm{length}
 +\sum_{\text{clause in }\varphi}\ \sum_{(v,b)\text{ in clause}}(v+3).
\]

Consequently, bounding both clause count and literal count, together with `numVars`, bounds the serialized length polynomially. The displayed literal bound alone misses arbitrarily many empty clauses.

At a halted configuration `c`, the required equation really is `d = c`, because `step c = c`. Adding these self-loops preserves acceptance reachability and is a harmless total-step convention. It does not make every live configuration reflexive, nor repair unbounded output.

**5. Membership, midpoint recursion, fresh variables, and hardness.** For membership, the raw input supplies all prefix bits and matrix bytes. The prefix length and every decoded variable index are at most the input length. Validate the complete grammar before committing to a false matrix result: trailing garbage makes the total decoder select the true fallback, even if a scanned prefix looked unsatisfiable. A depth-first traversal stores one of a constant number of phases/values per quantified variable, one current result bit, and cursors; matrix evaluation rereads the input and assignment bank. No stack of copied formulas or logarithmic-size return addresses per variable is needed. The total is `O(n+1)` visited cells, including initialization and parser failure paths.

For hardness, let `ℓ` be the polynomial code width of a **repaired** finite graph. Use an efficiently generated predicate `Valid` for valid vertices, `Next` for adjacency, and `Accept` for halted vertices with accepting output summary. Take

\[
\psi_0(a,b):=
\mathrm{Valid}(a)\land\mathrm{Valid}(b)
\land(a=b\lor\mathrm{Next}(a,b)),
\]
\[
\psi_{i+1}(a,b):=
\exists z\;\Bigl(\mathrm{Valid}(z)\land
\forall u\,v\;\bigl(
((u=a\land v=z)\lor(u=z\land v=b))
\Rightarrow\psi_i(u,v)\bigr)\Bigr),
\]

where every block has `ℓ` Boolean coordinates. For each fixed `z`, specializing the universal pair to `(a,z)` and `(z,b)` gives the two desired subpaths. Conversely, those two subpaths satisfy the implication for every pair, since its antecedent selects exactly those two pairs. The base includes length-zero paths, and splitting/concatenating paths establishes by induction

\[
\psi_i(a,b)\iff
\text{a path of length at most }2^i\text{ joins the valid vertices }a,b.
\]

There are at most `2^ℓ` codes; a shortest reachable path suffices at depth `ℓ`. Quantify an accepting target and constrain the starting code to the actual initial vertex. The quotient congruence lifts a path back to a genuine run and preserves the accepting summary. A unique erased accepting configuration is optional, not needed for this construction.

Finding 3 is independent of finding 1: on a hypothetical repaired finite carrier with image `{00,11}`, let the encoded relation be true on both diagonal valid pairs and whenever at least one endpoint is invalid, but false on `(00,11)` and `(11,00)`. It satisfies the required valid-pair identity-graph semantics. Nevertheless `01` is an existential midpoint giving a two-step path between the distinct valid vertices. A CNF for this four-bit relation exists by the supplied finite Boolean-function lemma.

Allocate disjoint `ℓ`-bit blocks for the midpoint and two universal endpoints at each level. Their quantifier order must follow the recursion, with every newly referenced index bound exactly once in the final initial-segment prefix. The recursion has only one copy of its predecessor, so its added scaffolding has `O(ℓ)` size per level, or `O(ℓ²)` altogether, plus the polynomial-size base/validity predicates. Use constant-arity gate constraints for CNF conversion; applying a truth-table CNF construction to an entire `ℓ`-bit equality or level would instead be exponential.

One safe auxiliary-variable discipline is to prenex the freshened recursion first, then existentially quantify all Tseitin gate values **after** its original prefix. For each complete original assignment, existence of consistent gate values is equivalent to truth of its propositional matrix; quantifying the original assignments preserves that equivalence. Gate values must not be existentially fixed before universal variables on which they depend. All variable indices and the clause/literal counts stay polynomial, so the preceding unary-serialization equation remains polynomial. A **uniform emitter** must still be proved, rather than obtained from S4's unannotated existence statement.

The definition of hardness is exactly polynomial-time many-one hardness; no claim of logspace-reduction completeness is delivered in this phase.

**6. Universal machine: literal clauses and a sound construction.** One machine `SU` is chosen first. For each fixed code `α` there is one positive constant `C`, independent of **both** `s` and `x`. If the decoded deterministic machine has a halting computation within `s` visited cells, the first clause requires the tagged output for every qualifying output/time witness. Determinism makes those output witnesses equal; extra post-halting time does not change output or space. In fact, the first existential antecedent is redundant, because each instance of its inner premises already supplies that antecedent. If no qualifying computation exists, the second clause demands a halting output exactly `[false]`. On well-formed outer triple encodings, the clauses are exhaustive and consistent.

A construction meeting them is:

1. Canonize the fixed code and prepare virtual access to `x`. The effective-scheme contract gives a finite canonizer time and space for this `α`; absorb it into `Cα`. No linear bound in code length is supplied by `EffectiveMachineCode`.
2. Probe the run with output suppressed. The coded machine has one work tape. Maintain the minimum and maximum visited positions, initially both zero, and reject if `max − min + 1 > s`. Unit head moves make this interval exactly the visited set; check a newly reached position even when that step halts.
3. Bound the silent probe by the number of possible cores in the radius-`s` window. For this fixed machine that count is at most
   \[
   (\#M.\mathrm{State}+1)(n+2)3^{2s+1}(2s+1).
   \]
   Its binary counter has `Oα(s + logSpace n + 1)` bits. A repeated live core in a deterministic run makes future control periodic, so no first halt can occur after an undetected repeat; output contents do not affect this argument.
4. On failure output `[false]`. On successful halting, reset the simulated banks, emit `true`, and replay the same run while forwarding its output. Reuse fixed workspace intervals between the two passes; do not buffer the entire output.

The input adapter, budget arithmetic, table/state storage, visited-interval counters, and clock all fit the claimed code-dependent bound. These machine implementations and their space ledgers remain fill obligations.

The logarithmic addend is justified by the `n+2` input-head factor in this clock. This establishes its need for the **proposed clock construction**, not an unconditional lower bound against every possible universal simulation. When `s ≥ logSpace n`, positivity gives

\[
s+\mathrm{logSpace}(n)+1\le 3s,
\]

so it is harmless under the standing above-log convention. Unlike the success-only exercise, the statement also specifies tagged outputs and failure totality; these are valid strengthenings that require the probe/replay work.

For `s = 0`, every coded machine has one work tape and has already visited its origin, so the failure clause applies on every input. For a code of a silent immediate-halting machine, the result at `s ≥ 1` is `[true]`; for a stationary infinite loop it is `[false]`. These examples do not require attributing either machine to a particular “junk” string: the supplied abstract scheme makes no such attribution.

**7. Little-oh, a repaired diagonal argument, and logarithmic domination.** Because `g(n) ≥ 1`, the stated arithmetic hypothesis is equivalent to `f(n)/g(n) → 0`. In one direction, for any positive real `ε`, choose a positive integer `A` with `1/A < ε`; eventually `A f(n) ≤ g(n)`, hence `f(n)/g(n) ≤ 1/A < ε`. In the other direction, for each integer `A > 0` use `ε = 1/A`; `A = 0` is automatic. No monotonicity is needed. When `f = g`, taking `A = 2` contradicts the positive floor, so the theorem is not vacuous on equal bounds.

For the ordinary inclusion, use `A = 1` eventually and absorb the finitely many earlier values of `f` into a multiplicative constant, since `g ≥ 1` everywhere.

Here is one repair of the strictness proof that uses S9's actual interface:

1. On an input of length `n`, compute `g(n)` using its fixed constructibility witness. Parse a fixed-code/payload pair; malformed pairs get a fixed answer.
2. On a valid pair with code `α`, try budgets `s = 0,1,…,g(n)`, reusing the same banks. Run `SU` on the virtual input `pairEncode (Nat.bits s) (pairEncode α originalInput)`, but abort an attempt before a simulated work head of this **fixed `SU`** leaves `[-g(n),g(n)]`.
3. Suppress its output and retain only the finite summary needed to distinguish failure, success with original output `[true]`, and other successful outputs. On the first success, return the opposite of acceptance; if every attempt fails or is capped, return a fixed bit. Each uncapped attempt halts by S9, and there are finitely many attempts.
4. There is now a uniform space bound: `SU` has a fixed number of work tapes, each confined to a fixed window. Budget/input-address counters and bank resets use `O(g(n))` additional cells; virtual input avoids storing the length-`n` original input. This constant is independent of `α`. Canonization inside a call is capped too.
5. Suppose the resulting language had a decider in `SPACE f`. Put that decider into a **space-preserving** one-work-tape code form, with fixed code `α` and bound `c₀ f(n)`. Fix this code and increase only the payload length. Choose the domination constant `A = Cα(c₀+2)`. Since `logSpace n ≤ f(n)` and `1 ≤ f(n)`, eventually
   \[
   C_\alpha\bigl(c_0f(n)+\mathrm{logSpace}(n)+1\bigr)
   \le C_\alpha(c_0+2)f(n)\le g(n).
   \]
6. Therefore all calls up to budget `c₀ f(n)` fit the cap, and a successful call occurs by that budget. Every successful call reports the same deterministic decider output on the original input. The diagonal answer is its opposite, a contradiction.

The bounded interpreter, resetting within fixed banks, virtual-input adapter, and space-preserving normal form need explicit fill contracts. A time-only normal-form theorem is not a space ledger. Also, simply capping **one** call made with budget `g(n)` is insufficient: S9's bound for that call is proportional to `Cα g(n)`, even when the actual simulated machine uses much less. The increasing-budget repair resolves this particular interface problem. Computability of `f` is unused; its bundled logarithmic floor is used in step 5.

For S11, an explicit eventual bound is available. Fix `A ∈ ℕ`, set `K = max(4,2A)`, and take `n ≥ 2^K`. With `k = floor(log₂ n)`, one has `k ≥ K`, and

\[
n\ge 2^k\ge k^2\ge 2Ak\ge A(k+1)=A\,\mathrm{logSpace}(n).
\]

Here `2^k ≥ k²` follows from equality at `k = 4` and induction using `2k² ≥ (k+1)²` for `k ≥ 4`. This proves the required bound, even with `n` instead of `n+1`. Applying the hierarchy theorem and then the degree-one inclusion into `PSPACE` yields strict containment.

**8. Padding and games.** Use the concrete padding function

\[
x\longmapsto \mathrm{pairEncode}\bigl(x,\mathrm{replicate}((\operatorname{length}x)^2,\mathrm{true})\bigr).
\]

For `n = length x`, its output length is `m = n² + 2n + 2`, including at `n = 0`. The padded-language decider verifies this exact syntax/length, rejects other strings, and simulates the original quadratic-space decider on the first component. Its simulation uses `O(n²+1) ⊆ O(m+1)` space. Under `SPACE(n+1) = NP`, the padded language is in `NP`, and the polynomial-time padding reduction puts the original language in `NP = SPACE(n+1)`. This is the correct reduction direction: **unpadded language reduces to padded language**. Downward closure follows by composing the reduction with the bounded-certificate verifier and bounding its certificate polynomial at the polynomially bounded reduction output length.

For the hierarchy contradiction, when `n ≥ max(1,2A)`,

\[
A(n+1)\le 2An\le n^2\le n^2+1.
\]

Use constructibility of `n+1` and `n²+1` (the latter is attributed to the concurrent P4.2 layer; its source file is not attached, so its exact signature/import should be verified at fill time). There is no claim of either inclusion between `NP` and linear space.

For games, length induction gives `length(playOut s₁ s₂ n) = n`, so parity matches the stated convention. For fixed horizon `n`, define the Boolean position value `V(h)` to mean **player one** can force a win. At terminal histories it is `W(h)`; at even nonterminal histories it is the OR of the two child values, and at odd histories it is their AND. If the initial value is true, pick a true child at even nodes; if false, pick a false child at odd nodes. Finite Boolean case analysis suffices, so classical excluded middle and choice are permissible but not intrinsically needed for this restricted theorem. At `n = 0`, the two predicates reduce to `W [] = true` and `W [] = false` respectively. They cannot both hold: play their alleged winning strategies against each other. General game-tree encodings and treatment of draws remain outside the formal statement; assigning a draw to a player changes the winning condition of the original game.

## Adversarial instantiations and verification

| Test | Instance | Result |
|---|---|---|
| A1 | `decode []`, `decode [false]`, `decode [true]` | Pair parsing fails; all three decode to the true fallback and belong to `TQBF`. |
| A2 | `decode [false,true]` | Pair parsing succeeds with empty components; matrix parsing fails; the fallback matrix is true. |
| A3 | Empty-prefix encodings of `[]` and `[[]]` | Their bit strings are respectively `010` and `01100`; the first is in `TQBF`, the second is not. Thus accepting malformed strings does not trivialize the language. |
| A4 | Empty prefix with `m = [[(0,true)]]` | Matrix satisfiable, quantified truth false. Removing S1's coverage hypothesis is unsound. |
| A5 | Prefix of five existential quantifiers with `m = [[(0,true)]]` | True; four unused variables do not matter. Also tested empty matrices and empty clauses at zero prefix length. |
| A6 | Equality CNF on variables 0 and 1 | `∀x ∃y (x=y)` is true; `∃x ∀y (x=y)` is false, checking both quantifier polarity and index order. |
| A7 | `n = 0` game, separately `W [] = true` and false | Exactly the corresponding player's winning predicate holds; the lack of moves is handled correctly. |
| A8 | Codec with `n = s = 0`, all tapes blank, arbitrarily long output | Contradicts fixed-length injectivity; finding 1. The counterexample also works with zero work tapes. |
| A9 | Halted configuration versus distinct halted configuration | Exact-step adjacency must be equality, not arbitrary acceptance equivalence. This also independently forces codec injectivity. |
| A10 | One work tape, `s = 1`, positions `0 → 1 → 1`, then halt | Two visited cells while every head position remains in `[-1,1]`; the proposed window-only detector is insufficient. |
| A11 | One work tape, `s = 0`, immediate halt at the origin | The original run uses one cell and must trigger the universal failure clause. |
| A12 | Emit once, then loop forever at the same work position | The universal result must be exactly `[false]`; forwarding an output prefix during the probe makes this impossible. |
| A13 | Valid identity graph on codes `00,11`, invalid midpoint `01` | On-valid-pair correctness does not prevent a spurious two-step path through an invalid code. |
| A14 | `φ = List.replicate r []` | Literal count zero, serialized length `2r+1`; finding 8. |
| A15 | `f = g` with the constructibility floor | `A = 2` defeats the domination premise; strictness is not asserted for equal bounds. |
| A16 | Increasing padded aliases of one machine code | Effective-code laws give no bound on how the chosen `Cα` changes; padding the payload of one fixed code avoids that dependence. |

An independent Python transcription checked **14,353 encoding round trips**, **1,449 existential-prefix/satisfiability instances**, and **all 278 Boolean winner predicates for binary games of horizons 0 through 3** against strategy enumeration. All passed. The formula family contained all matrices with at most two clauses, each of width at most two, over variables 0 and 1; round-trip prefixes had lengths zero through four. The coverage tests and counterexamples above are mathematical arguments; these finite checks are supplementary and do not constitute Lean kernel certification.

## Source fidelity, attestations, and repair gate

I consulted the 2009 book text, including printed pp. 77, 79–85, 86–87, 92–94, through this [PDF copy of Arora–Barak](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press(2009).pdf). The comparisons are to the book itself, not answers on discussion sites. No separate reading of [SM73] or [SHL65] was required by the pack.

Definitions 4.9–4.10 and Theorem 4.13 support the hardness/completeness and QBF targets. Claim 4.4(2) covers arbitrary candidate bit strings; the attached guarded package does not. Theorem 4.8 has the little-oh hypothesis used here. Exercise 4.1 specifies successful simulation, whereas this contract also totalizes failure. Exercise 4.10 excludes draws, and Exercise 3.2 claims inequality without either inclusion. The source comparison does not cure the implementation-specific defects above.

The two declared codec weakenings—width `O(s+n)` and polynomial instead of linear formula size—are acceptable for polynomial-space hardness **after** the carrier, validity, and uniform-construction repairs. The other declared normalization choices are accounted for in the definition/statement reviews. The exact raw-output equality in S4 is an undeclared, fatal mismatch.

The source inventory is:

| Module | Definitions | Sorried statements |
|---|---:|---:|
| `Formulas/QBF` | 4 | 1 |
| `Formulas/QBFEncoding` | 4 | 1 |
| `ClassPSPACE/TQBF` | 3 | 5 |
| `ClassPSPACE/Games` | 3 | 1 |
| `ClassPSPACE` facade | 0 | 0 |
| `SpaceComplexity/Hierarchy` | 0 | 4 |
| `Formulas` facade | 0 | 0 |
| **Total** | **14** | **12** |

The supplied sweep lists all seven modules, starts with the advertised full commit, contains exactly 12 admission warnings at the expected declarations, contains zero `error:` lines, and ends with `P4.3_SWEEP_DONE`. The lint summaries report 0 FAIL / 0 WARN for the 5-file Formulas tree, 2-file ClassPSPACE tree, and 42-file SpaceComplexity tree. The attached Formulas facade now has its QBF imports before the module docstring and includes both Contents entries; the QBF sketch uses the corrected `Complexity.eval_congr_of_lt_numVars` reference. The historical changes from `572304e5`, actual exits, actual olean freshness, and root facade reachability were not independently established. Tactic proofs and the broader P4.2/routine layers were not re-audited.

To close this gate, re-audit the repaired codec carrier and both equality clauses, the actual uniform construction interface, its invalid-code treatment, and the corrected universal/hierarchy sketches. Recommended permanent sanity statements are: quantifier-bit inverse and encoding injectivity; truth of the empty prefix and covered existential prefixes; quotient-code round trip plus rejection/guarding of invalid codes; universal failure at zero budget and correct interval accounting; and game play length, zero-move outcomes, and mutual exclusion. None of the false raw-configuration claims should survive as a frozen fill target.

## Notation glossary

- `c_j`: the halted blank-work configuration with `j` false output bits used in the counterexample.
- `C`, `Cα`: respectively the codec constant and the universal-simulation constant for one fixed code `α`; subscripts here make the existing dependence explicit.
- `ℓ`: bit width of a repaired configuration-quotient encoding.
- `Valid`, `Next`, `Accept`: proposed predicates for valid encoded vertices, one-step adjacency, and accepting vertices.
- `ψ_i(a,b)`: proposed formula for reachability in at most `2^i` steps; `a,b,z,u,v` are `ℓ`-bit vertex blocks in that construction.
- `V(h)`: Boolean value meaning player one can force a win from history `h` at the fixed horizon.
- `A`, `K`, `k`: domination multiplier, the threshold `max(4,2A)`, and `floor(log₂ n)` in the explicit logarithmic calculation.
- `c₀`: a fixed space multiplier for the hypothetical coded decider in the hierarchy argument.
- `Q,R`: the two QBF structures in the injectivity argument. `ε`: a positive real tolerance in the little-oh equivalence. `Oα`: big-oh with constants allowed to depend on the fixed code `α`.
- `n,m`: original and padded input lengths in the padding argument; elsewhere `n,s` retain the pack's input-length and space-budget meanings. `r` counts repeated empty clauses. Other declaration names and symbols are those already used in the bundle.
```


## ===== audits/evidence/ch4-p43-r2-repairs.diff =====

```
diff --git a/TCSlib/Complexity/ClassPSPACE/Games.lean b/TCSlib/Complexity/ClassPSPACE/Games.lean
index 094b1bdf..310129d3 100644
--- a/TCSlib/Complexity/ClassPSPACE/Games.lean
+++ b/TCSlib/Complexity/ClassPSPACE/Games.lean
@@ -80,15 +80,17 @@ is determined — exactly one quantifier alternation wins, so in particular
 one of the players has a winning strategy.
 
 **Proof sketch.** Backward induction on the remaining plies, generalized
-over the history prefix: the position value
-`V h := "the mover from h can force a win for their side"` satisfies the
-alternating recursion `V h = ∃/∀ b, V (h ++ [b])` by ply parity, with the
-base `V` of complete histories read off `W`; classical excluded middle turns
-"not every move loses" into a winning move at each `∀`-node (the
-`Complexity.QBF.truthAux` recursion is the same shape, which is Example
-4.15's point). Assembling the per-position choices into whole strategies is
-the only bookkeeping: define `s₁` by choosing a winning move wherever `V`
-holds (classical choice), arbitrary elsewhere. Mutual exclusion (`¬(FirstWins
+over the history prefix: the position value is taken at the **fixed player-one
+perspective**, `V h := "player one can force W = true from h"` — a
+mover-relative value flips polarity with the turn and breaks the recursion
+(round-1 finding 9) — and satisfies `V h = ∃ b, V (h ++ [b])` at even
+histories, `V h = ∀ b, V (h ++ [b])` at odd ones, with the base read off `W`
+(the `Complexity.QBF.truthAux` recursion is the same shape, which is Example
+4.15's point). Strategy assembly covers both polarities: if `V []` holds,
+`s₁` picks a true-valued child at every even node it can reach; if not, `s₂`
+picks a false-valued child at every odd node — each extended arbitrarily off
+its winning tree. At fixed horizon the case analysis is finite, so classical
+instances are available but not essential. Mutual exclusion (`¬(FirstWins
 ∧ SecondWins)`) follows by playing the two winning strategies against each
 other — not claimed in this statement, which renders the exercise's "one of
 the two players has a winning strategy" disjunction. -/
diff --git a/TCSlib/Complexity/ClassPSPACE/TQBF.lean b/TCSlib/Complexity/ClassPSPACE/TQBF.lean
index 001c2e0a..61c2d946 100644
--- a/TCSlib/Complexity/ClassPSPACE/TQBF.lean
+++ b/TCSlib/Complexity/ClassPSPACE/TQBF.lean
@@ -24,21 +24,32 @@ adjacency-formula half of Claim 4.4(2), and the Stockmeyer-Meyer theorem that
 * **Def 4.9 verbatim over the campaign's `≤ₚ`** (`Complexity.PolyTimeReducible`,
   chapter 2); the logspace-reduction variant ([AB09, Exercise 4.9]) waits for
   phase P4.4's `≤ₗ`.
-* **Claim 4.4(2) at polynomial size, over a packaged codec.** The statement
-  supplies, for each machine: a configuration bit-codec (injective on the
-  space-`s` window, fixed length linear in `s + n`) **and** a CNF family of
-  size polynomial in `s + n` deciding adjacency of coded configuration pairs.
-  Two declared deviations from the book's Claim 4.4(2), both harmless to every
-  consumer: (i) the codec length is `O(s + n)` rather than `O(s)` — the input
-  head is carried on a one-hot track to keep adjacency *local* (the book's
-  `O(S)` presumes the binary head encoding of part 1, whose adjacency is not
-  local; Cook-Levin's marker discipline is the model); (ii) the CNF size is
-  bounded polynomially rather than linearly — Theorem 4.13's reduction only
-  needs the formula polynomial and emittable in polynomial time. The codec and
-  family are **existentially packaged** (the `exists_comp_partial` precedent
-  for guarded interfaces): their sole consumer is `TQBF`'s hardness fill;
-  D6-style promotion to named definitions is recorded for when a second
-  consumer appears (the phase-P4.4 `PATH` encoding is the candidate).
+* **Claim 4.4(2) at polynomial size, over a packaged quotient codec.** The
+  statement supplies, for each machine and each `(n, s)`: a configuration
+  bit-codec of fixed length linear in `s + n`, **factoring through the input
+  and the P4.2 vertex quotient** `Turing.NDTM.coreSum` — full configurations
+  are *not* injectively codable at fixed length, the output tape being
+  unbounded (round-1 blocker, finding 1) — together with **three** CNFs over
+  the code bits: a validity predicate characterizing exactly the codec image
+  (unguarded midpoint quantification admits paths through junk codes —
+  round-1 finding 3), the adjacency test (true on same-input windowed pairs
+  iff the step descends to the vertex quotient; false across distinct
+  inputs), and the acceptance test (halted state with `accept` summary).
+  Declared deviations from the book's Claim 4.4(2), each argued harmless to
+  Theorem 4.13: (i) the codec length is `O(s + n)` rather than `O(s)` — the
+  code carries the **input content** and a one-hot input-position track, so
+  every check is *local* and the formulas are input-independent (Cook-Levin's
+  marker discipline; round-1 finding 7); (ii) the CNF sizes are bounded
+  through their **serialized lengths** — polynomial, not linear; a
+  literal-occurrence count alone misses empty clauses (round-1 finding 8);
+  (iii) adjacency compares `coreSum (step c)` with `coreSum d`, so halted
+  vertices are self-adjacent and live ones are not — the ψ-recursion's base
+  case supplies `a = b` separately (round-1 finding 6). **The package is
+  existence, not an algorithm** (round-1 major 2): the uniform
+  polynomial-time emitter of the three formulas is a private, named fill
+  obligation of `TQBF`'s hardness proof, never a claim of this statement.
+  Sole consumer unchanged; D6-style promotion recorded for a second consumer
+  (the phase-P4.4 `PATH` encoding remains the candidate).
 * **The facade discipline**: `ClassPSPACE.lean` is this phase's own new
   facade; nothing frozen is touched.
 
@@ -52,7 +63,7 @@ adjacency-formula half of Claim 4.4(2), and the Stockmeyer-Meyer theorem that
 
 * `Complexity.PSPACE_eq_P_of_pspaceComplete_mem_P` — a `PSPACE`-complete
   language in `P` collapses `PSPACE` to `P`. [AB09, §4.2, after Definition 4.9]
-* `Complexity.exists_adjacency_codec_cnf` — Claim 4.4(2), packaged form.
+* `Complexity.exists_adjacency_codec_cnf` — Claim 4.4(2), packaged quotient form.
 * `Complexity.TQBF_mem_PSPACE` — [AB09, Theorem 4.13, membership half].
 * `Complexity.TQBF_PSPACEHard` — [AB09, Theorem 4.13, hardness half]; a fill
   summit (the `ψᵢ` emitter).
@@ -67,6 +78,20 @@ adjacency-formula half of Claim 4.4(2), and the Stockmeyer-Meyer theorem that
   STOC 1973. (Cited through [AB09]; no external text required.)
 -/
 
+namespace Turing
+
+/-- A configuration lies **in the radius-`s` window** when every work head
+sits within `[-s, s]` and every work cell outside `[-s, s]` is blank — the
+side condition under which the packaged codec of
+`Complexity.exists_adjacency_codec_cnf` is faithful. (The input head needs no
+clause: its type bounds it.) -/
+def Cfg.InWindow {k : ℕ} {Symbol State : Type} {x : List Symbol} (s : ℕ)
+    (c : Cfg k Symbol State x) : Prop :=
+  (∀ i, |c.workTapePos i| ≤ (s : ℤ)) ∧
+  ∀ (i : Fin k) (z : ℤ), (s : ℤ) < |z| → c.workTapes i z = none
+
+end Turing
+
 namespace Complexity
 
 open Std.Sat (CNF)
@@ -94,48 +119,79 @@ theorem PSPACE_eq_P_of_pspaceComplete_mem_P {L' : Language Bool}
     (h : PSPACEComplete L') (hP : L' ∈ P) : PSPACE = P := by
   sorry
 
-/-- **Claim 4.4(2), packaged form** (spec, fill pending — phase P4.3; see the
-module docstring's two declared deviations): for every machine there are a
-constant `C`, a configuration bit-codec — fixed length `C · (s + n + 1)`,
-injective on the configurations whose heads and nonblank cells lie in the
-window `[-s, s]` — and a CNF family of size at most `C · (s + n + 1) ^ C`
-over variables below twice the code length, such that evaluating the formula
-on the concatenated codes of two windowed configurations decides exactly
-whether the second is the step of the first.
+/-- **Claim 4.4(2), packaged quotient form** (spec, fill pending — phase
+P4.3 round 2; see the module docstring's declared deviations): for every
+machine there is a constant `C` such that for all `(n, s)` there are a
+configuration bit-codec — fixed length `C · (s + n + 1)`, injective **down to
+the input and the vertex quotient** `Turing.NDTM.coreSum` on windowed
+configurations — and three CNFs: `φv` characterizing exactly the codec image
+among the length-matching strings, `φa` deciding adjacency (the step, read on
+the vertex quotient) on same-input windowed pairs and rejecting cross-input
+pairs, and `φacc` deciding acceptance (halted state, `accept` summary); all
+three with `numVars` inside the code width and serialized lengths bounded by
+`C · (s + n + 1) ^ C`.
 
 **Proof sketch.** The codec is the marker discipline of the Cook-Levin
-tableau row (`TCSlib.Complexity.CookLevin` precedents): a one-hot state
-block, a one-hot input-position track of length `n + 2`, and per work tape a
-window track of `2s + 1` cells, each cell three-valued symbol plus a
-head-marker bit — total length linear in `s + n` with the machine's
-constants in `C`; injectivity on the window mirrors
-`Turing.MultiTapeTM.ConfigCount.coreCode_inj`. Adjacency is a conjunction of
-local checks — unmarked cells copy, the marked cell and its two neighbors
-update by the transition table, the one-hot tracks shift by at most one, the
-state block rewrites per the table — each over a constant number of bits per
-machine, hence a constant-size CNF per position by the chapter-2 CNF
-universality (`Complexity.exists_cnf_boolFun`); summing over `O(s + n)`
-positions gives the polynomial (indeed linear, but only the polynomial is
-claimed) size. Fill obligations: the codec definition and its injectivity;
-the per-position check enumeration; the size ledger; the final eval-iff-step
-equivalence. -/
+tableau row (`TCSlib.Complexity.CookLevin` precedents), now carrying the
+input: an input-content track of `n` bits, a one-hot input-position track of
+length `n + 2`, a one-hot state block (halt included), per work tape a window
+track of `2s + 1` cells — three-valued symbol plus a head-marker bit — and a
+two-bit summary block; total length linear in `s + n` with the machine's
+constants in `C`, padded to the exact `C · (s + n + 1)`. Injectivity to
+`(x, coreSum)` mirrors `Turing.MultiTapeTM.ConfigCount.coreCode_inj` on the
+window tracks plus the content track; the output enters only through the
+summary block (full-output injectivity is impossible and not claimed —
+round-1 finding 1). `φv` conjoins per-track well-formedness (one-hot blocks,
+trit ranges, canonical padding); `φacc` reads the halt pattern and the
+summary block; `φa` conjoins content-track equality, locality of unmarked
+window cells, the marked-cell and neighbor updates by the transition table —
+the scanned input bit read from the content track under the position
+marker — the one-hot shifts by at most one, the state rewrite, and the
+summary update (`Turing.outSummary`'s append table): each check spans a
+constant number of bits per machine, a constant-size CNF per position by the
+chapter-2 universality (`Complexity.exists_cnf_boolFun`, applied per
+**gate**, never per row — a whole-row truth table is exponential); summing
+over `O(s + n)` positions bounds clause count, `numVars`, and the serialized
+lengths polynomially (the chapter-2 grammar's serialization-length equation —
+clause count enters it explicitly, round-1 finding 8). Fill obligations,
+named: the codec definition with exact-length padding; the two injectivity
+lemmas; the validity characterization in both directions; the per-position
+check enumeration; the three serialized-size ledgers; the
+step-iff-adjacency equivalence through `Turing.NDTM.coreSum_stepWith`. -/
 theorem exists_adjacency_codec_cnf (M : Turing.FinTM Bool) :
     ∃ C : ℕ, 0 < C ∧ ∀ (n s : ℕ),
       ∃ (code : (x : List Bool) → Cfg M.k Bool M.State x → List Bool)
-        (φ : CNF ℕ),
+        (φv φa φacc : CNF ℕ),
         (∀ (x : List Bool) (c : Cfg M.k Bool M.State x),
           (code x c).length = C * (s + n + 1)) ∧
-        (∀ (x : List Bool), x.length = n → ∀ c d : Cfg M.k Bool M.State x,
-          (∀ i, |c.workTapePos i| ≤ (s : ℤ)) →
-          (∀ i, |d.workTapePos i| ≤ (s : ℤ)) →
-          (∀ i (z : ℤ), (s : ℤ) < |z| → c.workTapes i z = none) →
-          (∀ i (z : ℤ), (s : ℤ) < |z| → d.workTapes i z = none) →
-          (code x c = code x d → c = d) ∧
-          (φ.eval (fun v =>
-              ((code x c ++ code x d).getD v false)) = true ↔
-            M.tm.step c = d)) ∧
-        φ.numVars ≤ 2 * (C * (s + n + 1)) ∧
-        (φ.map List.length).sum ≤ C * (s + n + 1) ^ C := by
+        (∀ (x x' : List Bool), x.length = n → x'.length = n →
+          ∀ (c : Cfg M.k Bool M.State x) (c' : Cfg M.k Bool M.State x'),
+            c.InWindow s → c'.InWindow s → code x c = code x' c' → x = x') ∧
+        (∀ (x : List Bool), x.length = n →
+          ∀ c d : Cfg M.k Bool M.State x, c.InWindow s → d.InWindow s →
+            code x c = code x d → NDTM.coreSum c = NDTM.coreSum d) ∧
+        (∀ w : List Bool, w.length = C * (s + n + 1) →
+          (φv.eval (fun v => w.getD v false) = true ↔
+            ∃ (x : List Bool), x.length = n ∧
+              ∃ c : Cfg M.k Bool M.State x, c.InWindow s ∧ w = code x c)) ∧
+        (∀ (x : List Bool), x.length = n →
+          ∀ c d : Cfg M.k Bool M.State x, c.InWindow s → d.InWindow s →
+            (φa.eval (fun v => (code x c ++ code x d).getD v false) = true ↔
+              NDTM.coreSum (M.tm.step c) = NDTM.coreSum d)) ∧
+        (∀ (x x' : List Bool), x.length = n → x'.length = n → x ≠ x' →
+          ∀ (c : Cfg M.k Bool M.State x) (c' : Cfg M.k Bool M.State x'),
+            c.InWindow s → c'.InWindow s →
+            φa.eval (fun v => (code x c ++ code x' c').getD v false) = false) ∧
+        (∀ (x : List Bool), x.length = n →
+          ∀ c : Cfg M.k Bool M.State x, c.InWindow s →
+            (φacc.eval (fun v => (code x c).getD v false) = true ↔
+              (c.state = none ∧ outSummary c.output = OutSummary.accept))) ∧
+        φv.numVars ≤ C * (s + n + 1) ∧
+        φacc.numVars ≤ C * (s + n + 1) ∧
+        φa.numVars ≤ 2 * (C * (s + n + 1)) ∧
+        (CNF.serialize φv).length ≤ C * (s + n + 1) ^ C ∧
+        (CNF.serialize φa).length ≤ C * (s + n + 1) ^ C ∧
+        (CNF.serialize φacc).length ≤ C * (s + n + 1) ^ C := by
   sorry
 
 /-- **The language `TQBF`** [AB09, §4.2]: binary strings whose decoded
@@ -148,12 +204,16 @@ def TQBF : Language Bool :=
 /-- **`TQBF ∈ PSPACE`** ([AB09, Theorem 4.13, membership half]; spec, fill
 pending): truth of a quantified formula is decidable in polynomial space.
 
-**Proof sketch.** The recursive evaluator `A` of [AB09]: peel the first
-quantifier, evaluate both restrictions, combine by the quantifier — realized
-iteratively with a partial-assignment word of one trit per prefix variable
-(the book's footnote: the linear-space global-array variant) walked
-depth-first by the loop combinator; the base case evaluates the CNF matrix
-under the assembled assignment by one scan per clause. Space: the assignment
+**Proof sketch.** Validate the **entire** encoding before any matrix
+verdict: trailing garbage makes the total decoder select the true fallback,
+so a scanned prefix that "looks unsatisfiable" must not short-circuit
+(round-1 answer 5). Then the recursive evaluator `A` of [AB09]: peel the
+first quantifier, evaluate both restrictions, combine by the quantifier —
+realized iteratively with a partial-assignment word of one trit per prefix
+variable (the book's footnote: the linear-space global-array variant) walked
+depth-first by the loop combinator, with no per-level formula copies; the
+base case evaluates the CNF matrix under the assembled assignment by one
+scan per clause, re-reading prefix bits and matrix bytes from the input. Space: the assignment
 word (linear), the matrix cursor (linear), the recursion is depth-first on
 the word in place — `O(n)` cells, inside `SPACE (n + 1) ⊆ PSPACE`. Fill
 obligations, named: the depth-first assignment walker (a §12 loop/catalog
@@ -167,28 +227,46 @@ theorem TQBF_mem_PSPACE : TQBF ∈ PSPACE := by
 fill pending — **the phase-P4.3 fill summit**, the `ψᵢ` emitter).
 
 **Proof sketch.** Let `L ∈ PSPACE`, decided by `M` in space `c₀ · (n^c + 1)`.
-On input `x` (length `n`, space budget `s := c₀·(n^c + 1)`), the reduction
-emits a quantified formula asserting "some accepting configuration is
-reachable from the initial one within `2^m` steps", `m := ⌈log₂⌉` of the
-configuration count (`O(s + n)` by the codec of
-`Complexity.exists_adjacency_codec_cnf`): the midpoint recursion
-`ψᵢ(C, C') = ∃ C'' ∀ D₁ D₂ ((D₁,D₂) = (C,C'') ∨ (D₁,D₂) = (C'',C')) → ψᵢ₋₁(D₁,D₂)`
-([AB09]'s succinct form, with the `∀`-trick keeping one copy of `ψᵢ₋₁`),
-unfolded `m` times down to `ψ₀ :=` the adjacency CNF `φ` of the packaged
-claim — all equality/disjunction scaffolding converted to CNF clauses via the
-chapter-2 universality, with fresh auxiliary variables per level (the Tseitin
-step the CH34-Q5 decision pays here). Size: `O(m)` levels of `O(s + n)`-bit
-blocks plus one `φ`, polynomial; truth iff `M` accepts `x` iff `x ∈ L`
-(the graph dictionary `Turing.NDTM.reflTransGen_cfgStep_iff` through
-`Turing.MultiTapeTM.toNDTM`, with the halting normalization absorbed into
-the accepting-configuration predicate — erase-work-tapes normalization per
-[AB09], the received `cleanTM` precedent). The emitting machine is a
-chapter-2-style streaming emitter (`CookLevin/Hardness.lean` discipline, the
-six-stage output-silence contract; §12 catalog routines); **continuation
-budget certain**. Fill obligations, named: the level emitter and its
-serialization-length ledger; the variable-indexing scheme (level-blocked,
-unary-serialized per the CNF grammar); the truth-preservation induction
-`ψᵢ true ↔ reachability within 2^i`; the final assembly through
+On input `x` (length `n`, window radius `s := c₀·(n^c + 1)`), the reduction
+emits a quantified formula asserting "some accepting vertex is reachable
+from the initial vertex within `2^ℓ` steps" over the packaged carrier of
+`Complexity.exists_adjacency_codec_cnf`: vertices are the
+`ℓ := C·(s + n + 1)`-bit codes of input-carrying windowed quotient
+configurations, with `Valid := φv`, `Next := φa`, `Accept := φacc`. The
+midpoint recursion is
+`ψ₀(a, b) := Valid a ∧ Valid b ∧ (a = b ∨ Next (a, b))` — the base includes
+length-zero paths, since live vertices are not `Next`-reflexive (round-1
+finding 6) — and
+`ψᵢ₊₁(a, b) := ∃ z (Valid z ∧ ∀ u v, ((u,v) = (a,z) ∨ (u,v) = (z,b)) → ψᵢ(u,v))`
+([AB09]'s succinct `∀`-trick keeping one copy of `ψᵢ`, with the midpoint
+**guarded by `Valid`** — unguarded quantification admits paths through junk
+codes, round-1 finding 3), unfolded to depth `ℓ` (at most `2^ℓ` codes, so a
+shortest path fits), against the emitted initial-vertex code and an
+existentially quantified `Accept` target (no unique accepting configuration
+is needed). Prenex first, then Tseitin: the gate variables of the CNF
+conversion are existentially quantified **after** the original prefix — gate
+values must not be fixed before universal variables they depend on (round-1
+answer 5) — with constant-arity gate constraints via the chapter-2
+universality (`Complexity.exists_cnf_boolFun` per gate, never per level).
+Size: `O(ℓ)` scaffolding per level over `ℓ` levels plus the three packaged
+CNFs — polynomial by their serialized-length clauses. Truth iff reachability
+iff `M` accepts `x`: the quotient dictionary
+(`Turing.NDTM.reflTransGen_cfgStep_iff` through `Turing.MultiTapeTM.toNDTM`)
+with path lifting via `Turing.NDTM.coreSum_stepWith`, the space bound
+keeping every genuine run inside the window. **The packaged existential
+supplies no algorithm** (round-1 major 2): the uniform emitter — the
+polynomial-time construction and serialization of `φv`/`φa`/`φacc`, the
+initial-vertex code, the per-level scaffolding with its level-blocked
+variable indexing, and the final assembly through
+`Complexity.QBF.decode_encode` — is a set of **private, named fill
+obligations of this proof**, in the chapter-2 streaming-emitter discipline
+(`CookLevin/Hardness.lean`, the six-stage output-silence contract; §12
+catalog routines); **continuation budget certain**. Fill obligations, named:
+the three-CNF emitter family and its serialization-length ledger; the
+initial-code computation; the level-blocked indexing scheme (unary-serialized
+per the CNF grammar); the truth-preservation induction
+`ψᵢ ↔ reachability within 2^i`, both directions of the guarded recursion;
+the Tseitin-after-prefix equivalence; the final assembly through
 `Complexity.QBF.decode_encode`. -/
 theorem TQBF_PSPACEHard : PSPACEHard TQBF := by
   sorry
diff --git a/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean b/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
index eca62a0a..0d778a03 100644
--- a/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
+++ b/TCSlib/Complexity/SpaceComplexity/Hierarchy.lean
@@ -40,8 +40,8 @@ positive normalization per the P0 convention —
   `S(n) > log n` convention.
 * **Both bounds space-constructible**, as in the book; constructibility of
   `g` drives the budget computation and the clock, constructibility of `f`
-  is carried for fidelity (the proof uses only `g`'s — recorded in the
-  sketch, seeded to the audit).
+  is carried for fidelity (the proof uses only `g`'s witness and `f`'s
+  bundled `logSpace` floor — round-1 confirmed, recorded in the sketch).
 * Facade wiring: root-wired while the P4.1 gate was live; the
   `SpaceComplexity.lean` facade has carried this module since that gate
   closed.
@@ -75,21 +75,35 @@ logarithmic addend; the time is existential, as
 `Turing.FinTM.ComputesInTime`'s halting demands, with no stated bound).
 
 **Proof sketch.** The interpreter of the chapter-1 `universal` machine
-(table capture, virtual input, one simulated work tape held on one real
-tape) is already constant-factor in *space*: the simulated tape occupies
-one bank of at most `s` cells plus markers, the captured table and state
-word are `O(|α|) ≤ C` cells, and the virtual-input discipline reads `x`
-from the real input tape without copying. Non-halting-within-space is
-detected by the configuration-count clock: a binary step counter of
-`log₂ (configBound) = O(s + logSpace n)` bits (the
-`Turing.MultiTapeTM.ConfigCount` arithmetic as in
-`ComputesInTime.of_spaceUsed_le`), decremented per simulated step; window
-overflow (the simulated head leaving `[-s, s]`) and counter exhaustion both
-produce the `[false]` clause. Fill obligations, named: the space ledger of
-the interpreter's banks (a §12 R1/R3 consumer — bank embedding and the
-catalog space rows); the clock machine (`incrementTM` discipline at width
-`O(s + logSpace n)`); the overflow detector; the two-clause assembly
-mirroring `Turing.timed_universal`'s packaging. -/
+(table capture, virtual input, the simulated work tape held on one real
+bank) is constant-factor in *space*; the budget test and the output contract
+need care (round-1 finding 4). (i) **Space is tested as visited-interval
+cardinality, not window membership**: maintain the simulated head's minimum
+and maximum positions — both start at `0`, so one cell is visited
+immediately, and at `s = 0` the failure clause fires on every input; unit
+moves make `max − min + 1` exactly the visited count, checked **including
+the final configuration**, with `max − min + 1 > s` rejecting (head
+membership in `[-s, s]` does not count cells: visiting `0` then `1` uses two
+cells inside `[-1, 1]`). (ii) **Non-halting-within-space is detected by the
+core-count clock**: a binary counter of `O_α(s + logSpace n)` bits bounding
+`(|Q|+1)·(n+2)·3^{2s+1}·(2s+1)` — a deterministic run repeating a live core
+inside the window is periodic forever, so no first halt occurs after an
+undetected repeat; outputs never enter the argument, cores excluding the
+output tape (the `Turing.MultiTapeTM.ConfigCount` arithmetic as in
+`ComputesInTime.of_spaceUsed_le`). (iii) **Probe silently, then replay**:
+streamed output cannot be retracted when a later overflow or clock
+exhaustion must yield exactly `[false]`, so the first pass runs with output
+captured (W1); on success the machine resets the simulated banks, emits
+`true`, and replays the run forwarding output — fixed banks reused between
+the passes. (iv) The canonizer cost is a **finite code-dependent constant**
+absorbed into `C` (the effective scheme supplies no bound linear in the code
+length, and none is claimed). The `+ logSpace n` addend pays for the clock's
+input-position factor under this construction — no lower-bound claim against
+other universal simulations — and is absorbed under the standing
+`s ≥ logSpace n` convention (`s + logSpace n + 1 ≤ 3s`). Fill obligations,
+named: the interval counters with the final-configuration check; the
+core-count clock at the stated width; the probe/replay two-pass assembly
+over fixed banks (a §12 R1/R3 consumer); the per-code constant ledger. -/
 theorem space_universal :
     ∃ SU : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
       ∀ (s : ℕ) (x : List Bool),
@@ -131,22 +145,38 @@ floor, so the P0 zero-bound convention needs no side condition.
 
 **Proof sketch.** The diagonal language of the padded-code discipline
 (`TCSlib.Complexity.TimeHierarchy.CodePrefix`'s `preTM`/`scanPre`
-self-application, exactly as the received time hierarchy): on input
-`pairEncode α w`, compute the budget `g(n)` bits by `g`'s constructibility
-witness (space `O(g n)`), run `Complexity.space_universal`'s interpreter on
-the self-applied input at window budget proportional to `g n`, and flip the
-answer; the flip is total because the universal's second clause answers
-`[false]` on window or clock overflow. `D ∈ SPACE g` by the universal's
-`C · (g n + logSpace n + 1)` bound and the floor `logSpace ≤ g`. If
-`D ∈ SPACE f` via machine `M` with constant `c₀`, normal-form and code `M`
-(the scheme's canonization), pad to a code string `α_M` long enough that
-`C_M · (c₀ · f n + logSpace n + 1) ≤ g n` at the diagonal length — the
-eventual-domination hypothesis instantiated at the constant assembled from
-`C_M`, `c₀`, and the floor — and the flipped verdict contradicts `M`'s on
-that input, both runs fitting inside the simulated window. Fill
-obligations, named: the budget computation and window wiring; the
-self-application assembly (`scanPre_pairEncode_append` precedent); the
-contradiction arithmetic; `D`'s `DecidesInSpace` packaging. -/
+self-application), with a **capped increasing-budget loop** that removes the
+per-code constant from the space ledger (round-1 finding 5: `∀ α, ∃ Cα`
+gives no uniform `O(g)` bound when the code is read off the input, and
+padding a code can change its constant): on input `pairEncode α w`, `D`
+(i) computes `g n` by `g`'s constructibility witness (space `O(g n)`);
+(ii) tries budgets `s = 0, 1, …, g n`, reusing fixed banks, running
+`Complexity.space_universal`'s machine on the self-applied virtual input at
+budget `s` while **hard-capping the fixed universal's own work heads**
+inside `[-g n, g n]` — a cap depending only on that machine's fixed tape
+count, hence uniform in `α`; capped or failed attempts advance the budget;
+(iii) answers the **opposite** of the first successful attempt's verdict,
+retaining only a three-valued attempt summary (failure, success with
+`[true]`, success otherwise; output suppressed, W1), and a fixed answer if
+every attempt caps out. `D ∈ SPACE g`: the universal's fixed tapes confined
+to the cap, the budget and address counters, and the bank resets are
+`O(g n)` cells, uniformly in the input's code part. If `D ∈ SPACE f` via
+machine `M` with constant `c₀`: put `M` into a **space-preserving
+one-work-tape coded normal form** — a named fill obligation; the chapter-1
+time-only normal form is not a space ledger — with fixed code `α_M`, and pad
+the **payload**, never the code (the `CodePrefix` discipline keeps one code
+fixed so a single constant `C_{α_M}` applies). By the eventual-domination
+hypothesis at the assembled constant `A := C_{α_M} · (c₀ + 2)`, using the
+bundled floors `logSpace n ≤ f n` and `1 ≤ f n`,
+`C_{α_M}·(c₀·f n + logSpace n + 1) ≤ C_{α_M}·(c₀ + 2)·f n ≤ g n` eventually,
+so some attempt at budget at most `c₀ · f n` succeeds within every cap, and
+every successful attempt reports `M`'s deterministic verdict on the
+self-applied input — which `D` flips: contradiction. Constructibility of `f`
+contributes only its bundled floor. Fill obligations, named: the budget loop
+with fixed-bank resets and the uniform cap; the attempt-summary discipline;
+the space-preserving normal form; the self-application assembly
+(`scanPre_pairEncode_append` precedent); the contradiction arithmetic;
+`D`'s `DecidesInSpace` packaging. -/
 theorem space_hierarchy (f g : ℕ → ℕ) (hf : SpaceConstructible f)
     (hg : SpaceConstructible g)
     (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) :
@@ -177,11 +207,15 @@ under `≤ₚ` (the chapter-2 bounded-certificate transport — a derived
 obligation from `Complexity.mem_NP_iff_exists_length_le`, Exercise 2.1's
 bounded form, named for the brief). Padding transfers space bounds down:
 for `L ∈ SPACE (n² + 1)`, the padded language
-`L' := {x ++ 1^(|x|²) markers}` lies in `SPACE (m + 1)` in the padded
-length `m` (run the `L`-decider on the unpadded prefix; the pad supplies
-the room — the chapter-2 padding-cluster discipline, `EXP_subset_NEXP`'s
-precedent), so `L' ∈ NP` by the assumption, and `L ≤ₚ L'` by the padding
-reduction (a `polyUnary` emitter), so `L ∈ NP = SPACE (n + 1)`. Hence
+`L' := {pairEncode x (List.replicate (|x|²) true)}` — padded length exactly
+`m = n² + 2n + 2`, syntax validated — lies in `SPACE (m + 1)` in the padded
+length (validate, then run the `L`-decider on the first component; the pad
+supplies the room — the chapter-2 padding-cluster discipline,
+`EXP_subset_NEXP`'s precedent), so `L' ∈ NP` by the assumption, and
+`L ≤ₚ L'` by the padding reduction (a `polyUnary` emitter; the **unpadded**
+language reduces to the **padded** one), so `L ∈ NP = SPACE (n + 1)` — the
+`NP` pullback composing the reduction with the bounded-certificate verifier
+at the reduction's polynomial output length. Hence
 `SPACE (n² + 1) ⊆ SPACE (n + 1)`, contradicting
 `Complexity.space_hierarchy` at the constructible pair
 (`Complexity.spaceConstructible_linear`,
```


## ===== audits/ch4-p42-resolutions.md =====

```
# Chapter 4, phase P4.2 (configuration graphs and Savitch) — audit loop resolutions

**Gate: CLOSED (round 1, 2026-10-08).** One round: **PASS — 0 blockers,
0 majors, 5 minors, 3 notes** (`audits/ch4-p42-findings.md`, verbatim). All 5
definitions blind-restated clean; all 10 sorried statements accepted with
independent derivations — including the exact three-class minimality proof
for the `OutSummary` quotient, the full splice/pad argument with the window
side condition made explicit, the complete exponent ledger for the
exponential-time simulation (vertex count, constructor cost through the
received deterministic count theorem, and sequential-access table
accounting), the base-case-corrected midpoint recurrence for Savitch, and
both constant absorptions of `PSPACE_eq_NPSPACE` with explicit multipliers.
The bundle hash was independently recomputed; 15 adversarial instantiations
ran, including a 12,645-case finite model of the append-summary table.

## Minors, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| 1 | `acceptsWithin_of_spaceUsedWith_le`'s sketch no longer asserts that padded **siblings** stay halted (the statement has no sibling-halting hypothesis — the auditor's two-choice counterexample has a live all-`true` branch): it is the accepting branch that stays halted under padding, and nothing else is needed |
| 2 | `polyTimeReducible_of_mem_NL`'s docstring now records the **textbook erratum** explicitly: Exercise 4.3's printed wording says "complete for `NL`", which is false for arbitrary nontrivial targets (an undecidable target defeats completeness); the theorem claims hardness, and completeness additionally requires `L ∈ NL` |
| 3 | `configBound`'s docstring cites the received deterministic count by its real name, `Turing.FinTM.configBound` (not `Turing.MultiTapeTM.ConfigCount.configBound`) |
| 4 | `NL_subset_P`'s sketch no longer calls the received `LOGSPACE_subset_P` "the deterministic special case of the same search": that proof keeps the original machine and bounds its halting time through `ComputesInSpace`, building no search or table — the shared ingredient is the count arithmetic |
| 5 | `NSPACE_subset_exp_dtime`'s prose no longer claims the `+ 1` "keeps the exponent positive" (the `c = 0` component has exponent `0`): the time bound is everywhere positive regardless, and the `+ 1`'s job is the input-head absorption |

Re-verification: `ConfigGraph` and `Savitch` re-elaborate with zero errors
(10 `sorry` warnings exactly); the pack's question 3 carried the same
sibling-halting slip as the sketch — a **pack erratum, acknowledged here**
(shipped packs are never edited).

## Notes (dispositions recorded)

* **Note 6 (carrier bridge)**: `CfgStep` relates full configurations while
  the counting lives on windowed summary vertices. Carried verbatim into the
  fill briefs: canonical decoding, outside-window edge rejection, quotient
  path lifting from the true initial configuration, enumeration of accepting
  vertices (no unique-target assumption), and the reflexive base case of
  bounded reachability.
* **Note 7 (resource ledgers)**: the constructor's exponential **time** bound
  flows through the received `Turing.FinTM.ComputesInTime.of_spaceUsed_le`
  (not circular — deterministic, received); Savitch's frames must reuse
  **fixed physical tape intervals** under the visited-cell measure; the
  polynomial constructor must emit exactly `(n^c + 1).bits`, including the
  final `+ 1` and the `n = 0` case. All carried into the fill briefs.
* **Note 8 (attestation posture)**: revision identity, the prose-only
  landing comparison, and olean freshness remain maintainer attestations;
  recorded, no action.
* **Cross-filed from concurrent rounds**: the P4.3 round's note 10 and the
  P4.4 round's note 7 both examined this phase's `coreSum`/`CfgStep`
  declarations and found no defect, flagging only the carrier-bridge
  distinction already carried as note 6 here. The P4.3 round's blocker is a
  P4.3-side misuse of the finite-counting idea (full-configuration codec),
  not an inherited defect of this surface.
* **Auditor-supplied constructions banked for fill**: the sequential-access
  BFS ledger (no unit-cost lookup assumed), the min/max-interval overflow
  observation, the `2a ≤ a² + 1` absorption chain, and the suggested additive
  sanity lemmas (`outSummary` append table, iterated `coreSum_stepWith`,
  `¬ AcceptsWithin x 0`, tape-count lower bound, bounded-code lifting).

## Consequences

* The `SpaceComplexity` surface of this phase is **closed**; the P4.4 gate
  (closed the same day) consumes it, and the open P4.3 repair round re-states
  its codec over this phase's `coreSum` quotient exactly as this round's
  design intended.
* Statement-freeze baseline for the closed surface: the closing commit
  (minors are docstring/sketch prose only; no declaration changed).
```


## ===== audits/ch4-p41-resolutions.md =====

```
# Chapter 4, phase P4.1 (space classes) — audit loop resolutions

**Gate: CLOSED (round 1, 2026-10-08).** One round: **PASS — 0 blockers,
0 majors, 5 minors, 4 notes** (`audits/ch4-p41-findings.md`, verbatim). All 10
definitions blind-restated clean; all 14 sorried statements accepted with
independent derivations (including the König's-lemma argument that the
per-input budget existential adds no uniformity restriction, and the full
fixed-window ledger for `NP ⊆ PSPACE`); the commit comparison between landing
and audited revisions independently pinned.

## Minors, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| 1 | `spaceConstructible_logSpace`'s sketch now states the bits-length identity for positive inputs only (`Nat.bits 0 = []`), special-cases the empty input to emit `[true]`, and bounds the counters by `A·(logSpace n + 1)` before absorbing |
| 2 | `spaceConstructible_linear`'s sketch initializes the counter at `1` (an uncorrected length counter emits the wrong word), includes width and boundary cells in the ledger, and the docstring now describes the `+ 1` as preventing the inherited collapse rather than "avoiding a vacuous zero bound" |
| 3 | The `Constructible.lean` module docstring no longer claims the exact-space variant is refuted by the chapter-1 exact-time argument (a space deadline forces no premature halt); constant slack is described as implementing the book's own asymptotic convention |
| 4 | `evenLang_mem_LOGSPACE`'s sketch keeps the **direct** proof route and records why: deriving it from `ZeroSpace`'s zero-tape witness would invert the existing `ZeroSpace → Examples` import (the pack's deviation-8 suggestion was cycle-inducing — a pack erratum, acknowledged below) |
| 5 | Pack erratum, acknowledged here (shipped packs are never edited): the inventory undercounted the definitions (10, not "2 + 6"), did not declare the proved `visitedWith_nil` as skeleton-time surface, and omitted three referenced attachments (the P0 resolutions, `audits/TEMPLATE.md`, `ClassNP/NTIME.lean`), which the auditor recovered at the exact commit. Future manifests: count declarations programmatically (the standing pack-erratum lesson) |

Re-verification: `Constructible`, `Examples`, `Inclusions` re-elaborate with
zero errors; `SpaceComplexity` lint 0 FAIL / 0 WARN (42 files).

## Notes (dispositions recorded)

* **Note 6**: the `NSPACE` zero-bound collapse is inherited and contained by
  the normalized classes; the `NSPACE` sanity twins (tape-count bound,
  collapse, normalization identities — the auditor supplied the derivations)
  are recorded as a **future additive sanity layer**, alongside a local
  mention in the `NSPACE` documentation, scheduled with the fills.
* **Note 7**: the exact-length quantifier is sound; the **short-prefix
  argument** (not just post-halt invariance) goes into the
  `spaceUsedWith_append_of_halt` fill; no equivalence with the book's
  non-halting convention is advertised for unqualified bounds.
* **Note 8**: `NP_subset_PSPACE`'s fill has a **hard dependency** on
  space-preserving bank-embedding/seam/reset contracts (§12 R1/R2/R3) or a
  separately proved direct simulation; the five host obligations of the
  report's question 5 are carried into the fill brief verbatim.
* **Note 9**: `SAT3_mem_PSPACE`'s docstring now states its delivered
  (polynomial, not linear) strength.

## Consequences

1. **The `SpaceComplexity.lean` facade is unfrozen**: the phase-P4.2/P4.3/
   P4.4 modules (`ConfigGraph`, `Savitch`, `Hierarchy`, `Logspace/*`) are now
   wired through the facade, and the temporary root imports are removed.
2. The P4.2 statement-gate pack is unblocked (its layering caveat now cites
   a **closed** P4.1 gate).
3. Fill obligations and the carried notes join the chapter-3/4 fill-epoch
   briefs.
```


## ===== audits/ch34-p0-resolutions.md =====

```
# Chapters 3-4, phase P0 (reception) — audit loop resolutions

**Gate: CLOSED (round 2, 2026-10-08).** Two rounds; the closing round reported
**0 blockers, 0 majors, 3 minors**, all three swept in the closing commit and
re-verified below. The received surface — Hydroxyi's `TimeHierarchy/`,
`SpaceComplexity/`, the `CounterProg` substrate and the five `ClassNP`
additions, 44 modules — is adopted as the chapters-3/4 foundation.

## Round 1 (`audits/ch34-p0-pack.md` → `audits/ch34-p0-findings.md`)

0 blockers, **1 major**, 7 minors, 2 notes; gate held open.

* **Finding 1 (major) — the zero-bound collapse.** Every machine satisfies
  `k ≤ spaceUsed` (each work tape visits its origin), so one zero of `s`
  forces a `SPACE s` decider to zero work tapes globally:
  `SPACE s = SPACE (fun _ => 0)` whenever `s` has a zero; literal
  `SPACE (fun n => n)` is not linear space. Maintainer-verified before repair.
  **Repair**: positive-bound convention adopted (plan §2.4; Ex 3.2 restated at
  `SPACE(n+1)`); collapse documented at the definition site
  (`SpaceComplexity/Basic.lean`); sanity layer
  `SpaceComplexity/ZeroSpace.lean` added (S1-S6). Round 2: **closed**, with
  every sanity statement independently derived true as stated.
* **Findings 2-5, 8 (minors)** — docstring repairs in `CounterProgRun` (plus
  the requested S9 statement `sim_run_of_regs_le`), `Program`, `ARM`,
  `PClosure`, `ARMSim`/`Compile`/`Layout`. Round 2: **closed**.
* **Finding 6 (minor)** — `ReachesB` endpoint wording: repaired, but the
  repair's `Reaches.toB` reference was itself inaccurate; residual swept in
  the closing commit (below).
* **Finding 7 (minor)** — sweep-log provenance: replaced by a sweep recording
  its revision at start. Round 2: **closed** for the replacement evidence;
  the original log's trailing-revision reading stands as a **round-1 pack
  erratum** (acknowledged; shipped packs are never edited).
* **Notes 9-10** — delivered-strength reading of the time hierarchy; the
  non-delivery of general Lemma 4.17. Frozen, no change, both carried into
  the chapters-3/4 statements as recorded in the plan.

## Round 2 (`audits/ch34-p0-r2-pack.md` → `audits/ch34-p0-r2-findings.md`)

**PASS — 0 blockers, 0 majors, 3 minors**, with the repair diff reconstructed
hash-exactly against the round-1 bundle and all ten new statements (S1-S6, S9)
independently derived. Bonus result recorded for fill time: S9's hypotheses
support the tighter bound `t·(2B + 3)`; the stated `t·(2B + 5)` is sound and
deliberately conservative — fills may sharpen it, statement unchanged.

**Closing-commit sweeps (this commit), re-verified:**

| R2 finding | Sweep |
|---|---|
| 6 (residual) | `ReachesB`'s consumer note now states the required separate endpoint hypothesis and says explicitly that `Reaches.toB` does **not** supply it; `Reaches.toB`'s own docstring rewritten (pre-final coordinate → pre-final interval; no reached-configuration bound implied) |
| 11 | "machine-checked" wording corrected to "elaborated sanity statements, proofs deferred to fill" in `ZeroSpace.lean`'s docstring and the plan's §2.4 paragraph |
| 12 | The two timed witness statements added to `ZeroSpace.lean` (sorried, as authorized): `exists_zeroTape_const_oneStep` (zero tapes, `[true]` within one step) and `exists_zeroTape_parity_decider` (zero tapes, `DecidesInTime evenLang (n + 1)`), per the report's own constructions; membership corollaries kept |

Re-verification: `ParseCmp` and `ZeroSpace` re-elaborate with zero errors
(`ZeroSpace` now 11 admission warnings — the nine round-1 statements plus the
two finding-12 witnesses); style lint 0 FAIL over the `SpaceComplexity` tree.

**Round-2 pack erratum (acknowledged):** the pack's phrase "as the log header
records" overstated the sweep-log header — it records the revision, branch,
start time and the wipe statement, but working-tree cleanliness and the
untracked directories were maintainer attestations, not log contents.

## Standing obligations out of this gate

1. **Fill obligations**: the 11 `ZeroSpace` statements and
   `CounterProg.sim_run_of_regs_le` (optionally at the tighter `2B + 3`).
   Scheduled with the chapters-3/4 fill epochs.
2. **The positive-bound convention** binds every future asymptotic space
   statement (`n + 1`, `n^c + 1`, `logSpace`; never a bound with a zero) —
   plan §2.4; the space-hierarchy and Savitch phases must restate it in their
   packs.
3. **Delivered-strength discipline** (notes 9-10): the `f²` time hierarchy is
   never cited as [AB09, Thm 3.1] verbatim until the Hennie-Stearns build
   lands; nothing received is cited as general Lemma 4.17.
4. The P3.1 and P4.1 statement gates, deferred behind this one, are now
   unblocked.
```


## ===== TCSlib/Complexity/Formulas/QBF.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Logic.Function.Basic
import TCSlib.Complexity.Formulas.CNF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Quantified Boolean formulas (prenex, CNF matrix)

[AB09, §4.2, Definition 4.10]: a quantified Boolean formula is
`Q₁x₁ Q₂x₂ … Qₙxₙ φ(x₁, …, xₙ)` with each `Qᵢ` one of `∀`/`∃`, the variables
ranging over `{0, 1}`, and `φ` a plain Boolean formula. Phase P4.3 of
`AroraBarakChapters3-4Plan.md`; the campaign carrier per decision CH34-Q5:
**prenex form with a CNF matrix**, reusing the chapter-2 carrier
(`Std.Sat.CNF ℕ`, `TCSlib.Complexity.Formulas.CNF`).

## Divergences from [AB09] (each deliberate, recorded for the audit)

* **CNF matrix.** Definition 4.10 allows an arbitrary unquantified matrix and
  notes (p. 83) that restricting to 3CNF is harmless via auxiliary variables.
  The campaign takes the CNF restriction *as the carrier* (decision CH34-Q5):
  `TQBF`'s hardness pays the Tseitin step inside its reduction, and a
  general-formula carrier remains future work (`backlog.md`, general Boolean
  formulas).
* **Prenex by construction**: the quantifier prefix is a `List`, the matrix
  follows; non-prenex formulas are out of scope (the book converts to prenex
  in polynomial time, p. 83 — not formalized here).
* **Free variables read `false`.** Quantifier `i` binds variable `i` (the
  prefix binds an initial segment of `ℕ`); matrix variables at or beyond the
  prefix length are unbound and evaluate at the all-`false` base assignment.
  [AB09] considers only closed formulas; this totalization (in the spirit of
  the chapter-2 `codeFallback` conventions) makes `QBF.truth` total without a
  well-formedness side condition, and well-formed consumers never rely on it.

## Main definitions

* `Complexity.QBF.Quant`, `Complexity.QBF` — the prefix alphabet and the
  formula. [AB09, Definition 4.10]
* `Complexity.QBF.truth` — the truth value, by recursion on the prefix.
  [AB09, Definition 4.10 and Example 4.11]

## Main results (sorried; phase-P4.3 statement)

* `Complexity.QBF.truth_exPrefix_iff_satisfiable` — an all-`∃` prefix covering
  the matrix's variables renders exactly satisfiability: the `SAT` embedding
  of [AB09, Example 4.12].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Definitions 4.9-4.10, Examples
  4.11-4.12.)
-/

namespace Complexity

open Std.Sat (CNF)

namespace QBF

/-- A quantifier of the prenex prefix. [AB09, Definition 4.10] -/
inductive Quant where
  /-- the existential quantifier `∃` -/
  | ex
  /-- the universal quantifier `∀` -/
  | all
deriving DecidableEq

end QBF

/-- A prenex quantified Boolean formula with CNF matrix: the quantifier
prefix (quantifier `i` binds variable `i`) and the matrix. Matrix variables
beyond the prefix length are free and read `false` under `QBF.truth` (see the
divergences list). [AB09, Definition 4.10, with decision CH34-Q5's CNF
restriction] -/
structure QBF where
  /-- the prenex quantifier prefix; entry `i` binds variable `i` -/
  quants : List QBF.Quant
  /-- the CNF matrix over the chapter-2 carrier -/
  matrix : CNF ℕ

namespace QBF

/-- Truth of the matrix `m` under the remaining prefix, the partial
assignment built so far, and the next variable index: the recursion of
[AB09, Definition 4.10]'s semantics ("∀ and ∃ have their standard meaning"),
peeling one quantifier per step. -/
def truthAux (m : CNF ℕ) : List Quant → (ℕ → Bool) → ℕ → Prop
  | [], σ, _ => m.eval σ = true
  | .ex :: qs, σ, i => ∃ b : Bool, truthAux m qs (Function.update σ i b) (i + 1)
  | .all :: qs, σ, i => ∀ b : Bool, truthAux m qs (Function.update σ i b) (i + 1)

/-- **The truth value of a QBF** [AB09, Definition 4.10]: peel the prefix
from variable `0`, starting at the all-`false` base assignment (free
variables read `false`; see the divergences list). Since every prefix
variable is bound, a closed formula's truth is assignment-independent. -/
def truth (Q : QBF) : Prop :=
  truthAux Q.matrix Q.quants (fun _ => false) 0

/-- **The `SAT` embedding** ([AB09, Example 4.12]; spec, fill pending —
phase P4.3): under an all-`∃` prefix covering every matrix variable, truth
is exactly satisfiability of the matrix.

**Proof sketch.** Forward: the recursion's witnesses assemble an assignment
on `[0, n)` under which the matrix evaluates `true`; variables `≥ n` carry
the base `false`, and `Complexity.eval_congr_of_lt_numVars` (chapter 2)
transports evaluation to the assembled assignment. Backward: given a
satisfying `σ`, choose the witness `σ i` at step `i`; after `n` updates the
built assignment agrees with `σ` below `numVars m ≤ n`, and
`eval_congr_of_lt_numVars` closes. Fill obligations: the update-prefix
agreement lemma (`Function.update` accumulation agrees with `σ` on the
consumed segment) and the two inductions. -/
theorem truth_exPrefix_iff_satisfiable (m : CNF ℕ) (n : ℕ) (hn : m.numVars ≤ n) :
    QBF.truth ⟨List.replicate n .ex, m⟩ ↔ m.Satisfiable := by
  sorry

end QBF

end Complexity
```


## ===== TCSlib/Complexity/Formulas/QBFEncoding.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.QBF
import TCSlib.Complexity.Formulas.CNFEncoding
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary encoding of quantified Boolean formulas

The serialization layer for `Complexity.QBF`, mirroring the chapter-2 CNF
conventions (`TCSlib.Complexity.Formulas.CNFEncoding`): a self-delimiting
pair of the quantifier prefix (one bit per quantifier, `true` for `∃`) and
the matrix's LL(1) serialization, with a total `decode` whose fallback is the
closed trivial formula. Phase P4.3 of `AroraBarakChapters3-4Plan.md`; the
language `TQBF` (`TCSlib.Complexity.ClassPSPACE.TQBF`) is defined over this
decoding.

## Conventions

* `encode Q := Turing.pairEncode (prefix bits) (CNF.serialize Q.matrix)` —
  the campaign's aligned pairing, so one aligned parse recovers both
  components.
* `decode` totalizes with the fallback `⟨[], CNF.fallback⟩` (empty prefix,
  empty matrix) on strings that fail the pair parse; the matrix component
  reuses `CNF.decode`'s own fallback behavior. The fallback formula is
  **true** (the empty CNF evaluates `true`), so non-well-formed strings lie
  **in** `TQBF` — the same polarity as the chapter-2 `SAT` fallback
  convention, recorded there and here.

## Main definitions

* `Complexity.QBF.encode`, `Complexity.QBF.decode` — serialization and total
  decoding.

## Main results (sorried; phase-P4.3 statement)

* `Complexity.QBF.decode_encode` — decoding inverts encoding.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2; representation conventions as in
  §2.3's footnote 3.)
-/

namespace Complexity.QBF

open Std.Sat (CNF)
open Turing

/-- One bit per quantifier: `true` for `∃`, `false` for `∀`. -/
def quantBit : Quant → Bool
  | .ex => true
  | .all => false

/-- The quantifier of a bit, inverse to `Complexity.QBF.quantBit`. -/
def quantOfBit (b : Bool) : Quant :=
  if b then .ex else .all

/-- **Serialize a QBF**: the aligned pair of the prefix bits and the
chapter-2 matrix serialization. -/
def encode (Q : QBF) : List Bool :=
  pairEncode (Q.quants.map quantBit) (CNF.serialize Q.matrix)

/-- **Total decoding** with the closed trivial fallback: parse the aligned
pair, read the prefix bitwise, decode the matrix by the chapter-2 total
decoder; strings failing the pair parse decode to `⟨[], CNF.fallback⟩`
(which is **true** — the `SAT`-polarity fallback convention, see the module
docstring). -/
def decode (x : List Bool) : QBF :=
  match pairDecode x with
  | some (q, m) => ⟨q.map quantOfBit, CNF.decode m⟩
  | none => ⟨[], CNF.fallback⟩

/-- **Decoding inverts encoding** (spec, fill pending — phase P4.3): every
serialized formula decodes to itself.

**Proof sketch.** `Turing.pairDecode_pairEncode` splits the pair;
`quantOfBit ∘ quantBit = id` by cases (`List.map_map` and `List.map_id`);
`CNF.decode_serialize` (chapter 2) recovers the matrix. -/
theorem decode_encode (Q : QBF) : decode (encode Q) = Q := by
  sorry

end Complexity.QBF
```


## ===== TCSlib/Complexity/ClassPSPACE/TQBF.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.QBFEncoding
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `PSPACE`-completeness and `TQBF`

[AB09, §4.2]: `PSPACE`-hardness and -completeness (Definition 4.9), the
adjacency-formula half of Claim 4.4(2), and the Stockmeyer-Meyer theorem that
`TQBF` is `PSPACE`-complete (Theorem 4.13). Phase P4.3 of
`AroraBarakChapters3-4Plan.md`.

## Design

* **Def 4.9 verbatim over the campaign's `≤ₚ`** (`Complexity.PolyTimeReducible`,
  chapter 2); the logspace-reduction variant ([AB09, Exercise 4.9]) waits for
  phase P4.4's `≤ₗ`.
* **Claim 4.4(2) at polynomial size, over a packaged quotient codec.** The
  statement supplies, for each machine and each `(n, s)`: a configuration
  bit-codec of fixed length linear in `s + n`, **factoring through the input
  and the P4.2 vertex quotient** `Turing.NDTM.coreSum` — full configurations
  are *not* injectively codable at fixed length, the output tape being
  unbounded (round-1 blocker, finding 1) — together with **three** CNFs over
  the code bits: a validity predicate characterizing exactly the codec image
  (unguarded midpoint quantification admits paths through junk codes —
  round-1 finding 3), the adjacency test (true on same-input windowed pairs
  iff the step descends to the vertex quotient; false across distinct
  inputs), and the acceptance test (halted state with `accept` summary).
  Declared deviations from the book's Claim 4.4(2), each argued harmless to
  Theorem 4.13: (i) the codec length is `O(s + n)` rather than `O(s)` — the
  code carries the **input content** and a one-hot input-position track, so
  every check is *local* and the formulas are input-independent (Cook-Levin's
  marker discipline; round-1 finding 7); (ii) the CNF sizes are bounded
  through their **serialized lengths** — polynomial, not linear; a
  literal-occurrence count alone misses empty clauses (round-1 finding 8);
  (iii) adjacency compares `coreSum (step c)` with `coreSum d`, so halted
  vertices are self-adjacent and live ones are not — the ψ-recursion's base
  case supplies `a = b` separately (round-1 finding 6). **The package is
  existence, not an algorithm** (round-1 major 2): the uniform
  polynomial-time emitter of the three formulas is a private, named fill
  obligation of `TQBF`'s hardness proof, never a claim of this statement.
  Sole consumer unchanged; D6-style promotion recorded for a second consumer
  (the phase-P4.4 `PATH` encoding remains the candidate).
* **The facade discipline**: `ClassPSPACE.lean` is this phase's own new
  facade; nothing frozen is touched.

## Main definitions

* `Complexity.PSPACEHard`, `Complexity.PSPACEComplete` — [AB09, Definition 4.9].
* `Complexity.TQBF` — the true quantified Boolean formulas, over
  `Complexity.QBF.decode`. [AB09, §4.2, before Theorem 4.13]

## Main results (all sorried; phase-P4.3 statements)

* `Complexity.PSPACE_eq_P_of_pspaceComplete_mem_P` — a `PSPACE`-complete
  language in `P` collapses `PSPACE` to `P`. [AB09, §4.2, after Definition 4.9]
* `Complexity.exists_adjacency_codec_cnf` — Claim 4.4(2), packaged quotient form.
* `Complexity.TQBF_mem_PSPACE` — [AB09, Theorem 4.13, membership half].
* `Complexity.TQBF_PSPACEHard` — [AB09, Theorem 4.13, hardness half]; a fill
  summit (the `ψᵢ` emitter).
* `Complexity.TQBF_PSPACEComplete` — [AB09, Theorem 4.13].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Definition 4.9, Claim 4.4,
  Theorem 4.13.)
* [SM73] L. Stockmeyer, A. Meyer, *Word problems requiring exponential time*,
  STOC 1973. (Cited through [AB09]; no external text required.)
-/

namespace Turing

/-- A configuration lies **in the radius-`s` window** when every work head
sits within `[-s, s]` and every work cell outside `[-s, s]` is blank — the
side condition under which the packaged codec of
`Complexity.exists_adjacency_codec_cnf` is faithful. (The input head needs no
clause: its type bounds it.) -/
def Cfg.InWindow {k : ℕ} {Symbol State : Type} {x : List Symbol} (s : ℕ)
    (c : Cfg k Symbol State x) : Prop :=
  (∀ i, |c.workTapePos i| ≤ (s : ℤ)) ∧
  ∀ (i : Fin k) (z : ℤ), (s : ℤ) < |z| → c.workTapes i z = none

end Turing

namespace Complexity

open Std.Sat (CNF)
open Turing

/-- **`PSPACE`-hardness** [AB09, Definition 4.9]: every `PSPACE` language
Karp-reduces to `L'` in polynomial time. (The logspace variant is phase
P4.4's.) -/
def PSPACEHard (L' : Language Bool) : Prop :=
  ∀ L ∈ PSPACE, L ≤ₚ L'

/-- **`PSPACE`-completeness** [AB09, Definition 4.9]: `PSPACE`-hard and in
`PSPACE`. -/
def PSPACEComplete (L' : Language Bool) : Prop :=
  L' ∈ PSPACE ∧ PSPACEHard L'

/-- **A `PSPACE`-complete language in `P` collapses the class**
([AB09, §4.2, the paragraph after Definition 4.9]; spec, fill pending):
if some `PSPACE`-complete `L'` lies in `P`, then `PSPACE = P`.

**Proof sketch.** `⊇` is `Complexity.P_subset_PSPACE` (phase P4.1). `⊆`: a
`PSPACE` member reduces to `L'` (hardness), and `P` is closed downward under
`≤ₚ` (`Complexity.mem_P_of_polyTimeReducible`, chapter 2). -/
theorem PSPACE_eq_P_of_pspaceComplete_mem_P {L' : Language Bool}
    (h : PSPACEComplete L') (hP : L' ∈ P) : PSPACE = P := by
  sorry

/-- **Claim 4.4(2), packaged quotient form** (spec, fill pending — phase
P4.3 round 2; see the module docstring's declared deviations): for every
machine there is a constant `C` such that for all `(n, s)` there are a
configuration bit-codec — fixed length `C · (s + n + 1)`, injective **down to
the input and the vertex quotient** `Turing.NDTM.coreSum` on windowed
configurations — and three CNFs: `φv` characterizing exactly the codec image
among the length-matching strings, `φa` deciding adjacency (the step, read on
the vertex quotient) on same-input windowed pairs and rejecting cross-input
pairs, and `φacc` deciding acceptance (halted state, `accept` summary); all
three with `numVars` inside the code width and serialized lengths bounded by
`C · (s + n + 1) ^ C`.

**Proof sketch.** The codec is the marker discipline of the Cook-Levin
tableau row (`TCSlib.Complexity.CookLevin` precedents), now carrying the
input: an input-content track of `n` bits, a one-hot input-position track of
length `n + 2`, a one-hot state block (halt included), per work tape a window
track of `2s + 1` cells — three-valued symbol plus a head-marker bit — and a
two-bit summary block; total length linear in `s + n` with the machine's
constants in `C`, padded to the exact `C · (s + n + 1)`. Injectivity to
`(x, coreSum)` mirrors `Turing.MultiTapeTM.ConfigCount.coreCode_inj` on the
window tracks plus the content track; the output enters only through the
summary block (full-output injectivity is impossible and not claimed —
round-1 finding 1). `φv` conjoins per-track well-formedness (one-hot blocks,
trit ranges, canonical padding); `φacc` reads the halt pattern and the
summary block; `φa` conjoins content-track equality, locality of unmarked
window cells, the marked-cell and neighbor updates by the transition table —
the scanned input bit read from the content track under the position
marker — the one-hot shifts by at most one, the state rewrite, and the
summary update (`Turing.outSummary`'s append table): each check spans a
constant number of bits per machine, a constant-size CNF per position by the
chapter-2 universality (`Complexity.exists_cnf_boolFun`, applied per
**gate**, never per row — a whole-row truth table is exponential); summing
over `O(s + n)` positions bounds clause count, `numVars`, and the serialized
lengths polynomially (the chapter-2 grammar's serialization-length equation —
clause count enters it explicitly, round-1 finding 8). Fill obligations,
named: the codec definition with exact-length padding; the two injectivity
lemmas; the validity characterization in both directions; the per-position
check enumeration; the three serialized-size ledgers; the
step-iff-adjacency equivalence through `Turing.NDTM.coreSum_stepWith`. -/
theorem exists_adjacency_codec_cnf (M : Turing.FinTM Bool) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n s : ℕ),
      ∃ (code : (x : List Bool) → Cfg M.k Bool M.State x → List Bool)
        (φv φa φacc : CNF ℕ),
        (∀ (x : List Bool) (c : Cfg M.k Bool M.State x),
          (code x c).length = C * (s + n + 1)) ∧
        (∀ (x x' : List Bool), x.length = n → x'.length = n →
          ∀ (c : Cfg M.k Bool M.State x) (c' : Cfg M.k Bool M.State x'),
            c.InWindow s → c'.InWindow s → code x c = code x' c' → x = x') ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c d : Cfg M.k Bool M.State x, c.InWindow s → d.InWindow s →
            code x c = code x d → NDTM.coreSum c = NDTM.coreSum d) ∧
        (∀ w : List Bool, w.length = C * (s + n + 1) →
          (φv.eval (fun v => w.getD v false) = true ↔
            ∃ (x : List Bool), x.length = n ∧
              ∃ c : Cfg M.k Bool M.State x, c.InWindow s ∧ w = code x c)) ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c d : Cfg M.k Bool M.State x, c.InWindow s → d.InWindow s →
            (φa.eval (fun v => (code x c ++ code x d).getD v false) = true ↔
              NDTM.coreSum (M.tm.step c) = NDTM.coreSum d)) ∧
        (∀ (x x' : List Bool), x.length = n → x'.length = n → x ≠ x' →
          ∀ (c : Cfg M.k Bool M.State x) (c' : Cfg M.k Bool M.State x'),
            c.InWindow s → c'.InWindow s →
            φa.eval (fun v => (code x c ++ code x' c').getD v false) = false) ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c : Cfg M.k Bool M.State x, c.InWindow s →
            (φacc.eval (fun v => (code x c).getD v false) = true ↔
              (c.state = none ∧ outSummary c.output = OutSummary.accept))) ∧
        φv.numVars ≤ C * (s + n + 1) ∧
        φacc.numVars ≤ C * (s + n + 1) ∧
        φa.numVars ≤ 2 * (C * (s + n + 1)) ∧
        (CNF.serialize φv).length ≤ C * (s + n + 1) ^ C ∧
        (CNF.serialize φa).length ≤ C * (s + n + 1) ^ C ∧
        (CNF.serialize φacc).length ≤ C * (s + n + 1) ^ C := by
  sorry

/-- **The language `TQBF`** [AB09, §4.2]: binary strings whose decoded
quantified formula is true. The decoding fallback is the true closed formula,
so non-well-formed strings are members — the `SAT`-polarity convention of
`Complexity.QBF.decode`. -/
def TQBF : Language Bool :=
  {x | (QBF.decode x).truth}

/-- **`TQBF ∈ PSPACE`** ([AB09, Theorem 4.13, membership half]; spec, fill
pending): truth of a quantified formula is decidable in polynomial space.

**Proof sketch.** Validate the **entire** encoding before any matrix
verdict: trailing garbage makes the total decoder select the true fallback,
so a scanned prefix that "looks unsatisfiable" must not short-circuit
(round-1 answer 5). Then the recursive evaluator `A` of [AB09]: peel the
first quantifier, evaluate both restrictions, combine by the quantifier —
realized iteratively with a partial-assignment word of one trit per prefix
variable (the book's footnote: the linear-space global-array variant) walked
depth-first by the loop combinator, with no per-level formula copies; the
base case evaluates the CNF matrix under the assembled assignment by one
scan per clause, re-reading prefix bits and matrix bytes from the input. Space: the assignment
word (linear), the matrix cursor (linear), the recursion is depth-first on
the word in place — `O(n)` cells, inside `SPACE (n + 1) ⊆ PSPACE`. Fill
obligations, named: the depth-first assignment walker (a §12 loop/catalog
consumer), the CNF evaluator machine (one-pass per clause over the decoded
matrix), the parser reuse (`Complexity.QBF.decode` realized by the chapter-2
parser machinery), and the `DecidesInSpace` packaging. -/
theorem TQBF_mem_PSPACE : TQBF ∈ PSPACE := by
  sorry

/-- **`TQBF` is `PSPACE`-hard** ([AB09, Theorem 4.13, hardness half]; spec,
fill pending — **the phase-P4.3 fill summit**, the `ψᵢ` emitter).

**Proof sketch.** Let `L ∈ PSPACE`, decided by `M` in space `c₀ · (n^c + 1)`.
On input `x` (length `n`, window radius `s := c₀·(n^c + 1)`), the reduction
emits a quantified formula asserting "some accepting vertex is reachable
from the initial vertex within `2^ℓ` steps" over the packaged carrier of
`Complexity.exists_adjacency_codec_cnf`: vertices are the
`ℓ := C·(s + n + 1)`-bit codes of input-carrying windowed quotient
configurations, with `Valid := φv`, `Next := φa`, `Accept := φacc`. The
midpoint recursion is
`ψ₀(a, b) := Valid a ∧ Valid b ∧ (a = b ∨ Next (a, b))` — the base includes
length-zero paths, since live vertices are not `Next`-reflexive (round-1
finding 6) — and
`ψᵢ₊₁(a, b) := ∃ z (Valid z ∧ ∀ u v, ((u,v) = (a,z) ∨ (u,v) = (z,b)) → ψᵢ(u,v))`
([AB09]'s succinct `∀`-trick keeping one copy of `ψᵢ`, with the midpoint
**guarded by `Valid`** — unguarded quantification admits paths through junk
codes, round-1 finding 3), unfolded to depth `ℓ` (at most `2^ℓ` codes, so a
shortest path fits), against the emitted initial-vertex code and an
existentially quantified `Accept` target (no unique accepting configuration
is needed). Prenex first, then Tseitin: the gate variables of the CNF
conversion are existentially quantified **after** the original prefix — gate
values must not be fixed before universal variables they depend on (round-1
answer 5) — with constant-arity gate constraints via the chapter-2
universality (`Complexity.exists_cnf_boolFun` per gate, never per level).
Size: `O(ℓ)` scaffolding per level over `ℓ` levels plus the three packaged
CNFs — polynomial by their serialized-length clauses. Truth iff reachability
iff `M` accepts `x`: the quotient dictionary
(`Turing.NDTM.reflTransGen_cfgStep_iff` through `Turing.MultiTapeTM.toNDTM`)
with path lifting via `Turing.NDTM.coreSum_stepWith`, the space bound
keeping every genuine run inside the window. **The packaged existential
supplies no algorithm** (round-1 major 2): the uniform emitter — the
polynomial-time construction and serialization of `φv`/`φa`/`φacc`, the
initial-vertex code, the per-level scaffolding with its level-blocked
variable indexing, and the final assembly through
`Complexity.QBF.decode_encode` — is a set of **private, named fill
obligations of this proof**, in the chapter-2 streaming-emitter discipline
(`CookLevin/Hardness.lean`, the six-stage output-silence contract; §12
catalog routines); **continuation budget certain**. Fill obligations, named:
the three-CNF emitter family and its serialization-length ledger; the
initial-code computation; the level-blocked indexing scheme (unary-serialized
per the CNF grammar); the truth-preservation induction
`ψᵢ ↔ reachability within 2^i`, both directions of the guarded recursion;
the Tseitin-after-prefix equivalence; the final assembly through
`Complexity.QBF.decode_encode`. -/
theorem TQBF_PSPACEHard : PSPACEHard TQBF := by
  sorry

/-- **The Stockmeyer-Meyer theorem**: `TQBF` is `PSPACE`-complete.
[AB09, Theorem 4.13]

**Proof sketch.** `Complexity.TQBF_mem_PSPACE` with
`Complexity.TQBF_PSPACEHard`. -/
theorem TQBF_PSPACEComplete : PSPACEComplete TQBF := by
  sorry

end Complexity
```


## ===== TCSlib/Complexity/ClassPSPACE/Games.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Logic.Function.Basic
import TCSlib.Complexity.Formulas.QBF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite perfect-information games: determinacy

[AB09, Exercise 4.10] (Zermelo): in every finite two-person game with perfect
information and no draws, one of the two players has a winning strategy. The
connection to `PSPACE` is Example 4.15's QBF game — "player 1 has a winning
strategy" *is* the truth of an alternating quantified formula — and this
module supplies the game vocabulary and the determinacy statement at the
same binary granularity as `Complexity.QBF`. Phase P4.3 of
`AroraBarakChapters3-4Plan.md`.

## Design

* **The game is `n` alternating binary moves**: player one moves at even
  plies, player two at odd plies, the history is the list of moves (most
  recent last), and `W` decides the winner from the complete history —
  `true` meaning player one wins. No draws, matching the exercise's premise;
  finite games with draws reduce by splitting the draw outcome.
* A **strategy** is a function from the history so far to the next move;
  `playOut` folds two strategies into the complete history. This is
  deliberately the plainest rendering — richer game trees (variable
  branching, chess-like boards) are out of scope, as [AB09]'s own discussion
  of generalized boards notes (p. 87).

## Main definitions

* `Complexity.Game.playOut` — the history of a strategy pair.
* `Complexity.Game.FirstWins`, `Complexity.Game.SecondWins` — the two
  winning-strategy predicates.

## Main results (sorried; phase-P4.3 statement)

* `Complexity.Game.determined` — [AB09, Exercise 4.10].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.2, Example 4.15, Exercise 4.10.)
-/

namespace Complexity.Game

/-- The complete history of an `n`-ply game under the strategy pair
`(s₁, s₂)`: at each ply the mover — player one on even plies, player two on
odd — applies their strategy to the history so far, and the move is
appended. -/
def playOut (s₁ s₂ : List Bool → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 =>
    let h := playOut s₁ s₂ n
    h ++ [if h.length % 2 = 0 then s₁ h else s₂ h]

/-- Player one has a **winning strategy** in the `n`-ply game with win
predicate `W` (`true` = player one wins the completed history): some
strategy of theirs beats every strategy of player two.
[AB09, §4.2.2 and Exercise 4.10] -/
def FirstWins (n : ℕ) (W : List Bool → Bool) : Prop :=
  ∃ s₁ : List Bool → Bool, ∀ s₂ : List Bool → Bool, W (playOut s₁ s₂ n) = true

/-- Player two has a winning strategy: some strategy of theirs defeats every
strategy of player one. -/
def SecondWins (n : ℕ) (W : List Bool → Bool) : Prop :=
  ∃ s₂ : List Bool → Bool, ∀ s₁ : List Bool → Bool, W (playOut s₁ s₂ n) = false

/-- **Zermelo determinacy** ([AB09, Exercise 4.10]; spec, fill pending —
phase P4.3): every finite two-person perfect-information game without draws
is determined — exactly one quantifier alternation wins, so in particular
one of the players has a winning strategy.

**Proof sketch.** Backward induction on the remaining plies, generalized
over the history prefix: the position value is taken at the **fixed player-one
perspective**, `V h := "player one can force W = true from h"` — a
mover-relative value flips polarity with the turn and breaks the recursion
(round-1 finding 9) — and satisfies `V h = ∃ b, V (h ++ [b])` at even
histories, `V h = ∀ b, V (h ++ [b])` at odd ones, with the base read off `W`
(the `Complexity.QBF.truthAux` recursion is the same shape, which is Example
4.15's point). Strategy assembly covers both polarities: if `V []` holds,
`s₁` picks a true-valued child at every even node it can reach; if not, `s₂`
picks a false-valued child at every odd node — each extended arbitrarily off
its winning tree. At fixed horizon the case analysis is finite, so classical
instances are available but not essential. Mutual exclusion (`¬(FirstWins
∧ SecondWins)`) follows by playing the two winning strategies against each
other — not claimed in this statement, which renders the exercise's "one of
the two players has a winning strategy" disjunction. -/
theorem determined (n : ℕ) (W : List Bool → Bool) :
    FirstWins n W ∨ SecondWins n W := by
  sorry

end Complexity.Game
```


## ===== TCSlib/Complexity/ClassPSPACE.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassPSPACE.TQBF
import TCSlib.Complexity.ClassPSPACE.Games

/-!
# `PSPACE`-completeness

[AB09, §4.2]: `PSPACE`-hardness and -completeness, the `TQBF` language and
the Stockmeyer-Meyer theorem, and the game-playing face of the class. The
headline statements (phase P4.3 of `AroraBarakChapters3-4Plan.md`) are
`Complexity.TQBF_PSPACEComplete` ([AB09, Theorem 4.13]) with its two halves,
the packaged adjacency-formula interface of Claim 4.4(2), and Zermelo
determinacy for finite perfect-information games ([AB09, Exercise 4.10]).

## Contents

- `ClassPSPACE.TQBF`: Definition 4.9, the collapse corollary, Claim 4.4(2)
  in packaged form, `TQBF`, and Theorem 4.13
- `ClassPSPACE.Games`: finite two-person perfect-information games and
  Zermelo determinacy

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.)
-/
```


## ===== TCSlib/Complexity/SpaceComplexity/Hierarchy.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.TimeHierarchy.CodePrefix
import TCSlib.Complexity.TimeHierarchy.Diagonal
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The space hierarchy theorem

[AB09, §4.1.3, Theorem 4.8] with its tool, the space-bounded universal
machine ([AB09, Exercise 4.1]), the strictness corollary `L ⊊ PSPACE` on the
p. 92 chain, and `SPACE(n+1) ≠ NP` ([AB09, Exercise 3.2], restated with the
positive normalization per the P0 convention —
`AroraBarakChapters3-4Plan.md` §2.4). Phase P4.3.

## Design

* **Constant-factor overhead is the point** ([AB09]: "one can have a
  universal TM using only a constant factor of space overhead, and hence we
  don't need the logarithmic term of Theorem 3.1"): the hierarchy hypothesis
  below is eventual domination of every constant multiple — no square, no
  log — in contrast to the received `f²` time hierarchy.
* **The space-universal machine** reuses the fixed code scheme
  `Complexity.TimeHierarchy.code` (one-work-tape binary codes) and mirrors
  the two-clause shape of `Turing.timed_universal`, with the budget a
  **space** bound: simulate within constant-factor space, and detect
  non-halting-within-space by the configuration-count clock
  (`Turing.MultiTapeTM.ConfigCount`). Its space bound carries a
  `+ logSpace n` addend for the clock — a declared deviation from
  Exercise 4.1's literal `C_α · t`, which presumes the standing
  `S(n) > log n` convention.
* **Both bounds space-constructible**, as in the book; constructibility of
  `g` drives the budget computation and the clock, constructibility of `f`
  is carried for fidelity (the proof uses only `g`'s witness and `f`'s
  bundled `logSpace` floor — round-1 confirmed, recorded in the sketch).
* Facade wiring: root-wired while the P4.1 gate was live; the
  `SpaceComplexity.lean` facade has carried this module since that gate
  closed.

## Main results (all sorried; phase-P4.3 statements)

* `Complexity.space_universal` — [AB09, Exercise 4.1].
* `Complexity.space_hierarchy` — [AB09, Theorem 4.8].
* `Complexity.LOGSPACE_ssubset_PSPACE` — `L ⊊ PSPACE` on the p. 92 chain.
* `Complexity.SPACE_linear_ne_NP` — [AB09, Exercise 3.2], normalized.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.3, Theorem 4.8, Exercise 4.1;
  Exercise 3.2; [SHL65] through [AB09].)
-/

namespace Complexity

open Turing

/-- **The space-bounded universal machine** ([AB09, Exercise 4.1]; spec,
fill pending — phase P4.3): for the fixed scheme there is a machine `SU`
such that for every code `α` there is a constant `C` with, on input
`⟨bits s, ⟨α, x⟩⟩`: if the coded machine computes some output on `x` within
`s` visited work cells, `SU` outputs `true :: output` ; otherwise `SU`
outputs `[false]` — in both cases within `C · (s + logSpace |x| + 1)`
visited work cells (constant-factor space overhead plus the clock's
logarithmic addend; the time is existential, as
`Turing.FinTM.ComputesInTime`'s halting demands, with no stated bound).

**Proof sketch.** The interpreter of the chapter-1 `universal` machine
(table capture, virtual input, the simulated work tape held on one real
bank) is constant-factor in *space*; the budget test and the output contract
need care (round-1 finding 4). (i) **Space is tested as visited-interval
cardinality, not window membership**: maintain the simulated head's minimum
and maximum positions — both start at `0`, so one cell is visited
immediately, and at `s = 0` the failure clause fires on every input; unit
moves make `max − min + 1` exactly the visited count, checked **including
the final configuration**, with `max − min + 1 > s` rejecting (head
membership in `[-s, s]` does not count cells: visiting `0` then `1` uses two
cells inside `[-1, 1]`). (ii) **Non-halting-within-space is detected by the
core-count clock**: a binary counter of `O_α(s + logSpace n)` bits bounding
`(|Q|+1)·(n+2)·3^{2s+1}·(2s+1)` — a deterministic run repeating a live core
inside the window is periodic forever, so no first halt occurs after an
undetected repeat; outputs never enter the argument, cores excluding the
output tape (the `Turing.MultiTapeTM.ConfigCount` arithmetic as in
`ComputesInTime.of_spaceUsed_le`). (iii) **Probe silently, then replay**:
streamed output cannot be retracted when a later overflow or clock
exhaustion must yield exactly `[false]`, so the first pass runs with output
captured (W1); on success the machine resets the simulated banks, emits
`true`, and replays the run forwarding output — fixed banks reused between
the passes. (iv) The canonizer cost is a **finite code-dependent constant**
absorbed into `C` (the effective scheme supplies no bound linear in the code
length, and none is claimed). The `+ logSpace n` addend pays for the clock's
input-position factor under this construction — no lower-bound claim against
other universal simulations — and is absorbed under the standing
`s ≥ logSpace n` convention (`s + logSpace n + 1 ≤ 3s`). Fill obligations,
named: the interval counters with the final-configuration check; the
core-count clock at the stated width; the probe/replay two-pass assembly
over fixed banks (a §12 R1/R3 consumer); the per-code constant ledger. -/
theorem space_universal :
    ∃ SU : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, 0 < C ∧
      ∀ (s : ℕ) (x : List Bool),
        ((∃ (output : List Bool) (t : ℕ),
            ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t ∧
            ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
              (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s) →
          ∀ (output : List Bool) (t : ℕ),
            ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t →
            ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
              (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s →
            ∃ t' : ℕ,
              SU.ComputesInTime (pairEncode (Nat.bits s) (pairEncode α x))
                (true :: output) t' ∧
              SU.tm.spaceUsed
                  (SU.tm.initCfg (pairEncode (Nat.bits s) (pairEncode α x))) t'
                ≤ C * (s + logSpace x.length + 1)) ∧
        ((¬ ∃ (output : List Bool) (t : ℕ),
            ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x output t ∧
            ((TimeHierarchy.code).decode α).toFinTM.tm.spaceUsed
              (((TimeHierarchy.code).decode α).toFinTM.tm.initCfg x) t ≤ s) →
          ∃ t' : ℕ,
            SU.ComputesInTime (pairEncode (Nat.bits s) (pairEncode α x))
              [false] t' ∧
            SU.tm.spaceUsed
                (SU.tm.initCfg (pairEncode (Nat.bits s) (pairEncode α x))) t'
              ≤ C * (s + logSpace x.length + 1)) := by
  sorry

/-- **The space hierarchy theorem** ([AB09, Theorem 4.8]; [SHL65] through
[AB09]; spec, fill pending — phase P4.3): for space-constructible `f` and
`g`, if every constant multiple of `f` is eventually below `g`, then
`SPACE f ⊊ SPACE g`. Constant-factor hypothesis — no square and no
logarithmic term, by the constant-overhead universal simulation
(`Complexity.space_universal`); both constructibility hypotheses are the
book's, and the proof consumes only `g`'s (recorded here, seeded to the
audit). Positivity of both bounds is automatic from the bundled `logSpace`
floor, so the P0 zero-bound convention needs no side condition.

**Proof sketch.** The diagonal language of the padded-code discipline
(`TCSlib.Complexity.TimeHierarchy.CodePrefix`'s `preTM`/`scanPre`
self-application), with a **capped increasing-budget loop** that removes the
per-code constant from the space ledger (round-1 finding 5: `∀ α, ∃ Cα`
gives no uniform `O(g)` bound when the code is read off the input, and
padding a code can change its constant): on input `pairEncode α w`, `D`
(i) computes `g n` by `g`'s constructibility witness (space `O(g n)`);
(ii) tries budgets `s = 0, 1, …, g n`, reusing fixed banks, running
`Complexity.space_universal`'s machine on the self-applied virtual input at
budget `s` while **hard-capping the fixed universal's own work heads**
inside `[-g n, g n]` — a cap depending only on that machine's fixed tape
count, hence uniform in `α`; capped or failed attempts advance the budget;
(iii) answers the **opposite** of the first successful attempt's verdict,
retaining only a three-valued attempt summary (failure, success with
`[true]`, success otherwise; output suppressed, W1), and a fixed answer if
every attempt caps out. `D ∈ SPACE g`: the universal's fixed tapes confined
to the cap, the budget and address counters, and the bank resets are
`O(g n)` cells, uniformly in the input's code part. If `D ∈ SPACE f` via
machine `M` with constant `c₀`: put `M` into a **space-preserving
one-work-tape coded normal form** — a named fill obligation; the chapter-1
time-only normal form is not a space ledger — with fixed code `α_M`, and pad
the **payload**, never the code (the `CodePrefix` discipline keeps one code
fixed so a single constant `C_{α_M}` applies). By the eventual-domination
hypothesis at the assembled constant `A := C_{α_M} · (c₀ + 2)`, using the
bundled floors `logSpace n ≤ f n` and `1 ≤ f n`,
`C_{α_M}·(c₀·f n + logSpace n + 1) ≤ C_{α_M}·(c₀ + 2)·f n ≤ g n` eventually,
so some attempt at budget at most `c₀ · f n` succeeds within every cap, and
every successful attempt reports `M`'s deterministic verdict on the
self-applied input — which `D` flips: contradiction. Constructibility of `f`
contributes only its bundled floor. Fill obligations, named: the budget loop
with fixed-bank resets and the uniform cap; the attempt-summary discipline;
the space-preserving normal form; the self-application assembly
(`scanPre_pairEncode_append` precedent); the contradiction arithmetic;
`D`'s `DecidesInSpace` packaging. -/
theorem space_hierarchy (f g : ℕ → ℕ) (hf : SpaceConstructible f)
    (hg : SpaceConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * f n ≤ g n) :
    SPACE f ⊂ SPACE g := by
  sorry

/-- **`L ⊊ PSPACE`** — the strict step of the p. 92 chain ([AB09, §4.3.2,
"the hierarchy theorems imply `L ⊊ PSPACE`"]; spec, fill pending).

**Proof sketch.** `Complexity.space_hierarchy` at `f := logSpace`,
`g := fun n => n + 1` (both constructible — the received
`Complexity.spaceConstructible_logSpace` and
`Complexity.spaceConstructible_linear` of phase P4.1; domination:
`A · logSpace n ≤ n + 1` eventually, a logarithm-versus-identity
inequality), then `SPACE (n + 1) ⊆ PSPACE`
(`Complexity.space_poly_subset_PSPACE` at degree one) and strictness
transports along the inclusion. -/
theorem LOGSPACE_ssubset_PSPACE : LOGSPACE ⊂ PSPACE := by
  sorry

/-- **`SPACE(n + 1) ≠ NP`** ([AB09, Exercise 3.2], stated at the positive
normalization `n + 1` per the P0 convention — the literal `SPACE(n)` is the
zero-work-tape class; spec, fill pending). Neither inclusion between the
two classes is claimed, matching the book's remark.

**Proof sketch.** Suppose `SPACE (n + 1) = NP`. `NP` is closed downward
under `≤ₚ` (the chapter-2 bounded-certificate transport — a derived
obligation from `Complexity.mem_NP_iff_exists_length_le`, Exercise 2.1's
bounded form, named for the brief). Padding transfers space bounds down:
for `L ∈ SPACE (n² + 1)`, the padded language
`L' := {pairEncode x (List.replicate (|x|²) true)}` — padded length exactly
`m = n² + 2n + 2`, syntax validated — lies in `SPACE (m + 1)` in the padded
length (validate, then run the `L`-decider on the first component; the pad
supplies the room — the chapter-2 padding-cluster discipline,
`EXP_subset_NEXP`'s precedent), so `L' ∈ NP` by the assumption, and
`L ≤ₚ L'` by the padding reduction (a `polyUnary` emitter; the **unpadded**
language reduces to the **padded** one), so `L ∈ NP = SPACE (n + 1)` — the
`NP` pullback composing the reduction with the bounded-certificate verifier
at the reduction's polynomial output length. Hence
`SPACE (n² + 1) ⊆ SPACE (n + 1)`, contradicting
`Complexity.space_hierarchy` at the constructible pair
(`Complexity.spaceConstructible_linear`,
`Complexity.spaceConstructible_poly` at degree two; domination
`A · (n + 1) ≤ n² + 1` eventually). Fill obligations, named: the `NP`
`≤ₚ`-closure lemma; the padded-language space decider; the padding
reduction machine; the strictness extraction. -/
theorem SPACE_linear_ne_NP : SPACE (fun n => n + 1) ≠ NP := by
  sorry

end Complexity
```


## ===== TCSlib/Complexity/Formulas.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNF
import TCSlib.Complexity.Formulas.CNFEncoding
import TCSlib.Complexity.Formulas.DNF
import TCSlib.Complexity.Formulas.QBF
import TCSlib.Complexity.Formulas.QBFEncoding

/-!
# Complexity — Boolean formulas

The formula layer of the Arora-Barak Chapter 2 development (see
`AroraBarakChapter2Plan.md`): CNF formulas over the Lean-core carrier
`Std.Sat.CNF ℕ`, and their binary serialization for the string languages
`SAT`/`3SAT` (in `TCSlib.Complexity.ClassNP`).

## Contents

* `CNF` — satisfiability, the variable-count measure, clause-width bounds, and
  CNF universality [AB09, §2.3.1, Claim 2.13], over `Std.Sat.CNF ℕ`.
* `CNFEncoding` — the unary-index LL(1) serialization, the exact-consumption
  parser, and the fixed-fallback totalization [AB09, §2.3.1, footnote 3].
* `DNF` — the DNF reading of the same carrier, the De Morgan dual, and the
  dual-tautology pivot [AB09, §2.6.1].
* `QBF` — prenex quantified Boolean formulas with CNF matrix, their truth
  semantics, and the `SAT` embedding [AB09, §4.2, Definition 4.10].
* `QBFEncoding` — the quantifier-prefix serialization over the CNF encoding,
  with the fixed-fallback totalization [AB09, §4.2].
-/
```


## ===== TCSlib/Complexity/Formulas/CNF.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Std.Sat.CNF
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Dedup

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CNF formulas for the complexity development

[AB09, §2.3.1]: a CNF formula is an AND of ORs of literals (variables or their
negations); a `k`CNF is a CNF in which every clause has **at most** `k` literals.
This module supplies the formula layer that `SAT`, `3SAT`, and the Cook-Levin
development consume: the carrier type, satisfiability, the variable-count measure
used by certificate-length formulas, clause-width bounds, and the statement of
[AB09, Claim 2.13] (CNF universality).

## Design and deviations from [AB09]

* **The carrier is `Std.Sat.CNF ℕ`** — the Lean-core SAT type: a formula is a
  `List` of clauses, a clause a `List` of literals, a literal a pair
  `(v, b) : ℕ × Bool` satisfied by an assignment `a` exactly when `a v = b` (so
  `b = true` is the positive literal `u_v` and `b = false` its negation). This is
  the **provisional resolution of the phase-3 seeded design question** (in-house
  type vs. `Std.Sat.CNF`; see the plan's decision log): the in-house candidate
  would have been byte-for-byte this shape, core supplies the evaluation
  (`Std.Sat.CNF.eval`, an all/any nest exactly matching [AB09]'s ⋀⋁), the
  mentioned-variable machinery (`Std.Sat.CNF.Mem`, `Std.Sat.CNF.eval_congr`),
  and relabeling with `Std.Sat.CNF.eval_relabel` (the fresh-variable tool of the
  clause-splitting and tableau constructions), and the repository policy is to
  use an existing mechanism rather than invent a parallel one. The type is pinned
  by `lean-toolchain`; the risk of upstream namespace drift is accepted and
  recorded. Campaign-side additions live in the `Std.Sat.CNF` namespace when they
  are formula-level (this file and the serialization layer) and in `Complexity`
  when they are complexity-level.
* **Conventions inherited from the carrier**: the empty formula evaluates `true`
  (`Std.Sat.CNF.eval_nil`) and an empty clause evaluates `false` — [AB09]'s
  standard reading of empty conjunctions/disjunctions.
* **Assignments are total functions `ℕ → Bool`.** [AB09] assigns to the `n`
  variables of the formula; a total assignment restricted to the mentioned
  variables carries the same information, and `Complexity.eval_congr_of_lt_numVars`
  (below) is the bridge that lets a finite certificate of `numVars φ` bits
  determine the value.
* **`kCNF` is "at most `k` literals per clause"** ([AB09, §2.3.1] verbatim);
  `Std.Sat.CNF.WidthAtMost` renders it.
* **Claim 2.13's size measure**: [AB09] counts `∧`/`∨` symbols (size `ℓ·2^ℓ`).
  Our statement bounds the clause count by `2^ℓ` and every clause's width by `ℓ`,
  from which [AB09]'s connective count follows by the trivial accounting
  (`#∧ = clauses − 1`, `#∨ = Σ (width − 1)` on nonempty data); the two
  renderings carry the same content and ours is the form the consumers use.

## Main definitions

* `Std.Sat.CNF.Satisfiable` — some assignment evaluates to `true`.
  [AB09, §2.3.1]
* `Std.Sat.CNF.numVars` — one plus the largest mentioned variable index (`0` for
  formulas mentioning nothing); the measure certificate-length formulas use.
* `Std.Sat.CNF.WidthAtMost` — every clause has at most `k` literals ([AB09]'s
  `k`CNF, §2.3.1).

## Main results

* `Complexity.eval_congr_of_lt_numVars` — evaluation depends only on the first
  `numVars` assignment bits.
* `Complexity.exists_cnf_boolFun` — CNF universality. [AB09, Claim 2.13]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.3.1, pp. 44-45; Claim 2.13, p. 46.)
-/

namespace Std.Sat.CNF

/-- The formula `φ` is *satisfiable*: some assignment makes it evaluate `true`
[AB09, §2.3.1]. (Core's `Std.Sat.CNF.Sat` fixes the assignment and
`Std.Sat.CNF.Unsat` is the universal negative; this is the existential the
language `SAT` quantifies.) -/
def Satisfiable {α : Type} (φ : CNF α) : Prop :=
  ∃ a : α → Bool, φ.eval a = true

/-- One plus the largest variable index mentioned in `φ`, and `0` when `φ`
mentions no variable (in particular on the empty formula and on empty clauses).
Every mentioned variable of `φ` is `< φ.numVars`, so an assignment certificate
of `numVars` bits determines the evaluation
(`Complexity.eval_congr_of_lt_numVars`); this is the measure the explicit
certificate-length formulas of `SAT ∈ NP` are budgeted against. -/
def numVars (φ : CNF ℕ) : ℕ :=
  (φ.flatMap fun C => C.map fun ℓ => ℓ.1 + 1).foldr max 0

/-- Every clause of `φ` has at most `k` literals — [AB09, §2.3.1]'s `k`CNF
("a CNF formula in which all clauses contain at most `k` literals"). The empty
formula qualifies vacuously for every `k`. -/
def WidthAtMost {α : Type} (φ : CNF α) (k : ℕ) : Prop :=
  ∀ C ∈ φ, C.length ≤ k

end Std.Sat.CNF

namespace Complexity

open Std.Sat (CNF)

/-- Every member of a list of natural numbers is bounded by its maximum fold. -/
private theorem le_foldr_max_of_mem {n : ℕ} {s : List ℕ} (h : n ∈ s) :
    n ≤ s.foldr max 0 := by
  induction s with
  | nil => cases h
  | cons m s ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

/-- Evaluation reads only the first `numVars` assignment values: assignments that
agree below `φ.numVars` evaluate `φ` identically. This is the bridge from finite
assignment certificates to total assignments.

**Proof sketch.** Every variable `v` mentioned in `φ` (`Std.Sat.CNF.Mem v φ`)
contributes `v + 1` to the `foldr max` defining `Std.Sat.CNF.numVars`, so
`v < φ.numVars` (a list-membership-to-fold bound, by induction on the flattened
list); then `Std.Sat.CNF.eval_congr` applies, its agreement hypothesis
discharged by the assumed agreement below `numVars`. -/
theorem eval_congr_of_lt_numVars {φ : CNF ℕ} {a b : ℕ → Bool}
    (h : ∀ v < φ.numVars, a v = b v) : φ.eval a = φ.eval b := by
  apply Std.Sat.CNF.eval_congr a b φ
  intro v hv
  apply h v
  apply Nat.lt_of_succ_le
  apply le_foldr_max_of_mem
  obtain ⟨C, hC, hv⟩ := hv
  apply List.mem_flatMap.mpr
  refine ⟨C, hC, ?_⟩
  rcases hv with hv | hv
  · exact List.mem_map.mpr ⟨(v, false), hv, rfl⟩
  · exact List.mem_map.mpr ⟨(v, true), hv, rfl⟩

/-- A termwise upper bound bounds the maximum fold, including the empty list. -/
private theorem foldr_max_le_of_forall {s : List ℕ} {n : ℕ}
    (h : ∀ k ∈ s, k ≤ n) : s.foldr max 0 ≤ n := by
  induction s with
  | nil => exact Nat.zero_le _
  | cons k s ih =>
      exact Nat.max_le.mpr
        ⟨h k (List.mem_cons_self), ih (fun j hj => h j (List.mem_cons_of_mem k hj))⟩

/-- The clause excluding precisely the assignment `v`, as in [AB09, Claim 2.13]. -/
private def falsifyingClause {ℓ : ℕ} (v : Fin ℓ → Bool) : CNF.Clause ℕ :=
  List.ofFn fun i => (i.val, !(v i))

/-- The excluding clause is false exactly on the assignment it excludes.
This is the pointwise step of [AB09, Claim 2.13]. -/
private theorem falsifyingClause_eval_false {ℓ : ℕ} (v : Fin ℓ → Bool)
    (a : ℕ → Bool) :
    (falsifyingClause v).eval a = false ↔ (fun i : Fin ℓ => a i.val) = v := by
  simp only [falsifyingClause, CNF.Clause.eval, List.any_eq_false]
  constructor
  · intro h
    funext i
    have hi := h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    cases ha : a i.val <;> cases hv : v i <;> simp_all
  · intro h p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    have hi := congrFun h i
    change ¬(a i.val == !(v i)) = true
    rw [hi]
    cases v i <;> decide

/-- The conjunction of all falsifying-assignment clauses in [AB09, Claim 2.13]. -/
private noncomputable def falsifyingCNF {ℓ : ℕ} (f : (Fin ℓ → Bool) → Bool) : CNF ℕ :=
  ((Finset.univ.filter fun v => f v = false).toList).map falsifyingClause

/-- The truth-table construction uses only the prescribed variables. -/
private theorem falsifyingCNF_numVars {ℓ : ℕ} (f : (Fin ℓ → Bool) → Bool) :
    (falsifyingCNF f).numVars ≤ ℓ := by
  unfold CNF.numVars falsifyingCNF
  apply foldr_max_le_of_forall
  intro k hk
  obtain ⟨C, hC, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hC
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact i.isLt

/-- There is at most one clause per assignment in the truth-table construction. -/
private theorem falsifyingCNF_length {ℓ : ℕ} (f : (Fin ℓ → Bool) → Bool) :
    (falsifyingCNF f).length ≤ 2 ^ ℓ := by
  classical
  simpa only [falsifyingCNF, List.length_map, Finset.length_toList,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
    (Finset.card_filter_le (Finset.univ : Finset (Fin ℓ → Bool))
      (fun v => f v = false))

/-- Every truth-table clause has width at most the prescribed arity; its
constructed length is exactly that arity. -/
private theorem falsifyingCNF_width {ℓ : ℕ} (f : (Fin ℓ → Bool) → Bool) :
    (falsifyingCNF f).WidthAtMost ℓ := by
  intro C hC
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hC
  exact (List.length_ofFn (f := fun i : Fin ℓ => (i.val, !(v i)))).le

/-- The truth-table CNF computes the original Boolean function.

**Proof sketch.** Its conjunction is false iff one of its clauses is false.
That clause excludes exactly the restricted assignment, so it is present iff
the original function is false there. Equality follows by Boolean cases. -/
private theorem falsifyingCNF_eval {ℓ : ℕ} (f : (Fin ℓ → Bool) → Bool)
    (a : ℕ → Bool) : (falsifyingCNF f).eval a = f (fun i => a i.val) := by
  classical
  have hfalse : (falsifyingCNF f).eval a = false ↔ f (fun i => a i.val) = false := by
    simp only [CNF.eval, List.all_eq_false, ← Bool.eq_false_iff]
    constructor
    · rintro ⟨C, hC, hCa⟩
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hC
      have hvf := (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2
      rw [(falsifyingClause_eval_false v a).mp hCa]
      exact hvf
    · intro ha
      refine ⟨falsifyingClause (fun i : Fin ℓ => a i.val), ?_,
        (falsifyingClause_eval_false _ a).mpr rfl⟩
      exact List.mem_map.mpr ⟨_, Finset.mem_toList.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩), rfl⟩
  cases hc : (falsifyingCNF f).eval a <;>
    cases hf : f (fun i => a i.val) <;> simp_all

/-- **CNF universality** [AB09, Claim 2.13]: every Boolean function
`f : {0,1}^ℓ → {0,1}` is computed by an `ℓ`-variable CNF formula with at most
`2^ℓ` clauses of width at most `ℓ` ([AB09]'s size measure `ℓ·2^ℓ` follows by
counting connectives — see the deviations list). The formula mentions only
variables `< ℓ`, so its evaluation at a total assignment is `f` of the
assignment's restriction.

**Proof sketch.** [AB09]'s construction. For each `v : Fin ℓ → Bool` with
`f v = false`, the clause `C_v = [(i, !(v i)) : i < ℓ]` evaluates to `false`
exactly at the assignments restricting to `v` (a literal `(i, !(v i))` is
satisfied iff `a i ≠ v i`, so `C_v.eval a = false` iff `a` agrees with `v` below
`ℓ`). Take `φ` to be the list of `C_v` over the (finitely many, at most `2^ℓ`)
falsifying `v`, e.g. via `Finset.univ.filter (fun v => f v = false)` on the
`Fintype` of `Fin ℓ → Bool`. Then `φ.eval a = false` iff some `C_v` fails at `a`
iff `f` of `a`'s restriction is `false`. Bounds: clause count at most
`2^ℓ = Fintype.card (Fin ℓ → Bool)`, width exactly `ℓ`, mentioned variables
`< ℓ` so `numVars ≤ ℓ`. Edge cases: at `ℓ = 0` the function is a constant on
the empty vector — `φ = []` (evaluating `true`) or `φ = [[]]` (one empty
clause, evaluating `false`, width `0 ≤ ℓ`), both within the `2^0 = 1` clause
bound. -/
theorem exists_cnf_boolFun (ℓ : ℕ) (f : (Fin ℓ → Bool) → Bool) :
    ∃ φ : CNF ℕ, φ.numVars ≤ ℓ ∧ φ.length ≤ 2 ^ ℓ ∧ φ.WidthAtMost ℓ ∧
      ∀ a : ℕ → Bool, φ.eval a = f fun i => a i.val := by
  exact ⟨falsifyingCNF f, falsifyingCNF_numVars f, falsifyingCNF_length f,
    falsifyingCNF_width f, falsifyingCNF_eval f⟩

end Complexity
```


## ===== TCSlib/Complexity/Formulas/CNFEncoding.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary serialization of CNF formulas

The languages `SAT` and `3SAT` are sets of **binary strings** ([AB09, §2.3.1]),
so formulas need a serialization, a parser, and — per [AB09, footnote 3] — a
totalization mapping non-well-formed strings to "some fixed formula". This module
supplies all three, together with the statements that tie them together: the
parse/serialize round trip and the variable-count bound that certificate-length
formulas rely on.

## Design and deviations from [AB09]

* **[AB09] fixes no concrete scheme** (footnote 3 explicitly waves the issue);
  any polynomially bounded, machine-parsable scheme is faithful. Ours is chosen
  for **parser-machine simplicity** and is the phase-3 serialization design
  question's provisional answer (see the plan's decision log):
  - a **literal** `(v, b)` is `v + 1` `true`s, then `false`, then the bit `b` —
    variable indices in **unary**, so the parsing machine counts a run instead
    of doing binary arithmetic;
  - a **clause** is its literals concatenated, then `false` (a clause-start
    position reading `false` means the clause is over — unambiguous, since
    every literal starts with `true`);
  - a **formula** is each clause prefixed by `true`, concatenated, then `false`
    (a formula-level position reading `true` announces another clause, `false`
    ends the formula).
  The grammar is LL(1): at every position the next bit alone determines the
  production. The empty formula is `[false]`; the empty clause is
  `[true, false]`.
* **Unary indices cost only a polynomial factor**: a literal on variable `v`
  occupies `v + 3` bits, so a serialized formula has length at least the sum of
  its `v + 1`-runs — which is what makes `numVars_decode_le` (below) true with
  the plain bound `|x|` — and at most polynomially more than any binary-index
  scheme on the formulas the campaign produces (the Cook-Levin tableau formula
  has polynomially many variables, so its unary serialization stays
  polynomial). Every downstream consumer is polynomial-time, so the choice is
  immaterial to every stated class-membership or hardness result.
* **The parser is fuel-indexed**: `parseClause`/`parseClauses` recurse on an
  explicit fuel argument (structural recursion, no termination proof
  obligations), and `parse` supplies fuel `x.length` — adequate because every
  production consumes at least one input bit before recursing, which is part of
  the round-trip statement's burden, not an axiom.
* **Exact consumption**: `parse` succeeds only when the grammar consumes the
  whole string; trailing garbage makes a string non-well-formed.
* **The fallback is the empty formula** `[]` — trivially satisfiable, a
  tautology, and of width `0`. [AB09, footnote 3] maps non-well-formed strings
  to "some fixed formula" and notes the choice is immaterial; consequences of
  this particular choice (every non-well-formed string lies in `SAT` and
  `3SAT`) are recorded where the languages are defined.

## Main definitions

* `Std.Sat.CNF.serialize` (with `serializeLit`, `serializeClause`) — the
  encoding.
* `Std.Sat.CNF.parse` (with `takeTrues`, `parseLit`, `parseClause`,
  `parseClauses`) — the exact-consumption parser.
* `Std.Sat.CNF.fallback`, `Std.Sat.CNF.decode` — the [AB09, footnote 3]
  totalization.

## Main results

* `Std.Sat.CNF.parse_serialize`, `Std.Sat.CNF.decode_serialize` — the round
  trip: serialized formulas are well-formed and decode to themselves.
* `Std.Sat.CNF.numVars_decode_le` — a decoded formula mentions at most `|x|`
  variables; the bound certificate-length formulas are budgeted against.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.3.1 with footnote 3, p. 45.)
-/

namespace Std.Sat.CNF

/-- Serialize one literal `(v, b)`: the variable index in unary (`v + 1` `true`s
— nonempty even for `v = 0`), the run terminator `false`, then the polarity bit
`b` verbatim. -/
def serializeLit (ℓ : Literal ℕ) : List Bool :=
  List.replicate (ℓ.1 + 1) true ++ [false, ℓ.2]

/-- Serialize one clause: its literals concatenated, closed by `false`. The
terminator is unambiguous because every literal begins with `true`. -/
def serializeClause (C : Clause ℕ) : List Bool :=
  C.flatMap serializeLit ++ [false]

/-- Serialize a formula: every clause prefixed by `true`, concatenated, closed
by `false`. At any formula-level position, `true` announces another clause and
`false` ends the formula; the empty formula is `[false]`. -/
def serialize (φ : CNF ℕ) : List Bool :=
  (φ.flatMap fun C => true :: serializeClause C) ++ [false]

/-- Split off the leading run of `true`s: `takeTrues x = (k, rest)` where `x`
begins with exactly `k` `true`s and `rest` is the remainder (which is empty or
begins with `false`). -/
def takeTrues : List Bool → ℕ × List Bool
  | true :: r => let (k, rest) := takeTrues r; (k + 1, rest)
  | r => (0, r)

/-- Parse one literal from the front: a nonempty run of `k + 1` `true`s, the
terminator `false`, and a polarity bit yield the literal `(k, ·)` and the
unconsumed remainder; anything else (no leading `true`, or the string ending
inside the literal) fails. -/
def parseLit (x : List Bool) : Option (Literal ℕ × List Bool) :=
  match takeTrues x with
  | (0, _) => none
  | (k + 1, false :: b :: rest) => some ((k, b), rest)
  | _ => none

/-- Parse one clause body with explicit fuel: a leading `false` closes the
clause; a leading `true` parses one literal and recurses. Exhausted fuel or an
exhausted string inside a clause fails. `Std.Sat.CNF.parse` supplies fuel
`x.length`, adequate because every literal consumes at least three bits. -/
def parseClause : ℕ → List Bool → Option (Clause ℕ × List Bool)
  | _, false :: rest => some ([], rest)
  | fuel + 1, x@(true :: _) =>
      match parseLit x with
      | some (ℓ, rest) =>
          match parseClause fuel rest with
          | some (C, rest') => some (ℓ :: C, rest')
          | none => none
      | none => none
  | _, _ => none

/-- Parse a clause list with explicit fuel: a leading `false` ends the formula;
a leading `true` parses one clause and recurses. -/
def parseClauses : ℕ → List Bool → Option (CNF ℕ × List Bool)
  | _, false :: rest => some ([], rest)
  | fuel + 1, true :: rest =>
      match parseClause fuel rest with
      | some (C, rest') =>
          match parseClauses fuel rest' with
          | some (φ, rest'') => some (C :: φ, rest'')
          | none => none
      | none => none
  | _, _ => none

/-- Parse a whole string as a formula, requiring **exact consumption**: the
grammar must account for every bit, and trailing garbage fails the parse.
Fuel `x.length` is adequate because every production consumes at least one bit
before recursing (part of the round-trip statement's burden). -/
def parse (x : List Bool) : Option (CNF ℕ) :=
  match parseClauses x.length x with
  | some (φ, []) => some φ
  | _ => none

/-- The fixed fallback formula of [AB09, footnote 3]: the empty CNF — trivially
satisfiable, a tautology, and of width `0`. -/
def fallback : CNF ℕ := []

/-- Total decoding: parse, and map non-well-formed strings to the fixed
`Std.Sat.CNF.fallback` ([AB09, footnote 3] — "such strings represent some fixed
formula"; the `Turing.MachineCode` decode-totality convention is the in-repo
precedent). -/
def decode (x : List Bool) : CNF ℕ :=
  (parse x).getD fallback

/-- Reading a nonempty unary run stops at its following `false`, preserving
the entire suffix. -/
private theorem takeTrues_replicate (k : ℕ) (r : List Bool) :
    takeTrues (List.replicate (k + 1) true ++ false :: r) = (k + 1, false :: r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (let (n, s) := takeTrues (List.replicate (k + 1) true ++ false :: r)
              (n + 1, s)) = _
      rw [ih]

/-- A serialized literal parses correctly with any unconsumed suffix. -/
private theorem parseLit_serializeLit (ℓ : Literal ℕ) (r : List Bool) :
    parseLit (serializeLit ℓ ++ r) = some (ℓ, r) := by
  simp only [serializeLit, List.append_assoc, List.cons_append, List.nil_append,
    parseLit, takeTrues_replicate]

/-- A clause round-trips with any suffix and any fuel at least its serialized
length.

**Proof sketch.** Induct on the literal list. The terminator closes the empty
clause without spending fuel. A literal consumes at least three bits, leaving
the decremented fuel large enough for the tail; apply the literal round trip
and then the induction hypothesis. -/
private theorem parseClause_serializeClause (C : Clause ℕ) (r : List Bool)
    (fuel : ℕ) (hf : (serializeClause C).length ≤ fuel) :
    parseClause fuel (serializeClause C ++ r) = some (C, r) := by
  induction C generalizing fuel with
  | nil => simp only [serializeClause, List.flatMap_nil, List.nil_append,
      List.cons_append, parseClause]
  | cons ℓ C ih =>
      cases fuel with
      | zero =>
          simp only [serializeClause, List.length_append, List.length_cons,
            List.length_nil] at hf
          omega
      | succ fuel =>
          have htail : (serializeClause C).length ≤ fuel := by
            simp only [serializeClause, List.flatMap_cons, List.length_append,
              serializeLit, List.length_replicate, List.length_cons, List.length_nil] at hf ⊢
            omega
          have hx : serializeClause (ℓ :: C) ++ r =
              serializeLit ℓ ++ (serializeClause C ++ r) := by
            simp only [serializeClause, List.flatMap_cons, List.append_assoc]
          rw [hx]
          have hlit := parseLit_serializeLit ℓ (serializeClause C ++ r)
          simp only [serializeLit, List.replicate_succ, List.cons_append] at hlit ⊢
          simp only [parseClause, hlit, ih fuel htail]

/-- A formula round-trips with any suffix and any fuel at least its serialized
length.

**Proof sketch.** Induct on the clause list. The empty formula reads its
terminator. A clause record has its leading marker and a nonempty serialized
body, so the decremented fuel suffices both for the clause body and for the
remaining formula. Thread the same suffix through the two round trips. -/
private theorem parseClauses_serialize (φ : CNF ℕ) (r : List Bool)
    (fuel : ℕ) (hf : (serialize φ).length ≤ fuel) :
    parseClauses fuel (serialize φ ++ r) = some (φ, r) := by
  induction φ generalizing fuel with
  | nil => simp only [serialize, List.flatMap_nil, List.nil_append,
      List.cons_append, parseClauses]
  | cons C φ ih =>
      cases fuel with
      | zero =>
          simp only [serialize, List.length_append, List.length_cons,
            List.length_nil] at hf
          omega
      | succ fuel =>
          have hclause : (serializeClause C).length ≤ fuel := by
            simp only [serialize, List.flatMap_cons, List.length_append,
              List.length_cons, List.length_nil] at hf
            omega
          have htail : (serialize φ).length ≤ fuel := by
            simp only [serialize, List.flatMap_cons, List.length_append,
              List.length_cons, List.length_nil] at hf ⊢
            omega
          have hx : serialize (C :: φ) ++ r =
              true :: (serializeClause C ++ (serialize φ ++ r)) := by
            simp only [serialize, List.flatMap_cons, List.cons_append, List.append_assoc]
          rw [hx]
          simp only [parseClauses, parseClause_serializeClause C _ fuel hclause,
            ih fuel htail]

/-- **The round trip**: serialized formulas parse back to themselves (with the
whole string consumed).

**Proof sketch.** Strengthen to suffix-carrying forms and induct.
(i) `takeTrues (List.replicate (k+1) true ++ false :: r) = (k+1, false :: r)`
by induction on `k`, so `parseLit (serializeLit ℓ ++ r) = some (ℓ, r)`.
(ii) For every clause `C` and suffix `r`, and any fuel at least
`(serializeClause C).length`,
`parseClause fuel (serializeClause C ++ r) = some (C, r)`: induction on `C`,
the nil case reading the closing `false`, the cons case chaining (i) and the
induction hypothesis — each literal consumes at least three bits, so the fuel
decrement stays adequate. (iii) The analogous statement for `parseClauses` over
the clause list, each clause consuming at least two bits. (iv) Instantiate at
the empty suffix: fuel `(serialize φ).length` suffices, the final `false` closes
the formula, and the remainder is exactly `[]`, so `parse` accepts. -/
theorem parse_serialize (φ : CNF ℕ) : parse (serialize φ) = some φ := by
  have h := parseClauses_serialize φ [] (serialize φ).length (Nat.le_refl _)
  simp only [List.append_nil] at h
  simp only [parse, h]

/-- Decoding inverts serialization: `decode` on a serialized formula is the
formula itself.

**Proof sketch.** `Std.Sat.CNF.parse_serialize` and `Option.getD` on a
`some`. -/
theorem decode_serialize (φ : CNF ℕ) : decode (serialize φ) = φ := by
  simp only [decode, parse_serialize, Option.getD_some]

/-- The counted unary run and the returned suffix partition the input length. -/
private theorem takeTrues_length (x : List Bool) :
    (takeTrues x).1 + (takeTrues x).2.length = x.length := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      cases b with
      | false => simp only [takeTrues, Nat.zero_add]
      | true =>
          simp only [takeTrues, List.length_cons]
          omega

/-- A successful literal parse consumes exactly its unary run, terminator,
and polarity bit. -/
private theorem parseLit_length {x r : List Bool} {ℓ : Literal ℕ}
    (h : parseLit x = some (ℓ, r)) : ℓ.1 + 3 + r.length = x.length := by
  have hlen := takeTrues_length x
  unfold parseLit at h
  split at h
  · cases h
  · rename_i k b rest ht
    cases h
    simp only [ht, List.length_cons] at hlen
    omega
  · cases h

/-- On a successful clause parse, the remainder is no longer than the input,
and every variable contribution fits inside the consumed prefix.

**Proof sketch.** Induct on fuel and distinguish the input marker. A closing
marker produces no literals. A literal consumes exactly its index plus three
bits; the induction hypothesis bounds the remaining parse. Add the final
remainder length to each variable contribution to avoid truncated subtraction. -/
private theorem parseClause_bounds {fuel : ℕ} {x r : List Bool} {C : Clause ℕ}
    (h : parseClause fuel x = some (C, r)) :
    r.length ≤ x.length ∧ ∀ ℓ ∈ C, ℓ.1 + 1 + r.length ≤ x.length := by
  induction fuel generalizing x C r with
  | zero =>
      cases x with
      | nil =>
          simp only [parseClause] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClause, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun ℓ hℓ => False.elim (List.not_mem_nil hℓ)⟩
          | true =>
              simp only [parseClause] at h
              cases h
  | succ fuel ih =>
      cases x with
      | nil =>
          simp only [parseClause] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClause, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun ℓ hℓ => False.elim (List.not_mem_nil hℓ)⟩
          | true =>
              cases hl : parseLit (true :: s) with
              | none =>
                  simp only [parseClause, hl] at h
                  cases h
              | some p =>
                  obtain ⟨lit, t⟩ := p
                  cases hc : parseClause fuel t with
                  | none =>
                      simp only [parseClause, hl, hc] at h
                      cases h
                  | some p =>
                      obtain ⟨D, u⟩ := p
                      simp only [parseClause, hl, hc, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl⟩
                      obtain ⟨hlen, hvars⟩ := ih hc
                      have hcons := parseLit_length hl
                      constructor
                      · omega
                      · intro ℓ hℓ
                        rcases List.mem_cons.mp hℓ with rfl | hℓ
                        · omega
                        · have hv := hvars ℓ hℓ
                          omega

/-- On a successful formula parse, the remainder is no longer than the input,
and every variable contribution fits inside the consumed prefix.

**Proof sketch.** Induct on fuel. A closing marker has no variables. Otherwise,
apply the clause bound to the first clause and the induction hypothesis to
the remaining formula. The final remainder is no longer than either earlier
suffix, so both sets of variable bounds persist when the parses are composed. -/
private theorem parseClauses_bounds {fuel : ℕ} {x r : List Bool} {φ : CNF ℕ}
    (h : parseClauses fuel x = some (φ, r)) :
    r.length ≤ x.length ∧ ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 + 1 + r.length ≤ x.length := by
  induction fuel generalizing x φ r with
  | zero =>
      cases x with
      | nil =>
          simp only [parseClauses] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClauses, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun C hC => False.elim (List.not_mem_nil hC)⟩
          | true =>
              simp only [parseClauses] at h
              cases h
  | succ fuel ih =>
      cases x with
      | nil =>
          simp only [parseClauses] at h
          cases h
      | cons b s =>
          cases b with
          | false =>
              simp only [parseClauses, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              exact ⟨Nat.le_succ _, fun C hC => False.elim (List.not_mem_nil hC)⟩
          | true =>
              cases hc : parseClause fuel s with
              | none =>
                  simp only [parseClauses, hc] at h
                  cases h
              | some p =>
                  obtain ⟨D, t⟩ := p
                  cases ht : parseClauses fuel t with
                  | none =>
                      simp only [parseClauses, hc, ht] at h
                      cases h
                  | some p =>
                      obtain ⟨ψ, u⟩ := p
                      simp only [parseClauses, hc, ht, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl⟩
                      obtain ⟨hclen, hcvars⟩ := parseClause_bounds hc
                      obtain ⟨htlen, htvars⟩ := ih ht
                      simp only [List.length_cons]
                      constructor
                      · omega
                      · intro C hC ℓ hℓ
                        rcases List.mem_cons.mp hC with rfl | hC
                        · have hv := hcvars ℓ hℓ
                          omega
                        · have hv := htvars C hC ℓ hℓ
                          omega

/-- A uniform bound on literal contributions bounds the formula's maximum
variable index plus one. -/
private theorem numVars_le_of_literal_bounds (φ : CNF ℕ) (n : ℕ)
    (h : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 + 1 ≤ n) : φ.numVars ≤ n := by
  have fold_bound : ∀ s : List ℕ, (∀ k ∈ s, k ≤ n) → s.foldr max 0 ≤ n := by
    intro s hs
    induction s with
    | nil => exact Nat.zero_le _
    | cons k s ih =>
        exact Nat.max_le.mpr ⟨hs k List.mem_cons_self,
          ih (fun j hj => hs j (List.mem_cons_of_mem k hj))⟩
  unfold numVars
  apply fold_bound
  intro k hk
  obtain ⟨C, hC, hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hk
  exact h C hC ℓ hℓ

/-- **A decoded formula mentions at most `|x|` variables**: for every string
`x`, `(decode x).numVars ≤ x.length`. This is the bound that lets the `SAT`
certificate length be the explicit formula `(n + 1)` bits — an assignment
certificate never needs more bits than the input is long.

**Proof sketch.** For the fallback (parse failure), `numVars [] = 0`. For a
successful parse, strengthen over the parsing functions: whenever
`parseLit`/`parseClause`/`parseClauses` succeeds on a string `y` returning a
remainder `r`, the consumed prefix has length `y.length - r.length`, and every
literal `(k, b)` produced consumed its own `k + 1` `true`s within that prefix —
so `k + 1 ≤ y.length`. Every mentioned variable of the parsed formula therefore
satisfies `v + 1 ≤ x.length`, and the `foldr max` defining
`Std.Sat.CNF.numVars` is bounded by `x.length` (each contribution is). -/
theorem numVars_decode_le (x : List Bool) : (decode x).numVars ≤ x.length := by
  unfold decode parse
  cases hp : parseClauses x.length x with
  | none => exact Nat.zero_le _
  | some p =>
      obtain ⟨φ, r⟩ := p
      cases r with
      | nil =>
          change φ.numVars ≤ x.length
          apply numVars_le_of_literal_bounds
          intro C hC ℓ hℓ
          simpa only [List.length_nil, Nat.add_zero] using
            (parseClauses_bounds hp).2 C hC ℓ hℓ
      | cons b r => exact Nat.zero_le _

end Std.Sat.CNF
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


## ===== TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Logic.Relation
import TCSlib.Complexity.SpaceComplexity.NSPACE
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.SpaceComplexity.ConfigCount
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.ClassNP.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configuration graphs of nondeterministic machines

[AB09, §4.1.1]: the configuration graph `G_{M,x}` of a machine on an input —
vertices the configurations, edges the one-step transitions (out-degree at most
two for a binary-choice NDTM) — together with the counting half of Claim 4.4(1)
for nondeterministic branches, the exponential-time simulation
([AB09, Theorem 4.2, third inclusion]), `NL ⊆ P`, and the coarseness of
polynomial-time reductions below `P` ([AB09, Exercise 4.3]). This is phase P4.2
of `AroraBarakChapters3-4Plan.md`; Savitch's theorem, the other consumer of
this layer, is `TCSlib.Complexity.SpaceComplexity.Savitch`.

**Status: statement skeleton (phase P4.2).** Definitions are real; every
contract is sorried with a sketch naming its fill obligations.

## Design

* **The vertex is a core plus a bounded output summary.** The received
  deterministic counting layer (`Turing.MultiTapeTM.ConfigCount`) counts
  *cores* — configurations without their output tapes — which is sound for
  halting-time bounds because output is write-only. For *acceptance* along a
  branch it is **not** sufficient by itself: acceptance means output exactly
  `[true]` at a halted configuration, and splicing out a cycle between equal
  cores could delete the branch's one emission (the P0 reception audit's
  fitness note, `audits/ch34-p0-findings.md` §7, anticipated exactly this). The
  vertex therefore carries `Turing.OutSummary` — the three-valued quotient of
  the output by its relation to `[true]`: still empty, exactly `[true]`, or
  irrecoverably dead — which is compatible with the append-only output
  discipline and multiplies the core count by three
  (`Turing.FinNDTM.configBound`).
* **The graph is the step relation, not a finite object**: `Turing.NDTM.CfgStep`
  is a relation on configurations, with `Relation.ReflTransGen` as
  reachability; the finite counting enters only through the (sorried) bounds.
  Efficient vertex *encoding* reuses `Turing.MultiTapeTM.ConfigCount.coreCode`;
  the adjacency CNF of Claim 4.4(2) is deliberately phase P4.3.
* **Facade wiring**: root-wired while the P4.1 gate was live; since that
  gate closed (round 1, PASS), the `SpaceComplexity.lean` facade carries this
  module and `Savitch`.

## Main definitions

* `Turing.OutSummary`, `Turing.outSummary` — the three-valued output summary.
* `Turing.NDTM.coreSum` — the configuration-graph vertex: core plus summary.
* `Turing.NDTM.CfgStep` — the edge relation (one `stepWith`, either choice).
  [AB09, §4.1.1: out-degree at most two]
* `Turing.FinNDTM.configBound` — the vertex count at window radius `s`:
  three times the deterministic `configBound` formula. [AB09, Claim 4.4(1)]

## Main results (all sorried; phase-P4.2 statements)

* `Turing.NDTM.reflTransGen_cfgStep_iff` — reachability is the choice-word run.
* `Turing.NDTM.coreSum_stepWith` — a step's vertex depends only on the vertex.
* `Turing.FinNDTM.acceptsWithin_of_spaceUsedWith_le` — Claim 4.4(1),
  acceptance form: a space-`s` accepting branch shortens to the vertex count.
* `Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound` — the
  packaged interface the simulations consume.
* `Complexity.NSPACE_subset_exp_dtime` — [AB09, Theorem 4.2, third inclusion].
* `Complexity.NL_subset_P` — the p. 92 chain's nondeterministic step.
* `Complexity.polyTimeReducible_of_mem_NL` — [AB09, Exercise 4.3]: every
  nontrivial language is `NL`-hard under polynomial-time reductions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4, Theorem 4.2;
  §4.1.2; Exercise 4.3.)
-/

namespace Turing

variable {k : ℕ} {S : Type} {x : List Bool}

/-- The three-valued summary of an append-only output word relative to the
acceptance target `[true]`: still empty, exactly `[true]`, or dead — no
further appending can reach `[true]` from a dead output. The quotient the
configuration-graph vertex carries alongside the core (see the module
docstring for why the core alone cannot certify acceptance). -/
inductive OutSummary where
  /-- nothing emitted yet -/
  | empty
  /-- the output is exactly `[true]` -/
  | accept
  /-- the output can no longer become `[true]` -/
  | dead
deriving DecidableEq

/-- The summary of an output word: `[]` is `empty`, `[true]` is `accept`,
everything else is `dead`. Compatible with appending — the summary of
`out ++ e` is a function of the summary of `out` and `e` alone, which is what
makes the vertex sound for splicing arguments. -/
def outSummary : List Bool → OutSummary
  | [] => .empty
  | [true] => .accept
  | _ => .dead

namespace NDTM

/-- The configuration-graph **vertex** of a configuration: its core (state,
input position, work tapes, work heads — `Turing.MultiTapeTM.ConfigCount.core`)
together with the output summary. Two configurations with equal vertices have
equal futures up to output-suffix equality, which is exactly what acceptance
needs. [AB09, §4.1.1] -/
def coreSum (c : Cfg k Bool S x) :
    (Option S × Fin (x.length + 2) × (Fin k → ℤ → Option Bool) × (Fin k → ℤ)) ×
      OutSummary :=
  (MultiTapeTM.ConfigCount.core c, outSummary c.output)

/-- The configuration-graph **edge relation** of [AB09, §4.1.1]: `c` steps to
`c'` under some choice bit. A binary-choice NDTM gives out-degree at most two;
a halted configuration self-loops (`Turing.NDTM.stepWith_of_halt`). -/
def CfgStep (tm : NDTM k Bool S) (c c' : Cfg k Bool S x) : Prop :=
  ∃ b : Bool, tm.stepWith b c = c'

/-- **Reachability in the configuration graph is the choice-word run**
(spec, fill pending — phase P4.2): `c'` is `Relation.ReflTransGen`-reachable
from `c` along `Turing.NDTM.CfgStep` iff some choice word runs `c` to `c'`.
This is the dictionary between [AB09]'s graph language and the campaign's
`runWith` semantics.

**Proof sketch.** Forward: induction on the reflexive-transitive chain,
appending the step's choice bit (`Turing.NDTM.runWith_append` at a singleton).
Backward: induction on the word, `Relation.ReflTransGen.head` at each consumed
bit (`Turing.NDTM.runWith_cons`). -/
theorem reflTransGen_cfgStep_iff (tm : NDTM k Bool S) (c c' : Cfg k Bool S x) :
    Relation.ReflTransGen (tm.CfgStep) c c' ↔ ∃ w : List Bool, tm.runWith w c = c' := by
  sorry

/-- **A step's vertex depends only on the vertex** (spec, fill pending — phase
P4.2; the nondeterministic, summary-carrying analogue of
`Turing.MultiTapeTM.ConfigCount.core_step`): configurations with equal
`coreSum` have equal `coreSum` after one `stepWith` under the same choice bit.

**Proof sketch.** The action is selected from the state and the scanned
symbols, all read off the core (as in `core_step`: `Cfg.inputSymbol` and
`Cfg.workTapeSymbols` are core-determined), so the two steps apply the same
action to cores that agree; the new output is the old output appended by the
action's emission, and `Turing.outSummary` of an append is a function of the
old summary and the emission (case analysis on the three summary values and
the optional emitted bit — the compatibility fact of the summary quotient). -/
theorem coreSum_stepWith (tm : NDTM k Bool S) (b : Bool) {c d : Cfg k Bool S x}
    (h : coreSum c = coreSum d) :
    coreSum (tm.stepWith b c) = coreSum (tm.stepWith b d) := by
  sorry

end NDTM

namespace FinNDTM

/-- The configuration-graph **vertex count** of `N` on inputs of length `n`
with window radius `s`: three (the output summaries) times the deterministic
core-code count of `Turing.FinTM.configBound` —
`3 · (|Q| + 1) · (n + 2) · 3^{k(2s+1)} · (2s+1)^k`. [AB09, Claim 4.4(1), with
the campaign's explicit constants] -/
def configBound (N : FinNDTM Bool) (n s : ℕ) : ℕ :=
  3 * ((Fintype.card N.State + 1) * (n + 2) * 3 ^ (N.k * (2 * s + 1)) *
    (2 * s + 1) ^ N.k)

/-- **Claim 4.4(1), acceptance form** (spec, fill pending — phase P4.2): an
accepting branch of length `T` whose sibling branches of length `T` all stay
within `s` visited work cells shortens to an accepting branch of length the
vertex count: `AcceptsWithin x (N.configBound x.length s)`.

**Proof sketch.** Fix the accepting word `w`, `|w| = T`. Along its run every
head and nonblank cell stays in the window `[-s, s]` (the branch-space
hypothesis at `w` itself, through the interval structure of visited sets —
the `Turing.NDTM.visitedWith` analogues of `abs_pos_lt_card_visited` and
`mem_visited_of_ne_none`, named fill obligations). If two prefixes of the run
share a `Turing.NDTM.coreSum`, splice out the cycle: by
`Turing.NDTM.coreSum_stepWith` (iterated along the remaining choice bits) the
spliced run replays the suffix's vertices, so it halts with the same summary —
and `accept` as a final summary is acceptance, outputs being read only through
the summary. Iterate until all vertices along the branch are distinct; their
codes (`Turing.MultiTapeTM.ConfigCount.coreCode` within the window, paired
with the summary) are injective (`coreCode_inj`), so the branch length is at
most `N.configBound x.length s`, and the shortened word pads back up to the
exact count (`Turing.FinNDTM.AcceptsWithin.mono` — `AcceptsWithin` demands
exact word length); if the original `T` is already smaller, pad directly
instead (the same `mono`). In either case it is the **accepting branch**
that stays halted under padding (`Turing.NDTM.runWith_of_halt`): the
statement carries no sibling-halting hypothesis and needs none (round-1
audit, finding 1). -/
theorem acceptsWithin_of_spaceUsedWith_le (N : FinNDTM Bool) {x : List Bool}
    {T s : ℕ} (hacc : N.AcceptsWithin x T)
    (hs : ∀ w : List Bool, w.length = T →
      N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ s) :
    N.AcceptsWithin x (N.configBound x.length s) := by
  sorry

/-- **The packaged graph interface** (spec, fill pending — phase P4.2): a
machine deciding `L` in space `s` accepts exactly the members within the
vertex-count budget. This is the single statement the exponential-time
simulation ([AB09, Theorem 4.2]), `Complexity.NL_subset_P`, and Savitch's
midpoint recursion all consume.

**Proof sketch.** Forward: `Turing.FinNDTM.DecidesInSpace` supplies the budget
`T` with all-branch halting, the branch-space bound, and the acceptance
equivalence; `Turing.FinNDTM.acceptsWithin_of_spaceUsedWith_le` shortens to
the vertex count. Backward: given an accepting branch at the vertex-count
budget, compare with `T`: if the budget exceeds `T`, the branch's `T`-prefix
is already halted (`Turing.NDTM.HaltsWithin`) with the run frozen
(`Turing.NDTM.runWith_of_halt`), so the prefix accepts and membership follows
from the equivalence at `T`; otherwise pad
(`Turing.FinNDTM.AcceptsWithin.mono`). -/
theorem DecidesInSpace.mem_iff_acceptsWithin_configBound {N : FinNDTM Bool}
    {L : Language Bool} {s : ℕ → ℕ} (h : N.DecidesInSpace L s) (x : List Bool) :
    x ∈ L ↔ N.AcceptsWithin x (N.configBound x.length (s x.length)) := by
  sorry

end FinNDTM

end Turing

namespace Complexity

open Turing

/-- **Nondeterministic space sits inside exponential time**
([AB09, Theorem 4.2, third inclusion]): for space-constructible `S`,
`NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c · (S n + 1)))`. The union over `c` renders the
book's `2^{O(S(n))}`; the `+ 1` is a harmless normalization whose job is the
input-head absorption (`n + 2 ≤ 2 ^ (S n + 1)`, since `SpaceConstructible`
bundles `logSpace n ≤ S n`) — the displayed time bound is everywhere positive
regardless, and the `c = 0` component has exponent `0` (round-1 audit,
finding 5).

**Proof sketch.** Let `N` decide `L` in space `c₀ · s`. The deterministic
simulator, on input `x`: (i) computes the window radius `c₀ · S |x|` from the
constructibility witness; (ii) runs a breadth-first search over the
configuration graph on the coded vertices
(`Turing.MultiTapeTM.ConfigCount.coreCode` plus the summary): the vertex count
is `N.configBound |x| (c₀·S |x|) ≤ 2^{O(S |x|)}` (the exponent arithmetic of
the received `configBound_logSpace_le`, generalized from `logSpace` to `S`),
each vertex has out-degree two computed by one transition-table application,
and the search maintains a visited table of coded vertices — the catalog
copy/compare/increment routines and the loop combinator are the engine
(`machine-library-design.md` §12 R3, `Build/Catalog.lean`); (iii) accepts iff
a vertex with halted state and `accept` summary is reached, which is
membership by
`Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound` and
`Turing.NDTM.reflTransGen_cfgStep_iff`. Total time: vertices × edges × table
operations, `2^{O(S n)}`, normalized into the stated exponent with the
`n + 2 ≤ 2^{S n + 1}` absorption. Fill obligations, named: the BFS controller
(continuation budget anticipated), the vertex codec machine, the
bound-generalized `configBound` arithmetic. -/
theorem NSPACE_subset_exp_dtime (S : ℕ → ℕ) (hS : SpaceConstructible S) :
    NSPACE S ⊆ ⋃ c : ℕ, DTIME fun n => 2 ^ (c * (S n + 1)) := by
  sorry

/-- **`NL ⊆ P`** — the nondeterministic step of the p. 92 chain
([AB09, §4.1.2 with Exercise 4.3's premise]). At `S = logSpace` the vertex
count is polynomial, so the breadth-first search runs in polynomial time.

**Proof sketch.** Instantiate the simulator of
`Complexity.NSPACE_subset_exp_dtime` at `logSpace`: the vertex count
`N.configBound n (c₀ · logSpace n)` is bounded by a fixed polynomial in `n`
(the received `Turing.FinTM.configBound_logSpace_le` arithmetic, times three),
so the BFS with its table fits in `DTIME (n^d + 1)` for a fixed `d` —
with count arithmetic analogous to the received
`Complexity.LOGSPACE_subset_P` — whose own proof keeps the original machine
and bounds its halting time through `ComputesInSpace`, constructing no
search or visited table (round-1 audit, finding 4). Continuation budget
anticipated: the external prior art's `NL ⊆ P` was a full submission on its
own ([Bon26] context in `machine-library-design.md` §12 — reachability-table
construction; design only, nothing ported). -/
theorem NL_subset_P : NL ⊆ P := by
  sorry

/-- **Polynomial-time reductions are too coarse below `P`**
([AB09, Exercise 4.3]): every language that is neither empty nor full is
`NL`-hard under polynomial-time Karp reductions — so `NL`-completeness is
only meaningful for the logspace reductions of phase P4.4
([AB09, Definition 4.16]; the exercise's intended moral, recorded in its
docstring rather than left implicit). **Corrects the exercise's printed
wording**: p. 93 says "complete for `NL`" for an arbitrary nontrivial target,
which is false without target membership in `NL` (an undecidable nontrivial
target defeats completeness); only hardness is claimed here, and
completeness additionally requires `L ∈ NL` (round-1 audit, finding 2).

**Proof sketch.** Fix witnesses `y₀ ∈ L` and `z₀ ∉ L` (classical choice). For
`L' ∈ NL`, `Complexity.NL_subset_P` gives a polynomial-time decider of `L'`;
the reduction `f x := if x ∈ L' then y₀ else z₀` is polynomial-time
computable by the conditional catalog (`Complexity.polyTimeComputable_ite`
over the decider with two `Complexity.polyTimeComputable_const` branches),
and `x ∈ L' ↔ f x ∈ L` holds by the choice of witnesses. -/
theorem polyTimeReducible_of_mem_NL (L : Language Bool) (hy : ∃ y, y ∈ L)
    (hz : ∃ z, z ∉ L) {L' : Language Bool} (hL' : L' ∈ NL) : L' ≤ₚ L := by
  sorry

end Complexity
```


## ===== TCSlib/Complexity/SpaceComplexity/Constructible.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.ClassP.TimeConstructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space-constructible functions

[AB09, §4.1, p. 79]: `S : ℕ → ℕ` is space-constructible when some machine
computes `S(|x|)` from `x` within `O(S(|x|))` space, and the book's standing
convention is `S(n) > log n`. The definition mirrors
`Complexity.TimeConstructible` — output in binary (`Nat.bits`), constant slack
`c · S n`, which implements the book's own asymptotic space convention
([AB09, p. 79]: "computes `S(|x|)` in `O(S(|x|))` space"); whether an
exact-space variant is also satisfiable is a separate question this campaign
does not pose (the chapter-1 exact-**time** refutation does not transfer: a
space deadline forces no premature halt — round-1 audit, finding 3) — and
carries the book's
convention as the conjunct `∀ n, logSpace n ≤ S n`, so that downstream
statements (the space hierarchy, Savitch) can draw on it without restating it;
results needing only weaker hypotheses must say so (seeded to the P4.1 audit).

## Main definitions

* `Complexity.SpaceConstructible` — the binary-output, constant-slack,
  above-log form. [AB09, §4.1, p. 79]

## Main results (sorried; phase-P4.1 statements)

* `Complexity.spaceConstructible_logSpace` — `log` is space-constructible.
* `Complexity.spaceConstructible_linear` — `n + 1` is space-constructible.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, p. 79.)
-/

namespace Complexity

open Turing

/-- A function `S` is **space-constructible** when it dominates the logarithm
(`Complexity.logSpace`, the book's standing `S(n) > log n` convention carried as
data) and some machine computes the binary representation of `S (|x|)` from `x`
within `c · S (|x|)` visited work-tape cells. Mirrors
`Complexity.TimeConstructible` (binary output via `Nat.bits`, constant slack).
[AB09, §4.1, p. 79] -/
def SpaceConstructible (S : ℕ → ℕ) : Prop :=
  (∀ n, logSpace n ≤ S n) ∧
  ∃ c : ℕ, 0 < c ∧ ∃ M : FinTM Bool,
    M.ComputesInSpace (fun x => (S x.length).bits) fun n => c * S n

/-- **The logarithm is space-constructible.** [AB09, p. 79: "all functions of
interest, including `log n`, …, are space-constructible"]

**Proof sketch.** Fill obligations: a machine that (i) counts the input length
in binary on a work tape by one left-to-right input scan with a binary
increment at each step (the `Turing.counterTM`/`incrementTM` idiom — P11 of
`machine-library-design.md` §4, space-annotated per §12 R3) — the counter word
has `|Nat.bits n| = logSpace n` cells **for `n > 0` only** (`Nat.bits 0 = []`
has length `0 ≠ logSpace 0 = 1`; round-1 audit, finding 1), so (ii) the empty
input is special-cased to emit `(logSpace 0).bits = [true]` directly, and
otherwise the machine computes the counter word's bit-length by a second count
and emits its bits. Space: the counters and markers fit in
`A·(logSpace n + 1) ≤ 2A·logSpace n` visited cells (boundary cells included
before absorbing, since `logSpace n ≥ 1`); the dominance conjunct is `le_refl`
at `S = logSpace`. -/
theorem spaceConstructible_logSpace : SpaceConstructible logSpace := by
  sorry

/-- **Linear space is constructible**: `n ↦ n + 1` is space-constructible (the
`+ 1` prevents the inherited zero-bound collapse at `n = 0` — the P0
convention, `SpaceComplexity/ZeroSpace.lean` — and satisfies the dominance
conjunct; zero-space classes are nonempty, so this is about collapse, not
vacuity).

**Proof sketch.** The input-scan counter of
`Complexity.spaceConstructible_logSpace`, **initialized at `1`** so that after
`n` consumed symbols it holds `n + 1` (an uncorrected length counter holds `n`
and emits the wrong word — round-1 audit, finding 2); emit its bits. Space:
the counter's binary width plus fixed administrative cells fit in
`A·(n + 2) ≤ 2A·(n + 1)` visited cells; dominance is `logSpace n ≤ n + 1`
(`1 ≤ 1` at `n = 0`; a small arithmetic lemma otherwise). -/
theorem spaceConstructible_linear : SpaceConstructible fun n => n + 1 := by
  sorry

end Complexity
```


## ===== TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.NSPACE

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The space complexity classes: `PSPACE`, `NPSPACE`, `NL`, `coNL`

[AB09, Definition 4.5]: `PSPACE = ⋃_c SPACE(n^c)`, `NPSPACE = ⋃_c NSPACE(n^c)`,
`L = SPACE(log n)` and `NL = NSPACE(log n)`. The deterministic logarithmic class
already exists as `Complexity.LOGSPACE` (received surface, phase P0); this
module adds the remaining three, in the campaign's polynomial normal form
`n ^ c + 1` (mirroring `Complexity.P`/`Complexity.EXP`) and with the received
`Complexity.logSpace` bound (`⌊log₂ n⌋ + 1`). `coNL` is the complement class,
in the same complement form as `Complexity.coNP` — [AB09, §4.3.2]; the
Immerman-Szelepcsényi theorem (`NL = coNL`) is a phase-P4.4 statement, not
claimed here.

## Main definitions

* `Complexity.PSPACE`, `Complexity.NPSPACE` — polynomial space, deterministic
  and nondeterministic. [AB09, Definition 4.5]
* `Complexity.NL` — nondeterministic logarithmic space. [AB09, Definition 4.5]
* `Complexity.coNL` — complements of `NL` languages. [AB09, §4.3.2]

## Main results (sorried; phase-P4.1 statements)

* `Complexity.space_poly_subset_PSPACE`, `Complexity.PSPACE_subset_NPSPACE`,
  `Complexity.LOGSPACE_subset_NL` — the definitional inclusions.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2, Definition 4.5; §4.3.2.)
-/

namespace Complexity

/-- **`PSPACE`** [AB09, Definition 4.5]: the languages decidable in polynomial
space, `⋃ c, SPACE (n ^ c + 1)` in the campaign's polynomial normal form. -/
def PSPACE : Set (Language Bool) := ⋃ c : ℕ, SPACE fun n => n ^ c + 1

/-- **`NPSPACE`** [AB09, Definition 4.5]: the languages decidable in
nondeterministic polynomial space. `PSPACE = NPSPACE` is Savitch's theorem
([AB09, Theorem 4.14], phase P4.2), not a definitional fact. -/
def NPSPACE : Set (Language Bool) := ⋃ c : ℕ, NSPACE fun n => n ^ c + 1

/-- **`NL`** [AB09, Definition 4.5]: the languages decidable in nondeterministic
logarithmic space, over the received bound `Complexity.logSpace` (whose `+ 1`
floor and missing `s ≥ log n` convention are recorded divergences — see
`TCSlib.Complexity.SpaceComplexity.Basic`). -/
def NL : Set (Language Bool) := NSPACE logSpace

/-- **`coNL`** [AB09, §4.3.2]: the complements of `NL` languages, in the same
complement form as `Complexity.coNP`. `NL = coNL` is the Immerman-Szelepcsényi
theorem ([AB09, Theorem 4.20], phase P4.4). -/
def coNL : Set (Language Bool) := {L | Lᶜ ∈ NL}

/-- Every fixed-degree polynomial space class is contained in `PSPACE`.

**Proof sketch.** `Set.subset_iUnion` at the given degree, as for
`Complexity.dtime_poly_subset_P`. -/
theorem space_poly_subset_PSPACE (c : ℕ) : SPACE (fun n => n ^ c + 1) ⊆ PSPACE := by
  sorry

/-- `PSPACE ⊆ NPSPACE`: determinism is a special case, degree by degree.

**Proof sketch.** `Complexity.SPACE_subset_NSPACE` at each degree, then the
union is monotone (`Set.iUnion_mono`). -/
theorem PSPACE_subset_NPSPACE : PSPACE ⊆ NPSPACE := by
  sorry

/-- `L ⊆ NL` (in the campaign's names, `LOGSPACE ⊆ NL`).
[AB09, p. 92 chain]

**Proof sketch.** `Complexity.SPACE_subset_NSPACE` at `Complexity.logSpace`. -/
theorem LOGSPACE_subset_NL : LOGSPACE ⊆ NL := by
  sorry

end Complexity
```


## ===== TCSlib/Complexity/SpaceComplexity/NSPACE.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.NondeterministicSpace
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.SpaceComplexity.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic space-bounded computation and `NSPACE`

[AB09, Definition 4.1, second clause]: `L ∈ NSPACE(s(n))` when some NDTM decides
`L` within `c · s(n)` work-tape cells on inputs of length `n`, regardless of its
nondeterministic choices. Built on the campaign NDTM
(`TCSlib.Complexity.TuringMachine.Nondeterministic`) with the visited-cells
branch-space measure (`Turing.NDTM.spaceUsedWith`).

## Divergences from [AB09] (shared with `SPACE` where applicable)

* **All branches halt** (`AroraBarakChapters3-4Plan.md`, CH34-Q7, maintainer
  decision 2026-10-08): deciding includes `Turing.NDTM.HaltsWithin` — every
  choice word of the budget length halts the machine. [AB09, Remark 4.3] notes
  this restriction is harmless for space-constructible bounds; adopting it
  outright matches `Complexity.NTIME`'s totality convention and the
  configuration-counting arguments of phase P4.2.
* **Visited cells, not nonblank cells**: [AB09]'s own Definition 4.1 counts
  visited locations for `SPACE` but nonblank locations for `NSPACE`; the
  campaign uses the visited measure for both (recorded in
  `TCSlib.Complexity.SpaceComplexity.Basic`).
* **Exact-length choice words**: the space condition quantifies over choice
  words of length exactly `T` (the halting budget); by
  `Turing.NDTM.spaceUsedWith_append_of_halt` all-branch halting at `T` freezes
  every branch's space, so longer words add nothing.
* Constants are absorbed as `c · s n`, and there is **no** `s(n) ≥ log n` side
  condition, as for `Complexity.SPACE`.

## Main definitions

* `Turing.FinNDTM.DecidesInSpace` — all branches halt, all branches respect the
  space bound, and membership is existential-branch acceptance.
  [AB09, Definition 4.1]
* `Complexity.NSPACE` — the class, with constant absorption.
  [AB09, Definition 4.1]

## Main results (sorried; phase-P4.1 statements)

* `Complexity.NSPACE.mono` — monotone in the space bound.
* `Complexity.SPACE_subset_NSPACE` — [AB09, Theorem 4.2, second inclusion].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definition 4.1, Remark 4.3,
  Theorem 4.2.)
-/

namespace Turing.FinNDTM

/-- The machine `N` decides `L` in space `s`, nondeterministically: on every
input `x` there is a budget `T` such that every branch of length `T` has halted
(`Turing.NDTM.HaltsWithin` — the all-branch convention, CH34-Q7), every such
branch has visited at most `s |x|` work-tape cells, and `x ∈ L` exactly when
some branch accepts. The time budget `T` is existential and unconstrained — only
space is bounded; by `Turing.NDTM.spaceUsedWith_append_of_halt` the exact-length
quantifiers already govern all longer branches. [AB09, Definition 4.1, second
clause, visited-cells convention] -/
def DecidesInSpace (N : FinNDTM Bool) (L : Language Bool) (s : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, ∃ T : ℕ,
    N.tm.HaltsWithin x T ∧
    (∀ w : List Bool, w.length = T →
      N.tm.spaceUsedWith w (N.tm.initCfg x) ≤ s x.length) ∧
    (x ∈ L ↔ N.AcceptsWithin x T)

end Turing.FinNDTM

namespace Complexity

open Turing

/-- The class of languages decidable nondeterministically in space `c · s` for
some constant `c`: `L ∈ NSPACE s` iff some finite binary-alphabet NDTM decides
it within `c · s n` visited work-tape cells on inputs of length `n`, in the
sense of `Turing.FinNDTM.DecidesInSpace`. [AB09, Definition 4.1] -/
def NSPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.DecidesInSpace L fun n => c * s n}

/-- `NSPACE` is monotone in the space bound.

**Proof sketch.** The same machine and the same per-input budgets witness the
larger bound: `c · s₁ n ≤ c · s₂ n` pointwise (`Nat.mul_le_mul_left`), and only
the space inequality mentions the bound. -/
theorem NSPACE.mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : NSPACE s₁ ⊆ NSPACE s₂ := by
  sorry

/-- **Deterministic space is nondeterministic space**: `SPACE s ⊆ NSPACE s`.
[AB09, Theorem 4.2, second inclusion]

**Proof sketch.** Let `M` decide `L` in space `c · s` with halting time `t x` on
input `x` (`Turing.FinTM.DecidesInSpace` supplies both). Embed as
`M.toFinNDTM`; take the budget `T := t x`. Every choice word of length `T` runs
identically to `M`'s deterministic run (`Turing.MultiTapeTM.toNDTM_runWith`), so
all-branch halting is `M`'s halting, the branch space is `M`'s space by
`Turing.MultiTapeTM.toNDTM_spaceUsedWith`, and the unique branch accepts (output
`[true]`) iff `x ∈ L` by the indicator equation — mirroring
`Complexity.DTIME_subset_NTIME`. -/
theorem SPACE_subset_NSPACE (s : ℕ → ℕ) : SPACE s ⊆ NSPACE s := by
  sorry

end Complexity
```


## ===== TCSlib/Complexity/SpaceComplexity/Basic.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space-bounded computation, `SPACE`, `L`, and implicitly logspace computable functions

[AB09, Def 4.1]: a language is in `SPACE(s(n))` when some machine decides it while
visiting at most `c · s(n)` work-tape cells on every input of length `n`; `L = SPACE(log n)`
[AB09, Def 4.5]. [AB09, Def 4.16]: a function `f` is *implicitly logspace computable* when it
is polynomially bounded and the two languages "the `i`-th bit of `f(x)` is `1`" and
"`i` is a position of `f(x)`" are in `L`.

## The machine model

We reuse the campaign's machines (`Turing.FinTM Bool`) unchanged. They already have the
shape of [AB09, Fig. 4.1]:

* **the input tape is read-only**: a transition (`Turing.Action`) has no write component
  for the input tape, only a head move, clamped to the input and its two boundary blanks;
* **the output tape is write-once, append-only**: a step appends at most one symbol;
* **space is the number of work-tape cells visited** (`Turing.MultiTapeTM.spaceUsed`, the
  sum over the work tapes of the visited cells), exactly the measure of [AB09, Def 4.1]
  ("at most `c · s(n)` locations on M's work tapes (excluding the input tape) are ever
  visited by M's head").

## Main definitions

* `Turing.FinTM.ComputesInSpace` — `M` computes `f`, halting on every input, visiting at most
  `s(|x|)` work cells.
* `Turing.FinTM.DecidesInSpace` — `M` decides `L` within space `s`. [AB09, Def 4.1]
* `Complexity.SPACE` — the class of languages decidable in space `c · s(n)`. [AB09, Def 4.1]
* `Complexity.logSpace` — the logarithmic space bound `⌊log₂ n⌋ + 1`.
* `Complexity.LOGSPACE` — the class `L = SPACE(log n)`. [AB09, Def 4.5]
* `Complexity.indexLang` — the language `{⟨x, i⟩ | p x i}` with `i` in binary.
* `Complexity.ImplicitlyLogspaceComputable` — [AB09, Def 4.16].

## Main results

* `Complexity.SPACE.mono` — `SPACE` is monotone in the space bound.

## Divergences from [AB09]

* **The logarithm.** [AB09] writes `SPACE(log n)` and requires `s(n) ≥ log n` (p. 79). We use
  `logSpace n = ⌊log₂ n⌋ + 1`, which is at least `1` (so short inputs get constant space, the
  standard reading of the convention) and is `Θ(log n)` for `n ≥ 2`.
* **Pairs and indices** (Def 4.16). The pair `⟨x, i⟩` is `Turing.pairEncode x (Nat.bits i)`:
  the campaign's self-delimiting pairing with the index in little-endian binary without
  redundant zeros (`Nat.bits 0 = []`). Indices are **`0`-based**: the bit language is
  `{⟨x, i⟩ | f(x)ᵢ = 1}` with `f(x)ᵢ` the `i`-th bit from `0`, and the length language is
  `{⟨x, i⟩ | i < |f(x)|}` where [AB09] writes `i ≤ |f(x)|` for `1`-based `i`.
* **Polynomial bound** (Def 4.16). [AB09] asks `|f(x)| ≤ |x|^c`; at `x = ε` that forces
  `f(ε) = ε` for `c ≥ 1`. We use the campaign normal form `|f(x)| ≤ C · (|x| + 1)^c`
  (`Complexity.PolyBound` shape).
* **Halting.** Deciding (resp. computing) includes halting on every input, as in [AB09]
  ("a TM M deciding L"); the space bound is checked at the halting time, and since space is
  monotone in time and frozen after halting this is the space of the whole computation.
* **One measure for both classes.** [AB09, Def 4.1]'s own wording splits: *visited*
  work-tape locations for `SPACE` (the clause quoted above) but *nonblank* locations for
  `NSPACE`. The campaign convention is the visited-cells measure for both; the planned
  `NSPACE` (`AroraBarakChapters3-4Plan.md`, phase P4.1) counts visited cells along every
  choice word, with all branches halting.
* **Zero bounds collapse the class** (P0 reception audit, round 1, finding 1): every
  work tape's visited set contains its origin, so every machine satisfies
  `M.k ≤ spaceUsed` on every input at every time. A single length with `s n = 0`
  therefore forces a deciding machine to have **no work tapes at all** — and then it
  has zero space on *every* input — so `SPACE s = SPACE (fun _ => 0)` (semantically
  the two-way-finite-automaton class) whenever `s` has a zero; multiplicative
  absorption cannot repair this, since `c * 0 = 0`. In particular the literal
  `SPACE (fun n => n)` is **not** linear space: `n = 0` collapses it. **Campaign
  convention:** every asymptotic chapter statement uses an everywhere-positive bound —
  `fun n => n + 1`, `fun n => n ^ c + 1`, `Complexity.logSpace` — never a bound with a
  zero. The characterization and the harmless-normalization identities are the sanity
  layer `TCSlib.Complexity.SpaceComplexity.ZeroSpace`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definitions 4.1 and 4.5; §4.3, Definition 4.16.)
-/

namespace Turing.FinTM

/-- The machine `M` computes `f` in space `s`: on every input `x` it halts with output `f x`,
and up to that time it has visited at most `s |x|` work-tape cells (summed over its work
tapes). The input tape (read-only) and the output tape (append-only) do not count.
[AB09, Def 4.1, for functions] -/
def ComputesInSpace (M : FinTM Bool) (f : List Bool → List Bool) (s : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, ∃ t, M.ComputesInTime x (f x) t ∧
    M.tm.spaceUsed (M.tm.initCfg x) t ≤ s x.length

/-- The machine `M` decides `L` in space `s`: it computes the indicator `[x ∈ L]` (a
one-bit output) in space `s`. [AB09, Def 4.1] -/
def DecidesInSpace (M : FinTM Bool) (L : Language Bool) (s : ℕ → ℕ) : Prop :=
  M.ComputesInSpace (fun x => [MultiTapeTM.indicator (L : Set (List Bool)) x]) s

/-- A space bound can be weakened. -/
theorem ComputesInSpace.mono {M : FinTM Bool} {f : List Bool → List Bool} {s s' : ℕ → ℕ}
    (h : M.ComputesInSpace f s) (hs : ∀ n, s n ≤ s' n) : M.ComputesInSpace f s' := by
  intro x
  obtain ⟨t, ht, hsp⟩ := h x
  exact ⟨t, ht, hsp.trans (hs _)⟩

end Turing.FinTM

namespace Complexity

open Turing

/-- **`SPACE(s)`** [AB09, Def 4.1]: the languages decided by some finite binary-alphabet
machine visiting at most `c · s(n)` work-tape cells on inputs of length `n`, for some
constant `c`. -/
def SPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L fun n => c * s n}

/-- `SPACE` is monotone in the space bound. -/
theorem SPACE.mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : SPACE s₁ ⊆ SPACE s₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, hM.mono fun n => Nat.mul_le_mul_left c (h n)⟩

/-- The logarithmic space bound `⌊log₂ n⌋ + 1`: `Θ(log n)`, and at least `1`, following the
convention `s(n) ≥ log n` of [AB09, p. 79]. -/
def logSpace (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- **The class `L`** [AB09, Def 4.5]: `L = SPACE(log n)`, the languages decidable by a
machine visiting `O(log n)` work-tape cells. (Named `LOGSPACE` to keep the letter `L` free
for language variables.) -/
def LOGSPACE : Set (Language Bool) := SPACE logSpace

/-- The language `{⟨x, i⟩ | p x i}`, the pair encoded as `Turing.pairEncode x (Nat.bits i)`
(index in little-endian binary). The shape of the two languages of [AB09, Def 4.16]. -/
def indexLang (p : List Bool → ℕ → Prop) : Language Bool :=
  {w | ∃ x i, w = pairEncode x (Nat.bits i) ∧ p x i}

/-- **Implicitly logspace computable functions** [AB09, Def 4.16]: `f` is polynomially
bounded, `|f(x)| ≤ C · (|x| + 1)^c`, and both the bit language
`{⟨x, i⟩ | f(x)ᵢ = 1}` and the length language `{⟨x, i⟩ | i < |f(x)|}` are in `L`.
Indices are `0`-based and written in binary (`Nat.bits`); see the module docstring for the
divergences (`0`-based `i < |f(x)|` for the book's `1`-based `i ≤ |f(x)|`, and the `+ 1`
in the polynomial bound). -/
def ImplicitlyLogspaceComputable (f : List Bool → List Bool) : Prop :=
  (∃ C c : ℕ, ∀ x : List Bool, (f x).length ≤ C * (x.length + 1) ^ c) ∧
  indexLang (fun x i => (f x).getD i false = true) ∈ LOGSPACE ∧
  indexLang (fun x i => i < (f x).length) ∈ LOGSPACE

/-- `logSpace` is monotone. -/
lemma logSpace_mono {a b : ℕ} (h : a ≤ b) : logSpace a ≤ logSpace b := by
  unfold logSpace
  have := Nat.log_mono_right (b := 2) h
  omega

end Complexity
```


## ===== TCSlib/Complexity/TimeHierarchy/CodePrefix.lean =====

```
/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Code-prefix duplication

Glue for the diagonal machine of the time hierarchy theorem
[AB09, Theorem 3.1, proof].

* **Code-prefix duplication.** The universal machine of this development
  (`Turing.universal`) reads its input as `pairEncode α x` — code first. The diagonal
  machine must run the machine coded in its input *on that same input*. On an input
  of the shape `x = pairEncode α w` this is `pairEncode α x`, which is the aligned
  doubled-bit prefix of `x` (up to and including the separator) followed by all of
  `x`. The machine `preTM` computes `x ↦ scanPre x ++ x` in linear time, where
  `scanPre` is that prefix (`scanPre_pairEncode`).
* **Timed partial composition** is `Turing.FinTM.bufferedCompTM_computesInTime`
  (`TCSlib.Complexity.TuringMachine.Composition`).

## Design

* Fixing the code `α` and padding the *input* (rather than taking ever longer codes of
  the same machine, as [AB09] does via "every machine has infinitely many codes") is
  forced here: the universal machine's constant depends on the code string itself,
  with no uniform bound in its length (see `Turing.universal`), so the diagonal
  argument must simulate one fixed code on longer and longer inputs.

## Main definitions

* `Complexity.TimeHierarchy.scanPre` — the aligned doubled-bit prefix of a word.
* `Complexity.TimeHierarchy.preTM` — the prefix-duplication machine.

## Main results

* `Complexity.TimeHierarchy.preTM_computes` — `preTM` computes `x ↦ scanPre x ++ x`
  within `3|x| + 5` steps.
* `Complexity.TimeHierarchy.scanPre_pairEncode_append` — on `pairEncode α w` the
  computed word is `pairEncode α (pairEncode α w)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, §3.1.)
-/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-- The aligned doubled-bit prefix of a word: read aligned pairs, keep them while
they are `00` or `11`, and stop after (and including) the first other pair; a final
unpaired bit is kept. On `pairEncode α w` this is the doubled `α` and the separator. -/
def scanPre : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | b :: b' :: r => b :: b' :: (if b = b' then scanPre r else [])

/-- On a code-first pair, the scanned prefix is the doubled code and the separator. -/
lemma scanPre_pairEncode (α w : List Bool) :
    scanPre (pairEncode α w) = (α.flatMap fun b => [b, b]) ++ [false, true] := by
  induction α with
  | nil => simp [pairEncode, scanPre]
  | cons b α ih =>
    simp only [pairEncode, List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc] at ih ⊢
    simp only [scanPre, if_true]
    rw [ih]

/-- **Prefix duplication on code-first pairs:** `scanPre x ++ x = pairEncode α x` for
`x = pairEncode α w`. -/
lemma scanPre_pairEncode_append (α w : List Bool) :
    scanPre (pairEncode α w) ++ pairEncode α w = pairEncode α (pairEncode α w) := by
  rw [scanPre_pairEncode]
  simp [pairEncode]

/-- Control states of the prefix-duplication machine. -/
inductive PreState where
  | scan0 : PreState
  | scan1 : Bool → PreState
  | rwStart : PreState
  | rwScan : PreState
  | copy : PreState
  deriving DecidableEq, Fintype

/-- Transition table of the prefix-duplication machine (no work tapes): scan and emit
aligned pairs while they are doubled bits, rewind the input head, then copy the
whole input to the output. -/
def preTr (q : PreState) (inp : Option Bool) (_work : Fin 0 → Option Bool) :
    Action 0 Bool PreState :=
  match q, inp with
  | .scan0, some b => ⟨.pos, fun _ => (none, 0), some b, some (.scan1 b)⟩
  | .scan0, none => controlAction 0 (some .rwStart)
  | .scan1 b, some b' =>
    ⟨.pos, fun _ => (none, 0), some b', some (if b = b' then .scan0 else .rwStart)⟩
  | .scan1 _, none => controlAction 0 (some .rwStart)
  | .rwStart, _ => controlAction .neg (some .rwScan)
  | .rwScan, some _ => controlAction .neg (some .rwScan)
  | .rwScan, none => controlAction .pos (some .copy)
  | .copy, some b => ⟨.pos, fun _ => (none, 0), some b, some .copy⟩
  | .copy, none => ⟨0, fun _ => (none, 0), none, none⟩

/-- **The prefix-duplication machine**: on input `x` it outputs `scanPre x ++ x`. -/
def preTM : FinTM Bool where
  k := 0
  State := PreState
  tm := { q₀ := .scan0, tr := preTr }

/-- One live step applies the table. -/
private lemma preTM_step {x : List Bool} (c : Cfg 0 Bool PreState x) (q : PreState)
    (h : c.state = some q) :
    preTM.tm.step c = (preTr q c.inputSymbol c.workTapeSymbols).apply c := by
  unfold MultiTapeTM.step
  rw [h]
  rfl

/-- The scanning phase: from input position `i + 1` with `drop i x = rest`, the
machine reaches the rewind state within `|rest| + 1` steps, having appended
`scanPre rest`.

**Proof sketch.** Strong recursion on `rest`, two symbols at a time. If `rest` is
empty, the head reads a blank and one step enters the rewind state, emitting nothing
new. If `rest = [b]`, two steps read `b`, then a blank, and enter the rewind state
having emitted what `scanPre [b]` prescribes. If `rest = b :: b' :: r`, two steps read
the pair and emit `b, b'`; when `b = b'` the machine is back in the scanning state two
cells further on, and the recursive call on `r` gives the rest of the run (with step
count `2 + t ≤ |rest| + 1`); when `b ≠ b'` the pair is the terminator of the prefix and
the machine is already in the rewind state after two steps. -/
private theorem pre_scan (x : List Bool) : ∀ (rest : List Bool) (i : ℕ)
    (c : Cfg 0 Bool PreState x), x.drop i = rest → i ≤ x.length →
    c.state = some .scan0 → c.inputPos.val = i + 1 →
    ∃ t ≤ rest.length + 1, (preTM.tm.runFrom c t).state = some .rwStart ∧
      (preTM.tm.runFrom c t).output = c.output ++ scanPre rest
  | [], i, c, hd, hi, hs, hp => by
    have hin : c.inputSymbol = none := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    refine ⟨1, le_refl _, ?_, ?_⟩
    · change (preTM.tm.step c).state = _
      rw [preTM_step c _ hs, hin]; rfl
    · change (preTM.tm.step c).output = _
      rw [preTM_step c _ hs, hin]; simp [preTr, controlAction, scanPre]
  | [b], i, c, hd, hi, hs, hp => by
    have hlt : i < x.length := by
      have := congrArg List.length hd; simp at this; omega
    have hin : c.inputSymbol = some b := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    let c1 := preTM.tm.step c
    have hc1 : c1 = (preTr .scan0 (some b) c.workTapeSymbols).apply c := by
      simp only [c1]; rw [preTM_step c _ hs, hin]
    have hp1 : c1.inputPos.val = (i + 1) + 1 := by
      rw [hc1]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    have hin1 : c1.inputSymbol = none := by
      rw [inputSymbol_at c1 (i + 1) (by omega) hp1, ← List.head?_drop]
      have : x.drop (i + 1) = [] := by rw [← List.drop_drop, hd]; rfl
      rw [this]; rfl
    have hs1 : c1.state = some (.scan1 b) := by rw [hc1]; rfl
    refine ⟨2, le_refl _, ?_, ?_⟩
    · change (preTM.tm.step c1).state = _
      rw [preTM_step c1 _ hs1, hin1]; rfl
    · change (preTM.tm.step c1).output = _
      rw [preTM_step c1 _ hs1, hin1, hc1]
      simp [preTr, controlAction, scanPre]
  | b :: b' :: r, i, c, hd, hi, hs, hp => by
    have hlt : i + 1 < x.length := by
      have := congrArg List.length hd; simp at this; omega
    have hin : c.inputSymbol = some b := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    let c1 := preTM.tm.step c
    have hc1 : c1 = (preTr .scan0 (some b) c.workTapeSymbols).apply c := by
      simp only [c1]; rw [preTM_step c _ hs, hin]
    have hp1 : c1.inputPos.val = (i + 1) + 1 := by
      rw [hc1]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    have hd1 : x.drop (i + 1) = b' :: r := by rw [← List.drop_drop, hd]; rfl
    have hin1 : c1.inputSymbol = some b' := by
      rw [inputSymbol_at c1 (i + 1) (by omega) hp1, ← List.head?_drop, hd1]; rfl
    have hs1 : c1.state = some (.scan1 b) := by rw [hc1]; rfl
    let c2 := preTM.tm.step c1
    have hc2 : c2 = (preTr (.scan1 b) (some b') c1.workTapeSymbols).apply c1 := by
      simp only [c2]; rw [preTM_step c1 _ hs1, hin1]
    have hp2 : c2.inputPos.val = (i + 2) + 1 := by
      rw [hc2]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp1]
    have hout2 : c2.output = c.output ++ [b, b'] := by
      rw [hc2, hc1]; simp [preTr]
    have hrun2 : preTM.tm.runFrom c 2 = c2 := rfl
    by_cases hbb : b = b'
    · have hs2 : c2.state = some .scan0 := by rw [hc2]; simp [preTr, hbb]
      have hd2 : x.drop (i + 2) = r := by rw [← List.drop_drop, hd]; rfl
      obtain ⟨t, ht, h1, h2⟩ := pre_scan x r (i + 2) c2 hd2 (by omega) hs2 hp2
      refine ⟨2 + t, by simp; omega, ?_, ?_⟩
      · rw [MultiTapeTM.runFrom_add, hrun2]; exact h1
      · rw [MultiTapeTM.runFrom_add, hrun2, h2, hout2]
        simp [scanPre, hbb]
    · have hs2 : c2.state = some .rwStart := by rw [hc2]; simp [preTr, hbb]
      refine ⟨2, by simp, ?_, ?_⟩
      · rw [hrun2]; exact hs2
      · rw [hrun2, hout2]; simp [scanPre, hbb]

/-- The copying phase: from input position `i + 1` with `drop i x = rest`, the machine
halts after exactly `|rest| + 1` steps, having appended `rest`.

**Proof sketch.** Recursion on `rest`. On an empty remainder the head reads a blank
and the machine halts in one step without output. On `b :: r` one step copies `b` to
the output and advances the input head, staying in the copy state; the recursive call
on `r` from position `i + 2` accounts for the remaining `|r| + 1` steps. -/
private theorem pre_copy (x : List Bool) : ∀ (rest : List Bool) (i : ℕ)
    (c : Cfg 0 Bool PreState x), x.drop i = rest → i ≤ x.length →
    c.state = some .copy → c.inputPos.val = i + 1 →
    (preTM.tm.runFrom c (rest.length + 1)).state = none ∧
      (preTM.tm.runFrom c (rest.length + 1)).output = c.output ++ rest
  | [], i, c, hd, hi, hs, hp => by
    have hin : c.inputSymbol = none := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    change (preTM.tm.step c).state = none ∧ (preTM.tm.step c).output = _
    rw [preTM_step c _ hs, hin]
    simp [preTr]
  | b :: r, i, c, hd, hi, hs, hp => by
    have hlt : i < x.length := by
      have := congrArg List.length hd; simp at this; omega
    have hin : c.inputSymbol = some b := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    let c1 := preTM.tm.step c
    have hc1 : c1 = (preTr .copy (some b) c.workTapeSymbols).apply c := by
      simp only [c1]; rw [preTM_step c _ hs, hin]
    have hp1 : c1.inputPos.val = (i + 1) + 1 := by
      rw [hc1]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    have hd1 : x.drop (i + 1) = r := by rw [← List.drop_drop, hd]; rfl
    have hs1 : c1.state = some .copy := by rw [hc1]; rfl
    obtain ⟨h1, h2⟩ := pre_copy x r (i + 1) c1 hd1 (by omega) hs1 hp1
    have hrun : preTM.tm.runFrom c ((b :: r).length + 1) =
        preTM.tm.runFrom c1 (r.length + 1) := by
      rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    rw [hrun]
    refine ⟨h1, ?_⟩
    rw [h2, hc1]
    simp [preTr]

/-- **Prefix duplication** [glue for AB09, Theorem 3.1]: `preTM` computes
`x ↦ scanPre x ++ x` within `3|x| + 5` steps.

**Proof sketch.** Scan (`pre_scan`, at most `|x| + 1` steps, emitting `scanPre x`),
rewind the input head (`Turing.FinTM.timed_rewind`, at most `|x| + 3` steps), and copy
(`pre_copy`, exactly `|x| + 1` steps, emitting `x`). -/
theorem preTM_computes (x : List Bool) :
    preTM.ComputesInTime x (scanPre x ++ x) (3 * x.length + 5) := by
  obtain ⟨t₁, ht₁, h1, h2⟩ := pre_scan x x 0 (preTM.tm.initCfg x) (by simp) (by omega) rfl rfl
  let c₁ := preTM.tm.runFrom (preTM.tm.initCfg x) t₁
  obtain ⟨r, hr, hrun⟩ := timed_rewind preTM.tm PreState.rwStart PreState.rwScan
    (some .copy) (fun inp _ => by cases inp <;> rfl) (fun inp _ => by cases inp <;> rfl) c₁ h1
  let c₂ : Cfg 0 Bool PreState x := {c₁ with state := some .copy, inputPos := 1}
  have hc := pre_copy x x 0 c₂ (by simp) (by omega) rfl rfl
  have hrun' : preTM.tm.runFrom (preTM.tm.initCfg x) (t₁ + r + (x.length + 1)) =
      preTM.tm.runFrom c₂ (x.length + 1) := by
    rw [MultiTapeTM.runFrom_add _ (t₁ + r), MultiTapeTM.runFrom_add _ t₁ r]
    change preTM.tm.runFrom (preTM.tm.runFrom c₁ r) _ = _
    rw [hrun]
  have hcomp : preTM.ComputesInTime x (scanPre x ++ x) (t₁ + r + (x.length + 1)) := by
    rw [computesInTime_iff, hrun']
    refine ⟨hc.1, ?_⟩
    rw [hc.2]
    change c₁.output ++ x = _
    rw [h2]
    rfl
  apply hcomp.mono
  have := c₁.inputPos.isLt
  omega

end Complexity.TimeHierarchy
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


## ===== TCSlib/Complexity/ClassNP/NP.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The class NP

[AB09, §2.1, Definition 2.1]: a language `L` is in `NP` when membership has
polynomial-length certificates verifiable in polynomial time — `x ∈ L` iff some
certificate `u` of the prescribed polynomial length makes the verifier accept.

## Design and deviations from [AB09]

* **The certificate length is an explicit polynomial formula**, exactly
  `C · (|x| + 1)^c` bits: the definition quantifies over the *coefficient and
  degree*, not over an abstract length function. This is the phase-1 audit's
  repair (findings 1-2, Argument A): a length function constrained only by a
  numerical bound can itself smuggle undecidable information through length
  arithmetic — certificate *content* never enters — putting every
  length-determined language in the class. An explicit formula is computable,
  monotone, and information-free by construction. The numerical helper
  `Complexity.PolyBound` survives for bound bookkeeping only; it never appears
  in a class definition.
* **The verifier is a language, not a machine.** We render "polynomial-time TM
  `M` with `M(x, u) = 1`" as membership of the concatenation `x ++ u` in a
  verifier language `V ∈ P` — reusing the audited Chapter-1 class. The phase-1
  audit certified this abstraction sound (finding 10): `V ∈ P` supplies one
  uniform total decider, and for a fixed length formula, `V`'s values off the
  constrained strings change no membership statement.
* **Pairing is concatenation in the exact-length form** ([AB09], footnote 4):
  the definition never splits `x ++ u` — the membership equivalence quantifies
  over `x` and `u` separately, and with the explicit formula, any consumer
  that must recover the split can (`n + n·formula` arithmetic is computable
  and `n ↦ n + C(n+1)^c` is strictly increasing). The **bounded-length**
  variant ([AB09, Exercise 2.1]) is different: with `∃ u, |u| ≤ …` and plain
  concatenation, the empty certificate forces `V ⊆ L`, which collapses every
  prefix-free language to its verifier (audit finding 2, Argument B) — so the
  bounded form below pairs its inputs with the audited self-delimiting
  `Turing.pairEncode` instead.
* **Certificates have length exactly `C(|x|+1)^c`** (Definition 2.1 verbatim,
  with the formula for [AB09]'s "polynomial `p`").

## Main definitions

* `Complexity.NP` — the class NP. [AB09, Definition 2.1]

## Main results

* `Complexity.P_subset_NP` — `P ⊆ NP` (empty certificates). [AB09, §2.1]
* `Complexity.mem_NP_iff_exists_length_le` — bounded-length *paired*
  certificates define the same class. [AB09, Exercise 2.1, repaired per the
  phase-1 audit]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1, Definition 2.1, pp. 39-41;
  Exercise 2.1.)
-/

namespace Complexity

open Turing

/-- **The class NP** [AB09, Definition 2.1]: `L ∈ NP` iff there are a certificate
coefficient `C`, degree `c`, and a polynomial-time-decidable verifier language
`V ∈ P` such that `x ∈ L` exactly when some certificate `u` of length exactly
`C · (|x| + 1)^c` makes the concatenation `x ++ u` a member of `V`. The
certificate length is an explicit formula in `|x|` — never an abstract
function — so it is computable and carries no information beyond `|x|`
(phase-1 audit, finding 1). -/
def NP : Set (Language Bool) :=
  {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- **`P ⊆ NP`** [AB09, §2.1, after Definition 2.1]: a language decidable in
polynomial time is verifiable with empty certificates.

**Proof sketch.** Take `C = 0` (certificate length `0 · (n+1)^0 = 0`) and
`V = L`: the only certificate of length `0` is `[]`, and `x ++ [] = x`, so the
membership equivalence is the identity. The audit confirmed this covers
`L = ∅`, `L = univ`, and `x = []` (finding table, question 2). -/
theorem P_subset_NP : P ⊆ NP := by
  intro L hL
  refine ⟨0, 0, L, hL, fun x => ?_⟩
  simp only [zero_mul, List.length_eq_zero_iff, exists_eq_left, List.append_nil]


/-- Remove the last `true` marker and the following false suffix. No marker
means failure, so stripping cannot cross the certificate boundary. -/
private def stripCertificate : List Bool → Option (List Bool)
  | [] => none
  | b :: v => match stripCertificate v with
    | some u => some (b :: u)
    | none => if b then some [] else none

/-- An all-false certificate region contains no marker. -/
private lemma stripCertificate_false (k : ℕ) :
    stripCertificate (List.replicate k false) = none := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, stripCertificate, ih]

/-- Stripping a padded certificate recovers the original certificate, including
the empty certificate and certificates that themselves contain `true`. -/
private lemma stripCertificate_pad (u : List Bool) (k : ℕ) :
    stripCertificate (u ++ true :: List.replicate k false) = some u := by
  induction u with
  | nil => simp [stripCertificate, stripCertificate_false]
  | cons b u ih => simp [stripCertificate, ih]

/-- Successful stripping identifies precisely the last-true decomposition.

**Proof sketch.** Induct from the right through the recursive call. A marker in
the tail survives, with the head prepended; otherwise the head must be `true`
and the tail must be all false. The simultaneous no-marker assertion supplies
that latter fact. -/
private lemma stripCertificate_spec (v : List Bool) :
    (stripCertificate v = none ↔ v = List.replicate v.length false) ∧
    (∀ u, stripCertificate v = some u ↔
      ∃ k, v = u ++ true :: List.replicate k false) := by
  induction v with
  | nil => simp [stripCertificate]
  | cons b v ih =>
    cases hv : stripCertificate v with
    | none =>
      have hfalse := ih.1.mp hv
      constructor
      · constructor
        · intro h
          cases b with
          | false => simpa [List.replicate_succ] using congrArg (false :: ·) hfalse
          | true => simp [stripCertificate, hv] at h
        · intro h
          rw [h]
          exact stripCertificate_false _
      · intro u
        constructor
        · intro h
          cases b with
          | false => simp [stripCertificate, hv] at h
          | true =>
            have hu : u = [] := by simpa [stripCertificate, hv] using h.symm
            subst u
            exact ⟨v.length, by simpa using congrArg (true :: ·) hfalse⟩
        · rintro ⟨j, hj⟩
          rw [hj]
          exact stripCertificate_pad u j
    | some w =>
      obtain ⟨k, hk⟩ := (ih.2 w).mp hv
      constructor
      · constructor
        · simp [stripCertificate, hv]
        · intro heq
          have : stripCertificate (b :: v) = none := by
            rw [heq]; exact stripCertificate_false _
          simp [stripCertificate, hv] at this
      · intro u
        constructor
        · intro h
          have hu : b :: w = u := by simpa [stripCertificate, hv] using h
          subst u
          exact ⟨k, by simp [hk]⟩
        · rintro ⟨j, hj⟩
          rw [hj]
          exact stripCertificate_pad u j

/-- The padded total length is strictly increasing, even at degree zero. -/
private lemma certificateTotal_strictMono (C c : ℕ) :
    StrictMono (fun n : ℕ => n + (C + 1) * (n + 1) ^ c) := by
  intro m n h
  dsimp only
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.le_of_lt h) 1) c
  have hmul := Nat.mul_le_mul_left (C + 1) hpow
  omega

/-- The repaired exact width leaves room for the mandatory marker. -/
private lemma certificate_room (C c n : ℕ) :
    C * (n + 1) ^ c + 1 ≤ (C + 1) * (n + 1) ^ c := by
  have h := Nat.one_le_pow c (n + 1) (Nat.succ_pos n)
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Bounded search for the unique legal split. Failure remains `none`. -/
private def certificateSplit (C c m : ℕ) : Option ℕ :=
  (List.range (m + 1)).find? fun n => n + (C + 1) * (n + 1) ^ c == m

/-- The bounded search succeeds exactly at a solution of the length equation.

**Proof sketch.** Any solution is at most the total length, hence lies in the
search range. A failed search would reject that very solution; a successful
search returns a solution, and strict monotonicity makes it unique. -/
private lemma certificateSplit_spec (C c m n : ℕ) :
    certificateSplit C c m = some n ↔ n + (C + 1) * (n + 1) ^ c = m := by
  constructor
  · intro h
    have hh := List.find?_some (p := fun i => i + (C + 1) * (i + 1) ^ c == m) h
    simpa only [beq_iff_eq] using hh
  · intro h
    have hn : n ∈ List.range (m + 1) := by simp only [List.mem_range]; omega
    cases hs : certificateSplit C c m with
    | none =>
      have hf := (List.find?_eq_none.mp hs) n hn
      simp [h] at hf
    | some j =>
      have hj : j + (C + 1) * (j + 1) ^ c = m :=
        by
          have hh := List.find?_some (p := fun i => i + (C + 1) * (i + 1) ^ c == m) hs
          simpa only [beq_iff_eq] using hh
      have : j = n := (certificateTotal_strictMono C c).injective (hj.trans h.symm)
      simp [this]

/-- In particular the empty input has no legal split. -/
private lemma certificateSplit_zero (C c : ℕ) : certificateSplit C c 0 = none := by
  cases h : certificateSplit C c 0 with
  | none => rfl
  | some n =>
    have hn := (certificateSplit_spec C c 0 n).mp h
    have hr := certificate_room C c n
    omega

/-- The forward verifier parses the audited pairing, enforces the original
exact width, and consults the old verifier on the concatenated word. -/
private def pairedVerifier (C c : ℕ) (V : Language Bool) : Language Bool :=
  {y | ∃ x u, pairDecode y = some (x, u) ∧
    u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}

/-- On an encoded pair, the forward verifier imposes exactly the prescribed
length test and the old verification condition. -/
private lemma pairedVerifier_pair (C c : ℕ) (V : Language Bool) (x u : List Bool) :
    pairEncode x u ∈ pairedVerifier C c V ↔
      u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V := by
  change (∃ a b, pairDecode (pairEncode x u) = some (a, b) ∧
    b.length = C * (a.length + 1) ^ c ∧ a ++ b ∈ V) ↔ _
  simp [pairDecode_pairEncode]

/-- A malformed pair is rejected before consulting the old verifier. -/
private lemma pairedVerifier_malformed (C c : ℕ) (V : Language Bool) (y : List Bool)
    (h : pairDecode y = none) : y ∉ pairedVerifier C c V := by
  rintro ⟨x, u, hp, -⟩
  rw [h] at hp
  cases hp

/-- The reverse verifier rejects a missing length split or marker, rechecks the
original bound after stripping, and consults the old paired verifier. -/
private def paddedVerifier (C c : ℕ) (V : Language Bool) : Language Bool :=
  {y | ∃ n u, certificateSplit C c y.length = some n ∧
    stripCertificate (y.drop n) = some u ∧
    u.length ≤ C * (n + 1) ^ c ∧ pairEncode (y.take n) u ∈ V}

/-- A missing solution of the length equation is rejection, not a default
split. In particular this covers the empty input by `certificateSplit_zero`. -/
private lemma paddedVerifier_no_split (C c : ℕ) (V : Language Bool) (y : List Bool)
    (h : certificateSplit C c y.length = none) : y ∉ paddedVerifier C c V := by
  rintro ⟨n, u, hn, -⟩
  rw [h] at hn
  cases hn

/-- For the prescribed exact width the search recovers precisely the input
boundary; no marker in the input can be mistaken for a certificate marker. -/
private lemma paddedVerifier_append (C c : ℕ) (V : Language Bool) (x v : List Bool)
    (hv : v.length = (C + 1) * (x.length + 1) ^ c) :
    x ++ v ∈ paddedVerifier C c V ↔ ∃ u, stripCertificate v = some u ∧
      u.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x u ∈ V := by
  have hs : certificateSplit C c (x ++ v).length = some x.length := by
    apply (certificateSplit_spec _ _ _ _).mpr
    simp only [List.length_append, hv]
  change (∃ n u, certificateSplit C c (x ++ v).length = some n ∧
    stripCertificate ((x ++ v).drop n) = some u ∧
    u.length ≤ C * (n + 1) ^ c ∧ pairEncode ((x ++ v).take n) u ∈ V) ↔ _
  rw [hs]
  simp

/-- An all-false region is rejected even when the input itself contains true
bits: the strip function is applied only after the recovered boundary. -/
private lemma paddedVerifier_no_marker (C c : ℕ) (V : Language Bool) (x : List Bool) :
    x ++ List.replicate ((C + 1) * (x.length + 1) ^ c) false ∉ paddedVerifier C c V := by
  rw [paddedVerifier_append C c V x _ (List.length_replicate ..)]
  simp only [stripCertificate_false, reduceCtorEq, false_and, exists_false, not_false_eq_true]

/-- Even a correctly marked certificate that fits in the enlarged exact
region is rejected if its stripped witness exceeds the original bound. -/
private lemma paddedVerifier_too_long (C c : ℕ) (V : Language Bool) (x u : List Bool)
    (k : ℕ) (hv : (u ++ true :: List.replicate k false).length =
      (C + 1) * (x.length + 1) ^ c) (hu : C * (x.length + 1) ^ c < u.length) :
    x ++ (u ++ true :: List.replicate k false) ∉ paddedVerifier C c V := by
  rw [paddedVerifier_append C c V x _ hv]
  rintro ⟨u', hs, hu', -⟩
  rw [stripCertificate_pad] at hs
  have he : u = u' := Option.some.inj hs
  subst u'
  exact Nat.not_le_of_lt hu hu'

/-- Padding and stripping give the exact witness equivalence; the runtime
obligations are separate from this purely semantic statement. -/
private lemma paddedVerifier_witness (C c : ℕ) (V : Language Bool) (x : List Bool) :
    (∃ v, v.length = (C + 1) * (x.length + 1) ^ c ∧ x ++ v ∈ paddedVerifier C c V) ↔
    ∃ u, u.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x u ∈ V := by
  constructor
  · rintro ⟨v, hv, h⟩
    obtain ⟨u, -, hu, hV⟩ := (paddedVerifier_append C c V x v hv).mp h
    exact ⟨u, hu, hV⟩
  · rintro ⟨u, hu, hV⟩
    let k := (C + 1) * (x.length + 1) ^ c - (u.length + 1)
    have hroom : u.length + 1 ≤ (C + 1) * (x.length + 1) ^ c :=
      (Nat.add_le_add_right hu 1).trans (certificate_room C c x.length)
    have hv : (u ++ true :: List.replicate k false).length =
        (C + 1) * (x.length + 1) ^ c := by
      simp only [List.length_append, List.length_cons, List.length_replicate]
      dsimp [k]
      omega
    refine ⟨_, hv, (paddedVerifier_append C c V x _ hv).mpr ?_⟩
    exact ⟨u, stripCertificate_pad u k, hu, hV⟩


/-- The catalog's guarded pair-to-concatenation function. -/
private def verifier_concat (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (a, b) => a ++ b
  | none => []

/-- The two bounded searches are literally equal at the shifted coefficient. -/
private lemma verifier_split_bridge (C c : ℕ) :
    solveSplit (C + 1) c = certificateSplit C c := rfl

/-- The library's reverse scan implements the existing recursive strip spec.

**Proof sketch.** The semantic strip specification gives either an all-false
word or its last-true decomposition. Reversing that decomposition makes the
library scan discard exactly the false suffix and the marker. -/
private lemma verifier_strip_bridge : splitAtLastTrue = stripCertificate := by
  funext v
  cases hs : stripCertificate v with
  | none =>
    have hv := (stripCertificate_spec v).1.mp hs
    rw [hv]
    simp [splitAtLastTrue]
  | some u =>
    obtain ⟨k, hk⟩ := ((stripCertificate_spec v).2 u).mp hs
    rw [hk]
    simp [splitAtLastTrue]

/-- The original-bound test returns one Boolean, rejecting parse failures. -/
private def verifier_bound (C c : ℕ) (z : List Bool) : Bool :=
  match pairDecode z with
  | some (a, b) => decide (b.length ≤ C * (a.length + 1) ^ c)
  | none => false

/-- P8 supplies the timed original-bound test, with its parameters unchanged. -/
private lemma verifier_poly_bound (C c : ℕ) :
    PolyTimeComputable (fun z => [verifier_bound C c z]) := by
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_pairLenCheck C c
  exact ⟨M, a, c + 1, hM⟩

/-- Normalize a `P` decider through the audited capture-and-branch host.
The W3 controller uses `capture_run` to capture the old verifier's complete
singleton verdict, including an emission on its halting transition. -/
private lemma verifier_poly_indicator {V : Language Bool} (hV : V ∈ P) :
    PolyTimeComputable (fun x => [MultiTapeTM.indicator V x]) := by
  obtain ⟨C, c, M, hM⟩ := mem_P_iff.mp hV
  have h : PolyTimeComputable (fun x => [MultiTapeTM.indicator V x]) := ⟨M, C, c, hM⟩
  have hc := polyTimeComputable_ite h (polyTimeComputable_const [true])
    (polyTimeComputable_const [false])
  convert hc using 1
  funext x
  cases MultiTapeTM.indicator V x <;> rfl

/-- A polynomial-time singleton indicator is a polynomial-time decider. -/
private lemma verifier_mem_P {V : Language Bool}
    (h : PolyTimeComputable (fun x => [MultiTapeTM.indicator V x])) : V ∈ P := by
  obtain ⟨M, C, c, hM⟩ := h
  exact mem_P_iff.mpr ⟨C, c, M, hM⟩

/-- The reverse length comparison uses general pairing and P8 at `(1,1)`.

**Proof sketch.** Generate `C(|a|+1)^c` in unary and prepend one bit. Pair the
old payload with this generated word. P8 then tests
`C(|a|+1)^c + 1 ≤ |b| + 1`, exactly the required reverse inequality. -/
private lemma verifier_poly_reverseBound (C c : ℕ) :
    PolyTimeComputable (fun z =>
      [decide (C * ((pairFstD z).length + 1) ^ c ≤ (pairSndD z).length)]) := by
  have hfst := polyTimeComputable_pairFstD
  have hsnd := polyTimeComputable_pairSndD
  obtain ⟨U, a, hU⟩ := FinTM.computesFunInTime_polyUnary C c
  have hgen : PolyTimeComputable (fun x => List.replicate (C * (x.length + 1) ^ c) true) :=
    ⟨U, a, c + 1, hU⟩
  have hpre := polyTimeComputable_of_linear (FinTM.computesFunInTime_prepend [true])
  have hpair := hsnd.pairEncode (hpre.comp (hgen.comp hfst))
  simpa only [Function.comp_def, verifier_bound, pairDecode_pairEncode,
    List.singleton_append, List.length_cons, List.length_replicate, Nat.pow_one,
    Nat.one_mul, Nat.add_le_add_iff_right] using (verifier_poly_bound 1 1).comp hpair

/-- The forward verifier is decided by the guarded exact-width pipeline.

**Proof sketch.** Validate the pairing grammar, test both length inequalities,
concatenate the components, and capture the old decider's verdict. All branches
are timed catalog compositions; malformed words never reach the old verifier. -/
private lemma pairedVerifier_mem_P (C c : ℕ) {V : Language Bool} (hV : V ∈ P) :
    pairedVerifier C c V ∈ P := by
  classical
  have hfalse := polyTimeComputable_const [false]
  have hcat : PolyTimeComputable verifier_concat :=
    polyTimeComputable_of_linear FinTM.computesFunInTime_pairConcat
  have hrun := (verifier_poly_indicator hV).comp hcat
  have hreverse := polyTimeComputable_ite (verifier_poly_reverseBound C c) hrun hfalse
  have hwidth := polyTimeComputable_ite (verifier_poly_bound C c) hreverse hfalse
  have hfinal := polyTimeComputable_ite
    (polyTimeComputable_of_linear FinTM.computesFunInTime_pairValid) hwidth hfalse
  apply verifier_mem_P
  convert hfinal using 1
  funext y
  cases hy : pairDecode y with
  | none =>
    simp [hy, pairedVerifier, MultiTapeTM.indicator]
  | some p =>
    rcases p with ⟨x, u⟩
    by_cases hlo : u.length ≤ C * (x.length + 1) ^ c
    · by_cases hhi : C * (x.length + 1) ^ c ≤ u.length
      · have he := Nat.le_antisymm hlo hhi
        simp [hy, verifier_bound, pairFstD, pairSndD, verifier_concat,
          pairedVerifier, MultiTapeTM.indicator, he]
      · have he : u.length ≠ C * (x.length + 1) ^ c := fun h => hhi h.ge
        simp [hy, verifier_bound, pairFstD, pairSndD,
          pairedVerifier, MultiTapeTM.indicator, hlo, hhi, he]
    · have he : u.length ≠ C * (x.length + 1) ^ c := fun h => hlo h.le
      simp [hy, verifier_bound, pairedVerifier, MultiTapeTM.indicator, hlo, he]

/-- The shifted split machine retains the recovered input as the pair head. -/
private def verifier_split (C c : ℕ) (y : List Bool) : List Bool :=
  match solveSplit (C + 1) c y.length with
  | some n => pairEncode (y.take n) (y.drop n)
  | none => []

/-- Strip only the payload of a valid pair, retaining its original input. -/
private def verifier_strip (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (a, v) =>
    match splitAtLastTrue v with
    | some u => pairEncode a u
    | none => []
  | none => []

/-- The reverse verifier is decided by shifted split, marker, and bound guards.

**Proof sketch.** P10 at `(C+1,c)` recovers and retains the input prefix. A
grammar guard rejects its empty failure output. P9 strips only that pair's
payload; a second grammar guard rejects marker failure. P8 at the original
`(C,c)` rechecks the stripped witness before the captured old paired decider
runs. The search equation gives `n ≤ |y|`, so the retained prefix has exactly
length `n`; the two vocabulary bridges identify the original semantic spec. -/
private lemma paddedVerifier_mem_P (C c : ℕ) {V : Language Bool} (hV : V ∈ P) :
    paddedVerifier C c V ∈ P := by
  classical
  obtain ⟨S, a, hS⟩ := FinTM.computesFunInTime_splitSolve (C + 1) c
  have hsplit : PolyTimeComputable (verifier_split C c) := ⟨S, a, c + 2, hS⟩
  obtain ⟨T, b, hT⟩ := FinTM.computesFunInTime_stripLast
  have hstrip : PolyTimeComputable verifier_strip := ⟨T, b, 2, hT⟩
  have hvalid := polyTimeComputable_of_linear FinTM.computesFunInTime_pairValid
  have hfalse := polyTimeComputable_const [false]
  have hbound := polyTimeComputable_ite (verifier_poly_bound C c)
    (verifier_poly_indicator hV) hfalse
  have hmarked := polyTimeComputable_ite hvalid hbound hfalse
  have hfound := polyTimeComputable_ite hvalid (hmarked.comp hstrip) hfalse
  have hfinal := hfound.comp hsplit
  apply verifier_mem_P
  convert hfinal using 1
  funext y
  cases hs : certificateSplit C c y.length with
  | none =>
    simp [verifier_split, verifier_split_bridge, hs,
      pairDecode, paddedVerifier, MultiTapeTM.indicator]
  | some n =>
    have hn : n ≤ y.length := by
      have heq := (certificateSplit_spec C c y.length n).mp hs
      omega
    cases ht : stripCertificate (y.drop n) with
    | none =>
      simp [verifier_split, verifier_split_bridge, hs,
        verifier_strip, verifier_strip_bridge, ht, pairDecode_pairEncode,
        pairDecode, paddedVerifier, MultiTapeTM.indicator]
    | some u =>
      by_cases hu : u.length ≤ C * (n + 1) ^ c
      · simp [verifier_split, verifier_split_bridge, hs,
          verifier_strip, verifier_strip_bridge, ht, pairDecode_pairEncode,
          verifier_bound, List.length_take, Nat.min_eq_left hn,
          paddedVerifier, MultiTapeTM.indicator, hu]
      · simp [verifier_split, verifier_split_bridge, hs,
          verifier_strip, verifier_strip_bridge, ht, pairDecode_pairEncode,
          verifier_bound, List.length_take, Nat.min_eq_left hn,
          paddedVerifier, MultiTapeTM.indicator, hu]

/-- **Bounded-length paired certificates define the same class**
[AB09, Exercise 2.1, repaired per the phase-1 audit]: `L ∈ NP` iff there are
`C`, `c`, and a verifier `V ∈ P` with
`x ∈ L ↔ ∃ u, |u| ≤ C(|x|+1)^c ∧ pairEncode x u ∈ V`. The bounded form pairs
`x` with `u` via the audited self-delimiting `Turing.pairEncode`: with plain
concatenation the empty certificate would force `V ⊆ L` and collapse every
prefix-free language (audit finding 2, Argument B).

**Proof sketch.** (⇒) From the exact form `(C, c, V)`, take the paired verifier
`V' := {pairEncode x u : |u| = C(|x|+1)^c ∧ x ++ u ∈ V}` with the same bound:
deciding `V'` parses the aligned pair (the `Turing.pairDecode` grammar; a
polynomial-time scan), checks the length equality against the explicit formula,
reassembles `x ++ u`, and runs `V`'s decider — each a named machine obligation
for the fill, none exotic. (⇐) From the bounded form `(C, c, V)`, take exact
length `R n = (C+1)(n+1)^c` — **admissible** for the repaired `NP`
(coefficient `C+1`, degree `c`; the round-2 audit refuted the earlier choice
`C(n+1)^c + 1`, which is not of the class's required shape — round-2
finding 1) — leaving `R n - C(n+1)^c = (n+1)^c ≥ 1` room for the marker. Pad
each certificate right-self-delimitingly to `u ++ [true] ++ false-run` of
length `R n`. The new verifier, on `y` of length `m`: search `n ≤ m` for
`n + R n = m` — strict increase of `n ↦ n + R n` gives **at most one**
solution, and none may exist (e.g. `y = []`, since `R n ≥ 1`): **reject if no
such `n` exists** (round-3 audit, finding 1); otherwise split `y = x ++ v` at
that unique `n` with
`|v| = R n ≥ 1`; reject if `v` has no `true` bit (so stripping never enters
`x`); split `v = u ++ [true] ++ false-run` at the **last** `true`; check the
*original* bound `|u| ≤ C(n+1)^c` — checkable precisely because the bound is
the explicit formula (phase-1 finding 2's residual error, fixed in round 1) —
and consult `V` on `pairEncode x u`. Every old witness pads within `R n`
(`|u| + 1 ≤ C(n+1)^c + 1 ≤ R n`); every accepted new witness strips back to
an old one (the round-2 audit's reconstruction, checked there across the
`C = 0`, `c = 0`, `x = []`, `u = []`, all-`false`, and malformed edge
cases). -/
theorem mem_NP_iff_exists_length_le {L : Language Bool} :
    L ∈ NP ↔ ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ u : List Bool, u.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x u ∈ V  := by
  constructor
  · rintro ⟨C, c, V, hV, hL⟩
    refine ⟨C, c, pairedVerifier C c V, ?_, fun x => ?_⟩
    · -- Remaining machine obligation: aligned parsing, the explicit polynomial
      -- length-equality test, concatenation, and timed execution of V's decider.
      exact pairedVerifier_mem_P C c hV
    · rw [hL x]
      constructor
      · rintro ⟨u, hu, hVu⟩
        exact ⟨u, hu.le, (pairedVerifier_pair C c V x u).mpr ⟨hu, hVu⟩⟩
      · rintro ⟨u, -, hVu⟩
        exact ⟨u, (pairedVerifier_pair C c V x u).mp hVu⟩
  · rintro ⟨C, c, V, hV, hL⟩
    refine ⟨C + 1, c, paddedVerifier C c V, ?_, fun x => ?_⟩
    · -- Remaining machine obligation: bounded split search, last-true stripping,
      -- the original-bound test, pairing, and timed execution of V's decider.
      exact paddedVerifier_mem_P C c hV
    · exact (hL x).trans (paddedVerifier_witness C c V x).symm

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


## ===== audits/logs/ch4-p43-r2-sweep.log =====

```
P4.3 R2 GATE SWEEP at commit aa02db412a3a3b8edd8c76bbdae3eb8f97cb07f6 (aa02db41), branch complexity/arora-barak-ch3-4, started 2026-10-08 22:38:15
== TCSlib/Complexity/Formulas/QBF
TCSlib/Complexity/Formulas/QBF.lean:119:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/Formulas/QBFEncoding
TCSlib/Complexity/Formulas/QBFEncoding.lean:88:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/ClassPSPACE/TQBF
TCSlib/Complexity/ClassPSPACE/TQBF.lean:118:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:161:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:223:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:271:8: warning: declaration uses 'sorry'
TCSlib/Complexity/ClassPSPACE/TQBF.lean:279:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/ClassPSPACE/Games
TCSlib/Complexity/ClassPSPACE/Games.lean:97:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/ClassPSPACE
== TCSlib/Complexity/SpaceComplexity/Hierarchy
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:107:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:180:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:197:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:226:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/Formulas
P4.3_R2_SWEEP_DONE
```


## ===== audits/logs/ch4-p43-r2-stylelint.log =====

```
== TCSlib/Complexity/Formulas ==
INFO  TCSlib/Complexity/Formulas/CNF.lean          259 lines; 5 public / 9 private declarations
INFO  TCSlib/Complexity/Formulas/CNFEncoding.lean  475 lines; 13 public / 9 private declarations
INFO  TCSlib/Complexity/Formulas/DNF.lean          172 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/Formulas/QBF.lean          125 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/Formulas/QBFEncoding.lean  91 lines; 5 public / 0 private declarations

style_lint: 0 FAIL, 0 WARN over 5 files
== TCSlib/Complexity/ClassPSPACE ==
INFO  TCSlib/Complexity/ClassPSPACE/Games.lean  101 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBF.lean   282 lines; 9 public / 0 private declarations

style_lint: 0 FAIL, 0 WARN over 2 files
== TCSlib/Complexity/SpaceComplexity ==
INFO  TCSlib/Complexity/SpaceComplexity/Basic.lean                          161 lines; 10 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean                    460 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    305 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Constructible.lean                  95 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean                 495 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean              246 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Examples.lean                       65 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean                      229 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean                   416 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Inclusions.lean                     97 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean  116 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean                  68 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean                  136 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean            146 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean                   307 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean                93 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean              333 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean                285 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean                551 lines; 30 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean                  226 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean                   176 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Call.lean                  360 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean            495 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean                 438 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean            508 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean               266 lines; 11 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean               358 lines; 20 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean                  455 lines; 15 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean               479 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean                423 lines; 29 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean                   333 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean                 376 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                662 lines > target 600
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean                662 lines; 24 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean              445 lines; 14 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean            571 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Program.lean               347 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean                   564 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/NSPACE.lean                         114 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Savitch.lean                        131 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean                   86 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean                  319 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean                      217 lines; 11 public / 0 private declarations

style_lint: 0 FAIL, 0 WARN over 42 files
```
