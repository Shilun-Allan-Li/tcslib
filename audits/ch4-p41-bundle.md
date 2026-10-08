# External audit pack — Chapter 4, phase P4.1 (space classes), statement gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase P4.1 —
the nondeterministic space measure, `NSPACE`, the classes
`PSPACE`/`NPSPACE`/`NL`/`coNL`, space-constructibility, Theorem 4.2's first two
inclusions, Example 4.6's memberships, and Example 4.7's parity language.
Statement phase per `workflow.md` §2-3; the gate closes on a round with zero
blockers and zero majors.

Audited at commit `edea2663` (branch `complexity/arora-barak-ch3-4`); the seven
files under audit are byte-identical to their landing commit `2cf44f1d` except
the facade's import/Contents additions. Under audit:
`TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean` and
`TCSlib/Complexity/SpaceComplexity/{NSPACE,SpaceClasses,Constructible,Inclusions,Examples}.lean`
plus the `SpaceComplexity.lean` facade additions — **14 sorried statements,
2 definitions of measure, 6 class/predicate definitions.**

**This phase sits directly on the P0-closed reception surface**
(`audits/ch34-p0-resolutions.md`): `Complexity.SPACE`, `LOGSPACE`,
`Turing.FinTM.ComputesInSpace`, `logSpace`, and the **positive-bound
convention** adopted there (one zero of a bound collapses `SPACE` to the
zero-work-tape class; every asymptotic chapter bound is everywhere positive —
`n + 1`, `n ^ c + 1`, `logSpace`). The `ZeroSpace.lean` sanity layer is attached
as closed context.

## Brief for the auditor

Definitions, statements, docstrings. Failure modes per `audits/TEMPLATE.md`,
plus this phase's own two: **a space measure whose quantifier shape silently
under- or over-counts along nondeterministic branches**, and **a class
definition that re-opens the zero-bound collapse the P0 gate just closed**.
Blind restatements for every definition; true-as-stated arguments for every
sorried statement; at least **5 adversarial instantiations**; no blanket
approvals. Sources: [AB09] §4.1 (Definition 4.1, Remark 4.3, Theorem 4.2,
Definition 4.5, Examples 4.6-4.7, Figure 4.1) and §4.1's `S(n) > log n`
convention (p. 79).

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch4-p41-sweep.log`, revision recorded at
  start): all seven modules, 0 `error:` lines, fresh `.olean`s, exactly **14**
  `declaration uses 'sorry'` warnings (NondeterministicSpace 2, NSPACE 2,
  SpaceClasses 3, Constructible 2, Inclusions 4, Examples 1).
* Style lint (`audits/logs/ch34-p31-p41-stylelint.log`): `SpaceComplexity`
  0 FAIL / 0 WARN over 35 files.
* Statement-freeze baseline: commit `edea2663`.

## Known deviations and design decisions (declared — verify each, flag others)

1. **All branches halt** (`FinNDTM.DecidesInSpace`; maintainer decision
   CH34-Q7): deciding includes `Turing.NDTM.HaltsWithin` at an existential
   per-input budget `T`. [AB09, Remark 4.3] calls the restriction harmless for
   space-constructible bounds; the campaign adopts it outright, matching
   `NTIME`'s totality convention.
2. **Visited cells for both classes**: [AB09, Def 4.1]'s own wording counts
   visited locations for `SPACE` but nonblank for `NSPACE`; the campaign uses
   visited for both (documented at the definition site since P0). The branch
   measure `Turing.NDTM.spaceUsedWith` mirrors the deterministic
   `visitedByTapeHead` along `runWith` prefixes.
3. **Exact-length choice words**: the space condition quantifies over words of
   length exactly `T`; sufficiency is pinned by the (sorried) invariance
   statement `spaceUsedWith_append_of_halt` — all-branch halting at `T`
   freezes every branch's space. The definition stands alone; the lemma
   documents why the quantifier shape loses nothing.
4. **The zero-bound collapse is inherited, knowingly**: `spaceUsedWith` also
   dominates the tape count (every tape's visited set contains its origin),
   so `NSPACE s` with a zero of `s` collapses exactly as `SPACE s` does. The
   phase's own classes are positive-normalized (`n ^ c + 1`, `logSpace`); no
   `NSPACE`-side `ZeroSpace` twin is stated in this skeleton — **seeded
   question 2 asks whether the gate should demand one**.
5. **`SpaceConstructible` carries the book's convention as data**:
   `(∀ n, logSpace n ≤ S n) ∧ ∃ c > 0, ∃ M, ComputesInSpace (bits ∘ S ∘ length)
   (c · S)` — mirroring `TimeConstructible` (binary output, constant slack);
   results needing only weaker hypotheses must say so. Instances stated:
   `logSpace` and `fun n => n + 1`.
6. **`DecidesInSpace`'s time is an existential per input** (inherited from the
   received `ComputesInSpace`): the P0 round-2 auditor already judged this the
   right shape ("no uniform-time existential has to be added"); the
   configuration-count layer recovers time from space when needed.
7. **Deferred, recorded in the plan**: `MULT` (Ex 4.7's second language) to
   P4.4 with the encoding conventions; the nondeterministic and
   polynomial-width ARM extensions to the §12 gate + colleague sync; Theorem
   4.2(iii) and Savitch to P4.2 (configuration graphs).
8. **`evenLang`** is `{x | x.count true % 2 = 0}`; its `LOGSPACE` membership
   statement predates the P0 round-2 addition of the *zero-tape* witnesses in
   `ZeroSpace.lean` — at fill time the membership should flow from
   `evenLang_mem_SPACE_zero` by monotonicity, and the `Examples.lean` sketch's
   one-work-tape machine is superseded (seeded as a harmonization note, not a
   statement change).
9. **`DTIME_subset_SPACE`** handles vanishing time bounds by the established
   emptiness convention (`DTIME` with a zero is empty — no machine halts in
   zero steps from a live initial state); the sketch names the absorbed
   constant `k · c + k`.

## Specific questions (prioritized)

1. **The branch space measure** (`visitedWith`/`spaceUsedWith`): blind-restate
   and check the prefix indexing (`Finset.range (w.length + 1)`, prefixes via
   `w.take j`) — are the endpoints right (initial head counted; the position
   after the full word counted; nothing beyond)? Is per-branch counting (one
   word at a time, no union over branches) the faithful reading of [AB09,
   Def 4.1]'s "regardless of its nondeterministic choices"?
2. **`DecidesInSpace`/`NSPACE` shape**: does the existential budget `T`
   together with exact-length quantifiers deliver Definition 4.1 + Remark
   4.3, or can an adversarial machine exploit the shape (e.g. huge `T` with
   accepting branches halting early and *late* branches visiting more —
   covered by all-branch halting at `T`?)? Should the gate demand the
   `NSPACE` zero-bound sanity twin (deviation 4), or does the P0-closed
   convention suffice?
3. **`SpaceConstructible`** (deviation 5): is bundling `logSpace n ≤ S n`
   faithful to p. 79's `S(n) > log n` (note `logSpace = ⌊log₂ n⌋ + 1` — check
   the off-by-one against the book's strict inequality at small `n`), and are
   the two instance statements true as stated (in particular
   `logSpace n ≤ n + 1` at `n = 0`)?
4. **Theorem 4.2(i)/(ii) statements** (`DTIME_subset_SPACE`,
   `SPACE_subset_NSPACE`): check the constant-absorption arithmetic
   (`k · (c·T + 1) ≤ (k·c + k) · T` needs `T ≥ 1` — is the vacuity route at
   zeros airtight given `DTIME`'s own convention?), and the measure-transfer
   sketch for (ii) (`toNDTM_spaceUsedWith`, sorried in this same phase — is
   the dependency ordering of the two sorried statements sound?).
5. **Example 4.6's statements** (`NP_subset_PSPACE`, `SAT3_mem_PSPACE`): is
   the class-level statement the book's, and is the certificate-cycling
   sketch's space ledger (certificate tape + re-executed verifier through
   `DTIME_subset_SPACE` + counter) complete, or does it hide a
   composition-with-space obligation this phase cannot discharge (the §12
   space clauses are a concurrent gate — flag any hard dependency)?
6. **Class definitions** (`PSPACE`, `NPSPACE`, `NL`, `coNL`,
   `LOGSPACE_subset_NL`, `PSPACE_subset_NPSPACE`): any daylight against
   [AB09, Definition 4.5] and §4.3.2, given the positive normal forms and the
   received `logSpace` floor?
7. **Adversarial instantiations to attempt**: `s = 0` through `NSPACE` (the
   collapse, deviation 4); a machine whose branches halt at different times
   under one `T`; `w = []` in the branch measure; `NL` at inputs of length
   `0`/`1`; `SpaceConstructible (fun n => n + 1)` at `n = 0`; `coNL` of the
   empty and full languages.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch4-p41-findings.md`; the gate closes on zero blockers and majors.


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


## ===== TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Nondeterministic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Space usage of nondeterministic machines

The space measure for binary-choice NDTMs, mirroring the deterministic
`Turing.MultiTapeTM.visitedByTapeHead`/`spaceUsedByTape`/`spaceUsed` along
choice-word runs: the cells a work-tape head visits during the run under a given
choice word, summed over the work tapes. This is the campaign convention for
[AB09, Definition 4.1]'s nondeterministic clause — **visited** cells, the same
measure as the deterministic `SPACE` ([AB09]'s own wording switches to "nonblank"
locations for `NSPACE`; the split and the convention are recorded in
`TCSlib.Complexity.SpaceComplexity.Basic`). The class `Complexity.NSPACE` built on
this measure lives in `TCSlib.Complexity.SpaceComplexity.NSPACE`.

## Main definitions

* `Turing.NDTM.visitedWith` — the set of cells visited by one work-tape head
  along the run under a choice word (prefixes included).
* `Turing.NDTM.spaceUsedWith` — total visited cells, summed over work tapes.
  [AB09, Definition 4.1, nondeterministic clause, visited-cells convention]

## Main results

* `Turing.NDTM.visitedWith_nil` — the empty run visits the starting positions.
* `Turing.MultiTapeTM.toNDTM_spaceUsedWith` — the embedded deterministic machine's
  space under any choice word is the deterministic space at that time (sorried;
  the measure-transfer obligation behind `SPACE ⊆ NSPACE`).
* `Turing.NDTM.spaceUsedWith_append_of_halt` — once a branch has halted, extending
  the choice word does not change the space (sorried; the invariance that makes
  the exact-length quantifier in `Complexity.NSPACE` sufficient).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definition 4.1.)
-/

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

namespace NDTM

/-- The cells visited by the head of work tape `i` along the run of `tm` under the
choice word `w` from `cfg`: the head positions after every prefix of `w` (the empty
prefix included, so the starting position always counts) — the nondeterministic
counterpart of `Turing.MultiTapeTM.visitedByTapeHead`. -/
def visitedWith (tm : NDTM k Symbol State) (w : List Bool)
    (cfg : Cfg k Symbol State input) (i : Fin k) : Finset ℤ :=
  (Finset.range (w.length + 1)).image fun j => (tm.runWith (w.take j) cfg).workTapePos i

/-- The space used by `tm` along the run under the choice word `w` from `cfg`: the
number of visited cells, summed over the work tapes — the nondeterministic
counterpart of `Turing.MultiTapeTM.spaceUsed`, for one branch. The input tape
(read-only) and the output tape (append-only) do not count.
[AB09, Definition 4.1, nondeterministic clause, visited-cells convention] -/
def spaceUsedWith (tm : NDTM k Symbol State) (w : List Bool)
    (cfg : Cfg k Symbol State input) : ℕ :=
  ∑ i, (tm.visitedWith w cfg i).card

/-- The empty choice word visits exactly the starting position of each head. -/
@[simp]
lemma visitedWith_nil (tm : NDTM k Symbol State) (cfg : Cfg k Symbol State input)
    (i : Fin k) : tm.visitedWith [] cfg i = {cfg.workTapePos i} := by
  simp [visitedWith]

/-- **Space stabilizes at halting**: if the branch under `w` has halted, running
under any extension `w ++ w'` visits no further cells, so the space is unchanged.
This is why `Complexity.NSPACE` may quantify over choice words of one exact
length: all-branch halting at that length freezes every branch's space.

**Proof sketch.** For `j ≤ |w|` the prefixes agree (`List.take_append_of_le_length`
-style splitting); for `j > |w|`, `(w ++ w').take j = w ++ w'.take (j - |w|)`,
`Turing.NDTM.runWith_append` factors the run through the halted configuration,
and `Turing.NDTM.runWith_of_halt` freezes it, so the head position equals the one
at prefix `w`. The two images therefore coincide (`Finset.image_congr` after
splitting `Finset.range`), tape by tape. -/
theorem spaceUsedWith_append_of_halt (tm : NDTM k Symbol State) {w : List Bool}
    {cfg : Cfg k Symbol State input} (h : (tm.runWith w cfg).state = none)
    (w' : List Bool) : tm.spaceUsedWith (w ++ w') cfg = tm.spaceUsedWith w cfg := by
  sorry

end NDTM

/-- The embedded deterministic machine's space along any choice word is its
deterministic space at the corresponding time: `toNDTM` ignores its choices
(`Turing.MultiTapeTM.toNDTM_runWith`), so the visited sets coincide prefix by
prefix. The measure-transfer obligation behind `Complexity.SPACE_subset_NSPACE`.

**Proof sketch.** Fix a tape `i`. For every `j ≤ |w|`,
`tm.toNDTM.runWith (w.take j) cfg = tm.runFrom cfg j` by
`Turing.MultiTapeTM.toNDTM_runWith` and `List.length_take_of_le`, so the images
defining `Turing.NDTM.visitedWith` and `Turing.MultiTapeTM.visitedByTapeHead`
agree pointwise on `Finset.range (|w| + 1)` (`Finset.image_congr`), and the card
sums agree. -/
theorem MultiTapeTM.toNDTM_spaceUsedWith (tm : MultiTapeTM k Symbol State)
    (w : List Bool) (cfg : Cfg k Symbol State input) :
    tm.toNDTM.spaceUsedWith w cfg = tm.spaceUsed cfg w.length := by
  sorry

end Turing

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
`c · S n` (the exact-bound variant is refuted in this model for the same reason
as in time, `audits/phase1-findings.md` finding 1) — and carries the book's
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
`machine-library-design.md` §4, space-annotated per §12 R3), using
`|bits n| = logSpace n` cells for the counter; then (ii) computes the bit-length
of that counter word — a second unary-to-binary count over `logSpace n` cells —
and emits its bits. Total space `O(logSpace n)`; the dominance conjunct is
`le_refl` at `S = logSpace`. -/
theorem spaceConstructible_logSpace : SpaceConstructible logSpace := by
  sorry

/-- **Linear space is constructible**: `n ↦ n + 1` is space-constructible (the
`+ 1` avoids the vacuous zero bound at `n = 0`, as in the campaign's polynomial
normal forms).

**Proof sketch.** The same input-scan counter as in
`Complexity.spaceConstructible_logSpace`, with the space budget now dominated by
the counter's `logSpace n ≤ n + 1` cells; dominance is `logSpace n ≤ n + 1`
(`Nat.log_lt` / induction — a small arithmetic lemma). -/
theorem spaceConstructible_linear : SpaceConstructible fun n => n + 1 := by
  sorry

end Complexity

```


## ===== TCSlib/Complexity/SpaceComplexity/Inclusions.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.ClassNP.SAT

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Time against space: the easy inclusions

The first two inclusions of [AB09, Theorem 4.2]
(`DTIME(S) ⊆ SPACE(S) ⊆ NSPACE(S)`), the polynomial-level corollaries on the
p. 92 chain (`P ⊆ PSPACE`), and the certificate-cycling memberships of
[AB09, Example 4.6] (`NP ⊆ PSPACE`, `3SAT ∈ PSPACE`). The third inclusion of
Theorem 4.2 (`NSPACE(S) ⊆ DTIME(2^{O(S)})`) needs the configuration-graph layer
and is phase P4.2; the parity example of [AB09, Example 4.7] lives in
`TCSlib.Complexity.SpaceComplexity.Examples`.

## Main results (sorried; phase-P4.1 statements)

* `Complexity.DTIME_subset_SPACE` — [AB09, Theorem 4.2, first inclusion].
* `Complexity.P_subset_PSPACE` — the polynomial corollary.
* `Complexity.NP_subset_PSPACE` — [AB09, Example 4.6].
* `Complexity.SAT3_mem_PSPACE` — [AB09, Example 4.6].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Theorem 4.2, Example 4.6.)
-/

namespace Complexity

open Turing

/-- **Time bounds space**: `DTIME T ⊆ SPACE T` — a machine can visit at most one
new cell per head per step. [AB09, Theorem 4.2, first inclusion]

**Proof sketch.** Let `M` decide `L` within `c · T n` steps. Each of `M`'s `k`
work-tape heads visits at most `c · T n + 1` cells in `c · T n` steps
(`Turing.MultiTapeTM.visitedByTapeHead` is an image of `Finset.range
(c·T n + 1)`, so `Finset.card_image_le` bounds it), hence
`spaceUsed ≤ k · (c · T n + 1) ≤ (k · c + k) · T n` whenever `T n ≥ 1`. If
`T n = 0` for some `n` then every `c · T` vanishes there and `DTIME T = ∅` by
the `Complexity.DTIME_eq_empty_of_exists_zero` argument (no machine halts in
`0` steps from a live initial state), so the inclusion is vacuous. The space
witness reuses `M` itself with the absorbed constant `k · c + k`, and the
halting time `c · T |x|` instantiates `Turing.FinTM.ComputesInSpace`'s
existential time. -/
theorem DTIME_subset_SPACE (T : ℕ → ℕ) : DTIME T ⊆ SPACE T := by
  sorry

/-- `P ⊆ PSPACE` — the polynomial-level corollary, on the p. 92 chain.

**Proof sketch.** Degree by degree: `DTIME (n^c + 1) ⊆ SPACE (n^c + 1)` by
`Complexity.DTIME_subset_SPACE`, then `Set.iUnion_mono` across the unions
defining `Complexity.P` and `Complexity.PSPACE`. -/
theorem P_subset_PSPACE : P ⊆ PSPACE := by
  sorry

/-- **Certificates can be cycled through in polynomial space**: `NP ⊆ PSPACE`.
[AB09, Example 4.6: "a similar idea of cycling through all potential
certificates applies to any NP language"]

**Proof sketch.** Let `L ∈ NP` with verifier language `V ∈ P` and certificate
length `C·(n+1)^c` (`Complexity.mem_NP_iff`-shape data). Fill obligations,
named for the brief: (i) a certificate enumerator holding the current
certificate `u` on a work tape and stepping it in place by fixed-width binary
increment (`incrementTM`, P11/§12 R3 — the space-annotated form), never using
more than `C·(n+1)^c + O(1)` cells; (ii) for each `u`, a run of `V`'s decider
on the **virtual input** `x ++ u` assembled from the input tape and the
certificate tape (the virtual-input idiom of
`TCSlib.Complexity.TuringMachine.UniversalStartup`), with the decider's space
bounded through `Complexity.DTIME_subset_SPACE` applied to `V`'s polynomial
time bound — this is where the run is *re-executed* rather than stored, the
space-reuse point of [AB09, Example 4.6]; (iii) accept as soon as one `u`
verifies, reject after the last. Total space: certificate + decider + control,
all polynomial in `n`. (The decider-subroutine space composition is a §12
space-clause consumer — `machine-library-design.md` §12, R1/R3.) -/
theorem NP_subset_PSPACE : NP ⊆ PSPACE := by
  sorry

/-- `3SAT` is decidable in polynomial space. [AB09, Example 4.6]

**Proof sketch.** `Complexity.SAT3_mem_NP` with `Complexity.NP_subset_PSPACE`.
(The book's direct cycling-through-assignments machine is subsumed by the
general certificate cycle.) -/
theorem SAT3_mem_PSPACE : SAT3 ∈ PSPACE := by
  sorry

end Complexity

```


## ===== TCSlib/Complexity/SpaceComplexity/Examples.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Logspace examples: the parity language

[AB09, Example 4.7]: `EVEN = {x : x has an even number of 1s}` is in `L`. (The
example's second language, `MULT`, needs the campaign's number-triple encoding
conventions and is scheduled with the logspace-reduction phase — phase P4.4 of
`AroraBarakChapters3-4Plan.md` — rather than here.) A worked ARM-compiled
example of a `LOGSPACE` membership already exists in the received surface
(`Complexity.dblLang_mem`, `TCSlib.Complexity.SpaceComplexity.Machines.DblLang`);
parity is the book's own first example and gets the direct statement.

## Main definitions

* `Complexity.evenLang` — the even-parity language. [AB09, Example 4.7]

## Main results (sorried; phase-P4.1 statement)

* `Complexity.evenLang_mem_LOGSPACE` — parity is decidable in logarithmic
  space. [AB09, Example 4.7]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2, Example 4.7.)
-/

namespace Complexity

open Turing

/-- **The parity language** `EVEN`: binary strings containing an even number of
`1`s (rendered as `true`s). [AB09, Example 4.7] -/
def evenLang : Language Bool :=
  {x | x.count true % 2 = 0}

/-- **Parity is decidable in logarithmic space** — in fact in constant space,
which the `c · logSpace n` budget absorbs since `logSpace n ≥ 1`.
[AB09, Example 4.7]

**Proof sketch.** A two-state one-work-tape machine scans the input left to
right, keeping the running parity in its control state, never moving its work
head (one visited cell), and at the end-of-input emits `[true]` iff the parity
state is even. Space: `1 ≤ 1 · logSpace n` visited cells; halting at time
`n + O(1)`. The machine is a `Turing.FinTM` built directly (the
`Turing.MultiTapeTM.indicator` output convention of
`Turing.FinTM.DecidesInSpace`); correctness is a single left-to-right scan
invariant — parity of the consumed prefix — in the style of the received
`Complexity.dblLang_mem` but without the ARM layer. -/
theorem evenLang_mem_LOGSPACE : evenLang ∈ LOGSPACE := by
  sorry

end Complexity

```


## ===== TCSlib/Complexity/SpaceComplexity.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.SpaceComplexity.ConfigCount
import TCSlib.Complexity.SpaceComplexity.Machines.Layout
import TCSlib.Complexity.SpaceComplexity.Machines.Program
import TCSlib.Complexity.SpaceComplexity.Machines.Sim
import TCSlib.Complexity.SpaceComplexity.Machines.CallReturn
import TCSlib.Complexity.SpaceComplexity.Machines.Call
import TCSlib.Complexity.SpaceComplexity.Machines.Compile
import TCSlib.Complexity.SpaceComplexity.Machines.CleanSweep
import TCSlib.Complexity.SpaceComplexity.Machines.Clean
import TCSlib.Complexity.SpaceComplexity.Machines.Bank
import TCSlib.Complexity.SpaceComplexity.Machines.Bin
import TCSlib.Complexity.SpaceComplexity.Machines.Lib
import TCSlib.Complexity.SpaceComplexity.Machines.FragDec
import TCSlib.Complexity.SpaceComplexity.Machines.Frag
import TCSlib.Complexity.SpaceComplexity.Machines.ParsePlain
import TCSlib.Complexity.SpaceComplexity.Machines.Parse
import TCSlib.Complexity.SpaceComplexity.Machines.Parse2
import TCSlib.Complexity.SpaceComplexity.Machines.ParseCmp
import TCSlib.Complexity.SpaceComplexity.Machines.ARM
import TCSlib.Complexity.SpaceComplexity.Machines.ARMSim
import TCSlib.Complexity.SpaceComplexity.Machines.ARMRun
import TCSlib.Complexity.SpaceComplexity.Machines.ARMProof
import TCSlib.Complexity.SpaceComplexity.Machines.ARMKit
import TCSlib.Complexity.SpaceComplexity.Machines.DblLang
import TCSlib.Complexity.SpaceComplexity.UnaryLogspace
import TCSlib.Complexity.SpaceComplexity.CounterProgSim
import TCSlib.Complexity.SpaceComplexity.CounterProgSimRun
import TCSlib.Complexity.SpaceComplexity.ImplicitPoly
import TCSlib.Complexity.SpaceComplexity.NSPACE
import TCSlib.Complexity.SpaceComplexity.SpaceClasses
import TCSlib.Complexity.SpaceComplexity.Constructible
import TCSlib.Complexity.SpaceComplexity.Inclusions
import TCSlib.Complexity.SpaceComplexity.Examples
import TCSlib.Complexity.SpaceComplexity.ZeroSpace

/-!
# Space complexity

Space-bounded computation and logarithmic space [AB09, §4.1, §4.3]: the classes `SPACE(s)`
and `L`, `L ⊆ P` by configuration counting, implicitly logspace computable functions and
their polynomial-time computability, with a toolkit of logspace machines (register-tape
programs calling logspace deciders on virtual inputs, and abstract register machines
compiled onto them).

Related model: `Complexity.CounterProg` (`TCSlib.Complexity.TuringMachine.CounterProg`) is a
goto program over unary counters for the polynomial-time emitters of [AB09, §6.2]. It overlaps
in spirit with the programs here, which store registers in binary (as logarithmic space
requires) and call deciders on virtual inputs; the two are kept separate, and a polynomially
running counter program is simulated by an abstract register machine in
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`.

## Contents

- `SpaceComplexity.Basic`: Def 4.1 space-bounded computation, `SPACE(s)`, `L`; Def 4.16
  implicitly logspace computable functions
- `SpaceComplexity.ConfigCount`: configuration counting; `L ⊆ P`; logspace functions run in
  polynomial time
- `SpaceComplexity.Machines.Layout`: virtual inputs assembled from segments
- `SpaceComplexity.Machines.Program`: register-tape programs with call nodes and their
  compilation
- `SpaceComplexity.Machines.Sim`: the lockstep simulation of a call's decider
- `SpaceComplexity.Machines.CallReturn`: compiled configurations; the return phase of a call
- `SpaceComplexity.Machines.Call`: the run of a call node
- `SpaceComplexity.Machines.Compile`: correctness and space of compiled programs
- `SpaceComplexity.Machines.CleanSweep`: the cleaned machine; the cleanup sweeps of one tape
- `SpaceComplexity.Machines.Clean`: the clean normal form of deciders (the whole run)
- `SpaceComplexity.Machines.Bank`: a bank of clean deciders
- `SpaceComplexity.Machines.Bin`: binary words of numbers
- `SpaceComplexity.Machines.Lib`: register steps and the increment fragment
- `SpaceComplexity.Machines.FragDec`: decrement and clear fragments
- `SpaceComplexity.Machines.Frag`: halve and equality fragments
- `SpaceComplexity.Machines.ParsePlain`: input shapes; the format check on inputs `⟨1ⁿ, w⟩`
- `SpaceComplexity.Machines.Parse`: comparisons on inputs `⟨1ⁿ, w⟩`
- `SpaceComplexity.Machines.Parse2`: the format check on inputs `⟨1ⁿ, ⟨u, w⟩⟩`
- `SpaceComplexity.Machines.ParseCmp`: comparisons on inputs `⟨1ⁿ, ⟨u, w⟩⟩`
- `SpaceComplexity.Machines.ARM`: abstract register machines and their compilation
- `SpaceComplexity.Machines.ARMSim`: per-instruction simulation
- `SpaceComplexity.Machines.ARMRun`: the run and space theorems of compiled machines
- `SpaceComplexity.Machines.ARMProof`: proving abstract machines correct; `arm_decides`
- `SpaceComplexity.Machines.ARMKit`: calls on unary inputs; `arm_decides_poly`
- `SpaceComplexity.Machines.DblLang`: reading the unary length `⟨1ⁿ, bits (2n)⟩` in
  logarithmic space
- `SpaceComplexity.ImplicitPoly`: implicitly logspace computable functions are
  polynomial-time computable
- `SpaceComplexity.UnaryLogspace`: functions of the unary length computable in logarithmic
  space (`UnaryLogspace`, `unaryExt`)
- `SpaceComplexity.CounterProgSim`, `SpaceComplexity.CounterProgSimRun`: polynomially
  running counter programs on unary-logspace inputs are unary-logspace
- `SpaceComplexity.NSPACE`: Def 4.1's nondeterministic clause, `NSPACE(s)` (chapters-3-4
  campaign, phase P4.1)
- `SpaceComplexity.SpaceClasses`: Def 4.5's `PSPACE`, `NPSPACE`, `NL`, and `coNL`
- `SpaceComplexity.Constructible`: space-constructible functions (p. 79)
- `SpaceComplexity.Inclusions`: Thm 4.2's first two inclusions; `P ⊆ PSPACE`;
  Example 4.6 (`NP ⊆ PSPACE`, `3SAT ∈ PSPACE`)
- `SpaceComplexity.Examples`: Example 4.7's parity language
- `SpaceComplexity.ZeroSpace`: the zero-bound collapse of unnormalized `SPACE` and the
  positive-normalization identities (P0 reception audit, round 1)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, §4.3.)
-/

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


## ===== TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.Examples

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The zero-space collapse and positive normalization

The sanity layer for the P0 reception audit's finding 1 (round 1, sanity targets
S1-S6): because every work tape's visited set contains its origin, `SPACE s`
collapses to the zero-work-tape class as soon as `s` has a **single** zero — in
particular the literal `SPACE (fun n => n)` is not linear space — while additive
normalization by `+ 1` is harmless for everywhere-positive bounds. These
statements pin the campaign convention (every asymptotic chapter bound is
everywhere positive) to elaborated sanity statements — their proofs are fill
obligations; the round-2 audit certified each statement true as stated — so
the convention cannot be overlooked. The
zero-space class is nevertheless not trivial: constant languages and the parity
language have zero-work-tape deciders (input is read in finite control).

## Main results (sorried; P0 round-1 sanity statements)

* `Turing.FinTM.k_le_spaceUsed` — S1: the tape count lower-bounds the space, at
  every input and time.
* `Turing.FinTM.ComputesInSpace.k_eq_zero_of_exists_zero` — S2: one zero of the
  bound forces zero work tapes.
* `Complexity.SPACE_eq_zero_of_exists_zero`, `Complexity.SPACE_id_eq_SPACE_zero`
  — S3: the collapse, and its instantiation at the identity bound.
* `Complexity.SPACE_succ_of_pos`, `Complexity.SPACE_succ_eq_max_one` — S4: when
  the `+ 1` normalization is invisible.
* `Turing.pairEncode_bits_inj` — S5: the `Complexity.indexLang` encoding is
  injective, index `0` included.
* `Complexity.trueLang_mem_SPACE_zero`, `Complexity.evenLang_mem_SPACE_zero` —
  S6: the zero-space class contains constants and parity (so it is not empty,
  and not only constants).
* `Complexity.exists_zeroTape_const_oneStep`,
  `Complexity.exists_zeroTape_parity_decider` — S6 with the explicit time
  contracts (P0 round 2, finding 12): the one-step constant machine and the
  `n + 1`-step parity decider, both with zero work tapes.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, Definition 4.1 — the received
  `SPACE`; the collapse itself has no book counterpart, being an artifact of
  unnormalized bounds that the book's `S(n) > log n` convention rules out.)
-/

namespace Turing.FinTM

/-- **S1 — the tape count lower-bounds the space**: every work tape's visited set
contains the position of its head at time `0`, so `spaceUsed` is at least the
number of work tapes, on every input at every time.

**Proof sketch.** `Turing.MultiTapeTM.spaceUsedByTape` is the cardinality of
`Turing.MultiTapeTM.visitedByTapeHead`, an image of the nonempty
`Finset.range (t + 1)`; a nonempty image has positive cardinality
(`Finset.Nonempty.image`, `Finset.card_pos`). Sum `1 ≤ card` over the `k` tapes
(`Finset.card_le_card_of_injOn` is not needed — `Finset.sum_le_sum` on the
constant-one function). -/
theorem k_le_spaceUsed (M : FinTM Bool) (x : List Bool) (t : ℕ) :
    M.k ≤ M.tm.spaceUsed (M.tm.initCfg x) t := by
  sorry

/-- **S2 — one zero of the bound forces zero work tapes**: a machine computing
within space `s` where `s n₀ = 0` for even a single length `n₀` has no work
tapes at all (and hence zero space on **every** input).

**Proof sketch.** Instantiate the contract at the input
`List.replicate n₀ false`: it supplies a halting time `t` with
`spaceUsed ≤ s n₀ = 0`; `Turing.FinTM.k_le_spaceUsed` gives `M.k ≤ 0`
(`Nat.le_zero`). -/
theorem ComputesInSpace.k_eq_zero_of_exists_zero {M : FinTM Bool}
    {f : List Bool → List Bool} {s : ℕ → ℕ} (h : M.ComputesInSpace f s)
    (hz : ∃ n, s n = 0) : M.k = 0 := by
  sorry

end Turing.FinTM

namespace Complexity

open Turing

/-- **S3 — the collapse**: as soon as the bound has a single zero, `SPACE s` is
the zero-work-tape class `SPACE (fun _ => 0)`. Multiplicative absorption cannot
repair this: `c * 0 = 0` for every `c`.

**Proof sketch.** `⊆`: a witness machine has `M.k = 0` by
`Turing.FinTM.ComputesInSpace.k_eq_zero_of_exists_zero` (at the bound
`fun n => c * s n`, whose zero is inherited from `s`'s); a zero-tape machine has
`spaceUsed = 0` (`Finset.sum_empty` over `Fin 0`) on every input, so the same
machine and times witness `DecidesInSpace L (fun _ => 0)`. `⊇`: `0 ≤ c * s n`
pointwise, so the zero-space contract weakens to any bound
(`Turing.FinTM.ComputesInSpace.mono`). -/
theorem SPACE_eq_zero_of_exists_zero {s : ℕ → ℕ} (hz : ∃ n, s n = 0) :
    SPACE s = SPACE (fun _ => 0) := by
  sorry

/-- **S3, instantiated — literal `SPACE (fun n => n)` is the zero-work-tape
class**, because of the zero at the empty input. This is the statement that
makes the positive-normalization convention impossible to overlook: the
chapter-3/4 campaign states Exercise 3.2 and every other asymptotic space bound
with everywhere-positive functions (`fun n => n + 1`, `fun n => n ^ c + 1`,
`Complexity.logSpace`).

**Proof sketch.** `Complexity.SPACE_eq_zero_of_exists_zero` at `⟨0, rfl⟩`. -/
theorem SPACE_id_eq_SPACE_zero : SPACE (fun n => n) = SPACE (fun _ => 0) := by
  sorry

/-- **S4, first half — `+ 1` is invisible on everywhere-positive bounds**:
`SPACE s = SPACE (fun n => s n + 1)` when `0 < s n` for all `n`.

**Proof sketch.** `⊆`: `s n ≤ s n + 1`, `Complexity.SPACE.mono`. `⊇`: from
positivity `s n + 1 ≤ 2 * s n`, so a `c · (s n + 1)` contract is a
`(2c) · s n` contract — constant absorption inside the class's existential. -/
theorem SPACE_succ_of_pos {s : ℕ → ℕ} (hpos : ∀ n, 0 < s n) :
    SPACE s = SPACE (fun n => s n + 1) := by
  sorry

/-- **S4, second half — for arbitrary bounds, `+ 1` is the `max 1`
normalization**: `SPACE (fun n => s n + 1) = SPACE (fun n => max 1 (s n))`.

**Proof sketch.** Pointwise `max 1 (s n) ≤ s n + 1 ≤ 2 * max 1 (s n)` (case on
`s n = 0`); both directions are `Complexity.SPACE.mono` plus constant
absorption, as in `Complexity.SPACE_succ_of_pos`. -/
theorem SPACE_succ_eq_max_one (s : ℕ → ℕ) :
    SPACE (fun n => s n + 1) = SPACE (fun n => max 1 (s n)) := by
  sorry

end Complexity

namespace Turing

/-- **S5 — the index-pair encoding is injective, index `0` included**:
`pairEncode x (Nat.bits i)` determines both the string and the index. At
`i = 0` the payload is empty but the separator remains (`pairEncode [] [] =
[false, true] ≠ []`), so no collision with malformed words arises — the
boundary behavior behind `Complexity.indexLang`.

**Proof sketch.** Forward: `Turing.pairDecode_pairEncode` recovers both
components, and `Nat.bits` is injective (its value inverse — the
`Complexity.LogProg.bitsVal`/`bits_injective` layer of
`TCSlib.Complexity.SpaceComplexity.Machines.Bin`, or `Nat.bits` induction).
Backward: congruence. -/
theorem pairEncode_bits_inj (x y : List Bool) (i j : ℕ) :
    pairEncode x (Nat.bits i) = pairEncode y (Nat.bits j) ↔ x = y ∧ i = j := by
  sorry

end Turing

namespace Complexity

open Turing

/-- **S6a — the zero-space class contains the constant languages**: the full
language is decided by a zero-work-tape machine (emit `[true]`, halt), with
space `0` and even constant `c = 0` in the class existential.

**Proof sketch.** A one-live-state machine with `k = 0` whose single transition
emits `true` and halts; `spaceUsed` is the empty sum. Halting time `1` feeds
`Turing.FinTM.ComputesInSpace`'s existential. -/
theorem trueLang_mem_SPACE_zero : ({x | True} : Language Bool) ∈ SPACE fun _ => 0 := by
  sorry

/-- **S6b — the zero-space class is not only constants**: parity
(`Complexity.evenLang`) has a zero-work-tape decider — the input is read
two-way-read-only and the running parity lives in finite control. (With
`Complexity.SPACE.mono` this also strengthens
`Complexity.evenLang_mem_LOGSPACE`.) A zero-tape machine still takes `n + 1`
steps here, which is why no `2^{O(s)}` time bound without the input factor can
hold below logarithmic space — the received `configBound` correctly keeps its
`n + 2` factor.

**Proof sketch.** A two-state (`parity bit in control`) zero-tape machine scans
the input left to right (`n + 1` steps), then emits the indicator of even
parity and halts; the scan invariant is the parity of the consumed prefix, as
in the direct machine of `Complexity.evenLang_mem_LOGSPACE`'s sketch, minus the
work tape. -/
theorem evenLang_mem_SPACE_zero : evenLang ∈ SPACE fun _ => 0 := by
  sorry

/-- **S6a with the time contract** (P0 round 2, finding 12): a zero-work-tape
machine computes `[true]` within **one step** on every input — the explicit
witness behind `Complexity.trueLang_mem_SPACE_zero`, whose membership statement
alone leaves the halting time an unspecified existential.

**Proof sketch.** One live state, `k = 0`; the single transition emits `true`
and halts (`state := none`); `Turing.FinTM.ComputesInTime x [true] 1` holds on
every input, and the space is the empty sum. -/
theorem exists_zeroTape_const_oneStep :
    ∃ M : Turing.FinTM Bool, M.k = 0 ∧
      ∀ x : List Bool, M.ComputesInTime x [true] 1 := by
  sorry

/-- **S6b with the time contract** (P0 round 2, finding 12): a zero-work-tape
machine decides the parity language within `n + 1` steps — the explicit
witness behind `Complexity.evenLang_mem_SPACE_zero`. The construction is the
round-2 report's: two live control states carrying the parity of the consumed
prefix (toggle on `true`, keep on `false`), `x.length` symbol steps and one
final emit-and-halt step at the right blank.

**Proof sketch.** The scan invariant "control state = parity of
`(x.take j).count true`" by induction on the consumed prefix; at the boundary
emit `[Turing.MultiTapeTM.indicator evenLang x]` and halt, within
`x.length + 1` steps; `k = 0` makes the space the empty sum. -/
theorem exists_zeroTape_parity_decider :
    ∃ M : Turing.FinTM Bool, M.k = 0 ∧
      M.DecidesInTime evenLang fun n => n + 1 := by
  sorry

end Complexity

```


## ===== TCSlib/Complexity/SpaceComplexity/ConfigCount.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import TCSlib.Complexity.SpaceComplexity.Basic
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.ClassNP.PolyTime

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Configuration counting: space-bounded machines halt quickly, `L ⊆ P`

[AB09, §4.1.1 and Thm 4.2]: a deterministic machine that halts never repeats a
configuration, and a machine using `s` work cells has at most `2^{O(s)} · poly(n)`
configurations, so it halts within that many steps. For `s = O(log n)` this is a
polynomial, giving `L ⊆ P` and "logspace computations run in polynomial time" [AB09, p. 112].

## Main definitions

* `Turing.FinTM.configBound` — the configuration count
  `(|Q| + 1) · (n + 2) · 3^{k(2s+1)} · (2s + 1)^k` of a `k`-tape machine with state set `Q`
  on inputs of length `n` with at most `s` visited work cells.

## Main results

* `Turing.MultiTapeTM.abs_pos_lt_card_visited` — the visited cells of a tape form an
  interval around the origin, so every visited position `z` has `|z| < #visited`.
* `Turing.FinTM.ComputesInTime.of_spaceUsed_le` — a computation that has halted by time `t`
  having visited at most `s` cells has in fact halted by time `configBound M |x| s`.
  [AB09, §4.1.1, the deterministic case of Thm 4.2]
* `Complexity.LOGSPACE_subset_P` — `L ⊆ P`. [AB09, Thm 4.2 for `S = log n`]
* `Complexity.polyTimeComputable_of_computesInSpace` — a function computed in logarithmic
  space is polynomial-time computable. [AB09, p. 112: "logspace computations run in
  polynomial time"]

## Design

A configuration of the vendored model also records the output tape, which grows; the
argument is run on the *core* `(state, input position, work tapes, work heads)`, whose
evolution does not depend on the output. If two times before the first halting time have
the same core, the core sequence is periodic from then on and the machine never halts.
Cores reached with at most `s` visited cells are coded injectively into a finite type:
heads lie in `[-s, s]` (the visited set is an interval containing `0`, by a discrete
intermediate value argument) and every nonblank cell has been visited.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Claim 4.4 and Theorem 4.2; §6.2.1, p. 112.)
-/

namespace Turing

namespace MultiTapeTM

variable {k : ℕ} {S : Type} {x : List Bool}

/-! ### Internal helpers: cores of configurations -/

namespace ConfigCount

/-- The core of a configuration: everything but the output tape. -/
def core (c : Cfg k Bool S x) :
    Option S × Fin (x.length + 2) × (Fin k → ℤ → Option Bool) × (Fin k → ℤ) :=
  (c.state, c.inputPos, c.workTapes, c.workTapePos)

/-- The core after a step depends only on the core before it. -/
lemma core_step (tm : MultiTapeTM k Bool S) {c d : Cfg k Bool S x} (h : core c = core d) :
    core (tm.step c) = core (tm.step d) := by
  simp only [core, Prod.mk.injEq] at h
  obtain ⟨hs, hi, hw, hp⟩ := h
  have hsym : c.inputSymbol = d.inputSymbol := by
    unfold Cfg.inputSymbol; simp only [hi]
  have hws : c.workTapeSymbols = d.workTapeSymbols := by
    funext i; simp only [Cfg.workTapeSymbols, hw, hp]
  unfold step
  rw [hs]
  cases d.state with
  | none => simp [core, hs, hi, hw, hp]
  | some q =>
    simp only [core, Action.apply, hsym, hws, hi, hw, hp]

/-- Equal cores stay equal along runs. -/
lemma core_runFrom (tm : MultiTapeTM k Bool S) {c d : Cfg k Bool S x} (h : core c = core d)
    (t : ℕ) : core (tm.runFrom c t) = core (tm.runFrom d t) := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    rw [runFrom_succ_eq_step', runFrom_succ_eq_step']
    exact core_step tm ih

/-- Before the first halting time, no core repeats.

**Proof sketch.** If the cores at times `t₁ < t₂` agree, then the cores at `t₁ + j` and
`t₂ + j` agree for every `j`, so the core at `t₁ + r` equals the core at `t₁ + (r mod p)`
with `p = t₂ - t₁`. At the first halting time `T = t₁ + r` the state is `none`, but
`t₁ + (r mod p) < t₂ < T` is an earlier, non-halted time. -/
lemma core_injOn (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (T : ℕ)
    (hT : (tm.runFrom c T).state = none)
    (hmin : ∀ t < T, (tm.runFrom c t).state ≠ none) {t₁ t₂ : ℕ} (h₁₂ : t₁ < t₂)
    (h₂ : t₂ < T) : core (tm.runFrom c t₁) ≠ core (tm.runFrom c t₂) := by
  intro heq
  set p := t₂ - t₁ with hp
  have hpos : 0 < p := by omega
  -- the core at `t₁ + r` equals the one at `t₁ + (r - p)` once `r ≥ p`
  have hback : ∀ r, p ≤ r →
      core (tm.runFrom c (t₁ + r)) = core (tm.runFrom c (t₁ + (r - p))) := by
    intro r hr
    have e1 : t₁ + r = t₂ + (r - p) := by omega
    rw [e1, runFrom_add, runFrom_add c t₁]
    exact core_runFrom tm heq.symm _
  have hmod : ∀ r, core (tm.runFrom c (t₁ + r)) = core (tm.runFrom c (t₁ + r % p)) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      by_cases hr : r < p
      · rw [Nat.mod_eq_of_lt hr]
      · rw [hback r (by omega), ih (r - p) (by omega), ← Nat.mod_eq_sub_mod (by omega)]
  have hTgt : t₂ < T := h₂
  have hr := hmod (T - t₁)
  rw [show t₁ + (T - t₁) = T by omega] at hr
  have hlt : t₁ + (T - t₁) % p < T := by
    have := Nat.mod_lt (T - t₁) hpos
    omega
  apply hmin _ hlt
  have := congrArg Prod.fst hr
  simp only [core] at this
  rw [← this, hT]

/-- Discrete intermediate values: a sequence of integers starting at `0` and moving by at
most one per step passes through every integer between `0` and any of its values.

**Proof sketch.** Induction on `t`. If `y` lies between `0` and `p t`, the induction hypothesis
applies. Otherwise `y` lies between `p t` and `p (t + 1)`, which differ by at most one, so `y =
p (t + 1)`. -/
lemma exists_eq_of_between (p : ℕ → ℤ) (h0 : p 0 = 0) (hstep : ∀ j, |p (j + 1) - p j| ≤ 1) :
    ∀ t (y : ℤ), (0 ≤ y ∧ y ≤ p t ∨ p t ≤ y ∧ y ≤ 0) → ∃ j ≤ t, p j = y := by
  intro t
  induction t with
  | zero =>
    intro y hy
    exact ⟨0, le_rfl, by rw [h0] at hy; omega⟩
  | succ t ih =>
    intro y hy
    have hs := hstep t
    rw [abs_le] at hs
    by_cases hin : 0 ≤ y ∧ y ≤ p t ∨ p t ≤ y ∧ y ≤ 0
    · obtain ⟨j, hj, hpj⟩ := ih y hin
      exact ⟨j, by omega, hpj⟩
    · exact ⟨t + 1, le_rfl, by omega⟩

end ConfigCount

open ConfigCount

/-- The positions visited by work head `i` from an initial configuration form a set in
which every position `z` satisfies `|z| < #visited`: the visited set contains the whole
interval between `0` and `z`.

**Proof sketch.** The visited set contains `0` (the start) and, by the discrete intermediate
value theorem (`exists_eq_of_between`, the head moves by at most one cell per step), every
integer between `0` and any visited `z`. So it contains the `|z| + 1` integers between `0` and
`z`, and its cardinality exceeds `|z|`. -/
lemma abs_pos_lt_card_visited (tm : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ)
    (i : Fin k) {z : ℤ} (hz : z ∈ tm.visitedByTapeHead (tm.initCfg x) t i) :
    |z| < (tm.visitedByTapeHead (tm.initCfg x) t i).card := by
  set p : ℕ → ℤ := fun j => (tm.runFrom (tm.initCfg x) j).workTapePos i with hpdef
  have h0 : p 0 = 0 := by simp [p]
  have hstep : ∀ j, |p (j + 1) - p j| ≤ 1 := by
    intro j
    simp only [p, runFrom_succ_eq_step']
    exact tm.workTapePos_step_le _ i
  obtain ⟨t', ht', hzt⟩ : ∃ t' ≤ t, p t' = z := by
    simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨t', ht', h⟩ := hz
    exact ⟨t', by omega, h⟩
  -- the interval between `0` and `z` lies in the visited set
  have hsub : Finset.Icc (min 0 z) (max 0 z) ⊆ tm.visitedByTapeHead (tm.initCfg x) t i := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    obtain ⟨j, hj, hpj⟩ := exists_eq_of_between p h0 hstep t' y (by
      rw [hzt]; rcases le_total 0 z with h | h
      · left; simp only [min_eq_left h, max_eq_right h] at hy; omega
      · right; simp only [min_eq_right h, max_eq_left h] at hy; omega)
    simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range]
    exact ⟨j, by omega, hpj⟩
  have hc := Finset.card_le_card hsub
  rw [Int.card_Icc] at hc
  rcases le_total 0 z with h | h
  · simp only [min_eq_left h, max_eq_right h] at hc
    rw [abs_of_nonneg h]; omega
  · simp only [min_eq_right h, max_eq_left h] at hc
    rw [abs_of_nonpos h]; omega

/-- A cell holding a nonblank symbol at time `t` was visited by its head before time `t`.

**Proof sketch.** Induction on `t`. Initially every work cell is blank. A step writes only the
cell under the head, which is visited at that step; other cells keep their contents and stay
visited by monotonicity of the visited sets. -/
lemma mem_visited_of_ne_none (tm : MultiTapeTM k Bool S) (x : List Bool) (t : ℕ)
    (i : Fin k) (z : ℤ) (hz : (tm.runFrom (tm.initCfg x) t).workTapes i z ≠ none) :
    z ∈ tm.visitedByTapeHead (tm.initCfg x) t i := by
  induction t with
  | zero => simp [initCfg, Cfg.init] at hz
  | succ t ih =>
    simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range] at ih ⊢
    rw [runFrom_succ_eq_step'] at hz
    unfold step at hz
    cases hs : (tm.runFrom (tm.initCfg x) t).state with
    | none =>
      rw [hs] at hz
      obtain ⟨j, hj, h⟩ := ih hz
      exact ⟨j, by omega, h⟩
    | some q =>
      rw [hs] at hz
      dsimp only [Action.apply] at hz
      cases hw : ((tm.tr q (tm.runFrom (tm.initCfg x) t).inputSymbol
          (tm.runFrom (tm.initCfg x) t).workTapeSymbols).workTapes i).1 with
      | none =>
        rw [hw] at hz
        obtain ⟨j, hj, h⟩ := ih hz
        exact ⟨j, by omega, h⟩
      | some a =>
        rw [hw] at hz
        dsimp only at hz
        by_cases hzp : z = (tm.runFrom (tm.initCfg x) t).workTapePos i
        · exact ⟨t, by omega, hzp.symm⟩
        · rw [Function.update_of_ne hzp] at hz
          obtain ⟨j, hj, h⟩ := ih hz
          exact ⟨j, by omega, h⟩

/-- Visited sets grow with time. -/
lemma visitedByTapeHead_mono (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) {t t' : ℕ}
    (h : t ≤ t') (i : Fin k) : tm.visitedByTapeHead c t i ⊆ tm.visitedByTapeHead c t' i := by
  intro z hz
  simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range] at hz ⊢
  obtain ⟨j, hj, h'⟩ := hz
  exact ⟨j, by omega, h'⟩

/-- Space used grows with time. -/
lemma spaceUsed_mono (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) {t t' : ℕ}
    (h : t ≤ t') : tm.spaceUsed c t ≤ tm.spaceUsed c t' :=
  Finset.sum_le_sum fun i _ => Finset.card_le_card (tm.visitedByTapeHead_mono c h i)

namespace ConfigCount

/-- The code of an integer in `[-B, B]` as an element of `Fin (2B + 1)`. -/
def posCode (B : ℕ) (z : ℤ) : Fin (2 * B + 1) :=
  ⟨min (z + B).toNat (2 * B), by omega⟩

/-- The position code is injective on positions of absolute value at most `B`. -/
lemma posCode_injOn (B : ℕ) {z z' : ℤ} (hz : |z| ≤ B) (hz' : |z'| ≤ B)
    (h : posCode B z = posCode B z') : z = z' := by
  simp only [posCode, Fin.mk.injEq] at h
  rw [abs_le] at hz hz'
  omega

/-- The finite code of a core with heads and nonblank cells in `[-B, B]`. -/
def coreCode (B : ℕ) (c : Cfg k Bool S x) :
    Option S × Fin (x.length + 2) × (Fin k → Fin (2 * B + 1) → Option Bool) ×
      (Fin k → Fin (2 * B + 1)) :=
  (c.state, c.inputPos, fun i j => c.workTapes i ((j : ℤ) - B),
    fun i => posCode B (c.workTapePos i))

/-- The code is injective on cores whose heads and nonblank cells lie in `[-B, B]`.

**Proof sketch.** State, input position and head positions are read off the code directly, the
positions by injectivity of `posCode` on `[-B, B]`. A cell `z` with `|z| ≤ B` is recorded in the
code. A cell with `|z| > B` is blank in both configurations by hypothesis. -/
lemma coreCode_inj (B : ℕ) {c d : Cfg k Bool S x}
    (hc : ∀ i, |c.workTapePos i| ≤ B ∧ ∀ z, c.workTapes i z ≠ none → |z| ≤ B)
    (hd : ∀ i, |d.workTapePos i| ≤ B ∧ ∀ z, d.workTapes i z ≠ none → |z| ≤ B)
    (h : coreCode B c = coreCode B d) : core c = core d := by
  simp only [coreCode, Prod.mk.injEq] at h
  obtain ⟨hs, hi, hw, hp⟩ := h
  simp only [core, Prod.mk.injEq]
  refine ⟨hs, hi, ?_, ?_⟩
  · funext i z
    by_cases hz : |z| ≤ B
    · have := congrFun (congrFun hw i) ⟨(z + B).toNat, by rw [abs_le] at hz; omega⟩
      simp only at this
      rwa [show (((z + B).toNat : ℕ) : ℤ) - B = z by rw [abs_le] at hz; omega] at this
    · have h1 : c.workTapes i z = none := by
        by_contra hne; exact hz ((hc i).2 z hne)
      have h2 : d.workTapes i z = none := by
        by_contra hne; exact hz ((hd i).2 z hne)
      rw [h1, h2]
  · funext i
    exact posCode_injOn B (hc i).1 (hd i).1 (congrFun hp i)

end ConfigCount

end MultiTapeTM

namespace FinTM

open MultiTapeTM MultiTapeTM.ConfigCount

/-- The number of codes of configurations of `M` on inputs of length `n` with heads and
nonblank cells in `[-s, s]`: `(|Q| + 1) · (n + 2) · 3^{k(2s+1)} · (2s + 1)^k`. -/
def configBound (M : FinTM Bool) (n s : ℕ) : ℕ :=
  (Fintype.card M.State + 1) * (n + 2) * 3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k

/-- **Space-bounded halting computations are short** [AB09, §4.1.1]: if `M` has halted on
`x` with output `w` by time `t`, having visited at most `s` work cells, then it has halted
with output `w` by time `configBound M |x| s`.

**Proof sketch.** Let `T ≤ t` be the first halting time. Up to time `t` every head lies in
`[-s, s]` (`abs_pos_lt_card_visited`: the visited cells of a tape form an interval around
`0`, of size at most the space used) and so does every nonblank cell
(`mem_visited_of_ne_none`). Hence the cores at times `< T` have pairwise distinct
(`core_injOn`) codes in a finite type of size `configBound M |x| s`, so `T` is at most
that size; the output is frozen after `T`. -/
theorem ComputesInTime.of_spaceUsed_le {M : FinTM Bool} {x w : List Bool} {t s : ℕ}
    (h : M.ComputesInTime x w t) (hs : M.tm.spaceUsed (M.tm.initCfg x) t ≤ s) :
    M.ComputesInTime x w (M.configBound x.length s) := by
  classical
  rw [computesInTime_iff] at h ⊢
  obtain ⟨hhalt, hout⟩ := h
  have hex : ∃ T, (M.tm.runFrom (M.tm.initCfg x) T).state = none := ⟨t, hhalt⟩
  set T := Nat.find hex with hTdef
  have hT : (M.tm.runFrom (M.tm.initCfg x) T).state = none := Nat.find_spec hex
  have hTt : T ≤ t := Nat.find_min' hex hhalt
  have hmin : ∀ t' < T, (M.tm.runFrom (M.tm.initCfg x) t').state ≠ none :=
    fun t' ht' => Nat.find_min hex ht'
  -- bounds on heads and nonblank cells up to time `t`
  have hbound : ∀ t' ≤ t, ∀ i, |(M.tm.runFrom (M.tm.initCfg x) t').workTapePos i| ≤ s ∧
      ∀ z, (M.tm.runFrom (M.tm.initCfg x) t').workTapes i z ≠ none → |z| ≤ s := by
    intro t' ht' i
    have hcard : (M.tm.visitedByTapeHead (M.tm.initCfg x) t i).card ≤ s :=
      (M.tm.spaceUsedByTape_le_spaceUsed _ t i).trans hs
    have hmem : ∀ z ∈ M.tm.visitedByTapeHead (M.tm.initCfg x) t i, |z| ≤ s := fun z hz =>
      ((M.tm.abs_pos_lt_card_visited x t i hz).trans_le (by exact_mod_cast hcard)).le
    refine ⟨hmem _ ?_, fun z hz => hmem z ?_⟩
    · simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_range]
      exact ⟨t', by omega, rfl⟩
    · exact M.tm.visitedByTapeHead_mono _ ht' i (M.tm.mem_visited_of_ne_none x t' i z hz)
  -- injectivity of the code map on times before `T`
  have hinj : Set.InjOn (fun t' => coreCode s (M.tm.runFrom (M.tm.initCfg x) t'))
      (Finset.range T : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have hc := coreCode_inj s (hbound a (by omega)) (hbound b (by omega)) hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact core_injOn M.tm _ T hT hmin h' hb hc
    · exact core_injOn M.tm _ T hT hmin h' ha hc.symm
  have hcardT : T ≤ M.configBound x.length s := by
    have := Finset.card_le_card_of_injOn _ (fun a _ => Finset.mem_univ _) hinj
    simp only [Finset.card_range, Finset.card_univ, Fintype.card_prod, Fintype.card_option,
      Fintype.card_fin, Fintype.card_pi, Finset.prod_const, Fintype.card_bool] at this
    rw [← pow_mul, Nat.mul_comm (2 * s + 1) M.k] at this
    refine this.trans (le_of_eq ?_)
    simp only [configBound]
    ring
  have hfin : M.tm.runFrom (M.tm.initCfg x) (M.configBound x.length s) =
      M.tm.runFrom (M.tm.initCfg x) T := by
    rw [show M.configBound x.length s = T + (M.configBound x.length s - T) by omega,
      runFrom_add, runFrom_of_halt _ hT]
  have hfin' : M.tm.runFrom (M.tm.initCfg x) t = M.tm.runFrom (M.tm.initCfg x) T := by
    rw [show t = T + (t - T) by omega, runFrom_add, runFrom_of_halt _ hT]
  rw [hfin]
  exact ⟨hT, by rw [← hfin']; exact hout⟩

/-- For a logarithmic space bound the configuration count is polynomial:
`configBound M n (c · logSpace n) ≤ A · (n + 1)^d` with `A = 2 (|Q| + 1) 2^{5kc + 3k}` and
`d = 5kc + 1`.

**Proof sketch.** Write `L = ⌊log₂ n⌋`, so `2^L ≤ n + 1`, and `s = c (L + 1)`. Bound
`3 ≤ 2²` and `2s + 1 ≤ 2^{s+1}`; the product `3^{k(2s+1)} (2s+1)^k` is then at most
`2^{5ks + 3k} = (2^L)^{5kc} · 2^{5kc + 3k}`, and `n + 2 ≤ 2 (n + 1)`. -/
theorem configBound_logSpace_le (M : FinTM Bool) (c n : ℕ) :
    M.configBound n (c * Complexity.logSpace n) ≤
      ((Fintype.card M.State + 1) * 2 * 2 ^ (5 * M.k * c + 3 * M.k)) *
        (n + 1) ^ (5 * M.k * c + 1) := by
  set L := Nat.log 2 n with hL
  set s := c * Complexity.logSpace n with hs
  have hsL : s = c * (L + 1) := rfl
  have h2L : 2 ^ L ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [hL, h]
    · exact (Nat.pow_log_le_self 2 (by omega)).trans (Nat.le_succ n)
  have h3 : 3 ^ (M.k * (2 * s + 1)) ≤ 2 ^ (2 * (M.k * (2 * s + 1))) := by
    rw [pow_mul 2 2]; exact Nat.pow_le_pow_left (show 3 ≤ 2 ^ 2 by decide) _
  have hs2 : 2 * s + 1 ≤ 2 ^ (s + 1) := by
    have := s.lt_two_pow_self
    rw [pow_succ]; omega
  have h4 : (2 * s + 1) ^ M.k ≤ 2 ^ ((s + 1) * M.k) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hs2 _
  have hexp : 2 * (M.k * (2 * s + 1)) + (s + 1) * M.k =
      L * (5 * M.k * c) + (5 * M.k * c + 3 * M.k) := by
    rw [hsL]; ring
  have hprod : 3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k ≤
      (n + 1) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k) := by
    calc 3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k
        ≤ 2 ^ (2 * (M.k * (2 * s + 1))) * 2 ^ ((s + 1) * M.k) := Nat.mul_le_mul h3 h4
      _ = (2 ^ L) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k) := by
        rw [← pow_add, hexp, pow_add, pow_mul]
      _ ≤ (n + 1) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2L _)
  calc M.configBound n s
      = (Fintype.card M.State + 1) * (n + 2) *
          (3 ^ (M.k * (2 * s + 1)) * (2 * s + 1) ^ M.k) := by
        simp only [configBound]; ring
    _ ≤ (Fintype.card M.State + 1) * (2 * (n + 1)) *
          ((n + 1) ^ (5 * M.k * c) * 2 ^ (5 * M.k * c + 3 * M.k)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hprod
    _ = ((Fintype.card M.State + 1) * 2 * 2 ^ (5 * M.k * c + 3 * M.k)) *
          (n + 1) ^ (5 * M.k * c + 1) := by ring

/-- A computation in logarithmic space is a computation in polynomial time, by the same
machine: if `M` computes `f` in space `c · logSpace`, then `M` computes `f` within
`A · (n + 1)^d` steps. [AB09, p. 112: "logspace computations run in polynomial time"]

**Proof sketch.** `ComputesInTime.of_spaceUsed_le` bounds the halting time by the
configuration count, which `configBound_logSpace_le` bounds by a polynomial. -/
theorem ComputesInSpace.computesFunInTime {M : FinTM Bool} {f : List Bool → List Bool}
    {c : ℕ} (h : M.ComputesInSpace f fun n => c * Complexity.logSpace n) :
    M.ComputesFunInTime f fun n =>
      ((Fintype.card M.State + 1) * 2 * 2 ^ (5 * M.k * c + 3 * M.k)) *
        (n + 1) ^ (5 * M.k * c + 1) := by
  intro x
  obtain ⟨t, ht, hsp⟩ := h x
  exact (ht.of_spaceUsed_le hsp).mono (configBound_logSpace_le M c x.length)

end FinTM

end Turing

namespace Complexity

open Turing

/-- **`L ⊆ P`** [AB09, Thm 4.2 with `S(n) = log n`; p. 112]: a language decided in
logarithmic space is decided in polynomial time — by the same machine.

**Proof sketch.** `Turing.FinTM.ComputesInSpace.computesFunInTime` turns the logspace
decider into a decider within `A · (n + 1)^d` steps; conclude with `Complexity.mem_P_iff`. -/
theorem LOGSPACE_subset_P : LOGSPACE ⊆ P := by
  rintro L ⟨c, M, hM⟩
  rw [mem_P_iff]
  exact ⟨_, _, M, FinTM.ComputesInSpace.computesFunInTime hM⟩

/-- A function computed by a machine in logarithmic space is polynomial-time computable.
[AB09, p. 112] -/
theorem polyTimeComputable_of_computesInSpace {f : List Bool → List Bool} {M : FinTM Bool}
    {c : ℕ} (h : M.ComputesInSpace f fun n => c * logSpace n) : PolyTimeComputable f :=
  ⟨M, _, _, FinTM.ComputesInSpace.computesFunInTime h⟩

end Complexity

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


## ===== TCSlib/Complexity/TuringMachine/Deterministic.lean =====

```
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger

Vendored from cslib (https://github.com/leanprover/cslib), file
`Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean`,
at commit a374775894efb9b7196cccf11235c60a97086dc1 (2026-09-14).
Local modifications (see policy.md §2, vendored code):
* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)
  for compatibility with our v4.25.0 toolchain;
* remapped `Mathlib.Basic.Sign.Defs` to `Mathlib.Data.Sign.Defs` (its location at our mathlib
  pin); dropped the cslib-internal `Cslib.Init` import; added
  `Mathlib.Logic.Embedding.Basic` explicitly (upstream receives it transitively);
* dropped the relational semantics (`TransitionRelation`,
  `relatesInSteps_iff_runFrom_eq`) because it depends on the cslib-internal
  `Cslib.Foundations.Data.RelatesInSteps`; the iterated-step semantics `runFrom` is
  self-contained and suffices for the Chapter 1 development. Re-add it (or migrate to
  upstream cslib) when the step-indexed relational view is needed, e.g. for
  nondeterministic machines;
* added the repository-standard `set_option` header;
* corrected the module docstring's attribution of the non-blank space measure
  ([AB09, Def 4.1] counts visited cells for `SPACE`, non-blank cells only for
  `NSPACE`); comments only, no code change (2026-10-08).
The remaining mathematical content is unchanged.
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Embedding.Basic
import TCSlib.Complexity.TuringMachine.Configuration

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic Multi-Tape Turing Machines

Defines deterministic Turing machines with a read-only input tape, `k` work tapes and one
write-only output tape.
The tapes contain symbols from `Option Symbol` for a finite alphabet `Symbol` (where `none` is the
blank symbol).

## Design

The multi-tape Turing machine uses a read-only input tape, `k` work tapes and a write-only output
tape.
The input head can move freely on the input, but any move attempt beyond one cell outside the input
results in no movement.
The transition function can optionally output one symbol, which models the write-only output tape.
Because of these restrictions, we ignore the input and output tapes for space usage of the machine.
The space usage is defined as the total number of cells the work tape heads visited during
execution.

Restricting the movement of the input head is not essential, but useful because it allows
us to easily bound the number of possible configurations of a space-bounded machine. Most textbooks
have this restriction.

Instead of considering the cells _visited_ by the work tape heads, some textbooks
only consider the number of cells that contain a non-blank symbol at some point in the
execution or the number of cells written to. ([AB09] itself splits: Definition 4.1 counts
_visited_ work-tape locations for `SPACE` — the measure used here — but _nonblank_
locations for `NSPACE`.) This allows
work tape heads to freely move at no cost as long as they do not write. It is
important to note that this causes `DSPACE(1)` to include `DSPACE(log log n)`, a class that
contains e.g. the non-regular language `{0^n 1^n | n ∈ ℕ}` (it is accepted by a TM that writes a
single marker on the work tape and then counts the number of symbols by work tape head movement
without writing).
Defining space usage via "cells visited" thus yields the more fine-grained "complexity world" in
which `DSPACE(1)` is exactly the class of regular languages.

This definition is adapted from the one in [Pap94], chapter 2.3 including
the sub-linear space modifications from chapter 2.5 with the following changes:
- We allow Turing machines to choose to not write on a tape. This is equivalent to
  writing the read symbol again but makes it easier to reason about the semantics.
- Our tapes are infinite in both directions instead of just to the right. This definition is
  equivalent (see [AB09], Claim 1.8). It saves us from having to add a "start marker" to
  the alphabet.
- We only have a single halting state. The different ways to halt (accepting, rejecting, etc) can
  be distinguished based on the output.
- The way to prevent the input head to move outside the input is enforced by the interpretation
  and not by a restriction on the transition function. The two definitions are equivalent, but
  not restricting the transition function makes it easier to define a universal machine.

## Main definitions

We define a number of structures and concepts related to multi-tape Turing machine computation:

* `MultiTapeTM`: the TM itself
* `MultiTapeTM.runFrom`: the configuration reached after a given number of execution steps
* `spaceUsed`: the number of work tape cells touched by the heads until a certain step,
    our main space measure
* `ComputesInTimeAndSpace`: a proof that a specific TM computes an output from an input in a certain
    number of steps and using a certain number of tape cells
* `ComputesFunInTimeAndSpace`: a machine computes a function between specified encodings,
    respecting time and space bounds on each actual input.
* `ComputableInTimeAndSpace`: such a machine exists with binary alphabet and finitely many states.
* `ComputableInTimeAndSpaceOfLength`: the specialization to bounds on encoded input length.
* `DecidableInTimeAndSpace`: a proof that a TM decides a language within a certain time
    and space bound.

## References

* [Pap94] C. Papadimitriou, *Computational Complexity*, Addison-Wesley, 1994.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013.
-/

namespace Turing

variable {k : ℕ} {State Symbol : Type*}

/--
A multi-tape Turing machine with `k` work tapes over the alphabet of `Option Symbol` (where `none`
is the blank tape symbol). Note that it is not required that `Symbol` or `State` are finite
to keep the definition more general. The restriction will be introduced once we start talking about
computability by Turing machines in general.
-/
structure MultiTapeTM (k : ℕ) (Symbol State : Type*) where
  /-- initial state -/
  q₀ : State
  /-- transition function, mapping a state, the current input symbol and a tuple of work head
  symbols to a movement for the input head, actions on the work tape, optionally a symbol to output
  and the successor state -/
  tr (q : State) (input : Option Symbol) (work : Fin k → Option Symbol) :
    Action k Symbol State

namespace MultiTapeTM

variable {input : List Symbol} {tm : MultiTapeTM k Symbol State}

section Cfg

/-!
## Stepping a Turing Machine

This section defines the step function that lets the machine transition from one configuration to
the next, and the configuration reached after a number of steps. Configurations themselves are
defined in `TCSlib.Complexity.TuringMachine.Configuration`.
-/

/-- The step function corresponding to a `MultiTapeTM`. -/
def step (cfg : Cfg k Symbol State input) : Cfg k Symbol State input :=
  match cfg.state with
  -- in the halting state, we stay at the configuration
  | none => cfg
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).apply cfg

/-- The symbol (optionally) output when executing one step starting from configuration `cfg`. -/
def outputSymbol (cfg : Cfg k Symbol State input) : Option Symbol :=
  match cfg.state with
  | none => none
  | some q => (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).output

/-- The initial configuration corresponding to an input string. -/
@[simp]
def initCfg (input : List Symbol) : Cfg k Symbol State input := Cfg.init tm.q₀ input

@[simp]
lemma step_of_halt {cfg : Cfg k Symbol State input} (h : cfg.state = none) :
    tm.step cfg = cfg := by
  unfold step
  rw [h]

/-- The configuration reached by running the Turing machine for `t` steps from `cfg`.
If the Turing machine halts, it will stay at the halting configuration. -/
def runFrom (cfg : Cfg k Symbol State input) (t : ℕ) : Cfg k Symbol State input := tm.step^[t] cfg

@[simp]
lemma runFrom_zero {cfg : Cfg k Symbol State input} :
    tm.runFrom cfg 0 = cfg := by
  simp [runFrom]

lemma runFrom_succ_eq_step {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.runFrom (tm.step cfg) t := by
  simp [runFrom, Function.iterate_succ_apply]

lemma runFrom_succ_eq_step' {cfg : Cfg k Symbol State input} {t : ℕ} :
    tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) := by
  simp [runFrom, Function.iterate_succ_apply']

/-- Running `a + b` steps equals running `b` steps from the configuration reached after `a`. -/
lemma runFrom_add (cfg : Cfg k Symbol State input) (a b : ℕ) :
    tm.runFrom cfg (a + b) = tm.runFrom (tm.runFrom cfg a) b := by
  unfold runFrom
  rw [Nat.add_comm, Function.iterate_add_apply]

/-- The physical input head can move right by at most one cell per step.
**Proof sketch.** Clamping never increases a proposed position. Check the
three movements, then induct over the run, treating halted steps as stationary. -/
lemma timed_input_bound (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runFrom cfg t).inputPos.val ≤ cfg.inputPos.val + t := by
  have hm (p : Fin (input.length + 2)) (m : SignType) :
      (moveInputPos p m).val ≤ p.val + 1 := by
    dsimp only [moveInputPos]
    split <;> dsimp <;> cases m <;> simp_all [SignType.cast] <;> omega
  have hstep (d : Cfg k Symbol State input) :
      (tm.step d).inputPos.val ≤ d.inputPos.val + 1 := by
    cases hs : d.state with
    | none => simp only [MultiTapeTM.step, hs]; omega
    | some q =>
      simpa only [MultiTapeTM.step, hs, Action.apply] using
        hm d.inputPos (tm.tr q d.inputSymbol d.workTapeSymbols).inputTape
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step']
    exact (hstep _).trans (by omega)

/-- If a function `f` that maps the configurations of one TM to those of another one commutes with
their `step` function, then it also commutes with their `runFrom` function. -/
lemma runFrom_comm_of_step {k' : ℕ} {State' : Type*} {input input' : List Symbol}
    {tm : MultiTapeTM k Symbol State} {tm' : MultiTapeTM k' Symbol State'}
    (f : Cfg k Symbol State input → Cfg k' Symbol State' input')
    (hstep : ∀ cfg, tm'.step (f cfg) = f (tm.step cfg))
    (cfg : Cfg k Symbol State input) (n : ℕ) :
    tm'.runFrom (f cfg) n = f (tm.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (hstep c).symm) n cfg).symm

/-- Running from a halting configuration stays at that configuration. -/
@[simp]
lemma runFrom_of_halt (cfg : Cfg k Symbol State input) (h : cfg.state = none) {n : ℕ} :
    tm.runFrom cfg n = cfg :=
  Function.iterate_fixed (step_of_halt h) n

@[simp]
lemma outputSymbol_of_halt {cfg : Cfg k Symbol State input} (h_halt : cfg.state = none) :
    tm.outputSymbol cfg = none := by
  simp [outputSymbol, h_halt]

/-- The work-tape head moves by at most one cell in a single step. -/
lemma workTapePos_step_le (c : Cfg k Symbol State input) (i : Fin k) :
    |(tm.step c).workTapePos i - c.workTapePos i| ≤ 1 := by
  unfold step
  cases hstate : c.state with
  | none => simp
  | some q => exact workTapePos_apply_le _ c i

end Cfg

section Space
/-! Now we define space usage and add some helper lemmas. -/

/-- The set of positions visited by the head of work tape `i` in the computation starting from
configuration `cfg` up to step `t`. -/
def visitedByTapeHead (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : Finset ℤ :=
  (Finset.range (t + 1)).image fun t' => (tm.runFrom cfg t').workTapePos i

/--
The number of work tape cells touched by the head of tape `i` in the computation starting from
configuration `cfg` up to step `t`.
-/
def spaceUsedByTape (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) : ℕ :=
  (tm.visitedByTapeHead cfg t i).card

/--
The number of work tape cells touched by a computation starting from configuration
`cfg` up to step `t`.
-/
def spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) : ℕ := ∑ i, tm.spaceUsedByTape cfg t i

/-- A zero-tape Turing machine uses zero space. -/
@[simp]
lemma spaceUsed_zero_tapes_eq_zero (cfg : Cfg k Symbol State input) (t : ℕ) (h_zero : k = 0) :
    tm.spaceUsed cfg t = 0 := by
  unfold spaceUsed
  subst h_zero
  simp

/-- Each tape's space usage is bounded by the total space used. -/
lemma spaceUsedByTape_le_spaceUsed (cfg : Cfg k Symbol State input) (t : ℕ) (i : Fin k) :
    tm.spaceUsedByTape cfg t i ≤ tm.spaceUsed cfg t :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

/-- The space used up to step `t` is the space touched by the configurations up to step `t`. -/
lemma spaceUsed_eq_spaceUsedOfCfgs (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t = spaceUsedOfCfgs ((List.range (t + 1)).map (tm.runFrom cfg)) := by
  unfold spaceUsed spaceUsedByTape spaceUsedOfCfgs
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card ?_
  ext z
  simp [visitedByTapeHead, visitedOfCfgs]

end Space

open Cfg

/-- One step appends the symbol (optionally) emitted by that step to the output tape. -/
@[simp]
lemma step_output (cfg : Cfg k Symbol State input) :
    (tm.step cfg).output = cfg.output ++ (tm.outputSymbol cfg).toList := by
  unfold step outputSymbol Action.apply
  cases cfg.state <;> simp

/-- The output does not change after the machine has halted. -/
lemma runFrom_output_eq_of_halt
    (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    (tm.runFrom cfg t).output = (tm.runFrom cfg τ).output := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [runFrom_add, runFrom_of_halt _ hhalt]

/-- A proof that the Turing machine `tm` on input `input` outputs `output` in at most `t` steps
and uses exactly `s` space.
Note that this does not require the alphabet or state set to be finite. -/
def ComputesInTimeAndSpace
    (tm : MultiTapeTM k Symbol State)
    (input output : List Symbol)
    (t s : ℕ) : Prop :=
  (tm.runFrom (tm.initCfg input) t).state = none ∧
  (tm.runFrom (tm.initCfg input) t).output = output ∧
  tm.spaceUsed (tm.initCfg input) t = s

/-- A machine computes `f` between the supplied encodings, with bounds depending on the input.
The machine's alphabet and state type need not be finite. -/
def ComputesFunInTimeAndSpace {α β : Type*}
    (tm : MultiTapeTM k Symbol State)
    (encIn : α ↪ List Symbol) (encOut : β ↪ List Symbol)
    (f : α → β) (t s : α → ℕ) : Prop :=
  ∀ a, ∃ t' ≤ t a, ∃ s' ≤ s a,
    ComputesInTimeAndSpace tm (encIn a) (encOut (f a)) t' s'

/-- A function is computable within the input-indexed bounds by a machine with binary alphabet
and finitely many states. -/
def ComputableInTimeAndSpace {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
    ComputesFunInTimeAndSpace tm encIn encOut f t s

/-- There exists a binary Turing machine with finitely many states that, for every input `a`,
computes `encOut (f a)` from `encIn a` in at most `t (encIn a).length` steps,
using at most `s (encIn a).length` work-tape cells. -/
abbrev ComputableInTimeAndSpaceOfLength {α β : Type*}
    (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (t s : ℕ → ℕ) : Prop :=
  ComputableInTimeAndSpace f encIn encOut
    (fun a => t (encIn a).length) (fun a => s (encIn a).length)

/-- Resource bounds can be weakened independently on every input. -/
theorem ComputesFunInTimeAndSpace.mono {α β : Type*}
    {tm : MultiTapeTM k Symbol State} {encIn : α ↪ List Symbol} {encOut : β ↪ List Symbol}
    {f : α → β} {t s t' s' : α → ℕ}
    (h : ComputesFunInTimeAndSpace tm encIn encOut f t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputesFunInTimeAndSpace tm encIn encOut f t' s' := fun a => by
  obtain ⟨u, hu, v, hv, hc⟩ := h a
  exact ⟨u, hu.trans (ht a), v, hv.trans (hs a), hc⟩

/-- Computability is monotone in the resource bounds. -/
theorem ComputableInTimeAndSpace.mono {α β : Type*}
    {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {t s t' s' : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : ∀ a, t a ≤ t' a) (hs : ∀ a, s a ≤ s' a) :
    ComputableInTimeAndSpace f encIn encOut t' s' := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := h
  exact ⟨k, State, hfinite, tm, htm.mono ht hs⟩

open Classical in
/-- The Boolean indicator function of a set. -/
noncomputable def indicator {α : Type*} (L : Set α) : α → Bool :=
  fun x => if x ∈ L then true else false

/-- A set is decidable within the given input-indexed bounds when its Boolean indicator is. -/
def DecidableInTimeAndSpace {α : Type*} (L : Set α) (enc : α ↪ List Bool)
    (t s : α → ℕ) : Prop :=
  ComputableInTimeAndSpace (indicator L) enc ⟨fun b => [b], by intro a b h; simpa using h⟩ t s

/-- The Turing machine `tm` halts after exactly `t` steps on input `input`
if its state is `none` at step `t` and non-none at step `t - 1`.
Note that every Turing machine hast to perform at least one step to halt. -/
def haltsAtStep (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) : Bool :=
  (tm.runFrom (tm.initCfg input) t).state.isNone &&
  !(tm.runFrom (tm.initCfg input) (t - 1)).state.isNone

/-- If a Turing machine halts, the time step is uniquely determined. -/
lemma halting_step_unique
    {tm : MultiTapeTM k Symbol State}
    {input : List Symbol}
    {t₁ t₂ : ℕ}
    (h_halts₁ : tm.haltsAtStep input t₁)
    (h_halts₂ : tm.haltsAtStep input t₂) :
    t₁ = t₂ := by
  wlog h : t₁ ≤ t₂
  · exact (this h_halts₂ h_halts₁ (Nat.le_of_not_le h)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d with
  | zero => rfl
  | succ d =>
    have halts₁ : (tm.runFrom (tm.initCfg input) t₁).state = none := by
      simp [haltsAtStep] at h_halts₁
      exact h_halts₁.left
    have halts₂ : (tm.runFrom (tm.initCfg input) (d + t₁)).state ≠ none := by
      grind [haltsAtStep, runFrom]
    refine absurd ?_ halts₂
    rw [Nat.add_comm, runFrom_add, tm.runFrom_of_halt _ halts₁]
    exact halts₁

/-- If a deterministic machine repeats a non-halting configuration, it never halts,
because the sequence between the two configurations will loop forever.
Note that this can be applied to two arbitrary and different time steps `t` and `t + Δ`
using `tm.runFrom_add`. -/
lemma not_halts_of_repeat_nonhalt
    (cfg : Cfg k Symbol State input)
    (h_not_halt : cfg.state ≠ none)
    (t : ℕ)
    (heq : tm.runFrom cfg (t + 1) = cfg) :
    ∀ t', (tm.runFrom cfg t').state ≠ none := by
  intro t'
  -- The configuration will repeat every `t + 1` steps.
  have hloop : ∀ n, tm.runFrom cfg (n * (t + 1)) = cfg := by
    intro n
    unfold runFrom
    rw [Nat.mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed heq n
  by_contra hnh
  -- Assuming the machine halts at step `t'`, it is also halted at step `t' * (t + 1)`
  have h₁ : (tm.runFrom cfg (t' * (t + 1))).state = none := by
    have hle : t' ≤ t' * (t + 1) := by grind
    obtain ⟨tΔ , htΔ⟩ := Nat.exists_eq_add_of_le hle
    rw [htΔ, tm.runFrom_add]
    simp [hnh]
  simp [hloop t', h_not_halt] at h₁

end MultiTapeTM

end Turing

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


## ===== audits/logs/ch4-p41-sweep.log =====

```
P4.1 GATE SWEEP at commit edea2663748fe2b1e47636094b95744ed50148f0 (edea2663), branch complexity/arora-barak-ch3-4, started 2026-10-08 17:50:57
== TCSlib/Complexity/TuringMachine/NondeterministicSpace
TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean:89:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean:107:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/SpaceComplexity/NSPACE
TCSlib/Complexity/SpaceComplexity/NSPACE.lean:97:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/NSPACE.lean:111:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/SpaceComplexity/SpaceClasses
TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean:69:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean:76:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/SpaceClasses.lean:83:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/SpaceComplexity/Constructible
TCSlib/Complexity/SpaceComplexity/Constructible.lean:68:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Constructible.lean:79:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/SpaceComplexity/Inclusions
TCSlib/Complexity/SpaceComplexity/Inclusions.lean:55:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Inclusions.lean:63:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Inclusions.lean:85:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Inclusions.lean:93:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/SpaceComplexity/Examples
TCSlib/Complexity/SpaceComplexity/Examples.lean:60:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/SpaceComplexity
P41_SWEEP_DONE

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
