# External audit pack — Chapter 3, phase P3.3, round 2 (re-audit of the round-1 repairs)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase
P3.3, round 2. Round 1 (`audits/ch3-p33-findings.md`, attached verbatim)
returned **0 blockers, 2 majors, 7 minors, 2 notes** — both majors in
`ntime_hierarchy`'s proof sketch (the per-code universal constant cannot be
absorbed by choosing a padded large index, and the stage locator as
sketched was not computable within the allowance); no literal statement was
refuted. This round audits the repairs. The gate closes on zero blockers
and zero majors.

Audited at commit `9a92fa1a` (branch `complexity/arora-barak-ch3-4`). The
complete repair is the attached diff
(`audits/evidence/ch3-p33-r2-repairs.diff`): **every theorem and definition
is unchanged**; the repairs are the rebuilt `ntime_hierarchy` sketch and
six sketch/docstring corrections. The inventory is unchanged (**7 sorried
statements, 7 definitions, 1 skeleton-time proof**).

## Brief for the auditor

You have the round-1 report. Your deliverables:

1. **For the two majors**: work the rebuilt lazy-diagonalization sketch
   against your own analysis. Its elements: **(i)** the fixed-code stage
   schedule `i = pair(j, r)` — every code recurs at infinitely many stages,
   so the alleged decider's constants (`C_α`, `C₁`, `c₀`) are **fixed**
   along its own subsequence and no padded-index selection occurs (your
   first proposed option); **(ii)** the `f`-adaptive ladder
   `T*_i := (f(ℓ_i + 1) + ℓ_i + 1)²`, `ℓ_{i+1} := 2^{(T*_i)²}`, located by
   **bit-length arithmetic with capped witness runs**, where an unfinished
   capped `f`-witness run itself decides the comparison (`ℓ_{i+1} > n`) —
   your "stop evaluating the next value when the current allowance is
   exhausted"; check the amortized locator ledger and your own oscillating
   interior example against it; **(iii)** the **self-clocked** mid-rung —
   the fixed interpreter core under `D`'s own fused `K·(g n + 1)` countdown
   with `K` independent of the code, cut branches rejecting — so
   `D ∈ NTIME (g+1)` holds by construction, and the chain (3.3) needs only
   that the *relevant* branches finish, which the domination hypothesis's
   `f(n+1)` addend supplies at the fixed assembled constant
   `A* := C_α·(C₁·c₀ + C₁ + 1) + 1`; **(iv)** the top rung at
   `T*_i ≥ C₁·(c₀·f(a) + 1)` eventually (a square against fixed constants
   — the hypothesis's `f n` addend instantiated at the stage bottom `a`,
   exactly your "also require the bound for `f(a)`"), with `BF`'s
   exponential cost beaten by `g n ≥ n = 2^{(T*_i)²}` along the
   subsequence. Verify each inequality chain and flag any remaining
   quantifier slip; the statements themselves are unchanged.
2. For the **minors**: verify the `2 · 27` record count with the scaled
   parser guard (finding 3); the arbitrary-time canonizer route with no
   polynomial claim (finding 4); the **amortized** countdown with the
   `Σ ν₂(j) ≤ t` ledger and the significant-end representation named
   (finding 5); `O_N((k+1)(t+1))` (finding 6); the honest timeout-polarity
   explanation — cut branches reject, no all-branch completion claim, the
   backward direction through the original decider's halting (finding 7);
   "every **positive** `A`" (finding 9). Finding 8 was a **pack erratum**
   (the round-1 pack wrongly asserted `g 0 = 0` impossible under
   `TimeConstructible`): acknowledged here — shipped packs are never
   edited — and the `g + 1`/`hpos` seam stands as the deterministic
   precedent documents.
3. Report anything the repairs broke or newly misstate, same table and
   severity scale. The round-1 notes (the monotone-equivalence
   qualification, the oscillating-bounds strengthening disclosure) are
   retained as declared.

Sources as in round 1 ([AB09] §1.4, §2.1.2 + Exercise 2.6, §3.2 with
Figure 3.1; [Coo72], [BGW70] through [AB09]).

## Scope

| Item | Where |
|---|---|
| Under audit | the attached diff: `TuringMachine/NDCodes.lean` (the existence sketch's record count and canonizer route) and `Diagonalization/NTimeHierarchy.lean` (the rebuilt hierarchy sketch, the timeout-polarity and amortized-clock bullets, the universal and normal-form sketch corrections, the showcase wording) |
| Unchanged, re-attached | every declaration of both files (byte-identity checkable in the diff) and the round-1 context set |
| Declared, out of scope | the concurrent §12/P3.2/P4.3 repairs in the same commit range (disjoint files, own rounds); tactic proofs |

## Per-finding disposition (verify each)

| # | Round-1 finding | Repair |
|---|---|---|
| 1 | **major** — per-code constants vs padded indices: no law preserves cost under padding | Fixed-code scheduling: the stage schedule runs code `α_j` at every stage `i = pair(j, r)`, so the decider's code — and hence `C_α` — is literally the same at infinitely many stages; the domination hypothesis is instantiated once, at the fixed assembled constant. Padding never enters |
| 2 | **major** — the ladder/locator was not computable within the allowance | The explicit recurrence `T*_i := (f(ℓ_i+1) + ℓ_i + 1)²`, `ℓ_{i+1} := 2^{(T*_i)²}` over `f`'s witness, compared against `n` by bit-length arithmetic with **capped runs whose failure itself decides the comparison**; completed stages sum geometrically, the final incomplete evaluation is capped, and `D`'s global `K·(g n + 1)` self-clock makes class membership hold by construction — separating the two obligations your report distinguished (uniform cost of `D`; eventual success for the fixed code) |
| 3 | minor — `2 · 9` records | `2 · 27 = 54` per state, with the parser guard scaled |
| 4 | minor — the polynomial canonizer is not received | The sketch follows the arbitrary-time mirror (`MathlibBridge` supersedes its polynomial variant); no polynomial ND canonizer claimed or needed |
| 5 | minor — per-tick decrement cost is unbounded | "Amortized", with the `Σ_{j≤t} ν₂(j) ≤ t` borrow ledger and the significant-end/zero-test representation named, in both the design bullet and the universal's sketch |
| 6 | minor — `O_N(k·t)` vanishes at `k = 0` | `O_N((k+1)·(t+1))`, with the zero-tape case named |
| 7 | minor — "the timeout polarity never bites" is wrong | The honest explanation: runaway guess branches exist even for total deciders and are cut; cut branches **reject**, which never creates a false positive; accepting witnesses finish within the forward bound; the backward direction truncates at the *original* decider's all-branch budget |
| 8 | minor — the pack's `g 0 = 0` claim | **Pack erratum acknowledged** (`timeConstructible_id` is the counterexample); the `g + 1` and `hpos` seam retained as in the deterministic precedent |
| 9 | minor — "fails for every `A`" | Now "fails for every **positive** `A`", with `A = 0` noted vacuous |
| 10-11 | notes | Retained as declared: the monotone-case equivalence and the genuine nonmonotone strengthening; the square showcase as the chosen alternative, not a rounding of `n^{3/2}` |

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch3-p33-r2-sweep.log`, revision recorded
  at start: `9a92fa1a`): both modules, 0 `error:` lines, fresh `.olean`s,
  exactly **7** `declaration uses 'sorry'` warnings (NDCodes 1,
  NTimeHierarchy 6).
* Style lint (`audits/logs/ch34-r2-repairs-stylelint.log`):
  `Diagonalization` 0 FAIL / 0 WARN over 4 files; `TuringMachine` 0 FAIL
  (size WARNs as recorded in the §12 round-2 pack).
* Statement-freeze baseline: commit `9a92fa1a`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch3-p33-r2-findings.md`; the gate closes on zero blockers and
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


## ===== audits/ch3-p33-findings.md =====

```
# P3.3 statement-gate audit

**Verdict: FAIL — 0 blockers, 2 majors, 7 minors, 2 notes. The gate remains open.**

The two majors concern the quantitative construction in `ntime_hierarchy`'s proof sketch. I found no counterexample to a literal Lean theorem statement. In particular, the findings do **not** refute the nondeterministic time hierarchy theorem. They identify missing arguments needed to turn this phase's particular interfaces and sketch into the promised uniform machine construction.

Audited input: `ch3-p33-bundle.md`, purported revision `a664c3e407a24e862d3ce719e589a8ef6533798c`. Its SHA-256 independently matches:

`45339e257283d441ad0afd38a6ed9d6c563ef72688a3f6b6e58b833e3b031ee1`

Scope: all seven definition bodies, seven sorried contracts, their sketches/docstrings, and `NDMachineCode.decode_encode`; the attached closed interfaces were read where needed. This was a single-agent audit. Declaration references below use the original attachment line numbers. `NDCodes.lean` and `NTimeHierarchy.lean` abbreviate the two full paths specified in the pack.

Primary-source comparison: [Arora–Barak, *Computational Complexity*, 2009, reproduced PDF](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press(2009).pdf), printed pp. 16, 19–20, 41–42, 64, 69–71, and the Exercise 2.6 hint on pp. 531–532. I checked the total-code/padding requirements, binary-choice and all-branch-time conventions, linear simulation exercise, and the delayed-diagonalization construction. The source states the shifted little-o hypothesis and illustrates a separation between linear time and time with exponent 3/2. Neither the referenced definition of time constructibility nor Theorem 3.2 explicitly adds monotonicity. No external Cook or Book–Greibach–Wegbreit text was needed.

**Findings**

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `NTimeHierarchy.lean` · `ntime_hierarchy`, sketch at lines 215, 220, 225, 227 | The per-code universal bound and arbitrarily large padded indices yield both a uniformly `O(g(n)+1)` diagonal machine and the required successful stage. | The universal provides `∀ α, ∃ Cα`, whereas class membership needs one constant for all input lengths and therefore all stages. Choosing a budget proportional to `g(n)` does not absorb unbounded `Cαᵢ`. Dividing the budget by `Cαᵢ` creates a second problem: padding changes `αᵢ`, hence potentially the constant and its eventual-domination threshold. Padding preserves `decode`; no stated law preserves cost. The inference from “arbitrarily large padded index” to “past the threshold for that index's constant” is invalid. Details below. | Supply a concrete uniformly clocked diagonal construction and resolve the padding dependence. Options include an explicit interpreter estimate with a padding-independent simulation rate plus controlled startup, or scheduling the **same fixed code** at arbitrarily late stages. Define the actual budget and account for computing it. At the stage bottom also require the bound for `f(a)`, not only `f(a+1)`. Preserve the linear-overhead signatures. |
| 2 | major | `NTimeHierarchy.lean` · `ntime_hierarchy`, sketch at lines 211, 212, 213, 217, 221 | The displayed recurrence defines an effective stage locator running in `O(g(n))`. | “BF's bound” uses existential code-dependent coefficients with no computability export. A sequence selected by classical choice is not automatically a TM-computable sequence. Even with explicit coefficients, the sketch does not supply a capped evaluation procedure or an amortized locator ledger. The top-branch inequality pays for BF **at the top**; it does not pay for finding the top from an interior input. `TimeConstructible g` does not imply `g(a) ≤ g(n)` for `a < n`. | Specify computable stage data, include the cost of code/budget preparation, and give a locator using bounded evaluation of the next stage value. Prove its cumulative cost, including the final incomplete computation, is bounded by one fixed multiple of `g(n)+1`. Explain how its clock itself has linear total cost. |
| 3 | minor | `NDCodes.lean` · `exists_effectiveNDMachineCode`, line 174 | There are `2 · 9` transition records per state. | The actual definition enumerates two choices and three reads independently on the input and each of two work tapes: `2 · 3 · 3 · 3 = 54 = 2 · 27`. Following the stated 18-record parser plan would not parse the actual serialization. | Replace `2 · 9` by `2 · 27`; update the parser's minimum-length guard and all enumeration lemmas accordingly. |
| 4 | minor | `NDCodes.lean` · `exists_effectiveNDMachineCode`, lines 178, 179 | The polynomial canonizer ledger is inherited from the deterministic construction. | Attached `MathlibBridge.lean`, lines 1078, 1085, 1089, explicitly supersedes the polynomial construction and delivers an arbitrary-time computability route. A polynomial ND parser/canonizer is plausible, but is a new obligation, not a received time ledger. | Either follow the arbitrary-time mirror, which suffices for the literal existence statement, or explicitly commission and justify a new polynomial construction. If hierarchy costs use the stronger property, expose and prove it. |
| 5 | minor | `NTimeHierarchy.lean` · `exists_timed_universal_NDTM`, lines 101, 105, 106 | Each binary decrement, and hence each simulated step, costs `O(table length)` independently of `t`. | At `t = 2^r`, an ordinary first decrement borrows across `r` low zero bits. Its worst-case cost is unbounded with `r` even for a fixed one-state table. The **total** countdown can nevertheless be linear; the amortized proof below repairs the argument. | Say “amortized,” name the counter representation/zero test, and include the total borrow-and-return ledger. Fusing the clock alone does not establish the claimed bound. |
| 6 | minor | `NTimeHierarchy.lean` · `FinNDTM.exists_codeNDTM_accepts_linear`, line 166 | The construction costs `O_N(k · t)` for every `k`. | For `k = 0`, it still guesses a display and performs the input-verification sweep. A bound proportional to `k · t` is zero. The theorem's `C · (t+1)` is sound. | Use `O_N((k+1)(t+1))`, then absorb the fixed tape count into `C`. |
| 7 | minor | `NTimeHierarchy.lean` module docstring, lines 34, 35, 36; pack deviation 4 | Under the contradiction hypothesis the coded machine beats the budget, so timeout polarity never matters. | The normal-form theorem deliberately gives no all-branch halting guarantee for the coded machine. Its proposed guess phase has infinite nonaccepting branches even when the original decider is total. Those branches still time out. Rejecting them is correct; accepting them could produce false positives. | Explain the actual reason: accepting witnesses finish within the forward bound, and every completed accepting display is sound. The original decider's halting bound is used for backward truncation. Do not assert that all coded branches finish. |
| 8 | minor | Pack · specific question 7 | `g 0 = 0` is impossible under `TimeConstructible`. | `TimeConstructible` permits `c · (T(n)+1)` time. Attached `timeConstructible_id` is an explicit counterexample to the assertion. The received deterministic hierarchy already documents this seam. | Record a pack erratum. Retain `g+1` and the explicit positivity hypothesis in the positive form. |
| 9 | minor | `NTimeHierarchy.lean` · `NTIME_linear_ssubset_square`, line 262 | `A · (2n+2)^2 ≤ (n+1)^2` fails for every `A`. | It holds for `A = 0`; it fails for every `A ≥ 1`. The pack's corresponding qualification is already correct. | Change the docstring to “every positive `A`.” |
| 10 | note | `ntime_hierarchy` and showcase · delivered strength | The extra `f(n)` term is harmless for monotone `f`, but genuinely restricts nonmonotone bounds; the square example is a weaker illustration than the book's example. | The exact comparison and an oscillating counterexample appear below. These restrictions are declared. The principal contracts retain linear, rather than quadratic, dependence on the simulated time. | Keep the qualifications visible: equivalence to the shifted gap is established for monotone `f`; the square is the chosen alternative showcase, not mere rounding of exponent `3/2`. |
| 11 | note | Pack · repository attestations | The attachments support the inventory/log readings, not independent replay of repository history or build freshness. | Source count is 7 definitions, 7 `sorry`s, and 1 proved theorem. The sweep contains 7 admission warnings and no `error:` lines. Root imports include both audited modules. No complete build checkout/toolchain was supplied here. | Preserve the distinction between independently checked packet facts and maintainer attestations; no new build claim is made by this audit. |

**Independent restatements of all seven definitions**

1. **`CodeNDTM` — line 86.** An element consists of a natural number `numStates` and a binary-choice nondeterministic TM with exactly two work tapes, binary nonblank symbols, and exactly `numStates+1` named live states. The initial live state is part of the underlying machine; halting is represented separately by `none`. Thus `numStates = 0` means one live state, not an empty state space.

2. **`CodeNDTM.toFinNDTM` — line 93.** Repackage that same machine as a bundled finite NDTM, retaining its two tapes, state type, initial state, and transition functions. There is no simulation or time change.

3. **`workPair` — line 100.** This is the two-coordinate function whose value at tape 0 is `w₀` and whose value at tape 1 is `w₁`. Since `Fin 2` has only these two elements, it enumerates every possible pair of work-head reads exactly once as its two arguments range independently over `Option Bool`.

4. **`actionBits₂` — line 106.** Concatenate the encodings of input move, tape-0 write, tape-0 move, tape-1 write, tape-1 move, optional emission, and optional successor state, in that order. Relative to `actionBits`, precisely one work-write/move pair is inserted before the emission. In particular, “no write” and “write blank” remain different encodings.

5. **`CodeNDTM.serialize` — line 119.** Encode the state-count parameter as the first component of `pairEncode`; its second component begins with the self-delimiting initial-state index and then lists all transition records. The order is choice, state, input read, tape-0 read, tape-1 read, with the last coordinate varying fastest. There are `54(numStates+1)` records. The calls to `workPair w₀ w₁` and the order of the two action records agree.

6. **`NDMachineCode` — line 134.** A scheme supplies an encoder, a total decoder, and the equation `decode(encode(M) ++ true^m) = M` for every machine and padding length. Consequently decoding is onto, encoding is one-to-one, and each machine has infinitely many codes, distinguished by length. These are three fields, not three independent proved computability laws: the structure alone does not require an effective decoder, encoder, or padding-time bound.

7. **`EffectiveNDMachineCode` — line 155.** Add one finite deterministic TM that computes the fixed serialization of the decoded machine on every string, with a time bound depending only on string length. Neither polynomial time nor computability of the supplied numerical bound is asserted. Crucially the output format is independent of the representation scheme: its complete finite table and initial state determine the coded machine, so a noncomputable semantic reassignment cannot be hidden by choosing a matching scheme-specific encoder.

These bodies have the intended meanings. The two-work-tape carrier is adequate for direct interpretation, exhaustive deterministic replay, and display-and-replay normalization. The weaker acceptance-only normal-form transfer is a declared design choice, not an accidental assertion of all-branch totality.

For the serialization arithmetic, each action uses six two-bit fields followed by a successor field of at least one bit. Therefore

\[
\#\text{records per state}=2\cdot3^3=54,
\qquad
\text{minimum action length}=6\cdot2+1=13.
\]

A useful minimum table-length guard is consequently `702(numStates+1)` bits. A one-state silent-halting machine with all stationary/no-write actions has serialization length

\[
2+1+54\cdot13=705.
\]

The first `2` is the paired empty state-count header, and the next `1` is `unaryFin 0`. Parsing the fixed number of records and then checking an all-true suffix distinguishes padding from the table; the final unary state terminator is consumed as part of its field.

**Skeleton-time proof: `NDMachineCode.decode_encode`**

The complete proof body is `simpa using c.decode_encode_pad M 0`. Its logical steps are exactly

\[
\begin{aligned}
&c.decode(c.encode(M)\mathbin{++}\operatorname{replicate}(0,\mathrm{true}))=M,\\
&\operatorname{replicate}(0,\mathrm{true})=[],\\
&c.encode(M)\mathbin{++}[]=c.encode(M),\\
&c.decode(c.encode(M))=M.
\end{aligned}
\]

The first line instantiates the structure field; the next two are list simplifications. The last is precisely the goal. No machine-construction theorem or admitted existence theorem is used by this proof.

**All seven sorried contracts: literal meaning and construction assessment**

1. **`exists_effectiveNDMachineCode`.** It asserts nonemptiness of the effective-scheme structure, without a polynomial bound. A parser with the corrected 54-record enumeration, range checks, immediate failure on insufficient data, a fixed fallback, and tolerance of an all-true suffix gives the required total decoder and round trip. Parsing and reserialization are effective finite-string operations; the arbitrary-time compiler route described in the attached deterministic mirror suffices, and a maximum of halting times over the finitely many strings of each length supplies the time-bound field. **True as stated; findings 3–4 correct its construction description.**

2. **`exists_timed_universal_NDTM`.** One machine is chosen after the scheme; after each code, one constant must work for every input and every budget, guaranteeing both unconditional all-branch termination and exactly bounded source acceptance. Copy/canonize only the code prefix, interpret the two tapes directly, consume a choice bit only at each simulated transition, and use an amortized countdown; simulated halting must be checked after the last permitted transition. On timeout, reject, even if the source has already emitted a singleton true without halting; a finite output-status flag suffices to emit a verdict only at completion. **True as stated with the clock accounting below; this interface alone does not supply finding 1's stage-uniform estimate.**

3. **`exists_ndAcceptsWithin_decider`.** One deterministic machine must output exactly `[true]` or `[false]` according to bounded acceptance, within one code-dependent exponential budget valid for all inputs. Enumerate all `2^t` length-`t` choice words, cut every replay after at most `t` source steps, and retain only whether the halted output is exactly `[true]`; reset the visited work intervals, virtual input position, choice head, and countdown between replays. With a fixed code-dependent constant `d`, this costs at most `d(t+1)2^t`, after enlarging `d` to cover startup. **True as stated; diverging branches cannot stall a replay, and the two implications exhaust all cases.**

4. **`FinNDTM.exists_codeNDTM_accepts_linear`.** For each finite NDTM, one two-work-tape coded machine and constant preserve acceptance forward within `C(t+1)`; conversely, any bounded acceptance of the coded machine implies eventual acceptance of the original, with no reverse time estimate. Guess fixed-width records with initial-state, transition, termination, and output checks in finite control; verify the input and each work tape in separate sweeps, using fixed-size binary blocks for any auxiliary marks. There are `k+1` sweeps, each linear in display length; rewinding the display and clearing the marked replay interval have the same cost. **True as stated, including `k=0`; infinitely guessing branches are permitted, and backward truncation below suffices for the consumer.**

5. **`ntime_hierarchy`.** Its conclusion is strict inclusion of sets of languages, under constructibility of both bounds and eventual domination of every constant multiple of the displayed sum. The inclusion follows rigorously by finite absorption as shown below; if the lower bound vanishes, strictness reduces to nonemptiness of the positive upper class. For positive lower bounds, the intended general separation is the standard hierarchy claim with a stronger domination premise, but the supplied stage construction does not yet establish it: findings 1–2 prevent a complete true-as-stated construction argument from these interfaces. **Statement not refuted; sketch not approved, including for the otherwise benign monotone instances.**

6. **`ntime_hierarchy_of_pos`.** It has the same premises plus positivity of `g`, and concludes strict inclusion into `NTIME g`. For every length and every constant, `c(g(n)+1) ≤ 2c g(n)`; all-branch halting and bounded acceptance transfer using extension and truncation. The opposite inclusion is monotonicity, so the two upper classes are equal. **Correct reduction conditional on the summit theorem; no additional gap.**

7. **`NTIME_linear_ssubset_square`.** This is the unconditional strict separation between the two specified positive integer-valued bounds. Substituting them into the summit gives exactly `A(3n+4) ≤ (n+1)^2` eventually, as verified below. An amortized input-scan counter computes `n+1`; binary grade-school multiplication then computes its square in a budget well inside `O((n+1)^2)`, including a constant budget at the empty input. **Sound intended instance; its proposed derivation still inherits the summit's unclosed construction obligations.**

**Resource and implication checks**

The nested input format has prefix length

\[
2\bigl(2\,|\operatorname{bits}(t)|+2+|\alpha|\bigr)+2
=4\,|\operatorname{bits}(t)|+2|\alpha|+6.
\]

It contains no contribution from `x`. The outer separator locates the end of the code, so startup need not scan the input suffix. The virtual left boundary must still be marked and its clamp emulated; the physical delimiter is not a virtual blank. During `t` source transitions only an initial distance of at most `t` can be visited. This also permits replay reset without searching for the far end of a huge input. Thus the absence of an input-length term in both universal contracts is sound.

For the countdown, let `ν₂(j)` be the number of trailing binary zeros of positive `j`. A decrement from `j` borrows across `ν₂(j)` cells; return-to-origin work is proportional to the same quantity. Summing over a full countdown gives

\[
\sum_{j=1}^{t}\nu_2(j)
=\sum_{r\ge1}\left\lfloor\frac{t}{2^r}\right\rfloor
\le t.
\]

All sums are finite after their zero terms are removed. A counter maintaining its significant end and testing zero without a full-width scan on every tick therefore has total cost `O(t+|bits(t)|+1)=O(t+1)`. For a fixed code, adding table scans and startup gives the stated `C(t+1)`. This is a total-cost argument; it does not justify the current pointwise claim about every tick.

For the deterministic evaluator, using `t+1 ≤ 2^(t+1)` and choosing `C ≥ max(d,2)` gives

\[
d(t+1)2^t
\le d\,2^{2t+1}
\le C\,2^{C(t+1)}.
\]

The empty choice word is the sole replay at `t=0`. Cleanup must delimit the visited interval even when virtual cells have been erased to blank; a fixed-size block encoding can carry the interval/origin marks. This is a concrete replay implementation obligation, not a need for a term depending on the full input length.

Choice-word alignment is valid in both directions. On an accepting source run, place its bits at successive interpreter transition boundaries, choose arbitrary bits at deterministic bookkeeping steps, then pad after the host halts. Conversely, extract the bits at completed source transitions from an accepting host branch and pad the extracted source word to length `t`. Output `[true]` without source halting must never count as acceptance. These observations also cover first halting exactly at the deadline.

Backward truncation uses the original machine's all-branch bound, never an assumed bound on the normalized machine. Precisely, if `N.tm.HaltsWithin x T`, then

\[
(\exists s,\ N.\mathrm{AcceptsWithin}(x,s))
\iff N.\mathrm{AcceptsWithin}(x,T).
\]

For the nontrivial direction, take an accepting word `w` of length `s`. If `s≤T`, pad it. If `T≤s`, split it as `w.take T ++ w.drop T`. The prefix has halted by the hypothesis, and `runWith_append` followed by `runWith_of_halt` makes the full run equal to that prefix run, preserving `[true]`. Hence the unbounded backward normal-form clause is exactly adequate.

Consequently, whenever `N` decides `L` within `c₀ f` and the budget at an input `x` is at least `C₁(c₀ f(|x|)+1)`,

\[
x\in L
\iff M'.\mathrm{AcceptsWithin}(x,\text{budget}).
\]

At a stage bottom `a=ℓᵢ+1`, the top flip needs this inequality with `f(a)`. The middle transition from `n` to `n+1` needs it with `f(n+1)`. The theorem's sum already contains both terms; the repaired ledger should use both.

For inclusion, choose a threshold from `hfg` with `A=1`, and define the finite constant

\[
F=1+\sum_{j<N} f(j).
\]

For `n<N`, `f(n)≤F≤F(g(n)+1)`; for `n≥N`, `f(n)≤g(n)≤F(g(n)+1)`. An `NTIME f` decider with coefficient `c` therefore works with coefficient `cF` for `g+1`, using the same extension/truncation argument. This part does not need monotonicity.

**Why the two major findings remain**

For finding 1, the two available facts have the forms

\[
\forall A\ \exists N\ \forall n\ge N:
A\bigl(f(n+1)+f(n)+n+1\bigr)\le g(n),
\]

and

\[
\forall R\ \exists i\ge R:\quad c.decode(\alpha_i)=M'.
\]

They do not imply that some such `i` lies past the domination threshold for a new coefficient depending on `αᵢ`. As a pure quantifier test, the eventually true inequalities `A≤n` have threshold `A`; along any increasing sequence of stage starts `aᵢ`, the varying coefficients `Aᵢ=aᵢ+1` fail at **every** corresponding start. The exports impose no condition that rules out this dependence. Merely enlarging existential overhead witnesses is already enough to show why selecting arbitrary witnesses cannot justify the inference.

There are two separate obligations here: bounding the running time of `D` uniformly over all codes used by its stages, and guaranteeing that a stage for the alleged decider eventually has enough simulation time. A clock on the diagonal machine's own work can solve the first without solving the second. Reusing one fixed code at arbitrarily late stages, or proving a padding-stable simulation coefficient with separately bounded startup, addresses the second. The current sketch supplies neither complete combination.

For finding 2, a numerical upper bound is not an executable stage locator. `canonizerTime` is not required to be computable, and neither universal theorem exports a computable function selecting its coefficient. The fill may choose concrete implementations with additional properties, but those properties must be established rather than inferred from the existing existential signatures.

There is also a distinct time issue for interior inputs. For example, take `f(n)=n+1` and let `g(n)=2^n` at odd lengths and `(n+1)^2` at even lengths. Both are time constructible in the attached convention and satisfy the displayed eventual domination condition. Nevertheless, at arbitrarily large odd `a`,

\[
a<a+1,
\qquad
g(a)=2^a\gg g(a+1)=(a+2)^2.
\]

An allowed constructibility witness can spend order `g(a)` time before returning; its upper bound provides no affordable uncapped call at an interior input of length `a+1`. A bounded evaluation procedure can potentially resolve this, so the example is **not** a counterexample to the theorem. It shows what must be proved about the proposed locator, particularly since the sketch mentions iterated `f`-witness runs while its budget is obtained from `g`.

At the top itself the advertised inequality is correct:

\[
\mathrm{BFbound}\le\ell_{i+1}=n\le g(n).
\]

The equality in the middle is essential. At an interior point it is instead `n<ℓᵢ₊₁`. A repaired sketch needs an explicit computable recurrence, a way to stop evaluating the next value when the current allowance is exhausted, and an amortized sum for completed stages plus that last attempt. I have not supplied or verified that full machine construction in this audit.

**Adversarial instantiations**

| Test | Instantiation and result |
|---|---|
| A1: zero budget | For every initialized NDTM, the only length-zero word is `[]`, and its run still has state `some q₀`. Thus bounded acceptance at zero is false. The universal must halt without acceptance, and BF must output `[false]`. Their witnesses cannot use `C=0`. |
| A2: immediate acceptance | A one-live-state machine whose two actions emit true and halt accepts every input at time 1, including the empty input, but never at time 0. The universal's deadline convention must distinguish these cases. |
| A3: output before halting | A two-state machine emits true, then loops forever without further output. It has no accepting bounded run despite eventually having output `[true]`. Timeout must reject. Simply halting a pass-through simulator would be unsound. |
| A4: malformed short codes | For the proposed parser scheme, `α=[]` and `α=[true]` fail the paired header and denote the silent-halting fallback. Universal and BF clauses still apply, with false bounded acceptance at all times. For an arbitrary effective scheme, these strings need not denote that fallback; the contracts correctly use whatever the total decoder returns. |
| A5: enormous input, tiny budget | Fix any code and `t∈{0,1}`; let the input length grow without bound. The prefix formula above is unchanged, and no suffix scan is necessary. No hidden input-length term was found. |
| A6: empty input and boundary moves | On `x=[]`, the virtual initial position is the right blank adjacent to the virtual left boundary. Repeated left moves must clamp at the virtual left blank, not expose the pairing delimiter. The established marker discipline handles this. |
| A7: zero work tapes | A zero-work-tape immediate acceptor is allowed. Its normalization needs a guessed record and input check, exposing the `k·t` prose error while satisfying the actual linear contract. |
| A8: long carry/borrow | Set `t=2^r` for a fixed code. The first binary decrement has an `r`-cell borrow, refuting a uniform per-tick bound but respecting the total amortized estimate. |
| A9: padded representations | Fix a machine and use every `encode M ++ true^m`. All decode to the same machine, but no law bounds or equates their canonization times or universal coefficients. This is the missing quantitative premise in finding 1. |
| A10: `f=g` | Already at `A=1`, `f(n+1)+f(n)+n+1>f(n)=g(n)`. No threshold exists, so the hypothesis correctly excludes self-separation. |
| A11: identity versus exponential | The attached witnesses support `f(n)=n`, `g(n)=2^n`; the domination sum is `3n+2` and is eventually dominated by the exponential. However `NTIME id=∅` because the bound vanishes at length zero, so this is a degenerate lower-class test, not a substantive hierarchy demonstration. The positive linear showcase avoids it. |
| A12: positive linear versus square | Here both classes have nonempty time bounds, and the domination calculation below succeeds. There is no zero-budget trivialization of the advertised showcase. |
| A13: nonmonotone bounds | The oscillating examples above and below separate the locator's missing monotonicity inference from the explicitly stronger hypothesis. They do not refute the repaired theorem statement. |

For the requested exponential domination in A11, choose `n≥max(4,3A+1)`. Induction gives `2^n≥n²` for `n≥4`, and

\[
n^2-A(3n+2)=n(n-3A)-2A\ge n-2A\ge0.
\]

**Strength, positive bounds, and showcase arithmetic**

When `f` is monotone, constructibility gives `n+1≤f(n+1)`, and hence

\[
f(n+1)
\le f(n+1)+f(n)+n+1
\le3f(n+1).
\]

Applying the book's eventual integer-multiple condition at `3A` proves the package's condition; the reverse implication is immediate. Thus the conditions are equivalent in the monotone case, without any monotonicity assumption on `g`.

Outside that case the strengthening is real. Set

\[
f(n)=\begin{cases}2^n&n\text{ even},\\n+1&n\text{ odd},\end{cases}
\qquad
g(n)=(n+1)f(n+1).
\]

These positive functions are constructible by length/parity counting, shifts, and elementary multiplication. Then

\[
\frac{f(n+1)}{g(n)}=\frac1{n+1}\longrightarrow0,
\qquad
\frac{f(n)}{g(n)}=\frac{2^n}{(n+1)(n+2)}\longrightarrow\infty
\quad(n\text{ even}).
\]

Thus the added `f(n)` condition is not “only” a change of notation for unrestricted functions. It is useful for the inclusion proof and also supplies the stage-bottom bound. This confirms the declared restriction, with the necessary source-fidelity qualification.

At zero, `TimeConstructible id` shows that constructibility does not imply positivity. If a time bound vanishes anywhere, the all-branch-halting clause makes its `NTIME` class empty; a positive bound admits at least a constant rejecting decider. Consequently the larger `g+1` class is always nonempty, and the `hpos` hypothesis is precisely what permits replacing it by `g`.

For the showcase, if `n≥3A+4`, then

\[
\begin{aligned}
(n+1)^2-A(3n+4)
&=n(n-3A)+2n+1-4A\\
&\ge6n+1-4A\\
&\ge14A+25>0.
\end{aligned}
\]

This verifies the stated threshold, including `A=0`. The two constructibility witnesses fit the actual `c(T+1)` convention: scanning/counting takes `O(n+1)` time, and grade-school multiplication on `O(log(n+2))` bits fits in `O((n+1)^2)`. At `n=0` each target value is 1 and may be emitted in constant time.

For the deterministic comparison, when `A≥1`,

\[
A(2n+2)^2=4A(n+1)^2>(n+1)^2.
\]

Thus the received quadratic-overhead hierarchy cannot be instantiated for this pair. This observation does not equate the square showcase with the book's three-halves example.

**Coverage and proposed permanent checks**

All eight numbered questions are addressed: Q1–Q3 by the definition/proof/parser checks; Q4–Q6 by the construction, clock, replay, and truncation arguments; Q7 by findings 1–2, the exact hypothesis comparison, and the stage-top check; Q8 by the positivity and arithmetic checks. All ten declared deviations were considered. Deviations 4 and 5 need corrected explanations, deviation 7 needs its monotone qualification retained, and deviation 9 is an explicitly weaker showcase.

I independently counted 185 and 278 lines in the audited modules, nine and six explicit public declarations respectively, and one plus six admissions. The supplied sweep and lint outputs have the advertised warning/error counts. I did **not** independently verify the git comparison `72718693..a664c3e4`, `.olean` freshness, the full transitive dependency graph, or rerun Lean/style lint. Existing tactic proofs were outside scope except the declared skeleton-time lemma. Numerical spot checks of the showcase threshold and borrow-count identity were supplementary; the symbolic arguments above are the evidence for those claims.

Useful permanent sanity lemmas are: `workPair` at both coordinates and injectivity; injectivity/round-trip parsing of the complete ND serialization; impossibility of initialized zero-step acceptance; acceptance-at-any-time iff acceptance-at-`T` under `HaltsWithin T`; immediate-accept and emit-then-loop deadline tests; and a padding-aware quantitative interpreter/locator invariant supporting the repaired hierarchy construction. The last item is the material closure requirement, not a suggestion to add more shallow tests.

**Glossary of notation introduced in this report.** `Cα` is an interpreter coefficient for the particular code `α`; `αᵢ` is the code used at stage `i`; `a` or `aᵢ` is a stage's first input length; `Aᵢ` is a varying coefficient used only in the quantifier counterexample; `ν₂(j)` is the number of trailing binary zeros of positive `j`; `d` is a fixed-code replay-cost constant; `s` is the length of an accepting choice word; `T` is an all-branch halting budget; `F` is the finite-absorption constant `1+Σ_{j<N}f(j)`; `R` is an arbitrary index threshold; `true^m` denotes a list of `m` true bits. All other machine, hierarchy, and stage symbols are those of the audited pack or are local quantified integers.
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


## ===== audits/evidence/ch3-p33-r2-repairs.diff =====

```
diff --git a/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean b/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean
index e97fabea..3484e461 100644
--- a/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean
+++ b/TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean
@@ -36,14 +36,21 @@ only, with facade wiring at that gate's close (the P4.2 precedent).
   step 1 says "if `M_i` has not halted in this time, then halt and accept";
   the campaign's universal instead delivers, on every budget-shaped input,
   all-branch halting within `C·(t+1)` **and** acceptance iff the coded
-  machine accepts within `t`. Under the contradiction's assumption the coded
-  machine beats the budget, so the timeout polarity never bites — the
-  packaging is a simplification, not a strengthening.
+  machine accepts within `t` — so a branch cut by the clock rejects. The
+  honest reason this is sound (round-1 finding 7 — it is **not** that every
+  coded branch finishes: the normal form guarantees no all-branch halting,
+  and its guess phase has infinite non-accepting branches even for total
+  deciders): accepting witnesses finish within the forward transfer bound,
+  every completed accepting display is sound, and the backward direction
+  uses the *original* decider's all-branch halting for truncation. Cut
+  branches reject, which can never create a false positive.
 * **Linear overhead `C·(t+1)` with `C` per code** (decision CH34-Q8): the
-  clock is fused into the interpreter loop (a countdown tick per simulated
-  step), not the deterministic `clockTM`'s re-scan — the received
-  `Turing.timed_universal` pays `C·(t+1)²` exactly there, and the quadratic
-  would surrender the book-strength hierarchy.
+  clock is fused into the interpreter loop — one countdown tick per
+  simulated step, with **amortized** linear total cost (a single decrement
+  can borrow across the whole counter width; the borrows sum to
+  `Σⱼ ν₂(j) ≤ t`, round-1 finding 5) — not the deterministic `clockTM`'s
+  re-scan: the received `Turing.timed_universal` pays `C·(t+1)²` exactly
+  there, and the quadratic would surrender the book-strength hierarchy.
 * **The domination hypothesis carries an extra `f n` addend**:
   `∀ A, A·(f(n+1) + f n + n + 1) ≤ g n` eventually. The `f(n+1)` term is the
   book's `f(n+1) = o(g(n))`; the `f n` term covers the inclusion half
@@ -99,12 +106,16 @@ corresponding table row, so `UN`'s branches at length `C·(t+1)` project onto
 the coded machine's branches at length `t` (the alignment lemma, both
 directions of the iff; deterministic bookkeeping steps ignore their bits, the
 binary-choice semantics' absorption). The clock is the budget word `bits t`
-counted **down one tick per simulated step, fused into the interpreter loop**
-— not the deterministic `clockTM` re-scan, whose `C·(t+1)²` is exactly what
-decision CH34-Q8 forbids — and every branch halts when the counter dies or
-the simulated machine halts, whichever is first. Per simulated step the cost
-is one table scan plus the tick, `O(|table|)` — a constant for fixed `α`,
-absorbed into `C`. Fill obligations, named: the startup reuse at the
+counted **down one tick per simulated step, fused into the interpreter
+loop** — not the deterministic `clockTM` re-scan, whose `C·(t+1)²` is
+exactly what decision CH34-Q8 forbids — and every branch halts when the
+counter dies or the simulated machine halts, whichever is first. The tick
+is **amortized**, not pointwise (round-1 finding 5): a decrement from `j`
+borrows across `ν₂(j)` trailing zeros, unbounded for a single tick, but
+`Σ_{j≤t} ν₂(j) ≤ t`, so a counter that maintains its significant end and
+tests zero without full-width scans has linear total cost. Per simulated
+step the remaining cost is one table scan, `O(|table|)` — a constant for
+fixed `α`, absorbed into `C`. Fill obligations, named: the startup reuse at the
 ND record format; the fused countdown; the two alignment directions; the
 halting absorption on exhausted budgets; the `C`-ledger per code. -/
 theorem exists_timed_universal_NDTM (c : EffectiveNDMachineCode) :
@@ -163,7 +174,9 @@ the simulator's finite control). Then the non-local reads are verified in
 against the real input tape, and each work tape `j` by replaying tape `j` on
 tape B — B's head tracks tape `j`'s claimed head, so each step checks the
 claimed read against B's cell and applies the claimed write at unit cost —
-rewinding A and clearing B between sweeps. Total `O_N(k · t) = C·(t+1)`.
+rewinding A and clearing B between sweeps. Total `O_N((k+1)·(t+1)) =
+C·(t+1)` — the `k+1` covers the zero-work-tape case, where the display
+guess and the input sweep remain (round-1 finding 6).
 Forward transfer: a genuine accepting run of length `t` yields the accepting
 display, guessed and verified within `C·(t+1)`. Backward: a verified display
 **is** a genuine run (the sweeps force consistency), so an accepting branch
@@ -202,37 +215,63 @@ square.
 
 **Proof sketch.** *Inclusion:* the hypothesis at `A = 1` gives
 `f n ≤ g n` eventually (the `f n` addend); finitely many lengths absorb into
-the constant (the received `Complexity.time_hierarchy` `F`-sum idiom).
-*Strictness* is lazy diagonalization [AB09, proof of Theorem 3.2 and
-Figure 3.1], over a scheme fixed by `Turing.exists_effectiveNDMachineCode`
-(the fill introduces the global scheme constant, mirroring
-`Complexity.TimeHierarchy.code`), with `UN` and `BF` its universal and
-evaluator. Fill obligations, named: **(i) the stage ladder**
-`ℓ₁ := 2`, `ℓ_{i+1} := (BF's bound at budget(ℓ_i + 1)) + ℓ_i + 1`, and its
-locator machine finding the sandwich `ℓ_i < n ≤ ℓ_{i+1}` within `O(g n)`
-(iterated `f`-witness runs and doubling counters — the book's `O(n^{1.5})`
-locating step); **(ii) the diagonal NDTM `D`**: on `1^n` with
-`ℓ_i < n < ℓ_{i+1}`, run `UN` on the virtual input
-`⟨bits (budget n), α_i, 1^{n+1}⟩` — `α_i` the `i`-th binary string
-(unranking), `budget` computed from `g`'s constructibility witness — and
-answer `UN`'s verdict; on `1^{ℓ_{i+1}}`, run `BF` at the stage bottom
-`⟨bits (budget (ℓ_i + 1)), α_i, 1^{ℓ_i + 1}⟩` and **flip**; reject non-unary
-inputs; **(iii) `D ∈ NTIME (g + 1)`**: `UN`'s unconditional all-branch clock,
-`BF`'s determinism with its bound at most `ℓ_{i+1} ≤ n ≤ g n` by the ladder's
-very definition and constructibility's floor `n ≤ g n`, and the locator
-ledger; **(iv) `L(D) ∉ NTIME f`**: given `N` deciding `L(D)` within
-`c₀ · f`, take `M'` and `C₁` from
-`Turing.FinNDTM.exists_codeNDTM_accepts_linear N`, and by true-padding
-(`Turing.NDMachineCode.decode_encode_pad`) pick `i` arbitrarily large with
-`decode α_i = M'` and `C₁·(c₀·f(n+1) + 1) ≤ budget n` on the whole stage
-(the domination hypothesis at the assembled constant — the `f(n+1)` and
-`n + 1` addends); then mid-rung `D(1^n) = [M' accepts 1^{n+1} within budget]`
-equals `[1^{n+1} ∈ L(D)]` — forward by the linear transfer and
-`Turing.FinNDTM.AcceptsWithin.mono`, backward by the unbounded transfer plus
-the truncation of `N`'s accepting word at `N`'s own all-branch budget
-(`Turing.NDTM.runWith_of_halt`) — which is the chain (3.3), while the top
-rung flips the stage bottom, (3.4); `N` agreeing with `D` on the whole stage
-collapses the chain into the contradiction of [AB09, Figure 3.1]. -/
+the constant (the received `Complexity.time_hierarchy` `F`-sum idiom; no
+monotonicity needed). *Strictness* is lazy diagonalization [AB09, proof of
+Theorem 3.2 and Figure 3.1], over a scheme fixed by
+`Turing.exists_effectiveNDMachineCode`, rebuilt per the round-1 audit (its
+two majors: a per-code universal constant cannot be absorbed by choosing a
+padded large index — padding preserves `decode`, no law preserves cost —
+and the stage locator must be computable within the allowance). The
+repaired construction: **(i) the fixed-code stage schedule**: stage
+`i = pair(j, r)` runs the `j`-th binary string `α_j` (unranking), so every
+code recurs at infinitely many stages — no padded-index selection, and the
+alleged decider's constants stay fixed along its own stage subsequence (the
+same discipline as the P3.2 enumeration's repetition coordinate).
+**(ii) the `f`-adaptive ladder with capped comparisons**: with
+`a := ℓ_i + 1` the stage bottom, `T*_i := (f a + a + 1)²` and
+`ℓ_{i+1} := 2^{(T*_i)²}` — an explicit recurrence over `f`'s
+constructibility witness; the locator compares `n` against `ℓ_{i+1}` by
+**bit-length arithmetic with capped witness runs** (the ladder value is
+never materialized in unary, and a capped run that fails to finish itself
+decides the comparison: an unfinished `f`-witness already certifies
+`ℓ_{i+1} > n`), with the completed stages' costs summing geometrically and
+the one incomplete evaluation capped — total `O(g n + 1)` after computing
+`g n` once by `g`'s witness. **(iii) the self-clocked mid-rung**: for
+`ℓ_i < n < ℓ_{i+1}`, `D` runs the fixed interpreter core on the virtual
+input `⟨α_j, 1^{n+1}⟩` at nominal simulated budget `g n`, under `D`'s
+**own fused countdown of `K·(g n + 1)` steps** — `K` fixed by `D`'s
+architecture, independent of the code — passing its choice bits through;
+branches cut by the countdown **reject** (sound: a cut branch is
+non-accepting, and completed accepting simulations are sound).
+**(iv) the top rung**: at `n = ℓ_{i+1}`, `D` runs `BF` on
+`⟨bits T*_i, α_j, 1^{a}⟩` under the same self-cap and **flips** a completed
+verdict (default answer if the cap trips); non-unary inputs reject.
+`D ∈ NTIME (g + 1)` **by construction**: every phase is cut by the
+`K·(g n + 1)` countdown, uniformly in the code. *The chain, for the alleged
+decider:* given `N` deciding `L(D)` within `c₀ · f`, take `M'` and `C₁`
+from `Turing.FinNDTM.exists_codeNDTM_accepts_linear N` and let `α` be
+`M'`'s code with its **fixed** interpreter constant `C_α`. Mid-rung, at the
+late stages of `α`'s subsequence: the genuine simulation of an accepting
+`N`-branch costs at most `C_α·(C₁·(c₀·f(n+1) + 1) + 1) ≤ A*·(f(n+1) + 1)`
+host steps with `A* := C_α·(C₁·c₀ + C₁ + 1) + 1` **fixed**, which the
+domination hypothesis (its `f(n+1)` addend) puts below `K·(g n + 1)`
+eventually — so the countdown never cuts the relevant branches, and
+`D(1^n) = [M'` accepts `1^{n+1}` within the window`] = [1^{n+1} ∈ L(D)]`
+(forward by the linear transfer and `AcceptsWithin.mono`; backward by the
+unbounded transfer plus truncation at `N`'s own all-branch budget,
+`Turing.NDTM.runWith_of_halt`) — the chain (3.3). Top rung: the flip needs
+the transfer at the **bottom** length `a` — the hypothesis's `f n` addend,
+instantiated at `n = a` — with `T*_i = (f a + a + 1)² ≥ C₁·(c₀·f a + 1)`
+eventually (fixed constants against a square), and `BF`'s cost
+`C_BF·2^{C_BF·(T*_i + 1)} ≤ K·(g n + 1)` eventually along the subsequence
+since `g n ≥ n = 2^{(T*_i)²}` — the ladder's square in the exponent
+outruns any fixed linear exponent — which is the chain's (3.4); `N`
+agreeing with `D` on the whole stage collapses (3.3) into (3.4)'s flip,
+the contradiction of [AB09, Figure 3.1]. Fill obligations, named: the
+schedule and unranking; the ladder recurrence and the capped-comparison
+locator with its amortized ledger; the self-clocked interpreter core at
+fixed `K`; the two transfer instantiations (at `f(n+1)` mid-rung, at `f a`
+bottom); the chain induction. -/
 theorem ntime_hierarchy {f g : ℕ → ℕ} (hf : TimeConstructible f)
     (hg : TimeConstructible g)
     (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
@@ -259,7 +298,8 @@ instance `NTIME(n) ⊊ NTIME(n^{1.5})` (fractional exponents have no ℕ-valued
 normal form in the campaign; the square is the nearest constructible bound).
 This is exactly what decision CH34-Q8 buys: under the received
 **deterministic** hierarchy's quadratic overhead, `A·(2n + 2)² ≤ (n + 1)²`
-fails for every `A`, so no square-overhead route separates these two classes
+fails for every **positive** `A` (round-1 finding 9; `A = 0` holds
+vacuously), so no square-overhead route separates these two classes
 — the linear-overhead universal is load-bearing.
 
 **Proof sketch.** `Complexity.ntime_hierarchy_of_pos` at `f := n + 1`,
diff --git a/TCSlib/Complexity/TuringMachine/NDCodes.lean b/TCSlib/Complexity/TuringMachine/NDCodes.lean
index 30e5c303..1f936e0b 100644
--- a/TCSlib/Complexity/TuringMachine/NDCodes.lean
+++ b/TCSlib/Complexity/TuringMachine/NDCodes.lean
@@ -171,12 +171,17 @@ format: `encode := CodeNDTM.serialize` itself; `decode` parses the
 `Turing.pairEncode`d state count, the initial state, and the two transition
 tables by the received parser architecture
 (`TCSlib.Complexity.TuringMachine.CodeParser`, retargeted to the
-`Turing.actionBits₂` record — the table is `2 · 9` records per state in the
-fixed enumeration order), with the single-state do-nothing machine as the
-fallback on parse failure and trailing `true`-padding tolerated by the
-end-marker discipline (property 2); the canonizer re-serializes the parsed
-record within a polynomial of the code length (the received parser/emitter
-time ledgers). Fill obligations, named: the record parser and its fallback
+`Turing.actionBits₂` record — the table is `2 · 27 = 54` records per state
+in the fixed enumeration order, two choices by three reads on each of the
+input and both work tapes; round-1 finding 3 corrected the earlier `2 · 9`
+miscount, and the parser's minimum-length guard scales accordingly), with
+the single-state do-nothing machine as the fallback on parse failure and
+trailing `true`-padding tolerated by the end-marker discipline
+(property 2); the canonizer re-serializes the parsed record by the
+**arbitrary-time computability route of the received construction** — the
+deterministic `MathlibBridge` explicitly supersedes its polynomial variant,
+and `canonizerTime` is an arbitrary bound, so no polynomial ND canonizer is
+claimed or needed by this phase's consumers (round-1 finding 4). Fill obligations, named: the record parser and its fallback
 totalization; the pad-tolerance lemma (`decode_encode_pad`); the canonizer
 assembly and its time bound. -/
 theorem exists_effectiveNDMachineCode : Nonempty EffectiveNDMachineCode := by
```


## ===== TCSlib/Complexity/TuringMachine/NDCodes.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Nondeterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Codes for nondeterministic machines

The nondeterministic counterpart of `TCSlib.Complexity.TuringMachine.Encoding`'s
code layer ([AB09, §1.4], extended to NDTMs as [AB09, §3.2] requires for the
nondeterministic time hierarchy): a coded normal form `Turing.CodeNDTM`, its
fixed scheme-independent serialization, the representation-scheme laws
(`Turing.NDMachineCode`), and the effective form with a canonizer
(`Turing.EffectiveNDMachineCode`). Phase P3.3 of
`AroraBarakChapters3-4Plan.md`; the consumers — the clocked universal NDTM of
[AB09, Exercise 2.6] at linear overhead (decision CH34-Q8) and the lazy
diagonalization of [AB09, Theorem 3.2] — are
`TCSlib.Complexity.Diagonalization.NTimeHierarchy`.

**Status: statement skeleton (phase P3.3).** Definitions are real; the scheme
existence is sorried with a sketch; `Turing.NDMachineCode.decode_encode` is a
skeleton-time proof mirroring the proved `Turing.MachineCode.decode_encode`
(declared for the audit, the `runWith`-algebra precedent).

## Design

* **The coded normal form has two work tapes** (`NDTM 2 Bool`), not one: the
  deterministic `Turing.CodeTM` is one-work-tape because the chapter-1
  robustness conversion eats a quadratic slowdown anyway, but phase P3.3's
  whole point (decision CH34-Q8) is **linear** overhead, and the
  guess-then-verify tape reduction ([BGW70]-style, stated as
  `Turing.FinNDTM.exists_codeNDTM_accepts_linear` in the consumer module)
  delivers linear overhead into **two** work tapes — one for the guessed
  display sequence, one replaying the verified tape — while the one-work-tape
  target is not known to suffice at linear cost.
* **The serialization mirrors `Turing.CodeTM.serialize` record for record**:
  the same `signBits`/`optOptBoolBits`/`optBoolBits`/`optStateBits` fields,
  with a second work-tape record per action (`Turing.actionBits₂`) and the
  table enumerated over the choice bit first (`false` then `true`), then
  states in `Fin` order, then the input read and the two work reads each over
  `none`, `some false`, `some true`.
* **The scheme laws are verbatim mirrors**: total decoding (property 1),
  recovery under arbitrary `true`-padding (property 2 — infinitely many
  representations, which [AB09, Theorem 3.2]'s proof uses to pick a large
  index), and the canonizer tying `decode` to effective semantics (the
  chapter-1 audit's Argument-A exclusion, inherited by construction).

## Main definitions

* `Turing.CodeNDTM`, `Turing.CodeNDTM.toFinNDTM` — the coded two-work-tape
  normal form. [AB09, §1.4, §3.2]
* `Turing.actionBits₂`, `Turing.CodeNDTM.serialize` — the fixed serialization.
* `Turing.NDMachineCode`, `Turing.EffectiveNDMachineCode` — the scheme laws
  and the effective scheme. [AB09, §1.4]

## Main results

* `Turing.NDMachineCode.decode_encode` — decoding recovers the machine
  (skeleton-time proof, mirror of `Turing.MachineCode.decode_encode`).
* `Turing.exists_effectiveNDMachineCode` — an effective scheme exists
  (sorried; phase-P3.3 statement).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, §2.1.2, Exercise 2.6; §3.2.)
* [BGW70] R. Book, S. Greibach, B. Wegbreit, *Time- and tape-bounded Turing
  acceptors and AFLs*, JCSS 4(6), 1970. (Cited through [AB09]; no external
  text is required for this audit.)
-/

namespace Turing

/-- The coded normal form of a nondeterministic machine: a binary-alphabet
NDTM with **two** work tapes and state space `Fin (numStates + 1)` (never
empty). Two work tapes, not one, because the guess-then-verify tape reduction
achieves linear overhead into two tapes (see the module docstring). Mirrors
`Turing.CodeTM`. [AB09, §1.4, §3.2] -/
structure CodeNDTM where
  /-- one less than the number of states (so the state space is never empty) -/
  numStates : ℕ
  /-- the underlying two-work-tape nondeterministic machine -/
  tm : NDTM 2 Bool (Fin (numStates + 1))

/-- The bundled machine of a coded nondeterministic machine. -/
def CodeNDTM.toFinNDTM (M : CodeNDTM) : FinNDTM Bool where
  k := 2
  State := Fin (M.numStates + 1)
  tm := M.tm

/-- The work-symbol function reading `w₀` on tape `0` and `w₁` on tape `1`,
for the fixed table enumeration of `Turing.CodeNDTM.serialize`. -/
def workPair (w₀ w₁ : Option Bool) : Fin 2 → Option Bool :=
  fun j => if j = 0 then w₀ else w₁

/-- Serialization of one two-work-tape transition record: the input-head move,
then each work tape's optional write and move in tape order, then the emission
and the successor state — `Turing.actionBits` with a second work-tape record. -/
def actionBits₂ {n : ℕ} (a : Action 2 Bool (Fin (n + 1))) : List Bool :=
  signBits a.inputTape ++
    optOptBoolBits (a.workTapes 0).1 ++ signBits (a.workTapes 0).2 ++
    optOptBoolBits (a.workTapes 1).1 ++ signBits (a.workTapes 1).2 ++
    optBoolBits a.output ++ optStateBits a.state

/-- The **fixed, scheme-independent** canonical serialization of a coded
nondeterministic machine, mirroring `Turing.CodeTM.serialize`: the state count,
the initial state, then the full two-table transition list in the fixed
enumeration order — the choice bit (`false` then `true`) outermost, then
states in `Fin` order, then the input read and the two work reads each over
`none`, `some false`, `some true`. This is the target format of
`Turing.EffectiveNDMachineCode.canonizer`. -/
def CodeNDTM.serialize (M : CodeNDTM) : List Bool :=
  pairEncode (Nat.bits M.numStates)
    (unaryFin M.tm.q₀ ++
      ([false, true] : List Bool).flatMap fun b =>
        (List.finRange (M.numStates + 1)).flatMap fun q =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
            ([none, some false, some true] : List (Option Bool)).flatMap fun w₀ =>
              ([none, some false, some true] : List (Option Bool)).flatMap fun w₁ =>
                actionBits₂ (M.tm.tr b q inp (workPair w₀ w₁)))

/-- The algebraic laws of a representation scheme for coded nondeterministic
machines, mirroring `Turing.MachineCode` [AB09, §1.4]: a total decoding
(property 1), an encoding, and recovery under arbitrary `true`-padding
(property 2 — every machine has infinitely many representations, which the
lazy diagonalization of [AB09, Theorem 3.2] uses to pick large indices). -/
structure NDMachineCode where
  /-- encode a machine as a binary string, `⌞N⌟` -/
  encode : CodeNDTM → List Bool
  /-- decode any binary string to a machine (total by type: property 1) -/
  decode : List Bool → CodeNDTM
  /-- a code followed by any amount of `true`-padding decodes to the machine
  (property 2: infinitely many representations) -/
  decode_encode_pad : ∀ M m, decode (encode M ++ List.replicate m true) = M

/-- Decoding a code recovers the machine ([AB09, §1.4]; padding by zero
symbols). Skeleton-time proof, mirroring `Turing.MachineCode.decode_encode`. -/
theorem NDMachineCode.decode_encode (c : NDMachineCode) (M : CodeNDTM) :
    c.decode (c.encode M) = M := by
  simpa using c.decode_encode_pad M 0

/-- An *effective* representation scheme for nondeterministic machines: the
algebraic laws together with a (deterministic) machine of this development
computing the fixed serialization of the decoded machine — the mirror of
`Turing.EffectiveMachineCode`, with the same Argument-A rationale: the target
`Turing.CodeNDTM.serialize` is scheme-independent, so a scheme whose `decode`
has noncomputable meaning admits no canonizer. -/
structure EffectiveNDMachineCode extends NDMachineCode where
  /-- a machine computing the fixed serialization of the decoded machine -/
  canonizer : FinTM Bool
  /-- the canonizer's time bound (arbitrary here; universal-machine constants
  absorb its value at each fixed code) -/
  canonizerTime : ℕ → ℕ
  /-- the canonizer computes `serialize ∘ decode` -/
  canonizer_computes :
    canonizer.ComputesFunInTime (fun α => (decode α).serialize) canonizerTime

/-- **An effective nondeterministic code scheme exists** (spec, fill pending —
phase P3.3): the mirror of `Turing.exists_effectiveMachineCode`.

**Proof sketch.** Mirror the deterministic construction
(`TCSlib.Complexity.TuringMachine.MathlibBridge`) over the extended record
format: `encode := CodeNDTM.serialize` itself; `decode` parses the
`Turing.pairEncode`d state count, the initial state, and the two transition
tables by the received parser architecture
(`TCSlib.Complexity.TuringMachine.CodeParser`, retargeted to the
`Turing.actionBits₂` record — the table is `2 · 27 = 54` records per state
in the fixed enumeration order, two choices by three reads on each of the
input and both work tapes; round-1 finding 3 corrected the earlier `2 · 9`
miscount, and the parser's minimum-length guard scales accordingly), with
the single-state do-nothing machine as the fallback on parse failure and
trailing `true`-padding tolerated by the end-marker discipline
(property 2); the canonizer re-serializes the parsed record by the
**arbitrary-time computability route of the received construction** — the
deterministic `MathlibBridge` explicitly supersedes its polynomial variant,
and `canonizerTime` is an arbitrary bound, so no polynomial ND canonizer is
claimed or needed by this phase's consumers (round-1 finding 4). Fill obligations, named: the record parser and its fallback
totalization; the pad-tolerance lemma (`decode_encode_pad`); the canonizer
assembly and its time bound. -/
theorem exists_effectiveNDMachineCode : Nonempty EffectiveNDMachineCode := by
  sorry

end Turing
```


## ===== TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassP.TimeConstructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic time hierarchy theorem

[AB09, §3.2, Theorem 3.2] ([Coo72]): for time-constructible `f` and `g` with
`f(n+1) = o(g(n))`, `NTIME(f) ⊊ NTIME(g)` — by **lazy diagonalization**, since
a nondeterministic machine cannot flip its own answer directly. The tools are
the clocked universal NDTM of [AB09, Exercise 2.6] at **linear overhead**
(decision CH34-Q8: the strongest form possible, and exactly what puts the
theorem at book strength), the trivial exponential-time deterministic
evaluation of nondeterministic acceptance (the flip at each stage top), and
the linear-overhead coded normal form ([BGW70]-style guess-then-verify).
Phase P3.3 of `AroraBarakChapters3-4Plan.md`, over the code layer of
`TCSlib.Complexity.TuringMachine.NDCodes`.

**Status: statement skeleton (phase P3.3).** Every contract is sorried with a
sketch naming its fill obligations. The `Diagonalization.lean` facade is
frozen under the live P3.2 gate; this module is wired through the root import
only, with facade wiring at that gate's close (the P4.2 precedent).

## Design (declared deviations, each for the audit)

* **The universal is iff-packaged with an unconditional clock.** [AB09]'s
  step 1 says "if `M_i` has not halted in this time, then halt and accept";
  the campaign's universal instead delivers, on every budget-shaped input,
  all-branch halting within `C·(t+1)` **and** acceptance iff the coded
  machine accepts within `t` — so a branch cut by the clock rejects. The
  honest reason this is sound (round-1 finding 7 — it is **not** that every
  coded branch finishes: the normal form guarantees no all-branch halting,
  and its guess phase has infinite non-accepting branches even for total
  deciders): accepting witnesses finish within the forward transfer bound,
  every completed accepting display is sound, and the backward direction
  uses the *original* decider's all-branch halting for truncation. Cut
  branches reject, which can never create a false positive.
* **Linear overhead `C·(t+1)` with `C` per code** (decision CH34-Q8): the
  clock is fused into the interpreter loop — one countdown tick per
  simulated step, with **amortized** linear total cost (a single decrement
  can borrow across the whole counter width; the borrows sum to
  `Σⱼ ν₂(j) ≤ t`, round-1 finding 5) — not the deterministic `clockTM`'s
  re-scan: the received `Turing.timed_universal` pays `C·(t+1)²` exactly
  there, and the quadratic would surrender the book-strength hierarchy.
* **The domination hypothesis carries an extra `f n` addend**:
  `∀ A, A·(f(n+1) + f n + n + 1) ≤ g n` eventually. The `f(n+1)` term is the
  book's `f(n+1) = o(g(n))`; the `f n` term covers the inclusion half
  `NTIME f ⊆ NTIME (g+1)` without assuming `f` monotone (the book reads it
  off `f(n+1) = o(g)` implicitly); the `n + 1` term covers linear
  startup/virtual-input costs. For monotone `f` the extra addend is absorbed,
  so no strength is lost against [AB09].
* **The larger class is `NTIME (g + 1)`**, as in the received deterministic
  `Complexity.time_hierarchy`; the positive-bound form recovers `NTIME g`.

## Main results (all sorried; phase-P3.3 statements)

* `Turing.exists_timed_universal_NDTM` — [AB09, Exercise 2.6] at linear
  overhead (CH34-Q8).
* `Turing.exists_ndAcceptsWithin_decider` — the exponential deterministic
  evaluation ("this trivial exponential simulation … does suffice").
* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded
  normal form ([BGW70]-style).
* `Complexity.ntime_hierarchy`, `Complexity.ntime_hierarchy_of_pos` —
  [AB09, Theorem 3.2].
* `Complexity.NTIME_linear_ssubset_square` — the ℕ-rendered showcase
  instance (the book displays `NTIME(n) ⊊ NTIME(n^{1.5})`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2, Theorem 3.2, Figure 3.1,
  Exercise 2.6.)
* [Coo72] S. Cook, *A hierarchy for nondeterministic time complexity*,
  STOC 1972. (Cited through [AB09]; no external text is required.)
* [BGW70] R. Book, S. Greibach, B. Wegbreit, *Time- and tape-bounded Turing
  acceptors and AFLs*, JCSS 4(6), 1970. (Cited through [AB09]; likewise.)
-/

namespace Turing

/-- **The clocked universal NDTM at linear overhead** ([AB09, Exercise 2.6];
decision CH34-Q8; spec, fill pending — phase P3.3): for every effective
nondeterministic scheme there is a universal NDTM `UN` such that for every
code `α` there is a constant `C` with, on input `⟨⟨bits t, α⟩, x⟩`: every
branch of `UN` halts within `C·(t+1)` steps, and `UN` accepts within
`C·(t+1)` iff the coded machine accepts `x` within `t`.

**Proof sketch.** Direct interpretation, not guess-then-verify: the coded
normal form has two work tapes (`Turing.CodeNDTM`), so `UN` maintains both
simulated tapes on two dedicated real tapes, holds the canonized table
(`Turing.EffectiveNDMachineCode.canonizer`) on a third, reads `x` in place by
the received virtual-input startup discipline
(`TCSlib.Complexity.TuringMachine.UniversalStartup` — no copying, so the
budget need not dominate `|x|`), and **passes its own choice bits through**:
at each simulated step boundary `UN` consumes one choice bit and applies the
corresponding table row, so `UN`'s branches at length `C·(t+1)` project onto
the coded machine's branches at length `t` (the alignment lemma, both
directions of the iff; deterministic bookkeeping steps ignore their bits, the
binary-choice semantics' absorption). The clock is the budget word `bits t`
counted **down one tick per simulated step, fused into the interpreter
loop** — not the deterministic `clockTM` re-scan, whose `C·(t+1)²` is
exactly what decision CH34-Q8 forbids — and every branch halts when the
counter dies or the simulated machine halts, whichever is first. The tick
is **amortized**, not pointwise (round-1 finding 5): a decrement from `j`
borrows across `ν₂(j)` trailing zeros, unbounded for a single tick, but
`Σ_{j≤t} ν₂(j) ≤ t`, so a counter that maintains its significant end and
tests zero without full-width scans has linear total cost. Per simulated
step the remaining cost is one table scan, `O(|table|)` — a constant for
fixed `α`, absorbed into `C`. Fill obligations, named: the startup reuse at the
ND record format; the fused countdown; the two alignment directions; the
halting absorption on exhausted budgets; the `C`-ledger per code. -/
theorem exists_timed_universal_NDTM (c : EffectiveNDMachineCode) :
    ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t) := by
  sorry

/-- **Nondeterministic acceptance evaluates deterministically in exponential
time** ([AB09, §3.2: "this trivial exponential simulation … does suffice to
establish a hierarchy theorem"]; spec, fill pending — phase P3.3): a
deterministic machine decides, on input `⟨⟨bits t, α⟩, x⟩`, whether the coded
machine accepts `x` within `t`, in time `C · 2^{C·(t+1)}`. This is the flip
at each stage top of the lazy diagonalization — the only place the answer is
ever negated.

**Proof sketch.** Enumerate the `2^t` choice words on a binary counter tape
in lexicographic order (`incrementTM` discipline); replay each word through
the deterministic core of `Turing.exists_timed_universal_NDTM`'s interpreter
— choices read from the counter instead of guessed — at cost `C_α·(t+1)` per
replay (virtual input, no copying), clearing the two simulated tapes between
replays (`O(t)` each); emit `[true]` on the first accepting replay, `[false]`
after the last. Ledger: `2^t · O_α(t+1) + 2^t` increments `≤ C·2^{C·(t+1)}`.
Fill obligations, named: the counter-driven replay loop (a §12 loop/catalog
consumer); the inter-replay cleanup; the first-accept/last-reject control;
the exponent arithmetic. -/
theorem exists_ndAcceptsWithin_decider (c : EffectiveNDMachineCode) :
    ∃ BF : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      ((c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (C * 2 ^ (C * (t + 1)))) ∧
      (¬(c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (C * 2 ^ (C * (t + 1)))) := by
  sorry

namespace FinNDTM

/-- **The linear-overhead coded normal form** ([BGW70]-style guess-then-verify,
cited through [AB09, §3.2]; spec, fill pending — phase P3.3): every
nondeterministic machine has a coded (two-work-tape) equivalent whose
acceptance tracks the original's at linear time overhead — forward with the
explicit constant, backward in unbounded form (the consumer recovers the
budgeted form from the original's all-branch halting by the truncation
argument, `Turing.NDTM.runWith_of_halt`).

**Proof sketch.** Guess-then-verify, the reason codes carry **two** work
tapes: on tape A the simulator guesses, left to right and one choice bit per
guessed bit, the full display sequence of a `k`-tape run of `N` — per step
the choice bit, the state, the `k + 1` scanned symbols, and the action record
(`O_N(1)` cells per step) — checking the **control-local** part on the fly
(each record must follow from its predecessor by `N`'s table, hardwired in
the simulator's finite control). Then the non-local reads are verified in
`k + 1` sweeps: the input claims by replaying the claimed input-head moves
against the real input tape, and each work tape `j` by replaying tape `j` on
tape B — B's head tracks tape `j`'s claimed head, so each step checks the
claimed read against B's cell and applies the claimed write at unit cost —
rewinding A and clearing B between sweeps. Total `O_N((k+1)·(t+1)) =
C·(t+1)` — the `k+1` covers the zero-work-tape case, where the display
guess and the input sweep remain (round-1 finding 6).
Forward transfer: a genuine accepting run of length `t` yields the accepting
display, guessed and verified within `C·(t+1)`. Backward: a verified display
**is** a genuine run (the sweeps force consistency), so an accepting branch
of the simulator exhibits an accepting branch of `N` at some length —
unbounded on purpose: runaway guessing branches never accept, and no
all-branch-halting claim is made for the simulator. State-space finiteness
packages as `Fin` by the received relabeling
(`Turing.MultiTapeTM.relabelState`, the `exists_codeTM` precedent). Fill
obligations, named: the display format and its on-the-fly control check; the
`k + 1` verification sweeps; the two transfer directions; the relabeling
packaging. -/
theorem exists_codeNDTM_accepts_linear (N : FinNDTM Bool) :
    ∃ (M : CodeNDTM) (C : ℕ),
      (∀ (x : List Bool) (t : ℕ),
        N.AcceptsWithin x t → M.toFinNDTM.AcceptsWithin x (C * (t + 1))) ∧
      (∀ (x : List Bool) (t : ℕ),
        M.toFinNDTM.AcceptsWithin x t → ∃ t', N.AcceptsWithin x t') := by
  sorry

end FinNDTM

end Turing

namespace Complexity

open Turing

/-- **The nondeterministic time hierarchy theorem** ([AB09, Theorem 3.2];
[Coo72]; spec, fill pending — phase P3.3, **the phase summit**): for
time-constructible `f` and `g`, if every constant multiple of
`f(n+1) + f(n) + n + 1` is eventually below `g(n)` — the book's
`f(n+1) = o(g(n))` with the two declared addends (module docstring) — then
`NTIME f ⊊ NTIME (g + 1)`. Book strength: the overhead on `f` is **linear**
(decision CH34-Q8), in contrast to the received deterministic hierarchy's
square.

**Proof sketch.** *Inclusion:* the hypothesis at `A = 1` gives
`f n ≤ g n` eventually (the `f n` addend); finitely many lengths absorb into
the constant (the received `Complexity.time_hierarchy` `F`-sum idiom; no
monotonicity needed). *Strictness* is lazy diagonalization [AB09, proof of
Theorem 3.2 and Figure 3.1], over a scheme fixed by
`Turing.exists_effectiveNDMachineCode`, rebuilt per the round-1 audit (its
two majors: a per-code universal constant cannot be absorbed by choosing a
padded large index — padding preserves `decode`, no law preserves cost —
and the stage locator must be computable within the allowance). The
repaired construction: **(i) the fixed-code stage schedule**: stage
`i = pair(j, r)` runs the `j`-th binary string `α_j` (unranking), so every
code recurs at infinitely many stages — no padded-index selection, and the
alleged decider's constants stay fixed along its own stage subsequence (the
same discipline as the P3.2 enumeration's repetition coordinate).
**(ii) the `f`-adaptive ladder with capped comparisons**: with
`a := ℓ_i + 1` the stage bottom, `T*_i := (f a + a + 1)²` and
`ℓ_{i+1} := 2^{(T*_i)²}` — an explicit recurrence over `f`'s
constructibility witness; the locator compares `n` against `ℓ_{i+1}` by
**bit-length arithmetic with capped witness runs** (the ladder value is
never materialized in unary, and a capped run that fails to finish itself
decides the comparison: an unfinished `f`-witness already certifies
`ℓ_{i+1} > n`), with the completed stages' costs summing geometrically and
the one incomplete evaluation capped — total `O(g n + 1)` after computing
`g n` once by `g`'s witness. **(iii) the self-clocked mid-rung**: for
`ℓ_i < n < ℓ_{i+1}`, `D` runs the fixed interpreter core on the virtual
input `⟨α_j, 1^{n+1}⟩` at nominal simulated budget `g n`, under `D`'s
**own fused countdown of `K·(g n + 1)` steps** — `K` fixed by `D`'s
architecture, independent of the code — passing its choice bits through;
branches cut by the countdown **reject** (sound: a cut branch is
non-accepting, and completed accepting simulations are sound).
**(iv) the top rung**: at `n = ℓ_{i+1}`, `D` runs `BF` on
`⟨bits T*_i, α_j, 1^{a}⟩` under the same self-cap and **flips** a completed
verdict (default answer if the cap trips); non-unary inputs reject.
`D ∈ NTIME (g + 1)` **by construction**: every phase is cut by the
`K·(g n + 1)` countdown, uniformly in the code. *The chain, for the alleged
decider:* given `N` deciding `L(D)` within `c₀ · f`, take `M'` and `C₁`
from `Turing.FinNDTM.exists_codeNDTM_accepts_linear N` and let `α` be
`M'`'s code with its **fixed** interpreter constant `C_α`. Mid-rung, at the
late stages of `α`'s subsequence: the genuine simulation of an accepting
`N`-branch costs at most `C_α·(C₁·(c₀·f(n+1) + 1) + 1) ≤ A*·(f(n+1) + 1)`
host steps with `A* := C_α·(C₁·c₀ + C₁ + 1) + 1` **fixed**, which the
domination hypothesis (its `f(n+1)` addend) puts below `K·(g n + 1)`
eventually — so the countdown never cuts the relevant branches, and
`D(1^n) = [M'` accepts `1^{n+1}` within the window`] = [1^{n+1} ∈ L(D)]`
(forward by the linear transfer and `AcceptsWithin.mono`; backward by the
unbounded transfer plus truncation at `N`'s own all-branch budget,
`Turing.NDTM.runWith_of_halt`) — the chain (3.3). Top rung: the flip needs
the transfer at the **bottom** length `a` — the hypothesis's `f n` addend,
instantiated at `n = a` — with `T*_i = (f a + a + 1)² ≥ C₁·(c₀·f a + 1)`
eventually (fixed constants against a square), and `BF`'s cost
`C_BF·2^{C_BF·(T*_i + 1)} ≤ K·(g n + 1)` eventually along the subsequence
since `g n ≥ n = 2^{(T*_i)²}` — the ladder's square in the exponent
outruns any fixed linear exponent — which is the chain's (3.4); `N`
agreeing with `D` on the whole stage collapses (3.3) into (3.4)'s flip,
the contradiction of [AB09, Figure 3.1]. Fill obligations, named: the
schedule and unranking; the ladder recurrence and the capped-comparison
locator with its amortized ledger; the self-clocked interpreter core at
fixed `K`; the two transfer instantiations (at `f(n+1)` mid-rung, at `f a`
bottom); the chain induction. -/
theorem ntime_hierarchy {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME (fun n => g n + 1) := by
  sorry

/-- **The nondeterministic time hierarchy for a positive bound**
([AB09, Theorem 3.2]; spec, fill pending): as `Complexity.ntime_hierarchy`,
with the larger class exactly `NTIME g` when `g` never vanishes — mirroring
`Complexity.time_hierarchy_of_pos`.

**Proof sketch.** `c·(g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so
`NTIME (g + 1) ⊆ NTIME g`; the reverse is `Complexity.NTIME.mono`; conclude
from `Complexity.ntime_hierarchy`. -/
theorem ntime_hierarchy_of_pos {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME g := by
  sorry

/-- **The showcase separation** (spec, fill pending — phase P3.3):
`NTIME(n + 1) ⊊ NTIME((n + 1)²)`, the ℕ-rendering of the book's displayed
instance `NTIME(n) ⊊ NTIME(n^{1.5})` (fractional exponents have no ℕ-valued
normal form in the campaign; the square is the nearest constructible bound).
This is exactly what decision CH34-Q8 buys: under the received
**deterministic** hierarchy's quadratic overhead, `A·(2n + 2)² ≤ (n + 1)²`
fails for every **positive** `A` (round-1 finding 9; `A = 0` holds
vacuously), so no square-overhead route separates these two classes
— the linear-overhead universal is load-bearing.

**Proof sketch.** `Complexity.ntime_hierarchy_of_pos` at `f := n + 1`,
`g := (n + 1)²`: positivity is immediate; domination is
`A·((n + 2) + (n + 1) + n + 1) = A·(3n + 4) ≤ (n + 1)²` for `n ≥ 3A + 4`.
Fill obligations, named: the two constructibility witnesses —
`TimeConstructible (n + 1)` (dominance `n ≤ n + 1`; an input-scan counter
emitting `bits (n + 1)`, the `Complexity.timeConstructible_id` idiom) and
`TimeConstructible ((n + 1)²)` (dominance `n ≤ (n + 1)²`; the grade-school
square of the scanned length within `O((n + 1)²)` steps — a §12
catalog/counter consumer). -/
theorem NTIME_linear_ssubset_square :
    NTIME (fun n => n + 1) ⊂ NTIME (fun n => (n + 1) ^ 2) := by
  sorry

end Complexity
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


## ===== TCSlib/Complexity/TuringMachine/Universal.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.UniversalBlock
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The universal Turing machine

[AB09, §1.4.1 and Theorem 1.9, relaxed form]: there is a single machine `U` that,
given a code and an input, simulates the machine the code denotes — `U(x, α) =
M_α(x)` — with the simulation overhead depending only on the code, not on the input.

The construction lives in `UniversalStartup.lean` (prefix parsing,
canonization, and table capture), `UniversalInterpreter.lean` (the four-tape
table interpreter and the block-simulation assembly), and `UniversalBlock.lean`
(the live table block and the checkpoint relation), split out mechanically at
the epoch-3→4 merge. This file holds the three public statements together with
the epoch-4 private layer proving `timed_universal` (the deadline interpreter
`timedUniversalTM` and its lemmas; epoch-4 audit, finding 3: this sentence
previously claimed the file held only the public statements).

## Design and deviations from [AB09] (all shaped by the phase-3 audit)

* Statements are relative to an `Turing.EffectiveMachineCode`: the purely algebraic
  scheme admits noncomputable-meaning pathologies against which no universal machine
  exists (audit finding 1, Argument A).
* **Input layout is `pairEncode α x` — code first, input second** — deviating from
  [AB09]'s `⟨x, α⟩`: with the input first, the startup cost of reaching the code
  grows with `|x|` and the stated bounds are false (audit finding 2, Argument B).
  With the code first, startup (parsing and canonizing `α`) costs a constant
  depending only on `α`, absorbed into `C`, and the simulated input head walks the
  verbatim `x` region on demand.
* `universal` is the **all-string evaluator** [AB09's `U(x, α) = M_α(x)`, p. 20]:
  it covers every `α` through `c.decode` (padded and fallback representations
  included), and it carries **both directions** — the forward time bound, and the
  converse that any *completed* output of `U` (output on halting; intermediate
  emissions of a non-halting run are unconstrained) is a completed output of the
  simulated machine, so divergence is preserved (round-1 finding 3; round-2
  Argument C).
* The constant `C` depends on the **representation** `α`, a documented weakening of
  [AB09]'s machine-dependent constant that is *necessary* at this generality: an
  effective scheme can reserve arbitrarily long identical-prefix representations of
  two fixed machines, defeating any constant that factors through `c.decode α`
  (round-2 audit, finding 6 and Argument E). Recovering the book's dependence would
  require further representation assumptions.
* **The core bound is linear**, `C · (t + 1)`: coded machines are already in
  one-work-tape binary normal form, so `U` pays a constant per simulated step.
  [AB09]'s relaxed quadratic bound reappears in `universal_quadratic`, where an
  *arbitrary* binary machine is first normal-formed ([AB09, Claims 1.5-1.6]); that
  corollary is stated — and labeled — at the level of **total function computation**
  (audit finding 4), the machine-level partial statement being `universal` itself.
  The `O(T log T)` sharpening ([AB09, §1.7]) is the phase-5 stretch goal.
* `timed_universal` outputs `true :: output` on success and `[false]` on timeout, a
  concrete rendering of [AB09]'s "special failure symbol" (§1.4.1); its budget is
  quadratic (binary clock maintenance). The deadline convention: halting is checked
  after every simulated transition *including the `t`-th*, so a machine first
  halting exactly at the deadline is a success; at budget `0` no initialized machine
  has halted, and the timeout branch applies (audit finding 6).

## Main results

* `Turing.universal` — the all-string evaluator [AB09, Theorem 1.9 core].
* `Turing.universal_quadratic` — the relaxed quadratic form for total functions of
  arbitrary binary machines [AB09, Theorem 1.9 as proved in §1.4.1].
* `Turing.timed_universal` — the time-bounded universal machine [AB09, §1.4.1].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4.1, Theorem 1.9, pp. 20-21; Figure 1.6.)
-/

namespace Turing

open FinTM

/-- **The universal machine as an all-string evaluator** [AB09, Theorem 1.9]: for any
effective scheme there is a single machine `U` such that for every string `α` there
is a constant `C` (depending on `α`, absorbing its decoding) with, for every input
`x`: whenever the machine `α` denotes halts on `x` within `t` steps with `output`,
`U` on `pairEncode α x` halts with the same output within `C · (t + 1)` steps —
and conversely every *completed* output of `U` on `pairEncode α x` (its output on
halting) is a completed output of the denoted machine on `x`, so divergence is
preserved.

**Proof sketch** (after [AB09, Figure 1.6], adapted to the code-first layout).
Startup: `U` runs the scheme's `canonizer` on the doubled-bit `α`-region (via the
composition combinators), leaving the fixed serialization of `M := c.decode α` — the
state count, initial state, and table — on a *table* work tape, and writes the
initial state on a *state* tape; cost `O(canonizerTime |α| + |α| + 1)`, a constant
for fixed `α`, absorbed into `C`. `U`'s input head then parks at the start of the
verbatim `x` region, and a *work* tape mirrors `M`'s work tape. **The simulated
input's left boundary must be emulated explicitly** (round-2 audit, finding 3): the
cell physically left of the `x` region is the pairing delimiter's `true`, not a
blank, so `U` keeps a marker on a spare work tape whose head tracks the virtual
input position — at virtual position zero it supplies a blank read and suppresses
further outward moves (mirroring `moveInputPos`'s clamp), and for empty `x` the
virtual head starts at the right boundary blank adjacent to that marked left
boundary. Each simulated step: read the mirrored work symbol and the input symbol
under the simulated head (the input head moves one cell per simulated move — `x` is
verbatim, no doubling — with the boundary marker moved in lockstep), scan the table
for the record matching (state, input read, work read) — at most the table length,
constant in `t` — and apply it: update the state tape, write/move on the mirrored
tape, emit `M`'s emission verbatim. Forward bound: `C · (t + 1)`. Converse:
`U` emits only what the simulation emits and halts only when the simulation halts,
so any completed output of `U` is an output of `M` on `x`. -/
theorem universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ x : List Bool,
      (∀ (output : List Bool) (t : ℕ),
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode α x) output (C * (t + 1))) ∧
      (∀ output : List Bool,
        (∃ t, U.ComputesInTime (pairEncode α x) output t) →
        ∃ t, (c.decode α).toFinTM.ComputesInTime x output t) := by
  refine ⟨universalTM c, ?_⟩
  apply universal_from_blocks c (universalTM c) (universalStartupBound c)
    (universalBlockBound c) (universalRelation c)
  · exact universalRelation_start c
  · intro α x src dst h
    by_cases hs : src.state = none
    · have hu := (universalRelation_halt c α x src dst h).mp hs
      refine ⟨1, le_refl _, ?_, ?_⟩
      · simp only [universalBlockBound]
        omega
      · rw [MultiTapeTM.step_of_halt hs, MultiTapeTM.runFrom_of_halt _ hu]
        exact h
    · -- A live source: lift the proved interpreter block through capture.
      obtain ⟨p, tapes, heads, hp, rfl⟩ := h
      obtain ⟨d, p', hd, hB, hp', he⟩ := universal_live_block (c.decode α) α src p hp hs
      refine ⟨d, hd, hB, p', tapes, heads, hp', ?_⟩
      change (universalCaptureTM (universalCanonTM c) universalInterpreter).tm.runFrom
        (rightCfg Sum.inr (universalSimulationCfg (c.decode α) α src p) tapes heads) d = _
      rw [universalCapture_interpreter_run, he]
  · exact universalRelation_halt c
  · exact universalRelation_output c

/-- **The relaxed quadratic form, for total functions** [AB09, Theorem 1.9 as proved
in §1.4.1 — labeled per audit finding 4: this is the total-function corollary; the
machine-level, partial-computation statement is `Turing.universal`]: every binary
machine computing a total function `f` within `T` has a code `α` such that the
*same* universal machine computes `f x` from `pairEncode α x` within
`C · (T |x| + 1)²`.

**Proof sketch.** Normal-form the machine with `Turing.FinTM.one_work_tape_binary`
(quadratic, [AB09, Claims 1.5-1.6]), relabel its states with `Turing.exists_codeTM`,
take `α := c.encode` of that coded machine (so `c.decode α` is that machine, by
`MachineCode.decode_encode`), and apply the forward direction of `Turing.universal`;
the constants compose as `C_U · (c₁ · (T n + 1)² + 1) ≤ C · (T n + 1)²`. -/
theorem universal_quadratic (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (M₀ : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ),
      M₀.ComputesFunInTime f T →
      ∃ (α : List Bool) (C : ℕ), ∀ x : List Bool,
        U.ComputesInTime (pairEncode α x) (f x) (C * (T x.length + 1) ^ 2) := by
  obtain ⟨U, hU⟩ := universal c
  refine ⟨U, ?_⟩
  intro M₀ f T hM
  obtain ⟨M₁, c₁, hk, h₁⟩ := FinTM.one_work_tape_binary M₀ f T hM
  obtain ⟨N, hN⟩ := exists_codeTM M₁ hk
  let α := c.encode N
  obtain ⟨C_U, hCU⟩ := hU α
  refine ⟨α, C_U * (c₁ + 1), fun x => ?_⟩
  have hcoded : (c.decode α).toFinTM.ComputesInTime x (f x)
      (c₁ * (T x.length + 1) ^ 2) := by
    rw [show c.decode α = N from c.toMachineCode.decode_encode N]
    exact (hN x (f x) _).2 (h₁ x)
  apply ((hCU x).1 (f x) _ hcoded).mono
  have hpow : 0 < (T x.length + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos _)
  calc C_U * (c₁ * (T x.length + 1) ^ 2 + 1)
      ≤ C_U * (c₁ * (T x.length + 1) ^ 2 + (T x.length + 1) ^ 2) :=
        Nat.mul_le_mul (le_refl C_U) (Nat.add_le_add_left hpow _)
    _ = C_U * (c₁ + 1) * (T x.length + 1) ^ 2 := by ring

/-! ### Epoch 4: private stopped-interpreter infrastructure

**Implementation note (epoch 4).** The private construction below implements the
frozen timed-machine sketch. A prefix parser saves the clock and canonizes only
the code. The interpreter borrows before each source transition and routes source
halting to a buffered-output phase. The final induction checks the successor's
halting state before requiring any further clock credit.

The stop controller follows the audited interpreter until an action is ready.
Its next transition then halts without applying that action. A live endpoint
therefore certifies that no earlier action was applied. This permits replay
through the clock/buffer wrapper using the existing table representation.
-/

/-- Stop immediately before applying a selected source record. -/
private def timedCutInterpreter : MultiTapeTM 4 Bool UniversalControl where
  q₀ := universalInterpreter.q₀
  tr := fun q inp ws => match q with
    | .applyRecord _ _ => ⟨0, fun _ => (none, 0), none, none⟩
    | _ => universalInterpreter.tr q inp ws

/-- The four administrative reads. -/
private lemma timedCut_Eval_reads {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) :
    (universalEvalCfg base q table tp state sp).workTapeSymbols =
      universalFour (bufferTape table tp) (state sp)
        (base.workTapeSymbols 2) (base.workTapeSymbols 3) := by
  funext i
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- One administrative action changes only the two designated tape cursors and
optionally the state-tape cell. -/
private lemma timedCut_Admin_apply {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q q' : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) (dt ds : SignType) (w : Option (Option Bool)) :
    (universalAdmin q' dt (w, ds)).apply (universalEvalCfg base q table tp state sp) =
      universalEvalCfg base q' table (tp + (dt : ℤ))
        (match w with | none => state | some b => Function.update state sp b)
        (sp + (ds : ℤ)) := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (List.append_nil _)
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> cases w <;> rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;>
      first | rfl | exact add_zero _

/-- Read-based administrative step rule. -/
private lemma timedCut_Eval_step {x : List Bool} (base : Cfg 4 Bool UniversalControl x)
    (q q' : UniversalControl) (table : List Bool) (tp : ℤ)
    (state : ℤ → Option Bool) (sp : ℤ) (dt ds : SignType) (w : Option (Option Bool))
    (h : timedCutInterpreter.tr q base.inputSymbol
      (universalFour (bufferTape table tp) (state sp)
        (base.workTapeSymbols 2) (base.workTapeSymbols 3)) = universalAdmin q' dt (w, ds)) :
    timedCutInterpreter.step (universalEvalCfg base q table tp state sp) =
      universalEvalCfg base q' table (tp + (dt : ℤ))
        (match w with | none => state | some b => Function.update state sp b)
        (sp + (ds : ℤ)) := by
  change (timedCutInterpreter.tr q _ _).apply _ = _
  rw [timedCut_Eval_reads]
  change (timedCutInterpreter.tr q base.inputSymbol _).apply _ = _
  conv_lhs => rw [h]
  cases w <;> exact timedCut_Admin_apply base q q' table tp state sp dt ds _

/-- Look up the first unconsumed cell of a contiguous table. -/
private lemma timedCut_table_read (l r : List Bool) (b : Bool) :
    bufferTape (l ++ b :: r) (l.length : ℤ) = some b := by
  rw [bufferTape_nat, List.getElem?_append_right (le_refl _)]
  simp

/-- Exact-cost table rewind. The initial unconditional left move has put the
cursor at `j-1`, where `j` is at most the table length.

**Proof sketch.** At `j=0`, the cursor is the left blank and one move right
starts the count parser. At positive `j`, a nonblank table cell is read and the
cursor decreases once. Induction accounts for every transition and leaves all
other tapes, physical input, and accumulated output unchanged. -/
private lemma timedCut_table_rewind {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (initial : Bool) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ) :
    ∀ j, j ≤ table.length →
      timedCutInterpreter.runFrom
        (universalEvalCfg base (.rewindTable initial index) table (j - 1) state sp) (j + 1) =
      universalEvalCfg base (.countFirst initial index) table 0 state sp := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.rewindTable initial index) (.countFirst initial index)
      table (-1) state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour])
    simpa using he
  | succ j ih =>
    intro hj
    have hr : bufferTape table (j : ℤ) = some table[j] := by
      rw [bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have he := timedCut_Eval_step base (.rewindTable initial index) (.rewindTable initial index)
      table (j : ℤ) state sp .neg 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    have hh : (j + 1 : ℤ) - 1 = j := by omega
    simp only [Nat.cast_add, Nat.cast_one, hh]
    rw [he]
    simpa using ih (by omega)

/-- Skip an arbitrary doubled, delimited count field at exact cost. No binary
arithmetic on its value is needed by the interpreter.

**Proof sketch.** Each doubled pair returns the parser to its first-half state
in two transitions. The terminal aligned `false,true` pair selects the initial
state copier or skipper. Induct on the count-bit list while growing the consumed
prefix, so table lookup is justified at every cursor position. -/
private lemma timedCut_count_run {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (initial : Bool) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (bits : List Bool) (l r : List Bool)
    (ht : table = l ++ (bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.countFirst initial index) table l.length state sp)
      (2 * bits.length + 2) =
    universalEvalCfg base (if initial then .initialCopy else .initialSkip index) table
      (l.length + 2 * bits.length + 2) state sp := by
  induction bits generalizing l with
  | nil =>
    have hr0 : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l (true :: r) false
    have hr1 : bufferTape table (l.length + 1 : ℤ) = some true := by
      have h' : table = (l ++ [false]) ++ true :: r := by simp [ht, List.append_assoc]
      have h := timedCut_table_read (l ++ [false]) r true
      simpa [h', List.length_append] using h
    have he0 := timedCut_Eval_step base (.countFirst initial index)
      (.countSecond initial index false) table l.length state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr0])
    have he1 := timedCut_Eval_step base (.countSecond initial index false)
      (if initial then .initialCopy else .initialSkip index)
      table (l.length + 1) state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr1])
    change timedCutInterpreter.runFrom _ (0 + 1 + 1) = _
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, he0]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [he1]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero,
      List.length_nil, Nat.cast_zero, mul_zero]
    congr 1
  | cons b bits ih =>
    have hr0 : bufferTape table (l.length : ℤ) = some b := by
      rw [ht]
      simpa [List.flatMap_cons, List.append_assoc] using
        timedCut_table_read l (b :: ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r)) b
    have hr1 : bufferTape table (l.length + 1 : ℤ) = some b := by
      have h' : table = (l ++ [b]) ++ b :: ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) := by
        simp [ht, List.append_assoc]
      have h := timedCut_table_read (l ++ [b]) ((bits.flatMap fun b => [b, b]) ++ [false, true] ++ r) b
      simpa [h', List.length_append] using h
    have he0 := timedCut_Eval_step base (.countFirst initial index)
      (.countSecond initial index b) table l.length state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr0])
    have he1 := timedCut_Eval_step base (.countSecond initial index b)
      (.countFirst initial index) table (l.length + 1) state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr1])
    have h' : table = (l ++ [b, b]) ++ (bits.flatMap fun b => [b, b]) ++ [false, true] ++ r := by
      simp [ht, List.append_assoc]
    have hi := ih (l ++ [b, b]) h'
    conv_lhs => rw [show 2 * (b :: bits).length + 2 =
      1 + 1 + (2 * bits.length + 2) by simp; omega]
    rw [MultiTapeTM.runFrom_add]
    change timedCutInterpreter.runFrom
      (timedCutInterpreter.step (timedCutInterpreter.step _)) _ = _
    rw [he0]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [he1]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert hi using 1 <;> simp [List.length_append, List.length_cons] <;> congr 1 <;> omega


/-- Appending a next-state unary symbol extends the intact state tape. -/
private lemma timedCut_StateTape_append (n : ℕ) :
    Function.update (universalStateTape n) (n + 1 : ℤ) (some true) =
      universalStateTape (n + 1) := by
  have h := bufferTape_append (false :: List.replicate n true) true
  simpa only [universalStateTape, List.replicate_add, List.replicate_one,
    List.cons_append, List.length_cons, List.length_replicate,
    Nat.cast_add, Nat.cast_one] using h.symm

/-- An intact unary state reads its blank immediately after the last symbol. -/
private lemma timedCut_StateTape_end (n : ℕ) :
    universalStateTape n (n + 1) = none := by
  simp [universalStateTape, bufferTape]

/-- A marker-directed state rewind has exact cost equal to cursor plus one.
Its premise is deliberately independent of whether traversed cells are erased
blanks or retained unary ones.

**Proof sketch.** Each positive cursor sees a non-marker cell and moves left.
At zero the permanent marker causes one right move and transfer to the supplied
continuation. The entire tape, input head, and real output stay unchanged. -/
private lemma timedCut_state_rewind {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (q q' : UniversalControl)
    (table : List Bool) (tp : ℤ) (state : ℤ → Option Bool)
    (hzero : state 0 = some false)
    (hother : ∀ j : ℕ, 0 < j → state j ≠ some false)
    (hstop : ∀ inp work, work 1 = some false →
      timedCutInterpreter.tr q inp work = universalAdmin q' 0 (none, .pos))
    (hscan : ∀ inp work, work 1 ≠ some false →
      timedCutInterpreter.tr q inp work = universalAdmin q 0 (none, .neg)) :
    ∀ j : ℕ, timedCutInterpreter.runFrom
      (universalEvalCfg base q table tp state j) (j + 1) =
      universalEvalCfg base q' table tp state 1 := by
  intro j
  induction j with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base q q' table tp state 0 0 .pos none
      (hstop _ _ (by simpa [universalFour] using hzero))
    simpa using he
  | succ j ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have he := timedCut_Eval_step base q q table tp state (j + 1) 0 .neg none
      (hscan _ _ (by simpa [universalFour] using hother (j + 1) (by omega)))
    rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by omega, he]
    simpa using ih

/-- The table's initial-state unary field can be skipped at exact cost.

**Proof sketch.** Induct on the number of unary ones. Each one advances the table
cursor; the final zero advances once more and enters record-group selection. -/
private lemma timedCut_initial_skip {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (n : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.initialSkip index) table l.length state sp) (n + 1) =
      universalEvalCfg base (.group index) table (l.length + n + 1) state sp := by
  induction n generalizing l with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.initialSkip index) (.group index)
      table l.length state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate n true ++ false :: r) true
    have he := timedCut_Eval_step base (.initialSkip index) (.initialSkip index)
      table l.length state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    have hi := ih (l ++ [true]) ht'
    convert hi using 1 <;> simp [List.length_append, List.length_cons] <;> congr 1 <;> omega



/-- Copy a unary table field onto the state tape. This single gadget serves both
initial-state extraction and live successor-state replacement.

**Proof sketch.** A `true` table cell appends one unary state symbol and moves both
cursors right. A terminal `false` switches to the supplied continuation, with its
specified table movement. Induction preserves exact table/state positions and
accounts for all `n+1` transitions. -/
private lemma timedCut_unary_copy {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (q q' : UniversalControl) (doneMove : SignType)
    (table : List Bool)
    (htrue : ∀ inp work, work 0 = some true →
      timedCutInterpreter.tr q inp work = universalAdmin q .pos (some (some true), .pos))
    (hfalse : ∀ inp work, work 0 = some false →
      timedCutInterpreter.tr q inp work = universalAdmin q' doneMove (none, 0))
    (n j : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base q table l.length (universalStateTape j) (j + 1)) (n + 1) =
      universalEvalCfg base q' table (l.length + n + (doneMove : ℤ))
        (universalStateTape (j + n)) (j + n + 1) := by
  induction n generalizing l j with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base q q' table l.length (universalStateTape j) (j + 1)
      doneMove 0 none (hfalse _ _ (by simp [universalFour, hr]))
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate n true ++ false :: r) true
    have he := timedCut_Eval_step base q q table l.length (universalStateTape j) (j + 1)
      .pos .pos (some (some true)) (htrue _ _ (by simp [universalFour, hr]))
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, timedCut_StateTape_append]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    have hi := ih (j + 1) (l ++ [true]) ht'
    convert hi using 1 <;> simp [List.length_append, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 n, Int.add_assoc] <;> congr 1 <;> omega

/-- Installing a single permanent marker in an otherwise blank tape. -/
private lemma timedCut_install_marker (b : Bool) :
    Function.update (fun _ : ℤ => none) 0 (some b) = bufferTape [b] := by
  simpa using (bufferTape_append [] b).symm

/-- Interpreter entry with the captured table on its right blank and three
fresh auxiliary tapes. Physical input is already parked at the suffix start. -/
private def timedCut_InterpreterInitial {x : List Bool} (p : Fin (x.length + 2))
    (table : List Bool) : Cfg 4 Bool UniversalControl x :=
  ⟨some .start, p, universalFour (bufferTape table) (fun _ => none) (fun _ => none)
      (fun _ => none), universalFour table.length 0 0 0, []⟩

/-- Inactive data during interpreter initialization: physical input is stationary,
simulated work is blank, and the virtual-left marker is installed at zero with
its head at one (also for empty suffixes). -/
private def timedCut_InterpreterBase {x : List Bool} (p : Fin (x.length + 2)) :
    Cfg 4 Bool UniversalControl x :=
  ⟨some .main, p, universalFour (fun _ => none) (fun _ => none) (fun _ => none)
      (bufferTape [true]), universalFour 0 0 0 1, []⟩

/-- The first interpreter step installs the permanent markers and starts the
unconditional table rewind. -/
private lemma timedCut_Interpreter_first {x : List Bool} (p : Fin (x.length + 2))
    (table : List Bool) :
    timedCutInterpreter.step (timedCut_InterpreterInitial p table) =
      universalEvalCfg (timedCut_InterpreterBase p) (.rewindTable true 0) table
        (table.length - 1) (universalStateTape 0) 1 := by
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · rfl
    · exact timedCut_install_marker false
    · rfl
    · exact timedCut_install_marker true
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl

/-- Exact interpreter initialization for a canonical count/initial-state prefix.
No transition-table lookup is involved yet.

**Proof sketch.** Install both markers (one transition), rewind the whole captured
table (`|table|+1`), skip the doubled count (`2|bits|+2`), copy the initial unary
state (`n+1`), and rewind its cursor (`n+2`). The sum is
`|table| + 2|bits| + 2n + 7`. Every intermediate configuration keeps the physical
input fixed and real output empty. -/
private lemma timedCut_Interpreter_initialize {x : List Bool}
    (p : Fin (x.length + 2)) (table bits records : List Bool) (n : ℕ)
    (ht : table = pairEncode bits (List.replicate n true ++ false :: records)) :
    timedCutInterpreter.runFrom (timedCut_InterpreterInitial p table)
      (table.length + 2 * bits.length + 2 * n + 7) =
    universalEvalCfg (timedCut_InterpreterBase p) .main table
      (2 * bits.length + 2 + n + 1) (universalStateTape n) 1 := by
  let base := timedCut_InterpreterBase p
  have hrew := timedCut_table_rewind base true 0 table (universalStateTape 0) 1
    table.length (le_refl _)
  have hcount := timedCut_count_run base true 0 table (universalStateTape 0) 1
    bits [] (List.replicate n true ++ false :: records) (by simpa [pairEncode] using ht)
  let countPrefix := (bits.flatMap fun b => [b, b]) ++ [false, true]
  have hlen : countPrefix.length = 2 * bits.length + 2 := by
    simpa [countPrefix, pairEncode] using universal_pair_length bits []
  have hcopy := timedCut_unary_copy base .initialCopy (.rewindState none) .pos table
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) n 0 countPrefix records
    (by simpa [countPrefix, pairEncode, List.append_assoc] using ht)
  have hstate := timedCut_state_rewind base (.rewindState none) .main table
    (2 * bits.length + 2 + n + 1) (universalStateTape n)
    (universalStateTape_marker n).1 (universalStateTape_marker n).2
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) (n + 1)
  have htime : table.length + 2 * bits.length + 2 * n + 7 =
      1 + (table.length + 1) + (2 * bits.length + 2) + (n + 1) + (n + 2) := by omega
  rw [htime,
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1) + (2 * bits.length + 2) + (n + 1)) (n + 2),
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1) + (2 * bits.length + 2)) (n + 1),
    MultiTapeTM.runFrom_add _ (1 + (table.length + 1)) (2 * bits.length + 2),
    MultiTapeTM.runFrom_add _ 1 (table.length + 1)]
  change timedCutInterpreter.runFrom
    (timedCutInterpreter.runFrom
      (timedCutInterpreter.runFrom
        (timedCutInterpreter.runFrom
          (timedCutInterpreter.step (timedCut_InterpreterInitial p table))
          (table.length + 1)) (2 * bits.length + 2)) (n + 1)) (n + 2) = _
  rw [timedCut_Interpreter_first, hrew]
  have hc : timedCutInterpreter.runFrom
      (universalEvalCfg base (.countFirst true 0) table 0 (universalStateTape 0) 1)
      (2 * bits.length + 2) =
    universalEvalCfg base .initialCopy table (2 * bits.length + 2) (universalStateTape 0) 1 := by
    simpa using hcount
  rw [hc]
  have hp : timedCutInterpreter.runFrom
      (universalEvalCfg base .initialCopy table (2 * bits.length + 2) (universalStateTape 0) 1)
      (n + 1) =
    universalEvalCfg base (.rewindState none) table (2 * bits.length + 2 + n + 1)
      (universalStateTape n) (n + 1) := by
    simpa [hlen] using hcopy
  rw [hp]
  simpa using hstate



/-- Skip the remaining fixed action fields, one transition per bit.

**Proof sketch.** Descending induction on the number of fields still to skip.
The last field enters the unary scanner; every other field increments the
bounded field register. No tape content is inspected or modified. -/
private lemma timedCut_skip_fixed {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ) :
    ∀ (n : ℕ) (field : Fin 8) (tp : ℤ), field.val + n = 7 →
      timedCutInterpreter.runFrom
        (universalEvalCfg base (.skipFixed dest rem field) table tp state sp) (n + 1) =
      universalEvalCfg base (.skipUnary dest rem) table (tp + n + 1) state sp := by
  intro n
  induction n with
  | zero =>
    intro field tp hf
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.skipFixed dest rem field) (.skipUnary dest rem)
      table tp state sp .pos 0 none (by simp [timedCutInterpreter, universalInterpreter, show field.val = 7 by omega])
    simpa using he
  | succ n ih =>
    intro field tp hf
    have hne : field.val ≠ 7 := by omega
    have he := timedCut_Eval_step base (.skipFixed dest rem field)
      (.skipFixed dest rem ⟨field.val + 1, by omega⟩) table tp state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, hne])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih ⟨field.val + 1, by omega⟩ (tp + 1) (by simp; omega) using 1 <;>
      push_cast <;> congr 1 <;> omega


/-- The unary tail of a skipped record costs exactly its serialized length.

**Proof sketch.** A true cell advances once without changing control. The false
terminator either finishes the request or decrements the bounded record counter.
Induction grows the consumed list prefix by one cell. -/
private lemma timedCut_skip_unary {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (n : ℕ) (l r : List Bool)
    (ht : table = l ++ List.replicate n true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipUnary dest rem) table l.length state sp) (n + 1) =
    universalEvalCfg base
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table (l.length + n + 1) state sp := by
  induction n generalizing l with
  | zero =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa using timedCut_table_read l r false
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.skipUnary dest rem)
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table l.length state sp .pos 0 none
      (by
        by_cases h : rem.val = 0
        · have hz : rem = 0 := Fin.ext h
          simp [timedCutInterpreter, universalInterpreter, universalFour, hr, hz, universalSkipDone]
        · have hz : rem ≠ 0 := fun he => h (congrArg Fin.val he)
          simp [timedCutInterpreter, universalInterpreter, universalFour, hr, h, hz, universalSkipDone])
    simpa using he
  | succ n ih =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate n true ++ false :: r) true
    have he := timedCut_Eval_step base (.skipUnary dest rem) (.skipUnary dest rem)
      table l.length state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    have ht' : table = (l ++ [true]) ++ List.replicate n true ++ false :: r := by
      simp [ht, List.replicate_succ, List.append_assoc]
    convert ih (l ++ [true]) ht' using 1 <;>
      simp [List.length_append, List.length_cons] <;> congr 1 <;> omega

/-- Skip one complete serialized record at exact cost.

**Proof sketch.** Concatenate the eight fixed-field transitions and the unary
tail scan. The record grammar identifies their total with the record length. -/
private lemma timedCut_skip_record {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9)) (rem : Fin 9)
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (a : Action 1 Bool (Fin (n + 1))) (l r : List Bool)
    (ht : table = l ++ universalRecordBits a ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp)
      (universalRecordBits a).length =
    universalEvalCfg base
      (if h : rem.val = 0 then universalSkipDone dest
        else .skipFixed dest ⟨rem.val - 1, by omega⟩ 0)
      table (l.length + (universalRecordBits a).length) state sp := by
  have hlen : (universalRecordBits a).length = 8 + (universalNextOnes a.state + 1) := by
    rw [universal_record_shape]
    simp only [List.length_append, List.length_ofFn, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  have hfixed := timedCut_skip_fixed base dest rem table state sp 7 0 l.length rfl
  have hunary := timedCut_skip_unary base dest rem table state sp
    (universalNextOnes a.state) (l ++ List.ofFn (universalActionBits a)) r
    (by simpa [universal_record_shape, List.append_assoc] using ht)
  rw [hlen, MultiTapeTM.runFrom_add]
  have hf : timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp) 8 =
      universalEvalCfg base (.skipUnary dest rem) table (l.length + 8) state sp := by
    simpa only [Nat.cast_ofNat, Int.add_assoc, show (7 : ℤ) + 1 = 8 from rfl] using hfixed
  rw [hf]
  simpa only [List.length_append, List.length_ofFn, Nat.cast_add, Nat.cast_ofNat,
    Int.add_assoc] using hunary

/-- A bounded request skips precisely the specified nonempty list of records.

**Proof sketch.** Execute the first record and decrement the record counter.
The last record enters the requested continuation. Run addition adds the
serialized lengths, without an extra transition between consecutive records. -/
private lemma timedCut_skip_records {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (dest : Option (Fin 9))
    (table : List Bool) (state : ℤ → Option Bool) (sp : ℤ)
    (as : List (Action 1 Bool (Fin (n + 1)))) (l r : List Bool)
    (rem : Fin 9) (hlen : as.length = rem.val + 1)
    (ht : table = l ++ as.flatMap universalRecordBits ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.skipFixed dest rem 0) table l.length state sp)
      (as.flatMap universalRecordBits).length =
    universalEvalCfg base (universalSkipDone dest) table
      (l.length + (as.flatMap universalRecordBits).length) state sp := by
  induction as generalizing l rem with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons a as ih =>
    have hv : rem.val = as.length := by simp only [List.length_cons] at hlen; omega
    have he := timedCut_skip_record base dest rem table state sp a l
      (as.flatMap universalRecordBits ++ r)
      (by simpa only [List.flatMap_cons, List.append_assoc] using ht)
    rw [List.flatMap_cons, List.length_append, MultiTapeTM.runFrom_add, he]
    cases as with
    | nil => simp [hv]
    | cons b bs =>
      have hn : rem.val ≠ 0 := by simp only [List.length_cons] at hv; omega
      rw [dif_neg hn]
      have htail : (b :: bs).length = rem.val - 1 + 1 := by
        simp only [List.length_cons] at hv ⊢
        omega
      have hi := ih (l ++ universalRecordBits a) ⟨rem.val - 1, by omega⟩ htail
        (by simpa only [List.flatMap_cons, List.append_assoc] using ht)
      convert hi using 1 <;>
        simp only [List.length_append, Nat.cast_add] <;> congr 1 <;> omega

/-- Each erased unary state symbol skips exactly nine transition records.

**Proof sketch.** Erase the first remaining state symbol, run the nine-record
scanner, and repeat for the remaining groups. At the final blank one transition
enters the state rewind. The state-window invariant records all erasures. -/
private lemma timedCut_skip_groups {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9) (table : List Bool)
    (groups : List (List (Action 1 Bool (Fin (n + 1)))))
    (hg : ∀ g ∈ groups, g.length = 9) (l r : List Bool) (j : ℕ)
    (ht : table = l ++ groups.flatMap (fun g => g.flatMap universalRecordBits) ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length
        (universalStateWindow j groups.length) (j + 1))
      (groups.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length + 1) =
    universalEvalCfg base (.rewindState (some index)) table
      (l.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length)
      (universalStateWindow (j + groups.length) 0) (j + groups.length + 1) := by
  induction groups generalizing l j with
  | nil =>
    simp only [List.length_nil, List.flatMap_nil, Nat.add_zero, Nat.zero_add,
      Nat.cast_zero, add_zero, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.group index) (.rewindState (some index))
      table l.length (universalStateWindow j 0) (j + 1) 0 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, universalStateWindow_end])
    simpa using he
  | cons g gs ih =>
    have hgl : g.length = 9 := hg g (by simp)
    have he := timedCut_Eval_step base (.group index) (.skipFixed (some index) 8 0)
      table l.length (universalStateWindow j (gs.length + 1)) (j + 1) 0 .pos (some none)
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, universalStateWindow_read])
    have hskip := timedCut_skip_records base (some index) table
      (universalStateWindow (j + 1) gs.length) (j + 2) g l
      (gs.flatMap (fun g => g.flatMap universalRecordBits) ++ r) 8 hgl
      (by simpa [List.flatMap_cons, List.append_assoc] using ht)
    have hrest := ih (fun a ha => hg a (by simp [ha]))
      (l ++ g.flatMap universalRecordBits) (j + 1)
      (by simpa [List.flatMap_cons, List.append_assoc] using ht)
    have htime : (g :: gs).length +
        ((g :: gs).flatMap (fun g => g.flatMap universalRecordBits)).length + 1 =
        1 + (g.flatMap universalRecordBits).length +
          (gs.length + (gs.flatMap (fun g => g.flatMap universalRecordBits)).length + 1) := by
      simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega
    rw [htime, MultiTapeTM.runFrom_add _ (1 + (g.flatMap universalRecordBits).length)
      (gs.length + (gs.flatMap (fun g => g.flatMap universalRecordBits)).length + 1),
      MultiTapeTM.runFrom_add _ 1 (g.flatMap universalRecordBits).length]
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero, he]
    simp only [SignType.coe_zero, add_zero, SignType.pos_eq_one, SignType.coe_one,
      universalStateWindow_erase]
    rw [show (j : ℤ) + 1 + 1 = j + 2 by omega, hskip]
    simpa only [universalSkipDone, List.flatMap_cons, List.length_append, List.length_cons,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Int.add_assoc, Int.add_left_comm, Int.add_comm, Int.reduceAdd] using hrest

/-- Reading fixed action fields fills the finite eight-bit register exactly.

**Proof sketch.** The register already agrees with the record before the current
field. Read and update that field, maintaining agreement on a longer prefix.
After field seven the agreement covers every register entry. -/
private lemma timedCut_read_fixed {x : List Bool}
    (base : Cfg 4 Bool UniversalControl x) (table : List Bool)
    (state : ℤ → Option Bool) (sp : ℤ) (bits : Fin 8 → Bool) (l r : List Bool)
    (ht : table = l ++ List.ofFn bits ++ r) :
    ∀ (n : ℕ) (field : Fin 8) (old : Fin 8 → Bool), field.val + n = 7 →
      (∀ i : Fin 8, i.val < field.val → old i = bits i) →
      timedCutInterpreter.runFrom
        (universalEvalCfg base (.readAction field old) table
          (l.length + field.val) state sp) (n + 1) =
      universalEvalCfg base (.nextState bits) table (l.length + 8) state sp := by
  intro n
  induction n with
  | zero =>
    intro field old hf hknown
    have hv : field.val = 7 := by omega
    have hr : bufferTape table (l.length + field.val : ℤ) = some (bits field) := by
      rw [← Nat.cast_add, bufferTape_nat, ht, List.append_assoc,
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simpa using field.isLt), List.getElem?_ofFn]
      simp only [field.isLt, ↓reduceDIte]
    have hb : Function.update old field (bits field) = bits := by
      funext i
      by_cases hi : i = field
      · subst i; simp
      · rw [Function.update_of_ne hi]
        apply hknown
        have hn : i.val ≠ field.val := fun h => hi (Fin.ext h)
        omega
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have he := timedCut_Eval_step base (.readAction field old) (.nextState bits)
      table (l.length + field.val) state sp .pos 0 none
      (by
        simp only [timedCutInterpreter, universalInterpreter, universalFour, ↓reduceIte, hr]
        simp only [hv, ↓reduceDIte, hb])
    rw [he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    congr 1
    omega
  | succ n ih =>
    intro field old hf hknown
    have hv : field.val ≠ 7 := by omega
    have hr : bufferTape table (l.length + field.val : ℤ) = some (bits field) := by
      rw [← Nat.cast_add, bufferTape_nat, ht, List.append_assoc,
        List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left]
      rw [List.getElem?_append_left (by simpa using field.isLt), List.getElem?_ofFn]
      simp only [field.isLt, ↓reduceDIte]
    have hb : ∀ i : Fin 8, i.val < field.val + 1 →
        Function.update old field (bits field) i = bits i := by
      intro i hi
      by_cases he : i = field
      · subst i; simp
      · rw [Function.update_of_ne he]
        apply hknown
        have hn : i.val ≠ field.val := fun h => he (Fin.ext h)
        omega
    have he := timedCut_Eval_step base (.readAction field old)
      (.readAction ⟨field.val + 1, by omega⟩ (Function.update old field (bits field)))
      table (l.length + field.val) state sp .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr, hv])
    rw [MultiTapeTM.runFrom_succ_eq_step, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    convert ih ⟨field.val + 1, by omega⟩ _ (by simp; omega) hb using 1 <;>
      simp only [Fin.val_mk, Nat.cast_add, Nat.cast_one] <;> congr 1 <;> omega

/-- Successor decoding, copying, and rewinding cost, before applying the action. -/
private def timedCut_NextCost {n : ℕ} : Option (Fin (n + 1)) → ℕ
  | none => 1
  | some q => 2 * q.val + 4

/-- Decode the successor field and install its unary state at cursor one.

**Proof sketch.** A halting flag takes one transition. A live flag takes one,
copying its index takes `q+1`, and rewinding the new state takes `q+2`.
The table cursor stops on the field's false terminator in both cases. -/
private lemma timedCut_prepare_next {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (table : List Bool) (bits : Fin 8 → Bool)
    (next : Option (Fin (n + 1))) (l r : List Bool)
    (ht : table = l ++ List.replicate (universalNextOnes next) true ++ false :: r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.nextState bits) table l.length (universalStateTape 0) 1)
      (timedCut_NextCost next) =
    universalEvalCfg base (.applyRecord bits next.isNone) table
      (l.length + universalNextOnes next) (universalStateTape ((next.map Fin.val).getD 0)) 1 := by
  cases next with
  | none =>
    have hr : bufferTape table (l.length : ℤ) = some false := by
      rw [ht]; simpa [universalNextOnes] using timedCut_table_read l r false
    have he := timedCut_Eval_step base (.nextState bits) (.applyRecord bits true)
      table l.length (universalStateTape 0) 1 0 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    simpa [timedCut_NextCost, universalNextOnes, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero] using he
  | some q =>
    have hr : bufferTape table (l.length : ℤ) = some true := by
      rw [ht]; simpa [universalNextOnes, List.replicate_succ, List.append_assoc] using
        timedCut_table_read l (List.replicate q.val true ++ false :: r) true
    have he := timedCut_Eval_step base (.nextState bits) (.copyState bits)
      table l.length (universalStateTape 0) 1 .pos 0 none
      (by simp [timedCutInterpreter, universalInterpreter, universalFour, hr])
    have hcopy := timedCut_unary_copy base (.copyState bits) (.rewindNext bits) 0 table
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) q.val 0 (l ++ [true]) r
      (by simpa [universalNextOnes, List.replicate_succ, List.append_assoc] using ht)
    have hrew := timedCut_state_rewind base (.rewindNext bits) (.applyRecord bits false)
      table (l.length + q.val + 1) (universalStateTape q.val)
      (universalStateTape_marker q.val).1 (universalStateTape_marker q.val).2
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h])
      (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) (q.val + 1)
    have hc : timedCutInterpreter.runFrom
        (universalEvalCfg base (.copyState bits) table (l.length + 1) (universalStateTape 0) 1)
        (q.val + 1) =
      universalEvalCfg base (.rewindNext bits) table (l.length + q.val + 1)
        (universalStateTape q.val) (q.val + 1) := by
      simpa [List.length_append, Int.add_assoc, Int.add_comm 1] using hcopy
    change timedCutInterpreter.runFrom _ (2 * q.val + 4) = _
    rw [show 2 * q.val + 4 = 1 + (q.val + 1) + (q.val + 2) by omega,
      MultiTapeTM.runFrom_add _ (1 + (q.val + 1)) (q.val + 2),
      MultiTapeTM.runFrom_add _ 1 (q.val + 1)]
    rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero, he]
    simp only [SignType.pos_eq_one, SignType.coe_one, SignType.coe_zero, add_zero]
    rw [hc]
    simpa only [universalNextOnes, Option.isNone_some, Option.map_some, Option.getD_some,
      Nat.cast_add, Nat.cast_one, Nat.add_assoc, Int.add_assoc] using hrew

/-- The nine actions for a state, in input-major, work-minor order. -/
private def timedCut_Actions (M : CodeTM) (q : Fin (M.numStates + 1)) :
    List (Action 1 Bool (Fin (M.numStates + 1))) :=
  ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
    ([none, some false, some true] : List (Option Bool)).map fun work =>
      M.tm.tr q inp (fun _ => work)

/-- Each state contributes nine records and the read offset selects its action. -/
private lemma timedCut_Actions_lookup (M : CodeTM) (q : Fin (M.numStates + 1))
    (inp work : Option Bool) :
    (timedCut_Actions M q).length = 9 ∧
    (timedCut_Actions M q)[(universalRecordIndex inp work).val]'(by
      change (universalRecordIndex inp work).val < 9
      exact (universalRecordIndex inp work).isLt) = M.tm.tr q inp (fun _ => work) := by
  constructor
  · rfl
  · rcases inp with _ | (_ | _) <;> rcases work with _ | (_ | _) <;> rfl

/-- Count prefix and initial-state field, excluding transition records. -/
private def timedCut_Header (M : CodeTM) : List Bool :=
  pairEncode (Nat.bits M.numStates) [] ++ List.replicate M.tm.q₀.val true ++ [false]

/-- Serialization as a header followed by the ordered lists of nine actions.

**Proof sketch.** Expand the serializer into its count, initial state, and table.
Identify each encoded action by its finite directions, optional symbols, and
successor, then regroup the nested enumerations into nine actions per state. -/
private lemma timedCut_serialization_actions (M : CodeTM) :
    M.serialize = timedCut_Header M ++
      ((List.finRange (M.numStates + 1)).map (timedCut_Actions M)).flatMap
        (fun g => g.flatMap universalRecordBits) := by
  have hr : M.serialize = pairEncode (Nat.bits M.numStates)
      (List.replicate M.tm.q₀.val true ++ false :: universalRecords M) := by
    unfold CodeTM.serialize
    change pairEncode _ ((List.replicate M.tm.q₀.val true ++ [false]) ++ _) = _
    rw [List.append_assoc]
    apply congrArg (pairEncode (Nat.bits M.numStates))
    apply congrArg (fun r : List Bool => List.replicate M.tm.q₀.val true ++ false :: r)
    unfold universalRecords
    dsimp only [List.append]
    congr 1
    funext q
    congr 1
    funext inp
    congr 1
    funext work
    generalize M.tm.tr q inp (fun _ => work) = a
    rcases a with ⟨di, tapes, out, next⟩
    have htapes : tapes = fun _ => tapes 0 := by
      funext i
      have hi : i = 0 := Fin.eq_zero i
      rw [hi]
    rw [htapes]
    generalize tapes 0 = entry
    rcases entry with ⟨write, dm⟩
    cases di <;> cases dm <;> rcases write with _ | (_ | (_ | _)) <;>
      rcases out with _ | (_ | _) <;> cases next <;> rfl
  rw [hr]
  simp [pairEncode, timedCut_Header, universalRecords, timedCut_Actions,
    List.flatMap_map, List.append_assoc]

/-- Decompose the canonical table at the action selected by state and reads.

**Proof sketch.** Split the increasing state enumeration at the source state,
and split its nine-entry list at the read offset. The two prefixes are exactly
the groups and records traversed by the controller. -/
private lemma timedCut_lookup_parts (M : CodeTM) (q : Fin (M.numStates + 1))
    (inp work : Option Bool) :
    ∃ (groups : List (List (Action 1 Bool (Fin (M.numStates + 1)))))
      (before : List (Action 1 Bool (Fin (M.numStates + 1)))) (after : List Bool),
      groups.length = q.val ∧ (∀ g ∈ groups, g.length = 9) ∧
      before.length = (universalRecordIndex inp work).val ∧
      M.serialize = timedCut_Header M ++
        groups.flatMap (fun g => g.flatMap universalRecordBits) ++
        before.flatMap universalRecordBits ++
        universalRecordBits (M.tm.tr q inp (fun _ => work)) ++ after := by
  let states := List.finRange (M.numStates + 1)
  let index := universalRecordIndex inp work
  let actions := timedCut_Actions M q
  have hq : q.val < states.length := by simpa [states] using q.isLt
  have hi : index.val < actions.length := by
    rw [(timedCut_Actions_lookup M q inp work).1]
    exact index.isLt
  have hs : states = states.take q.val ++ q :: states.drop (q.val + 1) := by
    have h := List.take_append_drop q.val states
    rw [List.drop_eq_getElem_cons hq] at h
    simpa [states] using h.symm
  have ha : actions = actions.take index.val ++
      M.tm.tr q inp (fun _ => work) :: actions.drop (index.val + 1) := by
    have h := List.take_append_drop index.val actions
    rw [List.drop_eq_getElem_cons hi, (timedCut_Actions_lookup M q inp work).2] at h
    exact h.symm
  refine ⟨(states.take q.val).map (timedCut_Actions M), actions.take index.val,
    (actions.drop (index.val + 1)).flatMap universalRecordBits ++
      ((states.drop (q.val + 1)).map (timedCut_Actions M)).flatMap
        (fun g => g.flatMap universalRecordBits), ?_, ?_, ?_, ?_⟩
  · simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hq)]
  · intro g hg
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hg
    exact (timedCut_Actions_lookup M s none none).1
  · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    rfl
  · rw [timedCut_serialization_actions]
    change timedCut_Header M ++ (states.map (timedCut_Actions M)).flatMap _ = _
    conv_lhs => rw [hs, List.map_append, List.map_cons, List.flatMap_append,
      List.flatMap_cons]
    change timedCut_Header M ++ (_ ++ (actions.flatMap universalRecordBits ++ _)) = _
    conv_lhs => rw [ha]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- Decoding the four fixed pairs recovers the source action fields. -/
private lemma timedCut_ActionBits_decode {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    universalSign (universalActionBits a 0) (universalActionBits a 1) = a.inputTape ∧
    universalWrite (universalActionBits a 2) (universalActionBits a 3) = (a.workTapes 0).1 ∧
    universalSign (universalActionBits a 4) (universalActionBits a 5) = (a.workTapes 0).2 ∧
    (if universalActionBits a 6 then some (universalActionBits a 7) else none) = a.output := by
  simp only [universalActionBits]
  constructor
  · cases a.inputTape <;> rfl
  constructor
  · rcases (a.workTapes 0).1 with _ | (_ | (_ | _)) <;> rfl
  constructor
  · cases (a.workTapes 0).2 <;> rfl
  · rcases a.output with _ | (_ | _) <;> rfl


/-- Select a record by destructive state counting and the bounded read offset.

**Proof sketch.** Skip the preceding state groups while erasing the unary state.
Rewind the erased state tape to one, then skip the read-offset prefix. An offset
of zero enters the action reader directly. The table scans cost their total
serialized length, and state administration costs twice the old index plus three. -/
private lemma timedCut_select {x : List Bool} {n : ℕ}
    (base : Cfg 4 Bool UniversalControl x) (index : Fin 9) (table : List Bool)
    (groups : List (List (Action 1 Bool (Fin (n + 1)))))
    (hg : ∀ g ∈ groups, g.length = 9)
    (before : List (Action 1 Bool (Fin (n + 1)))) (hb : before.length = index.val)
    (l r : List Bool)
    (ht : table = l ++ groups.flatMap (fun g => g.flatMap universalRecordBits) ++
      before.flatMap universalRecordBits ++ r) :
    timedCutInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length
        (universalStateTape groups.length) 1)
      (2 * groups.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length +
        (before.flatMap universalRecordBits).length + 3) =
    universalEvalCfg base (.readAction 0 (fun _ => false)) table
      (l.length + (groups.flatMap (fun g => g.flatMap universalRecordBits)).length +
        (before.flatMap universalRecordBits).length) (universalStateTape 0) 1 := by
  let pg := groups.flatMap (fun g => g.flatMap universalRecordBits)
  let pb := before.flatMap universalRecordBits
  let next := if h : index.val = 0 then UniversalControl.readAction 0 (fun _ => false)
    else .skipFixed none ⟨index.val - 1, by omega⟩ 0
  have hgroup := timedCut_skip_groups base index table groups hg l (pb ++ r) 0
    (by simpa [pg, pb, List.append_assoc] using ht)
  have hgr : timedCutInterpreter.runFrom
      (universalEvalCfg base (.group index) table l.length (universalStateTape groups.length) 1)
      (groups.length + pg.length + 1) =
    universalEvalCfg base (.rewindState (some index)) table (l.length + pg.length)
      (universalStateTape 0) (groups.length + 1) := by
    simpa only [Nat.cast_zero, zero_add, universalStateWindow_empty,
      universalStateWindow_zero] using hgroup
  have hrew := timedCut_state_rewind base (.rewindState (some index)) next table
    (l.length + pg.length) (universalStateTape 0)
    (universalStateTape_marker 0).1 (universalStateTape_marker 0).2
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h, next])
    (by intro inp work h; simp [timedCutInterpreter, universalInterpreter, h]) (groups.length + 1)
  have hrw : timedCutInterpreter.runFrom
      (universalEvalCfg base (.rewindState (some index)) table (l.length + pg.length)
        (universalStateTape 0) (groups.length + 1)) (groups.length + 2) =
    universalEvalCfg base next table (l.length + pg.length) (universalStateTape 0) 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hrew
  have hskip : timedCutInterpreter.runFrom
      (universalEvalCfg base next table (l.length + pg.length) (universalStateTape 0) 1)
      pb.length = universalEvalCfg base (.readAction 0 (fun _ => false)) table
        (l.length + pg.length + pb.length) (universalStateTape 0) 1 := by
    by_cases hi : index.val = 0
    · have hz : before = [] := List.length_eq_zero_iff.mp (hb.trans hi)
      simp [next, hi, pb, hz]
    · have hh := timedCut_skip_records base none table (universalStateTape 0) 1
        before (l ++ pg) r ⟨index.val - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
        (by simpa [pg, pb, List.append_assoc] using ht)
      simpa only [next, dif_neg hi, universalSkipDone, List.length_append, Nat.cast_add]
        using hh
  change timedCutInterpreter.runFrom _ (2 * groups.length + pg.length + pb.length + 3) = _
  rw [show 2 * groups.length + pg.length + pb.length + 3 =
      (groups.length + pg.length + 1) + (groups.length + 2) + pb.length by omega,
    MultiTapeTM.runFrom_add _ ((groups.length + pg.length + 1) + (groups.length + 2)) pb.length,
    MultiTapeTM.runFrom_add _ (groups.length + pg.length + 1) (groups.length + 2),
    hgr, hrw, hskip]

/-- Concatenate two configuration equalities without unfolding either run. -/
private lemma timedCut_run_join {k : ℕ} {Q : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool Q) {a b c : Cfg k Bool Q x} {s t : ℕ}
    (hs : tm.runFrom a s = b) (ht : tm.runFrom b t = c) :
    tm.runFrom a (s + t) = c := by
  rw [MultiTapeTM.runFrom_add, hs, ht]


/-- Applying the decoded record commutes with the complete source checkpoint.

**Proof sketch.** Decode the four fixed pairs. The virtual-input movement lemma
supplies both the physical head equality and the marker-head equality. Optional
writes and emissions then agree field by field; the newly installed unary state
is precisely the successor representation, including the halting case. -/
private lemma timed_apply_record (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (oldp p : ℕ)
    (a : Action 1 Bool (Fin (M.numStates + 1))) :
    universalInterpreter.step
      (universalEvalCfg (universalSimulationCfg M α src oldp)
        (.applyRecord (universalActionBits a) a.state.isNone) M.serialize p
        (universalStateTape ((a.state.map Fin.val).getD 0)) 1) =
    universalSimulationCfg M α (a.apply src) p := by
  let base := universalSimulationCfg M α src oldp
  let cfg := universalEvalCfg base (.applyRecord (universalActionBits a) a.state.isNone)
    M.serialize p (universalStateTape ((a.state.map Fin.val).getD 0)) 1
  let d := virtualMove (decide (bufferTape [true] (src.inputPos.val : ℤ) ≠ some true))
    src.inputSymbol a.inputTape
  have hi : (if base.workTapeSymbols 3 = some true then none else base.inputSymbol) =
      src.inputSymbol := universalInput_read α src
  have hb := timedCut_ActionBits_decode a
  have htr : universalInterpreter.tr
      (.applyRecord (universalActionBits a) a.state.isNone) cfg.inputSymbol cfg.workTapeSymbols =
      (⟨d, universalFour (none, 0) (none, 0) (a.workTapes 0) (none, d), a.output,
        a.state.map (fun _ => .main)⟩ : Action 4 Bool UniversalControl) := by
    have hr3 : cfg.workTapeSymbols 3 = base.workTapeSymbols 3 := rfl
    have hip : cfg.inputSymbol = base.inputSymbol := rfl
    simp only [universalInterpreter, hr3, hip, hi, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    change (⟨d, universalFour (none, 0) (none, 0) (a.workTapes 0) (none, d), a.output,
      if a.state.isNone then none else some .main⟩ : Action 4 Bool UniversalControl) = _
    cases a.state <;> rfl
  change (universalInterpreter.tr _ cfg.inputSymbol cfg.workTapeSymbols).apply cfg = _
  rw [htr]
  have hmove := universalInput_move α src a.inputTape
  refine Cfg.ext rfl hmove.1 ?_ ?_ rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  · funext i
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact add_zero _
    · exact add_zero _
    · rfl
    · exact hmove.2

/-- A live lookup reaches the pending action whose application realizes one source transition.

**Proof sketch.** Read the virtual input and mirrored work symbol, rewind the
table, skip its count and initial-state fields, and select the source record.
Read its eight fixed bits and prepare its successor, stopping immediately before
the source action. Concatenate the exact runs; identify the pending native action
separately. The old cursor, count prefix, and all skipped records are each
bounded by the serialization length; every source state index is below the
number of states. The resulting bound is `3L + 5N + 20`. -/
private lemma timedCut_live_block (M : CodeTM) (α : List Bool) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (p : ℕ)
    (hp : p ≤ M.serialize.length) (hs : src.state ≠ none) :
    ∃ (d p' : ℕ) (ready : Cfg 4 Bool UniversalControl (pairEncode α x)),
      d ≤ 3 * M.serialize.length + 5 * (M.numStates + 1) + 20 ∧
      p' ≤ M.serialize.length ∧
      (∃ bits halt, ready.state = some (.applyRecord bits halt)) ∧
      timedCutInterpreter.runFrom (universalSimulationCfg M α src p) d = ready ∧
      universalInterpreter.step ready = universalSimulationCfg M α (M.tm.step src) p'  := by
  cases hq : src.state with
  | none => exact False.elim (hs hq)
  | some q =>
    let base := universalSimulationCfg M α src p
    let index := universalRecordIndex src.inputSymbol (src.workTapeSymbols 0)
    let a := M.tm.tr q src.inputSymbol (fun _ => src.workTapeSymbols 0)
    obtain ⟨groups, before, after, hglen, hg, hblen, hparts⟩ :=
      timedCut_lookup_parts M q src.inputSymbol (src.workTapeSymbols 0)
    let pg := groups.flatMap (fun g => g.flatMap universalRecordBits)
    let pb := before.flatMap universalRecordBits
    let count := pairEncode (Nat.bits M.numStates) []
    let k := 2 * (Nat.bits M.numStates).length + 2
    let pre := timedCut_Header M ++ pg ++ pb
    let bits := universalActionBits a
    let p' := pre.length + 8 + universalNextOnes a.state
    let selectTime := 2 * q.val + pg.length + pb.length + 3
    let d := 1 + (p + 1) + k + (M.tm.q₀.val + 1) + selectTime + 8 +
      timedCut_NextCost a.state
    have hclen : count.length = k := by
      simpa [count, k] using universal_pair_length (Nat.bits M.numStates) []
    have hhlen : (timedCut_Header M).length = k + M.tm.q₀.val + 1 := by
      change (count ++ List.replicate M.tm.q₀.val true ++ [false]).length = _
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil, hclen]
    have hplen : pre.length = (timedCut_Header M).length + pg.length + pb.length := by
      simp only [pre, List.length_append]
    have ht : M.serialize = pre ++ universalRecordBits a ++ after := by
      simpa only [pre, pg, pb, a, List.append_assoc] using hparts
    have hcfg : base = universalEvalCfg base .main M.serialize p (universalStateTape q.val) 1 := by
      simp only [base, universalSimulationCfg, universalEvalCfg, hq,
        Option.map_some, Option.getD_some]
      rfl
    have hi : (if base.workTapeSymbols 3 = some true then none else base.inputSymbol) =
        src.inputSymbol := universalInput_read α src
    have hmain : timedCutInterpreter.runFrom base 1 =
        universalEvalCfg base (.rewindTable false index) M.serialize (p - 1)
          (universalStateTape q.val) 1 := by
      rw [MultiTapeTM.runFrom_succ_eq_step' (t := 0), MultiTapeTM.runFrom_zero]
      conv_lhs => rw [hcfg]
      have he := timedCut_Eval_step base .main (.rewindTable false index)
        M.serialize p (universalStateTape q.val) 1 .neg 0 none (by
          change universalAdmin (.rewindTable false (universalRecordIndex
            (if base.workTapeSymbols 3 = some true then none else base.inputSymbol)
            (base.workTapeSymbols 2))) .neg = _
          rw [hi]
          rfl)
      simpa only [SignType.neg_eq_neg_one, SignType.coe_neg_one, SignType.coe_zero,
        add_zero, sub_eq_add_neg] using he
    have hrew := timedCut_table_rewind base false index M.serialize
      (universalStateTape q.val) 1 p hp
    have hcount := timedCut_count_run base false index M.serialize
      (universalStateTape q.val) 1 (Nat.bits M.numStates) []
      (List.replicate M.tm.q₀.val true ++ false :: (pg ++ pb ++ universalRecordBits a ++ after))
      (by simpa [timedCut_Header, pairEncode, pg, pb, a, List.append_assoc] using hparts)
    have hc : timedCutInterpreter.runFrom
        (universalEvalCfg base (.countFirst false index) M.serialize 0 (universalStateTape q.val) 1) k =
      universalEvalCfg base (.initialSkip index) M.serialize k (universalStateTape q.val) 1 := by
      simpa only [Bool.false_eq_true, ↓reduceIte, List.length_nil, Nat.cast_zero,
        zero_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcount
    have hinit := timedCut_initial_skip base index M.serialize (universalStateTape q.val) 1
      M.tm.q₀.val count (pg ++ pb ++ universalRecordBits a ++ after)
      (by simpa [count, timedCut_Header, pg, pb, a, List.append_assoc] using hparts)
    have hinit' : timedCutInterpreter.runFrom
        (universalEvalCfg base (.initialSkip index) M.serialize k (universalStateTape q.val) 1)
        (M.tm.q₀.val + 1) =
      universalEvalCfg base (.group index) M.serialize (timedCut_Header M).length
        (universalStateTape q.val) 1 := by
      simpa only [hclen, hhlen, Nat.cast_add, Nat.cast_one] using hinit
    have hselect := timedCut_select base index M.serialize groups hg before hblen
      (timedCut_Header M) (universalRecordBits a ++ after)
      (by simpa only [a, List.append_assoc] using hparts)
    have hsel : timedCutInterpreter.runFrom
        (universalEvalCfg base (.group index) M.serialize (timedCut_Header M).length
          (universalStateTape q.val) 1) selectTime =
      universalEvalCfg base (.readAction 0 (fun _ => false)) M.serialize pre.length
        (universalStateTape 0) 1 := by
      simpa only [hglen, hplen, Nat.cast_add] using hselect
    have hread := timedCut_read_fixed base M.serialize (universalStateTape 0) 1 bits pre
      (List.replicate (universalNextOnes a.state) true ++ false :: after)
      (by simpa [universal_record_shape, bits, List.append_assoc] using ht)
      7 0 (fun _ => false) rfl (by intro i hi; exact False.elim (Nat.not_lt_zero _ hi))
    have hrd : timedCutInterpreter.runFrom
        (universalEvalCfg base (.readAction 0 (fun _ => false)) M.serialize pre.length
          (universalStateTape 0) 1) 8 =
      universalEvalCfg base (.nextState bits) M.serialize (pre.length + 8)
        (universalStateTape 0) 1 := by
      simpa only [Fin.val_zero, Nat.cast_zero, add_zero] using hread
    have hnext := timedCut_prepare_next base M.serialize bits a.state
      (pre ++ List.ofFn bits) after
      (by simpa [universal_record_shape, bits, List.append_assoc] using ht)
    have hn : timedCutInterpreter.runFrom
        (universalEvalCfg base (.nextState bits) M.serialize (pre.length + 8)
          (universalStateTape 0) 1) (timedCut_NextCost a.state) =
      universalEvalCfg base (.applyRecord bits a.state.isNone) M.serialize p'
        (universalStateTape ((a.state.map Fin.val).getD 0)) 1 := by
      simpa only [p', List.length_append, List.length_ofFn, Nat.cast_add, Nat.cast_ofNat] using hnext
    have hrun := timedCut_run_join timedCutInterpreter
      (timedCut_run_join timedCutInterpreter
        (timedCut_run_join timedCutInterpreter
          (timedCut_run_join timedCutInterpreter
            (timedCut_run_join timedCutInterpreter
              (timedCut_run_join timedCutInterpreter hmain hrew) hc) hinit') hsel) hrd) hn
    have hstep : M.tm.step src = a.apply src := by
      have hw : src.workTapeSymbols = fun _ : Fin 1 => src.workTapeSymbols 0 := by
        funext i
        rw [Fin.eq_zero i]
      simp only [MultiTapeTM.step, hq]
      rw [hw]
    have hlength : M.serialize.length = pre.length + 8 +
        universalNextOnes a.state + 1 + after.length := by
      rw [ht, universal_record_shape]
      simp only [List.length_append, List.length_ofFn, List.length_replicate,
        List.length_cons, List.length_nil]
      omega
    have hnextBound : timedCut_NextCost a.state ≤ 2 * (M.numStates + 1) + 4 := by
      cases hnxt : a.state with
      | none => simp [timedCut_NextCost]
      | some q' => have hq' := q'.isLt; simp only [timedCut_NextCost]; omega
    have hqb := q.isLt
    have hq₀b := M.tm.q₀.isLt
    refine ⟨d, p', _, ?_, ?_, ⟨bits, a.state.isNone, rfl⟩, hrun, ?_⟩
    · dsimp only [d, selectTime]
      rw [hplen, hhlen] at hlength
      omega
    · dsimp only [p']; omega
    · rw [hstep]
      exact timed_apply_record M α src p p' a

/-- The physical prefix occupied by the twice-doubled clock and its delimiter. -/
private def timedClockPrefix (bs : List Bool) : List Bool :=
  bs.flatMap (fun b => [b, b, b, b]) ++ [false, false, true, true]

/-- Removing the clock region leaves precisely the original code-first pair. -/
private lemma timed_input_layout (bs α x : List Bool) :
    pairEncode (pairEncode bs α) x = timedClockPrefix bs ++ pairEncode α x := by
  induction bs with
  | nil => simp [pairEncode, timedClockPrefix]
  | cons b bs ih =>
    simpa only [pairEncode, timedClockPrefix, List.flatMap_cons, List.flatMap_append,
      List.cons_append, List.nil_append, List.append_assoc] using congrArg (fun l => b :: b :: b :: b :: l) ih

/-- The clock region has four physical cells per bit plus four delimiter cells. -/
private lemma timedClockPrefix_length (bs : List Bool) :
    (timedClockPrefix bs).length = 4 * bs.length + 4 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [timedClockPrefix, List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons] at *
    omega

/-- Finite control for separating the twice-doubled clock from the doubled code. -/
private inductive TimedPrefixControl where
  | clockFirst | clockSecond (b : Bool) | clockThird (b : Bool)
  | clockFourth (b : Bool) | clockEnd | codeFirst | codeSecond (b : Bool)
  deriving DecidableEq, Fintype

/-- The prefix parser stores only clock bits on its work tape and emits only code
bits. It stops on the outer separator, before reading the input suffix. -/
private def timedPrefixTM : FinTM Bool where
  k := 1
  State := TimedPrefixControl
  tm :=
    { q₀ := .clockFirst
      tr := fun q inp _ => match q with
        | .clockFirst => ⟨.pos, fun _ => (none, 0), none, inp.map .clockSecond⟩
        | .clockSecond b => ⟨.pos, fun _ => (none, 0), none, some (.clockThird b)⟩
        | .clockThird b => ⟨.pos, fun _ => (none, 0), none,
            some (if inp = some b then .clockFourth b else .clockEnd)⟩
        | .clockFourth b => ⟨.pos, fun _ => (some (some b), .pos), none, some .clockFirst⟩
        | .clockEnd => ⟨.pos, fun _ => (none, 0), none, some .codeFirst⟩
        | .codeFirst => ⟨.pos, fun _ => (none, 0), none, inp.map .codeSecond⟩
        | .codeSecond b =>
            if inp = some b then
              ⟨.pos, fun _ => (none, 0), some b, some .codeFirst⟩
            else ⟨.pos, fun _ => (none, 0), none, none⟩ }

/-- Configuration of the prefix parser, with its complete captured clock. -/
private def timedPrefixCfg (bs α x : List Bool) (q : Option TimedPrefixControl)
    (p : Fin ((pairEncode (pairEncode bs α) x).length + 2))
    (clock out : List Bool) : Cfg 1 Bool TimedPrefixControl (pairEncode (pairEncode bs α) x) :=
  ⟨q, p, fun _ => bufferTape clock, fun _ => clock.length, out⟩

/-- Length arithmetic for both nested delimiters. -/
private lemma timed_input_length (bs α x : List Bool) :
    (pairEncode (pairEncode bs α) x).length = 4 * bs.length + 2 * α.length + 6 + x.length := by
  rw [universal_pair_length, universal_pair_length]
  omega

/-- Every cell of a quadrupled clock bit has the same value. -/
private lemma timed_clock_get (bs α x : List Bool) (j r : ℕ)
    (hj : j < bs.length) (hr : r < 4) :
    (pairEncode (pairEncode bs α) x)[4 * j + r]? = some bs[j] := by
  rw [timed_input_layout]
  induction bs generalizing j with
  | nil => simp at hj
  | cons b bs ih =>
    cases j with
    | zero =>
      have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
      rcases h with rfl | rfl | rfl | rfl <;> rfl
    | succ j =>
      have hh := ih j (by simpa using hj)
      simpa only [timedClockPrefix, List.flatMap_cons, List.cons_append, List.nil_append,
        List.getElem?_cons_succ, List.getElem_cons_succ, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm 4 r] using hh

/-- The inner separator is doubled by the outer pairing. -/
private lemma timed_clock_separator (bs α x : List Bool) (r : ℕ) (hr : r < 4) :
    (pairEncode (pairEncode bs α) x)[4 * bs.length + r]? =
      [false, false, true, true][r]? := by
  rw [timed_input_layout]
  induction bs with
  | nil =>
    have h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl <;> rfl
  | cons b bs ih =>
    simpa only [timedClockPrefix, List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 4 r,
      List.getElem?_cons_succ] using ih

/-- A non-writing parser transition advances exactly one physical input cell. -/
private lemma timedPrefix_advance (bs α x clock out : List Bool)
    (q : TimedPrefixControl) (q' : Option TimedPrefixControl) (emit : Option Bool)
    (p : ℕ) (hp : p < (pairEncode (pairEncode bs α) x).length) (b : Bool)
    (hb : (pairEncode (pairEncode bs α) x)[p]? = some b)
    (htr : ∀ ws, timedPrefixTM.tm.tr q (some b) ws =
      ⟨.pos, fun _ => (none, 0), emit, q'⟩) :
    timedPrefixTM.tm.step
      (timedPrefixCfg bs α x (some q) ⟨p + 1, by omega⟩ clock out) =
    timedPrefixCfg bs α x q' ⟨p + 2, by omega⟩ clock (out ++ emit.toList) := by
  have hr : (timedPrefixCfg bs α x (some q) ⟨p + 1, by omega⟩ clock out).inputSymbol =
      some b := (inputSymbol_at _ p (by omega) rfl).trans hb
  change (timedPrefixTM.tm.tr q _ _).apply _ = _
  rw [hr, htr]
  refine Cfg.ext rfl ?_ rfl ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by change p + 1 ≠ (pairEncode (pairEncode bs α) x).length + 1; omega)
  · funext i; exact add_zero _

/-- The fourth cell of a clock bit appends exactly its undoubled value. -/
private lemma timedPrefix_write (bs α x clock : List Bool) (b : Bool)
    (p : ℕ) (hp : p < (pairEncode (pairEncode bs α) x).length) :
    timedPrefixTM.tm.step
      (timedPrefixCfg bs α x (some (.clockFourth b)) ⟨p + 1, by omega⟩ clock []) =
    timedPrefixCfg bs α x (some .clockFirst) ⟨p + 2, by omega⟩ (clock ++ [b]) [] := by
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · exact moveInputPos_pos_of_ne_right _ (by change p + 1 ≠ (pairEncode (pairEncode bs α) x).length + 1; omega)
  · funext i; exact (bufferTape_append clock b).symm
  · funext i
    change (clock.length : ℤ) + 1 = ((clock ++ [b]).length : ℤ)
    simp

/-- Clock extraction consumes four cells and stores one bit per iteration.
The physical suffix and the native output remain untouched.

**Proof sketch.** Induct on the clock prefix already consumed. Four physical copies
of a bit take four transitions, with just one write to the clock tape; concatenate
these runs while preserving the untouched code and input suffix. -/
private lemma timedPrefix_clock (bs α x : List Bool) :
    ∀ j, (hj : j ≤ bs.length) →
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * j) =
    timedPrefixCfg bs α x (some .clockFirst)
      ⟨4 * j + 1, by rw [timed_input_length]; omega⟩ (bs.take j) [] := by
  intro j
  induction j with
  | zero =>
    intro hj
    apply Cfg.ext <;> simp [timedPrefixTM, timedPrefixCfg]
  | succ j ih =>
    intro hj
    have hlen := timed_input_length bs α x
    have hj' : j < bs.length := by omega
    have h0 := timedPrefix_advance bs α x (bs.take j) [] .clockFirst
      (some (.clockSecond bs[j])) none (4 * j) (by omega) bs[j]
      (by simpa using timed_clock_get bs α x j 0 hj' (by omega)) (by intro ws; rfl)
    have h1 := timedPrefix_advance bs α x (bs.take j) [] (.clockSecond bs[j])
      (some (.clockThird bs[j])) none (4 * j + 1) (by omega) bs[j]
      (timed_clock_get bs α x j 1 hj' (by omega)) (by intro ws; rfl)
    have h2 := timedPrefix_advance bs α x (bs.take j) [] (.clockThird bs[j])
      (some (.clockFourth bs[j])) none (4 * j + 2) (by omega) bs[j]
      (timed_clock_get bs α x j 2 hj' (by omega)) (by intro ws; simp [timedPrefixTM])
    have h3 := timedPrefix_write bs α x (bs.take j) bs[j] (4 * j + 3) (by omega)
    simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1 h2 h3
    conv_lhs => rw [show 4 * (j + 1) = 4 * j + 1 + 1 + 1 + 1 by omega]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega), h0]
    rw [h1, h2, h3]
    have ht : bs.take j ++ [bs[j]] = bs.take (j + 1) := by
      rw [List.take_succ, List.getElem?_eq_getElem hj']
      rfl
    rw [ht]
    congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- The four physical delimiter cells transfer from clock capture to code extraction.

**Proof sketch.** Read the four separator cells in sequence. The first two zeros
are recognized as the start of the separator when the following one disagrees;
the fourth cell completes the switch to code extraction without writing a clock bit. -/
private lemma timedPrefix_clock_end (bs α x : List Bool) :
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 4) =
    timedPrefixCfg bs α x (some .codeFirst)
      ⟨4 * bs.length + 5, by rw [timed_input_length]; omega⟩ bs [] := by
  have hlen := timed_input_length bs α x
  have h0 := timedPrefix_advance bs α x bs [] .clockFirst (some (.clockSecond false)) none
    (4 * bs.length) (by omega) false
    (by simpa using timed_clock_separator bs α x 0 (by omega)) (by intro ws; rfl)
  have h1 := timedPrefix_advance bs α x bs [] (.clockSecond false) (some (.clockThird false)) none
    (4 * bs.length + 1) (by omega) false
    (timed_clock_separator bs α x 1 (by omega)) (by intro ws; rfl)
  have h2 := timedPrefix_advance bs α x bs [] (.clockThird false) (some .clockEnd) none
    (4 * bs.length + 2) (by omega) true
    (timed_clock_separator bs α x 2 (by omega)) (by intro ws; rfl)
  have h3 := timedPrefix_advance bs α x bs [] .clockEnd (some .codeFirst) none
    (4 * bs.length + 3) (by omega) true
    (timed_clock_separator bs α x 3 (by omega)) (by intro ws; rfl)
  simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1 h2 h3
  conv_lhs => rw [show 4 * bs.length + 4 = 4 * bs.length + 1 + 1 + 1 + 1 by omega]
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    timedPrefix_clock bs α x bs.length (le_refl _), List.take_length, h0]
  rw [h1, h2, h3]

/-- Suffix indexing after the complete clock prefix. -/
private lemma timed_code_get (bs α x : List Bool) (j : ℕ) :
    (pairEncode (pairEncode bs α) x)[4 * bs.length + 4 + j]? = (pairEncode α x)[j]? := by
  rw [timed_input_layout, ← timedClockPrefix_length,
    List.getElem?_append_right (by omega)]
  simp

/-- An aligned pair in the code region contains the corresponding code bit. -/
private lemma timed_pair_get (α x : List Bool) (j : ℕ) (hj : j < α.length) :
    (pairEncode α x)[2 * j]? = some α[j] ∧
      (pairEncode α x)[2 * j + 1]? = some α[j] := by
  induction α generalizing j with
  | nil => simp at hj
  | cons b α ih =>
    cases j with
    | zero => simp [pairEncode]
    | succ j =>
      simpa only [pairEncode, List.flatMap_cons, List.cons_append, List.nil_append,
        Nat.mul_add, Nat.mul_one, Nat.add_assoc, List.getElem?_cons_succ,
        List.getElem_cons_succ] using ih j (by simpa using hj)

/-- The aligned separator immediately follows the doubled code. -/
private lemma timed_pair_separator (α x : List Bool) :
    (pairEncode α x)[2 * α.length]? = some false ∧
      (pairEncode α x)[2 * α.length + 1]? = some true := by
  induction α with
  | nil => simp [pairEncode]
  | cons b α ih =>
    simpa only [pairEncode, List.flatMap_cons, List.cons_append, List.nil_append,
      List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc,
      List.getElem?_cons_succ] using ih

/-- Code extraction emits the undoubled code prefix and preserves the stored clock.

**Proof sketch.** Induct on the code prefix. Each equal pair emits one code bit and
advances two input cells. The unequal terminal pair halts the parser without an
emission, leaving the saved clock unchanged. -/
private lemma timedPrefix_code (bs α x : List Bool) :
    ∀ j, (hj : j ≤ α.length) →
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 4 + 2 * j) =
    timedPrefixCfg bs α x (some .codeFirst)
      ⟨4 * bs.length + 4 + 2 * j + 1, by rw [timed_input_length]; omega⟩ bs (α.take j) := by
  intro j
  induction j with
  | zero => intro hj; simpa only [Nat.mul_zero, Nat.add_zero, List.take_zero] using timedPrefix_clock_end bs α x
  | succ j ih =>
    intro hj
    have hlen := timed_input_length bs α x
    have hj' : j < α.length := by omega
    have hr := timed_pair_get α x j hj'
    have h0 := timedPrefix_advance bs α x bs (α.take j) .codeFirst
      (some (.codeSecond α[j])) none (4 * bs.length + 4 + 2 * j) (by omega) α[j]
      (by rw [timed_code_get]; exact hr.1) (by intro ws; rfl)
    have h1 := timedPrefix_advance bs α x bs (α.take j) (.codeSecond α[j])
      (some .codeFirst) (some α[j]) (4 * bs.length + 4 + 2 * j + 1) (by omega) α[j]
      (by rw [Nat.add_assoc _ (2 * j) 1, timed_code_get]; exact hr.2)
      (by intro ws; simp [timedPrefixTM])
    simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1
    conv_lhs => rw [show 4 * bs.length + 4 + 2 * (j + 1) =
      4 * bs.length + 4 + 2 * j + 1 + 1 by omega]
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    rw [h0, h1]
    have ht : α.take j ++ [α[j]] = α.take (j + 1) := by
      rw [List.take_succ, List.getElem?_eq_getElem hj']; rfl
    simp only [Option.toList_some, ht]
    congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- Exact completed parser configuration, including the clock tape and parked input.
Both delimiters are consumed, including when the clock and code are empty. -/
private lemma timedPrefix_complete (bs α x : List Bool) :
    timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 2 * α.length + 6) =
    timedPrefixCfg bs α x none
      ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩ bs α := by
  have hlen := timed_input_length bs α x
  have hr := timed_pair_separator α x
  have h0 := timedPrefix_advance bs α x bs α .codeFirst (some (.codeSecond false)) none
    (4 * bs.length + 4 + 2 * α.length) (by omega) false
    (by rw [timed_code_get]; exact hr.1) (by intro ws; rfl)
  have h1 := timedPrefix_advance bs α x bs α (.codeSecond false) none none
    (4 * bs.length + 4 + 2 * α.length + 1) (by omega) true
    (by rw [Nat.add_assoc _ (2 * α.length) 1, timed_code_get]; exact hr.2)
    (by intro ws; rfl)
  simp only [Nat.add_assoc, Nat.reduceAdd, Option.toList_none, List.append_nil] at h0 h1
  conv_lhs => rw [show 4 * bs.length + 2 * α.length + 6 =
      4 * bs.length + 4 + 2 * α.length + 1 + 1 by omega]
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    timedPrefix_code bs α x α.length (le_refl _), List.take_length]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [h0, h1]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- Little-endian value of a fixed-width clock word. -/
private def timedValue : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (timedValue bs)

/-- Canonical clock words represent their given deadline. -/
private lemma timedValue_bits (t : ℕ) : timedValue t.bits = t := by
  induction t using Nat.binaryRec' with
  | zero => simp [timedValue]
  | bit b t ht ih => rw [Nat.bits_append_bit t b ht]; exact congrArg (Nat.bit b) ih

/-- Fixed-width binary subtraction, carrying an underflow flag. -/
private def timedBorrow : Bool → List Bool → Bool × List Bool
  | carry, [] => (carry, [])
  | carry, b :: bs =>
    let rest := timedBorrow (carry && !b) bs
    (rest.1, Bool.xor b carry :: rest.2)

/-- A cleared borrow leaves the remaining word unchanged. -/
private lemma timedBorrow_false (bs : List Bool) : timedBorrow false bs = (false, bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [timedBorrow, ih]

/-- Subtraction preserves the allocated word width. -/
private lemma timedBorrow_length (carry : Bool) (bs : List Bool) :
    (timedBorrow carry bs).2.length = bs.length := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [timedBorrow, List.length_cons, ih]

/-- Borrow underflow detects exactly a zero remaining budget. -/
private lemma timedBorrow_underflow (bs : List Bool) :
    (timedBorrow true bs).1 = true ↔ timedValue bs = 0 := by
  induction bs with
  | nil => simp [timedBorrow, timedValue]
  | cons b bs ih =>
    cases b <;> simp [timedBorrow, timedBorrow_false, timedValue, Nat.bit_val, ih]

/-- A successful borrow removes exactly one transition from the budget. -/
private lemma timedBorrow_value (bs : List Bool) (h : 0 < timedValue bs) :
    timedValue (timedBorrow true bs).2 + 1 = timedValue bs := by
  induction bs with
  | nil => simp [timedValue] at h
  | cons b bs ih =>
    cases b with
    | false =>
      have ht : 0 < timedValue bs := by simpa [timedValue, Nat.bit_val] using h
      have hb := ih ht
      change Nat.bit true (timedValue (timedBorrow true bs).2) + 1 = Nat.bit false (timedValue bs)
      simp only [Nat.bit_val]
      change (2 * timedValue (timedBorrow true bs).2 + 1) + 1 = 2 * timedValue bs + 0
      omega
    | true => simp [timedBorrow, timedBorrow_false, timedValue, Nat.bit_val]

/-- Extra phases retain a selected action while its clock is serviced. -/
private inductive TimedControl where
  | work (q : UniversalControl)
  | clockBack (bits : Fin 8 → Bool) (halt : Bool)
  | borrow (bits : Fin 8 → Bool) (halt carry : Bool)
  | execute (bits : Fin 8 → Bool) (halt : Bool)
  | emitStart | emitBack | flush
  deriving DecidableEq, Fintype

/-- Four audited interpreter lanes followed by the clock and output buffer. -/
private def timedSix {A : Type} (core : Fin 4 → A) (clock buffer : A) : Fin 6 → A :=
  fun i => if i = 0 then core 0 else if i = 1 then core 1 else
    if i = 2 then core 2 else if i = 3 then core 3 else if i = 4 then clock else buffer

/-- Lift an interpreter action while buffering its emission and intercepting halt. -/
private def timedAction (a : Action 4 Bool UniversalControl) : Action 6 Bool TimedControl :=
  ⟨a.inputTape, timedSix a.workTapes (none, 0)
    (a.output.map some, if a.output = none then 0 else .pos), none,
    some ((a.state.map TimedControl.work).getD .emitStart)⟩

/-- A clock-only or output-buffer-only administrative action. -/
private def timedAdmin (q : Option TimedControl)
    (clock buffer : Option (Option Bool) × SignType) (emit : Option Bool := none) :
    Action 6 Bool TimedControl :=
  ⟨0, timedSix (fun _ => (none, 0)) clock buffer, emit, q⟩

/-- Finite timed interpreter. A selected action is applied only after a successful
borrow. Its halting transition remains live until the success tag and buffered
emissions have been flushed. A failed borrow emits only the timeout tag. -/
private def timedInterpreter : MultiTapeTM 6 Bool TimedControl where
  q₀ := .work .start
  tr := fun q inp ws => match q with
    | .work (.applyRecord bits halt) =>
        timedAdmin (some (.clockBack bits halt)) (none, .neg) (none, 0)
    | .work q => timedAction (universalInterpreter.tr q inp (fun i => ws (i.castAdd 2)))
    | .clockBack bits halt =>
        if ws 4 = none then timedAdmin (some (.borrow bits halt true)) (none, .pos) (none, 0)
        else timedAdmin (some (.clockBack bits halt)) (none, .neg) (none, 0)
    | .borrow bits halt carry => match ws 4 with
        | some b => timedAdmin (some (.borrow bits halt (carry && !b)))
            (some (some (Bool.xor b carry)), .pos) (none, 0)
        | none => if carry then timedAdmin none (none, 0) (none, 0) (some false)
            else timedAdmin (some (.execute bits halt)) (none, 0) (none, 0)
    | .execute bits halt =>
        timedAction (universalInterpreter.tr (.applyRecord bits halt) inp (fun i => ws (i.castAdd 2)))
    | .emitStart => timedAdmin (some .emitBack) (none, 0) (none, .neg)
    | .emitBack =>
        if ws 5 = none then timedAdmin (some .flush) (none, 0) (none, .pos) (some true)
        else timedAdmin (some .emitBack) (none, 0) (none, .neg)
    | .flush => match ws 5 with
        | some b => timedAdmin (some .flush) (none, 0) (none, .pos) (some b)
        | none => timedAdmin none (none, 0) (none, 0)

/-- The original output is represented on the buffer tape; no native emission
has occurred in a simulated checkpoint or during a table lookup. -/
private def timedLift {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) : Cfg 6 Bool TimedControl x :=
  ⟨some ((cfg.state.map TimedControl.work).getD .emitStart), cfg.inputPos,
    timedSix cfg.workTapes (bufferTape clock) (bufferTape cfg.output),
    timedSix cfg.workTapePos clock.length cfg.output.length, []⟩

/-- A non-record state is unaffected by the stopped-interpreter modification. -/
private lemma timedCut_regular (q : UniversalControl)
    (hq : ∀ bits halt, q ≠ .applyRecord bits halt) (inp : Option Bool)
    (ws : Fin 4 → Option Bool) :
    timedCutInterpreter.tr q inp ws = universalInterpreter.tr q inp ws := by
  cases q <;> first | rfl | exact (hq _ _ rfl).elim

/-- A live endpoint of the stopped interpreter excludes every earlier stop.
The same absorption argument also excludes earlier native halts. -/
private lemma timedCut_live_before {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    {s t : ℕ} (hst : s ≤ t) (ht : (timedCutInterpreter.runFrom cfg t).state ≠ none) :
    (timedCutInterpreter.runFrom cfg s).state ≠ none := by
  intro hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs] at ht
  exact ht hs

/-- Every transition strictly before a live endpoint avoids record application. -/
private lemma timedCut_no_record {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    {s t : ℕ} (hst : s < t) (ht : (timedCutInterpreter.runFrom cfg t).state ≠ none) :
    ∀ bits halt, (timedCutInterpreter.runFrom cfg s).state ≠ some (.applyRecord bits halt) := by
  intro bits halt hs
  have hl := timedCut_live_before cfg (show s + 1 ≤ t by omega) ht
  apply hl
  rw [MultiTapeTM.runFrom_succ_eq_step']
  simp only [MultiTapeTM.step, hs, timedCutInterpreter, Action.apply]

/-- The six lanes expose their four source reads and two auxiliary reads. -/
private lemma timedSix_core {A : Type} (a : Fin 4 → A) (b c : A) (i : Fin 4) :
    timedSix a b c (i.castAdd 2) = a i := by fin_cases i <;> rfl

/-- Applying a lifted source action captures even an emission on its halt transition. -/
private lemma timedAction_apply {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) (a : Action 4 Bool UniversalControl) :
    (timedAction a).apply (timedLift cfg clock) = timedLift (a.apply cfg) clock := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    fin_cases i <;> cases ho : a.output <;>
      simp [timedAction, timedLift, timedSix, Action.apply, ho, bufferTape_append]
  · funext i
    fin_cases i <;> cases ho : a.output <;>
      simp [timedAction, timedLift, timedSix, Action.apply, ho]

/-- Every ordinary interpreter step replays in one physical timed-machine step.

**Proof sketch.** Exclude the pending-action state, so both controllers select
the same native action. The action-lifting identity preserves the four simulated
tapes, keeps the clock fixed, and captures any emission on the buffer. -/
private lemma timed_regular_step {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) (hs : cfg.state ≠ none)
    (hq : ∀ bits halt, cfg.state ≠ some (.applyRecord bits halt)) :
    timedInterpreter.step (timedLift cfg clock) = timedLift (timedCutInterpreter.step cfg) clock := by
  cases he : cfg.state with
  | none => exact (hs he).elim
  | some q =>
    have hq' : ∀ bits halt, q ≠ .applyRecord bits halt := by
      intro bits halt hh; apply hq bits halt; simpa [hh] using he
    have hr : (fun i => (timedLift cfg clock).workTapeSymbols (i.castAdd 2)) =
        cfg.workTapeSymbols := by
      funext i; fin_cases i <;> rfl
    have hi : (timedLift cfg clock).inputSymbol = cfg.inputSymbol := rfl
    have htr : timedInterpreter.tr (.work q) (timedLift cfg clock).inputSymbol
        (timedLift cfg clock).workTapeSymbols =
        timedAction (universalInterpreter.tr q cfg.inputSymbol cfg.workTapeSymbols) := by
      cases q <;> first
        | exact (hq' _ _ rfl).elim
        | simp only [timedInterpreter, hr, hi]
    have hstate : (timedLift cfg clock).state = some (.work q) := by simp [timedLift, he]
    conv_lhs => unfold MultiTapeTM.step; rw [hstate]; dsimp only
    rw [htr, timedAction_apply]
    simp only [MultiTapeTM.step, he, timedCut_regular q hq']

/-- A stopped lookup with a live endpoint can be replayed unchanged. No countdown
or output phase is visited in its interior. -/
private lemma timed_replay {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (clock : List Bool) (t : ℕ) (ht : (timedCutInterpreter.runFrom cfg t).state ≠ none) :
    timedInterpreter.runFrom (timedLift cfg clock) t =
      timedLift (timedCutInterpreter.runFrom cfg t) clock := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (timedCut_live_before cfg (by omega) ht),
      timed_regular_step _ clock (timedCut_live_before cfg (by omega) ht)
        (timedCut_no_record cfg (by omega) ht), MultiTapeTM.runFrom_succ_eq_step']

/-- A single active tape lane, with every inactive tape taken from a base
configuration. This supports exact setup transductions in a multi-tape machine. -/
private def timed_laneCfg {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S)
    (z : ℤ) (l r : List (Option A)) : Cfg k A S x :=
  ⟨q, base.inputPos, Function.update base.workTapes lane (FinTM.sweepTape z l r),
    Function.update base.workTapePos lane z, base.output⟩

/-- An action that writes and moves just one lane, leaving input and output
stationary. -/
private def timed_laneAction {A S : Type} {k : ℕ} (lane : Fin k) (q : S)
    (s : Option A) (d : SignType) : Action k A S :=
  ⟨0, Function.update (fun _ => (none, 0)) lane (some s, d), none, some q⟩

/-- The active lane reads the first unprocessed zipper entry. -/
private lemma timed_laneCfg_read {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S)
    (z : ℤ) (l r : List (Option A)) :
    (timed_laneCfg base lane q z l r).workTapeSymbols lane = r.head?.join := by
  simp only [timed_laneCfg, Cfg.workTapeSymbols, Function.update_self, FinTM.sweepTape_read]

/-- The right-moving zipper identity lifts to one lane of any machine. -/
private lemma timed_laneCfg_right {A S : Type} {k : ℕ} {x : List A}
    (base : Cfg k A S x) (lane : Fin k) (q : Option S) (q' : S)
    (z : ℤ) (l r : List (Option A)) (a b : Option A) :
    (timed_laneAction lane q' b .pos).apply (timed_laneCfg base lane q z l (a :: r)) =
      timed_laneCfg base lane (some q') (z + 1) (b :: l) r := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · funext i
    by_cases hi : i = lane
    · subst i
      simp only [timed_laneAction, timed_laneCfg, Action.apply, Function.update_self]
      exact FinTM.sweepTape_right z l r a b
    · simp only [timed_laneAction, timed_laneCfg, Action.apply, Function.update_of_ne hi]
  · funext i
    by_cases hi : i = lane
    · subst i
      simp [timed_laneAction, timed_laneCfg]
    · simp [timed_laneAction, timed_laneCfg, hi]
  · exact List.append_nil _

/-- A finite forward transduction on one lane has exact cost equal to its word
length, without changing inactive tapes.
**Proof sketch.** The first entry supplies the local transition hypothesis.
One write-and-right step moves it into the left zipper stack, and induction
processes the remaining word. The full resulting configuration is retained. -/
private lemma timed_lane_run {A S R C : Type} {k : ℕ} {x : List A}
    (tm : MultiTapeTM k A S) (lane : Fin k)
    (state : R → S) (symbol : C → A) (visit : R → C → R × C)
    (htr : ∀ s c inp ws, ws lane = some (symbol c) →
      tm.tr (state s) inp ws = timed_laneAction lane (state (visit s c).1)
        (some (symbol (visit s c).2)) .pos)
    (base : Cfg k A S x) (as : List C) (s : R)
    (z : ℤ) (l r : List (Option A)) :
    tm.runFrom (timed_laneCfg base lane (some (state s)) z l
      (as.map (fun c => some (symbol c)) ++ r)) as.length =
    timed_laneCfg base lane (some (state (FinTM.sweepFold visit s as).1)) (z + as.length)
      (((FinTM.sweepFold visit s as).2.map (fun c => some (symbol c))).reverse ++ l) r := by
  induction as generalizing s z l with
  | nil => simp only [List.map_nil, List.nil_append, List.length_nil, MultiTapeTM.runFrom_zero,
      FinTM.sweepFold, Int.natCast_zero, add_zero, List.reverse_nil]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have hr : (timed_laneCfg base lane (some (state s)) z l
        (some (symbol a) :: (as.map (fun c => some (symbol c)) ++ r))).workTapeSymbols lane =
        some (symbol a) := timed_laneCfg_read _ _ _ _ _ _
    change tm.runFrom ((tm.tr (state s) _ _).apply _) as.length = _
    rw [htr s a _ _ hr, timed_laneCfg_right, ih]
    simp only [FinTM.sweepFold, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, Int.natCast_add, Int.natCast_one]
    congr 1
    omega


/-- A focused clock write agrees with the generic one-lane transducer action. -/
private lemma timedAdmin_clock (q : TimedControl) (b : Option Bool) (d : SignType) :
    timedAdmin (some q) (some b, d) (none, 0) = timed_laneAction (4 : Fin 6) q b d := by
  unfold timedAdmin timed_laneAction
  congr 1
  funext i
  fin_cases i <;> rfl

/-- A borrow sweep is the same local fold as the fixed-width arithmetic function. -/
private lemma timedBorrow_fold (carry : Bool) (bs : List Bool) :
    sweepFold (fun carry b => (carry && !b, Bool.xor b carry)) carry bs = timedBorrow carry bs := by
  induction bs generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [sweepFold, timedBorrow, ih]

/-- Exact borrow transduction; neither source tapes nor buffered output are touched. -/
private lemma timed_borrow_run {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (bits : Fin 8 → Bool) (halt carry : Bool) (bs : List Bool)
    (z : ℤ) (l r : List (Option Bool)) :
    timedInterpreter.runFrom
      (timed_laneCfg base 4 (some (.borrow bits halt carry)) z l (bs.map some ++ r)) bs.length =
    timed_laneCfg base 4 (some (.borrow bits halt (timedBorrow carry bs).1))
      (z + bs.length) (((timedBorrow carry bs).2.map some).reverse ++ l) r := by
  have h := timed_lane_run timedInterpreter (4 : Fin 6) (TimedControl.borrow bits halt)
    (fun b : Bool => b) (fun carry b => (carry && !b, Bool.xor b carry))
    (by
      intro carry b inp ws hw
      simp only [timedInterpreter, hw]
      exact timedAdmin_clock _ _ _) base bs carry z l r
  simpa only [timedBorrow_fold] using h

/-- Moving the frontier of a finite zipper does not change its tape. -/
private lemma timed_sweep_shift (z : ℤ) (l w r : List (Option Bool)) :
    sweepTape z l (w ++ r) = sweepTape (z + w.length) (w.reverse ++ l) r := by
  induction w generalizing z l with
  | nil => simp
  | cons a w ih =>
    have hs : Function.update (FinTM.sweepTape z l (a :: (w ++ r))) z a =
        FinTM.sweepTape z l (a :: (w ++ r)) := by
      funext p
      by_cases hp : p = z
      · subst p
        simp [FinTM.sweepTape_read]
      · exact Function.update_of_ne hp _ _
    have hm := FinTM.sweepTape_right z l (w ++ r) a a
    rw [hs] at hm
    simp only [List.cons_append, List.length_cons, List.reverse_cons]
    rw [hm, ih]
    simp only [List.append_assoc, List.singleton_append]
    congr 1
    omega

/-- A Boolean buffer is a zipper with an empty left stack. -/
private lemma timed_buffer_zipper (bs : List Bool) :
    bufferTape bs = sweepTape 0 [] (bs.map some) := by
  funext z
  by_cases h : 0 ≤ z
  · simp only [bufferTape, if_pos h, sweepTape, not_lt.mpr h, ↓reduceIte, sub_zero,
      List.getElem?_map]
    cases bs[z.toNat]? <;> rfl
  · simp [bufferTape, sweepTape, h, show z < 0 by omega]

/-- At the right blank the full buffer occupies the reversed left zipper stack. -/
private lemma timed_buffer_zipper_end (bs : List Bool) :
    bufferTape bs = sweepTape bs.length (bs.map some).reverse [] := by
  rw [timed_buffer_zipper]
  have h := timed_sweep_shift 0 [] (bs.map some) []
  simpa using h

/-- A clock phase overrides only the clock lane and the finite control. -/
private def timedClockCfg {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (q : TimedControl) (bs : List Bool) (p : ℤ) : Cfg 6 Bool TimedControl x :=
  { base with
    state := some q
    workTapes := Function.update base.workTapes 4 (bufferTape bs)
    workTapePos := Function.update base.workTapePos 4 p }

/-- A stationary-input clock action has an explicit one-lane effect. -/
private lemma timedClock_step {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (q q' : TimedControl) (bs : List Bool) (p : ℤ) (d : SignType)
    (htr : ∀ inp ws, ws 4 = bufferTape bs p →
      timedInterpreter.tr q inp ws = timedAdmin (some q') (none, d) (none, 0)) :
    timedInterpreter.step (timedClockCfg base q bs p) = timedClockCfg base q' bs (p + d) := by
  change (timedInterpreter.tr q _ _).apply _ = _
  rw [htr _ _ (by simp [timedClockCfg, Cfg.workTapeSymbols])]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ (List.append_nil _)
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [timedAdmin, timedSix, timedClockCfg, Action.apply]

/-- Rewind from the last clock bit to the left blank, then enter the borrow pass. -/
private lemma timed_clock_back {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (bits : Fin 8 → Bool) (halt : Bool) (bs : List Bool) :
    ∀ j, j ≤ bs.length →
    timedInterpreter.runFrom (timedClockCfg base (.clockBack bits halt) bs (j - 1)) (j + 1) =
      timedClockCfg base (.borrow bits halt true) bs 0 := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have h := timedClock_step base (.clockBack bits halt) (.borrow bits halt true) bs (-1) .pos
      (by intro inp ws hw; simp [timedInterpreter, hw])
    simpa using h
  | succ j ih =>
    intro hj
    have hr : bufferTape bs (j : ℤ) = some bs[j] := by
      rw [bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have h := timedClock_step base (.clockBack bits halt) (.clockBack bits halt) bs j .neg
      (by intro inp ws hw; simp [timedInterpreter, hw, hr])
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = j by omega, h]
    simpa using ih (by omega)

/-- Borrowing rewrites the clock in exactly one pass and preserves its width. -/
private lemma timed_clock_borrow {x : List Bool} (base : Cfg 6 Bool TimedControl x)
    (bits : Fin 8 → Bool) (halt carry : Bool) (bs : List Bool) :
    timedInterpreter.runFrom (timedClockCfg base (.borrow bits halt carry) bs 0) bs.length =
    timedClockCfg base (.borrow bits halt (timedBorrow carry bs).1)
      (timedBorrow carry bs).2 bs.length := by
  have h := timed_borrow_run base bits halt carry bs 0 [] []
  have hstart : timed_laneCfg base 4 (some (.borrow bits halt carry)) 0 []
      (bs.map some ++ []) = timedClockCfg base (.borrow bits halt carry) bs 0 := by
    simp only [List.append_nil, timed_laneCfg, timedClockCfg, ← timed_buffer_zipper]
  have hend : timed_laneCfg base 4 (some (.borrow bits halt (timedBorrow carry bs).1))
      (0 + (bs.length : ℤ)) (((timedBorrow carry bs).2.map some).reverse ++ []) [] =
      timedClockCfg base (.borrow bits halt (timedBorrow carry bs).1)
        (timedBorrow carry bs).2 bs.length := by
    simp only [zero_add, List.append_nil, timed_laneCfg, timedClockCfg]
    rw [← timedBorrow_length carry bs, ← timed_buffer_zipper_end]
  rw [hstart, hend] at h
  exact h

/-- The selected action enters the clock rewind without applying a source transition. -/
private lemma timed_clock_start {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) :
    timedInterpreter.step (timedLift cfg bs) =
    timedClockCfg (timedLift cfg bs) (.clockBack bits halt) bs (bs.length - 1) := by
  have hstate : (timedLift cfg bs).state = some (.work (.applyRecord bits halt)) := by
    simp [timedLift, hs]
  unfold MultiTapeTM.step
  rw [hstate]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i; fin_cases i <;> simp [timedInterpreter, timedAdmin, timedLift, timedSix, timedClockCfg, Action.apply]
  · funext i; fin_cases i <;> simp [timedInterpreter, timedAdmin, timedLift, timedSix, timedClockCfg, Action.apply, sub_eq_add_neg]

/-- A ready action reaches the completed borrow pass in `2w+2` transitions. -/
private lemma timed_clock_pass {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) :
    timedInterpreter.runFrom (timedLift cfg bs) (2 * bs.length + 2) =
    timedClockCfg (timedLift cfg bs) (.borrow bits halt (timedBorrow true bs).1)
      (timedBorrow true bs).2 bs.length := by
  have h0 : timedInterpreter.runFrom (timedLift cfg bs) 1 =
      timedClockCfg (timedLift cfg bs) (.clockBack bits halt) bs (bs.length - 1) := by
    exact timed_clock_start cfg bs bits halt hs
  have h1 := timed_clock_back (timedLift cfg bs) bits halt bs bs.length (le_refl _)
  have h2 := timed_clock_borrow (timedLift cfg bs) bits halt true bs
  have h := timedCut_run_join timedInterpreter (timedCut_run_join timedInterpreter h0 h1) h2
  simpa only [show 1 + (bs.length + 1) + bs.length = 2 * bs.length + 2 by omega] using h

/-- After a successful borrow, the retained action executes once. -/
private lemma timed_execute {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) :
    timedInterpreter.step { timedLift cfg bs with state := some (.execute bits halt) } =
      timedLift (universalInterpreter.step cfg) bs := by
  have hr : (fun i => (timedLift cfg bs).workTapeSymbols (i.castAdd 2)) =
      cfg.workTapeSymbols := by funext i; fin_cases i <;> rfl
  change (timedAction (universalInterpreter.tr (.applyRecord bits halt) cfg.inputSymbol
    (fun i => (timedLift cfg bs).workTapeSymbols (i.castAdd 2)))).apply
      { timedLift cfg bs with state := some (.execute bits halt) } = _
  rw [hr]
  have h := timedAction_apply cfg bs (universalInterpreter.tr (.applyRecord bits halt)
    cfg.inputSymbol cfg.workTapeSymbols)
  simpa only [MultiTapeTM.step, hs, Action.apply] using h

/-- A positive budget is decremented exactly once before the selected source action.

**Proof sketch.** Rewind the clock and run the fixed-width borrow sweep. Positive
value rules out a remaining carry at the right blank; one transition selects
execution and the next applies the source action through the buffering wrapper. -/
private lemma timed_clock_success {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) (hv : 0 < timedValue bs) :
    timedInterpreter.runFrom (timedLift cfg bs) (2 * bs.length + 4) =
      timedLift (universalInterpreter.step cfg) (timedBorrow true bs).2 := by
  have hf : (timedBorrow true bs).1 = false := by
    cases h : (timedBorrow true bs).1
    · rfl
    · have hz := (timedBorrow_underflow bs).mp h; omega
  let after := timedClockCfg (timedLift cfg bs) (.borrow bits halt false) (timedBorrow true bs).2 bs.length
  have hr : after.workTapeSymbols 4 = none := by
    simp only [after, timedClockCfg, Cfg.workTapeSymbols, Function.update_self]
    rw [← timedBorrow_length true bs, bufferTape_nat, List.getElem?_eq_none (le_refl _)]
  have he : timedInterpreter.step after =
      { timedLift cfg (timedBorrow true bs).2 with state := some (.execute bits halt) } := by
    change (timedInterpreter.tr (.borrow bits halt false) after.inputSymbol after.workTapeSymbols).apply after = _
    simp only [timedInterpreter, hr, Bool.false_eq_true, ↓reduceIte]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
    · funext i; fin_cases i <;> simp [after, timedAdmin, timedClockCfg, timedLift, timedSix, Action.apply]
    · funext i; fin_cases i <;> simp [after, timedAdmin, timedClockCfg, timedLift, timedSix, Action.apply, timedBorrow_length]
  rw [show 2 * bs.length + 4 = (2 * bs.length + 2) + 1 + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    timed_clock_pass cfg bs bits halt hs, hf]
  rw [he, timed_execute cfg _ bits halt hs]

/-- A zero budget halts with only the timeout tag, even if source emissions were buffered. -/
private lemma timed_clock_timeout {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (bits : Fin 8 → Bool) (halt : Bool)
    (hs : cfg.state = some (.applyRecord bits halt)) (hv : timedValue bs = 0) :
    let dst := timedInterpreter.runFrom (timedLift cfg bs) (2 * bs.length + 3)
    dst.state = none ∧ dst.output = [false] := by
  dsimp only
  have hf := (timedBorrow_underflow bs).mpr hv
  rw [show 2 * bs.length + 3 = (2 * bs.length + 2) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', timed_clock_pass cfg bs bits halt hs, hf]
  have hr : (timedClockCfg (timedLift cfg bs) (.borrow bits halt true)
      (timedBorrow true bs).2 bs.length).workTapeSymbols 4 = none := by
    simp only [timedClockCfg, Cfg.workTapeSymbols, Function.update_self]
    rw [← timedBorrow_length true bs, bufferTape_nat, List.getElem?_eq_none (le_refl _)]
  let after := timedClockCfg (timedLift cfg bs) (.borrow bits halt true)
    (timedBorrow true bs).2 bs.length
  have he : timedInterpreter.step after = (timedAdmin none (none, 0) (none, 0) (some false)).apply after := by
    change (timedInterpreter.tr (.borrow bits halt true) after.inputSymbol after.workTapeSymbols).apply after = _
    simp only [timedInterpreter, show after.workTapeSymbols 4 = none from hr, ↓reduceIte]
  change (timedInterpreter.step after).state = none ∧ (timedInterpreter.step after).output = [false]
  rw [he]
  exact ⟨rfl, rfl⟩

/-- Output-phase configurations retain all simulation and clock tapes. -/
private def timedOutputCfg {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (q : Option TimedControl) (p : ℤ) (out : List Bool) : Cfg 6 Bool TimedControl x :=
  { timedLift cfg bs with
    state := q
    workTapePos := Function.update (timedLift cfg bs).workTapePos 5 p
    output := out }

/-- A buffer scan moves only the output-buffer head and appends its designated bit. -/
private lemma timed_output_step {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (q : TimedControl) (q' : Option TimedControl) (p : ℤ)
    (out : List Bool) (d : SignType) (emit : Option Bool)
    (htr : ∀ inp ws, ws 5 = bufferTape cfg.output p →
      timedInterpreter.tr q inp ws = timedAdmin q' (none, 0) (none, d) emit) :
    timedInterpreter.step (timedOutputCfg cfg bs (some q) p out) =
      timedOutputCfg cfg bs q' (p + d) (out ++ emit.toList) := by
  change (timedInterpreter.tr q _ _).apply _ = _
  rw [htr _ _ (by simp [timedOutputCfg, timedLift, timedSix, Cfg.workTapeSymbols])]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [timedOutputCfg, timedLift, timedSix, timedAdmin, Action.apply]

/-- Rewinding the buffer emits the success tag at the left blank, before any data bit. -/
private lemma timed_output_back {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs out : List Bool) : ∀ j, j ≤ cfg.output.length →
    timedInterpreter.runFrom (timedOutputCfg cfg bs (some .emitBack) (j - 1) out) (j + 1) =
      timedOutputCfg cfg bs (some .flush) 0 (out ++ [true]) := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    have h := timed_output_step cfg bs .emitBack (some .flush) (-1) out .pos (some true)
      (by intro inp ws hw; simp [timedInterpreter, hw])
    simpa using h
  | succ j ih =>
    intro hj
    have hr : bufferTape cfg.output (j : ℤ) = some cfg.output[j] := by
      rw [bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    rw [MultiTapeTM.runFrom_succ_eq_step]
    have h := timed_output_step cfg bs .emitBack (some .emitBack) j out .neg none
      (by intro inp ws hw; simp [timedInterpreter, hw, hr])
    rw [show ((j + 1 : ℕ) : ℤ) - 1 = j by omega, h]
    simpa using ih (by omega)

/-- Flushing emits each remaining buffer bit once, then halts at the right blank.

**Proof sketch.** Induct on the unread buffer suffix. A symbol is emitted while
the buffer head advances; after the final symbol, the right blank produces the
halting transition without another emission. -/
private lemma timed_output_forward {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (r : List Bool) : ∀ l out, cfg.output = l ++ r →
    timedInterpreter.runFrom (timedOutputCfg cfg bs (some .flush) l.length out) (r.length + 1) =
      timedOutputCfg cfg bs none cfg.output.length (out ++ r) := by
  induction r with
  | nil =>
    intro l out hr
    have he : cfg.output = l := by simpa using hr
    have hread : bufferTape cfg.output (l.length : ℤ) = none := by
      rw [he, bufferTape_nat, List.getElem?_eq_none (le_refl _)]
    have h := timed_output_step cfg bs .flush none l.length out 0 none
      (by intro inp ws hw; simp [timedInterpreter, hw, hread])
    simpa [he] using h
  | cons b r ih =>
    intro l out hr
    have hread : bufferTape cfg.output (l.length : ℤ) = some b := by
      rw [hr]; exact universal_table_read l r b
    have h := timed_output_step cfg bs .flush (some .flush) l.length out .pos (some b)
      (by intro inp ws hw; simp [timedInterpreter, hw, hread])
    rw [show (b :: r).length + 1 = (r.length + 1) + 1 by simp,
      MultiTapeTM.runFrom_succ_eq_step, h]
    have hh := ih (l ++ [b]) (out ++ [b]) (by simpa [List.append_assoc] using hr)
    simpa only [SignType.pos_eq_one, SignType.coe_one, Option.toList_some,
      List.length_append, List.length_cons, List.length_nil, Nat.cast_add, Nat.cast_one,
      List.append_assoc, List.singleton_append] using hh

/-- Source halting is followed by the success tag and exactly the buffered output. -/
private lemma timed_flush {x : List Bool} (cfg : Cfg 4 Bool UniversalControl x)
    (bs : List Bool) (hs : cfg.state = none) :
    let dst := timedInterpreter.runFrom (timedLift cfg bs) (2 * cfg.output.length + 3)
    dst.state = none ∧ dst.output = true :: cfg.output := by
  dsimp only
  have hcfg : timedLift cfg bs = timedOutputCfg cfg bs (some .emitStart) cfg.output.length [] := by
    refine Cfg.ext ?_ rfl rfl ?_ rfl
    · simp [timedLift, timedOutputCfg, hs]
    · funext i; fin_cases i <;> rfl
  have h0 := timed_output_step cfg bs .emitStart (some .emitBack) cfg.output.length [] .neg none
    (by intros; rfl)
  have h1 := timed_output_back cfg bs [] cfg.output.length (le_refl _)
  have h2 := timed_output_forward cfg bs cfg.output [] [true] (by simp)
  have hstart : timedInterpreter.runFrom (timedLift cfg bs) 1 =
      timedOutputCfg cfg bs (some .emitBack) (cfg.output.length - 1) [] := by
    rw [hcfg]
    simpa using h0
  have h := timedCut_run_join timedInterpreter (timedCut_run_join timedInterpreter hstart h1) h2
  have ht : 1 + (cfg.output.length + 1) + (cfg.output.length + 1) = 2 * cfg.output.length + 3 := by omega
  rw [ht] at h
  rw [h]
  exact ⟨rfl, rfl⟩

/-- The parser is live immediately before consuming the final separator cell. -/
private lemma timedPrefix_penultimate (bs α x : List Bool) :
    (timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 2 * α.length + 5)).state ≠ none := by
  have hlen := timed_input_length bs α x
  have h0 := timedPrefix_advance bs α x bs α .codeFirst (some (.codeSecond false)) none
    (4 * bs.length + 4 + 2 * α.length) (by omega) false
    (by rw [timed_code_get]; exact (timed_pair_separator α x).1) (by intro ws; rfl)
  rw [show 4 * bs.length + 2 * α.length + 5 =
      (4 * bs.length + 4 + 2 * α.length) + 1 by omega,
    MultiTapeTM.runFrom_succ_eq_step', timedPrefix_code bs α x α.length (le_refl _),
    List.take_length, h0]
  exact Option.some_ne_none _

/-- No earlier parser step can halt, since halting is absorbing. -/
private lemma timedPrefix_live (bs α x : List Bool) (s : ℕ)
    (hs : s < 4 * bs.length + 2 * α.length + 6) :
    (timedPrefixTM.tm.runFrom (timedPrefixTM.tm.initCfg (pairEncode (pairEncode bs α) x)) s).state ≠ none := by
  intro h
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show s ≤ 4 * bs.length + 2 * α.length + 5 by omega)
  have hp := timedPrefix_penultimate bs α x
  rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ h] at hp
  exact hp h

/-- Only the extracted code is supplied to the scheme's canonizer. -/
private def timedCanonTM (c : EffectiveMachineCode) : FinTM Bool :=
  bufferedCompTM timedPrefixTM c.canonizer

/-- The parser's unique work tape remains the clock lane of the composed canonizer. -/
private def timedCanonClock (c : EffectiveMachineCode) : Fin (timedCanonTM c).k :=
  Fin.castAdd (1 + c.canonizer.k) (0 : Fin 1)

/-- Exact prefix-local canonizer entry retains the entire clock word unchanged. -/
private lemma timedCanon_start (c : EffectiveMachineCode) (bs α x : List Bool) :
    (timedCanonTM c).tm.runFrom ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 3 * α.length + 8) =
    bufferedSecondCfg timedPrefixTM c.canonizer (c.canonizer.tm.initCfg α) true
      ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩
      (fun _ => bufferTape bs) (fun _ => bs.length) := by
  change (bufferedCompTM timedPrefixTM c.canonizer).tm.runFrom _ _ = _
  rw [show 4 * bs.length + 3 * α.length + 8 =
      (4 * bs.length + 2 * α.length + 6) + (α.length + 2) by omega,
    MultiTapeTM.runFrom_add, bufferedFirstCfg_init,
    bufferedFirstCfg_run timedPrefixTM c.canonizer _ _ (fun s hs => timedPrefix_live bs α x s hs),
    timedPrefix_complete]
  exact bufferedFirstCfg_rewind timedPrefixTM c.canonizer _ rfl

/-- Canonization uses virtual input `α`; physical input and clock remain stationary. -/
private lemma timedCanon_run (c : EffectiveMachineCode) (bs α x : List Bool) (t : ℕ) :
    ∃ b, (timedCanonTM c).tm.runFrom
      ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 3 * α.length + 8 + t) =
    bufferedSecondCfg timedPrefixTM c.canonizer
      (c.canonizer.tm.runFrom (c.canonizer.tm.initCfg α) t) b
      ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩
      (fun _ => bufferTape bs) (fun _ => bs.length) := by
  rw [MultiTapeTM.runFrom_add, timedCanon_start]
  obtain ⟨b, -, he⟩ := bufferedSecondCfg_run timedPrefixTM c.canonizer
    (c.canonizer.tm.initCfg α) true
    (by constructor <;> intro h <;> simp_all [VirtualTag])
    (x := pairEncode (pairEncode bs α) x)
    ⟨4 * bs.length + 2 * α.length + 7, by rw [timed_input_length]; omega⟩
    (fun _ => bufferTape bs) (fun _ => bs.length) t
  exact ⟨b, he⟩

/-- Canonizer completion identifies the table, parked input, and preserved clock. -/
private lemma timedCanon_complete (c : EffectiveMachineCode) (bs α x : List Bool) :
    let cfg := (timedCanonTM c).tm.runFrom
      ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x))
      (4 * bs.length + 3 * α.length + 8 + c.canonizerTime α.length)
    cfg.state = none ∧ cfg.output = (c.decode α).serialize ∧
      cfg.inputPos.val = 4 * bs.length + 2 * α.length + 7 ∧
      cfg.workTapes (timedCanonClock c) = bufferTape bs ∧
      cfg.workTapePos (timedCanonClock c) = bs.length := by
  dsimp only
  obtain ⟨b, he⟩ := timedCanon_run c bs α x (c.canonizerTime α.length)
  rw [he]
  have hc := (computesInTime_iff _ _ _ _).mp (c.canonizer_computes α)
  refine ⟨?_, hc.2, rfl, ?_, ?_⟩
  · simp only [bufferedSecondCfg, hc.1, Option.map_none]
  · simp [bufferedSecondCfg, timedCanonClock]
  · simp [bufferedSecondCfg, timedCanonClock]

/-- The exact deadline-inclusive answer of a source configuration. -/
private def timedAnswer (M : CodeTM) {x : List Bool}
    (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (t : ℕ) : List Bool :=
  let dst := M.tm.runFrom src t
  if dst.state = none then true :: dst.output else [false]

/-- The timed interpreter finishes from every checkpoint, within a uniform ledger.

**Proof sketch.** Induct on the remaining numeric budget. Already-halted sources
flush immediately. Otherwise the stopped lookup reaches a pending action; a zero
budget times out without applying it, while a positive budget borrows once and
applies it. The recursive call is made on the successor, including its halting
state. Thus halting on the final allowed transition reaches the success branch.
The emission-length increment is at most one, leaving two units of slack per
transition in the displayed bound. -/
private lemma timed_interpret_finishes (M : CodeTM) (α : List Bool) {x : List Bool}
    (r : ℕ) : ∀ (src : Cfg 1 Bool (Fin (M.numStates + 1)) x) (p : ℕ) (bs : List Bool),
    p ≤ M.serialize.length → timedValue bs = r →
    ∃ d, d ≤ (3 * M.serialize.length + 5 * (M.numStates + 1) + 20 + 2 * bs.length + 8) * (r + 1) +
        2 * src.output.length ∧
      let dst := timedInterpreter.runFrom (timedLift (universalSimulationCfg M α src p) bs) d
      dst.state = none ∧ dst.output = timedAnswer M src r := by
  induction r with
  | zero =>
    intro src p bs hp hv
    by_cases hs : src.state = none
    · refine ⟨2 * src.output.length + 3, by omega, ?_⟩
      have h := timed_flush (universalSimulationCfg M α src p) bs
        (by simp [universalSimulationCfg, hs])
      simpa only [universalSimulationCfg, timedAnswer, MultiTapeTM.runFrom_zero, hs, ↓reduceIte] using h
    · obtain ⟨d, p', ready, hd, hp', ⟨bits, halt, hready⟩, he, ha⟩ := timedCut_live_block M α src p hp hs
      have hreplay := timed_replay (universalSimulationCfg M α src p) bs d (by rw [he, hready]; simp)
      rw [he] at hreplay
      have htimeout := timed_clock_timeout ready bs bits halt hready hv
      refine ⟨d + (2 * bs.length + 3), by omega, ?_⟩
      rw [MultiTapeTM.runFrom_add, hreplay]
      simpa only [timedAnswer, MultiTapeTM.runFrom_zero, if_neg hs] using htimeout
  | succ r ih =>
    intro src p bs hp hv
    by_cases hs : src.state = none
    · have hpos : 3 ≤
          (3 * M.serialize.length + 5 * (M.numStates + 1) + 20 + 2 * bs.length + 8) * (r + 1 + 1) := by
        have h := Nat.mul_le_mul_left
          (3 * M.serialize.length + 5 * (M.numStates + 1) + 20 + 2 * bs.length + 8)
          (show 1 ≤ r + 1 + 1 by omega)
        omega
      refine ⟨2 * src.output.length + 3, by omega, ?_⟩
      have h := timed_flush (universalSimulationCfg M α src p) bs
        (by simp [universalSimulationCfg, hs])
      simpa only [universalSimulationCfg, timedAnswer, MultiTapeTM.runFrom_of_halt _ hs, hs, ↓reduceIte] using h
    · obtain ⟨d, p', ready, hd, hp', ⟨bits, halt, hready⟩, he, ha⟩ := timedCut_live_block M α src p hp hs
      have hreplay := timed_replay (universalSimulationCfg M α src p) bs d (by rw [he, hready]; simp)
      rw [he] at hreplay
      have hc := timed_clock_success ready bs bits halt hready (by omega)
      rw [ha] at hc
      have hv' : timedValue (timedBorrow true bs).2 = r := by
        have h := timedBorrow_value bs (by omega); omega
      obtain ⟨d', hd', hfinish⟩ := ih (M.tm.step src) p' (timedBorrow true bs).2 hp' hv'
      have hlength : (M.tm.step src).output.length ≤ src.output.length + 1 := by
        rw [MultiTapeTM.step_output, List.length_append]
        cases M.tm.outputSymbol src <;> simp
      rw [timedBorrow_length] at hd'
      refine ⟨d + (2 * bs.length + 4) + d', ?_, ?_⟩
      · rw [Nat.mul_succ]
        omega
      · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hreplay, hc]
        simpa only [timedAnswer, MultiTapeTM.runFrom_succ_eq_step] using hfinish

/-- The five fresh lanes are table, state, simulated work, input marker, and output. -/
private def timedFive {A : Type} (core : Fin 4 → A) (buffer : A) : Fin 5 → A :=
  fun i => if i = 0 then core 0 else if i = 1 then core 1 else
    if i = 2 then core 2 else if i = 3 then core 3 else buffer

/-- Interpreter actions reuse the parser's clock lane and five fresh lanes. -/
private def timedFrameAction (M : FinTM Bool) (clock : Fin M.k)
    (a : Action 6 Bool TimedControl) : Action (M.k + 5) Bool (Option M.State ⊕ TimedControl) :=
  ⟨a.inputTape, Fin.addCases
    (Function.update (fun _ => (none, 0)) clock (a.workTapes 4))
    (timedFive (fun i => a.workTapes (i.castAdd 2)) (a.workTapes 5)),
    a.output, a.state.map Sum.inr⟩

/-- Capture the canonizer's table, then run the timed interpreter with the retained clock. -/
private def timedCaptureTM (M : FinTM Bool) (clock : Fin M.k) : FinTM Bool where
  k := M.k + (1 + 4)
  State := Option M.State ⊕ TimedControl
  tm :=
    { q₀ := .inl (some M.tm.q₀)
      tr := fun q inp work => match q with
        | .inl (some q) =>
          let a := M.tm.tr q inp (fun i => work (Fin.castAdd 5 i))
          ⟨a.inputTape, tapeBlocks a.workTapes
            (a.output.map some, if a.output = none then 0 else .pos)
            (fun _ => (none, 0)), none, some (.inl a.state)⟩
        | .inl none => controlAction 0 (some (.inr timedInterpreter.q₀))
        | .inr q => timedFrameAction M clock (timedInterpreter.tr q inp
            (timedSix (fun i => work (Fin.natAdd M.k (i.castAdd 1)))
              (work (clock.castAdd 5)) (work (Fin.natAdd M.k (4 : Fin 5))))) }

/-- Complete first-phase configuration of the output-capture wrapper. -/
private def timedCaptureCfg (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    Cfg (timedCaptureTM M clock).k Bool (timedCaptureTM M clock).State x where
  state := some (.inl cfg.state)
  inputPos := cfg.inputPos
  workTapes := tapeBlocks cfg.workTapes (bufferTape cfg.output) (fun _ _ => none)
  workTapePos := tapeBlocks cfg.workTapePos cfg.output.length (fun _ => 0)
  output := []

/-- The capture wrapper starts with a blank table and blank interpreter tapes. -/
private lemma timedCapture_init (M : FinTM Bool) (clock : Fin M.k) (x : List Bool) :
    (timedCaptureTM M clock).tm.initCfg x =
      timedCaptureCfg M clock (M.tm.initCfg x) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [timedCaptureCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [timedCaptureCfg, tapeBlocks]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [timedCaptureCfg, tapeBlocks]
    · intro j
      refine Fin.addCases ?_ ?_ j <;> intro j <;>
        simp [timedCaptureCfg, tapeBlocks]

/-- One live transition captures every emitted bit, including a bit emitted on
the source machine's halting transition. Administrative states remain live.

**Proof sketch.** The original work block and physical input move in lockstep.
An emission writes precisely the table's right blank and advances its head; the
buffer-append identity gives its new contents. No real output is emitted, and
the four later simulation and output-buffer tapes remain untouched. -/
private lemma timedCapture_step (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (hs : cfg.state ≠ none) :
    (timedCaptureTM M clock).tm.step (timedCaptureCfg M clock cfg) =
      timedCaptureCfg M clock (M.tm.step cfg) := by
  unfold MultiTapeTM.step
  cases hq : cfg.state with
  | none => exact False.elim (hs hq)
  | some q =>
    have hs' : (timedCaptureCfg M clock cfg).state = some (.inl (some q)) := by
      simp [timedCaptureCfg, hq]
    rw [hs']
    dsimp only [timedCaptureTM]
    have hr : (fun i => (timedCaptureCfg M clock cfg).workTapeSymbols
        (Fin.castAdd 5 i)) = cfg.workTapeSymbols := by
      funext i
      simp [timedCaptureCfg, Cfg.workTapeSymbols, tapeBlocks]
    have hi : (timedCaptureCfg M clock cfg).inputSymbol = cfg.inputSymbol := rfl
    rw [hr, hi]
    let a := M.tm.tr q cfg.inputSymbol cfg.workTapeSymbols
    change (⟨a.inputTape, tapeBlocks a.workTapes
      (a.output.map some, if a.output = none then 0 else .pos)
      (fun _ => (none, 0)), none, some (.inl a.state)⟩ :
      Action (M.k + (1 + 4)) Bool _).apply _ = timedCaptureCfg M clock (a.apply cfg)
    refine Cfg.ext rfl rfl ?_ ?_ ?_
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;>
            simp [timedCaptureCfg, tapeBlocks, Action.apply, ho, bufferTape_append]
        · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
    · funext i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
      · intro j
        refine Fin.addCases ?_ ?_ j
        · intro j
          cases ho : a.output <;> simp [timedCaptureCfg, tapeBlocks, Action.apply, ho]
        · intro j; simp [timedCaptureCfg, tapeBlocks, Action.apply]
    · simp [timedCaptureCfg, tapeBlocks, Action.apply]

/-- Lockstep capture through the first halting transition. -/
private lemma timedCapture_run (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (t : ℕ)
    (h : ∀ s, s < t → (M.tm.runFrom cfg s).state ≠ none) :
    (timedCaptureTM M clock).tm.runFrom (timedCaptureCfg M clock cfg) t =
      timedCaptureCfg M clock (M.tm.runFrom cfg t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun s hs => h s (by omega)),
      timedCapture_step M clock _ (h t (by omega)), MultiTapeTM.runFrom_succ_eq_step']

/-- Interpreter entry retains the halted canonizer's work and captured table.
Its clock lane becomes active again during interpretation. -/
private def timedCapturedCfg (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) :
    Cfg (timedCaptureTM M clock).k Bool (timedCaptureTM M clock).State x :=
  { timedCaptureCfg M clock cfg with state := some (.inr timedInterpreter.q₀) }

/-- A halted source configuration transfers to the live interpreter entry state. -/
private lemma timedCapture_transfer (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg M.k Bool M.State x) (h : cfg.state = none) :
    (timedCaptureTM M clock).tm.step (timedCaptureCfg M clock cfg) =
      timedCapturedCfg M clock cfg := by
  unfold MultiTapeTM.step
  simp only [timedCaptureCfg, h]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · rfl
  · funext i; exact add_zero _
  · rfl

/-- Every completed source computation reaches the interpreter with the table
captured in at most one extra transition.

**Proof sketch.** Choose the first source halting time. Lockstep capture holds
through that transition; one live administrative transition enters the interpreter.
Absorbing source halting identifies this first halted configuration with the one
at the supplied time bound, so all its fields (including parked input position)
are retained, not merely its completed output. -/
private lemma timedCapture_start (M : FinTM Bool) (clock : Fin M.k) (x : List Bool) (T : ℕ)
    (h : (M.tm.runFrom (M.tm.initCfg x) T).state = none) :
    ∃ t, t ≤ T + 1 ∧
      (timedCaptureTM M clock).tm.runFrom ((timedCaptureTM M clock).tm.initCfg x) t =
        timedCapturedCfg M clock (M.tm.runFrom (M.tm.initCfg x) T) := by
  classical
  have hh : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T, h⟩
  let t := Nat.find hh
  have ht : t ≤ T := Nat.find_min' hh h
  have hs : (M.tm.runFrom (M.tm.initCfg x) t).state = none := Nat.find_spec hh
  have he : M.tm.runFrom (M.tm.initCfg x) T = M.tm.runFrom (M.tm.initCfg x) t := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le ht
    rw [hd, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hs]
  refine ⟨t + 1, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_succ_eq_step', timedCapture_init,
    timedCapture_run M clock _ t (fun s hs => Nat.find_min hh hs),
    timedCapture_transfer M clock _ hs, he]


/-- A framed interpreter configuration shares precisely the retained clock lane. -/
private def timedFrame (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) : Cfg (timedCaptureTM M clock).k Bool (timedCaptureTM M clock).State x :=
  ⟨cfg.state.map Sum.inr, cfg.inputPos,
    Fin.addCases (Function.update tapes clock (cfg.workTapes 4))
      (timedFive (fun i => cfg.workTapes (i.castAdd 2)) (cfg.workTapes 5)),
    Fin.addCases (Function.update heads clock (cfg.workTapePos 4))
      (timedFive (fun i => cfg.workTapePos (i.castAdd 2)) (cfg.workTapePos 5)), cfg.output⟩

/-- The active six reads of a frame are exactly the interpreter's reads. -/
private lemma timedFrame_reads (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) :
    timedSix (fun i => (timedFrame M clock cfg tapes heads).workTapeSymbols
      (Fin.natAdd M.k (i.castAdd 1)))
      ((timedFrame M clock cfg tapes heads).workTapeSymbols (clock.castAdd 5))
      ((timedFrame M clock cfg tapes heads).workTapeSymbols (Fin.natAdd M.k (4 : Fin 5))) =
    cfg.workTapeSymbols := by
  funext i
  fin_cases i <;> simp [timedFrame, timedSix, timedFive, Cfg.workTapeSymbols]

/-- A framed action changes only the six active lanes. Inactive canonizer data remains framed.

**Proof sketch.** Compare configuration fields. Split tape indices into the old
canonizer block and the five fresh lanes, then distinguish the retained clock
inside the old block. Each active read, write, and head move agrees with its
six-lane counterpart; the other old lanes are unchanged. -/
private lemma timedFrame_apply (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) (a : Action 6 Bool TimedControl) :
    (timedFrameAction M clock a).apply (timedFrame M clock cfg tapes heads) =
      timedFrame M clock (a.apply cfg) tapes heads := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j
        simp only [timedFrameAction, timedFrame, Action.apply, Fin.addCases_left, Function.update_self]
      · simp [timedFrameAction, timedFrame, Action.apply, hj, Function.update_of_ne]
    · intro j
      fin_cases j <;> simp [timedFrameAction, timedFrame, timedFive, Action.apply]
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j
        simp only [timedFrameAction, timedFrame, Action.apply, Fin.addCases_left, Function.update_self]
      · simp [timedFrameAction, timedFrame, Action.apply, hj, Function.update_of_ne]
    · intro j
      fin_cases j <;> simp [timedFrameAction, timedFrame, timedFive, Action.apply]

/-- Every interpreter transition lifts to the assembled machine, including final halting. -/
private lemma timedFrame_step (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) :
    (timedCaptureTM M clock).tm.step (timedFrame M clock cfg tapes heads) =
      timedFrame M clock (timedInterpreter.step cfg) tapes heads := by
  cases hs : cfg.state with
  | none =>
    rw [MultiTapeTM.step_of_halt hs,
      MultiTapeTM.step_of_halt (show (timedFrame M clock cfg tapes heads).state = none by simp [timedFrame, hs])]
  | some q =>
    have hstate : (timedFrame M clock cfg tapes heads).state = some (.inr q) := by simp [timedFrame, hs]
    conv_lhs => unfold MultiTapeTM.step; rw [hstate]; dsimp only [timedCaptureTM]
    have hi : (timedFrame M clock cfg tapes heads).inputSymbol = cfg.inputSymbol := rfl
    rw [timedFrame_reads, hi, timedFrame_apply]
    simp only [MultiTapeTM.step, hs]

/-- Full interpreter runs lift without changing the inactive frame. -/
private lemma timedFrame_run (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (cfg : Cfg 6 Bool TimedControl x) (tapes : Fin M.k → ℤ → Option Bool)
    (heads : Fin M.k → ℤ) (t : ℕ) :
    (timedCaptureTM M clock).tm.runFrom (timedFrame M clock cfg tapes heads) t =
      timedFrame M clock (timedInterpreter.runFrom cfg t) tapes heads := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', ih, timedFrame_step, MultiTapeTM.runFrom_succ_eq_step']

/-- Capturing a completed canonizer yields the initial six-lane interpreter frame.

**Proof sketch.** Compare the five configuration fields, splitting old and fresh
lanes. At the retained clock, use the parser completion identities for its contents
and head; the remaining lanes are the captured table and fresh blank tapes. -/
private lemma timedCaptured_frame (M : FinTM Bool) (clock : Fin M.k) {x : List Bool}
    (src : Cfg M.k Bool M.State x) (bs : List Bool)
    (ht : src.workTapes clock = bufferTape bs) (hh : src.workTapePos clock = bs.length) :
    timedCapturedCfg M clock src =
      timedFrame M clock (timedLift (timedCut_InterpreterInitial src.inputPos src.output) bs)
        src.workTapes src.workTapePos := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j; simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, ht]
      · simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, hj]
    · intro j
      fin_cases j <;> simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift,
        timedSix, timedFive, timedCut_InterpreterInitial, universalFour, tapeBlocks] <;> rfl
  · funext i
    refine Fin.addCases (m := M.k) (n := 5) ?_ ?_ i
    · intro j
      by_cases hj : j = clock
      · subst j; simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, hh]
      · simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift, timedSix, tapeBlocks, hj]
    · intro j
      fin_cases j <;> simp [timedCapturedCfg, timedCaptureCfg, timedFrame, timedLift,
        timedSix, timedFive, timedCut_InterpreterInitial, universalFour, tapeBlocks] <;> rfl

/-- The complete timed universal machine has finite control and finitely many tapes. -/
private def timedUniversalTM (c : EffectiveMachineCode) : FinTM Bool :=
  timedCaptureTM (timedCanonTM c) (timedCanonClock c)

/-- The part of startup depending only on the code representation. -/
private def timedStartupBound (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
    2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 16

/-- The canonical header endpoint is inside the complete serialization. -/
private lemma timed_header_bound (M : CodeTM) :
    2 * (Nat.bits M.numStates).length + 2 + M.tm.q₀.val + 1 ≤ M.serialize.length := by
  obtain ⟨records, hr⟩ := universal_serialization_header M
  rw [hr, universal_pair_length]
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- Full startup retains the binary deadline, canonizes `α` alone, and reaches
an initialized source checkpoint within `4|bits|` plus a code-only constant.

**Proof sketch.** Run the prefix-local canonizer and capture its serialization.
Transfer to the framed interpreter, replay the stopped initialization gadgets,
and identify the initialized source checkpoint using the nested-pair length.
Add the canonizer, transfer, and header-initialization costs. -/
private lemma timed_initialized (c : EffectiveMachineCode) (bs α x : List Bool) :
    ∃ (t : ℕ) (tapes : Fin (timedCanonTM c).k → ℤ → Option Bool)
      (heads : Fin (timedCanonTM c).k → ℤ),
      t ≤ 4 * bs.length + timedStartupBound c α ∧
      (timedUniversalTM c).tm.runFrom
        ((timedUniversalTM c).tm.initCfg (pairEncode (pairEncode bs α) x)) t =
      timedFrame (timedCanonTM c) (timedCanonClock c)
        (timedLift (universalSimulationCfg (c.decode α) (pairEncode bs α)
          ((c.decode α).tm.initCfg x)
          (2 * (Nat.bits (c.decode α).numStates).length + 2 + (c.decode α).tm.q₀.val + 1)) bs)
        tapes heads := by
  let T := 4 * bs.length + 3 * α.length + 8 + c.canonizerTime α.length
  let src := (timedCanonTM c).tm.runFrom
    ((timedCanonTM c).tm.initCfg (pairEncode (pairEncode bs α) x)) T
  have hc := timedCanon_complete c bs α x
  obtain ⟨t, ht, he⟩ := timedCapture_start (timedCanonTM c) (timedCanonClock c)
    (pairEncode (pairEncode bs α) x) T hc.1
  obtain ⟨records, hrecords⟩ := universal_serialization_header (c.decode α)
  have hinit := timedCut_Interpreter_initialize src.inputPos (c.decode α).serialize
    (Nat.bits (c.decode α).numStates) records (c.decode α).tm.q₀.val hrecords
  let d := (c.decode α).serialize.length + 2 * (Nat.bits (c.decode α).numStates).length +
    2 * (c.decode α).tm.q₀.val + 7
  have hi := timed_replay (timedCut_InterpreterInitial src.inputPos (c.decode α).serialize) bs d
    (by rw [hinit]; exact Option.some_ne_none _)
  rw [hinit] at hi
  refine ⟨t + d, src.workTapes, src.workTapePos, ?_, ?_⟩
  · dsimp only [timedStartupBound, d, T] at *; omega
  · change (timedCaptureTM (timedCanonTM c) (timedCanonClock c)).tm.runFrom _ _ = _
    rw [MultiTapeTM.runFrom_add, he, timedCaptured_frame _ _ _ bs hc.2.2.2.1 hc.2.2.2.2]
    have ho : src.output = (c.decode α).serialize := hc.2.1
    rw [ho, timedFrame_run, hi]
    congr 2
    apply Cfg.ext
    · rfl
    · apply Fin.ext
      have hp : src.inputPos.val = 4 * bs.length + 2 * α.length + 7 := hc.2.2.1
      simp only [universalEvalCfg, timedCut_InterpreterBase, universalSimulationCfg,
        universalInputPos, MultiTapeTM.initCfg, Fin.val_mk]
      change src.inputPos.val = 2 * (pairEncode bs α).length + 2 + 1
      have hlen := universal_pair_length bs α
      omega
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [universalEvalCfg, timedCut_InterpreterBase,
        universalSimulationCfg, universalFour, Nat.cast_add]
    · rfl

/-- Absorb clock-width work and fixed startup into a code-only quadratic coefficient.

**Proof sketch.** Write n = t + 1. Both the clock width and n are at most n squared.
Bound startup by (S + 4) n squared, and the interpreter coefficient by (B + 10) n;
its multiplication by n supplies the remaining quadratic term. -/
private lemma timed_cost_bound (S B t w s d : ℕ) (hw : w ≤ t)
    (hs : s ≤ 4 * w + S) (hd : d ≤ (B + 2 * w + 8) * (t + 1)) :
    s + d ≤ (S + B + 14) * (t + 1) ^ 2 := by
  have hn : 1 ≤ t + 1 := by omega
  have hsq : t + 1 ≤ (t + 1) ^ 2 := by
    calc t + 1 = (t + 1) * 1 := by omega
      _ ≤ (t + 1) * (t + 1) := Nat.mul_le_mul_left _ hn
      _ = (t + 1) ^ 2 := by ring
  have hs' : s ≤ (S + 4) * (t + 1) ^ 2 := by
    have hw' := Nat.mul_le_mul_left 4 (show w ≤ (t + 1) ^ 2 by omega)
    have hS := Nat.mul_le_mul_left S (show 1 ≤ (t + 1) ^ 2 by omega)
    calc s ≤ 4 * w + S := hs
      _ ≤ 4 * (t + 1) ^ 2 + S * (t + 1) ^ 2 := by omega
      _ = (S + 4) * (t + 1) ^ 2 := by ring
  have hb : B + 2 * w + 8 ≤ (B + 10) * (t + 1) := by
    have hB := Nat.mul_le_mul_left (B + 8) hn
    have hw' := Nat.mul_le_mul_left 2 (show w ≤ t + 1 by omega)
    calc B + 2 * w + 8 ≤ (B + 8) * (t + 1) + 2 * (t + 1) := by omega
      _ = (B + 10) * (t + 1) := by ring
  calc s + d ≤ (S + 4) * (t + 1) ^ 2 + (B + 2 * w + 8) * (t + 1) :=
      Nat.add_le_add hs' hd
    _ ≤ (S + 4) * (t + 1) ^ 2 + ((B + 10) * (t + 1)) * (t + 1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hb) _
    _ = (S + B + 14) * (t + 1) ^ 2 := by ring

/-- The assembled finite machine computes the exact bounded answer uniformly in the input.

**Proof sketch.** Join the initialized outer run to the bounded inner run, lifting
the latter through the inactive canonizer frame. Its halted state and exact answer
give a completed computation; the clock-width estimate and cost ledger enlarge
the time bound to the stated code-dependent quadratic budget. -/
private lemma timed_computes (c : EffectiveMachineCode) (α x : List Bool) (t : ℕ) :
    (timedUniversalTM c).ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
      (timedAnswer (c.decode α) ((c.decode α).tm.initCfg x) t)
      ((timedStartupBound c α + universalBlockBound c α + 14) * (t + 1) ^ 2) := by
  obtain ⟨s, tapes, heads, hs, hstart⟩ := timed_initialized c (Nat.bits t) α x
  obtain ⟨d, hd, hfinish⟩ := timed_interpret_finishes (c.decode α) (pairEncode (Nat.bits t) α) t
    ((c.decode α).tm.initCfg x)
    (2 * (Nat.bits (c.decode α).numStates).length + 2 + (c.decode α).tm.q₀.val + 1)
    (Nat.bits t) (timed_header_bound (c.decode α)) (timedValue_bits t)
  have htime : s + d ≤
      (timedStartupBound c α + universalBlockBound c α + 14) * (t + 1) ^ 2 := by
    apply timed_cost_bound _ _ _ _ _ _ (length_bits_le_self t) hs
    simpa only [universalBlockBound, MultiTapeTM.initCfg, Cfg.init, List.length_nil,
      Nat.mul_zero, Nat.add_zero] using hd
  have hcompute : (timedUniversalTM c).ComputesInTime
      (pairEncode (pairEncode (Nat.bits t) α) x)
      (timedAnswer (c.decode α) ((c.decode α).tm.initCfg x) t) (s + d) := by
    apply (computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    change ((timedCaptureTM (timedCanonTM c) (timedCanonClock c)).tm.runFrom _ d).state = none ∧
      ((timedCaptureTM (timedCanonTM c) (timedCanonClock c)).tm.runFrom _ d).output = _
    rw [timedFrame_run]
    exact ⟨by simp only [timedFrame, hfinish.1, Option.map_none], hfinish.2⟩
  exact hcompute.mono htime

/-- **The time-bounded universal machine** [AB09, §1.4.1, "Universal TM with time
bound"]: a single machine that, given `⟨⟨⌞t⌟, α⟩, x⟩` (clock and code first, input
last), simulates the machine `α` denotes on `x` for at most `t` steps, reporting
success (`true :: output`) or timeout (`[false]`).

**Proof sketch.** Extend the simulation of `Turing.universal` with a binary
countdown clock on a further work tape, initialized from `⌞t⌟ = Nat.bits t` (parsed
from the doubled-bit region; cost `O(t + 1)`, within budget). Each simulated step
costs an additional `O((Nat.bits t).length + 1)` for the decrement, whence the
quadratic budget; `M`'s emissions are buffered on a work tape rather than emitted
(their total length is at most `t`, by `Turing.MultiTapeTM.output_length_le`).
Halting is checked after each simulated transition, **including the `t`-th**: if the
simulated machine has halted by the time the clock expires — deadline included —
`U` emits `true` and flushes the buffer; otherwise it emits `false`. At `t = 0` no
initialized machine has halted (`Turing.FinTM.not_computesInTime_zero`), and the
timeout branch applies (audit finding 6). The two cases below are exhaustive:
either some output witnesses halting within `t`, or every output fails to. -/
theorem timed_universal (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output) (C * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false] (C * (t + 1) ^ 2)) := by
  refine ⟨timedUniversalTM c, fun α =>
    ⟨timedStartupBound c α + universalBlockBound c α + 14, ?_⟩⟩
  intro x t
  have hu := timed_computes c α x t
  constructor
  · intro output hsource
    obtain ⟨hh, ho⟩ := (computesInTime_iff _ _ _ _).mp hsource
    simpa only [timedAnswer, hh, if_pos, ho] using hu
  · intro hsource
    have hh : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state ≠ none := by
      intro hhalt
      exact hsource _ ((computesInTime_iff _ _ _ _).mpr ⟨hhalt, rfl⟩)
    simpa only [timedAnswer, if_neg hh] using hu

/-- **The concrete bounded-answer export** [AB09, §1.4.1, time-bounded universal
simulation, with the realized constant]: the single simulator behind
`Turing.timed_universal`, with its code-dependent quadratic coefficient written
out in public vocabulary — the startup part
`3|α| + canonizerTime(|α|) + |serialize| + 2·|bits(numStates)| + 2·q₀ + 16`
plus the interpreter part `Turing.universalBlockBound` plus `14`. One simulator
is chosen **before** the code, the input, and the deadline; both the success
clause and the timeout clause of `Turing.timed_universal` are preserved
verbatim.

This is the maintainer export mandated by the Chapter-2 phase-3 audit and
requested by the epoch-2 TMSAT delivery (bridge protocol, step 3): the Chapter-2
bridge `timed_universal_quantitative` is discharged from this theorem by
monotonicity, after its side's arithmetic bound on this displayed coefficient.
No bound is asserted on the arbitrary existential witness of
`Turing.timed_universal` — the witness exhibited here is the concrete machine of
its proof, and the displayed coefficient is that proof's realized constant. No
Chapter-2 notion appears. New public surface, flagged for the shared
infrastructure audit round.

**Proof sketch.** `timed_computes` states exactly this bound for the concrete
simulator, with the startup written as `timedStartupBound`, whose definition is
the displayed startup expression; the two clauses then follow from the
deadline-inclusive answer `timedAnswer` by the same case analysis as
`Turing.timed_universal` (success: the halted source's output is reported behind
`true`; timeout: no completed output exists, so the source configuration is
live and the answer is `[false]`). -/
theorem timed_universal_concrete (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
      (∀ output : List Bool,
        (c.decode α).toFinTM.ComputesInTime x output t →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          (true :: output)
          ((3 * α.length + c.canonizerTime α.length +
              (c.decode α).serialize.length +
              2 * (Nat.bits (c.decode α).numStates).length +
              2 * (c.decode α).tm.q₀.val + 16 +
              universalBlockBound c α + 14) * (t + 1) ^ 2)) ∧
      ((∀ output : List Bool, ¬(c.decode α).toFinTM.ComputesInTime x output t) →
        U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x)
          [false]
          ((3 * α.length + c.canonizerTime α.length +
              (c.decode α).serialize.length +
              2 * (Nat.bits (c.decode α).numStates).length +
              2 * (c.decode α).tm.q₀.val + 16 +
              universalBlockBound c α + 14) * (t + 1) ^ 2)) := by
  refine ⟨timedUniversalTM c, fun α x t => ?_⟩
  -- The displayed coefficient is definitionally `timedStartupBound` expanded.
  have hu : (timedUniversalTM c).ComputesInTime
      (pairEncode (pairEncode (Nat.bits t) α) x)
      (timedAnswer (c.decode α) ((c.decode α).tm.initCfg x) t)
      ((3 * α.length + c.canonizerTime α.length +
          (c.decode α).serialize.length +
          2 * (Nat.bits (c.decode α).numStates).length +
          2 * (c.decode α).tm.q₀.val + 16 +
          universalBlockBound c α + 14) * (t + 1) ^ 2) :=
    timed_computes c α x t
  constructor
  · intro output hsource
    obtain ⟨hh, ho⟩ := (computesInTime_iff _ _ _ _).mp hsource
    simpa only [timedAnswer, hh, if_pos, ho] using hu
  · intro hsource
    have hh : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state ≠ none := by
      intro hhalt
      exact hsource _ ((computesInTime_iff _ _ _ _).mpr ⟨hhalt, rfl⟩)
    simpa only [timedAnswer, if_neg hh] using hu

end Turing
```


## ===== TCSlib/Complexity/TuringMachine/MathlibBridge.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.TMToPartrec
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.CodeParser
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Mathlib bridge: the effective scheme

The Mathlib-facing layer behind `Turing.exists_effectiveMachineCode`: it proves
the suffix scanner and prefix operation primitive recursive and converts that
fact into an actual finite binary machine. This module **quarantines the
`Mathlib.Computability.TMToPartrec` import** — Mathlib's recursion-theory and
TM2 development — behind this single module. The canonizer is obtained by the
arbitrary-time compiler route: primitive recursiveness of `Turing.codeCanonical`,
Mathlib's verified compilation of partial recursive functions to its TM2 stack
machines, a private in-model simulation of the compiled stack machine by the
four-work-tape controller `bridgeTM`, and the alphabet-reduction theorem to land
in a binary machine; **no polynomial time bound is claimed**. This module was
split out mechanically from `TCSlib.Complexity.TuringMachine.Encoding` at the
epoch-3→4 merge; its content is the epoch-3 fill, batch A. Its architectural
placement is **pending human review — `AroraBarakChapter1Plan.md` §5, open
design question 1**.

## Main results

* `Turing.exists_effectiveMachineCode` — a concrete effective representation
  scheme exists.
* `Turing.codePrim_machine` — every primitive recursive string function is computed
  by some finite binary machine (no time bound claimed).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

private lemma codePrimUnary : Primrec codeReadUnary := by
  have h := Primrec.list_rec (α := List Bool) (β := Bool) Primrec.id (Primrec.const (none : Option (ℕ × List Bool)))
    (Primrec.to₂ (Primrec.cond (Primrec.fst.comp Primrec.snd)
      (Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.to₂ (Primrec.pair (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd))))
      (Primrec.option_some.comp (Primrec.pair (Primrec.const 0) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))))
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    dsimp only [id, List.recOn] at ih ⊢
    cases b <;> simp [codeReadUnary, ih]

private lemma codePrimBit : Primrec₂ Nat.bit := by
  apply (Primrec.cond Primrec.fst
    (Primrec.succ.comp (Primrec.nat_double.comp Primrec.snd))
    (Primrec.nat_double.comp Primrec.snd)).of_eq
  intro p
  rcases p with ⟨b, n⟩
  cases b <;> simp [Nat.bit]

private lemma codePrimBitsNat : Primrec codeBitsNat :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (codePrimBit.comp₂ (Primrec.fst.comp₂ Primrec₂.right) (Primrec.snd.comp₂ Primrec₂.right))

/-- **Proof sketch.** A list recursion stores the aligned-parser results for both the current suffix and its tail. Adding one input bit can therefore inspect the next bit and reuse the result two positions ahead. This realizes the two-bit recursion using primitive recursive list operations. -/
private lemma codePrimPair : Primrec pairDecode := by
  let step : Bool × List Bool × (Option (List Bool × List Bool) × Option (List Bool × List Bool)) →
      Option (List Bool × List Bool) × Option (List Bool × List Bool) := fun p =>
    ((p.2.1.head?).bind fun b =>
      bif p.1 == b then p.2.2.2.map (fun q => (p.1 :: q.1, q.2))
      else bif p.1 then none else some ([], p.2.1.tail), p.2.2.1)
  have hstep : Primrec step := by
    apply Primrec.pair
    · apply Primrec.option_bind (Primrec.list_head?.comp (Primrec.fst.comp Primrec.snd))
      change Primrec _
      apply Primrec.cond (Primrec.beq.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      · apply Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        exact (Primrec.pair
          (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)).to₂
      · exact Primrec.cond (Primrec.fst.comp Primrec.fst) (Primrec.const none)
          (Primrec.option_some.comp (Primrec.pair (Primrec.const [])
            (Primrec.list_tail.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))))
    · exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_rec (α := List Bool) (β := Bool) Primrec.id
    (Primrec.const (none, none)) (hstep.comp Primrec.snd).to₂
  have he (xs : List Bool) :
      List.recOn xs (none, none) (fun b xs ih => step (b, xs, ih)) =
        (pairDecode xs, pairDecode xs.tail) := by
    induction xs with
    | nil => rfl
    | cons b xs ih =>
      dsimp only [List.recOn] at ih ⊢
      rw [ih]
      cases xs with
      | nil => cases b <;> rfl
      | cons a xs => cases b <;> cases a <;> rfl
  exact (Primrec.fst.comp h).of_eq fun xs => congrArg Prod.fst (he xs)

/-- **Proof sketch.** Use well-founded primitive recursion with the natural number itself as measure and its half as the sole recursive dependency. The zero case emits no bits; otherwise prepend the parity bit to the recursively computed bits of the half. -/
private lemma codePrimBits : Primrec Nat.bits := by
  let deps : ℕ → List ℕ := fun n => if n = 0 then [] else [n.div2]
  let step : ℕ → List (List Bool) → Option (List Bool) := fun n vals =>
    if n = 0 then some [] else vals.head?.map (fun xs => n.bodd :: xs)
  have hd : Primrec deps := Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const []) (Primrec.list_cons.comp Primrec.nat_div2 (Primrec.const []))
  have hs : Primrec₂ step := Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.const (some [])) (Primrec.option_map (Primrec.list_head?.comp Primrec.snd)
      (Primrec.to₂ (Primrec.list_cons.comp (Primrec.nat_bodd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)))
  apply Primrec.nat_omega_rec' Nat.bits (m := id) (l := deps) (g := step) Primrec.id hd hs
  · intro n a ha
    by_cases hn : n = 0
    · simp [deps, hn] at ha
    · simp only [deps, hn, ↓reduceIte, List.mem_singleton] at ha
      subst a
      exact Nat.binaryRec_decreasing hn
  · intro n
    by_cases hn : n = 0
    · simp [step, deps, hn]
    · have hb : n.div2 = 0 → n.bodd = true := by
        intro h
        have he := Nat.bit_bodd_div2 n
        rw [h] at he
        cases hh : n.bodd
        · simp [hh] at he
          exact (hn he.symm).elim
        · rfl
      simp only [deps, step, hn, ↓reduceIte, List.map_cons, List.map_nil, List.head?_cons, Option.map_some]
      congr 1
      exact (Nat.bits_append_bit n.div2 n.bodd hb).symm.trans (congrArg Nat.bits (Nat.bit_bodd_div2 n))

private lemma codePrimSkipPair (valid : Bool → Bool → Bool) : Primrec (codeSkipPair valid) := by
  have hi : Primrec₂ (fun p : Bool × List Bool => fun q : Bool × List Bool =>
      if valid p.1 q.1 then some q.2 else none) :=
    Primrec.ite (Primrec.eq.comp ((Primrec.dom_bool₂ valid).comp
      (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)) (Primrec.const true))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)
  have ho := Primrec.list_casesOn Primrec.snd (Primrec.const none) hi
  exact Primrec.list_casesOn Primrec.id (Primrec.const none) (ho.comp Primrec.snd).to₂

private lemma codePrimSkipFin : Primrec₂ codeSkipFin := by
  unfold codeSkipFin
  apply Primrec.option_bind (codePrimUnary.comp Primrec.snd)
  change Primrec _
  exact Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const none)

private lemma codePrimSkipState : Primrec₂ codeSkipState := by
  have h : Primrec₂ (fun p : ℕ × List Bool => fun q : Bool × List Bool =>
      if q.1 then codeSkipFin p.1 q.2 else some q.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true))
      (codePrimSkipFin.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_casesOn Primrec.snd (Primrec.const none) h

private lemma codePrimSkipAction : Primrec₂ codeSkipAction := by
  unfold codeSkipAction
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  apply Primrec.option_bind ((codePrimSkipPair _).comp Primrec.snd)
  change Primrec _
  exact codePrimSkipState.comp (Primrec.succ.comp
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))) Primrec.snd

private lemma codeSkipRepeat_iter (r : List Bool → Option (List Bool)) (n : ℕ) (xs : List Bool) :
    codeSkipRepeat r n xs = (fun o => o.bind r)^[n] (some xs) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [codeSkipRepeat, Function.iterate_succ_apply]
    cases h : r xs with
    | none =>
      simp only [Option.bind_none, Option.bind_some, h]
      clear ih xs h
      induction n with
      | zero => rfl
      | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih
    | some ys => simpa only [Option.bind_some, Option.bind_some, h] using ih ys

private lemma codePrimRepeat {A : Type} [Primcodable A]
    (r : A → List Bool → Option (List Bool)) (hr : Primrec₂ r)
    (count : A → ℕ) (hn : Primrec count) :
    Primrec₂ (fun a xs => codeSkipRepeat (r a) (count a) xs) := by
  have h := Primrec.nat_iterate (hn.comp Primrec.fst) (Primrec.option_some.comp Primrec.snd)
    (Primrec.option_bind Primrec.snd
      (hr.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂).to₂
  exact h.of_eq fun p => (codeSkipRepeat_iter (r p.1) (count p.1) p.2).symm

private lemma codePrimAll : Primrec (fun xs : List Bool => xs.all id) := by
  have h := Primrec.list_foldr (α := List Bool) (β := Bool) Primrec.id (Primrec.const true)
    ((Primrec.dom_bool₂ Bool.and).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun xs => by
    dsimp only [id]
    induction xs with
    | nil => rfl
    | cons b xs ih => simpa only [List.foldr_cons, List.all_cons, id_eq] using congrArg (fun z => b && z) ih

/-- **Proof sketch.** Compose primitive recursive readers, comparisons, and fixed-count iterations in the exact order of the erased parser. The canonical-count check and minimum-length check surround the state and record scans. The final branch accepts precisely an all-true suffix. -/
private lemma codePrimScan : Primrec codeScan := by
  unfold codeScan
  apply Primrec.option_bind codePrimPair
  change Primrec _
  apply Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
    (codePrimBits.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd)))).not)
    (Primrec.const none)
  apply Primrec.ite (Primrec.nat_lt.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_mul.comp (Primrec.const 81) (Primrec.succ.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd)))))
    (Primrec.const none)
  apply Primrec.option_bind (codePrimSkipFin.comp
    (Primrec.succ.comp (codePrimBitsNat.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd))
  change Primrec _
  have hr := codePrimRepeat _ (codePrimRepeat _ (codePrimRepeat _ codePrimSkipAction (fun _ => 3) (Primrec.const 3))
    (fun _ => 3) (Primrec.const 3)) (fun n => n + 1) Primrec.succ
  apply Primrec.option_bind (hr.comp
    (codePrimBitsNat.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  change Primrec _
  exact Primrec.ite (Primrec.eq.comp (codePrimAll.comp Primrec.snd) (Primrec.const true))
    (Primrec.option_some.comp Primrec.snd) (Primrec.const none)

private lemma codePrimDrop : Primrec₂ (fun xs : List Bool => fun n => xs.drop n) := by
  have h := Primrec.nat_iterate (α := List Bool × ℕ) (β := List Bool) Primrec.snd Primrec.fst (Primrec.list_tail.comp Primrec.snd).to₂
  apply h.of_eq
  intro p
  rcases p with ⟨xs, n⟩
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    cases xs <;> simp

private lemma codePrimPrefix : Primrec₂ (fun xs : List Bool => fun n => xs.take (xs.length - n)) := by
  have h := Primrec.list_reverse.comp (codePrimDrop.comp (Primrec.list_reverse.comp Primrec.fst) Primrec.snd)
  exact h.of_eq fun p => by simp only [List.reverse_drop, List.reverse_reverse, List.length_reverse]

private lemma codePrimCanonical : Primrec codeCanonical :=
  Primrec.option_casesOn codePrimScan (Primrec.const codeFallback.serialize)
    (codePrimPrefix.comp Primrec.fst (Primrec.list_length.comp Primrec.snd))


private abbrev BridgeAlphabet := Bool ⊕ PartrecToTM2.Γ'

private def bridgeIndex : PartrecToTM2.K' → Fin 4
  | .main => 0
  | .rev => 1
  | .aux => 2
  | .stack => 3

private def bridgeStack (xs : List PartrecToTM2.Γ') (z : ℤ) : Option BridgeAlphabet :=
  if 0 ≤ z + xs.length then (xs[(z + xs.length).toNat]?).map Sum.inr else none

private lemma bridgeStack_read (xs : List PartrecToTM2.Γ') :
    bridgeStack xs (-(xs.length : ℤ)) = xs.head?.map Sum.inr := by
  simp only [bridgeStack, neg_add_cancel, le_refl, if_pos, Int.toNat_zero]
  cases xs <;> rfl

private lemma bridgeStack_nil : bridgeStack [] = fun _ => none := by
  funext z
  simp [bridgeStack]

private lemma bridgeStack_push (xs : List PartrecToTM2.Γ') (a : PartrecToTM2.Γ') :
    Function.update (bridgeStack xs) (-(xs.length : ℤ) - 1) (some (.inr a)) =
      bridgeStack (a :: xs) := by
  funext z
  by_cases hz : z = -(xs.length : ℤ) - 1
  · subst z
    simp [bridgeStack]
  · rw [Function.update_of_ne hz]
    by_cases h : 0 ≤ z + xs.length
    · have h' : 0 ≤ z + (a :: xs).length := by simp; omega
      have hi : (z + (a :: xs).length).toNat = (z + xs.length).toNat + 1 := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        omega
      simp only [bridgeStack, if_pos h, if_pos h', hi, List.getElem?_cons_succ]
    · have h' : ¬0 ≤ z + (a :: xs).length := by simp; omega
      simp only [bridgeStack, if_neg h, if_neg h']

private lemma bridgeStack_pop (xs : List PartrecToTM2.Γ') (a : PartrecToTM2.Γ') :
    Function.update (bridgeStack (a :: xs)) (-((a :: xs).length : ℤ)) none =
      bridgeStack xs := by
  rw [← bridgeStack_push]
  have hi : -((a :: xs).length : ℤ) = -(xs.length : ℤ) - 1 := by simp; omega
  rw [hi, Function.update_idem]
  have hr : bridgeStack xs (-(xs.length : ℤ) - 1) = none := by
    have h : ¬0 ≤ -(xs.length : ℤ) - 1 + xs.length := by omega
    simp only [bridgeStack, if_neg h]
  rw [← hr, Function.update_eq_self]

private def bridgeKey : Fin 4 → PartrecToTM2.K' :=
  Fin.cases .main (Fin.cases .rev (Fin.cases .aux (fun _ => .stack)))

private lemma bridgeKey_index (k : PartrecToTM2.K') : bridgeKey (bridgeIndex k) = k := by
  cases k <;> rfl

private lemma bridgeIndex_key (i : Fin 4) : bridgeIndex (bridgeKey i) = i := by
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

private inductive BridgeState (Q : Type)
  | scan | startCons | startBit | back
  | pushInput (b : Bool)
  | exec (q : Q) (v : Option PartrecToTM2.Γ')
  | push (q : Q) (v : Option PartrecToTM2.Γ')
  | emit (carry : Option Bool)
  deriving Fintype, DecidableEq

private noncomputable def bridgeSupp (c : ToPartrec.Code) :=
  TM2.stmts PartrecToTM2.tr (PartrecToTM2.codeSupp c .halt)

private abbrev BridgeQ (c : ToPartrec.Code) := {q // q ∈ bridgeSupp c}

private def bridgeBit : Bool → PartrecToTM2.Γ'
  | false => .bit0
  | true => .bit1

private noncomputable def bridgeExec (c : ToPartrec.Code)
    (q : Option PartrecToTM2.Stmt') (v : Option PartrecToTM2.Γ') :
    Option (BridgeState (BridgeQ c)) := by
  classical
  exact if h : q ∈ bridgeSupp c then some (.exec ⟨q, h⟩ v) else none

private def bridgeIdle {Q : Type} (q : Option Q) : Action 4 BridgeAlphabet Q :=
  ⟨.zero, fun _ => (none, .zero), none, q⟩

private def bridgeOne {Q : Type} (k : Fin 4) (wr : Option (Option BridgeAlphabet))
    (d : SignType) (q : Option Q) : Action 4 BridgeAlphabet Q :=
  ⟨.zero, fun i => if i = k then (wr, d) else (none, .zero), none, q⟩

/-- A four-work-tape controller for Mathlib's proved partial-recursive compiler.
Each source stack occupies the negative cells ending at -1; its head points to the
stack top, and an empty stack has a blank head at zero. Source statements range
over the finite support of the selected program. Input bits live in the left
summand of the finite alphabet and stack symbols in the right summand. -/
private noncomputable def bridgeTM (c : ToPartrec.Code) : FinTM BridgeAlphabet := by
  classical
  exact {
    k := 4
    State := BridgeState (BridgeQ c)
    tm := {
      q₀ := .scan
      tr := fun q inp work =>
        match q with
        | .scan =>
          if inp.isSome then ⟨.pos, fun _ => (none, .zero), none, some .scan⟩
          else bridgeOne 0 none .neg (some .startCons)
        | .startCons => bridgeOne 0 (some (some (.inr .cons))) .neg (some .startBit)
        | .startBit => ⟨.neg, fun i => if i = 0 then
            (some (some (.inr .bit1)), .zero) else (none, .zero), none, some .back⟩
        | .back => match inp with
          | some (.inl b) => bridgeOne 0 none .neg (some (.pushInput b))
          | _ => bridgeIdle (bridgeExec c (some (PartrecToTM2.tr (PartrecToTM2.trNormal c .halt))) none)
        | .pushInput b => ⟨.neg, fun i => if i = 0 then
            (some (some (.inr (bridgeBit b))), .zero) else (none, .zero), none, some .back⟩
        | .exec q v =>
          match q.val with
          | none => bridgeIdle (some (.emit none))
          | some stmt => match stmt with
            | .push k _ _ => bridgeOne (bridgeIndex k) none .neg (some (.push q v))
            | .peek k f tail => bridgeIdle (bridgeExec c (some tail) (f v ((work (bridgeIndex k)).bind Sum.getRight?)))
            | .pop k f tail =>
              let w := work (bridgeIndex k)
              bridgeOne (bridgeIndex k) (some none) (if w.isSome then .pos else .zero)
                (bridgeExec c (some tail) (f v (w.bind Sum.getRight?)))
            | .load f tail => bridgeIdle (bridgeExec c (some tail) (f v))
            | .branch f yes no => bridgeIdle (bridgeExec c (some (if f v then yes else no)) v)
            | .goto f => bridgeIdle (bridgeExec c (some (PartrecToTM2.tr (f v))) v)
            | .halt => bridgeIdle (bridgeExec c none v)
        | .push q v =>
          match q.val with
          | some (.push k f tail) =>
            bridgeOne (bridgeIndex k) (some (some (.inr (f v)))) .zero (bridgeExec c (some tail) v)
          | _ => bridgeIdle none
        | .emit carry =>
          match work 0 with
          | some (.inr .bit0) =>
            { bridgeOne 0 (some none) .pos (some (.emit (some false))) with output := carry.map Sum.inl }
          | some (.inr .bit1) =>
            { bridgeOne 0 (some none) .pos (some (.emit (some true))) with output := carry.map Sum.inl }
          | _ => bridgeIdle none } }

private def bridgeCfg (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) :
    Cfg 4 BridgeAlphabet (BridgeState (BridgeQ c)) x :=
  ⟨q, p, fun i => bridgeStack (st (bridgeKey i)),
    fun i => -((st (bridgeKey i)).length : ℤ), out⟩

private lemma bridgeCfg_read (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') :
    (bridgeCfg c q p st out).workTapeSymbols (bridgeIndex k) =
      (st k).head?.map Sum.inr := by
  simp only [Cfg.workTapeSymbols, bridgeCfg, bridgeKey_index, bridgeStack_read]

private def bridgeReach {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) (a b : Cfg k A Q x) : Prop := ∃ t, M.runFrom a t = b

private lemma bridgeReach_refl {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) (a : Cfg k A Q x) : bridgeReach M a a := ⟨0, rfl⟩

private lemma bridgeReach_step {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) (a : Cfg k A Q x) : bridgeReach M a (M.step a) := ⟨1, rfl⟩

private lemma bridgeReach_trans {k : ℕ} {A Q : Type} {x : List A}
    (M : MultiTapeTM k A Q) {a b d : Cfg k A Q x}
    (h : bridgeReach M a b) (h' : bridgeReach M b d) : bridgeReach M a d := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, ht⟩ := h'
  exact ⟨s + t, by rw [MultiTapeTM.runFrom_add, hs, ht]⟩

private lemma bridgeCfg_idle (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) :
    (bridgeIdle q').apply (bridgeCfg c q p st out) = bridgeCfg c q' p st out := by
  apply Cfg.ext <;> simp [bridgeIdle, bridgeCfg]

/-- **Proof sketch.** On the selected tape, erasing the current top cell and moving right gives the representation of the tail stack. Other tapes and the input head stay fixed; configuration extensionality combines these field equations. -/
private lemma bridgeCfg_pop (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') (xs : List PartrecToTM2.Γ')
    (hs : st k = a :: xs) :
    (bridgeOne (bridgeIndex k) (some none) .pos q').apply (bridgeCfg c q p st out) =
      bridgeCfg c q' p (Function.update st k xs) out := by
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero p
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, hs]
      rw [bridgeKey_index, Function.update_self]
      exact bridgeStack_pop xs a
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply_workTapes, bridgeOne, bridgeCfg, hi, hk]
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, hs, SignType.pos_eq_one, SignType.coe_one, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      rw [bridgeKey_index, Function.update_self]
      omega
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply, bridgeOne, bridgeCfg, hi, hk]
  · simp [Action.apply, bridgeOne, bridgeCfg]

/-- **Proof sketch.** Move the selected work head one cell left, then write the pushed symbol. The stack representation lemma identifies the resulting tape with the extended stack. All other tapes and the input/output components are unchanged. -/
private lemma bridgeCfg_push (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q qm q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') :
    (bridgeOne (bridgeIndex k) (some (some (.inr a))) .zero q').apply
      ((bridgeOne (bridgeIndex k) none .neg qm).apply (bridgeCfg c q p st out)) =
      bridgeCfg c q' p (Function.update st k (a :: st k)) out := by
  apply Cfg.ext
  · rfl
  · simp [Action.apply, bridgeOne, bridgeCfg]
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one]
      rw [bridgeKey_index, Function.update_self]
      exact bridgeStack_push (st k) a
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply_workTapes, bridgeOne, bridgeCfg, hi, hk]
  · funext i
    by_cases hi : i = bridgeIndex k
    · subst i
      simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index,
        Function.update_self, SignType.neg_eq_neg_one, SignType.coe_neg_one,
        SignType.zero_eq_zero, SignType.coe_zero, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [bridgeKey_index, Function.update_self]
      simp
      omega
    · have hk : bridgeKey i ≠ k := by
        intro h
        exact hi (by rw [← bridgeIndex_key i, h])
      simp [Action.apply, bridgeOne, bridgeCfg, hi, hk]
  · simp [Action.apply, bridgeOne, bridgeCfg]

/-- **Proof sketch.** For an empty stack the tape is blank, so the machine erases a blank and stays. For a nonempty stack, apply the pop configuration lemma. These two cases match the stack machine pop semantics. -/
private lemma bridgeCfg_pop_any (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') :
    (bridgeOne (bridgeIndex k) (some none)
      (if (st k).head?.isSome then .pos else .zero) q').apply (bridgeCfg c q p st out) =
      bridgeCfg c q' p (Function.update st k (st k).tail) out := by
  cases hs : st k with
  | nil =>
    have hu : Function.update st k [] = st := by rw [← hs, Function.update_eq_self]
    simp only [List.head?_nil, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, List.tail_nil, hu]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero p
    · funext i
      by_cases hi : i = bridgeIndex k
      · subst i
        simp only [Action.apply, bridgeOne, bridgeCfg, ↓reduceIte, bridgeKey_index, hs,
          bridgeStack_nil]
        funext z
        simp
      · simp [Action.apply, bridgeOne, bridgeCfg, hi]
    · funext i
      by_cases hi : i = bridgeIndex k <;> simp [Action.apply, bridgeOne, bridgeCfg, hi]
    · simp [Action.apply, bridgeOne, bridgeCfg]
  | cons a xs =>
    simp only [List.head?_cons, Option.isSome_some, ↓reduceIte, List.tail_cons]
    exact bridgeCfg_pop c q q' p st out k a xs hs

private lemma bridgeExec_mem (c : ToPartrec.Code) (q : Option PartrecToTM2.Stmt')
    (v : Option PartrecToTM2.Γ') (h : q ∈ bridgeSupp c) :
    bridgeExec c q v = some (.exec ⟨q, h⟩ v) := by
  classical
  simp [bridgeExec, h]

private lemma bridge_step (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q : BridgeState (BridgeQ c)) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) :
    (bridgeTM c).tm.step (bridgeCfg c (some q) p st out) =
      ((bridgeTM c).tm.tr q (bridgeCfg c (some q) p st out).inputSymbol
        (bridgeCfg c (some q) p st out).workTapeSymbols).apply
          (bridgeCfg c (some q) p st out) := rfl

private lemma bridge_sub (c : ToPartrec.Code) (q tail : PartrecToTM2.Stmt')
    (hq : some q ∈ bridgeSupp c) (h : tail ∈ TM2.stmts₁ q) :
    some tail ∈ bridgeSupp c := TM2.stmts_trans h hq

private lemma bridge_none (c : ToPartrec.Code) : none ∈ bridgeSupp c := by
  classical
  simp [bridgeSupp, TM2.stmts]

/-- **Proof sketch.** Induct on the stack-machine statement. Push uses two native transitions; pop, peek, and register load use one before continuing recursively. Branch executes its chosen substatement. Goto and halt update the control label directly. The finite support lemma ensures every recursive substatement remains an available native state. -/
private lemma bridge_statement (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (out : List BridgeAlphabet) (q : PartrecToTM2.Stmt') :
    ∀ (v : Option PartrecToTM2.Γ') (st : PartrecToTM2.K' → List PartrecToTM2.Γ')
      (_hq : some q ∈ bridgeSupp c),
    bridgeReach (bridgeTM c).tm (bridgeCfg c (bridgeExec c (some q) v) p st out)
      (bridgeCfg c (bridgeExec c ((TM2.stepAux q v st).l.map PartrecToTM2.tr)
        (TM2.stepAux q v st).var) p (TM2.stepAux q v st).stk out) := by
  classical
  induction q with
  | push k f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) v)
      p (Function.update st k (f v :: st k)) out) ?_ (ih v _ ht)
    refine ⟨2, ?_⟩
    rw [bridgeExec_mem c _ v hq, show 2 = 1 + 1 from rfl,
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    change (bridgeTM c).tm.step
      ((bridgeOne (bridgeIndex k) none .neg (some (.push ⟨some (.push k f tail), hq⟩ v))).apply
        (bridgeCfg c (some (.exec ⟨some (.push k f tail), hq⟩ v)) p st out)) = _
    unfold MultiTapeTM.step
    dsimp only [Action.apply, bridgeTM]
    exact bridgeCfg_push c _ _ _ p st out k (f v)
  | peek k f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) (f v (st k).head?))
      p st out) ?_ (ih _ _ ht)
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    rw [bridgeCfg_read]
    have hh : ((st k).head?.map (Sum.inr (α := Bool))).bind Sum.getRight? = (st k).head? := by
      cases (st k).head? <;> rfl
    rw [hh]
    exact bridgeCfg_idle c _ _ p st out
  | pop k f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) (f v (st k).head?))
      p (Function.update st k (st k).tail) out) ?_ (ih _ _ ht)
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    rw [bridgeCfg_read]
    have hh : ((st k).head?.map (Sum.inr (α := Bool))).bind Sum.getRight? = (st k).head? := by
      cases (st k).head? <;> rfl
    rw [hh]
    simp only [Option.isSome_map]
    exact bridgeCfg_pop_any c _ _ p st out k
  | load f tail ih =>
    intro v st hq
    have ht := bridge_sub c _ tail hq (by exact Finset.mem_insert_of_mem TM2.stmts₁_self)
    apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some tail) (f v)) p st out)
      ?_ (ih _ _ ht)
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM]
    exact bridgeCfg_idle c _ _ p st out
  | branch f yes no ihy ihn =>
    intro v st hq
    cases hv : f v with
    | false =>
      have ht := bridge_sub c _ no hq (by exact Finset.mem_insert_of_mem (Finset.mem_union_right _ TM2.stmts₁_self))
      apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some no) v) p st out)
        ?_ (by simpa [TM2.stepAux, hv] using ihn v st ht)
      refine ⟨1, ?_⟩
      rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
        MultiTapeTM.runFrom_zero, bridge_step]
      simp only [bridgeTM, hv, Bool.false_eq_true, ↓reduceIte]
      exact bridgeCfg_idle c _ _ p st out
    | true =>
      have ht := bridge_sub c _ yes hq (by exact Finset.mem_insert_of_mem (Finset.mem_union_left _ TM2.stmts₁_self))
      apply bridgeReach_trans _ (b := bridgeCfg c (bridgeExec c (some yes) v) p st out)
        ?_ (by simpa [TM2.stepAux, hv] using ihy v st ht)
      refine ⟨1, ?_⟩
      rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
        MultiTapeTM.runFrom_zero, bridge_step]
      simp only [bridgeTM, hv, ↓reduceIte]
      exact bridgeCfg_idle c _ _ p st out
  | goto f =>
    intro v st hq
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM, TM2.stepAux, Option.map_some]
    exact bridgeCfg_idle c _ _ p st out
  | halt =>
    intro v st hq
    refine ⟨1, ?_⟩
    rw [bridgeExec_mem c _ v hq, MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_step]
    simp only [bridgeTM, TM2.stepAux, Option.map_none]
    exact bridgeCfg_idle c _ _ p st out

private lemma bridge_label (c : ToPartrec.Code) (l : Option PartrecToTM2.Λ')
    (h : l ∈ Finset.insertNone (PartrecToTM2.codeSupp c .halt)) :
    l.map PartrecToTM2.tr ∈ bridgeSupp c := by
  classical
  cases l with
  | none => exact bridge_none c
  | some l =>
    have hl := Finset.some_mem_insertNone.mp h
    apply Finset.some_mem_insertNone.mpr
    exact Finset.mem_biUnion.mpr ⟨l, hl, TM2.stmts₁_self⟩

/-- **Proof sketch.** Induct on finite reachability of the compiled stack machine. Its support theorem preserves membership in the finite label set. For each source step, the statement simulation supplies a finite native execution, and transitivity concatenates these executions. -/
private lemma bridge_simulate (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (out : List BridgeAlphabet)
    (a b : PartrecToTM2.Cfg') (h : TM2.Reaches PartrecToTM2.tr a b)
    (ha : a.l ∈ Finset.insertNone (PartrecToTM2.codeSupp c .halt)) :
    b.l ∈ Finset.insertNone (PartrecToTM2.codeSupp c .halt) ∧
    bridgeReach (bridgeTM c).tm
      (bridgeCfg c (bridgeExec c (a.l.map PartrecToTM2.tr) a.var) p a.stk out)
      (bridgeCfg c (bridgeExec c (b.l.map PartrecToTM2.tr) b.var) p b.stk out) := by
  classical
  letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal c .halt⟩
  have support := PartrecToTM2.tr_supports c PartrecToTM2.Cont'.halt
  induction h with
  | refl => exact ⟨ha, bridgeReach_refl _ _⟩
  | @tail b d h hd ih =>
    refine ⟨TM2.step_supports _ support hd ih.1, bridgeReach_trans _ ih.2 ?_⟩
    rcases b with ⟨l, v, st⟩
    cases l with
    | none => simp [TM2.step] at hd
    | some l =>
      simp only [TM2.step, Option.mem_def, Option.some.injEq] at hd
      subst d
      exact bridge_statement c p out (PartrecToTM2.tr l) v st (bridge_label c _ ih.1)

private def bridgeNumber (xs : List Bool) : ℕ := xs.foldr Nat.bit 1

private def bridgeWord (xs : List Bool) : List PartrecToTM2.Γ' :=
  xs.map bridgeBit ++ [.bit1, .cons]

private lemma bridgeNumber_pos (xs : List Bool) : 0 < bridgeNumber xs := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    cases b <;> simp only [bridgeNumber, List.foldr_cons, Nat.bit_val] at * <;> omega

/-- **Proof sketch.** Encode a bit string as its low-to-high bits followed by a high true sentinel. Induction on the string matches each binary numeral constructor with the corresponding stack symbol; positivity rules out the zero numeral case. Append the compiled list terminator. -/
private lemma bridgeWord_number (xs : List Bool) :
    PartrecToTM2.trList [bridgeNumber xs] = bridgeWord xs := by
  suffices h : PartrecToTM2.trNat (bridgeNumber xs) = xs.map bridgeBit ++ [.bit1] by
    simpa [PartrecToTM2.trList, bridgeWord, List.append_assoc] using
      congrArg (fun zs => zs ++ [PartrecToTM2.Γ'.cons]) h
  induction xs with
  | nil => simp [bridgeNumber, PartrecToTM2.trNat, PartrecToTM2.trNum,
      PartrecToTM2.trPosNum]
  | cons b xs ih =>
    have hp := bridgeNumber_pos xs
    cases hn : (bridgeNumber xs : Num) with
    | zero =>
      have hz := congrArg (fun n : Num => (n : ℕ)) hn
      simp only [Num.to_of_nat, Num.cast_zero] at hz
      change bridgeNumber xs = 0 at hz
      omega
    | pos n =>
      have hword : PartrecToTM2.trPosNum n = xs.map bridgeBit ++ [.bit1] := by
        simpa only [PartrecToTM2.trNat, hn, PartrecToTM2.trNum] using ih
      change PartrecToTM2.trNum (Num.ofNat' (Nat.bit b (bridgeNumber xs))) = _
      rw [Num.ofNat'_bit, Num.ofNat'_eq, hn]
      cases b <;> simp [Num.bit0, Num.bit1, PartrecToTM2.trNum,
        PartrecToTM2.trPosNum, hword, bridgeBit]

private lemma bridgeCfg_push_input (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q qm q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') (d : SignType) :
    ({ bridgeOne (bridgeIndex k) (some (some (.inr a))) .zero q' with inputTape := d }).apply
      ((bridgeOne (bridgeIndex k) none .neg qm).apply (bridgeCfg c q p st out)) =
      bridgeCfg c q' (moveInputPos p d) (Function.update st k (a :: st k)) out := by
  have h := bridgeCfg_push c q qm q' p st out k a
  apply Cfg.ext
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.state h
  · simp [Action.apply, bridgeOne, bridgeCfg]
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapes h
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapePos h
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.output h

private def bridgeStore (xs : List PartrecToTM2.Γ') : PartrecToTM2.K' → List PartrecToTM2.Γ' :=
  PartrecToTM2.K'.elim xs [] [] []

private lemma bridgeStore_push (xs : List PartrecToTM2.Γ') (b : PartrecToTM2.Γ') :
    Function.update (bridgeStore xs) .main (b :: bridgeStore xs .main) = bridgeStore (b :: xs) := by
  funext k
  cases k <;> simp [bridgeStore, PartrecToTM2.K'.elim]

/-- **Proof sketch.** Induct on the input head position while scanning backward. Each bit is pushed onto the main stack in two steps, extending the already loaded suffix. At the left endmarker the complete word is present and execution enters the compiled program. -/
private lemma bridge_back (c : ToPartrec.Code) (x : List Bool) :
    ∀ j (hj : j ≤ x.length),
    bridgeReach (bridgeTM c).tm
      (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨j, by simp; omega⟩
        (bridgeStore (bridgeWord (x.drop j))) [])
      (bridgeCfg c (bridgeExec c (some (PartrecToTM2.tr (PartrecToTM2.trNormal c .halt))) none)
        0 (bridgeStore (bridgeWord x)) []) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨1, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
    have hi : (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨0, by simp⟩
      (bridgeStore (bridgeWord (x.drop 0))) []).inputSymbol = none := by
      simp [bridgeCfg, Cfg.inputSymbol]
    rw [hi]
    simp only [bridgeTM, List.drop_zero]
    rw [bridgeCfg_idle]
    congr 1
  | succ j ih =>
    intro hj
    apply bridgeReach_trans _ (b := bridgeCfg (x := x.map Sum.inl) c (some .back)
      ⟨j, by simp; omega⟩ (bridgeStore (bridgeWord (x.drop j))) []) ?_ (ih (by omega))
    refine ⟨2, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
    have hi : (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨j + 1, by simp; omega⟩
      (bridgeStore (bridgeWord (x.drop (j + 1)))) []).inputSymbol = some (Sum.inl x[j]) := by
      exact (inputSymbolInner (cfg := bridgeCfg (x := x.map Sum.inl) c (some .back)
        ⟨j + 1, by simp; omega⟩ (bridgeStore (bridgeWord (x.drop (j + 1)))) []) j
        (by simp [bridgeCfg]; omega) (by simp; omega)).trans
        (congrArg some (List.getElem_map (Sum.inl : Bool → BridgeAlphabet)))
    rw [hi]
    simp only [bridgeTM]
    change ({ bridgeOne (bridgeIndex .main) (some (some (.inr (bridgeBit x[j]))))
      .zero (some (BridgeState.back : BridgeState (BridgeQ c))) with inputTape := .neg }).apply
        ((bridgeOne (bridgeIndex .main) none .neg (some (BridgeState.pushInput (Q := BridgeQ c) x[j]))).apply
          (bridgeCfg (x := x.map Sum.inl) c (some .back) ⟨j + 1, by simp; omega⟩
            (bridgeStore (bridgeWord (x.drop (j + 1)))) [])) = _
    rw [bridgeCfg_push_input]
    simp only [bridgeStore_push]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    have hw : bridgeBit x[j] :: bridgeWord (x.drop (j + 1)) = bridgeWord (x.drop j) := by
      rw [List.drop_eq_getElem_cons (by omega : j < x.length)]
      rfl
    rw [hw]
    apply Cfg.ext
    · rfl
    · apply Fin.ext; simp
    · rfl
    · rfl
    · rfl

private lemma bridgeStore_nil : bridgeStore [] = fun _ => [] := by
  funext k
  cases k <;> rfl

private lemma bridgeStore_at (xs : List PartrecToTM2.Γ') (i : Fin 4) :
    bridgeStore xs (bridgeKey i) = if i = 0 then xs else [] := by
  by_cases hi : i = 0
  · subst i; rfl
  · have hk : bridgeKey i ≠ .main := by
      intro h
      apply hi
      rw [← bridgeIndex_key i, h]
      rfl
    cases h : bridgeKey i <;> simp [bridgeStore, PartrecToTM2.K'.elim, hi, hk, h] at *

/-- **Proof sketch.** Induct on the number of input symbols passed. Before the right endmarker every symbol is nonblank, so the controller moves right without changing any work tape or output. -/
private lemma bridge_scan (c : ToPartrec.Code) (x : List Bool) : ∀ j (hj : j ≤ x.length),
    (bridgeTM c).tm.runFrom ((bridgeTM c).tm.initCfg (x.map Sum.inl)) j =
      bridgeCfg c (some .scan) ⟨j + 1, by simp; omega⟩ (bridgeStore []) [] := by
  intro j
  induction j with
  | zero =>
    intro _
    apply Cfg.ext <;> simp [MultiTapeTM.runFrom, bridgeTM, bridgeCfg, bridgeStore_nil,
      bridgeStack_nil, MultiTapeTM.initCfg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), bridge_step]
    have hi : (bridgeCfg (x := x.map Sum.inl) c (some .scan) ⟨j + 1, by simp; omega⟩
      (bridgeStore []) []).inputSymbol = some (Sum.inl x[j]) := by
      exact (inputSymbolInner (cfg := bridgeCfg (x := x.map Sum.inl) c (some .scan)
        ⟨j + 1, by simp; omega⟩ (bridgeStore []) []) j
        (by simp [bridgeCfg]; omega) (by simp; omega)).trans
        (congrArg some (List.getElem_map (Sum.inl : Bool → BridgeAlphabet)))
    rw [hi]
    simp only [bridgeTM, Option.isSome_some, ↓reduceIte]
    apply Cfg.ext
    · rfl
    · change moveInputPos ⟨j + 1, _⟩ .pos = _
      rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
      rfl
    · rfl
    · funext i; simp [Action.apply, bridgeCfg]
    · rfl

/-- **Proof sketch.** At the right endmarker, three transitions create the list terminator and high true sentinel on the main tape, then move the input head left. Extensionality verifies the empty stacks on the other tapes and the exact two-cell main stack. -/
private lemma bridge_seed (c : ToPartrec.Code) (x : List Bool) :
    (bridgeTM c).tm.runFrom
      (bridgeCfg (x := x.map Sum.inl) c (some .scan) ⟨x.length + 1, by simp⟩ (bridgeStore []) []) 3 =
      bridgeCfg c (some .back) ⟨x.length, by simp⟩ (bridgeStore [.bit1, .cons]) [] := by
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
    MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
  have hi : (bridgeCfg (x := x.map Sum.inl) c (some .scan) ⟨x.length + 1, by simp⟩
    (bridgeStore []) []).inputSymbol = none := by
    simp [bridgeCfg, Cfg.inputSymbol, Fin.ext_iff]
  rw [hi]
  simp only [bridgeTM, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  unfold MultiTapeTM.step
  dsimp only [Action.apply, bridgeOne, bridgeTM]
  apply Cfg.ext
  · rfl
  · simp only [Action.apply, bridgeCfg, bridgeOne, SignType.zero_eq_zero,
      moveInputPos_zero]
    rw [moveInputPos_neg_of_ne_left _ (by simp [Fin.ext_iff])]
    apply Fin.ext
    simp
  · funext i
    by_cases hi : i = 0
    · subst i
      simp only [bridgeCfg, bridgeStore_at, ↓reduceIte, List.length_nil, Nat.cast_zero,
        neg_zero, SignType.zero_eq_zero, SignType.coe_zero, SignType.neg_eq_neg_one,
        SignType.coe_neg_one, zero_add]
      change Function.update (Function.update (bridgeStack []) (-1) (some (.inr .cons)))
        (-2) (some (.inr .bit1)) = bridgeStack [.bit1, .cons]
      rw [show (-1 : ℤ) = -(([] : List PartrecToTM2.Γ').length : ℤ) - 1 from rfl,
        bridgeStack_push, show (-2 : ℤ) = -(([PartrecToTM2.Γ'.cons]).length : ℤ) - 1 from rfl,
        bridgeStack_push]
    · simp [bridgeCfg, bridgeStore_at, hi]
  · funext i
    by_cases hi : i = 0 <;> simp [bridgeCfg, bridgeStore_at, hi]
  · rfl

private lemma bridge_start (c : ToPartrec.Code) (x : List Bool) :
    bridgeReach (bridgeTM c).tm ((bridgeTM c).tm.initCfg (x.map Sum.inl))
      (bridgeCfg c (bridgeExec c (some (PartrecToTM2.tr (PartrecToTM2.trNormal c .halt))) none)
        0 (bridgeStore (bridgeWord x)) []) := by
  apply bridgeReach_trans _ ⟨x.length, bridge_scan c x _ (le_refl _)⟩
  apply bridgeReach_trans _ ⟨3, bridge_seed c x⟩
  simpa only [List.drop_length, bridgeWord, List.map_nil, List.nil_append] using
    bridge_back c x x.length (le_refl _)

private lemma bridgeCfg_pop_emit (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (q q' : Option (BridgeState (BridgeQ c))) (p : Fin (x.length + 2))
    (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet)
    (k : PartrecToTM2.K') (a : PartrecToTM2.Γ') (xs : List PartrecToTM2.Γ')
    (hs : st k = a :: xs) (e : Option BridgeAlphabet) :
    ({ bridgeOne (bridgeIndex k) (some none) .pos q' with output := e }).apply
      (bridgeCfg c q p st out) =
      bridgeCfg c q' p (Function.update st k xs) (out ++ e.toList) := by
  have h := bridgeCfg_pop c q q' p st out k a xs hs
  apply Cfg.ext
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.state h
  · exact moveInputPos_zero p
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapes h
  · simpa only [Action.apply, bridgeCfg] using congrArg Cfg.workTapePos h
  · rfl

private lemma bridge_emit_step (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (st : PartrecToTM2.K' → List PartrecToTM2.Γ')
    (out : List BridgeAlphabet) (carry : Option Bool) (b : Bool)
    (xs : List PartrecToTM2.Γ') (hs : st .main = bridgeBit b :: xs) :
    (bridgeTM c).tm.step (bridgeCfg c (some (.emit carry)) p st out) =
      bridgeCfg c (some (.emit (some b))) p (Function.update st .main xs)
        (out ++ carry.toList.map Sum.inl) := by
  rw [bridge_step]
  have hr := bridgeCfg_read c (some (.emit carry)) p st out .main
  rw [hs] at hr
  change (bridgeCfg c (some (.emit carry)) p st out).workTapeSymbols 0 = some (.inr (bridgeBit b)) at hr
  cases b <;> simp only [bridgeTM, hr, bridgeBit]
  all_goals
    simpa only [Option.toList_map] using bridgeCfg_pop_emit c (some (.emit carry)) _ p st out
      .main _ xs hs (carry.map Sum.inl)

/-- **Proof sketch.** Induct on the output bit string. The controller keeps one pending bit and emits the previous bit while advancing, so the last pending high sentinel is discarded at the list terminator. The empty-string case still consumes the sentinel and terminator without emitting a bit. -/
private lemma bridge_emit (c : ToPartrec.Code) {x : List BridgeAlphabet}
    (p : Fin (x.length + 2)) (xs : List Bool) :
    ∀ (st : PartrecToTM2.K' → List PartrecToTM2.Γ') (out : List BridgeAlphabet) (carry : Option Bool),
    st .main = bridgeWord xs →
    bridgeReach (bridgeTM c).tm (bridgeCfg c (some (.emit carry)) p st out)
      (bridgeCfg c none p (Function.update st .main [.cons])
        (out ++ carry.toList.map Sum.inl ++ xs.map Sum.inl)) := by
  induction xs with
  | nil =>
    intro st out carry hs
    refine ⟨2, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step',
      MultiTapeTM.runFrom_zero, bridge_emit_step c p st out carry true [.cons] hs, bridge_step]
    have hr := bridgeCfg_read c (some (.emit (some true))) p (Function.update st .main [.cons])
      (out ++ carry.toList.map Sum.inl) .main
    simp only [Function.update_self, List.head?_cons, Option.map_some] at hr
    change (bridgeCfg c (some (.emit (some true))) p (Function.update st .main [.cons])
      (out ++ carry.toList.map Sum.inl)).workTapeSymbols 0 = some (.inr .cons) at hr
    simp only [bridgeTM, hr, List.map_nil, List.append_nil]
    exact bridgeCfg_idle c _ none p (Function.update st .main [.cons]) _
  | cons b xs ih =>
    intro st out carry hs
    have hs' : st .main = bridgeBit b :: bridgeWord xs := hs
    apply bridgeReach_trans _ (b := bridgeCfg c (some (.emit (some b))) p
      (Function.update st .main (bridgeWord xs)) (out ++ carry.toList.map Sum.inl))
    · exact ⟨1, by simpa only [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero] using
        bridge_emit_step c p st out carry b (bridgeWord xs) hs'⟩
    · have h := ih (Function.update st .main (bridgeWord xs))
        (out ++ carry.toList.map Sum.inl) (some b) (Function.update_self _ _ _)
      simp only [Function.update_idem, Option.toList_some, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append] at h
      simpa only [List.map_cons, List.append_assoc] using h

/-- **Proof sketch.** The proved partial-recursive compiler gives a terminating stack-machine execution with the specified result. Load the sentinel-coded input, simulate that finite execution, then emit its result with the sentinel removed. The resulting halted native configuration has exactly the requested output. -/
private lemma bridge_compiles (c : ToPartrec.Code) (f : List Bool → List Bool)
    (hc : ∀ x, c.eval [bridgeNumber x] = Part.some [bridgeNumber (f x)]) (x : List Bool) :
    ∃ t, (bridgeTM c).ComputesInTime (x.map Sum.inl) ((f x).map Sum.inl) t := by
  classical
  have he := PartrecToTM2.tr_eval c [bridgeNumber x]
  rw [hc x] at he
  have hm : PartrecToTM2.halt [bridgeNumber (f x)] ∈
      Turing.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init c [bridgeNumber x]) := by
    rw [he]
    simp
  have hr := (Turing.mem_eval.mp hm).1
  have ha : (PartrecToTM2.init c [bridgeNumber x]).l ∈
      Finset.insertNone (PartrecToTM2.codeSupp c .halt) := by
    apply Finset.some_mem_insertNone.mpr
    exact PartrecToTM2.codeSupp_self _ _ (PartrecToTM2.trStmts₁_self _)
  have hs := (bridge_simulate c (x := x.map Sum.inl) 0 [] _ _ hr ha).2
  simp only [PartrecToTM2.init, PartrecToTM2.halt, Option.map_some, Option.map_none,
    bridgeWord_number, bridgeExec_mem c none none (bridge_none c)] at hs
  have hstart := bridge_start c x
  have hem : bridgeReach (bridgeTM c).tm
      (bridgeCfg c (some (.exec ⟨none, bridge_none c⟩ none)) (x := x.map Sum.inl) 0
        (bridgeStore (bridgeWord (f x))) [])
      (bridgeCfg c (some (.emit none)) 0 (bridgeStore (bridgeWord (f x))) []) := by
    refine ⟨1, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, bridge_step]
    exact bridgeCfg_idle c _ _ _ _ _
  have hf := bridge_emit c (x := x.map Sum.inl) 0 (f x)
    (bridgeStore (bridgeWord (f x))) [] none rfl
  have hall := bridgeReach_trans _ hstart (bridgeReach_trans _ hs (bridgeReach_trans _ hem hf))
  obtain ⟨t, ht⟩ := hall
  refine ⟨t, (FinTM.computesInTime_iff _ _ _ _).mpr ?_⟩
  change ((bridgeTM c).tm.runFrom ((bridgeTM c).tm.initCfg _) t).state = none ∧ _
  rw [ht]
  exact ⟨rfl, rfl⟩

private lemma bridge_binary (c : ToPartrec.Code) (f : List Bool → List Bool)
    (hc : ∀ x, c.eval [bridgeNumber x] = Part.some [bridgeNumber (f x)]) :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ), M.ComputesFunInTime f T := by
  classical
  choose t ht using bridge_compiles c f hc
  let T : ℕ → ℕ := fun n =>
    (Finset.univ : Finset (List.Vector Bool n)).sup fun x => t x.val
  have hT : (bridgeTM c).ComputesFunInTimeVia ⟨Sum.inl, Sum.inl_injective⟩ f T := by
    intro x
    exact (ht x).mono (Finset.le_sup (f := fun y : List.Vector Bool x.length => t y.val)
      (Finset.mem_univ (α := List.Vector Bool x.length) ⟨x, rfl⟩))
  obtain ⟨a, M, _, hM⟩ := FinTM.alphabet_reduction ⟨Sum.inl, Sum.inl_injective⟩ (bridgeTM c) f T hT
  exact ⟨M, _, hM⟩


private lemma bridgeNumber_bits (xs : List Bool) : (bridgeNumber xs).bits = xs ++ [true] := by
  induction xs with
  | nil => exact Nat.one_bits
  | cons b xs ih =>
    change (Nat.bit b (bridgeNumber xs)).bits = (b :: xs) ++ [true]
    rw [Nat.bits_append_bit _ _ (fun h => (Nat.ne_of_gt (bridgeNumber_pos xs) h).elim), ih]
    rfl

private def bridgeUnnumber (n : ℕ) : List Bool := n.bits.reverse.tail.reverse

private lemma bridgeUnnumber_number (xs : List Bool) : bridgeUnnumber (bridgeNumber xs) = xs := by
  simp [bridgeUnnumber, bridgeNumber_bits]

private lemma bridgePrimNumber : Primrec bridgeNumber :=
  Primrec.list_foldr Primrec.id (Primrec.const 1)
    (codePrimBit.comp₂ (Primrec.fst.comp₂ Primrec₂.right) (Primrec.snd.comp₂ Primrec₂.right))

private lemma bridgePrimUnnumber : Primrec bridgeUnnumber :=
  Primrec.list_reverse.comp (Primrec.list_tail.comp (Primrec.list_reverse.comp codePrimBits))

/-- Every primitive recursive string function `f : List Bool → List Bool` is computed by
some finite binary machine: there are `M : FinTM Bool` and a time bound `T : ℕ → ℕ` with
`M.ComputesFunInTime f T`. No bound on `T` is claimed (this is the arbitrary-time
compiler route, cf. [AB09, §1.4]).

**Proof sketch.** Number strings by the sentinel code `bridgeNumber` (which preserves
trailing `false` bits and the empty word), so that `f` becomes a primitive recursive
`ℕ → ℕ` map; Mathlib compiles it to a `ToPartrec.Code`, and `bridge_binary` turns that
code into a binary machine computing `f` on the un-numbered strings. -/
lemma codePrim_machine (f : List Bool → List Bool) (hf : Primrec f) :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ), M.ComputesFunInTime f T := by
  have hn := bridgePrimNumber.comp (hf.comp (bridgePrimUnnumber.comp
    (Primrec.vector_head (n := 0))))
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.of_prim hn)
  apply bridge_binary c f
  intro x
  have hx := hc (List.Vector.ofFn (fun _ : Fin 1 => bridgeNumber x))
  simpa [List.Vector.ofFn, bridgeUnnumber_number] using hx

/-- The verified suffix scanner computes exactly the fixed serialization of decode. -/
private lemma codeCanonical_machine :
    ∃ (M : FinTM Bool) (T : ℕ → ℕ),
      M.ComputesFunInTime (fun xs => (codeDecode xs).serialize) T := by
  have he : codeCanonical = fun xs => (codeDecode xs).serialize := funext codeCanonical_eq
  rw [← he]
  exact codePrim_machine codeCanonical codePrimCanonical

/-- A concrete effective representation scheme exists.

**Proof sketch.** Take `encode := CodeTM.serialize` — which records the state count,
the initial state, and the table (finding 5) — and let `decode` run the aligned-pair
parser of `pairEncode_injective` on the doubled-bit region to recover `numStates`,
then parse the unary initial state and the `9 · (numStates + 1)` fixed-format records;
any malformation (including trailing non-`true` junk) yields a canonical trivial
machine, making `decode` total. The parser **short-circuits on the first incomplete
record** (equivalently, rejects up front any state count whose minimum table length
exceeds the remaining input), so a short malformed string declaring a huge binary
state count is rejected in time polynomial in the string, not by enumerating its
missing records (round-2 audit, finding 8). A complete serialization determines its own length,
and the parser ignores a trailing all-`true` suffix, giving `decode_encode_pad`.
**[Original, superseded proposed sketch for the canonizer — the delivered proof
takes a different route; see the implementation note below (epoch-3 audit,
finding 1).]** The `canonizer` is a machine implementing exactly this parse
followed by re-serialization (on valid codes, the identity up to padding removal;
on invalid ones, the trivial machine's serialization), with a polynomial
`canonizerTime`; its construction uses the composition combinators of
`TCSlib.Complexity.TuringMachine.Composition`. **[End of superseded paragraph:
no polynomial `canonizerTime` is proved, and no combinator construction was
built.]**

**Epoch 3 implementation note.** The parser and erased suffix scanner implement
the grammar above, including the up-front minimum-length guard. For the canonizer,
this implementation takes the brief's arbitrary-time route: it proves the scanner
and prefix operation primitive recursive, uses Mathlib's proved partial-recursive
to stack-machine compiler, and supplies a private simulation by an actual finite
four-work-tape machine. A sentinel number encoding preserves empty strings and
trailing false bits. The proved alphabet-reduction theorem then gives a binary
machine. A finite maximum of the individual halting times at each input length
supplies the bound; no polynomial claim is made for this implementation. This
replaces the suggested composition-based implementation, not the fixed
serialization or its effectivity contract. No universal-machine admission is used. -/
theorem exists_effectiveMachineCode : Nonempty EffectiveMachineCode := by
  obtain ⟨M, T, h⟩ := codeCanonical_machine
  exact ⟨{
    encode := CodeTM.serialize
    decode := codeDecode
    decode_encode_pad := codeDecode_serialize_pad
    canonizer := M
    canonizerTime := T
    canonizer_computes := h }⟩

end Turing
```


## ===== TCSlib/Complexity/TuringMachine/CodeParser.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-code parser

The parser/decoder layer for the fixed serialization of coded machines
(`Turing.CodeTM.serialize`): field readers for the exact serialization grammar of
the phase-3 re-audit (Argument A), the total decoder `Turing.codeDecode` with its
padded round-trip law, parser soundness, and the erased suffix scanner
`Turing.codeScan` behind the canonizer target `Turing.codeCanonical`. This module
was split out mechanically from `TCSlib.Complexity.TuringMachine.Encoding` at the
epoch-3→4 merge; its content is the epoch-3 fill, batch A.

## Main definitions

* `Turing.codeDecode` — total decoding: every malformed string denotes the fixed
  fallback machine.
* `Turing.codeScan` / `Turing.codeCanonical` — the erased suffix scanner and the
  canonical-serialization function it induces.

## Main results

* `Turing.codeDecode_serialize_pad` — the decoder recovers a serialized machine
  under arbitrary `true`-padding.
* `Turing.codeCanonical_eq` — the scanner-based canonizer computes exactly
  `fun xs => (codeDecode xs).serialize`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, pp. 19-20.)
-/

namespace Turing

/-- Read a unary natural, stopping at its first false bit. -/
def codeReadUnary : List Bool → Option (ℕ × List Bool)
  | false :: xs => some (0, xs)
  | true :: xs => (codeReadUnary xs).map fun p => (p.1 + 1, p.2)
  | [] => none

/-- The unary reader leaves an arbitrary suffix untouched. -/
private lemma codeReadUnary_append (n : ℕ) (xs : List Bool) :
    codeReadUnary (List.replicate n true ++ false :: xs) = some (n, xs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa [List.replicate_succ, codeReadUnary] using
      congrArg (Option.map fun p : ℕ × List Bool => (p.1 + 1, p.2)) ih

/-- A unary index is accepted only when it belongs to the declared state space. -/
private def codeReadFin (n : ℕ) (xs : List Bool) : Option (Fin n × List Bool) := do
  let (i, rest) ← codeReadUnary xs
  if h : i < n then some (⟨i, h⟩, rest) else none

/-- Decode the fixed dictionary for a head movement. -/
private def codeReadSign : List Bool → Option (SignType × List Bool)
  | true :: true :: xs => some (.neg, xs)
  | false :: false :: xs => some (.zero, xs)
  | true :: false :: xs => some (.pos, xs)
  | _ => none

/-- Decode the fixed dictionary for an optional output bit. -/
private def codeReadOutput : List Bool → Option (Option Bool × List Bool)
  | false :: false :: xs => some (none, xs)
  | true :: false :: xs => some (some false, xs)
  | true :: true :: xs => some (some true, xs)
  | _ => none

/-- Decode the fixed dictionary for an optional work-tape write. -/
private def codeReadWrite : List Bool → Option (Option (Option Bool) × List Bool)
  | false :: false :: xs => some (none, xs)
  | false :: true :: xs => some (some none, xs)
  | true :: false :: xs => some (some (some false), xs)
  | true :: true :: xs => some (some (some true), xs)
  | _ => none

/-- Read the halt tag or a range-checked live successor state. -/
private def codeReadState (n : ℕ) : List Bool → Option (Option (Fin n) × List Bool)
  | false :: xs => some (none, xs)
  | true :: xs => (codeReadFin n xs).map fun p => (some p.1, p.2)
  | [] => none

/-- Read the five fields of a transition, failing as soon as any field fails. -/
private def codeReadAction (n : ℕ) (xs : List Bool) :
    Option (Action 1 Bool (Fin (n + 1)) × List Bool) := do
  let (im, xs) ← codeReadSign xs
  let (wr, xs) ← codeReadWrite xs
  let (wm, xs) ← codeReadSign xs
  let (out, xs) ← codeReadOutput xs
  let (q, xs) ← codeReadState (n + 1) xs
  pure (⟨im, fun _ => (wr, wm), out, q⟩, xs)

/-- Read one entry for each tape symbol, in blank/false/true order. -/
private def codeReadSymbols {A : Type} (read : List Bool → Option (A × List Bool))
    (xs : List Bool) : Option ((Option Bool → A) × List Bool) := do
  let (a, xs) ← read xs
  let (b, xs) ← read xs
  let (c, xs) ← read xs
  pure ((fun s => match s with | none => a | some false => b | some true => c), xs)

/-- Read a fixed-size vector. Its caller checks the minimum total input length
before invoking it; a malformed field also aborts immediately. -/
private def codeReadVec {A : Type} (read : List Bool → Option (A × List Bool)) :
    (n : ℕ) → List Bool → Option ((Fin n → A) × List Bool)
  | 0, xs => some (Fin.elim0, xs)
  | n + 1, xs => do
    let (a, xs) ← read xs
    let (as, xs) ← codeReadVec read n xs
    pure (Fin.cases a as, xs)

/-- Interpret a least-significant-bit-first word. Canonical syntax is checked
separately, so this function also has a value on noncanonical words. -/
def codeBitsNat (xs : List Bool) : ℕ := xs.foldr Nat.bit 0

/-- The fallback is the one-state, immediately halting, silent machine. -/
def codeFallback : CodeTM :=
  ⟨0, ⟨0, fun _ _ _ => ⟨.zero, fun _ => (none, .zero), none, none⟩⟩⟩

/-- Parse the exact serialization grammar of the phase-3 re-audit, Argument A.
The length guard precedes vector recursion: every state requires nine records,
each containing at least nine bits. The suffix must consist entirely of true bits. -/
private def codeParse (xs : List Bool) : Option CodeTM := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 81 * (n + 1) > rest.length then none else do
      let (q, rest) ← codeReadFin (n + 1) rest
      let (table, rest) ← codeReadVec
        (codeReadSymbols (codeReadSymbols (codeReadAction n))) (n + 1) rest
      if rest.all id then
        pure ⟨n, ⟨q, fun s inp w => table s inp (w 0)⟩⟩
      else none

/-- Total decoding: every malformed string denotes the fixed fallback. -/
def codeDecode (xs : List Bool) : CodeTM := (codeParse xs).getD codeFallback

/-- Reading an encoded bounded index is an exact prefix inverse. -/
private lemma codeReadFin_append {n : ℕ} (i : Fin n) (xs : List Bool) :
    codeReadFin n (unaryFin i ++ xs) = some (i, xs) := by
  simp [codeReadFin, unaryFin, List.append_assoc, codeReadUnary_append, i.isLt]

/-- Reading an encoded head movement is an exact prefix inverse. -/
private lemma codeReadSign_append (s : SignType) (xs : List Bool) :
    codeReadSign (signBits s ++ xs) = some (s, xs) := by
  cases s <;> rfl

/-- Reading an encoded optional output is an exact prefix inverse. -/
private lemma codeReadOutput_append (b : Option Bool) (xs : List Bool) :
    codeReadOutput (optBoolBits b ++ xs) = some (b, xs) := by
  rcases b with _ | b
  · rfl
  · cases b <;> rfl

/-- Reading an encoded optional write is an exact prefix inverse. -/
private lemma codeReadWrite_append (b : Option (Option Bool)) (xs : List Bool) :
    codeReadWrite (optOptBoolBits b ++ xs) = some (b, xs) := by
  rcases b with _ | (_ | b)
  · rfl
  · rfl
  · cases b <;> rfl

/-- Reading an encoded successor is an exact prefix inverse. -/
private lemma codeReadState_append {n : ℕ} (s : Option (Fin n)) (xs : List Bool) :
    codeReadState n (optStateBits s ++ xs) = some (s, xs) := by
  cases s with
  | none => rfl
  | some s => simp [optStateBits, codeReadState, codeReadFin_append]

/-- All five fields round-trip, including the unique work-tape coordinate. -/
private lemma codeReadAction_append {n : ℕ} (a : Action 1 Bool (Fin (n + 1)))
    (xs : List Bool) : codeReadAction n (actionBits a ++ xs) = some (a, xs) := by
  simp only [actionBits, List.append_assoc, codeReadAction, codeReadSign_append,
    codeReadWrite_append, codeReadOutput_append, codeReadState_append,
    bind, Option.bind, pure]
  congr 2
  cases a
  congr
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

/-- Three prefix inverses assemble in the required blank/false/true order. -/
private lemma codeReadSymbols_append {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (h : ∀ a xs, read (write a ++ xs) = some (a, xs))
    (f : Option Bool → A) (xs : List Bool) :
    codeReadSymbols read
      (([none, some false, some true] : List (Option Bool)).flatMap
        (fun s => write (f s)) ++ xs) = some (f, xs) := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc, codeReadSymbols, h, bind, Option.bind, pure]
  congr 2
  funext s
  rcases s with _ | b
  · rfl
  · cases b <;> rfl

/-- Fixed-size vector parsing is a prefix inverse of enumeration-order writing.
**Proof sketch.** Induct on the vector length. Read its first entry using the
supplied inverse, then its tail by induction. Finite-function extensionality
identifies the reconstructed head/tail function with the original vector.

**Proof sketch.** Induct on the vector length. The first field reader recovers the head and leaves the concatenated tail; the induction hypothesis recovers the remaining vector. Extensionality identifies the reconstructed function on bounded indices. -/
private lemma codeReadVec_append {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (h : ∀ a xs, read (write a ++ xs) = some (a, xs)) :
    ∀ n (f : Fin n → A) xs,
      codeReadVec read n ((List.finRange n).flatMap (fun i => write (f i)) ++ xs) =
        some (f, xs) := by
  intro n
  induction n with
  | zero =>
    intro f xs
    simp only [List.finRange_zero, List.flatMap_nil, List.nil_append, codeReadVec]
    congr 2
    funext i
    exact i.elim0
  | succ n ih =>
    intro f xs
    simp only [List.finRange_succ, List.flatMap_cons, List.flatMap_map,
      List.append_assoc, codeReadVec, h, bind, Option.bind, ih, pure]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Binary reconstruction inverts the canonical little-endian representation,
including the empty representation of zero. -/
private lemma codeBitsNat_bits (n : ℕ) : codeBitsNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [codeBitsNat]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    simpa only [codeBitsNat, List.foldr_cons] using congrArg (Nat.bit b) ih

/-- Every record has eight fixed bits and a nonempty successor field. -/
private lemma codeAction_length {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    9 ≤ (actionBits a).length := by
  have hs (s : SignType) : (signBits s).length = 2 := by cases s <;> rfl
  have ho (b : Option Bool) : (optBoolBits b).length = 2 := by
    rcases b with _ | b
    · rfl
    · cases b <;> rfl
  have hw (b : Option (Option Bool)) : (optOptBoolBits b).length = 2 := by
    rcases b with _ | (_ | b)
    · rfl
    · rfl
    · cases b <;> rfl
  have hq : 1 ≤ (optStateBits a.state).length := by
    cases a.state <;> simp [optStateBits, unaryFin]
  simp only [actionBits, List.length_append, hs, ho, hw]
  omega

/-- Concatenating words with a common length lower bound preserves that bound. -/
private lemma codeFlatMap_length {A : Type} (xs : List A) (f : A → List Bool)
    (c : ℕ) (h : ∀ a ∈ xs, c ≤ (f a).length) :
    c * xs.length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add,
      Nat.mul_one]
    omega

/-- The complete table contains at least 81 bits per live state.

**Proof sketch.** Every action contains eight fixed field bits and at least one successor bit. Summing this lower bound over the three work symbols, three input symbols, and all states gives at least 81 bits per state. -/
private lemma codeTable_length (M : CodeTM) :
    81 * (M.numStates + 1) ≤
      ((List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w)).length := by
  have h := codeFlatMap_length (List.finRange (M.numStates + 1))
    (fun q => ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
      ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
        actionBits (M.tm.tr q inp fun _ => w)) 81 (by
      intro q _
      have h := codeFlatMap_length ([none, some false, some true] : List (Option Bool))
        (fun inp => ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
          actionBits (M.tm.tr q inp fun _ => w)) 27 (by
            intro inp _
            simpa using codeFlatMap_length
              ([none, some false, some true] : List (Option Bool))
              (fun w => actionBits (M.tm.tr q inp fun _ => w)) 9
              (fun _ _ => codeAction_length _))
      simpa using h)
  simpa using h

/-- The table reader recovers every transition. Blank/false/true exhaust each
read alphabet; a one-work-tape read vector is determined by its zero coordinate. -/
private lemma codeReadTable_append (M : CodeTM) (xs : List Bool) :
    codeReadVec (codeReadSymbols (codeReadSymbols (codeReadAction M.numStates)))
      (M.numStates + 1)
      (((List.finRange (M.numStates + 1)).flatMap fun q =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
          ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
            actionBits (M.tm.tr q inp fun _ => w)) ++ xs) =
      some ((fun q inp w => M.tm.tr q inp (fun _ => w)), xs) :=
  codeReadVec_append _ _
    (fun _ _ => codeReadSymbols_append _ _
      (fun _ _ => codeReadSymbols_append _ _ codeReadAction_append _ _) _ _) _ _ _

/-- The complete parser recovers a serialized machine under arbitrary true padding.
**Proof sketch.** The doubled header recovers the canonical binary count. The
minimum table-length lemma discharges the short-circuit guard. The unary initial
state and enumerated records then round-trip with the padding left untouched.
All remaining bits are true, and extensionality recovers the transition function.

**Proof sketch.** The doubled-bit parser first recovers the canonical state-count bits. The table length bound discharges the early guard; the field and vector inverse laws then recover the initial state and every transition. The remaining replicated true bits pass the suffix test. -/
private lemma codeParse_serialize_pad (M : CodeTM) (m : ℕ) :
    codeParse (M.serialize ++ List.replicate m true) = some M := by
  have hp (a b c : List Bool) : pairEncode a b ++ c = pairEncode a (b ++ c) := by
    simp [pairEncode, List.append_assoc]
  unfold CodeTM.serialize
  rw [hp]
  unfold codeParse
  rw [pairDecode_pairEncode]
  dsimp only [bind, Option.bind]
  rw [codeBitsNat_bits]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  have hlen := codeTable_length M
  simp only [List.length_append, List.length_replicate] at *
  rw [if_neg (by omega)]
  simp only [codeBitsNat_bits, List.append_assoc, codeReadFin_append, bind, Option.bind,
    codeReadTable_append, List.all_replicate, id_eq, Bool.true_eq, or_true,
    ite_self, ↓reduceIte, pure]
  congr 1
  cases M with
  | mk n tm =>
    congr 1
    cases tm with
    | mk q tr =>
      congr 1
      funext s inp w
      apply congrArg (tr s inp)
      funext i
      exact congrArg w (Subsingleton.elim _ _)

/-- The total decoder satisfies the required exact padded round-trip law. -/
lemma codeDecode_serialize_pad (M : CodeTM) (m : ℕ) :
    codeDecode (M.serialize ++ List.replicate m true) = M := by
  simp only [codeDecode, codeParse_serialize_pad, Option.getD_some]

/-- Successful unary parsing characterizes the exact consumed prefix.

**Proof sketch.** Induct on the input. A false bit terminates the number immediately; a true bit increments the recursively recovered number. Empty input cannot succeed. -/
private lemma codeReadUnary_sound (xs : List Bool) (n : ℕ) (rest : List Bool)
    (h : codeReadUnary xs = some (n, rest)) :
    xs = List.replicate n true ++ false :: rest := by
  induction xs generalizing n with
  | nil => simp [codeReadUnary] at h
  | cons b xs ih =>
    cases b with
    | false =>
      simp only [codeReadUnary, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | true =>
      cases hr : codeReadUnary xs with
      | none => simp [codeReadUnary, hr] at h
      | some p =>
        rcases p with ⟨k, tail⟩
        simp only [codeReadUnary, hr, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp [List.replicate_succ, ih k hr]

/-- Successful bounded-index parsing determines its complete unary prefix. -/
private lemma codeReadFin_sound {n : ℕ} (xs : List Bool) (i : Fin n) (rest : List Bool)
    (h : codeReadFin n xs = some (i, rest)) : xs = unaryFin i ++ rest := by
  obtain ⟨⟨j, tail⟩, hj, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simpa [unaryFin, List.append_assoc] using codeReadUnary_sound xs j tail hj
  · contradiction

/-- A successful doubled header has exactly the paired form, including empty data.

**Proof sketch.** Induct by the same two-bit steps as the aligned parser. Equal bits extend the doubled prefix, the false/true separator ends it, and all incomplete or forbidden pairs are rejected. -/
private lemma codePairDecode_sound (xs a rest : List Bool)
    (h : pairDecode xs = some (a, rest)) : xs = pairEncode a rest := by
  induction xs using pairDecode.induct generalizing a with
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
  | case4 xs h₁ h₂ h₃ => simp [pairDecode, h₁, h₂, h₃] at h

/-- A successful movement read consumes precisely its two-bit dictionary entry. -/
private lemma codeReadSign_sound (xs : List Bool) (s : SignType) (rest : List Bool)
    (h : codeReadSign xs = some (s, rest)) : xs = signBits s ++ rest := by
  rcases xs with _ | ⟨b, _ | ⟨c, tail⟩⟩
  · simp [codeReadSign] at h
  · cases b <;> simp [codeReadSign] at h
  · cases b <;> cases c <;>
      simp only [codeReadSign, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals first | contradiction | (rcases h with ⟨rfl, rfl⟩; rfl)

/-- A successful output read consumes precisely its two-bit dictionary entry. -/
private lemma codeReadOutput_sound (xs : List Bool) (b : Option Bool) (rest : List Bool)
    (h : codeReadOutput xs = some (b, rest)) : xs = optBoolBits b ++ rest := by
  rcases xs with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · simp [codeReadOutput] at h
  · cases a <;> simp [codeReadOutput] at h
  · cases a <;> cases c <;>
      simp only [codeReadOutput, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals first | contradiction | (rcases h with ⟨rfl, rfl⟩; rfl)

/-- A successful write read consumes precisely its two-bit dictionary entry. -/
private lemma codeReadWrite_sound (xs : List Bool) (b : Option (Option Bool)) (rest : List Bool)
    (h : codeReadWrite xs = some (b, rest)) : xs = optOptBoolBits b ++ rest := by
  rcases xs with _ | ⟨a, _ | ⟨c, tail⟩⟩
  · simp [codeReadWrite] at h
  · cases a <;> simp [codeReadWrite] at h
  · cases a <;> cases c <;>
      simp only [codeReadWrite, Option.some.injEq, Prod.mk.injEq] at h
    all_goals rcases h with ⟨rfl, rfl⟩; rfl

/-- A successful successor read consumes exactly its halt/live unary field.

**Proof sketch.** Split the leading tag. A false tag is exactly the halted state encoding; a true tag delegates to the soundness of the bounded unary reader. Empty input is rejected. -/
private lemma codeReadState_sound {n : ℕ} (xs : List Bool) (s : Option (Fin n))
    (rest : List Bool) (h : codeReadState n xs = some (s, rest)) :
    xs = optStateBits s ++ rest := by
  rcases xs with _ | ⟨b, tail⟩
  · simp [codeReadState] at h
  · cases b with
    | false =>
      simp only [codeReadState, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | true =>
      cases hr : codeReadFin n tail with
      | none => simp [codeReadState, hr] at h
      | some p =>
        rcases p with ⟨i, suffix⟩
        simp only [codeReadState, hr, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [optStateBits, List.cons_append]
        exact congrArg (List.cons true) (codeReadFin_sound tail i suffix hr)

/-- Successful record parsing characterizes its complete serialized prefix.
**Proof sketch.** Decompose the five successful reads, apply the dictionary
inverse to each, and concatenate their consumed prefixes in order. -/
private lemma codeReadAction_sound {n : ℕ} (xs : List Bool)
    (a : Action 1 Bool (Fin (n + 1))) (rest : List Bool)
    (h : codeReadAction n xs = some (a, rest)) : xs = actionBits a ++ rest := by
  simp only [codeReadAction, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨im, r₁⟩, h₁, ⟨⟨wr, r₂⟩, h₂, ⟨⟨wm, r₃⟩, h₃,
    ⟨⟨out, r₄⟩, h₄, ⟨⟨q, r₅⟩, h₅, h⟩⟩⟩⟩⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rw [codeReadSign_sound xs im r₁ h₁, codeReadWrite_sound r₁ wr r₂ h₂,
    codeReadSign_sound r₂ wm r₃ h₃, codeReadOutput_sound r₃ out r₄ h₄,
    codeReadState_sound r₄ q r₅ h₅]
  simp [actionBits, List.append_assoc]

/-- Three sound prefix readers reconstruct the symbol-indexed row they consumed. -/
private lemma codeReadSymbols_sound {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (sound : ∀ xs a rest, read xs = some (a, rest) → xs = write a ++ rest)
    (xs : List Bool) (f : Option Bool → A) (rest : List Bool)
    (h : codeReadSymbols read xs = some (f, rest)) :
    xs = ([none, some false, some true] : List (Option Bool)).flatMap
      (fun s => write (f s)) ++ rest := by
  simp only [codeReadSymbols, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨a, r₁⟩, h₁, ⟨⟨b, r₂⟩, h₂, ⟨⟨c, r₃⟩, h₃, h⟩⟩⟩ := h
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  rw [sound xs a r₁ h₁, sound r₁ b r₂ h₂, sound r₂ c r₃ h₃]
  simp [List.append_assoc]

/-- Sound vector parsing reconstructs the entire consumed enumeration.
**Proof sketch.** Induct on the requested vector length. The first successful
entry determines a prefix and the induction hypothesis determines the tail;
the finite-vector constructor enumerates them in exactly that order.

**Proof sketch.** Induct on the number of entries. Successful parsing splits into a successful head parse and a successful tail parse. Their soundness equations concatenate in the same order as the bounded-state enumeration. -/
private lemma codeReadVec_sound {A : Type}
    (read : List Bool → Option (A × List Bool)) (write : A → List Bool)
    (sound : ∀ xs a rest, read xs = some (a, rest) → xs = write a ++ rest) :
    ∀ n xs (f : Fin n → A) rest, codeReadVec read n xs = some (f, rest) →
      xs = (List.finRange n).flatMap (fun i => write (f i)) ++ rest := by
  intro n
  induction n with
  | zero =>
    intro xs f rest h
    simpa only [codeReadVec, Option.some.injEq, Prod.mk.injEq,
      List.finRange_zero, List.flatMap_nil, List.nil_append] using
      (show xs = rest from congrArg Prod.snd (Option.some.inj h))
  | succ n ih =>
    intro xs f rest h
    simp only [codeReadVec, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a, r₁⟩, h₁, ⟨⟨as, r₂⟩, h₂, h⟩⟩ := h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rw [sound xs a r₁ h₁, ih r₁ as r₂ h₂]
    simp [List.finRange_succ, List.flatMap_map, List.append_assoc]

/-- An all-true suffix is exactly true padding of its own length. -/
private lemma codeAllTrue_eq (xs : List Bool) (h : xs.all id = true) :
    xs = List.replicate xs.length true := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false => simp at h
    | true =>
      simp only [List.all_cons, id_eq, Bool.true_and] at h
      simp only [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons true) (ih h)

/-- Acceptance characterizes a canonical serialization followed by true padding.
**Proof sketch.** Successful parsing fixes the count's canonical binary syntax,
the initial state, and every table record. Apply the soundness lemma for each
reader to reconstruct the consumed prefix; the final all-true test reconstructs
the padding. The one-work-tape read function is constant at its zero coordinate.

**Proof sketch.** Decompose a successful parse into its count, initial state, and table. Field soundness reconstructs each consumed prefix. The canonical-bits check fixes the count representation, and the final all-true check identifies the remainder as true padding. -/
private lemma codeParse_sound (xs : List Bool) (M : CodeTM)
    (h : codeParse xs = some M) :
    ∃ m, xs = M.serialize ++ List.replicate m true := by
  unfold codeParse at h
  obtain ⟨⟨bits, rest⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · contradiction
  next hb =>
    have hb : bits = (codeBitsNat bits).bits := not_not.mp hb
    split at h
    · contradiction
    next _ =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨q, r₁⟩, hq, ⟨⟨table, r₂⟩, ht, h⟩⟩ := h
      split at h
      next hpad =>
        simp only [pure, Option.some.injEq] at h
        subst M
        refine ⟨r₂.length, ?_⟩
        have htable := codeReadVec_sound _ _
          (fun _ _ _ => codeReadSymbols_sound _ _
            (fun _ _ _ => codeReadSymbols_sound _ _ codeReadAction_sound _ _ _) _ _ _)
          _ _ _ _ ht
        dsimp only at htable hpad
        rw [codePairDecode_sound xs bits rest hp, codeReadFin_sound rest q r₁ hq,
          htable, codeAllTrue_eq r₂ hpad]
        simp only [CodeTM.serialize, pairEncode, List.append_assoc]
        simp only [List.length_replicate]
        congr 1
        exact congrArg (List.flatMap fun b : Bool => [b, b]) hb
      · contradiction

/-- Erased readers keep only the unconsumed suffix. -/
def codeSkipPair (valid : Bool → Bool → Bool) (xs : List Bool) : Option (List Bool) :=
  xs.casesOn none fun a ys => ys.casesOn none fun b zs => if valid a b then some zs else none

/-- Skip a range-checked unary index, keeping only the unconsumed suffix. -/
def codeSkipFin (n : ℕ) (xs : List Bool) : Option (List Bool) :=
  (codeReadUnary xs).bind fun p => if p.1 < n then some p.2 else none

/-- Skip a halt tag or live successor field, keeping only the unconsumed suffix. -/
def codeSkipState (n : ℕ) (xs : List Bool) : Option (List Bool) :=
  xs.casesOn none fun b ys => if b then codeSkipFin n ys else some ys

/-- Skip one five-field transition record, keeping only the unconsumed suffix. -/
def codeSkipAction (n : ℕ) (xs : List Bool) : Option (List Bool) := do
  let xs ← codeSkipPair (fun a b => a || !b) xs
  let xs ← codeSkipPair (fun _ _ => true) xs
  let xs ← codeSkipPair (fun a b => a || !b) xs
  let xs ← codeSkipPair (fun a b => a || !b) xs
  codeSkipState (n + 1) xs

/-- Iterate a skipping reader a fixed number of times, keeping only the final suffix. -/
def codeSkipRepeat (r : List Bool → Option (List Bool)) : ℕ → List Bool → Option (List Bool)
  | 0, xs => some xs
  | n + 1, xs => (r xs).bind (codeSkipRepeat r n)

private lemma codeEraseFin (n : ℕ) (xs : List Bool) :
    (codeReadFin n xs).map Prod.snd = codeSkipFin n xs := by
  simp only [codeReadFin, codeSkipFin, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  split <;> rfl

private lemma codeEraseSign (xs : List Bool) :
    (codeReadSign xs).map Prod.snd = codeSkipPair (fun a b => a || !b) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

private lemma codeEraseOutput (xs : List Bool) :
    (codeReadOutput xs).map Prod.snd = codeSkipPair (fun a b => a || !b) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

private lemma codeEraseWrite (xs : List Bool) :
    (codeReadWrite xs).map Prod.snd = codeSkipPair (fun _ _ => true) xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> rfl
    | cons b xs => cases a <;> cases b <;> rfl

private lemma codeEraseState (n : ℕ) (xs : List Bool) :
    (codeReadState n xs).map Prod.snd = codeSkipState n xs := by
  cases xs with
  | nil => rfl
  | cons b xs =>
    cases b
    · rfl
    · simpa only [codeReadState, codeSkipState, ↓reduceIte,
        Option.map_map, Function.comp_def] using codeEraseFin n xs

private lemma codeErase_bind {A B : Type} (r : Option (A × List Bool))
    (f : List Bool → Option B) :
    r.bind (fun p => f p.2) = (r.map Prod.snd).bind f := by
  cases r <;> rfl

private lemma codeEraseAction (n : ℕ) (xs : List Bool) :
    (codeReadAction n xs).map Prod.snd = codeSkipAction n xs := by
  simp only [codeReadAction, codeSkipAction, bind, Option.map_bind, Function.comp_def, pure, Option.map_some]
  rw [← codeEraseSign xs, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseWrite p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseSign p.2, ← codeErase_bind]
  congr 1; funext p
  rw [← codeEraseOutput p.2, ← codeErase_bind]
  congr 1; funext p
  simpa only [Option.map_eq_bind, Function.comp_def] using codeEraseState (n + 1) p.2

private lemma codeEraseSymbols {A : Type} (r : List Bool → Option (A × List Bool)) (xs : List Bool) :
    (codeReadSymbols r xs).map Prod.snd = codeSkipRepeat (fun s => (r s).map Prod.snd) 3 xs := by
  simp only [codeReadSymbols, bind, Option.map_bind, Function.comp_def, pure, Option.map_some,
    codeSkipRepeat, Option.bind_map]

private lemma codeEraseVec {A : Type} (r : List Bool → Option (A × List Bool)) (n : ℕ) :
    ∀ xs, (codeReadVec r n xs).map Prod.snd = codeSkipRepeat (fun s => (r s).map Prod.snd) n xs := by
  induction n with
  | zero => intro xs; rfl
  | succ n ih =>
    intro xs
    simp only [codeReadVec, bind, Option.map_bind, Function.comp_def, pure, Option.map_some]
    have inner (p : A × List Bool) :
        (codeReadVec r n p.2).bind (fun q => some q.2) = codeSkipRepeat (fun s => (r s).map Prod.snd) n p.2 := by
      simpa only [Option.map_eq_bind, Function.comp_def] using ih p.2
    simp only [inner, codeErase_bind, codeSkipRepeat]

private def codeParseFull (xs : List Bool) : Option (CodeTM × List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 81 * (n + 1) > rest.length then none else do
      let (q, rest) ← codeReadFin (n + 1) rest
      let (table, rest) ← codeReadVec
        (codeReadSymbols (codeReadSymbols (codeReadAction n))) (n + 1) rest
      if rest.all id then
        pure (⟨n, ⟨q, fun s inp w => table s inp (w 0)⟩⟩, rest)
      else none

/-- The erased parser: accept exactly the strings the parser accepts, returning only the unconsumed all-true suffix. -/
def codeScan (xs : List Bool) : Option (List Bool) := do
  let (bits, rest) ← pairDecode xs
  let n := codeBitsNat bits
  if bits ≠ n.bits then none else do
    if 81 * (n + 1) > rest.length then none else do
      let rest ← codeSkipFin (n + 1) rest
      let rest ← codeSkipRepeat (codeSkipRepeat (codeSkipRepeat (codeSkipAction n) 3) 3) (n + 1) rest
      if rest.all id then pure rest else none

private lemma codeParse_full (xs : List Bool) : codeParse xs = (codeParseFull xs).map Prod.fst := by
  simp only [codeParse, codeParseFull, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  dsimp only
  split <;> try simp only [Option.map_none]
  split <;> try simp only [Option.map_none, Option.map_bind, Function.comp_def]
  congr 1; funext q
  congr 1; funext t
  dsimp only
  split <;> rfl

private lemma codeScan_full (xs : List Bool) : codeScan xs = (codeParseFull xs).map Prod.snd := by
  simp only [codeScan, codeParseFull, bind, Option.map_bind, Function.comp_def]
  congr 1
  funext p
  dsimp only
  split <;> try simp only [Option.map_none]
  split <;> try simp only [Option.map_none, Option.map_bind, Function.comp_def]
  have h (q : Fin (codeBitsNat p.1 + 1) × List Bool)
      (t : (Fin (codeBitsNat p.1 + 1) → Option Bool → Option Bool → Action 1 Bool (Fin (codeBitsNat p.1 + 1))) × List Bool) :
      (if t.2.all id then some ((⟨codeBitsNat p.1, ⟨q.1, fun s inp w => t.1 s inp (w 0)⟩⟩ : CodeTM), t.2) else none).map Prod.snd =
        (if t.2.all id then some t.2 else none) := by split <;> rfl
  simp only [pure, h]
  rw [← codeEraseFin _ _, ← codeErase_bind]
  congr 1; funext q
  have ht := codeEraseVec (codeReadSymbols (codeReadSymbols (codeReadAction (codeBitsNat p.1))))
    (codeBitsNat p.1 + 1) q.2
  simp only [codeEraseSymbols, codeEraseAction] at ht
  rw [← ht, ← codeErase_bind]

/-- **Proof sketch.** Use the same decomposition as parser soundness, retaining the exact unconsumed suffix. The field soundness equations and the canonical count check reconstruct the original input as the machine serialization followed by that suffix. -/
private lemma codeParseFull_sound (xs : List Bool) (M : CodeTM) (tail : List Bool)
    (h : codeParseFull xs = some (M, tail)) : xs = M.serialize ++ tail := by
  unfold codeParseFull at h
  obtain ⟨⟨bits, rest⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · contradiction
  next hb =>
    have hb : bits = (codeBitsNat bits).bits := not_not.mp hb
    split at h
    · contradiction
    next _ =>
      simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨q, r₁⟩, hq, ⟨⟨table, r₂⟩, ht, h⟩⟩ := h
      split at h
      next hpad =>
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have htable := codeReadVec_sound _ _
          (fun _ _ _ => codeReadSymbols_sound _ _
            (fun _ _ _ => codeReadSymbols_sound _ _ codeReadAction_sound _ _ _) _ _ _)
          _ _ _ _ ht
        dsimp only at htable
        rw [codePairDecode_sound xs bits rest hp, codeReadFin_sound rest q r₁ hq, htable]
        simp only [CodeTM.serialize, pairEncode, List.append_assoc]
        congr 1
        exact congrArg (List.flatMap fun b : Bool => [b, b]) hb
      · contradiction

/-- The canonical serialization of the machine a string denotes: the consumed prefix on scanner success, the fallback machine's serialization otherwise. -/
def codeCanonical (xs : List Bool) : List Bool :=
  (codeScan xs).casesOn codeFallback.serialize fun tail => xs.take (xs.length - tail.length)

/-- The suffix scanner computes exactly the fixed serialization of the decoded machine. -/
lemma codeCanonical_eq (xs : List Bool) : codeCanonical xs = (codeDecode xs).serialize := by
  unfold codeCanonical codeDecode
  rw [codeScan_full, codeParse_full]
  cases h : codeParseFull xs with
  | none => rfl
  | some p =>
    rcases p with ⟨M, tail⟩
    simp only [Option.map_some, Option.getD_some]
    rw [codeParseFull_sound xs M tail h]
    simp

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


## ===== TCSlib/Complexity/TimeHierarchy/Separation.lean =====

```
/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.TimeHierarchy.Diagonal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# P ⊊ EXP

[AB09, §3.1, after Theorem 3.1]: the time hierarchy theorem separates polynomial from
exponential time. We instantiate `Complexity.time_hierarchy` (more precisely, its two
halves `diagLang_mem_DTIME` and `diagLang_not_mem_DTIME`) with the budget `g(n) = 2ⁿ`:
the single diagonal language `diagLang (2^·)` lies in `DTIME(2ⁿ + 1) ⊆ EXP` and in no
`DTIME(nᵏ + 1)`, hence not in `P`.

## Main results

* `Complexity.timeConstructible_two_pow` — `n ↦ 2ⁿ` is time constructible
  [AB09, §1.3, example `2ⁿ`].
* `Complexity.eventually_poly_le_two_pow` — polynomials are eventually dominated by
  `2ⁿ`, with an arbitrary constant factor.
* `Complexity.dtime_poly_ssubset_dtime_two_pow` — `DTIME(nᵏ + 1) ⊊ DTIME(2ⁿ)` for
  every `k` (the hierarchy theorem at the polynomial/exponential gap).
* `Complexity.P_ssubset_EXP` — `P ⊊ EXP` [AB09, §3.1; cf. Claim 2.4 for `P ⊆ EXP`].
* `Complexity.P_ne_EXP` — `P ≠ EXP`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.3; §2.6, Claim 2.4; §3.1, Theorem 3.1.)
-/

namespace Complexity

open Turing Turing.FinTM TimeHierarchy

/-- The machine `x ↦ 0^|x| 1`, the binary representation of `2^|x|` (low bit first):
emit `false` for every input symbol, then `true`, and halt. -/
private def twoPowTM : FinTM Bool where
  k := 0
  State := Unit
  tm :=
    { q₀ := ()
      tr := fun _ inp _ =>
        match inp with
        | some _ => ⟨.pos, fun _ => (none, 0), some false, some ()⟩
        | none => ⟨0, fun _ => (none, 0), some true, none⟩ }

/-- The run invariant of `twoPowTM`: after `i ≤ |x|` steps it is live at input
position `i + 1` with `0^i` emitted. -/
private lemma twoPowTM_run (x : List Bool) : ∀ i, i ≤ x.length →
    (twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i).state = some () ∧
    ((twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i).inputPos : ℕ) = i + 1 ∧
    (twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i).output = List.replicate i false := by
  intro i
  induction i with
  | zero => intro _; exact ⟨rfl, rfl, rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨hs, hp, ho⟩ := ih (by omega)
    rw [MultiTapeTM.runFrom_succ_eq_step']
    generalize twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) i = c at hs hp ho
    have hin : c.inputSymbol = some (x[i]'(by omega)) := inputSymbolInner i (by omega) (by omega)
    unfold MultiTapeTM.step
    rw [hs]
    simp only [twoPowTM, hin, Action.apply]
    refine ⟨trivial, ?_, ?_⟩
    · rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    · simp [ho, List.replicate_succ']

/-- The binary representation of `2ⁿ`, low bit first. -/
private lemma bits_two_pow (n : ℕ) : (2 ^ n).bits = List.replicate n false ++ [true] := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 ^ (n + 1) = Nat.bit false (2 ^ n) := by
      simp [Nat.bit_val, Nat.pow_succ]; ring
    rw [h, Nat.bits_append_bit _ _ (fun h0 => absurd h0 (by positivity)), ih]
    simp [List.replicate_succ]

/-- **`2ⁿ` is time constructible** [AB09, §1.3: "`n`, `n log n`, `n²`, `2ⁿ` are time
constructible"]: `n ≤ 2ⁿ`, and `twoPowTM` writes `bits (2^|x|) = 0^|x| 1` in
`|x| + 1 ≤ 2^|x| + 1` steps. -/
theorem timeConstructible_two_pow : TimeConstructible (fun n => 2 ^ n) := by
  refine ⟨fun n => Nat.lt_two_pow_self.le, 1, Nat.one_pos, twoPowTM, fun x => ?_⟩
  obtain ⟨hs, hp, ho⟩ := twoPowTM_run x x.length (le_refl _)
  have hhalt : twoPowTM.ComputesInTime x (2 ^ x.length).bits (x.length + 1) := by
    rw [computesInTime_iff, MultiTapeTM.runFrom_succ_eq_step']
    generalize twoPowTM.tm.runFrom (twoPowTM.tm.initCfg x) x.length = c at hs hp ho
    have hin : c.inputSymbol = none := by
      have hpos : c.inputPos = ⟨x.length + 1, by omega⟩ := Fin.ext hp
      simp [Cfg.inputSymbol, hpos]
    unfold MultiTapeTM.step
    rw [hs]
    simp only [twoPowTM, hin, Action.apply]
    exact ⟨trivial, by simp [ho, bits_two_pow]⟩
  exact hhalt.mono (by have := @Nat.lt_two_pow_self x.length; simp only; omega)

/-- **Polynomials are eventually below `2ⁿ`**: for all constants `A` and `K` there is
`N` with `A · (n + 1)^K ≤ 2ⁿ` for all `n ≥ N`.

**Proof sketch.** Let `d = K + 1` and `m = ⌊n / d⌋`, so `n + 1 ≤ d (m + 1)` and
`d m ≤ n`. Then `A (n+1)^K ≤ A d^K (m+1)^K ≤ m · (2^m)^K < (2^m)^(K+1) ≤ 2ⁿ` as soon as
`m ≥ A d^K`, i.e. for `n ≥ d · A d^K`. -/
theorem eventually_poly_le_two_pow (A K : ℕ) :
    ∃ N, ∀ n ≥ N, A * (n + 1) ^ K ≤ 2 ^ n := by
  refine ⟨(K + 1) * (A * (K + 1) ^ K), fun n hn => ?_⟩
  set d := K + 1 with hd
  have hd0 : 0 < d := by omega
  set m := n / d with hm
  have hmA : A * d ^ K ≤ m := by
    rw [hm, Nat.le_div_iff_mul_le hd0]; rw [Nat.mul_comm]; exact hn
  have hn1 : n + 1 ≤ d * (m + 1) := Nat.lt_mul_div_succ n hd0
  have hdm : d * m ≤ n := Nat.mul_div_le n d
  have hm2 : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  calc A * (n + 1) ^ K ≤ A * (d * (m + 1)) ^ K :=
        Nat.mul_le_mul_left A (Nat.pow_le_pow_left hn1 K)
    _ = (A * d ^ K) * (m + 1) ^ K := by rw [mul_pow]; ring
    _ ≤ 2 ^ m * (2 ^ m) ^ K :=
        Nat.mul_le_mul (hmA.trans (Nat.le_of_lt (Nat.lt_two_pow_self)))
          (Nat.pow_le_pow_left hm2 K)
    _ = 2 ^ (d * m) := by rw [← pow_mul, ← pow_add, hd]; ring_nf
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hdm

/-- The hierarchy hypothesis for polynomial `f = nᵏ + 1` against `g = 2ⁿ`: for every
`A`, eventually `A · (nᵏ + 1 + n + 1)² ≤ 2ⁿ`. -/
theorem eventually_poly_sq_le_two_pow (k A : ℕ) :
    ∃ N, ∀ n ≥ N, A * (n ^ k + 1 + n + 1) ^ 2 ≤ 2 ^ n := by
  obtain ⟨N, hN⟩ := eventually_poly_le_two_pow (9 * A) (2 * k + 2)
  refine ⟨N, fun n hn => le_trans ?_ (hN n hn)⟩
  have h1 : n ^ k ≤ (n + 1) ^ (k + 1) :=
    (Nat.pow_le_pow_left (Nat.le_succ n) k).trans
      (Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_succ k))
  have h2 : n + 1 ≤ (n + 1) ^ (k + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have h3 : n ^ k + 1 + n + 1 ≤ 3 * (n + 1) ^ (k + 1) := by omega
  have h4 : (n ^ k + 1 + n + 1) ^ 2 ≤ 9 * (n + 1) ^ (2 * k + 2) := by
    calc (n ^ k + 1 + n + 1) ^ 2 ≤ (3 * (n + 1) ^ (k + 1)) ^ 2 := Nat.pow_le_pow_left h3 2
      _ = 9 * (n + 1) ^ (2 * k + 2) := by ring
  calc A * (n ^ k + 1 + n + 1) ^ 2 ≤ A * (9 * (n + 1) ^ (2 * k + 2)) :=
        Nat.mul_le_mul_left A h4
    _ = 9 * A * (n + 1) ^ (2 * k + 2) := by ring

/-- **The polynomial/exponential gap of the hierarchy theorem** [AB09, Theorem 3.1
instantiated]: `DTIME(nᵏ + 1) ⊊ DTIME(2ⁿ)` for every `k` (the `+ 1` normalization
is that of `Complexity.P`). -/
theorem dtime_poly_ssubset_dtime_two_pow (k : ℕ) :
    DTIME (fun n => n ^ k + 1) ⊂ DTIME (fun n => 2 ^ n) :=
  time_hierarchy_of_pos timeConstructible_two_pow (fun n => by positivity)
    (eventually_poly_sq_le_two_pow k)

/-- **`P ⊊ EXP`** [AB09, §3.1, consequence of the Time Hierarchy Theorem 3.1; the
inclusion is Claim 2.4]. The witness is the diagonal language `diagLang (2^·)`.

**Proof sketch.** Inclusion is `Complexity.P_subset_EXP`. The diagonal language with
budget `2ⁿ` lies in `DTIME(2ⁿ + 1) ⊆ DTIME(2^(n¹))` up to the constant `2`, hence in
`EXP`; and for every `k` it is not in `DTIME(nᵏ + 1)` (`diagLang_not_mem_DTIME`, whose
hypothesis `A (nᵏ + 1 + n + 1)² ≤ 2ⁿ` holds eventually by
`eventually_poly_sq_le_two_pow`), hence not in `P = ⋃ₖ DTIME(nᵏ + 1)`. -/
theorem P_ssubset_EXP : P ⊂ EXP := by
  refine ⟨P_subset_EXP, fun h => ?_⟩
  have hmem : diagLang (fun n => 2 ^ n) ∈ EXP := by
    obtain ⟨c, M, hM⟩ := diagLang_mem_DTIME timeConstructible_two_pow
    refine Set.mem_iUnion.mpr ⟨1, 2 * c, M, fun x => (hM x).mono ?_⟩
    have : 1 ≤ 2 ^ x.length := Nat.one_le_two_pow
    simp only [pow_one]
    nlinarith
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (h hmem)
  refine diagLang_not_mem_DTIME (T := fun n => n ^ k + 1) (fun A N₀ => ?_) hk
  obtain ⟨N, hN⟩ := eventually_poly_sq_le_two_pow k A
  exact ⟨max N N₀, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- **`P ≠ EXP`** [AB09, §3.1]. -/
theorem P_ne_EXP : P ≠ EXP := P_ssubset_EXP.ne

end Complexity
```


## ===== TCSlib.lean =====

```
import TCSlib.ErrorCorrectingCodes.Basic
import TCSlib.ErrorCorrectingCodes.SingletonBound
import TCSlib.ErrorCorrectingCodes.HammingBound
import TCSlib.ErrorCorrectingCodes.Entropy
import TCSlib.ErrorCorrectingCodes.LinearCodes
import TCSlib.ErrorCorrectingCodes.GilbertVarshamov
import TCSlib.ErrorCorrectingCodes.ListDecoding
import TCSlib.ErrorCorrectingCodes.QuantumSingleton
import TCSlib.ErrorCorrectingCodes.QuantumHamming
import TCSlib.ErrorCorrectingCodes.JohnsonBound
import TCSlib.ErrorCorrectingCodes.MRRW

import TCSlib.BooleanAnalysis.BLR
import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.ArrowTheorem
import TCSlib.BooleanAnalysis.Hypercontractivity
import TCSlib.BooleanAnalysis.Switching
import TCSlib.BooleanAnalysis.KKL
import TCSlib.BooleanAnalysis.ThresholdFunctions
import TCSlib.BooleanAnalysis.polylogIndep

import TCSlib.CommunicationComplexity.DeterministicCC
import TCSlib.CommunicationComplexity.NewmanTheorem

import TCSlib.Complexity.CircuitComplexity
import TCSlib.Complexity.NPReductions
import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.Uncomputability
import TCSlib.Complexity.ClassP
import TCSlib.Complexity.Formulas
import TCSlib.Complexity.CookLevin
import TCSlib.Complexity.ClassNP
import TCSlib.Complexity.ClassOracle
import TCSlib.Complexity.Diagonalization
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.Diagonalization.NTimeHierarchy
import TCSlib.Complexity.ClassPSPACE
import TCSlib.Complexity.PolyHierarchy
import TCSlib.Complexity.TimeHierarchy
import TCSlib.Complexity.SpaceComplexity

import TCSlib.ComputationalModels

import TCSlib.Cryptography.SchnorrProtocol
import TCSlib.Cryptography.SecretSharing
import TCSlib.Cryptography.MPC

import TCSlib.InformationTheory

import TCSlib.GraphTheory.Kruskal

import TCSlib.KikuchiLDC.Main

import TCSlib.LearningTheory.MistakeBounds
import TCSlib.LearningTheory.Hedge
import TCSlib.LearningTheory.JohnsonLindenstrauss
import TCSlib.LearningTheory.Minimax
```


## ===== audits/logs/ch3-p33-r2-sweep.log =====

```
P3.3_R2 GATE SWEEP at commit 9a92fa1aeb377d568972e42229979cf81562ba41 (9a92fa1a), branch complexity/arora-barak-ch3-4, started 2026-10-08 23:41:16
== TCSlib/Complexity/TuringMachine/NDCodes
TCSlib/Complexity/TuringMachine/NDCodes.lean:187:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/Diagonalization/NTimeHierarchy
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:121:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:146:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:191:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:275:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:289:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:314:8: warning: declaration uses 'sorry'
P3.3_R2_SWEEP_DONE
```


## ===== audits/logs/ch34-r2-repairs-stylelint.log =====

```
== TCSlib/Complexity/TuringMachine ==
WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  1012 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5713 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7636 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1109 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
INFO  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  1012 lines; 39 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean               157 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    580 lines; 19 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5713 lines; 8 public / 214 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7636 lines; 18 public / 318 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     454 lines; 13 public / 0 private declarations
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
== TCSlib/Complexity/Diagonalization ==
INFO  TCSlib/Complexity/Diagonalization/EXPCOM.lean                272 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean        318 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean  93 lines; 1 public / 0 private declarations
INFO  TCSlib/Complexity/Diagonalization/Relativization.lean        232 lines; 5 public / 0 private declarations

style_lint: 0 FAIL, 0 WARN over 4 files
== TCSlib/Complexity/Formulas ==
INFO  TCSlib/Complexity/Formulas/CNF.lean          259 lines; 5 public / 9 private declarations
INFO  TCSlib/Complexity/Formulas/CNFEncoding.lean  475 lines; 13 public / 9 private declarations
INFO  TCSlib/Complexity/Formulas/DNF.lean          172 lines; 13 public / 0 private declarations
INFO  TCSlib/Complexity/Formulas/QBF.lean          125 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/Formulas/QBFEncoding.lean  91 lines; 5 public / 0 private declarations

style_lint: 0 FAIL, 0 WARN over 5 files
== TCSlib/Complexity/ClassPSPACE ==
INFO  TCSlib/Complexity/ClassPSPACE/Games.lean  101 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/ClassPSPACE/TQBF.lean   296 lines; 9 public / 0 private declarations

style_lint: 0 FAIL, 0 WARN over 2 files
== TCSlib/Complexity/SpaceComplexity ==
INFO  TCSlib/Complexity/SpaceComplexity/Basic.lean                          161 lines; 10 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean                    460 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    305 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Constructible.lean                  95 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean                 495 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean              246 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Examples.lean                       65 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean                      234 lines; 4 public / 0 private declarations
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
