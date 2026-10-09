# External audit pack — Chapter 3, phase P3.2 (relativization), round 2 (re-audit of the round-1 repairs)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase
P3.2, round 2. Round 1 (`audits/ch3-p32-findings.md`, attached verbatim)
returned **1 blocker, 0 majors, 2 minors, 2 notes**; per `workflow.md` §3
the gate did not close. This round audits the repairs. The gate closes on
zero blockers and zero majors.

Audited at commit `9a92fa1a` (branch `complexity/arora-barak-ch3-4`). The
complete repair is the attached diff
(`audits/evidence/ch3-p32-r2-repairs.diff`): **one new structure, one new
sorried statement, one new noncomputable definition, one definition
restated** — `Turing.UniformMachineCode`,
`Turing.exists_uniformMachineCode`, `Complexity.expCode`, and `EXPCOM`
redefined over `expCode` — plus the rewritten scheme design bullet, the
corrected uniqueness citations, the updated `EXP ⊆ P^EXPCOM` and
`NP^EXPCOM ⊆ EXP` sketches, and the repaired enumeration sketch. The four
dependent statements (`NPOracle_EXPCOM_subset_EXP` and the three
identities) are **unchanged in shape**, now over the repaired oracle. The
inventory grows from 17 to **18 sorried statements** (OracleAgreement 7,
EXPCOM 6, Relativization 4, NotTimeConstructible 1).

**Layering update since round 1**: the P3.1 gate closed before round 1 ran
(`audits/ch3-p31-resolutions.md`); its clock-convention deviation (round-1
note 4) is retained as declared. `Turing.timed_universal`'s home module
(`Universal.lean`) and the concrete-scheme construction
(`MathlibBridge.lean`, `CodeParser.lean`) are now **attached**, per round-1
note 5's request.

## Brief for the auditor

You have the round-1 report. Your deliverables:

1. **For the blocker**: audit the repair as fresh surface. Blind-restate
   `Turing.UniformMachineCode` — the two simulator clauses decide bounded
   acceptance (`(decode α).toFinTM.ComputesInTime x [true] t`) on
   `⟨⟨bits t, α⟩, x⟩` within `simDegree · (|α| + |x| + t + 1) ^ simDegree`,
   **one polynomial uniform in the code** — and check it against your own
   counterconstructions: your tagged scheme `c_H` admits a canonizer but can
   it admit this simulator? (It cannot while `H ∉ EXP` — verify that the
   interface genuinely excludes both your `EXPCOM[c_H] ∉ EXP` scheme and
   your `P ≠ NP`-relativizing scheme.) Then check the four dependent
   statements over the repaired `EXPCOM`: is `NP^EXPCOM ⊆ EXP`'s ledger now
   payable (the updated sketch charges each query
   `simDegree · (3·p n + 2^(n') + 1) ^ simDegree = 2^{O(p n)}`), and do the
   identities follow? Also audit the **declared choice-over-a-sorried
   existence**: `expCode := Classical.choice exists_uniformMachineCode`
   mirrors `TimeHierarchy.code` structurally, but its existence is sorried
   — the pack declares that `EXPCOM` and its consumers carry `sorryAx`
   through the choice until that fill lands. Is `exists_uniformMachineCode`
   itself true as stated (the chapter-1 concrete scheme with its per-phase
   polynomial ledgers assembled — the sketch names the obligations)?
2. For the **minors**: the enumeration sketch now uses a **three-state**
   well-formed default (or the `toFinOracleTM` embedding) and an explicit
   repetition coordinate in a `ℕ × ℕ × ℕ × ℕ` pairing (finding 2); the
   uniqueness citations now read `pairEncode_injective` twice plus
   `List.length` on the replicated tails (finding 3). Verify both match
   your proposed fixes.
3. Report anything the repairs broke or newly misstate — in particular
   whether the uniform-simulator interface is **stronger than needed**
   anywhere it is consumed, whether `EXP ⊆ P^EXPCOM`'s fixed-code sketch
   survives the scheme change (it now encodes via `expCode`), and whether
   any statement outside the EXPCOM cluster accidentally depends on the
   new scheme — in the round-1 findings-table format and severity scale.

Sources as in round 1 ([AB09] §3.4, Example 3.6(3), Theorem 3.7, Exercise
3.5; [BGS75] at the scanned original, link in the round-1 pack).

## Scope

| Item | Where |
|---|---|
| Under audit | the attached diff: `Diagonalization/EXPCOM.lean` (the new structure, existence statement, `expCode`, the restated `EXPCOM`, the design-bullet and sketch rewrites) and `Diagonalization/Relativization.lean` (the enumeration-sketch repair) |
| Unchanged, re-attached | `TuringMachine/OracleAgreement.lean`, `Diagonalization/NotTimeConstructible.lean` (round 1 passed both; the latter's carry-aware equality sketch was already correct), the `Diagonalization.lean` facade, and the P3.1-closed oracle surface |
| Newly attached context | `TuringMachine/Universal.lean` (`timed_universal` — the per-code contrast), `TuringMachine/MathlibBridge.lean` and `TuringMachine/CodeParser.lean` (the concrete scheme the uniform fill assembles), `ClassNP/EXP.lean` |
| Declared, out of scope | the same commit range contains the concurrent §12/P4.3/P3.3 repairs (disjoint files, own rounds); tactic proofs; round-1 items passed without change |

## Per-finding disposition (verify each)

| # | Round-1 finding | Repair |
|---|---|---|
| 1 | **blocker** — an arbitrary effective scheme bounds no decoding time; permitted schemes put `EXPCOM` outside `EXP` and even separate its relativized `P` from `NP` | `EXPCOM` is redefined over `Complexity.expCode : Turing.UniformMachineCode` — the scheme packaged with a bounded-acceptance simulator at **one polynomial in `\|α\| + \|x\| + t + 1` jointly** (your proposed "scheme together with a proved uniform complexity property", as an interface; the existence is the new sorried statement, its fill the chapter-1 concrete scheme's ledgers assembled). Your tagged schemes satisfy `EffectiveMachineCode` but not the simulator clauses — deciding the embedded `H` in the uniform budget would put it in `EXP`. The hierarchy's `TimeHierarchy.code` is untouched, per your note that fixed-code arguments never needed uniformity |
| 2 | minor — the one-state default is not well-formed; bijective pairing has singleton fibers | The sketch now uses a three-state well-formed default (or the `toFinOracleTM` embedding of a one-state machine, which adjoins the three special states) and an explicit repetition coordinate as the fourth component of the pairing |
| 3 | minor — `pairEncode_replicate_inj` has the unary word on the wrong side | All citation sites now read: `Turing.pairEncode_injective` applied twice, then `List.length` on the equality of the replicated tails |
| 4 | note — fixed-oracle clocks vs [BGS75]'s all-oracle clocks | Retained as the declared P3.1 deviation; no change, per the round-1 disposition |
| 5 | note — `timed_universal` unattached; attestation limits | `Universal.lean`, `MathlibBridge.lean`, and `CodeParser.lean` attached this round; build-artifact claims remain maintainer attestations |

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch3-p32-r2-sweep.log`, revision recorded
  at start: `9a92fa1a`): all five modules, facade listed, 0 `error:` lines,
  fresh `.olean`s, exactly **18** `declaration uses 'sorry'` warnings
  (OracleAgreement 7, EXPCOM 6, Relativization 4, NotTimeConstructible 1).
* Style lint (`audits/logs/ch34-r2-repairs-stylelint.log`):
  `Diagonalization` 0 FAIL / 0 WARN over 4 files.
* Statement-freeze baseline: commit `9a92fa1a`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch3-p32-r2-findings.md`; the gate closes on zero blockers and
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


## ===== audits/ch3-p32-findings.md =====

```
# P3.2 statement-gate audit: Baker–Gill–Solovay relativization

**Verdict: FAIL — the gate does not close.** Findings: **1 blocker, 0 majors, 2 minors, 2 notes.** The blocking issue is the use of an arbitrary effective machine-code scheme in an assertion requiring uniformly efficient decoding. The diagonal construction and all seven locality statements survive the audit.

Audited packet: `ch3-p32-bundle.md`, declared commit `7fbac9bdff79aee148b916e077ad93b6ce4693f9`, branch `complexity/arora-barak-ch3-4`. SHA-256 independently verified:

```text
dbfadcfbc77ef508a89e927ab2d04c122c6ab65ddac98462e85fe0c0547c3e2a
```

This is a mathematical audit of definitions, statements, and proof sketches, not a Lean proof-completion or kernel audit. All four new definitions, all seventeen sorried statements, and the facade were inspected. File-local line numbers below refer to the source attachments extracted from the bundle.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **blocker** | `Diagonalization/EXPCOM.lean` · `EXPCOM` (82), `NPOracle_EXPCOM_subset_EXP` (162), and the three identities (170, 178, 187) | The fixed effective code scheme makes variable-code bounded acceptance decidable within the claimed exponential ledger. | `Encoding.lean:558–566` permits an arbitrary `canonizerTime`. `TimeHierarchy/Diagonal.lean:107` chooses an arbitrary inhabitant of `EffectiveMachineCode`; its universal-machine specification at 113 has **`∀ α, ∃ C`**, with no bound on the code-dependent constant. In contrast, EXPCOM queries contain variable codes. The ledger at `EXPCOM.lean:146–152` silently treats their decoding/simulation overhead as uniform. The construction below gives permitted effective schemes for which EXPCOM is outside EXP, and even schemes for which its relativized P and NP differ. | Select an explicitly efficient scheme for EXPCOM, or select a scheme together with a proved uniform complexity property. Prove a bounded-acceptance algorithm whose time includes code parsing, canonization, decoded-table size, and simulation, uniformly in the code. Re-audit the resulting definition and four dependent assertions. The existing hierarchy scheme need not be changed: arbitrary effective schemes are adequate for its fixed-code argument. |
| 2 | **minor** | `Diagonalization/Relativization.lean` · sketch of `exists_finOracleTM_enumeration`, 129–147, especially 135 | A “well-formed one-state default” totalizes the enumeration. | Both `OracleTM.WellFormed` and the bundled `FinOracleTM` require three pairwise distinct special states. No one-state machine satisfies this. The enumeration theorem itself is true. | Use a three-state default, or embed a plain one-state machine using the existing embedding, which adjoins three states. Specify a separate repetition coordinate to make recurrence explicit; a bijective triple pairing alone has singleton fibers. |
| 3 | **minor** | `Diagonalization/EXPCOM.lean` · uniqueness citations at 80–81, 107, 144–145 | `pairEncode_replicate_inj` is the fact recovering the unary component in this nesting. | `Encoding.lean:256–264` concerns `pairEncode (replicate n true) u`: the unary word is the **first** component. Here it is the second component of the inner pair. Uniqueness is nevertheless true. | Apply `pairEncode_injective` twice, then apply `List.length` to the equality of the two replicated lists. Remove or replace the mismatched citation; no definition change is needed for this finding. |
| 4 | **note** | **[P3.1]** `ClassOracle/Classes.lean` · `DTIMEOracle`, `NTIMEOracle`, `POracle`, `NPOracle` | The attached classes impose a bound under the selected oracle; BGS75 enumerates machines clocked under every oracle. | This is the declared quantifier difference. P3.2 does not infer any runtime bound under a temporary oracle from a bound under the final oracle. Its bounded simulation and exact-horizon behavioral equivalence avoid that error. | Retain the deviation record. A class-level equivalence with BGS75's convention uses a polynomial clock wrapper; P3.2's diagonal proof does not require that equivalence as an intermediate lemma. |
| 5 | **note** | Pack · repository-side attestations and dependency coverage | The attached logs certify a fresh build and the complete imported implementation. | The five new files contain exactly 4 definitions, 17 theorem stubs, 17 executable `sorry` tokens, and no `axiom` declarations. The supplied sweep contains exactly 17 sorry warnings and no `error:` lines. Fresh `.olean`s, unchanged-file claims, root export, and a full dependency build cannot be independently checked from these attachments. In particular, the body/signature of `timed_universal` is not attached. | Preserve these as maintainer attestations, distinct from this audit's checks. Supply the actual uniform simulator contract in the repair packet. This evidence limitation is not an additional blocker. |

Finding 1 belongs to **P3.2**, not the deferred P3.1 gate: it is a new, invalid use of the hierarchy's deliberately weak coding interface.

## Why finding 1 is substantive

### Effective decoding does not imply the required bound

Write `EXPCOM[c]` for the packet's definition with code scheme `c`. This notation is only for the audit; the submitted definition is not parameterized.

Choose a decidable language $H\notin\mathrm{EXP}$. For completeness, such a language can be constructed without assuming any unproved separation: effectively enumerate all triples of deterministic machines and natural-number clock parameters $(M_j,a_j,k_j)$, and define

\[
1^j\in H
\iff
\neg M_j.\mathrm{ComputesInTime}
       (1^j,[\mathrm{true}],a_j2^{j^{k_j}}),
\]

rejecting non-unary strings. This is a terminating finite simulation on every input. If a machine with parameters $a,k$ decided $H$ in time $a2^{n^k}$, its enumerated triple would give a contradictory verdict on the corresponding $1^j$. Thus $H$ is decidable and outside EXP. Repetitions in this enumeration are harmless.

Start with an ordinary effective scheme $c_0$. Let $M_+$ and $M_-$ be one-work-tape binary machines that halt in one step with outputs `[true]` and `[false]`, respectively. Define another scheme $c_H$ by

\[
\begin{aligned}
\mathrm{encode}_{c_H}(M)&=0\,\mathrm{encode}_{c_0}(M),\\
\mathrm{decode}_{c_H}(0\alpha)&=\mathrm{decode}_{c_0}(\alpha),\\
\mathrm{decode}_{c_H}(1s)&=
\begin{cases}M_+&s\in H,\\M_-&s\notin H,\end{cases}\\
\mathrm{decode}_{c_H}(\varepsilon)&=M_-.
\end{aligned}
\]

This satisfies the attached interface:

1. Decoding is total.
2. For every machine $M$ and padding length $r$,
   \[
   \mathrm{decode}_{c_H}(\mathrm{encode}_{c_H}(M)1^r)
   =\mathrm{decode}_{c_0}(\mathrm{encode}_{c_0}(M)1^r)=M.
   \]
3. A canonizer is computable: inspect the tag, then run the old canonizer or decide $H$ and emit the appropriate fixed serialization. Because this machine halts on every word, the maximum of its runtimes over the finitely many words of each length supplies `canonizerTime`. The interface requires no efficient bound on that maximum.

Now consider the linear-time map

\[
f(s)=\mathrm{pairEncode}(1s,
              \mathrm{pairEncode}(\varepsilon,\varepsilon)).
\]

Both empty components are legitimate, the padding exponent is zero, and $2^0=1$. Therefore

\[
\begin{aligned}
s\in H
&\iff \mathrm{decode}_{c_H}(1s)=M_+\\
&\iff \mathrm{decode}_{c_H}(1s)
       \text{ halts on }\varepsilon\text{ with }[\mathrm{true}]\text{ within one step}\\
&\iff f(s)\in\mathrm{EXPCOM}[c_H].
\end{aligned}
\]

Moreover, $\vert f(s)\vert =2\vert s\vert +6$. An EXP decider for `EXPCOM[c_H]` would consequently decide $H$ in EXP, a contradiction. Since any oracle belongs to its own relativized P, and relativized P is contained in relativized NP,

\[
\mathrm{EXPCOM}[c_H]\in
\mathrm P^{\mathrm{EXPCOM}[c_H]}
\subseteq\mathrm{NP}^{\mathrm{EXPCOM}[c_H]}.
\]

Thus the upper inclusion and both identities with EXP fail for permitted effective schemes. Taking a maximum of code-dependent constants over codes of bounded length does not repair this: the maximum exists but need not have an exponential bound.

The issue with `Classical.choice exists_effectiveMachineCode` is precise: it supplies an inhabitant of the weak type, not a proof that the chosen inhabitant is an efficiently decoding witness used inside an existence proof. No attached theorem identifies this choice with an efficient scheme. The counterexample establishes insufficient specification; it does not purport to evaluate an opaque choice operation.

### The P-versus-NP identity is also not uniform over effective schemes

The fourth dependent assertion, `POracle_EXPCOM_eq_NPOracle_EXPCOM`, cannot be justified merely by dropping the identities with EXP.

Take any effective scheme $c_0$ and put $E_0=\mathrm{EXPCOM}[c_0]$. There is a **decidable** language $H$ such that, for

\[
A=\{0z:z\in E_0\}\cup\{1z:z\in H\},
\qquad \mathrm P^A\ne\mathrm{NP}^A.
\]

Here is the required construction. Use an effective recurrent enumeration of deterministic oracle machines. At a fresh length $n_i$, simulate its $i$-th machine for $t_i=n_i^i+i<2^{n_i}$ steps on $1^{n_i}$. Answer tag-0 queries with the fixed decidable language $E_0$, and tag-1 queries with the finite set already placed into $H$. If the machine accepts, add nothing at length $n_i$; otherwise insert a length-$n_i$ word whose tag-1 query was not asked. Require $n_i\ge i+2$, and choose each later length larger than all earlier lengths and budgets. The query-count bound supplies the word, and locality preserves each flipped answer. The polynomial-budget domination proved below then excludes the unary witness language of $H$ from $\mathrm P^A$, while one guessed word and a tag-1 query put it in $\mathrm{NP}^A$.

All stages are effective: finite simulation calls only the decidable $E_0$ and a finite set; choose the least suitable length and least unqueried word. To decide membership in $H$ for a word of length $m$, run stages until their fresh length exceeds $m$. Increasing fresh lengths guarantee termination and permanent membership at length $m$.

Construct $c_H$ as above using this $H$. Then `EXPCOM[c_H]` and $A$ reduce to one another in polynomial time. To reduce `EXPCOM[c_H]` to $A$, parse the triple; a tag-0 code asks the corresponding $E_0$ triple, and a tag-1 code asks membership of its suffix in $H$. In the reverse direction, retag the code of a parsed $E_0$ triple, or use $f(s)$ for a tag-1 query. Malformed inputs map to a fixed nonmember. The maps use only parsing and copying. Substituting these reductions for oracle calls preserves polynomial time, also branchwise. Consequently

\[
\mathrm P^{\mathrm{EXPCOM}[c_H]}=\mathrm P^A
\ne\mathrm{NP}^A=\mathrm{NP}^{\mathrm{EXPCOM}[c_H]}.
\]

This is a mathematical counterconstruction, not a Lean-checked counterexample file.

## Blind restatements of the four definitions

These restatements follow the formal bodies, including their boundary cases.

| Definition | Restatement | Fidelity assessment |
|---|---|---|
| `OracleTM.queriesWithin M O x t` | Initialize $M$ on $x$, and run with $O$. For each integer $s=0,\ldots,t-1$, inspect the configuration after exactly $s$ steps. If its state is `some qQuery`, append that configuration's `queryString`; otherwise append nothing. Preserve order and repetitions. | Correct list of consultations performed by the first $t$ transitions. It records query-state occupancy before the answering transition, not merely entry into that state. No well-formedness hypothesis is required. |
| `OracleNDTM.queriesAlong N O x w` | For each $s<\vert w\vert $, run from initialization using the first $s$ bits of $w$. Record the query string exactly when that prefix run is in `qQuery`, in increasing $s$ order and with repetitions. | Correct fixed-branch analogue. Every transition consumes a bit; query-answer transitions ignore its value. `w.take t` gives a horizon of $\min(t,\vert w\vert )$. |
| `EXPCOM` | A word belongs iff it equals `pairEncode α (pairEncode x (replicate n true))` for some code word, input word, and natural number $n$, and the decoded machine has halted with output exactly `[true]` after $2^n$ transitions. Absorbing halting makes this equivalent to halting by that deadline. | The triple layout, inclusivity, and rejection of nontriples are sound. Empty code/input/padding are allowed. Every code word denotes a machine; a malformed *machine code* need not be rejected. The weak decoding specification invalidates the advertised EXP interpretation: finding 1. |
| `unaryWitnessLang B` | A word belongs iff it consists of $n$ true bits for some $n$, and $B$ contains a word of length exactly $n$. | Matches the intended unary witness language. The empty input belongs iff the empty word belongs to $B$. Every input containing a false bit is excluded. |

## All seventeen statement verdicts

“True” below means the statement survives a mathematical reconstruction over the attached semantics; it does not mean its `sorry` has been filled.

| # | Declaration | True-as-stated argument or obstruction |
|---|---|---|
| 1 | `OracleTM.runFrom_eq_of_agree_length_lt` | **True.** Induct on the elapsed steps up to $t$. At step $s<t$, an initialized query has length at most $s<t$; agreement therefore fixes the answer. Other steps are oracle-independent. |
| 2 | `OracleTM.runFrom_eq_of_agree_queriesWithin` | **True.** The same induction uses membership of the actual query at index $s$ in the first oracle's list. Equality of prefix configurations makes the asymmetry sufficient. |
| 3 | `OracleTM.length_le_of_mem_queriesWithin` | **True.** A listed word comes from an index $s<t$, with length at most $s$. In fact the stronger conclusion $\vert z\vert <t$ holds. |
| 4 | `OracleTM.queriesWithin_length_le` | **True.** `filterMap` retains at most one item per element of `List.range t`. |
| 5 | `OracleNDTM.runWith_eq_of_agree_length_lt` | **True.** Induct over prefixes of the fixed word. The same tape invariant holds because actions write at the old head and move by at most one, while query/halting transitions do not write. |
| 6 | `OracleNDTM.runWith_eq_of_agree_queriesAlong` | **True.** Prefix equality plus agreement on the first branch's submitted queries gives equality of the next transition under the common next bit. |
| 7 | `OracleNDTM.length_le_of_mem_queriesAlong` | **True.** A listed query occurs after $s<\vert w\vert $ transitions and has length at most $s$; again the strict bound is available. |
| 8 | `EXP_subset_POracle_EXPCOM` | **True even for the weak code interface.** For each language, fix one decider and one code once and for all; its code is a constant in the reduction. Quadratic normalization preserves exponential time. A sufficiently large polynomial unary exponent makes one query correct. No uniform decoding bound is used here. Finding 3 corrects a cited lemma only. |
| 9 | `NPOracle_EXPCOM_subset_EXP` | **Not cleared; finding 1.** Variable-code decoding can exceed every EXP bound. |
| 10 | `POracle_EXPCOM_eq_EXP` | **Not cleared; finding 1.** A permitted `EXPCOM` can itself be outside EXP while belonging to its own relativized P. |
| 11 | `NPOracle_EXPCOM_eq_EXP` | **Not cleared; finding 1.** The same counterexample applies to relativized NP. |
| 12 | `POracle_EXPCOM_eq_NPOracle_EXPCOM` | **Not cleared; finding 1.** The second counterconstruction above gives an effective coding scheme whose EXPCOM oracle separates the classes. |
| 13 | `unaryWitnessLang_mem_NPOracle` | **True.** The explicit scan/guess/query/answer construction below runs in at most $n+3$ steps, with rejection on every non-unary branch. |
| 14 | `exists_finOracleTM_enumeration` | **True.** Finite transition tables with fixed tape/state counts form a finite set; state relabeling preserves exact-horizon output predicates under every oracle. Enumerate the canonical tables and add a repetition coordinate. Correct the impossible default in finding 2. |
| 15 | `exists_oracle_ne` | **True.** The fresh-length construction, query preservation, and explicit polynomial domination below prove the stated conjunction. Neither EXPCOM nor uniform decoding is needed. |
| 16 | `baker_gill_solovay` | **The existential theorem is true. Its submitted assembly is blocked.** A conventional efficient bounded-acceptance oracle supplies the equality half, and statement 15 supplies the separation half. The particular choice `A := EXPCOM` is not justified until finding 1 is repaired. |
| 17 | `exists_not_timeConstructible` | **True.** Its HALT-bit witness dominates the identity, is nondecreasing, and would make HALT computable if a constructor existed. Details below. |

The facade imports all four relevant component modules, including `OracleAgreement`. Its headline EXPCOM descriptions inherit finding 1. It introduces no definition or theorem.

## Answers to the seven numbered questions

### 1. Behavioral equivalence and enumeration

The quantifier order is adequate:

\[
\exists N\;\forall M\;\forall i_0\;\exists i\ge i_0\;
\forall O,x,\mathrm{output},t\;[\text{equal bounded-output predicates}].
\]

The enumeration is fixed before constructing the final oracle. Selecting a late representative of an alleged decider afterward does not change the enumeration or the oracle. Because equivalence holds at every horizon and for both Boolean verdicts, monotonicity transfers a decider's output to the stage deadline; output uniqueness excludes the opposite output.

State relabeling is strong enough: a bijection on states preserves the initial state, all three distinguished states, transition outputs, and halting. Its configuration transport commutes with each step, including query resolution. Well-formedness ensures at least three states; all such machines occur among the canonical `Fin (m+1)` tables. Empty well-formed table sets at smaller state counts cause no completeness problem.

For explicit recurrence, first let $E(j)$ enumerate canonical tables with a valid default. Set

\[
N(\mathrm{pair}(j,r))=E(j).
\]

For each fixed $j$, injectivity of the pairing makes these indices infinite, hence unbounded. This proves the required recurrence without asserting literal equality of bundled state types.

### 2. Stage construction, consistency, and diagonal quantifiers

Write $t_i=n_i^i+i$. Choose each $n_i\ge i+2$ larger than every previous $n_j,t_j$, with

\[
2^{\lfloor n_i/10\rfloor}>t_i.
\]

Such choices exist because an exponential eventually exceeds each fixed polynomial. Let $O_i$ be the finite set of positive insertions before stage $i$. It contains no word of length $n_i$. Run $N_i^{O_i}$ on $1^{n_i}$ for $t_i$ transitions. If it has halted with output `[true]`, insert nothing; otherwise insert one length-$n_i$ word outside its query list. There are $2^{n_i}>t_i$ candidates and at most $t_i$ listed queries.

Treat every remaining word of length at most $\max(n_i,t_i)$ as permanently negative, while retaining earlier positives. This specifies the negative declarations that the sketch leaves implicit. Define $B=\bigcup_i O_i$.

For every query $z$ made at stage $i$:

\[
z\in O_i\Rightarrow z\in B;
\qquad
z\notin O_i\Rightarrow z\notin B.
\]

The second implication holds because the current inserted word is unqueried, and every later inserted word has length greater than $t_i\ge\vert z\vert $. Therefore the asymmetric locality theorem applies with **first oracle $O_i$** and **second oracle $B$**. It preserves the complete configuration at the deadline and hence the exact acceptance predicate. Consequently

\[
(N_i).\mathrm{ComputesInTime}(B,1^{n_i},[\mathrm{true}],t_i)
\iff 1^{n_i}\notin\mathrm{unaryWitnessLang}(B).
\]

Suppose a machine $M$ decided that language within $c(n^k+1)$. Select a behaviorally equal recurrence index

\[
i\ge\max(k+1,2c,2).
\]

Since $n_i\ge i+2$,

\[
c(n_i^k+1)
\le 2c\,n_i^k
\le n_i^{k+1}
\le n_i^i
\le t_i.
\]

Monotonicity and behavioral equivalence now give acceptance at the stage budget iff $1^{n_i}$ is in the language, contradicting the displayed flip. Nonhalting and wrong-output machines need not be deciders: both merely fall into the nonaccepting case. Earlier positives cannot conflict with the accepting-stage instruction because their lengths are strictly smaller than $n_i$.

### 3. EXPCOM's shape and uniqueness

The existential definition does not assume decidability or a complexity bound. Its parsing is unambiguous. From

\[
\mathrm{pairEncode}(\alpha,\mathrm{pairEncode}(x,1^n))
=\mathrm{pairEncode}(\beta,\mathrm{pairEncode}(y,1^m))
\]

two uses of pair injectivity give $\alpha=\beta$, $x=y$, and $1^n=1^m$; taking lengths gives $n=m$. The cited unary-first lemma is unnecessary and mismatched.

The total length is exactly

\[
|z|=2|\alpha|+2|x|+n+4.
\]

`ComputesInTime` requires both haltedness and the exact output, so it is faithful to inclusive “within.” A machine that has merely written `[true]` but has not halted is excluded. Bounded acceptance is computable for every effective scheme, but finding 1 shows it need not be in EXP.

### 4. EXPCOM simulation summit and the last-step boundary

The class-inclusion shape is appropriate for an efficiently coded oracle. Its boundary arithmetic is correct. If the answering transition is the last of $p(n)$ transitions, its query is read after $s=p(n)-1$ transitions, so

\[
n'\le|z|\le s<p(n).
\]

For a parsed triple the stronger $\vert z\vert =2\vert \alpha'\vert +2\vert x'\vert +n'+4$ also holds. If `qQuery` is only reached *after* transition $p(n)$, no query has yet been answered at that horizon. Moreover such a branch is still live and cannot satisfy all-branch halting at the promised deadline.

An actual halted branch cannot end with the answering transition either: that transition leaves a live answer state. The length bound above is valid even without using this additional restriction.

What fails is the next inference, from bounded query length to a uniform cost for decoding its code. A sufficient repair is a concrete timed simulator with a fixed polynomial bound in

\[
|\alpha'|+|x'|+t+1,
\qquad t=2^{n'},
\]

including canonization. With that property, $2^{p(n)}$ branch words, at most $p(n)$ calls per word, and polynomial parsing/copying overhead give total time $2^{\mathrm{poly}(n)}$. This includes emitting the deadline, restoring simulated tapes, and dispatching the next transition. A merely code-dependent constant does not suffice. The precise `timed_universal` success/timeout interface remains an unattached dependency; the mathematical inclusive-deadline algorithm itself is possible with an efficient scheme.

### 5. Locality indexing and nondeterministic horizons

There is no off-by-one defect. The transition from time $s$ to time $s+1$ consults the oracle exactly when the time-$s$ state is `qQuery`; these are precisely the indices $s<t$. At $t=0$, the query list is empty. At $t=1$, an initial query state submits the empty word and is correctly included.

For nondeterminism, `runWith` consumes the next bit before recursively processing the suffix, including when `stepWith` ignores it at a query state. Prefix length therefore equals elapsed transitions. In particular, the guess-writer's witness is the **first $n$ choice bits**, while the full word also has bits for its deterministic tail and any halting padding. Equality along prefixes and the initialized tape invariant prove all seven locality statements; well-formedness and finiteness of the state type are unnecessary for them.

### 6. Non-time-constructibility and monotonicity

The requested nontrivialization is adequate for Exercise 3.5. In fact the proposed witness already satisfies monotonicity. Write its HALT bit as $b(n)\in\{0,1\}$. Then

\[
T(n)=n+b(n),\qquad
n\le T(n)\le n+1\le T(n+1).
\]

Thus it is nondecreasing and differs from the identity by at most one. No statement change is necessary to meet the exercise.

Let `str` and `rank` be inverse effective enumerations between naturals and binary strings. A putative constructor, run on $1^{\mathrm{rank}(s)}$, would return the canonical binary representation of $T(\mathrm{rank}(s))$. Hence

\[
\begin{aligned}
\mathrm{HALT}(s)=\mathrm{true}
&\iff T(\mathrm{rank}(s))=\mathrm{rank}(s)+1\\
&\iff (T(\mathrm{rank}(s))).\mathrm{bits}
       \ne(\mathrm{rank}(s)).\mathrm{bits}.
\end{aligned}
\]

The last equivalence uses injectivity of canonical binary representation. Computing the rank, emitting the unary word, running the total constructor, and comparing finite words are all terminating computations; no runtime bound is needed. This contradicts the attached `HALT_not_computable`. Equality comparison handles odd ranks with a carry and rank zero; merely reading a low bit without accounting for the rank's parity would not.

### 7. Unary witness membership in NPOracle

A four-state machine suffices: scan, query, yes, no. While scanning a true input symbol, write the current choice bit in the current query-tape cell and advance both heads. On a false input symbol, emit `[false]` and halt. On the input-end blank, enter the query state without writing. The query-answer step moves to yes or no; the next step emits the corresponding Boolean and halts.

On unary input of length $n$, this uses $n$ write steps, one end-detection step, one answering step, and one output step:

\[
n+3\le3(n+1).
\]

The first $n$ choice bits fill exactly cells $0,\ldots,n-1$; cell $n$ stays blank, so `queryString` is exactly the guessed word. Every word of length $n$ can be the prefix of a choice word of length $3(n+1)$. The remaining bits are ignored by the tail or absorbing halted state. Every branch halts, and an accepting branch exists exactly when the input belongs to the stated language. If the input is non-unary, every branch rejects at its first false symbol. At $n=0$, the unique guessed word is empty and the same three-step tail works.

The actual class definitions have independent polynomial exponent and multiplicative constant. Choosing exponent $1$ and multiplier $3$ supplies the required membership witness.

## Adversarial instantiations

| Test | Instantiation | Result |
|---|---|---|
| A1 | Deterministic horizon $t=0$, or empty nondeterministic choice word; let the oracles disagree on the empty word. | No consultation occurs. Both runs remain initial and the lists are empty. Locality is not accidentally claiming a first-step answer. |
| A2 | Well-formed machine with `q₀ = qQuery`, horizon $1$, and oracles disagreeing on the empty word. | Exactly one empty query is recorded. The runs go to distinct answer states, showing why agreement on length-zero strings is necessary. |
| A3 | Write one true bit and enter `qQuery` in the first transition; use horizon $2$. | The one-bit query is answered by the last transition and recorded at index $1$, with length $t-1$. With horizon $1$, it is not yet submitted. |
| A4 | Raw machine with all special states equal to `qQuery` and initially in that state. | It can submit the unchanged empty query on every step. The list has repetitions and length exactly $t$; all locality assertions still hold without `WellFormed`. |
| A5 | Nondeterministic query step with next choice bit false versus true. | The bit is consumed in either case but the same oracle answer is returned. No choice-bit shift occurs in the prefix horizon. |
| A6 | $B=\varnothing$, $B=\{\varepsilon\}$, and $B$ equal to all binary words. | The unary languages are respectively empty, ${\varepsilon\}$, and all true-only words. In the last case `[false]` is still rejected. |
| A7 | EXPCOM padding exponent $0$, using a one-step accepting machine and a machine that accepts only at step $2$. | The first triple belongs and the second does not, because the deadline is exactly $1$. |
| A8 | Empty outer word, malformed inner pair, or inner suffix containing a false bit instead of a unary padding word. | The defining existential fails. Empty code/input and a genuinely empty padding suffix remain valid when the two separators are present. |
| A9 | Stage $i=0$, fresh length $n_0=10$, budget $10^0+0=1$, and a nonaccepting bounded run. | The margin is $2^{\lfloor10/10\rfloor}=2>1$. A length-10 insertion must be protected despite its length exceeding the budget. The corrected cutoff $\max(10,1)=10$ does so. |
| A10 | An earlier stage inserts a word; a later stage's simulation accepts. | The later fresh length exceeds the earlier insertion's length, so declaring the later length empty never removes the earlier positive. |
| A11 | Enumerated machine loops forever, halts with `[]`, or halts with `[true,false]`. | All are nonaccepting at the budget and cause an unqueried insertion. The flip is against the exact `[true]` predicate, not an assumed Boolean decider. |
| A12 | A one-state candidate default and a representative with an arbitrary finite state type of size at least three. | The former violates well-formedness (finding 2). The latter relabels exactly, including at query transitions; no slowdown or oracle-dependent representative is needed. |
| A13 | The tagged effective code scheme $c_H$, with the one-step deadline and empty simulated input. | It embeds an arbitrarily hard decidable membership question into decoding, refuting the uniform EXP claim without any long simulated run. |
| A14 | Consecutive HALT bits $b(n)=1,b(n+1)=0$, and an odd rank with HALT bit $1$. | $T(n)=T(n+1)=n+1$, so monotonicity survives the downward bit change. At odd rank, the full equality comparison still recovers the HALT bit despite the binary carry. |

## Source comparison and declared deviations

[AB09] §3.4 defines the query/answer model and the relativized classes; Example 3.6$3$ gives the EXPCOM identities, and Theorem 3.7 supplies the two existential oracle conclusions. The packet's unary language and headline statements match those targets, subject to finding 1's coding issue. Exercise 3.5 asks only for existence of a non-time-constructible function; domination is a legitimate strengthening. The book also mentions exclusion of every oracle time bound $o(2^n)$ in the separation proof; the packet does not state that stronger result.

[BGS75] p. 432 explicitly clocks enumerated machines under every oracle. Lemma 1 and Theorems 1–2 concern the complete-language and equality constructions; §3, Theorem 3 uses fresh lengths and preserves earlier query answers. The packet's external budgets correctly replace the internal clocks for its diagonalization. BGS75's recursive-oracle strengthening is not asserted by the submitted existential statements. Its self-referential equality construction is properly treated as a fallback, not as the submitted EXPCOM proof.

Declared-deviation disposition:

| Pack item | Disposition |
|---|---|
| 1. EXPCOM layout, fixed code, inclusivity, totalization | Layout/inclusivity/totalization pass. Fixed-code reuse is the blocker; unary-tail lemma attribution is minor. |
| 2. Deterministic-only, clock-free recurrent enumeration | Correct statement and sufficient strength. Repair the default and make the repetition coordinate explicit. |
| 3. Stage packaging, larger fresh lengths, explicit acceptance predicate | Pass, including the corrected maximum cutoff and nonaccepting-run convention. |
| 4. Query lists, asymmetry, fixed ND word | Pass. Multiplicity and all-step bit consumption are handled correctly. |
| 5. Identity-domination and HALT witness | Pass; the witness is also nondecreasing. |
| 6. Deferred helper locations | No semantic defect. The ND invariant and oracle state transport can be proved locally and promoted later as declared. |
| 7. Sketch-level imports | No correctness defect. Full dependency/export verification is outside the supplied evidence. |

Primary texts consulted: [AB09 published-text copy, pp. 73–75](https://kubokovac.eu/zlozitost/arora.pdf), [AB09 Exercise 3.5, p. 77, alternate published-text copy](https://nzdr.ru/data/media/biblio/kolxoz/Cs/CsNp/Arora%20S.%2C%20Barak%20B.%20Computational%20complexity..%20A%20modern%20approach%20%28CUP%2C%202009%29%28ISBN%200521424267%29%28605s%29_CsNp_.pdf), and [BGS75 original scan](https://cse.ucdenver.edu/~cscialtman/complexity/Relativizations%20of%20the%20P=NP%20Question%20(Original).pdf). The AB09 comparisons used retrieved indexed passages: direct PDF fetches were unavailable. BGS75's relevant pages were accessible. No claim is made that a complete published-book PDF was downloaded.

The new-file source inventory and warning counts were checked directly. The full imported machine library, private chapter-2 enumerator proofs, parser implementation, and `timed_universal` were not independently reverified. No source files were modified and no Lean elaboration was run. These limitations do not affect the counterexample, which uses the explicit attached coding interface and the chosen-code definition.

## Notation glossary

| Notation | Meaning |
|---|---|
| $\varepsilon$, $\vert w\vert $, $1^n$, $0w$, $1w$ | Empty binary word, word length, $n$ true bits, and prepending a false or true tag. Numerals in these word expressions denote bits. |
| $\mathrm P^O,\mathrm{NP}^O$ | The packet's `POracle O` and `NPOracle O`. `EXP` and all Lean declaration names retain their packet meanings. |
| `EXPCOM[c]` | The packet's EXPCOM formula with scheme $c$ in place of `TimeHierarchy.code`; audit notation only. |
| $H,c_0,c_H,M_+,M_-,f$ | Auxiliary decidable language, base coding scheme, tagged scheme, one-step accepting/rejecting machines, and the displayed triple-encoding reduction. The second counterconstruction makes a separate choice of $H$. |
| $M_j,a_j,k_j$ | The machine, multiplicative constant, and exponent in the decidable diagonal language's enumeration. |
| $E_0,A$ | EXPCOM for the base scheme and the tagged join of $E_0$ with $H$. |
| $E(j),N_i,\mathrm{pair}(j,r)$ | Canonical-table enumeration, its recurrent version, and an injective bijective pairing of natural numbers. $r$ is the repetition coordinate. |
| $n_i,t_i,O_i,B$ | Fresh stage length, stage deadline $n_i^i+i$, finite set of prior positive insertions, and their final union. |
| $c,k,p(n)$ | A hypothetical decider's polynomial multiplier and exponent, and its polynomial step budget; these are separate parameters. |
| $x,z,\alpha,n'$ | Input or query words, code word, and the unary exponent in a parsed EXPCOM query, as specified locally. Other natural-number indices and word variables are locally quantified dummy variables. |
| $T,b,\mathrm{str},\mathrm{rank}$ | The non-time-constructible witness, its HALT bit, an effective enumeration of words, and its inverse. `HALT` uses the packet's fixed effective scheme. |
| $\mathrm{poly}(n)$ | Some fixed polynomial in $n$; its coefficients and degree do not depend on the input. |
```


## ===== audits/ch3-p31-resolutions.md =====

```
# Chapter 3, phase P3.1 (oracle machines and classes) — audit loop resolutions

**Gate: CLOSED (round 1, 2026-10-08).** One round: **PASS — 0 blockers,
0 majors, 2 minors, 4 notes** (`audits/ch3-p31-findings.md`, verbatim). All 19
definitions blind-restated clean; all 10 sorried statements independently
argued true as stated; all nine declared skeleton-time proofs approved at
their claimed scope; the bundle hash independently recomputed.

## Minors, swept in the closing commit and re-verified

| # | Sweep |
|---|---|
| 1 | `ClassOracle/Classes.lean`'s module docstring now writes Theorem 2.6 as `NP = ⋃ c, NTIME (fun n => n ^ c + 1)`, matching the actual `Complexity.NP_eq_iUnion_NTIME` (the auditor supplied a full refutation of the `+1`-less reading under the exact-budget conventions — maintainer-verified against the Lean statement before sweeping) |
| 2 | `POracle_eq_P_of_mem_P`'s sketch rewritten with the auditor's explicit ledger: at most `t = c·(n^k+1)` queries of length ≤ `t`; per-query positioning/prefix-copy/restore `O(t+1)` plus decider-and-cleanup `O(d·((t+1)^e+1))`; total degree `k·(1 + max 1 e)` (not `k·e + O(1)`); the virtual input carries the **extracted prefix only**, blanked beyond the first blank (the cell-`1` garbage instance); preservation/reset invariants named as fill obligations |

Re-verification: `Classes.lean` and `SATOracle.lean` re-elaborate with zero
errors; `ClassOracle` lint 0 FAIL / 0 WARN.

## Notes (no change; dispositions recorded)

* **Note 3** (fixed-oracle clocks): the per-oracle class definitions stand;
  the timeout-wrapper reconciliation with [BGS75]'s all-oracle convention is
  exactly what phase P3.2's extrinsic budgets implement, and its round must
  justify its own clock coverage — carried as a P3.2-gate obligation.
* **Note 4**: the `SATᶜ` fallback polarity is confirmed benign.
* **Note 5**: the nine skeleton-time proofs are statement-approved; no fresh
  kernel replay was claimed.
* **Note 6**: build freshness, axiom closure, and the `edea2663 = 2cf44f1d`
  byte identity remain maintainer attestations, as every round records.

## Gifts recorded for the fill briefs

* The round's own construction for `compl_mem_POracle` — the direct
  emission-negating transformer — is simpler than the sketched capture
  wrapper; fills may take it.
* The explicit workhorse construction (redirect emissions to the query tape,
  replace the halting transition by query entry, two-step answer tail),
  including the `f x = []` case with no rewind.

## Standing obligations out of this gate

1. The ten fills, scheduled with the chapter-3/4 fill epochs; the Ex 3.6(2)
   fill carries the finding-2 ledger verbatim.
2. The natural-home promotions flagged by P3.2's skeleton into this surface
   (oracle locality lemmas, `stepWith` oracle-independence, relabelling)
   remain **deferred until the live P3.2 gate closes** — no file under a
   running audit moves.
```


## ===== audits/evidence/ch3-p32-r2-repairs.diff =====

```
diff --git a/TCSlib/Complexity/Diagonalization/EXPCOM.lean b/TCSlib/Complexity/Diagonalization/EXPCOM.lean
index e5ff9d0a..c416c5e4 100644
--- a/TCSlib/Complexity/Diagonalization/EXPCOM.lean
+++ b/TCSlib/Complexity/Diagonalization/EXPCOM.lean
@@ -30,24 +30,44 @@ of [BGS75, Theorem 1] stays recorded there as the fallback).
   `Turing.pairEncode α (Turing.pairEncode x 1ⁿ)` — the universal machine's
   layout (code before payload, chapter-1 phase-3 audit, Argument B), nested
   right so each component is recovered by one aligned-pair parse.
-* **The code scheme is the campaign's fixed `Complexity.TimeHierarchy.code`**,
-  reused rather than re-chosen, so the timed universal machine
-  (`Turing.timed_universal`) and every encoding lemma apply verbatim.
+* **The code scheme is a uniformly-timed scheme, not the hierarchy's
+  arbitrary one** (round-1 blocker): `Turing.EffectiveMachineCode` bounds no
+  decoding time — `canonizerTime` is arbitrary, and the round-1 audit built
+  a permitted scheme embedding an arbitrarily hard decidable language into
+  `decode`, putting `EXPCOM` outside `EXP` and even separating its
+  relativized `P` from `NP`. `EXPCOM` queries carry **variable** codes, so
+  per-code constants (`∀ α, ∃ C` — `Turing.timed_universal`'s shape) cannot
+  pay for them. The new `Turing.UniformMachineCode` packages the scheme with
+  a simulator whose time is **one polynomial in the code, the input, and
+  the deadline jointly**; `EXPCOM` is defined over a scheme chosen from its
+  sorried existence (`Turing.exists_uniformMachineCode` — the
+  `TimeHierarchy.code` mirror, with the choice-over-a-sorried-existence
+  declared). The hierarchy's own `Complexity.TimeHierarchy.code` is
+  unchanged: fixed-code arguments never needed uniformity.
 * **"Outputs `1` within `2ⁿ` steps"** is
   `Turing.FinTM.ComputesInTime x [true] (2 ^ n)`: halting is absorbing, so the
   predicate is monotone in the budget and "within" is faithful.
 * **Totalization**: a string that does not parse as a triple is simply not in
   `EXPCOM` (the existential fails); on genuine triples the witnessing
-  decomposition is unique (`Turing.pairEncode_injective`,
-  `Turing.pairEncode_replicate_inj`), so the defining condition is
-  unambiguous.
+  decomposition is unique — `Turing.pairEncode_injective` applied twice,
+  then `List.length` on the equality of the replicated tails (round-1
+  finding 3 corrected the earlier `pairEncode_replicate_inj` citation, whose
+  unary component sits on the wrong side for this nesting) — so the defining
+  condition is unambiguous.
 
 ## Main definitions
 
-* `Complexity.EXPCOM` — the oracle language. [AB09, Example 3.6(3)]
+* `Turing.UniformMachineCode` — an effective scheme with a uniformly timed
+  bounded-acceptance simulator (round-1 repair).
+* `Complexity.expCode` — the chosen uniformly-timed scheme (noncomputable;
+  via the sorried existence).
+* `Complexity.EXPCOM` — the oracle language, over `expCode`.
+  [AB09, Example 3.6(3)]
 
 ## Main results (all sorried; phase-P3.2 statements)
 
+* `Turing.exists_uniformMachineCode` — a uniformly-timed scheme exists.
+
 * `Complexity.EXP_subset_POracle_EXPCOM` — one padded query decides any
   `EXP` language.
 * `Complexity.NPOracle_EXPCOM_subset_EXP` — the fill summit: deterministic
@@ -66,23 +86,82 @@ of [BGS75, Theorem 1] stays recorded there as the fallback).
   fallback oracle for the `A` half.)
 -/
 
+namespace Turing
+
+/-- An effective representation scheme together with a **uniformly timed
+bounded-acceptance simulator**: one machine and one degree such that, on
+`⟨⟨bits t, α⟩, x⟩`, the simulator decides whether the decoded machine outputs
+`[true]` on `x` within `t` steps, in time one polynomial in
+`|α| + |x| + t + 1` **jointly** — uniform in the code, which is exactly what
+`EXPCOM`'s variable-code queries need and what a bare
+`Turing.EffectiveMachineCode` (arbitrary `canonizerTime`) or the per-code
+`∀ α, ∃ C` of `Turing.timed_universal` cannot supply (round-1 blocker). -/
+structure UniformMachineCode extends EffectiveMachineCode where
+  /-- the uniformly timed bounded-acceptance simulator -/
+  simulator : FinTM Bool
+  /-- the simulator's single polynomial degree and coefficient -/
+  simDegree : ℕ
+  /-- on bounded acceptance, the simulator answers `[true]` within the
+  uniform polynomial budget -/
+  simulator_accepts : ∀ (α x : List Bool) (t : ℕ),
+    (decode α).toFinTM.ComputesInTime x [true] t →
+    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
+      (simDegree * (α.length + x.length + t + 1) ^ simDegree)
+  /-- otherwise it answers `[false]` within the same budget -/
+  simulator_rejects : ∀ (α x : List Bool) (t : ℕ),
+    ¬(decode α).toFinTM.ComputesInTime x [true] t →
+    simulator.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
+      (simDegree * (α.length + x.length + t + 1) ^ simDegree)
+
+/-- **A uniformly-timed scheme exists** (spec, fill pending — phase P3.2
+round 2): the chapter-1 concrete scheme, with its time analysis made uniform.
+
+**Proof sketch.** The concrete scheme behind
+`Turing.exists_effectiveMachineCode`: its parser and canonizer
+(`TCSlib.Complexity.TuringMachine.CodeParser`) run within a fixed polynomial
+of the code length — the received construction's ledgers are per-phase
+polynomial, only never previously assembled into one exported bound — and
+the interpreter architecture of `Turing.timed_universal` costs a fixed
+polynomial of the **table size** per simulated step plus a clocked startup;
+the table size is itself polynomial in the code length. Reassembling the
+two-clause timed interface with these ledgers made explicit gives one
+degree in `|α| + |x| + t + 1` jointly. Fill obligations, named: the parser
+and canonizer uniform ledgers; the per-step interpreter cost as a
+polynomial of the code length; the clocked two-clause assembly
+(`timed_universal`'s packaging with the quadratic clock absorbed into the
+joint polynomial); the final degree arithmetic. **Continuation budget
+certain** (a re-derivation of the chapter-1 universal's time analysis with
+the code-length dependence exported). -/
+theorem exists_uniformMachineCode : Nonempty UniformMachineCode := by
+  sorry
+
+end Turing
+
 namespace Complexity
 
 open Turing
 
+/-- The chosen uniformly-timed scheme for the `EXPCOM` cluster — the
+`Complexity.TimeHierarchy.code` pattern over the **sorried** existence
+`Turing.exists_uniformMachineCode` (declared: until that fill lands, this
+definition and its consumers carry `sorryAx` through the choice). -/
+noncomputable def expCode : UniformMachineCode :=
+  Classical.choice exists_uniformMachineCode
+
 /-- **The `EXPCOM` oracle** [AB09, Example 3.6(3)]: the language of triples
 `⟨M, x, 1ⁿ⟩` such that the machine `M` outputs `1` on `x` within `2ⁿ` steps —
-rendered with the campaign's fixed code scheme `Complexity.TimeHierarchy.code`
-and the code-first nesting `Turing.pairEncode α (Turing.pairEncode x 1ⁿ)`, with
-"outputs `1` within `2ⁿ` steps" as
-`Turing.FinTM.ComputesInTime x [true] (2 ^ n)` (monotone in the budget, since
-halting is absorbing). Strings that do not parse as such a triple are not in
-the language; on genuine triples the decomposition is unique
-(`Turing.pairEncode_injective`, `Turing.pairEncode_replicate_inj`). -/
+rendered over the uniformly-timed scheme `Complexity.expCode` (round-1
+repair — see the module docstring) and the code-first nesting
+`Turing.pairEncode α (Turing.pairEncode x 1ⁿ)`, with "outputs `1` within
+`2ⁿ` steps" as `Turing.FinTM.ComputesInTime x [true] (2 ^ n)` (monotone in
+the budget, since halting is absorbing). Strings that do not parse as such a
+triple are not in the language; on genuine triples the decomposition is
+unique (`Turing.pairEncode_injective` twice, then `List.length` on the
+replicated tails). -/
 def EXPCOM : Language Bool :=
   {z | ∃ (α x : List Bool) (n : ℕ),
     z = pairEncode α (pairEncode x (List.replicate n true)) ∧
-    ((TimeHierarchy.code).decode α).toFinTM.ComputesInTime x [true] (2 ^ n)}
+    (expCode.decode α).toFinTM.ComputesInTime x [true] (2 ^ n)}
 
 /-- **One padded query decides any `EXP` language**: `EXP ⊆ P^EXPCOM`.
 [AB09, Example 3.6(3), the first inclusion of the chain
@@ -92,8 +171,9 @@ def EXPCOM : Language Bool :=
 (`Complexity.EXP` unfolds to such data). Normal-form `M` to a one-work-tape
 binary machine (`Turing.FinTM.one_work_tape_binary`, quadratic slowdown) and
 relabel it to a coded machine `N` (`Turing.exists_codeTM`); put
-`α_L := TimeHierarchy.code.encode N`, recovered by
-`code.toMachineCode.decode_encode`. Choose the padding exponent
+`α_L := expCode.encode N`, recovered by
+`Turing.MachineCode.decode_encode` (a **fixed** code: this inclusion never
+needed uniformity, as the round-1 audit confirmed). Choose the padding exponent
 `Q n := C · (n + 1)^c` with `C` absorbing `a`, the square, and the `+1`
 normalizations, so that `N` outputs `[χ_L x]` within `2^(Q |x|)` steps on every
 `x`. The reduction is `f x := pairEncode α_L (pairEncode x 1^(Q |x|))` —
@@ -104,8 +184,8 @@ polynomial-time by the chapter-2 padding cluster: the constant prefix
 of `Complexity.PolyTimeComputable.pairEncode`. Membership: if `x ∈ L` then the
 witness `(α_L, x, Q |x|)` puts `f x ∈ EXPCOM`; conversely a witness for
 `f x ∈ EXPCOM` is forced to be exactly `(α_L, x, Q |x|)`
-(`Turing.pairEncode_injective` twice, `Turing.pairEncode_replicate_inj`), and
-output determinism (`Turing.FinTM.ComputesInTime.output_unique`) against `N`'s
+(`Turing.pairEncode_injective` twice, then `List.length` on the replicated
+tails), and output determinism (`Turing.FinTM.ComputesInTime.output_unique`) against `N`'s
 verdict `[χ_L x]` forces `x ∈ L`. Conclude with
 `Complexity.mem_POracle_of_polyTimeReducible`. -/
 theorem EXP_subset_POracle_EXPCOM : EXP ⊆ POracle EXPCOM := by
@@ -136,17 +216,19 @@ machine, on input `x` of length `n`:
    as `pairEncode α' (pairEncode x' 1^(n'))` by aligned two-bit parsing (the
    `Turing.pairDecode` layer; `TCSlib.Complexity.TuringMachine.CodeParser`
    machine precedent) — malformed strings answer "no" — and decide
-   `z ∈ EXPCOM` by running the timed universal machine
-   (`Turing.timed_universal` at the fixed scheme `TimeHierarchy.code`) on
-   `(α', x')` with deadline `2^(n')`: answer "yes" exactly on success with
-   simulated output `[true]` (report `true :: [true]`); the deadline-inclusive
-   timeout clause makes the answer the exact membership bit, with
-   parse-uniqueness (`Turing.pairEncode_injective`,
-   `Turing.pairEncode_replicate_inj`) identifying the witness decomposition.
+   `z ∈ EXPCOM` by running **`expCode.simulator`** on
+   `⟨⟨bits 2^(n'), α'⟩, x'⟩`: its two uniform clauses make the answer the
+   exact membership bit at cost `simDegree · (|α'| + |x'| + 2^(n') + 1) ^
+   simDegree` — **uniform in the query's code**, which is the entire round-1
+   repair (query codes vary with the branch; `Turing.timed_universal`'s
+   per-code constant cannot pay for them) — with parse-uniqueness
+   (`Turing.pairEncode_injective` twice, then `List.length` on the
+   replicated tails) identifying the witness decomposition.
 4. **Ledger.** Each branch submits queries of length at most the elapsed
    budget (`Turing.OracleTM.queryString_length_le` transferred along the
-   simulation invariant), so `n' ≤ p n` and one oracle call costs
-   `O((2^(p n) + 1)^2)` universal-machine steps; a round is `p n` simulated
+   simulation invariant), so `n' ≤ p n`, `|α'|, |x'| ≤ p n`, and one oracle call costs
+   `simDegree · (3 · p n + 2^(p n) + 1) ^ simDegree = 2^(O(p n))` simulator
+   steps; a round is `p n` simulated
    steps of which each costs at most one call: the total over `2^(p n)` rounds
    is `2^(O(p n) )·(2^(p n))^2 = 2^(O(n^k))`, inside `DTIME (2^(n^(k+1)))` by
    `Complexity.DTIME`'s constant absorption — so `L ∈ EXP`.
diff --git a/TCSlib/Complexity/Diagonalization/Relativization.lean b/TCSlib/Complexity/Diagonalization/Relativization.lean
index cb454699..3e12c6cf 100644
--- a/TCSlib/Complexity/Diagonalization/Relativization.lean
+++ b/TCSlib/Complexity/Diagonalization/Relativization.lean
@@ -129,10 +129,15 @@ of [BGS75]'s machine/clock-exponent pairing).
 **Proof sketch.** For fixed tape count `k` and state count `m + 1`, the oracle
 machines over `Bool` with state space `Fin (m + 1)` form a finite type (the
 transition table is a function between finite types), so `Fintype.equivFin`
-enumerates the well-formed ones; a pairing of `ℕ` with `ℕ × ℕ × ℕ` (tape
-count, state count, table rank — with infinite fibers, supplying the
-recurrence and the unbounded clock exponents) produces the family, totalized
-by a fixed well-formed one-state default at indices whose rank overflows.
+enumerates the well-formed ones; a pairing of `ℕ` with `ℕ × ℕ × ℕ × ℕ` —
+tape count, state count, table rank, and an explicit **repetition
+coordinate** (a bijective pairing alone has singleton fibers; the fourth
+coordinate supplies the recurrence and the unbounded clock exponents —
+round-1 finding 2) — produces the family, totalized by a fixed well-formed
+**three-state** default at indices whose rank overflows (well-formedness
+demands three pairwise-distinct special states, so no one-state machine
+qualifies — round-1 finding 2; equivalently, embed a one-state plain
+machine by `Turing.FinTM.toFinOracleTM`, which adjoins them).
 Every bundled `M : Turing.FinOracleTM Bool` relabels its state type along
 `Fintype.equivFin` to some `Fin (m + 1)`, preserving runs
 configuration-by-configuration under every oracle — the oracle transport of
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
* **The code scheme is a uniformly-timed scheme, not the hierarchy's
  arbitrary one** (round-1 blocker): `Turing.EffectiveMachineCode` bounds no
  decoding time — `canonizerTime` is arbitrary, and the round-1 audit built
  a permitted scheme embedding an arbitrarily hard decidable language into
  `decode`, putting `EXPCOM` outside `EXP` and even separating its
  relativized `P` from `NP`. `EXPCOM` queries carry **variable** codes, so
  per-code constants (`∀ α, ∃ C` — `Turing.timed_universal`'s shape) cannot
  pay for them. The new `Turing.UniformMachineCode` packages the scheme with
  a simulator whose time is **one polynomial in the code, the input, and
  the deadline jointly**; `EXPCOM` is defined over a scheme chosen from its
  sorried existence (`Turing.exists_uniformMachineCode` — the
  `TimeHierarchy.code` mirror, with the choice-over-a-sorried-existence
  declared). The hierarchy's own `Complexity.TimeHierarchy.code` is
  unchanged: fixed-code arguments never needed uniformity.
* **"Outputs `1` within `2ⁿ` steps"** is
  `Turing.FinTM.ComputesInTime x [true] (2 ^ n)`: halting is absorbing, so the
  predicate is monotone in the budget and "within" is faithful.
* **Totalization**: a string that does not parse as a triple is simply not in
  `EXPCOM` (the existential fails); on genuine triples the witnessing
  decomposition is unique — `Turing.pairEncode_injective` applied twice,
  then `List.length` on the equality of the replicated tails (round-1
  finding 3 corrected the earlier `pairEncode_replicate_inj` citation, whose
  unary component sits on the wrong side for this nesting) — so the defining
  condition is unambiguous.

## Main definitions

* `Turing.UniformMachineCode` — an effective scheme with a uniformly timed
  bounded-acceptance simulator (round-1 repair).
* `Complexity.expCode` — the chosen uniformly-timed scheme (noncomputable;
  via the sorried existence).
* `Complexity.EXPCOM` — the oracle language, over `expCode`.
  [AB09, Example 3.6(3)]

## Main results (all sorried; phase-P3.2 statements)

* `Turing.exists_uniformMachineCode` — a uniformly-timed scheme exists.

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

namespace Turing

/-- An effective representation scheme together with a **uniformly timed
bounded-acceptance simulator**: one machine and one degree such that, on
`⟨⟨bits t, α⟩, x⟩`, the simulator decides whether the decoded machine outputs
`[true]` on `x` within `t` steps, in time one polynomial in
`|α| + |x| + t + 1` **jointly** — uniform in the code, which is exactly what
`EXPCOM`'s variable-code queries need and what a bare
`Turing.EffectiveMachineCode` (arbitrary `canonizerTime`) or the per-code
`∀ α, ∃ C` of `Turing.timed_universal` cannot supply (round-1 blocker). -/
structure UniformMachineCode extends EffectiveMachineCode where
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

/-- **A uniformly-timed scheme exists** (spec, fill pending — phase P3.2
round 2): the chapter-1 concrete scheme, with its time analysis made uniform.

**Proof sketch.** The concrete scheme behind
`Turing.exists_effectiveMachineCode`: its parser and canonizer
(`TCSlib.Complexity.TuringMachine.CodeParser`) run within a fixed polynomial
of the code length — the received construction's ledgers are per-phase
polynomial, only never previously assembled into one exported bound — and
the interpreter architecture of `Turing.timed_universal` costs a fixed
polynomial of the **table size** per simulated step plus a clocked startup;
the table size is itself polynomial in the code length. Reassembling the
two-clause timed interface with these ledgers made explicit gives one
degree in `|α| + |x| + t + 1` jointly. Fill obligations, named: the parser
and canonizer uniform ledgers; the per-step interpreter cost as a
polynomial of the code length; the clocked two-clause assembly
(`timed_universal`'s packaging with the quadratic clock absorbed into the
joint polynomial); the final degree arithmetic. **Continuation budget
certain** (a re-derivation of the chapter-1 universal's time analysis with
the code-length dependence exported). -/
theorem exists_uniformMachineCode : Nonempty UniformMachineCode := by
  sorry

end Turing

namespace Complexity

open Turing

/-- The chosen uniformly-timed scheme for the `EXPCOM` cluster — the
`Complexity.TimeHierarchy.code` pattern over the **sorried** existence
`Turing.exists_uniformMachineCode` (declared: until that fill lands, this
definition and its consumers carry `sorryAx` through the choice). -/
noncomputable def expCode : UniformMachineCode :=
  Classical.choice exists_uniformMachineCode

/-- **The `EXPCOM` oracle** [AB09, Example 3.6(3)]: the language of triples
`⟨M, x, 1ⁿ⟩` such that the machine `M` outputs `1` on `x` within `2ⁿ` steps —
rendered over the uniformly-timed scheme `Complexity.expCode` (round-1
repair — see the module docstring) and the code-first nesting
`Turing.pairEncode α (Turing.pairEncode x 1ⁿ)`, with "outputs `1` within
`2ⁿ` steps" as `Turing.FinTM.ComputesInTime x [true] (2 ^ n)` (monotone in
the budget, since halting is absorbing). Strings that do not parse as such a
triple are not in the language; on genuine triples the decomposition is
unique (`Turing.pairEncode_injective` twice, then `List.length` on the
replicated tails). -/
def EXPCOM : Language Bool :=
  {z | ∃ (α x : List Bool) (n : ℕ),
    z = pairEncode α (pairEncode x (List.replicate n true)) ∧
    (expCode.decode α).toFinTM.ComputesInTime x [true] (2 ^ n)}

/-- **One padded query decides any `EXP` language**: `EXP ⊆ P^EXPCOM`.
[AB09, Example 3.6(3), the first inclusion of the chain
`EXP ⊆ P^EXPCOM ⊆ NP^EXPCOM ⊆ EXP`]

**Proof sketch.** Let `L ∈ EXP`, say decided by `M` within `a · 2^(n^c)`
(`Complexity.EXP` unfolds to such data). Normal-form `M` to a one-work-tape
binary machine (`Turing.FinTM.one_work_tape_binary`, quadratic slowdown) and
relabel it to a coded machine `N` (`Turing.exists_codeTM`); put
`α_L := expCode.encode N`, recovered by
`Turing.MachineCode.decode_encode` (a **fixed** code: this inclusion never
needed uniformity, as the round-1 audit confirmed). Choose the padding exponent
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
(`Turing.pairEncode_injective` twice, then `List.length` on the replicated
tails), and output determinism (`Turing.FinTM.ComputesInTime.output_unique`) against `N`'s
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
   `z ∈ EXPCOM` by running **`expCode.simulator`** on
   `⟨⟨bits 2^(n'), α'⟩, x'⟩`: its two uniform clauses make the answer the
   exact membership bit at cost `simDegree · (|α'| + |x'| + 2^(n') + 1) ^
   simDegree` — **uniform in the query's code**, which is the entire round-1
   repair (query codes vary with the branch; `Turing.timed_universal`'s
   per-code constant cannot pay for them) — with parse-uniqueness
   (`Turing.pairEncode_injective` twice, then `List.length` on the
   replicated tails) identifying the witness decomposition.
4. **Ledger.** Each branch submits queries of length at most the elapsed
   budget (`Turing.OracleTM.queryString_length_le` transferred along the
   simulation invariant), so `n' ≤ p n`, `|α'|, |x'| ≤ p n`, and one oracle call costs
   `simDegree · (3 · p n + 2^(p n) + 1) ^ simDegree = 2^(O(p n))` simulator
   steps; a round is `p n` simulated
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
enumerates the well-formed ones; a pairing of `ℕ` with `ℕ × ℕ × ℕ × ℕ` —
tape count, state count, table rank, and an explicit **repetition
coordinate** (a bijective pairing alone has singleton fibers; the fourth
coordinate supplies the recurrence and the unbounded clock exponents —
round-1 finding 2) — produces the family, totalized by a fixed well-formed
**three-state** default at indices whose rank overflows (well-formedness
demands three pairwise-distinct special states, so no one-state machine
qualifies — round-1 finding 2; equivalently, embed a one-state plain
machine by `Turing.FinTM.toFinOracleTM`, which adjoins them).
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
  `NP = ⋃ c, NTIME (fun n => n ^ c + 1)` is Theorem 2.6 (the `+ 1` is load-bearing
  under the exact-budget conventions — P3.1 round 1, finding 1); but
  [AB09, Definition 3.5] *defines*
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
on the current query string. (i) At each query the host copies the query
tape's **extracted prefix only** — cell `0` up to the first blank — onto a
clean virtual-input region, blanks beyond it (garbage past the first blank or
at negative cells must not reach `D`: the round-1 audit's cell-`1` instance),
runs `D` there with output captured (W1) so the host stays silent, clears
`D`'s scratch, restores the suspended heads, and resumes in the answer state;
(ii) **the ledger, explicitly** (round-1 audit, finding 2): with oracle-time
budget `t = c·(n^k + 1)` there are at most `t` queries, each of length at most
`t` (`Turing.OracleTM.queryString_length_le`); positioning, prefix copy and
restoration cost `O(t + 1)` per query and `D`'s run plus cleanup
`O(d·((t+1)^e + 1))`, so the total is
`O(t + t·(t + 1 + d·((t+1)^e + 1))) = O((t+1)^(1+max 1 e)) =
O((n+1)^(k·(1+max 1 e)))` — the exponent depends on `k` and `e` jointly,
not `k·e + O(1)`; (iii) non-query steps are lockstep
(`Turing.OracleTM.step_eq_of_ne_qQuery`), and the preservation/reset
invariants (suspended tapes untouched, scratch cleared, fixed windows) are
named fill obligations. The composite bound sits inside `P`'s `⋃ c` by the
absorption `(n+1)^c ≤ 2^c·(n^c + 1)`. -/
theorem POracle_eq_P_of_mem_P {O : Language Bool} (h : O ∈ P) : POracle O = P := by
  sorry

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


## ===== audits/logs/ch3-p32-r2-sweep.log =====

```
P3.2_R2 GATE SWEEP at commit 9a92fa1aeb377d568972e42229979cf81562ba41 (9a92fa1a), branch complexity/arora-barak-ch3-4, started 2026-10-08 23:41:03
== TCSlib/Complexity/TuringMachine/OracleAgreement
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:109:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:132:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:146:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:158:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:199:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:217:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/OracleAgreement.lean:240:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/Diagonalization/EXPCOM
TCSlib/Complexity/Diagonalization/EXPCOM.lean:135:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/EXPCOM.lean:191:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/EXPCOM.lean:244:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/EXPCOM.lean:252:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/EXPCOM.lean:260:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/EXPCOM.lean:269:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/Diagonalization/Relativization
TCSlib/Complexity/Diagonalization/Relativization.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/Relativization.lean:153:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/Relativization.lean:214:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/Relativization.lean:227:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/Diagonalization/NotTimeConstructible
TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean:89:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/Diagonalization
P3.2_R2_SWEEP_DONE
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
