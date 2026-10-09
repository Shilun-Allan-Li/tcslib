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

## ===== briefs/retrofit-rb1.md =====

```
# Chapter-1/2 retrofit — Epoch R1, Batch RB1: dead code and the `emit_run` citation (`Build/Loop.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/retrofit-rb1`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `ff012d28ca3131452161669e1d7efe389b75ba2e`), and never
  rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `retrofit-rb1.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.
- Integration note (no action for you): the maintainer integrates retrofit
  deliveries on a side branch and opens a PR; this changes nothing about
  the delivery format above.

## What this is — read carefully, it differs from a fill batch

This is a **retrofit batch**: you are editing a fully proved, zero-sorry
file. The file must have **zero `sorry` and zero `error:` before and after
every commit you make**. There are no admissions to fill and none may be
introduced — a partial delivery means fewer tasks completed, never a
`sorry`. The authoritative task list below is extracted from the
commissioned inventory `audits/retrofit-inventory/loop.md` (in the repo;
read it for full context) and is **embedded here verbatim as the binding
contract**.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/TuringMachine/Build/Loop.lean` (5,713 lines, 8 public
declarations, 214 privates, 0 sorries).

**Task 1 — delete the 8 dead private declarations** (commit 1):

| Declaration | Defined at (line, at the recorded base) |
|---|---|
| `loop_silent_prefix` | 193 |
| `loopDebitTM` | 443 |
| `loopDebitCfg` | 459 |
| `loopBorrow_step` | 466 |
| `loopBorrow_run` | 492 |
| `loopBorrow_rewind` | 517 |
| `loopBorrow_correct` | 551 |
| `loopBody_capture` | 697 |

Inventory evidence (binding): the six `loopDebit*`/`loopBorrow*` members
(the standalone one-tape debit machine, lines 439–563 — its own docstring
says it "privately re-derives the counter template") refer only to each
other; `loop_silent_prefix` and `loopBody_capture` have no referrers at
all; the host performs its borrow itself (`loopHost_borrow*`). Delete each
declaration together with its docstring. **Also fix the historical
docstring sentence at line 2205** that mentions `loopBorrow_correct` —
rewrite that one sentence so it no longer references a deleted name;
change nothing else in that docstring.

**Deletion protocol**: the compile is the deadness proof. If removing any
of the eight breaks the check, **restore that declaration, record the
escalation in `REPORT.md` (which referencer the inventory missed), and
continue with the rest** — never "fix" a breakage by editing other code.

**Task 2 — replace the H4 family with the now-proved public lemma**
(commit 2). The three privates

| Declaration | Line |
|---|---|
| `emLoopForwardCfg` | 5185 |
| `emLoop_forward_apply` | 5192 |
| `emLoop_forward_run` | 5210 |

(lines 5183–5240, ≈56 lines) re-derive a forwarding lockstep; the
docstring at 5206 says it was "proved locally so this batch does not
depend on the concurrent `Turing.emit_run` admission". That admission is
gone: **`Turing.emit_run` (`Build/Wrappers.lean:273`) is proved** (the
file is zero-sorry). Replace the family with a derivation from the public
`Turing.emit_run` plus `leftCfg_run` (`Simulation.lean`). The inventory's
verified glue sketch (binding as the proof plan; adapt as the kernel
requires):

> a padded source `P.tr = leftAction 1 id (loopBodySource.tr …)`;
> `emitAction ∘ leftAction 1 id = leftAction 1 id ∘ emitAction` (closes by
> `simp` with `Option.map_id`); one `Cfg.ext` showing
> `emitCfg ∘ leftCfg = leftCfg ∘ emitCfg`; the liveness guard comes from
> `leftCfg_run`. About 15–25 lines replacing 56.

Update the sole consumer `emLoopHost_body_forward` (line 5275) to cite the
replacement (ideally it becomes a direct `emit_run` citation). If the
replacement does not land within budget, deliver Task 1 alone and record
the frontier — Task 1 is independent.

## Binding ground rules

1. **Public-surface freeze.** The 8 public declarations (`Turing.stateWord`,
   `Turing.loop_run`, `Turing.FinTM.exists_loopCfgTM`, `exists_loopTM`,
   `exists_loopFindTM`, `exists_emitLoopTM`, `exists_installCallTM`,
   `exists_emitCallTM`) stay **byte-identical** — signatures, statements,
   docstrings, and proof bodies. Only the privates named above change.
2. **No new private declarations** except what Task 2's replacement
   strictly needs (list every one in `REPORT.md`), and **zero new copies
   of existing proved material** — `policy.md` **Duplication** is binding:
   your `REPORT.md` must contain a duplication-ledger line (expected:
   "new copies: none").
3. **No renames, no re-signatures, no import changes** (`emit_run` and
   `leftCfg_run` are already in the import closure via Wrappers and
   Composition/Simulation).
4. Escalation on anything unprovable or unexpectedly live: stop that task,
   record the obstruction, deliver what stands.
5. Docstrings stay except the two named edits (line 2205; H4's removal).

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules), then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Catalog`.
- Iterate on your file per edit:
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Loop`.
- Final, in order: your file, then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Catalog`
  (the big direct importer), then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine`
  (the facade) — each with **zero `error:` lines and zero `sorry`
  warnings**, fresh `.olean`s.
- **Axiom prints**: `#print axioms` for all 8 public declarations on the
  final fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` and unchanged from the base;
  no `sorryAx`.
- Style lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  — 0 FAIL (the pre-existing size WARNs remain).

## REPORT.md checklist

- [ ] Base commit hash; working branch name.
- [ ] Deletions: all 8 (or the escalated subset, each with its found
      referencer); the line-2205 docstring sentence as rewritten.
- [ ] Task 2: the replacement derivation (new private helpers listed, with
      roles), `emLoopHost_body_forward`'s new form, net line delta — or
      the recorded frontier if not attempted/landed.
- [ ] Duplication ledger: "new copies: none" (or the disclosure, which
      requires maintainer approval before integration).
- [ ] Line count before/after; expected ≈ 5,513–5,523 after both tasks.
- [ ] Final sweep log tail (Loop + Catalog + facade, 0 errors / 0 sorries)
      + 8 axiom prints.
- [ ] Diff touches only `Build/Loop.lean`.

## Known pitfalls at this pin (hard-won)

- `Function.update_of_ne` (not `update_noteq`); after
  `cases hs : cfg.state`, `dsimp only` before rewriting; avoid bare `simp`
  with folded forms; `omega` needs beta-reduced goals.
- `Cfg` equality: `cases`-and-`rfl` or field congruence; beware eta.
- `emit_run`'s hypothesis is an *agreement* form (`hagree`-style): any
  host whose embedded actions are the emit-wrapped actions follows the
  trajectory — instantiate it at the padded source, do not specialize it
  away.
- Deleting a declaration with a preceding `/-- … -/` docstring: remove the
  docstring too, or the orphaned docstring attaches to the next
  declaration and changes its (frozen) text.
```

## ===== briefs/retrofit-rb2.md =====

```
# Chapter-1/2 retrofit — Epoch R1, Batch RB2: the dead emitter batch, Encoding swaps, and the splitSolve subsumption (`Build/Primitives.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/retrofit-rb2`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `ff012d28ca3131452161669e1d7efe389b75ba2e`), and never
  rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `retrofit-rb2.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.
- Integration note (no action for you): the maintainer integrates retrofit
  deliveries on a side branch and opens a PR; this changes nothing about
  the delivery format above.

## What this is — read carefully, it differs from a fill batch

This is a **retrofit batch** on a fully proved file: **zero `sorry` and
zero `error:` before and after every commit**. No admissions exist and
none may be introduced — a partial delivery means fewer tasks completed,
never a `sorry`. The task list is extracted from the commissioned
inventory `audits/retrofit-inventory/primitives.md` (read it for full
context) and embedded here verbatim as the binding contract.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/TuringMachine/Build/Primitives.lean` (7,636 lines,
18 public declarations, 318 privates, 0 sorries).

**Task 1 — delete the 62 dead private declarations** (commit 1). The
superseded earlier emitter batch (59) plus three split-search orphans.
Complete list (binding; delete each with its docstring):

- *F24a eval (6):* `emitterIdleTM`, `emitterEvalTM`, `emitterEvalCfg`,
  `emitter_eval_run`, `emitter_eval_initial`, `emitter_eval_first`.
- *F24b clear (13):* `emitterInterval`, `emitterCleared`,
  `emitter_cleared_step`, `emitterClearTM`, `emitterClearCfg`,
  `emitter_clear_left`, `emitter_cleared_zero`, `emitter_cleared_all`,
  `emitter_clear_scan`, `emitter_origin_erase`, `emitter_clear_origin`,
  `emitter_clear_run`, `emitter_clear_first`.
- *F24c track (18):* `emitterSpan`, `emitter_span_extend`, `emitterSlots`,
  `emitterTrackTM`, `emitterTrackCfg`, `emitterTrackMid`,
  `emitter_track_action`, `emitter_track_stamp`, `emitterLo`, `emitterHi`,
  `emitter_track_extent`, `emitter_track_support`, `emitter_span_zero`,
  `emitter_track_initial`, `emitter_track_run`, `emitter_track_computes`,
  `emitter_span_interval`, `emitter_track_clearable`.
- *F24d bank (11):* `emitterBankSymbols`, `emitterBankPart`,
  `emitterBankTM`, `emitterBankCfg`, `emitterBank_part`,
  `emitterBank_step`, `emitterBank_run`, `emitterClear_fixed`,
  `emitterBank_clear`, `emitterBank_fixed`, `emitterBank_first`.
- *F24e right (9):* `emitterRightTM`, `emitterRightCfg`,
  `emitter_right_step`, `emitter_right_run`, `emitterRightScan`,
  `emitter_right_scan`, `emitter_right_finish`, `emitter_right_endpoint`,
  `emitter_right_computes`.
- *F24f eval closers (2):* `emitter_prepared_eval_first`,
  `emitter_width_eval_first`.
- *Split orphans (3):* `splitFind_none`, `splitCount_firstHalt`,
  `splitPrepare_first`.

Inventory evidence (binding): none of the 62 is referenced from outside
the set; the only external mentions are docstrings (`Embed.lean` and
`CookLevin/Hardness.lean` — those files are NOT yours to touch and their
docstring mentions are harmless history). **Deletion protocol**: the
compile is the deadness proof. If removing any one breaks the check,
restore it, record the escalation (the found referencer) in `REPORT.md`,
and continue with the rest.

**Task 2 — the two Encoding swaps** (commit 2). Two privates are exact
duplicates of public lemmas already inside this file's import closure:

| Delete | Re-point its uses to |
|---|---|
| `catalogPair_inverse` | `Turing.eq_pairEncode_of_pairDecode` (`Encoding.lean:231`) |
| `catalogPair_length` | `Turing.length_pairEncode` (`Encoding.lean:192`) |

**Task 3 — comment-only cleanups** (same commit as Task 2): the module
docstring block at **L67–110** carries a stale "admitted" status (the file
is zero-sorry); the section blocks at **L4419–4439** and **L5956–5959**
describe the now-deleted families. Rewrite each minimally to the current
truth; touch no other comment.

**Task 4 (OPTIONAL STRETCH — attempt only after Tasks 1–3 are delivered-
ready; a delivery without it is complete)** — the splitSolve subsumption
(commit 3). `computesFunInTime_splitSolve` (line 4393) follows from
`computesFunInTime_splitSolveWith` (line 7399) plus
`computesFunInTime_polyBits`, because `solveSplitWith (fun i => C*(i+1)^e)`
unfolds to `solveSplit C e` **by definition** (`Convention.lean:125-133`).
The only mathematical work is the bound
`c*(n+1)*(b*(n+2)^(e+1)+n+2) ≤ K*(n+1)^(e+2)`. Rewrite the **proof body
only** of `computesFunInTime_splitSolve` (its statement, docstring, and
signature stay byte-identical — this is the single sanctioned public-body
change of this batch), then delete every private this frees and that the
compile confirms dead: the expected set is families F16–F18, F20, F22 and
parts of F13 of the inventory (≈35 further declarations beyond the three
orphans of Task 1, ≈870 lines) — enumerate the actual deleted set in
`REPORT.md`.

**Explicitly OUT OF SCOPE (do not touch, recorded decision):** the
`emitterCompare*` family (F25a) and the `emitterP2Erase*` family (F27a) —
their catalog replacement is deferred to the 12.2c window because it
requires a `Build/Catalog` import this file must not gain now. **Do not
add any import**, in particular not `Build.Catalog`.

## Binding ground rules

1. **Public-surface freeze.** All 18 public `computesFunInTime_*` rows stay
   byte-identical in signature, statement, and docstring; proof bodies stay
   byte-identical except `computesFunInTime_splitSolve` under Task 4.
2. **No new private declarations** except what Task 4 strictly needs (list
   each), and **zero new copies of existing proved material** —
   `policy.md` **Duplication** is binding; `REPORT.md` carries a
   duplication-ledger line (expected: "new copies: none").
3. **No renames, no re-signatures, no import changes.**
4. Escalation on anything unexpectedly live or unprovable: stop that item,
   record it, deliver what stands.
5. Docstrings stay except the named Task 3 blocks and deleted
   declarations' own docstrings.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules).
- Iterate on your file per edit:
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Primitives`.
- Final, in order: your file, then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine` (the
  facade) — zero `error:` lines, zero `sorry` warnings, fresh `.olean`s.
- **Axiom prints**: `#print axioms` for all 18 public rows on the final
  fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` and unchanged; no `sorryAx`.
- Style lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  — 0 FAIL.

## REPORT.md checklist

- [ ] Base commit hash; working branch name.
- [ ] Task 1: deletions confirmed 62/62 (or the escalated subset with
      referencer evidence).
- [ ] Task 2: both swaps with the re-pointed use sites listed.
- [ ] Task 3: the three comment blocks as rewritten.
- [ ] Task 4: done/not attempted/frontier; if done — the new proof route,
      the bound's constant `K`, the enumerated freed-and-deleted set, and
      confirmation the statement is byte-identical.
- [ ] Duplication ledger: "new copies: none".
- [ ] Line count before/after (expected ≈ 6,350 after Tasks 1–3; ≈ 5,480
      with Task 4).
- [ ] Final sweep log tail + 18 axiom prints.
- [ ] Diff touches only `Build/Primitives.lean`.

## Known pitfalls at this pin (hard-won)

- Deleting a declaration with a preceding `/-- … -/` docstring: remove the
  docstring too, or it attaches to the next declaration and silently
  changes frozen text.
- The Task 4 unfolding is definitional at `Convention.lean:125-133` —
  `show`/`change` to the `solveSplitWith` form rather than `simp`-unfolding
  `solveSplit` (bare `simp` with folded forms thrashes at this pin).
- `omega` needs beta-reduced, non-`Fin`-projection goals; for the Task 4
  bound prefer `calc` with `Nat.pow_le_pow_left/right` and explicit
  monotonicity over `nlinarith`.
- `Function.update_of_ne` (not `update_noteq`).
- The six private `instance`s in this file are live through `FinTM`'s
  `[Fintype]`/`[DecidableEq]` fields despite having no textual references
  — they are NOT dead; none is on the deletion list, leave them.
```

## ===== briefs/retrofit-rb3.md =====

```
# Chapter-1/2 retrofit — Epoch R1, Batch RB3: dead clusters, three strict swaps, and the `clFresh` seam citation (`CookLevin/Hardness.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/retrofit-rb3`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `ff012d28ca3131452161669e1d7efe389b75ba2e`), and never
  rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `retrofit-rb3.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.
- Integration note (no action for you): the maintainer integrates retrofit
  deliveries on a side branch and opens a PR; this changes nothing about
  the delivery format above.

## What this is — read carefully, it differs from a fill batch

This is a **retrofit batch** on the campaign's largest fully proved file:
**zero `sorry` and zero `error:` before and after every commit**. No
admissions exist and none may be introduced — a partial delivery means
fewer tasks completed, never a `sorry`. The task list is extracted from
the commissioned inventory `audits/retrofit-inventory/hardness.md` (read
it for full context) and embedded here verbatim as the binding contract.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/CookLevin/Hardness.lean` (8,904 lines; public surface =
`NPHard.polyTimeReducible`, `SAT_NPHard`, `SAT_NPComplete`, `SAT3_NPHard`,
`SAT3_NPComplete`; 553 privates, 0 sorries).

**Task 1 — delete the 6 dead private declarations** (commit 1):

| Declaration | Line | Inventory evidence |
|---|---|---|
| `clRefClockTM` | 899 | referenced only inside `clRefClockCfg` |
| `clRefClockCfg` | 914 | no referencers |
| `clCount_first` | 1151 | only inside `clRefCount_first` |
| `clRefCountTM` | 1188 | only inside `clRefCount_first` |
| `clRefCount_first` | 1205 | no code referencers; one docstring mention at 1242 |
| `clReadFields` | 3133 | only its own recursion |

Three closed clusters; nothing any public theorem reaches cites any of
them. **Also fix the `clCount_width` docstring at lines 1241–1243**, which
mentions `clRefCount_first` — rewrite that sentence to drop the deleted
name; change nothing else. **Deletion protocol**: the compile is the
deadness proof; if a removal breaks the check, restore it, record the
escalation (the found referencer) in `REPORT.md`, and continue.

**Task 2 — three strict swaps** (commit 2). Each private duplicates a
public fact already in this file's import closure; delete the private and
re-point its uses:

| Delete | Replacement | Use sites |
|---|---|---|
| `clCompute_comp` (4887–4901) | `FinTM.bufferedCompTM_computesInTime` (`Composition.lean:355`) + `output_length_le` + monotonicity | 5160, 5314 |
| `clBuffer_append_bit` (1711) | `(FinTM.bufferTape_append w b).symm` | 1757 |
| `clA5_pt_unaryLength` (6896) | `clNative_fill true` (this file's own private wrapper, line 693 region) | 10 sites — enumerate them in `REPORT.md` |

**Task 3 — the `clFresh` seam citation** (commit 3). The family `clFreshTM`
(3513), `clFresh_run`, `clFresh_idle`, `clFresh_first` (through 3584)
hand-builds exactly the §12 seam composite. Inventory finding (binding as
the proof plan):

> `clFreshTM` already has `seamCompTM`'s shape, up to unfolding: state
> `Fin 3 ⊕ clReadTM.State`, dispatch
> `FinTM.controlAction 0 (some (.inr entry))`, left branch
> `Action.mapState Sum.inl`. Hardness's `.mapState Sum.inl` /
> `.mapState Sum.inr` seams match the R2′ `seamCompTM_run_ofCfg` statement
> exactly. The stream head is displaced, which the general-configuration
> variant handles. No glue is needed. `clFresh_idle` / `clFresh_first`
> stay, because `clRead_run` has no first-return cut.

Redefine `clFreshTM` as the `seamCompTM` instance and re-prove
`clFresh_run` by citing `seamCompTM_run_ofCfg`
(`Build/Seam.lean` — the general-configuration trio). This **requires one
new import**: add
`import TCSlib.Complexity.TuringMachine.Build.Seam` to the header — this
is the single sanctioned import change of this batch, flag it prominently
in `REPORT.md` (Hardness becomes the first §12-layer consumer outside
`Build/`). If the citation does not land cleanly (e.g. a state-type
mismatch the inventory missed), escalate and deliver Tasks 1–2 — they are
independent.

## Binding ground rules

1. **Public-surface freeze.** The five public theorems stay byte-identical
   — signatures, statements, docstrings, and proof bodies.
2. **No new private declarations** except what Task 3 strictly needs (list
   each), and **zero new copies of existing proved material** —
   `policy.md` **Duplication** is binding; `REPORT.md` carries a
   duplication-ledger line (expected: "new copies: none").
3. **No renames, no re-signatures**; the one sanctioned import change is
   Task 3's `Build.Seam`.
4. Escalation on anything unexpectedly live or unprovable: stop that item,
   record it, deliver what stands.
5. Docstrings stay except the named 1241–1243 edit and deleted
   declarations' own docstrings.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules — Hardness is module 51; everything before it must be fresh).
  Then `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Seam`
  (Task 3's import; it may not be in the order list — check it before
  first use).
- Iterate on your file per edit:
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/CookLevin/Hardness`.
- Final, in order: your file, then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/CookLevin` (the
  facade) — zero `error:` lines, zero `sorry` warnings, fresh `.olean`s.
- **Axiom prints**: `#print axioms` for the five public theorems on the
  final fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` and unchanged; no `sorryAx`.
- Style lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/CookLevin`
  — 0 FAIL (the file-size WARN remains and is justified by the recorded
  retrofit/12.2c program).

## REPORT.md checklist

- [ ] Base commit hash; working branch name.
- [ ] Task 1: 6/6 deletions (or the escalated subset with referencer
      evidence); the 1241–1243 docstring as rewritten.
- [ ] Task 2: the three swaps with every re-pointed use site enumerated
      (the `clA5_pt_unaryLength` ten).
- [ ] Task 3: done/escalated; the new `clFreshTM` definition, the
      `seamCompTM_run_ofCfg` citation, the flagged `Build.Seam` import —
      or the recorded obstruction.
- [ ] Duplication ledger: "new copies: none".
- [ ] Line count before/after (expected ≈ 8,710 after all three tasks).
- [ ] Final sweep log tail (Hardness + CookLevin facade) + 5 axiom prints.
- [ ] Diff touches only `CookLevin/Hardness.lean`.

## Known pitfalls at this pin (hard-won)

- `seamCompTM`'s dispatch branch matches on `Sum.inl s` with
  `if s = exit`: after `cases`, `dsimp only` then `split` — the
  `DecidableEq` instance is a binder, don't `decide`.
- The general `_ofCfg` seam trio starts phase two from phase one's
  returned configuration with only the control state replaced
  (`Cfg.mapState`); `(Cfg.ofWords q w).mapState f = Cfg.ofWords (f q) w`
  is definitional-or-near.
- Deleting a declaration with a preceding `/-- … -/` docstring: remove the
  docstring too, or it attaches to the next declaration and silently
  changes frozen text.
- `Function.update_of_ne` (not `update_noteq`); after
  `cases hs : cfg.state`, `dsimp only` before rewriting; avoid bare `simp`
  with folded forms; `omega` needs beta-reduced goals.
- This file's five publics live in namespace `Complexity` — print axioms
  with the names exactly as the file declares them.
```

## ===== audits/retrofit-r1-agent-reports/rb1-REPORT.md =====

```
# Retrofit RB1 report

**Complete: both binding tasks landed in two checked commits.** No task escalations or unfinished frontier. No push, pull request, or rebase was performed.

## Base and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Starting branch: `complexity/arora-barak-ch3-4`.
- Recorded base: `5588628cbbddea9546f616907364b608e15557fd`.
- Working branch: `fill/retrofit-rb1`.
- Final commit: `2bb8f379e1560dbdf6c693c1a1f40f417297876f`.
- Brief-issued base: `ff012d28ca3131452161669e1d7efe389b75ba2e`. The owned file was byte-identical between that commit and the recorded base.
- The complete Git diff touches only `TCSlib/Complexity/TuringMachine/Build/Loop.lean`. The archive's `Loop.lean` is that full modified source file.

| Commit | Task | Result |
|---|---|---|
| `cccc46916d79f9dffbf3d27a2ad3f40e2e09c8e0` | Delete eight dead declarations and update the historical sentence | Fresh Loop check: 0 errors, 0 sorry warnings |
| `2bb8f379e1560dbdf6c693c1a1f40f417297876f` | Derive body forwarding from public `emit_run` | Fresh Loop check: 0 errors, 0 sorry warnings |

Each commit was created only after its successful fresh Loop check. Immediately after each commit, the committed blob and working file were verified byte-identical to the checked source. `commit-checks.log` records those checks and source hashes. The final committed version was then compiled afresh again in the final sweep.

## Task 1: completed

All eight declarations, together with their docstrings, were removed:

| Declaration | Disposition |
|---|---|
| `loop_silent_prefix` | Deleted |
| `loopDebitTM` | Deleted |
| `loopDebitCfg` | Deleted |
| `loopBorrow_step` | Deleted |
| `loopBorrow_run` | Deleted |
| `loopBorrow_rewind` | Deleted |
| `loopBorrow_correct` | Deleted |
| `loopBody_capture` | Deleted |

The post-deletion compile succeeded; no missed referencer was found and no declaration needed restoration.

The one historical sentence formerly referencing `loopBorrow_correct` now reads:

> The host performs the counter borrow and rewind in phases 8--10.

Every other byte of that docstring was retained.

## Task 2: completed

Removed `emLoop_forward_apply` and `emLoop_forward_run`, including their docstrings. Retained `emLoopForwardCfg` and its docstring byte-for-byte: the existing call representation and frame proofs still use that configuration definition. The local forwarding proof family is replaced by a direct `Turing.emit_run` citation inside its sole proof consumer, `emLoopHost_body_forward`.

The replacement follows the binding glue plan:

1. `padded` is a local machine extending `loopBodySource` by one inactive tape through `leftAction 1 id`.
2. Local fact `hrun` is a direct `leftCfg_run` application and supplies both the padded trajectory and its liveness guard.
3. Local fact `hcfg` uses one `Cfg.ext` to commute `emitCfg` with `leftCfg`.
4. Simplification, including `Option.map_id`, proves the host agreement by commuting `emitAction` with the padding action.
5. `Turing.emit_run` supplies the guarded forwarding run, including any emission on the source's final halting transition.

**New private declarations: none.** `src` and `padded` are local bindings; `hrun` and `hcfg` are local proof facts, with the roles above. No private declaration was renamed or re-signatured. The consumer's statement and docstring are unchanged. Its new proof body is:

```lean
  -- Pad the stopped body, then use the public forwarding contract in this host.
  let src := loopBodySource body F anchor
  let padded : MultiTapeTM (body.k + 1 + (1 + F.k) + 1) Bool (body.State × Bool) :=
    ⟨src.q₀, fun q inp work => leftAction 1 id (src.tr q inp (fun i => work i.castSucc))⟩
  have hrun (u : ℕ) := leftCfg_run src padded id (fun _ _ _ => rfl)
    c (fun _ : Fin 1 => bufferTape []) (fun _ => 0) u
  have hcfg (emb : body.State × Bool → LoopHostState body F) (ret : LoopHostState body F)
      (d : Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x) :
      Turing.emitCfg emb ret pre (leftCfg id d (fun _ : Fin 1 => bufferTape []) (fun _ => 0)) =
        emLoopForwardCfg emb ret pre d := by
    refine Cfg.ext ?_ rfl rfl rfl rfl
    simp [Turing.emitCfg, emLoopForwardCfg, leftCfg]
  rw [← hcfg]
  rw [Turing.emit_run padded _ _ _ ?_ pre _ t ?_, hrun t, hcfg]
  · intro q inp work
    simp [padded, src, emLoopHost, Turing.emitAction, leftAction, Option.map_id]
  · intro u hu
    rw [hrun u]
    simpa [Cfg.Halted, leftCfg] using hlive u hu
```

**Duplication ledger: new copies: none.** The old action proof and induction are removed; the replacement cites the existing public proofs. Other inherited families remain untouched as required by the brief.

## Size and freeze

| Version | Lines | Public declarations | Private declarations |
|---|---:|---:|---:|
| Base | 5713 | 8 | 214 |
| After Task 1 | 5550 | 8 | 206 |
| Final | 5515 | 8 | 204 |

Task 1: `5713 - 163 = 5550` lines. Task 2: delete 52 lines of local forwarding lemmas and replace a 2-line consumer proof by 19 lines, giving `5550 - 52 - 2 + 19 = 5515`. Total reduction: **198 lines**.

`scope.log` records byte comparisons and SHA-256 hashes for all eight public declarations, including their complete signatures, statements, docstrings, and proof bodies. All are unchanged. Imports are byte-identical. The declaration inventory loses exactly the eight Task-1 targets and the two replaced proof lemmas; it gains nothing. The only retained declarations whose text differs are `loopHost_contracts` (the permitted sentence) and `emLoopHost_body_forward` (its proof body).

## Verification

Lean: `4.25.0`, compiler commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`. Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. No tracked toolchain, dependency, import, or checking-script changes were made. All tcslib compilation used `scripts/lean_check_tree.sh`; no `lake build` command was issued for tcslib.

The baseline completed all 65 listed modules, then the separately requested Catalog check. The supplied module-order list omits six prerequisites now imported by its facades: `Build/Embed`, `Build/Seam`, `Build/Catalog`, `NDCodes`, `Formulas/QBF`, and `Formulas/QBFEncoding`. These were compiled in dependency order without source changes. The interrupted bootstrap resumed at the unfinished module; earlier completed results were retained.

The baseline bootstrap has four inherited sorry warnings in untouched files, listed below. These are outside this batch. The owned file had zero admissions at the base and after both commits, and the final three requested module checks have zero sorry warnings.

```text
TCSlib/Complexity/TuringMachine/CounterProgRun.lean:343:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/NDCodes.lean:187:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Formulas/QBF.lean:119:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Formulas/QBFEncoding.lean:88:8: warning: declaration uses 'sorry'
```

Final ordered sweep summaries (complete diagnostics in `final-sweep.log`):

```text
RESULT TCSlib/Complexity/TuringMachine/Build/Loop: exit=0; errors=0; sorry_warnings=0; fresh_olean=True; PASS
RESULT TCSlib/Complexity/TuringMachine/Build/Catalog: exit=0; errors=0; sorry_warnings=0; fresh_olean=True; PASS
RESULT TCSlib/Complexity/TuringMachine: exit=0; errors=0; sorry_warnings=0; fresh_olean=True; PASS
```

Style lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build` — **0 FAIL, 3 WARN**, the same pre-existing size-warning count as the base.

All eight final axiom prints are byte-identical to their baseline prints. `stateWord` uses no axioms; the seven theorems use exactly the three permitted standard axioms. There is no `sorryAx` in these footprints:

```text
'Turing.stateWord' does not depend on any axioms
'Turing.loop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopCfgTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopFindTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_emitLoopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_installCallTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_emitCallTM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The final sweep and all pre-commit checks require a fresh nonempty `.olean`; the repository checker removes the prior artifact before invoking Lean. `git diff --check` passed, the working tree is clean, the two patches replayed sequentially from the recorded base and reproduced `Loop.lean` byte-for-byte, and `git bundle verify` passed. The bundle records the base above as its prerequisite and exposes `refs/heads/fill/retrofit-rb1` at the final commit.

## Delivery

The archive is flat, with no enclosing directory. It includes this report, the full `Loop.lean`, two numbered format-patches, `retrofit-rb1.bundle`, the final sweep and axiom-print logs, baseline axiom prints, per-task/commit/freeze/lint evidence, bootstrap evidence, delivery validation logs, and `SHA256SUMS`. `axioms.lean` supplies the eight print commands. SHA-256 checksums cover every payload file except the checksum manifest itself.
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

## ===== audits/retrofit-r1-agent-reports/rb3-REPORT.md =====

```
# RB3 retrofit report

Base: `5588628cbbddea9546f616907364b608e15557fd`.
Working branch: `fill/retrofit-rb3`, branched directly from
`complexity/arora-barak-ch3-4`; never rebased, pushed, or submitted as a PR.
The brief's issue commit is `ff012d28ca3131452161669e1d7efe389b75ba2e`;
`Hardness.lean` is byte-identical between that commit and the recorded base.

## Scope and import change

Only `TCSlib/Complexity/CookLevin/Hardness.lean` is modified in Git.
The five public theorems, including their docstrings and complete proof
bodies, are frozen byte-for-byte. Remaining private signatures and
non-exempt docstrings are also frozen.

**Sanctioned import change (Task 3):**
`import TCSlib.Complexity.TuringMachine.Build.Seam`.
This makes Hardness the first proof consumer of the §12 seam layer outside
`Build/`, as commissioned. No other import is changed.

## Task 1

Done: 6/6 deletions, with no unexpectedly live referencer and no escalation.
Commit: `b347d72c5aa3c791896e7f3d6b93f478bc692c46`.

The six prescribed deletion targets are `clRefClockTM`, `clRefClockCfg`,
`clCount_first`, `clRefCountTM`, `clRefCount_first`, and `clReadFields`.
Their own docstrings are deleted with them. The permitted replacement
`clCount_width` docstring is:

```lean
/-- A counter below `2^w` occupies at most `w` bits. Together with the
counter runtime bound, this charges one administrative increment by two
binary scans plus two transitions, with no unary-position representation. -/
```

## Task 2

Done: all three swaps and all 13 use sites verified; no escalation.
Commit: `5ec0ac6449f85a93d99e2b3ed196f4384c0c6893`.

`clCompute_comp` is deleted. Its two callers directly use
`FinTM.bufferedCompTM_computesInTime`, `output_length_le`, and runtime
monotonicity, preserving the existing time bounds.

`clBuffer_append_bit` is deleted; `clCopy_write` uses
`(FinTM.bufferTape_append record b).symm`.

`clA5_pt_unaryLength` is deleted; all ten uses become
`(clNative_fill true).comp ...`.

| Removed helper | Caller | Base use line | Final use line |
|---|---|---:|---:|
| `clBuffer_append_bit` | `clCopy_write` | 1757 | 1636 |
| `clCompute_comp` | `clQueryCode_machine` | 5160 | 4984 |
| `clCompute_comp` | `clNative_image` | 5314 | 5145 |
| `clA5_pt_unaryLength` | `clA5Drop_native` | 7012 | 6833 |
| `clA5_pt_unaryLength` | `clA5Field_native` | 7080 | 6901 |
| `clA5_pt_unaryLength` | `clA5StoredRound_native` (header field) | 7191 | 7012 |
| `clA5_pt_unaryLength` | `clA5StoredRound_native` (header tail) | 7192 | 7013 |
| `clA5_pt_unaryLength` | `clA5Next_native` | 7208 | 7029 |
| `clA5_pt_unaryLength` | `clA5Sizes_native` (header field) | 7749 | 7570 |
| `clA5_pt_unaryLength` | `clA5Sizes_native` (header tail) | 7750 | 7571 |
| `clA5_pt_unaryLength` | `clA5Cursor_native` | 8112 | 7933 |
| `clA5_pt_unaryLength` | `clA5Indices_native` | 8134 | 7955 |
| `clA5_pt_unaryLength` | `clA5Fragment_native` | 8211 | 8032 |

## Task 3

Done: the general-configuration seam citation elaborates directly; no escalation.
Commit: `9f58177bf2c75e5adfc8d5e7cbcee3179b361622`.

The new `clFreshTM` definition is:

```lean
private def clFreshTM : FinTM Bool where
  k := 2
  State := (Fin 3) ⊕ clReadTM.State
  tm := seamCompTM clWipeTM.tm 2 clReadTM.tm (.inl none)
```

`clFresh_run` obtains the reset's first-return cut from `clWipe_first`,
then directly cites `seamCompTM_run_ofCfg` with `clRead_run` at the empty
target. The phase-two configuration is definitionally the reset's returned
configuration with only its control state replaced. The exact composite
duration is `a + 1 + (3 * w.length + 3)`, bounded by
`2 * old.length + 3 * w.length + 6` using the existing bound on `a`.
The citation in the proof is:

```lean
  exact seamCompTM_run_ofCfg clWipeTM.tm (2 : Fin 3) clReadTM.tm (.inl none)
    he rfl hf (clRead_run x p pre w tail [] (by simp))
```

The displaced stream head and all other configuration fields cross the
seam intact. No new glue declarations are needed. `clFresh_idle` and
`clFresh_first` remain byte-identical.

## Duplication and size

Duplication ledger: **new copies: none**.
New private declarations: **none**.
This is a deletion/citation retrofit; inherited unrelated duplication remains
outside the owned task list.

Before: 8,904 lines, 553 private declarations, five public declarations.
After: 8,725 lines, 544 private declarations, five public declarations.
Net reduction: 179 lines and nine private declarations.
The remaining size warning is covered by the recorded retrofit/12.2c program
in `backlog.md` §2, `AroraBarakChapters3-4Plan.md` §4d, and
`machine-library-design.md` §12. No uncommissioned file split was attempted.

## Verification and environment

Lean 4.25.0, release commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`;
mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
No `lake build` command was run.

The container needed a process-executable-path compatibility shim to locate
the Lean installation (`environment/self_exe.c`, outside the repository).
The required `lake exe cache get` was attempted; its native compiler exited
135. The same pinned cache downloader succeeded through
`lake env lean --run .lake/packages/mathlib/Cache/Main.lean get`, restricted
to the 32 external imports needed by the complete bootstrap closure (969
cached modules). `TAR_OPTIONS=--no-same-owner` handles archive ownership in
this container. These are environment adjustments, not Lean-source changes.

The initial bootstrap process ended during Hardness without a completion
status or fresh olean. It was not counted as a pass. The first 50 successful
checks were retained, and the sweep resumed at module 51 with `lean -j 1`;
subsequent retrofit checks use a bounded two-worker setting (`lean -j 2`). The
combined bootstrap log records only completed checks plus the resumed run.

An uncommitted Task 2 attempt reported one `omega` elaboration failure:
the inferred polynomial runtime still contained a beta-redex. Adding
`dsimp only` before that arithmetic step resolves it; the exact replacement
proof also passes an isolated Lean check. The failed attempt is retained in
`logs/task2-attempt1.log` and was never committed. Every committed state
passes the full zero-error, zero-sorry gate.

The prescribed 65-module order list omits six dependencies now imported by
its facades. To complete the fresh bootstrap, the unchanged `Build/Embed`,
`Build/Seam`, `Build/Catalog`, and `NDCodes` modules are checked before the
TuringMachine facade, and unchanged `QBF` and `QBFEncoding` before the
Formulas facade. Task 3's `Build.Seam` is therefore fresh before use.

All 65 listed modules and the six omitted dependencies passed with fresh
oleans. The bootstrap's only admission warnings are four inherited
out-of-scope admissions: one each in `CounterProgRun`, `NDCodes`, `QBF`,
and `QBFEncoding`; none is in Hardness's import closure. Hardness itself
passed at baseline, immediately before each of the three commits, and in
the final ordered Hardness → CookLevin-facade sweep. Each of those successful
gates has zero errors and zero sorry warnings. Each compiler check removed the old olean
first. After each commit, the committed source, worktree source, and fresh
olean were hash-compared against the pre-commit checked state; the post-commit
logs attest that the commit changed none of those checked bytes. The last
post-commit state is additionally compiled afresh in the final sweep.

The five public axiom prints are byte-identical to the baseline and are
within the permitted axiom triple. The final source-scope verifier passes:
exactly nine deletions, no new declarations, exactly the authorized changed
blocks, frozen public blocks and retained private signatures/docstrings,
and only the sanctioned import addition. Style lint: **0 FAIL, 1 WARN**
(the recorded file-size warning).

Final sweep tail:

```text
PASS Hardness: exit 0, fresh olean, zero errors, zero sorry warnings.
PASS CookLevin facade: exit 0, fresh olean, zero errors, zero sorry warnings.
```

Final axiom prints:

```text
'Complexity.NPHard.polyTimeReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT3_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT3_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Commit gates:

| Task | Commit | Before | After |
|---|---|---|---|
| 1 | `b347d72c5aa3c791896e7f3d6b93f478bc692c46` | `logs/task1-precommit.log`: PASS | `logs/task1-postcommit.log`: PASS |
| 2 | `5ec0ac6449f85a93d99e2b3ed196f4384c0c6893` | `logs/task2-precommit.log`: PASS | `logs/task2-postcommit.log`: PASS |
| 3 | `9f58177bf2c75e5adfc8d5e7cbcee3179b361622` | `logs/task3-precommit.log`: PASS | `logs/task3-postcommit.log`: PASS |


## Delivery

The archive contains this report, the full modified source at its repository
path, the three-commit format-patch series, an incremental Git bundle against
the recorded base, verification logs, and `SHA256SUMS` covering every other
payload file. Apply patches in filename order from the recorded base.
```

## ===== audits/evidence/retrofit-rb1.patch =====

```
From cccc46916d79f9dffbf3d27a2ad3f40e2e09c8e0 Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Fri, 9 Oct 2026 16:45:57 -0300
Subject: [PATCH 1/2] refactor(loop): remove eight dead private declarations

---
 .../Complexity/TuringMachine/Build/Loop.lean  | 167 +-----------------
 1 file changed, 2 insertions(+), 165 deletions(-)

diff --git a/TCSlib/Complexity/TuringMachine/Build/Loop.lean b/TCSlib/Complexity/TuringMachine/Build/Loop.lean
index c33e04c1..3e99b317 100644
--- a/TCSlib/Complexity/TuringMachine/Build/Loop.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/Loop.lean
@@ -189,16 +189,6 @@ private lemma loop_live_prefix {k : ℕ} {S : Type*} {x : List Bool}
       MultiTapeTM.runFrom_of_halt _ hh]
   exact ht (by rw [he]; exact hh)
 
-/-- An empty final output forces every earlier output to be empty. -/
-private lemma loop_silent_prefix {k : ℕ} {S : Type*} {x : List Bool}
-    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
-    (ht : (tm.runFrom cfg t).output = []) :
-    ∀ u ≤ t, (tm.runFrom cfg u).output = [] := by
-  intro u hu
-  have hp := tm.output_prefix cfg hu
-  rw [ht] at hp
-  simpa using hp
-
 /-- Replace a possibly padded halting-time witness by its first halt,
 retaining the entire endpoint configuration.
 **Proof sketch.** Choose the least halting time. Minimality supplies the
@@ -436,132 +426,6 @@ private lemma loopBuffer_write (pre bs : List Bool) (old new : Bool) :
         simp only [List.getElem?_cons, if_neg (by omega : z.toNat - pre.length ≠ 0)]
     · simp only [if_neg hn]
 
-/-- One-tape fixed-width decrement, followed by a rewind. The live states are
-borrow (`inl none`), rewind with success flag (`inl (some b)`), and return
-(`inr b`). No transition emits physical output. Return states wait for a
-surrounding controller. This privately re-derives the counter template. -/
-private def loopDebitTM : FinTM Bool where
-  k := 1
-  State := Option Bool ⊕ Bool
-  tm :=
-    { q₀ := .inl none
-      tr := fun q _ work => match q with
-        | .inl none => match work 0 with
-          | some false => ⟨0, fun _ => (some (some true), .pos), none, some (.inl none)⟩
-          | some true => ⟨0, fun _ => (some (some false), .neg), none, some (.inl (some true))⟩
-          | none => ⟨0, fun _ => (none, .neg), none, some (.inl (some false))⟩
-        | .inl (some b) => match work 0 with
-          | some _ => ⟨0, fun _ => (none, .neg), none, some (.inl (some b))⟩
-          | none => ⟨0, fun _ => (none, .pos), none, some (.inr b)⟩
-        | .inr b => controlAction 0 (some (.inr b)) }
-
-/-- A candidate on the borrow tape, with arbitrary native input-head position. -/
-private def loopDebitCfg (x : List Bool) (p : Fin (x.length + 2))
-    (q : Option Bool ⊕ Bool) (z : ℤ) (u : List Bool) :
-    Cfg loopDebitTM.k Bool loopDebitTM.State x :=
-  ⟨some q, p, fun _ => bufferTape u, fun _ => z, []⟩
-
-/-- One borrow transition writes only inside the fixed-width word, or detects
-the right blank without writing to it. -/
-private lemma loopBorrow_step (x : List Bool) (p : Fin (x.length + 2))
-    (pre bs : List Bool) :
-    loopDebitTM.tm.step (loopDebitCfg x p (.inl none) pre.length (pre ++ bs)) =
-      match bs with
-      | [] => loopDebitCfg x p (.inl (some false)) (pre.length - 1) pre
-      | true :: us => loopDebitCfg x p (.inl (some true)) (pre.length - 1) (pre ++ false :: us)
-      | false :: us => loopDebitCfg x p (.inl none) (pre.length + 1) (pre ++ true :: us) := by
-  unfold MultiTapeTM.step
-  change (loopDebitTM.tm.tr (.inl none) _ _).apply _ = _
-  simp only [loopDebitTM, loopDebitCfg, Cfg.workTapeSymbols, loopBuffer_read]
-  cases bs with
-  | nil =>
-    refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
-    · simp
-    · funext i; simp [Action.apply, sub_eq_add_neg]
-  | cons b bs =>
-    cases b <;> refine Cfg.ext rfl (moveInputPos_zero p) ?_ ?_ rfl
-    all_goals first
-      | (funext i; exact loopBuffer_write pre bs _ _)
-      | (funext i; simp [Action.apply, sub_eq_add_neg])
-
-/-- The borrow phase takes one step beyond the leading false prefix, including
-one blank test on underflow.
-**Proof sketch.** Induct on the remaining candidate. Each false bit is set
-and added to the processed prefix. A true bit or the right blank starts
-rewind without changing the width. -/
-private lemma loopBorrow_run (x : List Bool) (p : Fin (x.length + 2))
-    (u : List Bool) : ∀ pre : List Bool,
-    loopDebitTM.tm.runFrom (loopDebitCfg x p (.inl none) pre.length (pre ++ u))
-        (loopBorrowPos u + 1) =
-      loopDebitCfg x p (.inl (some (loopDebit u).2))
-        ((pre.length : ℤ) + loopBorrowPos u - 1) (pre ++ (loopDebit u).1) := by
-  induction u with
-  | nil =>
-    intro pre
-    simpa [loopBorrowPos, loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
-      loopBorrow_step x p pre []
-  | cons b u ih =>
-    intro pre
-    cases b with
-    | true =>
-      simpa [loopBorrowPos, loopDebit, MultiTapeTM.runFrom_succ_eq_step] using
-        loopBorrow_step x p pre (true :: u)
-    | false =>
-      simp only [loopBorrowPos]
-      rw [MultiTapeTM.runFrom_succ_eq_step, loopBorrow_step]
-      simpa [loopDebit, List.append_assoc, Nat.cast_add, Nat.cast_one,
-        add_assoc, add_comm, add_left_comm] using ih (pre ++ [true])
-
-/-- Rewind over `j` known candidate cells to the left blank, then return at
-cell zero in exactly `j+1` steps, retaining the candidate and success flag. -/
-private lemma loopBorrow_rewind (x : List Bool) (p : Fin (x.length + 2))
-    (u : List Bool) (b : Bool) : ∀ j, j ≤ u.length →
-    loopDebitTM.tm.runFrom (loopDebitCfg x p (.inl (some b)) ((j : ℤ) - 1) u)
-        (j + 1) = loopDebitCfg x p (.inr b) 0 u := by
-  intro j
-  induction j with
-  | zero =>
-    intro hj
-    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
-    simp only [Nat.cast_zero, zero_sub]
-    unfold MultiTapeTM.step
-    simp only [loopDebitTM, loopDebitCfg, Cfg.workTapeSymbols, bufferTape_left]
-    refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
-    funext i; simp [Action.apply]
-  | succ j ih =>
-    intro hj
-    rw [MultiTapeTM.runFrom_succ_eq_step]
-    have hstep : loopDebitTM.tm.step
-        (loopDebitCfg x p (.inl (some b)) ((j + 1 : ℕ) - 1) u) =
-          loopDebitCfg x p (.inl (some b)) ((j : ℤ) - 1) u := by
-      have hz : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
-      rw [hz]
-      unfold MultiTapeTM.step
-      simp only [loopDebitTM, loopDebitCfg, Cfg.workTapeSymbols, bufferTape_nat,
-        List.getElem?_eq_getElem (by omega : j < u.length)]
-      refine Cfg.ext rfl (moveInputPos_zero p) rfl ?_ rfl
-      funext i; simp [Action.apply, sub_eq_add_neg]
-    rw [hstep]
-    exact ih (by omega)
-
-/-- A complete fixed-width decrement and rewind costs `2j+2 ≤ 2|u|+2`,
-where `j` is the leading false-prefix length. It returns live at cell zero,
-retains the input head, and emits nothing. Width zero returns underflow only
-when this subroutine is called, so enumeration can process `[]` first. -/
-private lemma loopBorrow_correct (x : List Bool) (p : Fin (x.length + 2))
-    (u : List Bool) :
-    2 * loopBorrowPos u + 2 ≤ 2 * u.length + 2 ∧
-      loopDebitTM.tm.runFrom (loopDebitCfg x p (.inl none) 0 u)
-          (2 * loopBorrowPos u + 2) =
-        loopDebitCfg x p (.inr (loopDebit u).2) 0 (loopDebit u).1 := by
-  refine ⟨by have := loopBorrowPos_le u; omega, ?_⟩
-  have hr := loopBorrow_run x p u []
-  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add] at hr
-  rw [show 2 * loopBorrowPos u + 2 = (loopBorrowPos u + 1) + (loopBorrowPos u + 1) by omega,
-    MultiTapeTM.runFrom_add, hr]
-  exact loopBorrow_rewind x p (loopDebit u).1 (loopDebit u).2 _
-    (by rw [loopDebit_length]; exact loopBorrowPos_le u)
-
 /-- Stop the body at the next anchor entry, distinguishing that return from
 a genuine source halt on an extra one-cell flag tape. A true release bit
 forces one source action, even at the anchor; every source successor clears
@@ -689,33 +553,6 @@ private lemma loopBody_run (body : FinTM Bool) (anchor : body.State) {x : List B
     rw [if_neg ht, loopBody_step body anchor _ q _ none hq hgo]
     simp only [Nat.succ_ne_zero, ↓reduceIte, MultiTapeTM.runFrom_succ_eq_step']
 
-/-- W1 captures the stopped body's complete trace in any agreeing controller.
-This includes an output bit emitted by the halting transition.
-**Proof sketch.** The preceding simulation gives strict liveness of the
-stop wrapper before the endpoint. Apply the audited capture contract with
-the supplied controller as host, then substitute the simulated endpoint. -/
-private lemma loopBody_capture (body : FinTM Bool) (anchor : body.State)
-    {H : Type*} {x : List Bool} (host : MultiTapeTM (body.k + 1 + 1) Bool H)
-    (emb : body.State × Bool → H) (ret : H)
-    (hagree : ∀ s inp work, host.tr (emb s) inp work =
-      captureAction emb ret ((loopBodyTM body anchor).tm.tr s inp fun i => work i.castSucc))
-    (c : Cfg body.k Bool body.State x) (release : Bool) (hc : c.state ≠ none)
-    (t : ℕ) (hlive : ∀ u < t, (body.tm.runFrom c u).state ≠ none)
-    (hanchor : ∀ u < t, (u = 0 ∧ release = true) ∨
-      (body.tm.runFrom c u).state ≠ some anchor) :
-    host.runFrom (captureCfg emb ret [] [] (loopBodyCfg body anchor c release none)) t =
-      captureCfg emb ret [] []
-        (loopBodyCfg body anchor (body.tm.runFrom c t) (if t = 0 then release else false)
-          (if (body.tm.runFrom c t).state = none then some true else none)) := by
-  have hguard : ∀ u < t,
-      ¬((loopBodyTM body anchor).tm.runFrom (loopBodyCfg body anchor c release none) u).Halted := by
-    intro u hu
-    rw [loopBody_run body anchor c release hc u
-      (fun v hv => hlive v (by omega)) (fun v hv => hanchor v (by omega))]
-    simpa [Cfg.Halted, loopBodyCfg] using hlive u hu
-  rw [capture_run (loopBodyTM body anchor).tm host emb ret hagree [] [] _ t hguard,
-    loopBody_run body anchor c release hc t hlive hanchor]
-
 /-- Disjoint finite control for fuel, body calls, and fourteen controller phases. -/
 private abbrev LoopHostState (body F : FinTM Bool) :=
   F.State ⊕ ((Bool × (body.State × Bool)) ⊕ Fin 14)
@@ -2202,8 +2039,8 @@ iterated body word and `loopDebit` word, retaining the fuel work residue.
 `loop_orbit_inv` supplies every local body premise. The body simulation and
 first-halt lemmas identify the first stop; W1 preserves its full payload.
 Phase 7 either emits/replays that payload or starts the width-bounded
-borrow. `loopBorrow_correct` is the standalone counter template to be
-lifted into phases 8--10. Final zero underflow and phase 11 belong to the
+borrow. The host performs the counter borrow and rewind
+in phases 8--10. Final zero underflow and phase 11 belong to the
 last rejecting segment. If the last candidate accepts, choose any halted
 false/empty terminal. Sum the phase constants with the audit's maximum
 ledger. The missing proof is precisely the controller-level lifting and
-- 
2.51.1

From 2bb8f379e1560dbdf6c693c1a1f40f417297876f Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Fri, 9 Oct 2026 16:47:08 -0300
Subject: [PATCH 2/2] refactor(loop): derive body forwarding from emit_run

---
 .../Complexity/TuringMachine/Build/Loop.lean  | 73 +++++--------------
 1 file changed, 19 insertions(+), 54 deletions(-)

diff --git a/TCSlib/Complexity/TuringMachine/Build/Loop.lean b/TCSlib/Complexity/TuringMachine/Build/Loop.lean
index 3e99b317..dbb41eae 100644
--- a/TCSlib/Complexity/TuringMachine/Build/Loop.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/Loop.lean
@@ -5024,58 +5024,6 @@ private def emLoopForwardCfg {k : ℕ} {S H : Type} {x : List Bool}
     Cfg (k + 1) Bool H x :=
   leftCfg id (Turing.emitCfg emb ret pre c) (fun _ : Fin 1 => bufferTape []) (fun _ => 0)
 
-/-- A forwarded action preserves the padded source configuration and appends
-its optional bit after the accumulated prefix, including on a halting action. -/
-private lemma emLoop_forward_apply {k : ℕ} {S H : Type} {x : List Bool}
-    (emb : S → H) (ret : H) (pre : List Bool)
-    (a : Action k Bool S) (c : Cfg k Bool S x) :
-    (leftAction 1 id (Turing.emitAction emb ret a)).apply (emLoopForwardCfg emb ret pre c) =
-      emLoopForwardCfg emb ret pre (a.apply c) := by
-  unfold emLoopForwardCfg
-  rw [leftCfg_apply]
-  have he : (Turing.emitAction emb ret a).apply (Turing.emitCfg emb ret pre c) =
-      Turing.emitCfg emb ret pre (a.apply c) := by
-    refine Cfg.ext rfl rfl rfl rfl ?_
-    simp only [Turing.emitAction, Turing.emitCfg, Action.apply, List.append_assoc]
-  rw [he]
-
-/-- Guarded forwarding with one inactive tape, proved locally so this batch
-does not depend on the concurrent `Turing.emit_run` admission.
-**Proof sketch.** The host sees exactly the source's active symbols. Apply
-the forwarded-action identity once per live source step and induct; the source
-may halt on the final action, after that action's emission is forwarded. -/
-private lemma emLoop_forward_run {k : ℕ} {S H : Type} {x : List Bool}
-    (src : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
-    (emb : S → H) (ret : H)
-    (hagree : ∀ q inp work, host.tr (emb q) inp work =
-      leftAction 1 id (Turing.emitAction emb ret (src.tr q inp (fun i => work i.castSucc))))
-    (pre : List Bool) (c : Cfg k Bool S x) (t : ℕ)
-    (hlive : ∀ j < t, (src.runFrom c j).state ≠ none) :
-    host.runFrom (emLoopForwardCfg emb ret pre c) t =
-      emLoopForwardCfg emb ret pre (src.runFrom c t) := by
-  have hs (d : Cfg k Bool S x) (hd : d.state ≠ none) :
-      host.step (emLoopForwardCfg emb ret pre d) =
-        emLoopForwardCfg emb ret pre (src.step d) := by
-    cases hq : d.state with
-    | none => exact False.elim (hd hq)
-    | some q =>
-      have hstate : (emLoopForwardCfg emb ret pre d).state = some (emb q) := by
-        simp [emLoopForwardCfg, leftCfg, Turing.emitCfg, hq]
-      have hwork : (fun i => (emLoopForwardCfg emb ret pre d).workTapeSymbols i.castSucc) =
-          d.workTapeSymbols := by
-        funext i
-        simp [emLoopForwardCfg, leftCfg, Turing.emitCfg, Cfg.workTapeSymbols,
-          Fin.addCases, i.isLt]
-      have hin : (emLoopForwardCfg emb ret pre d).inputSymbol = d.inputSymbol := rfl
-      simp only [MultiTapeTM.step, hstate, hq]
-      rw [hagree, hwork, hin]
-      exact emLoop_forward_apply emb ret pre _ d
-  induction t with
-  | zero => rfl
-  | succ t ih =>
-    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
-      hs _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']
-
 /-- The forwarding call stores output physically and keeps the former payload
 tape blank at zero. All body, counter, and fuel data use the existing layout. -/
 private def emLoopCall (body F : FinTM Bool) (anchor : body.State) {x : List Bool}
@@ -5119,8 +5067,25 @@ private lemma emLoopHost_body_forward (body F : FinTM Bool) (anchor : body.State
       emLoopForwardCfg (fun s => .inr (.inl (startup, s)))
         (.inr (.inr (if startup then 6 else 7 : Fin 14))) pre
         ((loopBodySource body F anchor).runFrom c t) := by
-  exact emLoop_forward_run (loopBodySource body F anchor) (emLoopHost body F anchor findMode).tm
-    _ _ (by intros; rfl) pre c t hlive
+  -- Pad the stopped body, then use the public forwarding contract in this host.
+  let src := loopBodySource body F anchor
+  let padded : MultiTapeTM (body.k + 1 + (1 + F.k) + 1) Bool (body.State × Bool) :=
+    ⟨src.q₀, fun q inp work => leftAction 1 id (src.tr q inp (fun i => work i.castSucc))⟩
+  have hrun (u : ℕ) := leftCfg_run src padded id (fun _ _ _ => rfl)
+    c (fun _ : Fin 1 => bufferTape []) (fun _ => 0) u
+  have hcfg (emb : body.State × Bool → LoopHostState body F) (ret : LoopHostState body F)
+      (d : Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x) :
+      Turing.emitCfg emb ret pre (leftCfg id d (fun _ : Fin 1 => bufferTape []) (fun _ => 0)) =
+        emLoopForwardCfg emb ret pre d := by
+    refine Cfg.ext ?_ rfl rfl rfl rfl
+    simp [Turing.emitCfg, emLoopForwardCfg, leftCfg]
+  rw [← hcfg]
+  rw [Turing.emit_run padded _ _ _ ?_ pre _ t ?_, hrun t, hcfg]
+  · intro q inp work
+    simp [padded, src, emLoopHost, Turing.emitAction, leftAction, Option.map_id]
+  · intro u hu
+    rw [hrun u]
+    simpa [Cfg.Halted, leftCfg] using hlive u hu
 
 /-- A live anchor endpoint is forwarded after one additional stop step.
 The exact endpoint keeps every inactive tape and carries the false stop flag.
-- 
2.51.1

```

## ===== audits/evidence/retrofit-rb2.patch =====

```
From f2d1ad365091f7a6ce75708d0f97187e513fbfbd Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Fri, 9 Oct 2026 16:28:37 -0300
Subject: [PATCH 1/2] Retrofit RB2: delete 62 dead emitter and split-search
 privates

---
 .../TuringMachine/Build/Primitives.lean       | 1222 -----------------
 1 file changed, 1222 deletions(-)

diff --git a/TCSlib/Complexity/TuringMachine/Build/Primitives.lean b/TCSlib/Complexity/TuringMachine/Build/Primitives.lean
index 3d969bdf841d87c6827cbf71d715b4cd9c377abe..c1f48adba375ddb51ac72783356dbe7ead3b89f2 100644
--- a/TCSlib/Complexity/TuringMachine/Build/Primitives.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/Primitives.lean
@@ -2962,13 +2962,6 @@ private lemma splitFind_eq (C e : ℕ) (w : List Bool) :
   apply Bool.eq_iff_iff.mpr
   simp only [splitAccept, List.length_replicate, decide_eq_true_eq, beq_iff_eq]
 
-/-- Failed split search is equivalent to rejecting every candidate within fuel. -/
-private lemma splitFind_none (C e : ℕ) (w : List Bool) :
-    solveSplit C e w.length = none ↔
-      ∀ i ≤ w.length, splitAccept C e w ((splitStep w)^[i] []) = false := by
-  rw [← splitFind_eq, List.find?_eq_none]
-  simp only [List.mem_range, Nat.lt_succ_iff, Bool.not_eq_true]
-
 /-- Each successful orbit payload is exactly the split at the returned index;
 exhaustion returns the same empty word on both sides. -/
 private lemma splitLoop_result (C e : ℕ) (w : List Bool) :
@@ -3415,27 +3408,6 @@ private lemma splitCount_accept {k : ℕ} {S H : Type} (emb : S → Bool → H)
     · simp [he]
     · simp [hlt, he, show w.length < s.length + c.output.length by omega]
 
-/-- The counted simulation can be stopped at the source's first halt without
-losing the exact initialized-bank endpoint. This removes any padded halted
-tail from a source time bound before entering the next controller phase. -/
-private lemma splitCount_firstHalt {k : ℕ} {S H : Type}
-    (tm : MultiTapeTM k Bool S) (host : MultiTapeTM (k + 1) Bool H)
-    (emb : S → Bool → H) (ret : Bool → H)
-    (hagree : ∀ q over inp work, host.tr (emb q over) inp work =
-      splitCountAction emb ret over inp (tm.tr q none (fun i => work i.succ)))
-    (w s : List Bool) (c d : Cfg k Bool S []) (T : ℕ)
-    (hd : d.state = none) (hT : tm.runFrom c T = d) :
-    ∃ t ≤ T, host.runFrom (splitCountCfg emb ret w s c) t = splitCountCfg emb ret w s d := by
-  classical
-  have hh : ∃ t, (tm.runFrom c t).state = none := ⟨T, by rw [hT, hd]⟩
-  let t := Nat.find hh
-  have ht : t ≤ T := Nat.find_min' hh (by rw [hT, hd])
-  have hs : (tm.runFrom c t).state = none := Nat.find_spec hh
-  have he := tm.runFrom_add c t (T - t)
-  rw [Nat.add_sub_of_le ht, hT, tm.runFrom_of_halt _ hs] at he
-  refine ⟨t, ht, ?_⟩
-  rw [splitCount_run tm host emb ret hagree w s c t (fun j hj => Nat.find_min hh hj), ← he]
-
 /-- Prepare the polynomial loop bank by copying the candidate's length to all
 scratch tapes in parallel, adding the extra side-length cell, and rewinding
 all work heads along the untouched candidate. State 2 is the return seam. -/
@@ -3561,27 +3533,6 @@ private lemma splitPrepare_run (k : ℕ) (w s : List Bool) :
   rw [hinit, show 2 * (s.length + 1) = (s.length + 1) + (s.length + 1) by omega,
     MultiTapeTM.runFrom_add, hfirst, splitPrepare_rewind k w s s.length (le_refl _)]
 
-/-- Preparation can be exposed at its first return-state entry, with no
-premature visit and without changing its exact initialized-bank endpoint. -/
-private lemma splitPrepare_first (k : ℕ) (w s : List Bool) :
-    ∃ t ≤ 2 * (s.length + 1),
-      (∀ j < t, ((splitPrepareTM k).tm.runFrom
-        (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) j).state ≠
-          some (2, decide (w.length < s.length))) ∧
-      (splitPrepareTM k).tm.runFrom
-        (Cfg.ofWords (input := w) (0, false) (stateWord (k + 1) s)) t =
-          splitPrepareReady k w s 2 0 := by
-  apply catalogFirstEntry (splitPrepareTM k).tm (2, decide (w.length < s.length))
-  · intro z hz
-    unfold MultiTapeTM.step
-    rw [hz]
-    change (controlAction 0 (some (2, decide (w.length < s.length)))).apply z = z
-    rw [controlAction_apply, moveInputPos_zero]
-    cases z
-    simp_all
-  · rfl
-  · exact splitPrepare_run k w s
-
 /-- A phase trace excludes the round anchor even at its two endpoints. -/
 private def splitSafe {k : ℕ} {S : Type} {w : List Bool}
     (tm : MultiTapeTM k Bool S) (anchor : S) (c : Cfg k Bool S w) (t : ℕ) : Prop :=
@@ -4547,136 +4498,6 @@ private lemma emitterSplit_of_body (f TE : ℕ → ℕ) (body : FinTM Bool)
   convert hm.mono (emitterSplit_loop_bound c (A + a) w.length (TE (w.length + 1))) using 1
   exact (emitterSplit_result f w).symm
 
-/-- A zero-tape placeholder supplies only the empty inactive bank of the
-virtual-input wrapper. Its own transition is never entered by this phase. -/
-private def emitterIdleTM : FinTM Bool where
-  k := 0
-  State := Unit
-  tm := ⟨(), fun _ _ _ => controlAction 0 none⟩
-
-/-- The candidate evaluator is the guarded virtual-input phase of the proved
-buffered simulator, wrapped by the capture transformer. Its completed state
-is a live return state; no evaluated bit reaches the physical output. -/
-private def emitterEvalTM (M : FinTM Bool) : FinTM Bool where
-  k := (bufferedCompTM emitterIdleTM M).k + 1
-  State := (bufferedCompTM emitterIdleTM M).State ⊕ Unit
-  tm := {
-    q₀ := .inl (bufferedCompTM emitterIdleTM M).tm.q₀
-    tr := fun q inp work => match q with
-      | .inl q => captureAction Sum.inl (.inr ())
-          ((bufferedCompTM emitterIdleTM M).tm.tr q inp (fun i => work i.castSucc))
-      | .inr () => controlAction 0 (some (.inr ())) }
-
-/-- Exact evaluator configuration: the preserved candidate occupies tape zero,
-the source work bank follows it, and the final tape captures every source
-emission, including the halting emission. The original input head is fixed. -/
-private def emitterEvalCfg (M : FinTM Bool) {w s : List Bool}
-    (c : Cfg M.k Bool M.State s) (b : Bool) (p : Fin (w.length + 2)) :
-    Cfg (emitterEvalTM M).k Bool (emitterEvalTM M).State w :=
-  captureCfg Sum.inl (.inr ()) [] []
-    (bufferedSecondCfg emitterIdleTM M c b p (fun i => i.elim0) (fun i => i.elim0))
-
-/-- Guarded virtual simulation and capture commute through every live source
-prefix. The completed configuration, rather than a time bound, selects return.
-**Proof sketch.** The public virtual-input theorem supplies a valid arrival
-tag and the exact source configuration at each time. Its live prefixes meet
-the capture theorem's guard, so the latter captures exactly that same run. -/
-private lemma emitter_eval_run (M : FinTM Bool) {w s : List Bool}
-    (c : Cfg M.k Bool M.State s) (b : Bool) (hb : VirtualTag c.inputPos b)
-    (p : Fin (w.length + 2)) (t : ℕ)
-    (hlive : ∀ j < t, (M.tm.runFrom c j).state ≠ none) :
-    ∃ b', VirtualTag (M.tm.runFrom c t).inputPos b' ∧
-      (emitterEvalTM M).tm.runFrom (emitterEvalCfg M c b p) t =
-        emitterEvalCfg M (M.tm.runFrom c t) b' p := by
-  have hvirtual (j : ℕ) := bufferedSecondCfg_run emitterIdleTM M c b hb p
-    (fun i => i.elim0) (fun i => i.elim0) j
-  have hguard : ∀ j < t, ¬((bufferedCompTM emitterIdleTM M).tm.runFrom
-      (bufferedSecondCfg emitterIdleTM M c b p (fun i => i.elim0) (fun i => i.elim0)) j).Halted := by
-    intro j hj
-    obtain ⟨tag, _, he⟩ := hvirtual j
-    rw [he]
-    simpa only [Cfg.Halted, bufferedSecondCfg, Option.map_eq_none_iff] using hlive j hj
-  have hcap := capture_run (bufferedCompTM emitterIdleTM M).tm (emitterEvalTM M).tm
-    Sum.inl (.inr ()) (fun _ _ _ => rfl) [] []
-    (bufferedSecondCfg emitterIdleTM M c b p (fun i => i.elim0) (fun i => i.elim0)) t hguard
-  obtain ⟨tag, htag, he⟩ := hvirtual t
-  rw [he] at hcap
-  exact ⟨tag, htag, hcap⟩
-
-/-- A prepared candidate with blank source work and an empty capture tape is
-exactly the library state-word seam at the evaluator's initial virtual state.
-**Proof sketch.** Compare all configuration fields. Split a tape index into the candidate,
-source bank, and capture slot; all work heads start at zero. -/
-private lemma emitter_eval_initial (M : FinTM Bool) (w s : List Bool) :
-    emitterEvalCfg (w := w) M (M.tm.initCfg s) true 1 =
-      Cfg.ofWords (.inl (.inr (.inr (M.tm.q₀, true))))
-        (stateWord (emitterEvalTM M).k s) := by
-  refine Cfg.ext rfl rfl ?_ ?_ rfl
-  · funext i
-    change (if h : i.val < 0 + (1 + M.k) then
-      tapeBlocks (fun j : Fin 0 => j.elim0) (bufferTape s)
-        (fun _ : Fin M.k => fun _ => none) ⟨i.val, h⟩
-      else bufferTape []) = bufferTape (if i.val = 0 then s else [])
-    by_cases hi : i.val < 0 + (1 + M.k)
-    · rw [dif_pos hi]
-      by_cases hz : i.val = 0
-      · simp [tapeBlocks, Fin.addCases, hz]
-      · have h1 : ¬ i.val < 1 := by omega
-        simp [tapeBlocks, Fin.addCases, hz, h1]
-    · rw [dif_neg hi]
-      have hz : i.val ≠ 0 := by omega
-      simp [hz]
-  · funext i
-    dsimp only [emitterEvalCfg, captureCfg, bufferedSecondCfg,
-      MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords]
-    simp only [Fin.val_one, Nat.cast_one, sub_self, List.nil_append, List.length_nil, Nat.cast_zero]
-    split
-    · simp [tapeBlocks, Fin.addCases, emitterIdleTM]
-    · rfl
-
-/-- A timed evaluator reaches the actual first source halt, with no earlier
-visit to the live return state and with the exact complete capture buffer.
-**Proof sketch.** Take the least halting time justified by totality. Absorption
-identifies the output there with the specified output at the deadline. Apply
-captured virtual lockstep through that time and through every earlier prefix.
-The deadline is used only for the inequality, never as a native clock. -/
-private lemma emitter_eval_first (M : FinTM Bool) (w s out : List Bool) (T : ℕ)
-    (hM : M.ComputesInTime s out T) :
-    ∃ t ≤ T, ∃ b,
-      VirtualTag (M.tm.runFrom (M.tm.initCfg s) t).inputPos b ∧
-      (M.tm.runFrom (M.tm.initCfg s) t).state = none ∧
-      (M.tm.runFrom (M.tm.initCfg s) t).output = out ∧
-      (∀ j < t, ((emitterEvalTM M).tm.runFrom
-        (emitterEvalCfg (w := w) M (M.tm.initCfg s) true 1) j).state ≠ some (.inr ())) ∧
-      (emitterEvalTM M).tm.runFrom
-        (emitterEvalCfg (w := w) M (M.tm.initCfg s) true 1) t =
-          emitterEvalCfg (w := w) M (M.tm.runFrom (M.tm.initCfg s) t) b 1 := by
-  classical
-  have hspec := (computesInTime_iff M s out T).mp hM
-  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg s) t).state = none := ⟨T, hspec.1⟩
-  let t := Nat.find hex
-  have ht : t ≤ T := Nat.find_min' hex hspec.1
-  have hh : (M.tm.runFrom (M.tm.initCfg s) t).state = none := Nat.find_spec hex
-  have hlive : ∀ j < t, (M.tm.runFrom (M.tm.initCfg s) j).state ≠ none :=
-    fun j hj => Nat.find_min hex hj
-  have hout : (M.tm.runFrom (M.tm.initCfg s) t).output = out :=
-    ((computesInTime_iff M s _ t).mpr ⟨hh, rfl⟩).output_unique hM
-  have htag : VirtualTag (M.tm.initCfg s).inputPos true := by
-    simp [VirtualTag, MultiTapeTM.initCfg, Cfg.init]
-  obtain ⟨b, hb, hr⟩ := emitter_eval_run M (M.tm.initCfg s) true htag
-    (1 : Fin (w.length + 2)) t hlive
-  refine ⟨t, ht, b, hb, hh, hout, ?_, hr⟩
-  intro j hj
-  obtain ⟨b', _, hr'⟩ := emitter_eval_run M (M.tm.initCfg s) true htag
-    (1 : Fin (w.length + 2)) j (fun l hl => hlive l (by omega))
-  rw [hr']
-  cases hs : (M.tm.runFrom (M.tm.initCfg s) j).state with
-  | none => exact False.elim (hlive j hj hs)
-  | some q =>
-    dsimp only [emitterEvalCfg, captureCfg, bufferedSecondCfg]
-    rw [hs]
-    simp
-
 /-- Equality of one-longer prefixes checks the entire old prefix and the next
 optional bit. In particular, a missing bit differs from a present false bit. -/
 private lemma emitter_take_succ_eq (u v : List Bool) (j : ℕ) :
@@ -4819,575 +4640,6 @@ private lemma emitter_compare_run (w u v : List Bool) (p : Fin (w.length + 2)) :
     MultiTapeTM.runFrom_add, hfirst]
   exact emitter_compare_rewind w u v p (decide (u = v)) l (le_refl _)
 
-/-- A contiguous visited interval, marked independently of the simulated data.
-The bounds are proof data; the cleaner reads only the marker tape. -/
-private def emitterInterval (left : ℤ) (width : ℕ) (z : ℤ) : Option Bool :=
-  if left ≤ z ∧ z < left + width then some true else none
-
-/-- Erase the first `j` cells of a visited interval without changing any other
-cell. This describes the cleaner's successive physical tape contents. -/
-private def emitterCleared (data : ℤ → Option Bool) (left : ℤ) (j : ℕ) (z : ℤ) : Option Bool :=
-  if left ≤ z ∧ z < left + j then none else data z
-
-/-- One native erasure enlarges the cleared interval by exactly one cell. -/
-private lemma emitter_cleared_step (data : ℤ → Option Bool) (left : ℤ) (j : ℕ) :
-    Function.update (emitterCleared data left j) (left + j) none =
-      emitterCleared data left (j + 1) := by
-  funext z
-  by_cases hz : z = left + j
-  · subst z; simp [emitterCleared]
-  · rw [Function.update_of_ne hz]
-    have hiff : (left ≤ z ∧ z < left + j) ↔
-        (left ≤ z ∧ z < left + (j + 1 : ℕ)) := by omega
-    simp only [emitterCleared, hiff]
-
-/-- A marked finite work interval can be cleared natively despite arbitrary
-blank holes in its data. Tape one marks the visited interval; tape two marks
-only the origin. All three heads stay aligned. Return state three is silent. -/
-private def emitterClearTM : FinTM Bool where
-  k := 3
-  State := Fin 4
-  tm := {
-    q₀ := 0
-    tr := fun q _ work => match q.val with
-      | 0 => if work 1 = none then
-          ⟨0, fun _ => (none, .pos), none, some 1⟩
-        else ⟨0, fun _ => (none, .neg), none, some 0⟩
-      | 1 => if work 1 = none then
-          ⟨0, fun _ => (none, .neg), none, some 2⟩
-        else ⟨0, fun i => (if i = 2 then none else some none, .pos), none, some 1⟩
-      | 2 => if work 2 = none then
-          ⟨0, fun _ => (none, .neg), none, some 2⟩
-        else ⟨0, fun i => (if i = 2 then some none else none, 0), none, some 3⟩
-      | _ => controlAction 0 (some 3) }
-
-/-- The cleaner's three tapes hold data, the interval marker, and the origin
-marker, respectively. The native input and physical output are untouched. -/
-private def emitterClearCfg (w : List Bool) (p : Fin (w.length + 2)) (q : Fin 4)
-    (data marks origin : ℤ → Option Bool) (h : ℤ) : Cfg 3 Bool emitterClearTM.State w :=
-  ⟨some q, p, (fun i => match i.val with | 0 => data | 1 => marks | _ => origin), fun _ => h, []⟩
-
-/-- The initial left scan reaches the marked interval's left end in `j+2`
-steps, independently of blank holes in the data being cleared.
-**Proof sketch.** Induct on the distance from the marked left endpoint. The marker,
-independent of the data, forces every left move; its first blank triggers
-the one-step return to the first marked cell. -/
-private lemma emitter_clear_left (w : List Bool) (p : Fin (w.length + 2))
-    (data : ℤ → Option Bool) (left : ℤ) (width : ℕ) :
-    ∀ j, j < width →
-      emitterClearTM.tm.runFrom
-        (emitterClearCfg w p 0 data (emitterInterval left width) (bufferTape [true]) (left + j))
-        (j + 2) =
-      emitterClearCfg w p 1 data (emitterInterval left width) (bufferTape [true]) left := by
-  intro j
-  induction j with
-  | zero =>
-    intro hj
-    have hmark : emitterInterval left width left = some true := by
-      simp [emitterInterval]; omega
-    have hblank : emitterInterval left width (left - 1) = none := by
-      simp [emitterInterval]
-    have hs : emitterClearTM.tm.step
-        (emitterClearCfg w p 0 data (emitterInterval left width) (bufferTape [true]) left) =
-        emitterClearCfg w p 0 data (emitterInterval left width) (bufferTape [true]) (left - 1) := by
-      simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
-        hmark, reduceCtorEq, ↓reduceIte]
-      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
-      funext i; simp [Action.apply, sub_eq_add_neg]
-    have hs' : emitterClearTM.tm.step
-        (emitterClearCfg w p 0 data (emitterInterval left width) (bufferTape [true]) (left - 1)) =
-        emitterClearCfg w p 1 data (emitterInterval left width) (bufferTape [true]) left := by
-      simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
-        hblank, ↓reduceIte]
-      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
-      funext i; simp [Action.apply]
-    simpa only [Nat.cast_zero, add_zero] using
-      show emitterClearTM.tm.step (emitterClearTM.tm.step
-        (emitterClearCfg w p 0 data (emitterInterval left width) (bufferTape [true]) left)) = _
-        from by rw [hs, hs']
-  | succ j ih =>
-    intro hj
-    have hmark : emitterInterval left width (left + (j + 1 : ℕ)) = some true := by
-      simp [emitterInterval]; omega
-    have hs : emitterClearTM.tm.step
-        (emitterClearCfg w p 0 data (emitterInterval left width) (bufferTape [true])
-          (left + (j + 1 : ℕ))) =
-        emitterClearCfg w p 0 data (emitterInterval left width) (bufferTape [true]) (left + j) := by
-      simp only [emitterClearCfg, MultiTapeTM.step, emitterClearTM, Cfg.workTapeSymbols,
-        Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, hmark, reduceCtorEq, ↓reduceIte]
-      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
-      funext i; simp [Action.apply]; omega
-    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
-    exact ih (by omega)
-
-/-- Before any erasure, the data tape is unchanged. -/
-private lemma emitter_cleared_zero (data : ℤ → Option Bool) (left : ℤ) :
-    emitterCleared data left 0 = data := by
-  funext z
-  simp [emitterCleared]
-
-/-- Clearing the full marked interval removes all data if there was no data
-outside it. No assumption is made about holes or values inside the interval. -/
-private lemma emitter_cleared_all (data : ℤ → Option Bool) (left : ℤ) (width : ℕ)
-    (hdata : ∀ z, ¬(left ≤ z ∧ z < left + width) → data z = none) :
-    emitterCleared data left width = fun _ => none := by
-  funext z
-  by_cases hz : left ≤ z ∧ z < left + width
-  · simp [emitterCleared, hz]
-  · simp [emitterCleared, hz, hdata z hz]
-
-/-- The right scan clears data and its interval marker in lockstep while
-leaving the separate origin marker intact.
-**Proof sketch.** Induct on the number of remaining marked cells. Each transition clears
-one data cell and its marker, advances both heads, and preserves the origin. -/
-private lemma emitter_clear_scan (w : List Bool) (p : Fin (w.length + 2))
-    (data : ℤ → Option Bool) (left : ℤ) (width : ℕ) :
-    ∀ j, j ≤ width →
-      emitterClearTM.tm.runFrom
-        (emitterClearCfg w p 1 data (emitterInterval left width) (bufferTape [true]) left) j =
-      emitterClearCfg w p 1 (emitterCleared data left j)
-        (emitterCleared (emitterInterval left width) left j) (bufferTape [true]) (left + j) := by
-  intro j
-  induction j with
-  | zero => intro _; simp [emitter_cleared_zero]
-  | succ j ih =>
-    intro hj
-    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
-    have hmark : emitterCleared (emitterInterval left width) left j (left + j) = some true := by
-      simp [emitterCleared, emitterInterval]; omega
-    simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM,
-      Cfg.workTapeSymbols, Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, hmark,
-      reduceCtorEq, ↓reduceIte]
-    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
-    · funext i
-      fin_cases i
-      · simpa [Action.apply] using emitter_cleared_step data left j
-      · simpa [Action.apply] using emitter_cleared_step (emitterInterval left width) left j
-      · simp [Action.apply]
-    · funext i; simp [Action.apply]; omega
-
-/-- Removing the only origin marker makes its entire tape blank. -/
-private lemma emitter_origin_erase :
-    Function.update (bufferTape [true]) 0 none = fun _ => none := by
-  funext z
-  by_cases hz : z = 0
-  · subst z; simp
-  · rw [Function.update_of_ne hz]
-    by_cases h0 : 0 ≤ z
-    · have hn : 0 < z.toNat := by omega
-      simp [bufferTape, h0, List.getElem?_eq_none (by simp; omega : [true].length ≤ z.toNat)]
-    · simp [bufferTape, h0]
-
-/-- Once the interval is erased, the surviving origin marker returns all
-three heads to zero and is itself erased on the final transition.
-**Proof sketch.** Induct on the distance to zero. The singleton origin marker distinguishes
-the stopping cell; that transition erases the marker and retains all heads there. -/
-private lemma emitter_clear_origin (w : List Bool) (p : Fin (w.length + 2)) :
-    ∀ n : ℕ, emitterClearTM.tm.runFrom
-      (emitterClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n) (n + 1) =
-      emitterClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
-  intro n
-  induction n with
-  | zero =>
-    change (⟨0, (fun i : Fin 3 => (if i = 2 then some none else none, 0)),
-      none, some (3 : Fin 4)⟩ : Action 3 Bool (Fin 4)).apply
-      (emitterClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) 0) = _
-    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
-    · funext i
-      fin_cases i <;> simp [Action.apply, emitterClearCfg, emitter_origin_erase]
-    · funext i; simp [Action.apply, emitterClearCfg]
-  | succ n ih =>
-    have hblank : bufferTape [true] ((n + 1 : ℕ) : ℤ) = none := by
-      rw [bufferTape_nat]; simp
-    have hs : emitterClearTM.tm.step
-        (emitterClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) (n + 1 : ℕ)) =
-        emitterClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
-      simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
-        Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, hblank, ↓reduceIte]
-      refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
-      funext i; simp [Action.apply]
-    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
-    exact ih
-
-/-- Native cleanup of a finite marked work interval returns three blank tapes
-with all heads at zero in a positive, linear number of steps.
-**Proof sketch.** Scan left to the interval boundary, clear the entire interval
-while moving right, then use the untouched origin marker to rewind. That last
-marker is erased only when the heads are already at zero. All dispatches use
-observed tape symbols; the interval bounds occur solely in the proof. -/
-private lemma emitter_clear_run (w : List Bool) (p : Fin (w.length + 2))
-    (data : ℤ → Option Bool) (left : ℤ) (width j : ℕ)
-    (hleft : left ≤ 0) (hright : 0 < left + width) (hj : j < width)
-    (hdata : ∀ z, ¬(left ≤ z ∧ z < left + width) → data z = none) :
-    ∃ t, 0 < t ∧ t ≤ 3 * width + 4 ∧
-      emitterClearTM.tm.runFrom
-        (emitterClearCfg w p 0 data (emitterInterval left width) (bufferTape [true]) (left + j)) t =
-      emitterClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
-  let n := (left + width - 1).toNat
-  have hn : (n : ℤ) = left + width - 1 := by dsimp [n]; omega
-  have hnlt : n < width := by omega
-  have hscan := emitter_clear_scan w p data left width width (le_refl _)
-  rw [emitter_cleared_all data left width hdata,
-    emitter_cleared_all (emitterInterval left width) left width
-      (by intro z hz; simp [emitterInterval, hz])] at hscan
-  have hturn : emitterClearTM.tm.step
-      (emitterClearCfg w p 1 (fun _ => none) (fun _ => none)
-        (bufferTape [true]) (left + width)) =
-      emitterClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
-    simp only [MultiTapeTM.step, emitterClearCfg, emitterClearTM, Cfg.workTapeSymbols,
-      Fin.val_zero, Fin.val_one, Nat.one_ne_zero, ↓reduceIte, ↓reduceIte]
-    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
-    funext i; simp [Action.apply]; omega
-  have hforward : emitterClearTM.tm.runFrom
-      (emitterClearCfg w p 1 data (emitterInterval left width) (bufferTape [true]) left)
-      (width + 1) =
-      emitterClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
-    rw [MultiTapeTM.runFrom_succ_eq_step', hscan, hturn]
-  have hfirst : emitterClearTM.tm.runFrom
-      (emitterClearCfg w p 0 data (emitterInterval left width) (bufferTape [true]) (left + j))
-      ((j + 2) + (width + 1)) =
-      emitterClearCfg w p 2 (fun _ => none) (fun _ => none) (bufferTape [true]) n := by
-    rw [MultiTapeTM.runFrom_add, emitter_clear_left w p data left width j hj, hforward]
-  refine ⟨(j + 2) + (width + 1) + (n + 1), by omega, by omega, ?_⟩
-  rw [MultiTapeTM.runFrom_add, hfirst, emitter_clear_origin]
-
-/-- A closed visited-cell interval; nonblank data may have arbitrary holes
-inside this independently maintained marker. -/
-private def emitterSpan (lo hi z : ℤ) : Option Bool :=
-  if lo ≤ z ∧ z ≤ hi then some true else none
-
-/-- Marking a cell at most one step outside a contiguous visited interval
-extends exactly its appropriate endpoint. -/
-private lemma emitter_span_extend (lo hi h : ℤ) (hord : lo ≤ hi)
-    (hnear : lo - 1 ≤ h ∧ h ≤ hi + 1) :
-    Function.update (emitterSpan lo hi) h (some true) = emitterSpan (min lo h) (max hi h) := by
-  funext z
-  by_cases hz : z = h
-  · subst z
-    simp [emitterSpan, min_le_right, le_max_right]
-  · rw [Function.update_of_ne hz]
-    have he : (lo ≤ z ∧ z ≤ hi) ↔ (min lo h ≤ z ∧ z ≤ max hi h) := by omega
-    simp only [emitterSpan, he]
-
-/-- Three separate banks hold simulated data, visited-cell markers, and
-origin markers. Corresponding heads always move together. -/
-private def emitterSlots {α : Type} {k : ℕ} (data marks origin : Fin k → α) :
-    Fin (k + (k + k)) → α := Fin.addCases data (Fin.addCases marks origin)
-
-/-- A tracked evaluator uses two native steps per source step. The first
-performs the source action; the second marks the new head cells before
-possibly halting. Initialization marks each origin in both marker banks.
-Physical output remains the source output, ready for the capture wrapper. -/
-private def emitterTrackTM (M : FinTM Bool) : FinTM Bool where
-  k := M.k + (M.k + M.k)
-  State := M.State ⊕ (Option M.State ⊕ Unit)
-  tm := {
-    q₀ := .inr (.inr ())
-    tr := fun q inp work => match q with
-      | .inr (.inr ()) =>
-        ⟨0, emitterSlots (fun _ => (none, 0))
-          (fun _ => (some (some true), 0)) (fun _ => (some (some true), 0)),
-          none, some (.inl M.tm.q₀)⟩
-      | .inl q =>
-        let a := M.tm.tr q inp (fun i => work (Fin.castAdd (M.k + M.k) i))
-        ⟨a.inputTape, emitterSlots a.workTapes
-          (fun i => (none, (a.workTapes i).2)) (fun i => (none, (a.workTapes i).2)),
-          a.output, some (.inr (.inl a.state))⟩
-      | .inr (.inl next) =>
-        ⟨0, emitterSlots (fun _ => (none, 0))
-          (fun _ => (some (some true), 0)) (fun _ => (none, 0)),
-          none, next.map Sum.inl⟩ }
-
-/-- A completed tracked source step, with source data unchanged and the
-visited interval covering each current source head. -/
-private def emitterTrackCfg (M : FinTM Bool) {x : List Bool}
-    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ) :
-    Cfg (emitterTrackTM M).k Bool (emitterTrackTM M).State x :=
-  ⟨c.state.map Sum.inl, c.inputPos,
-    emitterSlots c.workTapes (fun i => emitterSpan (lo i) (hi i)) (fun _ => bufferTape [true]),
-    emitterSlots c.workTapePos c.workTapePos c.workTapePos, c.output⟩
-
-/-- The intermediate stamp state retains the previous interval markers while
-the source data, input, heads, and emitted output already reflect its action. -/
-private def emitterTrackMid (M : FinTM Bool) {x : List Bool}
-    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ) :
-    Cfg (emitterTrackTM M).k Bool (emitterTrackTM M).State x :=
-  { emitterTrackCfg M c lo hi with state := some (.inr (.inl c.state)) }
-
-/-- The source-action microstep preserves the exact data simulation and moves
-both marker heads by that same action. It includes any halting emission.
-**Proof sketch.** Unfold the actual source action and compare all configuration fields.
-Separate the three tape banks: data performs the source write, while both
-marker banks move without writing and retain aligned heads. -/
-private lemma emitter_track_action (M : FinTM Bool) {x : List Bool}
-    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ) (hc : c.state ≠ none) :
-    (emitterTrackTM M).tm.step (emitterTrackCfg M c lo hi) =
-      emitterTrackMid M (M.tm.step c) lo hi := by
-  cases hs : c.state with
-  | none => exact False.elim (hc hs)
-  | some q =>
-    have hin : (emitterTrackCfg M c lo hi).inputSymbol = c.inputSymbol := rfl
-    have hwork : (fun i => (emitterTrackCfg M c lo hi).workTapeSymbols
-        (Fin.castAdd (M.k + M.k) i)) = c.workTapeSymbols := by
-      funext i
-      simp [emitterTrackCfg, Cfg.workTapeSymbols, emitterSlots]
-    have hs' : (emitterTrackCfg M c lo hi).state = some (.inl q) := by
-      simp only [emitterTrackCfg, hs, Option.map_some]
-    simp only [MultiTapeTM.step, hs', hs]
-    change ((emitterTrackTM M).tm.tr (.inl q) _ _).apply _ = _
-    dsimp only [emitterTrackTM]
-    rw [hin, hwork]
-    refine Cfg.ext rfl rfl ?_ ?_ rfl
-    · funext i
-      refine Fin.addCases ?_ ?_ i
-      · intro j; simp [emitterTrackMid, emitterTrackCfg, emitterSlots, Action.apply, -Fin.natAdd_eq_addNat]
-      · intro j
-        refine Fin.addCases ?_ ?_ j <;> intro j <;>
-          simp [emitterTrackMid, emitterTrackCfg, emitterSlots, Action.apply, -Fin.natAdd_eq_addNat]
-    · funext i
-      refine Fin.addCases ?_ ?_ i
-      · intro j; simp [emitterTrackMid, emitterTrackCfg, emitterSlots, Action.apply, -Fin.natAdd_eq_addNat]
-      · intro j
-        refine Fin.addCases ?_ ?_ j <;> intro j <;>
-          simp [emitterTrackMid, emitterTrackCfg, emitterSlots, Action.apply, -Fin.natAdd_eq_addNat]
-
-/-- The second microstep stamps every new current head, extending the
-contiguous visited interval and halting only after those stamps are complete.
-**Proof sketch.** Split the three tape banks. The source and origin tapes are unchanged;
-writing the newly reached cell in the visited bank extends its interval
-by the one-step head bound, before the stored successor state is dispatched. -/
-private lemma emitter_track_stamp (M : FinTM Bool) {x : List Bool}
-    (c : Cfg M.k Bool M.State x) (lo hi : Fin M.k → ℤ)
-    (hord : ∀ i, lo i ≤ hi i)
-    (hnear : ∀ i, lo i - 1 ≤ c.workTapePos i ∧ c.workTapePos i ≤ hi i + 1) :
-    (emitterTrackTM M).tm.step (emitterTrackMid M c lo hi) =
-      emitterTrackCfg M c (fun i => min (lo i) (c.workTapePos i))
-        (fun i => max (hi i) (c.workTapePos i)) := by
-  simp only [MultiTapeTM.step, emitterTrackMid, emitterTrackTM]
-  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
-  · funext i
-    refine Fin.addCases ?_ ?_ i
-    · intro j; simp [emitterTrackCfg, emitterSlots, Action.apply, -Fin.natAdd_eq_addNat]
-    · intro j
-      refine Fin.addCases ?_ ?_ j
-      · intro j
-        simpa [emitterTrackCfg, emitterSlots, Action.apply, -Fin.natAdd_eq_addNat] using
-          emitter_span_extend (lo j) (hi j) (c.workTapePos j) (hord j) (hnear j)
-      · intro j; simp [emitterTrackCfg, emitterSlots, Action.apply, -Fin.natAdd_eq_addNat]
-  · funext i
-    refine Fin.addCases ?_ ?_ i
-    · intro j; simp [emitterTrackCfg, emitterSlots, Action.apply, -Fin.natAdd_eq_addNat]
-    · intro j
-      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [emitterTrackCfg, emitterSlots, Action.apply, -Fin.natAdd_eq_addNat]
-  · simp [emitterTrackCfg, Action.apply]
-
-/-- Leftmost visited source-head position, including the initial origin. -/
-private def emitterLo (M : FinTM Bool) (x : List Bool) : ℕ → Fin M.k → ℤ
-  | 0 => fun _ => 0
-  | t + 1 => fun i => min (emitterLo M x t i)
-      ((M.tm.runFrom (M.tm.initCfg x) (t + 1)).workTapePos i)
-
-/-- Rightmost visited source-head position, including the initial origin. -/
-private def emitterHi (M : FinTM Bool) (x : List Bool) : ℕ → Fin M.k → ℤ
-  | 0 => fun _ => 0
-  | t + 1 => fun i => max (emitterHi M x t i)
-      ((M.tm.runFrom (M.tm.initCfg x) (t + 1)).workTapePos i)
-
-/-- The visited interval contains zero and the current head and has width
-at most twice the elapsed source time plus one. -/
-private lemma emitter_track_extent (M : FinTM Bool) (x : List Bool) :
-    ∀ t (i : Fin M.k), emitterLo M x t i ≤ 0 ∧ 0 ≤ emitterHi M x t i ∧
-      emitterLo M x t i ≤ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ∧
-      (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i ≤ emitterHi M x t i ∧
-      -(t : ℤ) ≤ emitterLo M x t i ∧ emitterHi M x t i ≤ t := by
-  intro t
-  induction t with
-  | zero => intro i; simp [emitterLo, emitterHi, MultiTapeTM.initCfg, Cfg.init]
-  | succ t ih =>
-    intro i
-    have hp := M.tm.workTapePos_step_le (M.tm.runFrom (M.tm.initCfg x) t) i
-    rw [abs_le, ← MultiTapeTM.runFrom_succ_eq_step'] at hp
-    have hh := ih i
-    dsimp only [emitterLo, emitterHi]
-    push_cast
-    omega
-
-/-- Every cell written by the source lies inside its visited interval.
-The claim concerns actual writes and allows arbitrary blank cells inside it.
-**Proof sketch.** Induct over the actual source trace. An unwritten cell retains its old
-support bound; a newly written cell is the previous head, already in the
-previous interval and therefore in the enlarged interval. -/
-private lemma emitter_track_support (M : FinTM Bool) (x : List Bool) :
-    ∀ t (i : Fin M.k) (z : ℤ),
-      ¬(emitterLo M x t i ≤ z ∧ z ≤ emitterHi M x t i) →
-        (M.tm.runFrom (M.tm.initCfg x) t).workTapes i z = none := by
-  intro t
-  induction t with
-  | zero => intro i z hz; rfl
-  | succ t ih =>
-    intro i z hz
-    have hb := emitter_track_extent M x t i
-    have hz' : ¬(emitterLo M x t i ≤ z ∧ z ≤ emitterHi M x t i) := by
-      dsimp only [emitterLo, emitterHi] at hz
-      omega
-    have hne : z ≠ (M.tm.runFrom (M.tm.initCfg x) t).workTapePos i := by omega
-    rw [MultiTapeTM.runFrom_succ_eq_step']
-    unfold MultiTapeTM.step
-    cases hs : (M.tm.runFrom (M.tm.initCfg x) t).state with
-    | none => exact ih i z hz'
-    | some q =>
-      dsimp only [Action.apply]
-      cases hw : ((M.tm.tr q (M.tm.runFrom (M.tm.initCfg x) t).inputSymbol
-        (M.tm.runFrom (M.tm.initCfg x) t).workTapeSymbols).workTapes i).1
-      · exact ih i z hz'
-      · dsimp only
-        rw [Function.update_of_ne hne]
-        exact ih i z hz'
-
-/-- The singleton origin marker is the zero-width source trace's visited span. -/
-private lemma emitter_span_zero : emitterSpan 0 0 = bufferTape [true] := by
-  funext z
-  by_cases hz : z = 0
-  · subst z; rfl
-  · have hspan : ¬(0 ≤ z ∧ z ≤ 0) := by omega
-    by_cases hn : 0 ≤ z
-    · have hlen : [true].length ≤ z.toNat := by simp; omega
-      simp [emitterSpan, hspan, bufferTape, hn, List.getElem?_eq_none hlen]; omega
-    · simp [emitterSpan, hspan, bufferTape, hn]
-
-/-- A single native initialization step installs both origin markers while
-leaving source work blank, the source input head at one, and output empty. -/
-private lemma emitter_track_initial (M : FinTM Bool) (x : List Bool) :
-    (emitterTrackTM M).tm.runFrom ((emitterTrackTM M).tm.initCfg x) 1 =
-      emitterTrackCfg M (M.tm.initCfg x) (fun _ => 0) (fun _ => 0) := by
-  change (emitterTrackTM M).tm.step ((emitterTrackTM M).tm.initCfg x) = _
-  simp only [MultiTapeTM.step, MultiTapeTM.initCfg, Cfg.init, emitterTrackTM]
-  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ rfl
-  · funext i
-    refine Fin.addCases ?_ ?_ i
-    · intro j; simp [Action.apply, emitterTrackCfg, emitterSlots, -Fin.natAdd_eq_addNat]
-    · intro j
-      refine Fin.addCases ?_ ?_ j <;> intro j <;>
-        simpa only [Action.apply, emitterTrackCfg, emitterSlots, Fin.addCases_left,
-          Fin.addCases_right, emitter_span_zero, bufferTape_nil] using
-            (bufferTape_append [] true).symm
-  · funext i
-    refine Fin.addCases ?_ ?_ i
-    · intro j; simp [Action.apply, emitterTrackCfg, emitterSlots, -Fin.natAdd_eq_addNat]
-    · intro j
-      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [Action.apply, emitterTrackCfg, emitterSlots, -Fin.natAdd_eq_addNat]
-
-/-- The tracked machine has the exact source configuration after two native
-steps per source step, plus initialization. Its interval markers record the
-actual trace, including after the source has halted.
-**Proof sketch.** Initialization marks the origins. For a live source, its
-action moves all three corresponding heads together, then the stamp expands
-the visited interval by at most one cell. A halted source and its tracked
-image are both absorbing, and the already-contained head changes neither bound. -/
-private lemma emitter_track_run (M : FinTM Bool) (x : List Bool) :
-    ∀ t, (emitterTrackTM M).tm.runFrom ((emitterTrackTM M).tm.initCfg x) (1 + 2 * t) =
-      emitterTrackCfg M (M.tm.runFrom (M.tm.initCfg x) t) (emitterLo M x t) (emitterHi M x t) := by
-  intro t
-  induction t with
-  | zero => simpa [emitterLo, emitterHi] using emitter_track_initial M x
-  | succ t ih =>
-    let c := M.tm.runFrom (M.tm.initCfg x) t
-    have hb := emitter_track_extent M x t
-    have hnext : M.tm.runFrom (M.tm.initCfg x) (t + 1) = M.tm.step c := by
-      rw [MultiTapeTM.runFrom_succ_eq_step']
-    rw [show 1 + 2 * (t + 1) = (1 + 2 * t) + 2 by omega, MultiTapeTM.runFrom_add, ih]
-    cases hs : c.state with
-    | none =>
-      have hl : emitterLo M x (t + 1) = emitterLo M x t := by
-        funext i
-        simp only [emitterLo, MultiTapeTM.runFrom_succ_eq_step']
-        change min (emitterLo M x t i) ((M.tm.step c).workTapePos i) = _
-        rw [MultiTapeTM.step_of_halt hs, min_eq_left (hb i).2.2.1]
-      have hr : emitterHi M x (t + 1) = emitterHi M x t := by
-        funext i
-        simp only [emitterHi, MultiTapeTM.runFrom_succ_eq_step']
-        change max (emitterHi M x t i) ((M.tm.step c).workTapePos i) = _
-        rw [MultiTapeTM.step_of_halt hs, max_eq_left (hb i).2.2.2.1]
-      have hhalt : (emitterTrackCfg M c (emitterLo M x t) (emitterHi M x t)).state = none := by
-        simp only [emitterTrackCfg, hs, Option.map_none]
-      rw [hl, hr, hnext]
-      change (emitterTrackTM M).tm.runFrom (emitterTrackCfg M c _ _) 2 = emitterTrackCfg M (M.tm.step c) _ _
-      rw [MultiTapeTM.runFrom_of_halt _ hhalt, MultiTapeTM.step_of_halt hs]
-    | some q =>
-      have hlive : c.state ≠ none := by rw [hs]; simp
-      have hnear (i : Fin M.k) : emitterLo M x t i - 1 ≤ (M.tm.step c).workTapePos i ∧
-          (M.tm.step c).workTapePos i ≤ emitterHi M x t i + 1 := by
-        have hm := M.tm.workTapePos_step_le c i
-        rw [abs_le] at hm
-        have hh := hb i
-        dsimp only [c] at hm ⊢
-        omega
-      change (emitterTrackTM M).tm.step ((emitterTrackTM M).tm.step (emitterTrackCfg M c _ _)) = _
-      rw [emitter_track_action M c _ _ hlive,
-        emitter_track_stamp M (M.tm.step c) _ _ (fun i => by have hh := hb i; omega) hnear]
-      dsimp only [emitterLo, emitterHi]
-      rw [hnext]
-
-/-- The trace markers cost exactly two native steps per source step and one
-initialization step. The output and halting judgment are unchanged. -/
-private lemma emitter_track_computes (M : FinTM Bool) (x out : List Bool) (T : ℕ)
-    (hM : M.ComputesInTime x out T) :
-    (emitterTrackTM M).ComputesInTime x out (1 + 2 * T) := by
-  have hc := (computesInTime_iff M x out T).mp hM
-  apply (computesInTime_iff _ _ _ _).mpr
-  rw [emitter_track_run]
-  exact ⟨by simp only [emitterTrackCfg, hc.1, Option.map_none], hc.2⟩
-
-/-- A closed visited span is the cleaner's half-open interval with exactly
-one cell for each visited integer, including both endpoints. -/
-private lemma emitter_span_interval (lo hi : ℤ) (h : lo ≤ hi) :
-    emitterSpan lo hi = emitterInterval lo (hi - lo + 1).toNat := by
-  funext z
-  have hw : ((hi - lo + 1).toNat : ℤ) = hi - lo + 1 := by omega
-  have he : (lo ≤ z ∧ z ≤ hi) ↔
-      (lo ≤ z ∧ z < lo + ((hi - lo + 1).toNat : ℤ)) := by rw [hw]; omega
-  simp only [emitterSpan, emitterInterval, he]
-
-/-- Each actual source work tape, together with its tracked interval and
-origin marker, satisfies the native cleaner's full restoration contract.
-The common bound is linear in the actual elapsed source time.
-**Proof sketch.** The trace invariant gives a visited interval containing the
-head and zero, no nonblank cell outside it, and width at most `2T+1`.
-Instantiate the proved interval cleaner, whose entire three-tape endpoint is
-blank with every head zero, and absorb its cost into `6T+7`. -/
-private lemma emitter_track_clearable (M : FinTM Bool) (x w : List Bool)
-    (p : Fin (w.length + 2)) (T : ℕ) (i : Fin M.k) :
-    ∃ t, 0 < t ∧ t ≤ 6 * T + 7 ∧
-      emitterClearTM.tm.runFrom
-        (emitterClearCfg w p 0 ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
-          (emitterSpan (emitterLo M x T i) (emitterHi M x T i)) (bufferTape [true])
-          ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i)) t =
-      emitterClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
-  let lo := emitterLo M x T i
-  let hi := emitterHi M x T i
-  let h := (M.tm.runFrom (M.tm.initCfg x) T).workTapePos i
-  let width := (hi - lo + 1).toNat
-  let j := (h - lo).toNat
-  have hb := emitter_track_extent M x T i
-  have hw : (width : ℤ) = hi - lo + 1 := by dsimp only [width, hi, lo]; omega
-  have hj : (j : ℤ) = h - lo := by dsimp only [j, h, lo]; omega
-  have hwidth : width ≤ 2 * T + 1 := by dsimp only [hi, lo] at hw; omega
-  have hpos : 0 < lo + width := by dsimp only [lo, hi] at hw ⊢; omega
-  have hjlt : j < width := by dsimp only [h, lo, hi] at hw hj; omega
-  have hdata : ∀ z, ¬(lo ≤ z ∧ z < lo + width) →
-      (M.tm.runFrom (M.tm.initCfg x) T).workTapes i z = none := by
-    intro z hz
-    apply emitter_track_support M x T i z
-    dsimp only [lo, hi] at hw hz
-    omega
-  obtain ⟨t, htpos, ht, hr⟩ := emitter_clear_run w p
-    ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i) lo width j hb.1 hpos hjlt hdata
-  refine ⟨t, htpos, by omega, ?_⟩
-  have hhead : lo + j = h := by omega
-  rw [hhead] at hr
-  rw [emitter_span_interval _ _ (by have := hb; omega)]
-  exact hr
-
 /-- A phase with an absorbing return state can be cut at its actual first
 return while retaining its complete configuration endpoint.
 **Proof sketch.** Choose the least return-state visit. Absorption identifies
@@ -5445,40 +4697,6 @@ private lemma emitter_compare_first (w u v : List Bool) (p : Fin (w.length + 2))
     norm_num at hv
   exact ⟨t, hpos, ht, fun j hj b hb => hfirst j hj ⟨(2, b), hb, rfl⟩, hr⟩
 
-/-- Each tracked tape's native cleanup can dispatch at its actual positive
-first return with the exact blank endpoint, never at the analysis deadline.
-**Proof sketch.** Apply the per-tape bounded cleanup, then cut the absorbing return state
-at its first visit. The initial left-scan state proves positivity, and
-absorption preserves the complete blank endpoint. -/
-private lemma emitter_clear_first (M : FinTM Bool) (x w : List Bool)
-    (p : Fin (w.length + 2)) (T : ℕ) (i : Fin M.k) :
-    ∃ t, 0 < t ∧ t ≤ 6 * T + 7 ∧
-      (∀ j < t, (emitterClearTM.tm.runFrom
-        (emitterClearCfg w p 0 ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
-          (emitterSpan (emitterLo M x T i) (emitterHi M x T i)) (bufferTape [true])
-          ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i)) j).state ≠ some (3 : Fin 4)) ∧
-      emitterClearTM.tm.runFrom
-        (emitterClearCfg w p 0 ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
-          (emitterSpan (emitterLo M x T i) (emitterHi M x T i)) (bufferTape [true])
-          ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i)) t =
-        emitterClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0 := by
-  obtain ⟨t, _, ht, hr⟩ := emitter_track_clearable M x w p T i
-  obtain ⟨a, ha, hfirst, he⟩ := emitter_first_entry emitterClearTM.tm
-    (fun q : Fin 4 => q = 3) _ _ t (by
-      rintro z ⟨q, hz, rfl⟩
-      unfold MultiTapeTM.step
-      rw [hz]
-      change (controlAction 0 (some (3 : Fin 4))).apply z = z
-      rw [controlAction_apply, moveInputPos_zero]
-      cases z; simp_all) ⟨(3 : Fin 4), rfl, rfl⟩ hr
-  have hpos : 0 < a := by
-    by_contra h
-    have hz : a = 0 := by omega
-    have hh := congrArg Cfg.state he
-    have hv := congrArg (fun q : Option (Fin 4) => q.map Fin.val) hh
-    norm_num [hz, emitterClearCfg] at hv
-  exact ⟨a, hpos, ha.trans ht, fun j hj hh => hfirst j hj ⟨(3 : Fin 4), hh, rfl⟩, he⟩
-
 /-- Canonical binary words represent natural numbers injectively. This is
 used only to identify an already-completed whole-word comparison. -/
 private lemma emitter_bits_injective : Function.Injective Nat.bits := by
@@ -5490,419 +4708,6 @@ private lemma emitter_bits_injective : Function.Injective Nat.bits := by
   have he := congrArg (fun w : List Bool => w.foldr Nat.bit 0) h
   simpa only [decode] using he
 
-/-- Select a single data/visited/origin triple from the tracked bank layout. -/
-private def emitterBankSymbols {k : ℕ} (work : Fin (k + (k + k)) → Option Bool)
-    (i : Fin k) (j : Fin 3) : Option Bool :=
-  match j.val with
-  | 0 => work (Fin.castAdd (k + k) i)
-  | 1 => work (Fin.natAdd k (Fin.castAdd k i))
-  | _ => work (Fin.natAdd k (Fin.natAdd k i))
-
-/-- One component of simultaneous cleanup; a stopped component is stationary.
-The native input is ignored by the interval cleaner. -/
-private def emitterBankPart {k : ℕ} (q : Fin k → Option (Fin 4))
-    (work : Fin (k + (k + k)) → Option Bool) (i : Fin k) : Action 3 Bool (Fin 4) :=
-  match q i with
-  | none => controlAction 0 none
-  | some s => emitterClearTM.tm.tr s none (emitterBankSymbols work i)
-
-/-- Run all interval cleaners simultaneously on disjoint triples. The finite
-control stores every cleaner's state; no source-time clock is present. -/
-private def emitterBankTM (k : ℕ) : FinTM Bool where
-  k := k + (k + k)
-  State := Fin k → Option (Fin 4)
-  tm := {
-    q₀ := fun _ => some 0
-    tr := fun q _ work =>
-      let a := emitterBankPart q work
-      ⟨0, emitterSlots (fun i => (a i).workTapes 0)
-        (fun i => (a i).workTapes 1) (fun i => (a i).workTapes 2),
-        none, some (fun i => (a i).state)⟩ }
-
-/-- Reassemble cleaner configurations as a full bank while retaining an
-arbitrary physical input-head position and empty physical output. -/
-private def emitterBankCfg {k : ℕ} {w : List Bool} (p : Fin (w.length + 2))
-    (c : Fin k → Cfg 3 Bool (Fin 4) w) : Cfg (emitterBankTM k).k Bool (emitterBankTM k).State w :=
-  ⟨some (fun i => (c i).state), p,
-    emitterSlots (fun i => (c i).workTapes 0)
-      (fun i => (c i).workTapes 1) (fun i => (c i).workTapes 2),
-    emitterSlots (fun i => (c i).workTapePos 0)
-      (fun i => (c i).workTapePos 1) (fun i => (c i).workTapePos 2), []⟩
-
-/-- Selecting a bank component recovers precisely that cleaner's transition,
-including all three independently positioned work heads. -/
-private lemma emitterBank_part {k : ℕ} {w : List Bool} (p : Fin (w.length + 2))
-    (c : Fin k → Cfg 3 Bool (Fin 4) w) (i : Fin k) :
-    emitterBankPart (fun i => (c i).state) (emitterBankCfg p c).workTapeSymbols i =
-      match (c i).state with
-      | none => controlAction 0 none
-      | some q => emitterClearTM.tm.tr q (c i).inputSymbol (c i).workTapeSymbols := by
-  have hw : emitterBankSymbols (emitterBankCfg p c).workTapeSymbols i =
-      (c i).workTapeSymbols := by
-    funext j
-    fin_cases j <;>
-      simp [emitterBankSymbols, emitterBankCfg, emitterSlots, Cfg.workTapeSymbols,
-        -Fin.natAdd_eq_addNat]
-  unfold emitterBankPart
-  rw [hw]
-  dsimp only
-  cases hs : (c i).state <;> rfl
-
-/-- A bank step is exactly one step of every component cleaner.
-**Proof sketch.** Project the disjoint data, visited-marker, and origin banks.
-Each selected action is the corresponding cleaner action; a stopped component
-performs the identity. The bank itself preserves the physical input and output. -/
-private lemma emitterBank_step {k : ℕ} {w : List Bool} (p : Fin (w.length + 2))
-    (c : Fin k → Cfg 3 Bool (Fin 4) w) :
-    (emitterBankTM k).tm.step (emitterBankCfg p c) =
-      emitterBankCfg p (fun i => emitterClearTM.tm.step (c i)) := by
-  have ha : emitterBankPart (fun i => (c i).state) (emitterBankCfg p c).workTapeSymbols =
-      fun i => match (c i).state with
-        | none => controlAction 0 none
-        | some q => emitterClearTM.tm.tr q (c i).inputSymbol (c i).workTapeSymbols := by
-    funext i
-    exact emitterBank_part p c i
-  unfold MultiTapeTM.step
-  change ((emitterBankTM k).tm.tr (fun i => (c i).state) _ _).apply _ = _
-  dsimp only [emitterBankTM]
-  rw [ha]
-  refine Cfg.ext ?_ (moveInputPos_zero _) ?_ ?_ rfl
-  · dsimp only [Action.apply, emitterBankCfg]
-    congr 1
-    funext i
-    cases hs : (c i).state <;> simp [emitterBankCfg, MultiTapeTM.step, hs, controlAction, Action.apply]
-  · funext j
-    refine Fin.addCases ?_ ?_ j
-    · intro i
-      cases hs : (c i).state <;>
-        simp [emitterBankCfg, emitterSlots, MultiTapeTM.step, hs, controlAction, Action.apply,
-          -Fin.natAdd_eq_addNat]
-    · intro j
-      refine Fin.addCases ?_ ?_ j <;> intro i
-      all_goals cases hs : (c i).state <;>
-        simp [emitterBankCfg, emitterSlots, MultiTapeTM.step, hs, controlAction, Action.apply,
-          -Fin.natAdd_eq_addNat]
-  · funext j
-    refine Fin.addCases ?_ ?_ j
-    · intro i
-      cases hs : (c i).state <;>
-        simp [emitterBankCfg, emitterSlots, MultiTapeTM.step, hs, controlAction, Action.apply,
-          -Fin.natAdd_eq_addNat]
-    · intro j
-      refine Fin.addCases ?_ ?_ j <;> intro i
-      all_goals cases hs : (c i).state <;>
-        simp [emitterBankCfg, emitterSlots, MultiTapeTM.step, hs, controlAction, Action.apply,
-          -Fin.natAdd_eq_addNat]
-
-/-- A simultaneous bank run projects to the complete run of each cleaner. -/
-private lemma emitterBank_run {k : ℕ} {w : List Bool} (p : Fin (w.length + 2))
-    (c : Fin k → Cfg 3 Bool (Fin 4) w) (t : ℕ) :
-    (emitterBankTM k).tm.runFrom (emitterBankCfg p c) t =
-      emitterBankCfg p (fun i => emitterClearTM.tm.runFrom (c i) t) := by
-  induction t with
-  | zero => rfl
-  | succ t ih =>
-    simp only [MultiTapeTM.runFrom_succ_eq_step', ih, emitterBank_step]
-
-/-- A returned interval cleaner preserves every field on further steps. -/
-private lemma emitterClear_fixed {w : List Bool} (z : Cfg 3 Bool (Fin 4) w)
-    (hz : z.state = some 3) : emitterClearTM.tm.step z = z := by
-  unfold MultiTapeTM.step
-  rw [hz]
-  change (controlAction 0 (some (3 : Fin 4))).apply z = z
-  rw [controlAction_apply, moveInputPos_zero]
-  cases z
-  simp_all
-
-/-- Simultaneous cleanup clears the entire tracked source bank, not just one
-tape. All three banks become blank with every work head at zero; the physical
-input head and output are unchanged. The deadline is only an analysis bound.
-**Proof sketch.** Project the bank run to its independent interval cleaners.
-Each finishes within `6T+7`, where `T` is elapsed source time. Its return is
-absorbing, so its full blank endpoint persists to that common deadline.
-The argument also covers a source with no work tapes. -/
-private lemma emitterBank_clear (M : FinTM Bool) (x w : List Bool)
-    (p : Fin (w.length + 2)) (T : ℕ) :
-    (emitterBankTM M.k).tm.runFrom
-      (emitterBankCfg p (fun i => emitterClearCfg w p 0
-        ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
-        (emitterSpan (emitterLo M x T i) (emitterHi M x T i)) (bufferTape [true])
-        ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i))) (6 * T + 7) =
-      emitterBankCfg p (fun _ : Fin M.k =>
-        emitterClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0) := by
-  rw [emitterBank_run]
-  apply congrArg (emitterBankCfg p)
-  funext i
-  obtain ⟨t, _, ht, hr⟩ := emitter_track_clearable M x w p T i
-  rw [show 6 * T + 7 = t + (6 * T + 7 - t) by omega, MultiTapeTM.runFrom_add, hr]
-  exact Function.iterate_fixed (emitterClear_fixed _ rfl) _
-
-/-- A completed bank controller is absorbing on the entire configuration.
-**Proof sketch.** Every component's returned state produces a stationary,
-silent action. Project the three disjoint tape banks to see that no tape or
-head changes, and retain the completed vector of control states. -/
-private lemma emitterBank_fixed {k : ℕ} {w : List Bool}
-    (z : Cfg (emitterBankTM k).k Bool (emitterBankTM k).State w)
-    (hz : z.state = some (fun _ => some (3 : Fin 4))) :
-    (emitterBankTM k).tm.step z = z := by
-  unfold MultiTapeTM.step
-  rw [hz]
-  refine Cfg.ext hz.symm (moveInputPos_zero _) ?_ ?_ ?_
-  · funext j
-    refine Fin.addCases ?_ ?_ j
-    · intro i; simp [emitterBankTM, emitterBankPart, emitterClearTM, emitterSlots,
-        Action.apply, controlAction, -Fin.natAdd_eq_addNat]
-    · intro j
-      refine Fin.addCases ?_ ?_ j <;> intro i <;>
-        simp [emitterBankTM, emitterBankPart, emitterClearTM, emitterSlots,
-          Action.apply, controlAction, -Fin.natAdd_eq_addNat]
-  · funext j
-    refine Fin.addCases ?_ ?_ j
-    · intro i; simp [emitterBankTM, emitterBankPart, emitterClearTM, emitterSlots,
-        Action.apply, controlAction, -Fin.natAdd_eq_addNat]
-    · intro j
-      refine Fin.addCases ?_ ?_ j <;> intro i <;>
-        simp [emitterBankTM, emitterBankPart, emitterClearTM, emitterSlots,
-          Action.apply, controlAction, -Fin.natAdd_eq_addNat]
-  · simp [emitterBankTM, Action.apply]
-
-/-- The complete bank can dispatch at the first observed all-returned state,
-with the exact blank endpoint. A zero-tape bank may return at time zero; the
-surrounding phase must still supply the body's positive transition. -/
-private lemma emitterBank_first (M : FinTM Bool) (x w : List Bool)
-    (p : Fin (w.length + 2)) (T : ℕ) :
-    ∃ t ≤ 6 * T + 7,
-      (∀ j < t, ((emitterBankTM M.k).tm.runFrom
-        (emitterBankCfg p (fun i => emitterClearCfg w p 0
-          ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
-          (emitterSpan (emitterLo M x T i) (emitterHi M x T i)) (bufferTape [true])
-          ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i))) j).state ≠
-            some (fun _ => some (3 : Fin 4))) ∧
-      (emitterBankTM M.k).tm.runFrom
-        (emitterBankCfg p (fun i => emitterClearCfg w p 0
-          ((M.tm.runFrom (M.tm.initCfg x) T).workTapes i)
-          (emitterSpan (emitterLo M x T i) (emitterHi M x T i)) (bufferTape [true])
-          ((M.tm.runFrom (M.tm.initCfg x) T).workTapePos i))) t =
-        emitterBankCfg p (fun _ : Fin M.k =>
-          emitterClearCfg w p 3 (fun _ => none) (fun _ => none) (fun _ => none) 0) := by
-  exact catalogFirstEntry (emitterBankTM M.k).tm (fun _ => some (3 : Fin 4))
-    _ _ (6 * T + 7) emitterBank_fixed rfl (emitterBank_clear M x w p T)
-
-/-- After the source's actual halt, move to the native right input boundary
-without altering its output or work tapes. The initial positive move handles
-both blanks correctly, including the two distinct blanks of an empty input. -/
-private def emitterRightTM (M : FinTM Bool) : FinTM Bool where
-  k := M.k
-  State := M.State ⊕ Bool
-  tm := {
-    q₀ := .inl M.tm.q₀
-    tr := fun q inp work => match q with
-      | .inl q =>
-        let a := M.tm.tr q inp work
-        { a with state := some ((a.state.map Sum.inl).getD (.inr false)) }
-      | .inr false => controlAction .pos (some (.inr true))
-      | .inr true => match inp with
-        | some _ => controlAction .pos (some (.inr true))
-        | none => controlAction 0 none }
-
-/-- Before the right-boundary scan, the entire source configuration is
-preserved, with its halt replaced by a live administrative state. -/
-private def emitterRightCfg (M : FinTM Bool) {x : List Bool}
-    (c : Cfg M.k Bool M.State x) : Cfg M.k Bool (emitterRightTM M).State x :=
-  ⟨some ((c.state.map Sum.inl).getD (.inr false)), c.inputPos,
-    c.workTapes, c.workTapePos, c.output⟩
-
-/-- The wrapper follows each genuine source transition exactly, including its
-halting emission; only the successor control encoding changes. -/
-private lemma emitter_right_step (M : FinTM Bool) {x : List Bool}
-    (c : Cfg M.k Bool M.State x) (hc : c.state ≠ none) :
-    (emitterRightTM M).tm.step (emitterRightCfg M c) = emitterRightCfg M (M.tm.step c) := by
-  cases hs : c.state with
-  | none => exact False.elim (hc hs)
-  | some q =>
-    have hstate : (emitterRightCfg M c).state = some (.inl q) := by
-      simp only [emitterRightCfg, hs, Option.map_some, Option.getD_some]
-    simp only [MultiTapeTM.step, hstate, hs]
-    rfl
-
-/-- The right-boundary wrapper simulates exactly up to the actual source halt.
-No bound is substituted for the halting transition. -/
-private lemma emitter_right_run (M : FinTM Bool) {x : List Bool}
-    (c : Cfg M.k Bool M.State x) (t : ℕ)
-    (hlive : ∀ j < t, (M.tm.runFrom c j).state ≠ none) :
-    (emitterRightTM M).tm.runFrom (emitterRightCfg M c) t =
-      emitterRightCfg M (M.tm.runFrom c t) := by
-  induction t with
-  | zero => rfl
-  | succ t ih =>
-    rw [MultiTapeTM.runFrom_succ_eq_step', ih (fun j hj => hlive j (by omega)),
-      emitter_right_step M _ (hlive t (by omega)), MultiTapeTM.runFrom_succ_eq_step']
-
-/-- A rightward scan configuration carries the completed source data and
-output verbatim; its physical input position is the only moving field. -/
-private def emitterRightScan (M : FinTM Bool) {x : List Bool}
-    (c : Cfg M.k Bool M.State x) (q : Option Bool) (j : ℕ) (hj : j ≤ x.length) :
-    Cfg M.k Bool (emitterRightTM M).State x :=
-  ⟨q.map Sum.inr, ⟨j + 1, by omega⟩, c.workTapes, c.workTapePos, c.output⟩
-
-/-- From any interior position, the native scan reaches the right blank and
-halts silently. The scan does not confuse a blank work cell with an input end.
-**Proof sketch.** Induct on the number of remaining native input cells. A live
-cell costs one right move; the right blank costs the final silent halt. -/
-private lemma emitter_right_scan (M : FinTM Bool) {x : List Bool}
-    (c : Cfg M.k Bool M.State x) :
-    ∀ r j (hj : j ≤ x.length), j + r = x.length →
-      (emitterRightTM M).tm.runFrom (emitterRightScan M c (some true) j hj) (r + 1) =
-        emitterRightScan M c none x.length (le_refl _) := by
-  intro r
-  induction r with
-  | zero =>
-    intro j hj he
-    have hje : j = x.length := by omega
-    subst j
-    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
-    have hin : (emitterRightScan M c (some true) x.length (le_refl _)).inputSymbol = none := by
-      simp [emitterRightScan, Cfg.inputSymbol]
-    simp only [MultiTapeTM.step, emitterRightScan, Option.map_some]
-    change (match (emitterRightScan M c (some true) x.length (le_refl _)).inputSymbol with
-      | some _ => controlAction .pos (some (Sum.inr true))
-      | none => controlAction 0 none).apply _ = _
-    rw [hin, controlAction_apply, moveInputPos_zero]
-    rfl
-  | succ r ih =>
-    intro j hj he
-    have hjlt : j < x.length := by omega
-    have hin : (emitterRightScan M c (some true) j hj).inputSymbol = some (x[j]'hjlt) :=
-      inputSymbolInner j (by simp [emitterRightScan, Nat.add_comm]) hjlt
-    have hs : (emitterRightTM M).tm.step (emitterRightScan M c (some true) j hj) =
-        emitterRightScan M c (some true) (j + 1) (by omega) := by
-      simp only [MultiTapeTM.step, emitterRightScan, Option.map_some]
-      change (match (emitterRightScan M c (some true) j hj).inputSymbol with
-        | some _ => controlAction .pos (some (Sum.inr true))
-        | none => controlAction 0 none).apply _ = _
-      rw [hin, controlAction_apply]
-      refine Cfg.ext rfl ?_ rfl rfl rfl
-      exact moveInputPos_pos_of_ne_right _ (by simp; omega)
-    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
-    exact ih (j + 1) (by omega) (by omega)
-
-/-- The completed source enters the right scan by a positive native move.
-Clamping guarantees a position at least one even on empty input.
-**Proof sketch.** The mandatory positive move reaches a position of at least one.
-Apply the right-scan induction to its remaining distance; neither that move
-nor the scan changes the completed source work tapes or output. -/
-private lemma emitter_right_finish (M : FinTM Bool) {x : List Bool}
-    (c : Cfg M.k Bool M.State x) (hc : c.state = none) :
-    ∃ t ≤ x.length + 2,
-      (emitterRightTM M).tm.runFrom (emitterRightCfg M c) t =
-        emitterRightScan M c none x.length (le_refl _) := by
-  let p := moveInputPos c.inputPos .pos
-  have hp : 1 ≤ p.val := by
-    dsimp [p, moveInputPos]
-    split <;> simp_all <;> omega
-  let j := p.val - 1
-  have hj : j ≤ x.length := by have := p.isLt; dsimp [j]; omega
-  have hs : (emitterRightTM M).tm.step (emitterRightCfg M c) =
-      emitterRightScan M c (some true) j hj := by
-    simp only [MultiTapeTM.step, emitterRightCfg, hc, Option.map_none, Option.getD_none]
-    change (controlAction .pos (some (Sum.inr true))).apply _ = _
-    rw [controlAction_apply]
-    refine Cfg.ext rfl ?_ rfl rfl rfl
-    apply Fin.ext
-    change p.val = j + 1
-    dsimp [j]; omega
-  refine ⟨1 + (x.length - j + 1), by omega, ?_⟩
-  rw [MultiTapeTM.runFrom_add, show (emitterRightTM M).tm.runFrom (emitterRightCfg M c) 1 = _ from hs]
-  exact emitter_right_scan M c (x.length - j) j hj (by omega)
-
-/-- Right-boundary normalization preserves the entire completed source
-configuration, not just its output. This retains the tracked cleanup witnesses.
-**Proof sketch.** Choose the actual first source halt. The native right scan
-then costs at most `|x|+2`; absorb only the completed run to the advertised
-budget. Source absorption identifies its work tapes with those at the original
-deadline, including when that deadline exceeds the actual halt. -/
-private lemma emitter_right_endpoint (M : FinTM Bool) (x : List Bool) (T : ℕ)
-    (hc : (M.tm.runFrom (M.tm.initCfg x) T).state = none) :
-    (emitterRightTM M).tm.runFrom ((emitterRightTM M).tm.initCfg x) (T + x.length + 2) =
-      emitterRightScan M (M.tm.runFrom (M.tm.initCfg x) T) none x.length (le_refl _) := by
-  classical
-  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T, hc⟩
-  let t := Nat.find hex
-  let c := M.tm.runFrom (M.tm.initCfg x) t
-  have ht : t ≤ T := Nat.find_min' hex hc
-  have hs : c.state = none := Nat.find_spec hex
-  have hcT : M.tm.runFrom (M.tm.initCfg x) T = c := by
-    rw [show T = t + (T - t) by omega, MultiTapeTM.runFrom_add,
-      MultiTapeTM.runFrom_of_halt _ hs]
-  have hi : (emitterRightTM M).tm.initCfg x = emitterRightCfg M (M.tm.initCfg x) := rfl
-  have hr := emitter_right_run M (M.tm.initCfg x) t (fun j hj => Nat.find_min hex hj)
-  obtain ⟨r, hrle, hfinish⟩ := emitter_right_finish M c hs
-  have hrun : (emitterRightTM M).tm.runFrom ((emitterRightTM M).tm.initCfg x) (t + r) =
-      emitterRightScan M c none x.length (le_refl _) := by
-    rw [hi, MultiTapeTM.runFrom_add, hr]
-    exact hfinish
-  have hle : t + r ≤ T + x.length + 2 := by omega
-  rw [show T + x.length + 2 = (t + r) + (T + x.length + 2 - (t + r)) by omega,
-    MultiTapeTM.runFrom_add, hrun, MultiTapeTM.runFrom_of_halt _ (by rfl), hcT]
-
-/-- Every timed computation can finish at the right input boundary with only
-linear extra time, preserving the source's complete output. -/
-private lemma emitter_right_computes (M : FinTM Bool) (x out : List Bool) (T : ℕ)
-    (hM : M.ComputesInTime x out T) :
-    (emitterRightTM M).ComputesInTime x out (T + x.length + 2) ∧
-      ((emitterRightTM M).tm.runFrom ((emitterRightTM M).tm.initCfg x)
-        (T + x.length + 2)).inputPos.val = x.length + 1 := by
-  have hc := (computesInTime_iff M x out T).mp hM
-  have he := emitter_right_endpoint M x T hc.1
-  constructor
-  · apply (computesInTime_iff _ _ _ _).mpr
-    rw [he]
-    exact ⟨rfl, hc.2⟩
-  · rw [he]
-    rfl
-
-/-- A captured, tracked evaluator has an actual positive first return with
-its full trace banks, complete output buffer, and candidate head at the right
-boundary. It emits nothing to the physical output and fixes the physical input
-head at one. The entry is the canonical prepared state-word configuration by
-`emitter_eval_initial`. This is a phase contract, not the complete split-search body.
-**Proof sketch.** Track every source step, then normalize its virtual input
-head after its actual halt. Capture this composite through its first completed
-source state. Absorption equates that endpoint with the exact tracked trace at
-the advertised deadline; the virtual right boundary fixes the candidate head
-even for the empty word. The source deadline is never used as a native clock. -/
-private lemma emitter_prepared_eval_first (M : FinTM Bool) (w s out : List Bool) (T : ℕ)
-    (hM : M.ComputesInTime s out T) :
-    let R := emitterRightTM (emitterTrackTM M)
-    ∃ t, 0 < t ∧ t ≤ 1 + 2 * T + s.length + 2 ∧
-      (∀ j < t, ((emitterEvalTM R).tm.runFrom
-        (emitterEvalCfg (w := w) R (R.tm.initCfg s) true 1) j).state ≠ some (.inr ())) ∧
-      (emitterEvalTM R).tm.runFrom
-        (emitterEvalCfg (w := w) R (R.tm.initCfg s) true 1) t =
-          emitterEvalCfg (w := w) R
-            (emitterRightScan (emitterTrackTM M)
-              (emitterTrackCfg M (M.tm.runFrom (M.tm.initCfg s) T)
-                (emitterLo M s T) (emitterHi M s T)) none s.length (le_refl _)) false 1 := by
-  dsimp only
-  let R := emitterRightTM (emitterTrackTM M)
-  let D := 1 + 2 * T + s.length + 2
-  have htrack := emitter_track_computes M s out T hM
-  have hright := (emitter_right_computes (emitterTrackTM M) s out (1 + 2 * T) htrack).1
-  obtain ⟨t, ht, b, _, hh, _, hfirst, hr⟩ := emitter_eval_first R w s out D hright
-  have hpos : 0 < t := by
-    by_contra hn
-    have ht0 : t = 0 := by omega
-    simp [ht0, MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg, Cfg.init] at hh
-  have habs : R.tm.runFrom (R.tm.initCfg s) D = R.tm.runFrom (R.tm.initCfg s) t := by
-    rw [show D = t + (D - t) by omega, MultiTapeTM.runFrom_add,
-      MultiTapeTM.runFrom_of_halt _ hh]
-  have hend := emitter_right_endpoint (emitterTrackTM M) s (1 + 2 * T)
-    ((computesInTime_iff _ _ _ _).mp htrack).1
-  rw [emitter_track_run] at hend
-  refine ⟨t, hpos, ht, hfirst, ?_⟩
-  rw [hr, ← habs, hend]
-  rfl
-
 /-- Comparing entire canonical binary words is exactly the width equation
 on every candidate within the native input. This includes two empty words. -/
 private lemma emitter_binary_check (f : ℕ → ℕ) (w s : List Bool)
@@ -5926,33 +4731,6 @@ private lemma emitter_width_budget (f : ℕ → ℕ) (E : FinTM Bool)
   refine ⟨he, ?_, hTE hs⟩
   simpa only [hout] using E.tm.output_length_le s (TE s.length)
 
-/-- The arbitrary width evaluator has a positive observed return within the
-round's envelope, retaining its tracked work and exact captured output.
-**Proof sketch.** Apply prepared evaluation to the actual candidate with its
-own deadline. Only afterward use monotonicity and the candidate-length
-invariant to enlarge the analysis bound. Neither bound occurs in a transition. -/
-private lemma emitter_width_eval_first (f : ℕ → ℕ) (E : FinTM Bool)
-    (TE : ℕ → ℕ) (hTE : Monotone TE)
-    (hE : E.ComputesFunInTime (fun s => Nat.bits (f s.length)) TE)
-    (w s : List Bool) (hs : s.length ≤ w.length + 1) :
-    let R := emitterRightTM (emitterTrackTM E)
-    ∃ t, 0 < t ∧ t ≤ 3 * (TE (w.length + 1) + w.length + 2) ∧
-      (∀ j < t, ((emitterEvalTM R).tm.runFrom
-        (emitterEvalCfg (w := w) R (R.tm.initCfg s) true 1) j).state ≠ some (.inr ())) ∧
-      (emitterEvalTM R).tm.runFrom
-        (emitterEvalCfg (w := w) R (R.tm.initCfg s) true 1) t =
-          emitterEvalCfg (w := w) R
-            (emitterRightScan (emitterTrackTM E)
-              (emitterTrackCfg E (E.tm.runFrom (E.tm.initCfg s) (TE s.length))
-                (emitterLo E s (TE s.length)) (emitterHi E s (TE s.length)))
-              none s.length (le_refl _)) false 1 := by
-  dsimp only
-  obtain ⟨t, hp, ht, hi, hr⟩ :=
-    emitter_prepared_eval_first E w s (Nat.bits (f s.length)) (TE s.length) (hE s)
-  refine ⟨t, hp, ?_, hi, hr⟩
-  have hm := hTE hs
-  omega
-
 /-! **Emitter P2 implementation.** The generic relocation layer below is
 reimplemented from batch L's `emCall` family in `Build/Loop.lean`, per the
 private-harvest policy. It preserves inactive storage and follows observed

base-commit: 5588628cbbddea9546f616907364b608e15557fd
-- 
2.51.1

From de1036e6a3eddd870ba99b16ee069558d86b7113 Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Fri, 9 Oct 2026 16:32:49 -0300
Subject: [PATCH 2/2] Retrofit RB2: reuse Encoding lemmas within freeze and
 refresh status notes

---
 .../TuringMachine/Build/Primitives.lean       | 72 ++++++++-----------
 1 file changed, 28 insertions(+), 44 deletions(-)

diff --git a/TCSlib/Complexity/TuringMachine/Build/Primitives.lean b/TCSlib/Complexity/TuringMachine/Build/Primitives.lean
index c1f48adba375ddb51ac72783356dbe7ead3b89f2..406229dbeba4dd7a2b38a10132cf02b0a3c78f33 100644
--- a/TCSlib/Complexity/TuringMachine/Build/Primitives.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/Primitives.lean
@@ -64,11 +64,10 @@ P10's narrowing is recorded, and result-bearing search is now
   Cambridge University Press, 2009. (§1.2–§1.4: all entries are the
   folklore tape subroutines of the textbook's simulation arguments.)
 
-**Implementation note (batch P, partial).** The first eleven targets in the
-batch brief's fill order are now proved. The four continuation targets are
-`pairLenCheck`, `stripLast`, `pairMapSnd`, and `splitSolve`; their audited
-statements and admissions remain unchanged. The original spec-phase prose
-above and on the contracts is retained as the audit record. The length
+**Implementation note (batch P).** The first eleven targets in the batch
+brief's fill order and the four continuation targets `pairLenCheck`,
+`stripLast`, `pairMapSnd`, and `splitSolve` are proved. The original spec-phase
+prose above and on the contracts is retained as the audit record. The length
 counter is obtained from the public `Complexity.timeConstructible_id`, whose
 proved machine implements precisely the sketched amortized counter. The three
 extractors share one private buffered parser, so suffix-only extraction also
@@ -77,9 +76,8 @@ is unchanged. The fixed-width incrementer adapts the enumerator's carry
 semantics to two native-input scans, validating before physical emission.
 
 
-**Implementation note (batch P2, partial).** The threaded length checker and
-marker stripper are now proved; the threaded map and split search remain the
-unchanged continuation frontier. The length checker composes the existing
+**Implementation note (batch P2).** The threaded length checker, marker stripper,
+threaded map, and split search are proved. The length checker composes the existing
 buffered first extractor with the unary generator, captures the result with
 `capture_run`, then reparses and counts down on the native payload. Malformed
 inputs emit only `[false]`. The marker stripper first guards on a valid
@@ -88,25 +86,25 @@ whole original encoding, erases its final marker/false-run, and replays the
 retained encoding. The guard is complete before any physical output. Both
 routes reuse the in-file parser/scan invariant patterns and proved public
 wrappers. `catalogPayload_computes` supplies a proved relocated-simulation
-component for the next target, with its time evaluated at the actual suffix
-length; the retained-prefix/captured-output controller remains to be built.
+component for the threaded map, with its time evaluated at the actual suffix
+length; the retained-prefix/captured-output controller is proved below.
 
 
-**Implementation note (batch P3, partial).** The threaded map is now proved.
+**Implementation note (batch P3).** The threaded map is proved.
 `pairMapTM` captures `catalogPayload_computes` on the original physical input,
 rewinds the capture and input, validates without emission, then replays the
 original encoded prefix and captured result. `pairMap_computes` bounds this
 controller by `4 * (T n + n + 3)` and the public theorem uses coefficient 40.
 All original contract docstrings are retained as the audit record.
 
-The split-search theorem remains the unchanged admitted frontier. Its new
-private, admission-free components are the unary orbit/search bridges and
+The split-search theorem is proved. Its private components include the unary
+orbit/search bridges and
 `splitSolve_of_body`, which closes the public result only when supplied the
 actual startup and round contracts; a candidate-preserving unary-bank
 preparer; a counted source-simulation correspondence; the generator's exact
 loop endpoint; and a scratch-restoration controller with a positive first
-return and no earlier visit to its return state. These separate component
-proofs do not yet constitute a combined body or a proof of its `hround`.
+return and no earlier visit to its return state. The combined `splitBodyTM`
+and `splitBody_round` assemble these components and prove `hround`.
 -/
 
 /-! Batch P4 closure note: the split-search body is now constructed and proved.
@@ -2067,7 +2065,7 @@ private lemma catalogPayload_length (x : List Bool) :
   | none => simp
   | some p =>
     rcases p with ⟨a, b⟩
-    have hx := catalogPair_inverse x a b hd
+    have hx := Turing.eq_pairEncode_of_pairDecode x a b hd
     simp only [Option.map_some, Option.getD_some]
     rw [hx]
     simp only [pairEncode, List.length_append]
@@ -2656,12 +2654,6 @@ private lemma mapPayload_finish (M : FinTM Bool) {x : List Bool}
   simp [MultiTapeTM.step, pairMapTM, mapCfg, captureCfg, Cfg.workTapeSymbols,
     mapAction, Action.apply]
 
-/-- The encoding has exactly two symbols per first-component bit and two
-separator symbols, followed by the unmodified payload. -/
-private lemma catalogPair_length (a b : List Bool) :
-    (pairEncode a b).length = 2 * a.length + 2 + b.length := by
-  simp [pairEncode, Nat.mul_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
-
 /-- The complete controller retains the first component and appends the
 source's captured result, rejecting malformed inputs without any emission.
 **Proof sketch.** Concatenate capture/rewind, silent validation, input rewind,
@@ -2706,7 +2698,7 @@ private lemma pairMap_computes {M : FinTM Bool} {f : List Bool → List Bool}
         (mapCfg M c (some (.inr (.inl 4))) p 0 []) r =
         mapCfg M c (some (.inr (.inr (true, none)))) 1 0 [] := hr
     obtain ⟨p', hp'⟩ := mapPrefix_replay M c a b [] []
-      (by simpa using catalogPair_inverse x a b hd)
+      (by simpa using Turing.eq_pairEncode_of_pairDecode x a b hd)
     simp only [List.length_nil, Nat.zero_add, List.nil_append] at hp'
     rw [hpos] at hp'
     have hprefix : (pairMapTM M).tm.runFrom ((pairMapTM M).tm.initCfg x)
@@ -2726,7 +2718,7 @@ private lemma pairMap_computes {M : FinTM Bool} {f : List Bool → List Bool}
     have hpbound := p.isLt
     change r ≤ p.val + 2 at hrle
     have hxlen : x.length = 2 * a.length + 2 + b.length := by
-      rw [catalogPair_inverse x a b hd, catalogPair_length]
+      rw [Turing.eq_pairEncode_of_pairDecode x a b hd, Turing.length_pairEncode]
     omega
 
 /-- **C1, the threaded map combinator** (spec, fill pending; round-2
@@ -4367,27 +4359,18 @@ theorem computesFunInTime_incFixed :
       M.ComputesFunInTime (fun x => (incFixed x).getD []) fun n => c * (n + 1) := by
   exact ⟨incFixedTM, 3, incFixed_computes⟩
 
-/-! Emitter batch P checkpoint. The append-bit and unary-token contracts are
+/-! Emitter implementation. The append-bit and unary-token contracts are
 proved below with coefficients one and three. The width-parametric split
-contract remains admitted: the full native body is not yet assembled.
+contract is proved by the native `emitterP2*` controller.
 
 The `emitterSplit*` layer generalizes the in-file loop closure without any
-monotonicity assumption on the width function. The `emitterEval*`,
-`emitterCompare*`, `emitterClear*`, `emitterTrack*`, and `emitterRight*` families
-are reimplemented in this file from the A-continuation's `e3c*` templates in
+monotonicity assumption on the width function. The `emitterCompare*` family
+is reimplemented in this file from the A-continuation's `e3c*` templates in
 `ClassNP/Nondeterminism.lean` at base d7b5b6f94d28df8095165dd4dfe82fd09ba0d414.
 Those originals are unchanged and are not cited as imported privates. The
-native accepting emitter already exists here as `splitEmitTM`/`splitEmit_run`.
-
-The new `emitterBank*` product controller clears all tracked source triples
-simultaneously and dispatches on their actual completion. This supplies a
-whole-bank phase, but not the outer controller's embeddings or cleanup of
-argument/capture buffers. `emitter_width_eval_first` retains evaluation on the
-actual candidate before using monotonicity to enlarge its bound. A continuation
-must still connect those phases, prepare/evaluate the native suffix length,
-clear administrative words, restore every head, implement the positive
-past-end stall, and discharge `emitterSplit_of_body`'s literal configuration
-and strict-interior anchor contracts. No additional admissions are introduced. -/
+native accepting emitter is `splitEmitTM`/`splitEmit_run`. The controller below
+discharges `emitterSplit_of_body`'s literal configuration and strict-interior
+anchor contracts. -/
 
 /-- Width-parametric acceptance tests the exact length equation. It makes
 no monotonicity assumption on the width function. -/
@@ -4731,10 +4714,11 @@ private lemma emitter_width_budget (f : ℕ → ℕ) (E : FinTM Bool)
   refine ⟨he, ?_, hTE hs⟩
   simpa only [hout] using E.tm.output_length_le s (TE s.length)
 
-/-! **Emitter P2 implementation.** The generic relocation layer below is
-reimplemented from batch L's `emCall` family in `Build/Loop.lean`, per the
-private-harvest policy. It preserves inactive storage and follows observed
-returns, including the mandatory first action when entry equals exit. -/
+/-! **Emitter P2 implementation.** The controller below proves the
+width-parametric split contract. Its generic relocation layer is reimplemented
+from batch L's `emCall` family in `Build/Loop.lean`, per the private-harvest
+policy. It preserves inactive storage and follows observed returns, including
+the mandatory first action when entry equals exit. -/
 
 /-- Relocate an action to an arbitrary fixed set of host tape slots. The
 partial inverse selects active tapes; every inactive tape is stationary. -/
-- 
2.51.1

```

## ===== audits/evidence/retrofit-rb3.patch =====

```
From b347d72c5aa3c791896e7f3d6b93f478bc692c46 Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Fri, 9 Oct 2026 16:35:17 -0300
Subject: [PATCH 1/3] retrofit(Hardness): remove six dead private declarations

---
 TCSlib/Complexity/CookLevin/Hardness.lean | 128 +---------------------
 1 file changed, 2 insertions(+), 126 deletions(-)

diff --git a/TCSlib/Complexity/CookLevin/Hardness.lean b/TCSlib/Complexity/CookLevin/Hardness.lean
index a27121c6..262e84fc 100644
--- a/TCSlib/Complexity/CookLevin/Hardness.lean
+++ b/TCSlib/Complexity/CookLevin/Hardness.lean
@@ -892,31 +892,6 @@ private lemma clRef_apply (M : FinTM Bool) {l : ℕ} {S : Type}
             simpa only [clRefCfg, Action.apply, FinTM.tapeBlocks_buffer] using hm.1
           · intro j; simp [Action.apply, clRefCfg, a]
 
-/-- The bounded reference runner consumes one unary clock cell per source
-step. Clock exhaustion dispatches to a live return state; source halting
-does not dispatch. The initial configuration in its contract is prepared,
-not claimed to arise from native initialization without header installation. -/
-private def clRefClockTM (M : FinTM Bool) : FinTM Bool where
-  k := 1 + (1 + M.k)
-  State := (Option M.State × Bool) ⊕ Unit
-  tm := {
-    q₀ := .inl (some M.tm.q₀, true)
-    tr := fun q _ work => match q with
-      | .inr _ => FinTM.controlAction 0 (some (.inr ()))
-      | .inl (s, b) =>
-        if work (Fin.castAdd (1 + M.k) (0 : Fin 1)) = none then
-          FinTM.controlAction 0 (some (.inr ()))
-        else
-          clRefAction M (fun q b => .inl (q, b)) s b work (fun _ => (none, .pos)) }
-
-/-- Running configuration of the clocked reference component. Its clock
-head records source time, separately from any future administrative cost. -/
-private def clRefClockCfg (M : FinTM Bool) {x y : List Bool}
-    (c : Cfg M.k Bool M.State y) (b : Bool) (T t : ℕ) :
-    Cfg (clRefClockTM M).k Bool (clRefClockTM M).State x :=
-  clRefCfg M (fun q b => .inl (q, b)) c b 1
-    (fun _ : Fin 1 => FinTM.bufferTape (List.replicate T true)) (fun _ => t) []
-
 /-- Increment a little-endian binary word, extending it on overflow. -/
 private def clCountInc : List Bool → List Bool
   | [] => [true]
@@ -1142,104 +1117,14 @@ private lemma clCount_idle_run {x : List Bool} (c : Cfg 1 Bool (Fin 4) x)
   | zero => rfl
   | succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step, clCount_idle c hc, ih]
 
-/-- The complete increment reaches its result at a strictly positive
-first return, within two scans of the input counter plus two steps.
-**Proof sketch.** Minimize the first return-state occurrence before the
-proved completion time. Since that state is absorbing on the entire
-configuration, its first occurrence already has the proved final word
-and restored head. Initial carry control excludes duration zero. -/
-private lemma clCount_first (x : List Bool) (p : Fin (x.length + 2)) (w : List Bool) :
-    ∃ t ≤ 2 * w.length + 2, 0 < t ∧
-      (∀ j, j < t → (clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) j).state ≠ some (0 : Fin 4)) ∧
-      clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) t =
-        clCountCfg x 0 p 0 (clCountInc w) [] := by
-  let B := 2 * clCountCarry w + 2
-  have hfinish := clCount_run x p w
-  have hex : ∃ t, t ≤ B ∧ (clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) t).state = some (0 : Fin 4) :=
-    ⟨B, le_rfl, by rw [hfinish]; rfl⟩
-  let t := Nat.find hex
-  have ht := Nat.find_spec hex
-  have hp : 0 < t := by
-    by_contra h
-    have hz : t = 0 := by omega
-    have hs := ht.2
-    change (clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) t).state = some (0 : Fin 4) at hs
-    rw [hz, MultiTapeTM.runFrom_zero] at hs
-    norm_num [clCountCfg] at hs
-  refine ⟨t, ht.1.trans (by dsimp [B]; have := clCountCarry_le w; omega), hp, ?_, ?_⟩
-  · intro j hj hs
-    have hmin := Nat.find_min' hex (show j ≤ B ∧
-      (clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) j).state = some (0 : Fin 4) from ⟨by omega, hs⟩)
-    omega
-  · have hstay := clCount_idle_run
-      (clCountTM.tm.runFrom (clCountCfg x 1 p 0 w []) t) ht.2 (B - t)
-    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le ht.1] at hstay
-    exact hstay.symm.trans hfinish
-
 /-- The harvested tape representation is the library's canonical buffer,
 including every negative cell and both empty-word boundaries. -/
 private lemma clCountTape_eq (w : List Bool) : clCountTape w = FinTM.bufferTape w := by
   funext z
   by_cases hz : z < 0 <;> simp [clCountTape, FinTM.bufferTape, hz, show 0 ≤ z ↔ ¬z < 0 by omega]
 
-/-- Run an administrative binary-counter increment while retaining the
-entire virtual reference configuration in a disjoint bank. The finite
-control stores the source state and boundary tag throughout the call. -/
-private def clRefCountTM (M : FinTM Bool) : FinTM Bool where
-  k := 1 + (1 + M.k)
-  State := Option M.State × Bool × Fin 4
-  tm := {
-    q₀ := (some M.tm.q₀, true, 1)
-    tr := fun q inp work =>
-      FinTM.leftAction (1 + M.k) (fun s => (q.1, q.2.1, s))
-        (clCountTM.tm.tr q.2.2 inp (fun i => work (Fin.castAdd (1 + M.k) i))) }
-
-/-- A complete native counter update consumes physical time without
-advancing the represented source clock or disturbing any source tape or
-head. The counter returns canonical binary successor, with strict first
-return and an explicit sequential-scan bound.
-**Proof sketch.** Lift the proved in-place counter into the left bank.
-The right bank contains the virtual input and every source tape and head;
-the public disjoint-bank run theorem preserves that whole bank. The
-injective counter-state projection transfers the first-return property. -/
-private lemma clRefCount_first (M : FinTM Bool) {x y : List Bool}
-    (c : Cfg M.k Bool M.State y) (b : Bool) (n : ℕ) :
-    ∃ t ≤ 2 * n.bits.length + 2, 0 < t ∧
-      (∀ j, j < t →
-        ((clRefCountTM M).tm.runFrom
-          (clRefCfg M (fun s b => (s, b, (1 : Fin 4))) c b (1 : Fin (x.length + 2))
-            (fun _ : Fin 1 => FinTM.bufferTape n.bits) (fun _ => 0) []) j).state ≠
-          some (c.state, b, (0 : Fin 4))) ∧
-      (clRefCountTM M).tm.runFrom
-        (clRefCfg M (fun s b => (s, b, (1 : Fin 4))) c b (1 : Fin (x.length + 2))
-          (fun _ : Fin 1 => FinTM.bufferTape n.bits) (fun _ => 0) []) t =
-        clRefCfg M (fun s b => (s, b, (0 : Fin 4))) c b (1 : Fin (x.length + 2))
-          (fun _ : Fin 1 => FinTM.bufferTape (n + 1).bits) (fun _ => 0) [] := by
-  obtain ⟨t, ht, hp, hf, hr⟩ := clCount_first x 1 n.bits
-  have lift (j : ℕ) := FinTM.leftCfg_run clCountTM.tm (clRefCountTM M).tm
-    (fun s => (c.state, b, s)) (fun _ _ _ => rfl) (clCountCfg x 1 1 0 n.bits [])
-    (Fin.addCases (fun _ : Fin 1 => FinTM.bufferTape y) c.workTapes)
-    (Fin.addCases (fun _ : Fin 1 => (c.inputPos.val : ℤ) - 1) c.workTapePos) j
-  refine ⟨t, ht, hp, ?_, ?_⟩
-  · intro j hj hs
-    have hequiv := congrArg Cfg.state (lift j)
-    have hs' : (FinTM.leftCfg (fun s => (c.state, b, s))
-        (clCountTM.tm.runFrom (clCountCfg x 1 1 0 n.bits []) j)
-        (Fin.addCases (fun _ : Fin 1 => FinTM.bufferTape y) c.workTapes)
-        (Fin.addCases (fun _ : Fin 1 => (c.inputPos.val : ℤ) - 1) c.workTapePos)).state =
-          some (c.state, b, (0 : Fin 4)) := by
-      apply hequiv.symm.trans
-      simpa [FinTM.leftCfg, clCountCfg, clRefCfg, FinTM.tapeBlocks, clCountTape_eq] using hs
-    apply hf j hj
-    have he := congrArg (fun s => s.map (fun z => z.2.2)) hs'
-    simpa only [FinTM.leftCfg, Option.map_map, Function.comp_def, Option.map_id',
-      Option.map_some] using he
-  · have h := lift t
-    rw [hr, clCountInc_bits] at h
-    simpa [FinTM.leftCfg, clCountCfg, clRefCfg, FinTM.tapeBlocks, clCountTape_eq] using h
-
-/-- A counter below `2^w` occupies at most `w` bits. Together with
-`clRefCount_first`, this charges one administrative increment by two
+/-- A counter below `2^w` occupies at most `w` bits. Together with the
+counter runtime bound, this charges one administrative increment by two
 binary scans plus two transitions, with no unary-position representation. -/
 private lemma clCount_width (n w : ℕ) (hn : n < 2 ^ w) : n.bits.length ≤ w := by
   induction n using Nat.binaryRec' generalizing w with
@@ -3128,15 +3013,6 @@ private lemma clRowPrefix_fields {l : ℕ} (w : Fin l → List Bool) : ∀ j, j
     rw [List.take_succ_eq_append_getElem (by simpa using (show j < l by omega)), clFields_append]
     simp [clRowPrefix, show j < l by omega, ih (by omega), clFields]
 
-/-- Sequentially parse a specified number of self-delimiting fields.
-Malformed words return `none`; a successful parse retains the exact suffix. -/
-private def clReadFields : ℕ → List Bool → Option (List (List Bool) × List Bool)
-  | 0, xs => some ([], xs)
-  | n + 1, xs => do
-    let (w, rest) ← pairDecode xs
-    let (ws, tail) ← clReadFields n rest
-    pure (w :: ws, tail)
-
 /-- A native sequential field reader on two work tapes. It consumes an
 aligned doubled-bit field from a read-only stream, overwrites the target
 word, and rewinds only the target. The contract below requires the old
-- 
2.51.1

From 5ec0ac6449f85a93d99e2b3ed196f4384c0c6893 Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Fri, 9 Oct 2026 16:55:43 -0300
Subject: [PATCH 2/3] retrofit(Hardness): reuse composition, buffer and fill
 facts

---
 TCSlib/Complexity/CookLevin/Hardness.lean | 80 +++++++----------------
 1 file changed, 24 insertions(+), 56 deletions(-)

diff --git a/TCSlib/Complexity/CookLevin/Hardness.lean b/TCSlib/Complexity/CookLevin/Hardness.lean
index 262e84fc..830e1c3c 100644
--- a/TCSlib/Complexity/CookLevin/Hardness.lean
+++ b/TCSlib/Complexity/CookLevin/Hardness.lean
@@ -1591,13 +1591,6 @@ private lemma clTrack_round (M : FinTM Bool) {x y : List Bool}
       (clTrack_frame M (M.tm.step c) b' (fun _ => 0) (clAdvance d n))).trans
         (clTrack_dispatch M (M.tm.step c) b' (clAdvance d n))
 
-/-- Appending one bit at a contiguous buffer's right blank changes no other
-cell, including negative cells and the empty-buffer boundary. -/
-private lemma clBuffer_append_bit (w : List Bool) (b : Bool) :
-    Function.update (FinTM.bufferTape w) (w.length : ℤ) (some b) =
-      FinTM.bufferTape (w ++ [b]) := by
-  simpa only [List.append_nil, List.tail_nil, clCountTape_eq] using clCountTape_write w [] b
-
 /-- Two disjoint fixed tape slots, with no run-time indexing assumption. -/
 private def clTwo {α : Type} (a b : α) : Fin 2 → α := fun i => if i = 0 then a else b
 
@@ -1639,7 +1632,7 @@ private lemma clCopy_write (x : List Bool) (q q' : Fin 5) (p : Fin (x.length + 2
   · funext i
     fin_cases i
     · rfl
-    · exact clBuffer_append_bit record b
+    · exact (FinTM.bufferTape_append record b).symm
   · funext i
     fin_cases i <;> simp [clTwo, clCopyCfg, Action.apply]
 
@@ -4754,28 +4747,6 @@ private lemma clReplay_run (x : List Bool) (p : Fin (x.length + 2)) (w out : Lis
   simpa only [Nat.sub_zero, Nat.cast_zero, List.drop_zero] using
     clReplay_forward x p w 0 (by omega) out
 
-/-- Quantitative composition on actual completed words; the second machine
-need only be proved on the first machine's image. This uses the public
-buffered composition and its real capture/rewind startup ledger.
-**Proof sketch.** Start the second machine after the first completed run
-and its captured-output rewind. The public source-time lockstep then
-preserves the second computation, including its terminal emission. -/
-private lemma clCompute_comp (A B : FinTM Bool) (x y z : List Bool) (a b : ℕ)
-    (ha : A.ComputesInTime x y a) (hb : B.ComputesInTime y z b) :
-    (FinTM.bufferedCompTM A B).ComputesInTime x z (2 * a + b + 2) := by
-  obtain ⟨s, p, tapes, heads, hs, he⟩ := FinTM.bufferedComp_start A B x y a ha
-  obtain ⟨tag, _, hr⟩ := FinTM.bufferedSecondCfg_run A B (B.tm.initCfg y) true
-    (by simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads b
-  have endB := (FinTM.computesInTime_iff _ _ _ _).mp hb
-  have hc : (FinTM.bufferedCompTM A B).ComputesInTime x z (s + b) := by
-    apply (FinTM.computesInTime_iff _ _ _ _).mpr
-    rw [MultiTapeTM.runFrom_add, he, hr]
-    exact ⟨by simpa only [FinTM.bufferedSecondCfg, Option.map_eq_none_iff] using endB.1, endB.2⟩
-  have hlen : y.length ≤ a := by
-    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp ha).2
-    simpa only [ho] using A.tm.output_length_le x a
-  exact hc.mono (by omega)
-
 /-- Select one physical tape while framing every other tape and head. -/
 private def clOneSelect {k : ℕ} (i : Fin k) : Fin k → Option (Fin 1) :=
   fun j => if j = i then some 0 else none
@@ -5033,9 +5004,16 @@ private lemma clQueryCode_machine {l : ℕ} (pos neg : Fin l) (hne : pos ≠ neg
   refine ⟨FinTM.bufferedCompTM (clQueryFlagsTM pos neg) L, c, e, ?_⟩
   intro row target N W U tail hRow hTarget hWords
   have hQ := clQueryFlags_compute pos neg hne row target N W U tail hRow hTarget hWords
-  have h := clCompute_comp (clQueryFlagsTM pos neg) L _ _ _ _ _ hQ
+  have h := FinTM.bufferedCompTM_computesInTime (clQueryFlagsTM pos neg) L hQ
     (hL ((List.range N).map (fun s => clMatchFlag pos neg (row s) target)))
-  simpa only [List.length_map, List.length_range] using h
+  have hlen : ((List.range N).map (fun s => clMatchFlag pos neg (row s) target)).length ≤
+      2 * (clFields (List.ofFn (clQueryWords l target (clRows row N ++ tail) N)) ++ []).length +
+        9 + (l + 5) * (3 * U + 7) + N * (l * (5 * W + 7) + 2 * W + 7) := by
+    rw [← ((FinTM.computesInTime_iff _ _ _ _).mp hQ).2]
+    exact (clQueryFlagsTM pos neg).tm.output_length_le _ _
+  apply h.mono
+  simp only [List.length_map, List.length_range] at hlen ⊢
+  omega
 
 /-- Each field's complete word is contained, doubled, in the actual encoded
 argument; the bound includes separators and does not assume random access. -/
@@ -5187,7 +5165,7 @@ private lemma clNative_image {f g : List Bool → List Bool} (hf : PolyTimeCompu
   obtain ⟨A, a, d, hA⟩ := hf
   refine ⟨FinTM.bufferedCompTM A B, 2 * a + b * (a + 1) ^ r + 2, d * (r + 1), ?_⟩
   intro x
-  have hc := clCompute_comp A B x (f x) (g x) _ _ (hA x) (hB x)
+  have hc := FinTM.bufferedCompTM_computesInTime A B (hA x) (hB x)
   apply hc.mono
   have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hA x)).2
   have hlen : (f x).length ≤ a * (x.length + 1) ^ d := by
@@ -5205,6 +5183,9 @@ private lemma clNative_image {f g : List Bool → List Bool} (hf : PolyTimeCompu
   have hfirst := Nat.mul_le_mul_left (2 * a) hd
   have hlast : 1 ≤ (x.length + 1) ^ (d * (r + 1)) := Nat.one_le_pow _ _ (by omega)
   calc
+    _ ≤ 2 * (a * (x.length + 1) ^ d) + b * ((f x).length + 1) ^ r + 2 := by
+      dsimp only
+      omega
     _ ≤ (2 * a) * (x.length + 1) ^ (d * (r + 1)) +
         (b * (a + 1) ^ r) * (x.length + 1) ^ (d * (r + 1)) +
         2 * (x.length + 1) ^ (d * (r + 1)) := by
@@ -6768,19 +6749,6 @@ private lemma clA5Map_poly {S : Type} [Fintype S] [DecidableEq S]
   simpa only [Nat.pow_one, Nat.one_mul, hi, List.length_nil, List.nil_append] using
     clA5Map_run next emit finish start x x [] (by simp) start []
 
-/-- Replacing every bit by `true` computes the exact unary input length. -/
-private lemma clA5_pt_unaryLength : PolyTimeComputable (fun x => List.replicate x.length true) := by
-  have h := clA5Map_poly (S := Unit) (fun _ _ => ()) (fun _ _ => some true) (fun _ => none) ()
-  have he (x : List Bool) :
-      clA5MapWord (fun (_ : Unit) _ => ()) (fun _ _ => some true) (fun _ => none) () x =
-        List.replicate x.length true := by
-    induction x with
-    | nil => rfl
-    | cons b r ih => simpa [clA5MapWord, List.replicate_succ] using congrArg (true :: ·) ih
-  convert h using 1
-  funext x
-  exact (he x).symm
-
 /-- Removing the first bit is a two-state finite transduction. -/
 private lemma clA5_pt_tail : PolyTimeComputable List.tail := by
   let emit (q b : Bool) : Option Bool := if q then some b else none
@@ -6885,7 +6853,7 @@ of native tail calls. Each call is charged even after the word becomes empty. -/
 private lemma clA5Drop_native {s u : List Bool → List Bool}
     (hs : PolyTimeComputable s) (hu : PolyTimeComputable u) :
     PolyTimeComputable (fun x => (s x).drop (u x).length) := by
-  have h := clA5Iter_shrinking clA5_pt_tail hs (clA5_pt_unaryLength.comp hu)
+  have h := clA5Iter_shrinking clA5_pt_tail hs ((clNative_fill true).comp hu)
     (fun w => by simp [List.length_tail])
   convert h using 1
   funext x
@@ -6953,7 +6921,7 @@ private lemma clA5Field_native {s u : List Bool → List Bool}
     (hs : PolyTimeComputable s) (hu : PolyTimeComputable u) :
     PolyTimeComputable (fun x => clHeaderField (u x).length (s x)) := by
   have h := clA5Iter_shrinking (clHeaderTail_native 1) hs
-    (clA5_pt_unaryLength.comp hu) (fun w => (clA5Pair_sizes w).2)
+    ((clNative_fill true).comp hu) (fun w => (clA5Pair_sizes w).2)
   have hi (j : ℕ) (w : List Bool) : (clHeaderTail 1)^[j] w = clHeaderTail j w := by
     induction j with
     | zero => rfl
@@ -7064,8 +7032,8 @@ private lemma clA5StoredRound_native (M : FinTM Bool) :
     PolyTimeComputable (fun z => List.replicate (clA5StoredRound M z) true) := by
   have hh : PolyTimeComputable clA5StoredHeader :=
     (clHeaderField_native 0).comp (clHeaderTail_native 1)
-  have hx := clA5_pt_unaryLength.comp ((clHeaderField_native 0).comp hh)
-  have ht := clA5_pt_unaryLength.comp ((clHeaderTail_native 5).comp hh)
+  have hx := (clNative_fill true).comp ((clHeaderField_native 0).comp hh)
+  have ht := (clNative_fill true).comp ((clHeaderTail_native 5).comp hh)
   have h := clNative_append (clNative_append hx (clA5Times_native ht (M.k + 3)))
     (clA5_pt_const (List.replicate (M.k + 1) true))
   simpa only [clA5StoredRound, clLastRound, clA5Instance, ← Nat.add_assoc,
@@ -7081,7 +7049,7 @@ private def clA5Next (M : FinTM Bool) (z : List Bool) : List Bool :=
 /-- Saturating cursor update is an actual native word computation. -/
 private lemma clA5Next_native (M : FinTM Bool) : PolyTimeComputable (clA5Next M) := by
   have hu := clHeaderField_native 0
-  have hp := clA5Le_native (clA5_pt_unaryLength.comp hu) (clA5StoredRound_native M)
+  have hp := clA5Le_native ((clNative_fill true).comp hu) (clA5StoredRound_native M)
   have hc := clA5_pt_cond hp
     (clNative_append hu (clA5_pt_const [true])) hu
   simpa only [clA5Next, decide_eq_true_eq] using clNative_pair hc (clHeaderTail_native 1)
@@ -7622,8 +7590,8 @@ private lemma clA5Sizes_native :
     PolyTimeComputable (fun z => List.replicate (clA5Horizon z) true) := by
   have hh : PolyTimeComputable clA5StoredHeader :=
     (clHeaderField_native 0).comp (clHeaderTail_native 1)
-  exact ⟨clA5_pt_unaryLength.comp ((clHeaderField_native 4).comp hh),
-    clA5_pt_unaryLength.comp ((clHeaderTail_native 5).comp hh)⟩
+  exact ⟨(clNative_fill true).comp ((clHeaderField_native 4).comp hh),
+    (clNative_fill true).comp ((clHeaderTail_native 5).comp hh)⟩
 
 /-- Bounded numeric interpretation, total also on malformed requests. -/
 private def clA5SmallNum (w : List Bool) (N : ℕ) : ℕ := if clNum w ≤ N then clNum w else 0
@@ -7985,7 +7953,7 @@ private def clA5Cursor (z : List Bool) : ℕ := (clHeaderField 0 z).length
 private lemma clA5Cursor_native :
     PolyTimeComputable (fun z => List.replicate (clA5Cursor z) true) ∧
     PolyTimeComputable clA5Instance :=
-  ⟨clA5_pt_unaryLength.comp (clHeaderField_native 0),
+  ⟨(clNative_fill true).comp (clHeaderField_native 0),
     (clHeaderField_native 0).comp ((clHeaderField_native 0).comp (clHeaderTail_native 1))⟩
 
 /-- Residual ordinal after the pin family, before the singleton initial family. -/
@@ -8007,7 +7975,7 @@ private lemma clA5Indices_native (M : FinTM Bool) :
     PolyTimeComputable (fun z => List.replicate (clA5InputIndex z) true) ∧
     PolyTimeComputable (fun z => List.replicate (clA5WorkIndex z) true) ∧
     PolyTimeComputable (fun z => List.replicate (clA5AcceptIndex M z) true) := by
-  have hi := clA5Sub_native clA5Cursor_native.1 (clA5_pt_unaryLength.comp clA5Cursor_native.2)
+  have hi := clA5Sub_native clA5Cursor_native.1 ((clNative_fill true).comp clA5Cursor_native.2)
   have hs := clA5Sub_native hi (clA5_pt_const (List.replicate 1 true))
   have hn := clA5Sub_native hs clA5Sizes_native.2
   have hw := clA5Sub_native hn (clA5Add_native clA5Sizes_native.2 (clA5_pt_const (List.replicate 1 true)))
@@ -8084,7 +8052,7 @@ private lemma clA5Fragment_native (M : FinTM Bool) (code : CLFieldCode (Option M
     convert h using 1
     funext z
     by_cases hp : 0 < clA5InputSize z <;> simp [hp]
-  exact clA5IfLt_native clA5Cursor_native.1 (clA5_pt_unaryLength.comp clA5Cursor_native.2)
+  exact clA5IfLt_native clA5Cursor_native.1 ((clNative_fill true).comp clA5Cursor_native.2)
     (clA5Pin_native clA5Cursor_native.2 clA5Cursor_native.1)
     (clA5IfZero_native hi hinit (clA5IfLt_native hs hT
       (clA5Group_native M code CLTemplateKind.state hm hs (clA5Add_native hs ho) hz)
-- 
2.51.1

From 9f58177bf2c75e5adfc8d5e7cbcee3179b361622 Mon Sep 17 00:00:00 2001
From: Codex <codex@openai.com>
Date: Fri, 9 Oct 2026 17:03:58 -0300
Subject: [PATCH 3/3] retrofit(Hardness): compose fresh loader through
 Build.Seam

---
 TCSlib/Complexity/CookLevin/Hardness.lean | 31 +++--------------------
 1 file changed, 4 insertions(+), 27 deletions(-)

diff --git a/TCSlib/Complexity/CookLevin/Hardness.lean b/TCSlib/Complexity/CookLevin/Hardness.lean
index 830e1c3c..c63b4e7c 100644
--- a/TCSlib/Complexity/CookLevin/Hardness.lean
+++ b/TCSlib/Complexity/CookLevin/Hardness.lean
@@ -7,6 +7,7 @@ import TCSlib.Complexity.ClassNP.SAT
 import TCSlib.Complexity.ClassNP.TMSAT
 import TCSlib.Complexity.TuringMachine.Robustness.Oblivious
 import TCSlib.Complexity.CookLevin.Snapshot
+import TCSlib.Complexity.TuringMachine.Build.Seam
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -3382,12 +3383,7 @@ the banked reader. Stream positions and all reset/read transitions are charged.
 private def clFreshTM : FinTM Bool where
   k := 2
   State := (Fin 3) ⊕ clReadTM.State
-  tm := {
-    q₀ := .inl 0
-    tr := fun q inp work => match q with
-      | .inl q => if q = 2 then FinTM.controlAction 0 (some (.inr (.inl none)))
-          else (clWipeTM.tm.tr q inp work).mapState Sum.inl
-      | .inr q => (clReadTM.tm.tr q inp work).mapState Sum.inr }
+  tm := seamCompTM clWipeTM.tm 2 clReadTM.tm (.inl none)
 
 /-- Whole-configuration unrestricted loading, with a separate cost for
 clearing the old target. The new field may be empty, shorter, or unrelated.
@@ -3402,28 +3398,9 @@ private lemma clFresh_run (x : List Bool) (p : Fin (x.length + 2))
         (clReadCfg x p (.inr true) (pre ++ pairEncode w tail) w
           (pre.length + 2 * w.length + 2) 0).mapState Sum.inr := by
   obtain ⟨a, ha, _, hf, he⟩ := clWipe_first x p (pre ++ pairEncode w tail) old pre.length
-  have lift := clMap_run clWipeTM.tm clFreshTM.tm Sum.inl (fun q => q ≠ (2 : Fin 3))
-    (by intro q hq inp work; simp only [clFreshTM, if_neg hq])
-    (clWipeCfg x p 0 (pre ++ pairEncode w tail) old pre.length 0) a
-    (by intro j hj q hq heq; subst q; exact hf j hj hq)
-  rw [he] at lift
-  have dispatch : clFreshTM.tm.step
-      ((clWipeCfg x p 2 (pre ++ pairEncode w tail) [] pre.length 0).mapState Sum.inl) =
-      (clReadCfg x p (.inl none) (pre ++ pairEncode w tail) [] pre.length 0).mapState Sum.inr := by
-    change (FinTM.controlAction 0 (some (Sum.inr (.inl none) : clFreshTM.State))).apply _ = _
-    rw [FinTM.controlAction_apply, moveInputPos_zero]
-    rfl
-  have readRun := clMap_run clReadTM.tm clFreshTM.tm Sum.inr (fun _ => True)
-    (by intro q _ inp work; rfl)
-    (clReadCfg x p (.inl none) (pre ++ pairEncode w tail) [] pre.length 0)
-    (3 * w.length + 3) (by intros; trivial)
-  rw [clRead_run x p pre w tail [] (by simp)] at readRun
-  have arrived : clFreshTM.tm.runFrom
-      ((clWipeCfg x p 0 (pre ++ pairEncode w tail) old pre.length 0).mapState Sum.inl) (a + 1) =
-      (clReadCfg x p (.inl none) (pre ++ pairEncode w tail) [] pre.length 0).mapState Sum.inr := by
-    rw [MultiTapeTM.runFrom_succ_eq_step', lift, dispatch]
   refine ⟨a + 1 + (3 * w.length + 3), by omega, ?_⟩
-  rw [MultiTapeTM.runFrom_add, arrived, readRun]
+  exact seamCompTM_run_ofCfg clWipeTM.tm (2 : Fin 3) clReadTM.tm (.inl none)
+    he rfl hf (clRead_run x p pre w tail [] (by simp))
 
 /-- The unrestricted loader's completed state is absorbing. -/
 private lemma clFresh_idle {x : List Bool} (c : Cfg 2 Bool clFreshTM.State x)
-- 
2.51.1

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

## ===== audits/logs/retrofit-rb1-axioms.log =====

```
'Turing.stateWord' does not depend on any axioms
'Turing.loop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopCfgTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopFindTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_emitLoopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_installCallTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_emitCallTM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ===== audits/logs/retrofit-rb2-axioms.log =====

```
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

## ===== audits/logs/retrofit-rb3-axioms.log =====

```
'Complexity.NPHard.polyTimeReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT3_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.SAT3_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ===== maintainer E1 commit (7224d118) diff =====

```
commit 7224d118
MAINTAINER (RB2-E1, needs your approval by merge): complete the inverse swap


diff --git a/TCSlib/Complexity/TuringMachine/Build/Primitives.lean b/TCSlib/Complexity/TuringMachine/Build/Primitives.lean
index 406229db..bf6244f1 100644
--- a/TCSlib/Complexity/TuringMachine/Build/Primitives.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/Primitives.lean
@@ -2008,30 +2008,6 @@ private lemma anyTrue_computes : anyTrueTM.ComputesFunInTime
     exact ⟨hs, ho⟩
   exact hc.mono ht
 
-/-- A successful aligned parse reconstructs the input's exact encoding.
-**Proof sketch.** Induct over two-bit blocks: equal bits prepend one decoded
-bit; the separator exposes the entire remaining suffix. -/
-private lemma catalogPair_inverse (x : List Bool) :
-    ∀ a v, pairDecode x = some (a, v) → x = pairEncode a v := by
-  induction x using List.twoStepInduction with
-  | nil => intro a v h; simp [pairDecode] at h
-  | singleton b => intro a v h; cases b <;> simp [pairDecode] at h
-  | cons_cons b d rest ih _ =>
-    intro a v h
-    cases b <;> cases d
-    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
-      rcases p with ⟨u, w⟩
-      cases he
-      rw [ih u w hp]
-      rfl
-    · cases h; rfl
-    · simp [pairDecode] at h
-    · obtain ⟨p, hp, he⟩ := Option.map_eq_some_iff.mp h
-      rcases p with ⟨u, w⟩
-      cases he
-      rw [ih u w hp]
-      rfl
-
 /-- Marker absence is exactly the false verdict; a present marker can be
 stripped after any fixed prefix without disturbing that prefix.
 **Proof sketch.** Right induction follows `reverse.dropWhile`: append-false
@@ -2869,7 +2845,7 @@ theorem computesFunInTime_stripLast :
       rcases catalogMarker_cases v with ⟨ha, hs⟩ | ⟨w, ha, hs, hp⟩
       · simpa [hd, ha, hs] using hm
       · have hx : splitAtLastTrue x = some (pairEncode u w) := by
-          rw [catalogPair_inverse x u v hd]
+          rw [Turing.eq_pairEncode_of_pairDecode x u v hd]
           exact hp _
         simpa [hd, ha, hs, hx] using hm
   apply hh.mono
```
