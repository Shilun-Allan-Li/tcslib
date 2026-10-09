# External audit pack — Chapter 4, phase P4.2 (configuration graphs and Savitch), statement gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md`), phase P4.2 —
the configuration graph of a nondeterministic machine on an input, the counting
half of Claim 4.4(1) in acceptance form, Theorem 4.2's third inclusion
(nondeterministic space inside exponential time), `NL ⊆ P`, Exercise 4.3's
coarseness statement, Savitch's theorem, and `PSPACE = NPSPACE`. Statement
phase per `workflow.md` §2-3; the gate closes on a round with zero blockers
and zero majors.

Audited at commit `200f4693` (branch `complexity/arora-barak-ch3-4`); the two
files under audit are byte-identical to their landing commit `50d72880`
**except** (a) one Design-bullet / Status-paragraph refresh in each (commit
`3a511a6f`): the facade-freeze status lines became false when the P4.1 gate
closed, and were updated to say the `SpaceComplexity.lean` facade now carries
the two modules, and (b) **two review repairs** applied at `200f4693`, caught
by the pack-assembly verification and applied before this pack shipped (the
P3.2 review-repairs-before-gate pattern): `PSPACE_eq_NPSPACE`'s sketch now
routes degree 0 through the class's constant absorption — bare
`Complexity.NSPACE.mono`'s pointwise hypothesis fails at `n = 0`, where
`n ^ 0 + 1 = 2 > n + 1 = 1` — and `acceptsWithin_of_spaceUsedWith_le`'s
sketch pads the spliced word back to the exact count (`AcceptsWithin` demands
exact word length). All of (a)-(b) are docstring prose only; no declaration,
statement, or sketch *claim* is touched (verify:
`git diff 50d72880 200f4693 -- TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean TCSlib/Complexity/SpaceComplexity/Savitch.lean`).
Under audit: `TCSlib/Complexity/SpaceComplexity/{ConfigGraph,Savitch}.lean` —
**10 sorried statements (ConfigGraph 7, Savitch 3), 5 definitions**
(`Turing.OutSummary`, `Turing.outSummary`, `Turing.NDTM.coreSum`,
`Turing.NDTM.CfgStep`, `Turing.FinNDTM.configBound`). No skeleton-time proofs:
the two modules carry definitions and sorried statements only (12 + 3 public
declarations, checkable in the attached lint log). The facade carrying their
wiring since the P4.1 close is attached and swept.

**This phase sits on two closed surfaces.** The **closed** P4.1 statement gate
(`audits/ch4-p41-resolutions.md`: the branch space measure
`Turing.NDTM.spaceUsedWith`, `Turing.FinNDTM.DecidesInSpace`,
`Complexity.NSPACE`, the classes `PSPACE`/`NPSPACE`/`NL`/`coNL`,
`Complexity.SpaceConstructible`) and the **closed** P0 reception gate
(`audits/ch34-p0-resolutions.md`: the deterministic configuration-count layer
— `Turing.MultiTapeTM.ConfigCount.core`/`core_step`/`coreCode`/`coreCode_inj`,
`Turing.FinTM.configBound`, `configBound_logSpace_le` — and the
**positive-bound convention**: every asymptotic chapter bound is everywhere
positive).

**Two concurrent rounds, declared plainly:**

* **(a) The §12 routine layer** (`audits/routine-infra-pack.md`;
  `TCSlib/Complexity/TuringMachine/Build/{Embed,Seam,Catalog}.lean`) is under
  audit **in parallel**, and the Savitch and exponential-time-simulation
  sketches here name §12 R1/R2/R3 routines (bank embedding, seam composition,
  the space-annotated catalog rows, the loop combinator) as their fill
  engines. Findings against the §12 statements themselves go to that round;
  this gate audits whether the *statements here* are true as stated and the
  sketches coherent **given the declared interfaces**.
* **(b) The P4.3 and P4.4 packs** (`audits/ch4-p43-pack.md`,
  `audits/ch4-p44-pack.md`) run concurrently on disjoint files; findings
  about their modules (`Hierarchy`, `Formulas/*`, `ClassPSPACE/*`,
  `Logspace/*`) are filed there, labeled as such.

## Brief for the auditor

Definitions, statements, docstrings. Failure modes per `audits/TEMPLATE.md`,
plus this phase's own two: **a vertex abstraction that is too coarse (splicing
out a cycle changes acceptance) or uselessly fine (the count blows past
`2^{O(S)}`)**, and **a simulation statement whose exponent arithmetic silently
needs `S(n) ≥ log n` where the hypothesis doesn't supply it**. Blind
restatements for every definition (all 5); true-as-stated arguments for every
sorried statement (all 10); at least **5 adversarial instantiations**; no
blanket approvals. Sources: [AB09] §4.1.1 (the configuration-graph definition
and Claim 4.4(1)), Theorem 4.2's third inclusion, §4.1.2 (`NL ⊆ P`, the p. 92
chain), Exercise 4.3, §4.2.1 (Theorem 4.14, Savitch; `PSPACE = NPSPACE`).
[Sav70] is cited through [AB09]; no external text is required for this audit.

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/ch4-p42-sweep.log`, revision recorded at
  start: `200f4693`): 3 modules — the two under audit plus the
  `SpaceComplexity.lean` facade (every gate sweep lists its touched facades
  explicitly since the P4.3 landing erratum) — 0 `error:` lines, fresh
  `.olean`s, exactly **10** `declaration uses 'sorry'` warnings
  (ConfigGraph 7, Savitch 3, facade 0).
* Style lint (`audits/logs/ch4-p42-p44-stylelint.log`, one log shared with
  the concurrent P4.3/P4.4 packs): 0 FAIL / 0 WARN over 42 files — the whole
  `SpaceComplexity` tree, the concurrent phases' `Hierarchy` and `Logspace/*`
  modules included.
* Statement-freeze baseline: commit `200f4693`.
* Drafting provenance: maintainer-drafted skeleton, no sub-agent; landing
  commit `50d72880`.

## Known deviations and design decisions (declared — verify each, flag others)

1. **The vertex is a core plus a three-valued output summary**
   (`Turing.NDTM.coreSum` = the received `ConfigCount.core` paired with
   `Turing.outSummary` of the output). The received deterministic counting
   layer counts *cores* — sound for halting-time bounds, because output is
   write-only, but **not** by itself for acceptance along a branch: acceptance
   is output exactly `[true]` at a halted configuration, and splicing out a
   cycle between equal cores could delete the branch's one emission. The P0
   reception audit's fitness note (`audits/ch34-p0-findings.md` §7)
   anticipated exactly this gap; the summary closes it by design.
   Splicing-soundness is the point: the summary is append-compatible (the
   summary of `out ++ e` is a function of the summary of `out` and `e`
   alone), which is what makes vertex-level surgery preserve acceptance.
2. **The graph is the step relation, not a finite graph object**:
   `Turing.NDTM.CfgStep c c' := ∃ b, stepWith b c = c'`, with
   `Relation.ReflTransGen` as reachability; finiteness enters only through
   the sorried bounds. Efficient vertex *encoding* reuses the received
   `Turing.MultiTapeTM.ConfigCount.coreCode`; the `O(S)`-size adjacency CNF
   of Claim 4.4(2) is deliberately phase P4.3's.
3. **Explicit constants**: `Turing.FinNDTM.configBound N n s =
   3 · ((|Q| + 1) · (n + 2) · 3^{k(2s+1)} · (2s+1)^k)` — three (the
   summaries) times the received deterministic core-count formula, not an
   abstract `2^{O(s)}`.
4. **The all-siblings space hypothesis**:
   `acceptsWithin_of_spaceUsedWith_le` bounds the branch space over **all**
   choice words of length `T` (sibling branches), not only the accepting one
   — matching `Turing.FinNDTM.DecidesInSpace`'s own quantifier shape, so the
   packaged iff can discharge it directly.
5. **The exponential-time rendering**: `NSPACE_subset_exp_dtime` states
   `NSPACE S ⊆ ⋃ c, DTIME (2 ^ (c · (S n + 1)))` for the book's `2^{O(S(n))}`;
   the `+ 1` keeps the exponent positive and absorbs the input-head factor
   via `n + 2 ≤ 2 ^ (S n + 1)` — which needs the `logSpace n ≤ S n` floor
   bundled in `Complexity.SpaceConstructible`.
6. **Savitch is stated at `SPACE (S · S)` for space-constructible `S`**, with
   the midpoint recursion realized **iteratively**: an explicit stack of
   `O(S)` frames of `O(S)` bits (coded vertex pair plus midpoint cursor) on a
   dedicated bank, walked by the loop combinator — the §12 layer (R1 bank
   embedding, R2 seam composition, R3 catalog routines) is the declared fill
   engine (concurrent round (a) above).
7. **Degree zero is excluded from `spaceConstructible_poly`** (`1 ≤ c`):
   `n ^ 0 + 1 = 2` fails the bundled `logSpace n ≤ S n` from `n = 4` on
   (`logSpace 4 = 3`); consumers route degree 0 into
   degree 1 through the class's constant absorption, as
   `PSPACE_eq_NPSPACE`'s sketch does (review repair (b): bare
   `Complexity.NSPACE.mono` does not apply at `n = 0`).
8. **The square is absorbed at the polynomial level** by
   `(n^c + 1)² ≤ 4 · (n^{2c} + 1)`: Savitch at `n ^ c + 1` lands in
   `SPACE ((n^c + 1) · (n^c + 1))`, then `Complexity.SPACE.mono` plus the
   class's constant absorption land it in `SPACE (n^{2c} + 1) ⊆ PSPACE`
   (`Complexity.space_poly_subset_PSPACE`).
9. **Exercise 4.3 is stated with explicit nontriviality witnesses**
   (`∃ y, y ∈ L` and `∃ z, z ∉ L`) and the conclusion `L' ≤ₚ L` for every
   `L' ∈ NL`; the exercise's moral — polynomial-time reductions are too
   coarse below `P`, so `NL`-completeness means something only under the
   logspace reductions of phase P4.4 — is recorded in the docstring rather
   than left implicit.

## Specific questions (prioritized)

1. **The `OutSummary` quotient**: blind-restate `Turing.outSummary` and check
   append-compatibility case by case — `[] ++ e` (the summary of `e` itself),
   `[true] ++ e` (`accept` iff `e = []`, else `dead`), and `dead` absorbing
   (a word neither `[]` nor `[true]` stays so under every append). Is
   three-valued *exactly* right for acceptance = output exactly `[true]` at a
   halted configuration (`Turing.FinNDTM.AcceptsWithin`), and does
   `coreSum_stepWith`'s claim — the new summary is a function of the old
   summary plus the step's emission — hold for the campaign's step semantics
   (an `Action.apply` appends at most one optional bit per step)?
2. **`reflTransGen_cfgStep_iff`** — endpoints: halted configurations
   self-loop under `CfgStep` (`Turing.NDTM.stepWith_of_halt` at either bit);
   `Relation.ReflTransGen.refl` against the empty choice word. Is the iff
   sound in both directions as stated (forward: induction on the chain,
   appending each step's bit via `Turing.NDTM.runWith_append` at a singleton;
   backward: `Turing.NDTM.runWith_cons` with `Relation.ReflTransGen.head`)?
3. **`acceptsWithin_of_spaceUsedWith_le`** — is the all-siblings space
   hypothesis (deviation 4) faithful to Claim 4.4(1), and does the splice
   argument survive the summary: can splicing out a cycle delete the
   acceptance emission, or does the vertex's summary component rule that out
   by construction? Check the padding edge both ways: `configBound` above `T`
   (pad by `Turing.FinNDTM.AcceptsWithin.mono`; the padded siblings stay
   halted by `Turing.NDTM.runWith_of_halt`) and `configBound` below `T`
   (the splicing must genuinely shorten below the vertex count).
4. **The packaged iff** (`mem_iff_acceptsWithin_configBound`) — check the
   backward direction's truncation argument at both budget orders: budget
   above `T` (the branch's `T`-prefix is already halted by
   `Turing.NDTM.HaltsWithin` with the run frozen by
   `Turing.NDTM.runWith_of_halt`, so the prefix accepts and membership
   follows from the equivalence at `T`) and budget at most `T` (pad). Any
   gap between the two cases?
5. **`NSPACE_subset_exp_dtime`** — the exponent normalization: is
   `n + 2 ≤ 2 ^ (S n + 1)` actually enough to land the whole
   vertices × edges × table ledger in the stated exponent, and where exactly
   is space-constructibility used — the budget computation only, or also
   uniformity of the simulator? Does the `⋃ c` rendering (with `DTIME`'s own
   constant absorption inside) match the book's `2^{O(S)}`?
6. **Savitch** — is `S · S` the right target under the campaign's
   constant-absorption `SPACE` (the fill must deliver `c' · (S n · S n)`);
   is constructibility of `S` used only for the radius computation; does the
   `O(S²)` frame-stack ledger of the sketch (at most `log₂ V + 1` frames of
   `O(S n)` bits each) actually deliver the claimed bound? And is the
   degree-0 exclusion in `spaceConstructible_poly` (deviation 7) plus the
   degree-0 routing in `PSPACE_eq_NPSPACE` airtight?
7. **Exercise 4.3** — hypothesis and conclusion shape against the book's
   exercise (nontriviality as the two explicit witnesses; `NL`-hardness as
   `L' ≤ₚ L` for every `L' ∈ NL`); and the classical-choice reduction's
   computability: the sketch builds `f x := if x ∈ L' then y₀ else z₀` from
   the `NL ⊆ P` decider by `Complexity.polyTimeComputable_ite` over two
   `Complexity.polyTimeComputable_const` branches — is anything
   noncomputable smuggled in (the witnesses are fixed strings, chosen
   classically once)?
8. **Adversarial instantiations to attempt**: `s = 0` windows (the window is
   the single cell; `configBound n 0 = 3 (|Q| + 1)(n + 2) · 3^k`); `T = 0`
   budgets (the empty choice word — acceptance iff the initial configuration
   is already halted with output `[true]`); the empty input `x = []`; the
   all-rejecting machine through `mem_iff_acceptsWithin_configBound`; `L`
   full or empty in Exercise 4.3 (a witness hypothesis must fail); `c = 0`
   and `c = 1` in `PSPACE_eq_NPSPACE`'s routing; a machine whose only
   accepting branch is longer than the vertex count (the shortening must
   genuinely bite).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`; findings verbatim into
`audits/ch4-p42-findings.md`; the gate closes on zero blockers and majors.


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


## ===== audits/ch34-p0-findings.md =====

```
# Chapters 3–4, P0 reception audit

Date: 2026-10-08. Scope: the supplied audit pack and its 50 attachments, including all 44 modules in `scripts/ab_ch34_received_order.txt`.

Bundle SHA-256, independently recomputed: `69f84b8d7194081e3b7749467f41f2c77fc3f09409e655badac32a4ae6b3d05b`.

**Disposition: P0 does not close. Findings: 0 blockers, 1 major, 7 minors, 2 notes.** The major finding concerns the meaning of unrestricted `SPACE s`, particularly the plan's literal `SPACE(n)` target. It is not a claim that an attached Lean theorem is false. The principal time hierarchy, configuration count, and compiler statements withstand the adversarial checks below under their actual hypotheses.

This is a definition, statement, and documentation audit. No tactic proof was audited for correctness. The 244 definition-like declarations were first read in comment-stripped sources and restated in a separate record; docstrings were compared afterward. Appendix A includes every such restatement, including private definitions, structures, inductive types, and abbreviations. Appendix B checks every advertised headline result, grouping closely related results where their contracts have the same comparison. The two facade modules introduce no definitions. An explicit finite-type instance is accounted for separately.

## Findings table

File names below are relative to `TCSlib/Complexity/`, except the audit log and plan. Line numbers refer to the extracted attachments, not to the enclosing bundle.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **major** | `SpaceComplexity/Basic.lean:110` · `SPACE`; `AroraBarakChapters3-4Plan.md` · Ex. 3.2 target | Multiplicative absorption with no positivity convention supplies the ordinary asymptotic space classes for the planned chapter statements. | Every work tape contributes its initially visited origin. If `s(n₀)=0`, the uniform deciding machine must have `k ≤ spaceUsed ≤ c·s(n₀)=0`, hence `k=0` on **all** inputs. Consequently `SPACE s = SPACE (fun _ => 0)` whenever `s` has any zero. In particular literal `SPACE (fun n => n)` is the zero-work-tape class, not the intended linear-space class. Finite exceptional lengths cannot be absorbed by increasing `c`. See Q2 and sanity targets S1–S3. | Establish a positive-bound convention before adoption: retain the frozen definition but explicitly use `SPACE (fun n => s n + 1)` or an equivalent positive normalization in every asymptotic chapter statement, including Ex. 3.2; alternatively revise the class definition and re-gate it. Document the zero-bound characterization. Merely saying “constants are absorbed” does not resolve this. |
| 2 | minor | `TuringMachine/CounterProgRun.lean:308–313` · `sim_run` | The advertised bound applies whenever the registers stay at most `B` during a run. | The delivered theorem instead assumes `s.pos ≤ x.length` and `∀ r, s.regs r + t ≤ B`. A one-register `goto` loop starting at value `B`, run for one step, stays within `B` but fails `B+1 ≤ B`. The parenthetical sufficient condition in the docstring accurately describes the formal hypothesis; the broader opening is not the delivered interface. `exists_tm` from zero initialization is unaffected. | State the actual sufficient hypothesis in the headline, or add a theorem taking a bound on each intermediate register valuation. |
| 3 | minor | `SpaceComplexity/Machines/Program.lean:42–45,68–72` · `Mode`, `callSegs` | A `whole` call always gives `pairEncode x _`, and a `unaryFst` call gives a corresponding pair. | Empty argument lists are allowed by `CallSpec` and satisfy the distinctness condition. With `x=[]`, mode `whole`, and no arguments, `vword (callSegs …)=[]`; every `pairEncode x w` contains the two-bit separator. More generally the singleton segment has no separator. | Qualify the pair description by “with at least one argument.” Keep the legitimate zero-argument behavior, or explicitly restrict it if pair shape is intended. |
| 4 | minor | `SpaceComplexity/Machines/ARM.lean:69–72` · `Ins.valP`, `Ins.valQ` | These instructions merely check the displayed pairing shape. | `astep` checks `ValidPlain`/`ValidPair`, which additionally require canonical binary payloads. `pairEncode [] [false]` has the advertised plain pair shape but is rejected: `[false]` is not canonical. This is a useful restriction, but part of the public instruction contract. | Say that the payload word, or both inner payload words, must be canonical `Nat.bits` encodings. |
| 5 | minor | `ClassNP/PClosure.lean:160–167` · `lenEq_mem_P`, `lenLe_mem_P` | The accepted languages consist of pairs with the respective length relation. | Both projections default to `[]` on malformed input. Thus `z=[]`, which is not a pair encoding, belongs to both displayed languages. The theorems are valid for these totalized predicates, and their well-formed-pair preimage corollaries are fine. | Describe the default behavior explicitly; if the intended language rejects malformed words, add a successful-decoding guard and prove that variant. |
| 6 | minor | `SpaceComplexity/Machines/ParseCmp.lean:302–307` · `ReachesB` | The register head lies in the interval “throughout” the run, including the reached configuration. | Bounds are quantified only over `t<T`. Choosing `T=0` proves reflexive `ReachesB` even for a configuration whose head lies outside the interval. The endpoint is not bounded by this relation alone. Similar half-open conventions occur in `AReach`, `AHalt`, and `Dbl.Rch`; the main compiler obtains its inclusive bounds separately. | Say “strictly before the endpoint”; add an endpoint-bound hypothesis to any consumer needing an inclusive bound. No compiler counterexample was found. |
| 7 | minor | `audits/logs/ch34-p0-sweep.log:1439` · repository-side attestation | The attached fresh sweep attests the stated Lean-source baseline `84b79daf`. | The log identifies its revision as `e64cec9e`, whereas the pack identifies `84b79daf` and claims a documentation-only relation to `99b187fc`. No supplied revision relation or source diff binds the log to that baseline. The numerical success counts do agree with the log. | Supply the revision relationship and a Lean-source equivalence attestation, or a replacement sweep tied to `84b79daf`. Correct the pack's provenance wording. This is an evidence discrepancy, not a finding about proof correctness. |
| 8 | minor | `SpaceComplexity/Machines/ARMSim.lean:29`; `Machines/Compile.lean:28` · advertised exports | The received API exports `Complexity.LogProg.arm_step` and `Complexity.LogProg.CallsOK`. | Neither declaration occurs in the received surface. The actual interfaces are the instruction-specific `sim_*` results, the later `arm_run`, and singular `CallOK` quantified along a run. `Layout.lean:22` also points to an unattached `Machines.Gadget` module. This concerns missing referents, not naming style. | Update the result/definition lists to the declarations actually supplied; correct or supply the referenced module. |
| 9 | note | `TimeHierarchy/Diagonal.lean` · hierarchy family | The received theorem has the declared quadratic-overhead strength. | The exact scale is `(f(n)+n+1)²`; it becomes an `f²` scale under suitable lower bounds on `f`. The lower theorem uses arbitrarily large numerical domination points, while the class conclusion is ordinary nonmembership/strict inclusion. The book-strength result is explicitly deferred. | No theorem change required. Preserve the explicit hypothesis and the distinction from book strength in downstream citations. |
| 10 | note | `SpaceComplexity/ImplicitPoly.lean`; `UnaryLogspace.lean`; `CounterProgSimRun.lean` | The received function results are usable without asserting general composition. | `ImplicitlyLogspaceComputable` includes polynomial output length; `UnaryLogspace` alone does not. Its conversion theorem requires that extra bound. The counter-program result is a restricted closure theorem. General Lemma 4.17 is not delivered and the plan says so. | No change required. Do not treat these results as the missing general composition theorem. |

## Evidence and source boundary

The local bundle contains 865,996 bytes, 50 unique attachment paths, and exactly the manifest's 44 Lean files. Literal whole-word searches of those 44 files find neither `sorry` nor `axiom`. The attached sweep lists 71 distinct modules, includes the received set, and contains no `error:` lines or admission warnings. The style log records the claimed zero failures/warnings for the 34 non-facade TimeHierarchy/SpaceComplexity files; the size warnings elsewhere are not received files. The attachments do not establish the exception-file history.

There is no `lean` or `lake` executable in this audit environment. I did not independently elaborate the files, reproduce CI, inspect the purported 71 fresh `.olean` files, verify the scratch tree was wiped, regenerate snapshots, or verify the three-way commit relationship. These limits do not invalidate the supplied proofs; they limit independent confirmation of the repository attestations. Finding 7 records the concrete discrepancy.

The primary comparison text was the 2009 book itself, read from a [PDF mirror of AB09](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora%2C_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf). Printed pages, not PDF page indices, are used below. The following compact baseline supplies the book comparisons throughout the report:

| Source | Book baseline used in this audit |
|---|---|
| Theorem 3.1, pp. 68–69 | Constructible bounds with `f log f = o(g)` yield strict deterministic time inclusion. |
| Definition 4.1 and convention, pp. 78–79 | Deterministic space counts visited work locations; the nondeterministic wording counts nonblank locations. Work space excludes input. The chapter assumes `S(n)>log n`. |
| Claim 4.4 and Theorem 4.2, pp. 80–82 | Configurations have `O(S)`-bit encodings under that convention; counting yields exponential simulation. Adjacency also has a small CNF description. |
| Definition 4.5 | Logarithmic space defines `L`. |
| Definition 4.16 and Lemma 4.17, pp. 88–89 | Polynomial output length and logspace bit/length queries define implicit computation, using one-based indices. Reductions compose and logspace preimages preserve `L`. |
| Theorem 4.8 | Constructible space bounds with a little-o gap give strict space inclusion. |

Implementation types and microcode do not have numbered textbook counterparts. Their comparisons below concern their own documented contracts and whether they implement the relevant construction without weakening the final statement. Imported definitions such as `FinTM`, `DTIME`, `TimeConstructible`, pairing, and the vendored space measure are not re-audited as upstream designs; their relevant interface consequences are identified explicitly.

## Answers to the seven numbered questions

### 1. Hierarchy hypothesis, constants, positivity, and `P ⊊ EXP`

The quantifier order is right. Fix an alleged smaller-class decider, its time constant, its normal-form simulation constants, and its chosen code `α`. Only then obtain the universal simulation constant for `α` and combine these into `A`. The hypothesis supplies a threshold depending on that `A`; it does not demand a threshold uniform over machines. The code-dependent order `∀ α, ∃ C, ∀ x` in `univTM_spec` is sufficient. It is not a uniform-over-all-codes claim.

The exact hypothesis controls `(f(n)+n+1)²`, not `f(n)²` for arbitrary functions. If `f(n)≥n` and `f(n)≥1`, then

`f(n)² ≤ (f(n)+n+1)² ≤ 9f(n)²`.

Without those lower bounds, the input-length overhead matters. For example, even constant `f` requires the eventual domination of every constant multiple of `n²`. No constructibility assumption on `f` is needed for this delivered separation. Constructibility is imposed on `g` to build the clock. The book's narrower time gaps remain unavailable.

`diagLang_not_mem_DTIME` needs only `∀ A N, ∃ n≥N, A·(T(n)+n+1)²≤g(n)`. Padding a fixed code supplies **every** length `n≥2|α|+2` by choosing a payload of length `n−2|α|−2`; it does not restrict usable lengths to an arithmetic progression. The eventual hypothesis of `time_hierarchy` is stronger and suffices both for its lower bound and its inclusion. The phrase “infinitely-often separation” in the pack should be read with care: the exported conclusion is ordinary class nonmembership, with an infinitely-often numerical sufficient condition, not a definition of an infinitely-often complexity class.

The `+1` in `DTIME (g+1)` has a real boundary purpose. Under the imported all-length multiplicative time convention, a zero value of a time bound leaves no time even to emit a deciding bit; that class is empty. By contrast, constructibility uses a normalized computational budget and need not forbid `g(0)=0`. Thus one cannot erase `+1` unconditionally. If `∀n,0<g(n)`, then `g≤g+1≤2g`, so the classes coincide by constant absorption. `time_hierarchy_of_pos` has exactly the needed additional hypothesis. A finite alteration setting an otherwise exponential `g` to zero at length zero illustrates why eventual growth alone is insufficient for the unnormalized conclusion.

For the polynomial/exponential instance, put `a=(n+1)^(k+1)`. For every natural `n,k`, including zero, `n^k≤a`, `n+1≤a`, and `1≤a`. Therefore

`A·(n^k+1+n+1)² ≤ 9A·(n+1)^(2k+2)`.

This checks the actual exponent `2k+2` in `eventually_poly_sq_le_two_pow`. For an independent eventual-domination calculation, let `d=K+1` and `m=floor(n/d)`. Once `m≥A·d^K`, use `n+1≤d(m+1)` and `m+1≤2^m` to get

`A(n+1)^K ≤ A d^K (m+1)^K ≤ m·2^(mK) ≤ 2^(m(K+1)) ≤ 2^n`.

The case `A=0` is immediate. This is a numerical check, not a review of the Lean proof.

`twoPowTM` outputs `n` false bits followed by true in `n+1` steps, the canonical little-endian representation of `2^n`, and `n+1≤2^n+1`. Thus the constructibility instance is nonvacuous. Finally, `P_ssubset_EXP` uses the **same** `diagLang (fun n => 2^n)` against every polynomial exponent. Merely knowing a separate strict inclusion for each exponent would not suffice to separate their union; the common diagonal witness does. Its upper bound is in the exponent-one part of `EXP`, with the harmless factor from `2^n+1≤2·2^n` absorbed. The claimed separation is delivered.

### 2. Unrestricted `SPACE`, zero bounds, and short inputs

No received configuration-count or compiler theorem silently needs `s≥log n`: the count retains an explicit input-head factor, and compiler bounds are stated directly. `LOGSPACE_subset_P` is robust at lengths zero and one because `logSpace 0 = logSpace 1 = 1`.

The important exceptional behavior is stronger than “zero space permits only finite control.” `Clean.visited_interval` explicitly entails that each tape's visited set contains the origin, even at time zero. Consequently, for any machine and input,

`M.k ≤ M.tm.spaceUsed (M.tm.initCfg x) t`.

If `s(n₀)=0`, choose `x` to be `n₀` false bits and instantiate its space-deciding contract. It forces `M.k=0`. This is one fixed machine for every input, so the loss of work tapes is global. Conversely, a zero-tape decider uses zero work space for every input. Hence

`SPACE s = SPACE (fun _ => 0)` whenever `∃n, s n=0`.

The exact machine characterization is the languages decided by total, finite-state, zero-work-tape machines with a two-way read-only input and unread append-only output. This is the regular-language class: the one-bit output condition can be tracked in finite control, and two-way finite automata recognize the same languages as one-way automata ([Rabin–Scott 1959, Theorem 15, p. 123](https://www.cs.miami.edu/~burt/learning/csc427.222/docs/rabin-scott.pdf)). This last identification is mathematical, not a theorem linking the received definition to a formal regular-language predicate in this bundle.

In particular, `SPACE(n)` and `SPACE(n^d)` for positive `d` collapse to that class because of length zero. Literal `SPACE(n)≠NP` would then concern the wrong linear-space class. A zero at any other length has the same effect. This is finding 1. Positive normalizations remove this obstruction; merely requiring an eventual lower bound does not. The plan's proposed `n^c+1` normalization for polynomial space avoids it.

Neither `SPACE 0` nor `SPACE s` is empty: the constant languages have zero-tape machines that emit one Boolean and halt. Length parity is a nonconstant zero-space example. A zero-tape parity scanner takes `n+1` steps, so below logarithmic space one cannot remove the input factor and claim a `2^{O(s)}` time bound. A constant-time decider could not distinguish two sufficiently long all-false inputs of opposite length parity before reaching their ends. This does not challenge the received count, which retains `n+2`.

### 3. Independent configuration count and its actual halting premise

Fix the input, a machine with `k` work tapes and `q` live states, and a bound `s` on total visited work cells through a halting time. Each head starts at zero and moves by at most one. Reaching a coordinate requires visiting all intervening coordinates. Every nonblank cell was written at a visited coordinate. Thus the much larger window `[-s,s]` contains each relevant head and all nonblank tape content.

| Factor | Independent reason | Boundary behavior |
|---|---|---|
| `q+1` | Live state or halted marker. | Counts an extra terminal choice; it cannot undercount. |
| `n+2` | Input symbols plus two boundary positions. | Still two positions on the empty input. |
| `3^(k(2s+1))` | `Option Bool` has three values at each cell in each tape window. | Allows arbitrary contents in windows, including unreachable combinations. |
| `(2s+1)^k` | A head coordinate in the window for every tape. | For `k=0` both tape factors are one; for `s=0` the window has one coordinate. |

Multiplication gives exactly `configBound`. Using a radius `s` for **every** tape when the sum of visited cells is bounded by `s` overcounts. `posCode` is not globally injective: it clamps. The count only needs its injectivity on the bounded reachable coordinates, with blankness outside the window.

The counted object is a **core**, omitting output, not the full configuration including an arbitrarily long output list. This is legitimate for time-to-halt because output is unread. Equal cores have equal future core evolutions; a repeated live core before the first halt would make that evolution periodic and prevent a first halt. The final output is recovered at the same halting computation, not reconstructed from the core code.

`ComputesInTime.of_spaceUsed_le` explicitly assumes both an already-halting computation `h : M.ComputesInTime x y t` and its bound `spaceUsed … t ≤ s`. It moves that computation to the configuration-count budget. It does **not** assert that every space-bounded machine halts. A zero-tape stationary loop is a counterexample to that stronger assertion. Bounding space at time `t` also bounds earlier prefixes by monotonicity. These are the right hypotheses for the deterministic count-to-time implication; the nondeterministic simulation and adjacency CNF are not supplied here.

The logarithmic specialization can be checked uniformly, including short inputs. For natural `s`,

`3^(k(2s+1)) ≤ 2^(4ks+2k)` and `(2s+1)^k ≤ 2^(k(s+1))`.

Writing `ℓ=Nat.log 2 n` and `s=c(ℓ+1)`, use `2^ℓ≤n+1` and `n+2≤2(n+1)` to obtain

`configBound M n s ≤ (q+1)·2·2^(5kc+3k)·(n+1)^(5kc+1)`.

This is a fixed polynomial for fixed `M,c`. The factor also covers `n=0`, `c=0`, and `k=0`. There is no hidden logarithmic lower-bound premise in `LOGSPACE_subset_P`.

### 4. `LogProg` and ARM: what the contracts buy

The contracts are sufficient, and the restrictions are usable for the supplied examples. They are not a theorem for arbitrary oracle programs or arbitrary configurations.

`CleanRun` requires a finite halting run with exactly `[b]`, all work tapes blank at return, all work heads restored to zero, and inclusive head bounds through the halting time. It intentionally leaves the final input head unrestricted. The compiler's return phases restore the real input head to position one and the selected argument heads to zero. In particular, the input return begins by moving left; it does not mistake the right blank on an empty input for an already-restored left boundary.

`CallOK` separately requires: a duplicate-free argument list; real input position one; actual buffer encodings on argument tapes; argument heads at zero; intervals including `-1` and each word's right boundary; and a `CleanRun` with the **same** oracle answer used in the abstract step. Therefore `tapeWord`'s arbitrary-tape default cannot introduce an unrealizable oracle into the compilation theorem. Duplicate arguments are semantically definable abstractly, but the theorem deliberately rejects them because one physical head cannot independently track two argument segments.

The exact conclusion of `compile_correct` is finite-prefix simulation: for the supplied abstract step count `N`, some physical time reaches its `seam`, with inclusive head bounds. There is no halting premise or unconditional halting conclusion in that statement. If the abstract endpoint halts, its seam halts; `compile_space` explicitly adds that premise and the output equality. Thus the conditional docstring follows from the stronger prefix interface. The module's shorthand must be read with those conditions.

`compile_space` charges

`sum_r (hi(r)−lo(r)+1).toNat + kD·(2B+1)`.

The `+1` counts inclusive endpoints and therefore tape origins. At ARM level, intervals `[-1,W]` contribute `m(W+2)`. A bank has twice the maximum component tape count, accounting for data and cleanup markers. Its radius is at least one, even when the selected original decider has zero space; idle padded tapes still visit their origins. Cleaning between calls restores a reusable seam. Repeated calls do not enlarge the union of visited coordinates beyond the fixed charged windows.

`arm_decides` fixes finite decidable labels, a finite family of globally correct `LOGSPACE` languages, and a single ARM. For every input, `hcorr` must give `AHalt` from the live initial label, zero registers, and no answer, ending with the target membership bit. Its pre-endpoint invariant is `PreS` plus

`length (Nat.bits (register_value+1)) ≤ K·logSpace(input_length)`.

The successor in this bound budgets increment carry, including zero-to-one. `PreS` requires distinct equality operands, canonical valid inputs for input-component comparisons, and distinct call arguments. Validation instructions can reject malformed input without requiring the input to have been valid beforehand. A reflexive zero-step `AHalt` of an already answered configuration cannot falsify this theorem: its specified initial state is live and unanswered.

Virtual inputs have length at most `2n+2+m(2W+2)`, with `W=K·logSpace n`. This is `O(n+1)` for a fixed program. Logarithmic space in the virtual-input length therefore stays logarithmic in the original length. `arm_decides_poly` replaces the bit-width invariant with a uniform polynomial bound on numeric register values; it does not bound the run's time. Halting plus the eventual compiled space bound supplies polynomial time by configuration counting when needed.

The restrictions have concrete consequences: a self-comparison instruction must be simplified or implemented using a different fragment; repeated call arguments require separate copies; input comparison requires validation. None creates a gap between the antecedent and the compiled conclusion. The noncomputable abstract oracle and choice operations are specification devices; finite deciders discharge them before a `FinTM` class witness is produced.

### 5. Implicit computation, indexing zero, and composition

The index convention preserves the intended notion. The translation is `j=i+1`: `i<length(f(x))` corresponds exactly to the book's positive index bound. Canonical binary successor/predecessor translations are logarithmic-space operations; the supplied binary toolkit supports this, although the general reduction/composition theorem is still future work.

Pairing is `dbl x ++ [false,true] ++ Nat.bits i`. Inverting the pair recovers `x` and `Nat.bits i`; applying `bitsVal` recovers `i`. Thus the map `(x,i) ↦ pairEncode x (Nat.bits i)` is injective. At `i=0`, `Nat.bits 0=[]`, but the separator remains: for `x=[]` the encoding is `[false,true]`, not the empty word. A noncanonical payload such as `[false]` does not encode zero in `indexLang`: no natural has that canonical expansion.

The bit language returns false out of range. The length language separately distinguishes a valid zero bit from absence: for `f(x)=[false]`, the bit query at zero rejects while the length query at zero accepts. For `f(x)=[]`, both reject every index. No ambiguity or collision appears at the boundary.

The polynomial output-length conjunct is indispensable when composing implicit computations: relevant indices have logarithmic bit length relative to the original input. A future composition proof must also reject malformed or oversized query encodings, rather than silently assuming they were generated by a well-formed caller. `UnaryLogspace` intentionally omits this output bound; it is not itself interchangeable with `ImplicitlyLogspaceComputable`. For example, `g(n)=true^(2^n)` has simple unary bit/length predicates, since for a canonical index `i`, `i<2^n` is equivalent to `length(bits i)≤n`. The output is not polynomially bounded. This is why the conversion theorem's explicit length hypothesis matters.

The received `ImplicitlyLogspaceComputable.computesInSpace` gives a whole-output machine, and the time consequence follows from the count. It is one direction of the relevant equivalence, not all of Exercise 4.8 or Lemma 4.17. The received counter-program closure works for the stated one-way input model. None asserts general implicit composition.

### 6. Clock budgets and prefix preparation

`ctrVal` is ordinary little-endian value on arbitrary bit lists; canonicality is not required. In particular `[]` and an all-false list both have value zero. For canonical words, `ctrVal (Nat.bits v)=v`. Thus the clock budget generated for `g(length x)` is numerically the same budget used by `diagLang`.

The loop decrements before executing each simulated step. A positive budget permits exactly that many simulated steps; halting on the final permitted step is detected on that step, before another underflow check. The Boolean answer is false exactly when the completed output is the singleton `[true]`. An initial live machine cannot already have computed that output at time zero, so a zero budget correctly produces true without a simulated step. A machine that outputs multiple bits is distinguished by `OutReg`; it is not accepted merely because its first bit is true.

For an independent amortized check, let a positive counter word of length `l` have `j` initial false bits and `p` true bits. A successful decrement preserves length, decreases value by one, and changes the popcount to `p+j−1`. Therefore the decrease in

`4·value + 2(l−popcount) + l + 1`

is `4+2(j−1)=2j+2`. This pays for the `j` borrow moves, one simulated-machine step, and `j+1` return moves when simulation continues. Early halting only shortens the cycle. A zero-valued length-`l` counter underflows after `l+1` moves, at most its potential `3l+1`. Redundant high zeros are paid for by the length term.

Setup costs at most `tK+l+n+5`; the loop costs at most `4v+3l+1`. Their sum is the stated `tK+4l+n+4v+6`. No one-step deficit remains.

For prefix preparation, `scanPre (pairEncode α w)=dbl α ++ [false,true]`. Appending the original input gives exactly `pairEncode α (pairEncode α w)`, the self-application required by `diagSim`. The zero-work-tape preparer scans the prefix, rewinds, and copies the input within `3n+5`; empty input is covered. The total scanner also stops at an unequal `10` pair on arbitrary malformed input. That default does not affect the lemma about genuine pair encodings.

### 7. Fitness for the next chapter phases

**The convention in finding 1 is the present adoption wall.** Make every asymptotic space bound positive at every formal input length, or deliberately redefine the class. This must happen before assigning book meaning to linear space or a general hierarchy statement. Little-o hierarchy gaps can absorb machine-dependent multiplicative constants; exact constant-factor separations would require different statements. Constructibility and logarithmic lower bounds must be written into the future theorems, not inferred from unrestricted `SPACE`.

The per-input existential time in `ComputesInSpace` is appropriate. It asserts total computation by a single finite machine, and the configuration theorem derives a uniform time bound from a uniform space bound. No uniform-time existential has to be added to the definition.

For future `NSPACE`, the path quantifiers must be chosen and documented: accepting-path existence, correctness on rejecting inputs, and whether the space bound and halting requirement apply to all branches are separate obligations. The campaign's declared visited-cell convention is a reasonable basis for the intended count. A definition using only nonblank support could not reuse the present bounded-head encoding without a head-position/visited-range justification; arbitrarily long blank excursions are otherwise uncharged. The announced convention is therefore suitable for the intended theory, but should not be described as a proved equivalence to an unrestricted nonblank-only measure. No such equivalence is received. This observation does not audit a nonexistent NSPACE definition.

Configuration graphs need two additional explicit constructions. First, the current count is not an efficient vertex encoding/decoding or an adjacency CNF theorem. Second, `core` deliberately discards output, so it is insufficient by itself to label a terminal vertex as accepting. Two configurations with the same core and outputs `[true]` and `[false]` have the same core code. Acceptance must be represented in finite control or a separately bounded output summary. `CleanRun` also does not reset the input head; blank work tapes and zero work heads alone do not supply a unique terminal configuration. A normalizing return phase can provide one.

The ARM architecture is not a wall for polynomial space: `arm_space` already takes a general width `W` and bank radius `B`; the `LOGSPACE` wrapper specializes those parameters. A new nondeterministic compiler, graph-access primitives, and general implicit composition remain real work. The one-way `CounterProg.rd` is an explicit limitation and cannot simply be treated as random input access. These are unproved future interfaces, not hidden capabilities of the received toolkit.

## Adversarial instantiations

These are concrete mathematical substitutions into the received definitions and contracts. They are not presented as newly kernel-checked Lean examples.

| Test | Instantiation and calculation | Outcome |
|---|---|---|
| A1 | `s(n)=0`; use any input and `k≤spaceUsed≤c·0`. | Forces `k=0`; zero-space class is nonempty but restricted to finite-state input computation. |
| A2 | `s(n)=n`, input `[]`; the zero at this single length forces the same machine to have `k=0` everywhere. | Material collapse of intended linear space; finding 1. The same occurs for a bound positive everywhere except length seven. |
| A3 | A zero-tape machine emits a fixed Boolean and halts in one step, on every input. | Empty and universal languages belong to `SPACE s` for every `s`, even with `c=0`. No hidden positive-tape requirement. |
| A4 | A zero-tape parity scanner on `n` symbols, halting at the end in `n+1` steps. | Nonconstant language in zero space; refutes dropping the input factor below log space. |
| A5 | A zero-tape, one-state stationary self-loop, never emitting. | Space remains zero forever, but `ComputesInTime.of_spaceUsed_le` cannot be applied: its halting hypothesis fails. |
| A6 | `n=0` or `1` in `LOGSPACE`; `k=0` in the count. | `logSpace=1`; `configBound=(q+1)(n+2)`. Neither theorem divides by zero or loses the input positions. |
| A7 | `indexLang`, with `x=[]`, `i=0` and `i=1`. | Encodings are `[false,true]` and `[false,true,true]`, respectively. They are distinct; `[]` and noncanonical payload `[false]` do not enter accidentally. |
| A8 | `f(x)=[]` versus `f(x)=[false]`, query index zero. | The bit answers coincide (false), but length answers differ. The two-language definition preserves output length. |
| A9 | `g(n)=true^(2^n)` in `UnaryLogspace`. | The bit/length queries remain simple canonical-index comparisons; polynomial length fails. The extra hypothesis in its conversion theorem is necessary. |
| A10 | One register constantly equal to `B`, one abstract `goto` step. | Register stays bounded by `B`, but `sim_run`'s actual hypothesis `B+1≤B` fails. Finding 2, not a failure of `exists_tm`. |
| A11 | `whole` call, `x=[]`, empty argument list; compare with duplicate arguments `[r,r]`. | The first is permitted and has empty virtual input, not a pair. The second is excluded by `CallOK`/`PreS`. Findings 3 and the compiler's aliasing guard. |
| A12 | `valP` on `pairEncode [] [false]`; `.jeq r r`; `.jeqIn` on malformed `[]`. | Validation rejects the noncanonical payload. Self-comparison and malformed input comparison fail `PreS`, even when their abstract branch is meaningful. No application of `arm_decides` escapes those checks. |
| A13 | `ReachesB` at `T=0` with the distinguished head at `L+1`, for `L≥0`. | Relation holds reflexively; no endpoint bound follows. Finding 6. |
| A14 | Clock words `[]` and `false^l`. | Both allow zero simulated steps; the latter pays `l+1` underflow moves within `3l+1`. |
| A15 | Clock word `[true]`; machine halts with `[true]` after exactly one step, or instead needs two steps. | First case returns false; second times out and returns true. The final allowed step is included. |
| A16 | Budget two; machine emits true, then false and halts. | Completed output is `[true,false]`; clock returns true. A first-bit-only acceptance bug is absent. |
| A17 | `lenEq_mem_P` and `lenLe_mem_P` at malformed `z=[]`. | Both accept via default empty projections. Finding 5. |
| A18 | `AHalt` with `K=0`, at least one register, and the prescribed live zero-register start in `arm_decides`. | `T=0` cannot halt; at time zero `length(bits(0+1))=1`, so `1≤0` fails. The degenerate invariant does not prove every language logspace. With no registers this particular obstruction is legitimately absent. |

## Proposed machine-checkable sanity targets

These are requested follow-up statements, not claims of fresh elaboration. S1–S3 isolate the major finding using the existing visited-set API; the mathematical derivation above settles its substance. No change to tactic proofs is requested.

| ID | Exact mathematical target | Purpose |
|---|---|---|
| S1 | For every `M : FinTM Bool`, `x`, `t`, prove `M.k ≤ M.tm.spaceUsed (M.tm.initCfg x) t`. | Make the initially visited origins visible at the public interface. |
| S2 | From `M.ComputesInSpace f s` and `∃n, s n=0`, derive `M.k=0`. | Verify the zero-at-one-length propagation. |
| S3 | From `∃n, s n=0`, prove `SPACE s = SPACE (fun _ => 0)`; instantiate with `s(n)=n`. | Make the adoption convention impossible to overlook. |
| S4 | For everywhere-positive `s`, prove `SPACE s = SPACE (fun n => s n+1)`; separately prove `SPACE (fun n => s n+1)=SPACE (fun n => max 1 (s n))` for arbitrary `s`. | Document exactly when finite additive normalization is harmless. Use `s+1≤2s` or `s+1≤2 max(1,s)`. |
| S5 | `pairEncode x (Nat.bits i) = pairEncode y (Nat.bits j) ↔ x=y ∧ i=j`. | Package canonical index injectivity, including zero, from pair decoding and `bitsVal_bits`. |
| S6 | Exhibit a zero-tape constant Boolean decider and a zero-tape parity decider with the stated space and time contracts. | Bind the semantic zero-space characterization to the repository model. Full equivalence with a formal regular-language class requires an automata bridge not included here. |
| S7 | Produce the three clock cases: zero budget; exactly-one-step accepting halt with budget one; two-bit completed output with budget two. | Small executable regressions for the endpoint and output-shape contracts. |
| S8 | Prove the no-argument virtual-input identity and show `¬ValidPlain (pairEncode [] [false])`; exhibit reflexive `ReachesB` outside the box. | Lock in the boundary meanings underlying findings 3, 4, and 6. |
| S9 | Add an optional reachable-register-bound version of `CounterProg.sim_run`, retaining `s.pos≤length x` and assuming each pre-step register is at most `B`. | Deliver the broader run-bound interface if the opening docstring is retained. |

The bundle suffices to settle the numerical and logical checks in Q1–Q6 by inspection of definitions and theorem contracts. It does not settle S6's identification with a repository regular-language predicate, revision provenance, or the future graph/NSPACE interfaces. Those limits are stated rather than assumed away.

## Appendix A. All blind definition restatements

Coverage: 217 `def`, 6 `abbrev`, 17 `inductive`, and 4 `structure` declarations: **244 total**. Compiler-generated recursors and constructor functions are covered by their parent type, not counted as additional source declarations. Structure fields and instruction alternatives are included in the parent restatement. Names are local to the module shown, including nested namespaces and private definitions.

“Matches; auxiliary” means the independently obtained meaning agrees with its implementation docstring; the module-level source comparison explains why it is not being equated to a numbered book definition. A total helper outside its guarded simulation hypotheses is not thereby a correctness theorem.

### `TCSlib/Complexity/TuringMachine/UnaryTape.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `ones` · 44 | The integer-indexed tape contains true precisely at positions 0 through m−1 and blanks elsewhere. | Matches; auxiliary. |
| `wrT` · 78 | An absent write request preserves the tape; a present request replaces the addressed cell, possibly with blank. | Matches; auxiliary. |

### `TCSlib/Complexity/TuringMachine/CounterProg.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Instr` · 71 | Instructions halt, jump, emit a bit, increment/decrement a natural register, test zero, print a register's many true bits, or read the next input bit. Register operands belong to Fin R. | Matches; unary-print is one abstract step, not one TM step. One-way input is explicit. |
| `St` · 93 | An abstract configuration stores an optional instruction label, natural-valued registers, a natural input cursor, and an accumulated output list. | Matches; arbitrary states need the separate cursor/register simulation preconditions. |
| `step` · 106 | Halted configurations are fixed. Otherwise execute the selected instruction, with truncated subtraction, append-only output, and input advance only when rd finds a bit; an exhausted input leaves the cursor unchanged. | Matches; auxiliary. |
| `run` · 125 | Iterate the abstract step function exactly t times, including stationary steps after halting. | Matches; auxiliary. |
| `init` · 129 | Start at the supplied label with all registers zero, input cursor zero, and empty output. | Matches; auxiliary. |
| `TSt` · 185 | Compiled control states distinguish instruction entry, decrement/zero-test return, and the outward/return scans for unary printing. | Matches; auxiliary. |
| `act` · 199 | Construct an action that changes only the selected register tape, together with the specified input move, optional output, and next state. | Matches; auxiliary. |
| `ctl` · 204 | Construct an action affecting input, output, and control only; every work tape remains stationary and unwritten. | Matches; auxiliary. |
| `tr` · 208 | Compile each instruction using a unary tape whose head is at the register's right boundary. Tests and decrement inspect the preceding cell; printing scans left while emitting true and returns right. | Matches; auxiliary. |
| `toTM` · 237 | Bundle that transition table into a finite machine with R work tapes and the selected entry label, requiring finite decidable labels. | Matches; finite labels are required here even though the raw program type is unrestricted. |
| `enc` · 246 | Represent each register by its unary tape and right-boundary head, map the optional label to compiled entry, preserve output, and clamp cursor+1 to the right input endmarker. | Matches; auxiliary. |

### `TCSlib/Complexity/TuringMachine/CounterProgRun.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Goes` · 65 | For every initial output prefix, some run of at most b abstract steps reaches the specified label, register values and cursor, appending exactly e. | Matches; universal quantification over the old output prefix supports composition. |
| `MOp` · 204 | An output-template operation either emits one fixed bit or prints one register in unary. | Matches; auxiliary. |
| `MOp.exec` · 211 | Interpret one output-template operation as a bit list at the supplied register valuation. | Matches; auxiliary. |
| `tmplInstr` · 217 | At an in-range template index emit its operation and continue to the next indexed label; out of range jump to next. | Matches; auxiliary. |
| `LinE` · 262 | A nonnegative linear expression is a list of register references, allowing repetitions, together with a natural constant. | Matches; auxiliary. |
| `LinE.val` · 265 | Evaluate the expression by summing the referenced register values with multiplicity and adding its constant. | Matches; auxiliary. |
| `linOps` · 268 | Print each referenced register, then emit one true bit per unit of the constant. | Matches; auxiliary. |
| `bitsOps` · 290 | Convert a fixed bit list into consecutive single-bit output operations. | Matches; auxiliary. |

### `TCSlib/Complexity/ClassNP/CounterProgPolyTime.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

No definition-like declarations. Its received contribution consists of theorem statements, checked in Appendix B.

### `TCSlib/Complexity/ClassNP/ExpPoly.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `ExpPoly` · 42 | There are fixed natural K and k such that T(n) is at most 2 raised to K(n+1)^k for every n. | Matches this implementation normal form; not an exact restatement of a numbered chapter-3/4 definition. |

### `TCSlib/Complexity/ClassNP/PolyTimePairing.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `pairMapSnd` · 77 | Decode a pair, apply g to its second component, and re-encode; return the empty word on malformed input. | Matches; malformed input is deliberately totalized to the empty word. |
| `pairFstD` · 206 | Return the decoded first component, with the empty word as the malformed-input default. | Matches definition docstring; the later language prose needs finding 5. |
| `pairSndD` · 209 | Return the decoded second component, with the empty word as the malformed-input default. | Matches definition docstring; the later language prose needs finding 5. |

### `TCSlib/Complexity/ClassNP/PClosure.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

No definition-like declarations. Its received contribution consists of theorem statements, checked in Appendix B.

### `TCSlib/Complexity/ClassNP/Transducer.lean`

Source comparison: supporting program/FP/EXP infrastructure. These are implementation definitions, not numbered chapter-3/4 definitions; some module docstrings trace their original use to §6.2. They are included because the reception manifest includes them.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `transduce` · 51 | Scan left to right, updating a finite-state accumulator and emitting zero or one bit for each input bit; emit nothing at the end. | Matches; auxiliary. |
| `transducerTr` · 67 | On a bit, emit the transducer's optional bit, advance input, and update state; on blank, halt without output or work-tape activity. | Matches; auxiliary. |
| `transducerTM` · 73 | Bundle the transducer as a finite machine with zero work tapes and the given initial state. | Matches; zero work tapes are permitted, including on empty input. |

### `TCSlib/Complexity/SpaceComplexity/Basic.lean`

Source comparison: Definitions 4.1, 4.5, and 4.16, with the explicit conventions examined in Q2 and Q5.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `ComputesInSpace` · 85 | For every input there exists a finite time by which M has halted with output f(x), and the total work-tape space visited through that same time is at most s(length x). No uniform time bound is required. | Matches the deterministic measure of Def. 4.1 and the declared function/output adaptation. Q2 explains the zero-bound effect. |
| `DecidesInSpace` · 91 | Compute exactly the singleton Boolean membership indicator of L under ComputesInSpace. | Matches the declared singleton-indicator convention; both answers require halting. |
| `SPACE` · 110 | Choose one natural constant c and one finite machine, uniformly over all inputs, that decides L within c·s(n) visited work cells. No positivity, constructibility, or eventual-bound qualification is included. | Finding 1: dropping the standing lower-bound convention makes even one zero globally consequential. |
| `logSpace` · 120 | The bound is Nat.log 2 n plus one, including value one at n=0 and n=1. | Positive normalization is explicit and safe at n=0,1; it supplies the Def. 4.5 asymptotic scale. |
| `LOGSPACE` · 125 | Apply SPACE to logSpace. | Matches Def. 4.5 with the documented positive normalization; Q3 checks its time consequence. |
| `indexLang` · 129 | A word is accepted exactly when it is the pairing of some x and the canonical binary expansion of some natural i for which p(x,i) holds. Other encodings are rejected. | Matches the declared canonical pairing convention; malformed/noncanonical words are excluded, including at index zero. |
| `ImplicitlyLogspaceComputable` · 138 | Require a uniform polynomial output-length bound C(length x+1)^c, a LOGSPACE language for true output bits with false outside the list, and a LOGSPACE language for indices strictly below its length. | Def. 4.16 with the declared zero-based translation and all-length polynomial normalization; Q5 finds no lost strength. |

### `TCSlib/Complexity/SpaceComplexity/ConfigCount.lean`

Source comparison: implementation of the deterministic configuration argument in Claim 4.4/Theorem 4.2; the explicit input factor and omitted output are examined in Q3.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `core` · 73 | Discard output from a configuration, retaining optional control state, input position, work-tape contents, and work-head positions. | Matches; adequate for time-to-halt, but acceptance/output reconstruction needs extra data in a future graph. |
| `posCode` · 258 | Translate an integer by B, truncate below zero, and clamp above 2B to obtain a code in Fin(2B+1). It is not globally injective. | Matches; injectivity is only asserted on the bounded interval, not globally. |
| `coreCode` · 269 | Encode the core by recording each work tape on the window from −B through B and clamping each work-head coordinate into that window's finite index set. | Matches; finite-window completeness relies on reachable bounded cores and blankness outside. |
| `configBound` · 311 | Multiply the number of optional states, n+2 input positions, three symbols at every cell of every length-(2s+1) tape window, and 2s+1 head choices per work tape. Output is omitted. | Matches the displayed formula; conservative deterministic count with explicit n factor. Q3 supplies the independent derivation. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Layout.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Seg` · 63 | A segment is a bit list paired with a Boolean indicating whether to double each bit. | Matches; auxiliary. |
| `render` · 66 | Return the underlying word or its bit-doubled version according to the segment flag. | Matches; auxiliary. |
| `rlen` · 69 | Return the underlying length, multiplied by two precisely when the segment is doubled. | Matches; auxiliary. |
| `vword` · 81 | Render segments in order with the separator false,true between consecutive segments; the empty list renders to empty. | Matches; auxiliary. |
| `off` · 87 | Compute a segment offset by adding each preceding rendered length plus two. Beyond the supplied list it is a total recursive default, not a validity certificate. | Matches; auxiliary. |
| `seg` · 93 | Retrieve a segment by index, defaulting to the empty undoubled segment. | Matches; auxiliary. |
| `TPos` · 197 | A virtual input position is a left boundary, a word-cell index with a parity bit, or a right boundary. | Matches; auxiliary. |
| `wlen` · 204 | Return the undoubled word length of the selected segment, using seg's default. | Matches; auxiliary. |
| `TPos.Valid` · 207 | Only cell positions are constrained: their index must be below the segment's undoubled length. Both boundaries are always valid. | Matches; segment-index range is a separate premise in the movement/symbol theorems. |
| `cellOff` · 212 | For a doubled segment use twice the cell index plus its parity bit; otherwise use the cell index and ignore parity. | Matches; auxiliary. |
| `vpos` · 217 | Translate a segment-local position to the global input coordinate: left at its offset, cells at offset+1+cellOff, right at offset+1+rendered length. | Matches; auxiliary. |
| `tmove` · 233 | Move one virtual cell, handling doubled-bit parity, empty segments, separators, and saturated exterior endmarkers; correctness is restricted to valid segment positions. | Matches its guarded movement contract; total default behavior outside valid positions is not a simulation claim. |
| `vsym` · 370 | A cell exposes its underlying bit. Interior left/right boundaries expose true/false respectively; the two exterior boundaries expose blank. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Program.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Mode` · 67 | Call input modes select either the whole input with bit doubling, or the initial run of true bits without doubling. | Finding 3: paired-input prose needs the nonempty-argument qualification. |
| `Mode.seg0` · 76 | Construct that first virtual segment from x; unaryFst takes the maximal initial run of true bits literally. | Matches the function; the general pair-shape shorthand has finding 3. |
| `argSegs` · 81 | Turn argument words into segments, doubling all except the last. | Matches; auxiliary. |
| `CallSpec` · 114 | A call records a finite decider index, input mode, ordered list of register arguments, and yes/no continuation labels; distinct arguments are not a field-level requirement. | Matches; distinctness is deferred to CallOK, not enforced by this structure. |
| `RProg` · 128 | A program consists of a raw multitape machine and an optional call specification at each label. The raw model imposes no finiteness on labels. | Matches; the raw semantic model is broader than the finite class-witness interface. |
| `callSegs` · 135 | Prepend the mode-selected input segment to the argument-register words rendered by argSegs. | Matches; zero arguments produce one segment and no separator, as in finding 3. |
| `CSt` · 147 | Compiled states distinguish ordinary execution, decider simulation with virtual-head bookkeeping and first output bit, input rewind, and register rewind phases. | Matches; auxiliary. |
| `gstep` · 166 | Update virtual segment/parity/direction bookkeeping and the physical head motion for one requested virtual move, using character/boundary and endpoint flags. | Matches; auxiliary. |
| `toFin` · 179 | Clamp the natural segment number to m to obtain an element of Fin(m+1). | Matches; auxiliary. |
| `segDbl` · 182 | Segment zero is doubled exactly in whole mode; subsequent segments are doubled except the last argument. | Matches; auxiliary. |
| `segReg` · 186 | Select the argument register for a positive segment number; out-of-range requests default to register zero, requiring m>0. | Matches; the m>0 witness and call-validity hypotheses prevent misuse of the default register. |
| `isCharRead` · 191 | In the unary prefix segment only true is a character; in other segments any nonblank symbol is a character. | Matches; auxiliary. |
| `virtSym` · 195 | Translate a physical symbol plus segment/boundary information into the symbol the decider sees, inserting virtual separators and endmarkers. | Matches; auxiliary. |
| `regMove` · 201 | Move only the selected register head, writing no cells. | Matches; auxiliary. |
| `nextRet` · 206 | Continue restoring argument heads while both argument and register indices are in range; otherwise resume the yes/no continuation. | Matches; auxiliary. |
| `dIdle` · 216 | The decider-bank action neither writes nor moves any head. | Matches; auxiliary. |
| `ctr` · 224 | Run ordinary program steps on one tape bank; at calls simulate a decider on a virtual concatenation, retain its first output bit, then rewind input and argument heads. Decider-bank erasure is delegated to the decider's clean-run contract. | Matches; taking only the first output bit is sound at calls because CleanRun requires exactly one bit. |
| `compileTM` · 284 | Build the raw compiled machine with m+kD tapes and initial ordinary-program state at l₀. | Matches; a raw machine, with finite-state bundling deferred to compileFinTM. |
| `seam` · 291 | Embed a program configuration into the compiled machine, preserving input, registers and output while adding blank decider tapes at head position zero. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Sim.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `trackPos` · 52 | Translate local left/cell/right positions into physical coordinates −1/c/undoubled word length. | Matches; auxiliary. |
| `TPos.isCell` · 58 | Test whether a virtual position is a cell rather than a boundary. | Matches; auxiliary. |
| `Consistent` · 63 | Left/right boundaries require the corresponding direction flag; doubled cells require the stored parity to agree. Undoubled-cell parity is unconstrained. | Matches; auxiliary. |
| `regPos` · 202 | For argument registers, put already-passed segments at their right boundary, future segments at −1, and the active segment at its current physical position; preserve other register heads. | Matches; auxiliary. |
| `inPos` · 210 | Use the current physical input coordinate when segment zero is active; otherwise park input at the end of its selected prefix. | Matches; auxiliary. |
| `TrackRel` · 216 | Relate a compiled and decider configuration by virtual input position, unchanged register tapes, matching decider-bank tapes/heads, correct register/input heads, and preserved caller output. | Matches; caller output and all register tapes are preserved while virtual heads move. |
| `SimRel` · 231 | A live compiled simulation and a live decider have the same decider state, TrackRel, and an accumulator equal to the decider output's first bit. | Matches; auxiliary. |
| `HaltRel` · 238 | A compiled return-entry state corresponds to a halted decider satisfying TrackRel; its result is the first decider output bit, defaulting false. | Matches; singleton output is a stronger call-level premise, not part of this general relation. |

### `TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `mkCfg` · 43 | Assemble a compiled configuration from separate register and decider tape/head banks and the supplied control, input position, and output. | Matches; auxiliary. |
| `leftSide` · 271 | Determine whether a particular argument lies to the right of the virtual head or is the active argument approached from its left boundary. | Matches; auxiliary. |
| `retPos` · 387 | Reset heads of argument registers already processed by the restoration loop to zero; retain all other positions. | Matches; auxiliary. |
| `RegBox` · 392 | Nonargument heads retain their original positions; argument heads lie between −1 and the corresponding word's length, inclusively. | Matches; argument bounds are inclusive and include the empty-buffer boundaries. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Call.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `CleanRun` · 53 | From blank tapes at zero and the specified state/input, a finite run halts with exactly [b], blanks every work tape, resets every work head to zero, and keeps each head within [−B,B] throughout. Final input position is unrestricted. | Matches; final input position is intentionally unrestricted and caller return restores it. Q4. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Compile.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `tapeWord` · 52 | If the entire tape is the buffer encoding of a finite word, choose that word; otherwise return empty. This is a mathematical, noncomputable decoder. | Matches; mathematical choice, with actual buffer shape required before an atomic call is compiled. |
| `regWords` · 68 | Decode each register tape using tapeWord. | Matches; auxiliary. |
| `rstep` · 73 | Halted configurations stay fixed; noncall states take an ordinary step; calls atomically choose a continuation from the oracle on the virtual input, reset input to position one, and preserve registers/output. | Matches; atomic oracle semantics are discharged by CallOK rather than asserted free of cost. |
| `rrun` · 87 | Iterate the atomic-call step n times. | Matches; auxiliary. |
| `CallOK` · 100 | At any actual call require distinct argument registers, input at position one, valid buffer tapes and zero argument heads, adequate register intervals, and a clean decider run with the prescribed oracle answer and radius B. | Matches its declaration; module list has the nonexistent plural spelling in finding 8. |
| `compileFinTM` · 214 | Bundle compileTM as a finite machine when both program and decider control types are finite and decidable. | Matches; finite decidable program and decider labels are explicit. |

### `TCSlib/Complexity/SpaceComplexity/Machines/CleanSweep.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `CPh` · 41 | Cleanup phases mark the final head cell, seek the right boundary, erase leftward, and return to the marked origin. | Matches; auxiliary. |
| `CleanSt` · 53 | Control states initialize tracking, simulate the original state, or clean one selected tape in one cleanup phase. | Matches; auxiliary. |
| `idleK` · 65 | A bank action with no writes or head movement. | Matches; auxiliary. |
| `clAct` · 69 | Apply the specified data/marker writes and common head motion to one matching pair of tapes, leaving every other tape and input/output unchanged. | Matches; auxiliary. |
| `clNext` · 75 | Advance to cleanup of the next tape, or halt after the final tape. | Matches; auxiliary. |
| `cleanTM` · 80 | Double the tape bank, mark the origin and visited interval during simulation, preserve emitted output, and upon halting erase data/markers and restore each head to zero. Zero-tape simulation needs no cleanup loop. | Matches; doubles the data bank for markers, including correct k=0 behavior. |
| `ccfg` · 112 | Assemble a cleanup-machine configuration from separate data and marker banks. | Matches; auxiliary. |
| `wr` · 137 | Perform an optional cell update, distinguishing no write from writing blank. | Matches; auxiliary. |
| `markI` · 180 | Mark the origin by true, other points in the inclusive interval by false, and all remaining points blank. The origin is marked even if outside the interval. | Matches the total definition; the origin marker is unconditional, while meaningful interval uses contain zero. |
| `PB` · 184 | Every work head has absolute coordinate at most the supplied integer B. | Matches; pointwise head-radius predicate, not a total visited-space predicate. |
| `eraseAbove` · 275 | Keep cells at coordinates at most p and blank all cells above p. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Clean.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `markSet` · 54 | Mark origin true, other members of a finite set false, and all remaining coordinates blank. | Matches; auxiliary. |
| `simSt` · 58 | Map a live state to simulation mode; map a halted state to first cleanup, or directly to halt when there are no tapes. | Matches; auxiliary. |
| `visB` · 68 | Collect head positions at times strictly below t in the original run from state q on V. | Matches; the strict time cutoff differs from the inclusive visited-space measure and is used for marker bookkeeping. |
| `simCfg` · 72 | Embed the original run at time t with matching heads, output and input, plus marker tapes for visB and the origin. | Matches; auxiliary. |
| `stSt` · 220 | Select cleanup of tape i when i<k; otherwise use the halted state. | Matches; auxiliary. |
| `stg` · 223 | Represent a cleanup stage with all tape pairs of index below i blank and their heads at zero, preserving the remaining banks, input and output. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `padTM` · 50 | Run an original transition on the first k tracks of a K-track machine, supplying blanks for absent tracks and idling extra tracks. Semantic simulation requires k≤K separately. | Matches; k≤K is a theorem premise, not a condition on the total construction. |
| `padCfg` · 58 | Keep original tracks whose indices exist and fill additional tracks with blank tapes/zero heads; copy control, input and output. | Matches; auxiliary. |
| `sigmaTM` · 110 | Combine machines with a common tape count using an optional tagged control state. Its default state halts; a tagged state runs the corresponding machine. | Matches; auxiliary. |
| `sigCfg` · 120 | Embed a component configuration by tagging its live state with the component index; preserve other configuration fields. | Matches; auxiliary. |
| `bankK` · 151 | Take the maximum work-tape count of the finite decider family, with zero for an empty family. | Matches; finite maximum is zero for an empty family. |
| `BankS` · 158 | Use an optional dependent tagged union of the component machines' state types as the bank state type. | Matches; auxiliary. |
| `bankTM` · 161 | Pad all deciders to bankK, combine their state spaces, and apply the cleanup transformation, using twice bankK tapes. | Matches; its tape count includes the extra cleanup-marker bank. |
| `bankStart` · 165 | Start the cleanup wrapper at the tagged initial state of a chosen component decider. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `bitsVal` · 44 | Evaluate a bit list in little-endian binary; the empty list evaluates to zero. | Matches; auxiliary. |
| `incW` · 50 | Increment a little-endian bit list by propagating carry through initial true bits, extending an all-true word. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Lib.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `regCfg` · 66 | Replace one register tape/head and set a live control label, preserving the rest of the configuration. | Matches; auxiliary. |
| `regAct` · 76 | Write and move only one selected register tape and continue to a specified live label; input/output are unchanged. | Matches; auxiliary. |
| `incCAct` · 139 | Propagate increment carry by turning true into false and moving right; at false or blank write true and begin leftward return. | Matches; auxiliary. |
| `incBAct` · 145 | Move left through nonblank cells and then step right from the first blank to the continuation. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `decW` · 42 | Implement binary predecessor on canonical little-endian words, with empty fixed at zero; its total behavior on noncanonical words is merely the given recursion. | Matches the canonical predecessor contract; no general normalization claim for arbitrary bit lists. |
| `Canon` · 49 | A word is empty or its final, most significant bit is true. | Matches; zero is empty, so a nonempty all-false word is excluded. |
| `decDAct` · 114 | Borrow through false bits, change the first true to false, or start returning on blank; a follow-up phase determines whether the top bit must be removed. | Matches; auxiliary. |
| `decLAct` · 122 | Inspect the cell after the changed bit; at blank return to erase the top bit, otherwise return without erasure. | Matches; auxiliary. |
| `decEAct` · 129 | Erase the current bit and move left to the decrement-return phase. | Matches; auxiliary. |
| `toEndAct` · 317 | Scan right through a register word, then step left from the blank to the supplied continuation. | Matches; auxiliary. |
| `clrEAct` · 382 | Erase nonblank cells moving left; at blank step right and continue. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `halfLAct` · 47 | Move left, replacing the current bit by the carried optional bit and carrying its previous bit; at blank step right and finish. | Matches; auxiliary. |
| `halfSt` · 65 | Select the no-carry, false-carry, or true-carry phase according to an optional bit. | Matches; auxiliary. |
| `eqCfg` · 205 | Set a live state and both selected register heads to the same integer position; preserve all tapes, input and output. | Matches; auxiliary. |
| `mv2Act` · 210 | Move each selected head by the supplied direction once, even when the two indices coincide; write nothing. | Matches the total action; two-independent-register simulation additionally assumes distinct indices. |
| `eqCAct` · 229 | Compare the two current symbols, scan right while equal and nonblank, then start the appropriate leftward return for equality or inequality. | Matches; auxiliary. |
| `eqBAct` · 234 | Return both heads left while the first tape is nonblank, then step right to the chosen continuation. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `ValidPlain` · 46 | The input is a pairing of a unary true word and a canonical binary word. | Matches this definition docstring; the instruction-level shorthand omits canonicality (finding 4). |
| `ValidPair` · 50 | The input pairs a unary true word with a pair of two canonical binary words. | Matches this definition docstring; the instruction-level shorthand omits canonicality (finding 4). |
| `xCfg` · 63 | Set a live control state, input position, and one work-head coordinate, preserving tape contents, other heads and output. | Matches; auxiliary. |
| `xAct` · 72 | Move input and one selected work head without writing, and choose a live continuation. | Matches; auxiliary. |
| `rejAct` · 76 | Emit false and halt, leaving input/work positions and tapes unchanged. | Matches; auxiliary. |
| `inSym` · 99 | Coordinate zero is blank; positive coordinate q reads the zero-based input index q−1 with out-of-range blank. | Matches; auxiliary. |
| `tRun` · 220 | Count the maximal initial run of true bits. | Matches; auxiliary. |
| `valUAct` · 280 | Scan an initial true run while toggling parity; accept a false delimiter only at even parity and reject other endings. | Matches; auxiliary. |
| `valSAct` · 287 | Require the next delimiter symbol to be true; otherwise reject. | Matches; auxiliary. |
| `valWAct` · 293 | Scan a binary word remembering its last bit; reject if the final remembered bit is false, otherwise begin input rewind. Empty words pass. | Matches; auxiliary. |
| `FragOK` · 339 | On a good input, a finite call-free fragment returns to next with original data/output and reset input; on a bad input it halts after appending false. Intermediate configurations only change control/input and retain the selected head at p. | Matches; intermediate obligations are half-open, with separate target/rejection equalities. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `skipAct` · 117 | Skip initial true symbols and then advance past the first nontrue symbol into the second skip phase; standalone malformed-input behavior is not validation. | Matches a fragment action; it is not itself a total validator. |
| `cmpAct` · 123 | Compare input and register symbols, advancing both while equal and nonblank; otherwise begin register return with the equality result. | Matches; auxiliary. |
| `backAct` · 128 | Return a register head left to its first blank, then one step right to the continuation. | Matches; auxiliary. |
| `rewAct` · 134 | Return the input head left to blank, then one step right to the continuation. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `scanPairs` · 47 | Parse repeated equal-bit pairs up to a false,true delimiter, rejecting malformed pairs and noncanonical preceding words; return the suffix after the delimiter. | Matches; tests both pair shape and canonicality of the decoded first word. |
| `Rejects` · 105 | Some finite run halts after appending false and preserving designated head positions; every earlier configuration has the prescribed unchanged data/output shape and makes no calls. | Matches the separate endpoint condition plus strict-prefix invariant. |
| `Reaches` · 112 | Some finite run reaches the exact target, with every earlier configuration preserving the prescribed data/output/head shape and making no calls. A zero-step witness imposes no intermediate conditions. | Matches the formal relation; its zero-step case does not certify the target invariant. |
| `wSt` · 215 | Choose the word-validation phase for no previous bit, previous false, or previous true. | Matches; auxiliary. |
| `valP1Act` · 301 | Read the first bit of a doubled pair and remember it; reject blank. | Matches; auxiliary. |
| `valP2Act` · 307 | Recognize the delimiter subject to canonicality of the previous word, or require the second bit to equal the first and continue with updated last bit; reject other input. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ParseCmp.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `pskip1Act` · 42 | Remember whether the first bit of the next candidate pair is true, advancing input; nontrue defaults to the false phase. | Matches; auxiliary. |
| `pskip2Act` · 48 | At a false,true pair finish skipping; otherwise advance to scan the next pair. Correct use presupposes valid encoding. | Matches; well-formed-input hypotheses justify skipping without full validation. |
| `dcmp1Act` · 116 | Read and remember the first bit of a doubled input pair, advancing input. | Matches; auxiliary. |
| `dcmp2Act` · 122 | At the delimiter test that the register word is exhausted; otherwise compare its current symbol with the remembered first bit, advancing or returning. Validation of equal input pairs is a separate precondition. | Matches; auxiliary. |
| `ReachesB` · 303 | Some run reaches the exact target while all earlier configurations make no calls, preserve tape contents/output and other heads, and keep the selected head in [−1,L]. | Finding 6: the docstring must distinguish the strict prefix from the endpoint. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ARM.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Ins` · 50 | Register instructions increment, decrement, clear, halve, test zero/oddness/equality, call a decider, return a Boolean, validate encoded input, or compare a register with encoded input components. The syntax itself carries no safety proofs. | Finding 4 concerns validation payloads; comparison/call restrictions are separately supplied by PreS. |
| `ARM` · 81 | An abstract register machine is a function from labels to instructions. | Matches; auxiliary. |
| `plainWord` · 84 | Drop the initial true run and the following two symbols, regardless of whether they form valid encoding. | Matches on the advertised format; total malformed-input behavior is guarded by PreS at comparisons. |
| `pairWords` · 87 | Decode the suffix after that same prefix as a pair, defaulting to two empty words on failure. | Matches on the advertised format; default empty components are guarded by PreS at comparisons. |
| `AConf` · 107 | Store an optional current label, natural-valued registers, and an optional final Boolean answer; there is no abstract input head or output stream. | Matches; auxiliary. |
| `astep` · 111 | Execute the specified arithmetic/test/call instruction with fixed input x; return or failed validation halts with a Boolean. Input comparisons use totalized parsers even on invalid inputs. Halted configurations are fixed. | Matches; mathematical oracle semantics need compilation preconditions to become executable. |
| `arun` · 134 | Iterate astep exactly n times. | Matches; auxiliary. |
| `Ph` · 141 | A finite phase type enumerates entry, arithmetic scans, comparison returns, validation, and parsing subphases of compiled instructions. | Matches; auxiliary. |
| `goAct` · 155 | Change only the control state to the given live state. | Matches; auxiliary. |
| `retAct` · 158 | Emit one Boolean and halt without other changes. | Matches; auxiliary. |
| `rw2Act` · 161 | Rewind input left while nonblank, then step right to the continuation; the selected work head stays fixed. | Matches; auxiliary. |
| `junkAct` · 167 | Halt without output or any tape/input change. | Matches; auxiliary. |
| `insTr` · 171 | Implement each instruction by finite phases over canonical binary register buffers. Inapplicable phases and ordinary execution of a call halt via junkAct; calls are handled by the separate call map. | Matches; canonical buffers and instruction preconditions are theorem hypotheses, not field-level guarantees. |
| `armTr` · 275 | At a label and phase, use insTr for the instruction stored at that label. | Matches; auxiliary. |
| `insCall` · 280 | Only a call instruction at its start phase produces a call specification, with continuations lifted to start phases. | Matches; auxiliary. |
| `armCall` · 289 | Look up insCall from a paired instruction label and phase. | Matches; auxiliary. |
| `armProg` · 294 | Combine armTr and armCall into an RProg initialized at the selected label's start phase. | Matches; auxiliary. |
| `aseam` · 300 | Represent a live abstract configuration with canonical binary register tapes, all heads zero, input at one, chosen output prefix, and control at the instruction's start phase. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ARMSim.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Mid` · 44 | Every live control state is noncall, and each register head lies between −1 and W; tape contents/output are otherwise unrestricted. | Matches; no canonical-buffer claim is hidden in this intermediate head/call invariant. |
| `SimTo` · 131 | A finite atomic-call run reaches c′ exactly and satisfies Mid at every strictly earlier time. | Matches; strict-prefix invariant only, with endpoint facts supplied by the target configuration. |
| `HaltsWith` · 136 | A finite run halts after appending exactly b; all final register heads are bounded, and every strictly earlier configuration satisfies Mid. | Matches; unlike SimTo alone, this relation explicitly bounds final heads. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ARMRun.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Pre` · 44 | At equality tests require distinct registers; at input comparisons require the appropriate valid encoding; at calls require distinct arguments and a clean bounded decider run with the correct oracle answer; other instructions impose nothing. | Matches; this contains oracle realizability as well as syntactic restrictions. |
| `Inv` · 72 | All register heads lie in [−1,W], and the current configuration satisfies CallOK with that interval and decider radius B. | Matches; combines inclusive head positions with call preconditions at this configuration. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `AReach` · 45 | Some finite abstract run reaches a′ and satisfies G at every strictly earlier time; the endpoint is not required to satisfy G. | Matches the compositional half-open convention; no endpoint invariant is implied. |
| `AHalt` · 50 | Some finite abstract run halts with answer b and satisfies G at every strictly earlier time; a previously halted input configuration may have a zero-step witness. | Matches; the class theorem fixes a fresh live initial state, preventing a vacuous pre-answered witness. |
| `PreS` · 137 | Retain only the syntactic/input-validity portions of Pre: distinct equality operands, valid inputs for input comparison, and duplicate-free call arguments. No oracle correctness is asserted. | Matches; equality aliasing, malformed input comparisons, and duplicate arguments are excluded explicitly. |

### `TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean`

Source comparison: auxiliary machinery for Definition 4.16 and the restricted composition construction. General Lemma 4.17 is not received; see Q5.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `St` · 59 | Finite phases ask output length, ask the current bit, emit either bit, increment the index with return, and finish. | Matches; auxiliary. |
| `tm` · 64 | Emit the selected bit and increment one binary index register; the ask/bit/done labels otherwise halt in the raw table. | Matches; auxiliary. |
| `prog` · 75 | Use two oracle deciders: ask whether the current index is in range, then ask its output bit; raw transitions emit it and increment. | Matches; auxiliary. |
| `cfg` · 83 | Represent the chosen phase/index with one canonical binary register, zero head, input at one, and the supplied output prefix. | Matches; auxiliary. |
| `Shape` · 123 | Either the configuration is an ask/bit seam with index at most F, or it is noncall with its register head in [−1,W]. | Matches its permissive invariant purpose; it is not an exact characterization of reachable configurations. |

### `TCSlib/Complexity/SpaceComplexity/Machines/ARMKit.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

No definition-like declarations. Its received contribution consists of theorem statements, checked in Appendix B.

### `TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean`

Source comparison: machine-level implementation for §4.1 space accounting and/or the virtual-input construction of §4.3. There is no separate numbered textbook definition of these control states or fragments.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `dblLang` · 45 | Accept exactly pairings of a unary true word of length n with the canonical binary expansion of 2n. | Matches the worked implementation example; it is a helper language, not the textbook EVEN example verbatim. |
| `St` · 51 | Finite states validate the input, count its doubled unary prefix, rewind, compare the binary suffix, and accept/reject. | Matches; auxiliary. |
| `tr` · 59 | Validate the encoding, count every true in the doubled unary prefix using one binary register, compare that count with the suffix, and return a Boolean. | Matches; auxiliary. |
| `prog` · 83 | Use that one-register raw machine with no calls. | Matches; auxiliary. |
| `o` · 88 | The unique empty-family oracle function, since there are zero deciders. | Matches; auxiliary. |
| `K` · 94 | Construct a one-register configuration containing bits(v), with the supplied input/head positions and state and empty output. | Matches; auxiliary. |
| `Rch` · 111 | A finite atomic-call run reaches the target while its single work head stays in [−1,W] at every earlier time. | Matches its strict-prefix formal contract; endpoint facts must be read from the separate target. |
| `nilTM` · 273 | A zero-work-tape, one-state machine that halts in one step without output. | Matches; empty output means it is a dummy machine, not itself a Boolean-language decider. |

### `TCSlib/Complexity/SpaceComplexity/UnaryLogspace.lean`

Source comparison: auxiliary machinery for Definition 4.16 and the restricted composition construction. General Lemma 4.17 is not received; see Q5.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `uBit` · 53 | Accept canonical pairs (unary n,bits i) exactly when output bit i of g(n) is true; missing bits default false. | Matches; auxiliary. |
| `uLen` · 57 | Accept those canonical pairs exactly when i is strictly less than the length of g(n). | Matches; auxiliary. |
| `UnaryLogspace` · 61 | Require the unary bit and length languages to be in LOGSPACE. No output-length bound is included. | Matches the expressly weaker auxiliary notion; polynomial output length is absent (note 10, Q5). |
| `unaryExt` · 96 | Extend g to all bit strings by using g(length x) on all-true words and the empty word otherwise. | Matches; extension rejects nonunary arguments by producing empty output. |
| `ltLang` · 162 | Accept canonical pairs (unary n,bits i) exactly when i<n. | Matches; auxiliary. |
| `Lb` · 168 | Finite labels validate input, test a doubled counter by an oracle, compare the other counter to input, increment, and return. | Matches; auxiliary. |
| `A` · 175 | Validate; enumerate a counter and its double from zero, stopping at doubled n using dblLang, and accept if the input index is encountered before n. | Matches; auxiliary. |
| `vv` · 186 | A two-register valuation assigning a to register zero and b to register one. | Matches; auxiliary. |
| `orc` · 202 | The sole oracle answers membership in dblLang. | Matches; auxiliary. |
| `G` · 214 | Require PreS and bound both register values by 2(length y+1). | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean`

Source comparison: auxiliary machinery for Definition 4.16 and the restricted composition construction. General Lemma 4.17 is not received; see Q5.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `rg` · 55 | Embed an original register among the first R of R+3 registers. | Matches; auxiliary. |
| `rP` · 57 | Reserve register R for the simulated input cursor. | Matches; auxiliary. |
| `rO` · 59 | Reserve register R+1 for the simulated output count. | Matches; auxiliary. |
| `rT` · 61 | Reserve register R+2 for a temporary print counter. | Matches; auxiliary. |
| `ev` · 65 | Combine original register values with the three cursor/output/temporary counters. | Matches; auxiliary. |
| `Lb` · 119 | Finite-control constructors represent validation, simulated instruction entry, output counting, print/read substeps, and either Boolean answer. Finiteness requires finite original labels. | Matches; finite control is obtained from finite original labels by the explicit instance. |
| `A` · 172 | Build an ARM deciding an output bit or length query of a CounterProg run. Simulate arithmetic directly, replace reads by unary bit/length oracle calls, and count output until the queried position is reached. | Matches the restricted unary-query simulator; no random-access input or general composition theorem is asserted. |
| `ans` · 219 | In length mode return whether p is in range of O; in bit mode return O's bit at p with false as the default. | Matches; auxiliary. |
| `cf` · 223 | Construct a live abstract configuration with supplied simulator label/values and no answer yet. | Matches; auxiliary. |
| `G` · 233 | Require the simulator's PreS condition and bound every register by B. | Matches; auxiliary. |

### `TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean`

Source comparison: auxiliary machinery for Definition 4.16 and the restricted composition construction. General Lemma 4.17 is not received; see Q5.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `Bd` · 57 | Every original register value, input cursor, and output length is at most B. | Matches; bounds numeric values, cursor, and total output length, rather than merely register bit widths. |

### `TCSlib/Complexity/SpaceComplexity.lean`

Source comparison: import facade for the received §4.1/§4.3 implementation, with the same declared deviations as its constituent modules.

No definition-like declarations. This is an import facade.

### `TCSlib/Complexity/TimeHierarchy/ClockMachine.lean`

Source comparison: auxiliary constructions for §3.1/Theorem 3.1, with the received quadratic simulation convention. No separate numbered textbook definition is claimed.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `OutReg` · 82 | Summarize an output word as empty, exactly one specified Boolean, or at least two bits. | Matches the required output summary. Its three constructors give four values because the singleton constructor carries a Boolean. |
| `OutReg.ofList` · 89 | Classify a list by that summary, preserving the unique bit only for singleton lists. | Matches; auxiliary. |
| `OutReg.push` · 95 | Update the summary when an optional next output bit is appended. | Matches; auxiliary. |
| `ctrVal` · 123 | Evaluate an arbitrary little-endian bit list as a natural binary value, allowing noncanonical high zero bits. | Matches; permits redundant high zero bits and agrees with natural value on canonical bits. |
| `ctrPop` · 128 | Count true bits in a bit list. | Matches; auxiliary. |
| `ClockState` · 220 | Finite control tracks budget computation, counter/input rewind, and alternating decrement/simulation-return phases carrying the simulated state and output summary. | Matches; auxiliary. |
| `ctrIdx` · 230 | Select the one counter tape between K's work-tape bank and W's work-tape bank. | Matches; auxiliary. |
| `ctrAction` · 233 | Operate only on that counter tape and control state; input, output, and the other banks remain unchanged. | Matches; auxiliary. |
| `clockTr` · 238 | Simulate K while redirecting its output to a binary counter tape; rewind counter/input; decrement before each W step. A zero-budget underflow returns true; W halting returns the negation of having output exactly [true]. | Matches; final permitted halt is detected before another underflow, and full singleton output is checked. |
| `clockTM` · 275 | Bundle clockTr with K.k+1+W.k tapes and initial control simulating K's initial state. | Matches; auxiliary. |
| `kCfg` · 295 | Embed a K configuration, placing its output on the counter tape at its right boundary and leaving W's work tapes blank; the clock's output is empty. | Matches; auxiliary. |
| `ctrCfg` · 373 | Assemble a clock configuration from frozen K banks, a counter tape/head, W's configuration, and explicit clock state/output. | Matches; auxiliary. |
| `cScanCfg` · 435 | Represent the counter rewind at coordinate j−1 with counter word s, frozen K banks, and blank W work tapes. | Matches; auxiliary. |

### `TCSlib/Complexity/TimeHierarchy/ClockLoop.lean`

Source comparison: auxiliary constructions for §3.1/Theorem 3.1, with the received quadratic simulation convention. No separate numbered textbook definition is claimed.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `ctrBound` · 215 | The loop budget is 4·ctrVal(s)+2(length(s)−ctrPop(s))+length(s)+1. | Matches; Q6 independently checks the decrement potential and zero case. |
| `loopAnswer` · 219 | Negate the conjunction that W is halted after v steps from c and its full accumulated output is exactly [true]. | Matches; tests the whole accumulated output, not just its first bit. |

### `TCSlib/Complexity/TimeHierarchy/CodePrefix.lean`

Source comparison: auxiliary constructions for §3.1/Theorem 3.1, with the received quadratic simulation convention. No separate numbered textbook definition is claimed.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `scanPre` · 63 | Copy input pairs until and including the first unequal pair; if there is no such pair, copy the entire input, including a possible final unpaired bit. | Matches; malformed inputs have a total default, while the self-pairing lemma assumes a genuine pair. |
| `PreState` · 87 | Finite states scan a paired prefix, rewind input, and copy the whole input. | Matches; auxiliary. |
| `preTr` · 98 | Emit scanned prefix bits, rewind to the beginning, emit all input bits, and halt. It uses no work tapes. | Matches; auxiliary. |
| `preTM` · 113 | Bundle preTr as a finite zero-work-tape machine starting at prefix scan. | Matches; auxiliary. |

### `TCSlib/Complexity/TimeHierarchy/Diagonal.lean`

Source comparison: auxiliary constructions for §3.1/Theorem 3.1, with the received quadratic simulation convention. No separate numbered textbook definition is claimed.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `code` · 107 | Choose one witness of the existing EffectiveMachineCode existence theorem; no efficient evaluation of this Lean choice is asserted. | Matches; choice fixes an existing witness and does not introduce an axiom or computational-cost promise. |
| `univTM` · 110 | Choose the finite universal machine supplied for that fixed code system. | Matches; its simulation constant is code-dependent, as declared. |
| `diagSim` · 124 | Compose prefix preparation with the chosen universal machine using buffered composition. | Matches; auxiliary. |
| `diagLang` · 129 | Accept x exactly when diagSim fails to halt with the singleton output [true] within g(length x) steps. This includes timeout, rejection, and nonsingleton output. | Matches; timeout and non-singleton output are included in diagonal acceptance. Upper computability needs constructible g. |

### `TCSlib/Complexity/TimeHierarchy/Separation.lean`

Source comparison: auxiliary constructions for §3.1/Theorem 3.1, with the received quadratic simulation convention. No separate numbered textbook definition is claimed.

| Declaration · source line | Blind mathematical restatement | Comparison after reading documentation |
|---|---|---|
| `twoPowTM` · 45 | A private zero-work-tape machine emits false for every input bit, then true at the first blank and halts, producing the little-endian representation of 2^(input length). | Matches; output includes the final true bit at n=0 as well as for nonempty inputs. |

### `TCSlib/Complexity/TimeHierarchy.lean`

Source comparison: import facade for the received §3.1 implementation at the explicitly declared quadratic-overhead strength.

No definition-like declarations. This is an import facade.

The anonymous `Fintype (Lb Λ)` instance in `CounterProgSim.lean:134` supplies a finite enumeration of the simulator labels when the original label type is finite. It adds no unbounded register/state resource or new semantic oracle. Automatically derived finite/decidable instances similarly concern the displayed finite control types.

## Appendix B. Headline delivered-strength checks

The “book comparison” column refers to the compact source baseline above. “Auxiliary” explicitly means that the named result is an implementation theorem without a separately stated textbook version. Matching such a theorem to its own docstring does not promote it to the entire chapter theorem. Every item in the modules' “Main results” lists is covered below; a few important additional interfaces are included. The absent advertised `arm_step` is recorded as absent, not silently replaced with an invented theorem.

### Time hierarchy and exponential separation

| File · headline theorem(s) | Book comparison | Delivered statement and docstring check |
|---|---|---|
| `ClockMachine` · `clockTM_setup` | Auxiliary for Theorem 3.1. | Given the actual computation of budget word `s` in `tK`, reaches the loop with that counter and a fresh simulated initial configuration in at most `tK+length(s)+length(x)+5`. Frozen budget-machine tapes may remain nonblank; they are not reused as simulated tapes. Matches. |
| `ClockLoop` · `clockTM_loop` | Auxiliary for Theorem 3.1. | From an arbitrary **live** simulated configuration, halts within `ctrBound s` and emits `loopAnswer` for the value of `s`. No assumption that `s` is canonical. The live-state hypothesis is explicit; Q6 checks the potential and endpoint. Matches. |
| `ClockLoop` · `clockTM_spec` | Auxiliary for Theorem 3.1. | Given `K.ComputesInTime x s tK`, computes the negation of `W.ComputesInTime x [true] (ctrVal s)` within `tK+4 length(s)+length(x)+4 ctrVal(s)+6`. Tests halting and the exact singleton output. Matches. |
| `CodePrefix` · `preTM_computes` | Auxiliary self-application preparation. | Computes `scanPre x ++ x` within `3 length(x)+5` on all words, including malformed encodings and empty input. Matches. |
| `CodePrefix` · `scanPre_pairEncode_append` | Auxiliary self-application identity. | On genuine `pairEncode α w`, the prepared word is `pairEncode α (pairEncode α w)`. It requires no efficient code recognizer or infinite set of codes for one machine. Matches. |
| `Diagonal` · `univTM_spec` | Existing universality interface consumed by the construction. | For each code separately there is a fixed simulation constant valid on all inputs. This is the declared code-dependent constant, not a universal constant across codes. Matches. |
| `Diagonal` · `diagLang_mem_DTIME` | Upper-bound part of the received version of Theorem 3.1. | `TimeConstructible g` implies `diagLang g ∈ DTIME (fun n => g n+1)`. This is a total decider, even when the inner simulation never halts. Matches the documented normalization. |
| `Diagonal` · `diagLang_not_mem_DTIME` | Lower-bound part of the received version. | For every constant and lower threshold, a larger length satisfying the quadratic domination inequality suffices to exclude `diagLang g` from `DTIME T`. Constructibility is not needed for this purely lower-bound assertion. It proves class nonmembership, not an exported per-input disagreement-count formula. Matches when “infinitely often” refers to its numerical hypothesis. |
| `Diagonal` · `time_hierarchy` | Compare Theorem 3.1 baseline. | Constructible `g` and eventual domination of every `A(f+n+1)²` imply `DTIME f ⊂ DTIME (g+1)`. No constructibility of `f`. This is weaker in the growth gap and different at zero from the book baseline, as prominently declared. Q1 finds no undeclared weakening. |
| `Diagonal` · `time_hierarchy_of_pos` | Same comparison. | Adds `∀n,0<g n` and concludes strict inclusion into `DTIME g`. Positivity is exactly what permits all-length multiplicative removal of `+1`. Matches. |
| `Separation` · `timeConstructible_two_pow` | Constructible exponential example used by the separation. | The function `n↦2^n` meets the imported constructibility interface, including empty input. The displayed zero-tape generator emits its binary value in `n+1` steps. Matches. |
| `Separation` · `eventually_poly_le_two_pow`, `eventually_poly_sq_le_two_pow` | Auxiliary numerical domination. | Every `A(n+1)^K`, and then every `A(n^k+1+n+1)²`, is eventually at most `2^n`, uniformly after a threshold depending on the fixed parameters. The square uses exponent `2k+2` and factor `9A`; Q1 independently derives them. Matches. |
| `Separation` · `dtime_poly_ssubset_dtime_two_pow` | Polynomial/exponential instance of the hierarchy. | For each natural `k`, strictly separates `DTIME(n^k+1)` from `DTIME(2^n)`. Includes `k=0`; the positive normalization is intentional. Matches. |
| `Separation` · `P_ssubset_EXP`, `P_ne_EXP` | Chapter-3 polynomial/exponential consequence. | The common exponential diagonal language lies outside every polynomial member class, so the union is strictly smaller than `EXP`. `P_ne_EXP` follows from strictness. It does not rely on the invalid inference that a union of proper subclasses must be proper. Matches. |

### Space classes, configuration counting, and compilation

| File · headline theorem(s) | Book comparison | Delivered statement and docstring check |
|---|---|---|
| `Basic` · `ComputesInSpace.mono`, `SPACE.mono` | Elementary consequences of the declared space definition. | Pointwise domination at **all** lengths weakens the bound. Neither theorem asserts eventual-bound equivalence. Valid as stated; finding 1 concerns interpretation of the underlying unrestricted class. |
| `ConfigCount` · `abs_pos_lt_card_visited` | Auxiliary to Claim 4.4. | For a position actually in one tape's visited set from initialization, absolute coordinate is strictly below that set's cardinality. The interval starts around zero; it is not a claim about arbitrary configurations. Matches. |
| `ConfigCount` · `ComputesInTime.of_spaceUsed_le` | Deterministic count-to-time part of Claim 4.4/Theorem 4.2. | A computation already known to halt by `t`, with total visited space through `t` at most `s`, computes the same output within `configBound M (length x) s`. Halting is explicit and essential. The theorem is not a nondeterministic search or a CNF-adjacency result. Matches. |
| `ConfigCount` · `LOGSPACE_subset_P` | Def. 4.5 specialization of the count/time baseline. | Every language in the positive-normalized `LOGSPACE` is in `P`. Fixed tape/state counts and space multiplier produce the polynomial in Q3. Short inputs and zero tapes are covered. Matches. |
| `ConfigCount` · `ComputesInSpace.computesFunInTime`, `polyTimeComputable_of_computesInSpace` | Function version of the same implication. | A function computed by one finite machine in a constant multiple of `logSpace` is computed by that same machine within the explicit polynomial from Q3, and hence is polynomial-time computable. Unread output cannot postpone a first halt without distinct cores. Matches. |
| `Machines/Layout` · `vpos_tmove`, `inputSymbol_vpos` | Auxiliary for §4.3 virtual-input simulation. | Under segment-index and local-validity hypotheses, translated head movement and symbols agree with the real virtual word, including separators, empty segments, and clamped endmarkers. No correctness outside those hypotheses is asserted. Matches. |
| `Machines/Program` · `step_seam_prog` | Auxiliary compiler correspondence. | A live noncall program transition and its compiled transition agree at the seam; decider tapes remain idle. Explicitly excludes call nodes. Matches. |
| `Machines/Sim` · `gstep_tmove`, `sim_step` | Auxiliary virtual-input correspondence. | Guarded bookkeeping follows virtual movement; a related live decider step yields the corresponding continuing or returning compiled simulation configuration. Register data and caller output are preserved. It is local simulation, not a complete clean-call theorem. Matches. |
| `Machines/CallReturn` · `ret2_run`, `retR_run`, `regs_run` | Auxiliary return discipline. | With the specified return states, tracking relation, and valid buffers, restores input and then argument heads within the stated register box. Does not claim to erase arbitrary dirty decider tapes. Empty buffers/endmarkers are included. Matches. |
| `Machines/Call` · `call_run` | Auxiliary realization of one virtual-input oracle call. | Given clean decider termination, buffer/position validity and distinct arguments, a compiled call returns to the selected continuation, restoring heads and respecting the charged boxes. It does not realize an arbitrary uncomputable oracle. Matches. |
| `Machines/Compile` · `compile_correct` | Compiler infrastructure for the §4.3 construction. | For a bounded abstract prefix whose actual calls satisfy `CallOK`, reaches exactly the endpoint's seam with inclusive physical head bounds. A halting abstract endpoint therefore gives halting. The formal result is more general than the conditional halting description, not weaker. Q4. |
| `Machines/Compile` · `compile_space` | Same infrastructure with visited-space accounting. | Adds abstract halt/output hypotheses and finite label types, yielding a finite machine computation with bound `sum (hi−lo+1).toNat+kD(2B+1)`. All banks and endpoints are counted. Matches. |
| `Machines/CleanSweep` · `goR_run`, `erase_run`, `back_run` | Auxiliary cleanup construction. | Given the specified marked interval, control phase, and tape shapes, each sweep reaches its stated endpoint, blanks the intended region, and preserves the radius bound. They do not promise cleanup of arbitrary tapes without those interval premises. Matches. |
| `Machines/Clean` · `cleanTM_run` | Auxiliary space-preserving normalization. | Given a halt and a per-tape visited-cardinality bound `s`, the doubled-bank machine halts with the same output, blank work tapes, zero work heads, and inclusive radius `s`. Input head normalization is not in the conclusion. Matches the main-result description. |
| `Machines/Bank` · `bank_cleanRun` | Auxiliary finite family of reusable deciders. | From actual space-deciding contracts, each chosen bank entry returns its membership bit cleanly with radius `max(s_j(length V),1)`. Padding and marker tapes explain the extra one and doubled bank. Matches. |
| `Machines/ARMRun` · `arm_run` | Auxiliary abstract-to-register-machine compilation. | A live-start abstract run that halts with answer `b`, meeting `Pre` and the successor bit-width bound at every earlier step, yields a halting program with old output followed by `[b]`, bounded final heads, and the intermediate call/head invariant. Endpoint bounds are explicit here. Matches. |
| `Machines/ARMRun` · `arm_space` | Same construction composed with the concrete compiler. | From zero-register initialization and the same run premises, gives a finite machine computation using at most `m(W+2)+kD(2B+1)` cells. It is parametrized by general widths, not restricted to logarithmic widths. Matches. |
| `Machines/ARMProof` · `arm_decides` | Implementation route to the Def. 4.5 class. | One finite ARM, fixed logspace oracle languages, and all-input `AHalt` correctness under `PreS` plus `length(bits(v+1))≤K logSpace n` imply language membership in `LOGSPACE`. No polynomial abstract-time premise. The oracle contracts are discharged, not retained in the result. Matches. |
| `Machines/ARMKit` · `arm_decides_poly` | Same class wrapper with a convenient numeric invariant. | Replaces the successor bit-width bound by `v≤C₀(n+1)^c₀` and retains the other `arm_decides` requirements. Computes a suitable logarithmic width. It is about register values, not about polynomially many abstract steps. Matches. |

### Binary, parser, and implicit-computation toolkit

| File · headline theorem(s) | Book comparison | Delivered statement and docstring check |
|---|---|---|
| `Machines/Bin` · `bitsVal_bits`, `bits_injective` | Auxiliary canonical index arithmetic. | Natural binary encoding is decoded exactly and is injective; no claim that arbitrary noncanonical words are injectively decoded. Empty representation of zero is included. Matches. |
| `Machines/Bin` · `bits_succ`, `length_bits_le`, `length_bits_mono` | Auxiliary register-width arithmetic. | `incW(bits n)=bits(n+1)`; `n<2^m` bounds width by `m`; numeric monotonicity bounds canonical width. Matches. |
| `Machines/Lib` · `inc_run` | Auxiliary register operation. | Under the supplied transition/no-call conditions and initial buffer/head shape, increments a canonical register, restores its head, and stays in `[-1,length(bits(n+1))]`. The extra width for carry is present. Matches. |
| `Machines/FragDec` · `dec_run`, `toEnd_run`, `clr_run` | Auxiliary register operations. | Canonical predecessor is truncated at zero; scanning/clearing has the specified buffer and head preconditions and returns the promised tape/head shapes. The head may visit the blank boundary. Matches. |
| `Machines/Frag` · `half_run`, `eq_run`; re-exported `dec_run`, `clr_run` | Auxiliary register operations. | Halving produces canonical integer division by two; equality chooses the corresponding branch and restores heads, with **distinct-register** premise. Imported predecessor/clear results are not new proofs in this module. Matches. |
| `Machines/ParsePlain` · `rewind_x`, `validPlain_iff`, `valPlain_run` | Auxiliary guarded input format. | Rewind returns to the specified input position; validity includes canonicality and unary-prefix parity; validation either returns to its continuation with the input reset or halts with false. It rejects malformed inputs. Matches these definitions; instruction shorthand has finding 4. |
| `Machines/Parse` · `canon_eq_bits`, `jeqPlain_run` | Auxiliary input/register comparison. | Canonical words equal the bits of their value. On a valid plain encoding, the comparison reaches the selected branch with restored positions under its stated buffer/transition hypotheses. Not a theorem that the fragment safely handles arbitrary malformed inputs without validation. Matches. |
| `Machines/Parse2` · `valPair_run` | Auxiliary nested-pair validator. | Checks the outer unary prefix and both canonical inner components; success preserves the promised data and returns, failure appends false and halts. Matches. |
| `Machines/ParseCmp` · `jeqPairSnd_run`, `jeqPairFst_run` | Auxiliary nested-pair comparisons. | With valid encoded input and canonical register buffer, reaches the branch corresponding to the selected component equality within the specified prefix bounds. Finding 6 concerns what the helper relation alone says about its endpoint, not these explicit target configurations. |
| `Machines/ARMSim` · advertised `arm_step`; actual `sim_inc`, `sim_dec`, `sim_clr`, `sim_half`, `sim_jz`, `sim_jodd`, `sim_jeq`, `sim_call`, `sim_ret`, `sim_valP`, `sim_valQ`, `sim_jeqIn`, `sim_jeqFst`, `sim_jeqSnd` | Auxiliary instruction simulation. | No theorem named `arm_step` is received. The individual simulations supply the arithmetic, validation, branch, call, and return cases, with their validity/aliasing/decider hypotheses; whole-run assembly is in `arm_run`. Finding 8. |
| `Machines/ARMKit` · `vword_unary₁`, `vword_unary₂` | Auxiliary virtual-input identities. | For **one or two** arguments on a correctly paired unary-prefix input, produces the stated single/nested pair exactly. These identities are sound and do not claim the zero-argument case. Matches. |
| `Machines/DblLang` · `dblLang_mem` | Auxiliary worked logspace language. | Decides all encodings of unary `n` paired with `bits(2n)` and rejects malformed/noncanonical encodings, in `LOGSPACE`. The intermediate `run_valid` reaches a yes/no continuation; `ret_step` supplies the final output/halt. The class theorem supplies the full claim. Matches. |
| `ImplicitPoly` · `ImplicitlyLogspaceComputable.computesInSpace` | Constructive consequence of Def. 4.16; one direction of the associated equivalence. | Given the entire definition, including polynomial output length, produces some finite machine and constant with the whole function computed in logarithmic visited space. Empty outputs halt and do not emit an extra bit. Does not claim the converse or general composition. Matches. |
| `ImplicitPoly` · `ImplicitlyLogspaceComputable.polyTimeComputable` | Function time consequence. | The same hypothesis implies polynomial-time computability using the previous result and deterministic counting. Matches. |
| `UnaryLogspace` · `UnaryLogspace.implicitlyLogspaceComputable` | Restricted unary-domain conversion. | Requires `UnaryLogspace g` **and** a polynomial bound on `length(g n)`; concludes implicit computability of `unaryExt g`. Nonunary inputs have empty output. Matches the explicit extra premise. |
| `UnaryLogspace` · `ltLang_mem`, `unaryLogspace_replicate` | Auxiliary unary example. | Canonical unary/index pairs satisfying `i<n` form a logspace language; hence `n↦true^n` has logspace unary bit and length languages. Covers zero and rejects bad encodings. Matches. |
| `CounterProgSim` · `CPSim.sim_step` | Auxiliary for the restricted closure construction. | With correct unary input-query oracles, a bounded counter-program step either yields the correctly encoded successor simulator state or answers the requested output-position question. Requires the declared current/next bounds and cursor/output-position conditions. Matches. |
| `CounterProgSimRun` · `CPSim.sim_run` | Same restricted construction. | From a live counter state whose output has not passed the query, a halting bounded counter run yields `AHalt` with its bit/length answer, maintaining the simulator's polynomial-value invariant. The two input-query oracle contracts are explicit. Matches. |
| `CounterProgSimRun` · `UnaryLogspace.counterProg` | Special case related to the Lemma 4.17 construction, not the general lemma. | Unary-logspace input family plus one finite counter program halting in `C(n+1)^c` abstract steps with output `g n` implies `UnaryLogspace g`. The polynomial is in the unary parameter `n`, not an unconstrained output or virtual-input length. One-way reads are retained. Matches. |
| `CounterProgSimRun` · `CounterProg.length_out_le` | Auxiliary size bound. | A polynomial step bound from zero initialization yields a polynomial output-length bound, despite a unary-print instruction emitting a whole register in one abstract step. It does not grant polynomial length to arbitrary `UnaryLogspace` functions. Matches. |

### Counter programs and polynomial/exponential supporting results

| File · headline theorem(s) | Book comparison | Delivered statement and docstring check |
|---|---|---|
| `TuringMachine/UnaryTape` · `update_ones_succ`, `update_ones_pred` | Auxiliary unary-register representation. | Writing the next unary cell extends the represented natural; erasing its last occupied cell represents predecessor under the corresponding index hypotheses. Blank and zero cases use the stated guarded form. Matches. |
| `TuringMachine/CounterProg` · `sim_step` | Auxiliary finite-machine compilation. | For a live abstract state with cursor at most input length and registers at most `B`, produces the encoded one-step successor within `2B+3` concrete steps. This charges unary printing and return scans; it does not price every instruction as one concrete step. Matches. |
| `TuringMachine/CounterProgRun` · `sim_run` | Auxiliary run compilation. | Requires the cursor bound and **initial** values plus `t` at most `B`, and simulates `t` abstract steps within `t(2B+3)`. Finding 2 records the broader docstring wording. |
| `TuringMachine/CounterProgRun` · `exists_tm` | Auxiliary whole-program compilation. | A run from all-zero initialization that has halted at abstract time `t` is computed by the finite machine within `t(2t+3)` steps, with exactly the abstract output. Finite decidable labels are required. Matches; unaffected by finding 2. |
| `TuringMachine/CounterProgRun` · `Goes.trans`, `goes_loop` | Auxiliary program algebra. | Sequential bounds add and emitted suffixes concatenate, uniformly over existing output prefixes. The loop theorem assumes the stated body/control contracts and countdown invariant and yields its finite accumulated bound; it is not arbitrary-loop termination. Matches. |
| `TuringMachine/CounterProgRun` · `goes_tmpl`, `flatMap_exec_linOps` | Auxiliary output templates. | Installed template instructions emit their specified micro-operation list and continue; a linear-expression template emits a unary list of the sum with multiplicity plus constant. Matches. |
| `TuringMachine/CounterProgRun` · `run_pos_le`, `run_out`, `run_init_out_le` | Auxiliary growth bounds. | Cursor increases by at most one per abstract step; output only gains a suffix; a zero-initialized run emits at most `t(t+1)` bits. Arbitrary preloaded large registers are not covered by the last bound. Matches. |
| `ClassNP/CounterProgPolyTime` · `polyTimeComputable`, `polyTimeComputable_of_goes` | Auxiliary route to polynomial-time function witnesses. | Uniform finite program and all-input halting/output contract within `C(n+1)^c` imply polynomial-time computability; compilation gives a bound `(2C²+3C)(n+1)^(2c)`. The `Goes` variant retains the same halting/output obligations. Matches. |
| `ClassNP/ExpPoly` · `ExpPoly.of_le`, `ExpPoly.add`, `ExpPoly.mul`, `ExpPoly.comp_poly`, `expPoly_exp`, `expPoly_poly` | Auxiliary exponential-bound algebra. | The all-length `2^(K(n+1)^k)` envelope is downward closed, closed under sum/product and polynomial reindexing, and contains the indicated polynomial and exponential examples with suitable fixed parameters. Does not claim closure under arbitrary function composition. Matches. |
| `ClassNP/ExpPoly` · `ExpPoly.mem_EXP` | Supporting `EXP` normalization. | A language in `DTIME T` with such an envelope belongs to the repository `EXP`; fixed constants and finite short lengths are absorbed with positive exponential budgets. Matches. |
| `ClassNP/PolyTimePairing` · `polyTimeComputable_of_linear`, `polyTimeComputable_const` | Auxiliary FP constructions. | A uniform linear-time machine contract gives an FP witness; any one fixed finite word is a constant FP function. No constant may depend on the input. Matches. |
| `ClassNP/PolyTimePairing` · `PolyTimeComputable.pairMapSnd`, `.pairEncode`, `.append` | Auxiliary FP closure. | Under polynomial-time hypotheses, maps a decoded payload, pairs two computed outputs, or concatenates them in polynomial time. Pair-map malformed input uses its explicit empty default. Matches. |
| `ClassNP/PolyTimePairing` · `polyTimeComputable_unary`, `polyTimeComputable_polyUnary` | Auxiliary bounded output generators. | Produces true strings of length `length x` or `C(length x+1)^d` in polynomial time for fixed `C,d`, including empty input. Matches. |
| `ClassNP/PolyTimePairing` · `polyTimeComputable_pairFstD`, `polyTimeComputable_pairSndD`, `polyTimeComputable_pairSwap`, `polyTimeComputable_pairConcat`, `polyTimeComputable_prepend` | Auxiliary encoding operations. | The specified total projections, rearrangements, and fixed prefix operation are polynomial-time computable. Default behavior on malformed encodings belongs to the total function being proved computable. Matches. |
| `ClassNP/PolyTimePairing` · `polyTimeComputable_ite`, `polyTimeComputable_and`, `polyTimeComputable_lenLe`, `polyTimeComputable_lenEq` | Auxiliary tests/branching. | Polynomial tests and branches compose to the displayed Boolean and length-test functions, with the actual totalized projections. No arbitrary uncomputed predicate is promoted to polynomial time. Matches the formal interfaces. |
| `ClassNP/PClosure` · `mem_P_iff_polyTimeComputable`, `mem_P_of_test`, `test_of_mem_P` | Supporting language/function bridge. | Membership in `P` is equivalent to polynomial computation of the singleton membership bit, with the supplied Boolean-test formulations. The output is exactly one bit. Matches. |
| `ClassNP/PClosure` · `preimage_mem_P`, `inter_mem_P`, `union_mem_P`, `empty_mem_P`, `univ_mem_P`, `mem_P_of_atoms` | Supporting `P` closure. | Polynomial preimages and finite Boolean combinations preserve `P`; the finite atom family has a fixed size, so its truth function is finite data. Includes the constant languages. Matches. |
| `ClassNP/PClosure` · `lenEq_mem_P`, `lenLe_mem_P` | Supporting length predicates. | The predicates of total decoded projections are in `P`; malformed words with both defaults empty are accepted. Finding 5 records the mismatch with “pairs whose …”. |
| `ClassNP/PClosure` · `lenEq_preimage_mem_P`, `lenLe_preimage_mem_P` | Supporting comparisons of computed outputs. | For polynomial-time functions `f,g`, equality or the stated inequality of their output lengths defines a language in `P`. Actual pairing in the reduction makes the malformed-input default irrelevant. Matches. |
| `ClassNP/Transducer` · `transducerTM_computes`, `polyTimeComputable_transduce` | Auxiliary finite-state streaming construction. | A finite-state, at-most-one-output-bit-per-input-bit transducer computes its recursively defined output within `length x+1` concrete steps using zero work tapes; therefore the function is in FP. The last step halts and emits no extra bit. Matches. |

Both facade modules contain imports and documentation only. No additional theorem strength is inferred from their names.

## Notation glossary

| Notation used in this report | Meaning |
|---|---|
| `[]`, `[b]`, `++` | Empty bit list, singleton bit list, list concatenation. |
| `length x`, `n` | Input length; `n` is a natural unless stated otherwise. |
| `k`, `q` | Fixed work-tape count and number of live control states in the counting discussion. |
| `s`, `B`, `W` | Space function or numerical space bound; head radius; register bit-width/range parameter, as specified locally. |
| `A,C,K,c` | Fixed natural constants or exponents, quantified as stated; their roles are local to each calculation. |
| `ℓ` | `Nat.log 2 n` in the logarithmic configuration-bound calculation. |
| `bits i`, `Nat.bits i` | Canonical little-endian binary word for natural `i`; zero is encoded by the empty word. |
| `dbl x`, `pairEncode x w` | Repeat each bit of `x` twice; then append separator `[false,true]` and `w` to encode a pair. |
| `true^n`, `false^n` | A list of `n` copies of that Boolean, not exponentiation of a Boolean. |
| `⊂`, `⊆` | Proper inclusion and inclusion. The report uses `⊂` in the Lean statement's strict sense. |
| “core” | State, input head, work tapes, and work heads, with output omitted. |
| “seam” | A program configuration embedded in the compiled machine with blank, reset decider tapes. |
| “half-open” invariant | Required at times `0≤t<T`; the endpoint at `T` needs a separate assertion. |

Audit ends. No source modification or gate closure is asserted.
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
core-code count of `Turing.MultiTapeTM.ConfigCount.configBound` —
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
instead (the same `mono`, and the padded siblings stay halted by
`Turing.NDTM.runWith_of_halt`). -/
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
book's `2^{O(S(n))}`; the `+ 1` keeps the exponent positive and absorbs the
input-head factor (`n + 2 ≤ 2 ^ (S n + 1)`, since `SpaceConstructible` bundles
`logSpace n ≤ S n`).

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
mirroring the received `Complexity.LOGSPACE_subset_P`, whose proof is the
deterministic special case of the same search. Continuation budget
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
docstring rather than left implicit).

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


## ===== TCSlib/Complexity/SpaceComplexity/Savitch.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Savitch's theorem

[AB09, Theorem 4.14] ([Sav70]): for space-constructible `S`,
`NSPACE(S(n)) ⊆ SPACE(S(n)²)` — nondeterministic space costs only a quadratic
deterministic overhead, via the midpoint recursion `reach?(u, v, i)` over the
configuration graph of `TCSlib.Complexity.SpaceComplexity.ConfigGraph`. The
corollary `PSPACE = NPSPACE` ([AB09, §4.2.1]) closes the polynomial level.
Phase P4.2 of `AroraBarakChapters3-4Plan.md`.

**Status: statement skeleton (phase P4.2).** Every contract is sorried with a
sketch naming its fill obligations. The `SpaceComplexity.lean` facade has
carried this module since the P4.1 gate closed (root-wired while that gate
was live).

## Design

* **The positive-bound convention is respected without side conditions**:
  `Complexity.SpaceConstructible` bundles `logSpace n ≤ S n`, so `S` and
  `S · S` are everywhere positive and the P0-adopted convention
  (`TCSlib.Complexity.SpaceComplexity.ZeroSpace`) imposes no extra hypothesis.
* **The recursion is realized iteratively**: `reach?`'s call stack becomes an
  explicit stack of `O(S)`-bit frames (coded vertices and a midpoint cursor)
  on a dedicated bank, walked by the loop combinator — the §12 layer
  (`Build/Embed.lean`, `Build/Seam.lean`, `Build/Catalog.lean`) is the
  intended engine, with the depth `O(S)` and frame size `O(S)` giving the
  `O(S²)` ledger.

## Main results (all sorried; phase-P4.2 statements)

* `Complexity.spaceConstructible_poly` — the polynomial bounds of the
  campaign's normal form are space-constructible (degree at least one).
* `Complexity.savitch` — [AB09, Theorem 4.14].
* `Complexity.PSPACE_eq_NPSPACE` — [AB09, §4.2.1].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2.1, Theorem 4.14; §4.1.2.)
* [Sav70] W. J. Savitch, *Relationships between nondeterministic and
  deterministic tape complexities*, JCSS 4(2), 1970. (Cited through [AB09];
  no external text is required for this audit.)
-/

namespace Complexity

open Turing

/-- **The campaign's polynomial bounds are space-constructible** (spec, fill
pending — phase P4.2): for `1 ≤ c`, the normal-form bound `n ^ c + 1` is
`Complexity.SpaceConstructible`. (Degree zero is excluded: `n ^ 0 + 1 = 2`
fails the bundled `logSpace n ≤ S n` at large `n`; consumers route degree
zero through monotonicity into degree one.)

**Proof sketch.** Dominance: `logSpace n ≤ n + 1 ≤ n ^ c + 1` for `1 ≤ c`
(`logSpace n ≤ n + 1` by induction on the binary length; `n ≤ n ^ c` for
`n ≥ 1`, and the `n = 0` case is `1 ≤ 1`). The witness machine computes
`(n ^ c + 1).bits` within `O(n ^ c)` visited cells: a unary power bank built
by `c` nested input scans (the `polyUnary` catalog row with its space clause,
`Turing.FinTM.computesFunInTime_polyUnary_spaceUsed`,
`Build/Catalog.lean`), then a unary-to-binary count-down into a binary counter
(`incrementTM`'s discipline; the `polyBits` row's space clause gives the
assembled bound). Named fill obligations: the two catalog instantiations and
the `ComputesInSpace` repackaging of their joint time/space contracts. -/
theorem spaceConstructible_poly (c : ℕ) (hc : 1 ≤ c) :
    SpaceConstructible fun n => n ^ c + 1 := by
  sorry

/-- **Savitch's theorem** ([AB09, Theorem 4.14]; [Sav70]): for
space-constructible `S`, nondeterministic space `S` sits inside deterministic
space `S²`.

**Proof sketch.** Let `N` decide `L` in space `c₀ · S`. Membership is
acceptance within the vertex count
(`Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound`), i.e.
reachability, in the configuration graph restricted to the window
`[-c₀·S n, c₀·S n]`, from the initial vertex to an accepting one
(`Turing.NDTM.reflTransGen_cfgStep_iff` for the dictionary) within
`V := N.configBound n (c₀·S n)` steps, where `log₂ V = O(S n)` (the
`configBound` exponent arithmetic). The deterministic decider evaluates
`reach?(u, v, i)` — is there a path of length at most `2^i` — by the midpoint
recursion: enumerate midpoints `m` over the coded vertices and recurse on
`(u, m, i - 1)` and `(m, v, i - 1)`, **reusing the space** of the first
recursive call for the second ([AB09]'s crucial point). Realized iteratively:
an explicit stack of at most `log₂ V + 1 = O(S n)` frames, each one coded
vertex pair plus a midpoint cursor of `O(S n)` bits, held on a dedicated bank
and walked with the catalog copy/compare/increment routines under the loop
combinator; one extra bank runs the vertex-adjacency test (one
transition-table application on decoded cores) and the base case. Space:
frames × frame size `= O((S n)²)`, plus `O(S n)` administration — inside
`SPACE (S·S)`'s constant absorption. The initial radius computation is the
constructibility witness, whose own space is `O(S n)`. Named fill
obligations: the frame-stack discipline (a §12 R1/R2 consumer — bank
embedding for the stack bank, seam composition per frame transition), the
midpoint enumerator, the adjacency tester, and the arithmetic packaging
`O(S²) ≤ c' · (S n · S n)`. Positivity of the target bound is automatic
(`S ≥ logSpace ≥ 1`). -/
theorem savitch (S : ℕ → ℕ) (hS : SpaceConstructible S) :
    NSPACE S ⊆ SPACE fun n => S n * S n := by
  sorry

/-- **`PSPACE = NPSPACE`** ([AB09, §4.2.1]): at the polynomial level,
Savitch's quadratic overhead is absorbed.

**Proof sketch.** `⊆` is `Complexity.PSPACE_subset_NPSPACE` (phase P4.1).
`⊇`: a member of `NPSPACE` lives in some `NSPACE (n ^ c + 1)`; route `c = 0`
into `c = 1` by the class's constant absorption — a decider within
`c₁ · (n ^ 0 + 1) = 2 · c₁` cells is a decider within `2c₁ · (n ^ 1 + 1)`
cells (bare `Complexity.NSPACE.mono` does not apply: its pointwise hypothesis
fails at `n = 0`, where `n ^ 0 + 1 = 2 > n + 1 = 1`); for `1 ≤ c`,
`Complexity.savitch` with `Complexity.spaceConstructible_poly` gives
membership in `SPACE ((n^c + 1) · (n^c + 1))`, and
`(n^c + 1)² ≤ 4 · (n^{2c} + 1)` lets `Complexity.SPACE.mono` plus the class's
constant absorption land it in `SPACE (n^{2c} + 1) ⊆ PSPACE`
(`Complexity.space_poly_subset_PSPACE`). -/
theorem PSPACE_eq_NPSPACE : PSPACE = NPSPACE := by
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
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Savitch
import TCSlib.Complexity.SpaceComplexity.Hierarchy
import TCSlib.Complexity.SpaceComplexity.Logspace.Reductions
import TCSlib.Complexity.SpaceComplexity.Logspace.Path
import TCSlib.Complexity.SpaceComplexity.Logspace.ImmermanSzelepcsenyi
import TCSlib.Complexity.SpaceComplexity.Logspace.Mult

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
- `SpaceComplexity.ConfigGraph`: configuration graphs, the ND Claim 4.4(1), Thm 4.2(iii),
  `NL ⊆ P`, Ex 4.3 (chapters-3-4 campaign, phase P4.2)
- `SpaceComplexity.Savitch`: Savitch's theorem and `PSPACE = NPSPACE` (phase P4.2)
- `SpaceComplexity.Hierarchy`: the space-bounded universal machine, Thm 4.8,
  `L ⊊ PSPACE`, Ex 3.2 (phase P4.3)
- `SpaceComplexity.Logspace.{Reductions, Path, ImmermanSzelepcsenyi, Mult}`: `≤ₗ` and
  Lemma 4.17, `PATH` and Thm 4.18, Thm 4.20 and Cor 4.21, `MULT ∈ L` (phase P4.4)

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1, §4.3.)
-/
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


## ===== audits/logs/ch4-p42-sweep.log =====

```
P4.2 GATE SWEEP at commit 200f4693a40f30302efed75a4e23ac31216172b7 (200f4693), branch complexity/arora-barak-ch3-4, started 2026-10-08 20:30:48
== TCSlib/Complexity/SpaceComplexity/ConfigGraph
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:140:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:156:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:196:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:218:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:257:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:275:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean:291:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/SpaceComplexity/Savitch
TCSlib/Complexity/SpaceComplexity/Savitch.lean:77:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Savitch.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Savitch.lean:128:8: warning: declaration uses 'sorry'
== TCSlib/Complexity/SpaceComplexity
P4.2_SWEEP_DONE
```


## ===== audits/logs/ch4-p42-p44-stylelint.log =====

```
INFO  TCSlib/Complexity/SpaceComplexity/Basic.lean                          161 lines; 10 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigCount.lean                    460 lines; 19 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean                    295 lines; 12 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Constructible.lean                  95 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean                 495 lines; 25 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/CounterProgSimRun.lean              246 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Examples.lean                       65 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Hierarchy.lean                      195 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean                   416 lines; 16 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Inclusions.lean                     97 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean  116 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean                  68 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Path.lean                  134 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean            141 lines; 7 public / 0 private declarations
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
