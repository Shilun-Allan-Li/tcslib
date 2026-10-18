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
