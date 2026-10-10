# Proposal: extending the `LogProg` ARM layer for chapters 3-4

*For Jason (Hydroxyi) — from the Arora-Barak chapters 3-4 campaign
(branch `complexity/arora-barak-ch3-4`; Seyoon). This is the colleague-sync
item recorded in `AroraBarakChapters3-4Plan.md` §2.5/§4b and `backlog.md`
§2. Your `SpaceComplexity/Machines/` tree is co-owned per our CH34-Q2
agreement ("extend in place"), so nothing below gets drafted without your
sign-off on the interfaces.*

## Why

Chapter 4 is mostly space-bounded machine work, and the campaign's recorded
strategy is to write those algorithms as **register programs, not
hand-built transition tables** — your `LogProg.ARM` + `compile_space` is
the substrate. Three gaps stand between the current layer and the
chapter-4 fills.

## The three proposed extensions

Each would be its own audited statement phase (our usual loop: sorried
statements with sketches → external audit gate → fill), drafted by us
against interfaces you approve, or co-drafted — your call.

1. **A nondeterministic ARM.** A `choose` instruction (binary
   nondeterministic branch) compiling to `FinNDTM`, with the
   `compile_space` theorem carried over, and `arm_decides`-style bridges
   to `NSPACE`/`NL`. First customers: `PATH ∈ NL`, the
   Immerman-Szelepcsényi inductive counting, and Corollary 4.21.

2. **A polynomial-width ARM variant.** Registers of `poly(n)` bits rather
   than `O(log n)`, for the `PSPACE`-level algorithms: `TQBF ∈ PSPACE`,
   `NP ⊆ PSPACE`, and Savitch at the polynomial level. Structurally
   either a generalization of `compile_space` (width as a parameter) or a
   sibling compiler — we have no preference and would follow your sense of
   which fits the existing proof architecture better.

3. **A configuration codec as a program.** Encode a fixed machine's
   configurations — work tapes windowed to `s` cells, the input head as a
   register — in `O(s)`-bit register contents, with a successor/adjacency
   test as an ARM program. This is shared by Theorem 4.2(iii), Savitch,
   Theorem 4.18, Corollary 4.21, and the `TQBF`-hardness emitter. The
   counting half would extend your deterministic `ConfigCount` to NDTMs,
   adapting (citing, never vendoring) cslib's upstream
   `MultiTape/ConfigBound.lean` design — cslib targets a newer Lean, so
   nothing ports directly.

## A design question on `CounterProg`

The `2^O(S)`-time searches need to read the input at a simulated head
position, but `CounterProg`'s input access is one-way (`rd` only
advances). Two options we see: ARM-style indexed input access, or a rewind
instruction. Do you have a preference (or a third option)?

## Two provenance questions (asked, not asserted)

Our 2026-10-08 citation audit flagged two design similarities purely so
citations can be added **if** applicable — no assertion intended:

* Did the `LogProg` compiler draw on Édouard Bonnet's lax-434930
  `classical-complexity` (`TimeCompiler` module)?
* Does `ConfigCount.core` relate to cslib `ConfigBound`'s `Cfg.core`
  (upstream, Sept 2026)?

A one-line "no" settles both.

## Process and housekeeping

* Our side runs a statement-freeze + external-audit discipline
  (`workflow.md`), including a duplication policy (`policy.md`,
  **Duplication**): anything we add to your tree arrives as audited
  statements with named owners, never ad-hoc copies.
* Separately: `main` has moved a lot recently (your `BooleanAnalysis`
  work) — when we sync, it would be good to also agree on merge
  coordination for the eventual chapter-3/4 PRs (one per chapter, each
  carrying sweep + axiom evidence, per the recorded plan).

**What we need from you**: a yes/no/modify on each extension's interface
sketch above, the `CounterProg` preference, and the two one-line
provenance answers. Full detail: `AroraBarakChapters3-4Plan.md` §2.5
(design), §4b (where this sits in the roadmap), `backlog.md` §2 (the
tracking entry), `machine-library-design.md` (the construction-layer
conventions anything new would follow).
