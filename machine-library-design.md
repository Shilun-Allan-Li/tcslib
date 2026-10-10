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

### 12.6 Framed catalog contracts (2026-10-10, after ZF-A2's escalation)

**The gap.** The R3 rows (`transferTM`, `copyTM`, `clearTM`, `compareTM`,
`incrementTM`) are stated only from `Cfg.ofWords`: every head at the origin,
every tape a globally buffered word. The zone shift machines (`Build/Zone.lean`,
`exists_zoneShiftInTM`/`OutTM`) have **exactly two tapes**. One is the zoned data
tape; the other is a scratch tape that starts and ends as the unary level word.
Their staging, cleanup and binary navigation counter therefore all run at
**displaced heads beside unrelated data**, where no canonical contract applies.

ZF-A2 (`audits/zone-agent-reports/f1-A2-REPORT.md`) showed the gap concretely,
with a kernel-checked regression. On a valid three-level carrier, a bare transfer
from a displaced head reads past the word's end and erases a cell that belongs
to the next zone. The cure is a delimited word: blanks at relative positions
`-1` and `|w|`, installed by the consumer, which saves the overwritten cells in
finite control and restores them afterwards. Correspondingly, the contract must
quantify over an arbitrary surrounding frame.

**Decision (user, 2026-10-10).** A small §12 extension: maintainer-drafted
statements, a short statement gate, then a fill batch; ZF-A3 follows. The
routines are local, since each step reads only the scanned cells of the touched
tapes, so a framed contract is the faithful generalization. No new machine is
defined.

**The five statements** (`Build/Catalog.lean`, after the R3 rows, sorried):

| Contract | Exact time | Effect on the touched tapes |
|---|---|---|
| `transferTM_run_ofCfg` | `2·|w| + 2` | source interval blank; destination interval `w` (old destination contents arbitrary) |
| `copyTM_run_ofCfg` | `2·|w| + 2` | destination interval `w`; source intact |
| `clearTM_run_ofCfg` | `2·|w| + 2` | the word interval blank |
| `incrementTM_run_succ_ofCfg` | `2·p + 2`, where `p = (w.takeWhile id).length` | the word interval holds `v`, where `incFixed w = some v` |
| `incrementTM_run_overflow_ofCfg` | `2·|w| + 2` | the word interval all `false` |

In every case the routine reaches its `done` anchor exactly at the stated time
and not earlier. Every cell outside the word intervals, every head, the native
input position and the output are unchanged. Up to the exit the touched heads
stay within `[pos − 1, pos + |w|]` (for a successful increment, `[pos − 1,
pos + p]`) and all other heads are fixed. Space bounds follow from the
trajectory clause through `MultiTapeTM.spaceUsedByTape_le_card_Icc`.
`incrementTM`'s carry-sensitive `2p + 2` is the per-step cost that makes the zone
machines' anchored binary countdown sum geometrically, the audited `O(2^i)`
navigation ledger. The canonical `2|w| + 2` public bound is too loose for that,
as ZF-A2 flagged.

**Specialization and dedup.** With the origin heads and globally buffered words
of `Cfg.ofWords`, each framed contract specializes to its canonical R3 row. The
fill batch therefore proves the framed form and **re-derives each canonical row
from it**, through a sanctioned proof-body swap with the public statement
unchanged. That generalizes the private trace lemmas rather than duplicating
them. `compareTM` is not framed here, since no current consumer needs it; it
follows the same pattern on request.

**Pre-ship execution check (mandatory practice).** Every statement was executed
on concrete configurations with displaced heads, a nonblank outer frame and the
edge cases (`w = []`, `p = 0`, all-`true` overflow). The exact final
configuration, the no-earlier-exit clause and the trajectory were compared:
63 cases, all pass, and a wrong-time negative control fails
(`audits/evidence/s12-framed/`).

### 12.7 Counter-driven loops (design, 2026-10-10, after ZF-B3's escalation; decisions 12.7.1–12.7.6 taken by the user the same day)

**The gap.** ZF-B3 (`audits/zone-agent-reports/f1-B3-REPORT.md`,
`f1-B3-CONTINUATION.md`) stopped on two shared-interface requests:

- a public fixed-width **decrement** routine with a framed contract;
- a loop whose number of rounds is a **binary counter read from a tape**,
  with the body's state kept on **persistent, arbitrarily positioned tapes**.

Every public loop host (`exists_loopTM`, `exists_loopCfgTM`,
`exists_loopFindTM`, `exists_emitLoopTM`) does something else. It runs
`R x.length` rounds, a count fixed by the input's *length* through a fuel
machine, and every round runs between canonical
`Cfg.ofWords anchor (stateWord …)` seams. A simulator would therefore have to
re-serialize its two simulated work tapes every round, which ZF-B3 rightly
refused.

**This is a shared need, not a ZF-B3 one.**

| Consumer | Status | What it needs |
|---|---|---|
| `Codes2Tape.exists_uniformMachineCode2` | ZF-B3's open target | Simulate at most `t` source steps, `t` in binary on a tape, over two persistent source tapes; one joint polynomial |
| `Diagonalization/EXPCOM.lean` | sorried | The same pattern ("simulate at most `t` source transitions under a binary countdown") |
| `Diagonalization/NTimeHierarchy.lean` | sorried | A **fused** countdown at **linear** overhead: one tick per simulated step, the borrow cost amortized by `Σⱼ ν₂(j) ≤ t` (round-1 finding 5). It needs an **amortized total**, not a per-tick worst case |
| `SpaceComplexity/Hierarchy.lean` | sorried | A configuration-count clock |

**Existing clocks, all private or super-linear.** These are 12.2c candidates
for re-derivation as consumers of the shared host, not inputs to copy:

- `Build/Loop.lean`'s fuel debit: `loopDebit`, `loopValue`, `loopHost_borrow*`.
- `Build/Catalog.lean`'s `f2_loopDebitTM` / `f2_loopBorrow_correct`. This is a
  clean 1-tape little-endian decrement: exact `2·(borrow position) + 2`
  steps, zero wraps to all-`true` with an underflow verdict. It is stated
  only canonically.
- `Universal.lean`'s private deadline interpreter `timedUniversalTM`, the
  quadratic one-tape clock behind `timed_universal`.
- `TimeHierarchy/ClockMachine.lean`'s `clockTM`, the deterministic quadratic
  re-scan. These are colleagues' files; under the user's standing preference
  any dedup there is 12.2c work, not theirs.

**Proposed components.**

**C1 — `decrementTM k i : MultiTapeTM k Bool FlagPhase`**, an R3-family row,
the mirror of `incrementTM`. It scans `false` cells to `true` moving right; the
first `true` becomes `false`, with the success verdict; reaching the right
blank, the word is all `false`, so the value is `0`, and the verdict is
underflow, leaving the word all `true`. It returns to the origin through a
`rewind` phase. Framed contracts, in the §12.6 shape:

- `decrementTM_run_succ_ofCfg`, at exact time `2q + 2` where
  `q = (w.takeWhile (· = false)).length`;
- `decrementTM_run_underflow_ofCfg`, at `2|w| + 2`.

The **proof route must not copy the increment proof.** `decrementTM` is
`incrementTM` conjugated by bit complement, so its contracts are derived from
increment's proved framed contracts by a public symbol-complement transport
lemma (decision 12.7.4).

**C2 — `counterLoopTM`, the counter-driven loop host.** Given a body
`B : MultiTapeTM k Bool S` with a re-entry anchor `a`, the host has
`k + 1` tapes, the last one the counter, and states `S ⊕ FlagPhase`.

- At the anchor it runs `decrementTM` on the counter.
- On success it re-enters the body at `a`.
- On underflow it exits to a live `done` anchor.
- If a body round reaches a designated body exit (for a simulator: the
  simulated machine halted), the host exits to a second live `escape`
  anchor.

Its contract `counterLoopTM_run` is stated over **arbitrary configurations**
and has three parts:

- **The body's hypotheses.** A body invariant `P`. A round contract: from any
  `c` with `P c` at `a`, the body reaches, at the exact time `τ c > 0`, either
  the anchor again (with `P`, giving `next c`) or the exit (giving
  `exitCfg c`), without revisiting `a` earlier. And the body never touches the counter
  tape, which the host's embedding enforces.
- **The conclusion.** From the host configuration carrying `c` and a counter
  word `w` of value `d`, delimited:
  - if no round exits early, the host reaches `done` after exactly `d`
    rounds, with body part `next^[d] c` and counter `List.replicate |w| true`;
  - otherwise it reaches `escape` at the first exiting round `r < d`.
- **Total time, exact:** `Σ_{r<d} τ(next^[r] c)` plus the decrement costs
  `Σ_{v=1}^{d} (2ν₂(v) + 2) + (2|w| + 2)` (amortized, at most `4d + 2|w| + 2`)
  plus explicit per-round dispatch constants, fixed when the statements are
  drafted, in the first case; correspondingly in the second. **Uniform-bound
  corollary:** if `τ c ≤ B` whenever `P c`, the total is at most
  `d·B + 4d + 2|w| + O(d)`. Both cases come with no earlier exit and with trajectory
  bounds (counter head within `[pos − 1, pos + |w|]`, body heads as the body's
  own).

C2 is assembled from the §12 layer: the embedding for the body's tape
selection, seams for the anchor/decrement alternation, and the C1 contracts.
No loop-host proof is copied.

**Decisions (user, 2026-10-10).**

1. **Counter placement: a dedicated extra tape**, the host's last tape.
2. **Exits: two live anchors**, `done` and `escape`. A consumer attaches one
   continuation to each with two `seamCompTM` applications, so no new
   composition lemma is needed. A corollary drops the `escape` hypothesis for
   bodies that never exit early. The outermost machine adds its halt once.
3. **Round cost: an exact per-round cost function `τ` of the body
   configuration at the round's start.** The total time is stated exactly as
   the sum over the run's rounds. A round-indexed cost is the special case
   `σ r := τ(next^[r] c)`. A consumer that knows only a bound takes `τ` to be
   the first-return time, which is unique since the contract excludes earlier
   returns. The **uniform bound `B`** is a corollary. This is the
   sensitivity downstream consumers need, for example simulations whose step
   cost grows with tape content.
4. **Decrement proof route: a symbol-complement transport lemma** (option a).
   The §12.6 fill has landed, so increment's framed traces stay as they are.
   The lemma is generic over machines conjugated by a symbol involution, and
   it lives with C1.
5. **Home: a new `Build/CounterLoop.lean`**, importing Catalog, Embed and
   Seam. The 12.2c per-theme reorganization of `Build/` regroups it later.
6. **Scope: the amortized total is stated over the whole run**, not only
   per round.

**Statement phase (2026-10-10).** `Build/CounterLoop.lean` landed with 13
definitions and 10 sorried theorems. The refinements made while drafting:

- **The exit is an `Option S`.** The no-escape corollary is the
  instantiation `exit = none`, so no separate statement is needed.
- **The round hypotheses are stated along the orbit**, not through an
  invariant `P`. This is weaker and so more general; a consumer with an
  invariant derives them.
- **The uniform-bound corollary is pure arithmetic** over the exact time
  (`counterLoop_time_le`). Two amortization lemmas are stated: one for
  prefixes (`4r + 2|w|`) and one for the whole run (`4d + 2|w| + 2`).
- **`decrementTM` is defined as the conjugate** of `incrementTM` by
  `Equiv.boolNot`, through a generic `MultiTapeTM.mapWorkSymbols`. The C1
  contracts are therefore transports of the §12.6 ones.
- **The host has no dispatch steps.** Transitions into the anchor and the
  exit are redirected in place, so the time is exactly the round times plus
  `counterOverhead`.
- **Imports.** Seam is not imported, since consumers compose through
  `seamCompTM_run_ofCfg`. As with `Build/Zone.lean`, the file stays out of
  the `TuringMachine` facade during the statement phase.
- **The counter value** is Mathlib's `Nat.ofDigits 2 (w.map Bool.toNat)`,
  written inline; no new value function is defined.

The executed pre-ship check is `audits/evidence/s12-counter/`, and the gate
pack is `audits/s12-counter-{pack,bundle}.md`.

**Statement gate CLOSED (round 1, 2026-10-10: 0 blockers, 0 majors, 1 minor,
5 notes; `audits/s12-counter-findings.md`).** No false theorem and no missing
soundness hypothesis. Three notes correct or extend this design:

- **SC-4: two continuations need a public prefix lemma.** Two `seamCompTM`
  applications do wire both exits. The escape path through the first
  composite, however, needs the pre-dispatch prefix correspondence, which
  `seamCompTM_run_ofCfg`'s `hexit` cannot provide. The existing private
  `seamComp_left` (`Build/Seam.lean`) proves exactly that. It is to be
  promoted when the first two-continuation consumer is assembled, not copied.
  This corrects decision 12.7.2's claim that "no new composition lemma is
  needed."
- **SC-3: the NTIME consumer needs a nondeterministic lifting.** The host's
  contracts are deterministic (`MultiTapeTM`, `runFrom`). Before the NTIME
  hierarchy fill, a choice-stream lifting contract is needed, with branch
  alignment through the bookkeeping pauses.
- **SC-5: an optional visited-set corollary.** A public `spaceUsedByTape` or
  visited-set corollary of the trajectory clauses would save the space
  consumers repeated bookkeeping.

Next: the fill batch, after RB5 merges so the host proof can cite the
promoted `MultiTapeTM.runFrom_mapState_of_agreeOn`. ZF-B3's continuation
follows that fill. The existing private
clocks are on the 12.2c tasklist as re-derivation targets (plan §4d,
item 12).


### 12.8 Configuration-graph rows (design draft, 2026-10-10; for the statement phase)

*Drafted from the S1 research (maintainer-commissioned), recorded for the user's decisions 12.8.1–12.8.6. The maintainer's alternative for 12.8.1 is at the end.*

**Why.** The user chose design A for S1b, the summit of `ConfigGraph.lean`:
a configuration-level simulator built on §12 rows (decision log, 2026-10-10).
The S1 research found six capabilities that no public row provides.

| Gap | Missing capability |
|---|---|
| GAP-1 | a native-input-dependent clean seam |
| GAP-3 | a framed compare |
| GAP-4 | a configuration codec with transition application |
| GAP-5 | writing a word at a displaced head |
| GAP-6 | seek over delimited records |
| GAP-7 | two continuations after `counterLoopTM` |

This note proposes reusable rows for all six. Their consumers are every
configuration-graph walker of the campaign:

- S1b (`NSPACE ⊆ DTIME(2^{O(S)})`, hence `NL ⊆ P`);
- Savitch;
- the `PATH` reduction;
- the space hierarchy;
- `TQBF ∈ PSPACE`;
- `NP ⊆ PSPACE`.

**Constraints.**

- (i) **G1** is generalizing `Build/Embed`, `Build/Seam`, Catalog's R3
  sweeps and `FinTM.bufferTape` to `{Symbol : Type*}` in place. A row that
  extends those files' private traces waits for the G1 gate.
- (ii) **G2** (`copyMapTM`/`transferMapTM`) owns the mapped-sweep scanner in
  Catalog. Rows of that family are coordinated with it: one trace per routine
  family.
- (iii) Every row has a framed contract in the §12.6/§12.7 shape (template
  below).
- (iv) The campaign deciders are `FinTM Bool`. `incrementTM`, `decrementTM`,
  `counterLoopTM`, the compare contracts and the Loop hosts stay at `Bool` after
  G1. The record layer is therefore **binary**: decision 12.8.1.

#### Contract template (all rows)

For a tape `i` and a word `w`, write **`Delim d i w`** for the §12.6
hypothesis `∀ p, -1 ≤ p → p ≤ |w| → d.workTapes i (d.workTapePos i + p) =
bufferTape w p`. That is, `w` sits at the head with blanks at `-1` and `|w|`.
Each row `R` states, from any `d` in its start phase:

1. **Exact time** `τ`: `R.runFrom d τ = finish`, where `finish` is `d` with only
   the listed cells and control changed. Every other cell, every head, the
   native input position and the output are unchanged unless the row says
   otherwise.
2. **No earlier exit:** `∀ t < τ, state ≠ done`. (For verdict anchors, this is
   `∀ b`.)
3. **Trajectory:** touched heads stay in a stated interval, typically
   `[pos − 1, pos + |w|]`, and the other heads are fixed. Space follows by
   `MultiTapeTM.spaceUsedByTape_le_card_Icc`. That lemma lives in
   `Build/Zone.lean`, so Catalog rows cannot cite it; 12.2c item 9's Zone split
   is its natural moment to move down.

The time constants below are indicative. The statement phase fixes them by
the executed pre-ship check, as in §12.6 practice.

Where an exact closed form is unnatural (R8.7's step row), the contract is the
first-return form instead: `∃ t ≤ B`, plus the no-earlier-exit clause.
`counterLoopTM` consumes it with `τ :=` that `t`, which is unique (decision
12.7.3).

#### R8.1 Framed compare (GAP-3)

- `compareTM_run_ofCfg (fst snd) (hne : fst ≠ snd) (u v) (d)
  (hstate : d.state = some .run) (hu : Delim d fst u) (hv : Delim d snd v)`.
  - Exact time `2·δ + 2`, with `δ` the first index where `u` and `v` differ or
    either word ends (`δ ≤ min |u| |v|`, the private `catalog_compare_stop`).
  - Finish: `d` with state `done (decide (u = v))`, every tape unchanged.
  - No earlier `done b`. Trajectory: both heads in `[pos−1, pos+δ]`.
- **Alphabet:** generic with `[DecidableEq Symbol]`. G1 makes `compareTM`'s
  definition generic and keeps its contracts at `Bool`, so the framed row is
  stated generically from the start, and the canonical `compareTM_run` is
  re-derived from it by a sanctioned body swap, exactly as §12.6 did for
  copy/transfer/clear.
- **Trace:** generalize `catalog_compare_trace`, `catalogCompareF` and
  `catalogCompareR` over an outer frame and two start coordinates, on the
  shared `catalog_trace_run` skeleton. No second trace.
- **Home:** `Build/Catalog.lean`, **after the G1 gate**.
- **Note:** a record is a list of blank-separated fields (R8.7), so
  `recordEqTM` is `F` framed compares with R8.3 seeks between them.

#### R8.2 Fold: a finite-state scan with a verdict (new family member)

- `foldTM (i) (δ : A → Symbol → A) (a₀ : A) [Fintype A] [DecidableEq A]`.
  Phases are the forward pass `scan a`, the return `rewind a`, and the anchor
  `done a`.
- `foldTM_run_ofCfg (hw : Delim d i w)`:
  - exact time `2|w| + 2`;
  - finish: `d` with state `done (w.foldl δ a₀)`, all tapes unchanged;
  - no earlier `done`; trajectory `[pos−1, pos+|w|]`.
- **Why a row:** every read of a record field into finite control is a fold.
  That covers the state field, the tag field, "find the marked cell and its
  content and whether it sits at a field end", record validity, and
  acceptance tests. Validators elsewhere (TQBF's well-formedness pass, the
  `PATH` shape checks) are folds too.
- **Alphabet:** generic. **Trace:** `catalog_trace_run` with a read-only
  forward family, as for `copyTM` without the destination. **Home:** Catalog,
  after G1.

#### R8.3 Seek over delimited words and records (GAP-6)

- `skipTM i`: from `Delim d i w`, move right to the word's right delimiter
  and one cell beyond, the next word's first cell. Exact time `|w| + 1`; no
  write; trajectory `[pos, pos+|w|+1]`. `skipBackTM i` is the mirror, starting
  on the cell after the left delimiter of the previous word.
- `skipTM_run_ofCfg` and `skipBackTM_run_ofCfg` have the template shape, with
  the finish `{d with workTapePos i := pos + |w| + 1}`.
- `seekFieldsTM i m` (`m` fixed) composes `m` skips by `seamCompTM_run_ofCfg`.
  `seekEndTM i` skips until the next word is empty (two consecutive blanks);
  it is a fold-guarded loop, under the same skeleton.
- **Consumers:** record navigation (R8.7, S1b's table, Savitch's frame stack),
  and **G4**, which "scans outward across zones, using the separators". Both
  skip blank-separated words, so G4 should cite `skipTM` rather than trace its
  own scan.
- **Trace:** this is the forward half of the R3 trace. Add a forward-only
  sibling of `catalog_trace_run` (`catalog_forward_run`, private), to be shared
  with R8.2's forward phase.
- **Alphabet:** generic. **Home:** Catalog, after G1, **coordinated with G2/G4**.

#### R8.4 Writing words at displaced heads (GAP-5)

- **Computed words** are G2's `copyMapTM`/`transferMapTM` (`merge` and
  `extract`). With `extract := fun _ => b` they fill a blank-free interval with
  a constant (`fillTM i b` is the in-place case `src = dst`, which G2 must
  admit or state separately). Nothing new: G2.
- **Fixed words**: `writeConstTM i (w₀ : List Symbol)` writes the hardwired
  `w₀` from the head and returns.
  - `writeConstTM_run_ofCfg`: exact time `2|w₀| + 1`; finish: cells
    `[pos, pos+|w₀|)` hold `w₀` (old contents arbitrary), head back at `pos`;
    trajectory `[pos, pos+|w₀|]`.
  - The machine is a straight-line chain; its proof uses the public
    `FinTM.emit_run` pattern adapted to writes, so it shares no Catalog trace.
  - **Home:** new `Build/Scan.lean`; **can land now**.
  - **Consumers:** record field initializers (state code, tag code), marker
    cells, per-round patterns inside R8.6's body.

#### R8.5 Native-input rows (GAP-1)

All three are generic over `Symbol`, cite the public `FinTM.rewind_scan` and
`timed_rewind`, and live in new `Build/Scan.lean` (**now**). EmitIterBody's
private startup (`body_start`, `copy_step`, `rwTape_*`, `rwInput_*`) is the
same routine and should be re-derived from `inputCopyTM` in 12.2c T2 (CH7-D2,
coordinated with Aparna).

- `inputCopyTM i`: copy the native input onto tape `i` from the head, then
  rewind both heads.
  - Start: input head at `1`, `Delim`-free destination (old contents
    arbitrary).
  - Exact time `2|x| + c`. Finish: `[pos, pos+|x|)` holds `x`, input head at
    `1`, tape head at `pos`.
  - Trajectory: input head in `[0, |x|+1]`, tape head in `[pos−1, pos+|x|]`.
- `inputLengthTM i`: count `|x|` into a fixed-width binary counter on tape `i`
  (one `incrementTM` per input symbol, cited at its framed carry-sensitive cost).
  - Exact time `Σ_v (2·ν₂(v) + 2) + |x| + c`, amortized at most `4|x| + c`
    (§12.7's potential).
  - Finish: the counter holds `bits |x|` padded to its width, and the input head
    is back at `1`.
  - Bool only, because it uses `incrementTM`. Its home is `Build/CounterLoop.lean`
    or `Scan` importing it.
- `inputSeekTM i c`: move the input head to the binary position `p` held at
  tape `i`.
  - Mechanism: copy `p` to the counter tape `c` (`copyTM_run_ofCfg`), rewind the
    input (`timed_rewind`), then `counterLoopTM` with the one-step body "input
    right".
  - Exact time: the copy (`2|p| + 2`), the rewind (`≤ pos + 2`), then
    `p + counterOverhead w (p + 1)`.
  - Finish: input position `p`, counter tape all-`true` (`counterLoopTM_run_done`).
    Callers clear it (`clearTM_run_ofCfg`).
  - Bool only.
  - **Consumers:** R8.7's input read, `PATH_mem_NL`'s matrix indexing (`u·n + v`),
    virtual-input callers needing random access.
- Packaged combinator **`exists_inputCallTM`** = `inputCopyTM` +
  `exists_installCallTM`: call a function-level machine on the native input at a
  clean seam. It is GAP-1's general form. **Home:** new `Build/InputCall.lean`,
  importing Loop, **now**. It touches no G1 file, but must not collide with
  12.2c T1 item 11's Loop edits.

#### R8.6 Counter-driven expansion

- `expandTM (pat : List Bool)` = `counterLoopTM` around `writeConstTM pat`
  followed by a `skipTM`-like advance. From a counter word of value `d` at the
  counter tape and a blank region on tape `i`, it writes `pat` `d` times
  contiguously.
  - Exact time `Σ_{r<d} τ_pat + counterOverhead w (d+1)`, by
    `counterLoopTM_run_done` and `counterLoop_time_le`.
  - The written word is `pat`ⁿ with `n = d`, which is a framed `Delim` for later
    rows.
- **Consumers:**
  - S1b and Savitch: blank tape fields of `2s+1` cell codes, with `s` given in
    binary by the constructor;
  - `spaceConstructible_logSpace`/`_linear`/`_poly` (binary ↔ unary);
  - the space hierarchy's budget loop;
  - the §12.7 clocks.
- Bool. **Home:** `Build/CounterLoop.lean` (not G1-owned). **Can land now**,
  once R8.4's `writeConstTM` exists.

#### R8.7 Configuration records (GAP-4)

**Pure layer** (new `Build/CfgRecord.lean`; statements now).

- **Parameters:** a source `M : MultiTapeTM k Bool Q`, `[Fintype Q]`, a window
  radius `s`, an input length `n`, and a finite **tag** type `T` with an update
  `upd : T → Option Bool → T`. The tag carries emission history; the
  configuration graph instantiates `T := OutSummary` and `upd` := the Q1 append
  table. A Build-level row cannot mention `OutSummary`, which is defined
  downstream in `ConfigGraph.lean`; hence the parameter.
- **`cfgRecord n s (c : Cfg k Bool Q x) (τ : T) : List (List Bool)`**, a list of
  `k + 3` **blank-separated fields**, each a blank-free Bool word:
  - **F0** state: a one-hot code of `c.state : Option Q`, width `|Q|+1`;
  - **F1** input position: `c.inputPos` in little-endian binary at the fixed
    width `|bits (n+1)|`;
  - **F2…F(k+1)** tape `i`: `2s+1` three-bit cells
    `(nonblank, value, head-here)` for `z = −s … s`;
  - **F(k+2)** tag: a one-hot code of `τ`.

  Field lengths depend only on `(n, s)`, so records compare field-wise and
  enumerate by counting.
- **`recordTape`** lays the fields out with one blank between fields (and
  between records); the G3 carrier's separator discipline.
- **Window predicate.** `Turing.Cfg.InWindow s` already exists, defined in
  `ClassPSPACE/TQBF.lean`, *downstream* of every Build file. **Decision
  12.8.2:** relocate it verbatim (same name and body) to `CfgRecord.lean` and
  delete TQBF's copy. That is a surface move in a C1d-owned file, so it waits
  for C1d. The alternative is a second predicate under another name, a
  definitional duplicate.
- **`cfgRecord_inj`:** for `InWindow s c` and `InWindow s d` on the same input,
  `cfgRecord n s c τ = cfgRecord n s d τ' ↔ core c = core d ∧ τ = τ'`. It
  follows `ConfigCount.coreCode_inj`.
- **`cfgRecord_valid`:** a word list is a record iff a fold (R8.2) accepts each
  field. One-hot fields, three-bit cells with exactly one head mark per tape
  field, and `F1 ≤ n+1` (the last by `compareTM` against `bits (n+1)` or by
  a fold).

**Rows** (`Build/CfgRecord.lean`). The statements can be drafted now. The
fills need R8.1–R8.3, so they come after the G1 gate.

| Row | Effect (framed; record at the head of tape `r`; scratch tapes blank) | Built from |
|---|---|---|
| `recordReadTM` | Verdict `done (q, ι, σ, τ, edge)`: state, the input symbol at the coded position, the `k` scanned symbols, the tag, and which tape heads sit at a field end. Record unchanged; input head restored | R8.2 folds per field, R8.3 seeks, R8.5 `inputSeekTM` on a copy of F1, `clearTM` |
| `recordApplyTM a` (`a : Action k Bool Q` fixed, `upd` fixed) | Rewrites the record of `c` into that of `a.apply c`, with the tag updated by `a.output`. Per tape it rewrites the marked cell and moves the mark; F1 gets `incrementTM`/`decrementTM` (framed), with the clamp read off the edge data; F0 and the tag go through `writeConstTM`. Precondition: no mark leaves its field (checked by the read) | R8.4, R8.3, Catalog `incrementTM_run_*_ofCfg`, CounterLoop `decrementTM_run_*_ofCfg`, and one local `markShiftTM` per tape field (new, record-specific) |
| **`recordStepTM M upd`** | **The GAP-4 row.** Verdict `done true` with the record of `M.step c` (tag updated) if that configuration is in the window. Verdict `done false` with the record unchanged otherwise, or if `c` is halted (`done true`, unchanged: a halted vertex is its own successor). First-return contract, `t ≤ C_M·(L + n + 1)` with `L` the record length; trajectory inside the record interval and `[0, n+1]` on input | `recordReadTM` ; finite dispatch on `M.tr` ; `recordApplyTM a`, glued by `seamCompTM_run_ofCfg` and two-continuation dispatch (R8.8). An NDTM is consumed per choice bit through `NDTM.fixChoice` (S1a's promotion) |
| `recordInitTM` | Writes the record of `M.initCfg x` with tag `τ₀`, from a radius word (binary `s`) and the input length counter | R8.4, R8.5 `inputLengthTM`, R8.6 `expandTM` |
| `recordEqTM` | Verdict: the two records at the heads of tapes `r`, `r'` are equal | `k + 3` R8.1 compares with R8.3 seeks |
| `recordTestTM P` (`P` a finite predicate on `(state, tag)`) | Verdict `P (c.state, τ)`. Acceptance is `P := (· = none) ∧ (· = accept)` | R8.2 on F0 and the tag field |
| `recordNextTM` | Lexicographic successor among *valid* records (odometer over all field bits, skipping invalid ones), or an overflow verdict | `incrementTM` per field, carry cascade, `recordValidTM` |
| `recordValidTM` | Verdict `cfgRecord_valid` | R8.2 |

**Space.** Every record row is framed inside its record interval plus
`O(L)` scratch. `L = O(k·s + log n + |Q|)`, which is `O(S n)` for Savitch at
`S ≥ logSpace`. This is why F1 is **binary**: a one-hot input track would make
`L = Θ(n)` and break `SPACE(S²)` at `S = log`.

#### R8.8 Two continuations after a two-exit host (GAP-7)

- Promote the existing private `Turing.seamComp_left` (`Build/Seam.lean:173`)
  as **`seamCompTM_runFrom_left`**, statement unchanged. This is SC-4's
  resolution: "expose the existing prefix lemma … do not copy its induction".
- Add one corollary, **`seamCompTM₂_run_ofCfg`**: for a host with two live
  anchors `e₁`, `e₂` (`counterLoopTM`'s `done` and `escape`), nesting two
  `seamCompTM`s attaches a continuation to each. It states the run along
  whichever exit is reached, with the other continuation's summand
  unreachable.
- Generic after G1. **Home:** `Build/Seam.lean`, **after the G1 gate**.
- **Consumers:** every `counterLoopTM` user with an early exit. S1b's BFS
  (queue empty / counter exhausted), the space hierarchy's budget loop
  (success / cap), and `recordStepTM`'s internal dispatch.

#### Placement and timing

| Row(s) | Home | Touches a G1-owned file? | When |
|---|---|---|---|
| R8.4 `writeConstTM`; R8.5 `inputCopyTM`, `inputSeekTM`, `inputLengthTM` | new `Build/Scan.lean` (imports CounterLoop) | no | **now** |
| R8.5 `exists_inputCallTM` | new `Build/InputCall.lean` (imports Loop, Scan) | no | **now** (coordinate with 12.2c item 11) |
| R8.6 `expandTM` | `Build/CounterLoop.lean` | no | **now**, after `writeConstTM` |
| R8.7 pure layer, `InWindow` relocation | new `Build/CfgRecord.lean`; `ClassPSPACE/TQBF.lean` | no; TQBF is C1d's | statements now; relocation after C1d |
| R8.1 framed compare; R8.2 fold; R8.3 seek | `Build/Catalog.lean` | **yes** | **after the G1 gate**, with G2 (shared scanner) |
| R8.4 fill (in-place mapped sweep) | Catalog (G2) | **yes** | with G2 |
| R8.8 seam promotion + corollary | `Build/Seam.lean` | **yes** | **after the G1 gate** |
| R8.7 record rows (fill) | `Build/CfgRecord.lean` | no, but cites R8.1–R8.3 | fill after R8.1–R8.3 land |

The process is the house one: maintainer-drafted statements; an executed
pre-ship check (concrete configurations, displaced heads, nonblank outer
frames, `w = []`, `s = 0`, `k = 0`, a halted source); a short statement gate;
fill batches split now/after-G1; a fill gate.

#### Consumers: which rows each walker uses

| Consumer (audited sketch) | Rows |
|---|---|
| **S1b** `NSPACE_subset_exp_dtime` (BFS; then `NL_subset_P` and Ex 4.3 by the binding route) | R8.7 `recordInitTM`, `recordStepTM` (×2 choice bits), `recordEqTM`, `recordTestTM`; R8.3 table navigation; R8.4/G2 append and counter initialization; R8.6 window fields; R8.8; existing `counterLoopTM`, `embedSilentRetTM_run` (constructor capture), `seamCompTM_run_ofCfg`, `copyTM_run_ofCfg` |
| **Savitch** `savitch` ("frame stack … catalog copy/compare/increment … one extra bank runs the vertex-adjacency test") | `recordStepTM` + `recordEqTM` for `adj(u, v)` (`u = v ∨ step u = v`, both choice bits); `recordNextTM` + `recordValidTM` for the midpoint enumerator; R8.3 seek over the frame stack; `copyTM`/`clearTM` for frame push/pop at **fixed intervals** (note 7); `incrementTM` for the depth field; R8.8 for the recursion's two returns. Space contracts of every row are load-bearing |
| `spaceConstructible_poly`/`_logSpace`/`_linear` | R8.5 `inputLengthTM`; R8.6 `expandTM`; `incrementTM` |
| **`PATH_NLComplete`** hardness (adjacency "by one local transition-table check", logspace) | The sketch's engine is the ARM layer (`arm_decides`). Optionally, a TM route: `recordStepTM`'s space clause with binary F1 gives `O(log n)`-space adjacency deciders for the index languages. Decision 12.8.4 |
| **`PATH_mem_NL`** (matrix indexing) | R8.5 `inputSeekTM` (once a nondeterministic host exists, SC-3) |
| **Space hierarchy** `space_universal`, `space_hierarchy` (interval counters, core-count clock, budget loop, probe/replay over fixed banks) | `incrementTM`/`decrementTM` (interval counters), `counterLoopTM` + R8.6 (clock and budget loop), R8.8 (success/cap exits), R8.1 (`max − min + 1 > s` against the budget word), `clearTM` resets. It simulates a *coded* machine, so not R8.7 |
| **`TQBF_mem_PSPACE`** (validate-first, depth-first assignment walker, per-clause CNF evaluation) | R8.2 folds (validation, clause evaluation), R8.5 `inputSeekTM` (re-reading prefix bits and matrix bytes), `incrementTM` / a trit odometer (`recordNextTM`'s carry discipline) for the walker, R8.3 seek on the assignment word |
| `NP_subset_PSPACE` | existing `incrementTM` (certificate enumerator) and `vhostEmitTM` (virtual input); R8.8 for accept/exhaust |

#### S1b's machine plan as a composition of these rows

**Host.** A `FinTM Bool`. It has the native input; the constructor's embedded
tapes plus a capture tape; tape `Tab` (the record table); `Cur₀` and `Cur₁`
(successor workspaces); `Rad` (radius and length words); scratch for
`recordStepTM`; and `Cnt`, the counter, which is the last tape, as
`counterLoopTM` requires.

1. **Radius.** Run `M_S` (from `hS`) under `embedSilentRetTM_run`, with its
   output `bits (S n)` captured, then rewind the input (`timed_rewind`). Its time
   is at most `M_S.configBound n (a·S n)` (`ComputesInTime.of_spaceUsed_le`).
   Multiplying by `c₀` is a fixed binary shift-and-add or `c₀` copies.
2. **Initial table.** Lay down `recordInitTM` (via `inputLengthTM` and
   `expandTM`) on `Tab`, with tag `empty` and a one-bit flag field `[false]`
   ("unprocessed") appended to each record.
3. **Counter.** Copy `Tab`'s first record's fields to `Cnt` contiguously
   (`copyTM_run_ofCfg` + `skipTM`), then fill it with `true` (G2 in-place map).
   Its value `2^{bits(record)} − 1` exceeds the record count `V`, so `done` is
   unreachable before `escape` (or is wired anyway by R8.8).
4. **Round** (the `counterLoopTM` body, anchor `a`). `seekFieldsTM` finds the first
   record whose flag is `false`; if there is none, it reaches the body's exit, and
   the host escapes. Otherwise:
   - copy that record to `Cur₀` and `Cur₁`;
   - run `recordStepTM (N.fixChoice false)` on `Cur₀` and
     `recordStepTM (N.fixChoice true)` on `Cur₁`;
   - for each successor in the window, scan `Tab` with `recordEqTM`, and if it
     is absent, append it at `seekEndTM` with flag `[false]`;
   - set the processed record's flag (`incrementTM` on the one-bit field);
   - clear the workspaces, rewind `Tab` (`skipBackTM` to the table start), and
     return to `a`.

   The round's first-return time `τ` is at most `C·(|Tab| + n + L)` with
   `|Tab| ≤ V·(L + F)`.
5. **Verdict.** From either exit (R8.8), fold `recordTestTM accept` over
   `Tab`'s records and emit `[true]` or `[false]`; then halt (a fixed emission
   tail; `FinTM.emit_run` pattern).
6. **Correctness:**
   - The table is the windowed-reachable set: the BFS invariant, with each record
     identified with a `coreSum` by `cfgRecord_inj` at `T := OutSummary`.
   - Membership follows by S1a's targets 1–4 and the audit's note-6 bridge
     (canonical decoding, outside-window rejection by `recordStepTM`'s false
     verdict, path lifting from the true initial configuration, all accepting
     vertices tested, the initial vertex in the table).
7. **Time:**
   - `counterLoop_time_le`: `V·B + 4V + 2|w| + 2` with `B = O(V·L + n)`. Add the
     constructor and startup.
   - Everything is at most `K·2^{c'(S n+1)}`, by the generalized `configBound`
     arithmetic and `n + 2 ≤ 2^{S n + 1}`.
   - All budgets are evaluated at `n` itself. **No monotonicity of `S` is used.**

#### Decisions for the user (12.8.x)

1. **Binary records** (recommended). The rows stay on the `Bool` counter stack,
   with no generic increment or `counterLoopTM`. The alternative is a
   rich-alphabet record: one cell per simulated cell, a simpler step machine, and
   `alphabet_reduction{,_spaceUsed}` at the end. It needs `incrementTM`,
   `decrementTM` and `counterLoopTM` generalized over two designated digit
   symbols (Catalog is G1-owned; CounterLoop is not).
2. **`Cfg.InWindow` relocation** from TQBF to `Build/CfgRecord.lean`, after C1d.
3. **`recordStepTM`'s contract form:** first-return with a bound (recommended),
   or an exact closed form.
4. **`PATH` hardness engine:** ARM (as sketched) or TM record rows with space
   clauses.
5. **Fold and seek in Catalog** (one trace family, after G1), or in `Scan` now
   with their own private skeleton. The latter is faster, but it is a second
   trace of the R3 forward pass.
6. **EmitIterBody dedup** onto `inputCopyTM` in 12.2c T2 (coordinate with
   Aparna).

#### Maintainer's alternative for 12.8.1: rich-alphabet records through one embedding transport

Records could follow the §13d pattern instead of being bit-coded. Each record
cell is one rich symbol with tracks (content `Option Bool`, head mark, field
separators), as in the G3 `ZoneCell` carrier. Moving a head mark is then a G2
mapped sweep on one track, and no per-tape `markShiftTM` is needed. Fields
compare through the generic framed compare, and folds read one symbol per
cell.

The binary rows (`incrementTM`, `decrementTM`, `counterLoopTM`, the compare
contracts) need not be generalized. **One new transport lemma** runs them on
rich tapes: the embedding analogue of §12.7's `mapWorkSymbols`, which lifts a
`Bool` machine along `e : Bool ↪ Γ`. Its contract holds from configurations
whose work cells all lie in the image of `e` or are blank, which a dedicated
counter tape satisfies.

The simulator is finished by `alphabet_reduction` for time and by
`alphabet_reduction_spaceUsed` for space (space at most `(N+1)·space + k`).
The latter keeps Savitch and the space hierarchy within their bounds. The
input-position field stays binary over designated digits, so record length
stays `O(k·s + log n + |Q|)`.

The cost is the transport lemma, and records that wait for G2's mapped sweeps
(after the G1 gate). The gain is that the record machines become compositions
of generic rows instead of bit-group machines, and §12.8 and §13d share one
multi-track discipline.

## 13. The zone and virtual-input layer (proposed 2026-10-09, post-§12 close)

**Mandate** (user direction 2026-10-09, at the §12 fill-campaign close —
track A of the two parallel tracks, the other being the chapter-1/2
retrofit): the §12 scope note **R9 promoted**. R9 drew the line at
physical-tape selection — `ι` relocates whole tapes and "the Hennie-Stearns
and universal-machine consumers get their zone/virtual-input representation
layers separately" (`Build/Embed.lean` header). This increment is that
separate layer. It gates the two stage-1 builds (the Hennie-Stearns `k`→2
conversion and the two-work-tape universal machine, plan §2.1/§4b) and is
scoped, like §12, beyond its first consumers: the virtual-input half serves
the `NP^EXPCOM ⊆ EXP` summit and the 12.2c dedup, and the zone half is
shaped so the chapter-1 Robustness conversions can gain **space theorems
additively** (plan §2.7's fallback route to Ex 4.1/Thm 4.8). §12's space
mandate continues: **every item carries a space clause alongside its time
cost** (`Turing.MultiTapeTM.spaceUsed`, work tapes only).

**Evidence.** The virtual-input pattern has now been hand-built four times
over the proved corpus: the A2 forwarding controller's
`a2_mapVirtual`/`a2_mapVirtual_step`/`a2_mapVirtual_run` lockstep (15 of
its 45 privates; both boundary clamps, empty-word case, halt absorption —
all proved), F2A's `f2_splitCountAction`/`f2_splitCount_run`
(virtual *empty* input over preinstalled banks), the universal
interpreter's prefix-input discipline, and the oblivious candidate's
`obliviousVisit` virtual-tape transduction. All four sit on the same public
primitive — `virtualMove`/`VirtualTag`/`virtualNextTag` and
`bufferTape_inputSymbol` (`Simulation.lean`) — and each rebuilt the hosting
and lockstep privately. On the zone side, the in-repo precedents are the
`SingleTape.lean` multiplexing encoding (`SweepCell`/`tapeRow`) and
`ObliviousSetup.lean`'s guide-zone layout with its two-directional run
identities; what does not exist anywhere is a *reusable* zoned carrier with
shift routines. The F2 epoch audit's three optional regression corollaries
(zero-time startup, both virtual-input clamps, setup followed by an
emitting halting step) are adopted here as permanent lemmas of Z1.

**What already exists and is consumed, not duplicated**: the §12 layer
itself (R1/R2 and the catalog rows are the assembly language of every
construction below); `virtualMove`/`VirtualTag` (`Simulation.lean`);
`Turing.actionBits₂` and the `CodeNDTM` two-work-tape serialization
(`NDCodes.lean`, statement-frozen under the closed P3.3 gate) — Z3 builds
the deterministic sibling against the same record format, never a second
serialization; `UnaryTape.lean`; the harvest policy of §8 (reimplement
against the ABI with the original proof as template; audited originals stay
in place until the separately-tracked retrofit/12.2c dedup).

### Z1. Virtual-input hosting (the `a2_mapVirtual` pattern, promoted)

A transformer hosting a machine whose input is a **designated buffered
word** rather than the native input: given a host with an injective tape
selection (R1's `ι`) plus one buffer tape holding `y`, the hosted machine
runs with `y` as its virtual input, buffer head at
`source.inputPos - 1` under a `VirtualTag` boundary discipline. Spec shape:

* **lockstep** — one host step per source step, transported `runFrom`
  identity (the A2 `a2_mapVirtual_run` shape, generalized from its
  two-buffer controller to the R1 selection);
* **clamps** — both boundary clamps hold with **no nonempty-`y` premise**
  (empty `y`: position `0` is the right boundary, `-1` the left; outward
  moves stay, inward moves cross) — the binding A2/F2 audit contract;
* **halt absorption** — the source's halting action executes before the
  host control dies; later times are fixed;
* **emission policy** — suppressed or forwarded, mirroring R1's two modes
  (open decision 12.4 resolves both at once);
* **time** — exact; **space** — coefficient-one containment: each selected
  tape's host visited set is contained in the source's visited set on `y`
  at the same horizon (the R4 ledger shape, proved in `a2_map_space`).

Permanent regression lemmas (audit-adopted): the zero-time startup
instance, the two empty-`y` clamp instances, and the setup-then-emitting-
halt seam. Generic form of: `a2_mapVirtual*` (A2), `f2_splitCount*` (F2A,
the `y = []` specialization), the universal interpreter's input phase, and
the query simulation every oracle-summit machine will need.

**Z1 rider — the R1 selected-tape exports (decision D-R1, user
2026-10-09, from the retrofit inventories, plan §4d).** The three retrofit
inventories independently identified the same R1 API gap: `Embed.lean`
exports no selected-tape field lemmas (`embedSlot_selected`/`_unselected`
are private) and no agreeing-host lockstep, so no old-code R1 consumer can
be proved from the public surface. This statement phase adds, **additively
in `Embed.lean`** (shared-file mechanism, audited under this gate): public
selected-tape projections of `embedSilentCfg`/`embedEmitCfg` (contents and
head of tape `ι i`), and an `ofWords` transport form. Unlocks the blocked
Hardness families (M/N/AM/U, Z/AB/AG — ≈ 300-350 lines) at the next
retrofit window.

### Z5. Machine-agreement transfer (decision D-R3, user 2026-10-09)

A general lockstep-transfer lemma, the `hagree` genre of
`capture_run`/`emit_run` made standalone: two machines over the same tape
count and state type whose transition tables **agree on a set of states**
run identically, configuration for configuration, from agreeing starts for
as long as the run stays inside the agreement set; a guarded variant takes
the agreement hypothesis per reachable state. Natural home:
`Simulation.lean` beside the existing lockstep gadgets (placement open
decision 13.5: Simulation versus a `Build/` module). Customers (rule of
admission): the Loop forwarding host (H3's 14 verbatim re-proved phase
lemmas, ≈ 550 lines, collapse to one transfer — `emLoopHost` agrees with
`loopHost` on every non-body state); the 13 guarded `clSlot_run` agreement
sites in `CookLevin/Hardness.lean`; every future mode-variant host (the
§12 loop hosts' decision/find/emit triplet is exactly this pattern).
Estimate: ≈ 4 points spec + fill; the risk is quantifier placement on the
agreement set, not proof content.

### Z2. Zoned tape carrier (the Hennie-Stearns representation)

The representation of `m` virtual work tapes on **one** physical tape with
amortizable locality: a `ZoneLayout` (level count `ℓ`; per-level zones
`L_i`/`R_i` of capacity `2^i` around a home origin, [AB09] §1.7) and a
carrier predicate `ZoneCfg` relating one physical word to `m` virtual words
plus per-zone fullness states (empty / half / full). The layer owns:

* **the carrier** — `ZoneCfg` well-formedness, read/write-at-home
  contracts (the virtual heads always sit at the physical origin), and the
  cell-encoding convention (open decision 13.2: how `Option Bool` virtual
  cells embed into binary physical cells — paired-cell presence/data
  tracks, with `SingleTape.lean`'s `SweepCell` encoding as the precedent);
* **the shift routines** — per-level `shiftIn`/`shiftOut` rebalancing
  rows with **exact** costs `O(2^i)`, assembled from R3
  transfer/copy/clear via R2 seams, each with its space row (visited cells
  within the touched zones);
* **the cardinality lemmas** — visited-set bookkeeping for multiplexed
  tapes: physical space bounded by the sum of touched zone extents, the
  piece the Robustness space annotation (Z4) consumes.

Explicitly **on top, not inside**: the `2^i`-fullness invariant across a
run, the amortized `O(T log T)` charge, and the simulation theorem itself —
those are the Hennie-Stearns consumer's mathematics (plan §2.1), as the
§12 precedent kept the loop ledgers out of the loop host. Scope note:
Z2 is sized for the H-S discipline (one zoned tape + one scratch tape);
a general `k`→`k'` conversion is not in scope.

### Z3. Two-work-tape codes (the deterministic `actionBits₂` sibling)

The deterministic code layer currently covers only the one-work-tape
binary normal form (`EffectiveMachineCode`/`UniformMachineCode`,
`Encoding.lean`), which is why Thm 3.1 arrives at `f²` (plan §2.1). Z3
extends it: a deterministic two-work-tape code scheme over the
**same `actionBits₂` record format** as `CodeNDTM` (one branch instead of
two), with the `CodeParser` extension and the `UniformMachineCode`-style
uniform-decoding clause (the P3.2 lesson: variable-code consumers need the
uniformly-timed form). The two-work-tape **universal machine itself** is
the stage-1 consumer build, not part of this layer; Z3 ships the codes it
reads. Space rows on the parser rows from the start.

### Z4. Space annotation for the Robustness conversions (consumer-driven)

Additive `spaceUsed` theorems for the chapter-1 conversions
(`one_work_tape`, the alphabet reduction) via Z2's cardinality lemmas — no
signature changes, the audited surface untouched (the R3 retro-annotation
precedent). This is plan §2.7's fallback route to the space-efficient
universal (Ex 4.1, Thm 4.8). **Design-time obligation, recorded here**: at
the Z1-Z3 spec phase, assess whether the two-work-tape universal carrying
Z1/Z2 space rows yields Ex 4.1 directly; the answer (and hence whether Z4
is needed at all, and at which strength) is recorded before the statement
gate, so the chapter-4 risk register (§6 summit 1) is settled either way.

### Consumers (rule-of-admission check, §4: two named customers per item)

| Item | Customers |
|---|---|
| Z1 virtual-input hosting | the two-work-tape universal (stage 1); the `NP^EXPCOM ⊆ EXP` summit's query simulation; the 12.2c dedup of `a2_mapVirtual*`/`f2_splitCount*`; the P3.3 universal-NDTM fill's code/input discipline |
| Z2 zoned carrier + shifts | the Hennie-Stearns `k`→2 conversion (plan §2.1); the Robustness space annotation (Z4); the Ex 1.6 oblivious sharpening (recorded stretch goal, `Robustness/Oblivious.lean`) |
| Z3 two-work-tape codes | the two-work-tape universal; the Thm 3.1 re-derivation at `f log f` (Hydroxyi's diagonal argument over the new codes) |
| Z4 space annotation | Thm 4.8/Ex 4.1 fallback (plan §2.7); `L ⊊ PSPACE`/space-hierarchy fills (P4.3) if the universal route stalls |

### Placement, sequencing, cost

* New files `Build/VirtualInput.lean` (Z1) and `Build/Zone.lean` (Z2),
  namespace `Turing.FinTM`, order list after `Build/Catalog`; Z3 as a new
  `TuringMachine/Codes2.lean` beside `Encoding.lean` (placement open
  decision 13.3: a new file versus extending `Encoding.lean` — the frozen
  audited surface of `Encoding.lean` argues for the new file); Z4 lands
  additively in the `Robustness/` files through the shared-file mechanism,
  flagged for its own audit.
* Process per `workflow.md`, the §12 precedent verbatim: maintainer-serial
  spec layer (quantifier-sensitive), statement gate by external audit,
  fills as briefed batches with exclusive ownership, epoch-boundary fill
  audit. The gate must close before the H-S/two-tape-universal builds
  start; chapter-3/4 fill briefs written while this layer is open simply
  do not cite it (the EXPCOM brief prefers Z1 only if Z1 is closed).
* Estimate (campaign points): Z1 ≈ 8 (harvest-grade — the lockstep is
  proved four times over; the risk is quantifier hygiene, not proof
  content), Z2 ≈ 14 (genuinely new; the carrier predicate is the risk
  concentration, L-style), Z3 ≈ 6 (format fixed by `actionBits₂`), Z4 ≈ 6
  (retro-annotation against Z2's lemmas). Total ≈ 34, between the §12
  statement layer and one fill epoch.
* **Citation duty** (binding, the 2026-10-06 guideline and the 2026-10-08
  citation-audit row): the design adapts [AB09] §1.7 (Hennie-Stearns) and
  Exercise 1.5/1.6; the §12 duty extends here — Édouard Bonnet's
  lax-434930 `classical-complexity` (Apache-2.0, commit `0c084031…`) is
  cited in this addendum, the module docstrings, and the blueprint entries
  wherever its stack-machine routine catalog informed a row's shape; no
  external code is imported or transcribed.

### Open decisions (13.x, for the user at spec time)

1. **13.1 Zone discipline**: zones-with-fullness (the [AB09] §1.7 layout,
   proposed) versus plain interleaving (simpler carrier, no amortized
   locality — insufficient for H-S alone, but cheaper if Z2's only
   customer were Z4). Proposed: zones; interleaving is not built.
2. **13.2 Cell encoding**: how `Option Bool` virtual cells embed in binary
   physical cells (paired presence/data cells proposed; `SweepCell` as
   precedent).
3. **13.3 Z3 placement**: new `Codes2.lean` (proposed) versus extending
   the frozen `Encoding.lean`.
4. **13.4 Z1 mode shape**: one transformer with an emission-mode parameter
   versus two transformers — inherits open decision 12.4's resolution.
5. **13.5 Z5 placement**: the agreement-transfer lemma in `Simulation.lean`
   beside the lockstep gadgets (proposed) versus a `Build/` module.


### 13a. Decisions resolved; epoch structure (user, 2026-10-09)

All five open decisions resolved as proposed, with one rename:
**13.1** zones-with-fullness (interleaving is not built); **13.2** paired
presence/data cells (`SweepCell` precedent); **13.3** a new file, renamed
**`TuringMachine/Codes2Tape.lean`** so the "2" reads as *two-tape*;
**13.4** Z1 inherits 12.4's resolution (a silent/emit transformer pair over
one shared core); **13.5** Z5 lands in `Simulation.lean`.

**The statement phase runs in two tranches, each with its own gate:**

* **A-S1 — the virtual-input half**: Z5 (the agreement transfer,
  `Simulation.lean`, additive), Z1 (`Build/VirtualInput.lean`, new), and
  the Z1 rider (the R1 selected-tape exports, `Embed.lean`, additive via
  the shared-file mechanism). Rationale: harvest-grade risk (the lockstep
  is proved four times over; the rider's facts are proved privately), and
  its consumers are the *near-term* ones — the blocked retrofit R1
  families, the 12.2c dedup, the Loop H3 collapse, the EXPCOM summit.
* **A-S2 — the zone half**: Z2 (`Build/Zone.lean`), Z3
  (`Codes2Tape.lean`), Z4 (the Robustness space annotation). Rationale:
  Z2's carrier predicate is the genuine design risk and deserves an
  undiluted gate; its consumers (Hennie-Stearns, the two-tape universal)
  sit one stage later. The Z4 design-time obligation (does the two-tape
  universal's space bonus yield Ex 4.1?) is discharged in the A-S2 pack.

The canonical Z1 shape (spec-time refinement, recorded before drafting):
the transformer is defined on exactly `1 + M.k` work tapes — the buffer
first, the payload bank after it — and **relocation is not baked in**:
a consumer needing the buffer or bank elsewhere composes with R1. One
shared hosting core; `silent`/`emit` flavors per 12.4; the tag lives in
the transported control state (the `a2_MapState.run q tag` precedent).

### 13b. A-S1 gate close (2026-10-09, after `audits/vhost-infra-findings.md`)

Round-1 **PASS, 0 blockers / 0 majors / 2 minors**; loop summary
`audits/vhost-infra-resolutions.md`. Minor sweep recorded here per the
audit's proposed fix (A-S1-2): the Z1 rider's promised **`ofWords`
transport form is supplied by specialization** of the four delivered
selected-tape projections (instantiate `c := Cfg.ofWords …`); no
separately named specialization is exported now — if a consumer wants the
whole-configuration identity (with its frame, capture, head, and output
parameters spelled out), it is commissioned on need at the 12.2c window.
A-S1-1 (the pack under-counted the definitions: eight with
`MultiTapeTM.AgreeOn`, 23 audited declarations) is acknowledged as a pack
erratum; shipped packs stay verbatim. The audit's four recommended sanity
exports (initial-tag validity + `q₀`-independence, fixed-parameter
transport injectivity, native-head constancy for arbitrary host
configurations, named boundary/seam specializations) are **adopted as
optional permanent lemmas of the A-S1 fill brief** — offered, not
required. The audit's Z5 composition-of-responsibilities reading is
affirmed and binding on retrofit consumers: Z5 equates runs on one
carrier; heterogeneous `clSlot_run`-style sites first transport
(R1 + state renaming), then agree — a public guarded
configuration-transport theorem is a possible later export, not promised.

### 13c. A-S2 round-1 repairs (2026-10-09, after `audits/zone-infra-findings.md`)

The A-S2 statement gate returned **FAIL: 1 blocker, 1 major, 2 minors**;
repairs landed with the round-2 pack:

* **A-S2-1 (blocker) → the inward room premise removed and the wrappers
  split.** The spec had one shared room hypothesis on both shift
  directions; inward shifts *remove* donor cells, so a full donor — the
  exact classical case — was illegal, and the audit's full-chain family
  showed the delivered interface forcing `Ω(T²)` behavior. Repair:
  `zoneShiftInW` carries no room condition; `zoneShiftOutW`'s receiving
  room moved **inside its guard**; the contents wrappers are the
  hypothesis-free `zoneShiftIn`/`zoneShiftOut`; the head steps gain the
  guarded-total `zoneMove`; and the audit's required gate material landed —
  the full-donor regression (`zoneShiftInW_full_donor`) and the cascade
  statements (`zoneCascadeRight` with its represented-word, length, and
  geometric-cost lemmas), whose proofs adopt the audit's schedule analysis
  as the binding route. The rows now realize the **total guarded
  operation, identity branch included**.
* **A-S2-2 (major) → the Z4 one-tape sketch replaced.** The received
  `sweepTM` grows its window unconditionally (the audit's stationary-head
  scanner refutes it as a witness); the statement stands, and the binding
  route is now a **demand-grown** sweep witness with the audit's
  union-of-origin-intervals bound, interleaving factor, and the
  all-`Γ'`-inputs retraction (empty-alphabet and zero-tape cases named).
* **A-S2-5 (note, adopted) → the Ex 4.1 assessment stands as a
  *design-level* verdict, not an implementation discharge**: the stage-1
  universal must specify a space-accounted input interface (native/suffix
  access or an accounted buffer — a materialized input copy costs
  `Ω(|x|)` work cells, absent from the sketched ledger) and a parser with
  its own space ledger; the uniform scheme (Z3), not an arbitrary
  effective scheme, is what a space-accounted canonizer route would use.
* Minors: the pack's definition count corrected (22, not 25; inventory in
  the findings); the module's export list and the guard semantics
  docstrings corrected in place (A-S2-4).

### 13d. Revision: the zone layer at the book's design (draft, 2026-10-10)

**Status: design draft for user review. No Lean change has been made.**

**Process rule (user, 2026-10-10, binding for this revision).** Every Lean change
that results from this revision goes through **both** human approval, as a PR
the user merges, **and** a separate audit gate. Nothing is pushed directly to
the campaign branch. This covers the library generalization (G1), every new
statement phase, and every fill.

#### Why

ZF-A3 (`zone-f1-A3.zip`, held and not integrated) proved infrastructure only:
a geometric counter schedule, counter-driven navigation, a counter built from
the unary level, a window readout, and counter removal, 952 lines in all.
Neither shift machine was proved. A comparison with [AB09] §1.7 traces the
cost to four of our choices, not to the mathematics:

1. **A supplied level with pairwise shifts.** Each pairwise shift starts from
   home, so the machine must count its way to level `i`. In [AB09] the index
   `i₀` is *discovered* by scanning outward, and one sweep does all the work
   between adjacent zones where the head already is.
2. **No markers.** A binary physical tape carries no zone boundaries, which
   forces the binary counter.
3. **Catalog reuse on packed zones.** The generic routines need a blank on
   each side of a word, but packed zones abut, hence the save, blank, call,
   restore cycle around every call.
4. **Exactly two tapes per row,** so the counter shares the scratch tape with
   the level word.

There is also a **gap independent of the controller**. Plan §2.1 specifies
the book's route ("parallel tracks, buffer zones of size `2^i`, amortized
shifts"), but `ZoneContents` holds **one** simulated tape, and both rows
operate on a tape dedicated to it. In a two-tape simulator only one tape can
be zoned, so the present carrier serves only machines with one work tape,
and Hennie–Stearns needs each of `k` tracks to shift independently.

#### Decisions taken (user, 2026-10-10)

- **A rich alphabet, finished by alphabet reduction.** The Hennie–Stearns
  simulator is a two-tape `FinTM Γ` over a large alphabet `Γ`, as in [AB09]
  via Claim 1.5, and the public `Turing.FinTM.alphabet_reduction`
  (`Robustness/AlphabetReduction.lean`) finishes it. That theorem preserves
  the work-tape count (`M'.k = M.k`), costs `3(|Γ|+1) + 2` steps per source
  step, and is stated at the function level (`ComputesFunInTimeVia e f T`
  gives `ComputesFunInTime f (c·(T+1))`). A space form exists
  (`alphabet_reduction_spaceUsed`).
- **Option (b): generalize the library to arbitrary alphabets** rather than
  building a parallel `Γ`-only toolkit. Large-alphabet machines will recur.

#### Components

**G1. Alphabet-generic library (in place).** Change `Bool` to an arbitrary
`{Symbol : Type*}`, with `DecidableEq` where needed, in:

- **`Build/Seam.lean`:** `seamCompTM`, `seamReleaseTM`, and their
  general-configuration theorems (the `_ofCfg` trio and the release pair).
  The canonical `Cfg.ofWords` theorems stay Bool-specific and become
  instances of the general ones.
- **`Build/Embed.lean`:** the transformers, transports and all their
  theorems, including the RB5 state-transport lemma. The capture tape's
  buffer generalizes with `bufferTape`.
- **`FinTM.bufferTape`** (`Simulation.lean`): from `List Bool` to
  `List Symbol`. The definition is unchanged.
- **The R3 sweep rows in `Build/Catalog.lean`:** `transferTM`, `copyTM`,
  `clearTM`, `compareTM`, and their §12.6 framed contracts. Their tables
  never inspect a symbol's value except for equality, so they generalize.
  `incrementTM`, the canonical rows and the Part 2 space rows stay
  Bool-specific.

**Binding constraint:** every existing Bool statement either keeps its
statement verbatim or becomes a definitional instance at `Symbol := Bool`
that its consumers elaborate unchanged. The full downstream replay is the
evidence. This is a change of audited public signatures, so it gets **its
own gate**, before anything consumes it.

**G2. Mapped sweeps (new, alphabet-generic catalog rows).** Per-track
shifting moves one *component* of each cell and leaves the other tracks in
place, which whole-symbol copying cannot do. The rows are `copyMapTM` and
`transferMapTM`, parameterized by `extract : Γ → Δ` and
`merge : Γ → Δ → Γ`: they write `merge (dst cell) (extract src cell)`. Their
framed contracts follow the §12.6 shape (exact time `2|w| + 2`, finish
configuration, no earlier exit, trajectory). At `merge := fun _ s => s` they
are the plain rows. This is the reusable large-alphabet primitive. Its proofs
must share the generalized R3 trace, not copy it (one trace per routine
family, as §12.6 established).

**G3. The multi-track zoned carrier over `Γ`.**

- **Alphabet:** `ZoneSym k := Bool ⊕ ZoneCell k`, where
  `ZoneCell k := Fin k → Option (Option Bool)`. Per track, `none` is the
  buffer symbol `⊠` (an unoccupied slot) and `some v` an occupied slot
  storing the virtual symbol `v`. `Sum.inl` embeds the binary input and
  output (the `e` of `ComputesFunInTimeVia`). It is finite, so it is a
  `Fintype`.
- **Contents:** `Fin k → ZoneContents ℓ`. **The pure layer is reused
  verbatim per track:** the codec is unneeded, but the layout arithmetic,
  `ZoneContents`, `zoneSlot`, `zoneSide`, the pairwise ops and their
  word-preservation lemmas, the head steps, and the cascade with its
  lemmas all carry over.
- **Layout:** one physical cell per virtual slot, holding the whole tuple,
  with the home at cell 0 and **one blank separator cell between consecutive
  zones** on each side (decision 13d.1). Each zone is then a blank-delimited
  nonblank word of length `zoneCapacity i`, so the generalized framed sweeps
  (G1, G2) apply directly, with **no save/restore**. The separators also mark
  zone boundaries, so **no counter** is needed.
- **The home cell** holds all `k` tracks' virtual symbols, so the simulator
  reads and writes the virtual heads in one step.

**G4. Rebalance rows.** For a direction `d` and a track `t` (`t` in finite
control, since `k` is fixed for a given simulated machine), one machine:

1. starts at home and **scans outward** across zones, using the separators,
   to find `i₀ := zoneShiftIndex d (z t)`, the least level whose zone on the
   feeding side is non-empty. This is a new pure definition;
2. realizes the pure cascade at `i₀` on track `t` in a single
   outward-then-inward sweep, with mapped sweeps between adjacent zones and
   the scratch tape as the buffer;
3. leaves every other track and the separators unchanged, and returns home.

Its contract has the same shape as the current rows: exact final tape, live
exit or halt as the consumer needs, time `O(2^{i₀})`, the head within the
level-`(i₀+1)` extent, and scratch space `O(2^{i₀})`.

- **The left-move mirror** `zoneCascadeLeft` is new. It is defined through a
  pure left/right swap of `ZoneContents`, with its lemmas derived by
  symmetry, never copied.
- **The extent:** the carrier lays out `ℓ` levels, and a separate
  **extension row** lays out level `ℓ` (separator plus a half-full fresh
  zone, as in [AB09]'s "first time we encounter it") in `O(2^ℓ)`
  (decision 13d.2).

**G5. The assembly (stage-1 consumer, sketched for fit, not part of this
layer).** One simulated step:

1. read the home tuple;
2. apply M's transition in finite control;
3. write the home tuple;
4. rebalance each track by its head's move: `k` calls of G4, plus extension
   when needed;
5. handle the input and output tapes directly.

The amortization `Σ_i T/2^{i-1} · 2^i = O(T log T)` is the consumer's
mathematics, as before. Then `alphabet_reduction` turns the two-tape
`ZoneSym k` machine into a two-tape binary machine. With the Z3 two-tape
codes and the two-tape universal machine, Thm 3.1 follows at `f log f`.

#### What stays and what goes

- **Kept unchanged:**
  - the pure zone layer in `Build/Zone.lean` (about 820 of its 1,191
    lines): layout arithmetic, carrier, represented word, pairwise ops, head
    steps, the cascade and its lemmas, and the cardinality export. Its
    statements are untouched;
  - the rest of §13: Z1, Z3, Z5;
  - §12.6 and §12.7.

  No other file imports `Zone.lean`.
- **Superseded, to be retired through the G3/G4 gate:**
  - the binary physical realization `zoneTape`, `zoneTape_empty`,
    `zoneTape_blank_outside` and `zoneTape_homeWrite`;
  - the paired-cell codec, unneeded with a rich alphabet;
  - ZF-A2's seven staging-window lemmas;
  - the two current row statements, `exists_zoneShiftInTM` and
    `exists_zoneShiftOutTM`, to be replaced by the G4 rows.
- **ZF-A3's checkpoint** is held, not integrated. Almost all of it (counter
  navigation, counter construction, the binary window readout) becomes
  unnecessary. Integrate nothing from it unless G4's design reuses a piece.

#### Sequencing (each Lean step a PR plus its own gate, per the rule above)

1. **G1:** the generalization as one batch, its statements verified as
   instances, with the full downstream replay; then a **G1 audit gate**.
2. **G2–G4 statements:** the mapped sweeps, the carrier, the rebalance and
   extension rows, the swap mirror and the index function, with an executed
   pre-ship check on concrete instances; then a **statement gate**.
3. **Fill batches** for G2 and G4, then a **fill gate**.
4. The stage-1 Hennie–Stearns assembly, which needs its own statement
   phase.

#### Open decisions (13d.x, for the user)

1. **Zone boundaries:** blank separator cells (proposed; they give the
   catalog delimiters and boundaries at once) or a boundary flag in `Γ`
   (needs predicate-stopping sweeps instead).
2. **The extent:** a laid-out `ℓ` plus an extension row (proposed), or
   rows that extend lazily themselves.
3. **Rebalance totality:** realize the total pure cascade at the scanned
   index for every input (proposed; the A-S2 totality lesson, and the pure
   ops are already total), or a contract conditional on the classical
   fullness invariant.
4. **The track index:** in finite control, one row instance per
   `(direction, track)` (proposed), or on a tape.
5. **The shape of `Γ`:** `Bool ⊕ ZoneCell k` (proposed) or a structure
   with a bit field.
6. **Retiring the superseded declarations:** delete them through the G3/G4
   gate (proposed, since nothing imports them), or deprecate them first.
7. **G1's extent:** whether `Build/Loop.lean`'s public hosts also
   generalize now, or only when a large-alphabet consumer needs them.
   Proposed: only Seam, Embed, `bufferTape` and the R3 sweeps now.

#### Decisions 13d.1–13d.7 taken (user, 2026-10-10): all as proposed

1. Zone boundaries are **blank separator cells**.
2. **A laid-out `ℓ` plus an extension row.**
3. **Total rebalance contracts**: the rows realize the total pure cascade at
   the scanned index for every input.
4. **The track index lives in finite control.**
5. **`ZoneSym k := Bool ⊕ ZoneCell k`.**
6. The superseded declarations are **deleted through the G3/G4 gate**.
7. **G1 covers only Seam, Embed, `bufferTape` and the R3 sweeps.** What this
   means for the sweeps: the *definitions* of `transferTM`, `copyTM`,
   `clearTM` and `compareTM` (the last needs `[DecidableEq Symbol]`), and the
   three framed sweep contracts `transferTM_run_ofCfg`, `copyTM_run_ofCfg`
   and `clearTM_run_ofCfg`, generalize. The canonical `Cfg.ofWords` rows,
   the space rows, the compare contracts, and everything about `incrementTM`
   stay Bool-specific. The generalized definitions instantiate at `Bool`.

The G1 brief is `briefs/s13d-g1-generalize.md`.

