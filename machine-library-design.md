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
  now-option**: primitives (P1-P18), wrappers (W1-W3) and the loop (L) get
  `spaceUsed` theorems in this increment; the emitter combinators (E1-E4′)
  stay lazy until a space consumer appears.
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
