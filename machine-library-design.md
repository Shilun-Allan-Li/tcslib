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
- ~~No deep-embedded language, no verified compiler, no cost-sound surface
  syntax. (Mature end state; not justified by the remaining campaign.)~~
  **Superseded (user, 2026-10-12): a programming layer is commissioned now
  that the low-level layers are complete; see §15.**
- No model change, no Mathlib TM2 dependency, no space bounds (the design
  must not *obstruct* a later space story, but proves nothing about space).
  *(The space part is superseded in practice: §12's R3 rows and every later
  framed contract carry space or head-envelope clauses.)*
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
  byte-identical; no re-audit of closed work. **Lifted for the foundation
  migration (user, 2026-10-12): see §16.** Migrated files are rewritten, with a
  freeze check, a replay and a gate for each change.
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
  old rows, keeping `Primitives.lean` byte-identical (**the byte-identity is
  lifted for the §16 migration, user 2026-10-12**); a backlog item records
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
   `MultiTapeTM.spaceUsedByTape_le_card_Icc`. That lemma now lives in
   `Build/Catalog.lean` (moved from `Build/Zone.lean` by the B4 pre-issue promotion,
   2026-10-12), so Catalog rows and their consumers can cite it.

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
  - the space hierarchy's window radius and clock width (the window route, §16b item 3; the
    budget loop is gone);
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
  (queue empty / counter exhausted), the space hierarchy's windowed runner (halt, window
  exit, clock; the window route, §16b item 3), and `recordStepTM`'s internal dispatch.

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
| **Space hierarchy** `space_universal`, `space_hierarchy`. **Superseded 2026-10-12 by the window route** (§16b item 3): `space_universal` is forward-only (no interval counters, clock or probe/replay), and `space_hierarchy` runs a self-application universal `U₀` in a window on the record rows | **Now:** R8.7 (`recordInitTM`, `recordStepTM`, `recordTestTM`) under a configuration-count clock (`counterLoopTMVia`), with H2 (step block), H3 (windowed runner, three exits) and H5 (native and binary-position input devices). The earlier route (interval counters, budget loop, R8.8 success/cap exits) is dropped |
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

#### Decisions 12.8.1–12.8.6 (2026-10-10)

1. **Rich-alphabet records** (user): multi-track record cells, mark moves as
   G2 mapped sweeps, and Bool counter rows on rich tapes through **one new
   embedding transport**. Finished by `alphabet_reduction` and
   `alphabet_reduction_spaceUsed`. The maintainer's alternative below is
   adopted, and the binary plan above is superseded where they differ.
2. **`Cfg.InWindow` moves** verbatim to `Build/CfgRecord.lean` after C1d
   (default).
3. **`recordStepTM` has a first-return contract with a bound** (default).
4. **`PATH`-hardness stays on the ARM engine**, as audited (default). The
   record-row route remains an option.
5. **Fold and seek live in Catalog, after the G1 gate** (user), sharing the
   R3/G2 trace, one trace per routine family.
6. **EmitIterBody's private input-copy startup is re-derived** from the new
   input rows in 12.2c T2, with the ch7 owner (default).

**Next.** A revised statement draft for the rich design. What can start
now: the embedding transport and the alphabet-generic input and
constant-write rows. The record rows, fold and seek wait for G1 and G2.

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


### 12.8a Statement draft for the rich-alphabet design (2026-10-10)

*Recorded from the S1 agent's draft. Its probe is `audits/evidence/s12-8/S128StatementsProbe.lean.txt`; run by the maintainer against the G1 side-branch tree it gives 0 errors and 12 sorry warnings, one per statement left to the fill. Maintainer decisions O1, O4, O5, O6 and the user's O2, O3, O7 are recorded at the end (§8).*

*Landed as statements on 2026-10-11, branch `integrate/s12-8-statements`: §8 lists the landed names, which supersede the draft's below where they differ, the changes from the draft, the R8.0b target signatures, and the open questions for the statement gate.*

*Draft for the statement phase, 2026-10-10. Base: campaign `19964447`; G1 side branch `s13d/g1`
(`10c2c08d`, PR #15, awaiting its gate).*

**Probe.** `drafts/s12-8-probe.lean`, with its output in `s12-8-probe.out`. It contains the
exact Lean of everything below.

- Against the G1 tree (`tools/leanprobe-g1.sh`): **0 errors, 0 warnings other than 12
  `declaration uses 'sorry'`**, one per proposed statement whose proof is fill work.
- Part A, the transport, is fully proved and also elaborates at the campaign HEAD
  (`tools/leanprobe.sh`, extracted as `s1work/p8/partA-head.lean`): 0 errors, 0 warnings.
- Every exact time below that the probe could execute was checked by `decide` on concrete
  configurations (§12.6 practice). That covers seek, the constant writer, the scan with a
  mark-shift instance, the input copier, and the framed compare at displaced heads.

#### 0. What the rich design needs, and the one gap in the decision as worded

Decision 12.8.1 adopts rich record cells, with the `Bool` counter rows run on rich tapes
through one embedding transport. The transport (R8.0) does what was asked:

- it lifts **any** `Bool` machine along `e : Bool ↪ Γ`;
- the lifted increment and decrement rows run on a dedicated digit tape inside a rich host,
  through G1's generic R1 (Part B of the probe).

**It cannot lift a loop with a rich body.** `counterLoopTM M` requires
`M : MultiTapeTM k Bool S`, so lifting it only serves `Bool` bodies. S1b's BFS round, Savitch's
frame step and every record row have rich bodies. After G1, no loop host exists over a
non-`Bool` alphabet. Decision 13d.7 generalized only Seam, Embed, `bufferTape` and the R3
sweeps. It deferred the loop hosts "only when a large-alphabet consumer needs them", and
§12.8's records are that consumer.

The rich design therefore needs **R8.0b, `counterLoopTMVia`**, a counter loop over any
alphabet:

- the body runs through R1 on the first `k` tapes;
- the counter is a dedicated last tape of digits `e b`, decremented by the lifted
  `decrementTM 1 0`, also through R1.

No new trace is needed. The existing round induction is generalized in place, and the
`Bool` contracts are re-derived from the generic ones: at `e = Function.Embedding.refl Bool`
the two tables agree, so Z5's `MultiTapeTM.runFrom_eq_of_agreeOn` transfers. This is the one
substantive addition to the decision; see §5 for its sequencing.

Two smaller findings:

- **The tag type.** `alphabet_reduction` needs `[Fintype Γ]`, and
  `Γ = RecSym N.State T` is `Fintype` only when `T` is. `Turing.OutSummary`, which is frozen,
  derives only `DecidableEq`. So S1b uses `T := Fin 3` through a code of the summary, as S1a's
  private counting already does, or sanctions a `Fintype OutSummary` export. Open decision O4.
- **Space on foreign inputs.** `alphabet_reduction_spaceUsed` hypothesizes
  `∀ x : List Γ, ∀ t, spaceUsed ≤ S |x|`, that is, over **all** rich inputs, including
  non-`Bool` ones. A lifted `Bool` machine reads a foreign symbol as a blank (`decodeBool`), so
  its space on such inputs is not controlled. Every rich space-bounded simulator (Savitch, the
  space hierarchy) must therefore start with a native **input validation fold**, R8.5d, and stop
  on a foreign symbol.

#### 1. R8.0 — the embedding transport

**Home: a new low file `TuringMachine/SymbolLift.lean`, importing `TuringMachine/Finite`.**
The alternative was CounterLoop's `SymbolTransport` section. The transport uses only
`Configuration`/`Deterministic`/`Finite`, and it has consumers below `Build/`: the G3 carrier
(`ZoneSym := Bool ⊕ …` with `e := Sum.inl`) and the Robustness layer. A low home also keeps it
out of `CounterLoop.lean` while that file's §12.7 fill gate is open.

- **Imports:** `Finite` imports `Deterministic`, which imports `Configuration`. Its up-closure
  contains no `Build/` module, so no cycle is possible.
- **Facade:** the `TuringMachine` facade gains one import.
- `mapWorkSymbols` (CounterLoop) can join it at 12.2c's per-theme split.

**Exact declarations** (verbatim in probe Part A, proved):

```lean
def decodeBool [DecidableEq Γ] (e : Bool ↪ Γ) (γ : Γ) : Option Bool :=
  if γ = e true then some true else if γ = e false then some false else none
@[simp] lemma decodeBool_apply [DecidableEq Γ] (e : Bool ↪ Γ) (b : Bool) : decodeBool e (e b) = some b
def Action.liftSymbols (e : Bool ↪ Γ) (a : Action k Bool State) : Action k Γ State   -- writes/emission mapped by e
def Cfg.liftSymbols (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) : Cfg k Γ State (x.map e)
  -- state, heads unchanged; inputPos := Fin.cast _ c.inputPos; cells and output mapped by e
def MultiTapeTM.liftSymbols [DecidableEq Γ] (M : MultiTapeTM k Bool State) (e : Bool ↪ Γ) :
    MultiTapeTM k Γ State   -- reads through decodeBool e, writes through e
theorem MultiTapeTM.liftSymbols_runFrom [DecidableEq Γ] (M) (e) {x} (c : Cfg k Bool State x) (t : ℕ) :
    (M.liftSymbols e).runFrom (c.liftSymbols e) t = (M.runFrom c t).liftSymbols e
lemma MultiTapeTM.liftSymbols_initCfg : (M.liftSymbols e).initCfg (x.map e) = (M.initCfg x).liftSymbols e
lemma MultiTapeTM.liftSymbols_spaceUsed : (M.liftSymbols e).spaceUsed (c.liftSymbols e) t = M.spaceUsed c t
@[simp] lemma Cfg.liftSymbols_state, Cfg.liftSymbols_workTapePos   -- rfl
lemma Cfg.liftSymbols_inputSymbol : (c.liftSymbols e).inputSymbol = c.inputSymbol.map e
def FinTM.liftSymbols {Γ : Type} [DecidableEq Γ] (M : FinTM Bool) (e : Bool ↪ Γ) : FinTM Γ
theorem FinTM.liftSymbols_computesFunInTimeVia (h : M.ComputesFunInTime f T) :
    (M.liftSymbols e).ComputesFunInTimeVia e f T
```

The one-step lemma `MultiTapeTM.liftSymbols_step`, and `moveInputPos_cast`, are `private` in
the real file.

**Proof notes.**

- `MultiTapeTM.runFrom_comm_of_step` (vendored `Deterministic.lean`) is single-alphabet, so the
  run lemma is a direct induction with `runFrom_succ_eq_step`.
- The one-step lemma decodes the input symbol through
  `Cfg.liftSymbols_inputSymbol`, which needs `Fin.cast` care on the boundary tests.
- The work reads decode by `decodeBool_apply`. Writes commute with `Function.update`.
- The output is `(Option.map e o).toList = o.toList.map e`.

**Corollaries after the G1 merge** (probe Part B, proved). These touch no G1 file:

- `FinTM.bufferTape_map (e) (w) (p) : bufferTape (w.map e) p = (bufferTape w p).map e`. It lives
  in `SymbolLift.lean`, which then imports `Simulation`.
- **Framed lifted rows are one-line consequences.** The probe proves the increment success case:
  `((incrementTM k i).liftSymbols e).runFrom (d.liftSymbols e) (2p+2) = (finish).liftSymbols e`.
  So no per-row lifted statement is proposed; consumers rewrite with
  `liftSymbols_runFrom` and cite the `Bool` row.
- **Dedicated digit tape inside a rich host:**
  `(embedEmitTM ι ((incrementTM 1 0).liftSymbols e)).runFrom (embedEmitCfg ι tapes heads pre
  (d.liftSymbols e)) t = embedEmitCfg ι tapes heads pre ((… .runFrom d t).liftSymbols e)`. The
  host's other tapes (rich records) are R1's frame, so the transport's in-range hypothesis is
  only about the dedicated tape. This is the "dedicated counter tape" discipline of decision
  12.8.1, in usable form.

**Finishing.** Two cases:

- **Time.** A rich decider `D : FinTM Γ` with
  `D.ComputesFunInTimeVia e (fun x => [indicator L x]) T` becomes `FinTM Bool` by
  `FinTM.alphabet_reduction e D f T`, which gives `∃ c M', M'.ComputesFunInTime f (c·(T+1))`.
  The constructor and every `Bool` subroutine enter `D` as `FinTM.liftSymbols` /
  `MultiTapeTM.liftSymbols`, with unchanged time (`liftSymbols_computesFunInTimeVia`) and space
  (`liftSymbols_spaceUsed`).
- **Space.** Use `alphabet_reduction_spaceUsed`, subject to the foreign-input caveat of §0.

##### R8.0b — `counterLoopTMVia`, the counter loop over any alphabet

**Home:** `Build/CounterLoop.lean`. **When:** after the G1 gate (it needs generic
`embedEmitTM`/`embedEmitCfg`) **and** after the §12.7 fill gate. The probe's Part E has the
exact text.

```lean
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1)
def counterLoopTMVia {k} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) : MultiTapeTM (k + 1) Γ (CounterLoopState S)
  -- .body s : (embedEmitTM Fin.castSuccEmb M) redirected by counterLoopRedirect a exit
  -- .dec f  : (embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)) redirected by counterLoopDecExit a
  -- .done / .escape stationary
theorem counterLoopTMVia_run_done   -- counterLoopTM_run_done verbatim with Bool ↦ Γ, plus:
    (hw : ∀ p, -1 ≤ p → p ≤ |w| → ct (cp + p) = bufferTape (w.map e) p)   -- w : List Bool
    -- finish counter cells: `some (e true)`; time `Σ τ + counterOverhead w (d+1)` (unchanged)
theorem counterLoopTMVia_run_escape -- counterLoopTM_run_escape likewise; counter
    -- `bufferTape ((counterWord w (r₀+1)).map e)`
```

- **In-place generalizations (types only, bodies verbatim, G1 rule 2):** `counterLoopCfg` and
  `counterLoopOrbit` become `{Symbol : Type}`. The probe states them as `…Via` copies only to
  avoid a clash.
- `counterLoopTM`, its definition and all `Bool` statements stay byte-identical. Their **proof
  bodies** are swapped to instantiate the generic contracts. The route is
  `runFrom_eq_of_agreeOn` between `counterLoopTM M a exit` and
  `counterLoopTMVia (Function.Embedding.refl Bool) M a exit`. Their dec-phase tables agree
  pointwise (`decodeBool refl γ = some γ`, `Option.map refl = id`, and R1's single-tape action
  equals `decrementTM (k+1) (Fin.last k)`'s), and the other phases agree definitionally.
- **One round induction; net private count down.** `counterLoop_time_le` and the counter
  arithmetic are alphabet-free and reused as they are.

#### 2. The record carrier — `Build/CfgRecord.lean`

**Imports:** `Build/CounterLoop` (for R8.0b) and `TuringMachine/SymbolLift`. **No
`SpaceComplexity` import:** injectivity is stated componentwise rather than through
`ConfigCount.core`, and ConfigGraph converts. **When:** after the G1 merge, since `fieldsTape`
uses generic `bufferTape`. The window predicate lands with the 12.8.2 relocation (after C1d).
The probe's Part F has the exact text.

```lean
inductive RecSym (Q T : Type) where
  | digit (b : Bool)                          -- the `e` of the lift: input, position field, counters
  | cell (content : Option Bool) (mark : Bool)-- one simulated work cell: content track + head-mark track
  | st (q : Option Q)                         -- the state cell
  | tag (τ : T)                               -- the tag cell (emission summary)
deriving DecidableEq
instance recSymFintype (Q T : Type) [Fintype Q] [Fintype T] : Fintype (RecSym Q T) := derive_fintype% _
def RecSym.digitEmb (Q T : Type) : Bool ↪ RecSym Q T
def binDigits (w v : ℕ) : List Bool := (List.range w).map v.testBit       -- little-endian, fixed width
def posWidth (n : ℕ) : ℕ := (Nat.bits (n + 1)).length                      -- 2 ^ posWidth n > n + 1
def cfgRecord {k Q T} {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T) : List (List (RecSym Q T)) :=
  [RecSym.st c.state] ::                                                     -- F0
  ((binDigits (posWidth x.length) c.inputPos.val).map RecSym.digit) ::       -- F1, binary over digits
  (((List.finRange k).map fun i => (List.range (2 * s + 1)).map fun j =>     -- F2 … F(k+1)
      RecSym.cell (c.workTapes i ((j : ℤ) - s)) (decide (c.workTapePos i = (j : ℤ) - s))) ++
  [[RecSym.tag τ]])                                                          -- F(k+2)
def joinFields (fs : List (List Γ)) : List (Option Γ) := List.intercalate [none] (fs.map (List.map some))
def fieldsTape (fs : List (List Γ)) (z : ℤ) : Option Γ := if 0 ≤ z then ((joinFields fs)[z.toNat]?).join else none
def fieldOffset (fs : List (List Γ)) (j : ℕ) : ℕ := ((fs.take j).map (·.length + 1)).sum
theorem fieldsTape_field (fs) (j) (hj : j < fs.length) : ∀ p, -1 ≤ p → p ≤ |fs[j]| →
    fieldsTape fs (fieldOffset fs j + p) = FinTM.bufferTape fs[j] p   -- each field is a framed word
theorem cfgRecord_inj (s) (hc : c.InWindow s) (hd : d.InWindow s) :
    cfgRecord s c τ = cfgRecord s d τ' ↔
      (c.state = d.state ∧ c.inputPos = d.inputPos ∧ c.workTapes = d.workTapes ∧
        c.workTapePos = d.workTapePos) ∧ τ = τ'
theorem cfgRecord_length : (cfgRecord s c τ).length = k + 3   -- proved in the probe
def RecordValid (k n s : ℕ) (Q T) (fs) : Prop :=
  ∃ x (c : Cfg k Bool Q x) τ, x.length = n ∧ c.InWindow s ∧ cfgRecord s c τ = fs
theorem recordValid_iff (n s fs) : RecordValid k n s Q T fs ↔ fs.length = k + 3 ∧ (∃ q, fs[0] = [.st q]) ∧
    (fs[1] is posWidth n digits of value ≤ n + 1) ∧ (each tape field: 2s+1 `.cell`s, exactly one mark) ∧
    (∃ τ, fs[k+2] = [.tag τ])            -- the scan-checkable form, for `recordValidTM`
def RecordAt (d : Cfg K Γ S x) (r : Fin K) (fs) : Prop :=
  ∀ p, -1 ≤ p → p ≤ |joinFields fs| → d.workTapes r (d.workTapePos r + p) = fieldsTape fs p
```

- **Layout discipline.** One blank between fields and between records; no field is empty (F0
  and the tag have one cell, F1 has `posWidth n ≥ 1` cells, each tape field `2s+1` cells). So
  two consecutive blanks mark the end of a table, and every field is a §12.6-delimited word.
  This is the G3 separator discipline, so the generic framed rows apply field by field with no
  save/restore.
- **Space.** A record has `k(2s+1) + posWidth n + 2` cells plus `k + 2` separators, which is
  `O(k·s + log n + 1)`. That is `O(S n)` at `s = c₀·S n` with `S ≥ logSpace`. With
  `alphabet_reduction_spaceUsed`'s `c·(space+1)`, Savitch stays in `SPACE(S²)`.
- **Window predicate.** The probe uses `WindowedP`, a verbatim copy of TQBF's
  `Turing.Cfg.InWindow`. The real file uses `Cfg.InWindow`, relocated here (12.8.2). It **must
  land in the same change** that deletes TQBF's copy: once ConfigGraph imports `CfgRecord` (at
  S1b), TQBF, which is downstream, would otherwise see two definitions.

#### 3. The rows, restated for the rich design

Template (from the §12.8 note), with one change of form:

- **Machines that are single sweeps are defined** and get the §12.6 framed contract: exact
  time, finish configuration, no earlier exit, trajectory.
- **Composite modules are existential**, in the `exists_installCallTM` style
  (`∃ R entry exit C, …`): a first-return time `t ≤ C·(size)`, no earlier exit, an exact finish
  configuration, and the scratch tapes and heads restored.

The constants are indicative; the statement phase fixes them by execution. Tags: **[now]**
can land on the campaign branch before G1 merges. **[G1-merge]** touches no G1 file but uses
G1's generic statements. **[Catalog/G1]** goes in a G1-owned file, after the G1 gate. **[G2]**
is proposed as a G2 statement. **[rec]** is a record row, filled after G2 and the
Catalog/G1 rows.

| Row | Tag | Statement (probe part) | Contract |
|---|---|---|---|
| **R8.0** transport | **[now]** | `MultiTapeTM.liftSymbols_runFrom` and the rest of §1 (A) | proved |
| R8.0 corollaries | [G1-merge] | `FinTM.bufferTape_map`; the R1 composition (B) | proved |
| **R8.0b** `counterLoopTMVia` | [Catalog/G1]+§12.7 gate (CounterLoop) | `counterLoopTMVia_run_done/_escape` (E) | exact, as §12.7 |
| **R8.1** framed compare | [Catalog/G1] | `compareTM_run_ofCfg {Symbol} [DecidableEq Symbol]` (D) | `∃ δ ≤ min |u| |v|`, exact time `2δ+2`, finish `{d with state := done (decide (u = v))}`, no earlier verdict, trajectory `[pos−1, pos+δ]`. Canonical `compareTM_run` re-derived (body swap); the trace generalizes `catalog_compare_trace` |
| **R8.2** `scanTM δf δb a₀` (two-pass transducer) | **[G2]** | `scanTM_run_ofCfg` (D) | exact `2|w|+2`; interval rewritten to `(scanResult δf δb a₀ w).2`, verdict `done (scanResult …).1`; trajectory `[pos−1, pos+|w|]` |
| **R8.3** `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM` | [Catalog/G1] | `skipTM_run_ofCfg` (D); landed with `skipBackTM_run_ofCfg`, `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg` | skip: exact `|w|+1`, head to `pos+|w|+1`. Landed: skip back is skip's inverse, exact `|u|+3` from the next field's first cell to `u`'s; seek end exact `D+1` to `pos+D`, `D = fieldOffset ws |ws|`, `ws ≠ []`; seek start exact `D+4` back to the table start. Nothing written; the seeks stop at two consecutive blanks (table ends) |
| **R8.4** `writeConstTM i w₀` | [G1-merge] (Scan) | `writeConstTM_run_ofCfg` (C) | exact `2|w₀|+2` (executed), old contents arbitrary, head returns |
| R8.4′ `writeAdvTM i w₀` | [G1-merge] (Scan) | landed: `writeAdvTM_run_ofCfg` | writes `w₀` and leaves the head at `pos + |w₀|`, exact `|w₀| + 1`; the advancing round of `expandTM`. Landed cyclic, over `Fin (|w₀|+1)`: it returns to its start state `0`, the counter-loop round shape |
| **R8.5a** `inputCopyTM i` | [G1-merge] (Scan) | `inputCopyTM_run_ofCfg` (C) | from input position 1, exact `2|x|+2` (executed); both heads return in lockstep (no left delimiter needed) |
| **R8.5b** `exists_inputSeekTM` (`Bool`) | **[now]** | (C) | `∃ R … C`; moves the input head to the binary value on a dedicated tape, `t ≤ C·(|w| + pos + p + 1)`; tapes restored |
| **R8.5c** `exists_inputLengthTM` (`Bool`) | statement now; fill after R8.3 (it needs `skipTM` for the width extension) | — | writes `Nat.bits |x|` on a dedicated tape: per input symbol, `incrementTM` with width extension on overflow (`seekEnd` + `writeConst`), `t ≤ C·(|x|+1)` amortized (§12.7 potential) |
| **R8.5d** `inputFoldTM δ a₀` | [G1-merge] (Scan) | — | native scan of the input with a finite fold, verdict `done (x.foldl δ a₀)`, exact `2|x|+2`; the foreign-symbol validator of §0 |
| **R8.5e** `exists_inputCallTM` | [G1-merge] (`Build/InputCall.lean`; needs R8.5a) | — | `inputCopyTM` (at `Bool`, or lifted) + `exists_installCallTM`: a function-level machine on the native input at a clean seam |
| **R8.6** `exists_expandTM pat` (`Bool`); landed as the definition `expandTM` | [G1-merge] (CounterLoop; needs R8.4′) | landed: `expandTM_run_ofCfg` | `counterLoopTM` round = `writeAdvTM pat`; writes `pat` `d` times contiguously; exact `d(|pat|+1) + counterOverhead w (d+1)` |
| **R8.7** record rows | **[rec]** | `exists_recordStepTM`, `exists_recordEqTM` (G); landed with `exists_recordTestTM`; the rest below | first-return form; landed with `yes ≠ no` in each existential |
| **R8.8** `seamCompTM_runFrom_left` (promotion) + `seamCompTM₂_run_ofCfg` | [Catalog/G1] (Seam) | §12.8 note | statement unchanged from the private `seamComp_left` |

**R8.2 replaces fold, map, mark shift and odometer: one row, one trace.** It is proposed **as a
G2 statement**. Its instances:

- **fold:** `δf a γ := (δ a γ, γ)`, `δb` the identity;
- **in-place map** `f`: `δf a γ := (a, f γ)`;
- **head-mark shift right:** `δf prev γ := (mark γ, setMark γ prev)`, the forward delay (the probe
  checks a concrete shift);
- **shift left:** the same delay on the backward pass;
- **record odometer:** a carry transducer;
- **validity checks:** folds.

G2's planned two-tape `copyMapTM`/`transferMapTM` (§13d) are not needed by §12.8: records move
by plain generic `copyTM`. If G2 keeps them, one request: let `merge` take `Option Γ`, so that
blank destinations (scratch) are admitted. **Decision 12.8.5 is honored:** fold, and with it map,
is a Catalog row sharing the R3/G2 trace (`catalog_trace_run`), since G2 lives in Catalog.

**R8.7, the record rows.**

- All are existential modules over `RecSym Q T`.
- **Entry conditions:** the record at tape `0` (`RecordAt`), the scratch tapes `j ≠ 0` blank,
  and the native input `x.map RecSym.digitEmb`.
- **Exit conditions:** heads, input position, scratch and output restored.
- They are built from R8.0/R8.0b, R8.1–R8.5 and R2 seams, with **no private re-trace**.

| Module | Verdict / effect | Composition |
|---|---|---|
| `exists_recordStepTM M upd (hupd : ∀ τ, upd τ none = τ)` (GAP-4, exact text in G) | `yes` and record of `M.step c` with tag `upd τ (M.outputSymbol c)` if `(M.step c).InWindow s`; else `no`, nothing changed; `t ≤ C·(L + |x| + 1)` | read: `scanTM` folds on F0, the tag and the tape fields (scanned symbols and edge flags) via `skipTM`; copy F1 to a dedicated digit tape (`copyTM`), run the lifted `inputSeekTM`, read the input symbol, restore; finite dispatch on `M.tr`; apply: `scanTM` maps (content at the mark, F0, tag) and delay shifts (marks), F1 `±1` by the lifted increment/decrement on the dedicated tape with copy back, clamp from the edge data |
| `exists_recordEqTM` (G) | `yes` iff the two field lists are equal | `k+3` framed compares (R8.1) with `skipTM`s |
| `exists_recordTestTM P` | `P (state, tag)` | two `scanTM` folds |
| `exists_recordValidTM` | `RecordValid` via `recordValid_iff` | `scanTM` folds per field |
| `exists_recordInitTM` | writes `cfgRecord s (initCfg x) τ₀` from `bits (S n)`-style radius digits | `exists_inputLengthTM` (lifted), `exists_expandTM` (lifted) for the window halves, `scanTM` maps, `writeConstTM` |
| `exists_recordNextTM` | next valid record in odometer order, or overflow | `scanTM` carry over all fields + `exists_recordValidTM` filter, under `counterLoopTMVia` |
| `exists_tableAppendTM`, `exists_tableFindTM P` | append at `seekEndTM`; first record satisfying a fold, with an escape if none | `copyTM`, `seekEndTM`, `scanTM`, `counterLoopTMVia` |

#### 4. S1b's machine plan, recomposed (rich)

**Parameters.** `Γ := RecSym N.State (Fin 3)`, with the tag being the output summary through
its `Fin 3` code (O4), and `e := RecSym.digitEmb`. The host is a `FinTM Γ`.

**Tapes:**

- `Tab`, the table;
- `Cur₀` and `Cur₁`, the successor workspaces;
- scratch for the record modules;
- dedicated digit tapes: `Rad` (radius), `Len`, `Cnt` (the outer counter, last tape) and
  `Cnt'` (inner loops);
- the lifted constructor's bank and capture tape.

1. **Validate** with `inputFoldTM`. On a foreign symbol, emit `e false` and halt. This is needed
   only for space, but it is cheap.
2. **Radius.** Run `M_S.liftSymbols e` under generic `embedSilentRetTM` with its output
   captured on `Rad`, then rewind. Time at most `M_S.configBound n (a·S n)`
   (`of_spaceUsed_le` plus `liftSymbols_runFrom`).
3. **Window template.**
   - Lifted `exists_expandTM` with counter `bits (S n)` and pattern `false^{c₀}` writes the left
     half.
   - `writeConstTM [.cell none true]` writes the center.
   - `expandTM` again writes the right half.
   - A `scanTM` map turns the digits into `.cell none false`.

   No multiplication by `c₀` is needed: the pattern length carries it.
4. **Initial record.** `exists_recordInitTM` writes it, plus a one-digit flag field `[digit
   false]` ("unprocessed").
5. **Outer counter.** Copy the template fields `c_N` times onto `Cnt` (`copyTM` + `skipTM`),
   then map every cell to `digit true` (`scanTM`). Its value `2^{c_N·W} − 1` exceeds the record
   count `V` with `c_N := ⌈log₂(3(|Q|+1))⌉ + 4`. Here `W` is the record's cell count, and the
   proof uses `2^{posWidth n} ≥ n+2` and `8^{2s+1} ≥ 3^{2s+1}(2s+1)`.
6. **BFS** with `counterLoopTMVia e Round a (some ex)`. A round:
   - `exists_tableFindTM` finds the first record with flag `false` (escaping to `ex` if none),
     and copies it to `Cur₀` and `Cur₁`;
   - `exists_recordStepTM (N.fixChoice false)` runs on `Cur₀`, and
     `exists_recordStepTM (N.fixChoice true)` on `Cur₁`. The upd is the summary's append table
     on the code;
   - for each `yes`, an inner `counterLoopTMVia` over the table with `exists_recordEqTM`
     decides membership, and `exists_tableAppendTM` appends a new record with flag `false`;
   - the processed record's flag is set (`scanTM` map), the workspaces are cleared
     (`clearTM`), and the table head is rewound (`seekStartTM`).

   Both exits are wired by R8.8.
7. **Verdict.** `exists_tableFindTM (accept)` scans for a record with state `none` and tag
   `accept`. Emit `e true` or `e false`, then halt.
8. **Finish.** `alphabet_reduction` gives a `FinTM Bool` within `c·(T + 1)`.
9. **Correctness** is §12.8's chain, with `cfgRecord_inj` in place of the bit codec:
   - `T := Fin 3` identifies records with `coreSum`s;
   - note-6's bridge applies, the outside-window rejection being `recordStepTM`'s `no`;
   - S1a's four lemmas finish.
10. **Time.**
    - `counterLoop_time_le` gives `V·B + 4V + 2|w| + 2`, with `B = O(V·(L+F) + n)` from the
      nested table loop.
    - Add the startup terms: the constructor bound, `O(S n)`-cost expansions, and
      `O(n log n)` input length.
    - Then `alphabet_reduction`'s `c(T+1)`. The result is at most `K·2^{c'(S n+1)}`.
    - Every budget is evaluated at `n`; no monotonicity of `S` is used.

#### 5. Sequencing — what can be issued before the G1 gate closes

| Item | Lands | Blocked on |
|---|---|---|
| **R8.0 transport** (`SymbolLift.lean`) | **now**. The probe's Part A *is* the proof; a maintainer pre-issue landing or a tiny batch | nothing |
| **R8.5b** `exists_inputSeekTM` (`Bool`; composed of `copyTM`, `timed_rewind`, `counterLoopTM`, `clearTM`, all public at HEAD) | **now**, as a statement phase plus a fill batch | nothing; it lifts to rich hosts by R8.0 |
| R8.5c, R8.5e, R8.6 (`Bool` rows needing Scan or seek) | statements now; fills after the G1 merge (R8.5e, R8.6) or after R8.3 (R8.5c) | G1 merge / R8.3 |
| Statements of **everything else** | **draft now** (this document, probe green on `s13d/g1`) | — |
| R8.0 corollaries, R8.4, R8.5a/d, the `CfgRecord` pure layer | after **G1 merges** (no G1 file edited) | G1 gate; CfgRecord's `InWindow` also on C1d |
| R8.1, R8.3, R8.8 | after the **G1 gate**, in Catalog/Seam | G1 gate; coordinate with G2/G4 (one trace) |
| R8.2 `scanTM` | with **G2** | G1 gate; G2's statement phase adopts it |
| **R8.0b** `counterLoopTMVia` | after the **G1 gate and the §12.7 fill gate** | both gates |
| R8.7 record rows | after the R8.2 fill (G2) and the R8.1/R8.3 fills | G2 fill |
| S1b | after R8.7 | — |

**The sequencing change versus the note:** R8.0b is new, and it sits on two gates (G1, §12.7).
It is the long pole for every rich consumer, since no rich loop exists without it. Some things
can be issued before the G1 gate closes:

- R8.0, which the probe proves;
- R8.5b;
- the statement phase of every other row (the probe is green on `s13d/g1`).

The critical path is then the G1 gate, then R8.0b with R8.2 (G2) and R8.1/R8.3, then R8.7,
then S1b. Two items that the note called "landable now" in fact need the G1 merge, because
their statements use the generic `bufferTape`: `writeConstTM` and the input rows. `expandTM`
needs the advancing writer R8.4′.

#### 6. Per-consumer rows (updated)

| Consumer | Rows |
|---|---|
| **S1b** | §4: R8.0, R8.0b, R8.1–R8.5, R8.6, R8.7 (step, eq, test, init, table rows), R8.8, `alphabet_reduction` |
| **Savitch** | Rich records with binary F1 (`O(S)` cells); frame stack on a rich tape; R8.7 `recordStepTM` (both choice bits) + `recordEqTM` for adjacency; `recordNextTM` + `recordValidTM` for midpoints; R8.3 over frames; `copyTM`/`clearTM` at fixed intervals (note 7); R8.0b loops; R8.8; R8.5d validation; `alphabet_reduction_spaceUsed` |
| `spaceConstructible_*` | `Bool` only: R8.5c, R8.6, `incrementTM` |
| `PATH_NLComplete` (hardness) | ARM engine (12.8.4); no §12.8 row |
| `PATH_mem_NL` | R8.5b, once the nondeterministic host exists (SC-3) |
| Space hierarchy | `Bool` counters lifted by R8.0 on a rich simulator, or unlifted on a `Bool` one; R8.0b (budget loop), R8.8 (success/cap), R8.1 (budget comparison), `clearTM` resets, R8.5d. It simulates a coded machine, so it does not use R8.7 |
| `TQBF_mem_PSPACE` | R8.2 (validation folds, clause evaluation, the trit odometer), R8.5b (input re-reads), R8.3 |
| `NP_subset_PSPACE` | `incrementTM`, `vhostEmitTM`, R8.8 |
| **G3/G4 (§13d)** | R8.3 (zone scanning across separators), R8.2 (per-track maps), R8.0 (Bool counters on `ZoneSym` tapes via `e := Sum.inl`) |

#### 7. Open decisions

- **O1, transport home.** New `TuringMachine/SymbolLift.lean` (recommended), or CounterLoop's
  `SymbolTransport` section (during its open gate).
- **O2, R8.0b route.** In-place proof generalization with the `Bool` contracts re-derived by Z5
  (recommended; one round induction). The alternative is a second host with its own induction,
  which is a duplicated trace.
- **O3, `scanTM` as a G2 statement.** It needs G2's agreement. Separately, the optional
  `merge : Option Γ → Δ → Γ` request for `copyMapTM`.
- **O4, the S1b tag type.** `Fin 3` code (recommended; no frozen-surface change), or a sanctioned
  `Fintype OutSummary` export in ConfigGraph.
- **O5, table seeks.** `seekEndTM` and `seekStartTM` (double-blank stops) in the skip family, or
  as `counterLoopTMVia` loops over `skipTM` (slower, no new row).
- **O6, input validation (R8.5d).** Mandatory for rich space-bounded consumers. Confirm, or
  require every rich row's space bound to be input-independent instead (harder to state).
- **O7, R8.0 now.** Whether the transport lands as a maintainer pre-issue lemma, since the
  probe proof is complete (one file, about 120 lines), or through a statement gate plus fill
  like the other §12 rows.

#### 8. Decisions and the landed statement layer (2026-10-11)

**Decisions.**

- **User:** O2, generalize `counterLoopTM` in place, with the `Bool` contracts
  re-derived by Z5 (R8.0b, a later batch; target signatures below); O3, G2 is
  `scanTM`; O7, the transport lands by PR plus the §12.8 statement gate.
- **Maintainer:** O1, `TuringMachine/SymbolLift.lean` (landed, PR #16); O4, the
  `Fin 3` tag code; O5, dedicated `seekEndTM`/`seekStartTM` rows; O6, input
  validation (R8.5d) is mandatory for rich space-bounded consumers.

**Landed** on `integrate/s12-8-statements` (campaign `5e438f50` with PR #16,
merged at `b28e22ea`). Every machine and carrier is a real definition. Every
contract is sorried with a proof sketch, except the two results already
proved, which keep their proofs: `seamCompTM_runFrom_left`, promoted verbatim,
and `cfgRecord_length`. There are 25 new sorries. Records:
`audits/logs/s12-8-statements-*` and
`audits/evidence/s12-8/S128StatementsPreship.lean.txt`.

| Row | File | Landed declarations | Contract |
|---|---|---|---|
| one-tape actions | `Build/Catalog.lean`, Part 3 | `tapeAction`, `inputMoveAction` | the transition-table vocabulary of every §12.8 machine |
| field layout | Catalog, Part 3 | `joinFields`, `fieldsTape`, `fieldOffset`, `fieldsTape_field` | each field is a §12.6 delimited word in place |
| R8.1 | Catalog, Part 3 | `compareTM_run_ofCfg` | as drafted |
| R8.3 | Catalog, Part 3 | `SeekPhase`; `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM`, each with `_run_ofCfg` | as in the §3 row, with trajectories |
| R8.2, the G2 core | Catalog, Part 3 | `mealyRun`, `scanResult`, `ScanPhase`, `scanTM`, `scanTM_run_ofCfg`; the steps `scanKeep`, `scanFold`, `scanMap`, `scanShift`, `scanCarry`; the identities `scanResult_fold`, `scanResult_map`, `scanResult_shiftRight`, `scanResult_shiftLeft`, `scanResult_carry` | the scan contract as drafted. The instances are pure identities of `scanResult`, so the scan keeps one framed contract |
| R8.4, R8.4′, R8.5a, R8.5d | new `Build/Scan.lean` | `WritePhase`, `writeConstTM`, `writeAdvTM`, `inputCopyTM`, `inputFoldTM`, each with `_run_ofCfg` | constant writer `2|w₀|+2`; advancing writer `|w₀|+1`, cyclic; input copy and input fold `2|x|+2` from input position `1` |
| R8.5e, R8.5b | new `Build/InputCall.lean` | `FinTM.exists_inputCallTM`, `exists_inputSeekTM` | first-return modules |
| R8.6 | `Build/CounterLoop.lean` | `expandTM := counterLoopTM (writeAdvTM k i pat) 0 none`, `expandTM_run_ofCfg` | exact `d(|pat|+1) + counterOverhead w (d+1)`, with `d` copies of `pat` from `pos` |
| R8.7 | new `Build/CfgRecord.lean` | `Cfg.InWindow` (relocated verbatim from `ClassPSPACE/TQBF.lean`, which now imports it); `RecSym`, `recSymFintype`, `RecSym.digitEmb`, `binDigits`, `posWidth`, `cfgRecord`, `cfgRecord_length` (proved), `cfgRecord_inj`, `RecordValid`, `recordValid_iff`, `RecordAt`; `exists_recordStepTM`, `exists_recordEqTM`, `exists_recordTestTM` | first-return modules with distinct verdict anchors |
| R8.8 | `Build/Seam.lean` | `seamCompTM_runFrom_left` (promoted), `seamCompTM₂`, `seamCompTM₂_run_ofCfg` | one continuation per exit, each run unboundedly after the dispatch step |

**Changes from the draft.** Each was executed in the pre-ship probe where
executable.

1. **`yes ≠ no`** is part of every record row's existential. Without it, a
   module with `yes = no` satisfies `exists_recordEqTM` vacuously, and no
   consumer could branch on the verdict.
2. **The field layout lives in Catalog**, not in CfgRecord, because the seek
   rows' contracts are stated over it. CfgRecord imports Catalog and
   `SymbolLift`, not CounterLoop, since R8.0b is not in this step. TQBF's
   import closure gains Catalog, `SymbolLift` and CfgRecord; there is no
   cycle.
3. **`writeAdvTM` is cyclic** over `Fin (|w₀|+1)`. It returns to its start state
   `0`, so it is a counter-loop round as it stands. A seam caller that runs it
   once uses `seamReleaseTM`.
4. **R8.6 is the concrete `expandTM`** with an exact contract, not an
   existential.
5. **The seek family.** Skip back is the inverse of skip (`|u|+3`, from the
   next field's first cell), not its mirror. The seeks' exact times are `D+1`
   and `D+4`, with `D = fieldOffset ws |ws|`. Every row carries the §12.6
   trajectory clause.
6. **No new copier phase type.** The input copier reuses `SweepPhase`, and the
   input fold reuses `ScanPhase`.
7. **The scan instances** are stated as identities of `scanResult` rather than
   as five machine contracts. `scanTM_run_ofCfg` turns each into the
   instance's run.
8. **`Cfg.InWindow`** replaces the probe's `WindowedP`.
9. **One-tape actions.** The §12.8 machines' tables are written with two
   named actions, `tapeAction` and `inputMoveAction`, instead of literal
   `Action` tuples. With literal tuples, the copy-text screen found 17 new
   cross-file pairs: the input copier and the input fold against the R3
   sweeps and the scan. With the helpers there are none. Twelve new same-file
   pairs remain: the four seek tables among themselves, and the two writers.
   These are distinct small machines sharing their phases, not copied
   proofs. The proved R3 tables are unchanged.
10. **Not landed**, being outside this step:
    - `FinTM.bufferTape_map` and the other R8.0 corollaries;
    - R8.5c, `exists_inputLengthTM`;
    - R8.0b;
    - the record rows `exists_recordValidTM`, `exists_recordInitTM`,
      `exists_recordNextTM`, `exists_tableAppendTM` and
      `exists_tableFindTM`. Their statements need S1b's table layout (a
      header, the radius digits, the odometer order) and a template tape
      holding the widths a validity machine compares against.
11. **`MultiTapeTM.liftSymbols_step` is public** in the landed
    `SymbolLift.lean` (PR #16), as the transport's one-step form; §1 above
    made it private. Only `moveInputPos_cast` is private.

**R8.0b target signatures.** These land in a later batch, after this
statement gate. Home `Build/CounterLoop.lean`, which then imports
`SymbolLift`.

```lean
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) := ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩
def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) : MultiTapeTM (k + 1) Γ (CounterLoopState S)
  -- .body s : ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
  -- .dec f  : ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
  --             (counterLoopDecExit a)
  -- .done, .escape : stationary
-- generalized in place (types only, bodies verbatim; existing call sites unchanged):
def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol} (q : Option (CounterLoopState S))
    (c : Cfg k Symbol S x) (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x
def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x
theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol} … -- otherwise verbatim
-- the generic contracts are counterLoopTM_run_done / counterLoopTM_run_escape verbatim, with
--   M, τ, c over Γ; ct : ℤ → Option Γ; counterLoopTM M a exit ↦ counterLoopTMVia e M a exit;
--   hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p,
--     for the counter word w : List Bool;
--   done finish counter: fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q;
--   escape finish counter: fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
--     then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q;
--   all four clauses kept (finish, no earlier exit, counter head range, body heads).
theorem counterLoopTMVia_run_done …
theorem counterLoopTMVia_run_escape …
-- counterLoopTM and its two contracts: statements byte-identical; proofs re-derived at
-- e := Function.Embedding.refl Bool through MultiTapeTM.runFrom_eq_of_agreeOn (Z5), the
-- decrement tables agreeing pointwise (decodeBool refl γ = some γ, Option.map refl = id).
```

**Governance.** Catalog and Seam are G1-owned files, and `scanTM` is the G2
core of the §13d revision. Under the §13d rule this branch therefore lands by a
PR the user merges, with its own statement gate. Nothing is pushed by the
agent.

**Open questions for the statement gate.**

1. **Skip back.** Is the inverse convention right (from the next field's
   start, `|u|+3`), or should it be the mirror of skip (from a word's last
   cell, `|u|+1`)?
2. **The empty table.** `seekEndTM` requires `ws ≠ []`, since an empty table's
   end is its start. Should tables carry a header field, so that every seek
   precondition is uniform?
3. **The cyclic writer.** Is `writeAdvTM`'s anchor-equals-start shape
   acceptable, or should it have a stationary `done` with the loop adapting
   it?
4. **Tape layouts of the record rows.** `exists_recordStepTM` has
   `K + 1` existential tapes with the record on tape `0`; `exists_recordEqTM`
   has 2 tapes; `exists_recordTestTM` has 1. Hosts embed them by R1. Is the
   fixed layout acceptable, or should each row take a tape selection? The
   step row's fill will also import InputCall, for the input seek, which
   enlarges TQBF's import closure again.
5. **The deferred record rows.** Should validity, init, next and the table
   rows enter this gate, or S1b's statement phase, once the table layout is
   fixed?
6. **The facade.** Scan, InputCall and CfgRecord are not wired into the
   `TuringMachine` facade, following the precedent of `SymbolLift`,
   CounterLoop and Zone. Is facade wiring wanted at this gate?
7. **G2's agreement** to `scanTM` as its core, and whether the planned
   `copyMapTM`/`transferMapTM` are still wanted. §12.8 does not need them.

#### 9. Statement gate, round 1: decisions and repairs (2026-10-11)

Round 1 failed with 0 blockers, 1 major, 7 minors and 39 notes
(`audits/s12-8-statements-findings.md`).

**Decisions** (user, the auditor's recommendations, on the open questions
of §8):

1. Skip back stays the **inverse** of skip, at `|u| + 3`.
2. Shared tables get a **fixed nonempty header field**, so seek end always
   has a field to stop after. The table ends are two blank cells before the
   header and two after the last field. From seek end's stopping blank, a
   consumer reaches the table start by skipping back over the last field
   and then seeking start. The deferred table rows are stated with this
   layout.
3. `writeAdvTM` stays **cyclic**. One-shot callers use `seamReleaseTM`.
4. The record rows keep their **fixed local tape layouts**, and hosts embed
   them by R1.
5. The deferred record rows (validity, init, next, table append and find)
   get **their own statement gate** with S1b's concrete layout, before
   S1b's fill uses them. R8.0b and R8.5c are explicit prerequisites.
6. The new modules are **wired into the `TuringMachine` facade** at this
   gate: `SymbolLift`, `Build/CounterLoop`, `Build/Scan`, `Build/InputCall`
   and `Build/CfgRecord`. Nine older files of the topic are also absent
   from the facade; they are recorded as `backlog.md` FAC-1.
7. G2's core is `scanTM`, and `copyMapTM`/`transferMapTM` stay for G3/G4
   (§13d, G2).

**Repairs** (for round 2):

- **Major 1: work-space clauses.** The record rows and the input seek
  bounded time but not the cells they visit, so they were too weak for
  Savitch and logspace consumers. Each now bounds every work head, through
  its verdict or exit, to `C·(size + 1)` cells of its entry position. The
  size is the record's layout length for the step and test rows, `fs`'s
  layout length for the equality row, and `|w|` for the seek. So the space
  does not depend on how far the native input head travels, and repeated
  calls compose. The step row's sketch now names the obligations the auditor
  identified: save and restore the host's input position in binary, and
  clamp the position field at `0` and `|x| + 1`.
- **Minor 2.** The input seek's rewind: `timed_rewind` stops at position
  `1` within `pos + 2` steps, and one left move follows.
- **Minor 3.** The input call's first-return clause splits on whether the
  callee's entry equals its exit. If it does, `seamReleaseTM` supplies a
  fresh entry first.
- **Minors 4, 5 and 6.** `recordValid_iff`'s validator needs width
  templates. A record determines the configuration *core* together with the
  tag. `fieldOffset`'s end formula needs `fs ≠ []`.
- **Minors 7 and 8.** Corrected in the records: the declfreeze log
  miscounted the promotion's citations (3, not 4), and Catalog's ledger
  denominator is now 459.

### 12.8b Record tables, the deferred record rows and R8.5c (statements landed 2026-10-11; design W1 accepted by the user as drafted)

**Why.** §12.8a §8 item 10 deferred five record rows. Their statements need S1b's table layout,
the radius digits, the odometer order, and a template that the validity machine compares
against. §12.8a §9 decision 2 fixed the table convention:
- a nonempty header;
- two blank cells before it, and two after the last field;
- an end-to-start adapter.

Decision 5 sent the deferred rows to their own gate. This increment states that layout, the
five rows, R8.5c, and three small additions the rows and their consumers need.

**Homes.**

| Module | Imports | Contents |
|---|---|---|
| `Build/InputLength.lean` | `Build/CounterLoop` | R8.5c, `exists_inputLengthTM`, alone |
| `Build/RecordTable.lean` | `Build/CfgRecord`, `Build/Seam`, `Build/InputLength` | the layout lemmas, the record template, tables, the adapter, field copy, find and append, and the template, init, validity and next rows |

- R8.5c gets its own small module so that the constructibility files can use it without the
  record layer. 12.2c may fold it into `InputCall`.
- No in-flight file was touched, the imports are acyclic, and TQBF's closure is unchanged.
- Both modules are wired into the `TuringMachine` facade.

**Layout.**

| Declaration | Meaning |
|---|---|
| `tableFields h es` | `h :: es.flatten`, the header then the entries' fields |
| `TableAt d r o h es` | the cells `[-2, L+1]` around origin `o` show `fieldsTape (tableFields h es)` |
| `TableWF m h es` | a nonempty header; every entry has `m` nonempty fields |
| `tableOffset h es j` | where entry `j` starts |
| `recordLength k n s` | `k(2s+1) + posWidth n + k + 4`, the length of every valid record |
| `recordTemplate Q T n s` | the bound field `bits (n+1)` and a window of `2s+1` cells |

- `TableAt` is anchored at an origin, not at the head, because find moves the head and append
  changes the table.
- `TableWF` keeps double blanks at the two ends only, so the seek rows apply.
- `tableOffset` has a closed form, and at `j = |es|` it is the second trailing blank, where
  `seekEndTM` stops.
- `recordTemplate` carries what a candidate record cannot reveal.
- `recordValid_iff_exists_cfg` is the bridge Savitch needs: valid records are exactly the
  records of windowed configurations on the actual input.
- `tableRewindTM` is the adapter, as a real machine: `skipBackTM` then `seekStartTM`,
  R2-seamed, with an exact contract (time `D + 7`).

**Rows.** Every row follows the §12.8 gate conventions:
- an existential module;
- `yes ≠ no` for two-verdict rows;
- a first-return time bound;
- an exact finish that restores every head, the input position, the scratch and the output;
- the work-space clause `∀ u ≤ t, ∀ j, |pos_u j − pos_0 j| ≤ C·(size + 1)`;
- fixed local tape layouts hosted by R1.

| Row | Finish | Time |
|---|---|---|
| `exists_inputLengthTM` | `Nat.bits \|x\|` at the output head | `C(\|x\|+1)` |
| `exists_fieldsCopyTM m` | the source's field layout at the destination head | `C(L+1)` |
| `exists_tableFindTM e m δ a₀ acc` (`0 < m`) | the first entry satisfying the fold predicate, by `findIdx?`: `yes` with the head on it, or `no` with nothing changed | `C(L_tab + \|w\| + 1)` |
| `exists_tableAppendTM m suf` | the table extended by one entry | `C(L_tab + L_e + 1)` |
| `exists_recordTemplateTM` | `recordTemplate \|x\| s` | `C(L_tpl + \|ws\| + \|x\| + 1)` |
| `exists_recordInitTM` | `cfgRecord s (Cfg.init q₀ x) τ₀` | `C(L + \|ws\| + s + \|x\| + 1)` |
| `exists_recordValidTM` | `yes` iff `RecordValid`, nothing changed | `C(L_fs + L_tpl + n + 1)` |
| `exists_recordNextTM` | `first`/`next` over an existential duplicate-free enumeration of exactly the valid records | `C ^ (L + L_tpl + 1)` |

**Decisions** (the design's Q1–Q9, as drafted; the user accepted the draft on 2026-10-11, and the statement gate audits them):

1. **Existential order.** The enumeration order of `recordNext` is existential. Savitch needs
   only a duplicate-free walk of exactly the valid records, and an explicit order would need
   a rank of `Option Q` and `T`, which no consumer reads. The fill uses the carry odometer.
2. **Fuel.** Find takes fuel `|es| < val w` and restores it, because the number of entries is
   on no tape and the only rich loop host needs a counter. A dedicated scanner would be a
   second forward trace, against decision 12.8.5.
3. **R8.5c's route.** It uses a dedicated framed counter whose carry writes `true` on the
   first non-`true` cell, the blank delimiter included. That is the counting phase of
   Catalog's private `f2_counterTM`, framed. The pair goes to the duplication ledger for the
   12.2c window. (§12.8a's "increment with width extension" fails, because `seekEndTM` stops
   one cell past the delimiter.)
4. **Validity time includes `n`.** No public row compares two words by `≤`. The bound
   `v ≤ n+1` uses the `Bool` `counterLoopTM`, lifted onto two digit tapes, at cost `O(n)`.
   Space stays `O(L + L_tpl)`.
5. **The three additions are rows:** `fieldsCopy`, `recordTemplate` and the adapter. There is
   no `tableMem` row; S1b keeps its inner loop.
6. **Homes** as above, with facade wiring at landing.
7. **Input convention.** The rows that read the native input enter at position `1` and
   restore it, as `inputCopyTM` and `inputFoldTM` do. Contrast `recordStepTM`, which saves and
   restores an arbitrary position.
8. **`recordNext`'s exponential bound** is honest: gaps between valid records are exponential,
   and `ComputesInSpace` needs only halting.
9. **The table rows are generic over `Γ`.** Find takes `e : Bool ↪ Γ` for its counter.

**Degenerate cases** (checked in the statements or executed by the probe):
- find at `m = 0` would be false, since `tableFields h [] = tableFields h [[]]`; hence `0 < m`;
- validity needs `|fs| = k + 3`, without which the verdict is not a function of the tape;
- the empty table;
- `T` empty: `first` answers `no` through `match`;
- `k = 0`, `s = 0` and `n = 0`.

**Consumers.**
- **S1b (§12.8a §4):** the template, the counters, the initial table, the round's find,
  copy, step, membership and append, and the verdict find.
- **Savitch:** the template, the start vertex, the midpoint enumeration, adjacency through the
  landed step and equality rows, and frame push and pop. Every frame is `O(S n)`.
- **The constructibility files:** `exists_inputLengthTM`.

**Fill dependencies.**

| Rows | Need |
|---|---|
| find and next | R8.0b |
| adapter, fieldsCopy and append | the Catalog Part-3 fill (delivered, PR #42) |
| template, init and valid | R8.5c and R8.6 |

Evidence: `audits/evidence/wave1-statements/S128bStatementsProbe.lean.txt`, which runs the design's
executed checks against the landed definitions.

### 12.9 Oracle-machine rows (landed 2026-10-11 with epoch B1; `Build/OracleCall.lean`)

**Why.** Every §12 row is plain-machine level, and the oracle model (`TuringMachine/Oracle.lean`)
had no run algebra. The B1 one-query constructions needed three capabilities: (i) a computation
captured onto the **query tape** and submitted; (ii) the four-state **answer tail**; (iii) a way for
plain contracts to drive an oracle machine.

**Rows.**

- In `Oracle.lean`:
  - the run algebra: `step_of_halt`, `runFrom_succ_eq_step'`, `runFrom_add`, `runFrom_of_halt`,
    `runFrom_comm_of_step`, `ComputesInTime.mono`/`output_unique`;
  - the extraction contract: `queryString_length_le_of_blank` (C1-P1) and `queryString_eq_of_cells`;
  - **the transfer bridge** `runFrom_eq_plainEmptyOracle`, after `runFrom_eq_of_forall_ne_qQuery`.
    On a run segment that avoids `qQuery`, the oracle run is the run of the plain table
    `plainEmptyOracle`, so host-parametric plain contracts apply unchanged.
- In `OracleFinite.lean`: the bundled `mono` and `output_unique`.
- In `Build/OracleCall.lean`:
  - `queryString_bufferTape`;
  - `answerAction`, with `step_of_qQuery`, `step_of_answerAction` and `runFrom_two_of_qQuery`;
  - **query capture** `capture_reaches_qQuery`: W1 with its return state taken to be `qQuery`.
    W1 writes on the host's last tape, which is the query tape.
- In `Finite.lean`, the shared guard discharge: `MultiTapeTM.exists_first_halt`.

**Consumers.**

- `mem_POracle_of_polyTimeReducible`, and through it the `SAT`-oracle corollaries and
  `EXP_subset_POracle_EXPCOM` (B5);
- `unaryWitnessLang_mem_NPOracle`, using the tail through `OracleNDTM.fixChoice`;
- `compl_mem_POracle`, using `runFrom_comm_of_step`.

**Not yet here: oracle-call hosting.** This is a plain host simulating an oracle machine that runs
a decider on the extracted query word. It is the library gap behind `POracle_eq_P_of_mem_P`
(deferred) and B5's `NPOracle_EXPCOM_subset_EXP` dispatcher. Its rows need a design note and a
statement gate:

- the headline simulation;
- the private clean call of `ClassNP/EXP.lean` promoted, without the native-input rewind;
- origin tracking for the query tape;
- query extraction with cell `-1` saved;
- the dispatch host.

The draft headline statement, `FinOracleTM.exists_plain_simulation`, is recorded in
`audits/b1-integration.md`. **Designed and stated in §12.10** (2026-10-11).

### 12.10 Oracle-call simulation (statements landed 2026-10-11; design W2, route and homes accepted by the user)

**Why.** §12.9 records the gap, "not yet here: oracle-call hosting". No public row lets a
plain host simulate an oracle machine by running a decider on each extracted query. Two
targets are blocked:
- B1's last, `POracle_eq_P_of_mem_P`;
- B5's summit, `NPOracle_EXPCOM_subset_EXP`, and through it three `EXPCOM` identities and
  `baker_gill_solovay`.

**The decision: one trace, and nondeterminism by choice words.**
- **The deterministic row is the only oracle-call simulation trace.** It is a plain host that
  answers each query by a clean call of the decider.
- **The nondeterministic form is a reduction, not a second simulation:**
  1. the choice-word machine determinizes the oracle NDTM along a word on a work tape;
  2. the deterministic row simulates it;
  3. the plain certificate shell and the proved `exists_proj_decider` enumerate the words.

  The total is `2^O(p)`.
- **Branchwise simulation is rejected.** Branches would consume choice bits through every
  decider run, so the only public determinization would enumerate doubly exponentially many
  words. Avoiding that needs a sparse-guess row, which is a second trace under another name.
- **Virtual input stays at the plain level, after the simulation.** An oracle machine has one
  `qQuery` state, so an oracle-level Z1 would re-prove Z1's lockstep. This forces the
  deterministic row to be stated **from preloaded starts**. The `initCfg` form, the B1b draft
  headline, is a proved corollary.

**Rows.**

| Module | Declaration | Status |
|---|---|---|
| `Build/OracleSim.lean` | `FinTM.prefixWords` (+ `_nil`, `_update`), `Cfg.init_eq_ofWords`, `OracleTM.queryString_runFrom_length_le_of_blank` (W2-0) | proved |
| | **`FinOracleTM.exists_plain_simulation`** (W2-S): from any preloaded start, a plain host reproduces the oracle machine's halting output within `a·(t+1)² + a·Σ_{r<t} [query at r]·τ(\|query_r\|)` | **proved** (fills-4 to fills-6; wave-1 fill gate closed 2026-10-12) |
| | `…_of_monotone`, `…_initCfg`, `FinOracleTM.exists_plain_decider` | proved from W2-S |
| | `FinOracleNDTM.choiceOut`, `choiceOut_eq_true_iff`, `mem_iff_exists_choiceOut` | proved |
| | **`FinOracleNDTM.exists_choiceTM`** (W2-C): the choice-word machine, `≤ 2\|u\| + 2` steps, the same queries, except that at exhaustion in the query state one query may be submitted and its answer discarded (statement gate, minor 4) | **proved** (fills-4) |
| `Build/CertShell.lean` | **`FinTM.exists_certificateShell`** (W2-V): the plain shell deciding `{x ++ u \| \|u\| = C(\|x\|+1)^c ∧ out x u = [true]}` | **proved** (fills-4) |
| | `FinTM.certificateShell_proj` | proved |

- The exact sum, "`T_D` of the query lengths", needs no monotonicity.
- Both instantiations follow from the monotone corollary:
  - polynomial `τ` gives `P^O = P`;
  - exponential `τ`, at a polynomial-time machine, gives `P^EXPCOM ⊆ EXP`, and the summit
    follows through W2-C.

**Fill routes** (binding sketches in the docstrings).
- **W2-S:**
  - the source's tapes, a shadow tape tracking the query head's side of the origin, the Z1
    bank of the clean call `exists_installCallTM`, and a scratch tape;
  - off `qQuery`, the bridge `runFrom_eq_plainEmptyOracle` plus Z5;
  - at `qQuery`, nine R2-seamed phases: bookmark, origin walk, save and blank cell `-1`,
    `copyTM`, the Z1 call at `y = []`, read the verdict, restore, walk back, answer.
  - **As delivered** (fills-6; documented in the target's appendices, and confirmed sound and no
    weaker by the wave-1 fill gate): the host `oracleHost` is **one public phase host**
    (`phaseHostTM`), with a single R2 seam between the public copy and the relocated call
    (`oracleService_run`). Preparation takes at most `natAbs p + 3` steps and restoration
    exactly `natAbs p + 3`, for both signs of the displacement and for zero. A query costs at most
    `2·|p| + 2·|z| + tCall + 13`, redirects included.
- **W2-C:** lockstep by induction on `u`, in the `toOracleNDTM_runWith` shape. An exhausted
  word answers `false`, so an unhalted branch never shows `[true]`.
- **W2-V:** the native-input call R8.5e (`exists_inputCallTM`) at `splitSolve`, then Z1 inside
  the **returning** R1 capture, then a three-state scan. R8.5e is proved at the tip since PR
  #41, so W2-V's route cites no sorried row.

**Decisions.** The user took the first and third (2026-10-11); the rest are as drafted and
go to the statement gate.

1. **The route:** one trace, choice-word enumeration, no branchwise row.
2. **W2-S in preloaded generality,** with the `initCfg` form derived.
3. **W2-V in its own plain module,** `Build/CertShell.lean`, keeping plain consumers off the
   oracle module. Deduplicating the private 2B shell in `ntime_poly_subset_NP` is the shell's
   second customer, a 12.2c item.
4. **W2-C is public here.** It is the core of a relativized Theorem 2.6. It has one named
   customer, against the rule of admission's two.
5. **Time only.** The oracle layer has no space measure. This is flagged against the §12/§13
   space mandate.
6. **Sequencing.** W2-S and W2-C can be filled at once; W2-V's sorried dependency is gone.

**Mirrors, factored** (disclosed at landing; factored in round 2 of the wave-1 statement gate,
2026-10-11, user decision; `audits/wave1-statements-resolutions.md`):
- W2-0 and the private invariants `runFrom_workTapes_invariant` (`Oracle.lean`) and
  `runWith_headBlank` (`OracleNondeterministic.lean`) now all specialize the promoted
  `OracleTM.step_radius`/`OracleTM.runFrom_radius` (`Oracle.lean`).
- `certificateShell_proj` and `Nondeterminism.lean`'s split callers cite
  `append_split_unique` with `certificateLength_strictMono` or
  `expCertificateLength_strictMono` (new module `ChoiceWords.lean`). The private split lemmas
  are deleted.
- `mem_iff_exists_choiceOut` and `Nondeterminism.lean`'s acceptance argument share
  `choiceBudget_le` and `run_take_of_halted` (`ChoiceWords.lean`).

**Consumers** (derived in `audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`):
- `POracle_eq_P_of_mem_P`, which rests on W2-S alone;
- `NPOracle_EXPCOM_subset_EXP`, the summit;
- `baker_gill_solovay`.

Each is `rfl`-identical to its campaign statement, as are the three `EXPCOM` identities the
probe also derives. The probe's deterministic inclusion `POracle_EXPCOM_subset_EXP'` is
probe-local: it is derived from W2-S directly and has no campaign counterpart.

B5's own `exists_EXPCOM_decider` (home `Diagonalization/EXPCOM.lean`) is the summit's
query dispatcher. It is a B5 obligation, not a §12.10 row.

### 12.11 The format-parameterized code simulator (B5a; statements landed 2026-10-11; headline H1 by user decision, H2 in the backlog)

**Why.** Plan §4e decision 2: "B5 builds one format-parameterized uniform interpreter and
discharges ZF-B4, on top of 12.2c item 8's parameterized parse layer".
- `Universal`'s interpreter is hard-wired to one work tape, and is already copied once inside
  `Universal.lean`.
- ZF-B3's layer in `Codes2Tape` is format-specific and contains no interpreter.
- `CodeFormat` has no machine semantics.
- The two target files cannot host a layer for each other: EXPCOM's closure contains neither
  CounterLoop nor VirtualInput, and Codes2Tape is not imported by EXPCOM.

Hence a pre-issue statement module.

**Rows** (`TuringMachine/CodeSimulator.lean`).
- **`Turing.MachineFormat extends CodeFormat`** adds:
  - a work-tape count `k`;
  - a semantics `machine`;
  - two laws: `serialize_eq`, the fixed `k`-record serialization `serializeK`, and
    `skipTable_eq`, the fixed skipper `codeSkipTableK k`.
- **The generic writer layer:** `workReadsK`, `tableBitsK`, `serializeK`, `codeSkipTableK`,
  with proved bridges `tableBitsK_two` and `codeSkipTable2_eq_codeSkipTableK` to the frozen
  two-tape writers.
- **`oneTapeMachineFormat`,** public and proved. Its `decode` is `codeDecode`, and its
  machine is `CodeTM.toFinTM`, both by `rfl`.
- **`MachineFormat.exists_polyCanonizer`** (sorried): one machine computing
  `F.serialize (F.decode α)` in polynomial time. It serves the simulator's front end, the
  `canonizer` field of both uniform schemes, and, off-batch, the TMSAT concrete-scheme
  canonizer.
- **`MachineFormat.exists_uniformSimulator`** (sorried), **H1**. On
  `⟨⟨bits t, α⟩, x⟩` it answers `[true]` iff the decoded machine computes `[true]` on `x`
  within `t` steps, and `[false]` otherwise, within `d·(|α| + |x| + t + 1)^d`. This is
  field-for-field the shape of `UniformMachineCode.simulator_accepts`/`_rejects` and their
  `…2` mirrors.

**Inside H1:** exactly one private interpreter trace, a step block for one simulated
transition of a `k`-tape coded table. It is hosted by §12.7's `counterLoopTM` and Z1's
`vhostEmitTM`, built from the §12 layer, and is not a copy of `universalInterpreter`. Its
properties:
- states independent of the code;
- per-round cost `c·(|β| + 1)`, independent of `t` and `x`;
- input read only through its own head;
- silent;
- proved at the relation level.

Per-round cost independent of `t` and `x` lets stage 1, B6 and the NTIME deterministic core
reuse it under different hosts.

**Instances** (B5a fill):
- **EXPCOM:** `exists_uniformMachineCode` at `oneTapeMachineFormat`.
- **ZF-B4:** `exists_uniformMachineCode2` at a private two-tape format in `Codes2Tape`, whose
  laws are the two bridges.

The two assemblies are a forced mirror pair, as their target structures are. Both are
assembled from H1 in `audits/evidence/wave1-statements/B5aStatementsProbe.lean.txt`, resting only on the
two contracts. **NDCodes is not an instance:** ND codes denote NDTMs and need no interpreter.
A separate small parse-layer rider can handle them.

**Decisions** (from the dossier's D1–D9):
- **D1 (user, 2026-10-11).** A pre-issue statement phase. It is landed by the combined
  statement PR, under one gate.
- **D3 (user, 2026-10-11).** Headline **H1** for now. **H2** is per-code linear,
  `d·(|α|+1)^d·(t+1)` with no `|x|` term. It would serve stage 1 directly, but forces
  in-place suffix input and a suffix-input host that does not exist. H2 is recorded in
  `backlog.md`, and its corollary to H1 is proved in the probe.
- **D2 and D4–D9 are fill-brief matters**, settled when the B5a brief issues. The dossier
  recommends route Z, the generic interpreter at `k = 1`, for EXPCOM, with route W
  (Universal plus a post-processor) as an escalation fallback only. It also recommends moving
  ZF-B3's semantic layer into `CodeSimulator`, generalized, and deleting the dead ZF-B3
  privates.

**Forced writer pairs.** The generic `tableBitsK` reproduces part of the frozen writers'
text. The statement screen gives three such pairs: `oneTapeFormat` at 85%, `codeTable2Bits`
at 67% and `Code2TM.serialize` at 56%. The frozen bodies cannot be redefined, and
`tableBitsK_two` proves the equalities. This is item 8's pre-named residual watch item.

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
family, as §12.6 established). **Decision (user, 2026-10-11; the §12.8
statement gate's Q7).** G2's one-tape core is `scanTM` (§12.8a).
`copyMapTM`/`transferMapTM` stay, for the cross-tape G3/G4 consumers. Their
`merge` takes `Option Γ → Δ → Γ`, so that blank destinations are admitted,
and they share one trace with the scan.

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

**Scope (user, 2026-10-12; §16b item 5).** G2–G4 and the Hennie–Stearns assembly stay in this
campaign. They follow MIG-0b, so that their rows are stated as `Contract`s from the start.

## 14. Hosts first: the rule and the host registry (user, 2026-10-12)

**The rule** (`policy.md` §1, **Hosts come first**; `workflow.md` §2 and §4,
ground rule 4). A *host* is a control structure that drives other routines:
a search or traversal, a recursion or evaluation scheme, an interpreter step
block, a clocked or windowed runner, a dispatcher over a data structure, or an
input device. A host is never built `private` inside the proof that first
needs it. Its public contract is designed and statement-gated first, generic
in what its consumers vary, with time and head-envelope clauses; consumers
cite it, proved modulo while its fill runs. Leaf rows (copy, compare, seek,
arithmetic) are not hosts and keep the §4 rule of admission.

**Why** (the library-reuse assessment of 2026-10-12, four read-only reviews of
the tip `3462c1b4`). The configuration-level calculus (§12–§13: framed sweeps,
`scanTM`, seams, the phase host, R1 embedding, symbol lifts, counter loops,
configuration records) is general: alphabet-generic, with exact time, framing
and head envelopes. Overfitting entered one level up, where every theorem got
its own private host, because the briefs' ground rule 1 made new helpers
private by default:
- NP ⊆ PSPACE's evaluation host (`SpaceComplexity/Inclusions.lean`, about 70
  privates), S1b's BFS and windowed pieces (private by `briefs/ch34-s1b.md`,
  which lists three promotion candidates), B4 membership's assignment walker
  (private by `briefs/ch34-b4-mem.md`), and Cook–Levin's machine-to-formula
  kit (private in `CookLevin/Hardness.lean`);
- four configuration encodings (`coreCode`, `cfgRecord`, B4a's bit rows,
  Cook–Levin's snapshot blocks) and three reachability notions (configuration
  reachability in `ConfigGraph`, `Complexity.GraphReach`, `Kruskal.Reach`),
  none linked to Mathlib's `Digraph`/`SimpleGraph`;
- about 300 `f2_` private copies in `Build/Catalog.lean`, there only to attach
  space bounds to rows exported as existentials (the §2 design rule, *named*
  machines with spec theorems, was not followed by those rows).

**The registry.** Status as of 2026-10-12. Each entry gets a public contract
and a statement gate before a second consumer is briefed.

| # | Host | Status | Named consumers |
|---|---|---|---|
| 0 | **Framed-contract structure**: machine, entry/exit states, precondition, endpoint as a function of the start configuration, time, no-earlier-exit cut, head envelope; sequencing, phase host, R1 embedding, lift and counter loop as structure-to-structure theorems, space derived | to design; **requirements revised by §16** (exact time and cut first-class) | every host below; removes the inline restatements of the delimited-word precondition |
| H1 | **AND/OR evaluator**: a depth-first odometer over a path word of per-depth records with node kinds (AND/OR), a pluggable leaf-verdict module with its own framed contract, short-circuit semantics as a pure function; space = path + leaf + O(1) | the pure core is proved, private, in B4 membership's partial (`b4mValue`, `b4mValue_truth`, `b4mWalk_value`; fills-6); no machine walker was built. **Language first (user, 2026-10-12):** the general evaluator is written as a recursive program of §15's language, not as a machine host, and `TQBF_mem_PSPACE` follows as a program over that core (backlog MIG-22) | `TQBF_mem_PSPACE`; Savitch (midpoint records as digits); NP ⊆ PSPACE (re-derivation); `ClassPSPACE/Games.lean`'s game values; backtracking in the §15 layer |
| H2 | **Step block**: one simulated transition of a `k`-tape coded table, relation-level, with per-round time `B·(\|table\| + 1)` and a head envelope | **the complete step block is proved, private, in B5a H1's continuation (fills-7):** `h1RoundTM k`, one finite machine per `k` whose control does not depend on the state count, with `h1Round_effect` (`0 < T ≤ 50·(\|table\| + 1)`, strict interior, silent, head envelope). Promotion by PR and gate before a second consumer is briefed (backlog F7-1(a)) | H1 (`exists_uniformSimulator`); U-1; B6's self-application universal; C1 (with a choice-bit-indexed table); EXPCOM |
| H3 | **Windowed runner**: run a fixed machine on a windowed record, exiting on window exit, simulated halt, or a configuration-count clock | parts exist privately in S1b's partial (radius phase, records-to-runs bridge, the general-`S` count). S1b stopped (fills-6); B6's window route is the next consumer (adopted, §16b item 3) | S1b; B6 (the window route); Savitch; NL = coNL |
| H4 | **Search over a graph presented by rows** (enumerate, equality, adjacency, start, target), visited table, BFS | not built: S1b's partial has the record graph (records, edges, path lifting, counts) but no search machine, and it stopped there (user, fills-6). **Language first:** the general search is a program of §15's language, and `NSPACE ⊆ DTIME(2^O(S))` is re-derived through it (backlog MIG-19) | `NL ⊆ P`, `NSPACE ⊆ DTIME(2^O(S))`; `PATH ∈ P`; Immerman–Szelepcsényi counting; §15 graph algorithms |
| H5 | **Input devices** behind one interface: native, buffered (Z1, exists), unary marker, binary position (from `exists_inputSeekTM`), computed input | partial | B6 / `space_universal`; U-1 and H2 (backlog); C1 |
| H6 | **Machine-to-formula kit**: closed-form variable indexing, snapshot-keyed local gates, ordered emission by `exists_emitLoopTM`, Tseitin on `Std.Sat.CNF ℕ` correct for every prefix assignment | pattern private in `CookLevin/Hardness.lean`; B4a's codec is non-uniform (its orderings range over index types depending on `n` and `s`, and its public statement is `∀ n s, ∃ …`). **B4a is restated in place over this kit's indexing** (user, 2026-10-12; §16b item 2) | TQBF hardness; Cook–Levin deduplication; later machine-to-formula reductions |

Pure-Lean kits that the hosts' semantics share (not machines, so not hosts,
but designed with them): bounded reachability (`ReachWithin`, the midpoint
lemma, pigeonhole shortening) with bridges from configuration reachability,
`GraphReach` and `Kruskal.Reach` to Mathlib's `Digraph`/`SimpleGraph`.
Consumers: Savitch, TQBF hardness, Immerman–Szelepcsényi, PATH, §15.

**Work in flight when the rule was adopted.** No in-flight brief is withdrawn.
B4 membership and B5a H1 received addenda (`briefs/ch34-b4-mem-addendum-1.md`,
`briefs/b5a-fill-h1-addendum-1.md`): their hosts stay private for now, as
their ownership requires, but are written generic, with self-contained
statements, and listed as promotion candidates. They and S1b's candidates are
promoted, by PR and gate, before any second consumer is briefed.

**Proposed sequencing** (maintainer; for the user): item 0, then H1 (two
consumers ready: TQBF membership and Savitch), then H3/H4 from S1b's delivery,
then H5 with H2's self-application universal for B6, then H6 for TQBF
hardness. Each is a statement phase plus its gate, then a fill.

## 15. The programming layer (commissioned by the user, 2026-10-12)

**Decision.** "Support a programming layer now, now that we've got the really
low level stuff working" (user, 2026-10-12). This supersedes §1's non-goal.

**Why now.** The routine layer (§12), framed contracts (§12.6), counter loops
(§12.7), configuration records and tables (§12.8, §12.8b) and the zone and
virtual-input layer (§13) are proved or being filled. What is missing is any
way to write an algorithm once and get a machine with a proved bound:
- `CounterProg` has unary registers, `inc`/`dec`/`jz`/`out`/`pr` and a one-way
  input, compiled with a `t(2t + 3)` overhead (`CounterProgRun.lean`). It
  serves emitters, but cannot hold a string, an array or a graph;
- `LogProg.ARM` has `O(log n)`-bit registers and yes/no answers, and compiles
  for space only;
- the `PolyTimeComputable` closure algebra is `Bool`-only and existential;
- none of the three is built on `Build/`, and none is registered in
  `ComputationalModels.lean`.

So every machine-level algorithm is a hand-built host (§14), and an
introductory algorithms curriculum (graph search, shortest paths, MST,
sorting, with running times) cannot be written at all. The only
cost-annotated code, the `TimeM` in `Cryptography/RSA.lean`, charges trusted,
unchecked costs.

**Goals.** Write an algorithm once, as a program, and obtain: its semantics;
a step count that is sound by construction (only primitives charge cost);
and a compiled `FinTM` with a proved time bound polynomial in the program's
cost and a space bound linear in its register footprint, feeding `∈ P`,
`PolyTimeComputable` and `SPACE` memberships. The compile theorem is proved
once, from the contracts of the rows and hosts, never by tracing runs.

**Proposed architecture** (maintainer draft; decisions 15.x below):

```
L4  Algorithms     TCSlib/Algorithms/: curriculum algorithms, specs against Mathlib
L3  Programs       a deep-embedded structured language over word registers (+ arrays),
                   big-step semantics with cost, compile theorem to FinTM
L2  Contracts      the framed-contract structure (§14 item 0) and the registered hosts
L1  Routines       Build/: catalog rows, scans, seams, loops, records, tables
L0  Model          MultiTapeTM / FinTM, the run calculus
```

- **L3, programs.** Registers hold words over a finite alphabet, one tape
  each. Instructions are the catalog's word operations (copy, clear, append,
  compare, binary increment, add and `≤`, seek within delimited fields), reads
  of the native input, clean calls of `ComputesFunInTime` machines on
  registers, structured control (sequence, `if` on a register test, a bounded
  `for` over a register's value by counter loops, `while` with fuel), and
  calls of registered hosts. Each instruction is charged by its row's cost in
  the register lengths. Arrays and maps, in a later increment, are record
  tables (§12.8b) with charged access.
- **L4, algorithms.** Written in L3 when machine-faithful costs are the point,
  or as functional code over a cost model that is sound by construction (a
  query or operation monad whose primitives are the only cost source), with
  specifications against Mathlib (`List.Sorted`, `List.Perm`,
  `SimpleGraph.Reachable`, `Digraph`). The comparison-query form also states
  the sorting lower bound. `RSA.lean`'s `TimeM` (colleague-owned) is a
  candidate to relocate or replace here, after a provenance check
  (`backlog.md` §5).
- **Existing layers.** `CounterProg` and `LogProg.ARM` stay; each is bridged to
  L3 or re-based on it (15.4). The new models are registered in
  `ComputationalModels.lean` (policy §1, model registry).

**Open decisions (15.x, for the user).**
1. **Embedding.** (a) A deep embedding: syntax, semantics and a verified
   compiler (cost-sound by construction, the most reusable, the largest); or
   (b) shallow: programs are compositions of §14's contract structures
   (cheaper, but no syntax to reason about or teach from). Maintainer lean:
   (a), compiling into (b).
2. **Register alphabet.** `Bool` only, or any finite alphabet with
   `alphabet_reduction` at the end.
3. **First memory model.** Registers only, or registers plus record-table
   arrays from the start.
4. **`CounterProg` and `LogProg.ARM`.** Bridge, re-base, or leave as they are.
5. **Curriculum cost model.** A comparison-query monad first (sorting), an
   operation monad (graphs), or curriculum algorithms written in L3 directly.
6. **Shape of the compile bound.** Per-instruction affine in the register
   lengths (`C·(cost + n + 1)` overall, with register lengths bounded by the
   cost), or a polynomial.
7. **First consumers** (rule of admission, §4: two named customers). Proposed:
   machine side, the `NL ⊆ P` BFS (or `PATH ∈ P`) and TQBF membership or
   Savitch; curriculum side, merge sort and BFS.

**Prior art examined (2026-10-12; nothing taken yet).** Two formalizations of the
same result, Alman and Vassilevska Williams, *Truly Subquadratic 3SUM and Truly
Subcubic APSP via Triangles in Sparse Lopsided Graphs* (arXiv:2610.06783v1). Both
are word-RAM developments with a structured language, a program logic and a
verified compiler:
- **[AFM26]**: `anthropics/formal-math`, folder `3sum-apsp`, commit
  `e1a4e6508154ea59f030480661590a9fe3018011` (2026-10-05), Apache-2.0, © Anthropic,
  PBC, on Lean and Mathlib v4.33.1. It has 434 Lean files and 102,310 lines. Its parts:
  - the trusted `EndStatement.lean` (139 lines, core Lean only);
  - the language, logic and compiler in `Lang/` (about 9,000 lines) and `Machine/`
    (about 840);
  - the paper's algorithms as verified programs in `Programs/` (about 52,600).
- **[Xuanji26]**: user **xuanji on prove2me** (citation as directed by the user),
  file `3sumapsp_example.lean`, examined locally. It is the top-level assembly of a
  stronger 3SUM bound, `O(n^1.999074)` against [AFM26]'s `O(n^1.9992)`, which comes
  from an Exact Triangle saving of `9261/5000000`. The file builds on [AFM26]'s
  library: 264 of its 265 module docstrings and 125 of its 128 theorem blocks are
  verbatim in [AFM26]. Its 62 project imports, including the module that proves the
  improved saving, are not in the file.

The designs that §14 and §15 may adapt from them are:
- the program logic (`Ends`, `Meets`: postcondition predicates, time "within `T`",
  handed on rather than added up, and spec-only calls);
- the `SameOn` framing with `.keep` lemmas and default-argument tactics;
- tasks, solvers and hosts (`IsHost`);
- run limits built into the semantics;
- the `DetTimeModel` claim algebra;
- the asymptotics calculus with its `growth` tactic.

If adapted, they are cited per `policy.md` §2, *Design adaptation*: [AFM26] as the
origin of the design, and [Xuanji26] for the file the user supplied.

**Sequencing.** 15a: the contract structure (shared with §14). 15b: L3 with
registers only, its semantics, cost and compile theorem (a statement phase and
its gate, then fills). 15c: arrays over record tables. 15d: the curriculum
layer's first increment (cost model, merge sort with `≤ n⌈log₂ n⌉`
comparisons, BFS with an `O(n + m)` operation count). Every Lean step is a PR
plus its own gate.

### 15a. Language first; the spike (user decision and maintainer draft, 2026-10-12)

**Decision (user, 2026-10-12): language first.** The remaining results that are
algorithms are written as programs of the §15 language and compiled. (§16, decision 3,
confirms this for Savitch and `NSPACE ⊆ DTIME(2^O(S))`, which need machine-configuration routines
in the language.) These are
Savitch's recursion, the AND/OR evaluator (H1), graph search (H4), and the
intro-algorithms curriculum. The hosts that are *about machines* stay at machine
level and proceed now: H2 (step block), H3 (windowed runner), H5 (input devices)
and H6 (machine-to-formula). Work in flight is unaffected. S1b's BFS and B4's
walker finish as briefed, and may later be re-derived as programs.

**Architecture (proposed): two stages, as in [AFM26].**

```
program of the language  --stage 1-->  flat word-RAM program  --stage 2-->  FinTM Bool
                        (compiler; constant          (one simulation; polynomial
                         overhead, no tapes)          overhead, the only tapes)
```

- **Stage 1** is pure program reasoning and never mentions tapes. [AFM26]'s
  compiler from its language to its word RAM is about 2,500 lines. Its theorem
  says a run of `c` steps becomes at most `startCost + stepsPerStep·c` RAM steps,
  with constants that depend only on the program text.
- **Stage 2** is the only place tapes appear: one machine simulates a fixed RAM
  program, one instruction at a time. The RAM has about a dozen instruction
  kinds, so the tape-level proof surface is about a dozen instruction contracts
  (§14 item 0), one dispatcher over the program counter (the phase host), and one
  simulation induction.
- **The word RAM is a model in its own right**, registered in
  `ComputationalModels.lean`. In it the curriculum's statements have faithful,
  constant-factor costs. Stage 2 then turns them into P, PSPACE and L
  memberships.

**The language.** It is [AFM26]'s light language:
- integers and numbered local variables, with a flat memory `ℕ → ℤ`;
- expressions: constants, `+`, `−`, `×` and loads; tests `<` and `=`;
- statements: skip, assignment, store, sequence, if, while, and procedure calls,
  with recursion;
- unit costs per constant, variable, operation and load;
- the limits `word`, `space` and `depth` as part of the semantics;
- the logic `Ends`/`Meets` with its rules, frames and tactics.

It adds three things that our classes need:
- `inBit e` and `inLen`, which read the input string *in place*, never copied
  (logspace needs this);
- `emit e`, which appends a bit to the output, for reductions and function
  problems;
- possibly `half e`, cheap on both targets (decision 15a.4).

**The RAM.** It is [AFM26]'s `EndStatement.Instr`:
- `one`, and `add`/`sub`/`mul` modulo `2^W`;
- `load` and `store` (indirect);
- `bltz`, `accept` and `reject`.

It adds `rdIn` (an input bit at a computed position), `len` and `emit`.

**Stage 2's theorem (statement shape, draft).** For a RAM program `P` there are a
`FinTM Bool` machine `M` and a constant `A` (depending on `P` only) with the
following property. Whenever `P` halts on input `x` with word size `W` within `t`
steps, touching `f` distinct cells:
- `M` halts on `x` with the same verdict and output within
  `A·(t + 1)·(f·(W + a) + W² + |x|·log|x| + 1)` steps, where `a` is the width of
  an address;
- `M`'s space is at most `A·(f·(W + a) + W + log|x| + 1)`.

The per-step cost is dominated by one scan of the memory table, a
shift-and-add multiplication, and one input seek.

**What consumers get.**
- **P:** polynomial cost and limits give membership in P.
- **L:** `O(1)` cells, bounded depth and `W = O(log n)` give space `O(log n)`,
  because the input is read in place.
- **Savitch:** depth `O(S)` with `O(1)` locals of `O(S)` bits gives `O(S²)`.
- **TQBF ∈ PSPACE:** depth `O(n)` with `W = O(log n)` gives `O(n log n)`.

Results that need tight *linear* space may still want direct machines.

**Reuse from `Build/`:**
- the phase host, for dispatch on the program counter;
- the framed copy, compare, clear and increment rows;
- the `scanTM` carry family, for binary addition;
- `exists_inputSeekTM` and `exists_inputLengthTM`;
- counter loops, for the rounds of a multiplication;
- R1 embedding and `alphabet_reduction`.

**New rows needed:**
- two-tape addition and subtraction modulo `2^W`;
- multiplication;
- a sign test;
- find-by-key in a memory table, where the key is a word on another tape. The
  record-table find takes a finite-state predicate, so it does not cover this;
- in-place overwrite of a fixed-width field.

**Rough cost** (maintainer estimate, in lines):
- item 0's contract structure: 1,500–2,000;
- stage 2: 6,000–10,000;
- stage 1 with the language, logic and tactics: 5,000–7,000 if ported from
  [AFM26], more if re-implemented.

That is about 15,000–20,000 lines in all, or a few fill waves: about the size of
S1b plus the record tables.

**Open decisions (15a.x, for the user):**
1. **Two stages** (recommended) or a direct compiler from the language to machines.
2. **Port or re-implement [AFM26]'s language, logic and compiler.**
   - *Port:* Apache-2.0, vendored with its header, the upstream commit and a list
     of local modifications (`policy.md` §2, *Vendored code*).
   - *Re-implement:* follow the design, with a *Design adaptation* citation.

   A port is not mechanical. [AFM26] uses Lean v4.33's module system (`module`,
   `public import`, `@[expose] public section`), which our pin v4.25.0 and its
   Mathlib do not use. Porting means removing that layer and repairing
   Mathlib API drift. A port trial on the core (syntax, logic, rules, frames,
   calls, tactics and regions, about 1,900 lines) would settle it.
3. **The RAM's input convention:** read in place by instruction (recommended;
   logspace needs it), or loaded into memory as in [AFM26] (kept as a variant
   for curriculum statements).
4. **Halving** (`half e`) in the language and the RAM: yes or no.

**Next step after 15a.1–15a.3.** Statement drafts of item 0's contract structure
and of stage 2's theorem, as sorried Lean in a scratch worktree, with a pre-ship
elaboration check. Then a statement gate.

### 15b. The port of [AFM26]'s language, logic, routines and compiler (user decision, 2026-10-12)

**Decision (user, 2026-10-12): port it.** The user asked two things first:
- *Does their core serve our purposes?* It serves all of the language-first list, which is
  deterministic. Nondeterminism and randomization are not covered and become one planned
  extension, the coin stream (below).
- *Does their licence allow it?* Yes: Apache-2.0, as tcslib is. Vendored files keep their headers,
  list their changes, and carry the upstream `NOTICE` (repository `NOTICE`).

**The trial port**, read-only, with no build products:
- **Core and routines.** The language core with the merge-sort and power-table closures (18
  modules, 3,681 lines) elaborated at our v4.25.0 pin with 0 errors.
- **Compiler.** The compiler's correctness closure (23 modules, 5,565 lines) also elaborated with
  0 errors.
- **Axioms.** `sort_meets`, `merge_meets`, `powTable_meets`, `time_split`,
  `compileProgram_correct` and `sim` depend only on `[propext, Classical.choice, Quot.sound]`.

**What is vendored.** `TCSlib/Programs/` holds 41 modules (8,548 lines of the trial set) plus
`Compat.lean` and the facades `Programs`, `Programs/Util`, `Programs/WordRAM` and
`Programs/Light`:
- the language, its logic and tactics (`Light/`);
- 14 verified routines (`Light/Lib/`): copy, fill, merge, merge sort, counting sort, radix
  pass, logarithms, powers, modular reduction, square root, odometer and others;
- the compiler to the word RAM (`Light/Compiler/`, with `compileProgram_correct`);
- the word RAM and its run facts (`WordRAM/`);
- general list and index facts (`Util/`).

Their sieve is deferred: it needs `Nat.primesLE`, which our Mathlib pin lacks. The port is the
41-module import closure of the roots named in `scripts/vendor_afm26/README.md`. Two generic
upstream modules outside that closure are **deferred**, not excluded on principle (fidelity
gate, finding 3):
- `Lang/Renumber.lean` (procedure relocation), a candidate for the compiler extensions;
- `Machine/Footprint.lean` (read/write footprints), a candidate input to stage 2's space bound. The files are
generated by `scripts/vendor_afm26/` from upstream plus a recorded list of changes. The
per-file diff is `audits/evidence/programs-vendor/upstream-to-vendored.diff`, and the file map is
`.../file-map.md`.

**Local modifications** (listed in each file's header):
- the Lean module-system syntax removed, as in the cslib precedent;
- namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp`
  to `Light`;
- `EndStatement.lean` trimmed to the word RAM;
- `## References` sections and the standard options added;
- `with_unfolding_none`, absent in v4.25, replaced by `with_reducible`. This is an approximation:
  it keeps reducible definitions unfoldable, and every vendored proof passes with it;
- nine v4.25 proof repairs (`scripts/vendor_afm26/fixes.py`). Seven insert a beta reduction,
  because v4.25 leaves an instantiated motive or invariant unreduced. One rewrites a cast step,
  and one completes a `split_ifs`;
- three renamed lemmas provided in `Compat.lean`, each to be removed at the Mathlib bump that
  provides it.

**Checks.**
- The shipped files, concatenated, elaborate with 0 errors together with all fifteen
  `Complexity` facades and `ComputationalModels`. They declare 2,990 constants, none of which uses
  `sorryAx`, and no axiom.
- A textual screen of the 713 new public names against the other areas finds no clash.
- The style lint reports 0 FAIL and 0 WARN over the 45 files. The vendored files are registered
  as such.
- The user-run replay compiles each module separately, in dependency order
  (`audits/evidence/programs-vendor/replay-order.txt`). Its first run found one import gap.
  `Util/Index` uses a Batteries lemma that upstream reaches through its imports at Mathlib v4.33
  and ours does not; 16 modules failed with it. The fix is an added
  `import Batteries.Data.Nat.Lemmas`, listed in the file's header.
- The concatenated check had masked that gap: its union of all files' imports contained the
  lemma. A per-module closure check now elaborates each of the 46 modules and facades in exactly
  its own import environment (`scripts/vendor_afm26/closurecheck.py`), and all 46 are clean
  (`audits/logs/programs-vendor-closure-check.log`).
- **Replay passed** (user-run, at `155255ed`; `audits/logs/programs-vendor-replay.log`). All 47
  entries are clean, with 0 errors and no `sorry` warnings: the 42 modules, the four facades and
  `ComputationalModels`. The resumed run rebuilt the 17 modules that had failed and skipped the 30
  that were already clean.

**Models registered** in `ComputationalModels.lean`: `Light.Program` and `WordRAM.Instr`.

**Next, each a statement phase with its gate:**
1. the extensions: reading the input in place (`inBit`, `inLen`), `emit`, and the coin stream
   (`coin x`, read for each fixed stream, so that the deterministic logic and compiler carry
   over; nondeterminism and randomization then quantify over the stream);
2. stage 2, the RAM-to-`FinTM` simulation, with the contract structure (§14 item 0);
3. the first consumers.

### 15c. The language and RAM extensions: semantics decided (user, 2026-10-12)

A read-only survey of the vendored layer (2026-10-12) costed the four extensions and their
options. **Decision (user): all four go into one scripted vendored edit set**, with the
survey's recommended semantics:

- **Input read in place.** A statement `x := inBit e` (cost `e.cost + 1`; past the end it reads
  `0`) and a RAM instruction `rdIn`. `inLen` comes first from an argument cell (`|x|` passed as
  argument `i`, which needs no change); a `len` instruction follows only if a consumer needs it.
  Statements rather than expressions, because expression code must be `Straight` and `effect`
  touches only memory. The input string goes into `Limits` (never constructed in the port,
  so nothing breaks), and `Fits` gains `|x| ≤ word`. Stage 2 maps `rdIn` to
  `exists_inputSeekTM`, and `load` stays a table lookup. The rejected options were mapping the
  input into memory at the RAM level, and keeping [AFM26]'s memory-loaded input, which forces
  `lim.space ≥ n` and so rules out logspace.
- **Where the I/O state lives: new indices of `Exec`.** The bits emitted (`o`) and the coins
  consumed (`r`) become indices of the big-step relation, concatenated by `seq` and `while` and
  passed through `call`. `Ends` keeps its type, hiding them under `∃`, so `Meets` and the 14
  routines are untouched; a new `EndsIO` lets a postcondition see them. Six files mention
  `Exec`, against about 124 state literals in 24 files had the state grown instead.
- **Coins read once**, as a consumed `List Bool`. `coin x` sets `x` to either bit at cost `1`,
  consuming it. For a fixed stream `ρ`, `EndsIO ρ` asks for a run whose consumed word is a prefix
  of `ρ`. Nondeterministic acceptance is "some `ρ` of length `T` accepts". Randomized
  acceptance uses `randProb` over `Fin m → Bool`, which needs a determinism lemma for `Exec`
  (not yet stated). **Time bounds are uniform over all streams**, as `NTIME` and `NSPACE`
  require. Read-once coins are also right for NL and BPL, where two-way access to the coins
  would give NP's power, and they compile to both kinds of target. Stage 2 makes each `coin` one
  NDTM choice step; for BPP it produces a deterministic machine that takes the coins as a second
  input.
- **`emit e`** appends a bit to an append-only output, mirroring the machines' per-step output.
  Strictly, only space-bounded output (log-space reductions) needs it; time-bounded functions
  can use memory output. It is included now because it changes the same signatures.
- **`half e`**, as a statement and a RAM arithmetic-shift instruction (not an `Op`: `Op` is
  binary, and its effect lemma needs a range hypothesis). It is `O(W)` in stage 2 and helps
  configurations packed into words.

**Estimated size:** 600–1,000 lines of vendored edits, made by the generator scripts in
`scripts/vendor_afm26/` and listed in each file's header, plus 700–1,150 new lines (the `EndsIO`
rules and tactics, acceptance and probability, the determinism lemma, the new `sim_*` cases).
Every new construct needs a case in each exhaustive definition and induction over `Stmt`,
`Exec` and `Instr`. The hardest parts are carrying the output and the coins through the compiler
simulation, and threading the input through the RAM's run calculus.

**Obstacles the survey found** (backlog PROG-2, PROG-3):
1. **No footprint along a run.** `compileProgram_correct` and `Finished` describe only the final
   memory. Stage 2's space bound needs every intermediate memory inside `[-lowCell, lim.space)`.
   That needs a stronger `Steps`, or the deferred `Footprint.lean` (PROG-1(e)). L and Savitch
   need it, whatever the extensions.
2. **`Ends` is existential.** With a nondeterministic coin rule, specifications that mention I/O
   need `EndsIO` with an explicit stream, and probabilities need the determinism lemma.
3. **`Fits` has no input-length clause** (above).

**Corrections to §15a and §15b, from the survey:**
- the RAM has nine instruction kinds, not "about a dozen";
- the RAM additions are `rdIn` (with `len` later), `emit`, `coin` and `half`;
- the deterministic logic and compiler do not carry over unchanged for coins: the stream
  position is state, carried here by `Exec`'s index;
- [AFM26]'s memory-loaded input is not in force in the port: `SolvedBy` was dropped, `loadWords`
  is unused, and the compile theorem takes any memory satisfying `Input`;
- logspace from `O(1)` cells holds only with input read in place, and only once obstacle 1 is
  closed.

### 15d. Stage 2, PROG-2 and PROG-3: statement drafts (2026-10-12)

A maintainer sub-agent drafted the statements, and the maintainer re-elaborated them: 0 errors;
the only warnings are `sorry`s. They are evidence, not landed files:
`audits/evidence/stage2/Stage2Draft.lean.txt` (723 lines),
`audits/evidence/stage2/ExtensionsDraft.lean.txt` (415 lines), and the notes
`audits/evidence/stage2/NOTES.md`.

**Stage 2 (PROG-4).** It is drafted in two forms:
- `exists_simulation`, deterministic;
- `exists_ndSimulation`: each `coin` is one `FinNDTM` choice step, with bounds uniform over all
  coin streams.

Both are stated over a draft RAM that wraps the vendored one: the nine vendored instructions, plus
`rdIn`, `emit`, `coin` and `half`. With `n = |x|` and `W = W n`, the bounds are
`T = TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)` and
`S = SW n + A·(f·(W + 1) + W + logSpace n + 1)`.
- **The word size** is a hypothesis `WordSizeComputable W TW SW`: some machine outputs
  `Nat.bits (W n)` within `TW n` steps and `SW n` cells. Two bridges supply it: `c·logSpace`,
  from the input-length counter R8.5c, and `c·S`, from `SpaceConstructible`.
- **The corollaries:** DTIME and P, SPACE and LOGSPACE, log-space transducers, Savitch's
  `SPACE(S·S)`, NSPACE and NL.

**PROG-3.** `compileProgram_footprint`: a compiled run stays inside `[-lowCell, lim.space)`, its
reads included. The gap is only at the RAM level, where `Steps` and `Finished` speak of the final
memory.

**PROG-2.** A self-contained mirror of the four new statements and of `Exec`, with the output word
and the consumed coins as indices; `EndsIO` with 15 rules; the determinism lemma; acceptance and
`acceptProb`. `NOTES.md` §5 lists, by file and line, every exhaustive definition and induction
the real edit must extend.

**Corrections to §15a and §15c, read off the code:**
- there is no separate address width, because addresses are words (`WordRAM/Basic.lean`);
- the input seek row is linear (`exists_inputSeekTM`), so the per-step seek term is `n`, not
  `n·log n`;
- the word size's own computation is charged once, as `TW` and `SW`;
- `inBit` needs no input-length clause in `Fits`;
- `Exec.bounded` needs `1 ≤ lim.word`;
- about 32 lines of `Logic`, `Rules` and `Assigns` build or take apart `Ends` witnesses, so "the
  routines are untouched" holds for `Meets` and the library, not for those files.

The nondeterministic form's fill also needs one lemma not present today: a nondeterministic run
agrees with the deterministic one on states whose two transitions coincide. This is the
nondeterministic contract variant that §16 lists as later.

**Estimate** (not measured): about 9,500–15,000 lines beyond MIG-0a, made up of PROG-2
1.4k–2.3k, PROG-3 0.75k–1.35k and stage 2 6.1k–10.5k.

**Open questions for the user**, each with the drafter's recommendation (`NOTES.md` §6):
1. extend the RAM by a wrapper (recommended) or in place, which breaks about 50 configuration
   literals;
2. add `Exec`'s indices in place (option A, recommended, as §15c decided) or as a new relation
   (B);
3. `WordSizeComputable` with its two bridges (recommended), or `SpaceConstructible` directly;
4. `emit` appends "nonzero", and the footprint counts touched cells (both recommended as
   drafted).

**Answered (user, 2026-10-12): all four as recommended.** The RAM is extended by a wrapper, the
`Exec` indices are added in place (option A), the word size is `WordSizeComputable` with its two
bridges, `emit` appends "nonzero", and the footprint counts touched cells. Next: a statement-gate
pack for stage 2, PROG-2 and PROG-3.

## 16. The foundation migration (user decisions, 2026-10-12)

**Why.** The user: "I really think we should invest effort into building code in the right way,
especially in this foundational stage." Seven read-only reviews of the tip `9827cc99` costed a
retroactive migration onto the §14/§15 style:
- the Build foundation and the machine core;
- the machine-level files that stay on Turing machines;
- the algorithm files that could become programs.

Their per-file figures are the restyling backlog (`backlog.md` §2, MIG/RS).

**Decisions (user, 2026-10-12).**
1. **The no-retroactive-migration rules are lifted for this migration**: §8's byte-identity
   bullet and decision 12.2's byte-identical `Primitives.lean`.
2. **Scenario B.** Proof bodies are swapped onto contracts, and in addition the duplicate
   statement families are retired: the R3 canonical `_run` rows, `counterLoopTM` next to
   `counterLoopTMVia`, `EmitIterEmbed`'s embedding, and `Codes2Tape`'s mirror. Their consumers are
   edited. Proof-body swaps under unchanged statements are gated by a freeze check, a replay and
   a fidelity gate. Each retired or changed statement needs a full statement gate.
3. **Savitch and `NSPACE ⊆ DTIME(2^O(S))` are algorithms at heart.** They are written as programs
   of the §15 language and converted by the RAM-to-`FinTM` compiler (stage 2). TM-intrinsic
   results are *not* recast as programs: Cook–Levin, TMSAT, NP ⊆ PSPACE's machine,
   Nondeterminism, the oblivious and hierarchy constructions, and the universal machine.
   **S1b**, in flight at machine level and proving `NSPACE ⊆ DTIME(2^O(S))`, `NL ⊆ P` and Ex 4.3,
   **finishes as briefed** (user, 2026-10-12: "Let it finish"). Once stage 2 and the
   configuration routines exist, it is re-derived as a program and its private host retired,
   with its public statements unchanged (MIG-19).
   *Outcome (fills-6, user: "Stop at this partial"):* S1b landed `NL ⊆ P` and Ex 4.3 proved
   modulo `NSPACE ⊆ DTIME(2^O(S))`, without a search host. MIG-19 is now the route for the
   simulation itself.
4. **Restyling is opportunistic, with a clear backlog** to chip away at: the RS items. Each
   row has its estimate, prerequisites and gate.

**The estimate** (ranges are the reviewers'; ESTIMATED unless marked):

| Bucket | Today | Net change |
|---|---|---|
| Foundation: Build (43,143) and the core (3,887), MEASURED | 47,030 | about −12.5k (−8k to −17.5k). That includes the `f2_` deletion, −7.6k to −8.3k at high confidence, and about 3.6k of new infrastructure |
| Machine-level files staying on TMs: universal, robustness, Nondeterminism, diagonalization and time hierarchy, oracle model, Mathlib bridge | 26.3k | about −4k to −5k: −3.7k from restyling, −1.7k to −2.1k from duplicates found, and +0.5k to 1.5k of extra infrastructure |
| Scenario B's statement retirements | | about −1k more |
| **Total** | **73k** | **about −17k (−12k to −23k)**. About 30k lines of proofs are touched and 4–5k are written new |

**What the contract structure must support** (§14 item 0). The survey revises the "time within
`T`" default taken from [AFM26]'s program logic:
- **exact time, with a no-earlier-exit cut, as first-class fields**, and "within `T`" derived
  from them. About 34 public Build statements carry cuts and about 33 state exact times. Seams,
  counter loops and the zone layer's `2p + 2` compose exact times;
- a **positive-duration field**, for the universal machine's block converse;
- an **endpoint function and a frame predicate**, with tape-indexed `SameOn`-style frames and
  `.keep` lemmas;
- **head envelopes**, both radius and interval forms, with space derived from them;
- the **input tape** (clamped moves, virtual input) and **output appends**;
- **transports**: state renaming (`Sum`/`Sigma`), R1 embedding, symbol lift, alphabet reduction,
  and the lockstep combinators of the robustness layer (decoration, parallel coding, folding);
- **later**, nondeterministic (`runWith`) and oracle-step variants.

From [AFM26] the design takes framing, spec-only calls and default-argument tactics; it does not
take the treatment of time.

**Programs for Savitch and `NSPACE ⊆ DTIME`** (decision 3) need one more planned component:
**machine-configuration routines in the language**. A configuration of a given (nondeterministic)
machine is encoded in memory, and routines enumerate its successors, or test the step relation,
from the machine's finite table. This is narrower than a general machine interpreter, since the
programs are built per machine.

Savitch's `O(S²)` space is **decided (user, 2026-10-12; §16b item 1)**: configurations are held
as single words, with word size `Θ(S)`, so that `O(S)` frames times `O(S)`-bit words fits the
planned bound of cells times word size. Stage 2 therefore takes a computed word size. A
bit-accounted space bound in the compile theorem was declined.

`NSPACE ⊆ DTIME(2^O(S))` is unaffected, since polynomial overhead on `2^O(S)` stays `2^O(S)`.

**Order of work:**
1. Item 0's statement phase and gate, with the requirements above.
2. The certain savings, which need no new infrastructure: named witnesses and the `f2_` deletion
   (MIG-1), then the known duplicates (MIG-2 to MIG-10).
3. Contract instances and tactics, grown against the first migrated file; then rebasing the
   composition-heavy files (MIG-11 to MIG-17).
4. The asymptotics port (MIG-18).
5. The RS items, opportunistically.

**12.2c** (plan §4e) is folded into this migration. Its items are subsumed, moved, kept as MIG-20
and MIG-21, or lapsed, as recorded at the head of the 12.2c tasklist. **MIG-0 and MIG-1 now
precede §13d G2** (user, 2026-10-12), reversing "G2 comes before the Catalog split".

New and unfinished work is written in the new style from the start. Deliveries now in flight
in the old style (record tables, W2-S, B5a canonizer and H1, B4, S1b) join step 3.

### 16a. MIG-0, the contract structure: statement draft and decisions (2026-10-12)

**A sorried statement draft of `Build/Contract.lean` was written and fit-tested** (maintainer,
2026-10-12). It was informed by a read-only inventory of every public contract in `Build/`
(about 150 run statements: 24 exact closed-form times; about 45 cuts that include time `0` and
4 that do not; 25 interval and 12 radius envelopes; no frame predicate anywhere, and frames
written in four idioms).

**The structure** `Turing.Contract M entry exits ι x`:
- a precondition, an **exact time**, an **endpoint function** and per-tape head intervals
  `[lo, hi]`, all functions of a data index `i : ι` (the word or fields the module reads) and the
  start configuration;
- proofs: the run reaches the endpoint at that time; the endpoint is at an exit; **no exit is
  reached earlier, with the cut including time `0`**; and the heads stay in their intervals.
  Exits form a set, so single anchors, verdict pairs, loop exits and halting are one structure;
- derived: "within `B`" (`within`) and the per-tape space bound (`spaceUsedByTape_le`, through
  `spaceUsedByTape_le_card_Icc`); positivity is a predicate.

**Decisions (user, 2026-10-12):**
1. **Universe `Type`** for the alphabet, the states and the data index: the universe of
   `FinTM`, `phaseHostTM` and `counterLoopTMVia`. UNIV-1(a) stays an optional generalization.
2. **Frames are a derived layer**, not a field. The endpoint already states the frame as
   `{ d with … }`. The layer adds `Cfg.SameOutside` (a per-tape footprint), its composition,
   `.keep` lemmas for stored words and blank tapes, and `Contract.Frames`.

**Compositions, as thin wrappers over the existing rows:**
- `trans`: first-exit sequencing on one machine. It is not a general `RecordRun` concatenation
  (MIG-0a gate, round 1, major; see below);
- `seq`: the R2 seam, time `t₁ + 1 + t₂`;
- `inPhase`: one phase inside the phase host, whose redirect targets lie in other phases (a
  sufficient condition: the run must avoid every redirect target up to its endpoint);
- `embed`: the R1 embedding, with unselected tapes framed and output appended;
- `branch`: the two-way seam;
- `ReturnContract` with `release`: for rows that return to their anchor, whose cut starts at
  time `1`, such as the advancing writer. The install and emit calls quantify separate entry and
  exit states that may coincide, so with arbitrary witnesses they split on `entry = exit`
  (corrected at the gate, round 1, minor 5).

**Fit test.** `trans`, `seq`, `inPhase`, `embed` and `embedEmitCfg_select` are proved with no
statement change and no extra hypothesis, on the standard three axioms. So is the instance
`clearTM_contract`, R3 clear repackaged from `clearTM_run_ofCfg`. A second fit test then
proved the rest: the frames layer (the `SameOutside` lemmas are nearly definitional),
`clearTM_contract_frames` (the footprint is exactly where the endpoint writes blanks), `release`
and `branch`. **The whole MIG-0a draft is proved: 843 lines, 0 errors, 0 warnings**
(`audits/evidence/mig0/Contract-draft.lean.txt`).

Further observations from the fit tests:
- **Liveness is a lemma.** A contract's run is live strictly before its time, from the cut and
  `exit_mem`, since a halt would persist to the endpoint. `branch` needs it; promote it as
  `Contract.live`.
- **`branch`'s halting exit is untagged.** If both continuations may halt, a halted endpoint
  does not say which ran. The statement is still correct.
- **A third export:** a pointwise `seamReleaseTM_runFrom_pos`. The release's envelope went
  through `seamReleaseTM_visitedByTapeHead`, because the pointwise lemma is private.
- **Ergonomics:** a `@[simp]` unfolding lemma for `Frames` and `SameOutside`, so that `rw` sees
  a footprint's `if` without a `show`.

The test found two missing public exports, both additive:
- `embedEmitCfg_unselected_tape` and `_pos` (`Build/Embed.lean`). The proof of
  `embedEmitCfg_select` worked around their absence through `embedEmitTM_frame` and a trivial
  machine;
- a right-segment seam lemma (`Build/Seam.lean`), to replace the private `seamComp_right`. It is
  needed for set-valued exits; `seamCompTM_firstReturn_ofCfg` excludes only one target.

**Scope, in two increments:**
- **MIG-0a:** the structure, the derived lemmas, the frames layer, `trans`, `seq`, `inPhase`,
  `embed`, `branch`, `ReturnContract` with `release`, `Contract.live`, and two exports
  (`embedEmitCfg_unselected`, `seamCompTM_runFrom_right`); the pointwise release export is
  deferred to MIG-0b;
- **MIG-0b:** revised after the gate's round 1, below.

**MIG-0a gate, round 1** (2026-10-12: 0 blockers, 1 major, 5 minors; `audits/mig0a-findings.md`,
resolutions `audits/mig0a-resolutions.md`). No proved statement was found false. The major is
about the migration interface: a first-exit `Contract` does not directly replace three kinds of
existing specification, so the direct-replacement claims of MIG-12 and MIG-15 were wrong.
- **Segments.** `CfgRecord`'s `RecordRun` is a fixed-length run that avoids a forbidden verdict
  set; its endpoint need not be a first visit, and `recordRun_trans` concatenates on one machine
  with no dispatch step. The auditor's example: a machine idling at `a` gives a length-2 segment
  from `a` to `a`, which neither a positive `Contract` nor a `ReturnContract` can package.
- **Return-or-escape rounds.** `RecordTable`'s `rt_find_round_entry` and the counter loop's rounds
  end either back at their anchor or at a distinct escape, with positive cuts against both. A
  `Contract` fails its time-zero cut there, and a `ReturnContract` excludes the escape.
- **Joint trajectories.** `CounterLoop`'s `counterSpan` constrains the whole head vector along a
  run. Per-tape intervals cannot express a relation such as "the two heads are equal".

`Contract` stays the first-exit specialization. **MIG-0b** therefore covers, before any
dependent migration:
1. a **segment layer**: fixed-length segments avoiding a forbidden set, with same-machine
   concatenation (the `RecordRun` pattern), and a bridge to `Contract` when the endpoint is a
   first exit;
2. a **round layer**: return-or-escape rounds with positive cuts against the anchor and the
   escape, and the counter loop's composition over them;
3. a **joint-trajectory layer**: a relation on the head vector along the run, derived like
   `Frames` and preserved by the compositions;
4. the **layering split**: a core contract module that `Loop` and `CounterLoop` can import
   (round 1, minor 2), with the adapters and routine instances above it; the two exports move into
   `Build/Embed` and `Build/Seam` then. Round 2's import repair found that the file needs `Seam`,
   `Catalog` and `Mathlib.Tactic.Linarith` (which `CounterLoop` used to supply indirectly), so
   `CounterLoop` is no longer in its closure, but `Loop` still is, through `Catalog`. The core
   part needs only the machine core, apart from `MultiTapeTM.spaceUsedByTape_le_card_Icc`, which
   lives in `Catalog` and moves down first;
5. the pointwise release export `seamReleaseTM_runFrom_pos`;
6. the symbol lift (through `Cfg.decodeSymbols`), state renaming along an embedding
   (`runFrom_mapState_of_agreeOn`), and the alphabet-reduction and robustness-lockstep adapters
   (round 1, note 20);
7. the tactics, and the auditor's suggested sanity lemmas: the zero-time characterization
   (`time = 0 ↔ some entry ∈ exits` on admissible starts) and positivity of the compositions;
8. **the R1 reconstruction lemma** in `Build/Embed`, at the layering split (the wave-1 fill gate's
   major F1, acknowledged by the user): from the selected-bank projections and the unchanged
   ambient frame, equality of an embedded configuration, cited by `OracleSim.oracleBankCfg_eq`,
   `Loop.emCall_exit_fixed`'s local frame and `CodeSimulator.canonEmbedEq`.

MIG-0a's round 2 audits the corrected records and the documentation repairs; no statement or proof
of the file changes.

### 16b. Five route decisions (user, 2026-10-12)

The user took the five open route questions together, each as the maintainer recommended (plan
§4e, decision log, 2026-10-12).

1. **Savitch's space: words of `Θ(S)` bits.** A configuration of the simulated machine is one
   word, so a recursion level holds `O(1)` cells, and depth `O(S)` gives `f = O(S)` cells. Stage
   2's space bound stays cells times word width (§15a), which gives `O(S·(S + log S)) = O(S²)`.
   The alternative, charging each cell for the bits it holds, was declined: every cell still pays
   an `O(log S)`-bit address, so it reaches `O(S²)` only with packing as well. Consequences:
   - **Stage 2 takes a computed word size.** `W` is a function of the input length that the
     compiled machine computes within its space bound: `c·log n` for P and L (from the
     input-length counter, R8.5c) and `c·S(n)` for Savitch (from `S`'s constructibility
     witness).
   - The machine-configuration routines work on packed words, using `half` (PROG-2).
   - With `W = Θ(log n)` and packed configurations, the drafted bound already gives `O(S²)` for
     polynomial `S`. That suffices for `PSPACE = NPSPACE`, but not for `savitch`, which is stated
     for every space-constructible `S`.
2. **B4a is restated in place, over H6.** `exists_adjacency_codec_cnf` becomes public
   definitions of the codec and its three CNFs with closed-form variable indexing, and theorems
   about them in place of the `∃`. Its present formulas index variables through
   `Fintype.equivFin` over types that depend on `n` and `s`, so no machine or program can be
   proved to emit them (Finding A; the `TQBF_PSPACEHard` docstring: "The packaged existential
   supplies no algorithm"). The indexing is designed with H6 (§14), so that Cook–Levin and TQBF
   share one scheme.
   - It changes an audited public statement: a statement gate, then a re-fill. Its only consumer
     is the open `TQBF_PSPACEHard`.
   - Hardness also needs Tseitin on `Std.Sat.CNF ℕ`, correct for every prefix assignment.
   - Whether the `ψᵢ` emitter is a machine (H6) or a program with `emit` is decided with B4
     hardness's design.
   - **Designed (2026-10-12):** `audits/evidence/rd2/RD2-design.md`, with a sorried statement draft,
     `audits/evidence/rd2/RD2Draft.lean.txt`. The draft elaborates with 0 errors and 36 sorries;
     11 of its theorems are proved. It proposes:
     - the H6 kit as `Complexity.FormulaKit`: block variables, a truth-table gate template with
       closed-form wires, ledgers, and emission over `polyTimeComputable_emitIter`;
     - a generic Tseitin-after-prefix lemma, with its instance for `DAGCircuit.toCNF`;
     - `Complexity.ConfigCodec`: a closed-form layout of width `2n + 4 + Q + 3k(2s + 1)`,
       clause lists ordered by `List.range`, the old statement's clauses as 11 theorems, and new
       uniformity theorems.

     About 820 of the old proof's roughly 1,700 lines survive verbatim. Estimate: 2.5k–3.6k lines
     landed; a statement gate, then two fills.
   - **Answered (user, 2026-10-12): all five of the note's recommendations.**
     - `exists_adjacency_codec_cnf` is retired; no proof uses it.
     - The uniformity theorems are part of RD-2, as the fill RD-2b.
     - The ψ matrix is a guarded CNF, so the private Tseitin lemmas of the colleague-owned
       `DAGCircuitSat.lean` are not needed.
     - **The ψ emitter is a machine,** on H6 and the polynomial-time closure algebra.
     - The transition gates are truth-table templates, as in Cook–Levin.

     Next: a statement-gate pack for RD-2.
3. **B6 takes the window route, and `space_universal` is restated forward-only.**
   - **The window route.** `space_hierarchy`'s diagonalizer runs one fixed self-simulating
     universal machine `U₀` inside a window of radius `a·g(n)`, on the configuration-record rows,
     stopped by a configuration-count clock, and flips `U₀`'s verdict. It needs `U₀`'s forward
     direction with a space ledger, the windowed runner H3 (record-table rows 17–18, in flight),
     the step block H2 and the native input device of H5. The sketch's budget loop, head caps,
     interval counters and probe/replay go.
   - **Why:** the chapter-1 interpreter cannot serve (Finding B). It tracks the input head in
     unary on its fourth tape, so its space is `Θ(input travel)`, and the present sketch's
     premise fails whenever `S = o(n)`.
   - **`space_universal` keeps only its forward clause,** as [AB09, Exercise 4.1] states it (p. 93,
     checked 2026-10-12): if `M_α` halts on `x` before using `t` cells of its work tapes, then
     `SU(α, t, x) = M_α(x)`, and `SU` uses at most `C·t` cells. The `[false]` clause goes, and
     with it the interval counters, the core-count clock and the probe/replay. It still needs a
     code-first universal that reads its input through a binary-position device (H5).
   - The sketch drops its stale "space-preserving normal form" obligation: the normal form is
     proved (`Turing.FinTM.one_work_tape_binary_spaceUsed`, `Robustness/SingleTape.lean`), but
     two small steps around it are not, and they stay fill obligations: the space clause of
     the coding step `exists_codeTM`, which is time-only, and a decider's space bound at every
     time (the normal form needs it at every time; `DecidesInSpace` bounds it at the halt).
   - `U₀` and the windowed runner have no statements yet. `U₀` is a public row built from H2 and
     H5, not a private host of this proof. The runner needs three exits (halt, window exit,
     clock), while `counterLoopTMVia` has one, so H3's design must supply them.
   - The shortcut through a space ledger for the time hierarchy's `diagSim` is not taken.
   - The restatement and the re-routed sketches go through a statement gate.
4. **C2 is written as programs with coins.** `PATH ∈ NL`, Immerman–Szelepcsényi and their
   corollaries are programs of the language using read-once `coin` (PROG-2), compiled by stage 2.
   This removes C2's dependency on the nondeterministic `LogProg` extension asked of Hydroxyi
   (plan §2.5; `backlog.md` §2, *ARM extensions*). Stage 2 therefore needs, besides item 1's word
   size:
   - **a nondeterministic form:** each `coin` is one choice step of a `FinNDTM`, with time and
     space bounds uniform over the coin streams (§15c);
   - **a logspace grade:** `O(1)` cells and `W = O(log n)` give space `O(log n)`. This needs the
     input read in place (PROG-2) and the footprint along runs (PROG-3).

   `PATH_NLComplete`'s hardness half needs only the deterministic layer.
5. **§13d G2–G4 stay in the campaign**, after MIG-0b, so that the mapped sweeps, the carrier's
   rows and the rebalance rows are stated as `Contract`s from the start. They share no file with
   stage 2 and can run alongside it. The two open zone rows (`exists_zoneShiftInTM`,
   `exists_zoneShiftOutTM`) retire through the G3/G4 gate, as §13d planned.

**Stage 2's statement** (`backlog.md` PROG-4), drafted together with PROG-2 and PROG-3, therefore
carries a computed word size, deterministic and nondeterministic forms, and a space bound good
enough for L.
