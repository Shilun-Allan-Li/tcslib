# Formalization Plan: Arora-Barak Chapter 7 — Randomized Computation

Continuation of the Arora-Barak campaign (`AroraBarakChapter1Plan.md`, complete and
audited end to end; `AroraBarakChapter2Plan.md`, in progress), on branch
`complexity/arora-barak-ch7`, under the methodology of [`workflow.md`](workflow.md):
audited statement phases with policy-grade proof sketches, a cross-vendor LLM audit
gate before fill, then a fill campaign verified through `scripts/lean_check_tree.sh`
(**`lake build` stays banned on the campaign branch**), `scripts/style_lint.py`
conformance, drift attestations, and a blueprint increment at closure. Audit
artifacts are named `audits/ch7-phase*` / `audits/ch7-epoch*`; briefs `briefs/ch7-*`.

> **Backfill note (2026-10-09).** This plan is written *retroactively*. The Chapter-7
> statement surface landed earlier and was reviewed by the maintainer over three
> rounds (approved at `4a683979`), and some fill had begun before the by-the-book
> campaign artifacts existed. Per the maintainer's instruction ("pause fill, do it by
> the book, backfill without deleting progress"), the plan, module-order file, and the
> **external** cross-vendor statement-audit gate are being produced now, over the
> frozen statement surface, before any further fill. The decision log (§6) records the
> true order of events; no proved Lean is discarded.

## 1. Scope: what Chapter 7 contains

[AB09, ch. 7, pp. 125-146; 2007 web draft, reference pair under
`blueprint/src/references/`.] The mandatory core of this campaign is split into two
model-independent tiers plus a machine instantiation.

* **Tier A — model-free probability and spectral facts** (over symmetric stochastic
  matrices and finite probability, no computational model):
  * **§7.2.2 / Lemma 7.5** — the Schwartz-Zippel lemma (zero-set density of a nonzero
    low-degree multivariate polynomial over a finite field).
  * **Hoeffding/Chernoff core** — the two-sided tail bound for an average of i.i.d.
    `[0,1]` (here Bernoulli) random variables, and the error-reduction corollary
    (the corrected Cor 7.11, see §2).
  * **§7.B expander material** — `λ(G)` (second-largest eigenvalue modulus of a
    symmetric stochastic matrix); the Expander Mixing Lemma (Lemma 7.37, normalized
    form); the expander-walk theorem (Theorem 7.38) and its decomposition lemma
    (Lemma 7.40); the expander Chernoff bound (Theorem 7.41) as a documented
    **statement-only** result (§2).

* **Tier B — randomized complexity classes** (certificate view of Definition 7.4
  over an abstract `VerifierModel`; see §2):
  * **§7.1 / Definition 7.4** — `BPP`, `RP`, `coRP`, `ZPP` (the last in Las Vegas /
    abort form, §2).
  * **Theorem 7.8** — `ZPP = RP ∩ coRP`.
  * **Theorem 7.10** — two-sided error reduction (`BPP` with error `2^{-p(n)}`).
  * **Lemma 7.9** — `BPP_{n^{-c}} = BPP` (amplification from an inverse-polynomial gap).
  * **Theorem 7.17** — `BPP ⊆ P/poly` (Adleman).
  * **Theorem 7.18** — `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` (Sipser-Gács).

* **Machine instantiation** (`Randomized/PolyTimeModel.lean`): the abstract
  `VerifierModel` instantiated by genuine polynomial-time machines via
  `Turing.pairEncode`, discharging the Tier-B closure hypotheses against the
  Chapter-1/2 class `Complexity.P`, and identifying the certificate-style `Σ₂` with
  `Complexity.SigmaP 2`.

**Deferred (not scheduled in the mandatory core):** Tier C — probabilistic Turing
machines proper (the PTM/`PrTM` machine model), `BPL`/`RL`, and `UPATH ∈ RL`
(§7.4-7.5); the full `BPP ⊆ P/poly` via PTM snapshots (we take the
circuit-per-fixed-randomness route); any quantitative strengthening of Theorem 7.41
(Gillman 1998).

## 2. Foundation decisions

* **Randomized classes are certificate-first over an abstract `VerifierModel`**
  (the analogue of Chapter 2's verifier-first `NP`). A `VerifierModel` supplies an
  efficiency predicate `Eff` on `Option Bool`-valued verifiers `M x r` (so that
  zero-error "don't know" verifiers and ordinary Boolean verifiers share one notion)
  and `EffTwoWitness` for the two-witness predicates of `Σ₂`-statements. The
  class theorems (7.8, 7.9, 7.10, 7.17, 7.18) are proved **abstractly**, taking the
  closure properties they need (`ClosedUnderRace`, `ClosedUnderMajority`,
  `ClosedUnderAny`, `ClosedUnderAnswerIs`, `ClosedUnderNot`, `ClosedUnderShiftOr`,
  `VerifierHasCircuits`) as **named hypotheses**; `PolyTimeModel.lean` then
  discharges each against `Complexity.P`. This isolates the probability from the
  machine model and reuses the audited Chapter-1/2 `P`.

* **All class-level probability is carried out in ℚ by exact counting**, not through
  the book's `e^{-2ε²k}` analytic bound. `randProb` is a rational counting ratio over
  `{0,1}^m`; the deviation (vote counts have an exact binomial distribution, and the
  tail is bounded by the elementary `2^K (s(1-s))^{⌊K/2⌋}` max-term estimate plus a
  rational Bernoulli inequality `(1-x)^m (1+mx) ≤ 1`) proves the *same class
  statements* with no analytic prerequisites. **This is the deviation most in need of
  auditor scrutiny** (seeded question CH7-Q1): the claim is fidelity of the proved
  statements, not of the book's intermediate bound.

* **Certificate / randomness length schedules are explicit effective formulas**
  `polyLen a k n = a·(n+1)^k` (never an abstract bounded function), exactly as
  Chapter 2 repaired `NP` (the Argument-A lesson: length arithmetic over an abstract
  bound can smuggle undecidable information). All amplification parameters are
  concrete schedules in this form.

* **`ZPP` is stated in Las Vegas / abort form**, not via expected running time: a
  zero-error verifier outputs `some b` (committing to answer `b`) or `none` (abort),
  with the abort probability bounded. The equivalence to the expected-time
  formulation is standard but outside the abstract model; recorded as seeded
  question CH7-Q2.

* **Theorem 7.41 (expander Chernoff) ships as a documented statement-only stub.**
  [AB09] omits its proof ("whose proof we omit"); the quantitative proof follows
  Gillman 1998 and is out of scope. The statement carries the **sign-corrected**
  bound (seeded question CH7-Q3) and full documentation. It is the only intentional
  long-term `sorry` in the mandatory core.

* **The error-reduction corollary carries the Cor 7.11 erratum correction.** The
  book's stated constant is off; the corrected two-sided bound is used and documented
  in `ErrorReduction.lean`.

* **Circuits for `BPP ⊆ P/poly` come from the fixed-randomness route.**
  `VerifierHasCircuits M p` says each fixing of the random string turns the verifier
  into a polynomial-size circuit family; for the polynomial-time instantiation this is
  dischargeable from `Complexity.P_subset_PPoly` (the tableau construction) with the
  random bits hard-wired. No PTM-snapshot machinery is introduced.

* **λ(G) is developed over `EuclideanSpace`/`WithLp` via the operator norm** on the
  complement of the all-ones vector; the mixing and walk theorems are proved by
  orthogonal decomposition and an L²-contraction estimate, reusing Mathlib's inner
  product and `Finset.inner_mul_le_norm_mul_norm` family rather than a bespoke
  spectral theory.

## 3. Architecture and module layout

Two directories under `TCSlib/Complexity/` (namespace `Randomized` for the classes;
`Randomized`/expander defs model-free), with facades. The Chapter-1/2 and upstream
Boolean-analysis/circuit surfaces remain frozen; any addition to them is flagged.

| Module | Contents |
|---|---|
| `Complexity/Expanders/Basic.lean` | `λ(G)` foundations: `toCLM`/inner-product helpers, `norm_toCLM_apply_le` (L² contraction, Ex. 10), `norm_mulVec_le_lambda`, `lambda_nonneg`, `lambda_le_one` |
| `Complexity/Expanders/Mixing.lean` | Expander Mixing Lemma (Lemma 7.37, normalized), by orthogonal decomposition |
| `Complexity/Expanders/Walks.lean` | `opNorm_le_one`, `exists_decomposition` (Lemma 7.40, incl. `λ = 0`), `walk_filter_sum`, the expander-walk theorem (Theorem 7.38) |
| `Complexity/Expanders/Chernoff.lean` | Theorem 7.41 (expander Chernoff), **statement-only**, sign-corrected |
| `Complexity/Randomized/SchwartzZippel.lean` | Lemma 7.5, over Mathlib's `MvPolynomial.schwartz_zippel_totalDegree` |
| `Complexity/Randomized/ErrorReduction.lean` | i.i.d. Bernoulli Hoeffding bounds (corrected Cor 7.11 + the Thm 7.10 calculation), from Mathlib sub-Gaussian machinery |
| `Complexity/Randomized/Classes.lean` | `VerifierModel`, `polyLen`, the class definitions and constructions, the `randProb` counting toolkit, `InBPP.compl`, Theorems 7.8/7.10, Lemma 7.9 |
| `Complexity/Randomized/Adleman.lean` | `VerifierHasCircuits`, Theorem 7.17 (`adleman`) |
| `Complexity/Randomized/SipserGacs.lean` | XOR-shift helpers, balanced shift-count arithmetic, Theorem 7.18 |
| `Complexity/Randomized/PolyTimeModel.lean` | `polyTimeModel`, the closure discharges, `inSigma2_polyTimeModel_iff`, the poly-time `sipser_gacs`/`adleman`/`zpp` corollaries |

## 4. Phasing

The chapter landed as a **single statement phase** covering all three parts of §1
(the slices are tightly coupled through the abstract `VerifierModel`, so there was no
natural intermediate freeze), followed by fill. Within the `workflow.md` pipeline:

1. **Phase 1 — the full statement surface** (this gate): all Tier-A and Tier-B
   definitions and statements plus the `PolyTimeModel` instantiation, every proof a
   `sorry` under a policy-grade sketch. This is what the external audit (§3 of the
   workflow) reviews. Because fill began before the gate was formalized, the pack
   attests which targets are already proved (their *statements* are frozen and under
   audit; their tactic proofs are out of scope for the statement gate and will be
   re-audited at fill closure).

2. **Fill campaign** — ordered by risk retirement:
   * (E1) Tier A, which is independent of the model: `Basic`/`Mixing`/`Walks`,
     `SchwartzZippel`, `ErrorReduction`. **Landed.**
   * (E2) Tier B abstract class theorems over the `VerifierModel`: `Classes`,
     `Adleman`, `SipserGacs`, with the `randProb` ℚ-counting toolkit. **Landed.**
   * (E3) the `PolyTimeModel` discharges — the machine-level summit (see §5).
     **In progress:** `closedUnderAnswerIs`, `closedUnderNot`,
     `inSigma2_polyTimeModel_iff`, and `closedUnderRace` are proved; the remaining
     discharges are `takePrefixByLen`/`dropPrefixByLen` (a counter-program slicing
     primitive), `closedUnderMajority`/`closedUnderAny`/`closedUnderShiftOr` (a
     polynomial loop of `P`-decider queries), and `verifierHasCircuits` (the
     fixed-randomness circuit construction).
   * (E4) closure: zero-sorry sweep (modulo the intentional Theorem 7.41 stub), drift
     attestation, final fill-audit pack, blueprint increment.

## 5. Risks and honest effort assessment

* **The `PolyTimeModel` discharges are the summit.** Three of them need a polynomial
  loop that invokes a `P`-decider per randomness block and aggregates (vote count /
  OR), built on the upstream `TuringMachine/Build/Loop.lean` combinators plus
  `exists_installCallTM`; one needs a fixed-randomness circuit built from
  `P_subset_PPoly` with `DAGGate.remap`/hard-wiring to route `Turing.pairEncode`'s
  bit-doubling. Each is on the scale of an existing infrastructure file.
* **The ℚ-counting Chernoff deviation** is load-bearing for every Tier-B probability
  statement; its fidelity (not the book's bound, but the proved statements) is the
  primary audit target.
* **Theorem 7.41** stays a documented `sorry` by design; closure attests exactly one
  intentional admission beyond any still-open fill targets.
* Estimated mandatory-core scale: ~27 audited statements; Tier A + Tier B fill
  landed; the `PolyTimeModel` summit is the remaining effort.

## Open design questions (human review required)

Reserved for a **human** maintainer; audit rounds verify but do not dispose of them.
Full statements belong in [`backlog.md`](backlog.md) §CH7 (to be added); the stable
numbering below is what audit documents cite.

1. **CH7-Q1 — the ℚ-counting Chernoff development.** Is replacing the book's
   `e^{-2ε²k}` bound by the exact binomial distribution plus the elementary
   `2^K (s(1-s))^{⌊K/2⌋}` tail and the rational Bernoulli inequality a *faithful*
   rendering of Theorems 7.10/7.17/7.18 and Lemma 7.9 — i.e. are the proved class
   statements the intended ones, with the analytic bound a dispensable intermediate?
   Provisional maintainer choice: yes, keep the ℚ development; the classes are
   insensitive to the particular tail constant.
2. **CH7-Q2 — `ZPP` in Las Vegas / abort form** rather than expected running time.
   Keep the abort-form definition (committing `some b` or aborting `none`, with
   bounded abort probability), with the expected-time equivalence left as related
   work? Provisional: keep the abort form.
3. **CH7-Q3 — Theorem 7.41 statement-only + sign.** Confirm the sign-corrected bound
   is the intended inequality and that shipping it proof-free (book omits the proof)
   is acceptable. Provisional: statement-only, sign as documented.
4. **CH7-Q4 — the `polyTimeModel` certificate rendering of "M is a polynomial-time
   TM"** (Definition 7.4): efficiency as `P`-membership of the `some true`/`some
   false` sets of `M` on `Turing.pairEncode x r`, and `EffTwoWitness` via the nested
   pairing used by `Complexity.SigmaP`. Confirm this is a faithful instantiation and
   that the abstract closure hypotheses are exactly the book's implicit machine
   closures. Provisional: as stated.

## 6. Decision log

| Decision | Status |
|---|---|
| Chapter 7 proceeds on branch `complexity/arora-barak-ch7`; same methodology, gates, tooling, and delivery as Chapters 1-2; artifacts under `ch7-*` names | Decided |
| Randomized classes defined **certificate-first over an abstract `VerifierModel`**, with the machine closures as named hypotheses discharged in `PolyTimeModel.lean`; Tier A kept model-free | Decided |
| **All class-level probability carried out in ℚ by exact counting** (binomial vote distribution + elementary max-term tail + rational Bernoulli), replacing the book's `e^{-2ε²k}`; documented as a deviation in `Classes.lean`/`ErrorReduction.lean`. Seeded as CH7-Q1 | Decided (to auditors) |
| `ZPP` stated in Las Vegas / abort form; expected-time equivalence deferred. Seeded as CH7-Q2 | Decided (to auditors) |
| Randomness/certificate lengths are explicit `polyLen a k n = a·(n+1)^k` formulas (the Argument-A discipline from Chapter 2) | Decided |
| Theorem 7.41 (expander Chernoff) ships **statement-only**, sign-corrected (book omits the proof; Gillman 1998 out of scope). Seeded as CH7-Q3 | Decided (to auditors) |
| Error reduction carries the **Cor 7.11 erratum** correction | Decided |
| `BPP ⊆ P/poly` via the fixed-randomness circuit route (`VerifierHasCircuits` + `P_subset_PPoly`), not PTM snapshots | Decided |
| Tier C (PTMs proper, `BPL`/`RL`, `UPATH ∈ RL`) deferred, not scheduled | Decided |
| Statement surface landed and maintainer-reviewed over **three fidelity rounds**, approved at `4a683979` ("the mathematical statements are ready for proof development") — a lighter fork review standing in for the formal external gate at the time | Decided |
| Upstream `main` (hypercontractivity reorganization + Chapter 10 + the design-adaptation citation policy, `4aea7cfd`) merged into the branch via the fork sync; branch head `440e5034`, full tree builds green | Decided |
| Tier A + Tier B fill landed (21 of the original stubs proved); `PolyTimeModel` partially filled — `closedUnderAnswerIs`/`closedUnderNot`/`inSigma2_polyTimeModel_iff` proved, then `closedUnderRace` proved at `243b106b` (reduced to the `takePrefixByLen`/`dropPrefixByLen` slicing primitive via the unary `polyUnary` length, no in-machine exponentiation) | Decided |
| **Plan backfilled and the external cross-vendor statement-audit gate opened retroactively** (2026-10-09), over the frozen statement surface, per the maintainer's "do it by the book" instruction; fill paused pending gate closure; no proved Lean discarded | Decided |
| External proof-fill delivered (`722738a1`, authored by a different-vendor model the maintainer drove): three new support modules (`TuringMachine/CounterProgInput`, `CircuitComplexity/PairEncode`, `ClassNP/PolyTimePrefix`) closing `takePrefixByLen`/`dropPrefixByLen` and `verifierHasCircuits`, dropping `PolyTimeModel` from 6 open targets to 3. The author could not run Lean; the commit as delivered **did not elaborate** (reserved-keyword `prefix` parse errors; five `PairEncode` proof errors; a stray `omega`; nonexistent `Bool.true_eq_true`/`Bool.false_eq_true`). Mechanical gate (fresh sweep) **rejected** it on arrival | **Superseded** by the repair row below |
| Repaired to green (`76fe2f46`) with **no statement or signature changed** (comment-stripped freeze check: `PolyTimeModel` 20 declarations identical; the three new modules are pure additions). Fixes were purely proof-engineering (keyword rename, dependent-`rw` avoidance, beta-before-`omega`, two re-proved list lemmas, lemma-name corrections). Verified: 13-module `lean_check_tree` sweep green; the four closed leaves (`takePrefixByLen`/`dropPrefixByLen`/`verifierHasCircuits`/`closedUnderRace`) print `[propext, Classical.choice, Quot.sound]` — no `sorryAx`; `adleman_polyTime` still carries `sorryAx` via the open `closedUnderMajority`, as expected. New trusted surface (the three modules) folded into the ch7-phase1 audit scope; the pack/bundle regenerated at this commit. Remaining machine sorries: `closedUnderMajority`/`closedUnderAny`/`closedUnderShiftOr` (+ the intentional Thm 7.41) | Decided |

| **Phase-1 statement-audit gate CLOSED on round 1** (`audits/ch7-phase1-{findings,resolutions}.md`): the cross-vendor auditor reported zero blockers, zero majors, one minor, one note over the 13-module surface at `76fe2f46`, confirming CH7-Q1..Q7 (notably the ℚ-counting Chernoff fidelity and the new circuit/prefix modules). Minor swept (the `closedUnderShiftOr` sketch now notes truncating `zipWith` on arbitrary lengths); note adopted (the `inZPP_iff_inRP_and_inCoRP` docstring distinguishes the abort-form identity from [AB09, Def 7.7]'s expected-time form) — both comment-only, re-elaborated green. Fill may resume on `closedUnderMajority`/`closedUnderAny`/`closedUnderShiftOr`; Thm 7.41 stays the intentional stub | Decided |
| **Fill resumed: block-closure statement skeleton landed** (per `briefs/ch7-pclosure-blocks.md`). New chapter-neutral helper `ClassNP/PolyTimeBlockLoop.lean`: `sliceTakeAt`/`sliceDropAt`/`blockAt`/`xorD` and small FP helpers (proved); five open fill targets — `polyTimeComputable_emitIter` (the machine summit: `exists_emitLoopTM` host with clean-call rounds), `polyTimeComputable_xorD` (counter program), and the three aggregated block tests. `ClassNP/PClosure.lean` **extended** (a frozen, audited Chapter-1/2 file — **flagged for the next audit round**; additive only, pre-existing lint finding on its docstring left untouched) with `mem_P_of_blockAny`/`_blockMajority`/`_blockXorAny`, proofs complete modulo the helper. `PolyTimeModel`'s `closedUnderMajority`/`closedUnderAny`/`closedUnderShiftOr` discharged in full as thin consumers (statements untouched; docstring sketches updated to the reduction). Tree sorry count: 6 (five helper stubs + the intentional Thm 7.41); `sorryAx` now flows only from the helper stubs. Verified: `lean_check_tree` green on the helper, `PClosure`, `PolyHierarchy/{Padding,Normalize,Levels,Collapse}`, `PolyTimeModel`; no repo-wide name collisions; `ClassNP.lean` facade and `KarpLiptonPrefix` untouched by the additive change (their import closures are outside the ch7 scratch-olean tree) | Decided |
| **Fill campaign machine summit CLOSED: the whole ch7 tree is proved modulo the intentional Thm 7.41 stub.** The bounded block-query loop landed in full: new general infrastructure `TuringMachine/Build/EmitIterEmbed.lean` (safe runs, output-prefix commutation, append-only output, the tape-padding state-injecting module-run embedding, control steps — all public, reusable) and `TuringMachine/Build/EmitIterBody.lean` (the emit-iteration body: input-copier startup, anchored two-call rounds from `exists_emitCallTM`/`exists_installCallTM`, `exists_emitIterTM` assembling `exists_emitLoopTM` with the orbit invariant and the `C·(n+1)^c` normal-form budget). `polyTimeComputable_emitIter` discharged; `polyTimeComputable_xorD` proved as a loop customer (no counter program needed — the sketch's CounterProg route was wrong, as a one-pass register machine cannot pair bits across the separator); the three block tests proved earlier now close end to end. The `emitIter` statement's envelope hypothesis was corrected before any consumer landed (orbit-only `horbit` replacing the undischargeable all-states form). **Verification:** 13-module ch7 sweep green, exactly 1 sorry (Chernoff.lean:66, intentional); `#print axioms` on `closedUnderMajority`/`closedUnderAny`/`closedUnderShiftOr`, `adleman_polyTime`, `sipser_gacs_polyTime`, `zpp_eq_rp_inter_corp_polyTime`, the three `mem_P_of_block*`, `polyTimeComputable_emitIter`/`_xorD`, and `exists_emitIterTM` all print exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`; `style_lint` clean on all new/touched files. New trusted surface for the next audit round: `EmitIterEmbed`, `EmitIterBody`, `PolyTimeBlockLoop`, `PolyTimeBlockTests`, `PolyTimeBlockMajority`, and the `PClosure` extension flagged above | Decided |
| **Campaign closure executed; fill-audit gate OPENED** (`audits/ch7-fill-{pack,kickoff,bundle}.md`, `audits/evidence/ch7/ch7-fill-drift-attestation.md`). Closure documentation sweep: 31 comment-only findings (missing proof sketches, attribution tags, `## Main definitions` sections) fixed across nine modules, each mechanically verified comment-only (comment-stripped bytes identical) and re-elaborated green. Drift attestation vs the gate baseline `76fe2f46`: all 13 audited modules comment-stripped identical (`PolyTimeModel`: same 20 declarations, zero signature changes, import block byte-identical — only the three `sorry` bodies became proofs); `PClosure` gained exactly the three flagged headliners as an ordered-prefix extension. **Closure evidence** (`audits/logs/ch7-fill-{sweep,axioms,lint}.log`): 19/19-module sweep green with exactly 1 sorry (Thm 7.41, intentional); 36 axiom prints — 35 headline results at exactly `[propext, Classical.choice, Quot.sound]`, 1 intentional `sorryAx` (`walk_visits_concentration`); lint clean except the single pre-existing `Classes.lean` size finding (1329 > 1000 lines) — **split submitted for approval via the fill gate, not done unilaterally** (frozen audited module). Blueprint increment deferred to the main merge per the Chapter-2 precedent (`dep_graph` needs full-build artifacts). Gate closes on an external cross-vendor round over the bundle: zero blockers / zero majors | Decided |

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009 (ch. 7; 2007 web draft, reference pair under
  `blueprint/src/references/`).
* Gillman, D. *A Chernoff bound for random walks on expander graphs.* SIAM J.
  Comput. 27(4), 1998 — the quantitative Theorem 7.41 proof, out of scope.
* [`workflow.md`](workflow.md), [`policy.md`](policy.md) — process and standards.
