# External audit pack — Chapter 7, Phase 1 (randomized computation, full statement surface)

Audited Lean surface: commit `76fe2f46` on `complexity/arora-barak-ch7` (green,
repaired). This pack/bundle were regenerated on top of it. This is the
**statement-audit gate of the Chapter 7 campaign** (`AroraBarakChapter7Plan.md`),
covering the full statement surface in one phase: Tier A probability/spectral facts,
Tier B randomized classes over an abstract verifier model, the polynomial-time machine
instantiation, **and the three new support modules that the recent fill added**
(counter-program input-shift, a poly-time prefix calculus, and the `pairEncode`
fixed-randomness circuit builder). Record findings in `audits/ch7-phase1-findings.md`.

> **Provenance — read first.** This gate runs **retroactively**, and the surface has
> two layers:
> 1. The original 10-module surface (Tier A + Tier B + `PolyTimeModel` skeleton),
>    maintainer-reviewed over three fidelity rounds, approved at `4a683979`.
> 2. Three **new** support modules and three filled `PolyTimeModel` targets delivered
>    by a *different-vendor model* (commit `722738a1`). That commit **did not compile**
>    as delivered (its author could not run Lean); it was repaired to green at
>    `76fe2f46` with **no statement or signature changed** (see attestation 1). The
>    repairs were pure proof-engineering.
>
> The product under audit is the **statements, their definitions, and (for the
> remaining `sorry`s) their proof sketches** — not tactic scripts, which Lean checks.
> Treat every statement, proved or sorried, with equal suspicion: a *wrong-but-proved*
> statement is the worst outcome, and the new modules are externally-drafted, so
> blind-restate them like any other surface.

Source text: [AB09] ch. 7 (2007 web draft; reference pair under
`blueprint/src/references/`): Lemma 7.5; Definition 7.4 (`BPP`/`RP`/`coRP`/`ZPP`);
Theorem 7.8; Theorem 7.10 + Corollary 7.11; Lemma 7.9; Theorem 7.17; Theorem 7.18; and
§7.B Lemma 7.37, Theorem 7.38, Lemma 7.40, Theorem 7.41. The auditor must have the
chapter at hand.

## Repository-side attestations (maintainer, remote machine — verify or challenge)

1. **Statement freeze.** The fill modified one previously-audited file,
   `Randomized/PolyTimeModel.lean`, by replacing three `sorry` bodies only: a
   comment-stripped comparison of `243b106b` (pre-fill) vs `76fe2f46` (post-repair)
   shows the **same 20 declarations with zero signatures changed, added, or removed**.
   The three new modules and the three one-line facade imports are **pure additions**.
   No other audited `.lean` file is touched.
2. **Elaboration.** Full **13-module** fresh-olean sweep via `scripts/lean_check_tree.sh`
   in `scripts/ab_ch7_module_order.txt` order (Lean 4.25.0, Mathlib at the branch pin;
   **`lake build` not used** — banned on the campaign branch): every module exits 0,
   emits a fresh `.olean`, **zero `error:` lines**.
3. **Admissions inventory.** Exactly **4** `declaration uses 'sorry'` warnings
   tree-wide:
   * `Expanders/Chernoff.lean:66` — `walk_visits_concentration` (Theorem 7.41),
     **intentional and permanent** (book omits the proof).
   * `Randomized/PolyTimeModel.lean:248,255,273` — `polyTimeModel_closedUnderMajority`,
     `…_closedUnderAny`, `…_closedUnderShiftOr`: the three open fill targets (a
     polynomial loop of `P`-decider queries with vote/OR aggregation). Each carries a
     proof sketch.
4. **Axiom hygiene (anti-tamper).** `#print axioms` on the fresh olean tree: the fill's
   closed leaves — `CounterProg.run_shiftInput`, `CounterProg.Goes.prepend_input`,
   `polyTimeComputable_takePrefixByLength`/`…dropPrefixByLength`,
   `DAGCircuit.pairEncode_eval`/`…_size`, `DAGCircuitFamily.pairEncode_eval_eq_true_iff`,
   `Randomized.polyTimeComputable_takePrefixByLen`/`…dropPrefixByLen`,
   `polyTimeModel_verifierHasCircuits`, `polyTimeModel_closedUnderRace` — all print
   exactly `[propext, Classical.choice, Quot.sound]` (a subset for two of them); **no
   `sorryAx`**. `adleman_polyTime` prints `sorryAx` as expected, via the still-open
   `closedUnderMajority`.
5. **Policy conformance.** `scripts/style_lint.py` reports fill-style findings (missing
   `**Proof sketch.**` markers on some landed proofs, `Classes.lean` > 1000 lines, a
   few undocstringed helpers, Lean "unused simp arg" / "unnecessary simpa" linter
   warnings in the repaired modules). These are scoped to fill closure and alter no
   statement; flag any you believe bear on fidelity.

## What is under audit

The original surface, unchanged (see the prior pack revision for its full table): Tier A
(`Expanders/{Basic,Mixing,Walks,Chernoff}`, `Randomized/{SchwartzZippel,ErrorReduction}`)
and Tier B (`Randomized/{Classes,Adleman,SipserGacs}`), headline results Lemma 7.5,
Theorems 7.8/7.10/7.17/7.18, Lemma 7.9, §7.B Lemmas 7.37/7.40 + Theorems 7.38/7.41.
`Randomized/PolyTimeModel.lean` instantiates the abstract model; `closedUnderRace`,
`closedUnderAnswerIs`, `closedUnderNot`, `verifierHasCircuits`, and
`inSigma2_polyTimeModel_iff` are proved, the three closures above remain `sorry`.

**New support surface (this revision):**

| Module | Key definitions | Key statements |
|---|---|---|
| `TuringMachine/CounterProgInput.lean` | `CounterProg.shiftInput` (shift an abstract state's input position) | `run_shiftInput`, `Goes.prepend_input` — a bounded suffix run stays valid after prepending already-consumed input, with positions shifted |
| `ClassNP/PolyTimePrefix.lean` | `PrefixByLength.take`/`drop` (on `pairEncode u s`, return `s.take \|u\|` / `s.drop \|u\|`; malformed pairs → `[]`), via a counter program | `polyTimeComputable_takePrefixByLength`, `…_dropPrefixByLength` |
| `CircuitComplexity/PairEncode.lean` | `DAGCircuit.bufferInputs` (route a circuit's inputs through buffered copies/constants), `DAGCircuit.pairEncode` (compute `C` on `pairEncode x r` with `r` fixed), `pairWiring`/`pairEncodeInput` | `pairEncode_eval`, `pairEncode_isFaninTwo`/`isWellFormed`, `pairEncode_size` (`= n + C.size`), `DAGCircuitFamily.pairEncode_eval_eq_true_iff` |

These discharge, respectively, `takePrefixByLen`/`dropPrefixByLen` (hence
`closedUnderRace`) and `verifierHasCircuits` (hence Adleman's circuit hypothesis).

## Known deviations (verify benign; flag others)

All deviations from the prior pack revision still apply (ℚ-counting Chernoff — **CH7-Q1,
highest priority**; Las Vegas `ZPP` — CH7-Q2; statement-only sign-corrected Thm 7.41 —
CH7-Q3; explicit `polyLen a k n = a·(n+1)^k`; certificate `VerifierModel` with named
closures — CH7-Q4; Cor 7.11 erratum; fixed-randomness circuit route). New with this
revision:

* **The circuit buffer adds `n` vertices** (`pairEncode_size = n + C.size`), because the
  library's `pairEncode` *doubles* the first component, so each free input feeds two
  encoded coordinates via two buffered copies, with the separator and the fixed word `r`
  as constants. The overhead is polynomial and independent of `r`'s contents.
* **`PrefixByLength.take`/`drop` are total**: on a malformed pair (`pairDecode = none`,
  e.g. the forbidden aligned `10`) they return `[]`, matching `pairFstD`/`pairSndD = []`.

## Specific questions for this phase

Carry over CH7-Q1..Q4 from the prior revision (CH7-Q1 — ℚ-Chernoff fidelity — remains
priority one). New, on the added surface:

5. **Circuit fidelity.** Does `pairWiring`/`pairEncodeInput` realize the library's
   `Turing.pairEncode (List.ofFn v) r` *exactly* as circuit input wires (doubled first
   component as two copies per bit, constant separator `[false,true]`, constant `r`)?
   Does `DAGCircuitFamily.pairEncode_eval_eq_true_iff` state the intended acceptance
   correspondence that `polyTimeModel_verifierHasCircuits` consumes — neither off by a
   coordinate nor collapsing when `n = 0` or `r = []`?
6. **Prefix fidelity + the bridge.** Do `PrefixByLength.take`/`drop` agree with
   `Randomized.takePrefixByLen`/`dropPrefixByLen` as used in `closedUnderRace` (the fill
   bridges them by `simp` unfolding — confirm the two definitions are the same
   function, so the poly-time proof is about the function `closedUnderRace` actually
   uses)? Is the malformed-input convention (`→ []`) faithful to `pairFstD`/`pairSndD`?
7. **Input-shift semantics.** Do `CounterProg.run_shiftInput` / `Goes.prepend_input`
   state the "execute on the suffix = execute on the whole with position shifted"
   property correctly, with no sign/▸off-by-one in the position arithmetic?

## Brief for the auditor

As before: audit the trusted surface (definitions, statements, sketches); do not review
tactic scripts. Hunt infidelity, trivialization, unprovability, missing hypotheses.
Blind-restate every definition (old and new) before reading its docstring; argue each
sorried statement (Thm 7.41 and the three closures) true-as-stated or exhibit the
problem; attempt ≥3 adversarial instantiations (`n = 0`, `r = []`, a constant verifier,
a degenerate graph). No blanket approval; justify an empty table with the restatements.
The gate closes only on a round reporting **zero blockers and zero majors**.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = downstream work would build on a wrong statement;
**major** = statement fixable but materially misleading; **minor** = edge case or
naming/attribution; **note** = observation.


## ===== AroraBarakChapter7Plan.md =====

```
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

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009 (ch. 7; 2007 web draft, reference pair under
  `blueprint/src/references/`).
* Gillman, D. *A Chernoff bound for random walks on expander graphs.* SIAM J.
  Comput. 27(4), 1998 — the quantitative Theorem 7.41 proof, out of scope.
* [`workflow.md`](workflow.md), [`policy.md`](policy.md) — process and standards.
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

## ===== scripts/ab_ch7_module_order.txt =====

```
TCSlib/Complexity/Expanders/Basic
TCSlib/Complexity/Expanders/Mixing
TCSlib/Complexity/Expanders/Walks
TCSlib/Complexity/Expanders/Chernoff
TCSlib/Complexity/Randomized/SchwartzZippel
TCSlib/Complexity/Randomized/ErrorReduction
TCSlib/Complexity/Randomized/Classes
TCSlib/Complexity/Randomized/Adleman
TCSlib/Complexity/Randomized/SipserGacs
TCSlib/Complexity/TuringMachine/CounterProgInput
TCSlib/Complexity/CircuitComplexity/PairEncode
TCSlib/Complexity/ClassNP/PolyTimePrefix
TCSlib/Complexity/Randomized/PolyTimeModel
```

## ===== audits/ch7-prefix-circuits-source-review.md =====

```
# Chapter 7: prefix operations and fixed-randomness circuits

Base: `69a606dac3366a878f98683812b69c40356e4c0b`, branch
`complexity/arora-barak-ch7`.

Proof implementations replace three stubs in `Randomized/PolyTimeModel.lean`:

- `polyTimeComputable_takePrefixByLen`
- `polyTimeComputable_dropPrefixByLen`
- `polyTimeModel_verifierHasCircuits`

All 20 pre-existing definition and theorem signatures in that file are unchanged.
The new support modules contain no admissions or additional axioms. Their imports
are added to the existing topic facades. These are additive infrastructure changes
in the Chapter 1–2 function, machine, and circuit layers; existing declarations in
those layers are unchanged.

## Proof arguments

The shared prefix program counts one source bit per aligned doubled pair. At the
separator it either copies that many payload bits or skips them and copies the
remaining payload. Incomplete encodings and the forbidden aligned pair `10`
halt without output. The abstract step bound is `5(|z|+1)`; the existing
counter-program compiler gives polynomial-time machines.

The circuit construction applies the proved `P ⊆ P/poly` theorem to the verifier's
paired acceptance language. Each encoded input coordinate receives a distinct
buffer vertex: the doubled input bits are copies, and the separator and random
bits are constants. Shifting all old vertex numbers preserves distinct inputs and
fan-in. The resulting circuit has exactly `n + C.size` vertices. The proof composes
the paired-length polynomial with the family's size polynomial to obtain a bound
independent of the random string's contents.

## Validation

- Independent source reviews of both constructions and the main circuit proof.
- `scripts/style_lint.py`: zero findings in all seven touched Lean files.
- Prefix-program model: all 8,190 input/mode combinations for bit strings of
  length at most 11 passed output and abstract-time checks.
- Circuit-buffer model: 2,790 evaluation and well-formedness checks passed,
  including empty input and random strings and gates reading both doubled copies.
- Uniform circuit-size arithmetic: 7,776 parameter combinations passed,
  including zero coefficients and exponents.
- No public-statement drift in `PolyTimeModel.lean`; no new `sorry`, `admit`,
  custom `axiom`, or `unsafe` declaration in the support modules.

**Lean elaboration and kernel checking remain unverified.** The execution environment
has no Lean runtime or working LeanInfoView, and `AGENTS.md` requires proof-state
checking through LeanInfoView rather than shell build commands. The finite model
checks above validate the algorithms and arithmetic; they do not certify the Lean
proof terms. This commit is a proof implementation awaiting that check.

Three machine-model admissions remain: majority, OR repetition, and shifted OR.
The separate expander-Chernoff theorem remains intentionally statement-only.
The specialized ZPP, Adleman, and Sipser–Gács corollaries consequently still depend
on unfinished closure proofs.
```

## ===== TCSlib/Complexity/Expanders/Basic.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Symmetric

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetric stochastic matrices and the parameter λ

The linear-algebraic foundations of Arora–Barak's appendix 7.A: probability
distributions on vertices as vectors, the normalized adjacency matrix of a
regular graph as a symmetric stochastic matrix, and the parameter `λ(A)` —
the maximum stretch of `A` on the space orthogonal to the uniform
distribution ([AB09, Def 7.25]).

## Main definitions

* `Expander.IsSymmStochastic` — a real square matrix that is symmetric, entrywise
  nonnegative, with every row summing to `1` ([AB09, §7.A.1]).
* `Expander.uniform` — the uniform distribution `(1/n, …, 1/n)` as a vector.
* `Expander.lambda` — the parameter `λ(A)` [AB09, Def 7.25].

## Main results

* `Expander.lambda_nonneg`, `Expander.lambda_le_one` — `0 ≤ λ(A) ≤ 1`
  ([AB09, Rmk 7.26], via Exercise 10).
* `Expander.norm_toCLM_apply_le` — a symmetric stochastic matrix is an `L²`
  contraction ([AB09, Exercise 10]), the helper behind `lambda_le_one` and
  `Expander.opNorm_le_one` in `Expanders.Walks`.
* `Expander.norm_mulVec_le_lambda` — the defining inequality
  `‖A𝐯‖₂ ≤ λ(A)‖𝐯‖₂` for `𝐯 ⊥ 1`.
* `Expander.mulVec_uniform` — `A·1 = 1`: the uniform distribution is stable.

## Deviation from the source

[AB09, §7.A] states these notions for the normalized adjacency matrix of a
`d`-regular `n`-vertex multigraph, remarking that any such matrix is symmetric
stochastic and that the definitions only use that structure.  We take the
symmetric stochastic matrix itself as the primitive object, so every result
applies to a regular multigraph via its normalized adjacency matrix; no graph
type is fixed at this layer.  `λ` is defined by a supremum over the unit
sphere of `1^⊥`, which for `n ≤ 1` is empty; `sSup ∅ = 0` makes `λ = 0` there,
consistent with the convention that a one-vertex graph is a perfect expander.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Expander

open Matrix

variable {n : ℕ}

/-- A real square matrix is *symmetric stochastic* when it is symmetric,
entrywise nonnegative, and every row sums to `1` (hence, by symmetry, every
column does too).  The normalized adjacency matrix `A(G)` of any `d`-regular
multigraph is of this form.  [AB09, §7.A.1] -/
structure IsSymmStochastic (A : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- The matrix is symmetric: `Aᵢⱼ = Aⱼᵢ`. -/
  symm : A.IsSymm
  /-- All entries are nonnegative. -/
  nonneg : ∀ i j, 0 ≤ A i j
  /-- Every row sums to one. -/
  rowSum : ∀ i, ∑ j, A i j = 1

/-- The uniform distribution `𝟙 = (1/n, …, 1/n)` on `n` vertices, as a vector
in Euclidean space.  [AB09, Def 7.25] -/
noncomputable def uniform (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm fun _ => (n : ℝ)⁻¹

/-- The action of a matrix on Euclidean space, as a continuous linear map;
`‖·‖` of this map is the `L²` operator norm. -/
noncomputable def toCLM (A : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) A

/-- Each coordinate of the uniform vector is `1/n`. -/
@[simp] theorem uniform_apply (i : Fin n) : uniform n i = (n : ℝ)⁻¹ := rfl

/-- `toCLM` acts coordinatewise as matrix–vector multiplication. -/
theorem toCLM_apply_coord (A : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    toCLM A v i = ∑ j, A i j * v j := rfl

/-- The real Euclidean inner product, in coordinates. -/
theorem inner_eq_sum (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ i, x i * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply,
    star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A symmetric matrix is self-adjoint for the Euclidean inner product:
`⟨A𝐱, 𝐲⟩ = ⟨𝐱, A𝐲⟩`. -/
theorem inner_toCLM_right {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (toCLM A x) y = inner ℝ x (toCLM A y) := by
  rw [inner_eq_sum, inner_eq_sum]
  simp_rw [toCLM_apply_coord, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hA.apply j i]
  ring

/-- `⟨𝟙, 𝟙⟩ = 1/n` (also for `n = 0`, where both sides vanish). -/
theorem inner_uniform_self :
    inner ℝ (uniform n) (uniform n) = (n : ℝ)⁻¹ := by
  rw [inner_eq_sum]
  show ∑ _i : Fin n, (n : ℝ)⁻¹ * (n : ℝ)⁻¹ = (n : ℝ)⁻¹
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases eq_or_ne (n : ℝ) 0 with h | h
  · rw [h]; simp
  · field_simp

/-- `toCLM` commutes with scalar multiplication of the matrix. -/
theorem toCLM_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    toCLM (c • A) = c • toCLM A := by
  refine ContinuousLinearMap.ext fun v => PiLp.ext fun i => ?_
  show ∑ j, c * A i j * v j = c * ∑ j, A i j * v j
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `toCLM` commutes with matrix addition. -/
theorem toCLM_add (A B : Matrix (Fin n) (Fin n) ℝ) :
    toCLM (A + B) = toCLM A + toCLM B := by
  refine ContinuousLinearMap.ext fun v => PiLp.ext fun i => ?_
  show ∑ j, (A i j + B i j) * v j = (∑ j, A i j * v j) + ∑ j, B i j * v j
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `toCLM` commutes with matrix subtraction. -/
theorem toCLM_sub (A B : Matrix (Fin n) (Fin n) ℝ) :
    toCLM (A - B) = toCLM A - toCLM B := by
  refine ContinuousLinearMap.ext fun v => PiLp.ext fun i => ?_
  show ∑ j, (A i j - B i j) * v j = (∑ j, A i j * v j) - ∑ j, B i j * v j
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The parameter `λ(A)`, also written `λ(G)` for the normalized adjacency
matrix of a graph `G`: the maximum of `‖A𝐯‖₂` over all unit vectors `𝐯`
orthogonal to the uniform distribution.  For a symmetric stochastic matrix
this equals the second largest absolute value of an eigenvalue, and `1 - λ(A)`
is the *spectral gap*.  [AB09, Def 7.25] -/
noncomputable def lambda (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun v => ‖toCLM A v‖) ''
    {v : EuclideanSpace ℝ (Fin n) | inner ℝ v (uniform n) = 0 ∧ ‖v‖ = 1})

/-- A symmetric stochastic matrix fixes the uniform distribution: `A𝟙 = 𝟙`.
[AB09, Rmk 7.26: "`A`**1** `=` **1**"]

**Proof sketch.** The `i`-th coordinate of `A𝟙` is `(1/n)·Σⱼ Aᵢⱼ`, and row `i`
sums to one. -/
theorem mulVec_uniform {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymmStochastic A) :
    toCLM A (uniform n) = uniform n := by
  refine PiLp.ext fun i => ?_
  show ∑ j, A i j * (n : ℝ)⁻¹ = (n : ℝ)⁻¹
  rw [← Finset.sum_mul, hA.rowSum i, one_mul]

/-- The defining property of `λ`: `A` shrinks any vector orthogonal to the
uniform distribution by a factor of at least `λ(A)`.  [AB09, Def 7.25],
unfolded as used in the proof of [AB09, Lem 7.27].

**Proof sketch.** For `𝐯 = 0` both sides vanish.  Otherwise `𝐯/‖𝐯‖₂` lies in
the unit sphere of `𝟙^⊥`, so `‖A(𝐯/‖𝐯‖₂)‖₂` is one of the values whose
supremum is `λ(A)`; the supremum is attained/bounded because the sphere is
compact and `v ↦ ‖A𝐯‖₂` is continuous.  Multiply through by `‖𝐯‖₂`. -/
theorem norm_mulVec_le_lambda {A : Matrix (Fin n) (Fin n) ℝ}
    (_hA : IsSymmStochastic A) {v : EuclideanSpace ℝ (Fin n)}
    (hv : inner ℝ v (uniform n) = 0) :
    ‖toCLM A v‖ ≤ lambda A * ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  · have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
    have hbdd : BddAbove ((fun w => ‖toCLM A w‖) ''
        {w : EuclideanSpace ℝ (Fin n) | inner ℝ w (uniform n) = 0 ∧ ‖w‖ = 1}) := by
      refine ⟨‖toCLM A‖, ?_⟩
      rintro x ⟨w, ⟨-, hw1⟩, rfl⟩
      simpa [hw1] using (toCLM A).le_opNorm w
    have hmem : ‖v‖⁻¹ • v ∈
        {w : EuclideanSpace ℝ (Fin n) | inner ℝ w (uniform n) = 0 ∧ ‖w‖ = 1} := by
      refine ⟨?_, ?_⟩
      · rw [real_inner_smul_left, hv, mul_zero]
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne']
    have hle : ‖toCLM A (‖v‖⁻¹ • v)‖ ≤ lambda A := le_csSup hbdd ⟨_, hmem, rfl⟩
    rw [map_smul, norm_smul, norm_inv, norm_norm] at hle
    calc ‖toCLM A v‖ = ‖v‖ * (‖v‖⁻¹ * ‖toCLM A v‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ hvn.ne', one_mul]
      _ ≤ ‖v‖ * lambda A := mul_le_mul_of_nonneg_left hle hvn.le
      _ = lambda A * ‖v‖ := mul_comm _ _

/-- `λ(A) ≥ 0` (for `n ≥ 2`; for `n ≤ 1` the defining set is empty and
`λ(A) = 0` by convention).  [AB09, Rmk 7.26]

**Proof sketch.** `λ` is a supremum of norms, which are nonnegative; for
`n ≥ 2` the unit sphere of `𝟙^⊥` is nonempty, so the supremum dominates one
such norm. -/
theorem lambda_nonneg (A : Matrix (Fin n) (Fin n) ℝ) (_hn : 2 ≤ n) :
    0 ≤ lambda A :=
  Real.sSup_nonneg fun x hx => by
    obtain ⟨v, -, rfl⟩ := hx
    exact norm_nonneg _

/-- A symmetric stochastic matrix is an `L²` contraction:
`‖A𝐯‖₂ ≤ ‖𝐯‖₂` for every `𝐯`.  This is the pointwise content of
[AB09, Exercise 10] (`‖A‖ ≤ 1`); the bundled operator-norm form is
`Expander.opNorm_le_one` in `Expanders.Walks`.

**Proof.** `(A𝐯)ᵢ² = (Σⱼ Aᵢⱼ𝐯ⱼ)² ≤ (Σⱼ Aᵢⱼ)·(Σⱼ Aᵢⱼ𝐯ⱼ²) = Σⱼ Aᵢⱼ𝐯ⱼ²` by
Cauchy–Schwarz with weights `Aᵢⱼ` (rows sum to one); summing over `i` and
using that columns sum to one (symmetry) gives `Σᵢ(A𝐯)ᵢ² ≤ Σⱼ𝐯ⱼ²`. -/
theorem norm_toCLM_apply_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) (v : EuclideanSpace ℝ (Fin n)) :
    ‖toCLM A v‖ ≤ ‖v‖ := by
  have hcol : ∀ j, ∑ i, A i j = 1 := fun j => by
    rw [Finset.sum_congr rfl fun i _ => hA.symm.apply j i]
    exact hA.rowSum j
  have hstep : ∀ i, (∑ j, A i j * v j) ^ 2 ≤ ∑ j, A i j * v j ^ 2 := fun i => by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (r := fun j => A i j * v j) (f := fun j => A i j)
      (g := fun j => A i j * v j ^ 2)
      (fun j _ => hA.nonneg i j)
      (fun j _ => mul_nonneg (hA.nonneg i j) (sq_nonneg _))
      (fun j _ => by ring)
    rwa [hA.rowSum i, one_mul] at h
  have hsum : ∑ i, (∑ j, A i j * v j) ^ 2 ≤ ∑ j, v j ^ 2 :=
    calc ∑ i, (∑ j, A i j * v j) ^ 2
        ≤ ∑ i, ∑ j, A i j * v j ^ 2 := Finset.sum_le_sum fun i _ => hstep i
      _ = ∑ j, ∑ i, A i j * v j ^ 2 := Finset.sum_comm
      _ = ∑ j, (∑ i, A i j) * v j ^ 2 :=
          Finset.sum_congr rfl fun j _ => (Finset.sum_mul ..).symm
      _ = ∑ j, v j ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [hcol j, one_mul]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖toCLM A v i‖ ^ 2
      = ∑ i, (∑ j, A i j * v j) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.norm_eq_abs, sq_abs]
        rfl
    _ ≤ ∑ j, v j ^ 2 := hsum
    _ = ∑ j, ‖v j‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]

/-- Every eigenvalue of a symmetric stochastic matrix has absolute value at
most one; consequently `λ(A) ≤ 1`.  [AB09, Rmk 7.26], proved as
[AB09, Exercise 10].

**Proof sketch.** A symmetric stochastic matrix has `L²` operator norm at most
`1`: for any `𝐯`, `(A𝐯)ᵢ² = (Σⱼ Aᵢⱼ𝐯ⱼ)² ≤ Σⱼ Aᵢⱼ𝐯ⱼ²` by Cauchy–Schwarz with
weights `Aᵢⱼ` (rows sum to one), and summing over `i` uses that columns sum to
one (`Expander.norm_toCLM_apply_le`).  The supremum defining `λ` runs over
unit vectors, so it is bounded by the operator norm. -/
theorem lambda_le_one {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymmStochastic A) :
    lambda A ≤ 1 := by
  refine Real.sSup_le ?_ zero_le_one
  rintro x ⟨v, ⟨-, hv1⟩, rfl⟩
  exact (norm_toCLM_apply_le hA v).trans_eq hv1

end Expander
```

## ===== TCSlib/Complexity/Expanders/Mixing.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Expanders.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Expander Mixing Lemma

Arora–Barak's Lemma 7.37: in an `(n,d,λ)`-graph, the number of edges between
any two vertex sets `S` and `T` deviates from its "random-graph" expectation
`(d/n)|S||T|` by at most `λd√(|S||T|)`.

## Main results

* `Expander.inner_indicator_mulVec_le` — the normalized form
  `|𝐬ᵀA𝐭 − |S||T|/n| ≤ λ√(|S||T|)`, which is [AB09, Lem 7.37, eq. (2)].

## Deviation from the source

[AB09, Lem 7.37] is stated for the edge count `E(S,T)` of an `(n,d,λ)`-graph;
its proof immediately reduces to the equivalent normalized statement (2) about
the normalized adjacency matrix, `|𝐬A𝐭 − |S||T|/n| ≤ λ√(|S||T|)`, which no
longer mentions the degree.  We formalize (2) for an arbitrary symmetric
stochastic matrix with `λ(A) ≤ λ`; the book's form is recovered by
multiplying through by `d`, since `|E(S,T)| = d·𝐬ᵀA(G)𝐭` for the normalized
adjacency matrix of a `d`-regular multigraph (with edges counted with
multiplicity, and, as in the book's convention for `E(S,S̄)`-style counts,
orientation-sensitively).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Expander

open Matrix Finset

variable {n : ℕ}

/-- The indicator vector `𝐬 ∈ ℝⁿ` of a finite set `S` of vertices:
`𝐬ᵢ = 1` if `i ∈ S` and `𝐬ᵢ = 0` otherwise.  [AB09, proof of Lem 7.37] -/
noncomputable def indicator (S : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm fun i => if i ∈ S then 1 else 0

/-- **Expander Mixing Lemma**, normalized form.  For a symmetric stochastic
`A` with `λ(A) ≤ λ` and vertex sets `S, T`,

`|⟨𝐬, A𝐭⟩ − |S||T|/n| ≤ λ·√(|S||T|)`,

where `𝐬, 𝐭` are the indicator vectors of `S, T`.  For the normalized
adjacency matrix of a `d`-regular multigraph, `d·⟨𝐬, A𝐭⟩` is the number of
edges `|E(S,T)|`, so multiplying through by `d` gives the book's statement
`| |E(S,T)| − (d/n)|S||T| | ≤ λd√(|S||T|)`.  [AB09, Lem 7.37, via eq. (2)]

**Proof sketch.** Decompose the indicator vectors against the uniform
direction: `𝐬 = 𝐬∥ + 𝐬⊥` and `𝐭 = 𝐭∥ + 𝐭⊥` with `𝐬∥ = (|S|/n)·n𝟙`,
`𝐭∥ = (|T|/n)·n𝟙` the components along `𝟙` and `𝐬⊥, 𝐭⊥ ⊥ 𝟙`.  Since
`A𝐭∥ = 𝐭∥` and `A𝐭⊥ ⊥ 𝟙` (both from `IsSymmStochastic`),

`⟨𝐬, A𝐭⟩ − |S||T|/n = ⟨𝐬⊥, A𝐭⊥⟩`,

because `⟨𝐬, 𝐭∥⟩ = |S||T|/n` and the cross terms vanish by orthogonality.
Now `|⟨𝐬⊥, A𝐭⊥⟩| ≤ ‖𝐬⊥‖₂·‖A𝐭⊥‖₂ ≤ λ‖𝐬⊥‖₂‖𝐭⊥‖₂ ≤ λ‖𝐬‖₂‖𝐭‖₂ = λ√(|S||T|)`
by Cauchy–Schwarz, the defining property of `λ`
(`Expander.norm_mulVec_le_lambda`), and Pythagoras (`‖𝐬⊥‖ ≤ ‖𝐬‖`).  Both
bounds follow from the single absolute value.  (Deviation from the book's
printed proof: [AB09] argues through the `A = (1−λ)J + λC` decomposition of
Lemma 7.40, which cleanly yields only the upper bound — the lower bound
needs the orthogonal-decomposition argument above, so we use it for
both.) -/
theorem inner_indicator_mulVec_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam : ℝ} (hlam : lambda A ≤ lam)
    (S T : Finset (Fin n)) :
    |inner ℝ (indicator S) (toCLM A (indicator T)) -
        (S.card * T.card : ℝ) / n| ≤
      lam * Real.sqrt (S.card * T.card) := by
  classical
  -- Inner products against the uniform vector.
  have hu : ∀ U : Finset (Fin n),
      inner ℝ (indicator U) (uniform n) = (U.card : ℝ) * (n : ℝ)⁻¹ := fun U => by
    rw [inner_eq_sum]
    show ∑ i, (if i ∈ U then (1 : ℝ) else 0) * (n : ℝ)⁻¹ = _
    rw [← Finset.sum_mul, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  -- The components of the indicators orthogonal to the uniform direction.
  set sp : EuclideanSpace ℝ (Fin n) :=
    indicator S - (S.card : ℝ) • uniform n with hsp_def
  set tp : EuclideanSpace ℝ (Fin n) :=
    indicator T - (T.card : ℝ) • uniform n with htp_def
  have hsu : inner ℝ sp (uniform n) = 0 := by
    rw [hsp_def, inner_sub_left, real_inner_smul_left, hu, inner_uniform_self, sub_self]
  have htu : inner ℝ tp (uniform n) = 0 := by
    rw [htp_def, inner_sub_left, real_inner_smul_left, hu, inner_uniform_self, sub_self]
  -- The deviation equals `⟪s^⊥, A t^⊥⟫`.
  have hAt : toCLM A (indicator T) = toCLM A tp + (T.card : ℝ) • uniform n := by
    rw [htp_def, map_sub, map_smul, mulVec_uniform hA, sub_add_cancel]
  have h1 : inner ℝ sp ((T.card : ℝ) • uniform n) = 0 := by
    rw [real_inner_smul_right, hsu, mul_zero]
  have h2 : inner ℝ ((S.card : ℝ) • uniform n) (toCLM A tp) = 0 := by
    rw [real_inner_smul_left, ← inner_toCLM_right hA.symm, mulVec_uniform hA,
      real_inner_comm, htu,
      mul_zero]
  have h3 : inner ℝ ((S.card : ℝ) • uniform n) ((T.card : ℝ) • uniform n) =
      (S.card * T.card : ℝ) / n := by
    rw [real_inner_smul_left, real_inner_smul_right, inner_uniform_self, div_eq_mul_inv]
    ring
  have key : inner ℝ (indicator S) (toCLM A (indicator T)) -
      (S.card * T.card : ℝ) / n = inner ℝ sp (toCLM A tp) := by
    have hs : indicator S = sp + (S.card : ℝ) • uniform n := by
      rw [hsp_def, sub_add_cancel]
    rw [hAt]
    conv_lhs => rw [hs]
    rw [inner_add_left, inner_add_right, inner_add_right, h1, h2, h3]
    ring
  -- Pythagoras: dropping the uniform component shrinks the norm.
  have hperp_le : ∀ x y : EuclideanSpace ℝ (Fin n),
      inner ℝ (x - y) y = 0 → ‖x - y‖ ≤ ‖x‖ := fun x y hxy => by
    have h := norm_add_sq_real (x - y) y
    rw [sub_add_cancel, hxy] at h
    have h2 : ‖x - y‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]
    calc ‖x - y‖ = Real.sqrt (‖x - y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt h2
      _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)
  -- The norm of an indicator vector is `√|U|`.
  have hnormInd : ∀ U : Finset (Fin n),
      ‖indicator U‖ = Real.sqrt U.card := fun U => by
    rw [EuclideanSpace.norm_eq]
    congr 1
    have hcoord : ∀ i, ‖indicator U i‖ ^ 2 = if i ∈ U then (1 : ℝ) else 0 :=
      fun i => by
        show ‖(if i ∈ U then (1 : ℝ) else 0)‖ ^ 2 = _
        split <;> simp
    rw [Finset.sum_congr rfl fun i _ => hcoord i, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hps : ‖sp‖ ≤ Real.sqrt S.card := by
    rw [← hnormInd S]
    refine hperp_le _ _ ?_
    rw [real_inner_smul_right, hsu, mul_zero]
  have hpt : ‖tp‖ ≤ Real.sqrt T.card := by
    rw [← hnormInd T]
    refine hperp_le _ _ ?_
    rw [real_inner_smul_right, htu, mul_zero]
  -- `λ ≥ 0`, so the hypothesis `λ(A) ≤ lam` makes `lam` nonnegative.
  have hlam0 : 0 ≤ lam :=
    le_trans (Real.sSup_nonneg fun x hx => by
      obtain ⟨v, -, rfl⟩ := hx; exact norm_nonneg _) hlam
  -- Put it together with Cauchy–Schwarz and the defining property of `λ`.
  rw [key]
  calc |inner ℝ sp (toCLM A tp)|
      ≤ ‖sp‖ * ‖toCLM A tp‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖sp‖ * (lam * ‖tp‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact (norm_mulVec_le_lambda hA htu).trans
          (mul_le_mul_of_nonneg_right hlam (norm_nonneg _))
    _ ≤ Real.sqrt S.card * (lam * Real.sqrt T.card) := by gcongr
    _ = lam * Real.sqrt (S.card * T.card) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _)]
        ring

end Expander
```

## ===== TCSlib/Complexity/Expanders/Walks.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Expanders.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ENNReal.BigOperators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Expander walks

Random walks driven by a symmetric stochastic matrix, and Arora–Barak's
Theorem 7.38: a random walk on an expander escapes any small vertex set with
probability exponentially close to one.

## Main definitions

* `Expander.unifMatrix` — the matrix `J` with all entries `1/n`.
* `Expander.stepPMF` — one step of the walk from a vertex, as a `PMF`.
* `Expander.walkPMF` — the `k`-step random walk started uniformly, as a `PMF`
  on `Fin (k+1) → Fin n` (a sequence of `k+1` visited vertices).
* `Expander.resMatrix`, `Expander.resVec` — the `B`-restricted transition
  matrix `B̂A` and the vectors `(B̂A)^k B̂𝟙` of the proof of Thm 7.38.

## Main results

* `Expander.opNorm_le_one` — a symmetric stochastic matrix has `L²` operator
  norm at most `1` ([AB09, after Def 7.39], via [AB09, Exercise 10]).
* `Expander.exists_decomposition` — `A = (1−λ)J + λC` with `‖C‖ ≤ 1`
  ([AB09, Lem 7.40]).
* `Expander.walk_filter_sum` — the probability that the walk stays in `B`
  and ends at `j` is the `j`-th entry of `(B̂A)^k B̂𝟙`.
* `Expander.walk_all_mem_le` — the expander-walk bound [AB09, Thm 7.38].

## Deviations from the source

* [AB09, Def 7.39] defines the matrix norm as "the maximum `α` such that
  `‖A𝐯‖₂ ≤ α‖𝐯‖₂` for every `𝐯`" (i.e. the minimum such bound); we use
  Mathlib's `L²` operator norm of the associated continuous linear map, which
  is that quantity.
* [AB09, Thm 7.38] speaks of a `(k−1)`-step walk `X₁,…,X_k` on an
  `(N,d,λ)`-graph and bounds `Pr[∀ i ≤ k, X_i ∈ B] ≤ ((1−λ)√β + λ)^{k−1}`.
  We index by the number of *steps* `k`, so the walk visits `k+1` vertices
  and the bound's exponent is `k`.  As in `Expanders.Basic`, the graph is
  represented by its normalized adjacency matrix, and the eigenvalue bound
  `λ(G) ≤ λ` is a hypothesis `lambda A ≤ lam`; the set-size bound `|B| ≤ βN`
  is the hypothesis `hB`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Expander

open Matrix
open scoped ENNReal

variable {n : ℕ}

/-- The `n × n` matrix `J` with `J i j = 1/n` for every `i, j`: the normalized
adjacency matrix of the `n`-clique with self-loops.  `J𝐩` is the uniform
distribution for every probability vector `𝐩`.  [AB09, Lem 7.40] -/
noncomputable def unifMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun _ _ => (n : ℝ)⁻¹

/-- A symmetric stochastic matrix has `L²` operator norm at most `1`.
[AB09, remark after Def 7.39: "if `A` is a normalized adjacency matrix then
`‖A‖ = 1`"]; the inequality is [AB09, Exercise 10].

**Proof sketch.** For a unit vector `𝐯`, expand `‖A𝐯‖₂²` and apply
Cauchy–Schwarz with the weights `Aᵢⱼ` in each coordinate, using that every
row and every column of `A` sums to one. -/
theorem opNorm_le_one {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymmStochastic A) :
    ‖toCLM A‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]
    exact norm_toCLM_apply_le hA v

/-- **Decomposition of an expander step.**  If `A` is symmetric stochastic and
`λ(A) ≤ λ` with `0 ≤ λ`, then `A = (1−λ)J + λC` where `J` is the all-`1/n`
matrix and `‖C‖ ≤ 1`: a step of the walk behaves, for the purposes of `L²`
analysis, like moving to the uniform distribution with probability `1−λ`.
(`C` may have negative entries, so this is not a literal convex combination
of walks.)  [AB09, Lem 7.40], including the degenerate case `λ = 0` the book
permits (e.g. `A = J` itself).

**Proof sketch.** For `λ > 0`, define `C = (1/λ)(A − (1−λ)J)`.  Decompose
any `𝐯` as `𝐮 + 𝐰` with `𝐮 = α𝟙` and `𝐰 ⊥ 𝟙`.  Then `C𝐮 = 𝐮` (both `A` and
`J` fix `𝟙`), and `C𝐰 = (1/λ)A𝐰` (as `J𝐰 = 0`), which has norm at most
`‖𝐰‖₂` by the defining property of `λ`.  Since `C𝐮 = 𝐮 ⊥ C𝐰 ∈ 𝟙^⊥`,
Pythagoras gives `‖C𝐯‖₂ ≤ ‖𝐯‖₂`.  For `λ = 0` the hypothesis forces `A` to
annihilate `𝟙^⊥` (`‖A𝐰‖ ≤ 0`), and `A𝟙 = 𝟙 = J𝟙`, so `A = J`; take
`C = 0`. -/
theorem exists_decomposition {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam : ℝ} (hlam : lambda A ≤ lam)
    (hlam0 : 0 ≤ lam) :
    ∃ C : Matrix (Fin n) (Fin n) ℝ,
      A = (1 - lam) • unifMatrix n + lam • C ∧ ‖toCLM C‖ ≤ 1 := by
  classical
  rcases hlam0.eq_or_lt' with rfl | hpos
  · -- `λ = 0`: the hypothesis forces `A` to annihilate `𝟙^⊥`, so `A = J`.
    refine ⟨0, ?_, ?_⟩
    · have hzero : ∀ w : EuclideanSpace ℝ (Fin n),
          inner ℝ w (uniform n) = 0 → toCLM A w = 0 := fun w hw => by
        have h0 : ‖toCLM A w‖ ≤ 0 :=
          (norm_mulVec_le_lambda hA hw).trans
            (mul_nonpos_of_nonpos_of_nonneg hlam (norm_nonneg _))
        simpa using le_antisymm h0 (norm_nonneg _)
      have hone : ∀ j : Fin n,
          inner ℝ (EuclideanSpace.single j (1 : ℝ)) (uniform n) =
            (n : ℝ)⁻¹ := fun j => by
        rw [inner_eq_sum]
        simp only [EuclideanSpace.single_apply, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, uniform_apply]
      have hAe : ∀ j : Fin n,
          toCLM A (EuclideanSpace.single j (1 : ℝ)) = uniform n := fun j => by
        have hw : inner ℝ (EuclideanSpace.single j (1 : ℝ) - uniform n)
            (uniform n) = 0 := by
          rw [inner_sub_left, hone, inner_uniform_self, sub_self]
        have hsplit : toCLM A (EuclideanSpace.single j (1 : ℝ)) =
            toCLM A (EuclideanSpace.single j (1 : ℝ) - uniform n) +
              toCLM A (uniform n) := by
          rw [← map_add, sub_add_cancel]
        rw [hsplit, hzero _ hw, mulVec_uniform hA, zero_add]
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      ext i j
      show A i j = (n : ℝ)⁻¹
      have h2 : toCLM A (EuclideanSpace.single j (1 : ℝ)) i = uniform n i := by
        rw [hAe j]
      rw [toCLM_apply_coord] at h2
      simpa only [EuclideanSpace.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, uniform_apply] using h2
    · have h0 : toCLM (0 : Matrix (Fin n) (Fin n) ℝ) = 0 :=
        map_zero (Matrix.toEuclideanCLM (𝕜 := ℝ))
      rw [h0]
      simp
  · -- `λ > 0`: take `C = (1/λ)(A − (1−λ)J)` and check it contracts.
    refine ⟨lam⁻¹ • (A - (1 - lam) • unifMatrix n), ?_, ?_⟩
    · rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      abel
    · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      rw [one_mul]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · -- `n = 0`: the space is trivial, both norms vanish.
        have hz : ∀ x : EuclideanSpace ℝ (Fin 0), ‖x‖ = 0 := fun x => by
          rw [EuclideanSpace.norm_eq]
          simp
        simp [hz]
      · have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        -- Decompose `v = p + w`, `p` along `𝟙` and `w ⊥ 𝟙`.
        set p : EuclideanSpace ℝ (Fin n) :=
          ((n : ℝ) * inner ℝ v (uniform n)) • uniform n with hp_def
        set w : EuclideanSpace ℝ (Fin n) := v - p with hw_def
        have hvpw : v = p + w := by rw [hw_def, add_comm, sub_add_cancel]
        have hwu : inner ℝ w (uniform n) = 0 := by
          rw [hw_def, hp_def, inner_sub_left, real_inner_smul_left,
            inner_uniform_self, mul_comm ((n : ℝ)) _, mul_assoc,
            mul_inv_cancel₀ hne, mul_one, sub_self]
        have hsumw : (∑ j, w j) = 0 := by
          have h := hwu
          rw [inner_eq_sum] at h
          simp only [uniform_apply] at h
          rw [← Finset.sum_mul] at h
          exact (mul_eq_zero.mp h).resolve_right (inv_ne_zero hne)
        have hJw : toCLM (unifMatrix n) w = 0 := by
          refine PiLp.ext fun i => ?_
          show ∑ j, (n : ℝ)⁻¹ * w j = 0
          rw [← Finset.mul_sum, hsumw, mul_zero]
        have hJu : toCLM (unifMatrix n) (uniform n) = uniform n := by
          refine PiLp.ext fun i => ?_
          show ∑ _j : Fin n, (n : ℝ)⁻¹ * (n : ℝ)⁻¹ = (n : ℝ)⁻¹
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
        have hJp : toCLM (unifMatrix n) p = p := by rw [hp_def, map_smul, hJu]
        have hAp : toCLM A p = p := by
          rw [hp_def, map_smul, mulVec_uniform hA]
        -- `Cv = p + (1/λ)·Aw`.
        have hCv : toCLM (lam⁻¹ • (A - (1 - lam) • unifMatrix n)) v
            = p + lam⁻¹ • toCLM A w := by
          rw [toCLM_smul, toCLM_sub, toCLM_smul]
          simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
          rw [hvpw, map_add, map_add, hAp, hJp, hJw, add_zero]
          have hcomb : p + toCLM A w - (1 - lam) • p = lam • p + toCLM A w := by
            rw [sub_smul, one_smul]
            abel
          rw [hcomb, smul_add, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
        -- Orthogonality of the two components, before and after `C`.
        have hpw : inner ℝ p w = 0 := by
          rw [hp_def, real_inner_smul_left, real_inner_comm w (uniform n), hwu,
            mul_zero]
        have hpq : inner ℝ p (lam⁻¹ • toCLM A w) = 0 := by
          rw [real_inner_smul_right, hp_def, real_inner_smul_left,
            ← inner_toCLM_right hA.symm, mulVec_uniform hA,
            real_inner_comm w (uniform n), hwu]
          ring
        -- Norm bound on the orthogonal part.
        have hq_le : ‖lam⁻¹ • toCLM A w‖ ≤ ‖w‖ := by
          rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos,
            inv_mul_le_iff₀ hpos]
          exact (norm_mulVec_le_lambda hA hwu).trans
            (mul_le_mul_of_nonneg_right hlam (norm_nonneg _))
        -- Pythagoras twice.
        have hv2 : ‖v‖ ^ 2 = ‖p‖ ^ 2 + ‖w‖ ^ 2 := by
          conv_lhs => rw [hvpw]
          rw [norm_add_sq_real, hpw]
          ring
        have hC2 : ‖p + lam⁻¹ • toCLM A w‖ ^ 2 ≤ ‖v‖ ^ 2 := by
          rw [norm_add_sq_real, hpq, hv2]
          nlinarith [hq_le, norm_nonneg (lam⁻¹ • toCLM A w), norm_nonneg w]
        rw [hCv]
        calc ‖p + lam⁻¹ • toCLM A w‖
            = Real.sqrt (‖p + lam⁻¹ • toCLM A w‖ ^ 2) :=
              (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (‖v‖ ^ 2) := Real.sqrt_le_sqrt hC2
          _ = ‖v‖ := Real.sqrt_sq (norm_nonneg _)

/-- One step of the random walk from vertex `i`: move to `j` with probability
`A i j`.  For the normalized adjacency matrix of a `d`-regular multigraph
this is exactly "choose a random neighbor of `i` (with multiplicity)".
[AB09, §7.A.1] -/
noncomputable def stepPMF {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) (i : Fin n) : PMF (Fin n) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (A i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => hA.nonneg i j,
      hA.rowSum i, ENNReal.ofReal_one])

/-- The `B`-restricted transition matrix `B̂A`: row `i` of `A` where `i ∈ B`,
zero rows elsewhere.  One application advances the walk one step and kills
the probability mass outside `B`.  [AB09, proof of Thm 7.38] -/
noncomputable def resMatrix (A : Matrix (Fin n) (Fin n) ℝ) (B : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i ∈ B then A i j else 0

@[simp] theorem resMatrix_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Finset (Fin n)) (i j : Fin n) :
    resMatrix A B i j = if i ∈ B then A i j else 0 := rfl

/-- The sub-probability vector of the `B`-restricted walk: `resVec A B k j`
will be shown to equal the probability that the first `k + 1` vertices of the
walk all lie in `B` and the last one is `j` (`Expander.walk_filter_sum`).
[AB09, proof of Thm 7.38: the vector `(B̂A)^k B̂𝟙`] -/
noncomputable def resVec (A : Matrix (Fin n) (Fin n) ℝ) (B : Finset (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => (WithLp.equiv 2 (Fin n → ℝ)).symm fun j => if j ∈ B then (n : ℝ)⁻¹ else 0
  | k + 1 => toCLM (resMatrix A B) (resVec A B k)

/-- The restricted-walk vectors are entrywise nonnegative. -/
theorem resVec_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymmStochastic A)
    (B : Finset (Fin n)) : ∀ (k : ℕ) (j : Fin n), 0 ≤ resVec A B k j
  | 0, j => by
    show (0 : ℝ) ≤ if j ∈ B then (n : ℝ)⁻¹ else 0
    split
    · positivity
    · exact le_refl 0
  | k + 1, j => by
    show (0 : ℝ) ≤ ∑ l, (if j ∈ B then A j l else 0) * resVec A B k l
    refine Finset.sum_nonneg fun l _ => mul_nonneg ?_ (resVec_nonneg hA B k l)
    split
    · exact hA.nonneg j l
    · exact le_refl 0

variable [NeZero n]

omit [NeZero n] in
/-- Cauchy–Schwarz against the all-ones vector: the coordinate sum of a
Euclidean vector is at most `√n` times its `L²` norm ([AB09, Note 7.24],
the comparison `|𝐯|₁ ≤ √n·‖𝐯‖₂`, without absolute values on the left). -/
theorem sum_le_sqrt_mul_norm (x : EuclideanSpace ℝ (Fin n)) :
    ∑ j, x j ≤ Real.sqrt n * ‖x‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ => (1 : ℝ)) (fun j => x j)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  calc ∑ j, x j ≤ |∑ j, x j| := le_abs_self _
    _ = Real.sqrt ((∑ j, x j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((n : ℝ) * ∑ j, x j ^ 2) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt n * Real.sqrt (∑ j, x j ^ 2) :=
        Real.sqrt_mul (Nat.cast_nonneg _) _
    _ = Real.sqrt n * ‖x‖ := by
        have hsq : ∑ j, x j ^ 2 = ∑ j, ‖x j‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs, sq_abs]
        rw [EuclideanSpace.norm_eq, hsq]

/-- The starting vector of the restricted walk has `L²` norm at most
`√β/√n` when `|B| ≤ βn`. -/
theorem norm_resVec_zero_le {A : Matrix (Fin n) (Fin n) ℝ} {B : Finset (Fin n)}
    {β : ℝ} (hβ0 : 0 ≤ β) (hB : (B.card : ℝ) ≤ β * n) :
    ‖resVec A B 0‖ ≤ Real.sqrt β / Real.sqrt n := by
  have hn : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hsum : ∑ j, ‖resVec A B 0 j‖ ^ 2 = (B.card : ℝ) * ((n : ℝ)⁻¹) ^ 2 := by
    have hcoord : ∀ j, ‖resVec A B 0 j‖ ^ 2 =
        if j ∈ B then ((n : ℝ)⁻¹) ^ 2 else 0 := fun j => by
      show ‖(if j ∈ B then (n : ℝ)⁻¹ else 0)‖ ^ 2 = _
      split <;> simp
    rw [Finset.sum_congr rfl fun j _ => hcoord j, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hdiv : Real.sqrt β / Real.sqrt n = Real.sqrt (β * (n : ℝ)⁻¹) := by
    rw [Real.sqrt_mul hβ0, Real.sqrt_inv, div_eq_mul_inv]
  rw [EuclideanSpace.norm_eq, hsum, hdiv]
  apply Real.sqrt_le_sqrt
  calc (B.card : ℝ) * ((n : ℝ)⁻¹) ^ 2
      ≤ β * (n : ℝ) * ((n : ℝ)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right hB (by positivity)
    _ = β * ((n : ℝ) * (n : ℝ)⁻¹) * (n : ℝ)⁻¹ := by ring
    _ = β * (n : ℝ)⁻¹ := by rw [mul_inv_cancel₀ hn.ne', mul_one]

/-- The key operator estimate behind [AB09, Thm 7.38]: one `B`-restricted
step shrinks the `L²` norm by a factor `(1−λ)√β + λ`, via the decomposition
`A = (1−λ)J + λC` of [AB09, Lem 7.40]. -/
theorem norm_toCLM_resMatrix_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam β : ℝ} (hlam : lambda A ≤ lam)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {B : Finset (Fin n)}
    (hβ0 : 0 ≤ β) (hB : (B.card : ℝ) ≤ β * n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖toCLM (resMatrix A B) x‖ ≤ ((1 - lam) * Real.sqrt β + lam) * ‖x‖ := by
  classical
  have hn : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  obtain ⟨C, hdecomp, hC⟩ := exists_decomposition hA hlam hlam0
  -- Restriction distributes over the decomposition.
  have hres : resMatrix A B =
      (1 - lam) • resMatrix (unifMatrix n) B + lam • resMatrix C B := by
    ext i j
    have hij : A i j = ((1 - lam) • unifMatrix n + lam • C) i j := by
      rw [← hdecomp]
    by_cases h : i ∈ B <;>
      simp [h, hij, Matrix.add_apply, Matrix.smul_apply, unifMatrix,
        smul_eq_mul]
  -- Restriction never increases the norm of a matrix–vector product.
  have hrestrict : ∀ (M : Matrix (Fin n) (Fin n) ℝ)
      (y : EuclideanSpace ℝ (Fin n)),
      ‖toCLM (resMatrix M B) y‖ ≤ ‖toCLM M y‖ := fun M y => by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum fun i _ => ?_
    have hcoord : toCLM (resMatrix M B) y i =
        if i ∈ B then toCLM M y i else 0 := by
      rw [toCLM_apply_coord, toCLM_apply_coord]
      by_cases h : i ∈ B
      · rw [if_pos h]
        exact Finset.sum_congr rfl fun j _ => by rw [resMatrix_apply, if_pos h]
      · rw [if_neg h]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [resMatrix_apply, if_neg h, zero_mul]
    rw [hcoord]
    by_cases h : i ∈ B
    · rw [if_pos h]
    · rw [if_neg h]
      simpa using sq_nonneg ‖toCLM M y i‖
  -- The uniform part: `‖B̂J𝐲‖ ≤ √β‖𝐲‖`.
  have hJ : ∀ y : EuclideanSpace ℝ (Fin n),
      ‖toCLM (resMatrix (unifMatrix n) B) y‖ ≤ Real.sqrt β * ‖y‖ := fun y => by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ => (1 : ℝ)) (fun j => y j)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
    have hcoord : ∀ i, toCLM (resMatrix (unifMatrix n) B) y i =
        if i ∈ B then (n : ℝ)⁻¹ * ∑ j, y j else 0 := fun i => by
      rw [toCLM_apply_coord]
      by_cases h : i ∈ B
      · rw [if_pos h, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [resMatrix_apply, if_pos h]
        rfl
      · rw [if_neg h]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [resMatrix_apply, if_neg h, zero_mul]
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
      show Real.sqrt β * Real.sqrt (∑ j, ‖y j‖ ^ 2) =
        Real.sqrt (β * ∑ j, ‖y j‖ ^ 2) from (Real.sqrt_mul hβ0 _).symm]
    apply Real.sqrt_le_sqrt
    have hsq : ∀ j, ‖y j‖ ^ 2 = y j ^ 2 := fun j => by
      rw [Real.norm_eq_abs, sq_abs]
    calc ∑ i, ‖toCLM (resMatrix (unifMatrix n) B) y i‖ ^ 2
        = ∑ i, (if i ∈ B then ((n : ℝ)⁻¹ * ∑ j, y j) ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcoord i]
          split
          · rw [Real.norm_eq_abs, sq_abs]
          · simp
      _ = (B.card : ℝ) * ((n : ℝ)⁻¹ * ∑ j, y j) ^ 2 := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
            nsmul_eq_mul]
      _ ≤ β * (n : ℝ) * ((n : ℝ)⁻¹ * ∑ j, y j) ^ 2 :=
          mul_le_mul_of_nonneg_right hB (sq_nonneg _)
      _ = β * ((n : ℝ) * (n : ℝ)⁻¹) * ((n : ℝ)⁻¹ * (∑ j, y j) ^ 2) := by
          ring
      _ = β * ((n : ℝ)⁻¹ * (∑ j, y j) ^ 2) := by
          rw [mul_inv_cancel₀ hn.ne', mul_one]
      _ ≤ β * ((n : ℝ)⁻¹ * ((n : ℝ) * ∑ j, y j ^ 2)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hcs (by positivity)) hβ0
      _ = β * (((n : ℝ)⁻¹ * (n : ℝ)) * ∑ j, y j ^ 2) := by ring
      _ = β * ∑ j, ‖y j‖ ^ 2 := by
          rw [inv_mul_cancel₀ hn.ne', one_mul]
          exact congrArg _ (Finset.sum_congr rfl fun j _ => (hsq j).symm)
  -- Assemble by the triangle inequality.
  have hCb : ∀ y : EuclideanSpace ℝ (Fin n),
      ‖toCLM (resMatrix C B) y‖ ≤ 1 * ‖y‖ := fun y => by
    rw [one_mul]
    refine (hrestrict C y).trans (((toCLM C).le_opNorm y).trans ?_)
    calc ‖toCLM C‖ * ‖y‖
        ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hC (norm_nonneg _)
      _ = ‖y‖ := one_mul _
  calc ‖toCLM (resMatrix A B) x‖
      = ‖(1 - lam) • toCLM (resMatrix (unifMatrix n) B) x +
          lam • toCLM (resMatrix C B) x‖ := by
        rw [hres, toCLM_add, toCLM_smul, toCLM_smul]
        simp only [ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply]
    _ ≤ ‖(1 - lam) • toCLM (resMatrix (unifMatrix n) B) x‖ +
          ‖lam • toCLM (resMatrix C B) x‖ := norm_add_le _ _
    _ = (1 - lam) * ‖toCLM (resMatrix (unifMatrix n) B) x‖ +
          lam * ‖toCLM (resMatrix C B) x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam), abs_of_nonneg hlam0]
    _ ≤ (1 - lam) * (Real.sqrt β * ‖x‖) + lam * (1 * ‖x‖) := by
        have h1 := hJ x
        have h2 := hCb x
        have h3 : (0:ℝ) ≤ 1 - lam := by linarith
        exact add_le_add (mul_le_mul_of_nonneg_left h1 h3)
          (mul_le_mul_of_nonneg_left h2 hlam0)
    _ = ((1 - lam) * Real.sqrt β + lam) * ‖x‖ := by ring

/-- Iterating the one-step estimate:
`‖(B̂A)^k B̂𝟙‖ ≤ ((1−λ)√β + λ)^k · ‖B̂𝟙‖`. -/
theorem norm_resVec_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam β : ℝ} (hlam : lambda A ≤ lam)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {B : Finset (Fin n)}
    (hβ0 : 0 ≤ β) (hB : (B.card : ℝ) ≤ β * n) (k : ℕ) :
    ‖resVec A B k‖ ≤
      ((1 - lam) * Real.sqrt β + lam) ^ k * ‖resVec A B 0‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hbase0 : 0 ≤ (1 - lam) * Real.sqrt β + lam :=
      add_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) hlam0
    calc ‖resVec A B (k + 1)‖
        = ‖toCLM (resMatrix A B) (resVec A B k)‖ := rfl
      _ ≤ ((1 - lam) * Real.sqrt β + lam) * ‖resVec A B k‖ :=
          norm_toCLM_resMatrix_le hA hlam hlam0 hlam1 hβ0 hB _
      _ ≤ ((1 - lam) * Real.sqrt β + lam) *
            (((1 - lam) * Real.sqrt β + lam) ^ k * ‖resVec A B 0‖) :=
          mul_le_mul_of_nonneg_left ih hbase0
      _ = ((1 - lam) * Real.sqrt β + lam) ^ (k + 1) * ‖resVec A B 0‖ := by
          ring

/-- The `k`-step random walk driven by `A`, started at a uniformly random
vertex: a probability distribution on the `k+1` visited vertices
`X₀, X₁, …, X_k` (the book's `X₁, …, X_k` with `k` vertices and `k−1` steps).
[AB09, Thm 7.38] -/
noncomputable def walkPMF {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) : (k : ℕ) → PMF (Fin (k + 1) → Fin n)
  | 0 => (PMF.uniformOfFintype (Fin n)).map fun v _ => v
  | k + 1 => (walkPMF hA k).bind fun f =>
      (stepPMF hA (f (Fin.last k))).map fun j => Fin.snoc f j

/-- The walk of length `0` is the uniform distribution on single vertices:
every one-vertex trajectory has probability `1/n`. -/
theorem walkPMF_zero_apply {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) (f : Fin 1 → Fin n) :
    walkPMF hA 0 f = (n : ℝ≥0∞)⁻¹ := by
  have hf : f = fun _ => f 0 := funext fun i => by rw [Subsingleton.elim i 0]
  show ((PMF.uniformOfFintype (Fin n)).map fun v _ => v) f = _
  rw [PMF.map_apply]
  refine (tsum_eq_single (L := SummationFilter.unconditional _) (f 0)
    fun v hv => ?_).trans ?_
  · exact if_neg fun h => hv (congrFun h 0).symm
  · rw [if_pos hf, PMF.uniformOfFintype_apply, Fintype.card_fin]

/-- Splitting off the last step of a walk: the probability of the trajectory
`g ⌢ j` is the probability of `g` times the transition probability from the
endpoint of `g` to `j`. -/
theorem walkPMF_succ_apply {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) (k : ℕ) (g : Fin (k + 1) → Fin n) (j : Fin n) :
    walkPMF hA (k + 1) (Fin.snoc g j) =
      walkPMF hA k g * ENNReal.ofReal (A (g (Fin.last k)) j) := by
  show ((walkPMF hA k).bind fun f =>
      (stepPMF hA (f (Fin.last k))).map fun j' =>
        (Fin.snoc f j' : Fin (k + 2) → Fin n))
      (Fin.snoc g j) = _
  rw [PMF.bind_apply]
  have hoff : ∀ g' : Fin (k + 1) → Fin n, g' ≠ g →
      walkPMF hA k g' *
        ((stepPMF hA (g' (Fin.last k))).map fun j' =>
          (Fin.snoc g' j' : Fin (k + 2) → Fin n)) (Fin.snoc g j) = 0 :=
      fun g' hg' => by
    have h2 : ((stepPMF hA (g' (Fin.last k))).map fun j' =>
        (Fin.snoc g' j' : Fin (k + 2) → Fin n)) (Fin.snoc g j) = 0 := by
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.mpr fun j' => if_neg fun h => hg' ?_
      have h3 := congrArg Fin.init h
      rw [Fin.init_snoc, Fin.init_snoc] at h3
      exact h3.symm
    rw [h2, mul_zero]
  rw [tsum_eq_single g hoff]
  congr 1
  rw [PMF.map_apply]
  refine (tsum_eq_single (L := SummationFilter.unconditional _) j
    fun j' hj' => ?_).trans ?_
  · refine if_neg fun h => hj' ?_
    have h2 := congrArg (fun f => f (Fin.last (k + 1))) h
    simp only [Fin.snoc_last] at h2
    exact h2.symm
  · rw [if_pos rfl]
    rfl

/-- The probability that the walk stays inside `B` and ends at `j` is the
`j`-th entry of the restricted-walk vector `resVec A B k`:
in matrix language, of `(B̂A)^k B̂𝟙`.  [AB09, proof of Thm 7.38] -/
theorem walk_filter_sum {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) (B : Finset (Fin n)) :
    ∀ (k : ℕ) (j : Fin n),
      (∑ f ∈ Finset.univ.filter
          (fun f : Fin (k + 1) → Fin n =>
            (∀ i, f i ∈ B) ∧ f (Fin.last k) = j),
        walkPMF hA k f) = ENNReal.ofReal (resVec A B k j)
  | 0, j => by
    classical
    have hn : (0 : ℝ) < n :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
    by_cases hj : j ∈ B
    · have hfilter : Finset.univ.filter
          (fun f : Fin 1 → Fin n =>
            (∀ i, f i ∈ B) ∧ f (Fin.last 0) = j) = {fun _ => j} := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · rintro ⟨-, hlast⟩
          exact funext fun i => by rw [Subsingleton.elim i (Fin.last 0), hlast]
        · rintro rfl
          exact ⟨fun _ => hj, rfl⟩
      have hres : resVec A B 0 j = (n : ℝ)⁻¹ := by
        show (if j ∈ B then (n : ℝ)⁻¹ else 0) = _
        rw [if_pos hj]
      rw [hfilter, Finset.sum_singleton, walkPMF_zero_apply hA, hres,
        ENNReal.ofReal_inv_of_pos hn, ENNReal.ofReal_natCast]
    · have hfilter : Finset.univ.filter
          (fun f : Fin 1 → Fin n =>
            (∀ i, f i ∈ B) ∧ f (Fin.last 0) = j) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        exact fun f _ => fun ⟨hall, hlast⟩ => hj (hlast ▸ hall (Fin.last 0))
      have hres : resVec A B 0 j = 0 := by
        show (if j ∈ B then (n : ℝ)⁻¹ else 0) = 0
        rw [if_neg hj]
      rw [hfilter, hres, Finset.sum_empty, ENNReal.ofReal_zero]
  | k + 1, j => by
    classical
    by_cases hj : j ∈ B
    · have hsnoc_mem : ∀ (g : Fin (k + 1) → Fin n) (x : Fin n),
          (∀ i, (Fin.snoc g x : Fin (k + 2) → Fin n) i ∈ B) ↔
            (∀ i, g i ∈ B) ∧ x ∈ B := fun g x => by
        constructor
        · intro h
          refine ⟨fun i => ?_, ?_⟩
          · have h2 := h i.castSucc
            rwa [Fin.snoc_castSucc] at h2
          · have h2 := h (Fin.last _)
            rwa [Fin.snoc_last] at h2
        · rintro ⟨hg, hx⟩ i
          refine Fin.lastCases ?_ (fun i' => ?_) i
          · rwa [Fin.snoc_last]
          · rw [Fin.snoc_castSucc]
            exact hg i'
      rw [Finset.sum_filter,
        ← Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin n)
          (fun p => if (∀ i, (Fin.snoc p.2 p.1 : Fin (k + 2) → Fin n) i ∈ B) ∧
              (Fin.snoc p.2 p.1 : Fin (k + 2) → Fin n) (Fin.last (k + 1)) = j
            then walkPMF hA (k + 1) (Fin.snoc p.2 p.1) else 0)
          (fun f => if (∀ i, f i ∈ B) ∧ f (Fin.last (k + 1)) = j
            then walkPMF hA (k + 1) f else 0)
          (fun p => rfl),
        Fintype.sum_prod_type]
      simp only [Fin.snoc_last, hsnoc_mem, walkPMF_succ_apply hA]
      rw [Finset.sum_eq_single j
        (fun x _ hx => Finset.sum_eq_zero fun g _ => if_neg fun hc => hx hc.2)
        (fun h => absurd (Finset.mem_univ j) h)]
      simp only [hj, and_true]
      rw [← Finset.sum_filter,
        ← Finset.sum_fiberwise
          (Finset.univ.filter fun g : Fin (k + 1) → Fin n => ∀ i, g i ∈ B)
          (fun g => g (Fin.last k))
          (fun g => walkPMF hA k g *
            ENNReal.ofReal (A (g (Fin.last k)) j))]
      have hfiber : ∀ l : Fin n,
          (∑ g ∈ (Finset.univ.filter
              fun g : Fin (k + 1) → Fin n => ∀ i, g i ∈ B).filter
              (fun g => g (Fin.last k) = l),
            walkPMF hA k g * ENNReal.ofReal (A (g (Fin.last k)) j))
            = ENNReal.ofReal (resVec A B k l) *
                ENNReal.ofReal (A l j) := fun l => by
        rw [Finset.filter_filter]
        calc (∑ g ∈ Finset.univ.filter
                (fun g : Fin (k + 1) → Fin n =>
                  (∀ i, g i ∈ B) ∧ g (Fin.last k) = l),
              walkPMF hA k g * ENNReal.ofReal (A (g (Fin.last k)) j))
            = ∑ g ∈ Finset.univ.filter
                (fun g : Fin (k + 1) → Fin n =>
                  (∀ i, g i ∈ B) ∧ g (Fin.last k) = l),
              walkPMF hA k g * ENNReal.ofReal (A l j) :=
              Finset.sum_congr rfl fun g hg => by
                rw [(Finset.mem_filter.mp hg).2.2]
          _ = (∑ g ∈ Finset.univ.filter
                (fun g : Fin (k + 1) → Fin n =>
                  (∀ i, g i ∈ B) ∧ g (Fin.last k) = l),
              walkPMF hA k g) * ENNReal.ofReal (A l j) :=
              (Finset.sum_mul ..).symm
          _ = ENNReal.ofReal (resVec A B k l) * ENNReal.ofReal (A l j) := by
              rw [walk_filter_sum hA B k l]
      rw [Finset.sum_congr rfl fun l _ => hfiber l,
        Finset.sum_congr rfl fun l _ =>
          (ENNReal.ofReal_mul (resVec_nonneg hA B k l)).symm,
        ← ENNReal.ofReal_sum_of_nonneg fun l _ =>
          mul_nonneg (resVec_nonneg hA B k l) (hA.nonneg l j)]
      congr 1
      show ∑ l, resVec A B k l * A l j =
        ∑ l, (if j ∈ B then A j l else 0) * resVec A B k l
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [if_pos hj, hA.symm.apply j l]
      ring
    · have hfilter : Finset.univ.filter
          (fun f : Fin (k + 2) → Fin n =>
            (∀ i, f i ∈ B) ∧ f (Fin.last (k + 1)) = j) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        exact fun f _ => fun ⟨hall, hlast⟩ =>
          hj (hlast ▸ hall (Fin.last (k + 1)))
      have hres : resVec A B (k + 1) j = 0 := by
        show ∑ l, (if j ∈ B then A j l else 0) * resVec A B k l = 0
        refine Finset.sum_eq_zero fun l _ => ?_
        rw [if_neg hj, zero_mul]
      rw [hfilter, hres, Finset.sum_empty, ENNReal.ofReal_zero]

/-- **Expander walks** ([AB09, Thm 7.38]).  Let `A` be symmetric stochastic
with `λ(A) ≤ λ` (for a graph: an `(N,d,λ)`-graph), and let `B` be a set of at
most `βN` vertices.  The probability that a uniformly-started `k`-step random
walk stays inside `B` for all of its `k+1` visited vertices is at most
`((1−λ)√β + λ)^k`.

(The book's statement, with `k` visited vertices, has exponent `k−1`; note
that if `λ, β < 1` are constants then so is `(1−λ)√β + λ`.  The hypothesis
`lam ≤ 1` makes explicit the `λ < 1` of the book's `(N,d,λ)`-graph
[AB09, Def 7.31]; without it the base `(1−λ)√β + λ` can be negative and the
bound false.)

**Proof sketch.** If `β ≥ 1` the bound is trivial: `lam ≤ 1` makes the base
`(1−λ)√β + λ ≥ (1−λ) + λ = 1`, so the right-hand side is at least `1` and
every probability qualifies.  So assume `β < 1`.  With `B̂` the diagonal
projection that zeroes coordinates outside `B`, the probability equals
`|(B̂A)^k B̂𝟙|₁`.  By Lemma 7.40, `B̂A = B̂((1−λ)J + λC)`, so
`‖B̂A‖ ≤ (1−λ)‖B̂J‖ + λ‖B̂C‖ ≤ (1−λ)√β + λ`, since `J`'s image consists of
uniform vectors of which `B̂` keeps `|B| ≤ βN` coordinates, and
`‖B̂‖, ‖C‖ ≤ 1`.  As `‖B̂𝟙‖₂ = √|B|/N ≤ √β/√N` (the hypothesis `hB` is an
inequality, not an equality), we get
`‖(B̂A)^k B̂𝟙‖₂ ≤ ((1−λ)√β + λ)^k √β/√N`, and `|𝐯|₁ ≤ √N ‖𝐯‖₂`
(Note 7.24) concludes, dropping the extra factor `√β`, which is `≤ 1` in
the case `β < 1` under consideration. -/
theorem walk_all_mem_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam : ℝ} (hlam : lambda A ≤ lam)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {B : Finset (Fin n)} {β : ℝ}
    (hβ0 : 0 ≤ β) (hB : (B.card : ℝ) ≤ β * n) (k : ℕ) :
    (walkPMF hA k).toMeasure {f | ∀ i, f i ∈ B} ≤
      ENNReal.ofReal (((1 - lam) * Real.sqrt β + lam) ^ k) := by
  classical
  have hn : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hbase0 : 0 ≤ (1 - lam) * Real.sqrt β + lam :=
    add_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) hlam0
  rcases le_or_gt 1 β with hβ1 | hβ1
  · -- `β ≥ 1`: the base is at least `1`, so any probability qualifies.
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt β := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hβ1
    have hb1 : (1 : ℝ) ≤ (1 - lam) * Real.sqrt β + lam := by
      have h := mul_le_mul_of_nonneg_left hsqrt1
        (by linarith : (0 : ℝ) ≤ 1 - lam)
      linarith
    have hbk : (1 : ℝ) ≤ ((1 - lam) * Real.sqrt β + lam) ^ k :=
      one_le_pow₀ hb1
    calc (walkPMF hA k).toMeasure {f | ∀ i, f i ∈ B}
        ≤ 1 := MeasureTheory.prob_le_one
      _ ≤ ENNReal.ofReal (((1 - lam) * Real.sqrt β + lam) ^ k) := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hbk
  · -- `β < 1`: the `L²` estimate via the restricted-walk vectors.
    have hset : {f : Fin (k + 1) → Fin n | ∀ i, f i ∈ B} =
        ↑(Finset.univ.filter fun f : Fin (k + 1) → Fin n =>
          ∀ i, f i ∈ B) := by
      ext f
      simp
    rw [hset, PMF.toMeasure_apply_finset,
      ← Finset.sum_fiberwise
        (Finset.univ.filter fun f : Fin (k + 1) → Fin n => ∀ i, f i ∈ B)
        (fun f => f (Fin.last k)) (fun f => walkPMF hA k f)]
    have hfib : ∀ j : Fin n,
        (∑ f ∈ (Finset.univ.filter
            fun f : Fin (k + 1) → Fin n => ∀ i, f i ∈ B).filter
            (fun f => f (Fin.last k) = j), walkPMF hA k f)
          = ENNReal.ofReal (resVec A B k j) := fun j => by
      rw [Finset.filter_filter]
      exact walk_filter_sum hA B k j
    rw [Finset.sum_congr rfl fun j _ => hfib j,
      ← ENNReal.ofReal_sum_of_nonneg fun j _ => resVec_nonneg hA B k j]
    apply ENNReal.ofReal_le_ofReal
    have hsqrtn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn
    have hβle : Real.sqrt β ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hβ1.le
    calc ∑ j, resVec A B k j
        ≤ Real.sqrt n * ‖resVec A B k‖ := sum_le_sqrt_mul_norm _
      _ ≤ Real.sqrt n *
            (((1 - lam) * Real.sqrt β + lam) ^ k * ‖resVec A B 0‖) :=
          mul_le_mul_of_nonneg_left
            (norm_resVec_le hA hlam hlam0 hlam1 hβ0 hB k) hsqrtn.le
      _ ≤ Real.sqrt n * (((1 - lam) * Real.sqrt β + lam) ^ k *
            (Real.sqrt β / Real.sqrt n)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_resVec_zero_le hβ0 hB)
              (pow_nonneg hbase0 k)) hsqrtn.le
      _ = ((1 - lam) * Real.sqrt β + lam) ^ k * Real.sqrt β := by
          field_simp
      _ ≤ ((1 - lam) * Real.sqrt β + lam) ^ k * 1 :=
          mul_le_mul_of_nonneg_left hβle (pow_nonneg hbase0 k)
      _ = ((1 - lam) * Real.sqrt β + lam) ^ k := mul_one _

end Expander
```

## ===== TCSlib/Complexity/Expanders/Chernoff.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Expanders.Walks

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Expander Chernoff Bound

Arora–Barak's Theorem 7.41: the fraction of time a random walk on an expander
spends inside a set `B` of density `β` concentrates around `β`, with the same
exponential decay (up to the spectral gap factor `1−λ`) as for independent
samples.  This is the tool behind randomness-efficient error reduction for
*two-sided* error algorithms (run the algorithm on the `k` coin strings
visited by a walk and take the majority).

## Main results (intentionally statement-only)

* `Expander.walk_visits_concentration` — [AB09, Thm 7.41].

## Deviations from the source

* As in `Expanders.Walks`, our walk `walkPMF hA k` visits `k+1` vertices
  (the book's `X₁,…,X_k` has `k` vertices), so `k+1` replaces the book's `k`.
* **Erratum.** The draft prints the bound as `2e^{(1−λ)δ²k/60}`, with a
  positive exponent, which is vacuous; the intended bound (cf. Gillman,
  *A Chernoff bound for random walks on expander graphs*, SIAM J. Comput.
  1998) is `2e^{−(1−λ)δ²k/60}`.  We state it with the negative exponent.
* The book's proof is omitted ("whose proof we omit"), so the eventual proof
  here will follow an external source rather than [AB09].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [Gil98] D. Gillman, *A Chernoff bound for random walks on expander graphs*,
  SIAM Journal on Computing 27(4), 1998.
-/

namespace Expander

open Matrix

variable {n : ℕ} [NeZero n]

/-- **Expander Chernoff Bound** ([AB09, Thm 7.41]).  Let `A` be symmetric
stochastic with `λ(A) ≤ λ` (for a graph: an `(N,d,λ)`-graph) and `B` a set of
exactly `βN` vertices.  For a uniformly-started `k`-step random walk visiting
`X₀, …, X_k`, let `Bᵢ` be the indicator that `Xᵢ ∈ B`.  Then for every
`δ > 0`,

`Pr[ |(Σᵢ Bᵢ)/(k+1) − β| > δ ] < 2·exp(−(1−λ)δ²(k+1)/60)`.

The draft's positive exponent is a typo; see the module docstring.

**Proof sketch** (omitted in [AB09]; after [Gil98]): bound the moment
generating function `E[exp(t·Σᵢ Bᵢ)]` by the largest eigenvalue of the
perturbed transition operator `A·exp(t·B̂)`, control that eigenvalue via the
spectral gap `1−λ` using first-order perturbation theory, and conclude by the
exponential Markov inequality applied to both tails. -/
theorem walk_visits_concentration {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsSymmStochastic A) {lam : ℝ} (hlam : lambda A ≤ lam)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {B : Finset (Fin n)} {β δ : ℝ}
    (hB : (B.card : ℝ) = β * n) (hδ : 0 < δ) (k : ℕ) :
    (walkPMF hA k).toMeasure
        {f | δ < |(∑ i, if f i ∈ B then (1 : ℝ) else 0) / (k + 1) - β|} <
      ENNReal.ofReal (2 * Real.exp (-((1 - lam) * δ ^ 2 * (k + 1)) / 60)) := by
  sorry

end Expander
```

## ===== TCSlib/Complexity/Randomized/SchwartzZippel.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Schwartz–Zippel lemma, Arora–Barak form

Arora–Barak's Lemma 7.5, the probabilistic tool behind polynomial identity
testing: a nonzero integer polynomial of total degree at most `d` evaluates
to a nonzero value with probability at least `1 − d/|S|` when its arguments
are drawn independently and uniformly from a finite set of integers `S`.

Mathlib already proves the core inequality
(`MvPolynomial.schwartz_zippel_totalDegree`, over any integral domain, in the
sharp "count the zeros" form); this file only restates it in the book's form,
so the lemma is *reused*, not re-proved.

## Main results

* `Randomized.schwartz_zippel` — [AB09, Lem 7.5].

## Deviations from the source

* [AB09, Lem 7.5] samples `a₁, …, a_m` "randomly with replacement from `S`"
  and bounds `Pr[p(a₁,…,a_m) ≠ 0] ≥ 1 − d/|S|`.  Uniform sampling with
  replacement of the tuple is the uniform distribution on `S^m`, so the
  probability is the counting ratio `#{a ∈ S^m | p(a) ≠ 0} / |S|^m`; we state
  the bound as that ratio, valued in `ℚ≥0` (with truncated subtraction, which
  makes the statement trivially true — and still correct — when `d ≥ |S|`).
* The book leaves implicit that `p` is not the zero polynomial (otherwise the
  claim fails); `hp` makes this explicit.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open MvPolynomial Finset Fintype

/-- **Schwartz–Zippel lemma** ([AB09, Lem 7.5]).  Let `p(x₁,…,x_m)` be a
nonzero integer polynomial of total degree at most `d` and `S` a nonempty
finite set of integers.  When `a₁,…,a_m` are chosen independently and
uniformly from `S`, then `Pr[p(a₁,…,a_m) ≠ 0] ≥ 1 − d/|S|`, stated as the
counting ratio over all of `S^m`.

**Proof sketch.** The complementary count is
`MvPolynomial.schwartz_zippel_totalDegree`:
`#{a ∈ S^m | p(a) = 0}/|S|^m ≤ totalDegree p/|S| ≤ d/|S|`; subtract from `1`
and split `S^m` into zeros and non-zeros of `p`. -/
theorem schwartz_zippel {m : ℕ} {p : MvPolynomial (Fin m) ℤ} (hp : p ≠ 0)
    {d : ℕ} (hd : p.totalDegree ≤ d) (S : Finset ℤ) (hS : S.Nonempty) :
    (1 : ℚ≥0) - d / S.card ≤
      ({f ∈ piFinset fun _ : Fin m => S | eval f p ≠ 0}.card : ℚ≥0) /
        (S.card ^ m : ℚ≥0) := by
  have hS0 : (0 : ℚ≥0) < (S.card : ℚ≥0) := by exact_mod_cast hS.card_pos
  have hT : (0 : ℚ≥0) < (S.card : ℚ≥0) ^ m := pow_pos hS0 m
  have hmain : ({f ∈ piFinset fun _ : Fin m => S | eval f p = 0}.card : ℚ≥0) /
      (S.card ^ m : ℚ≥0) ≤ (d : ℚ≥0) / S.card :=
    (MvPolynomial.schwartz_zippel_totalDegree hp S).trans
      (by gcongr)
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := piFinset fun _ : Fin m => S) (p := fun f => eval f p = 0)
  have hpi : (piFinset fun _ : Fin m => S).card = S.card ^ m := by
    simp [Fintype.card_piFinset]
  have hNZ : {f ∈ piFinset fun _ : Fin m => S | eval f p ≠ 0}.card
      + {f ∈ piFinset fun _ : Fin m => S | eval f p = 0}.card
      = S.card ^ m := by
    have h2 : {f ∈ piFinset fun _ : Fin m => S | eval f p = 0}.card
        + {f ∈ piFinset fun _ : Fin m => S | eval f p ≠ 0}.card
        = S.card ^ m := by
      rw [← hpi]
      simpa using hsplit
    omega
  have hcount : ({f ∈ piFinset fun _ : Fin m => S | eval f p ≠ 0}.card : ℚ≥0)
      = (S.card : ℚ≥0) ^ m -
        ({f ∈ piFinset fun _ : Fin m => S | eval f p = 0}.card : ℚ≥0) :=
    eq_tsub_of_add_eq (by exact_mod_cast hNZ)
  rw [hcount, tsub_div, div_self hT.ne']
  exact tsub_le_tsub_left hmain 1

end Randomized
```

## ===== TCSlib/Complexity/Randomized/ErrorReduction.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Error reduction by repetition: the Chernoff core

The probabilistic heart of Arora–Barak's error-reduction theorem
([AB09, Thm 7.10]): run `k` independent trials of a decision procedure that
is correct with probability `p ≥ 1/2 + ε` and take the majority; the
probability that the majority is wrong is exponentially small in `k`.

This file states the machine-independent core over i.i.d. Bernoulli random
variables: the Chernoff-type concentration bound [AB09, Cor 7.11] and the
majority-vote error bound instantiating [AB09, Thm 7.10]'s calculation.
Wrapping these into statements about `BPP`-style verifier classes is Tier B
work and lives elsewhere.

## Main results

* `Randomized.iid_bernoulli_avg_concentration` — [AB09, Cor 7.11], with a
  corrected constant (see **Deviations**).
* `Randomized.majority_error_le` — the calculation proving [AB09, Thm 7.10].
* `Randomized.iidBernoulli_tail_le` — the shared one-sided Hoeffding bound,
  from Mathlib's sub-Gaussian machinery
  (`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`).

## Deviations from the source

* [AB09, Cor 7.11] is stated for abstract i.i.d. Boolean random variables
  `X₁,…,X_k` with `Pr[Xᵢ = 1] = p`; we realize them concretely as the product
  measure of `k` Bernoulli(`p`) distributions on `Fin k → Bool`, which is the
  same joint distribution.
* **Erratum.** [AB09, Cor 7.11] prints the bound
  `Pr[|(1/k)ΣXᵢ − p| > δ] < e^{−(δ²/4)pk}`, which is false: for a single
  trial (`k = 1`) with `p = 1/2` and `δ = 1/4`, the deviation event has
  probability `1` while the claimed bound is `e^{−1/128} < 1`.  We state the
  standard two-sided Hoeffding bound `≤ 2·e^{−2δ²k}` instead, which is what
  the error-reduction argument needs.
* [AB09, Thm 7.10] is stated for polynomial-time PTMs, with
  `p = 1/2 + |x|^{−c}` and final bound `2^{−|x|^d}`; `majority_error_le` is
  its probabilistic content with `ε` in place of `|x|^{−c}`: the one-sided
  Hoeffding bound gives majority error at most `e^{−2ε²k}`, which for
  `k = Θ((n+1)^{2c+d})` is at most `2^{−(n+1)^d}`.  The book's displayed
  intermediate step normalizes the sum by `1/n` where `1/k` is meant; we
  state it with `1/k`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open MeasureTheory
open scoped NNReal ENNReal

/-- The joint distribution of `k` independent Bernoulli(`p`) trials, as a
measure on `Fin k → Bool`.  [AB09, Cor 7.11: "independent identically
distributed Boolean random variables"] -/
noncomputable def iidBernoulli (k : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    Measure (Fin k → Bool) :=
  Measure.pi fun _ => (PMF.bernoulli p hp).toMeasure

/-- The number of successes among the `k` trials `ω`, as a real number. -/
def successCount {k : ℕ} (ω : Fin k → Bool) : ℝ :=
  ∑ i, if ω i then (1 : ℝ) else 0

instance isProbabilityMeasure_iidBernoulli (k : ℕ) (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (iidBernoulli k p hp) := by
  unfold iidBernoulli
  infer_instance

/-- The indicator of success in the `i`-th trial, as a real random variable. -/
def coordIndicator (k : ℕ) (i : Fin k) (ω : Fin k → Bool) : ℝ :=
  if ω i then 1 else 0

theorem measurable_coordIndicator {k : ℕ} (i : Fin k) :
    Measurable (coordIndicator k i) := by
  unfold coordIndicator
  exact (Measurable.of_discrete (f := fun b : Bool => if b then (1 : ℝ) else 0)).comp
    (measurable_pi_apply i)

/-- Under the i.i.d. Bernoulli measure, each trial succeeds with
probability `p` in expectation. -/
theorem integral_coordIndicator {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ} (i : Fin k) :
    ∫ ω, coordIndicator k i ω ∂(iidBernoulli k p hp) = (p : ℝ) := by
  have hmp : MeasurePreserving (Function.eval i) (iidBernoulli k p hp)
      ((PMF.bernoulli p hp).toMeasure) :=
    measurePreserving_eval
      (μ := fun _ : Fin k => (PMF.bernoulli p hp).toMeasure) i
  have hmap := integral_map (φ := Function.eval i) (μ := iidBernoulli k p hp)
    (f := fun b : Bool => if b then (1 : ℝ) else 0)
    (measurable_pi_apply i).aemeasurable
    Measurable.of_discrete.aestronglyMeasurable
  calc ∫ ω, coordIndicator k i ω ∂(iidBernoulli k p hp)
      = ∫ b, (if b then (1 : ℝ) else 0)
          ∂(Measure.map (Function.eval i) (iidBernoulli k p hp)) := hmap.symm
    _ = ∫ b, (if b then (1 : ℝ) else 0) ∂((PMF.bernoulli p hp).toMeasure) := by
        rw [hmp.map_eq]
    _ = (p : ℝ) := by
        simp only [← Bool.cond_eq_ite]
        exact PMF.bernoulli_expectation hp

theorem integrable_coordIndicator {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ} (i : Fin k) :
    Integrable (coordIndicator k i) (iidBernoulli k p hp) :=
  Integrable.of_mem_Icc 0 1 (measurable_coordIndicator i).aemeasurable
    (MeasureTheory.ae_of_all _ fun ω => by
      unfold coordIndicator
      split <;> norm_num)

/-- The trial indicators are independent under the product measure. -/
theorem iIndepFun_coordIndicator {p : ℝ≥0} (hp : p ≤ 1) (k : ℕ) :
    ProbabilityTheory.iIndepFun (coordIndicator k) (iidBernoulli k p hp) :=
  ProbabilityTheory.iIndepFun_pi
    (X := fun _ : Fin k => fun b : Bool => if b then (1 : ℝ) else 0)
    (μ := fun _ : Fin k => (PMF.bernoulli p hp).toMeasure)
    fun _ => Measurable.of_discrete.aemeasurable

/-- Hoeffding's lemma for a centered trial: `Xᵢ − p` is sub-Gaussian with
parameter `(1/2)² = 1/4`. -/
theorem hasSubgaussianMGF_coordIndicator_sub {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ}
    (i : Fin k) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun ω => coordIndicator k i ω - (p : ℝ)) ((1 / 2 : ℝ≥0) ^ 2)
      (iidBernoulli k p hp) := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.coe_nonneg
  have hp1 : (p : ℝ) ≤ 1 := hp
  have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := iidBernoulli k p hp)
    (X := fun ω => coordIndicator k i ω - (p : ℝ))
    (a := -(p : ℝ)) (b := 1 - (p : ℝ))
    ((measurable_coordIndicator i).sub_const _).aemeasurable
    (MeasureTheory.ae_of_all _ fun ω => by
      have hbeta : (fun ω : Fin k → Bool => coordIndicator k i ω - (p : ℝ)) ω
          = (if ω i then (1 : ℝ) else 0) - p := rfl
      rw [hbeta, Set.mem_Icc]
      by_cases h : ω i
      · rw [if_pos h]
        constructor <;> linarith
      · rw [if_neg h]
        constructor <;> linarith)
    (by
      rw [integral_sub (integrable_coordIndicator hp i) (integrable_const _),
        integral_coordIndicator hp, integral_const]
      simp)
  have h2 : ((‖(1 - (p : ℝ)) - -(p : ℝ)‖₊ / 2 : ℝ≥0) ^ 2) = (1 / 2 : ℝ≥0) ^ 2 := by
    rw [show (1 - (p : ℝ)) - -(p : ℝ) = 1 from by ring, nnnorm_one]
  rw [← h2]
  exact h

/-- Hoeffding's lemma for the reflected centered trial: `p − Xᵢ` is
sub-Gaussian with parameter `(1/2)² = 1/4`. -/
theorem hasSubgaussianMGF_sub_coordIndicator {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ}
    (i : Fin k) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun ω => (p : ℝ) - coordIndicator k i ω) ((1 / 2 : ℝ≥0) ^ 2)
      (iidBernoulli k p hp) :=
  (hasSubgaussianMGF_coordIndicator_sub hp i).neg.congr
    (MeasureTheory.ae_of_all _ fun ω => by
      show -(coordIndicator k i ω - (p : ℝ)) = _
      ring)

/-- **One-sided Hoeffding bound for the trials**: for any family `Y` of
independent `(1/4)`-sub-Gaussian functions of the trials (in practice the
centered indicators `±(Xᵢ − p)`),
`Pr[Σᵢ Yᵢ ≥ tk] ≤ e^{−2t²k}`. -/
theorem iidBernoulli_tail_le {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ} (hk : 0 < k)
    {Y : Fin k → (Fin k → Bool) → ℝ}
    (hYind : ProbabilityTheory.iIndepFun Y (iidBernoulli k p hp))
    (hsubG : ∀ i, ProbabilityTheory.HasSubgaussianMGF (Y i) ((1 / 2 : ℝ≥0) ^ 2)
      (iidBernoulli k p hp))
    {t : ℝ} (ht : 0 ≤ t) :
    iidBernoulli k p hp {ω | t * k ≤ ∑ i, Y i ω} ≤
      ENNReal.ofReal (Real.exp (-2 * t ^ 2 * k)) := by
  have hH := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYind
    (c := fun _ : Fin k => (1 / 2 : ℝ≥0) ^ 2) (s := Finset.univ)
    (fun i _ => hsubG i) (ε := t * k)
    (mul_nonneg ht (Nat.cast_nonneg k))
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_nonneg _),
    ← measureReal_def]
  refine hH.trans (le_of_eq ?_)
  congr 1
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hsum : ((∑ _i : Fin k, ((1 / 2 : ℝ≥0) ^ 2) : ℝ≥0) : ℝ) = k / 4 := by
    push_cast
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  push_cast [hsum]
  field_simp
  ring

/-- **Concentration for i.i.d. Boolean trials** (the role of
[AB09, Cor 7.11], stated as the two-sided Hoeffding bound).  Let `X₁,…,X_k`
be i.i.d. Boolean random variables with `Pr[Xᵢ = 1] = p`, and `δ > 0`.  Then
`Pr[|(1/k)Σᵢ Xᵢ − p| > δ] ≤ 2·e^{−2δ²k}`.

The book's printed bound `< e^{−(δ²/4)pk}` is false (see the module
docstring's **Erratum**); this is the standard replacement, and suffices for
[AB09, Thm 7.10].

**Proof sketch.** Hoeffding's inequality for sums of independent bounded
random variables (in Mathlib: `measure_sum_ge_le_of_iIndepFun` for
sub-Gaussian summands; a `{0,1}`-valued variable is sub-Gaussian with
parameter `1/4` by Hoeffding's lemma), applied to `Xᵢ − p` on each of the
two tails with threshold `t = δk`, each tail contributing `e^{−2δ²k}`. -/
theorem iid_bernoulli_avg_concentration {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ}
    (hk : 0 < k) {δ : ℝ} (hδ0 : 0 < δ) :
    iidBernoulli k p hp {ω | δ < |successCount ω / k - (p : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * δ ^ 2 * k)) := by
  classical
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  -- Split the two-sided deviation into the two one-sided tails.
  have hsub : {ω : Fin k → Bool | δ < |successCount ω / k - (p : ℝ)|} ⊆
      {ω | δ * k ≤ ∑ i, (coordIndicator k i ω - (p : ℝ))} ∪
      {ω | δ * k ≤ ∑ i, ((p : ℝ) - coordIndicator k i ω)} := fun ω hω => by
    rw [Set.mem_setOf_eq, lt_abs] at hω
    have hsum1 : ∑ i, (coordIndicator k i ω - (p : ℝ))
        = successCount ω - k * p := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_comm]
      rfl
    have hsum2 : ∑ i, ((p : ℝ) - coordIndicator k i ω)
        = k * p - successCount ω := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rfl
    rcases hω with h | h
    · left
      rw [Set.mem_setOf_eq, hsum1]
      have h2 : (δ + (p : ℝ)) * k < successCount ω := by
        rw [← lt_div_iff₀ hk0]
        linarith
      nlinarith
    · right
      rw [Set.mem_setOf_eq, hsum2]
      have h2 : successCount ω < ((p : ℝ) - δ) * k := by
        rw [← div_lt_iff₀ hk0]
        linarith
      nlinarith
  -- Independence of the two centered families.
  have hXind := iIndepFun_coordIndicator hp k
  have hind1 : ProbabilityTheory.iIndepFun
      (fun i ω => coordIndicator k i ω - (p : ℝ)) (iidBernoulli k p hp) :=
    hXind.comp (fun _ : Fin k => fun x : ℝ => x - (p : ℝ))
      fun _ => measurable_id.sub_const _
  have hind2 : ProbabilityTheory.iIndepFun
      (fun i ω => (p : ℝ) - coordIndicator k i ω) (iidBernoulli k p hp) :=
    hXind.comp (fun _ : Fin k => fun x : ℝ => (p : ℝ) - x)
      fun _ => measurable_id.const_sub _
  have h1 := iidBernoulli_tail_le hp hk hind1
    (fun i => hasSubgaussianMGF_coordIndicator_sub hp i) hδ0.le
  have h2 := iidBernoulli_tail_le hp hk hind2
    (fun i => hasSubgaussianMGF_sub_coordIndicator hp i) hδ0.le
  calc iidBernoulli k p hp {ω | δ < |successCount ω / k - (p : ℝ)|}
      ≤ iidBernoulli k p hp
          ({ω | δ * k ≤ ∑ i, (coordIndicator k i ω - (p : ℝ))} ∪
            {ω | δ * k ≤ ∑ i, ((p : ℝ) - coordIndicator k i ω)}) :=
        measure_mono hsub
    _ ≤ iidBernoulli k p hp
          {ω | δ * k ≤ ∑ i, (coordIndicator k i ω - (p : ℝ))} +
        iidBernoulli k p hp
          {ω | δ * k ≤ ∑ i, ((p : ℝ) - coordIndicator k i ω)} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-2 * δ ^ 2 * k)) +
          ENNReal.ofReal (Real.exp (-2 * δ ^ 2 * k)) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * Real.exp (-2 * δ ^ 2 * k)) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
        congr 1
        ring

/-- **Majority-vote error reduction, concentration core** (the calculation
proving [AB09, Thm 7.10]).  If each of `k` i.i.d. trials succeeds with
probability `p ≥ 1/2 + ε`, the probability that at most half the trials
succeed — i.e. that the majority vote errs — is at most `e^{−2ε²k}`
(one-sided Hoeffding; the book's `e^{−(δ²/4)pk}`-based route is unsound,
see the module docstring's **Erratum**).

For advantage `ε ≥ (n+1)^{−c}/6` and `k = Θ((n+1)^{2c+d})` repetitions this
is at most `2^{−(n+1)^d}`, which is [AB09, Thm 7.10]'s bound.

**Proof sketch.** If at most half the trials succeed then
`(1/k)Σᵢ Xᵢ ≤ 1/2 ≤ p − ε`, so the lower tail `Σᵢ(Xᵢ − p) ≤ −εk` has
occurred; one-sided Hoeffding for independent `{0,1}`-valued summands bounds
it by `e^{−2ε²k}`. -/
theorem majority_error_le {p : ℝ≥0} (hp : p ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hpε : 1 / 2 + ε ≤ (p : ℝ)) {k : ℕ} (hk : 0 < k) :
    iidBernoulli k p hp {ω | 2 * successCount ω ≤ k} ≤
      ENNReal.ofReal (Real.exp (-2 * ε ^ 2 * k)) := by
  classical
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hsub : {ω : Fin k → Bool | 2 * successCount ω ≤ k} ⊆
      {ω | ε * k ≤ ∑ i, ((p : ℝ) - coordIndicator k i ω)} := fun ω hω => by
    have hsum : ∑ i, ((p : ℝ) - coordIndicator k i ω)
        = k * p - successCount ω := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rfl
    rw [Set.mem_setOf_eq] at hω
    rw [Set.mem_setOf_eq, hsum]
    have h3 : (k : ℝ) * (1 / 2 + ε) ≤ k * p :=
      mul_le_mul_of_nonneg_left hpε hk0.le
    nlinarith
  have hind : ProbabilityTheory.iIndepFun
      (fun i ω => (p : ℝ) - coordIndicator k i ω) (iidBernoulli k p hp) :=
    (iIndepFun_coordIndicator hp k).comp
      (fun _ : Fin k => fun x : ℝ => (p : ℝ) - x)
      fun _ => measurable_id.const_sub _
  exact (measure_mono hsub).trans (iidBernoulli_tail_le hp hk hind
    (fun i => hasSubgaussianMGF_sub_coordIndicator hp i) hε.le)

end Randomized
```

## ===== TCSlib/Complexity/Randomized/Classes.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The randomized complexity classes BPP, RP, coRP, ZPP

Verifier-style definitions of Arora–Barak's randomized complexity classes,
following the certificate view of [AB09, Def 7.4]: a language is in a
randomized class when some efficient two-input predicate `M(x, r)`, run on the
input `x` and a uniformly random string `r` of polynomially-bounded length,
decides membership with the class's acceptance-probability profile.

## Main definitions

* `Randomized.randProb` — the probability of an event over a uniform random
  string of a given length, as a rational counting ratio.
* `Randomized.polyLen` — the canonical polynomial length schedule
  `n ↦ a·(n+1)^k` for random strings.
* `Randomized.VerifierModel` — an abstract *efficiency notion* standing in for
  "polynomial-time Turing machine" (see **Deviations** below).
* `Randomized.InBPP` — [AB09, Def 7.4] (equivalently Def 7.1 via the
  certificate view).
* `Randomized.InRP`, `Randomized.InCoRP` — [AB09, Def 7.6] and the remark
  following it.
* `Randomized.InZPP` — [AB09, Def 7.7], in the zero-error "abort"
  formulation (see **Deviations**).
* `Randomized.raceVerifier`, `Randomized.majorityVerifier` — the two verifier
  constructions used by Theorems 7.8 and 7.10.

## Main results

* `Randomized.inZPP_iff_inRP_and_inCoRP` — `ZPP = RP ∩ coRP` [AB09, Thm 7.8].
* `Randomized.InBPP.compl` — `BPP = coBPP` (used by [AB09, Thm 7.18]).
* `Randomized.bpp_error_reduction` — error reduction [AB09, Thm 7.10].
* `Randomized.inBPPWeak_iff_inBPP` — `BPP_{n^{-c}} = BPP` [AB09, Lem 7.9].

## Deviations from the source

* **Machine model.** [AB09] defines these classes with polynomial-time Turing
  machines.  Per the repository's agreed scope, we use the certificate view of
  [AB09, Def 7.4] — predicates over inputs and random strings — and replace
  "`M` is a polynomial-time TM" by membership in an abstract
  `VerifierModel` `E`, a predicate on verifiers.  Every class and theorem is
  parametrized by `E`.  The closure properties that [AB09]'s proofs use
  (building the race, majority, complement, and projection verifiers out of
  given ones) are stated as explicit named hypotheses (`ClosedUnder…`), all of
  which hold for the intended instantiation "computable in polynomial time".
  Intended instantiation targets, once a uniform-computability layer is
  available: the `P`/`PolyTime` development of the `complexity/arora-barak-ch1`
  branch, or Mathlib's `Turing.TM2ComputableInPolyTime`.
* **Length schedules.** [AB09, Def 7.4] draws `r ∈ {0,1}^{p(|x|)}` for a
  polynomial `p`.  We fix the canonical schedule `polyLen a k : n ↦ a·(n+1)^k`
  (existentially quantified over `a, k : ℕ`) rather than an arbitrary
  `p : ℕ → ℕ` with a polynomial bound: an arbitrary bounded `p` need not be
  computable and could smuggle undecidable information through the schedule
  itself.  Every polynomial is dominated by some `polyLen a k`, and a verifier
  can ignore padding bits, so the class is unchanged.
* **Probability.** `Pr_{r ∈ {0,1}^m}` is the counting ratio
  `#{r : accepted}/2^m` valued in `ℚ`; random strings of length `m` are
  `Fin m → Bool`, passed to verifiers as lists via `List.ofFn`.
* **ZPP.** [AB09, Def 7.7] defines `ZPP` by expected running time of a
  zero-error machine.  Expected time is not expressible for abstract
  predicates, so we use the standard equivalent "Las Vegas" formulation: a
  verifier with values in `Option Bool` that is never wrong and outputs `none`
  ("don't know") with probability at most `1/2`.  [AB09, §7.4.2] sketches the
  equivalence of expected-time and worst-case formulations (truncation via
  Markov's inequality).
* **The weak threshold of Lemma 7.9.** The book's success threshold
  `1/2 + |x|^{-c}` exceeds `1` for `|x| ≤ 1`, making the literal class
  `BPP_{n^{-c}}` empty; we require advantage `min (1/6) ((|x|+1)^{-c})`
  instead, which for `c ≥ 1` agrees with the book's (up to the `n+1` shift) for
  `|x| ≥ 5` and makes `BPP ⊆ BPP_{n^{-c}}` hold as the book intends.
* The constant `2/3` follows [AB09, Defs 7.1/7.6]; `1/2` in `InZPP` is the
  conventional choice (any constant in `(0,1)` gives the same class, by the
  same repetition argument as [AB09, §7.4.1]).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset

/-- The probability, over a uniformly random string `r ∈ {0,1}^m`, that the
event `A` holds of `r` (as a list): the counting ratio `#{r : A r}/2^m`.
[AB09, Def 7.4: "`Pr_{r ∈_R {0,1}^{p(|x|)}}`"] -/
def randProb (m : ℕ) (A : List Bool → Prop) [DecidablePred A] : ℚ :=
  ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ) / 2 ^ m

/-- Two events that agree on every random string have the same
probability. -/
theorem randProb_congr {m : ℕ} {A B : List Bool → Prop} [DecidablePred A]
    [DecidablePred B]
    (h : ∀ r : Fin m → Bool, A (List.ofFn r) ↔ B (List.ofFn r)) :
    randProb m A = randProb m B := by
  unfold randProb
  rw [Finset.filter_congr fun r _ => h r]

/-- Probabilities are nonnegative. -/
theorem randProb_nonneg {m : ℕ} {A : List Bool → Prop} [DecidablePred A] :
    0 ≤ randProb m A := by
  unfold randProb
  positivity

/-- There are `2^m` random strings of length `m`. -/
theorem card_univ_bitstrings (m : ℕ) :
    (univ : Finset (Fin m → Bool)).card = 2 ^ m := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- Probabilities are at most one. -/
theorem randProb_le_one {m : ℕ} {A : List Bool → Prop} [DecidablePred A] :
    randProb m A ≤ 1 := by
  unfold randProb
  rw [div_le_one (by positivity)]
  calc ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ)
      ≤ ((univ : Finset (Fin m → Bool)).card : ℚ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = 2 ^ m := by rw [card_univ_bitstrings]; push_cast; rfl

/-- Probability is monotone in the event. -/
theorem randProb_mono {m : ℕ} {A B : List Bool → Prop} [DecidablePred A]
    [DecidablePred B]
    (h : ∀ r : Fin m → Bool, A (List.ofFn r) → B (List.ofFn r)) :
    randProb m A ≤ randProb m B := by
  unfold randProb
  gcongr
  exact h _

/-- Complement rule: `Pr[¬A] = 1 − Pr[A]`. -/
theorem randProb_not {m : ℕ} (A : List Bool → Prop) [DecidablePred A] :
    randProb m (fun l => ¬ A l) = 1 - randProb m A := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset (Fin m → Bool))) (p := fun r => A (List.ofFn r))
  rw [card_univ_bitstrings] at hsplit
  have h2 : ((2 : ℚ) ^ m) ≠ 0 := by positivity
  have hcast : ((univ.filter fun r : Fin m → Bool => ¬ A (List.ofFn r)).card : ℚ)
      = 2 ^ m - ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ) := by
    have h3 : ((univ.filter fun r : Fin m → Bool => A (List.ofFn r)).card : ℚ)
        + ((univ.filter fun r : Fin m → Bool => ¬ A (List.ofFn r)).card : ℚ)
        = 2 ^ m := by
      exact_mod_cast hsplit
    linarith
  show ((univ.filter fun r : Fin m → Bool => ¬ A (List.ofFn r)).card : ℚ) / 2 ^ m
      = 1 - randProb m A
  unfold randProb
  rw [hcast, sub_div, div_self h2]

/-- The certain event has probability one. -/
theorem randProb_true {m : ℕ} : randProb m (fun _ => True) = 1 := by
  unfold randProb
  rw [Finset.filter_true_of_mem fun _ _ => trivial, card_univ_bitstrings]
  push_cast
  exact div_self (by positivity)

/-- Every list of length `m` arises from a tuple of `m` bits. -/
theorem exists_ofFn_eq {l : List Bool} {m : ℕ} (h : l.length = m) :
    ∃ r : Fin m → Bool, l = List.ofFn r := by
  refine ⟨fun i => l[(i : ℕ)]'(by omega), ?_⟩
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp

/-- **Independence of disjoint segments**: if the event is a conjunction of a
condition on the first `m₁` bits and a condition on the remaining `m₂` bits,
the probability factors. -/
theorem randProb_split (m₁ m₂ : ℕ) (A B : List Bool → Prop)
    [DecidablePred A] [DecidablePred B] :
    randProb (m₁ + m₂) (fun r => A (r.take m₁) ∧ B (r.drop m₁)) =
      randProb m₁ A * randProb m₂ B := by
  unfold randProb
  rw [div_mul_div_comm, ← pow_add, ← Nat.cast_mul]
  congr 2
  rw [← Finset.card_product]
  refine (Finset.card_bij (fun uv _ => Fin.append uv.1 uv.2) ?_ ?_ ?_).symm
  · rintro ⟨u, v⟩ huv
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at huv
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [List.ofFn_fin_append, List.take_left' (by simp)]
      exact huv.1.2
    · rw [List.ofFn_fin_append, List.drop_left' (by simp)]
      exact huv.2.2
  · intro uv huv uv' huv' h
    exact (Fin.appendEquiv m₁ m₂).injective (by exact h)
  · intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨-, hA, hB⟩ := hr
    have hdec : Fin.append (fun i => r (Fin.castAdd m₂ i))
        (fun i => r (Fin.natAdd m₁ i)) = r := Fin.append_castAdd_natAdd
    refine ⟨(fun i => r (Fin.castAdd m₂ i), fun i => r (Fin.natAdd m₁ i)),
      ?_, hdec⟩
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
    rw [← hdec, List.ofFn_fin_append] at hA hB
    rw [List.take_left' (by simp)] at hA
    rw [List.drop_left' (by simp)] at hB
    exact ⟨⟨Finset.mem_univ _, hA⟩, Finset.mem_univ _, hB⟩

/-- A condition on only the first `m₁ ≤ m` bits has the same probability over
`m`-bit strings as over `m₁`-bit strings: padding bits are ignored. -/
theorem randProb_take {m₁ m : ℕ} (h : m₁ ≤ m) (A : List Bool → Prop)
    [DecidablePred A] :
    randProb m (fun r => A (r.take m₁)) = randProb m₁ A := by
  obtain ⟨m₂, rfl⟩ := Nat.exists_eq_add_of_le h
  calc randProb (m₁ + m₂) (fun r => A (r.take m₁))
      = randProb (m₁ + m₂) (fun r => A (r.take m₁) ∧ (fun _ => True) (r.drop m₁)) :=
        randProb_congr fun r => by simp
    _ = randProb m₁ A * randProb m₂ (fun _ => True) :=
        randProb_split m₁ m₂ A (fun _ => True)
    _ = randProb m₁ A := by rw [randProb_true, mul_one]

/-- The canonical polynomial length schedule `n ↦ a·(n+1)^k` for random
strings — a concrete, computable stand-in for [AB09, Def 7.4]'s "polynomial
`p`" (see the module docstring's **Deviations**: an arbitrary polynomially
*bounded* `ℕ → ℕ` need not be computable and would let the schedule itself
decide undecidable languages). -/
def polyLen (a k : ℕ) : ℕ → ℕ := fun n => a * (n + 1) ^ k

/-- An abstract *efficiency notion* for verifiers, standing in for
"polynomial-time Turing machine" in [AB09, Def 7.4] (see the module
docstring's **Deviations**).  `Eff M` reads "`M` is an efficient verifier";
verifiers are `Option Bool`-valued so that zero-error ("don't know") verifiers
and ordinary Boolean verifiers share one notion.  `EffTwoWitness N` is the
corresponding notion for predicates of an input and two witness strings, the
verifier format of `Σ₂`-statements (used by [AB09, Thm 7.18]).  Intended
instantiations: a polynomial-time TM layer (the `complexity/arora-barak-ch1`
branch's `PolyTime`, or Mathlib's `Turing.TM2ComputableInPolyTime`). -/
structure VerifierModel where
  /-- "`M` is an efficient (poly-time) verifier." -/
  Eff : (List Bool → List Bool → Option Bool) → Prop
  /-- "`N` is an efficient (poly-time) two-witness predicate." -/
  EffTwoWitness : (List Bool → List Bool → List Bool → Bool) → Prop

/-- A Boolean verifier, viewed as an `Option Bool`-valued one. -/
def boolVerifier (M : List Bool → List Bool → Bool) :
    List Bool → List Bool → Option Bool :=
  fun x r => some (M x r)

variable (E : VerifierModel)

/-- `L ∈ BPP`: some efficient verifier `M` with polynomially-long randomness
decides `L` with two-sided error at most `1/3` — for every input `x`,
`Pr_{r ∈ {0,1}^{p(|x|)}}[M(x,r) = L(x)] ≥ 2/3`, where `p = polyLen a k`.
[AB09, Def 7.4] (the certificate form of [AB09, Def 7.1]). -/
def InBPP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = false)

/-- `L ∈ RP`: one-sided error — inputs in `L` are accepted with probability
at least `2/3`, inputs outside `L` are *never* accepted.  [AB09, Def 7.6] -/
def InRP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 2/3 ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) = false)

/-- `L ∈ coRP` iff its complement is in `RP`: one-sided error in the other
direction.  [AB09, §7.3: "`coRP = {L | L̄ ∈ RP}`"] -/
def InCoRP (L : Language Bool) : Prop :=
  InRP E Lᶜ

/-- `L ∈ ZPP`: some efficient zero-error verifier decides `L` — it may output
`none` ("don't know") with probability at most `1/2`, but whenever it outputs
an answer, the answer is correct.  [AB09, Def 7.7], in the equivalent
Las Vegas formulation (see the module docstring's **Deviations**). -/
def InZPP (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Option Bool) (a k : ℕ),
    E.Eff M ∧
    ∀ x : List Bool,
      (x ∈ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some false) ∧
      (x ∉ L → ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some true) ∧
      randProb (polyLen a k x.length) (fun r => M x r = none) ≤ 1/2

section Constructions

/-- The *race* of an `RP` verifier for `L` and an `RP` verifier for `Lᶜ` on
split randomness: on `r = r₁ ++ r₂`, answer `some true` if `M₁` accepts `r₁`,
else `some false` if `M₂` accepts `r₂`, else `none`.  The construction behind
`RP ∩ coRP ⊆ ZPP` in [AB09, Thm 7.8]. -/
def raceVerifier (M₁ M₂ : List Bool → List Bool → Bool) (p₁ : ℕ → ℕ) :
    List Bool → List Bool → Option Bool := fun x r =>
  if M₁ x (r.take (p₁ x.length)) then some true
  else if M₂ x (r.drop (p₁ x.length)) then some false
  else none

/-- The `k`-fold repetition of a verifier with majority vote, on randomness
split into `k` blocks of length `p(|x|)`: the construction behind error
reduction [AB09, Thm 7.10]. -/
def majorityVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → Bool := fun x r =>
  let n := x.length
  let votes := (List.range (k n)).countP fun i =>
    M x ((r.drop (i * p n)).take (p n))
  k n < 2 * votes

/-- `E` can race two of its Boolean verifiers on a polynomial split point
(closure of polynomial time under running two machines on split
randomness). -/
def ClosedUnderRace : Prop :=
  ∀ M₁ M₂ a k, E.Eff (boolVerifier M₁) → E.Eff (boolVerifier M₂) →
    E.Eff (raceVerifier M₁ M₂ (polyLen a k))

/-- `E` can turn a zero-error verifier into the Boolean verifier answering
"did it output `some b`?" (closure of polynomial time under postprocessing
the output). -/
def ClosedUnderAnswerIs : Prop :=
  ∀ M b, E.Eff M →
    E.Eff (boolVerifier fun x r => M x r = some b)

/-- The `k`-fold repetition of a verifier accepting if *any* repetition
accepts, on randomness split into `k` blocks of length `p(|x|)`: the
one-sided amplifier (an `OR`, not a majority — a strict majority cannot
amplify success probability exactly `1/2`, whereas for one-sided error the
`OR` drives the failure probability to `(1/2)^k` without hurting
soundness).  Used by [AB09, Thm 7.8]'s `ZPP ⊆ RP` direction. -/
def anyVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → Bool := fun x r =>
  (List.range (k x.length)).any fun i =>
    M x ((r.drop (i * p x.length)).take (p x.length))

/-- `E` can repeat a Boolean verifier a polynomial number of times, on blocks
of polynomial length, and take the majority (closure of polynomial time under
polynomial repetition). -/
def ClosedUnderMajority : Prop :=
  ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.Eff (boolVerifier (majorityVerifier M (polyLen a k) (polyLen a' k')))

/-- `E` can repeat a Boolean verifier a polynomial number of times, on blocks
of polynomial length, and accept if any repetition accepts (closure of
polynomial time under polynomial repetition with an `OR`). -/
def ClosedUnderAny : Prop :=
  ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.Eff (boolVerifier (anyVerifier M (polyLen a k) (polyLen a' k')))

/-- `E` can negate a Boolean verifier's answer (closure of polynomial time
under complementation of the output). -/
def ClosedUnderNot : Prop :=
  ∀ M, E.Eff (boolVerifier M) →
    E.Eff (boolVerifier fun x r => !(M x r))

end Constructions

section Counting

/-- `Pr[∅] = 0`. -/
theorem randProb_false {m : ℕ} : randProb m (fun _ => False) = 0 := by
  unfold randProb
  rw [Finset.filter_false]
  simp

/-- Additivity over disjoint events. -/
theorem randProb_or_disjoint {m : ℕ} (A B : List Bool → Prop)
    [DecidablePred A] [DecidablePred B]
    (h : ∀ r : Fin m → Bool, ¬ (A (List.ofFn r) ∧ B (List.ofFn r))) :
    randProb m (fun l => A l ∨ B l) = randProb m A + randProb m B := by
  unfold randProb
  rw [← add_div, ← Nat.cast_add]
  congr 2
  rw [Finset.filter_or]
  refine Finset.card_union_of_disjoint ?_
  rw [Finset.disjoint_left]
  intro r hrA hrB
  rw [Finset.mem_filter] at hrA hrB
  exact h r ⟨hrA.2, hrB.2⟩

/-- Partitioning by the value of a natural-number statistic. -/
theorem randProb_mem_eq_sum {m : ℕ} (g : List Bool → ℕ) (T : Finset ℕ) :
    randProb m (fun l => g l ∈ T) = ∑ j ∈ T, randProb m (fun l => g l = j) := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty,
      randProb_congr (B := fun _ => False) fun r => by simp]
    exact randProb_false
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, ← ih,
      randProb_congr (B := fun l => g l = a ∨ g l ∈ T) fun r => by
        simp [Finset.mem_insert]]
    exact randProb_or_disjoint _ _ fun r ⟨h1, h2⟩ => ha (h1 ▸ h2)

/-- `Pr[B = false] = 1 − Pr[B = true]` for a Boolean test. -/
theorem randProb_bool_false {m : ℕ} (B : List Bool → Bool) :
    randProb m (fun l => B l = false) =
      1 - randProb m (fun l => B l = true) := by
  rw [randProb_congr (B := fun l => ¬ (B l = true)) fun r => by simp]
  exact randProb_not _

/-- The number of the `K` successive length-`q` blocks of `l` on which the
Boolean test `B` succeeds: the vote count of `majorityVerifier` and
`anyVerifier`, abstracted over the test. -/
def blockCount (q K : ℕ) (B : List Bool → Bool) (l : List Bool) : ℕ :=
  (List.range K).countP fun i => B ((l.drop (i * q)).take q)

theorem blockCount_le (q K : ℕ) (B : List Bool → Bool) (l : List Bool) :
    blockCount q K B l ≤ K := by
  calc blockCount q K B l ≤ (List.range K).length := List.countP_le_length ..
    _ = K := List.length_range ..

/-- Peeling off the first block. -/
theorem blockCount_succ (q K : ℕ) (B : List Bool → Bool) (l : List Bool) :
    blockCount q (K + 1) B l =
      (if B (l.take q) then 1 else 0) + blockCount q K B (l.drop q) := by
  unfold blockCount
  rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]
  have hfun : ((fun i => B ((l.drop (i * q)).take q)) ∘ Nat.succ)
      = fun i => B (((l.drop q).drop (i * q)).take q) := by
    funext i
    simp only [Function.comp_apply]
    rw [Nat.succ_mul, Nat.add_comm (i * q) q, ← List.drop_drop]
  rw [hfun, zero_mul, List.drop_zero]
  exact Nat.add_comm _ _

/-- **The vote count is binomially distributed**: over a uniform string of
`K` blocks of `q` bits each, `Pr[blockCount = j] = C(K,j)·s^j·(1−s)^{K−j}`,
where `s` is the single-block success probability. -/
theorem randProb_blockCount (q : ℕ) (B : List Bool → Bool) :
    ∀ K j : ℕ, j ≤ K →
      randProb (K * q) (fun l => blockCount q K B l = j) =
        (K.choose j : ℚ) * (randProb q (fun l => B l = true)) ^ j *
          (1 - randProb q (fun l => B l = true)) ^ (K - j)
  | 0, 0, _ => by
    rw [randProb_congr (B := fun _ => True) fun r => by simp [blockCount],
      randProb_true]
    simp
  | 0, j + 1, h => absurd h (by omega)
  | K + 1, 0, _ => by
    have hmul : (K + 1) * q = q + K * q := by ring
    rw [hmul]
    have hev : randProb (q + K * q) (fun l => blockCount q (K + 1) B l = 0)
        = randProb (q + K * q) (fun l =>
            (fun l' => B l' = false) (l.take q) ∧
            (fun w => blockCount q K B w = 0) (l.drop q)) :=
      randProb_congr fun r => by
        rw [blockCount_succ]
        rcases hb : B ((List.ofFn r).take q) <;> simp [hb]
    rw [hev, randProb_split q (K * q) (fun l' => B l' = false)
        (fun w => blockCount q K B w = 0),
      randProb_bool_false, randProb_blockCount q B K 0 (by omega)]
    simp [pow_succ]
    ring
  | K + 1, j + 1, h => by
    have hmul : (K + 1) * q = q + K * q := by ring
    rw [hmul]
    have hev : randProb (q + K * q)
        (fun l => blockCount q (K + 1) B l = j + 1)
        = randProb (q + K * q) (fun l =>
            ((fun l' => B l' = true) (l.take q) ∧
              (fun w => blockCount q K B w = j) (l.drop q)) ∨
            ((fun l' => B l' = false) (l.take q) ∧
              (fun w => blockCount q K B w = j + 1) (l.drop q))) :=
      randProb_congr fun r => by
        rw [blockCount_succ]
        rcases hb : B ((List.ofFn r).take q) <;> simp [hb] <;> omega
    rw [hev, randProb_or_disjoint _ _ (fun r => by
      rintro ⟨⟨h1, -⟩, h2, -⟩
      rw [h1] at h2
      exact absurd h2 (by simp)),
      randProb_split q (K * q) (fun l' => B l' = true)
        (fun w => blockCount q K B w = j),
      randProb_split q (K * q) (fun l' => B l' = false)
        (fun w => blockCount q K B w = j + 1),
      randProb_bool_false]
    rcases Nat.lt_or_ge j K with hjK | hjK
    · rw [randProb_blockCount q B K j (by omega),
        randProb_blockCount q B K (j + 1) (by omega)]
      have hpascal : (((K + 1).choose (j + 1) : ℕ) : ℚ)
          = (K.choose j : ℚ) + (K.choose (j + 1) : ℚ) := by
        exact_mod_cast Nat.choose_succ_succ K j
      have he1 : K + 1 - (j + 1) = K - j := by omega
      have he2 : K - j = (K - (j + 1)) + 1 := by omega
      rw [he1, hpascal, he2, pow_succ]
      ring
    · have hjeq : j = K := by omega
      rw [hjeq, randProb_blockCount q B K K (le_refl _)]
      have hzero : randProb (K * q)
          (fun w => blockCount q K B w = K + 1) = 0 := by
        rw [randProb_congr (B := fun _ => False) fun r => by
          have := blockCount_le q K B (List.ofFn r)
          simp
          omega]
        exact randProb_false
      rw [hzero, mul_zero, add_zero]
      simp [Nat.choose_self, pow_succ]
      ring

/-- **Elementary Chernoff-type tail bound** for the vote count: if each
block succeeds with probability at most `1/2 − ε`, then at least half of
the `K` blocks succeed with probability at most `2·(1 − 4ε²)^⌊K/2⌋`.
(The elementary `2^K·(s(1−s))^{⌊K/2⌋}` estimate; no exponential function
is needed, which keeps the whole development inside `ℚ`.) -/
theorem randProb_tail_le (q K : ℕ) (B : List Bool → Bool) {ε : ℚ}
    (hε0 : 0 ≤ ε) (hs : randProb q (fun l => B l = true) ≤ 1/2 - ε) :
    randProb (K * q) (fun l => K ≤ 2 * blockCount q K B l) ≤
      2 * (1 - 4 * ε ^ 2) ^ (K / 2) := by
  have hs0 : (0:ℚ) ≤ randProb q (fun l => B l = true) := randProb_nonneg
  have hs1 : randProb q (fun l => B l = true) ≤ 1 := randProb_le_one
  set s : ℚ := randProb q (fun l => B l = true) with hs_def
  have hf0 : (0:ℚ) ≤ 1 - s := by linarith
  have hεhalf : ε ≤ 1/2 := by linarith
  set T : Finset ℕ := (Finset.range (K + 1)).filter (fun j => K ≤ 2 * j)
    with hT
  have hev : randProb (K * q) (fun l => K ≤ 2 * blockCount q K B l)
      = ∑ j ∈ T, randProb (K * q) (fun l => blockCount q K B l = j) := by
    rw [← randProb_mem_eq_sum (fun l => blockCount q K B l) T]
    refine randProb_congr fun r => ?_
    rw [hT]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact ⟨Nat.lt_succ_of_le (blockCount_le q K B _), h⟩
    · exact fun h => h.2
  rw [hev]
  have hterm : ∀ j ∈ T, randProb (K * q) (fun l => blockCount q K B l = j)
      ≤ (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) := by
    intro j hj
    rw [hT, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjK, hKj⟩ := hj
    have hjK' : j ≤ K := by omega
    rw [randProb_blockCount q B K j hjK', ← hs_def]
    have hj₀ : K - K / 2 ≤ j := by omega
    have hsf : s ≤ 1 - s := by linarith
    -- shift the exponent towards the balanced point
    have hstep1 : s ^ j * (1 - s) ^ (K - j)
        ≤ s ^ (K - K / 2) * (1 - s) ^ (K / 2) := by
      have e1 : s ^ j = s ^ (K - K / 2) * s ^ (j - (K - K / 2)) := by
        rw [← pow_add]
        congr 1
        omega
      have e2 : (1 - s) ^ (K / 2)
          = (1 - s) ^ (K - j) * (1 - s) ^ (j - (K - K / 2)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [e1, e2]
      have hpow : s ^ (j - (K - K / 2)) ≤ (1 - s) ^ (j - (K - K / 2)) :=
        pow_le_pow_left₀ hs0 hsf _
      calc s ^ (K - K / 2) * s ^ (j - (K - K / 2)) * (1 - s) ^ (K - j)
          ≤ s ^ (K - K / 2) * (1 - s) ^ (j - (K - K / 2)) *
              (1 - s) ^ (K - j) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
        _ = s ^ (K - K / 2) * ((1 - s) ^ (K - j) *
              (1 - s) ^ (j - (K - K / 2))) := by ring
    have hstep2 : s ^ (K - K / 2) * (1 - s) ^ (K / 2)
        ≤ (s * (1 - s)) ^ (K / 2) := by
      have e3 : s ^ (K - K / 2) = s ^ (K / 2) * s ^ (K - 2 * (K / 2)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [e3, mul_pow]
      have hle1 : s ^ (K - 2 * (K / 2)) ≤ 1 := pow_le_one₀ hs0 hs1
      calc s ^ (K / 2) * s ^ (K - 2 * (K / 2)) * (1 - s) ^ (K / 2)
          ≤ s ^ (K / 2) * 1 * (1 - s) ^ (K / 2) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hle1 (by positivity)) (by positivity)
        _ = s ^ (K / 2) * (1 - s) ^ (K / 2) := by ring
    have hmono := hstep1.trans hstep2
    calc (K.choose j : ℚ) * s ^ j * (1 - s) ^ (K - j)
        = (K.choose j : ℚ) * (s ^ j * (1 - s) ^ (K - j)) := by ring
      _ ≤ (K.choose j : ℚ) * ((s * (1 - s)) ^ (K / 2)) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
  have hTsub : T ⊆ Finset.range (K + 1) := by
    rw [hT]
    exact Finset.filter_subset _ _
  have hsum2 : ∑ j ∈ T, (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2)
      ≤ ∑ j ∈ Finset.range (K + 1),
          (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hTsub fun j _ _ => by positivity
  have hsum3 : ∑ j ∈ Finset.range (K + 1),
      (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2)
      = (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    rfl
  have hprod : s * (1 - s) ≤ 1/4 - ε ^ 2 := by nlinarith
  have hprod0 : (0:ℚ) ≤ s * (1 - s) := by positivity
  have hfinal : (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2)
      ≤ 2 * (1 - 4 * ε ^ 2) ^ (K / 2) := by
    have h2K : (2 : ℚ) ^ K ≤ 2 * 4 ^ (K / 2) := by
      have e4 : K = 2 * (K / 2) + K % 2 := by omega
      calc (2 : ℚ) ^ K = 2 ^ (2 * (K / 2)) * 2 ^ (K % 2) := by
            rw [← pow_add, ← e4]
        _ ≤ 2 ^ (2 * (K / 2)) * 2 ^ 1 := by
            refine mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
        _ = 2 * 4 ^ (K / 2) := by
            rw [pow_mul]
            norm_num
            ring
    have hpow : (s * (1 - s)) ^ (K / 2) ≤ (1/4 - ε ^ 2) ^ (K / 2) :=
      pow_le_pow_left₀ hprod0 hprod _
    calc (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2)
        ≤ (2 * 4 ^ (K / 2)) * (1/4 - ε ^ 2) ^ (K / 2) := by
          refine mul_le_mul h2K hpow (by positivity) (by positivity)
      _ = 2 * (4 * (1/4 - ε ^ 2)) ^ (K / 2) := by
          rw [mul_pow]
          ring
      _ = 2 * (1 - 4 * ε ^ 2) ^ (K / 2) := by
          congr 2
          ring
  calc ∑ j ∈ T, randProb (K * q) (fun l => blockCount q K B l = j)
      ≤ ∑ j ∈ T, (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ j ∈ Finset.range (K + 1),
          (K.choose j : ℚ) * (s * (1 - s)) ^ (K / 2) := hsum2
    _ = (2 : ℚ) ^ K * (s * (1 - s)) ^ (K / 2) := hsum3
    _ ≤ 2 * (1 - 4 * ε ^ 2) ^ (K / 2) := hfinal

/-- The rational Bernoulli estimate `(1−x)^m ≤ 1/2` once `m·x ≥ 1`:
`(1−x)^m·(1+mx) ≤ 1` by induction, and `1+mx ≥ 2`. -/
theorem one_sub_pow_le_half {x : ℚ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m : ℕ}
    (hm : 1 ≤ (m : ℚ) * x) : (1 - x) ^ m ≤ 1/2 := by
  have key : ∀ m' : ℕ, (1 - x) ^ m' * (1 + (m' : ℚ) * x) ≤ 1 := by
    intro m'
    induction m' with
    | zero => simp
    | succ m' ih =>
      have h1 : (0:ℚ) ≤ (1 - x) ^ m' := pow_nonneg (by linarith) m'
      have hstep : (1 - x) * (1 + ((m' : ℚ) + 1) * x) ≤ 1 + (m' : ℚ) * x := by
        have hnn : 0 ≤ ((m' : ℚ) + 1) * x ^ 2 := by positivity
        have hexp : (1 - x) * (1 + ((m' : ℚ) + 1) * x)
            = 1 + (m' : ℚ) * x - ((m' : ℚ) + 1) * x ^ 2 := by ring
        rw [hexp]
        linarith
      calc (1 - x) ^ (m' + 1) * (1 + ((m' + 1 : ℕ) : ℚ) * x)
          = (1 - x) ^ m' * ((1 - x) * (1 + ((m' : ℚ) + 1) * x)) := by
            push_cast
            ring
        _ ≤ (1 - x) ^ m' * (1 + (m' : ℚ) * x) :=
            mul_le_mul_of_nonneg_left hstep h1
        _ ≤ 1 := ih
  have h3 := key m
  nlinarith [pow_nonneg (by linarith : (0:ℚ) ≤ 1 - x) m]

/-- Iterating `one_sub_pow_le_half`: `(1−x)^e ≤ (1/2)^T` once `e ≥ m·T`
with `m·x ≥ 1`. -/
theorem one_sub_pow_le_half_pow {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {m T e : ℕ} (hm : 1 ≤ (m : ℚ) * x) (he : m * T ≤ e) :
    (1 - x) ^ e ≤ (1/2 : ℚ) ^ T := by
  calc (1 - x) ^ e ≤ (1 - x) ^ (m * T) :=
      pow_le_pow_of_le_one (by linarith) (by linarith) he
    _ = ((1 - x) ^ m) ^ T := by rw [pow_mul]
    _ ≤ (1/2 : ℚ) ^ T :=
      pow_le_pow_left₀ (pow_nonneg (by linarith) m)
        (one_sub_pow_le_half hx0 hx1 hm) T

end Counting

/-- `BPP` is closed under complementation (`BPP = coBPP`): swap the two
acceptance clauses and negate the verifier's answer.  Used by
[AB09, Thm 7.18]'s proof ("it is enough to prove `BPP ⊆ Σ₂ᵖ` because `BPP`
is closed under complementation").

**Proof sketch.** If `M` decides `L` with two-sided error `1/3`, then
`¬M` decides `Lᶜ` with the same error: the `x ∈ Lᶜ` clause for `¬M` is the
`x ∉ L` clause for `M` and vice versa, since
`¬M x r = true ↔ M x r = false`. -/
theorem InBPP.compl (hNot : ClosedUnderNot E) {L : Language Bool}
    (hL : InBPP E L) : InBPP E Lᶜ := by
  obtain ⟨M, a, k, hM, hacc⟩ := hL
  refine ⟨fun x r => !(M x r), a, k, hNot M hM, fun x => ?_⟩
  constructor
  · intro hx
    calc (2/3 : ℚ)
        ≤ randProb (polyLen a k x.length) fun r => M x r = false :=
          (hacc x).2 hx
      _ = randProb (polyLen a k x.length) fun r => (!(M x r)) = true :=
          randProb_congr fun r => by simp
  · intro hx
    calc (2/3 : ℚ)
        ≤ randProb (polyLen a k x.length) fun r => M x r = true :=
          (hacc x).1 (Set.not_notMem.mp hx)
      _ = randProb (polyLen a k x.length) fun r => (!(M x r)) = false :=
          randProb_congr fun r => by simp

/-- From a zero-error verifier whose definite answers are never wrong, a
one-sided witness: on members it answers `some b` with probability at least
`1/2` (it never answers `some (!b)` and aborts with probability at most
`1/2`), and on non-members it never answers `some b`; a 2-fold `OR`
(`anyVerifier`) amplifies `1/2` to `3/4 ≥ 2/3`.  The common core of the
inclusions `ZPP ⊆ RP` and `ZPP ⊆ coRP` in [AB09, Thm 7.8]. -/
theorem inRP_of_zeroError (hAns : ClosedUnderAnswerIs E)
    (hAny : ClosedUnderAny E) {M : List Bool → List Bool → Option Bool}
    {a k : ℕ} (hM : E.Eff M) (L' : Language Bool) (b : Bool)
    (hin : ∀ x ∈ L', (∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some (!b)) ∧
        randProb (polyLen a k x.length) (fun r => M x r = none) ≤ 1/2)
    (hout : ∀ x ∉ L', ∀ r : Fin (polyLen a k x.length) → Bool,
        M x (List.ofFn r) ≠ some b) :
    InRP E L' := by
  classical
  refine ⟨anyVerifier (fun x r => decide (M x r = some b)) (polyLen a k)
    (polyLen 2 0), 2 * a, k, hAny _ a k 2 0 (hAns M b hM), fun x => ?_⟩
  have hlen : polyLen (2 * a) k x.length
      = polyLen a k x.length + polyLen a k x.length := by
    unfold polyLen
    ring
  -- Unfold the 2-fold `OR` on an arbitrary random string.
  have hN_iff : ∀ l : List Bool,
      anyVerifier (fun x r => decide (M x r = some b)) (polyLen a k)
          (polyLen 2 0) x l = true ↔
        (M x (l.take (polyLen a k x.length)) = some b ∨
          M x ((l.drop (polyLen a k x.length)).take
            (polyLen a k x.length)) = some b) := by
    intro l
    unfold anyVerifier
    rw [show polyLen 2 0 x.length = 2 from by unfold polyLen; ring,
      show List.range 2 = [0, 1] from rfl]
    simp
  constructor
  · -- members are accepted with probability at least `3/4`
    intro hx
    obtain ⟨hnever, habort⟩ := hin x hx
    -- one run answers `some b` with probability at least `1/2`
    have hone : 1/2 ≤ randProb (polyLen a k x.length)
        (fun l => M x l = some b) := by
      have hmono : randProb (polyLen a k x.length)
          (fun l => ¬ (M x l = none)) ≤
          randProb (polyLen a k x.length) (fun l => M x l = some b) := by
        refine randProb_mono fun r hr => ?_
        rcases hcase : M x (List.ofFn r) with _ | b'
        · exact absurd hcase hr
        · have hb' : b' ≠ !b := fun h => hnever r (h ▸ hcase)
          have hbb : b' = b := by cases b <;> cases b' <;> simp_all
          rw [hbb]
      have hnot := randProb_not (m := polyLen a k x.length)
        (fun l => M x l = none)
      linarith
    rw [hlen]
    have hstep1 : randProb (polyLen a k x.length + polyLen a k x.length)
        (fun l => ¬ (anyVerifier (fun x r => decide (M x r = some b))
          (polyLen a k) (polyLen 2 0) x l = true)) =
        randProb (polyLen a k x.length + polyLen a k x.length)
          (fun l => (fun l' => ¬ (M x l' = some b))
              (l.take (polyLen a k x.length)) ∧
            (fun w => ¬ (M x (w.take (polyLen a k x.length)) = some b))
              (l.drop (polyLen a k x.length))) :=
      randProb_congr fun rr => by
        rw [hN_iff (List.ofFn rr)]
        exact not_or
    have hstep2 := randProb_split (polyLen a k x.length) (polyLen a k x.length)
      (fun l' => ¬ (M x l' = some b))
      (fun w => ¬ (M x (w.take (polyLen a k x.length)) = some b))
    have hstep3 := randProb_take (le_refl (polyLen a k x.length))
      (fun l' => ¬ (M x l' = some b))
    have hfail : randProb (polyLen a k x.length + polyLen a k x.length)
        (fun l => ¬ (anyVerifier (fun x r => decide (M x r = some b))
          (polyLen a k) (polyLen 2 0) x l = true)) =
        randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b)) *
          randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b)) := by
      rw [hstep1, hstep2, hstep3]
    have hs_le : randProb (polyLen a k x.length)
        (fun l => ¬ (M x l = some b)) ≤ 1/2 := by
      rw [randProb_not]
      linarith
    have hs_nonneg : (0 : ℚ) ≤ randProb (polyLen a k x.length)
        (fun l => ¬ (M x l = some b)) := randProb_nonneg
    have hfail_le : randProb (polyLen a k x.length + polyLen a k x.length)
        (fun l => ¬ (anyVerifier (fun x r => decide (M x r = some b))
          (polyLen a k) (polyLen 2 0) x l = true)) ≤ 1/4 := by
      rw [hfail]
      calc randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b)) *
            randProb (polyLen a k x.length) (fun l => ¬ (M x l = some b))
          ≤ (1/2) * (1/2) := mul_le_mul hs_le hs_le hs_nonneg (by norm_num)
        _ = 1/4 := by norm_num
    have hnotN := randProb_not
      (m := polyLen a k x.length + polyLen a k x.length)
      (fun l => anyVerifier (fun x r => decide (M x r = some b))
        (polyLen a k) (polyLen 2 0) x l = true)
    linarith
  · -- non-members are never accepted
    intro hx rr
    rw [Bool.eq_false_iff]
    intro hacc
    rw [hN_iff (List.ofFn rr)] at hacc
    have hlen' : (List.ofFn rr).length
        = polyLen a k x.length + polyLen a k x.length := by
      rw [List.length_ofFn, hlen]
    rcases hacc with h | h
    · have hb1 : ((List.ofFn rr).take (polyLen a k x.length)).length
          = polyLen a k x.length := by
        rw [List.length_take, hlen']
        omega
      obtain ⟨r', hr'⟩ := exists_ofFn_eq hb1
      rw [hr'] at h
      exact hout x hx r' h
    · have hb2 : (((List.ofFn rr).drop (polyLen a k x.length)).take
          (polyLen a k x.length)).length = polyLen a k x.length := by
        rw [List.length_take, List.length_drop, hlen']
        omega
      obtain ⟨r', hr'⟩ := exists_ofFn_eq hb2
      rw [hr'] at h
      exact hout x hx r' h

/-- **`ZPP = RP ∩ coRP`** ([AB09, Thm 7.8]).  Stated relative to the
efficiency notion `E`, under the closure properties the two directions use.

**Proof sketch.** (⊆) A zero-error verifier yields an `RP` verifier by
answering `true` exactly on output `some true` (`hAns`): inputs outside `L`
are never accepted (zero error), and inputs in `L` are accepted whenever the
verifier does not abort, hence with probability at least `1/2`.  Amplify
`1/2` to `2/3` with a 2-fold `OR` (`anyVerifier`, `hAny`): soundness is
preserved (an `OR` of never-accepting runs never accepts) and the failure
probability drops to `(1/2)² = 1/4`, so success is `≥ 3/4 ≥ 2/3`.  (A strict
*majority* cannot amplify success probability exactly `1/2`, which is why
the one-sided `OR` closure is the right tool here.)  Symmetrically with
`some false` for `Lᶜ`, giving `coRP`.  (⊇) Race an `RP` verifier `M₁` for
`L` against an `RP` verifier `M₂` for `Lᶜ` on split randomness
(`raceVerifier`): a definite answer is never wrong, since `M₁` accepting
certifies `x ∈ L` and `M₂` accepting certifies `x ∉ L`; and whichever of the
two is the "live" verifier for `x` accepts with probability ≥ `2/3`, so the
race aborts with probability at most `1/3 ≤ 1/2`. -/
theorem inZPP_iff_inRP_and_inCoRP (hRace : ClosedUnderRace E)
    (hAns : ClosedUnderAnswerIs E) (hAny : ClosedUnderAny E)
    (L : Language Bool) :
    InZPP E L ↔ InRP E L ∧ InCoRP E L := by
  classical
  constructor
  · rintro ⟨M, a, k, hM, hprop⟩
    constructor
    · refine inRP_of_zeroError E hAns hAny hM L true
        (fun x hx => ⟨?_, (hprop x).2.2⟩) (fun x hx => (hprop x).2.1 hx)
      simpa using (hprop x).1 hx
    · refine inRP_of_zeroError E hAns hAny hM Lᶜ false
        (fun x hx => ⟨?_, (hprop x).2.2⟩)
        (fun x hx => (hprop x).1 (Set.not_notMem.mp hx))
      simpa using (hprop x).2.1 hx
  · rintro ⟨⟨M₁, a₁, k₁, hM₁, h₁⟩, M₂, a₂, k₂, hM₂, h₂⟩
    -- Trim `M₂` to its first `polyLen a₂ k₂` bits, then race.
    set M₂' : List Bool → List Bool → Bool :=
      anyVerifier M₂ (polyLen a₂ k₂) (polyLen 1 0) with hM₂'def
    have hM₂'eff : E.Eff (boolVerifier M₂') := hAny M₂ a₂ k₂ 1 0 hM₂
    have hM₂'eq : ∀ (x : List Bool) (w : List Bool),
        M₂' x w = M₂ x (w.take (polyLen a₂ k₂ x.length)) := by
      intro x w
      show (List.range (polyLen 1 0 x.length)).any _ = _
      rw [show polyLen 1 0 x.length = 1 by simp [polyLen]]
      show (List.range 1).any _ = _
      rw [show List.range 1 = [0] from rfl]
      simp [List.any_cons]
    refine ⟨raceVerifier M₁ M₂' (polyLen a₁ k₁), a₁ + a₂, k₁ + k₂,
      hRace M₁ M₂' a₁ k₁ hM₁ hM₂'eff, fun x => ?_⟩
    set n := x.length
    set q₁ := polyLen a₁ k₁ n with hq₁
    set q₂ := polyLen a₂ k₂ n with hq₂
    set Q := polyLen (a₁ + a₂) (k₁ + k₂) n with hQ
    have hone : 1 ≤ n + 1 := Nat.le_add_left 1 n
    have hQ₁ : q₁ ≤ Q := by
      rw [hq₁, hQ]
      unfold polyLen
      calc a₁ * (n + 1) ^ k₁ ≤ a₁ * (n + 1) ^ (k₁ + k₂) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hone (by omega))
        _ ≤ (a₁ + a₂) * (n + 1) ^ (k₁ + k₂) :=
            Nat.mul_le_mul_right _ (by omega)
    have hQ₂ : q₁ + q₂ ≤ Q := by
      rw [hq₁, hq₂, hQ]
      unfold polyLen
      have e₁ : a₁ * (n + 1) ^ k₁ ≤ a₁ * (n + 1) ^ (k₁ + k₂) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hone (by omega))
      have e₂ : a₂ * (n + 1) ^ k₂ ≤ a₂ * (n + 1) ^ (k₁ + k₂) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hone (by omega))
      calc a₁ * (n + 1) ^ k₁ + a₂ * (n + 1) ^ k₂
          ≤ a₁ * (n + 1) ^ (k₁ + k₂) + a₂ * (n + 1) ^ (k₁ + k₂) := by omega
        _ = (a₁ + a₂) * (n + 1) ^ (k₁ + k₂) := by ring
    -- Lengths of the two segments fed to the verifiers.
    have hlen₁ : ∀ rr : Fin Q → Bool, ((List.ofFn rr).take q₁).length = q₁ := by
      intro rr
      simp [List.length_take, List.length_ofFn]
      omega
    have hlen₂ : ∀ rr : Fin Q → Bool,
        (((List.ofFn rr).drop q₁).take q₂).length = q₂ := by
      intro rr
      simp [List.length_take, List.length_drop, List.length_ofFn]
      omega
    -- The three branches of the race on a concrete random string.
    have hrace_val : ∀ rr : Fin Q → Bool,
        raceVerifier M₁ M₂' (polyLen a₁ k₁) x (List.ofFn rr) =
          if M₁ x ((List.ofFn rr).take q₁) then some true
          else if M₂ x (((List.ofFn rr).drop q₁).take q₂) then some false
          else none := by
      intro rr
      show (if M₁ x ((List.ofFn rr).take q₁) then some true
        else if M₂' x ((List.ofFn rr).drop q₁) then some false else none) = _
      rw [hM₂'eq]
    refine ⟨fun hx rr => ?_, fun hx rr => ?_, ?_⟩
    · -- `x ∈ L`: never answers `some false`
      rw [hrace_val rr]
      have hx' : x ∉ Lᶜ := Set.not_notMem.mpr hx
      obtain ⟨r₂, hr₂⟩ := exists_ofFn_eq (hlen₂ rr)
      have hM₂false : M₂ x (((List.ofFn rr).drop q₁).take q₂) = false := by
        rw [hr₂]
        exact (h₂ x).2 hx' r₂
      rw [hM₂false]
      split
      · simp
      · simp
    · -- `x ∉ L`: never answers `some true`
      rw [hrace_val rr]
      obtain ⟨r₁, hr₁⟩ := exists_ofFn_eq (hlen₁ rr)
      have hM₁false : M₁ x ((List.ofFn rr).take q₁) = false := by
        rw [hr₁]
        exact (h₁ x).2 hx r₁
      rw [hM₁false]
      split
      · simp_all
      · split <;> simp
    · -- aborts with probability at most `1/2`
      obtain ⟨m₂, hm₂⟩ : ∃ m₂, Q = q₁ + m₂ := ⟨Q - q₁, by omega⟩
      have hq₂m₂ : q₂ ≤ m₂ := by omega
      have hs1 : randProb Q
          (fun l => raceVerifier M₁ M₂' (polyLen a₁ k₁) x l = none) =
          randProb Q (fun l => (fun l' => ¬ (M₁ x l' = true)) (l.take q₁) ∧
            (fun w => ¬ (M₂ x (w.take q₂) = true)) (l.drop q₁)) :=
        randProb_congr fun rr => by
          rw [hrace_val rr]
          rcases hb₁ : M₁ x ((List.ofFn rr).take q₁) <;>
            rcases hb₂ : M₂ x (((List.ofFn rr).drop q₁).take q₂) <;> simp_all
      have hs3 := randProb_split q₁ m₂ (fun l' => ¬ (M₁ x l' = true))
        (fun w => ¬ (M₂ x (w.take q₂) = true))
      have hs4 := randProb_take hq₂m₂ (fun l' => ¬ (M₂ x l' = true))
      have hnone_eq : randProb Q
          (fun l => raceVerifier M₁ M₂' (polyLen a₁ k₁) x l = none) =
          randProb q₁ (fun l => ¬ (M₁ x l = true)) *
            randProb q₂ (fun l => ¬ (M₂ x l = true)) := by
        rw [hs1, hm₂, hs3, hs4]
      rw [hnone_eq]
      by_cases hx : x ∈ L
      · have hacc := (h₁ x).1 hx
        have h1 : randProb q₁ (fun l => ¬ (M₁ x l = true)) ≤ 1/3 := by
          rw [randProb_not]
          linarith
        calc randProb q₁ (fun l => ¬ (M₁ x l = true)) *
              randProb q₂ (fun l => ¬ (M₂ x l = true))
            ≤ (1/3) * 1 := by
              refine mul_le_mul h1 randProb_le_one randProb_nonneg (by norm_num)
          _ ≤ 1/2 := by norm_num
      · have hacc := (h₂ x).1 hx
        have h2 : randProb q₂ (fun l => ¬ (M₂ x l = true)) ≤ 1/3 := by
          rw [randProb_not]
          linarith
        calc randProb q₁ (fun l => ¬ (M₁ x l = true)) *
              randProb q₂ (fun l => ¬ (M₂ x l = true))
            ≤ 1 * (1/3) := by
              refine mul_le_mul randProb_le_one h2 randProb_nonneg (by norm_num)
          _ ≤ 1/2 := by norm_num

/-- The advantage demanded of a weak `BPP` verifier on inputs of length `n`:
`min (1/6) ((n+1)^{-c})`.  For `c ≥ 1` and `n ≥ 5` this is the book's
`n^{-c}` up to the `n+1` shift (for `c = 0` both the book's `n^{-c}` and
`(n+1)^{-c}` are the constant `1`, and the cap takes over); the cap `1/6`
keeps the threshold `1/2 + weakAdv c n ≤ 2/3` attainable at small lengths,
where the book's literal `1/2 + n^{-c}` exceeds `1` (see the module
docstring's **Deviations**). -/
def weakAdv (c n : ℕ) : ℚ :=
  min (1/6) (((n : ℚ) + 1)⁻¹ ^ c)

theorem weakAdv_pos (c n : ℕ) : 0 < weakAdv c n := by
  unfold weakAdv
  refine lt_min (by norm_num) ?_
  positivity

theorem weakAdv_le_sixth (c n : ℕ) : weakAdv c n ≤ 1/6 :=
  min_le_left _ _

theorem weakAdv_ge (c n : ℕ) :
    (((n : ℚ) + 1)⁻¹) ^ c / 6 ≤ weakAdv c n := by
  have hy0 : (0:ℚ) ≤ (((n : ℚ) + 1)⁻¹) ^ c := by positivity
  have hy1 : (((n : ℚ) + 1)⁻¹) ^ c ≤ 1 := by
    refine pow_le_one₀ (by positivity) ?_
    rw [inv_le_one₀ (by positivity)]
    have := Nat.cast_nonneg (α := ℚ) n
    linarith
  unfold weakAdv
  exact le_min (by linarith) (by linarith)

/-- The arithmetic core of the amplification: with
`k(n) = 56·(n+1)^{2c+d}` repetitions, the elementary tail bound beats
`2^{-((n+1)^d + 1)}`. -/
theorem weakAdv_tail_bound (c d n : ℕ) :
    2 * (1 - 4 * weakAdv c n ^ 2) ^ (polyLen 56 (2 * c + d) n / 2) ≤
      (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := by
  have hε0 : 0 < weakAdv c n := weakAdv_pos c n
  have hε6 : weakAdv c n ≤ 1/6 := weakAdv_le_sixth c n
  set ε := weakAdv c n with hε
  have hx1 : 4 * ε ^ 2 ≤ 1 := by nlinarith
  have hx0 : (0:ℚ) ≤ 4 * ε ^ 2 := by positivity
  have hy0 : (0:ℚ) ≤ (((n : ℚ) + 1)⁻¹) ^ c := by positivity
  have hc0 : (0:ℚ) ≤ ((n : ℚ) + 1) ^ c := by positivity
  have hcancel : ((n : ℚ) + 1) ^ c * (((n : ℚ) + 1)⁻¹) ^ c = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (by positivity), one_pow]
  have hεge : (((n : ℚ) + 1)⁻¹) ^ c / 6 ≤ ε := weakAdv_ge c n
  have hm : 1 ≤ ((9 * (n + 1) ^ (2 * c) : ℕ) : ℚ) * (4 * ε ^ 2) := by
    have hcast : ((9 * (n + 1) ^ (2 * c) : ℕ) : ℚ)
        = 9 * ((n : ℚ) + 1) ^ (2 * c) := by
      push_cast
      ring
    rw [hcast]
    have h1 : (((n : ℚ) + 1)⁻¹) ^ c ≤ 6 * ε := by linarith
    have h2 : (((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c
        ≤ (6 * ε) * (6 * ε) := mul_self_le_mul_self hy0 h1
    have h3 : ((n : ℚ) + 1) ^ (2 * c) *
        ((((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c) = 1 := by
      rw [two_mul, pow_add]
      calc ((n : ℚ) + 1) ^ c * ((n : ℚ) + 1) ^ c *
            ((((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c)
          = (((n : ℚ) + 1) ^ c * (((n : ℚ) + 1)⁻¹) ^ c) *
            (((n : ℚ) + 1) ^ c * (((n : ℚ) + 1)⁻¹) ^ c) := by ring
        _ = 1 := by rw [hcancel, one_mul]
    have h4 : ((n : ℚ) + 1) ^ (2 * c) *
        ((((n : ℚ) + 1)⁻¹) ^ c * (((n : ℚ) + 1)⁻¹) ^ c)
        ≤ ((n : ℚ) + 1) ^ (2 * c) * ((6 * ε) * (6 * ε)) := by
      refine mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith [h3, h4]
  have hexp : (9 * (n + 1) ^ (2 * c)) * ((n + 1) ^ d + 2) ≤
      polyLen 56 (2 * c + d) n / 2 := by
    have h562 : polyLen 56 (2 * c + d) n / 2 = 28 * (n + 1) ^ (2 * c + d) := by
      unfold polyLen
      omega
    rw [h562, pow_add]
    have hge1 : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    have hge2 : 1 ≤ (n + 1) ^ (2 * c) := Nat.one_le_pow _ _ (by omega)
    nlinarith [hge1, hge2]
  have hhalf := one_sub_pow_le_half_pow hx0 hx1 hm hexp
  calc 2 * (1 - 4 * ε ^ 2) ^ (polyLen 56 (2 * c + d) n / 2)
      ≤ 2 * (1/2 : ℚ) ^ ((n + 1) ^ d + 2) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ = (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := by
        rw [show (n + 1) ^ d + 2 = ((n + 1) ^ d + 1) + 1 from rfl, pow_succ]
        ring

/-- `L ∈ BPP_{n^{-c}}`: like `InBPP`, but with success probability only
`1/2 + weakAdv c |x|`, i.e. an inverse-polynomial advantage over guessing.
[AB09, Lem 7.9], with the small-length repair described in the module
docstring. -/
def InBPPWeak (c : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 1/2 + weakAdv c x.length ≤
        randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 1/2 + weakAdv c x.length ≤
        randProb (polyLen a k x.length) fun r => M x r = false)

/-- `L ∈ BPP` with error at most `2^{-((|x|+1)^d + 1)}` — the amplified form
produced by error reduction.  The exponent `(|x|+1)^d + 1 ≥ |x|^d`
strengthens [AB09, Thm 7.10]'s `2^{-|x|^d}` uniformly in `|x|`, and the
`+ 1` keeps the success threshold at least `3/4 > 2/3` at *every* length
and every `d` (including `d = 0` and the empty input), so
`InBPPStrong E d L → InBPP E L` follows directly using the same witnesses
(via the arithmetic inequality `2/3 ≤ 1 − (1/2)^{(n+1)^d + 1}`), with no closure
assumption on `E`.  (With the bare exponent `(|x|+1)^d`, a fair coin would
satisfy the definition at `d = 0` for every language, and at `|x| = 0` for
every `d` — a finite exception that cannot be patched for an abstract
model.) -/
def InBPPStrong (d : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤
        randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤
        randProb (polyLen a k x.length) fun r => M x r = false)

/-- **Error reduction** ([AB09, Thm 7.10]).  A language decidable with an
inverse-polynomial advantage is decidable with success probability
`1 − 2^{-((|x|+1)^d + 1)}`, for every constant `d` — relative to `E`,
assuming `E` is closed under polynomial majority repetition.

**Proof.** Run the weak verifier `k(n) = 56·(n+1)^{2c+d}` times on
independent blocks of randomness and take the majority
(`majorityVerifier`).  The vote count is binomially distributed
(`randProb_blockCount`), and the elementary tail estimate
`randProb_tail_le` bounds the error by `2·(1 − 4ε²)^{⌊k/2⌋}` with
`ε = weakAdv c n ≥ (n+1)^{-c}/6`; the rational Bernoulli bound
`one_sub_pow_le_half_pow` then gives `≤ 2^{-((n+1)^d + 1)}`
(`weakAdv_tail_bound`).  (The book computes with `e^{−2ε²k}`; the
elementary `(4p(1−p))^{k/2}` bound proves the same statement while keeping
every quantity rational.) -/
theorem bpp_error_reduction (hMaj : ClosedUnderMajority E) {c : ℕ}
    {L : Language Bool} (hL : InBPPWeak E c L) (d : ℕ) :
    InBPPStrong E d L := by
  classical
  obtain ⟨M, a, k, hM, hprop⟩ := hL
  refine ⟨majorityVerifier M (polyLen a k) (polyLen 56 (2 * c + d)),
    56 * a, 2 * c + d + k, hMaj M a k 56 (2 * c + d) hM, fun x => ?_⟩
  have hqK : polyLen (56 * a) (2 * c + d + k) x.length
      = polyLen 56 (2 * c + d) x.length * polyLen a k x.length := by
    unfold polyLen
    ring
  set n := x.length with hn
  set q := polyLen a k n with hq
  set K := polyLen 56 (2 * c + d) n with hK
  have hε0 : 0 < weakAdv c n := weakAdv_pos c n
  -- The majority verifier accepts iff more than half the blocks accept.
  have hmaj_iff : ∀ l : List Bool,
      majorityVerifier M (polyLen a k) (polyLen 56 (2 * c + d)) x l = true ↔
        K < 2 * blockCount q K (M x) l := by
    intro l
    show decide (K < 2 * blockCount q K (M x) l) = true ↔ _
    rw [decide_eq_true_iff]
  -- Complementary vote counts.
  have hcount : ∀ l : List Bool,
      blockCount q K (M x) l +
        blockCount q K (fun l' => !(M x l')) l = K := by
    intro l
    unfold blockCount
    have haux : ∀ (p : ℕ → Bool) (li : List ℕ),
        li.countP p + li.countP (fun i => !(p i)) = li.length := by
      intro p li
      induction li with
      | nil => simp
      | cons hd tl ih =>
        rw [List.countP_cons, List.countP_cons, List.length_cons]
        rcases hp : p hd <;> simp [hp] <;> omega
    rw [haux (fun i => M x ((l.drop (i * q)).take q)) (List.range K)]
    exact List.length_range
  -- Single-run probabilities.
  have hs_false : randProb q (fun l => M x l = false)
      = 1 - randProb q (fun l => M x l = true) := randProb_bool_false (M x)
  have hs_not : randProb q (fun l => (!(M x l)) = true)
      = randProb q (fun l => M x l = false) :=
    randProb_congr fun r => by simp
  rw [hqK]
  constructor
  · -- `x ∈ L`: the failure event is `K ≤ 2·(false votes)`
    intro hx
    have hW := (hprop x).1 hx
    have hsf : randProb q (fun l => (!(M x l)) = true) ≤ 1/2 - weakAdv c n := by
      rw [hs_not, hs_false]
      linarith
    have htail := randProb_tail_le q K (fun l' => !(M x l')) hε0.le hsf
    have hev : randProb (K * q)
        (fun l => ¬ (majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x l = true))
        = randProb (K * q) (fun l =>
            K ≤ 2 * blockCount q K (fun l' => !(M x l')) l) :=
      randProb_congr fun r => by
        rw [hmaj_iff]
        have := hcount (List.ofFn r)
        constructor
        · intro h
          omega
        · intro h
          omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M (polyLen a k)
        (polyLen 56 (2 * c + d)) x l = true)
    have hbound := weakAdv_tail_bound c d n
    rw [hev] at hnot
    have : randProb (K * q) (fun l =>
        K ≤ 2 * blockCount q K (fun l' => !(M x l')) l)
        ≤ (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := le_trans htail (by
      rw [hK]
      exact hbound)
    linarith
  · -- `x ∉ L`: the failure event is `K < 2·(true votes)`
    intro hx
    have hW := (hprop x).2 hx
    have hst : randProb q (fun l => M x l = true) ≤ 1/2 - weakAdv c n := by
      have := hs_false
      linarith
    have htail := randProb_tail_le q K (M x) hε0.le hst
    have hmono : randProb (K * q)
        (fun l => ¬ (majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x l = false))
        ≤ randProb (K * q) (fun l => K ≤ 2 * blockCount q K (M x) l) := by
      refine randProb_mono fun r hr => ?_
      have h1 : majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x (List.ofFn r) = true := by
        rcases hb : majorityVerifier M (polyLen a k)
          (polyLen 56 (2 * c + d)) x (List.ofFn r)
        · exact absurd hb hr
        · rfl
      have h2 := (hmaj_iff (List.ofFn r)).mp h1
      omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M (polyLen a k)
        (polyLen 56 (2 * c + d)) x l = false)
    have hbound := weakAdv_tail_bound c d n
    have : randProb (K * q) (fun l => K ≤ 2 * blockCount q K (M x) l)
        ≤ (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := le_trans htail (by
      rw [hK]
      exact hbound)
    linarith

/-- The amplified form implies plain `BPP` membership: the success
threshold `1 − 2^{-((|x|+1)^d+1)}` is at least `3/4 ≥ 2/3` at every length,
using the same witnesses. -/
theorem InBPPStrong.toInBPP {d : ℕ} {L : Language Bool}
    (hL : InBPPStrong E d L) : InBPP E L := by
  obtain ⟨M, a, k, hM, hprop⟩ := hL
  refine ⟨M, a, k, hM, fun x => ?_⟩
  have he : 2 ≤ (x.length + 1) ^ d + 1 := by
    have := Nat.one_le_pow d (x.length + 1) (by omega)
    omega
  have hth : (2/3 : ℚ) ≤ 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) := by
    have h2 : (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤ (1/2 : ℚ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) he
    norm_num at h2
    linarith
  exact ⟨fun hx => hth.trans ((hprop x).1 hx),
    fun hx => hth.trans ((hprop x).2 hx)⟩

/-- **`BPP_{n^{-c}} = BPP`** ([AB09, Lem 7.9]): the success threshold `2/3`
in the definition of `BPP` can be weakened to an inverse-polynomial advantage
over `1/2` without changing the class.

**Proof.** `BPP ⊆ BPP_{n^{-c}}` since `weakAdv c n ≤ 1/6` makes the
weak threshold at most `2/3` at every length.  Conversely, error reduction
at `d = 0` (`bpp_error_reduction`) amplifies the weak advantage to success
probability `1 − (1/2)^{(n+1)^0+1} ≥ 3/4 ≥ 2/3`
(`InBPPStrong.toInBPP`). -/
theorem inBPPWeak_iff_inBPP (hMaj : ClosedUnderMajority E) (c : ℕ)
    (L : Language Bool) :
    InBPPWeak E c L ↔ InBPP E L := by
  constructor
  · intro hL
    exact (bpp_error_reduction E hMaj hL 0).toInBPP
  · rintro ⟨M, a, k, hM, hprop⟩
    refine ⟨M, a, k, hM, fun x => ?_⟩
    have hadv : 1/2 + weakAdv c x.length ≤ 2/3 := by
      have := weakAdv_le_sixth c x.length
      linarith
    exact ⟨fun hx => hadv.trans ((hprop x).1 hx),
      fun hx => hadv.trans ((hprop x).2 hx)⟩

end Randomized
```

## ===== TCSlib/Complexity/Randomized/Adleman.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.CircuitComplexity.PPoly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Adleman's theorem: BPP ⊆ P/poly

Arora–Barak's Theorem 7.17: every language decidable by a randomized
polynomial-time algorithm has polynomial-size circuits.  The proof is a
counting argument: after error reduction, so few random strings are bad for
any input that one string `r₀` is good for *all* inputs of a given length,
and hardwiring `r₀` turns the verifier into a circuit.

## Main definitions

* `Randomized.VerifierHasCircuits` — "each fixing of the random string turns
  the verifier into a polynomial-size circuit family", the certificate-view
  residue of "`M` is a polynomial-time TM" (see **Deviations**).

## Main results

* `Randomized.adleman` — [AB09, Thm 7.17].

## Deviations from the source

In [AB09] the verifier is a polynomial-time TM, and the hardwiring step
quotes the simulation of poly-time TMs by poly-size circuits
([AB09, Thm 6.6], `P ⊆ P/poly`).  At this file's abstract level that
simulation enters as the explicit hypothesis
`hCirc : … → VerifierHasCircuits M p` on the efficiency notion `E`; for the
polynomial-time instantiation it is dischargeable from the library's
`Complexity.P_subset_PPoly` tableau machinery (see
`Randomized.PolyTimeModel`).  Circuits are the fan-in-two
`BoolCircuit.DAGCircuit` model of `CircuitComplexity.PPoly`, and the
conclusion is `Language.InPPoly` [AB09, Def 6.5].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open BoolCircuit

variable (E : VerifierModel)

/-- The verifier `M` (with random strings of length `p n` on length-`n`
inputs) turns into polynomial-size circuits when its random string is fixed:
there are constants `a, k` such that for every `n` and every random string
`r` of length `p n`, some well-formed fan-in-two circuit of size at most
`a·(n+1)^k` computes `x ↦ M x r` on length-`n` inputs.  This is what the
polynomial-time simulation [AB09, Thm 6.6] provides for TM verifiers; note
the single size bound uniform in `r`, which the counting argument needs. -/
def VerifierHasCircuits (M : List Bool → List Bool → Bool) (p : ℕ → ℕ) :
    Prop :=
  ∃ a k : ℕ, ∀ (n : ℕ) (r : List Bool), r.length = p n →
    ∃ D : DAGCircuit n,
      D.IsWellFormed ∧ D.IsFaninTwo ∧ D.size ≤ a * (n + 1) ^ k ∧
      ∀ v : Fin n → Bool, D.eval v = M (List.ofFn v) r

/-- **Adleman's theorem: `BPP ⊆ P/poly`** ([AB09, Thm 7.17]).  Relative to
the efficiency notion `E`: if `L ∈ BPP` and `E`-verifiers have circuits when
their random string is fixed (`hCirc`, the residue of [AB09, Thm 6.6]), then
`L` has polynomial-size circuits.

**Proof sketch.** By error reduction ([AB09, Thm 7.10],
`bpp_error_reduction`) take a verifier `M` for `L` with error at most
`2^{-(n+2)}` on inputs of length `n`, using `m = p n` random bits.  Call `r`
*bad* for `x` if `M(x,r) ≠ L(x)`; for each `x` at most `2^m/2^{n+2}` strings
are bad, so at most `2^n · 2^m/2^{n+2} = 2^m/4 < 2^m` strings are bad for
*some* length-`n` input.  Hence some `r₀ ∈ {0,1}^m` is good for every
`x ∈ {0,1}^n`.  By `hCirc`, `x ↦ M x r₀` is computed by a circuit of size
polynomial in `n`, and that circuit decides `L` on length-`n` inputs; the
resulting `DAGCircuitFamily` (one good circuit per length, well-formed and
fan-in-two with the uniform size bound) witnesses `L.InSIZE (polyLen a k)`
and hence `L.InPPoly`. -/
theorem adleman (hMaj : ClosedUnderMajority E) {L : Language Bool}
    (hL : InBPP E L)
    (hCirc : ∀ M a k, E.Eff (boolVerifier M) →
      VerifierHasCircuits M (polyLen a k)) :
    L.InPPoly := by
  classical
  -- Amplify to error at most `2^{-(n+2)}` (error reduction at `d = 1`).
  obtain ⟨M, a, k, hM, hprop⟩ :=
    bpp_error_reduction E hMaj ((inBPPWeak_iff_inBPP E hMaj 0 L).mpr hL) 1
  -- At every length some random string is good for all inputs at once.
  have hgood : ∀ n : ℕ, ∃ r₀ : Fin (polyLen a k n) → Bool,
      ∀ v : Fin n → Bool,
        (List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r₀) = true) ∧
        (List.ofFn v ∉ L → M (List.ofFn v) (List.ofFn r₀) = false) := by
    intro n
    by_contra hbad
    rw [not_exists] at hbad
    have hbad' : ∀ r₀ : Fin (polyLen a k n) → Bool, ∃ v : Fin n → Bool,
        ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r₀) = true) ∧
           (List.ofFn v ∉ L → M (List.ofFn v) (List.ofFn r₀) = false)) :=
      fun r₀ => not_forall.mp (hbad r₀)
    -- each input's bad set has probability at most `2^{-(n+2)}`
    have hv : ∀ v : Fin n → Bool,
        randProb (polyLen a k n) (fun l =>
          ¬ ((List.ofFn v ∈ L → M (List.ofFn v) l = true) ∧
             (List.ofFn v ∉ L → M (List.ofFn v) l = false))) ≤
          (1/2 : ℚ) ^ (n + 2) := by
      intro v
      have hlen : (List.ofFn v).length = n := List.length_ofFn
      have hth := hprop (List.ofFn v)
      rw [hlen] at hth
      have hexp : (n + 1) ^ 1 + 1 = n + 2 := by ring
      by_cases hxL : List.ofFn v ∈ L
      · have h1 := hth.1 hxL
        rw [hexp] at h1
        have hcongr : randProb (polyLen a k n) (fun l =>
            ¬ ((List.ofFn v ∈ L → M (List.ofFn v) l = true) ∧
               (List.ofFn v ∉ L → M (List.ofFn v) l = false))) =
            randProb (polyLen a k n)
              (fun l => ¬ (M (List.ofFn v) l = true)) :=
          randProb_congr fun r => by simp [hxL]
        rw [hcongr, randProb_not]
        linarith
      · have h1 := hth.2 hxL
        rw [hexp] at h1
        have hcongr : randProb (polyLen a k n) (fun l =>
            ¬ ((List.ofFn v ∈ L → M (List.ofFn v) l = true) ∧
               (List.ofFn v ∉ L → M (List.ofFn v) l = false))) =
            randProb (polyLen a k n)
              (fun l => ¬ (M (List.ofFn v) l = false)) :=
          randProb_congr fun r => by simp [hxL]
        rw [hcongr, randProb_not]
        linarith
    -- turn the probabilities into cardinalities and union-bound
    set m := polyLen a k n with hm
    have hcardv : ∀ v : Fin n → Bool,
        ((Finset.univ.filter fun r : Fin m → Bool =>
          ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r) = true) ∧
             (List.ofFn v ∉ L → M (List.ofFn v) (List.ofFn r) = false))).card
          : ℚ) ≤ (1/2 : ℚ) ^ (n + 2) * 2 ^ m := by
      intro v
      have := hv v
      unfold randProb at this
      rw [div_le_iff₀ (by positivity)] at this
      exact this
    have hcover : (Finset.univ : Finset (Fin m → Bool)) ⊆
        Finset.univ.biUnion (fun v : Fin n → Bool =>
          Finset.univ.filter fun r : Fin m → Bool =>
            ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r) = true) ∧
               (List.ofFn v ∉ L → M (List.ofFn v) (List.ofFn r) = false))) := by
      intro r _
      obtain ⟨v, hv'⟩ := hbad' r
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v,
        Finset.mem_filter.mpr ⟨Finset.mem_univ r, hv'⟩⟩
    have hcard : ((2 : ℚ)) ^ m ≤ (2 : ℚ) ^ n * ((1/2 : ℚ) ^ (n + 2) * 2 ^ m) := by
      have h1 : (2 : ℕ) ^ m ≤ (Finset.univ.biUnion
          (fun v : Fin n → Bool =>
            Finset.univ.filter fun r : Fin m → Bool =>
              ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r) = true) ∧
                 (List.ofFn v ∉ L →
                   M (List.ofFn v) (List.ofFn r) = false)))).card := by
        rw [← card_univ_bitstrings m]
        exact Finset.card_le_card hcover
      have h2 := Finset.card_biUnion_le
        (s := (Finset.univ : Finset (Fin n → Bool)))
        (t := fun v : Fin n → Bool =>
          Finset.univ.filter fun r : Fin m → Bool =>
            ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r) = true) ∧
               (List.ofFn v ∉ L → M (List.ofFn v) (List.ofFn r) = false)))
      have h3 : ((2 : ℚ)) ^ m ≤
          ∑ v : Fin n → Bool, ((Finset.univ.filter fun r : Fin m → Bool =>
            ¬ ((List.ofFn v ∈ L → M (List.ofFn v) (List.ofFn r) = true) ∧
               (List.ofFn v ∉ L →
                 M (List.ofFn v) (List.ofFn r) = false))).card : ℚ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast le_trans h1 h2
      calc ((2 : ℚ)) ^ m ≤ ∑ _v : Fin n → Bool,
            ((1/2 : ℚ) ^ (n + 2) * 2 ^ m) :=
            le_trans h3 (Finset.sum_le_sum fun v _ => hcardv v)
        _ = (2 : ℚ) ^ n * ((1/2 : ℚ) ^ (n + 2) * 2 ^ m) := by
            rw [Finset.sum_const, card_univ_bitstrings, nsmul_eq_mul]
            push_cast
            ring
    -- but `2^n · 2^{-(n+2)} = 1/4 < 1`
    have hq : (2 : ℚ) ^ n * (1/2 : ℚ) ^ (n + 2) = 1/4 := by
      rw [div_pow, one_pow, pow_add]
      field_simp
      ring
    nlinarith [pow_pos (by norm_num : (0:ℚ) < 2) m, hcard, hq]
  choose r₀ hr₀ using hgood
  obtain ⟨a', k', hC⟩ := hCirc M a k hM
  have hDn : ∀ n : ℕ, ∃ D : DAGCircuit n,
      D.IsWellFormed ∧ D.IsFaninTwo ∧ D.size ≤ a' * (n + 1) ^ k' ∧
      ∀ v : Fin n → Bool, D.eval v = M (List.ofFn v) (List.ofFn (r₀ n)) :=
    fun n => hC n (List.ofFn (r₀ n)) List.length_ofFn
  choose D hD using hDn
  refine ⟨a', k', ⟨D⟩, fun n => (hD n).2.1, fun n => (hD n).2.2.1, ?_⟩
  ext w
  rw [DAGCircuitFamily.mem_language_iff]
  have heval := (hD w.length).2.2.2 w.get
  rw [List.ofFn_get] at heval
  constructor
  · intro hacc
    by_contra hw
    have := (hr₀ w.length w.get).2
    rw [List.ofFn_get] at this
    rw [heval, this hw] at hacc
    exact absurd hacc (by simp)
  · intro hw
    have := (hr₀ w.length w.get).1
    rw [List.ofFn_get] at this
    rw [heval, this hw]

end Randomized
```

## ===== TCSlib/Complexity/Randomized/SipserGacs.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Classes

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Sipser–Gács theorem: BPP ⊆ Σ₂ ∩ Π₂

Arora–Barak's Theorem 7.18: `BPP` sits in the second level of the polynomial
hierarchy.  The proof shows `BPP ⊆ Σ₂`: after error reduction the set `S_x`
of accepting random strings is either almost all of `{0,1}^m` or a tiny
fraction, and two quantifier alternations — "there exist shifts `u₁,…,u_k`
whose translates of `S_x` cover `{0,1}^m`" — distinguish the two cases.

## Main definitions

* `Randomized.InSigma2`, `Randomized.InPi2` — verifier-style `Σ₂ᵖ` and `Π₂ᵖ`
  (two quantified witness strings over an efficient predicate), the classes
  in which [AB09, Thm 7.18] places `BPP`.
* `Randomized.shiftOrVerifier` — the predicate
  `(u, v) ↦ ⋁_{i ≤ k} M(x, v ⊕ uᵢ)` built from a `BPP` verifier, where `u`
  encodes the `k` shifts `u₁,…,u_k` as one concatenated string.

## Main results

* `Randomized.bpp_subset_sigma2` — `BPP ⊆ Σ₂ᵖ`, the core argument.
* `Randomized.sipser_gacs` — [AB09, Thm 7.18].

## Deviations from the source

`Σ₂ᵖ` is defined here in the same certificate style as the chapter's other
classes (an efficient two-witness predicate with polynomially-bounded
witness lengths), rather than via oracle machines or the book's Chapter 5
definitions; `Π₂ᵖ` is its complement-dual, and `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` becomes
"`L` and `Lᶜ` are both `Σ₂`".  As throughout `Randomized.Classes`,
"polynomial time" is the abstract notion `E`, and the single computability
fact the proof uses — that the shifted-OR predicate built from an efficient
verifier is an efficient two-witness predicate — is the explicit hypothesis
`hShift`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

variable (E : VerifierModel)

/-- `L ∈ Σ₂ᵖ`, certificate-style: there is an efficient two-witness
predicate `N` and polynomial witness-length bounds such that
`x ∈ L ↔ ∃ u ∀ v, N(x, u, v)`.  [AB09, Thm 7.18]'s target class, defined in
the style of [AB09, Def 7.4] (see the module docstring's **Deviations**). -/
def InSigma2 (L : Language Bool) : Prop :=
  ∃ (N : List Bool → List Bool → List Bool → Bool) (a₁ k₁ a₂ k₂ : ℕ),
    E.EffTwoWitness N ∧
    ∀ x : List Bool,
      x ∈ L ↔ ∃ u : List Bool, u.length = polyLen a₁ k₁ x.length ∧
        ∀ v : List Bool, v.length = polyLen a₂ k₂ x.length → N x u v = true

/-- `L ∈ Π₂ᵖ` iff its complement is in `Σ₂ᵖ` (equivalently,
`x ∈ L ↔ ∀ u ∃ v, …`). -/
def InPi2 (L : Language Bool) : Prop :=
  InSigma2 E Lᶜ

/-- The two-witness predicate `(u, v) ↦ ⋁_{i < k} M(x, v ⊕ uᵢ)`, where the
first witness `u` is the concatenation of `k` shift strings `u₁,…,u_k` of
length `p(|x|)` each and `⊕` is bitwise XOR: the predicate with which
[AB09, Thm 7.18]'s proof expresses "the translates of the accepting set by
`u₁,…,u_k` cover all random strings `v`". -/
def shiftOrVerifier (M : List Bool → List Bool → Bool) (p k : ℕ → ℕ) :
    List Bool → List Bool → List Bool → Bool := fun x u v =>
  (List.range (k x.length)).any fun i =>
    M x (List.zipWith xor v ((u.drop (i * p x.length)).take (p x.length)))

/-- `E` recognizes the shifted-OR construction: from an efficient Boolean
verifier, the predicate `shiftOrVerifier M p k` is an efficient two-witness
predicate for polynomial block lengths `p` and shift counts `k` (closure of
polynomial time under XOR-shifts and a polynomial OR). -/
def ClosedUnderShiftOr : Prop :=
  ∀ M a k a' k', E.Eff (boolVerifier M) →
    E.EffTwoWitness (shiftOrVerifier M (polyLen a k) (polyLen a' k'))

section Helpers

/-- `zipWith` of two `ofFn` lists is the `ofFn` of the pointwise image. -/
theorem zipWith_ofFn {α β γ : Type*} {m : ℕ} (f : α → β → γ)
    (a : Fin m → α) (b : Fin m → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) =
      List.ofFn (fun i => f (a i) (b i)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

/-- XOR-ing the random string with a fixed mask (on the left) preserves
probabilities: the map `r ↦ c ⊕ r` is an involution of `{0,1}^m`. -/
theorem randProb_xor_right {m : ℕ} (c : Fin m → Bool)
    (P : List Bool → Prop) [DecidablePred P] :
    randProb m (fun l => P (List.zipWith xor (List.ofFn c) l)) =
      randProb m P := by
  unfold randProb
  congr 2
  have hinv : ∀ r : Fin m → Bool,
      (fun i => xor (c i) (xor (c i) (r i))) = r := by
    intro r
    funext i
    cases c i <;> cases r i <;> rfl
  refine Finset.card_nbij' (fun r => fun i => xor (c i) (r i))
    (fun r => fun i => xor (c i) (r i)) ?_ ?_ ?_ ?_
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
      true_and] at hr ⊢
    show P (List.ofFn fun i => xor (c i) (r i))
    rw [← zipWith_ofFn]
    exact hr
  · intro r hr
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ,
      true_and] at hr ⊢
    show P (List.zipWith xor (List.ofFn c)
      (List.ofFn fun i => xor (c i) (r i)))
    rw [zipWith_ofFn, hinv r]
    exact hr
  · intro r _
    funext i
    show xor (c i) (xor (c i) (r i)) = r i
    cases c i <;> cases r i <;> rfl
  · intro r _
    funext i
    show xor (c i) (xor (c i) (r i)) = r i
    cases c i <;> cases r i <;> rfl

/-- XOR-ing the random string with a fixed mask (on the right) preserves
probabilities. -/
theorem randProb_xor_left {m : ℕ} (c : Fin m → Bool)
    (P : List Bool → Prop) [DecidablePred P] :
    randProb m (fun l => P (List.zipWith xor l (List.ofFn c))) =
      randProb m P := by
  have hswap : ∀ r : Fin m → Bool,
      List.zipWith xor (List.ofFn r) (List.ofFn c) =
        List.zipWith xor (List.ofFn c) (List.ofFn r) := by
    intro r
    rw [zipWith_ofFn, zipWith_ofFn]
    congr 1
    funext i
    cases c i <;> cases r i <;> rfl
  rw [randProb_congr (B := fun l => P (List.zipWith xor (List.ofFn c) l))
    fun r => by rw [hswap r]]
  exact randProb_xor_right c P

/-- The exponential beats the linear shift count:
`(19A+20)·X < 2^{(A+7)·X}` for `X ≥ 1`.  (The book's choice `k = ⌈m/n⌉+1`
needs `k < 2^n`, which fails at small `n`; balancing against the error
exponent instead works at every length.) -/
theorem shift_count_lt_two_pow (A X : ℕ) (hX : 1 ≤ X) :
    (19 * A + 20) * X < 2 ^ ((A + 7) * X) := by
  have h128 : 128 * X ≤ 128 ^ X := by
    clear hX
    induction X with
    | zero => omega
    | succ Y ih =>
      rcases Nat.eq_zero_or_pos Y with rfl | hY'
      · norm_num
      · have h1 : 128 ^ (Y + 1) = 128 ^ Y * 128 := pow_succ 128 Y
        nlinarith
  have hA : A + 1 ≤ 2 ^ A := Nat.lt_two_pow_self
  have hsplit : 2 ^ ((A + 7) * X) = (2 ^ A) ^ X * 128 ^ X := by
    rw [pow_mul, pow_add, mul_pow]
    norm_num
  have h3 : 2 ^ A ≤ (2 ^ A) ^ X := by
    conv_lhs => rw [← pow_one (2 ^ A)]
    exact Nat.pow_le_pow_right Nat.one_le_two_pow hX
  calc (19 * A + 20) * X < (128 * (A + 1)) * X :=
      (Nat.mul_lt_mul_right (by omega)).mpr (by omega)
    _ = (A + 1) * (128 * X) := by ring
    _ ≤ (2 ^ A) * (128 * X) := Nat.mul_le_mul_right _ hA
    _ ≤ (2 ^ A) ^ X * 128 ^ X := Nat.mul_le_mul h3 h128
    _ = 2 ^ ((A + 7) * X) := hsplit.symm

/-- The tail crunch for the constant advantage `1/6`: `(18b+18)·(n+1)^e`
majority repetitions drive the error below `2^{-b(n+1)^e}`. -/
theorem const_tail_bound (b e n : ℕ) :
    2 * (1 - 4 * (1/6 : ℚ) ^ 2) ^ (polyLen (18 * b + 18) e n / 2) ≤
      (1/2 : ℚ) ^ polyLen b e n := by
  have hx0 : (0:ℚ) ≤ 4 * (1/6 : ℚ) ^ 2 := by norm_num
  have hx1 : 4 * (1/6 : ℚ) ^ 2 ≤ 1 := by norm_num
  have hm : 1 ≤ ((9 : ℕ) : ℚ) * (4 * (1/6 : ℚ) ^ 2) := by norm_num
  have hexp : 9 * (polyLen b e n + 1) ≤ polyLen (18 * b + 18) e n / 2 := by
    unfold polyLen
    have h1 : (18 * b + 18) * (n + 1) ^ e / 2 = (9 * b + 9) * (n + 1) ^ e := by
      rw [show 18 * b + 18 = 2 * (9 * b + 9) from by ring, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num)]
    rw [h1]
    have hge : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hhalf := one_sub_pow_le_half_pow hx0 hx1 hm hexp
  calc 2 * (1 - 4 * (1/6 : ℚ) ^ 2) ^ (polyLen (18 * b + 18) e n / 2)
      ≤ 2 * (1/2 : ℚ) ^ (polyLen b e n + 1) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
    _ = (1/2 : ℚ) ^ polyLen b e n := by
        rw [pow_succ]
        ring

/-- Error reduction with an explicit error schedule `2^{-b(n+1)^e}` and an
explicit randomness schedule — the form [AB09, Thm 7.18]'s proof consumes:
a `BPP` witness `(M₀, a₀, k₀)` amplified by `(18b+18)·(n+1)^e` majority
repetitions. -/
theorem amplify_concrete (hMaj : ClosedUnderMajority E) {L : Language Bool}
    {M₀ : List Bool → List Bool → Bool} {a₀ k₀ : ℕ}
    (hM₀ : E.Eff (boolVerifier M₀))
    (hprop₀ : ∀ x : List Bool,
      (x ∈ L → 2/3 ≤
        randProb (polyLen a₀ k₀ x.length) fun r => M₀ x r = true) ∧
      (x ∉ L → 2/3 ≤
        randProb (polyLen a₀ k₀ x.length) fun r => M₀ x r = false))
    (b e : ℕ) :
    ∃ M : List Bool → List Bool → Bool,
      E.Eff (boolVerifier M) ∧
      ∀ x : List Bool,
        (x ∈ L → 1 - (1/2 : ℚ) ^ polyLen b e x.length ≤
          randProb (polyLen ((18 * b + 18) * a₀) (e + k₀) x.length)
            fun r => M x r = true) ∧
        (x ∉ L → 1 - (1/2 : ℚ) ^ polyLen b e x.length ≤
          randProb (polyLen ((18 * b + 18) * a₀) (e + k₀) x.length)
            fun r => M x r = false) := by
  classical
  refine ⟨majorityVerifier M₀ (polyLen a₀ k₀) (polyLen (18 * b + 18) e),
    hMaj M₀ a₀ k₀ (18 * b + 18) e hM₀, fun x => ?_⟩
  have hqK : polyLen ((18 * b + 18) * a₀) (e + k₀) x.length
      = polyLen (18 * b + 18) e x.length * polyLen a₀ k₀ x.length := by
    unfold polyLen
    ring
  set n := x.length with hn
  set q := polyLen a₀ k₀ n with hq
  set K := polyLen (18 * b + 18) e n with hK
  have hmaj_iff : ∀ l : List Bool,
      majorityVerifier M₀ (polyLen a₀ k₀)
          (polyLen (18 * b + 18) e) x l = true ↔
        K < 2 * blockCount q K (M₀ x) l := by
    intro l
    show decide (K < 2 * blockCount q K (M₀ x) l) = true ↔ _
    rw [decide_eq_true_iff]
  have hcount : ∀ l : List Bool,
      blockCount q K (M₀ x) l +
        blockCount q K (fun l' => !(M₀ x l')) l = K := by
    intro l
    unfold blockCount
    have haux : ∀ (p : ℕ → Bool) (li : List ℕ),
        li.countP p + li.countP (fun i => !(p i)) = li.length := by
      intro p li
      induction li with
      | nil => simp
      | cons hd tl ih =>
        rw [List.countP_cons, List.countP_cons, List.length_cons]
        rcases hp : p hd <;> simp [hp] <;> omega
    rw [haux (fun i => M₀ x ((l.drop (i * q)).take q)) (List.range K)]
    exact List.length_range
  have hs_false : randProb q (fun l => M₀ x l = false)
      = 1 - randProb q (fun l => M₀ x l = true) := randProb_bool_false (M₀ x)
  have hs_not : randProb q (fun l => (!(M₀ x l)) = true)
      = randProb q (fun l => M₀ x l = false) :=
    randProb_congr fun r => by simp
  rw [hqK]
  constructor
  · intro hx
    have hW := (hprop₀ x).1 hx
    have hsf : randProb q (fun l => (!(M₀ x l)) = true) ≤ 1/2 - 1/6 := by
      rw [hs_not, hs_false]
      linarith
    have htail := randProb_tail_le q K (fun l' => !(M₀ x l'))
      (by norm_num : (0:ℚ) ≤ 1/6) hsf
    have hev : randProb (K * q)
        (fun l => ¬ (majorityVerifier M₀ (polyLen a₀ k₀)
          (polyLen (18 * b + 18) e) x l = true))
        = randProb (K * q) (fun l =>
            K ≤ 2 * blockCount q K (fun l' => !(M₀ x l')) l) :=
      randProb_congr fun r => by
        rw [hmaj_iff]
        have := hcount (List.ofFn r)
        constructor
        · intro h
          omega
        · intro h
          omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M₀ (polyLen a₀ k₀)
        (polyLen (18 * b + 18) e) x l = true)
    rw [hev] at hnot
    have hfin : randProb (K * q) (fun l =>
        K ≤ 2 * blockCount q K (fun l' => !(M₀ x l')) l)
        ≤ (1/2 : ℚ) ^ polyLen b e n := le_trans htail (by
      rw [hK]
      exact const_tail_bound b e n)
    linarith
  · intro hx
    have hW := (hprop₀ x).2 hx
    have hst : randProb q (fun l => M₀ x l = true) ≤ 1/2 - 1/6 := by
      have := hs_false
      linarith
    have htail := randProb_tail_le q K (M₀ x)
      (by norm_num : (0:ℚ) ≤ 1/6) hst
    have hmono : randProb (K * q)
        (fun l => ¬ (majorityVerifier M₀ (polyLen a₀ k₀)
          (polyLen (18 * b + 18) e) x l = false))
        ≤ randProb (K * q) (fun l => K ≤ 2 * blockCount q K (M₀ x) l) := by
      refine randProb_mono fun r hr => ?_
      have h1 : majorityVerifier M₀ (polyLen a₀ k₀)
          (polyLen (18 * b + 18) e) x (List.ofFn r) = true := by
        rcases hb : majorityVerifier M₀ (polyLen a₀ k₀)
          (polyLen (18 * b + 18) e) x (List.ofFn r)
        · exact absurd hb hr
        · rfl
      have h2 := (hmaj_iff (List.ofFn r)).mp h1
      omega
    have hnot := randProb_not (m := K * q)
      (fun l => majorityVerifier M₀ (polyLen a₀ k₀)
        (polyLen (18 * b + 18) e) x l = false)
    have hfin : randProb (K * q) (fun l =>
        K ≤ 2 * blockCount q K (M₀ x) l)
        ≤ (1/2 : ℚ) ^ polyLen b e n := le_trans htail (by
      rw [hK]
      exact const_tail_bound b e n)
    linarith

end Helpers

/-- A set smaller than the whole type misses some element. -/
theorem exists_notMem_of_card_lt {α : Type*} [Fintype α]
    {S : Finset α} (h : S.card < Fintype.card α) : ∃ a, a ∉ S := by
  by_contra hall
  push_neg at hall
  have heq : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
  rw [heq, Finset.card_univ] at h
  exact absurd h (lt_irrefl _)

/-- **`BPP ⊆ Σ₂ᵖ`**, the core of [AB09, Thm 7.18]. -/
theorem bpp_subset_sigma2 (hMaj : ClosedUnderMajority E)
    (hShift : ClosedUnderShiftOr E) {L : Language Bool} (hL : InBPP E L) :
    InSigma2 E L := by
  classical
  obtain ⟨M₀, a₀, k₀, hM₀, hprop₀⟩ := hL
  obtain ⟨M, hM, hprop⟩ := amplify_concrete E hMaj hM₀ hprop₀ (a₀ + 7) k₀
  refine ⟨shiftOrVerifier M (polyLen ((18 * (a₀ + 7) + 18) * a₀) (k₀ + k₀))
      (polyLen (19 * a₀ + 20) k₀),
    (19 * a₀ + 20) * ((18 * (a₀ + 7) + 18) * a₀), k₀ + (k₀ + k₀),
    (18 * (a₀ + 7) + 18) * a₀, k₀ + k₀,
    hShift M ((18 * (a₀ + 7) + 18) * a₀) (k₀ + k₀) (19 * a₀ + 20) k₀ hM,
    fun x => ?_⟩
  set n := x.length with hn
  set m := polyLen ((18 * (a₀ + 7) + 18) * a₀) (k₀ + k₀) n with hm
  set T := polyLen (a₀ + 7) k₀ n with hT
  set ks := polyLen (19 * a₀ + 20) k₀ n with hks
  have hX1 : 1 ≤ (n + 1) ^ k₀ := Nat.one_le_pow _ _ (by omega)
  have hulen : polyLen ((19 * a₀ + 20) * ((18 * (a₀ + 7) + 18) * a₀))
      (k₀ + (k₀ + k₀)) n = ks * m := by
    rw [hks, hm]
    unfold polyLen
    ring
  have hclaim1 : ((ks : ℕ) : ℚ) < 2 ^ T := by
    rw [hks, hT]
    unfold polyLen
    exact_mod_cast shift_count_lt_two_pow a₀ ((n + 1) ^ k₀) hX1
  have hclaim2 : m < T * ks := by
    rw [hm, hT, hks]
    unfold polyLen
    have hXX : (n + 1) ^ (k₀ + k₀) = (n + 1) ^ k₀ * (n + 1) ^ k₀ :=
      pow_add _ _ _
    rw [hXX]
    have hC : (18 * (a₀ + 7) + 18) * a₀ < (a₀ + 7) * (19 * a₀ + 20) := by
      nlinarith
    calc (18 * (a₀ + 7) + 18) * a₀ * ((n + 1) ^ k₀ * (n + 1) ^ k₀)
        < (a₀ + 7) * (19 * a₀ + 20) * ((n + 1) ^ k₀ * (n + 1) ^ k₀) := by
          have hXp : 0 < (n + 1) ^ k₀ * (n + 1) ^ k₀ := by positivity
          exact (Nat.mul_lt_mul_right hXp).mpr hC
      _ = (a₀ + 7) * (n + 1) ^ k₀ * ((19 * a₀ + 20) * (n + 1) ^ k₀) := by
          ring
  have hacc := hprop x
  rw [← hn, ← hm, ← hT] at hacc
  constructor
  · -- `x ∈ L`: the probabilistic method produces covering shifts
    intro hx
    have haccx := hacc.1 hx
    have hs1 : randProb m (fun l => M x l = true) ≤ 1 := randProb_le_one
    have hfail : 1 - randProb m (fun l => M x l = true) ≤ (1/2 : ℚ) ^ T := by
      linarith
    have hfail0 : (0:ℚ) ≤ 1 - randProb m (fun l => M x l = true) := by
      linarith
    have hbadv : ∀ v : Fin m → Bool,
        ((Finset.univ.filter fun u : Fin (ks * m) → Bool =>
          blockCount m ks (fun w => M x (List.zipWith xor (List.ofFn v) w))
            (List.ofFn u) = 0).card : ℚ)
          ≤ (1/2 : ℚ) ^ (T * ks) * 2 ^ (ks * m) := by
      intro v
      have hsB : randProb m (fun w =>
          M x (List.zipWith xor (List.ofFn v) w) = true)
          = randProb m (fun l => M x l = true) :=
        randProb_xor_right v (fun w => M x w = true)
      have hdist := randProb_blockCount m
        (fun w => M x (List.zipWith xor (List.ofFn v) w)) ks 0
        (Nat.zero_le _)
      rw [hsB] at hdist
      simp only [Nat.choose_zero_right, pow_zero, Nat.cast_one, one_mul,
        Nat.sub_zero] at hdist
      have hle : randProb (ks * m) (fun l =>
          blockCount m ks (fun w => M x (List.zipWith xor (List.ofFn v) w))
            l = 0) ≤ (1/2 : ℚ) ^ (T * ks) := by
        rw [hdist]
        calc (1 - randProb m (fun l => M x l = true)) ^ ks
            ≤ ((1/2 : ℚ) ^ T) ^ ks := pow_le_pow_left₀ hfail0 hfail ks
          _ = (1/2 : ℚ) ^ (T * ks) := by rw [← pow_mul]
      unfold randProb at hle
      rw [div_le_iff₀ (by positivity)] at hle
      exact hle
    have hexists : ∃ u : Fin (ks * m) → Bool, ∀ v : Fin m → Bool,
        blockCount m ks (fun w => M x (List.zipWith xor (List.ofFn v) w))
          (List.ofFn u) ≠ 0 := by
      by_contra hforall
      push_neg at hforall
      have hcover : (Finset.univ : Finset (Fin (ks * m) → Bool)) ⊆
          Finset.univ.biUnion (fun v : Fin m → Bool =>
            Finset.univ.filter fun u : Fin (ks * m) → Bool =>
              blockCount m ks
                (fun w => M x (List.zipWith xor (List.ofFn v) w))
                (List.ofFn u) = 0) := by
        intro u _
        obtain ⟨v, hv⟩ := hforall u
        exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v,
          Finset.mem_filter.mpr ⟨Finset.mem_univ u, hv⟩⟩
      have h1 : (2:ℕ) ^ (ks * m) ≤ (Finset.univ.biUnion
          (fun v : Fin m → Bool =>
            Finset.univ.filter fun u : Fin (ks * m) → Bool =>
              blockCount m ks
                (fun w => M x (List.zipWith xor (List.ofFn v) w))
                (List.ofFn u) = 0)).card := by
        rw [← card_univ_bitstrings (ks * m)]
        exact Finset.card_le_card hcover
      have h2 := Finset.card_biUnion_le
        (s := (Finset.univ : Finset (Fin m → Bool)))
        (t := fun v : Fin m → Bool =>
          Finset.univ.filter fun u : Fin (ks * m) → Bool =>
            blockCount m ks
              (fun w => M x (List.zipWith xor (List.ofFn v) w))
              (List.ofFn u) = 0)
      have h3 : ((2:ℚ)) ^ (ks * m) ≤
          ∑ v : Fin m → Bool, ((Finset.univ.filter
            fun u : Fin (ks * m) → Bool =>
              blockCount m ks
                (fun w => M x (List.zipWith xor (List.ofFn v) w))
                (List.ofFn u) = 0).card : ℚ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast le_trans h1 h2
      have h4 : ((2:ℚ)) ^ (ks * m) ≤
          (2:ℚ) ^ m * ((1/2 : ℚ) ^ (T * ks) * 2 ^ (ks * m)) := by
        calc ((2:ℚ)) ^ (ks * m)
            ≤ ∑ _v : Fin m → Bool, ((1/2 : ℚ) ^ (T * ks) * 2 ^ (ks * m)) :=
              le_trans h3 (Finset.sum_le_sum fun v _ => hbadv v)
          _ = (2:ℚ) ^ m * ((1/2 : ℚ) ^ (T * ks) * 2 ^ (ks * m)) := by
              rw [Finset.sum_const, card_univ_bitstrings, nsmul_eq_mul]
              push_cast
              ring
      have hlt : ((2:ℚ)) ^ m < 2 ^ (T * ks) :=
        pow_lt_pow_right₀ (by norm_num) hclaim2
      have hfrac : (2:ℚ) ^ m * (1/2 : ℚ) ^ (T * ks) < 1 := by
        rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
        exact hlt
      nlinarith [pow_pos (show (0:ℚ) < 2 by norm_num) (ks * m), h4, hfrac]
    obtain ⟨u, hu⟩ := hexists
    refine ⟨List.ofFn u, ?_, ?_⟩
    · rw [List.length_ofFn]
      exact hulen.symm
    · intro v hvlen
      obtain ⟨v', hv'⟩ := exists_ofFn_eq hvlen
      have hbc := hu v'
      have hpos : 0 < blockCount m ks
          (fun w => M x (List.zipWith xor (List.ofFn v') w))
          (List.ofFn u) := Nat.pos_of_ne_zero hbc
      unfold blockCount at hpos
      rw [List.countP_pos_iff] at hpos
      obtain ⟨i, hi_mem, hi⟩ := hpos
      show (List.range ks).any _ = true
      rw [List.any_eq_true]
      refine ⟨i, hi_mem, ?_⟩
      rw [hv']
      exact hi
  · -- `x ∉ L`: no shifts can cover, by counting the accepted strings
    rintro ⟨u, hu_len, hall⟩
    by_contra hx
    have hrej := hacc.2 hx
    have hboolf := randProb_bool_false (m := m) (M x)
    have hst : randProb m (fun l => M x l = true) ≤ (1/2 : ℚ) ^ T := by
      linarith
    rw [hulen] at hu_len
    have hblock_len : ∀ i, i < ks → ((u.drop (i * m)).take m).length = m := by
      intro i hi
      have h1 : (i + 1) * m ≤ ks * m := Nat.mul_le_mul_right m (by omega)
      rw [Nat.succ_mul] at h1
      rw [List.length_take, List.length_drop, hu_len]
      omega
    have hacc_card : ∀ i ∈ Finset.range ks,
        ((Finset.univ.filter fun v : Fin m → Bool =>
          M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
            = true).card : ℚ) ≤ (1/2 : ℚ) ^ T * 2 ^ m := by
      intro i hi
      obtain ⟨ci, hci⟩ := exists_ofFn_eq (hblock_len i (Finset.mem_range.mp hi))
      have hxor : randProb m (fun l =>
          M x (List.zipWith xor l (List.ofFn ci)) = true)
          = randProb m (fun l => M x l = true) :=
        randProb_xor_left ci (fun w => M x w = true)
      have hle : randProb m (fun l =>
          M x (List.zipWith xor l ((u.drop (i * m)).take m)) = true)
          ≤ (1/2 : ℚ) ^ T := by
        rw [show (u.drop (i * m)).take m = List.ofFn ci from hci, hxor]
        exact hst
      unfold randProb at hle
      rw [div_le_iff₀ (by positivity)] at hle
      exact hle
    have hcover : (Finset.univ.filter fun v : Fin m → Bool =>
        ∃ i ∈ Finset.range ks,
          M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
            = true) ⊆
        (Finset.range ks).biUnion (fun i =>
          Finset.univ.filter fun v : Fin m → Bool =>
            M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
              = true) := by
      intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨-, i, hi, hMi⟩ := hv
      exact Finset.mem_biUnion.mpr ⟨i, hi,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMi⟩⟩
    have hcard : ((Finset.univ.filter fun v : Fin m → Bool =>
        ∃ i ∈ Finset.range ks,
          M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
            = true).card : ℚ) < 2 ^ m := by
      have h1 := Finset.card_le_card hcover
      have h2 := Finset.card_biUnion_le (s := Finset.range ks)
        (t := fun i => Finset.univ.filter fun v : Fin m → Bool =>
          M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
            = true)
      have h3 : ((Finset.univ.filter fun v : Fin m → Bool =>
          ∃ i ∈ Finset.range ks, M x (List.zipWith xor (List.ofFn v)
            ((u.drop (i * m)).take m)) = true).card : ℚ) ≤
          ∑ i ∈ Finset.range ks, ((Finset.univ.filter
            fun v : Fin m → Bool => M x (List.zipWith xor (List.ofFn v)
              ((u.drop (i * m)).take m)) = true).card : ℚ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast le_trans h1 h2
      have h6 : (ks : ℚ) * ((1/2 : ℚ) ^ T * 2 ^ m) < 2 ^ m := by
        have h7 : (ks : ℚ) * (1/2 : ℚ) ^ T < 1 := by
          rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
          exact hclaim1
        nlinarith [pow_pos (show (0:ℚ) < 2 by norm_num) m, h7]
      calc ((Finset.univ.filter fun v : Fin m → Bool =>
          ∃ i ∈ Finset.range ks, M x (List.zipWith xor (List.ofFn v)
            ((u.drop (i * m)).take m)) = true).card : ℚ)
          ≤ ∑ i ∈ Finset.range ks, ((Finset.univ.filter
              fun v : Fin m → Bool => M x (List.zipWith xor (List.ofFn v)
                ((u.drop (i * m)).take m)) = true).card : ℚ) := h3
        _ ≤ ∑ _i ∈ Finset.range ks, ((1/2 : ℚ) ^ T * 2 ^ m) :=
            Finset.sum_le_sum hacc_card
        _ = (ks : ℚ) * ((1/2 : ℚ) ^ T * 2 ^ m) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ < 2 ^ m := h6
    have hcardN : (Finset.univ.filter fun v : Fin m → Bool =>
        ∃ i ∈ Finset.range ks,
          M x (List.zipWith xor (List.ofFn v) ((u.drop (i * m)).take m))
            = true).card < Fintype.card (Fin m → Bool) := by
      have hcardfun : Fintype.card (Fin m → Bool) = 2 ^ m := by
        rw [← card_univ_bitstrings m, Finset.card_univ]
      rw [hcardfun]
      exact_mod_cast hcard
    obtain ⟨v', hv'⟩ := exists_notMem_of_card_lt hcardN
    have hvfalse : ∀ i ∈ List.range ks,
        M x (List.zipWith xor (List.ofFn v')
          ((u.drop (i * m)).take m)) = false := by
      intro i hi
      rw [List.mem_range] at hi
      rcases hb : M x (List.zipWith xor (List.ofFn v')
          ((u.drop (i * m)).take m))
      · rfl
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨i, Finset.mem_range.mpr hi, hb⟩⟩) hv'
    have hN := hall (List.ofFn v') (by rw [List.length_ofFn])
    have hfalse : shiftOrVerifier M
        (polyLen ((18 * (a₀ + 7) + 18) * a₀) (k₀ + k₀))
        (polyLen (19 * a₀ + 20) k₀) x u (List.ofFn v') = false := by
      show (List.range ks).any _ = false
      rw [List.any_eq_false]
      intro i hi
      show ¬ (M x (List.zipWith xor (List.ofFn v')
        ((u.drop (i * m)).take m)) = true)
      rw [hvfalse i hi]
      simp
    rw [hN] at hfalse
    exact absurd hfalse (by simp)

/-- **Sipser–Gács** ([AB09, Thm 7.18]): `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` — relative to the
efficiency notion `E`, under the closure hypotheses the proof uses.

**Proof.** It suffices to prove `BPP ⊆ Σ₂ᵖ` (`bpp_subset_sigma2`) and
apply it to `Lᶜ` as well, since `BPP` is closed under complementation
(`InBPP.compl`, which is where the hypothesis `hNot` is used).  Given
`L ∈ BPP` with witness `(M₀, a₀, k₀)`, amplify by majority
(`amplify_concrete`, using `hMaj`) to error `2^{−T(n)}` with
`T(n) = (a₀+7)(n+1)^{k₀}`; the amplified verifier uses
`m(n) = (18(a₀+7)+18)·a₀·(n+1)^{2k₀}` random bits.  Take
`k(n) = (19a₀+20)(n+1)^{k₀}` shifts — a `polyLen` schedule, as the
`shiftOrVerifier` closure (`hShift`) requires.  The two counting claims
are balanced against `T` rather than the book's `n` (whose choice
`k = ⌈m/n⌉ + 1` needs `k < 2^n` and fails at small `n`):
(Claim 1) `k(n) < 2^{T(n)}` (`shift_count_lt_two_pow`), so for `x ∉ L`
the `k` translates of the accepting set, each of measure `≤ 2^{−T}`,
cannot cover `{0,1}^m`; a union bound exhibits an uncovered `v` for
every `u`.  (Claim 2) `m(n) < T(n)·k(n)`, so for `x ∈ L` the probability
that `k` random shifts miss some `v` is at most `2^m·2^{−Tk} < 1`
(the vote-count distribution `randProb_blockCount` at `j = 0` and the
XOR-invariance `randProb_xor_right`), and the probabilistic method
yields covering shifts.  Hence
`x ∈ L ↔ ∃ u₁,…,u_k ∀ v, ⋁ᵢ M(x, v ⊕ uᵢ)`, the `Σ₂`-shape
`shiftOrVerifier` expresses; all the lengths involved are `polyLen`
schedules. -/
theorem sipser_gacs (hMaj : ClosedUnderMajority E)
    (hNot : ClosedUnderNot E) (hShift : ClosedUnderShiftOr E)
    {L : Language Bool} (hL : InBPP E L) :
    InSigma2 E L ∧ InPi2 E L :=
  ⟨bpp_subset_sigma2 E hMaj hShift hL,
    bpp_subset_sigma2 E hMaj hShift (InBPP.compl E hNot hL)⟩

end Randomized
```

## ===== TCSlib/Complexity/TuringMachine/CounterProgInput.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.CounterProgRun

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Shifting the input of a counter program

Counter programs read their input from left to right. Once a prefix has been consumed,
executing on the remaining suffix is equivalent to executing on the original input with
the input position shifted by the prefix length.

## Main definitions

* `Complexity.CounterProg.shiftInput` shifts an abstract state's input position.

## Main results

* `Complexity.CounterProg.run_shiftInput` transports a run from a suffix to a prefixed input.
* `Complexity.CounterProg.Goes.prepend_input` transports the bounded run relation.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the machine model.)

The lemmas below are technical facts about the counter-program implementation, rather
than additional textbook claims.
-/

namespace Complexity.CounterProg

variable {R : ℕ} {Λ : Type}

/-- Shift only the input position of an abstract state by `n`. -/
def shiftInput (n : ℕ) (s : St R Λ) : St R Λ :=
  { s with pos := n + s.pos }

/-- Indexing after a prefix reads the corresponding symbol of the suffix. -/
theorem getElem?_append_length_add (pre suffix : List Bool) (p : ℕ) :
    (pre ++ suffix)[pre.length + p]? = suffix[p]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

/-- A program step after a consumed prefix is the corresponding suffix step with its
input position shifted. -/
theorem step_shiftInput (P : Λ → Instr R Λ) (pre suffix : List Bool) (s : St R Λ) :
    step P (pre ++ suffix) (shiftInput pre.length s) =
      shiftInput pre.length (step P suffix s) := by
  rcases s with ⟨lbl, ρ, p, o⟩
  cases lbl with
  | none => rfl
  | some l =>
    cases hP : P l <;> simp only [step, shiftInput, hP]
    all_goals try rfl
    rw [getElem?_append_length_add]
    cases hread : suffix[p]? with
    | none => rfl
    | some b => cases b <;> simp [shiftInput, Nat.add_assoc]

/-- A run after a consumed prefix is the corresponding suffix run with its input
position shifted.

**Proof sketch.** Induct on the number of steps, using the one-step input-shift identity. -/
theorem run_shiftInput (P : Λ → Instr R Λ) (pre suffix : List Bool)
    (s : St R Λ) (t : ℕ) :
    run P (pre ++ suffix) (shiftInput pre.length s) t =
      shiftInput pre.length (run P suffix s t) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, step_shiftInput, ih, run_succ]

/-- A bounded suffix run remains valid after prepending input already consumed; its
initial and final input positions both increase by the prefix length. -/
theorem Goes.prepend_input {P : Λ → Instr R Λ} {suffix : List Bool} {l : Λ}
    {l' : Option Λ} {ρ ρ' : Fin R → ℕ} {p p' : ℕ} {e : List Bool} {b : ℕ}
    (h : Goes P suffix l ρ p l' ρ' p' e b) (pre : List Bool) :
    Goes P (pre ++ suffix) l ρ (pre.length + p) l' ρ' (pre.length + p') e b := by
  intro o
  obtain ⟨t, ht, hrun⟩ := h o
  refine ⟨t, ht, ?_⟩
  change run P (pre ++ suffix) (shiftInput pre.length ⟨some l, ρ, p, o⟩) t =
    shiftInput pre.length ⟨l', ρ', p', o ++ e⟩
  rw [run_shiftInput, hrun]

end Complexity.CounterProg
```

## ===== TCSlib/Complexity/CircuitComplexity/PairEncode.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Data.List.OfFn
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import TCSlib.Complexity.TuringMachine.Encoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Circuits with paired inputs and fixed randomness

The hard-wiring step of [AB09, Thm 7.17], for the library's self-delimiting
`Turing.pairEncode`. The first component is doubled, so simply fixing a suffix
is insufficient: two buffered copies of each free input supply its two encoded
coordinates, followed by constants for the separator and the fixed second word.

## Main definitions

* `BoolCircuit.inputGate`, `inputBuffer`, `inputValues` — copy or fix circuit inputs.
* `BoolCircuit.DAGCircuit.bufferInputs` — replace a circuit's inputs by buffered sources.
* `BoolCircuit.DAGCircuit.pairEncode` — compute a circuit on `pairEncode x r` with `r` fixed.

## Main results

* `BoolCircuit.DAGCircuit.pairEncode_eval` — the paired circuit computes the original
  circuit on the encoded input and fixed random word.
* `BoolCircuit.DAGCircuit.pairEncode_isFaninTwo`, `pairEncode_size` — fan-in is preserved
  and buffering adds exactly one free-input vertex per input bit.

## Deviations from the source

The book's hard-wiring preserves size; explicitly buffering the doubled first
component adds `n` vertices. The overhead is polynomial and independent of the
contents of the fixed word. Copies remain distinct vertices, preserving the
model's requirement that a gate does not read the same vertex twice.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.6, Theorem 7.17; §6.3, Theorem 6.18.)
-/

namespace BoolCircuit

/-- A source input is copied by a singleton `∧`; a fixed bit is supplied by a constant. -/
def inputGate {n : ℕ} : Fin n ⊕ Bool → DAGGate
  | .inl i => ⟨.and, [i.val]⟩
  | .inr b => constGate b

/-- One buffer gate for each original input vertex. -/
def inputBuffer {n m : ℕ} (s : Fin m → Fin n ⊕ Bool) : List DAGGate :=
  List.ofFn fun i => inputGate (s i)

/-- The original inputs supplied by the free input vector and fixed source bits. -/
def inputValues {n m : ℕ} (s : Fin m → Fin n ⊕ Bool) (x : Fin n → Bool) :
    Fin m → Bool := fun i =>
  match s i with
  | .inl j => x j
  | .inr b => b

/-- A buffer gate reads only free input vertices. -/
theorem inputGate_args_lt {n : ℕ} (s : Fin n ⊕ Bool) :
    ∀ a ∈ (inputGate s).args, a < n := by
  cases s with
  | inl i =>
      intro a ha
      simp only [inputGate, List.mem_singleton] at ha
      subst a
      exact i.isLt
  | inr b =>
      intro a ha
      simp [inputGate] at ha

/-- Replace each original input by a distinct copy or constant vertex, then shift
every original gate and its output by the number of free inputs.

**Proof sketch.** Buffer gates read only the `n` free inputs. Each original
gate has all of its vertex numbers shifted by `n`, so its earlier-vertex
inequalities remain valid after the `m` buffer gates. The output is shifted
by the same amount and remains within the enlarged circuit. -/
def DAGCircuit.bufferInputs {n m : ℕ} (C : DAGCircuit m)
    (s : Fin m → Fin n ⊕ Bool) : DAGCircuit n where
  gates := inputBuffer s ++ C.gates.map (DAGGate.remap fun v => n + v)
  output := n + C.output
  args_lt := by
    intro i hi a ha
    have hlen : (inputBuffer s).length = m := by simp [inputBuffer]
    by_cases him : i < m
    · rw [List.getElem_append_left (by rw [hlen]; exact him)] at ha
      have hargs := inputGate_args_lt (s ⟨i, him⟩) a
        (by simpa [inputBuffer] using ha)
      omega
    · rw [List.getElem_append_right (by rw [hlen]; omega)] at ha
      simp only [List.getElem_map, DAGGate.remap, List.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      have hiC : i - (inputBuffer s).length < C.gates.length := by
        simp only [List.length_append, List.length_map, hlen] at hi
        omega
      have hargs := C.args_lt (i - (inputBuffer s).length) hiC b hb
      omega
  output_lt := by
    have houtput := C.output_lt
    simp only [List.length_append, List.length_map, inputBuffer, List.length_ofFn]
    omega

/-- Buffer gate `i` evaluates to its selected source input bit or constant. -/
theorem inputBuffer_value {n m : ℕ}
    (s : Fin m → Fin n ⊕ Bool) (x : Fin n → Bool) (i : Fin m) :
    (runWith DAGGate.eval (inputBuffer s) (List.ofFn x)).getD
      (n + i.val) false = inputValues s x i := by
  have hi : i.val < (inputBuffer s).length := by
    simpa [inputBuffer] using i.isLt
  have hg := runWith_getD_gate DAGGate.eval (inputBuffer s) (List.ofFn x) hi false
  simp only [List.length_ofFn] at hg
  rw [hg]
  have hgate : (inputBuffer s)[i.val] = inputGate (s i) := by
    simp [inputBuffer]
  rw [hgate]
  cases hsi : s i with
  | inl j =>
      simpa [inputGate, DAGGate.eval, inputValues, hsi,
        List.getD_eq_getD_getElem?, j.isLt] using
        (runWith_getD_of_lt DAGGate.eval ((inputBuffer s).take i.val)
          (List.ofFn x) (v := j.val) (by simpa using j.isLt) false)
  | inr b =>
      simp [inputGate, inputValues, hsi]

/-- Buffered inputs preserve the original circuit's value on the supplied input vector.

**Proof sketch.** Each buffer vertex holds its selected input or constant. Shift every
original vertex by `n`; gate evaluation commutes with this renaming, so the shifted
output has the original output's value. -/
theorem DAGCircuit.bufferInputs_eval {n m : ℕ}
    (C : DAGCircuit m) (s : Fin m → Fin n ⊕ Bool) (x : Fin n → Bool) :
    (C.bufferInputs s).eval x = C.eval (inputValues s x) := by
  have key := runWith_remap_rel DAGGate.eval Eq false (fun v => n + v)
    (fun g _ _ h => DAGGate.eval_remap g _ h)
    (L := m) (L' := n + m)
    (List.ofFn (inputValues s x))
    (runWith DAGGate.eval (inputBuffer s) (List.ofFn x))
    (by simp)
    (by simp [inputBuffer])
    (fun v hv => by simp only []; omega)
    (fun i => by simp only []; omega)
    (fun v hv => by
      simpa [List.getD_eq_getD_getElem?, hv] using inputBuffer_value s x ⟨v, hv⟩)
    C.gates C.args_lt C.output C.output_lt
  unfold DAGCircuit.eval DAGCircuit.values DAGCircuit.bufferInputs
  dsimp only
  rw [runWith_append]
  exact key

/-- Buffering inputs preserves well-formedness and fan-in at most two, and adds
exactly `n` vertices to the original circuit's size.

**Proof sketch.** Each buffer is either a singleton identity gate or a constant gate.
Shifting every old vertex number by `n` is injective, so it preserves distinct gate
inputs, gate kinds, and fan-in. There are `n` inputs, `m` buffer gates, and all
of the original gates. -/
theorem DAGCircuit.bufferInputs_structure {n m : ℕ} (C : DAGCircuit m)
    (s : Fin m → Fin n ⊕ Bool) (hC : C.IsFaninTwo) :
    (C.bufferInputs s).IsWellFormed ∧
      (C.bufferInputs s).IsFaninTwo ∧
      (C.bufferInputs s).size = n + C.size := by
  have hall : ∀ g ∈ (C.bufferInputs s).gates, g.FaninTwo := by
    intro g hg
    change g ∈ inputBuffer s ++ C.gates.map (DAGGate.remap (fun v => n + v)) at hg
    rcases List.mem_append.mp hg with hg | hg
    · change g ∈ List.ofFn (fun i => inputGate (s i)) at hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
      cases hs : s i with
      | inl j =>
          simp [inputGate, hs, DAGGate.FaninTwo, DAGGate.WellFormed]
      | inr b =>
          simpa [inputGate, hs] using constGate_faninTwo b
    · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hnd, hnot⟩ := hC.1 g₀ hg₀
      refine ⟨⟨hnd.map (fun a b hab => Nat.add_left_cancel hab), ?_⟩, ?_⟩
      · intro h
        simpa [DAGGate.remap] using hnot h
      · simpa [DAGGate.remap] using hC.2 g₀ hg₀
  have hw : (C.bufferInputs s).IsWellFormed := fun g hg => (hall g hg).1
  refine ⟨hw, ⟨hw, fun g hg => (hall g hg).2⟩, ?_⟩
  simp [DAGCircuit.size, DAGCircuit.bufferInputs, inputBuffer, Nat.add_assoc]

/-- The doubled free-input sources, followed by the separator and fixed-word constants. -/
def pairWireList (n : ℕ) (r : List Bool) : List (Fin n ⊕ Bool) :=
  (List.ofFn (fun i : Fin n => Sum.inl i)).flatMap (fun s => [s, s]) ++
    ([false, true] ++ r).map Sum.inr

/-- The wire list has the paired input's length, and evaluating its sources produces
the self-delimiting encoding of the free input and fixed word.

**Proof sketch.** Mapping source values through a duplicated list duplicates their
values, by induction on that list. The remaining sources are constants supplying the
separator and fixed word. Taking lengths gives the stated size. -/
theorem pairWireList_spec (n : ℕ) (r : List Bool) :
    (pairWireList n r).length = 2 * n + 2 + r.length ∧
      ∀ v : Fin n → Bool,
        (pairWireList n r).map (fun s =>
          match s with
          | .inl i => v i
          | .inr b => b) = Turing.pairEncode (List.ofFn v) r := by
  have hdup (f : Fin n ⊕ Bool → Bool) (l : List (Fin n ⊕ Bool)) :
      (l.flatMap (fun s => [s, s])).map f =
        (l.map f).flatMap (fun b => [b, b]) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
        simp only [List.flatMap_cons, List.map_append, List.map_cons,
          List.map_nil, ih]
  have hmap (v : Fin n → Bool) :
      (pairWireList n r).map (fun s =>
        match s with
        | .inl i => v i
        | .inr b => b) = Turing.pairEncode (List.ofFn v) r := by
    unfold pairWireList
    rw [List.map_append, hdup]
    simp [Turing.pairEncode, List.map_map, Function.comp_def, List.append_assoc]
  refine ⟨?_, hmap⟩
  have hlen := congrArg List.length (hmap (fun _ => false))
  simpa only [List.length_map, Turing.length_pairEncode, List.length_ofFn] using hlen

/-- View a list of length `m` as a vector indexed by `Fin m`. -/
def vectorOfList {α : Type*} {m : ℕ} (l : List α) (h : l.length = m) :
    Fin m → α :=
  fun i => l.get (Fin.cast h.symm i)

/-- Turning a list into its indexed vector and back recovers the list. -/
@[simp] theorem vectorOfList_ofFn {α : Type*} {m : ℕ}
    (l : List α) (h : l.length = m) :
    List.ofFn (vectorOfList l h) = l := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [List.getElem_ofFn, vectorOfList, List.get_eq_getElem, Fin.coe_cast]

/-- The vector of source wires for the self-delimiting paired input. -/
def pairWiring (n : ℕ) (r : List Bool) : Fin (2 * n + 2 + r.length) → Fin n ⊕ Bool :=
  vectorOfList (pairWireList n r) (pairWireList_spec n r).1

/-- The input vector encoding the free word and the fixed second word. -/
def pairEncodeInput {n : ℕ} (r : List Bool) (v : Fin n → Bool) :
    Fin (2 * n + 2 + r.length) → Bool :=
  inputValues (pairWiring n r) v

/-- The circuit computing `C` on the self-delimiting pair of its free input and fixed
word `r`. This is the hard-wiring construction of [AB09, Thm 7.17], with explicit
copies for the doubled first component of the library's encoding. -/
def DAGCircuit.pairEncode {n : ℕ} (r : List Bool)
    (C : DAGCircuit (2 * n + 2 + r.length)) : DAGCircuit n :=
  C.bufferInputs (pairWiring n r)

/-- Converting the paired input vector to a word gives the exact library encoding. -/
theorem pairEncodeInput_ofFn {n : ℕ} (r : List Bool) (v : Fin n → Bool) :
    List.ofFn (pairEncodeInput r v) = Turing.pairEncode (List.ofFn v) r := by
  have e1 : List.ofFn (pairEncodeInput r v)
      = (List.ofFn (pairWiring n r)).map
          (fun s : Fin n ⊕ Bool => match s with | .inl j => v j | .inr b => b) := by
    rw [List.map_ofFn]
    rfl
  rw [e1]
  unfold pairWiring
  rw [vectorOfList_ofFn]
  exact (pairWireList_spec n r).2 v

/-- The paired circuit computes the original circuit on `pairEncode x r`, with `r`
fixed. This is the circuit step of [AB09, Thm 7.17]. -/
theorem DAGCircuit.pairEncode_eval {n : ℕ} (r : List Bool)
    (C : DAGCircuit (2 * n + 2 + r.length)) (v : Fin n → Bool) :
    (C.pairEncode r).eval v = C.eval (pairEncodeInput r v) :=
  C.bufferInputs_eval (pairWiring n r) v

/-- Encoding and fixing a word preserves fan-in at most two, as needed in
[AB09, Thm 7.17]. -/
theorem DAGCircuit.pairEncode_isFaninTwo {n : ℕ} (r : List Bool)
    (C : DAGCircuit (2 * n + 2 + r.length)) (hC : C.IsFaninTwo) :
    (C.pairEncode r).IsFaninTwo :=
  (C.bufferInputs_structure (pairWiring n r) hC).2.1

/-- Encoding and fixing a word preserves well-formedness for a fan-in-two circuit. -/
theorem DAGCircuit.pairEncode_isWellFormed {n : ℕ} (r : List Bool)
    (C : DAGCircuit (2 * n + 2 + r.length)) (hC : C.IsFaninTwo) :
    (C.pairEncode r).IsWellFormed :=
  (C.bufferInputs_structure (pairWiring n r) hC).1

/-- Buffering an encoded input adds exactly `n` vertices. The overhead in the
hard-wiring step of [AB09, Thm 7.17] is independent of the fixed word's bits. -/
theorem DAGCircuit.pairEncode_size {n : ℕ} (r : List Bool)
    (C : DAGCircuit (2 * n + 2 + r.length)) :
    (C.pairEncode r).size = n + C.size := by
  simp [DAGCircuit.size, DAGCircuit.pairEncode, DAGCircuit.bufferInputs,
    inputBuffer, Nat.add_assoc]

/-- A circuit family's language contains a word formed from a vector exactly when
the circuit at that vector's length accepts the vector. -/
theorem DAGCircuitFamily.mem_language_ofFn {m : ℕ} (F : DAGCircuitFamily)
    (v : Fin m → Bool) :
    List.ofFn v ∈ F.language ↔ (F.circuit m).eval v = true := by
  have htuple :
      (⟨(List.ofFn v).length, (List.ofFn v).get⟩ :
        Σ k : ℕ, Fin k → Bool) = ⟨m, v⟩ :=
    List.equivSigmaTuple.right_inv ⟨m, v⟩
  exact (F.mem_language_iff (List.ofFn v)).trans
    (Iff.of_eq (congrArg
      (fun p : Σ k : ℕ, Fin k → Bool =>
        (F.circuit p.1).eval p.2 = true) htuple))

/-- Acceptance of an encoded input vector is membership of the exact paired word in
the circuit family's language. This avoids index casts in [AB09, Thm 7.17]'s use of
the polynomial-size family. -/
theorem DAGCircuitFamily.pairEncode_eval_eq_true_iff {n : ℕ}
    (F : DAGCircuitFamily) (r : List Bool) (v : Fin n → Bool) :
    (F.circuit (2 * n + 2 + r.length)).eval (pairEncodeInput r v) = true ↔
      Turing.pairEncode (List.ofFn v) r ∈ F.language :=
  (F.mem_language_ofFn (pairEncodeInput r v)).symm.trans
    (Iff.of_eq (congrArg (fun w : List Bool => w ∈ F.language)
      (pairEncodeInput_ofFn r v)))

end BoolCircuit
```

## ===== TCSlib/Complexity/ClassNP/PolyTimePrefix.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.CounterProgPolyTime
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.TuringMachine.CounterProgInput

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time prefix operations

The second component of a self-delimiting pair can be truncated, or have its
prefix removed, at the length of the first component. A one-register counter
program counts the doubled first component, then copies or skips that many
symbols of the second component. Malformed pairs produce the empty string.

## Main definitions

* `Complexity.PrefixByLength.take` and `drop` — total prefix operations on pairs.

## Main results

* `Complexity.polyTimeComputable_takePrefixByLength` and
  `polyTimeComputable_dropPrefixByLength` — both operations are polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.3: splitting random strings in the
  proof of Theorem 7.8; §7.4.1: repeated trials.)
-/

namespace Complexity

namespace PrefixByLength

open Turing CounterProg

/-- Take a prefix of the second component of a pair as long as its first component;
malformed inputs return the empty string. -/
def take (z : List Bool) : List Bool :=
  (pairSndD z).take (pairFstD z).length

/-- Drop a prefix of the second component of a pair as long as its first component;
malformed inputs return the empty string. -/
def drop (z : List Bool) : List Bool :=
  (pairSndD z).drop (pairFstD z).length

/-- Control states of the shared prefix-copying program. -/
private inductive Label where
  | scan | secondFalse | secondTrue | bump | head | read | dec
  | emit (b : Bool) | copy | copyEmit (b : Bool) | stop
  deriving DecidableEq, Fintype

/-- One register stores the remaining number of prefix symbols. -/
private def regs (n : ℕ) : Fin 1 → ℕ := fun _ => n

/-- The program parses aligned doubled bits before the separator. In take mode
it copies until the counter reaches zero; in drop mode it skips that prefix,
then copies everything remaining. -/
private def program (keep : Bool) : Label → Instr 1 Label
  | .scan => .rd .stop .secondFalse .secondTrue
  | .secondFalse => .rd .stop .bump .head
  | .secondTrue => .rd .stop .stop .bump
  | .bump => .inc 0 .scan
  | .head => .jz 0 (if keep then .stop else .copy) .read
  | .read => if keep then .rd .stop (.emit false) (.emit true)
      else .rd .stop .dec .dec
  | .dec => .dec 0 .head
  | .emit b => .out b .dec
  | .copy => .rd .stop (.copyEmit false) (.copyEmit true)
  | .copyEmit b => .out b .copy
  | .stop => .halt

/-- Updating the only register replaces its constant value. -/
private theorem update_regs (n m : ℕ) :
    Function.update (regs n) (0 : Fin 1) m = regs m := by
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst hi
  simp [regs]

/-- The final copying phase prints the unread suffix in two steps per bit.
**Proof sketch.** Each read selects an output instruction and returns to the
copying state. At the end, one read and one halt finish the computation. -/
private theorem goes_copy (keep : Bool) (n : ℕ) (r : List Bool) :
    Goes (program keep) r .copy (regs n) 0 none (regs n) r.length r
      (2 * r.length + 2) := by
  induction r with
  | nil =>
    have hread : Goes (program keep) [] .copy (regs n) 0
        (some .stop) (regs n) 0 [] 1 :=
      goes_rd_end rfl (by simp)
    have hhalt : Goes (program keep) [] .stop (regs n) 0 none (regs n) 0 [] 1 :=
      goes_halt rfl
    simpa using hread.trans hhalt
  | cons b r ih =>
    have hread : Goes (program keep) (b :: r) .copy (regs n) 0
        (some (.copyEmit b)) (regs n) 1 [] 1 := by
      cases b
      · exact goes_rd_false rfl (by simp)
      · exact goes_rd_true rfl (by simp)
    have hwrite : Goes (program keep) (b :: r) (.copyEmit b) (regs n) 1
        (some .copy) (regs n) 1 [b] 1 :=
      goes_out rfl
    have hrest := ih.prepend_input [b]
    have h := (hread.trans hwrite).trans hrest
    exact h.congr rfl rfl rfl (by simp; omega) (by simp) (by simp; omega)

/-- The countdown instruction removes one from the only register. -/
private theorem goes_dec_one (keep : Bool) (x : List Bool) (n p : ℕ) :
    Goes (program keep) x .dec (regs (n + 1)) p (some .head) (regs n) p [] 1 := by
  have h : Goes (program keep) x .dec (regs (n + 1)) p (some .head)
      (Function.update (regs (n + 1)) 0 ((regs (n + 1)) 0 - 1)) p [] 1 :=
    goes_dec rfl
  have he : (regs (n + 1)) (0 : Fin 1) - 1 = n := by simp [regs]
  rw [he, update_regs] at h
  exact h

/-- Starting with a counter of value `n`, the payload phase produces the
requested prefix or suffix in a linear number of steps.
**Proof sketch.** Induct on the payload. A positive counter consumes one bit
and decrements. A zero counter either halts immediately (take mode), or
enters the copying phase (drop mode). End-of-input halts in either mode. -/
private theorem goes_payload (keep : Bool) (r : List Bool) (n : ℕ) :
    Goes (program keep) r .head (regs n) 0 none (regs (n - r.length))
      (if keep then min n r.length else r.length)
      (if keep then r.take n else r.drop n) (4 * r.length + 3) := by
  induction r generalizing n with
  | nil =>
    cases n with
    | zero =>
      cases keep
      · have htest : Goes (program false) [] .head (regs 0) 0
            (some .copy) (regs 0) 0 [] 1 :=
          goes_jz_zero rfl rfl
        simpa using htest.trans (goes_copy false 0 [])
      · have htest : Goes (program true) [] .head (regs 0) 0
            (some .stop) (regs 0) 0 [] 1 :=
          goes_jz_zero rfl rfl
        have hhalt : Goes (program true) [] .stop (regs 0) 0
            none (regs 0) 0 [] 1 := goes_halt rfl
        exact (htest.trans hhalt).congr rfl rfl rfl (by simp) (by simp) (by simp)
    | succ n =>
      have htest : Goes (program keep) [] .head (regs (n + 1)) 0
          (some .read) (regs (n + 1)) 0 [] 1 :=
        goes_jz_pos rfl (by simp [regs])
      have hread : Goes (program keep) [] .read (regs (n + 1)) 0
          (some .stop) (regs (n + 1)) 0 [] 1 := by
        cases keep <;> exact goes_rd_end rfl (by simp)
      have hhalt : Goes (program keep) [] .stop (regs (n + 1)) 0
          none (regs (n + 1)) 0 [] 1 := goes_halt rfl
      exact ((htest.trans hread).trans hhalt).congr rfl (by simp) rfl
        (by cases keep <;> simp) (by cases keep <;> simp) (by simp)
  | cons b r ih =>
    cases n with
    | zero =>
      cases keep
      · have htest : Goes (program false) (b :: r) .head (regs 0) 0
            (some .copy) (regs 0) 0 [] 1 := goes_jz_zero rfl rfl
        exact (htest.trans (goes_copy false 0 (b :: r))).congr rfl (by simp) rfl
          (by simp) (by simp) (by simp; omega)
      · have htest : Goes (program true) (b :: r) .head (regs 0) 0
            (some .stop) (regs 0) 0 [] 1 := goes_jz_zero rfl rfl
        have hhalt : Goes (program true) (b :: r) .stop (regs 0) 0
            none (regs 0) 0 [] 1 := goes_halt rfl
        exact (htest.trans hhalt).congr rfl (by simp) rfl (by simp) (by simp)
          (by simp)
    | succ n =>
      have htest : Goes (program keep) (b :: r) .head (regs (n + 1)) 0
          (some .read) (regs (n + 1)) 0 [] 1 :=
        goes_jz_pos rfl (by simp [regs])
      have hbody : Goes (program keep) (b :: r) .read (regs (n + 1)) 0
          (some .head) (regs n) 1 (if keep then [b] else []) 3 := by
        cases keep
        · have hread : Goes (program false) (b :: r) .read (regs (n + 1)) 0
              (some .dec) (regs (n + 1)) 1 [] 1 := by
            cases b
            · exact goes_rd_false rfl (by simp)
            · exact goes_rd_true rfl (by simp)
          exact (hread.trans (goes_dec_one false (b :: r) n 1)).congr
            rfl rfl rfl rfl (by simp) (by omega)
        · have hread : Goes (program true) (b :: r) .read (regs (n + 1)) 0
              (some (.emit b)) (regs (n + 1)) 1 [] 1 := by
            cases b
            · exact goes_rd_false rfl (by simp)
            · exact goes_rd_true rfl (by simp)
          have hwrite : Goes (program true) (b :: r) (.emit b) (regs (n + 1)) 1
              (some .dec) (regs (n + 1)) 1 [b] 1 := goes_out rfl
          simpa using (hread.trans hwrite).trans (goes_dec_one true (b :: r) n 1)
      have hrest := (ih n).prepend_input [b]
      exact ((htest.trans hbody).trans hrest).congr rfl (by simp) rfl
        (by cases keep <;> simp <;> omega)
        (by cases keep <;> simp)
        (by simp; omega)

/-- Each doubled source bit increments the length counter once. -/
private theorem goes_inc_one (keep : Bool) (x : List Bool) (n p : ℕ) :
    Goes (program keep) x .bump (regs n) p (some .scan) (regs (n + 1)) p [] 1 := by
  have h : Goes (program keep) x .bump (regs n) p (some .scan)
      (Function.update (regs n) 0 ((regs n) 0 + 1)) p [] 1 := goes_inc rfl
  have he : (regs n) (0 : Fin 1) + 1 = n + 1 := rfl
  rw [he, update_regs] at h
  exact h

/-- Parsing a doubled prefix adds its length to the counter and prints nothing.
**Proof sketch.** Induct on the prefix. Two reads recognize each equal bit
pair, then one increment returns to the scanning state. The remainder of
the run is transported past the two consumed input bits. -/
private theorem goes_doubled (keep : Bool) (u tail : List Bool) (n : ℕ) :
    Goes (program keep) (dbl u ++ tail) .scan (regs n) 0 (some .scan)
      (regs (n + u.length)) (2 * u.length) [] (3 * u.length) := by
  induction u generalizing n with
  | nil =>
    simp only [dbl_nil, List.nil_append, List.length_nil, Nat.add_zero, Nat.mul_zero]
    intro o
    exact ⟨0, le_rfl, by simp [run_zero]⟩
  | cons b u ih =>
    have hfirst : Goes (program keep) (dbl (b :: u) ++ tail) .scan (regs n) 0
        (some (if b then .secondTrue else .secondFalse)) (regs n) 1 [] 1 := by
      cases b
      · exact goes_rd_false rfl (by simp)
      · exact goes_rd_true rfl (by simp)
    have hsecond : Goes (program keep) (dbl (b :: u) ++ tail)
        (if b then .secondTrue else .secondFalse) (regs n) 1
        (some .bump) (regs n) 2 [] 1 := by
      cases b
      · exact goes_rd_false rfl (by simp)
      · exact goes_rd_true rfl (by simp)
    have hinc := goes_inc_one keep (dbl (b :: u) ++ tail) n 2
    have hrest := (ih (n + 1)).prepend_input [b, b]
    have h := ((hfirst.trans hsecond).trans hinc).trans hrest
    exact h.congr rfl (by congr 1; simp; omega) rfl (by simp; omega)
      (by simp) (by simp; omega)

/-- On a well-formed pair the complete program computes the desired prefix
operation with at most `5(|z|+1)` abstract steps.
**Proof sketch.** Parse the doubled first component, consume the separator,
then run the payload phase with the counted length. The three linear time
bounds add to a linear bound in the encoded input length. -/
private theorem goes_pair (keep : Bool) (u r : List Bool) :
    ∃ (ρ : Fin 1 → ℕ) (p : ℕ), Goes (program keep) (pairEncode u r) .scan (regs 0) 0
      none ρ p (if keep then r.take u.length else r.drop u.length)
      (5 * ((pairEncode u r).length + 1)) := by
  have hfirst : Goes (program keep) ([false, true] ++ r) .scan (regs u.length) 0
      (some .secondFalse) (regs u.length) 1 [] 1 :=
    goes_rd_false rfl (by simp)
  have hsecond : Goes (program keep) ([false, true] ++ r) .secondFalse
      (regs u.length) 1 (some .head) (regs u.length) 2 [] 1 :=
    goes_rd_true rfl (by simp)
  have hhead := (goes_payload keep r u.length).prepend_input [false, true]
  have hsep := (hfirst.trans hsecond).trans hhead
  have hprefix : Goes (program keep) (dbl u ++ ([false, true] ++ r)) .scan (regs 0) 0
      (some .scan) (regs u.length) (2 * u.length) [] (3 * u.length) := by
    simpa using goes_doubled keep u ([false, true] ++ r) 0
  have hshift : Goes (program keep) (dbl u ++ ([false, true] ++ r)) .scan
      (regs u.length) (2 * u.length) none (regs (u.length - r.length))
      (2 * u.length + 2 + (if keep then min u.length r.length else r.length))
      (if keep then r.take u.length else r.drop u.length) (4 * r.length + 5) := by
    exact (hsep.prepend_input (dbl u)).congr rfl rfl (by simp)
      (by simp; omega) (by simp) (by omega)
  have hrun := hprefix.trans hshift
  have he : dbl u ++ ([false, true] ++ r) = pairEncode u r := by
    simp [pairEncode_eq_dbl, List.append_assoc]
  rw [he] at hrun
  refine ⟨regs (u.length - r.length),
    2 * u.length + 2 + (if keep then min u.length r.length else r.length), ?_⟩
  exact hrun.congr rfl rfl rfl rfl (by simp) (by simp [length_pairEncode]; omega)

/-- An incomplete or forbidden aligned pair halts without printing.
**Proof sketch.** The only invalid tails are an empty word, one bit, or a
tail starting with `10`. At most two reads reach the halt instruction. -/
private theorem goes_bad_tail (keep : Bool) (tail : List Bool) (n : ℕ)
    (htail : tail = [] ∨ (∃ b, tail = [b]) ∨ ∃ r, tail = true :: false :: r) :
    ∃ p : ℕ, Goes (program keep) tail .scan (regs n) 0 none (regs n) p [] 3 := by
  rcases htail with rfl | ⟨b, rfl⟩ | ⟨r, rfl⟩
  · have hread : Goes (program keep) [] .scan (regs n) 0
        (some .stop) (regs n) 0 [] 1 := goes_rd_end rfl (by simp)
    have hhalt : Goes (program keep) [] .stop (regs n) 0
        none (regs n) 0 [] 1 := goes_halt rfl
    exact ⟨0, (hread.trans hhalt).congr rfl rfl rfl rfl (by simp) (by omega)⟩
  · have hfirst : Goes (program keep) [b] .scan (regs n) 0
        (some (if b then .secondTrue else .secondFalse)) (regs n) 1 [] 1 := by
      cases b
      · exact goes_rd_false rfl (by simp)
      · exact goes_rd_true rfl (by simp)
    have hsecond : Goes (program keep) [b]
        (if b then .secondTrue else .secondFalse) (regs n) 1
        (some .stop) (regs n) 1 [] 1 := by
      cases b <;> exact goes_rd_end rfl (by simp)
    have hhalt : Goes (program keep) [b] .stop (regs n) 1
        none (regs n) 1 [] 1 := goes_halt rfl
    exact ⟨1, by simpa using (hfirst.trans hsecond).trans hhalt⟩
  · have hfirst : Goes (program keep) (true :: false :: r) .scan (regs n) 0
        (some .secondTrue) (regs n) 1 [] 1 := goes_rd_true rfl (by simp)
    have hsecond : Goes (program keep) (true :: false :: r) .secondTrue (regs n) 1
        (some .stop) (regs n) 2 [] 1 := goes_rd_false rfl (by simp)
    have hhalt : Goes (program keep) (true :: false :: r) .stop (regs n) 2
        none (regs n) 2 [] 1 := goes_halt rfl
    exact ⟨2, by simpa using (hfirst.trans hsecond).trans hhalt⟩

/-- The complete program computes the total prefix operation on every input.
**Proof sketch.** A decoded pair is handled by `goes_pair`. If decoding
fails, the input consists of a doubled prefix followed by an invalid tail;
parse that prefix and apply `goes_bad_tail`. Neither phase prints anything,
agreeing with the empty total projections of a malformed pair. -/
private theorem goes_total (keep : Bool) (z : List Bool) :
    ∃ (ρ : Fin 1 → ℕ) (p : ℕ), Goes (program keep) z .scan (regs 0) 0
      none ρ p (if keep then take z else drop z) (5 * (z.length + 1)) := by
  cases hz : pairDecode z with
  | some ab =>
    obtain ⟨u, r⟩ := ab
    have he := eq_pairEncode_of_pairDecode z u r hz
    subst z
    simpa [take, drop] using goes_pair keep u r
  | none =>
    obtain ⟨u, tail, he, htail⟩ := pairDecode_eq_none z hz
    subst z
    have hprefix : Goes (program keep) (dbl u ++ tail) .scan (regs 0) 0
        (some .scan) (regs u.length) (2 * u.length) [] (3 * u.length) := by
      simpa using goes_doubled keep u tail 0
    obtain ⟨p, hbad⟩ := goes_bad_tail keep tail u.length htail
    have hshift : Goes (program keep) (dbl u ++ tail) .scan (regs u.length)
        (2 * u.length) none (regs u.length) (2 * u.length + p) [] 3 := by
      simpa using hbad.prepend_input (dbl u)
    have hrun := hprefix.trans hshift
    refine ⟨regs u.length, 2 * u.length + p, ?_⟩
    exact hrun.congr rfl rfl rfl rfl
      (by cases keep <;> simp [take, drop, pairFstD, pairSndD, hz])
      (by simp; omega)

end PrefixByLength

/-- Taking from the second component of a pair a prefix as long as its first
component is polynomial-time computable. Malformed inputs return `[]`.
**Proof sketch.** Compile the one-register prefix program. Its abstract run
takes at most `5(|z|+1)` steps; counter-program simulation has polynomial
overhead. This implements the splitting operation used in [AB09, §7.3,
Theorem 7.8]. -/
theorem polyTimeComputable_takePrefixByLength :
    PolyTimeComputable PrefixByLength.take := by
  apply CounterProg.polyTimeComputable_of_goes
    (PrefixByLength.program true) PrefixByLength.Label.scan PrefixByLength.take 5 1
  intro z
  simpa using PrefixByLength.goes_total true z

/-- Dropping from the second component of a pair a prefix as long as its first
component is polynomial-time computable. Malformed inputs return `[]`.
**Proof sketch.** Use the same program in drop mode: skip the counted
prefix, then copy the remaining input. Its abstract time bound is still
`5(|z|+1)`, so compilation gives a polynomial-time machine. This is the
other splitting operation used in [AB09, §7.3, Theorem 7.8]. -/
theorem polyTimeComputable_dropPrefixByLength :
    PolyTimeComputable PrefixByLength.drop := by
  apply CounterProg.polyTimeComputable_of_goes
    (PrefixByLength.program false) PrefixByLength.Label.scan PrefixByLength.drop 5 1
  intro z
  simpa using PrefixByLength.goes_total false z

end Complexity
```

## ===== TCSlib/Complexity/Randomized/PolyTimeModel.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SipserGacs
import TCSlib.Complexity.Randomized.Adleman
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.ClassNP.PolyTimePrefix
import TCSlib.Complexity.CircuitComplexity.PSubsetPPoly
import TCSlib.Complexity.CircuitComplexity.PairEncode
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.PolyHierarchy.Defs
import TCSlib.Complexity.PolyHierarchy.Normalize
import TCSlib.Complexity.PolyHierarchy.Collapse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The polynomial-time verifier model

The instantiation of `Randomized.VerifierModel` by genuine polynomial-time
Turing machines, now that the Chapter 1–2 development (`Complexity.P`,
`Complexity.PolyTimeComputable`, `Turing.pairEncode`, `Complexity.SigmaP`)
is on `main`.  This connects the abstract Chapter 7 class theorems to the
book's machine-based statements: each `ClosedUnder…` hypothesis becomes a
a result about `P`, and the certificate-style `Σ₂` coincides with
`Complexity.SigmaP 2`.

## Main definitions

* `Randomized.polyTimeModel` — the `VerifierModel` whose efficient verifiers
  are those computed by a `P`-language on the `Turing.pairEncode`d input.

## Main results

* `Randomized.polyTimeModel_closedUnderRace` /
  `…_closedUnderAnswerIs` / `…_closedUnderMajority` / `…_closedUnderAny` /
  `…_closedUnderNot` / `…_closedUnderShiftOr` — the closure hypotheses of
  `Randomized.Classes` and `Randomized.SipserGacs` hold for polynomial time.
* `Randomized.inSigma2_polyTimeModel_iff` — certificate-style `Σ₂` for the
  poly-time model coincides with `Complexity.SigmaP 2`.
* `Randomized.zpp_eq_rp_inter_corp_polyTime`,
  `Randomized.sipser_gacs_polyTime` — [AB09, Thm 7.8] and [AB09, Thm 7.18]
  for polynomial-time machines, with no abstract hypotheses.

## Deviations from the source

None beyond those of `Randomized.Classes`: these declarations *discharge*
the deviations by instantiating the abstract model.  With the library's
`Complexity.P_subset_PPoly` ([AB09, Thm 6.6]) now available, Adleman's
circuit hypothesis is dischargeable too
(`Randomized.polyTimeModel_verifierHasCircuits`), so [AB09, Thm 7.17] is
stated unconditionally as `Randomized.adleman_polyTime`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Complexity

/-- The polynomial-time verifier model: a verifier is *efficient* when its
output is computed by `P`-languages on the `Turing.pairEncode`d pair of
input and random string (`some true`-set and `some false`-set each in `P`),
and a two-witness predicate is efficient when its truth set, on the nested
pairing used by `Complexity.SigmaP`, is in `P`.  This is "`M` is a
polynomial-time TM" of [AB09, Def 7.4], in the library's encoding
conventions. -/
noncomputable def polyTimeModel : VerifierModel where
  Eff M := ∃ V₁ V₀ : Language Bool, V₁ ∈ P ∧ V₀ ∈ P ∧
    ∀ x r : List Bool,
      (M x r = some true ↔ Turing.pairEncode x r ∈ V₁) ∧
      (M x r = some false ↔ Turing.pairEncode x r ∈ V₀)
  EffTwoWitness N := ∃ V : Language Bool, V ∈ P ∧
    ∀ x u v : List Bool,
      (N x u v = true ↔ Turing.pairEncode (Turing.pairEncode x u) v ∈ V)

/-- Keep the input `x` and the first `polyLen a k |x|` bits of the random
string: the pair-level reindexing behind the race and shifted constructions.
On `Turing.pairEncode x r` it returns `Turing.pairEncode x (r.take (polyLen a k |x|))`. -/
def sliceTake (a k : ℕ) (z : List Bool) : List Bool :=
  Turing.pairEncode (pairFstD z) ((pairSndD z).take (polyLen a k (pairFstD z).length))

/-- Keep the input `x` and drop the first `polyLen a k |x|` bits of the random
string.  On `Turing.pairEncode x r` it returns
`Turing.pairEncode x (r.drop (polyLen a k |x|))`. -/
def sliceDrop (a k : ℕ) (z : List Bool) : List Bool :=
  Turing.pairEncode (pairFstD z) ((pairSndD z).drop (polyLen a k (pairFstD z).length))

/-- Take, from the second component of a pair, a prefix as long as the first
component: on `Turing.pairEncode u s` it returns `s.take |u|`.  The
length-gated prefix primitive underlying `sliceTake` (and the block slicing of
the shifted construction); the polynomial `polyLen a k` enters only through the
unary length `u`, so no in-machine exponentiation is needed. -/
def takePrefixByLen (p : List Bool) : List Bool := (pairSndD p).take (pairFstD p).length

/-- Drop, from the second component of a pair, a prefix as long as the first
component: on `Turing.pairEncode u s` it returns `s.drop |u|`. -/
def dropPrefixByLen (p : List Bool) : List Bool := (pairSndD p).drop (pairFstD p).length

/-- `takePrefixByLen` is polynomial-time computable.
**Proof sketch.** A single left-to-right pass (`Complexity.CounterProg`):
mirror `Turing.pairDecode` over the doubled first component, counting its
length `|u|` into a register; at the separator, copy the second component
while the register counts down, truncating once it reaches zero.  Malformed
inputs (`pairDecode = none`) halt with empty output, matching
`pairFstD`/`pairSndD = []`.  The abstract step count is linear in `|p|`, so
`Complexity.CounterProg.polyTimeComputable` applies. -/
theorem polyTimeComputable_takePrefixByLen : PolyTimeComputable takePrefixByLen := by
  simpa only [takePrefixByLen, Complexity.PrefixByLength.take] using
    Complexity.polyTimeComputable_takePrefixByLength

/-- `dropPrefixByLen` is polynomial-time computable.
**Proof sketch.** As `takePrefixByLen`, but the copy phase emits only after the
length register has counted down past the first `|u|` bits of the second
component. -/
theorem polyTimeComputable_dropPrefixByLen : PolyTimeComputable dropPrefixByLen := by
  simpa only [dropPrefixByLen, Complexity.PrefixByLength.drop] using
    Complexity.polyTimeComputable_dropPrefixByLength

/-- `sliceTake a k` is polynomial-time computable.
**Proof.** `polyLen a k |x| = a·(|x|+1)^k` is available as a *unary* string via
`Complexity.polyTimeComputable_polyUnary`; pair it with the random string and
apply `takePrefixByLen`, which truncates to that length without any in-machine
exponentiation. -/
theorem polyTimeComputable_sliceTake (a k : ℕ) :
    PolyTimeComputable (sliceTake a k) := by
  have hu : PolyTimeComputable
      (fun z => List.replicate (polyLen a k (pairFstD z).length) true) :=
    (polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD
  have henc : PolyTimeComputable (fun z => Turing.pairEncode
      (List.replicate (polyLen a k (pairFstD z).length) true) (pairSndD z)) :=
    PolyTimeComputable.pairEncode hu polyTimeComputable_pairSndD
  have hg : PolyTimeComputable
      (fun z => (pairSndD z).take (polyLen a k (pairFstD z).length)) := by
    have heq : (fun z => (pairSndD z).take (polyLen a k (pairFstD z).length)) =
        takePrefixByLen ∘ (fun z => Turing.pairEncode
          (List.replicate (polyLen a k (pairFstD z).length) true) (pairSndD z)) := by
      funext z
      simp only [Function.comp, takePrefixByLen, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate]
    rw [heq]
    exact polyTimeComputable_takePrefixByLen.comp henc
  exact PolyTimeComputable.pairEncode polyTimeComputable_pairFstD hg

/-- `sliceDrop a k` is polynomial-time computable.
**Proof.** As `sliceTake`, with `dropPrefixByLen` in place of
`takePrefixByLen`. -/
theorem polyTimeComputable_sliceDrop (a k : ℕ) :
    PolyTimeComputable (sliceDrop a k) := by
  have hu : PolyTimeComputable
      (fun z => List.replicate (polyLen a k (pairFstD z).length) true) :=
    (polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD
  have henc : PolyTimeComputable (fun z => Turing.pairEncode
      (List.replicate (polyLen a k (pairFstD z).length) true) (pairSndD z)) :=
    PolyTimeComputable.pairEncode hu polyTimeComputable_pairSndD
  have hg : PolyTimeComputable
      (fun z => (pairSndD z).drop (polyLen a k (pairFstD z).length)) := by
    have heq : (fun z => (pairSndD z).drop (polyLen a k (pairFstD z).length)) =
        dropPrefixByLen ∘ (fun z => Turing.pairEncode
          (List.replicate (polyLen a k (pairFstD z).length) true) (pairSndD z)) := by
      funext z
      simp only [Function.comp, dropPrefixByLen, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate]
    rw [heq]
    exact polyTimeComputable_dropPrefixByLen.comp henc
  exact PolyTimeComputable.pairEncode polyTimeComputable_pairFstD hg

/-- Polynomial time is closed under the race construction.
**Proof sketch.** The `some true`-set of the race is the preimage of `M₁`'s
`some true`-set `V₁` under `sliceTake a k`, and the `some false`-set is the
intersection of the complement of that preimage with the preimage of `M₂`'s
`some true`-set `V₂` under `sliceDrop a k`; both are in `P` by
`Complexity.preimage_mem_P`, `Complexity.compl_mem_P`, and
`Complexity.inter_mem_P`, once `sliceTake`/`sliceDrop` are polynomial-time
(`polyTimeComputable_sliceTake`/`_sliceDrop`).  The off-pair freedom in the
efficiency notion lets us use these preimages verbatim. -/
theorem polyTimeModel_closedUnderRace : ClosedUnderRace polyTimeModel := by
  rintro M₁ M₂ a k ⟨V₁, _, hV₁, _, hM₁⟩ ⟨V₂, _, hV₂, _, hM₂⟩
  refine ⟨sliceTake a k ⁻¹' V₁,
    {z | z ∈ (sliceTake a k ⁻¹' V₁)ᶜ ∧ z ∈ sliceDrop a k ⁻¹' V₂},
    preimage_mem_P hV₁ (polyTimeComputable_sliceTake a k),
    inter_mem_P (compl_mem_P (preimage_mem_P hV₁ (polyTimeComputable_sliceTake a k)))
      (preimage_mem_P hV₂ (polyTimeComputable_sliceDrop a k)),
    fun x r => ?_⟩
  have hv1 : (Turing.pairEncode x r ∈ sliceTake a k ⁻¹' V₁) ↔
      M₁ x (r.take (polyLen a k x.length)) = true := by
    simp only [Set.mem_preimage, sliceTake, pairFstD_pairEncode, pairSndD_pairEncode]
    have h := (hM₁ x (r.take (polyLen a k x.length))).1
    simp only [boolVerifier, Option.some.injEq] at h
    exact h.symm
  have hv2 : (Turing.pairEncode x r ∈ sliceDrop a k ⁻¹' V₂) ↔
      M₂ x (r.drop (polyLen a k x.length)) = true := by
    simp only [Set.mem_preimage, sliceDrop, pairFstD_pairEncode, pairSndD_pairEncode]
    have h := (hM₂ x (r.drop (polyLen a k x.length))).1
    simp only [boolVerifier, Option.some.injEq] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · rw [hv1]
    cases h1 : M₁ x (r.take (polyLen a k x.length)) <;>
      cases h2 : M₂ x (r.drop (polyLen a k x.length)) <;>
      simp [raceVerifier, h1, h2]
  · rw [Set.mem_setOf_eq, Set.mem_compl_iff, hv1, hv2]
    cases h1 : M₁ x (r.take (polyLen a k x.length)) <;>
      cases h2 : M₂ x (r.drop (polyLen a k x.length)) <;>
      simp [raceVerifier, h1, h2]

/-- Polynomial time is closed under the output-postprocessing construction.
**Proof sketch.** The `some b`-set of `M` is literally one of the two
`P`-languages witnessing `Eff M`, and the `some (!b)`-set of the resulting
Boolean verifier is its complement (`Complexity.compl_mem_P`). -/
theorem polyTimeModel_closedUnderAnswerIs :
    ClosedUnderAnswerIs polyTimeModel := by
  rintro M b ⟨V₁, V₀, hV₁, hV₀, hM⟩
  cases b
  · refine ⟨V₀, V₀ᶜ, hV₀, compl_mem_P hV₀, fun x r => ?_⟩
    have h := (hM x r).2
    constructor
    · show some (decide (M x r = some false)) = some true ↔ _
      simp only [Option.some.injEq, decide_eq_true_eq]
      exact h
    · show some (decide (M x r = some false)) = some false ↔ _
      simp only [Option.some.injEq, decide_eq_false_iff_not]
      rw [h]
      exact Iff.rfl
  · refine ⟨V₁, V₁ᶜ, hV₁, compl_mem_P hV₁, fun x r => ?_⟩
    have h := (hM x r).1
    constructor
    · show some (decide (M x r = some true)) = some true ↔ _
      simp only [Option.some.injEq, decide_eq_true_eq]
      exact h
    · show some (decide (M x r = some true)) = some false ↔ _
      simp only [Option.some.injEq, decide_eq_false_iff_not]
      rw [h]
      exact Iff.rfl

/-- Polynomial time is closed under polynomial majority repetition.
**Proof sketch.** A counting loop over `polyLen a' k' |x|` blocks, each
block a run of the `P`-verifier on a poly-time-extractable slice of the
random string; the vote count and the final comparison are poly-time
(`Complexity.CounterProgPolyTime`). -/
theorem polyTimeModel_closedUnderMajority :
    ClosedUnderMajority polyTimeModel := by
  sorry

/-- Polynomial time is closed under polynomial `OR`-repetition.
**Proof sketch.** As for the majority closure, with the vote count replaced
by a single accepting flag. -/
theorem polyTimeModel_closedUnderAny : ClosedUnderAny polyTimeModel := by
  sorry

/-- Polynomial time is closed under negating the verifier's answer.
**Proof.** Swap the two witnessing `P`-languages. -/
theorem polyTimeModel_closedUnderNot : ClosedUnderNot polyTimeModel := by
  rintro M ⟨V₁, V₀, hV₁, hV₀, hM⟩
  refine ⟨V₀, V₁, hV₀, hV₁, fun x r => ?_⟩
  have h := hM x r
  simp only [boolVerifier, Option.some.injEq] at h ⊢
  rw [Bool.not_eq_true', Bool.not_eq_false']
  exact ⟨h.2, h.1⟩

/-- Polynomial time recognizes the shifted-OR construction.
**Proof sketch.** Decode the nested pair, slice `u` into its
`polyLen a' k' |x|` shift blocks, XOR each with `v` (bitwise XOR of
equal-length lists is poly-time), run the `P`-verifier on each, and `OR`
the results. -/
theorem polyTimeModel_closedUnderShiftOr :
    ClosedUnderShiftOr polyTimeModel := by
  sorry

/-- Polynomial-time verifiers have polynomial-size circuits when their
random string is fixed, with one size bound uniform in the random string:
the form of [AB09, Thm 6.6] that Adleman's counting argument consumes.
**Proof sketch.** Apply `Complexity.P_subset_PPoly` to the verifier's paired
acceptance language. For each input length and fixed random string, the
resulting circuit reads the doubled input bits, the separator, and the
random bits. A buffer supplies two distinct copies of each input bit and
constants for the separator and random string. Shifting all old vertex
numbers preserves distinct gate inputs and fan-in at most two.

The buffer adds exactly the number of free input bits to the old circuit
size. The paired length is bounded by a polynomial in the input length,
with coefficients depending only on the original randomness schedule.
Composing this bound with the circuit family's size polynomial gives one
bound uniform in the contents of the fixed random string. -/
theorem polyTimeModel_verifierHasCircuits :
    ∀ M a k, polyTimeModel.Eff (boolVerifier M) →
      VerifierHasCircuits M (polyLen a k) := by
  classical
  rintro M a k ⟨V₁, V₀, hV₁, hV₀, hM⟩
  have hPoly : V₁.InPPoly := Complexity.P_subset_PPoly hV₁
  obtain ⟨b, j, F, hF, hSize, hLanguage⟩ := hPoly
  refine ⟨b * (a + 3) ^ j + 1, (k + 1) * (j + 1), fun n r hr => ?_⟩
  let ell := 2 * n + 2 + r.length
  let C := F.circuit ell
  let D : BoolCircuit.DAGCircuit n := BoolCircuit.DAGCircuit.pairEncode r C
  have hD : D.IsFaninTwo :=
    BoolCircuit.DAGCircuit.pairEncode_isFaninTwo r C (hF ell)
  refine ⟨D, hD.1, hD, ?_, fun v => ?_⟩
  · -- The paired length is polynomial in n, uniformly in the chosen random string.
    have hN : 0 < n + 1 := Nat.succ_pos n
    have hnPow : n + 1 ≤ (n + 1) ^ (k + 1) :=
      Nat.le_self_pow (Nat.succ_ne_zero k) (n + 1)
    have hkPow : (n + 1) ^ k ≤ (n + 1) ^ (k + 1) :=
      Nat.pow_le_pow_right hN (Nat.le_succ k)
    have hLen : ell + 1 ≤ (a + 3) * (n + 1) ^ (k + 1) := by
      dsimp only [ell]
      rw [hr]
      unfold polyLen
      nlinarith [Nat.mul_le_mul_left a hkPow]
    have hCircuit : C.size ≤
        b * (a + 3) ^ j * (n + 1) ^ ((k + 1) * j) := by
      calc
        C.size ≤ b * (ell + 1) ^ j := hSize ell
        _ ≤ b * ((a + 3) * (n + 1) ^ (k + 1)) ^ j :=
          Nat.mul_le_mul_left b (Nat.pow_le_pow_left hLen j)
        _ = b * (a + 3) ^ j * (n + 1) ^ ((k + 1) * j) := by
          rw [mul_pow, ← pow_mul]
          ring
    have hExponent : (k + 1) * j ≤ (k + 1) * (j + 1) :=
      Nat.mul_le_mul_left (k + 1) (Nat.le_succ j)
    have hCircuit' : C.size ≤
        b * (a + 3) ^ j * (n + 1) ^ ((k + 1) * (j + 1)) :=
      hCircuit.trans (Nat.mul_le_mul_left (b * (a + 3) ^ j)
        (Nat.pow_le_pow_right hN hExponent))
    have hPositive : 0 < (k + 1) * (j + 1) :=
      Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos j)
    have hnSize : n ≤ (n + 1) ^ ((k + 1) * (j + 1)) :=
      (Nat.le_succ n).trans
        (Nat.le_self_pow (Nat.ne_of_gt hPositive) (n + 1))
    calc
      D.size = n + C.size := BoolCircuit.DAGCircuit.pairEncode_size r C
      _ ≤ (n + 1) ^ ((k + 1) * (j + 1)) +
          b * (a + 3) ^ j * (n + 1) ^ ((k + 1) * (j + 1)) :=
        Nat.add_le_add hnSize hCircuit'
      _ = (b * (a + 3) ^ j + 1) *
          (n + 1) ^ ((k + 1) * (j + 1)) := by ring
  · -- The buffer feeds the old circuit exactly the encoded pair (x,r).
    rw [BoolCircuit.DAGCircuit.pairEncode_eval r C v]
    have hAccept : C.eval (BoolCircuit.pairEncodeInput r v) = true ↔
        Turing.pairEncode (List.ofFn v) r ∈ V₁ := by
      rw [← hLanguage]
      exact BoolCircuit.DAGCircuitFamily.pairEncode_eval_eq_true_iff F r v
    have hVerifier := (hM (List.ofFn v) r).1
    simp only [boolVerifier, Option.some.injEq] at hVerifier
    have hCorrect := hAccept.trans hVerifier.symm
    cases hC : C.eval (BoolCircuit.pairEncodeInput r v) <;>
      cases hV : M (List.ofFn v) r <;> simp_all

/-- **Adleman's theorem for polynomial-time machines** ([AB09, Thm 7.17],
unconditionally): `BPP ⊆ P/poly`, with both sides the library's own classes
(`InBPP polyTimeModel` and `Language.InPPoly`). -/
theorem adleman_polyTime {L : Language Bool}
    (hL : InBPP polyTimeModel L) : L.InPPoly :=
  adleman polyTimeModel polyTimeModel_closedUnderMajority hL
    polyTimeModel_verifierHasCircuits

/-- Certificate-style `Σ₂` over the polynomial-time model coincides with the
library's `Complexity.SigmaP 2` ([AB09, Definition 5.3]).
**Proof sketch.** Both say: a `P`-predicate of the nested pair
`⟨⟨x, u⟩, v⟩` with `∃ u ∀ v` over blocks of length `C·(|x|+1)^c`.  The two
length normal forms (`polyLen a k` here, `C·(n+1)^c` in `PolyHierarchy`)
are identical, so the translation is a re-bracketing of the quantifiers
plus padding of the two block lengths to a common bound. -/
theorem inSigma2_polyTimeModel_iff (L : Language Bool) :
    InSigma2 polyTimeModel L ↔ L ∈ SigmaP 2 := by
  classical
  constructor
  · rintro ⟨N, a₁, k₁, a₂, k₂, ⟨V, hV, hN⟩, hiff⟩
    have h₁ : PolyHierarchy.UnaryPT
        (fun y : List Bool => polyLen a₁ k₁ y.length) := by
      have h := PolyHierarchy.unaryPT_poly a₁ k₁ polyTimeComputable_id
      simpa [polyLen] using h
    have h₂ : PolyHierarchy.UnaryPT
        (fun y : List Bool => polyLen a₂ k₂ y.length) := by
      have h := PolyHierarchy.unaryPT_poly a₂ k₂ polyTimeComputable_id
      simpa [polyLen] using h
    have hmem := PolyHierarchy.mem_altClass_of_normal (b := true) (i := 1)
      hV polyTimeComputable_id h₁ h₂
    have hkey : L = {y | qStep true (polyLen a₁ k₁ y.length)
        fun U => altQuant V (polyLen a₂ k₂ y.length) false 1
          (id (Turing.pairEncode y U))} := by
      ext y
      rw [Set.mem_setOf_eq, hiff y]
      constructor
      · rintro ⟨u, hu, hall⟩
        refine ⟨u, hu, fun v hv => ?_⟩
        show Turing.pairEncode (Turing.pairEncode y u) v ∈ V
        exact (hN y u v).mp (hall v hv)
      · rintro ⟨u, hu, hall⟩
        refine ⟨u, hu, fun v hv => ?_⟩
        exact (hN y u v).mpr (hall v hv)
    rw [hkey]
    exact hmem
  · intro hL
    obtain ⟨C, c, V, hV, hiff⟩ := mem_SigmaP_two_iff_exists_forall.mp hL
    refine ⟨fun x u v =>
        decide (Turing.pairEncode (Turing.pairEncode x u) v ∈ V),
      C, c, C, c,
      ⟨V, hV, fun x u v => by rw [decide_eq_true_eq]⟩, fun x => ?_⟩
    rw [hiff x]
    constructor
    · rintro ⟨u, hu, hall⟩
      refine ⟨u, hu, fun v hv => ?_⟩
      rw [decide_eq_true_eq]
      exact hall v hv
    · rintro ⟨u, hu, hall⟩
      refine ⟨u, hu, fun v hv => ?_⟩
      have h := hall v hv
      rw [decide_eq_true_eq] at h
      exact h

/-- **`ZPP = RP ∩ coRP` for polynomial-time machines** ([AB09, Thm 7.8],
unconditionally): the abstract theorem at `polyTimeModel`, with every
closure hypothesis discharged. -/
theorem zpp_eq_rp_inter_corp_polyTime (L : Language Bool) :
    InZPP polyTimeModel L ↔ InRP polyTimeModel L ∧ InCoRP polyTimeModel L :=
  inZPP_iff_inRP_and_inCoRP polyTimeModel polyTimeModel_closedUnderRace
    polyTimeModel_closedUnderAnswerIs polyTimeModel_closedUnderAny L

/-- **Sipser–Gács for polynomial-time machines** ([AB09, Thm 7.18],
unconditionally): `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ` with the library's own polynomial
hierarchy (`Complexity.SigmaP`/`Complexity.PiP`).

**Proof sketch.** The abstract `sipser_gacs` at `polyTimeModel` with its
closure hypotheses discharged, transported along
`inSigma2_polyTimeModel_iff` (and its complement instance for the `Π₂`
half). -/
theorem sipser_gacs_polyTime {L : Language Bool}
    (hL : InBPP polyTimeModel L) :
    L ∈ SigmaP 2 ∧ L ∈ PiP 2 := by
  obtain ⟨h1, h2⟩ := sipser_gacs polyTimeModel
    polyTimeModel_closedUnderMajority polyTimeModel_closedUnderNot
    polyTimeModel_closedUnderShiftOr hL
  exact ⟨(inSigma2_polyTimeModel_iff L).mp h1,
    (inSigma2_polyTimeModel_iff Lᶜ).mp h2⟩

end Randomized
```
