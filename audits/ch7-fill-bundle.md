## ===== audits/ch7-fill-pack.md =====

# External audit pack — Chapter 7, fill gate (the block-query loop and the closed machine surface)

Audited Lean surface: the **merged tree** on `complexity/arora-barak-ch3-4` at
`49658bb6`, where PR #11 and a follow-up merge brought the Chapter-7 campaign. The
summit landed at `d450376` on `complexity/arora-barak-ch7`; the closure sweep and this
pack's first draft sit on top of it at `0c22ae33`. Every ch7 module is byte-identical
on the merged tree to `0c22ae33`, except `ClassNP/PClosure.lean`, which also carries a
comment-only correction from the ch3-4 branch (attestation 1). This revision of the
pack (maintainer, 2026-10-10) re-runs attestations 1, 2, 4 and 5 on the merged tree
and adds question 7 (duplication). This is the **fill-audit gate of the Chapter 7
campaign**: the statement surface was audited and CLOSED at ch7-phase1
(`audits/ch7-phase1-{pack,findings,resolutions}.md`, zero blockers / zero majors at
`76fe2f46`); this gate covers everything the fill campaign **added** to the trusted
surface while discharging the last three machine closures. Record findings in
`audits/ch7-fill-findings.md`.

> **Provenance — read first.** After the phase-1 gate closed, the three remaining
> `PolyTimeModel` closures (`closedUnderMajority`/`closedUnderAny`/`closedUnderShiftOr`)
> were reduced to one chapter-neutral primitive — *`P` is closed under running a
> `P`-decider on polynomially many fixed-size blocks with OR / strict-majority /
> XOR-then-OR aggregation* (`briefs/ch7-pclosure-blocks.md`) — and that primitive was
> built and proved in this repository by the maintainer's agent. **No statement of the
> phase-1 audited surface changed** (attestation 1). What is new, and what you are
> auditing, is the surface the primitive added: two machine-infrastructure modules,
> three `P`-closure modules, and three additive headline lemmas in the frozen
> Chapter-1/2 file `ClassNP/PClosure.lean`.
>
> The product under audit is **definitions and theorem statements** — not tactic
> scripts, which Lean checks. Everything in scope is *proved*; remember that a
> wrong-but-proved statement is the worst outcome, so blind-restate each definition
> and statement before reading its docstring.

Source text: [AB09] ch. 7 (2007 web draft; reference pair under
`blueprint/src/references/`): the implicit machine-closure steps of Theorem 7.8
(`ZPP = RP ∩ coRP`: the OR amplifier), Theorem 7.10/Corollary 7.11 and Theorem 7.17
(majority repetition), and Theorem 7.18 (the XOR-shift OR of the Sipser–Gács proof).
The loop host itself is §1.2-folklore machine engineering ("simulate the machine on
each block"), audited for model fidelity rather than against a numbered theorem.

## Repository-side attestations (maintainer, remote machine — verify or challenge)

1. **Statement freeze / drift.** `audits/evidence/ch7/ch7-fill-drift-attestation.md`:
   of the 13 phase-1 modules, 12 are comment-stripped **identical** to the audited
   baseline `76fe2f46`; `Randomized/PolyTimeModel.lean` has the **same 20
   declarations, same order, zero signatures changed, import block byte-identical** —
   only the three `sorry` bodies became proofs. The frozen `ClassNP/PClosure.lean`
   gained exactly the three headline lemmas (additive; baseline sequence is an
   ordered prefix; one import added). No other pre-existing `.lean` file differs.
   **On the merged tree**, `PClosure.lean` additionally carries the ch3-4 branch's
   P0-gate correction (finding 5) to the docstrings of `lenEq_mem_P` and
   `lenLe_mem_P`. It is comment-stripped identical to `0c22ae33`. "No other file
   differs" holds relative to the ch7 branch. On the merged tree, the rest of
   `TCSlib/` is the ch3-4 campaign's own audited material and lies outside this gate.
2. **Elaboration.** Full **19-module** fresh-olean sweep (the 13 phase-1 modules plus
   the six fill modules, `scripts/ab_ch7_module_order.txt` order) via
   `scripts/lean_check_tree.sh` (Lean 4.25.0, Mathlib at the branch pin; **`lake
   build` not used** — banned on the campaign branch): every module exits 0, emits a
   fresh `.olean`, **zero `error:` lines** (`audits/logs/ch7-fill-sweep.log`).
   **Re-run on the merged tree** with the four touched facades (`Expanders`,
   `Randomized`, `ClassNP`, `TuringMachine`) appended: 23/23 modules exit 0, zero
   `error:` lines (`audits/logs/ch7-fill-merged-sweep.log`).
3. **Admissions inventory.** Exactly **1** `declaration uses 'sorry'` warning
   tree-wide: `Expanders/Chernoff.lean` — `walk_visits_concentration` (Theorem 7.41),
   **intentional and permanent** (book omits the proof; CH7-Q3, confirmed at
   phase-1). The fill campaign closed every other admission.
4. **Axiom hygiene (anti-tamper).** `audits/logs/ch7-fill-axioms.log`: 36 headline
   prints on the fresh olean tree — the Tier A/B results, all eight `polyTimeModel`
   closure/instantiation theorems, `adleman_polyTime`, `sipser_gacs_polyTime`,
   `zpp_eq_rp_inter_corp_polyTime`, the three `mem_P_of_block*` lemmas, the three
   block tests, `polyTimeComputable_emitIter`/`_xorD`, the slice lemmas, and
   `FinTM.exists_emitIterTM` — 35 print exactly
   `[propext, Classical.choice, Quot.sound]`; the single exception is the
   intentional Theorem 7.41 stub, which prints `sorryAx` as expected. **Re-run on
   the merged tree**: the 36 print lines are byte-identical
   (`audits/logs/ch7-fill-merged-axioms.log`).
5. **Policy conformance.** `audits/logs/ch7-fill-lint.log` over the 19-module
   surface: the fill modules and the closure's documentation sweep leave **one**
   standing finding — `Randomized/Classes.lean` is 1,328 lines (the documentation
   sweep grew it from the 1,266 lines first stated here; > 1,000, policy
   "must split"). Splitting a frozen, audited module is deliberately **not** done
   unilaterally at closure; the proposed disposition (split the counting layer out
   of `Classes.lean` post-gate, statements unchanged) is submitted to this round for
   approval. Flag if you believe the size bears on fidelity. **Re-run on the merged
   tree** (`audits/logs/ch7-fill-merged-lint.log`, five directories): 0 FAIL. This is
   the only WARN on the ch7 surface.

## What is under audit (the new trusted surface)

| Module | Key definitions | Key statements (all proved) |
|---|---|---|
| `TuringMachine/Build/EmitIterEmbed.lean` (18 public) | `SafeRun` (run avoiding a state strictly inside), `padAction`/`embedCfg` (tape-padding, state-injecting embedding of an `m`-tape module into a `k`-tape host) | `runFrom_output_prefix` (output-prefix commutation), `runFrom_output_extends` (append-only output), `embed_step`/`embed_run` (module runs embed step-for-step on live, off-exit states), `control_step`/`control_step'` |
| `TuringMachine/Build/EmitIterBody.lean` (1 public) | the body machine, copier and round lemmas are private | `FinTM.exists_emitIterTM`: machines for a step `g` and a chunk `e` within `C·(n+1)^c` budgets, plus an orbit length envelope `∀ w i, |g^[i] w| ≤ b·(|w|+1)^l`, yield one machine computing `w ↦ (range (a'·(|w|+1)^k' + 1)).flatMap (fun i => e (g^[i] w))` in `C·(n+1)^c` normal form |
| `ClassNP/PolyTimeBlockLoop.lean` (22 public) | `sliceTakeAt`/`sliceDropAt` (keep the first pair component, take/drop `a·(n+1)^k` of the second), `xorD` (truncating bitwise XOR of a pair's components), `blockDone`/`isNilB` (loop-state conventions) | `polyTimeComputable_emitIter` (the `FP`-level loop, consuming `exists_emitIterTM`), `polyTimeComputable_xorD`, the slice/`take1`/`headD`/`tail`/`isNil`/`or`/`not` `FP` helpers, `flatMap_range_eq_single`, `length_pair_components_le` |
| `ClassNP/PolyTimeBlockTests.lean` (3 public) | `blockAt a k z i` — the `i`-th length-`a·(n+1)^k` block of `pairSndD z`, `n = ‖pairFstD z‖` | `polyTimeComputable_blockAnyTest`, `polyTimeComputable_blockXorAnyTest` — the one-bit OR / XOR-then-OR aggregated block tests of a `P` indicator are poly-time |
| `ClassNP/PolyTimeBlockMajority.lean` (1 public) | private vote-counter loop | `polyTimeComputable_blockMajorityTest` — the strict-majority aggregated test is poly-time |
| `ClassNP/PClosure.lean` (**+3**, frozen file) | — | `mem_P_of_blockAny` (`{z \| ∃ i < a'·(n+1)^k', pairEncode (pairFstD z) (blockAt a k z i) ∈ V} ∈ P`), `mem_P_of_blockMajority` (strict majority of block indicators, `a'·(n+1)^k' < 2·countP`), `mem_P_of_blockXorAny` (nested pair `⟨⟨x,u⟩,v⟩`; blocks of `u` XORed with `v`, truncating) |

Consumption (already audited statements, proofs now closed): the three
`PolyTimeModel` closures reduce to the three headliners exactly as
`closedUnderRace` reduced to the slice primitives at phase-1.

## Known deviations and design choices (verify benign; flag others)

* **Truncating XOR.** `xorD` and the `mem_P_of_blockXorAny` statement use
  `List.zipWith xor` semantics (truncate to the shorter word) — the convention the
  phase-1 audit already confirmed for `shiftOrVerifier` (phase-1 finding 1 sweep).
* **The brief's sketch was wrong and is superseded.** `briefs/ch7-pclosure-blocks.md`
  sketched `xorD` as a one-register counter program; a one-pass register machine
  cannot pair bits across the separator. The landed `xorD` is instead a customer of
  the emit-iteration loop (one XOR bit per round). The *statement* is as the brief
  proposed; only the construction route changed.
* **Orbit-only envelope.** `polyTimeComputable_emitIter` demands
  `∀ w i, (g^[i] w).length ≤ b·(w.length+1)^l` — over **all** inputs and iteration
  counts, not only scheduled rounds. Customers discharge it with absorbing done
  states. (An earlier draft hypothesis quantifying over all state words was
  undischargeable and was replaced before any consumer landed; the statement was
  never part of an audited surface.)
* **Unary aggregation state.** Vote counts and countdowns are unary words inside the
  `pairEncode`d loop state; polynomial budgets enter only through
  `polyTimeComputable_polyUnary`-style unary schedules (the Argument-A discipline).
* **`blockAt`'s length source.** The block length and count schedules are evaluated
  at `(pairFstD z).length` — for the nested `blockXorAny` surface, at
  `(pairFstD (pairFstD w)).length`, i.e. the *inner* first component `x`, matching
  `shiftOrVerifier`'s `p x.length`.

## Specific questions for this gate

1. **Block fidelity.** Does `blockAt a k z i = ((pairSndD z).drop (i·q)).take q`,
   `q = a·(n+1)^k` at `n = ‖pairFstD z‖`, match the block conventions of
   `anyVerifier`/`majorityVerifier` (blocks of the random string at `p = polyLen a k`)
   and — through `blockAt a k (pairFstD w) i` with the *nested* length source — of
   `shiftOrVerifier`? Check off-by-one in `i·q`, the `+1` in the round count
   `a'·(n+1)^k' + 1`, and the degenerate schedules `a' = 0`, `a = 0`, `k = k' = 0`.
2. **Headline-statement fidelity.** Are the three `mem_P_of_block*` sets precisely
   the `some true`-sets of the three verifier constructions on `pairEncode`d inputs
   (given the efficiency witness's iff), so that complementation gives the
   `some false`-sets? Pay attention to the strict majority (`K < 2·count`, no
   off-by-one at even/odd `K`) and to malformed pairs (`pairFstD z = []` conventions).
3. **The loop statement.** Is `exists_emitIterTM`'s computed function — concatenation
   of `e (g^[i] w)` over `i ∈ range (a'·(|w|+1)^k' + 1)` — the right general form,
   and is its budget genuinely `C·(n+1)^c` (no hidden dependence on the orbit beyond
   the envelope)? Is the envelope hypothesis non-vacuous and dischargeable (the three
   customers and `xorD` discharge it; try to construct a natural customer that
   cannot)?
4. **Embedding soundness as stated.** Do `padAction`/`embedCfg` state the intended
   "module untouched on the padding tapes" semantics (no tape aliasing, inputs read
   through `Fin.castLE`, output preserved), and do `embed_step`/`embed_run`'s
   hypotheses (live states, off-exit, host transition equals padded module
   transition) match how a dispatch-style host actually behaves at its exit state?
5. **Output-prefix commutation.** Is `runFrom_output_prefix` the correct statement
   (the table never reads the output; output is append-only, per
   `runFrom_output_extends`), and is it strong enough for the round assembly's
   claim that the install call's own output stays empty?
6. **`PClosure` extension safety.** Do the three additions interact with the
   existing closure calculus only additively (no instance/namespace capture, no
   changed behavior of the pre-existing 13 declarations)?
7. **Duplication (this repository's `audits/TEMPLATE.md` failure mode 5, attached).**
   Screen the surface for duplicated proved material and verify the maintainer
   pre-screen (`audits/evidence/ch7/ch7-fill-duplication-screen.md`, attached). It
   reports no copies of pre-existing repository material. It does report one family of
   renamed re-proofs inside the stack: the OR, XOR and majority loops each carry their
   own copy of the same orbit, length and init lemmas, which puts
   `PolyTimeBlockMajority` at 4 of 14 declarations (28.6%), over this repository's
   one-fifth threshold. Report each confirmed copy family at **major** with the
   proposed fix "human acknowledgment required"; the gate may not close over them
   until the human maintainer accepts the debt and names its resolution. The family
   above is **already acknowledged** (the human maintainer, 2026-10-10: it is resolved
   in this repository's 12.2c refactor, as one generic lemma set with statements
   unchanged). Confirm its extent; it then does not hold the gate, though any further
   family you find does. Say whether
   the screen missed any copy, including re-derivations it cannot detect. Separately,
   compare the public `EmitIterEmbed` embedding layer (`padAction`/`embedCfg`/
   `embed_step`/`embed_run`) with the §12 `Build/Embed.lean` layer (attached). Report
   the overlap as facts, meaning what one layer states that the other does not, and do
   not propose a merge of the two; that merge is already scheduled in this
   repository's per-theme refactor (12.2c).

## Brief for the auditor

As at phase-1: audit the trusted surface (definitions and statements); do not review
tactic scripts. Hunt infidelity, trivialization, and missing hypotheses.
Blind-restate every definition before reading its docstring; attempt ≥3 adversarial
instantiations (suggested: `a' = 0`; `z` a malformed pair; `V = ∅` and `V = univ`;
`cE = cG = 0` budgets; an `e` emitting multiple bits per round). No blanket
approval; justify an empty table with the restatements. The gate closes only on a
round reporting **zero blockers and zero majors**.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = downstream work would build on a wrong statement;
**major** = statement fixable but materially misleading; **minor** = edge case or
naming/attribution; **note** = observation.

## ===== AroraBarakChapter7Plan.md =====

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

## ===== policy.md =====

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

## ===== workflow.md =====

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

## ===== audits/TEMPLATE.md =====

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

## ===== scripts/ab_ch7_module_order.txt =====

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
TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed
TCSlib/Complexity/TuringMachine/Build/EmitIterBody
TCSlib/Complexity/ClassNP/PolyTimeBlockLoop
TCSlib/Complexity/ClassNP/PolyTimeBlockTests
TCSlib/Complexity/ClassNP/PolyTimeBlockMajority
TCSlib/Complexity/ClassNP/PClosure
TCSlib/Complexity/Randomized/PolyTimeModel

## ===== audits/evidence/ch7/ch7-fill-drift-attestation.md =====

# Chapter-7 fill-campaign drift attestation

Baseline: the ch7-phase1 gate-audited surface, commit `76fe2f46` (the pack/bundle
commit; the post-gate minor/note sweeps at `c4114867` were comment-only and vanish
under comment stripping). Current: the campaign head carrying the completed fill
(`d450376` plus this closure commit, which also carries the closure documentation
sweep — 31 comment-only docstring/sketch additions across nine audited modules,
each mechanically verified comment-only and therefore invisible to the comparison
below). Method per `workflow.md` §6: strip comments
from every module, compare the ordered declaration sequence and multiset against
the baseline, and enumerate public declarations gained / lost / signature-changed.
Signature comparison splits each declaration at its first top-level `:=`
(whitespace-normalized), so a filled proof body never masks a statement change.

## The 13-module audited surface

| Module | decls (base → now) | result |
|---|---:|---|
| `Expanders/Basic` | 17 | comment-stripped **identical** |
| `Expanders/Mixing` | 2 | comment-stripped **identical** |
| `Expanders/Walks` | 17 | comment-stripped **identical** |
| `Expanders/Chernoff` | 1 | comment-stripped **identical** (Thm 7.41 stub untouched) |
| `Randomized/SchwartzZippel` | 1 | comment-stripped **identical** |
| `Randomized/ErrorReduction` | 13 | comment-stripped **identical** |
| `Randomized/Classes` | 50 | comment-stripped **identical** (gate's minor sweep was comment-only) |
| `Randomized/Adleman` | 2 | comment-stripped **identical** |
| `Randomized/SipserGacs` | 13 | comment-stripped **identical** (gate's note sweep was comment-only) |
| `TuringMachine/CounterProgInput` | 5 | comment-stripped **identical** |
| `CircuitComplexity/PairEncode` | 22 | comment-stripped **identical** |
| `ClassNP/PolyTimePrefix` | 16 | comment-stripped **identical** |
| `Randomized/PolyTimeModel` | 20 → 20 | **same 20 declarations, same order, zero signatures changed, import block byte-identical**; the only comment-stripped difference is the three `sorry` bodies (`closedUnderMajority`/`closedUnderAny`/`closedUnderShiftOr`) replaced by proofs. The consumed `mem_P_of_block*` lemmas reach the module through its pre-existing `PolyHierarchy/{Padding → Normalize → Collapse}` import chain (`Padding` imports `ClassNP/PClosure`) |

## The frozen Chapter-1/2 file extended by this campaign

| Module | decls (base → now) | result |
|---|---:|---|
| `ClassNP/PClosure` | 13 → 16 | baseline sequence is an **ordered prefix** of the current sequence; gained exactly `mem_P_of_blockAny`, `mem_P_of_blockMajority`, `mem_P_of_blockXorAny` (all public, all proved); **nothing lost, zero signatures changed**; one import added (`ClassNP/PolyTimeBlockMajority`) |

## New trusted surface (no baseline — enumerated for the fill-audit pack)

| Module | decls | public |
|---|---:|---|
| `TuringMachine/Build/EmitIterEmbed` | 18 | 18 (safe runs, output-prefix commutation, padding embedding, control steps) |
| `TuringMachine/Build/EmitIterBody` | 19 | 1 (`FinTM.exists_emitIterTM`; the body machine, copier, and round lemmas are private) |
| `ClassNP/PolyTimeBlockLoop` | 32 | 22 (slices, FP helpers, `polyTimeComputable_emitIter`, `xorD`) |
| `ClassNP/PolyTimeBlockTests` | 25 | 3 (`blockAt`, the OR and XOR-then-OR tests) |
| `ClassNP/PolyTimeBlockMajority` | 14 | 1 (the strict-majority test) |

No other `.lean` file differs from the baseline anywhere in the repository
(`git diff --name-only 76fe2f46..HEAD -- 'TCSlib/*'` lists exactly the modules
tabled above).

**Conclusion.** Nothing audited moved: the phase-1 statement surface is intact
declaration-for-declaration and signature-for-signature; the campaign's additions
are the enumerated new modules and the three additive `PClosure` headliners, all
within the fill-audit pack's scope.

## ===== audits/evidence/ch7/ch7-fill-duplication-screen.md =====

# Chapter-7 fill surface — duplication screen (merged tree)

Maintainer pre-screen for the ch7 fill gate's duplication question (pack question 7),
run on the merged tree `complexity/arora-barak-ch3-4` at `49658bb6` under this
repository's duplication governance (`policy.md` **Duplication**, `workflow.md` §4,
`audits/TEMPLATE.md` failure mode 5). The auditor verifies these facts and judges the
classification; it is a starting point, not a substitute for the audit.

## Method

Script: `audits/evidence/ch7/ch7-fill-duplication-screen.py`. Every `.lean` file under
`TCSlib/` (561 files) is comment-stripped and split into declarations. Each of the
**112 declarations** of the six-file surface (`Build/EmitIterEmbed`,
`Build/EmitIterBody`, `ClassNP/PolyTimeBlockLoop`, `PolyTimeBlockTests`,
`PolyTimeBlockMajority`, and the three new `PClosure` headliners) is cut into token
shingles in two modes: **exact** (25-token runs) and **renamed** (50-token runs with
every identifier abstracted, so a consistently renamed copy still matches). A
declaration's overlap is the fraction of its shingles found in one other declaration
anywhere in the tree. Reported threshold: ≥ 50%.

**Coverage qualification.** The screen detects contiguous reproduction, exact or under
consistent renaming. It does not detect re-derivations whose proofs are restructured,
and it says nothing about design-level parallels. Whether `EmitIterEmbed` duplicates
the §12 `Build/Embed` layer is a non-mechanical question for the auditor.

## Results

**Class A: one per-loop lemma set re-proved under renaming (debt).** The OR, XOR and
strict-majority loops each carry their own copy of the same orbit, length and init
lemmas. The proofs are identical up to the step function's name; a single lemma
quantified over the step function would serve all three. The later instance of each
pair is counted as the copy (`PolyTimeBlockTests` predates the split that produced
`PolyTimeBlockMajority`; within `Tests` the OR loop predates the XOR loop).

| Copy | Original | Overlap (renamed / exact) | Lines |
|---|---|---|---:|
| `Majority::length_majStep_iterate` | `Tests::length_xorStep_iterate` | 100% / 39% | 15 |
| `Majority::majStep_orbit_done` | `Tests::anyStep_orbit_done` | 100% / 49% | 16 |
| `Majority::length_majStep_le` | `Tests::length_xorStep_le` | 72% / 63% | 46 |
| `Majority::polyTimeComputable_majInit` | `Tests::polyTimeComputable_anyInit` | 53% / 38% (reverse direction 83%) | 8 |
| `Tests::xorStep_orbit_done` | `Tests::anyStep_orbit_done` | 53% / 27% | 21 |
| `Tests::xorLoop_output` | `Tests::anyLoop_output` | 51% / 19% (reverse 59%) | 30 |

All six members are `private`. Per-file totals:

- **`PolyTimeBlockMajority`: 4 of 14 declarations (28.6%, 85 lines). This is above the
  one-fifth threshold** (`workflow.md` §4), so a `backlog.md` §1 human-review item is
  opened. **The human maintainer has acknowledged it** (2026-10-10): it is resolved in
  the 12.2c refactor, as one generic lemma set with statements unchanged.
- **`PolyTimeBlockTests`: 2 of 25 declarations (8.0%).**

**Class B: mirror pairs (dual statements; conventional, not counted).** These are
dual statements whose proofs coincide under the swap, the usual Lean
`_left`/`_right` pattern:

- `PolyTimeBlockLoop`: `polyTimeComputable_take1`/`_tail` and
  `polyTimeComputable_sliceTakeAt`/`_sliceDropAt` (100% renamed).
- `EmitIterBody`: `embed_ofWords_left`/`_right` (100% renamed).
- `PolyTimeBlockLoop::length_pairSndD_le` against
  `PolyTimePairing::length_pairFstD_le` (53% renamed, only 19 shingles — the Snd/Fst
  dual).

**Borderline (auditor to judge).**

- `PolyTimeBlockLoop::length_xorPairStep_le` against `length_sliceDropAt_le` in the
  same file: 87% renamed, 0% exact. They have the same proof shape over different step
  functions.
- `Majority::majStep` against `polyTimeComputable_majStep`: 55–63%. This is a
  definition overlapping its own poly-time proof, which restates its case structure;
  it is not believed to be duplication.

**Class C: copies of pre-existing repository material: none.** Matched against
everything outside the six files, the largest overlap is the 19-shingle Snd/Fst dual
above (53%). The rest:

| Surface declaration | Closest outside match | Overlap |
|---|---|---|
| `polyTimeComputable_or` | `PolyTimePairing::polyTimeComputable_and` (a dual) | 44% exact |
| `EmitIterEmbed::embedCfg` | `Oracle::Cfg.embedOracle` (a design parallel) | 42% renamed |
| `mem_P_of_blockMajority` | `PolyTimeModel::polyTimeModel_closedUnderMajority` (its consumer) | 25% |

None of the §12 material (`Build/Embed`, `Build/Seam`, `Build/Catalog`) or the loop
library (`Build/Loop`, `Build/Primitives`) appears among the matches.

## Design-level parallel (not mechanical; recorded in the ledger watch items)

`EmitIterEmbed.lean` exports a **public** tape-padding, state-injecting embedding layer
(`padAction`, `embedCfg`, `embed_step`, `embed_run`, `SafeRun`: 18 public
declarations, no private ones). It was written against `main`, which lacks the §12
`Build/Embed.lean` (attached to the bundle for comparison). The two layers are
independently written, and the screen finds no copies between them. Consolidating them
into one embedding API is on the **12.2c docket** (user decision, 2026-10-10).

## ===== briefs/ch7-pclosure-blocks.md =====

# Brief: block-query closure of `P` (shared composition primitive)

**Status:** coordination proposal (not yet scheduled fill). Rides the ch7 → ch3-4
coordination PR. Target branch for the eventual fill: the shared `complexity/arora-barak-ch3-4`.

## Why this exists

`Randomized/PolyTimeModel.lean`'s three open closures — `polyTimeModel_closedUnderMajority`,
`_closedUnderAny`, `_closedUnderShiftOr` — all reduce to one missing, **chapter-neutral**
fact: *`P` is closed under running a `P`-decider on a polynomial number of fixed-size
blocks of the input and aggregating the answers* (OR / strict-majority / XOR-then-OR).
The library has pointwise `P`-closure (`PClosure.lean`: preimage, ∩, ∪, complement,
finite `mem_P_of_atoms`) but **no** "polynomially-many `P`-queries with aggregation"
closure (the earlier infra survey confirmed: an `OracleTM` type exists, but no `P^P = P`
style lemma anywhere). ch3-4's closure/composition work needs the same primitive, so it
is built **once** here and consumed by both.

## Placement (per policy §1)

* **Headline closure lemmas → extend `TCSlib/Complexity/ClassNP/PClosure.lean`** (the
  `P`-closure home; 183 lines now, room to grow; `mem_P_of_*` naming). *This modifies a
  frozen, audited Chapter-1/2 file — flag it for audit per standing practice.*
* **Heavy machinery → a new general helper `TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean`**
  (namespace `Complexity`), imported by `PClosure.lean`, so the closure file stays a
  statements layer and the loop/aggregator proofs don't blow its size budget. Reuses the
  existing general pieces: `PolyTimePrefix` (take/drop at a length), `CounterProgInput`,
  `TuringMachine/Build/Loop.lean` (the bounded `emit`/`find` loop combinators),
  `test_of_mem_P`/`mem_P_of_test`.
* `Randomized/PolyTimeModel.lean` stays a **thin consumer** — the three `closedUnder*`
  discharges become a few lines each, exactly as `closedUnderRace` reduced to the slice
  primitives.

## Sub-obligations (general, reusable)

1. **Block extraction, poly-time.** `fun w i => (pairSndD w).drop (i * q |pairFstD w|) |>.take (q |pairFstD w|)` and the re-paired `pairEncode (pairFstD w) (that block)` are `PolyTimeComputable` in `w` for each loop index, with `q` a `polyLen` schedule. Generalizes `PolyTimePrefix.take/drop` from a single prefix to the `i`-th block.
2. **Bitwise XOR, poly-time.** `fun p => List.zipWith xor (pairFstD p) (pairSndD p)` is `PolyTimeComputable` (truncating on unequal lengths — see the audited ch7-phase1 finding 1). Needed only for `shiftOr`.
3. **Bounded aggregation loop.** Given `V ∈ P` (hence its indicator is `PolyTimeComputable` by `test_of_mem_P`), the counts/flags
   * `fun w => (List.range (k |pairFstD w|)).countP (fun i => blockTest V w i)` and
   * `fun w => (List.range (k |pairFstD w|)).any (fun i => blockTest V w i)`

   are `PolyTimeComputable`, via a `Build/Loop.lean` host that installs the `P`-decider as
   the per-round call (the pattern the repaired `PolyTimePrefix` counter program already
   uses). This is the one genuinely new combinator.

## Headline lemmas to add to `PClosure.lean`

Stated for an arbitrary per-block `P`-language `V` and `polyLen` schedules `q = polyLen a k`,
`K = polyLen a' k'` (sketch signatures; final forms agreed with ch3-4):

```
theorem mem_P_of_blockAny     (hV : V ∈ P) (a k a' k') :
  { w | ∃ i < K |pairFstD w|, pairEncode (pairFstD w) (block q w i) ∈ V } ∈ P
theorem mem_P_of_blockMajority (hV : V ∈ P) (a k a' k') :
  { w | K |pairFstD w| < 2 * ((List.range (K |pairFstD w|)).countP
          (fun i => decide (pairEncode (pairFstD w) (block q w i) ∈ V))) } ∈ P
theorem mem_P_of_blockXorAny  (hV : V ∈ P) (a k a' k') :   -- nested pair ⟨⟨x,u⟩,v⟩, for shiftOr
  { w | ∃ i < K …, pairEncode x (List.zipWith xor v (block q u i)) ∈ V } ∈ P
```

## How the three closures reduce (thin, in `PolyTimeModel.lean`)

* `closedUnderAny`: the some-true set of `anyVerifier M (polyLen a k) (polyLen a' k')` is
  exactly `mem_P_of_blockAny` instantiated at `V = M`'s some-true `P`-language; some-false
  set is its complement (`compl_mem_P`). (Same off-pair-freedom argument as
  `closedUnderRace`.)
* `closedUnderMajority`: some-true set = `mem_P_of_blockMajority`; some-false = complement.
* `closedUnderShiftOr` (two-witness): the `EffTwoWitness` set = `mem_P_of_blockXorAny` on
  the nested `pairEncode (pairEncode x u) v`.

## Verification

Per `workflow.md §6`: `scripts/lean_check_tree.sh` green on `PClosure.lean`, the new helper,
and `PolyTimeModel.lean`; `#print axioms` on the three `closedUnder*` and the downstream
`adleman_polyTime`/`sipser_gacs_polyTime` showing `[propext, Classical.choice, Quot.sound]`
once filled (no `sorryAx`). Then the only remaining ch7 admission is the intentional
Thm 7.41.

## Coordination note for ch3-4

If ch3-4 already has a block-loop / P-query-composition combinator, we adopt theirs and
delete this (or vice versa) — the goal is one shared primitive, not two. The headline
`mem_P_of_block*` names and the `PolyTimeBlockLoop` helper are proposals open to their
conventions.

## ===== TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Run embedding for loop bodies

Generic machine-construction infrastructure shared by loop-body assemblies
(first customer: `TCSlib.Complexity.TuringMachine.Build.EmitIterBody`):

* **safe runs** — a run segment that never visits an avoided (anchor) state
  strictly before its endpoint, closed under prepending a step and under
  concatenation: the shape of the `Turing.FinTM.exists_emitLoopTM` startup
  and round obligations;
* **output-prefix commutation** — the transition table never reads the
  output tape and the output is append-only, so prepending a fixed output
  prefix commutes with running the machine, and outputs only ever extend;
* **the tape-padding, state-injecting embedding** — a clean-call module over
  `m ≤ k` tapes runs inside a `k`-tape host on its first `m` work tapes with
  its states injected into the host's state type, step for step
  (`embed_step`/`embed_run`), while the padding tapes stay blank;
* **control steps** — a transition that only changes control (and possibly
  moves the input head) replaces just those configuration components.

## Main definitions

* `Turing.SafeRun`, `Turing.padAction`, `Turing.embedCfg`.

## Main results

* `Turing.runFrom_output_prefix`, `Turing.runFrom_output_extends`,
  `Turing.embed_run`, `Turing.control_step`, `Turing.control_step'`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the machine model these
  constructions assemble.)
-/

namespace Turing

open MultiTapeTM

variable {k m : ℕ} {B SS : Type} {x : List Bool}

/-! ### Safe runs

A run segment together with the promise that no strictly earlier
configuration sits at the avoided (anchor) state: the shape of the
`exists_emitLoopTM` startup and round obligations, closed under
single-step prepending and concatenation. -/

/-- A run from `c` to `c'` in exactly `t` steps that never visits the state
`avoid` strictly before `t`. -/
def SafeRun (H : MultiTapeTM k Bool B) (avoid : B)
    (c : Cfg k Bool B x) (t : ℕ) (c' : Cfg k Bool B x) : Prop :=
  H.runFrom c t = c' ∧ ∀ t' < t, (H.runFrom c t').state ≠ some avoid

/-- The empty run is safe. -/
theorem SafeRun.zero {H : MultiTapeTM k Bool B} {avoid : B}
    {c : Cfg k Bool B x} : SafeRun H avoid c 0 c :=
  ⟨rfl, fun t' ht' => absurd ht' (by omega)⟩

/-- Prepend one non-avoided step to a safe run. -/
theorem SafeRun.cons {H : MultiTapeTM k Bool B} {avoid : B}
    {c c₁ c' : Cfg k Bool B x} {t : ℕ} (hstep : H.step c = c₁)
    (hc : c.state ≠ some avoid) (h : SafeRun H avoid c₁ t c') :
    SafeRun H avoid c (t + 1) c' := by
  have hone : H.runFrom c 1 = c₁ := by
    simp [runFrom, hstep]
  refine ⟨?_, ?_⟩
  · rw [show t + 1 = 1 + t by omega, runFrom_add, hone]
    exact h.1
  · intro t' ht'
    cases t' with
    | zero => simpa using hc
    | succ u =>
      rw [show u + 1 = 1 + u by omega, runFrom_add, hone]
      exact h.2 u (by omega)

/-- Concatenate safe runs. -/
theorem SafeRun.trans {H : MultiTapeTM k Bool B} {avoid : B}
    {c c₁ c' : Cfg k Bool B x} {t₁ t₂ : ℕ} (h₁ : SafeRun H avoid c t₁ c₁)
    (h₂ : SafeRun H avoid c₁ t₂ c') : SafeRun H avoid c (t₁ + t₂) c' := by
  refine ⟨?_, ?_⟩
  · rw [runFrom_add, h₁.1]
    exact h₂.1
  · intro t' ht'
    by_cases hlt : t' < t₁
    · exact h₁.2 t' hlt
    · obtain ⟨u, rfl⟩ : ∃ u, t' = t₁ + u := ⟨t' - t₁, by omega⟩
      rw [runFrom_add, h₁.1]
      exact h₂.2 u (by omega)

/-! ### Output-prefix commutation

The transition table never reads the output tape and the output is
append-only, so prepending a fixed prefix to the output commutes with
running the machine. -/

/-- One step commutes with an output prefix. -/
theorem step_output_prefix (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (pre : List Bool) :
    H.step { c with output := pre ++ c.output } =
      { H.step c with output := pre ++ (H.step c).output } := by
  obtain ⟨st, pos, tapes, tpos, out⟩ := c
  cases st with
  | none => rfl
  | some q =>
    have hws : (⟨some q, pos, tapes, tpos, pre ++ out⟩ : Cfg k Bool B x).workTapeSymbols =
        (⟨some q, pos, tapes, tpos, out⟩ : Cfg k Bool B x).workTapeSymbols := rfl
    simp [MultiTapeTM.step, Action.apply, Cfg.inputSymbol, hws, List.append_assoc]

/-- A run commutes with an output prefix. -/
theorem runFrom_output_prefix (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (pre : List Bool) (t : ℕ) :
    H.runFrom { c with output := pre ++ c.output } t =
      { H.runFrom c t with output := pre ++ (H.runFrom c t).output } := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
    rw [runFrom_succ_eq_step, runFrom_succ_eq_step, step_output_prefix]
    exact ih (H.step c)

/-- The output tape is append-only along a run. -/
theorem runFrom_output_extends (H : MultiTapeTM k Bool B)
    (c : Cfg k Bool B x) (t : ℕ) :
    ∃ o, (H.runFrom c t).output = c.output ++ o := by
  induction t generalizing c with
  | zero => exact ⟨[], by simp⟩
  | succ t ih =>
    rw [runFrom_succ_eq_step]
    obtain ⟨o, ho⟩ := ih (H.step c)
    unfold MultiTapeTM.step at ho ⊢
    cases hq : c.state with
    | none =>
      rw [hq] at ho
      exact ⟨o, ho⟩
    | some q =>
      rw [hq] at ho
      refine ⟨(H.tr q c.inputSymbol c.workTapeSymbols).output.toList ++ o, ?_⟩
      rw [ho]
      simp [Action.apply]

/-! ### Halted runs are stationary -/

/-- A halted configuration never changes. -/
theorem runFrom_of_halted (H : MultiTapeTM k Bool B)
    {c : Cfg k Bool B x} (h : c.state = none) (t : ℕ) : H.runFrom c t = c := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [runFrom_add, ih]
    simp [runFrom, step_of_halt h]

/-- Every configuration strictly before a live endpoint is live. -/
theorem state_isSome_of_runFrom (H : MultiTapeTM k Bool B)
    {c : Cfg k Bool B x} {t : ℕ} {qf : B}
    (hf : (H.runFrom c t).state = some qf) {j : ℕ} (hj : j ≤ t) :
    ∃ q, (H.runFrom c j).state = some q := by
  cases hq : (H.runFrom c j).state with
  | some q => exact ⟨q, rfl⟩
  | none =>
    exfalso
    have hstat : H.runFrom c t = H.runFrom c j := by
      obtain ⟨u, rfl⟩ : ∃ u, t = j + u := ⟨t - j, by omega⟩
      rw [runFrom_add, runFrom_of_halted H hq]
    rw [hstat, hq] at hf
    exact Option.noConfusion hf

/-! ### Tape-padding, state-injecting embedding

A clean-call module over `m ≤ k` tapes runs inside the `k`-tape body on its
first `m` work tapes, with its states injected into the body's state type;
the extra tapes stay blank and their heads stay at the origin. -/

/-- Pad a module action to the host: act on the first `m` tapes, leave the
rest alone, and map the successor state. -/
def padAction (hmk : m ≤ k) (f : Option SS → Option B)
    (a : Action m Bool SS) : Action k Bool B where
  inputTape := a.inputTape
  workTapes := fun i =>
    if h : (i : ℕ) < m then a.workTapes ⟨i, h⟩ else (none, 0)
  output := a.output
  state := f a.state

/-- Embed a module configuration into the host. -/
def embedCfg (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) : Cfg k Bool B x where
  state := c.state.map inject
  inputPos := c.inputPos
  workTapes := fun i =>
    if h : (i : ℕ) < m then c.workTapes ⟨i, h⟩ else fun _ => none
  workTapePos := fun i =>
    if h : (i : ℕ) < m then c.workTapePos ⟨i, h⟩ else 0
  output := c.output

/-- Embedding a canonical seam gives a canonical seam with the padded word
assignment. -/
theorem embedCfg_ofWords (hmk : m ≤ k) (inject : SS → B) (q : SS)
    (w : Fin m → List Bool) :
    embedCfg hmk inject (Cfg.ofWords (input := x) q w) =
      Cfg.ofWords (inject q)
        (fun i => if h : (i : ℕ) < m then w ⟨i, h⟩ else []) := by
  unfold embedCfg Cfg.ofWords
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases h : (i : ℕ) < m <;> simp [h]
  · funext i
    by_cases h : (i : ℕ) < m <;> simp [h]

/-- Applying a padded action to an embedded configuration embeds the applied
module configuration. -/
theorem padAction_apply (hmk : m ≤ k) (inject : SS → B)
    (a : Action m Bool SS) (c : Cfg m Bool SS x) (b : B) :
    (padAction hmk (Option.map inject) a).apply
        { embedCfg hmk inject c with state := some b } =
      embedCfg hmk inject (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    by_cases h : (i : ℕ) < m
    · simp only [Action.apply, padAction, embedCfg, dif_pos h]
    · simp only [Action.apply, padAction, embedCfg, dif_neg h]
  · funext i
    by_cases h : (i : ℕ) < m
    · simp only [Action.apply, padAction, embedCfg, dif_pos h]
    · simp only [Action.apply, padAction, embedCfg, dif_neg h]
      rfl

/-- The embedded configuration reads the module's work symbols on the first
`m` tapes. -/
theorem embedCfg_workTapeSymbols (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) (b : B) :
    (fun i => ({ embedCfg hmk inject c with state := some b } :
        Cfg k Bool B x).workTapeSymbols (Fin.castLE hmk i)) =
      c.workTapeSymbols := by
  funext i
  have h : ((Fin.castLE hmk i : Fin k) : ℕ) < m := i.isLt
  simp only [Cfg.workTapeSymbols, embedCfg, dif_pos h]
  congr 1 <;> exact congrArg _ (Fin.eta i i.isLt) <;> rfl

/-- Embedding commutes with replacing the output. -/
theorem embedCfg_output (hmk : m ≤ k) (inject : SS → B)
    (c : Cfg m Bool SS x) (o : List Bool) :
    embedCfg hmk inject { c with output := o } =
      { embedCfg hmk inject c with output := o } := rfl

/-- A one-step run is a step. -/
theorem runFrom_one (H : MultiTapeTM k Bool B) (c : Cfg k Bool B x) :
    H.runFrom c 1 = H.step c := by
  simp [MultiTapeTM.runFrom]

/-- One host step at a state behaving like the module's state `q` tracks one
module step.
**Proof sketch.** Both steps dispatch their transition tables on live states;
the embedded configuration reads the same input symbol and, through
`embedCfg_workTapeSymbols`, the same work symbols, so the host's action is
the padded module action, and `padAction_apply` pushes it through the
embedding. -/
theorem embed_step (hmk : m ≤ k) (M : MultiTapeTM m Bool SS)
    (H : MultiTapeTM k Bool B) (inject : SS → B)
    (c : Cfg m Bool SS x) (q : SS) (hq : c.state = some q) (b : B)
    (htr : ∀ inp work, H.tr b inp work =
      padAction hmk (Option.map inject)
        (M.tr q inp (fun i => work (Fin.castLE hmk i)))) :
    H.step { embedCfg hmk inject c with state := some b } =
      embedCfg hmk inject (M.step c) := by
  have hIS : ({ embedCfg hmk inject c with state := some b } :
      Cfg k Bool B x).inputSymbol = c.inputSymbol := rfl
  have hstepL : H.step { embedCfg hmk inject c with state := some b } =
      (H.tr b ({ embedCfg hmk inject c with state := some b } :
          Cfg k Bool B x).inputSymbol
        ({ embedCfg hmk inject c with state := some b } :
          Cfg k Bool B x).workTapeSymbols).apply
        { embedCfg hmk inject c with state := some b } := rfl
  have hstepR : M.step c = (M.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hq]
  rw [hstepL, hstepR, htr, hIS, embedCfg_workTapeSymbols]
  exact padAction_apply hmk inject _ c b

/-- A module run strictly inside the avoided exit embeds step-for-step into
the host, provided the host's transition at every injected live state is the
padded module transition.
**Proof sketch.** Induction on the run length: every strictly earlier
configuration is live and off the exit by hypothesis, so `embed_step`
transports each step. -/
theorem embed_run (hmk : m ≤ k) (M : MultiTapeTM m Bool SS)
    (H : MultiTapeTM k Bool B) (inject : SS → B) (ex : SS)
    (htr : ∀ q : SS, q ≠ ex → ∀ inp work,
      H.tr (inject q) inp work =
        padAction hmk (Option.map inject)
          (M.tr q inp (fun i => work (Fin.castLE hmk i))))
    (c : Cfg m Bool SS x) (t : ℕ)
    (hstate : ∀ j < t, ∃ q, (M.runFrom c j).state = some q ∧ q ≠ ex) :
    H.runFrom (embedCfg hmk inject c) t = embedCfg hmk inject (M.runFrom c t) := by
  induction t generalizing c with
  | zero => simp
  | succ t ih =>
    obtain ⟨q, hq, hqex⟩ := hstate 0 (by omega)
    simp only [runFrom_zero] at hq
    have hstep : H.step (embedCfg hmk inject c) = embedCfg hmk inject (M.step c) := by
      have hc : { embedCfg hmk inject c with state := some (inject q) } =
          embedCfg hmk inject c := by
        simp [embedCfg, hq]
      rw [← hc]
      exact embed_step hmk M H inject c q hq (inject q) (htr q hqex)
    rw [runFrom_succ_eq_step, runFrom_succ_eq_step, hstep]
    exact ih (M.step c) (fun j hj => by
      have := hstate (j + 1) (by omega)
      simpa [runFrom, Function.iterate_succ_apply] using this)


end Turing
```

## ===== TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.TuringMachine.Build.EmitIterEmbed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The emit-iteration body

The host machine behind `Complexity.polyTimeComputable_emitIter` (in
`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`): one finite machine that, on
input `w`, concatenates the chunks `e (g^[i] w)` for `i = 0, …, R |w|`, in
polynomial time, given machines for the step `g` and the chunk `e` and a
polynomial length envelope for the orbit of `g`.

It is an instance of `Turing.FinTM.exists_emitLoopTM`.  The body machine's
startup copies the native input onto work tape zero (the loop's round state)
and rewinds both heads to the canonical seam; each round is two clean calls
on the tape-resident state word — an emit-mode call
(`Turing.FinTM.exists_emitCallTM`) forwarding the chunk `e s` to the physical
output, then an install-mode call (`Turing.FinTM.exists_installCallTM`)
replacing the word by `g s` — glued by two control states.  The clean-call
modules run on the body's first tapes through a tape-padding, state-injecting
embedding (`padAction`/`embedCfg` below); the round assembly commutes the
already-emitted chunk past the install call with an output-prefix lemma.

## Main definitions

None — the body machine, its embedding, and the phase configurations are
private to this file.

## Main results

* `Turing.FinTM.exists_emitIterTM` — the finite machine computing the
  concatenated chunks of a polynomially clocked iteration, within a
  polynomial budget in the `C·(n+1)^c` normal form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; §7.3–§7.4: the folklore
  "simulate the machine on each block" loop this host implements.)
-/


namespace Turing

open MultiTapeTM

variable {k m : ℕ} {B SS : Type} {x : List Bool}

/-! ### The body machine

Startup copies the native input onto work tape zero and rewinds both heads;
a round is the emit-mode call (whose first action the anchor itself performs,
so an entry state equal to the exit state still runs), a control handoff, the
install-mode call (likewise inlined into `gStart`), and a control return to
the anchor. -/

/-- Control states of the emit-iteration body. -/
private inductive BodyState (SE SG : Type) where
  | copy
  | rwTape
  | rwInput0
  | rwInput
  | anchor
  | callE (q : SE)
  | gStart
  | callG (q : SG)
  deriving DecidableEq

private instance {SE SG : Type} [Fintype SE] [Fintype SG] :
    Fintype (BodyState SE SG) := derive_fintype% _

/-- The emit-iteration body: copy the input onto tape zero, then alternate
the two clean-call modules under the anchored round discipline. -/
private def emitIterBody (Em Gm : FinTM Bool) (hek : 0 < Em.k)
    (ee ex : Em.State) (ge gx : Gm.State) : FinTM Bool where
  k := max Em.k Gm.k
  State := BodyState Em.State Gm.State
  tm := {
    q₀ := .copy
    tr := fun q inp work => match q with
      | .copy => match inp with
        | some s => ⟨.pos,
            fun i => if (i : ℕ) = 0 then (some (some s), 1) else (none, 0),
            none, some .copy⟩
        | none => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0),
            none, some .rwTape⟩
      | .rwTape =>
        match work ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left _ _)⟩ with
        | some _ => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0),
            none, some .rwTape⟩
        | none => ⟨0,
            fun i => if (i : ℕ) = 0 then (none, 1) else (none, 0),
            none, some .rwInput0⟩
      | .rwInput0 => FinTM.controlAction .neg (some .rwInput)
      | .rwInput => match inp with
        | some _ => FinTM.controlAction .neg (some .rwInput)
        | none => FinTM.controlAction .pos (some .anchor)
      | .anchor =>
        padAction (Nat.le_max_left _ _) (Option.map .callE)
          (Em.tm.tr ee inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i)))
      | .callE q =>
        if q = ex then FinTM.controlAction 0 (some .gStart)
        else
          padAction (Nat.le_max_left _ _) (Option.map .callE)
            (Em.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i)))
      | .gStart =>
        padAction (Nat.le_max_right _ _) (Option.map .callG)
          (Gm.tm.tr ge inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i)))
      | .callG q =>
        if q = gx then FinTM.controlAction 0 (some .anchor)
        else
          padAction (Nat.le_max_right _ _) (Option.map .callG)
            (Gm.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i))) }

/-- A pure control transition replaces only the state. -/
private theorem control_step {H : MultiTapeTM k Bool B} {q r : B}
    (h : ∀ inp work, H.tr q inp work = FinTM.controlAction 0 (some r))
    {c : Cfg k Bool B x} (hc : c.state = some q) :
    H.step c = { c with state := some r } := by
  have hs : H.step c = (H.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hc]
  rw [hs, h]
  refine Cfg.ext rfl ?_ ?_ ?_ ?_ <;>
    simp [FinTM.controlAction, Action.apply]

/-- A moving control transition replaces the state and moves the input head. -/
private theorem control_step' {H : MultiTapeTM k Bool B} {q r : B} {mv : SignType}
    (h : ∀ inp work, H.tr q inp work = FinTM.controlAction mv (some r))
    {c : Cfg k Bool B x} (hc : c.state = some q) :
    H.step c = { c with
      state := some r
      inputPos := moveInputPos c.inputPos mv } := by
  have hs : H.step c = (H.tr q c.inputSymbol c.workTapeSymbols).apply c := by
    unfold MultiTapeTM.step
    rw [hc]
  rw [hs, h]
  refine Cfg.ext rfl rfl ?_ ?_ ?_ <;>
    simp [FinTM.controlAction, Action.apply]

section Body

variable (Em Gm : FinTM Bool) (ee ex : Em.State) (ge gx : Gm.State)

/-- Embedding an `Em`-seam into the body gives a body seam: tape zero's word
survives and the padding tapes are blank on both sides. -/
private theorem embed_ofWords_left (hek : 0 < Em.k) (s : List Bool) :
    embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
        (Cfg.ofWords (input := x) ee (stateWord Em.k s)) =
      Cfg.ofWords (BodyState.callE ee) (stateWord (max Em.k Gm.k) s) := by
  rw [embedCfg_ofWords]
  congr 1
  funext i
  by_cases h : (i : ℕ) < Em.k
  · simp [stateWord, h]
  · have h0 : ¬ (i : ℕ) = 0 := fun hz => h (hz ▸ hek)
    simp [stateWord, h, h0]

/-- Embedding a `Gm`-seam into the body gives a body seam, provided `Gm` has
a genuine tape (otherwise tape zero's word would be lost). -/
private theorem embed_ofWords_right (hgk : 0 < Gm.k) (s : List Bool) :
    embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
        (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) =
      Cfg.ofWords (BodyState.callG ge) (stateWord (max Em.k Gm.k) s) := by
  rw [embedCfg_ofWords]
  congr 1
  funext i
  by_cases h : (i : ℕ) < Gm.k
  · simp [stateWord, h]
  · have h0 : ¬ (i : ℕ) = 0 := fun hz => h (hz ▸ hgk)
    simp [stateWord, h, h0]

/-- **The round segment.** From the anchor seam carrying `s`, the body runs
the emit-mode module (emitting `es`), hands control to the install-mode
module (installing `gs`), and returns to the anchor seam, in positive time,
without visiting the anchor strictly inside.
**Proof sketch.** The anchor itself fires the emit module's first action, so
an entry state equal to the exit state still runs; `embed_run` transports the
rest of the emit run, landing at the handoff state with the chunk emitted and
the word preserved.  One control step enters `gStart`, which fires the
install module's first action; the install run is transported likewise, with
the already-emitted chunk commuted past it by `runFrom_output_prefix` (the
install module's own output stays empty along the run, by the append-only
output).  One final control step re-enters the anchor carrying the stepped
word.  The anchor-exclusion clause reads the visited state off the
appropriate phase equality: an injected call state, or a control state,
never the anchor. -/
private theorem body_round (hek : 0 < Em.k) (hgk : 0 < Gm.k) (s es gs : List Bool)
    (tE : ℕ) (htE : 0 < tE)
    (hEfirst : ∀ t', 0 < t' → t' < tE →
      (Em.tm.runFrom (Cfg.ofWords (input := x) ee (stateWord Em.k s)) t').state ≠
        some ex)
    (hErun : Em.tm.runFrom (Cfg.ofWords (input := x) ee (stateWord Em.k s)) tE =
      { Cfg.ofWords ex (stateWord Em.k s) with output := es })
    (tG : ℕ) (htG : 0 < tG)
    (hGfirst : ∀ t', 0 < t' → t' < tG →
      (Gm.tm.runFrom (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) t').state ≠
        some gx)
    (hGrun : Gm.tm.runFrom (Cfg.ofWords (input := x) ge (stateWord Gm.k s)) tG =
      Cfg.ofWords gx (stateWord Gm.k gs)) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.runFrom
        (Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) s))
        (tE + 1 + tG + 1) =
      { Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) gs)
          with output := es } ∧
    ∀ t', 0 < t' → t' < tE + 1 + tG + 1 →
      ((emitIterBody Em Gm hek ee ex ge gx).tm.runFrom
        (Cfg.ofWords (input := x) .anchor (stateWord (max Em.k Gm.k) s))
          t').state ≠ some .anchor := by
  set H := (emitIterBody Em Gm hek ee ex ge gx).tm with hH
  set c₀ : Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
    Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) s) with hc₀
  set subc₀ : Cfg Em.k Bool Em.State x := Cfg.ofWords ee (stateWord Em.k s) with hsubc₀
  set subg₀ : Cfg Gm.k Bool Gm.State x := Cfg.ofWords ge (stateWord Gm.k s) with hsubg₀
  have htrE : ∀ q : Em.State, q ≠ ex → ∀ inp work,
      H.tr (.callE q) inp work =
        padAction (Nat.le_max_left Em.k Gm.k) (Option.map .callE)
          (Em.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_left _ _) i))) := by
    intro q hq inp work
    simp [hH, emitIterBody, hq]
  have htrG : ∀ q : Gm.State, q ≠ gx → ∀ inp work,
      H.tr (.callG q) inp work =
        padAction (Nat.le_max_right Em.k Gm.k) (Option.map .callG)
          (Gm.tm.tr q inp (fun i => work (Fin.castLE (Nat.le_max_right _ _) i))) := by
    intro q hq inp work
    simp [hH, emitIterBody, hq]
  -- the first module step, fired from the anchor
  have hstep₁ : H.step c₀ =
      embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
        (Em.tm.step subc₀) := by
    have h := embed_step (Nat.le_max_left Em.k Gm.k) Em.tm H
      (BodyState.callE (SG := Gm.State)) subc₀ ee rfl .anchor (fun inp work => rfl)
    have hcfg : ({ embedCfg (Nat.le_max_left Em.k Gm.k)
        (BodyState.callE (SG := Gm.State)) subc₀ with
        state := some .anchor } : Cfg (max Em.k Gm.k) Bool _ x) = c₀ := by
      rw [hsubc₀, embed_ofWords_left Em Gm ee hek]
      rfl
    rw [← hcfg]
    exact h
  -- the module chain after the first step
  have hEsome : ∀ j ≤ tE, ∃ q, (Em.tm.runFrom subc₀ j).state = some q := by
    intro j hj
    exact state_isSome_of_runFrom Em.tm (by rw [hErun]; rfl) hj
  have hone : Em.tm.runFrom subc₀ 1 = Em.tm.step subc₀ := by
    simp [MultiTapeTM.runFrom]
  have hEchain : ∀ u ≤ tE - 1,
      H.runFrom c₀ (1 + u) =
        embedCfg (Nat.le_max_left Em.k Gm.k) (BodyState.callE (SG := Gm.State))
          (Em.tm.runFrom subc₀ (1 + u)) := by
    intro u hu
    rw [runFrom_add, runFrom_one, hstep₁]
    rw [embed_run (Nat.le_max_left Em.k Gm.k) Em.tm H
      (BodyState.callE (SG := Gm.State)) ex htrE (Em.tm.step subc₀) u ?hstates]
    · rw [runFrom_add, hone]
    case hstates =>
      intro j hj
      have hj1 : 1 + j ≤ tE := by omega
      obtain ⟨q, hq⟩ := hEsome (1 + j) hj1
      rw [runFrom_add, hone] at hq
      refine ⟨q, hq, ?_⟩
      intro hqex
      subst hqex
      have := hEfirst (1 + j) (by omega) (by omega)
      rw [runFrom_add, hone] at this
      exact this hq
  -- checkpoint A: after tE steps, at the handoff state with the chunk emitted
  have hA : H.runFrom c₀ tE =
      { Cfg.ofWords (BodyState.callE ex) (stateWord (max Em.k Gm.k) s)
          with output := es } := by
    have h := hEchain (tE - 1) le_rfl
    rw [show 1 + (tE - 1) = tE from by omega] at h
    rw [h, hErun]
    rw [embedCfg_output, embed_ofWords_left Em Gm ex hek]
  -- checkpoint B: the control handoff
  have hB : H.runFrom c₀ (tE + 1) =
      { Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s)
          with output := es } := by
    rw [runFrom_add, hA, runFrom_one, control_step (q := BodyState.callE ex) ?_ rfl]
    · rfl
    · intro inp work
      simp [hH, emitIterBody]
  -- the install chain, lifted along the emitted prefix
  have hstep₂ : H.step (Cfg.ofWords (BodyState.gStart (SE := Em.State) (SG := Gm.State))
        (stateWord (max Em.k Gm.k) s)) =
      embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
        (Gm.tm.step subg₀) := by
    have h := embed_step (Nat.le_max_right Em.k Gm.k) Gm.tm H
      (BodyState.callG (SE := Em.State)) subg₀ ge rfl
      (BodyState.gStart (SE := Em.State) (SG := Gm.State)) (fun inp work => rfl)
    have hcfg : ({ embedCfg (Nat.le_max_right Em.k Gm.k)
        (BodyState.callG (SE := Em.State)) subg₀ with
        state := some (BodyState.gStart (SE := Em.State) (SG := Gm.State)) } :
          Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) =
        Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s) := by
      rw [hsubg₀, embed_ofWords_right Em Gm ge hgk]
      rfl
    rw [← hcfg]
    exact h
  have hGsome : ∀ j ≤ tG, ∃ q, (Gm.tm.runFrom subg₀ j).state = some q := by
    intro j hj
    exact state_isSome_of_runFrom Gm.tm (by rw [hGrun]; rfl) hj
  have honeG : Gm.tm.runFrom subg₀ 1 = Gm.tm.step subg₀ := by
    simp [MultiTapeTM.runFrom]
  have hGchain : ∀ u ≤ tG - 1,
      H.runFrom (Cfg.ofWords (BodyState.gStart (SE := Em.State) (SG := Gm.State)) (stateWord (max Em.k Gm.k) s)) (1 + u) =
        embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
          (Gm.tm.runFrom subg₀ (1 + u)) := by
    intro u hu
    rw [runFrom_add, runFrom_one, hstep₂]
    rw [embed_run (Nat.le_max_right Em.k Gm.k) Gm.tm H
      (BodyState.callG (SE := Em.State)) gx htrG (Gm.tm.step subg₀) u ?hstatesG]
    · rw [runFrom_add, honeG]
    case hstatesG =>
      intro j hj
      have hj1 : 1 + j ≤ tG := by omega
      obtain ⟨q, hq⟩ := hGsome (1 + j) hj1
      rw [runFrom_add, honeG] at hq
      refine ⟨q, hq, ?_⟩
      intro hqex
      subst hqex
      have := hGfirst (1 + j) (by omega) (by omega)
      rw [runFrom_add, honeG] at this
      exact this hq
  have hGout : ∀ u ≤ tG, 1 ≤ u →
      H.runFrom c₀ (tE + 1 + u) =
        { embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
            (Gm.tm.runFrom subg₀ u) with output := es } := by
    intro u hu h1u
    rw [show tE + 1 + u = (tE + 1) + u from rfl, runFrom_add, hB]
    have hpre : ({ Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s)
        with output := es } : Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) =
        { (Cfg.ofWords BodyState.gStart (stateWord (max Em.k Gm.k) s) :
            Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x) with
          output := es ++ (Cfg.ofWords (input := x)
            (BodyState.gStart (SE := Em.State) (SG := Gm.State))
            (stateWord (max Em.k Gm.k) s)).output } := by
      simp [Cfg.ofWords]
    have hsubout : (Gm.tm.runFrom subg₀ u).output = [] := by
      obtain ⟨o2, h2⟩ := runFrom_output_extends Gm.tm (Gm.tm.runFrom subg₀ u) (tG - u)
      rw [← runFrom_add, show u + (tG - u) = tG from by omega, hGrun] at h2
      have : ([] : List Bool) = (Gm.tm.runFrom subg₀ u).output ++ o2 := h2
      exact (List.append_eq_nil_iff.mp this.symm).1
    rw [hpre, runFrom_output_prefix]
    obtain ⟨u', rfl⟩ : ∃ u', u = 1 + u' := ⟨u - 1, by omega⟩
    rw [hGchain u' (by omega)]
    rw [show (embedCfg (Nat.le_max_right Em.k Gm.k) (BodyState.callG (SE := Em.State))
      (Gm.tm.runFrom subg₀ (1 + u'))).output = [] from hsubout, List.append_nil]
  -- checkpoint C and the final control return
  have hC : H.runFrom c₀ (tE + 1 + tG) =
      { Cfg.ofWords (BodyState.callG gx) (stateWord (max Em.k Gm.k) gs)
          with output := es } := by
    rw [hGout tG le_rfl (by omega), hGrun, embed_ofWords_right Em Gm gx hgk]
  constructor
  · rw [show tE + 1 + tG + 1 = (tE + 1 + tG) + 1 from rfl, runFrom_add, hC,
      runFrom_one, control_step (q := BodyState.callG gx) ?_ rfl]
    · rfl
    · intro inp work
      simp [hH, emitIterBody]
  · intro t' ht'0 ht'
    rcases lt_trichotomy t' (tE + 1) with hlt | heq | hgt
    · rcases Nat.lt_or_ge t' tE with hltE | hgeE
      · obtain ⟨u, rfl⟩ : ∃ u, t' = 1 + u := ⟨t' - 1, by omega⟩
        rw [hEchain u (by omega)]
        obtain ⟨q, hq⟩ := hEsome (1 + u) (by omega)
        simp [embedCfg, hq]
      · have he : t' = tE := by omega
        subst he
        rw [hA]
        simp [Cfg.ofWords]
    · subst heq
      rw [hB]
      simp [Cfg.ofWords]
    · obtain ⟨u, rfl⟩ : ∃ u, t' = tE + 1 + u := ⟨t' - (tE + 1), by omega⟩
      rw [hGout u (by omega) (by omega)]
      obtain ⟨q, hq⟩ := hGsome u (by omega)
      simp [embedCfg, hq]

/-! #### The startup copier -/

/-- The copy-phase configuration: the first `i` input symbols already written
on tape zero, both heads past them. -/
private def copyCfg (x : List Bool) (i : ℕ) (hi : i ≤ x.length) :
    Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
  ⟨some .copy, ⟨i + 1, by omega⟩,
    fun j => if (j : ℕ) = 0 then FinTM.bufferTape (x.take i) else fun _ => none,
    fun j => if (j : ℕ) = 0 then (i : ℤ) else 0, []⟩

/-- A rewind-phase configuration: the whole input on tape zero, the input
head at `p`, the tape-zero head at `z`. -/
private def fullCfg (x : List Bool) (st : BodyState Em.State Gm.State)
    (p : ℕ) (hp : p < x.length + 2) (z : ℤ) :
    Cfg (max Em.k Gm.k) Bool (BodyState Em.State Gm.State) x :=
  ⟨some st, ⟨p, hp⟩,
    fun j => if (j : ℕ) = 0 then FinTM.bufferTape x else fun _ => none,
    fun j => if (j : ℕ) = 0 then z else 0, []⟩

/-- The body's initial configuration is the empty copy configuration. -/
private theorem initCfg_eq_copyCfg (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.initCfg x =
      copyCfg Em Gm x 0 (Nat.zero_le _) := by
  refine Cfg.ext rfl (Fin.ext (by simp [copyCfg])) ?_ ?_ rfl
  · funext j
    by_cases hj : (j : ℕ) = 0 <;>
      simp [copyCfg, emitIterBody, hj, MultiTapeTM.initCfg, Cfg.init]
  · funext j
    by_cases hj : (j : ℕ) = 0 <;>
      simp [copyCfg, emitIterBody, hj, MultiTapeTM.initCfg, Cfg.init]

/-- One copy step: read the next input symbol, write it, advance both heads.
**Proof sketch.** The input symbol under the head is the `i`-th input bit;
the applied action writes it at tape-zero cell `i` (`bufferTape_append`
extends the copied prefix) and moves both heads right. -/
private theorem copy_step (hek : 0 < Em.k) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x i (le_of_lt hi)) =
      copyCfg Em Gm x (i + 1) hi := by
  have hinp : (copyCfg Em Gm x i (le_of_lt hi)).inputSymbol = some x[i] :=
    inputSymbolInner i (by simp only [copyCfg]; omega) hi
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x i (le_of_lt hi)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .copy
        (copyCfg Em Gm x i (le_of_lt hi)).inputSymbol
        (copyCfg Em Gm x i (le_of_lt hi)).workTapeSymbols).apply
        (copyCfg Em Gm x i (le_of_lt hi)) := rfl
  rw [h1, hinp]
  have htake : x.take (i + 1) = x.take i ++ [x[i]] := by
    rw [List.take_succ, List.getElem?_eq_getElem hi]
    rfl
  have hlen : ((x.take i).length : ℤ) = (i : ℤ) := by
    simp [List.length_take, Nat.min_eq_left (le_of_lt hi)]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos = _
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    rfl
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, hj, if_pos]
      rw [htake, FinTM.bufferTape_append, hlen]
    · simp [emitIterBody, Action.apply, copyCfg, hj]
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, hj, if_pos]
      simp only [SignType.coe_one]
      omega
    · simp [emitIterBody, Action.apply, copyCfg, hj]

/-- The copy phase ends at the right input boundary and starts the tape
rewind.
**Proof sketch.** At the right boundary the input read is blank, so the
copy state's other branch fires: the input head stays, tape zero (now
holding the whole input, `List.take_length`) steps left. -/
private theorem copy_end (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x x.length le_rfl) =
      fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((x.length : ℤ) - 1) := by
  have hinp : (copyCfg Em Gm x x.length le_rfl).inputSymbol = none := by
    have h := FinTM.inputSymbol_at (copyCfg Em Gm x x.length le_rfl) x.length le_rfl
      (by simp [copyCfg])
    simpa using h
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step (copyCfg Em Gm x x.length le_rfl) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .copy
        (copyCfg Em Gm x x.length le_rfl).inputSymbol
        (copyCfg Em Gm x x.length le_rfl).workTapeSymbols).apply
        (copyCfg Em Gm x x.length le_rfl) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, fullCfg, hj, if_pos]
      rw [List.take_length]
    · simp [emitIterBody, Action.apply, copyCfg, fullCfg, hj]
  · funext j
    by_cases hj : (j : ℕ) = 0
    · simp only [emitIterBody, Action.apply, copyCfg, fullCfg, hj, if_pos,
        SignType.neg_eq_neg_one, SignType.coe_neg_one]
      omega
    · simp [emitIterBody, Action.apply, copyCfg, fullCfg, hj]

/-- One tape-rewind step over a written cell.
**Proof sketch.** The tape-zero read at cell `j` is the `j`-th copied bit,
so the rewind state keeps moving left; only the head position changes. -/
private theorem rwTape_some (hek : 0 < Em.k) (x : List Bool) (j : ℕ) (hj : j < x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) =
      fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((j : ℤ) - 1) := by
  have hw : (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols
      ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left Em.k Gm.k)⟩ = some x[j] := by
    simp only [fullCfg, Cfg.workTapeSymbols]
    simp [List.getElem?_eq_getElem hj]
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).inputSymbol
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols).apply
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)) := rfl
  have htr : (emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).inputSymbol
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (j : ℤ)).workTapeSymbols =
      ⟨0, fun i => if (i : ℕ) = 0 then (none, -1) else (none, 0), none, some .rwTape⟩ := by
    simp only [emitIterBody]
    rw [hw]
  rw [h1, htr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;> simp [Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp only [Action.apply, fullCfg, hi, if_pos, SignType.neg_eq_neg_one,
        SignType.coe_neg_one]
      omega
    · simp [Action.apply, fullCfg, hi]

/-- The tape rewind reaches the left blank and turns the head back to the
origin.
**Proof sketch.** Cell `-1` is blank (`bufferTape_left`), so the rewind
state's blank branch fires: the head steps right to the origin and control
moves to the input rewind. -/
private theorem rwTape_none (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) =
      fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0 := by
  have hw : (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols
      ⟨0, Nat.lt_of_lt_of_le hek (Nat.le_max_left Em.k Gm.k)⟩ = none := by
    simp only [fullCfg, Cfg.workTapeSymbols]
    simp
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).inputSymbol
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols).apply
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)) := rfl
  have htr : (emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwTape
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).inputSymbol
      (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) (-1)).workTapeSymbols =
      ⟨0, fun i => if (i : ℕ) = 0 then (none, 1) else (none, 0), none, some .rwInput0⟩ := by
    simp only [emitIterBody]
    rw [hw]
  rw [h1, htr]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) 0 = _
    rw [moveInputPos_zero]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;> simp [Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp only [Action.apply, fullCfg, hi, if_pos, SignType.coe_one]
      omega
    · simp [Action.apply, fullCfg, hi]

/-- The input rewind's unconditional first move. -/
private theorem rwIn0_step (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0) =
      fullCfg Em Gm x .rwInput x.length (by omega) 0 := by
  rw [control_step' (mv := .neg) (r := BodyState.rwInput) (fun _ _ => rfl) rfl]
  refine Cfg.ext rfl ?_ rfl rfl rfl
  show moveInputPos (⟨x.length + 1, by omega⟩ : Fin (x.length + 2)) .neg = _
  rw [moveInputPos_neg_of_ne_left _ (by
    intro h
    have := congrArg Fin.val h
    simp at this)]
  rfl

/-- One input-rewind step over an input symbol.
**Proof sketch.** At interior position `p ≥ 1` the input read is the
`(p-1)`-st bit, so the rewind keeps moving left
(`moveInputPos_neg_of_ne_left`); nothing else changes. -/
private theorem rwInput_some (hek : 0 < Em.k) (x : List Bool) (p : ℕ)
    (hp1 : 1 ≤ p) (hpn : p ≤ x.length) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput p (by omega) 0) =
      fullCfg Em Gm x .rwInput (p - 1) (by omega) 0 := by
  have hinp : (fullCfg Em Gm x .rwInput p (by omega) 0).inputSymbol = some x[p - 1] :=
    inputSymbolInner (p - 1) (by simp only [fullCfg]; omega) (by omega)
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwInput p (by omega) 0) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwInput
        (fullCfg Em Gm x .rwInput p (by omega) 0).inputSymbol
        (fullCfg Em Gm x .rwInput p (by omega) 0).workTapeSymbols).apply
        (fullCfg Em Gm x .rwInput p (by omega) 0) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨p, by omega⟩ : Fin (x.length + 2)) .neg = _
    rw [moveInputPos_neg_of_ne_left _ (by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega)]
    rfl
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, hi]

/-- The input rewind reaches the left boundary and enters the anchor seam.
**Proof sketch.** At position zero the input read is blank, so the final
branch fires: the head steps right to the canonical position one and control
enters the anchor; the resulting configuration is literally the
`Cfg.ofWords` seam carrying the copied input on tape zero. -/
private theorem rwInput_zero (hek : 0 < Em.k) (x : List Bool) :
    (emitIterBody Em Gm hek ee ex ge gx).tm.step
        (fullCfg Em Gm x .rwInput 0 (by omega) 0) =
      Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x) := by
  have hinp : (fullCfg Em Gm x .rwInput 0 (by omega) 0).inputSymbol = none := by
    simp only [fullCfg, Cfg.inputSymbol]
    rw [dif_pos (by apply Fin.ext; simp)]
  have h1 : (emitIterBody Em Gm hek ee ex ge gx).tm.step
      (fullCfg Em Gm x .rwInput 0 (by omega) 0) =
      ((emitIterBody Em Gm hek ee ex ge gx).tm.tr .rwInput
        (fullCfg Em Gm x .rwInput 0 (by omega) 0).inputSymbol
        (fullCfg Em Gm x .rwInput 0 (by omega) 0).workTapeSymbols).apply
        (fullCfg Em Gm x .rwInput 0 (by omega) 0) := rfl
  rw [h1, hinp]
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · show moveInputPos (⟨0, by omega⟩ : Fin (x.length + 2)) .pos = _
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    apply Fin.ext
    simp [Cfg.ofWords]
  · funext i
    by_cases hi : (i : ℕ) = 0
    · simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords,
        stateWord, hi]
    · simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords,
        stateWord, hi]
  · funext i
    by_cases hi : (i : ℕ) = 0 <;>
      simp [emitIterBody, FinTM.controlAction, Action.apply, fullCfg, Cfg.ofWords, hi]

/-- **The startup segment.** From its initial configuration the body copies
the input onto tape zero, rewinds both heads, and enters the anchor seam
carrying the input, within `3·|x| + 4` steps and without visiting the anchor
earlier.
**Proof sketch.** Chain the safe runs of the four phases: `|x|` copy steps,
the boundary turnaround, `|x| + 1` tape-rewind steps, the unconditional
input-rewind entry, and `|x| + 1` input-rewind steps, each phase by
induction on its counter; every visited state is a copier state, never the
anchor. -/
private theorem body_start (hek : 0 < Em.k) :
    SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
      ((emitIterBody Em Gm hek ee ex ge gx).tm.initCfg x) (3 * x.length + 4)
      (Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x)) := by
  have hcopy : ∀ i (hi : i ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (copyCfg Em Gm x 0 (Nat.zero_le _)) i (copyCfg Em Gm x i hi) := by
    intro i
    induction i with
    | zero => intro _; exact SafeRun.zero
    | succ i ih =>
      intro hi
      exact SafeRun.trans (ih (by omega))
        (SafeRun.cons (copy_step Em Gm ee ex ge gx hek x i (by omega))
          (by simp [copyCfg]) SafeRun.zero)
  have hrwt : ∀ j (hj : j ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (fullCfg Em Gm x .rwTape (x.length + 1) (by omega) ((j : ℤ) - 1)) (j + 1)
        (fullCfg Em Gm x .rwInput0 (x.length + 1) (by omega) 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 from by omega]
      exact SafeRun.cons (rwTape_none Em Gm ee ex ge gx hek x) (by simp [fullCfg])
        SafeRun.zero
    | succ j ih =>
      intro hj
      rw [show ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) from by push_cast; ring]
      exact SafeRun.cons (rwTape_some Em Gm ee ex ge gx hek x j (by omega))
        (by simp [fullCfg]) (ih (by omega))
  have hrwi : ∀ p (hp : p ≤ x.length),
      SafeRun (emitIterBody Em Gm hek ee ex ge gx).tm .anchor
        (fullCfg Em Gm x .rwInput p (by omega) 0) (p + 1)
        (Cfg.ofWords .anchor (stateWord (max Em.k Gm.k) x)) := by
    intro p
    induction p with
    | zero =>
      intro _
      exact SafeRun.cons (rwInput_zero Em Gm ee ex ge gx hek x) (by simp [fullCfg])
        SafeRun.zero
    | succ p ih =>
      intro hp
      exact SafeRun.cons (rwInput_some Em Gm ee ex ge gx hek x (p + 1) (by omega) hp)
        (by simp [fullCfg]) (ih (by omega))
  have hchain := ((((hcopy x.length le_rfl).trans
    (SafeRun.cons (copy_end Em Gm ee ex ge gx hek x) (by simp [copyCfg]) SafeRun.zero)).trans
    (hrwt x.length le_rfl)).trans
    (SafeRun.cons (rwIn0_step Em Gm ee ex ge gx hek x) (by simp [fullCfg]) SafeRun.zero)).trans
    (hrwi x.length le_rfl)
  rw [initCfg_eq_copyCfg]
  rw [show 3 * x.length + 4 =
    x.length + (0 + 1) + (x.length + 1) + (0 + 1) + (x.length + 1) from by omega]
  exact hchain

end Body

/-- **The emit-iteration machine** ([AB09] §7.3–§7.4 folklore: simulate a
machine on polynomially many rounds and concatenate the outcomes).  Given
machines computing the step `g` and the chunk `e` within polynomial budgets,
and a polynomial length envelope for the orbit of `g`, one finite machine
computes the concatenation of the chunks `e (g^[i] w)` for
`i = 0, …, a'·(|w|+1)^k'`, within a polynomial budget in the `C·(n+1)^c`
normal form.

**Proof sketch.** Instantiate `Turing.FinTM.exists_emitLoopTM` at the body
machine `emitIterBody` built from the two clean-call modules
(`exists_emitCallTM` for `e`, `exists_installCallTM` for `g`), the
polynomial-bits fuel machine (`computesFunInTime_polyBits`), the orbit
invariant `∃ i, s = g^[i] w`, and the budget `T` summing the fuel, startup,
and round envelopes; `body_start` and `body_round` discharge the startup and
round obligations, with the call budgets bounded through the orbit envelope
and the one-symbol-per-step output bound.  The loop host's
`c·(T+1)·(R+2)` budget is then absorbed into the polynomial normal form. -/
theorem FinTM.exists_emitIterTM (G E : FinTM Bool) (g e : List Bool → List Bool)
    (CG cG CE cE : ℕ)
    (hG : G.ComputesFunInTime g (fun n => CG * (n + 1) ^ cG))
    (hE : E.ComputesFunInTime e (fun n => CE * (n + 1) ^ cE))
    (a' k' b l : ℕ)
    (horbit : ∀ (w : List Bool) (i : ℕ), (g^[i] w).length ≤ b * (w.length + 1) ^ l) :
    ∃ (M : FinTM Bool) (C c : ℕ),
      M.ComputesFunInTime
        (fun w => (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap
          (fun i => e (g^[i] w)))
        (fun n => C * (n + 1) ^ c) := by
  classical
  obtain ⟨Ce, eentry, eexit, cEcall, hke, hEcall⟩ :=
    FinTM.exists_emitCallTM E e _ hE
  obtain ⟨Cg, gentry, gexit, cGcall, hkg, hGcall⟩ :=
    FinTM.exists_installCallTM G g _ hG
  obtain ⟨F, cF, hF⟩ := FinTM.computesFunInTime_polyBits a' k'
  -- output-length bounds from the one-symbol-per-step discipline
  have hElen : ∀ s : List Bool, (e s).length ≤ CE * (s.length + 1) ^ cE := by
    intro s
    have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hE s)).2
    simpa only [hout] using E.tm.output_length_le s (CE * (s.length + 1) ^ cE)
  have hGlen : ∀ s : List Bool, (g s).length ≤ CG * (s.length + 1) ^ cG := by
    intro s
    have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hG s)).2
    simpa only [hout] using G.tm.output_length_le s (CG * (s.length + 1) ^ cG)
  -- the budget
  set L : ℕ → ℕ := fun n => b * (n + 1) ^ l with hL
  set TEb : ℕ → ℕ := fun n => CE * (L n + 1) ^ cE with hTEb
  set TGb : ℕ → ℕ := fun n => CG * (L n + 1) ^ cG with hTGb
  set T : ℕ → ℕ := fun n => cF * (n + 1) ^ (k' + 1) + (3 * n + 4) +
    (cEcall * (2 * TEb n + L n + 1) + cGcall * (2 * TGb n + L n + 1) + 2) with hT
  set body := emitIterBody Ce Cg hke eentry eexit gentry gexit with hbody
  have hF' : F.ComputesFunInTime
      (fun x => Nat.bits (a' * (x.length + 1) ^ k')) T := by
    intro x
    refine (hF x).mono ?_
    simp only [hT]
    omega
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ t' < t, (body.tm.runFrom (body.tm.initCfg x) t').state ≠
        some BodyState.anchor) ∧
      body.tm.runFrom (body.tm.initCfg x) t =
        Cfg.ofWords .anchor (stateWord body.k x) := by
    intro x
    obtain ⟨hrun, hsafe⟩ := body_start Ce Cg eentry eexit gentry gexit hke (x := x)
    exact ⟨3 * x.length + 4, by simp only [hT]; omega, hsafe, hrun⟩
  have hround : ∀ (x s : List Bool), (∃ i, s = g^[i] x) →
      ∃ t, 0 < t ∧ t ≤ T x.length ∧
        (∀ t', 0 < t' → t' < t →
          (body.tm.runFrom
            (Cfg.ofWords (input := x) .anchor (stateWord body.k s)) t').state ≠
              some BodyState.anchor) ∧
        body.tm.runFrom
          (Cfg.ofWords (input := x) .anchor (stateWord body.k s)) t =
            { Cfg.ofWords .anchor (stateWord body.k (g s)) with output := e s } := by
    rintro x s ⟨i, rfl⟩
    set s := g^[i] x with hs
    have hsL : s.length ≤ L x.length := horbit x i
    obtain ⟨tEc, htEb', htEpos, hEfirst, hErun⟩ := hEcall x s
    obtain ⟨tGc, htGb', htGpos, hGfirst, hGrun⟩ := hGcall x s
    obtain ⟨hrun, hsafe⟩ := body_round Ce Cg eentry eexit gentry gexit hke hkg
      (x := x) s (e s) (g s) tEc htEpos hEfirst hErun tGc htGpos hGfirst hGrun
    refine ⟨tEc + 1 + tGc + 1, by omega, ?_, hsafe, hrun⟩
    have hpow : s.length + 1 ≤ L x.length + 1 := by omega
    have hTEs : CE * (s.length + 1) ^ cE ≤ TEb x.length :=
      Nat.mul_le_mul_left CE (Nat.pow_le_pow_left hpow cE)
    have hTGs : CG * (s.length + 1) ^ cG ≤ TGb x.length :=
      Nat.mul_le_mul_left CG (Nat.pow_le_pow_left hpow cG)
    have hes := hElen s
    have hgs := hGlen s
    have htE2 : tEc ≤ cEcall * (2 * TEb x.length + L x.length + 1) :=
      le_trans htEb' (Nat.mul_le_mul_left cEcall (by omega))
    have htG2 : tGc ≤ cGcall * (2 * TGb x.length + L x.length + 1) :=
      le_trans htGb' (Nat.mul_le_mul_left cGcall (by omega))
    simp only [hT]
    omega
  obtain ⟨M, c, hM⟩ := FinTM.exists_emitLoopTM body F .anchor
    (fun w s => ∃ i, s = g^[i] w) (fun _ s => g s) (fun _ s => e s)
    (fun w => w) (fun n => a' * (n + 1) ^ k') T hF'
    (fun w => ⟨0, rfl⟩)
    (fun w s hs => by
      obtain ⟨i, rfl⟩ := hs
      exact ⟨i + 1, (Function.iterate_succ_apply' g i w).symm⟩)
    hstart hround
  -- polynomial normal form
  set D : ℕ := k' + 1 + l * cE + l * cG + l + 1 with hD
  have honeD : ∀ n : ℕ, 1 ≤ (n + 1) ^ D := fun n => Nat.one_le_pow _ _ (by omega)
  have hTle : ∀ n, T n ≤
      (cF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
        cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2) * (n + 1) ^ D := by
    intro n
    have hone : 1 ≤ (n + 1) ^ l := Nat.one_le_pow _ _ (by omega)
    have hLb : L n + 1 ≤ (b + 1) * (n + 1) ^ l := by
      simp only [hL]
      calc b * (n + 1) ^ l + 1 ≤ b * (n + 1) ^ l + (n + 1) ^ l := by omega
        _ = (b + 1) * (n + 1) ^ l := by ring
    have hpowD : ∀ a : ℕ, a ≤ D → (n + 1) ^ a ≤ (n + 1) ^ D :=
      fun a ha => Nat.pow_le_pow_right (by omega) ha
    have hTEbn : TEb n ≤ CE * (b + 1) ^ cE * (n + 1) ^ (l * cE) := by
      simp only [hTEb]
      calc CE * (L n + 1) ^ cE ≤ CE * ((b + 1) * (n + 1) ^ l) ^ cE :=
            Nat.mul_le_mul_left CE (Nat.pow_le_pow_left hLb cE)
        _ = CE * (b + 1) ^ cE * (n + 1) ^ (l * cE) := by
            rw [mul_pow, ← pow_mul]
            ring
    have hTGbn : TGb n ≤ CG * (b + 1) ^ cG * (n + 1) ^ (l * cG) := by
      simp only [hTGb]
      calc CG * (L n + 1) ^ cG ≤ CG * ((b + 1) * (n + 1) ^ l) ^ cG :=
            Nat.mul_le_mul_left CG (Nat.pow_le_pow_left hLb cG)
        _ = CG * (b + 1) ^ cG * (n + 1) ^ (l * cG) := by
            rw [mul_pow, ← pow_mul]
            ring
    have h1 : cF * (n + 1) ^ (k' + 1) ≤ cF * (n + 1) ^ D :=
      Nat.mul_le_mul_left cF (hpowD _ (by omega))
    have h2 : 3 * n + 4 ≤ 4 * (n + 1) ^ D := by
      have : n + 1 ≤ (n + 1) ^ D := le_trans (by omega)
        (Nat.le_self_pow (by omega) (n + 1))
      omega
    have h3 : TEb n ≤ CE * (b + 1) ^ cE * (n + 1) ^ D :=
      le_trans hTEbn (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have h4 : TGb n ≤ CG * (b + 1) ^ cG * (n + 1) ^ D :=
      le_trans hTGbn (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have h5 : L n + 1 ≤ (b + 1) * (n + 1) ^ D :=
      le_trans hLb (Nat.mul_le_mul_left _ (hpowD _ (by omega)))
    have hE3 : cEcall * (2 * TEb n + L n + 1) ≤
        cEcall * (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D := by
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left cEcall ?_
      calc 2 * TEb n + L n + 1 ≤
            2 * (CE * (b + 1) ^ cE * (n + 1) ^ D) + (b + 1) * (n + 1) ^ D +
              (n + 1) ^ D := by
            have := honeD n
            omega
        _ = (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D := by ring
    have hG3 : cGcall * (2 * TGb n + L n + 1) ≤
        cGcall * (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D := by
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left cGcall ?_
      calc 2 * TGb n + L n + 1 ≤
            2 * (CG * (b + 1) ^ cG * (n + 1) ^ D) + (b + 1) * (n + 1) ^ D +
              (n + 1) ^ D := by
            have := honeD n
            omega
        _ = (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D := by ring
    have h6 : 2 ≤ 2 * (n + 1) ^ D := by
      have := honeD n
      omega
    simp only [hT]
    calc cF * (n + 1) ^ (k' + 1) + (3 * n + 4) +
          (cEcall * (2 * TEb n + L n + 1) + cGcall * (2 * TGb n + L n + 1) + 2) ≤
        cF * (n + 1) ^ D + 4 * (n + 1) ^ D +
          (cEcall * (2 * CE * (b + 1) ^ cE + b + 2) * (n + 1) ^ D +
            cGcall * (2 * CG * (b + 1) ^ cG + b + 2) * (n + 1) ^ D +
            2 * (n + 1) ^ D) :=
          Nat.add_le_add (Nat.add_le_add h1 h2)
            (Nat.add_le_add (Nat.add_le_add hE3 hG3) h6)
      _ = (cF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
            cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2) * (n + 1) ^ D := by ring
  set K₀ : ℕ := cF + 4 + cEcall * (2 * CE * (b + 1) ^ cE + b + 2) +
    cGcall * (2 * CG * (b + 1) ^ cG + b + 2) + 2 with hK₀
  refine ⟨M, c * (K₀ + 1) * (a' + 2), D + k', fun w => ?_⟩
  have hMw := hM w
  refine hMw.mono ?_
  set n := w.length
  have hT1 : T n + 1 ≤ (K₀ + 1) * (n + 1) ^ D := by
    have h := hTle n
    have h1 := honeD n
    calc T n + 1 ≤ K₀ * (n + 1) ^ D + (n + 1) ^ D := by omega
      _ = (K₀ + 1) * (n + 1) ^ D := by ring
  have hR2 : a' * (n + 1) ^ k' + 2 ≤ (a' + 2) * (n + 1) ^ k' := by
    have h1 : 1 ≤ (n + 1) ^ k' := Nat.one_le_pow _ _ (by omega)
    calc a' * (n + 1) ^ k' + 2 ≤ a' * (n + 1) ^ k' + 2 * (n + 1) ^ k' := by omega
      _ = (a' + 2) * (n + 1) ^ k' := by ring
  calc c * (T n + 1) * (a' * (n + 1) ^ k' + 2) ≤
        c * ((K₀ + 1) * (n + 1) ^ D) * ((a' + 2) * (n + 1) ^ k') :=
      Nat.mul_le_mul (Nat.mul_le_mul_left c hT1) hR2
    _ = c * (K₀ + 1) * (a' + 2) * (n + 1) ^ (D + k') := by
      rw [pow_add]
      ring

end Turing
```

## ===== TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.ClassNP.CounterProgPolyTime
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassNP.PolyTimePrefix
import TCSlib.Complexity.TuringMachine.CounterProgInput
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.TuringMachine.Build.EmitIterBody

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bounded block-query loop

The chapter-neutral composition primitive behind "run a `P`-decider on
polynomially many fixed-size blocks of the input and aggregate the answers":
the folklore closure of polynomial time under polynomial repetition, used
tacitly throughout [AB09] (§7.3, proof of Theorem 7.8; §7.4.1, repeated
trials; proofs of Theorems 7.17 and 7.18).

Everything here lives at the level of `Complexity.PolyTimeComputable`; the
`P`-closure corollaries (`Complexity.mem_P_of_blockAny` and friends) are
stated in `TCSlib.Complexity.ClassNP.PClosure`, which imports this file.

## Main definitions

* `Complexity.sliceTakeAt` / `Complexity.sliceDropAt` — keep the first
  component and take/drop a polynomial-length prefix of the second.
* `Complexity.xorD` — truncating bitwise XOR of the two components of a pair.

## Main results

* `Complexity.polyTimeComputable_emitIter` — the machine-level loop: iterating
  a polynomial-time step function a polynomial number of times, concatenating
  a polynomial-time chunk of each iterate, is polynomial-time, provided the
  iterates stay inside a polynomial length envelope.  This is the one genuinely
  new combinator; it is built on `Turing.FinTM.exists_emitLoopTM` with
  clean-call modules (`Turing.FinTM.exists_installCallTM` /
  `exists_emitCallTM`) as the per-round body.
* `Complexity.polyTimeComputable_xorD` — truncating bitwise XOR is
  polynomial-time (a one-pass counter program).
* The aggregated one-bit block tests live in
  `TCSlib.Complexity.ClassNP.PolyTimeBlockTests`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.3, Theorem 7.8; §7.4.1; Theorems
  7.17–7.18: the implicit "simulate the machine on each block" closures.)
-/

namespace Complexity

open Turing

/-! ### Slicing the second component at a polynomial schedule

The `Randomized`-layer `sliceTake`/`sliceDrop` of
`TCSlib.Complexity.Randomized.PolyTimeModel` are instances of the following
chapter-neutral forms (stated here, below the `Randomized` layer, so that the
block loop can be shared with the Chapter 3–4 development). -/

/-- Keep the first component of a pair and the first `a·(n+1)^k` symbols of its
second component, where `n` is the first component's length: on
`Turing.pairEncode x r` it returns `Turing.pairEncode x (r.take (a·(|x|+1)^k))`. -/
def sliceTakeAt (a k : ℕ) (z : List Bool) : List Bool :=
  pairEncode (pairFstD z) ((pairSndD z).take (a * ((pairFstD z).length + 1) ^ k))

/-- Keep the first component of a pair and drop the first `a·(n+1)^k` symbols of
its second component: on `Turing.pairEncode x r` it returns
`Turing.pairEncode x (r.drop (a·(|x|+1)^k))`. -/
def sliceDropAt (a k : ℕ) (z : List Bool) : List Bool :=
  pairEncode (pairFstD z) ((pairSndD z).drop (a * ((pairFstD z).length + 1) ^ k))

/-- `sliceTakeAt a k` is polynomial-time computable.
**Proof sketch.** `a·(n+1)^k` is available as a unary string via
`Complexity.polyTimeComputable_polyUnary`; pair it with the second component and
apply the length-gated prefix primitive
`Complexity.polyTimeComputable_takePrefixByLength`, so no in-machine
exponentiation is needed. -/
theorem polyTimeComputable_sliceTakeAt (a k : ℕ) :
    PolyTimeComputable (sliceTakeAt a k) := by
  have hu : PolyTimeComputable
      (fun z => List.replicate (a * ((pairFstD z).length + 1) ^ k) true) :=
    (polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD
  have henc : PolyTimeComputable (fun z => pairEncode
      (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) :=
    PolyTimeComputable.pairEncode hu polyTimeComputable_pairSndD
  have hg : PolyTimeComputable
      (fun z => (pairSndD z).take (a * ((pairFstD z).length + 1) ^ k)) := by
    have heq : (fun z => (pairSndD z).take (a * ((pairFstD z).length + 1) ^ k)) =
        PrefixByLength.take ∘ (fun z => pairEncode
          (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) := by
      funext z
      simp only [Function.comp, PrefixByLength.take, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
    rw [heq]
    exact polyTimeComputable_takePrefixByLength.comp henc
  exact PolyTimeComputable.pairEncode polyTimeComputable_pairFstD hg

/-- `sliceDropAt a k` is polynomial-time computable.
**Proof sketch.** As `sliceTakeAt`, with
`Complexity.polyTimeComputable_dropPrefixByLength` in place of the take
primitive. -/
theorem polyTimeComputable_sliceDropAt (a k : ℕ) :
    PolyTimeComputable (sliceDropAt a k) := by
  have hu : PolyTimeComputable
      (fun z => List.replicate (a * ((pairFstD z).length + 1) ^ k) true) :=
    (polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD
  have henc : PolyTimeComputable (fun z => pairEncode
      (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) :=
    PolyTimeComputable.pairEncode hu polyTimeComputable_pairSndD
  have hg : PolyTimeComputable
      (fun z => (pairSndD z).drop (a * ((pairFstD z).length + 1) ^ k)) := by
    have heq : (fun z => (pairSndD z).drop (a * ((pairFstD z).length + 1) ^ k)) =
        PrefixByLength.drop ∘ (fun z => pairEncode
          (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) := by
      funext z
      simp only [Function.comp, PrefixByLength.drop, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
    rw [heq]
    exact polyTimeComputable_dropPrefixByLength.comp henc
  exact PolyTimeComputable.pairEncode polyTimeComputable_pairFstD hg

/-! ### Small Boolean and list helpers -/

/-- Removing the head symbol is polynomial-time computable.
**Proof sketch.** `w.drop 1` is the length-gated drop
`Complexity.PrefixByLength.drop` applied to `Turing.pairEncode [true] w`. -/
theorem polyTimeComputable_tail : PolyTimeComputable (fun w => w.drop 1) := by
  have henc : PolyTimeComputable (fun w => pairEncode [true] w) :=
    (polyTimeComputable_const [true]).pairEncode polyTimeComputable_id
  have heq : (fun w : List Bool => w.drop 1) =
      PrefixByLength.drop ∘ (fun w => pairEncode [true] w) := by
    funext w
    simp [Function.comp, PrefixByLength.drop]
  rw [heq]
  exact polyTimeComputable_dropPrefixByLength.comp henc

/-- The emptiness test is polynomial-time computable (as a one-bit output).
**Proof sketch.** `w = []` iff `|w| ≤ |[]|`, the pair length test
`Complexity.polyTimeComputable_lenLe` at `Turing.pairEncode [] w`. -/
theorem polyTimeComputable_isNil :
    PolyTimeComputable (fun w => [decide (w = [])]) := by
  have henc : PolyTimeComputable (fun w => pairEncode [] w) :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  have h := polyTimeComputable_lenLe.comp henc
  convert h using 1
  funext w
  simp only [Function.comp, pairFstD_pairEncode, pairSndD_pairEncode, List.length_nil,
    Nat.le_zero, List.length_eq_zero_iff]

/-- Polynomial-time Boolean disjunction of two one-bit tests. -/
theorem polyTimeComputable_or {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x || q x]) := by
  convert polyTimeComputable_ite hp (polyTimeComputable_const [true]) hq using 1
  funext x
  cases p x <;> rfl

/-- Polynomial-time Boolean negation of a one-bit test. -/
theorem polyTimeComputable_not {p : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) :
    PolyTimeComputable (fun x => [!p x]) := by
  convert polyTimeComputable_ite hp (polyTimeComputable_const [false])
    (polyTimeComputable_const [true]) using 1
  funext x
  cases p x <;> rfl

/-- The first projection of the empty word. -/
theorem pairFstD_nil : pairFstD ([] : List Bool) = [] := rfl

/-- The second component of a pair is shorter than the pair. -/
theorem length_pairSndD_le (z : List Bool) : (pairSndD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairSndD, h]
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z p u h
    rw [hz, pairSndD_pairEncode, length_pairEncode]
    omega

/-- A word with a nonempty first projection is a genuine pair. -/
theorem eq_pairEncode_of_pairFstD_ne {z : List Bool} (h : pairFstD z ≠ []) :
    z = pairEncode (pairFstD z) (pairSndD z) := by
  cases hd : pairDecode z with
  | none => exact absurd (by simp [pairFstD, hd]) h
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z p u hd
    rw [hz, pairFstD_pairEncode, pairSndD_pairEncode]

/-- Both projections of a word fit inside it, jointly and doubled. -/
theorem length_pair_components_le (y : List Bool) :
    2 * (pairFstD y).length + (pairSndD y).length ≤ y.length := by
  cases hd : pairDecode y with
  | none =>
    have hf : pairFstD y = [] := by simp [pairFstD, hd]
    have hs : pairSndD y = [] := by simp [pairSndD, hd]
    simp [hf, hs]
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode y p u hd
    conv_rhs => rw [hz]
    rw [length_pairEncode, hz, pairFstD_pairEncode, pairSndD_pairEncode]
    omega

/-- Dropping a slice never grows a word beyond `max` with the constant pair. -/
theorem length_sliceDropAt_le (a k : ℕ) (z : List Bool) :
    (sliceDropAt a k z).length ≤ max z.length 2 := by
  cases h : pairDecode z with
  | none =>
    have h1 : pairFstD z = [] := by simp [pairFstD, h]
    have h2 : pairSndD z = [] := by simp [pairSndD, h]
    refine le_trans ?_ (le_max_right _ _)
    simp [sliceDropAt, h1, h2, length_pairEncode]
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z p u h
    refine le_trans ?_ (le_max_left _ _)
    rw [hz]
    simp only [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_drop]
    omega

/-- A range-indexed concatenation with a single live chunk is that chunk. -/
theorem flatMap_range_eq_single {c : ℕ → List Bool} {N K : ℕ} {b : List Bool}
    (hKN : K < N) (hc : ∀ i < N, c i = if i = K then b else []) :
    (List.range N).flatMap c = b := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hNK : N = K
    · subst hNK
      have hpre : (List.range N).flatMap c = [] := by
        refine List.flatMap_eq_nil_iff.mpr (fun i hi => ?_)
        have hiN := List.mem_range.mp hi
        rw [hc i (by omega), if_neg (by omega)]
      rw [hpre, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        hc N (by omega), if_pos rfl]
    · have hKN' : K < N := by omega
      rw [ih hKN' (fun i hi => hc i (by omega))]
      rw [List.flatMap_cons, hc N (by omega), if_neg hNK]
      simp

/-- The absorbing end state of the block loops. -/
def blockDone : List Bool := pairEncode [] []

/-- The Boolean emptiness test, in the shape
`Complexity.polyTimeComputable_ite` consumes. -/
def isNilB (w : List Bool) : Bool := decide (w = [])

/-- Keeping only the head symbol is polynomial-time computable.
**Proof sketch.** `w.take 1` is the length-gated take
`Complexity.PrefixByLength.take` applied to `Turing.pairEncode [true] w`. -/
theorem polyTimeComputable_take1 : PolyTimeComputable (fun w => w.take 1) := by
  have henc : PolyTimeComputable (fun w => pairEncode [true] w) :=
    (polyTimeComputable_const [true]).pairEncode polyTimeComputable_id
  have heq : (fun w : List Bool => w.take 1) =
      PrefixByLength.take ∘ (fun w => pairEncode [true] w) := by
    funext w
    simp [Function.comp, PrefixByLength.take]
  rw [heq]
  exact polyTimeComputable_takePrefixByLength.comp henc

/-- The head bit (defaulting to `false`) is polynomial-time computable as a
one-bit output.
**Proof sketch.** `[w.headD false] = (w ++ [false]).take 1`. -/
theorem polyTimeComputable_headD :
    PolyTimeComputable (fun w => [w.headD false]) := by
  have happ : PolyTimeComputable (fun w : List Bool => w ++ [false]) :=
    PolyTimeComputable.append polyTimeComputable_id (polyTimeComputable_const [false])
  have heq : (fun w : List Bool => [w.headD false]) =
      (fun w : List Bool => w.take 1) ∘ (fun w : List Bool => w ++ [false]) := by
    funext w
    cases w <;> simp [Function.comp]
  rw [heq]
  exact polyTimeComputable_take1.comp happ

/-! ### The emit-iteration combinator -/

/-- **The bounded loop of polynomial-time rounds** — the machine-level engine
of every block-query closure: iterating a polynomial-time step function `g` a
polynomial number of times from the input, concatenating a polynomial-time
chunk `e` of each iterate, is again polynomial-time, provided every iterate
stays inside one polynomial length envelope `b·(n+1)^l` of the *original*
input length.

**Proof sketch.** Unpack the two machines and apply
`Turing.FinTM.exists_emitIterTM` (in
`TCSlib.Complexity.TuringMachine.Build.EmitIterBody`): an instance of
`Turing.FinTM.exists_emitLoopTM` whose body copies its input onto work tape
zero and runs each round as two clean calls on the tape-resident state word —
an emit-mode call (`Turing.FinTM.exists_emitCallTM`) forwarding the chunk
`e s`, then an install-mode call (`Turing.FinTM.exists_installCallTM`)
replacing the word by `g s`.  The host's admissibility invariant is "the
state word is an orbit point of `g` from the input", so the orbit-only
length envelope `horbit` bounds each call's budget by one polynomial in the
input length; the fuel machine is
`Turing.FinTM.computesFunInTime_polyBits`. -/
theorem polyTimeComputable_emitIter {g e : List Bool → List Bool}
    (hg : PolyTimeComputable g) (he : PolyTimeComputable e)
    (a' k' b l : ℕ)
    (horbit : ∀ (w : List Bool) (i : ℕ),
      (g^[i] w).length ≤ b * (w.length + 1) ^ l) :
    PolyTimeComputable (fun w =>
      (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap (fun i => e (g^[i] w))) := by
  obtain ⟨G, CG, cG, hG⟩ := hg
  obtain ⟨E, CE, cE, hE⟩ := he
  obtain ⟨M, C, c, hM⟩ :=
    FinTM.exists_emitIterTM G E g e CG cG CE cE hG hE a' k' b l horbit
  exact ⟨M, C, c, hM⟩

/-! ### Truncating bitwise XOR -/

/-- Bitwise XOR of the two components of a pair, truncating to the shorter
component (`List.zipWith` semantics); malformed pairs give `[]`. -/
def xorD (z : List Bool) : List Bool :=
  List.zipWith xor (pairFstD z) (pairSndD z)

/-- One round of the XOR transducer: drop the head of both components. -/
private def xorPairStep (s : List Bool) : List Bool :=
  pairEncode ((pairFstD s).drop 1) ((pairSndD s).drop 1)

/-- The XOR transducer's chunk: one XOR bit while both components are
nonempty, nothing afterwards. -/
private def xorPairEmit (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) || isNilB (pairSndD s) then []
  else if (pairFstD s).headD false then
    if (pairSndD s).headD false then [false] else [true]
  else
    if (pairSndD s).headD false then [true] else [false]

private theorem polyTimeComputable_xorPairStep : PolyTimeComputable xorPairStep :=
  (polyTimeComputable_tail.comp polyTimeComputable_pairFstD).pairEncode
    (polyTimeComputable_tail.comp polyTimeComputable_pairSndD)

private theorem polyTimeComputable_xorPairEmit : PolyTimeComputable xorPairEmit := by
  have hguard : PolyTimeComputable (fun s =>
      [isNilB (pairFstD s) || isNilB (pairSndD s)]) :=
    polyTimeComputable_or (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD)
      (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
  have hd1 : PolyTimeComputable (fun s => [(pairFstD s).headD false]) :=
    polyTimeComputable_headD.comp polyTimeComputable_pairFstD
  have hd2 : PolyTimeComputable (fun s => [(pairSndD s).headD false]) :=
    polyTimeComputable_headD.comp polyTimeComputable_pairSndD
  exact polyTimeComputable_ite hguard (polyTimeComputable_const [])
    (polyTimeComputable_ite hd1
      (polyTimeComputable_ite hd2 (polyTimeComputable_const [false])
        (polyTimeComputable_const [true]))
      (polyTimeComputable_ite hd2 (polyTimeComputable_const [true])
        (polyTimeComputable_const [false])))

/-- One XOR round never grows the state beyond `max` with the empty pair. -/
private theorem length_xorPairStep_le (s : List Bool) :
    (xorPairStep s).length ≤ max s.length 2 := by
  cases h : pairDecode s with
  | none =>
    have h1 : pairFstD s = [] := by simp [pairFstD, h]
    have h2 : pairSndD s = [] := by simp [pairSndD, h]
    refine le_trans ?_ (le_max_right _ _)
    simp [xorPairStep, h1, h2, length_pairEncode]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode s a b h
    refine le_trans ?_ (le_max_left _ _)
    rw [hz]
    simp only [xorPairStep, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_drop]
    omega

/-- Orbit envelope for the XOR transducer. -/
private theorem length_xorPairStep_iterate (w : List Bool) (i : ℕ) :
    (xorPairStep^[i] w).length ≤ 2 * (w.length + 1) ^ 1 := by
  have hmax : (xorPairStep^[i] w).length ≤ max w.length 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_xorPairStep_le _) (max_le ih (le_max_right _ _))
  refine le_trans hmax ?_
  rw [pow_one]
  exact max_le (by omega) (by omega)

/-- The XOR transducer's orbit drops both components one symbol per round. -/
private theorem xorPairStep_orbit (p u : List Bool) (i : ℕ) :
    xorPairStep^[i] (pairEncode p u) = pairEncode (p.drop i) (u.drop i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [xorPairStep, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]

/-- On two nonempty components the chunk is the single XOR bit of the heads. -/
private theorem xorPairEmit_cons (b c : Bool) (p u : List Bool) :
    xorPairEmit (pairEncode (b :: p) (c :: u)) = [xor b c] := by
  cases b <;> cases c <;> simp [xorPairEmit, isNilB]

/-- Once a component is exhausted the chunk is empty. -/
private theorem xorPairEmit_nil {p u : List Bool} (h : p = [] ∨ u = []) :
    xorPairEmit (pairEncode p u) = [] := by
  rcases h with rfl | rfl <;> simp [xorPairEmit, isNilB]

/-- The concatenated chunks of the XOR transducer compute `List.zipWith xor`.
**Proof sketch.** Induction on the round budget, generalizing the two
components: each cons-cons round contributes its head XOR
(`xorPairEmit_cons`) and the orbit shifts both tails; an exhausted component
silences every later round. -/
private theorem xorPair_output : ∀ (N : ℕ) (p u : List Bool),
    min p.length u.length ≤ N →
    (List.range N).flatMap (fun i => xorPairEmit (pairEncode (p.drop i) (u.drop i))) =
      List.zipWith xor p u := by
  intro N
  induction N with
  | zero =>
    intro p u h
    have : p = [] ∨ u = [] := by
      rcases p with _ | ⟨b, p⟩
      · exact Or.inl rfl
      rcases u with _ | ⟨c, u⟩
      · exact Or.inr rfl
      simp at h
    rcases this with rfl | rfl <;> simp
  | succ N ih =>
    intro p u h
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rcases p with _ | ⟨b, p⟩
    · simp only [List.zipWith_nil_left, List.drop_nil]
      rw [xorPairEmit_nil (Or.inl rfl), List.nil_append]
      refine List.flatMap_eq_nil_iff.mpr (fun i _ => ?_)
      exact xorPairEmit_nil (Or.inl rfl)
    rcases u with _ | ⟨c, u⟩
    · simp only [List.zipWith_nil_right, List.drop_nil]
      rw [xorPairEmit_nil (Or.inr rfl), List.nil_append]
      refine List.flatMap_eq_nil_iff.mpr (fun i _ => ?_)
      exact xorPairEmit_nil (Or.inr rfl)
    rw [List.drop_zero, List.drop_zero, xorPairEmit_cons, List.zipWith_cons_cons]
    have hrest : (List.range N).flatMap
        (fun i => xorPairEmit (pairEncode ((b :: p).drop (i + 1)) ((c :: u).drop (i + 1)))) =
        List.zipWith xor p u := by
      have heq : (fun i => xorPairEmit (pairEncode ((b :: p).drop (i + 1))
          ((c :: u).drop (i + 1)))) =
          (fun i => xorPairEmit (pairEncode (p.drop i) (u.drop i))) := by
        funext i
        rfl
      rw [heq]
      exact ih p u (by simp at h; omega)
    rw [hrest]
    rfl

/-- `xorD` is polynomial-time computable.
**Proof sketch.** An instance of `Complexity.polyTimeComputable_emitIter`:
the loop state is the pair of not-yet-consumed components; each round emits
the XOR of the two head bits (nothing once either component is exhausted) and
drops both heads, so the concatenated output is exactly the truncating
`List.zipWith xor`.  The round budget `|z|+1` dominates the shorter
component's length.  (The truncating semantics on unequal lengths is the
audited ch7-phase1 finding 1 convention.) -/
theorem polyTimeComputable_xorD : PolyTimeComputable xorD := by
  have hloop := polyTimeComputable_emitIter polyTimeComputable_xorPairStep
    polyTimeComputable_xorPairEmit 1 1 2 1 (fun w i => length_xorPairStep_iterate w i)
  have hinit : PolyTimeComputable (fun z => pairEncode (pairFstD z) (pairSndD z)) :=
    polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD
  have heq : xorD = (fun w => (List.range (1 * (w.length + 1) ^ 1 + 1)).flatMap
      (fun i => xorPairEmit (xorPairStep^[i] w))) ∘
      (fun z => pairEncode (pairFstD z) (pairSndD z)) := by
    funext z
    rw [Function.comp_apply]
    have horb : ∀ i, xorPairStep^[i] (pairEncode (pairFstD z) (pairSndD z)) =
        pairEncode ((pairFstD z).drop i) ((pairSndD z).drop i) :=
      xorPairStep_orbit (pairFstD z) (pairSndD z)
    have hbudget : min (pairFstD z).length (pairSndD z).length ≤
        1 * ((pairEncode (pairFstD z) (pairSndD z)).length + 1) ^ 1 + 1 := by
      have h1 := length_pairFstD_le z
      rw [pow_one, length_pairEncode]
      omega
    calc xorD z = List.zipWith xor (pairFstD z) (pairSndD z) := rfl
      _ = (List.range (1 * ((pairEncode (pairFstD z) (pairSndD z)).length + 1) ^ 1 + 1)).flatMap
          (fun i => xorPairEmit (pairEncode ((pairFstD z).drop i) ((pairSndD z).drop i))) :=
        (xorPair_output _ (pairFstD z) (pairSndD z) hbudget).symm
      _ = _ := by
        simp only [horb]
  rw [heq]
  exact hloop.comp hinit

/-- `xorD` computes the truncating bitwise XOR on genuine pairs. -/
@[simp]
theorem xorD_pairEncode (a b : List Bool) :
    xorD (pairEncode a b) = List.zipWith xor a b := by
  simp [xorD]

end Complexity
```

## ===== TCSlib/Complexity/ClassNP/PolyTimeBlockTests.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The aggregated block tests

The three customers of the bounded block-query loop
(`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`): the one-bit OR,
strict-majority, and XOR-then-OR aggregations of a polynomial-time one-bit
indicator over polynomially many polynomial-length blocks are polynomial-time.
Each is an instance of `Complexity.polyTimeComputable_emitIter` with the
aggregation state (flag, vote counters, XOR mask) carried inside the loop's
tape-resident state word; the per-round work is assembled from the existing
`FP` combinators, and the orbit is computed in closed form by induction.

These are the `PolyTimeComputable` engines of the `P`-closure lemmas
`Complexity.mem_P_of_blockAny` / `_blockMajority` / `_blockXorAny` in
`TCSlib.Complexity.ClassNP.PClosure`.

## Main definitions

* `Complexity.blockAt` — the `i`-th length-`a·(n+1)^k` block of the second
  component of a pair, where `n` is the first component's length.

## Main results

* `Complexity.polyTimeComputable_blockAnyTest` / `_blockXorAnyTest` — the
  aggregated one-bit OR and XOR-then-OR block tests of a polynomial-time
  one-bit indicator are polynomial-time.  The strict-majority test lives in
  `TCSlib.Complexity.ClassNP.PolyTimeBlockMajority`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.3, Theorem 7.8; §7.4.1; Theorems
  7.17–7.18: the implicit "simulate the machine on each block" closures.)
-/

namespace Complexity

open Turing

/-- The `i`-th length-`a·(n+1)^k` block of the second component of a pair,
where `n` is the first component's length. -/
def blockAt (a k : ℕ) (z : List Bool) (i : ℕ) : List Bool :=
  ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))).take
    (a * ((pairFstD z).length + 1) ^ k)

/-! #### The OR-aggregating loop -/

/-- One round of the OR-aggregating block loop on state
`pairEncode [flag] (pairEncode countdown (pairEncode x rem))`: OR the
indicator of the current block into the flag, drop the block, decrement the
unary countdown.  A done or malformed state is sent to the absorbing
`blockDone`; an exhausted countdown is sent to `blockDone` one step after the
chunk function has emitted the flag. -/
private noncomputable def anyStep (V : Language Bool) (a k : ℕ) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then blockDone
  else if isNilB (pairFstD (pairSndD s)) then blockDone
  else
    pairEncode
      (if MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s))) then [true]
        else pairFstD s)
      (pairEncode ((pairFstD (pairSndD s)).drop 1)
        (sliceDropAt a k (pairSndD (pairSndD s))))

/-- The chunk function: emit the flag exactly at countdown exhaustion. -/
private def anyEmit (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then []
  else if isNilB (pairFstD (pairSndD s)) then pairFstD s
  else []

/-- The initial state: clear flag, unary countdown `a'·(n+1)^k'`, and the
normalized input pair. -/
private def anyInit (a' k' : ℕ) (z : List Bool) : List Bool :=
  pairEncode [false]
    (pairEncode (List.replicate (a' * ((pairFstD z).length + 1) ^ k') true)
      (pairEncode (pairFstD z) (pairSndD z)))

/-- The OR round is polynomial-time.
**Proof sketch.** Assemble the two guards, the indicator of the sliced block,
the flag update, the countdown tail, and the dropped remainder from the `FP`
combinators (`polyTimeComputable_ite`/`pairEncode`/`comp` and the slice
primitives). -/
private theorem polyTimeComputable_anyStep {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z])) (a k : ℕ) :
    PolyTimeComputable (anyStep V a k) := by
  have hcd : PolyTimeComputable (fun s => pairFstD (pairSndD s)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hzz : PolyTimeComputable (fun s => pairSndD (pairSndD s)) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp hcd
  have hind : PolyTimeComputable
      (fun s => [MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s)))]) :=
    hV.comp ((polyTimeComputable_sliceTakeAt a k).comp hzz)
  have hflag : PolyTimeComputable (fun s =>
      if MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s))) then [true]
      else pairFstD s) :=
    polyTimeComputable_ite hind (polyTimeComputable_const [true]) polyTimeComputable_pairFstD
  have hrest : PolyTimeComputable (fun s =>
      pairEncode ((pairFstD (pairSndD s)).drop 1)
        (sliceDropAt a k (pairSndD (pairSndD s)))) :=
    (polyTimeComputable_tail.comp hcd).pairEncode
      ((polyTimeComputable_sliceDropAt a k).comp hzz)
  have hinner := polyTimeComputable_ite ht2 (polyTimeComputable_const blockDone)
    (hflag.pairEncode hrest)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const blockDone) hinner

private theorem polyTimeComputable_anyEmit : PolyTimeComputable anyEmit := by
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const [])
    (polyTimeComputable_ite ht2 polyTimeComputable_pairFstD (polyTimeComputable_const []))

private theorem polyTimeComputable_anyInit (a' k' : ℕ) :
    PolyTimeComputable (anyInit a' k') := by
  have hcnt : PolyTimeComputable
      (fun z => List.replicate (a' * ((pairFstD z).length + 1) ^ k') true) :=
    (polyTimeComputable_polyUnary a' k').comp polyTimeComputable_pairFstD
  exact (polyTimeComputable_const [false]).pairEncode
    (hcnt.pairEncode (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD))

/-- One loop round never grows the state beyond `max` with the done state's
length.
**Proof sketch.** The done branches have length two.  A live round keeps the
flag within the old flag's length, shortens the countdown, and replaces the
remainder by a dropped slice; summing the `Turing.length_pairEncode`
decompositions, the round shrinks the state by at least the two symbols the
countdown loses. -/
private theorem length_anyStep_le (V : Language Bool) (a k : ℕ) (s : List Bool) :
    (anyStep V a k s).length ≤ max s.length 2 := by
  unfold anyStep
  cases h1 : isNilB (pairFstD s) with
  | true =>
    simp only [if_pos rfl]
    refine le_trans ?_ (le_max_right _ _)
    simp [blockDone, length_pairEncode]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h2 : isNilB (pairFstD (pairSndD s)) with
    | true =>
      simp only [if_pos rfl]
      refine le_trans ?_ (le_max_right _ _)
      simp [blockDone, length_pairEncode]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : pairFstD s ≠ [] := by simpa [isNilB] using h1
      have hcd : pairFstD (pairSndD s) ≠ [] := by simpa [isNilB] using h2
      have hs := eq_pairEncode_of_pairFstD_ne hf
      have ht := eq_pairEncode_of_pairFstD_ne hcd
      refine le_trans ?_ (le_max_left _ _)
      have hslice := length_sliceDropAt_le a k (pairSndD (pairSndD s))
      have hfl : (if MultiTapeTM.indicator V
          (sliceTakeAt a k (pairSndD (pairSndD s))) then [true]
          else pairFstD s).length ≤ (pairFstD s).length := by
        cases MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD s)))
        · simp
        · simpa using Nat.one_le_iff_ne_zero.mpr
            (by simpa [List.length_eq_zero_iff] using hf)
      have hlens : s.length =
          2 * (pairFstD s).length + 2 +
            (2 * (pairFstD (pairSndD s)).length + 2 + (pairSndD (pairSndD s)).length) := by
        conv_lhs => rw [hs]
        rw [length_pairEncode]
        congr 2
        conv_lhs => rw [ht]
        rw [length_pairEncode]
      have hcd1 : 1 ≤ (pairFstD (pairSndD s)).length :=
        Nat.one_le_iff_ne_zero.mpr (by simpa [List.length_eq_zero_iff] using hcd)
      rw [length_pairEncode, length_pairEncode]
      simp only [List.length_drop]
      have hslice' : (sliceDropAt a k (pairSndD (pairSndD s))).length ≤
          (pairSndD (pairSndD s)).length + 2 :=
        le_trans hslice (by omega)
      omega

/-- Orbit envelope for the OR loop, in the shape
`Complexity.polyTimeComputable_emitIter` consumes. -/
private theorem length_anyStep_iterate (V : Language Bool) (a k : ℕ)
    (w : List Bool) (i : ℕ) :
    ((anyStep V a k)^[i] w).length ≤ 2 * (w.length + 1) ^ 1 := by
  have hmax : ((anyStep V a k)^[i] w).length ≤ max w.length 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_anyStep_le V a k _) (max_le ih (le_max_right _ _))
  refine le_trans hmax ?_
  rw [pow_one]
  exact max_le (by omega) (by omega)

/-- The done state is absorbing. -/
private theorem anyStep_done (V : Language Bool) (a k : ℕ) :
    anyStep V a k blockDone = blockDone := by
  unfold anyStep
  simp [blockDone, isNilB]

/-- Closed form of the OR loop's orbit up to countdown exhaustion.
**Proof sketch.** Induction on the round index: the guards see a one-bit flag
and a positive countdown, so the step fires; the slice primitives advance the
remainder by one block, `List.range_succ` extends the OR by the current
block's indicator, and the countdown loses one `true`. -/
private theorem anyStep_orbit (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : i ≤ a' * ((pairFstD z).length + 1) ^ k') :
    (anyStep V a k)^[i] (anyInit a' k' z) =
      pairEncode
        [(List.range i).any (fun j => MultiTapeTM.indicator V
          (pairEncode (pairFstD z) (blockAt a k z j)))]
        (pairEncode
          (List.replicate (a' * ((pairFstD z).length + 1) ^ k' - i) true)
          (pairEncode (pairFstD z)
            ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))))) := by
  induction i with
  | zero => simp [anyInit]
  | succ i ih =>
    have hii : i ≤ a' * ((pairFstD z).length + 1) ^ k' := Nat.le_of_succ_le hi
    rw [Function.iterate_succ_apply', ih hii]
    have hcd : a' * ((pairFstD z).length + 1) ^ k' - i =
        (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) + 1 := by omega
    rw [hcd, List.replicate_succ]
    unfold anyStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, if_neg (by simp [isNilB])]
    rw [pairFstD_pairEncode, pairSndD_pairEncode]
    congr 1
    · rw [sliceTakeAt, pairFstD_pairEncode, pairSndD_pairEncode]
      rw [List.range_succ, List.any_append]
      cases hb : MultiTapeTM.indicator V (pairEncode (pairFstD z)
          (((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))).take
            (a * ((pairFstD z).length + 1) ^ k))) with
      | true =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = true := hb
        simp [hb']
      | false =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = false := hb
        simp [hb']
    · congr 1
      · rw [pairFstD_pairEncode]
        simp
      · rw [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
        congr 2
        ring

/-- Beyond exhaustion the orbit sits at the done state. -/
private theorem anyStep_orbit_done (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : a' * ((pairFstD z).length + 1) ^ k' < i) :
    (anyStep V a k)^[i] (anyInit a' k' z) = blockDone := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + (K + 1) := ⟨i - (K + 1), by omega⟩
  rw [Function.iterate_add_apply]
  have hend : (anyStep V a k)^[K + 1] (anyInit a' k' z) = blockDone := by
    rw [Function.iterate_succ_apply', anyStep_orbit V a k a' k' z (le_refl K)]
    unfold anyStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB, hK])]
  rw [hend]
  clear hi
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, anyStep_done]

/-- The OR loop's machine-level output is the single aggregated bit.
**Proof sketch.** The countdown exhausts within the machine's larger round
budget (the input embeds its own first component, and the schedule is
monotone).  Rounds before exhaustion emit nothing, the exhaustion round emits
the flag, and the absorbing done state emits nothing after it, so the
single-live-chunk concatenation lemma applies. -/
private theorem anyLoop_output (V : Language Bool) (a k a' k' : ℕ) (z : List Bool) :
    (List.range (a' * ((anyInit a' k' z).length + 1) ^ k' + 1)).flatMap
      (fun i => anyEmit ((anyStep V a k)^[i] (anyInit a' k' z))) =
      [(List.range (a' * ((pairFstD z).length + 1) ^ k')).any
        (fun j => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))] := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  have hlen : (pairFstD z).length ≤ (anyInit a' k' z).length := by
    rw [anyInit, length_pairEncode, length_pairEncode, length_pairEncode]
    omega
  have hKN : K < a' * ((anyInit a' k' z).length + 1) ^ k' + 1 := by
    have := Nat.mul_le_mul_left a'
      (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) k')
    omega
  refine flatMap_range_eq_single hKN (fun i _ => ?_)
  rcases Nat.lt_trichotomy i K with hiK | rfl | hiK
  · rw [if_neg (by omega), anyStep_orbit V a k a' k' z (le_of_lt hiK)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_neg (by simp [isNilB]; omega)]
  · rw [if_pos rfl, anyStep_orbit V a k a' k' z (le_refl K)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB]; omega), pairFstD_pairEncode]
  · rw [if_neg (by omega), anyStep_orbit_done V a k a' k' z hiK]
    unfold anyEmit
    rw [if_pos (by simp [blockDone, isNilB])]

/-- The OR-aggregated block test of a polynomial-time one-bit indicator is
polynomial-time: one bit saying whether some of the `a'·(n+1)^k'` blocks of
length `a·(n+1)^k` passes the test on `Turing.pairEncode`d (first component,
block).

**Proof sketch.** An instance of `Complexity.polyTimeComputable_emitIter`.
The loop state is `pairEncode [flag] (pairEncode countdown (pairEncode x rem))`
with a unary countdown initialized at `a'·(|x|+1)^k'`
(`Complexity.polyTimeComputable_polyUnary`); each round ORs the indicator of
`sliceTakeAt a k` into the flag, drops the block (`sliceDropAt a k`), and
decrements; the chunk function emits `[flag]` exactly at countdown exhaustion
(the step then moves to an absorbing done state), so the concatenated output
is the single aggregated bit.  The orbit is computed in closed form by
induction on the round index. -/
theorem polyTimeComputable_blockAnyTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun z =>
      [(List.range (a' * ((pairFstD z).length + 1) ^ k')).any
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i)))]) := by
  have hloop := polyTimeComputable_emitIter (polyTimeComputable_anyStep hV a k)
    polyTimeComputable_anyEmit a' k' 2 1 (length_anyStep_iterate V a k)
  have heq : (fun z => [(List.range (a' * ((pairFstD z).length + 1) ^ k')).any
      (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i)))]) =
      ((fun w => (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap
        (fun i => anyEmit ((anyStep V a k)^[i] w))) ∘ anyInit a' k') := by
    funext z
    rw [Function.comp_apply, anyLoop_output V a k a' k' z]
  rw [heq]
  exact hloop.comp (polyTimeComputable_anyInit a' k')

/-! #### The XOR-shifted OR loop -/

/-- One round of the XOR-shifted OR loop on state
`pairEncode [flag] (pairEncode countdown (pairEncode v (pairEncode x u)))`:
XOR the mask `v` with the current block of `u`, test paired with `x`, OR
into the flag, drop the block, decrement. -/
private noncomputable def xorStep (V : Language Bool) (a k : ℕ) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then blockDone
  else if isNilB (pairFstD (pairSndD s)) then blockDone
  else
    pairEncode
      (if MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))))) then [true]
        else pairFstD s)
      (pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode (pairFstD (pairSndD (pairSndD s)))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s))))))

/-- The initial state of the XOR-shifted loop on the nested pair
`⟨⟨x, u⟩, v⟩`: clear flag, unary countdown `a'·(|x|+1)^k'`, the mask `v`, and
the normalized `⟨x, u⟩`. -/
private def xorInit (a' k' : ℕ) (w : List Bool) : List Bool :=
  pairEncode [false]
    (pairEncode
      (List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k') true)
      (pairEncode (pairSndD w)
        (pairEncode (pairFstD (pairFstD w)) (pairSndD (pairFstD w)))))

/-- The XOR-shifted round is polynomial-time.
**Proof sketch.** As the OR round, with the per-round test precomposed with
the truncating XOR of the carried mask and the sliced block
(`Complexity.polyTimeComputable_xorD`). -/
private theorem polyTimeComputable_xorStep {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z])) (a k : ℕ) :
    PolyTimeComputable (xorStep V a k) := by
  have hcd : PolyTimeComputable (fun s => pairFstD (pairSndD s)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hmask : PolyTimeComputable (fun s => pairFstD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hzz : PolyTimeComputable (fun s => pairSndD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp hcd
  have hblk : PolyTimeComputable (fun s =>
      pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))) :=
    polyTimeComputable_pairSndD.comp ((polyTimeComputable_sliceTakeAt a k).comp hzz)
  have htest : PolyTimeComputable (fun s =>
      [MultiTapeTM.indicator V
        (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
          (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
            (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))))))]) :=
    hV.comp ((polyTimeComputable_pairFstD.comp hzz).pairEncode
      (polyTimeComputable_xorD.comp (hmask.pairEncode hblk)))
  have hflag : PolyTimeComputable (fun s =>
      if MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))))) then [true]
        else pairFstD s) :=
    polyTimeComputable_ite htest (polyTimeComputable_const [true])
      polyTimeComputable_pairFstD
  have hrest : PolyTimeComputable (fun s =>
      pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode (pairFstD (pairSndD (pairSndD s)))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s)))))) :=
    (polyTimeComputable_tail.comp hcd).pairEncode
      (hmask.pairEncode ((polyTimeComputable_sliceDropAt a k).comp hzz))
  have hinner := polyTimeComputable_ite ht2 (polyTimeComputable_const blockDone)
    (hflag.pairEncode hrest)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const blockDone) hinner

private theorem polyTimeComputable_xorInit (a' k' : ℕ) :
    PolyTimeComputable (xorInit a' k') := by
  have hx : PolyTimeComputable (fun w => pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hu : PolyTimeComputable (fun w => pairSndD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hcnt : PolyTimeComputable (fun w =>
      List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k') true) :=
    (polyTimeComputable_polyUnary a' k').comp hx
  exact (polyTimeComputable_const [false]).pairEncode
    (hcnt.pairEncode (polyTimeComputable_pairSndD.pairEncode (hx.pairEncode hu)))

/-- One XOR-shifted round respects the slack measure `|s| + 16·|countdown s|`.
**Proof sketch.** As the majority round's bound; the mask is copied verbatim
and the joint-projection bound `length_pair_components_le` charges it against
the old state. -/
private theorem length_xorStep_le (V : Language Bool) (a k : ℕ) (s : List Bool) :
    (xorStep V a k s).length +
      16 * (pairFstD (pairSndD (xorStep V a k s))).length ≤
      max (s.length + 16 * (pairFstD (pairSndD s)).length) 2 := by
  unfold xorStep
  cases h1 : isNilB (pairFstD s) with
  | true =>
    simp only [if_pos rfl]
    refine le_trans ?_ (le_max_right _ _)
    simp [blockDone, length_pairEncode, pairFstD_nil]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h2 : isNilB (pairFstD (pairSndD s)) with
    | true =>
      simp only [if_pos rfl]
      refine le_trans ?_ (le_max_right _ _)
      simp [blockDone, length_pairEncode, pairFstD_nil]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : pairFstD s ≠ [] := by simpa [isNilB] using h1
      have hcd : pairFstD (pairSndD s) ≠ [] := by simpa [isNilB] using h2
      have hs := eq_pairEncode_of_pairFstD_ne hf
      have ht := eq_pairEncode_of_pairFstD_ne hcd
      refine le_trans ?_ (le_max_left _ _)
      have hfl : (if MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))))) then [true]
          else pairFstD s).length ≤ (pairFstD s).length := by
        cases MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD s))))
            (xorD (pairEncode (pairFstD (pairSndD (pairSndD s)))
              (pairSndD (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))))))
        · simp
        · simpa using Nat.one_le_iff_ne_zero.mpr
            (by simpa [List.length_eq_zero_iff] using hf)
      have hslice := length_sliceDropAt_le a k (pairSndD (pairSndD (pairSndD s)))
      have hslice' : (sliceDropAt a k (pairSndD (pairSndD (pairSndD s)))).length ≤
          (pairSndD (pairSndD (pairSndD s))).length + 2 := le_trans hslice (by omega)
      have hY := length_pair_components_le (pairSndD (pairSndD s))
      have hlens : s.length =
          2 * (pairFstD s).length + 2 +
            (2 * (pairFstD (pairSndD s)).length + 2 + (pairSndD (pairSndD s)).length) := by
        conv_lhs => rw [hs]
        rw [length_pairEncode]
        congr 2
        conv_lhs => rw [ht]
        rw [length_pairEncode]
      have hcd1 : 1 ≤ (pairFstD (pairSndD s)).length :=
        Nat.one_le_iff_ne_zero.mpr (by simpa [List.length_eq_zero_iff] using hcd)
      simp only [pairSndD_pairEncode, pairFstD_pairEncode, length_pairEncode,
        List.length_drop]
      omega

/-- Orbit envelope for the XOR-shifted loop. -/
private theorem length_xorStep_iterate (V : Language Bool) (a k : ℕ)
    (w : List Bool) (i : ℕ) :
    ((xorStep V a k)^[i] w).length ≤ 17 * (w.length + 1) ^ 1 := by
  have hmax : ((xorStep V a k)^[i] w).length +
      16 * (pairFstD (pairSndD ((xorStep V a k)^[i] w))).length ≤
      max (w.length + 16 * (pairFstD (pairSndD w)).length) 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_xorStep_le V a k _) (max_le ih (le_max_right _ _))
  have h1 : (pairFstD (pairSndD w)).length ≤ w.length :=
    le_trans (length_pairFstD_le _) (length_pairSndD_le w)
  rw [pow_one]
  omega

/-- The done state is absorbing for the XOR-shifted loop. -/
private theorem xorStep_done (V : Language Bool) (a k : ℕ) :
    xorStep V a k blockDone = blockDone := by
  unfold xorStep
  simp [blockDone, isNilB]

/-- Closed form of the XOR-shifted loop's orbit up to countdown exhaustion.
**Proof sketch.** As the OR orbit, with the carried mask constant and the
per-round indicator applied to the mask XORed with the current block
(`xorD_pairEncode`). -/
private theorem xorStep_orbit (V : Language Bool) (a k a' k' : ℕ) (w : List Bool)
    {i : ℕ} (hi : i ≤ a' * ((pairFstD (pairFstD w)).length + 1) ^ k') :
    (xorStep V a k)^[i] (xorInit a' k' w) =
      pairEncode
        [(List.range i).any (fun j => MultiTapeTM.indicator V
          (pairEncode (pairFstD (pairFstD w))
            (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) j))))]
        (pairEncode
          (List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - i) true)
          (pairEncode (pairSndD w)
            (pairEncode (pairFstD (pairFstD w))
              ((pairSndD (pairFstD w)).drop
                (i * (a * ((pairFstD (pairFstD w)).length + 1) ^ k)))))) := by
  induction i with
  | zero => simp [xorInit]
  | succ i ih =>
    have hii : i ≤ a' * ((pairFstD (pairFstD w)).length + 1) ^ k' :=
      Nat.le_of_succ_le hi
    rw [Function.iterate_succ_apply', ih hii]
    have hcd : a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - i =
        (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - (i + 1)) + 1 := by omega
    rw [hcd, List.replicate_succ]
    unfold xorStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, if_neg (by simp [isNilB])]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    have hdrop1 : (true :: List.replicate
        (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - (i + 1)) true).drop 1 =
        List.replicate (a' * ((pairFstD (pairFstD w)).length + 1) ^ k' - (i + 1)) true :=
      rfl
    have hslice2 : sliceDropAt a k (pairEncode (pairFstD (pairFstD w))
        ((pairSndD (pairFstD w)).drop
          (i * (a * ((pairFstD (pairFstD w)).length + 1) ^ k)))) =
        pairEncode (pairFstD (pairFstD w))
          ((pairSndD (pairFstD w)).drop
            ((i + 1) * (a * ((pairFstD (pairFstD w)).length + 1) ^ k))) := by
      rw [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
      congr 2
      ring
    rw [hdrop1, hslice2]
    congr 2
    simp only [sliceTakeAt, pairFstD_pairEncode, pairSndD_pairEncode, xorD_pairEncode]
    rw [List.range_succ, List.any_append]
    cases hb : MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
        (List.zipWith xor (pairSndD w)
          (((pairSndD (pairFstD w)).drop
            (i * (a * ((pairFstD (pairFstD w)).length + 1) ^ k))).take
              (a * ((pairFstD (pairFstD w)).length + 1) ^ k)))) with
    | true =>
      have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))) = true := hb
      simp [hb']
    | false =>
      have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))) = false := hb
      simp [hb']

/-- Beyond exhaustion the XOR-shifted orbit sits at the done state. -/
private theorem xorStep_orbit_done (V : Language Bool) (a k a' k' : ℕ) (w : List Bool)
    {i : ℕ} (hi : a' * ((pairFstD (pairFstD w)).length + 1) ^ k' < i) :
    (xorStep V a k)^[i] (xorInit a' k' w) = blockDone := by
  set K := a' * ((pairFstD (pairFstD w)).length + 1) ^ k' with hK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + (K + 1) := ⟨i - (K + 1), by omega⟩
  rw [Function.iterate_add_apply]
  have hend : (xorStep V a k)^[K + 1] (xorInit a' k' w) = blockDone := by
    rw [Function.iterate_succ_apply', xorStep_orbit V a k a' k' w (le_refl K)]
    unfold xorStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB, hK])]
  rw [hend]
  clear hi
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, xorStep_done]

/-- The XOR-shifted loop's machine-level output is the single aggregated bit.
**Proof sketch.** As the OR output lemma, over the nested pairing: the
countdown is scheduled at the inner first component's length, which the
initial state's length dominates. -/
private theorem xorLoop_output (V : Language Bool) (a k a' k' : ℕ) (w : List Bool) :
    (List.range (a' * ((xorInit a' k' w).length + 1) ^ k' + 1)).flatMap
      (fun i => anyEmit ((xorStep V a k)^[i] (xorInit a' k' w))) =
      [(List.range (a' * ((pairFstD (pairFstD w)).length + 1) ^ k')).any
        (fun j => MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) j))))] := by
  set K := a' * ((pairFstD (pairFstD w)).length + 1) ^ k' with hK
  have hlen : (pairFstD (pairFstD w)).length ≤ (xorInit a' k' w).length := by
    have h1 : (pairFstD (pairFstD w)).length ≤ w.length :=
      le_trans (length_pairFstD_le _) (length_pairFstD_le w)
    simp only [xorInit, length_pairEncode, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  have hKN : K < a' * ((xorInit a' k' w).length + 1) ^ k' + 1 := by
    have := Nat.mul_le_mul_left a'
      (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) k')
    omega
  refine flatMap_range_eq_single hKN (fun i _ => ?_)
  rcases Nat.lt_trichotomy i K with hiK | rfl | hiK
  · rw [if_neg (by omega), xorStep_orbit V a k a' k' w (le_of_lt hiK)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_neg (by simp [isNilB]; omega)]
  · rw [if_pos rfl, xorStep_orbit V a k a' k' w (le_refl K)]
    unfold anyEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB]; omega), pairFstD_pairEncode]
  · rw [if_neg (by omega), xorStep_orbit_done V a k a' k' w hiK]
    unfold anyEmit
    rw [if_pos (by simp [blockDone, isNilB])]

/-- The XOR-then-OR aggregated block test of a polynomial-time one-bit
indicator is polynomial-time: the input is a nested pair
`⟨⟨x, u⟩, v⟩`; block `i` is drawn from `u`, XORed bitwise with `v`
(truncating, `Complexity.xorD`), and tested paired with `x`.

**Proof sketch.** As `Complexity.polyTimeComputable_blockAnyTest`, with the
per-round test precomposed with the XOR mask: the loop state additionally
carries `v`, and the round's test input is
`pairEncode x (xorD (pairEncode v block))`
(`Complexity.polyTimeComputable_xorD`). -/
theorem polyTimeComputable_blockXorAnyTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun w =>
      [(List.range (a' * ((pairFstD (pairFstD w)).length + 1) ^ k')).any
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))))]) := by
  have hloop := polyTimeComputable_emitIter (polyTimeComputable_xorStep hV a k)
    polyTimeComputable_anyEmit a' k' 17 1 (length_xorStep_iterate V a k)
  have heq : (fun w => [(List.range (a' * ((pairFstD (pairFstD w)).length + 1) ^ k')).any
      (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
        (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))))]) =
      ((fun v => (List.range (a' * (v.length + 1) ^ k' + 1)).flatMap
        (fun i => anyEmit ((xorStep V a k)^[i] v))) ∘ xorInit a' k') := by
    funext w
    rw [Function.comp_apply, xorLoop_output V a k a' k' w]
  rw [heq]
  exact hloop.comp (polyTimeComputable_xorInit a' k')

end Complexity
```

## ===== TCSlib/Complexity/ClassNP/PolyTimeBlockMajority.lean =====

```
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassNP.PolyTimeBlockTests

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The majority-aggregated block test

The strict-majority customer of the bounded block-query loop
(`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`), split from
`TCSlib.Complexity.ClassNP.PolyTimeBlockTests` for size: the loop state
carries two unary vote counters, and at countdown exhaustion the emitted bit
is their strict comparison.

## Main definitions

None — the loop state, step, and chunk functions are private to this file.

## Main results

* `Complexity.polyTimeComputable_blockMajorityTest` — the strict-majority
  aggregated one-bit block test of a polynomial-time one-bit indicator is
  polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.4.1, repeated trials with a majority
  vote; Theorem 7.17.)
-/

namespace Complexity

open Turing

/-! #### The majority-aggregating loop -/

/-- One round of the majority-aggregating block loop on state
`pairEncode [true] (pairEncode countdown (pairEncode (pairEncode uT uF)
(pairEncode x rem)))`: push one vote onto the passed (`uT`) or failed (`uF`)
unary counter according to the indicator of the current block, drop the
block, decrement the countdown. -/
private noncomputable def majStep (V : Language Bool) (a k : ℕ) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then blockDone
  else if isNilB (pairFstD (pairSndD s)) then blockDone
  else
    pairEncode [true]
      (pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode
          (if MultiTapeTM.indicator V
              (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))) then
            pairEncode (true :: pairFstD (pairFstD (pairSndD (pairSndD s))))
              (pairSndD (pairFstD (pairSndD (pairSndD s))))
          else
            pairEncode (pairFstD (pairFstD (pairSndD (pairSndD s))))
              (true :: pairSndD (pairFstD (pairSndD (pairSndD s)))))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s))))))

/-- The chunk function: at countdown exhaustion, emit one bit comparing the
two unary vote counters strictly (`uF < uT`). -/
private def majEmit (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then []
  else if isNilB (pairFstD (pairSndD s)) then
    [!decide ((pairFstD (pairFstD (pairSndD (pairSndD s)))).length ≤
      (pairSndD (pairFstD (pairSndD (pairSndD s)))).length)]
  else []

/-- The initial state: live marker, unary countdown `a'·(n+1)^k'`, empty vote
counters, and the normalized input pair. -/
private def majInit (a' k' : ℕ) (z : List Bool) : List Bool :=
  pairEncode [true]
    (pairEncode (List.replicate (a' * ((pairFstD z).length + 1) ^ k') true)
      (pairEncode (pairEncode [] [])
        (pairEncode (pairFstD z) (pairSndD z))))

/-- The majority round is polynomial-time.
**Proof sketch.** As the OR round, with the flag update replaced by the
two-counter vote push, assembled from the same `FP` combinators. -/
private theorem polyTimeComputable_majStep {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z])) (a k : ℕ) :
    PolyTimeComputable (majStep V a k) := by
  have hcd : PolyTimeComputable (fun s => pairFstD (pairSndD s)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hzz : PolyTimeComputable (fun s => pairSndD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hacc : PolyTimeComputable (fun s => pairFstD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp hcd
  have hind : PolyTimeComputable (fun s =>
      [MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s))))]) :=
    hV.comp ((polyTimeComputable_sliceTakeAt a k).comp hzz)
  have huT : PolyTimeComputable (fun s =>
      pairFstD (pairFstD (pairSndD (pairSndD s)))) :=
    polyTimeComputable_pairFstD.comp hacc
  have huF : PolyTimeComputable (fun s =>
      pairSndD (pairFstD (pairSndD (pairSndD s)))) :=
    polyTimeComputable_pairSndD.comp hacc
  have hconsT : PolyTimeComputable (fun s =>
      true :: pairFstD (pairFstD (pairSndD (pairSndD s)))) :=
    (polyTimeComputable_prepend [true]).comp huT
  have hconsF : PolyTimeComputable (fun s =>
      true :: pairSndD (pairFstD (pairSndD (pairSndD s)))) :=
    (polyTimeComputable_prepend [true]).comp huF
  have hvote : PolyTimeComputable (fun s =>
      if MultiTapeTM.indicator V
          (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))) then
        pairEncode (true :: pairFstD (pairFstD (pairSndD (pairSndD s))))
          (pairSndD (pairFstD (pairSndD (pairSndD s))))
      else
        pairEncode (pairFstD (pairFstD (pairSndD (pairSndD s))))
          (true :: pairSndD (pairFstD (pairSndD (pairSndD s))))) :=
    polyTimeComputable_ite hind (hconsT.pairEncode huF) (huT.pairEncode hconsF)
  have hrest : PolyTimeComputable (fun s =>
      pairEncode ((pairFstD (pairSndD s)).drop 1)
        (pairEncode
          (if MultiTapeTM.indicator V
              (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))) then
            pairEncode (true :: pairFstD (pairFstD (pairSndD (pairSndD s))))
              (pairSndD (pairFstD (pairSndD (pairSndD s))))
          else
            pairEncode (pairFstD (pairFstD (pairSndD (pairSndD s))))
              (true :: pairSndD (pairFstD (pairSndD (pairSndD s)))))
          (sliceDropAt a k (pairSndD (pairSndD (pairSndD s)))))) :=
    (polyTimeComputable_tail.comp hcd).pairEncode
      (hvote.pairEncode ((polyTimeComputable_sliceDropAt a k).comp hzz))
  have hinner := polyTimeComputable_ite ht2 (polyTimeComputable_const blockDone)
    ((polyTimeComputable_const [true]).pairEncode hrest)
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const blockDone) hinner

/-- The majority chunk function is polynomial-time.
**Proof sketch.** The emitted bit is the negated pair length test
`Complexity.polyTimeComputable_lenLe` on the swapped vote counters, guarded
by the two emptiness tests. -/
private theorem polyTimeComputable_majEmit : PolyTimeComputable majEmit := by
  have hacc : PolyTimeComputable (fun s => pairFstD (pairSndD (pairSndD s))) :=
    polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have ht1 : PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairFstD
  have ht2 : PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
    polyTimeComputable_isNil.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have hswap : PolyTimeComputable (fun s =>
      pairEncode (pairSndD (pairFstD (pairSndD (pairSndD s))))
        (pairFstD (pairFstD (pairSndD (pairSndD s))))) :=
    (polyTimeComputable_pairSndD.comp hacc).pairEncode
      (polyTimeComputable_pairFstD.comp hacc)
  have hle : PolyTimeComputable (fun s =>
      [decide ((pairFstD (pairFstD (pairSndD (pairSndD s)))).length ≤
        (pairSndD (pairFstD (pairSndD (pairSndD s)))).length)]) := by
    have h := polyTimeComputable_lenLe.comp hswap
    have heq : (fun s =>
        [decide ((pairFstD (pairFstD (pairSndD (pairSndD s)))).length ≤
          (pairSndD (pairFstD (pairSndD (pairSndD s)))).length)]) =
        ((fun z => [decide ((pairSndD z).length ≤ (pairFstD z).length)]) ∘
          (fun s => pairEncode (pairSndD (pairFstD (pairSndD (pairSndD s))))
            (pairFstD (pairFstD (pairSndD (pairSndD s)))))) := by
      funext s
      simp [Function.comp]
    rw [heq]
    exact h
  exact polyTimeComputable_ite ht1 (polyTimeComputable_const [])
    (polyTimeComputable_ite ht2 (polyTimeComputable_not hle)
      (polyTimeComputable_const []))

private theorem polyTimeComputable_majInit (a' k' : ℕ) :
    PolyTimeComputable (majInit a' k') := by
  have hcnt : PolyTimeComputable
      (fun z => List.replicate (a' * ((pairFstD z).length + 1) ^ k') true) :=
    (polyTimeComputable_polyUnary a' k').comp polyTimeComputable_pairFstD
  exact (polyTimeComputable_const [true]).pairEncode
    (hcnt.pairEncode ((polyTimeComputable_const (pairEncode [] [])).pairEncode
      (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD)))

/-- The vote push grows the accumulator by at most four symbols. -/
private theorem length_majVote_le (b : Bool) (acc : List Bool) :
    (if b then pairEncode (true :: pairFstD acc) (pairSndD acc)
      else pairEncode (pairFstD acc) (true :: pairSndD acc)).length ≤ acc.length + 4 := by
  have hb := length_pair_components_le acc
  cases b with
  | true =>
    rw [if_pos rfl, length_pairEncode, List.length_cons]
    omega
  | false =>
    rw [if_neg (by simp), length_pairEncode, List.length_cons]
    omega

/-- One majority round respects the slack measure `|s| + 16·|countdown s|`.
**Proof sketch.** As the OR round's length bound, except that the vote push
can grow the state by a bounded constant (`length_majVote_le`); the countdown
loses one symbol per round, so sixteen units of slack per remaining round
absorb the growth. -/
private theorem length_majStep_le (V : Language Bool) (a k : ℕ) (s : List Bool) :
    (majStep V a k s).length +
      16 * (pairFstD (pairSndD (majStep V a k s))).length ≤
      max (s.length + 16 * (pairFstD (pairSndD s)).length) 2 := by
  unfold majStep
  cases h1 : isNilB (pairFstD s) with
  | true =>
    simp only [if_pos rfl]
    refine le_trans ?_ (le_max_right _ _)
    simp [blockDone, length_pairEncode, pairFstD_nil]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h2 : isNilB (pairFstD (pairSndD s)) with
    | true =>
      simp only [if_pos rfl]
      refine le_trans ?_ (le_max_right _ _)
      simp [blockDone, length_pairEncode, pairFstD_nil]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : pairFstD s ≠ [] := by simpa [isNilB] using h1
      have hcd : pairFstD (pairSndD s) ≠ [] := by simpa [isNilB] using h2
      have hs := eq_pairEncode_of_pairFstD_ne hf
      have ht := eq_pairEncode_of_pairFstD_ne hcd
      refine le_trans ?_ (le_max_left _ _)
      have hvote := length_majVote_le
        (MultiTapeTM.indicator V (sliceTakeAt a k (pairSndD (pairSndD (pairSndD s)))))
        (pairFstD (pairSndD (pairSndD s)))
      have hslice := length_sliceDropAt_le a k (pairSndD (pairSndD (pairSndD s)))
      have hslice' : (sliceDropAt a k (pairSndD (pairSndD (pairSndD s)))).length ≤
          (pairSndD (pairSndD (pairSndD s))).length + 2 := le_trans hslice (by omega)
      have hY := length_pair_components_le (pairSndD (pairSndD s))
      have hlens : s.length =
          2 * (pairFstD s).length + 2 +
            (2 * (pairFstD (pairSndD s)).length + 2 + (pairSndD (pairSndD s)).length) := by
        conv_lhs => rw [hs]
        rw [length_pairEncode]
        congr 2
        conv_lhs => rw [ht]
        rw [length_pairEncode]
      have hcd1 : 1 ≤ (pairFstD (pairSndD s)).length :=
        Nat.one_le_iff_ne_zero.mpr (by simpa [List.length_eq_zero_iff] using hcd)
      have hf1 : 1 ≤ (pairFstD s).length :=
        Nat.one_le_iff_ne_zero.mpr (by simpa [List.length_eq_zero_iff] using hf)
      simp only [pairSndD_pairEncode, pairFstD_pairEncode, length_pairEncode,
        List.length_drop, List.length_cons, List.length_nil]
      omega

/-- Orbit envelope for the majority loop. -/
private theorem length_majStep_iterate (V : Language Bool) (a k : ℕ)
    (w : List Bool) (i : ℕ) :
    ((majStep V a k)^[i] w).length ≤ 17 * (w.length + 1) ^ 1 := by
  have hmax : ((majStep V a k)^[i] w).length +
      16 * (pairFstD (pairSndD ((majStep V a k)^[i] w))).length ≤
      max (w.length + 16 * (pairFstD (pairSndD w)).length) 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_majStep_le V a k _) (max_le ih (le_max_right _ _))
  have h1 : (pairFstD (pairSndD w)).length ≤ w.length :=
    le_trans (length_pairFstD_le _) (length_pairSndD_le w)
  rw [pow_one]
  omega

/-- The done state is absorbing for the majority loop. -/
private theorem majStep_done (V : Language Bool) (a k : ℕ) :
    majStep V a k blockDone = blockDone := by
  unfold majStep
  simp [blockDone, isNilB]

/-- Closed form of the majority loop's orbit up to countdown exhaustion.
**Proof sketch.** As the OR orbit, with `List.countP` over `List.range`
replacing the OR: the vote push turns the passed counter `cT i` into
`cT i + 1` exactly when the current block's indicator holds
(`List.countP_append` at `List.range_succ`), and the failed counter is
`i - cT i` throughout. -/
private theorem majStep_orbit (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : i ≤ a' * ((pairFstD z).length + 1) ^ k') :
    (majStep V a k)^[i] (majInit a' k' z) =
      pairEncode [true]
        (pairEncode
          (List.replicate (a' * ((pairFstD z).length + 1) ^ k' - i) true)
          (pairEncode
            (pairEncode
              (List.replicate ((List.range i).countP (fun j =>
                MultiTapeTM.indicator V
                  (pairEncode (pairFstD z) (blockAt a k z j)))) true)
              (List.replicate (i - (List.range i).countP (fun j =>
                MultiTapeTM.indicator V
                  (pairEncode (pairFstD z) (blockAt a k z j)))) true))
            (pairEncode (pairFstD z)
              ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k)))))) := by
  induction i with
  | zero => simp [majInit]
  | succ i ih =>
    have hii : i ≤ a' * ((pairFstD z).length + 1) ^ k' := Nat.le_of_succ_le hi
    rw [Function.iterate_succ_apply', ih hii]
    have hcd : a' * ((pairFstD z).length + 1) ^ k' - i =
        (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) + 1 := by omega
    rw [hcd, List.replicate_succ]
    unfold majStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, if_neg (by simp [isNilB])]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode]
    have hle : (List.range i).countP (fun j =>
        MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) ≤ i :=
      le_trans List.countP_le_length (by simp)
    have hcnt : (List.range (i + 1)).countP (fun j =>
        MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
        (List.range i).countP (fun j =>
          MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) +
        (if MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
          then 1 else 0) := by
      rw [List.range_succ, List.countP_append]
      simp [List.countP_cons]
    have hdrop1 : (true :: List.replicate
        (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) true).drop 1 =
        List.replicate (a' * ((pairFstD z).length + 1) ^ k' - (i + 1)) true := rfl
    have hslice2 : sliceDropAt a k (pairEncode (pairFstD z)
        ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k)))) =
        pairEncode (pairFstD z)
          ((pairSndD z).drop ((i + 1) * (a * ((pairFstD z).length + 1) ^ k))) := by
      rw [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
      congr 2
      ring
    have hvoteq : (if MultiTapeTM.indicator V (sliceTakeAt a k (pairEncode (pairFstD z)
        ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))))) then
          pairEncode (true :: List.replicate ((List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
            (List.replicate (i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
        else
          pairEncode (List.replicate ((List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
            (true :: List.replicate (i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)) =
        pairEncode
          (List.replicate ((List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true)
          (List.replicate (i + 1 - (List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) true) := by
      rw [sliceTakeAt, pairFstD_pairEncode, pairSndD_pairEncode]
      cases hb : MultiTapeTM.indicator V (pairEncode (pairFstD z)
          (((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))).take
            (a * ((pairFstD z).length + 1) ^ k))) with
      | true =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = true := hb
        have hcT1 : (List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
            (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) + 1 := by
          rw [hcnt, hb']
          simp
        rw [if_pos rfl, hcT1, List.replicate_succ,
          show i + 1 - ((List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) + 1) =
            i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))
          from by omega]
      | false =>
        have hb' : MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i))
            = false := hb
        have hcT0 : (List.range (i + 1)).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
            (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) := by
          rw [hcnt, hb']
          simp
        rw [if_neg (by simp), hcT0,
          show i + 1 - (List.range i).countP (fun j =>
            MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) =
            (i - (List.range i).countP (fun j =>
              MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j)))) + 1
          from by omega, List.replicate_succ]
    rw [hdrop1, hslice2, hvoteq]

/-- Beyond exhaustion the majority orbit sits at the done state. -/
private theorem majStep_orbit_done (V : Language Bool) (a k a' k' : ℕ) (z : List Bool)
    {i : ℕ} (hi : a' * ((pairFstD z).length + 1) ^ k' < i) :
    (majStep V a k)^[i] (majInit a' k' z) = blockDone := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + (K + 1) := ⟨i - (K + 1), by omega⟩
  rw [Function.iterate_add_apply]
  have hend : (majStep V a k)^[K + 1] (majInit a' k' z) = blockDone := by
    rw [Function.iterate_succ_apply', majStep_orbit V a k a' k' z (le_refl K)]
    unfold majStep
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB, hK])]
  rw [hend]
  clear hi
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, majStep_done]

/-- The majority loop's machine-level output is the single aggregated bit.
**Proof sketch.** As the OR output lemma; at exhaustion the emitted
comparison of the unary counters `¬(cT ≤ K - cT)` is the strict majority
`K < 2·cT`, by `decide_not` and arithmetic. -/
private theorem majLoop_output (V : Language Bool) (a k a' k' : ℕ) (z : List Bool) :
    (List.range (a' * ((majInit a' k' z).length + 1) ^ k' + 1)).flatMap
      (fun i => majEmit ((majStep V a k)^[i] (majInit a' k' z))) =
      [decide (a' * ((pairFstD z).length + 1) ^ k' <
        2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
          (fun j => MultiTapeTM.indicator V
            (pairEncode (pairFstD z) (blockAt a k z j))))] := by
  set K := a' * ((pairFstD z).length + 1) ^ k' with hK
  have hlen : (pairFstD z).length ≤ (majInit a' k' z).length := by
    simp only [majInit, length_pairEncode, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  have hKN : K < a' * ((majInit a' k' z).length + 1) ^ k' + 1 := by
    have := Nat.mul_le_mul_left a'
      (Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) k')
    omega
  have hcT : (List.range K).countP (fun j =>
      MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z j))) ≤ K :=
    le_trans List.countP_le_length (by simp)
  refine flatMap_range_eq_single hKN (fun i _ => ?_)
  rcases Nat.lt_trichotomy i K with hiK | rfl | hiK
  · rw [if_neg (by omega), majStep_orbit V a k a' k' z (le_of_lt hiK)]
    unfold majEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_neg (by simp [isNilB]; omega)]
  · rw [if_pos rfl, majStep_orbit V a k a' k' z (le_refl K)]
    unfold majEmit
    rw [if_neg (by simp [isNilB]), pairSndD_pairEncode, pairFstD_pairEncode]
    rw [if_pos (by simp [isNilB]; omega)]
    simp only [pairSndD_pairEncode, pairFstD_pairEncode, List.length_replicate]
    congr 1
    rw [← decide_not]
    exact decide_eq_decide.mpr (by omega)
  · rw [if_neg (by omega), majStep_orbit_done V a k a' k' z hiK]
    unfold majEmit
    rw [if_pos (by simp [blockDone, isNilB])]

/-- The strict-majority-aggregated block test of a polynomial-time one-bit
indicator is polynomial-time.

**Proof sketch.** As `Complexity.polyTimeComputable_blockAnyTest`, with the
flag replaced by two unary vote counters (passed and failed blocks); at
countdown exhaustion the emitted bit is the strict comparison of their
lengths (`Complexity.polyTimeComputable_lenLe` after a `pairSwap`), which
equals `a'·(n+1)^k' < 2·(passed votes)` since the counts sum to the round
total. -/
theorem polyTimeComputable_blockMajorityTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun z =>
      [decide (a' * ((pairFstD z).length + 1) ^ k' <
        2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
          (fun i => MultiTapeTM.indicator V
            (pairEncode (pairFstD z) (blockAt a k z i))))]) := by
  have hloop := polyTimeComputable_emitIter (polyTimeComputable_majStep hV a k)
    polyTimeComputable_majEmit a' k' 17 1 (length_majStep_iterate V a k)
  have heq : (fun z => [decide (a' * ((pairFstD z).length + 1) ^ k' <
      2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
        (fun i => MultiTapeTM.indicator V
          (pairEncode (pairFstD z) (blockAt a k z i))))]) =
      ((fun w => (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap
        (fun i => majEmit ((majStep V a k)^[i] w))) ∘ majInit a' k') := by
    funext z
    rw [Function.comp_apply, majLoop_output V a k a' k' z]
  rw [heq]
  exact hloop.comp (polyTimeComputable_majInit a' k')

end Complexity
```

## ===== TCSlib/Complexity/ClassNP/PClosure.lean =====

```
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.CoNP
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassNP.PolyTimeBlockMajority

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Closure properties of `P`

The class `P` [AB09, Def 1.13] is closed under polynomial-time preimages (many-one
reductions), under the Boolean operations, and hence under Boolean functions of finitely
many tests. These facts are used tacitly throughout [AB09] (e.g. ch. 2, ch. 5, ch. 6); here
they are derived from the function class FP (`TCSlib.Complexity.ClassNP.PolyTimePairing`)
and the closure under complement (`Complexity.compl_mem_P`, `ClassNP/CoNP.lean`).

## Main definitions

None — this module only proves theorems about existing definitions.

## Main results

* `Complexity.mem_P_iff_polyTimeComputable` — `V ∈ P` iff its one-bit indicator is in FP;
  `Complexity.mem_P_of_test`, `Complexity.test_of_mem_P` — the same for Boolean tests.
* `Complexity.preimage_mem_P` — `P` is closed under polynomial-time preimages.
* `Complexity.inter_mem_P`, `Complexity.union_mem_P`, `Complexity.empty_mem_P`,
  `Complexity.univ_mem_P` — Boolean closure.
* `Complexity.mem_P_of_atoms` — `P` is closed under Boolean functions of finitely many
  tests.
* `Complexity.lenEq_mem_P`, `lenLe_mem_P`, `lenEq_preimage_mem_P`, `lenLe_preimage_mem_P`
  — length comparisons are in `P`.
* `Complexity.mem_P_of_blockAny`, `Complexity.mem_P_of_blockMajority`,
  `Complexity.mem_P_of_blockXorAny` — `P` is closed under running a `P`-decider on
  polynomially many polynomial-length blocks of the input and aggregating the answers
  (OR / strict majority / XOR-then-OR), the folklore repetition closures used tacitly
  by [AB09] ch. 7 (Theorems 7.8, 7.10, 7.17, 7.18); the machine engine is
  `TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6, Definition 1.13; §2.2.)
-/

namespace Complexity

open Turing

/-! ### `P` and polynomial-time functions -/

/-- `V ∈ P` iff its singleton indicator `x ↦ [1_V(x)]` is polynomial-time computable. -/
theorem mem_P_iff_polyTimeComputable {V : Language Bool} :
    V ∈ P ↔ PolyTimeComputable (fun x => [MultiTapeTM.indicator V x]) := by
  constructor
  · intro h
    obtain ⟨C, c, M, hM⟩ := mem_P_iff.mp h
    exact ⟨M, C, c, hM⟩
  · rintro ⟨M, C, c, hM⟩
    exact mem_P_iff.mpr ⟨C, c, M, hM⟩

/-- **`P` is closed under polynomial-time preimages**: if `V ∈ P` and `g` is
polynomial-time computable then `g⁻¹(V) ∈ P` (the decider of `V` run on `g x`). -/
theorem preimage_mem_P {V : Language Bool} {g : List Bool → List Bool} (hV : V ∈ P)
    (hg : PolyTimeComputable g) : g ⁻¹' V ∈ P :=
  mem_P_iff_polyTimeComputable.mpr ((mem_P_iff_polyTimeComputable.mp hV).comp hg)

/-- A language whose Boolean test is polynomial-time computable (as a one-bit output) is
in `P`. -/
theorem mem_P_of_test {b : List Bool → Bool} (h : PolyTimeComputable (fun z => [b z])) :
    {z | b z = true} ∈ P := by
  rw [mem_P_iff_polyTimeComputable]
  convert h using 2 with z
  by_cases hz : b z = true <;> simp [MultiTapeTM.indicator, hz]

/-- The Boolean test of a language in `P` is polynomial-time computable. -/
theorem test_of_mem_P {L : Language Bool} (h : L ∈ P) :
    PolyTimeComputable (fun z => [MultiTapeTM.indicator L z]) :=
  mem_P_iff_polyTimeComputable.mp h

/-! ### Boolean closure -/

/-- **`P` is closed under intersection.** -/
theorem inter_mem_P {L₁ L₂ : Language Bool} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) :
    {z | z ∈ L₁ ∧ z ∈ L₂} ∈ P := by
  have h := mem_P_of_test (polyTimeComputable_and (test_of_mem_P h₁) (test_of_mem_P h₂))
  convert h using 1
  ext z
  by_cases a : z ∈ L₁ <;> by_cases b : z ∈ L₂ <;> simp [MultiTapeTM.indicator, a, b]

/-- **`P` is closed under union** (branching on the first test). -/
theorem union_mem_P {L₁ L₂ : Language Bool} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) :
    {z | z ∈ L₁ ∨ z ∈ L₂} ∈ P := by
  have ht : PolyTimeComputable
      (fun z => [MultiTapeTM.indicator L₁ z || MultiTapeTM.indicator L₂ z]) := by
    convert polyTimeComputable_ite (test_of_mem_P h₁) (polyTimeComputable_const [true])
      (test_of_mem_P h₂) using 1
    funext z
    cases MultiTapeTM.indicator L₁ z <;> rfl
  convert mem_P_of_test ht using 1
  ext z
  by_cases a : z ∈ L₁ <;> by_cases b : z ∈ L₂ <;> simp [MultiTapeTM.indicator, a, b]

/-- The empty language is in `P`. -/
theorem empty_mem_P : ({_z | false = true} : Language Bool) ∈ P :=
  mem_P_of_test (polyTimeComputable_const [false])

/-- The full language is in `P`. -/
theorem univ_mem_P : ({_z | true = true} : Language Bool) ∈ P :=
  mem_P_of_test (polyTimeComputable_const [true])

/-- **`P` is closed under Boolean functions of finitely many tests**: if each test
`b i` decides a language in `P`, so does `z ↦ F (b · z)` for any `F`.

**Proof sketch.** The language is the finite union, over the valuations `β` with
`F β = true`, of the finite intersections `⋂ᵢ {z | b i z = β i}`; each set in the
intersection is a test language or its complement. -/
theorem mem_P_of_atoms {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → List Bool → Bool)
    (hb : ∀ i, ({z | b i z = true} : Language Bool) ∈ P) (F : (ι → Bool) → Bool) :
    ({z | F (fun i => b i z) = true} : Language Bool) ∈ P := by
  classical
  -- one valuation
  have hval : ∀ β : ι → Bool, ∀ s : Finset ι,
      ({z | ∀ i ∈ s, b i z = β i} : Language Bool) ∈ P := by
    intro β s
    induction s using Finset.induction_on with
    | empty => simpa using univ_mem_P
    | insert i s hi ih =>
      have hi' : ({z | b i z = β i} : Language Bool) ∈ P := by
        cases hβ : β i
        · have := compl_mem_P (hb i)
          convert this using 1
          ext z
          change b i z = false ↔ ¬ (b i z = true)
          simp
        · exact hb i
      have := inter_mem_P hi' ih
      convert this using 1
      ext z
      simp
  have hunion : ∀ s : Finset (ι → Bool),
      ({z | ∃ β ∈ s, ∀ i, b i z = β i} : Language Bool) ∈ P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using empty_mem_P
    | insert β s hβ ih =>
      have h1 := hval β Finset.univ
      have := union_mem_P h1 ih
      convert this using 1
      ext z
      change (∃ β' ∈ insert β s, ∀ i, b i z = β' i) ↔
        (∀ i ∈ Finset.univ, b i z = β i) ∨ (∃ β' ∈ s, ∀ i, b i z = β' i)
      simp
  have h := hunion (Finset.univ.filter fun β => F β = true)
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz; exact ⟨_, hz, fun i => rfl⟩
  · rintro ⟨β, hβ, hb'⟩
    have : (fun i => b i z) = β := funext hb'
    rw [this]; exact hβ

/-! ### Length comparisons -/

/-- The words whose two components under the total default projections
(`pairFstD`/`pairSndD`, both `[]` on malformed input) have equal length form a language
in `P`. Malformed words project to `([], [])` and are therefore members — e.g. `[]`
itself; the well-formed-pair corollaries below are unaffected (P0 round 1, finding 5). -/
theorem lenEq_mem_P : {z : List Bool | (pairFstD z).length = (pairSndD z).length} ∈ P := by
  have h := mem_P_of_test polyTimeComputable_lenEq
  simpa using h

/-- The words whose second default-projected component is at most as long as the first
form a language in `P` — with the same totalization as `Complexity.lenEq_mem_P`:
malformed words project to `([], [])` and are members. -/
theorem lenLe_mem_P : {z : List Bool | (pairSndD z).length ≤ (pairFstD z).length} ∈ P := by
  have h := mem_P_of_test polyTimeComputable_lenLe
  simpa using h

/-- Comparing the lengths of two polynomial-time computable strings is in `P`. -/
theorem lenEq_preimage_mem_P {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : {z | (f z).length = (g z).length} ∈ P := by
  have h := preimage_mem_P lenEq_mem_P (hf.pairEncode hg)
  simpa using h

/-- `|g z| ≤ |f z|` for polynomial-time `f`, `g` is decidable in `P`. -/
theorem lenLe_preimage_mem_P {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : {z | (g z).length ≤ (f z).length} ∈ P := by
  have h := preimage_mem_P lenLe_mem_P (hf.pairEncode hg)
  simpa using h

/-! ### Block-query closure

`P` is closed under running a `P`-decider on polynomially many fixed-size blocks of
the second component of a pair and aggregating the answers.  `blockAt a k z i` is the
`i`-th length-`a·(n+1)^k` block of `pairSndD z`, with `n = |pairFstD z|`; the block
count is `a'·(n+1)^k'`.  These are the folklore "repeat the machine polynomially many
times" closures that [AB09] ch. 7 uses tacitly (§7.3, Theorem 7.8; §7.4.1;
Theorems 7.17–7.18); the machine-level loop lives in
`TCSlib.Complexity.ClassNP.PolyTimeBlockLoop`. -/

/-- **`P` is closed under a polynomial block-OR**: if `V ∈ P` then so is the set of
pairs some of whose `a'·(n+1)^k'` blocks of length `a·(n+1)^k` passes `V`'s test,
paired with the first component. -/
theorem mem_P_of_blockAny {V : Language Bool} (hV : V ∈ P) (a k a' k' : ℕ) :
    {z : List Bool | ∃ i < a' * ((pairFstD z).length + 1) ^ k',
      pairEncode (pairFstD z) (blockAt a k z i) ∈ V} ∈ P := by
  have h := mem_P_of_test (polyTimeComputable_blockAnyTest (test_of_mem_P hV) a k a' k')
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, hmem⟩
    exact ⟨i, hi, by simp [MultiTapeTM.indicator, hmem]⟩
  · rintro ⟨i, hi, hbit⟩
    refine ⟨i, hi, ?_⟩
    by_contra hmem
    simp [MultiTapeTM.indicator, hmem] at hbit

/-- **`P` is closed under a polynomial block-majority**: if `V ∈ P` then so is the
set of pairs a strict majority of whose `a'·(n+1)^k'` blocks of length `a·(n+1)^k`
passes `V`'s test, paired with the first component. -/
theorem mem_P_of_blockMajority {V : Language Bool} (hV : V ∈ P) (a k a' k' : ℕ) :
    {z : List Bool | a' * ((pairFstD z).length + 1) ^ k' <
      2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i)))} ∈ P := by
  have h := mem_P_of_test (polyTimeComputable_blockMajorityTest (test_of_mem_P hV) a k a' k')
  convert h using 1
  ext z
  simp only [Set.mem_setOf_eq, decide_eq_true_eq]

/-- **`P` is closed under a polynomial XOR-shifted block-OR**: on a nested pair
`⟨⟨x, u⟩, v⟩`, if `V ∈ P` then so is the set of nested pairs some of whose
`a'·(|x|+1)^k'` blocks of `u` of length `a·(|x|+1)^k`, XORed bitwise with `v`
(truncating to the shorter word), passes `V`'s test paired with `x`. -/
theorem mem_P_of_blockXorAny {V : Language Bool} (hV : V ∈ P) (a k a' k' : ℕ) :
    {w : List Bool | ∃ i < a' * ((pairFstD (pairFstD w)).length + 1) ^ k',
      pairEncode (pairFstD (pairFstD w))
        (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i)) ∈ V} ∈ P := by
  have h := mem_P_of_test (polyTimeComputable_blockXorAnyTest (test_of_mem_P hV) a k a' k')
  convert h using 1
  ext w
  simp only [Set.mem_setOf_eq, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, hmem⟩
    exact ⟨i, hi, by simp [MultiTapeTM.indicator, hmem]⟩
  · rintro ⟨i, hi, hbit⟩
    refine ⟨i, hi, ?_⟩
    by_contra hmem
    simp [MultiTapeTM.indicator, hmem] at hbit

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
**Proof sketch.** The `some true`-set of the majority verifier is exactly the
block-majority closure `Complexity.mem_P_of_blockMajority` at `M`'s
`some true`-language `V₁` (the vote over block `i` is the indicator of
`sliceTake`-style block `i`, by the efficiency witness), and the `some
false`-set is its complement (`Complexity.compl_mem_P`).  The off-pair
freedom in the efficiency notion lets us use these sets verbatim. -/
theorem polyTimeModel_closedUnderMajority :
    ClosedUnderMajority polyTimeModel := by
  classical
  rintro M a k a' k' ⟨V₁, _, hV₁, _, hM⟩
  have hblock := mem_P_of_blockMajority hV₁ a k a' k'
  refine ⟨_, _, hblock, compl_mem_P hblock, fun x r => ?_⟩
  have hMt : ∀ s : List Bool, M x s = true ↔ Turing.pairEncode x s ∈ V₁ := by
    intro s
    have h := (hM x s).1
    simpa only [boolVerifier, Option.some.injEq] using h
  have hcount : ∀ l : List ℕ,
      l.countP (fun i => Turing.MultiTapeTM.indicator V₁
          (Turing.pairEncode x ((r.drop (i * (a * (x.length + 1) ^ k))).take
            (a * (x.length + 1) ^ k)))) =
        l.countP (fun i => M x ((r.drop (i * (a * (x.length + 1) ^ k))).take
          (a * (x.length + 1) ^ k))) := by
    intro l
    apply List.countP_congr
    intro i _
    have hi := hMt ((r.drop (i * (a * (x.length + 1) ^ k))).take (a * (x.length + 1) ^ k))
    by_cases hb : M x ((r.drop (i * (a * (x.length + 1) ^ k))).take
        (a * (x.length + 1) ^ k)) = true
    · simp [Turing.MultiTapeTM.indicator, hi.mp hb, hb]
    · have hnot : Turing.pairEncode x ((r.drop (i * (a * (x.length + 1) ^ k))).take
          (a * (x.length + 1) ^ k)) ∉ V₁ := fun hc => hb (hi.mpr hc)
      simp [Turing.MultiTapeTM.indicator, hnot, Bool.eq_false_iff.mpr hb]
  have hmem : Turing.pairEncode x r ∈
      {z : List Bool | a' * ((pairFstD z).length + 1) ^ k' <
        2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
          (fun i => Turing.MultiTapeTM.indicator V₁
            (Turing.pairEncode (pairFstD z) (blockAt a k z i)))} ↔
      majorityVerifier M (polyLen a k) (polyLen a' k') x r = true := by
    simp only [Set.mem_setOf_eq, pairFstD_pairEncode, pairSndD_pairEncode,
      majorityVerifier, polyLen, blockAt, decide_eq_true_eq]
    rw [hcount]
  constructor
  · constructor
    · intro h
      exact hmem.mpr (by simpa only [boolVerifier, Option.some.injEq] using h)
    · intro hw
      exact congrArg some (hmem.mp hw)
  · constructor
    · intro h hw
      have ht := hmem.mp hw
      have hf : majorityVerifier M (polyLen a k) (polyLen a' k') x r = false := by
        simpa only [boolVerifier, Option.some.injEq] using h
      exact absurd (ht.symm.trans hf) (by decide)
    · intro hc
      cases hb : majorityVerifier M (polyLen a k) (polyLen a' k') x r with
      | false => exact congrArg some hb
      | true => exact absurd (hmem.mpr hb) (fun hw => hc hw)

/-- Polynomial time is closed under polynomial `OR`-repetition.
**Proof sketch.** As for the majority closure, via the block-OR closure
`Complexity.mem_P_of_blockAny`: the `some true`-set of the `OR`-verifier is
the set of pairs some of whose random blocks puts the re-paired input in
`M`'s `some true`-language, and the `some false`-set is its complement. -/
theorem polyTimeModel_closedUnderAny : ClosedUnderAny polyTimeModel := by
  classical
  rintro M a k a' k' ⟨V₁, _, hV₁, _, hM⟩
  have hblock := mem_P_of_blockAny hV₁ a k a' k'
  refine ⟨_, _, hblock, compl_mem_P hblock, fun x r => ?_⟩
  have hMt : ∀ s : List Bool, M x s = true ↔ Turing.pairEncode x s ∈ V₁ := by
    intro s
    have h := (hM x s).1
    simpa only [boolVerifier, Option.some.injEq] using h
  have hmem : Turing.pairEncode x r ∈
      {z : List Bool | ∃ i < a' * ((pairFstD z).length + 1) ^ k',
        Turing.pairEncode (pairFstD z) (blockAt a k z i) ∈ V₁} ↔
      anyVerifier M (polyLen a k) (polyLen a' k') x r = true := by
    simp only [Set.mem_setOf_eq, pairFstD_pairEncode, pairSndD_pairEncode,
      anyVerifier, polyLen, blockAt, List.any_eq_true, List.mem_range]
    constructor
    · rintro ⟨i, hi, hv⟩
      exact ⟨i, hi, (hMt _).mpr hv⟩
    · rintro ⟨i, hi, hv⟩
      exact ⟨i, hi, (hMt _).mp hv⟩
  constructor
  · constructor
    · intro h
      exact hmem.mpr (by simpa only [boolVerifier, Option.some.injEq] using h)
    · intro hw
      exact congrArg some (hmem.mp hw)
  · constructor
    · intro h hw
      have ht := hmem.mp hw
      have hf : anyVerifier M (polyLen a k) (polyLen a' k') x r = false := by
        simpa only [boolVerifier, Option.some.injEq] using h
      exact absurd (ht.symm.trans hf) (by decide)
    · intro hc
      cases hb : anyVerifier M (polyLen a k) (polyLen a' k') x r with
      | false => exact congrArg some hb
      | true => exact absurd (hmem.mpr hb) (fun hw => hc hw)

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
`polyLen a' k' |x|` shift blocks, and XOR each with `v`.  Here
`shiftOrVerifier` uses `List.zipWith xor v block`, which is poly-time on
lists of *arbitrary* lengths and truncates to the shorter of `|v|` and the
block length; the exact-length witnesses quantified in `InSigma2` (where
`|v|` equals the block length) recover the book's equal-length bitwise XOR.
Run the `P`-verifier on each XORed block and `OR` the results — the
XOR-shifted block-OR closure `Complexity.mem_P_of_blockXorAny` at `M`'s
`some true`-language, on the nested pairing used by `Complexity.SigmaP`. -/
theorem polyTimeModel_closedUnderShiftOr :
    ClosedUnderShiftOr polyTimeModel := by
  classical
  rintro M a k a' k' ⟨V₁, _, hV₁, _, hM⟩
  have hblock := mem_P_of_blockXorAny hV₁ a k a' k'
  refine ⟨_, hblock, fun x u v => ?_⟩
  have hMt : ∀ s : List Bool, M x s = true ↔ Turing.pairEncode x s ∈ V₁ := by
    intro s
    have h := (hM x s).1
    simpa only [boolVerifier, Option.some.injEq] using h
  have hbridge : Turing.pairEncode (Turing.pairEncode x u) v ∈
      {w : List Bool | ∃ i < a' * ((pairFstD (pairFstD w)).length + 1) ^ k',
        Turing.pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i)) ∈ V₁} ↔
      ∃ i < a' * (x.length + 1) ^ k',
        Turing.pairEncode x (List.zipWith xor v
          ((u.drop (i * (a * (x.length + 1) ^ k))).take (a * (x.length + 1) ^ k))) ∈ V₁ := by
    simp only [Set.mem_setOf_eq, pairFstD_pairEncode, pairSndD_pairEncode, blockAt]
  have hleft : shiftOrVerifier M (polyLen a k) (polyLen a' k') x u v = true ↔
      ∃ i < a' * (x.length + 1) ^ k',
        Turing.pairEncode x (List.zipWith xor v
          ((u.drop (i * (a * (x.length + 1) ^ k))).take (a * (x.length + 1) ^ k))) ∈ V₁ := by
    simp only [shiftOrVerifier, polyLen, List.any_eq_true, List.mem_range]
    constructor
    · rintro ⟨i, hi, hv⟩
      exact ⟨i, hi, (hMt _).mp hv⟩
    · rintro ⟨i, hi, hv⟩
      exact ⟨i, hi, (hMt _).mpr hv⟩
  exact hleft.trans hbridge.symm

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
the probability factors.

**Proof sketch.** Combine the denominators by `2^{m₁+m₂} = 2^{m₁}·2^{m₂}`;
the numerators then agree via `Finset.card_bij` with the bijection
`(u, v) ↦ Fin.append u v` from pairs of accepted strings to accepted
concatenations.  `List.ofFn_fin_append` together with `List.take_left'` /
`List.drop_left'` matches the events on each side, injectivity is that of
`Fin.appendEquiv`, and surjectivity splits an arbitrary `r` by
`Fin.append_castAdd_natAdd`. -/
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

/-- The vote count over `K` blocks is at most `K`: it counts a subset of the
`K` block indices. -/
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
where `s` is the single-block success probability.

**Proof sketch.** Recursion on the number of blocks.  `blockCount_succ`
peels off the first block, and splitting the event by that block's outcome
gives a disjoint union (`randProb_or_disjoint`) whose branches factor into
first-block times remaining-blocks probabilities by `randProb_split`; the
recursive values recombine through Pascal's rule `Nat.choose_succ_succ`.
In the boundary case `j = K`, the branch asking for `K + 1` successes among
`K` blocks has probability zero by `blockCount_le`. -/
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
is needed, which keeps the whole development inside `ℚ`.)

**Proof sketch.** Partition the tail event by the exact vote count `j`
ranging over `{j ≤ K : K ≤ 2j}` (`randProb_mem_eq_sum`) and expand each
term with the binomial formula `randProb_blockCount`.  Since `s ≤ 1 − s`,
shifting exponents toward the balanced point bounds each
`s^j·(1−s)^{K−j}` by `(s(1−s))^{⌊K/2⌋}`, and summing *all* binomial
coefficients (`Nat.sum_range_choose`) leaves `2^K·(s(1−s))^{⌊K/2⌋}`.
Finally `s(1−s) ≤ 1/4 − ε²` and `2^K ≤ 2·4^{⌊K/2⌋}` reshape this into
`2·(1 − 4ε²)^{⌊K/2⌋}`. -/
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
`(1−x)^m·(1+mx) ≤ 1` by induction, and `1+mx ≥ 2`.

**Proof sketch.** The key inequality `(1−x)^{m'}·(1 + m'·x) ≤ 1` holds for
every `m'` by induction: the step rewrites
`(1−x)·(1 + (m'+1)·x) = 1 + m'·x − (m'+1)·x²` and drops the nonnegative
correction term.  At `m' = m` the hypothesis gives `1 + m·x ≥ 2`, and
nonlinear arithmetic turns `(1−x)^m·(1 + m·x) ≤ 1` into
`(1−x)^m ≤ 1/2`. -/
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
inclusions `ZPP ⊆ RP` and `ZPP ⊆ coRP` in [AB09, Thm 7.8].

**Proof sketch.** The `RP` witness is `anyVerifier` over the test
`M x r = some b`, run on two independent randomness blocks.  For `x ∈ L'`,
one run answers `some b` with probability at least `1/2`: a non-aborting
answer is never `some (!b)`, so `randProb_mono` lifts `Pr[¬abort] ≥ 1/2`
(from `randProb_not` and the abort bound) to `Pr[some b] ≥ 1/2`; the OR
fails only when both halves fail, a product `≤ (1/2)² = 1/4` by
`randProb_split` and `randProb_take`, so acceptance is `≥ 3/4 ≥ 2/3`.
For `x ∉ L'`, each half of the random string is a genuine length-`q`
string (`exists_ofFn_eq`) on which `hout` forbids the answer `some b`, so
the OR never accepts. -/
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

This is the identity for the **Las Vegas / abort-form** `ZPP` (`InZPP`: a
zero-error verifier that outputs `some b` or aborts with `none`, abort
probability `≤ 1/2`), **not** the book's expected-polynomial-time formulation
([AB09, Def 7.7]).  The two are equivalent by the standard truncate-and-repeat
bridge, which is not formalized here; until it is, read this as the abort-form
identity (the documented deviation, plan question CH7-Q2).

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

/-- The weak advantage is positive: both the cap `1/6` and the
inverse-polynomial `(n+1)^{-c}` are positive. -/
theorem weakAdv_pos (c n : ℕ) : 0 < weakAdv c n := by
  unfold weakAdv
  refine lt_min (by norm_num) ?_
  positivity

/-- The weak advantage never exceeds its cap `1/6`, keeping the weak success
threshold `1/2 + weakAdv c n` at most `2/3` at every length. -/
theorem weakAdv_le_sixth (c n : ℕ) : weakAdv c n ≤ 1/6 :=
  min_le_left _ _

/-- The weak advantage is inverse-polynomially large: `weakAdv c n` is at
least `(n+1)^{-c}/6`, since `(n+1)^{-c} ≤ 1` puts a sixth of it below both
branches of the `min`. -/
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
`2^{-((n+1)^d + 1)}`.

**Proof sketch.** Write `ε = weakAdv c n`; by `weakAdv_ge`,
`6ε ≥ (n+1)^{-c}`, whence `9·(n+1)^{2c}·(4ε²) ≥ 1` — the hypothesis
`m·x ≥ 1` of the Bernoulli bound, with `m = 9(n+1)^{2c}` and `x = 4ε²`.
The exponent `⌊56(n+1)^{2c+d}/2⌋ = 28(n+1)^{2c+d}` dominates
`9(n+1)^{2c}·((n+1)^d + 2)`, so `one_sub_pow_le_half_pow` yields
`(1 − 4ε²)^{⌊k/2⌋} ≤ (1/2)^{(n+1)^d + 2}`, and the leading factor `2`
absorbs one halving. -/
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

**Proof sketch.** Run the weak verifier `k(n) = 56·(n+1)^{2c+d}` times on
independent blocks of randomness and take the majority
(`majorityVerifier`).  In each of the two symmetric cases the failure
event is a vote-count tail — for `x ∈ L` the *false* votes reach `k/2`
(rephrased through the complementary vote-count identity), for `x ∉ L`
the *true* votes do — where each single block errs with probability
`≤ 1/2 − ε` with `ε = weakAdv c n ≥ (n+1)^{-c}/6`, so the elementary tail
estimate `randProb_tail_le` (built on the binomial distribution
`randProb_blockCount`) bounds it by `2·(1 − 4ε²)^{⌊k/2⌋}`; the arithmetic
crunch `weakAdv_tail_bound` (via the rational Bernoulli bound
`one_sub_pow_le_half_pow`) then gives `≤ 2^{-((n+1)^d + 1)}`.  (The book
computes with `e^{−2ε²k}`; the elementary `(4p(1−p))^{k/2}` bound proves
the same statement while keeping every quantity rational.) -/
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
probabilities: the map `r ↦ c ⊕ r` is an involution of `{0,1}^m`.

**Proof sketch.** The two counting sets are matched by
`Finset.card_nbij'` with `r ↦ (i ↦ c i xor r i)` as both the forward and
the inverse map: XOR by a fixed mask undoes itself, checked bitwise by
cases on the two bits, and `zipWith_ofFn` rewrites the list-level event
into the pointwise form the bijection transports. -/
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
exponent instead works at every length.)

**Proof sketch.** Two ingredients: `128·X ≤ 128^X` (induction on `X`) and
`A + 1 ≤ 2^A` (`Nat.lt_two_pow_self`).  Splitting
`2^{(A+7)·X} = (2^A)^X · 128^X`, the chain
`(19A+20)·X < 128(A+1)·X = (A+1)·(128·X) ≤ 2^A·(128·X) ≤ (2^A)^X·128^X`
closes the bound, using `2^A ≤ (2^A)^X` for `X ≥ 1` in the last step. -/
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
majority repetitions drive the error below `2^{-b(n+1)^e}`.

**Proof sketch.** With `x = 4·(1/6)² = 1/9` the Bernoulli hypothesis
`m·x ≥ 1` holds at `m = 9`, and the exponent
`⌊(18b+18)(n+1)^e/2⌋ = (9b+9)(n+1)^e` dominates `9·(b(n+1)^e + 1)`, so
`one_sub_pow_le_half_pow` bounds the power by `(1/2)^{b(n+1)^e + 1}`; the
leading factor `2` absorbs the extra halving. -/
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
repetitions.

**Proof sketch.** The witness is `majorityVerifier M₀` over
`K = (18b+18)·(n+1)^e` blocks of `q = a₀·(n+1)^{k₀}` bits.  In each of the
two symmetric cases the failure event is a vote-count tail: for `x ∈ L`
the *false* votes reach `K/2` (rephrased through the complementary
vote-count identity), for `x ∉ L` the *true* votes do.  A single block
errs with probability `≤ 1/3 = 1/2 − 1/6`, so `randProb_tail_le` bounds
the tail by `2·(1 − 4·(1/6)²)^{⌊K/2⌋}`, which `const_tail_bound` crunches
to `(1/2)^{b(n+1)^e}`. -/
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

/-- **`BPP ⊆ Σ₂ᵖ`**, the core of [AB09, Thm 7.18].

**Proof sketch.** *Setup*: amplify the `BPP` witness (`amplify_concrete`
at `b = a₀ + 7`, `e = k₀`) to error `2^{-T}`, `T = (a₀+7)·(n+1)^{k₀}`, on
`m` random bits; the `Σ₂` predicate is `shiftOrVerifier` with
`ks = (19a₀+20)·(n+1)^{k₀}` shift blocks, and two counting claims are
recorded: `ks < 2^T` (`shift_count_lt_two_pow`) and `m < T·ks`.
*Completeness* (`x ∈ L`, the probabilistic method): for each fixed `v`,
all `ks` independent shift blocks miss `v`'s translate with probability
`(1 − s)^{ks} ≤ 2^{-T·ks}` — the binomial distribution
`randProb_blockCount` at `j = 0` after the XOR-invariance
`randProb_xor_right` — so a union bound over the `2^m` choices of `v`
covers less than the `2^{ks·m}` shift tuples by the second claim, and
some concatenated shift string `u` hits every `v`.  *Soundness*
(`x ∉ L`, counting): each of the `ks` translates of the accepting set
has measure `≤ 2^{-T}` (`randProb_xor_left`), so by the first claim they
cover fewer than `2^m` strings, and `exists_notMem_of_card_lt` exhibits
an uncovered `v'` falsifying the assumed `∀ v` witness. -/
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

## ===== TCSlib/Complexity/TuringMachine/Build/Embed.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.StateRenaming

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: bank embedding (R1)

The general tape-embedding layer of the machine-construction library
(`machine-library-design.md` §12, R1): a verified routine on its own
`m`-tape set runs on any injectively selected subset of a `k`-tape host's
work tapes, cost unchanged, everything else framed. This is the §5
deferral promoted — the design deferred the general form "until a third
site needs it", and the third, fourth, and fifth sites have arrived (the
chapter-1/2 retrofit families, the Hennie–Stearns conversion, the
two-work-tape universal machine). **Scope, stated precisely** (round-1
note R9): `ι` selects whole distinct physical tapes with coordinates
intact — it does not multiplex several virtual tapes onto zones of one
physical tape, shrink the tape count, or alter the source input word; the
Hennie–Stearns and universal-machine consumers get their zone/virtual-input
representation layers separately, with this module supplying only the
fixed-physical-bank routine relocation. It is the generic form of the private
`emitterBank*`/`emitterP2*` relocation families of
`TCSlib.Complexity.TuringMachine.Build.Primitives`, of the 4A chain's
`clBank*`/`clSlot*` families, and of the retained-tape disciplines that
`Build/Loop.lean` and `Build/Wrappers.lean` carry internally.

**Status: statement skeleton (§12 statement phase).** The transformers and
configuration transports below are real definitions; every contract is
sorried, each with a proof sketch naming its fill obligations.

## Design

Per frozen decision 12.4 there are **two named transformers over one
shared private core** (`embedActionCore`), so each spec stays crisp and a
consumer cites whichever fits:

* `Turing.embedSilentTM` — the W1/capture flavor: the embedded routine's
  emissions are recorded on a designated host work tape `cap` outside the
  selected bank, and the host's physical output stays silent.
* `Turing.embedEmitTM` — the E2/forwarding flavor: emissions pass to the
  host's physical output verbatim.

The two **closed** transformers preserve the source state type and map
the source halt to the host halt; their lockstep is unguarded, holding at
every time with the step count preserved exactly. The round-1 audit
(finding R1) refuted the earlier claim that live-return dispatch could be
left to the seam combinator: a source whose final transition emits and
halts loses that emission either way — the closed embedding is halted
after it, and a seam exit at the sole live state dispatches *before* it.
The **returning** flavors below repair this with an explicit halt-to-live
adapter built into the action core: `Turing.embedSilentRetTM` and
`Turing.embedEmitRetTM` run the source on states `S ⊕ Unit`, execute every
source action **through the halting transition** — the final emission
included — and land in the live return anchor `Sum.inr ()`, which a seam
then consumes as its left exit (`Turing.captureAction`'s and
`Turing.emitterRightTM`'s halt-to-live discipline, now exported).
`Turing.captureAction`/`Turing.capture_run` and
`Turing.emitAction`/`Turing.emit_run` are the fixed-shape precursors
(last-tape capture, identity selection); their statements are untouched.

## Main definitions

* `Turing.embedSilentCfg`, `Turing.embedEmitCfg` — a source configuration
  transported along `ι : Fin m ↪ Fin k`, with the unselected host tapes
  carried as frame parameters.
* `Turing.embedSilentTM`, `Turing.embedEmitTM` — the two closed machine
  transformers.
* `Turing.embedSilentRetTM`, `Turing.embedEmitRetTM` — the two returning
  transformers (round-1 repair R1): source halts land in the live return
  anchor `Sum.inr ()`, with the halting transition executed in full.

## Main results

All sorried (statement phase):

* `Turing.embedSilentTM_runFrom`, `Turing.embedEmitTM_runFrom` — lockstep:
  the transported run is the transport of the source run, same step count.
* `Turing.embedSilentTM_frame`, `Turing.embedEmitTM_frame` — tapes outside
  `Set.range ι` byte-identical with heads unmoved, input position tracking
  the source, output per flavor.
* `Turing.embedSilentTM_visitedByTapeHead`,
  `Turing.embedEmitTM_visitedByTapeHead` (and `_frame` companions),
  `Turing.embedSilentTM_spaceUsedByTape_cap` — per-tape space: host tape
  `ι i` visits exactly the source's tape-`i` cells, unselected tapes visit
  nothing new, and the capture tape is bounded by the recorded output.
* `Turing.embedSilentRetTM_run`, `Turing.embedEmitRetTM_run` — the
  through-halt contracts: live lockstep, then the handover at the source's
  first halt, final emission and source residue preserved, with the return
  anchor reached first exactly there.
* `Turing.embedSilentRetTM_visitedByTapeHead`,
  `Turing.embedEmitRetTM_visitedByTapeHead` — the returning flavors visit
  exactly what the closed flavors visit, at every time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2; tape-subset simulations are the
  folklore of the §1.3/§1.7 robustness and simulation arguments.)
* [Bon26] É. Bonnet, *classical-complexity*, Lax Archive entry lax-434930,
  module `proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`, commit
  `0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0, examined
  2026-10-05. Design adaptation with nothing transcribed (different
  toolchain and machine model — TM2-style keyed stacks there, `FinTM`
  tapes with heads here): the bank-embedding shape is `StackRename`'s
  `rename_executes`.
-/

namespace Turing

variable {m k : ℕ} {S : Type*} {x : List Bool}

/-- The partial inverse of the tape selection: the source index that `ι`
sends to host tape `j`, or `none` when `j` is unselected. Injectivity of
`ι` makes the first `List.find?` hit the unique preimage. -/
private def embedSlot (ι : Fin m ↪ Fin k) (j : Fin k) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide (ι i = j)

/-- Searching at a selected tape returns its unique source index. -/
private lemma embedSlot_selected (ι : Fin m ↪ Fin k) (i : Fin m) :
    embedSlot ι (ι i) = some i := by
  unfold embedSlot
  cases hs : (List.finRange m).find? (fun j => decide (ι j = ι i)) with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp)
    simp at hn
  | some j =>
    have hj := List.find?_some hs
    have hji : j = i := ι.injective (of_decide_eq_true hj)
    subst j
    rfl

/-- Searching outside the selected bank returns no source index. -/
private lemma embedSlot_unselected (ι : Fin m ↪ Fin k) (j : Fin k)
    (hj : j ∉ Set.range ι) : embedSlot ι j = none := by
  unfold embedSlot
  rw [List.find?_eq_none]
  intro i _
  simp only [decide_eq_true_eq]
  exact fun hij => hj ⟨i, hij⟩

/-- The shared private core of the two embedding transformers (frozen
decision 12.4): transport one source action along `ι`, keeping the input
move and the successor state, performing the source's tape-`i` action on
host tape `ι i`, and leaving every unselected tape stationary and
unwritten — except that an emission is handled per the mode `sink`:
`sink = some cap` records it on host tape `cap` with a right move (the
capture discipline of `Turing.captureAction`) and keeps the host output
silent, while `sink = none` forwards it as the host's physical emission
(the discipline of `Turing.emitAction`). -/
private def embedActionCore (ι : Fin m ↪ Fin k) (sink : Option (Fin k))
    (a : Action m Bool S) : Action k Bool S where
  inputTape := a.inputTape
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => a.workTapes i
    | none =>
      match sink with
      | some cap =>
        if j = cap then
          match a.output with
          | some b => (some (some b), SignType.pos)
          | none => (none, 0)
        else (none, 0)
      | none => (none, 0)
  output :=
    match sink with
    | some _ => none
    | none => a.output
  state := a.state

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, suppressing flavor: same control state and input position,
source tape `i` sitting on host tape `ι i` (content and head), the
designated capture tape `cap` holding `pre ++ c.output` — the emissions
recorded so far after a pre-existing prefix — with its head one past that
word, every other unselected tape holding the ambient frame `tapes j` with
its head at `heads j`, and the host's physical output the untouched
`out₀`. Generic form of the `emitterBank*`/`clBank*` configuration
correspondences; for a source of `m` tapes in a host of `m + 1` with the
last tape selected as capture, it degenerates to `Turing.captureCfg` up to
the state embedding (round-1 restatement note: the specialization enlarges
the tape count by one — it is not `m = k`). [Bon26] -/
def embedSilentCfg (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) : Cfg k Bool S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none =>
      if j = cap then FinTM.bufferTape (pre ++ c.output) else tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none =>
      if j = cap then ((pre ++ c.output).length : ℤ) else heads j
  output := out₀

/-- A source configuration viewed inside a `k`-tape host along the
selection `ι`, forwarding flavor: same control state and input position,
source tape `i` on host tape `ι i`, every unselected tape holding the
ambient frame, and the host's physical output equal to the host's prior
output `pre` followed by everything the source has emitted. Generic form
of the `emitterP2*` relocation correspondences; at `ι = id` it is
`Turing.emitCfg` up to the state embedding. [Bon26] -/
def embedEmitCfg (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) : Cfg k Bool S x where
  state := c.state
  inputPos := c.inputPos
  workTapes := fun j =>
    match embedSlot ι j with
    | some i => c.workTapes i
    | none => tapes j
  workTapePos := fun j =>
    match embedSlot ι j with
    | some i => c.workTapePos i
    | none => heads j
  output := pre ++ c.output

/-- **R1, the suppressing embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, recording every emission on the designated host work tape `cap`
(intended outside `Set.range ι`) and emitting nothing physically — the
W1/capture flavor. States are preserved and the source halt is the host
halt; live return dispatch is the seam combinator's job. -/
def embedSilentTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S) : MultiTapeTM k Bool S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι (some cap) (M.tr q inp fun i => w (ι i))

/-- **R1, the forwarding embedding transformer** (design §12, decision
12.4; [Bon26]). Run the `m`-tape machine `M` on the host tapes selected by
`ι`, with every emission passed to the host's physical output verbatim —
the E2 flavor. States are preserved and the source halt is the host
halt. -/
def embedEmitTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S) :
    MultiTapeTM k Bool S where
  q₀ := M.q₀
  tr := fun q inp w =>
    embedActionCore ι none (M.tr q inp fun i => w (ι i))

/-- Applying the silent core commutes with configuration transport.
**Proof sketch.** Selected tapes perform the source action. Off-bank tapes
are stationary, except that capture appends the emitted bit at the old
word length. Input movement and successor control are copied verbatim. -/
private lemma embedSilent_apply (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (a : Action m Bool S) :
    (embedActionCore ι (some cap) a).apply
        (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            ← List.append_assoc, FinTM.bufferTape_append]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · funext j
    cases hs : embedSlot ι j with
    | some i => simp [embedActionCore, embedSilentCfg, Action.apply, hs]
    | none =>
      by_cases hj : j = cap
      · subst j
        cases ho : a.output <;>
          simp [embedActionCore, embedSilentCfg, Action.apply, hs, ho,
            Nat.cast_add, add_assoc]
      · simp [embedActionCore, embedSilentCfg, Action.apply, hs, hj]
  · simp [embedActionCore, embedSilentCfg, Action.apply]

/-- The silent host reads the source action and executes all its effects
in one step; halted configurations remain fixed on both sides. -/
private lemma embedSilent_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) :
    (embedSilentTM ι cap M).step (embedSilentCfg ι cap tapes heads pre out₀ c) =
      embedSilentCfg ι cap tapes heads pre out₀ (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedSilentCfg, hs]
  | some q =>
    rw [show (embedSilentCfg ι cap tapes heads pre out₀ c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedSilentCfg ι cap tapes heads pre out₀ c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedSilentCfg, embedSlot_selected]
    change (embedActionCore ι (some cap) (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedSilent_apply ι cap tapes heads pre out₀ c _

/-- **R1 lockstep, suppressing flavor** (spec, fill pending — design §12;
[Bon26], `rename_executes`). The transported run *is* the transport of the
source run, at every time and with the step count preserved exactly: `t`
host steps simulate `t` source steps. No liveness guard is needed — the
transformer preserves states, so a halted source transports to a halted
host and both runs stall together.

**Proof sketch.** One-step commutation plus
`Turing.MultiTapeTM.runFrom_comm_of_step`. For the step: a halted source
makes both sides the identity. For a live source state, the host reads the
source symbols through `ι` (the transport puts source tape `i` at `ι i`),
so the host applies `embedActionCore` of the very action the source
applies; componentwise, selected tapes update as the source's
(`Turing.Action.apply` through the `embedSlot` inverse, whose two
equations `embedSlot ι (ι i) = some i` and `embedSlot ι j = none` off the
range are the `List.find?` glue obligations), unselected tapes receive the
stationary no-write action, the capture tape appends the optional emission
at head `|pre ++ c.output|` (`Turing.FinTM.bufferTape_append`, exactly as
in `capture_apply`), silence keeps the output at `out₀`, and the states
agree. -/
theorem embedSilentTM_runFrom (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t =
      embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step
    (embedSilentCfg ι cap tapes heads pre out₀)
    (embedSilent_step ι cap M tapes heads pre out₀) c t

/-- **R1 frame, suppressing flavor** (spec, fill pending — design §12).
Along the whole transported run, every host tape outside the selected bank
and distinct from the capture tape is byte-identical to its ambient frame
with its head unmoved; the input position tracks the source's; and the
host's physical output stays `out₀` (output silence).

**Proof sketch.** Project the lockstep equation
`embedSilentTM_runFrom` componentwise: the transport's `workTapes`/
`workTapePos` at an unselected `j ≠ cap` are the frame parameters by the
`embedSlot` off-range equation, its `inputPos` is the source's, and its
`output` is `out₀` by definition. -/
theorem embedSilentTM_frame (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι → j ≠ cap →
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapes j
        = tapes j ∧
      ((embedSilentTM ι cap M).runFrom
          (embedSilentCfg ι cap tapes heads pre out₀ c) t).workTapePos j
        = heads j) ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedSilentTM ι cap M).runFrom
        (embedSilentCfg ι cap tapes heads pre out₀ c) t).output = out₀ := by
  rw [embedSilentTM_runFrom ι cap hcap]
  refine ⟨?_, rfl, rfl⟩
  intro j hj hjc
  simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]

/-- **R1 space, suppressing flavor, selected tapes** (spec, fill pending —
design §12: "cells visited on host tape `ι i` equal cells visited on
source tape `i`"). The visited set of host tape `ι i` up to time `t` is
exactly the source's visited set of tape `i`, so the per-tape space
agrees on the nose.

**Proof sketch.** Both visited sets are images of `Finset.range (t + 1)`
under the respective head trajectories
(`Turing.MultiTapeTM.visitedByTapeHead`), and the lockstep equation
`embedSilentTM_runFrom` makes the trajectories pointwise equal at `ι i`
via the transport's `workTapePos` clause and `embedSlot ι (ι i) = some i`.
The cardinality clause is `congrArg Finset.card`. -/
theorem embedSilentTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) (i : Fin m) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, suppressing flavor, unselected tapes** (spec, fill
pending — design §12: "unselected tapes visit nothing new"). A host tape
outside the selected bank and distinct from the capture tape visits
exactly the singleton of its initial head position, so its space usage is
one cell.

**Proof sketch.** By `embedSilentTM_frame` the head of such a tape never
moves, so the trajectory image collapses to `{heads j}`; the cardinality
clause is `Finset.card_singleton`. -/
theorem embedSilentTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (cap : Fin k) (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) (hjc : j ≠ cap) :
    (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} ∧
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j = 1 := by
  have hv : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedSilentTM_runFrom ι cap hcap]
    simp [embedSilentCfg, embedSlot_unselected ι j hj, hjc]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1 space, suppressing flavor, the capture tape** (spec, fill
pending — design §12; every unselected tape is accounted for, the capture
tape included). The capture tape's space usage up to time `t` is bounded
by the number of emissions recorded in that window plus one: the head
starts one past `pre ++ c.output` and advances right exactly once per
recorded emission.

**Proof sketch.** By lockstep the capture head position at time `t'` is
`|pre| + |(M.runFrom c t').output|`, which is nondecreasing in `t'` with
increments bounded by one emission per step; the visited set is therefore
the integer interval from the initial head to the final one, of
cardinality the output growth plus one
(`Turing.MultiTapeTM.output_prefix` gives the monotone growth).

**Fill appendix.** For the stated upper bound, the formal proof only
needs containment in this interval, followed by its cardinality. -/
theorem embedSilentTM_spaceUsedByTape_cap (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (embedSilentTM ι cap M).spaceUsedByTape
        (embedSilentCfg ι cap tapes heads pre out₀ c) t cap
      ≤ (M.runFrom c t).output.length - c.output.length + 1 := by
  have hgrowth : c.output.length ≤ (M.runFrom c t).output.length := by
    simpa using (M.output_prefix c (Nat.zero_le t)).length_le
  have hsub : (embedSilentTM ι cap M).visitedByTapeHead
      (embedSilentCfg ι cap tapes heads pre out₀ c) t cap ⊆
      Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    have hut : u ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
    have hlo : c.output.length ≤ (M.runFrom c u).output.length := by
      simpa using (M.output_prefix c (Nat.zero_le u)).length_le
    have hhi := (M.output_prefix c hut).length_le
    rw [embedSilentTM_runFrom ι cap hcap]
    simp only [embedSilentCfg, embedSlot_unselected ι cap hcap, ↓reduceIte,
      Finset.mem_Icc, List.length_append, Nat.cast_add]
    constructor <;> omega
  calc
    _ ≤ (Finset.Icc ((pre ++ c.output).length : ℤ)
        ((pre ++ (M.runFrom c t).output).length : ℤ)).card :=
      Finset.card_le_card hsub
    _ = (M.runFrom c t).output.length - c.output.length + 1 := by
      rw [Int.card_Icc]
      simp only [List.length_append, Nat.cast_add]
      omega

/-- Applying the forwarding core commutes with configuration transport:
selected tapes update identically, the frame stays fixed, and appending
the optional emission associates with the existing output prefix. -/
private lemma embedEmit_apply (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (a : Action m Bool S) :
    (embedActionCore ι none a).apply (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ ?_
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · funext j
    cases hs : embedSlot ι j <;>
      simp [embedActionCore, embedEmitCfg, Action.apply, hs]
  · simp [embedActionCore, embedEmitCfg, Action.apply, List.append_assoc]

/-- The forwarding host reads the same source action and executes it
completely in one step, including an emission on a halting transition. -/
private lemma embedEmit_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) :
    (embedEmitTM ι M).step (embedEmitCfg ι tapes heads pre c) =
      embedEmitCfg ι tapes heads pre (M.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedEmitCfg, hs]
  | some q =>
    rw [show (embedEmitCfg ι tapes heads pre c).state = some q from hs]
    dsimp only
    have hr : (fun i => (embedEmitCfg ι tapes heads pre c).workTapeSymbols
        (ι i)) = c.workTapeSymbols := by
      funext i
      simp [Cfg.workTapeSymbols, embedEmitCfg, embedSlot_selected]
    change (embedActionCore ι none (M.tr q c.inputSymbol _)).apply _ = _
    rw [hr]
    exact embedEmit_apply ι tapes heads pre c _

/-- **R1 lockstep, forwarding flavor** (spec, fill pending — design §12;
[Bon26], `rename_executes`). The transported run is the transport of the
source run, at every time and with the step count preserved exactly;
emissions are forwarded, so the host's output is `pre` followed by the
source's output at every instant (through the transport).

**Proof sketch.** As `embedSilentTM_runFrom`, with the capture clause
replaced by the output clause: the one-step commutation appends the
optional emission after `pre` (associativity of `++`, exactly as in
`emit_apply`), and `Turing.MultiTapeTM.runFrom_comm_of_step` iterates. -/
theorem embedEmitTM_runFrom (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (embedEmitTM ι M).runFrom (embedEmitCfg ι tapes heads pre c) t =
      embedEmitCfg ι tapes heads pre (M.runFrom c t) := by
  exact MultiTapeTM.runFrom_comm_of_step (embedEmitCfg ι tapes heads pre)
    (embedEmit_step ι M tapes heads pre) c t

/-- **R1 frame, forwarding flavor** (spec, fill pending — design §12).
Along the whole transported run, every host tape outside the selected
bank is byte-identical to its ambient frame with its head unmoved, the
input position tracks the source's, and the host's physical output is
`pre` followed by the source's output so far.

**Proof sketch.** Project `embedEmitTM_runFrom` componentwise, as in the
suppressing flavor; the output clause is the transport's definition. -/
theorem embedEmitTM_frame (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) :
    (∀ j : Fin k, j ∉ Set.range ι →
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapes j = tapes j ∧
      ((embedEmitTM ι M).runFrom
          (embedEmitCfg ι tapes heads pre c) t).workTapePos j = heads j) ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).inputPos
      = (M.runFrom c t).inputPos ∧
    ((embedEmitTM ι M).runFrom
        (embedEmitCfg ι tapes heads pre c) t).output
      = pre ++ (M.runFrom c t).output := by
  rw [embedEmitTM_runFrom]
  refine ⟨?_, rfl, rfl⟩
  intro j hj
  simp [embedEmitCfg, embedSlot_unselected ι j hj]

/-- **R1 space, forwarding flavor, selected tapes** (spec, fill pending —
design §12). The visited set of host tape `ι i` up to time `t` is exactly
the source's visited set of tape `i`; per-tape space agrees on the nose.

**Proof sketch.** As `embedSilentTM_visitedByTapeHead`: pointwise equal
head trajectories from `embedEmitTM_runFrom`, then image and
cardinality. -/
theorem embedEmitTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) (i : Fin m) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.visitedByTapeHead c t i ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t (ι i)
      = M.spaceUsedByTape c t i := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t (ι i) =
      M.visitedByTapeHead c t i := by
    unfold MultiTapeTM.visitedByTapeHead
    congr 1
    funext u
    rw [embedEmitTM_runFrom]
    simp [embedEmitCfg, embedSlot_selected]
  exact ⟨hv, congrArg Finset.card hv⟩

/-- **R1 space, forwarding flavor, unselected tapes** (spec, fill
pending — design §12). A host tape outside the selected bank visits
exactly the singleton of its initial head position; its space usage is
one cell.

**Proof sketch.** By `embedEmitTM_frame` the head never moves; collapse
the trajectory image to `{heads j}` and take cardinalities. -/
theorem embedEmitTM_visitedByTapeHead_frame (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ)
    (j : Fin k) (hj : j ∉ Set.range ι) :
    (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j = {heads j} ∧
    (embedEmitTM ι M).spaceUsedByTape
        (embedEmitCfg ι tapes heads pre c) t j = 1 := by
  have hv : (embedEmitTM ι M).visitedByTapeHead
      (embedEmitCfg ι tapes heads pre c) t j = {heads j} := by
    unfold MultiTapeTM.visitedByTapeHead
    simp_rw [embedEmitTM_runFrom]
    simp only [embedEmitCfg, embedSlot_unselected ι j hj]
    exact Finset.image_const ⟨0, by simp⟩ _
  refine ⟨hv, ?_⟩
  simp [MultiTapeTM.spaceUsedByTape, hv]

/-- **R1′, the returning suppressing embedding** (round-1 repair R1). As
`Turing.embedSilentTM`, on states `S ⊕ Unit`: live source states run the
capture-flavored core, but a source action whose successor is `none` lands
in the **live return anchor** `Sum.inr ()` — the halting transition is
executed in full, its emission recorded on `cap`, before control arrives at
the anchor (the `Turing.captureAction`/`Turing.emitterRightTM` halt-to-live
discipline, exported). The anchor itself idles (stationary, silent, live),
which is exactly what a seam combinator overrides as its left exit. -/
def embedSilentRetTM (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S) : MultiTapeTM k Bool (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι (some cap) a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- **R1′, the returning forwarding embedding** (round-1 repair R1). As
`Turing.embedEmitTM`, on states `S ⊕ Unit`, with source halts landing in
the live return anchor `Sum.inr ()` after the halting transition — its
forwarded emission included — has executed in full. -/
def embedEmitRetTM (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S) :
    MultiTapeTM k Bool (S ⊕ Unit) where
  q₀ := Sum.inl M.q₀
  tr := fun q inp w =>
    match q with
    | Sum.inl s =>
      let a := M.tr s inp fun i => w (ι i)
      let h := embedActionCore ι none a
      ⟨h.inputTape, h.workTapes, h.output,
        some (a.state.elim (Sum.inr ()) Sum.inl)⟩
    | Sum.inr _ => ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩

/-- Replace an action's optional successor by the live return encoding,
without changing any input, work-tape, or output effect. -/
private def embedReturnAction (a : Action k Bool S) : Action k Bool (S ⊕ Unit) :=
  ⟨a.inputTape, a.workTapes, a.output, some (a.state.elim (Sum.inr ()) Sum.inl)⟩

/-- Encode a closed host configuration with live left states and a live
right return anchor, preserving all four non-control fields. -/
private def embedReturnCfg (c : Cfg k Bool S x) : Cfg k Bool (S ⊕ Unit) x :=
  { c with state := some (c.state.elim (Sum.inr ()) Sum.inl) }

/-- At a live configuration, the return encoding is ordinary left state
mapping; at a halt it instead uses the live right anchor. -/
private lemma embedReturnCfg_live (c : Cfg k Bool S x) (hc : c.state ≠ none) :
    embedReturnCfg c = c.mapState Sum.inl := by
  cases hs : c.state with
  | none => exact (hc hs).elim
  | some q => simp [embedReturnCfg, Cfg.mapState, hs]

/-- Direct comparison of a closed host step with a returning host step.
**Proof sketch.** At a live left state, both hosts execute the same action
and only the successor encoding differs. At a closed halt, the returning
anchor's idle action preserves every non-control field, just as absorption
does on the closed side. No property of a source embedding is needed. -/
private lemma embedReturn_step (N : MultiTapeTM k Bool S)
    (R : MultiTapeTM k Bool (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Bool S x) :
    R.step (embedReturnCfg c) = embedReturnCfg (N.step c) := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [embedReturnCfg, hs, hidle, Action.apply]
  | some q =>
    rw [show (embedReturnCfg c).state = some (Sum.inl q) by
      simp [embedReturnCfg, hs]]
    dsimp only
    have hin : (embedReturnCfg c).inputSymbol = c.inputSymbol := rfl
    have hw : (embedReturnCfg c).workTapeSymbols = c.workTapeSymbols := rfl
    rw [hin, hw, hleft]
    rfl

/-- The silent returning step executes the entire transported source
action, then encodes its successor as a live left state or return anchor. -/
private lemma embedSilentRet_step (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (hc : c.state ≠ none) :
    (embedSilentRetTM ι cap M).step
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) =
      embedReturnCfg (embedSilentCfg ι cap tapes heads pre out₀ (M.step c)) := by
  have h := embedReturn_step (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c)
  rw [embedReturnCfg_live (embedSilentCfg ι cap tapes heads pre out₀ c) hc,
    embedSilent_step] at h
  exact h

/-- A live-step transport reaches the return anchor exactly at a positive
first halt, with all transported data intact.
**Proof sketch.** The initially live state and terminal halt imply positive
time. Induct over the strict live prefix, where the successor encoding is
ordinary left mapping. Execute the step from the last live configuration
separately; its halted successor encodes the return anchor. Earlier states
are left constructors, so none is the right anchor. -/
private lemma embedThroughHalt (M : MultiTapeTM m Bool S)
    (R : MultiTapeTM k Bool (S ⊕ Unit))
    (E : Cfg m Bool S x → Cfg k Bool S x)
    (hstate : ∀ d, (E d).state = d.state)
    (hstep : ∀ d, d.state ≠ none →
      R.step ((E d).mapState Sum.inl) = embedReturnCfg (E (M.step d)))
    (c : Cfg m Bool S x) (T : ℕ) (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl) ∧
    R.runFrom ((E c).mapState Sum.inl) T =
      { E (M.runFrom c T) with state := some (Sum.inr ()) } ∧
    ∀ t < T, (R.runFrom ((E c).mapState Sum.inl) t).state ≠
      some (Sum.inr ()) := by
  have hT : 0 < T := by
    by_contra hn
    have hz : T = 0 := by omega
    subst T
    exact hc (by simpa using hhalt)
  have hrun : ∀ t < T, R.runFrom ((E c).mapState Sum.inl) t =
      (E (M.runFrom c t)).mapState Sum.inl := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        hstep _ (hlive t (by omega)), ← MultiTapeTM.runFrom_succ_eq_step']
      apply embedReturnCfg_live
      rw [hstate]
      exact hlive _ ht
  refine ⟨hrun, ?_, ?_⟩
  · have hlast : T - 1 + 1 = T := by omega
    calc
      R.runFrom ((E c).mapState Sum.inl) T =
          R.step (R.runFrom ((E c).mapState Sum.inl) (T - 1)) :=
        (congrArg (R.runFrom ((E c).mapState Sum.inl)) hlast).symm.trans
          MultiTapeTM.runFrom_succ_eq_step'
      _ = embedReturnCfg (E (M.runFrom c T)) := by
        rw [hrun _ (by omega), hstep _ (hlive _ (by omega)),
          ← MultiTapeTM.runFrom_succ_eq_step', hlast]
      _ = _ := by simp [embedReturnCfg, hstate, hhalt]
  · intro t ht
    rw [hrun t ht]
    simp only [Cfg.mapState, hstate]
    cases (M.runFrom c t).state <;> simp

/-- **R1′ through-halt contract, suppressing flavor** (spec, fill pending —
round-1 repair R1): if the source first halts at time `T`, the returning
embedding runs in `Sum.inl`-lockstep through every live time and, at `T`,
sits at the **live return anchor** over the completed transport — the
halting transition's emission recorded on `cap`, the source tape residue
preserved on the selected bank, the frame untouched — having visited the
anchor first exactly there. The start must be **live** (`hc` — round-2
blocker: an initially halted `c` at `T = 0` satisfies the other hypotheses
vacuously while the handover state projection would demand
`none = some (Sum.inr ())`; under `hlive` **and** `hhalt` together, `hc` is
equivalent to `0 < T` — the forward direction uses `hhalt`, the reverse
`hlive 0` (round-3 finding 1 sharpened the earlier `hhalt`-only phrasing).
The smallest case is the round-1 counterexample cured: a one-state source
that emits and halts on its first transition lands at time `1` in
`Sum.inr ()` with `pre ++ [b]` on the capture tape (the audit's S8 check).

**Proof sketch.** Live times: the `Sum.inl` branch applies the very core of
`Turing.embedSilentTM`, so `embedSilentTM_runFrom`'s one-step commutation
transports verbatim under `Cfg.mapState Sum.inl` (`Cfg.mapState_apply`).
At the halting step, the source action's tape and capture effects are those
of the closed flavor — `Turing.FinTM.bufferTape_append` records the final
emission — while the successor `Option.elim` lands in `Sum.inr ()` instead
of `none`; the anchor cannot occur earlier because live source states map
into `Sum.inl`. Fill obligations, named: the two `Option.elim` successor
equations; the through-halt step case; the first-visit projection. -/
theorem embedSilentRetTM_run (ι : Fin m ↪ Fin k) (cap : Fin k)
    (hcap : cap ∉ Set.range ι) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t =
        (embedSilentCfg ι cap tapes heads pre out₀
          (M.runFrom c t)).mapState Sum.inl) ∧
    (embedSilentRetTM ι cap M).runFrom
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) T =
      { embedSilentCfg ι cap tapes heads pre out₀ (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedSilentRetTM ι cap M).runFrom
          ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl)
          t).state ≠ some (Sum.inr ()) := by
  exact embedThroughHalt M (embedSilentRetTM ι cap M)
    (embedSilentCfg ι cap tapes heads pre out₀) (fun _ => rfl)
    (embedSilentRet_step ι cap M tapes heads pre out₀) c T hc hlive hhalt

/-- The forwarding returning step preserves the complete source action,
including its final emission, and changes only the successor encoding. -/
private lemma embedEmitRet_step (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (hc : c.state ≠ none) :
    (embedEmitRetTM ι M).step ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) =
      embedReturnCfg (embedEmitCfg ι tapes heads pre (M.step c)) := by
  have h := embedReturn_step (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c)
  rw [embedReturnCfg_live (embedEmitCfg ι tapes heads pre c) hc, embedEmit_step] at h
  exact h

/-- **R1′ through-halt contract, forwarding flavor** (spec, fill pending —
round-1 repair R1): as `Turing.embedSilentRetTM_run` with the final
emission forwarded to the physical output (`pre ++ (M.runFrom c T).output`
at the anchor).

**Proof sketch.** As `embedSilentRetTM_run`, with the forwarding core: live
times transport under `Cfg.mapState Sum.inl` by `embedEmitTM_runFrom`'s
one-step commutation, the halting step applies the closed forwarding core's
tape and output effects (the final emission appended to the physical
output) with the successor `Option.elim` landing in `Sum.inr ()`, and the
first-visit clause projects from the `Sum.inl` lockstep. Fill obligations,
named: the successor equations; the through-halt step case; the
first-visit projection. -/
theorem embedEmitRetTM_run (ι : Fin m ↪ Fin k) (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (T : ℕ)
    (hc : c.state ≠ none)
    (hlive : ∀ t < T, (M.runFrom c t).state ≠ none)
    (hhalt : (M.runFrom c T).state = none) :
    (∀ t < T,
      (embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t =
        (embedEmitCfg ι tapes heads pre (M.runFrom c t)).mapState Sum.inl) ∧
    (embedEmitRetTM ι M).runFrom
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) T =
      { embedEmitCfg ι tapes heads pre (M.runFrom c T) with
          state := some (Sum.inr ()) } ∧
    ∀ t < T,
      ((embedEmitRetTM ι M).runFrom
          ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t).state ≠
        some (Sum.inr ()) := by
  exact embedThroughHalt M (embedEmitRetTM ι M)
    (embedEmitCfg ι tapes heads pre) (fun _ => rfl)
    (embedEmitRet_step ι M tapes heads pre) c T hc hlive hhalt

/-- Direct host comparison preserves every visited-head set, from any
initial configuration and for every finite horizon.
**Proof sketch.** Initially halted configurations stay halted on both
sides. From a live start, iterate the direct step comparison under the
return encoding, whose head positions are unchanged. Equality of the
head trajectories gives equality of their finite images. This uses no
termination hypothesis, source simulation, or capture-tape separation. -/
private lemma embedReturn_visited (N : MultiTapeTM k Bool S)
    (R : MultiTapeTM k Bool (S ⊕ Unit))
    (hleft : ∀ q inp work, R.tr (Sum.inl q) inp work =
      embedReturnAction (N.tr q inp work))
    (hidle : ∀ inp work, R.tr (Sum.inr ()) inp work =
      ⟨0, fun _ => (none, 0), none, some (Sum.inr ())⟩)
    (c : Cfg k Bool S x) (t : ℕ) (j : Fin k) :
    R.visitedByTapeHead (c.mapState Sum.inl) t j = N.visitedByTapeHead c t j := by
  unfold MultiTapeTM.visitedByTapeHead
  congr 1
  funext u
  by_cases hc : c.state = none
  · rw [R.runFrom_of_halt _ (by simp [Cfg.mapState, hc]), N.runFrom_of_halt _ hc]
    rfl
  · have hrun := MultiTapeTM.runFrom_comm_of_step embedReturnCfg
      (embedReturn_step N R hleft hidle) c u
    rw [embedReturnCfg_live c hc] at hrun
    exact congrArg (fun d => d.workTapePos j) hrun

/-- **R1′ space, suppressing flavor** (spec, fill pending — round-1 repair
R1): at every time and on every tape, the returning embedding's visited set
from the `Sum.inl`-mapped seam equals the closed embedding's from the plain
seam — the trajectories coincide through the halt, and afterwards one idles
at the live anchor while the other sits halted, both stationary.

**Proof sketch.** For `t` up to the first source halt, both machines apply
identical tape actions (`embedSilentRetTM_run`'s lockstep and the halting
step's shared core); beyond it, the anchor's idle action and the halted
absorption are both stationary, freezing both visited sets.

**Fill appendix.** The direct host comparison `embedReturn_visited`
handles initially halted and live starts separately. It uses neither
through-halt contract nor a capture-separation hypothesis. -/
theorem embedSilentRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k) (cap : Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (t : ℕ) (j : Fin k) :
    (embedSilentRetTM ι cap M).visitedByTapeHead
        ((embedSilentCfg ι cap tapes heads pre out₀ c).mapState Sum.inl) t j =
      (embedSilentTM ι cap M).visitedByTapeHead
        (embedSilentCfg ι cap tapes heads pre out₀ c) t j := by
  exact embedReturn_visited (embedSilentTM ι cap M) (embedSilentRetTM ι cap M)
    (fun _ _ _ => rfl) (fun _ _ => rfl)
    (embedSilentCfg ι cap tapes heads pre out₀ c) t j

/-- **R1′ space, forwarding flavor** (spec, fill pending — round-1 repair
R1): the forwarding analogue of
`Turing.embedSilentRetTM_visitedByTapeHead`.

**Proof sketch.** As the suppressing flavor: identical tape actions through
the first source halt, then the live idle and the halted absorption are
both stationary, freezing both visited sets — the trajectories coincide at
every time. -/
theorem embedEmitRetTM_visitedByTapeHead (ι : Fin m ↪ Fin k)
    (M : MultiTapeTM m Bool S)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (t : ℕ) (j : Fin k) :
    (embedEmitRetTM ι M).visitedByTapeHead
        ((embedEmitCfg ι tapes heads pre c).mapState Sum.inl) t j =
      (embedEmitTM ι M).visitedByTapeHead
        (embedEmitCfg ι tapes heads pre c) t j := by
  exact embedReturn_visited (embedEmitTM ι M) (embedEmitRetTM ι M)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (embedEmitCfg ι tapes heads pre c) t j


/-! ### Selected-tape exports (§13 Z1 rider, decision D-R1)

The retrofit inventories (`audits/retrofit-inventory/`) found, three times
independently, that no old-code R1 consumer can be proved from this file's
public surface: the frame lemmas cover only unselected tapes, and
`embedSlot_selected` is private. These four projections export the
selected-tape fields of the two configuration transports. They are
skeleton-time proofs (statement-phase additions flagged for the A-S1
audit): each is definitional at `embedSlot_selected`. -/

/-- The silent transport holds the source's tape `i` on host tape `ι i`. -/
theorem embedSilentCfg_selected_tape (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapes (ι i) =
      c.workTapes i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The silent transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedSilentCfg_selected_pos (ι : Fin m ↪ Fin k) (cap : Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre out₀ : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedSilentCfg ι cap tapes heads pre out₀ c).workTapePos (ι i) =
      c.workTapePos i := by
  simp [embedSilentCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape `i` on host tape
`ι i`. -/
theorem embedEmitCfg_selected_tape (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapes (ι i) = c.workTapes i := by
  simp [embedEmitCfg, embedSlot_selected]

/-- The forwarding transport holds the source's tape-`i` head on host tape
`ι i`. -/
theorem embedEmitCfg_selected_pos (ι : Fin m ↪ Fin k)
    (tapes : Fin k → ℤ → Option Bool) (heads : Fin k → ℤ)
    (pre : List Bool) (c : Cfg m Bool S x) (i : Fin m) :
    (embedEmitCfg ι tapes heads pre c).workTapePos (ι i) = c.workTapePos i := by
  simp [embedEmitCfg, embedSlot_selected]

end Turing
```
