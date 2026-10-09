# External audit pack — Chapter 7, Phase 1 (randomized computation, full statement surface)

Audits commit `03ed4568` on `complexity/arora-barak-ch7` (the Chapter-7 campaign
backfill; the **Lean statement surface is unchanged since `243b106b`** — `03ed4568`
adds only `AroraBarakChapter7Plan.md` and `scripts/ab_ch7_module_order.txt`). This is
the **statement-audit gate of the Chapter 7 campaign** (`AroraBarakChapter7Plan.md`),
covering the chapter's full statement surface in one phase (Tier A probability/spectral
facts, Tier B randomized classes over an abstract verifier model, and the
polynomial-time machine instantiation). Record findings in
`audits/ch7-phase1-findings.md`.

> **Unusual provenance — read first.** This gate is being run **retroactively**. The
> statement surface was previously reviewed by the maintainer over three fidelity
> rounds (approved at `4a683979`), and fill has already begun: of the headline
> results, Tier A and the Tier-B *abstract* class theorems are proved, and in the
> machine instantiation `polyTimeModel_closedUnderRace`/`_closedUnderAnswerIs`/
> `_closedUnderNot` and `inSigma2_polyTimeModel_iff` are proved. Those proofs are
> machine-checked; **do not review tactic scripts**. The product under audit is the
> **statements, their conventions, and (for the remaining `sorry`s) their proof
> sketches** — exactly as at any statement gate. The already-proved tactic proofs are
> re-audited at fill closure, not here. Please treat a proved statement no more gently
> than a sorried one: a *wrong but proved* statement is the worst outcome.

Source text: [AB09] ch. 7 (2007 web draft; the reference pair is under
`blueprint/src/references/`). Specifically: Lemma 7.5 (Schwartz-Zippel); Definition 7.4
(`BPP`/`RP`/`coRP`/`ZPP`); Theorem 7.8 (`ZPP = RP ∩ coRP`); Theorem 7.10 and its
Corollary 7.11 (error reduction); Lemma 7.9 (`BPP_{n^{-c}} = BPP`); Theorem 7.17
(`BPP ⊆ P/poly`, Adleman); Theorem 7.18 (`BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ`, Sipser-Gács); and §7.B
Lemma 7.37 (mixing), Theorem 7.38 (walks), Lemma 7.40, Theorem 7.41 (expander
Chernoff). The auditor must have the chapter at hand.

## Repository-side attestations (maintainer, remote machine — verify or challenge)

1. **Freeze.** The backfill commit `03ed4568` touches exactly two files —
   `AroraBarakChapter7Plan.md` (new) and `scripts/ab_ch7_module_order.txt` (new) —
   and **no `.lean` file** (verifiable by path enumeration of `243b106b..03ed4568`).
   The Chapter-7 Lean surface is therefore exactly as at `243b106b`. Upstream `main`
   (Boolean-analysis reorganization, Chapter 10, the design-adaptation policy row) was
   merged at `440e5034`; no upstream `.lean` file is modified by the Chapter-7 work
   (the ch7 modules are all new files under `Complexity/Expanders/` and
   `Complexity/Randomized/`).
2. **Elaboration.** Full 10-module fresh-olean sweep via `scripts/lean_check_tree.sh`
   in `scripts/ab_ch7_module_order.txt` order (Lean 4.25.0, Mathlib at the branch
   pin), **`lake build` not used** (banned on the campaign branch). Every module
   exits 0, emits a fresh `.olean`, and reports **zero `error:` lines**. Disclosure:
   `Adleman` and `PolyTimeModel` import upstream modules (`CircuitComplexity.PPoly`,
   `PolyHierarchy.*`, `ClassP.P`, `TuringMachine.Encoding`) that are not in the ch7
   order list; the scratch olean tree was seeded with the already-built dependency
   oleans so those imports resolve, then the two modules were re-elaborated fresh.
3. **Admissions inventory.** Exactly **7** `declaration uses 'sorry'` warnings
   tree-wide, all in the ch7 surface:
   * `Expanders/Chernoff.lean:66` — `walk_visits_concentration` (Theorem 7.41),
     **intentional and permanent** (book omits the proof; see Known deviations).
   * `Randomized/PolyTimeModel.lean` — six open fill targets:
     `polyTimeComputable_takePrefixByLen` (112), `…_dropPrefixByLen` (119),
     `polyTimeModel_closedUnderMajority` (243), `…_closedUnderAny` (250),
     `…_closedUnderShiftOr` (268), `polyTimeModel_verifierHasCircuits` (282).
   No other module admits a `sorry`. Each sorried declaration sits under a docstring
   whose **Proof sketch** names its intended construction.
4. **Policy conformance — a disclosed gap.** `scripts/style_lint.py` (the per-file
   policy linter adopted under this name at the main merge) reports **35 findings**
   over the ten ch7 files. They are **fill-style**, not statement-fidelity, and are
   scoped to fill closure, but are disclosed here in full honesty:
   * the majority are *landed proofs longer than the linter's threshold without a
     `**Proof sketch.**` docstring marker* (the sketches were written at skeleton time
     for the `sorry`s; several filled proofs did not re-assert the marker);
   * `Randomized/Classes.lean` is 1259 lines (> 1000; a facade split is a closure
     task);
   * a few helper theorems (`blockCount_le`, `weakAdv_pos/le_sixth/ge`) lack
     docstrings;
   * one **false positive**: `PolyTimeModel.lean:26` is prose inside the module
     docstring ("each `ClosedUnder…` hypothesis becomes a lemma about `P`"), which the
     regex misreads as a declaration named `about`.
   None of these alters a statement; the maintainer will clear them before the fill
   gate. Flag any that you believe *do* bear on fidelity.
5. **New surface inventory.** The ch7 surface is 10 new modules: Tier A —
   `Expanders/{Basic,Mixing,Walks,Chernoff}`, `Randomized/{SchwartzZippel,
   ErrorReduction}`; Tier B — `Randomized/{Classes,Adleman,SipserGacs}`; instantiation
   — `Randomized/PolyTimeModel`. The headline results are the ten theorems named under
   "Source text"; the modules additionally carry the supporting definitions
   (`IsSymmStochastic`, `lambda`, `VerifierModel`, `polyLen`, the class predicates
   `InBPP/InRP/InCoRP/InZPP/InSigma2/InPi2`, the verifier constructions, the `randProb`
   counting calculus) and their lemmas, all in namespace `Randomized` (Tier A defs
   model-free) building only on Mathlib and the frozen Chapter-1/2 + circuit surfaces.

## What is under audit

| Module | Key definitions | Headline statements |
|---|---|---|
| `Expanders/Basic.lean` | `IsSymmStochastic`, `uniform`, `toCLM`, `lambda` (λ(G)) | `mulVec_uniform`, `norm_mulVec_le_lambda`, `norm_toCLM_apply_le` (L²-contraction, Ex. 10), `lambda_nonneg`, `lambda_le_one` |
| `Expanders/Mixing.lean` | `indicator` | `inner_indicator_mulVec_le` (Expander Mixing Lemma, Lemma 7.37, normalized) |
| `Expanders/Walks.lean` | `unifMatrix`, `walkPMF`, `resMatrix`/`resVec` | `exists_decomposition` (Lemma 7.40), `walk_filter_sum`, `walk_all_mem_le` (expander-walk Theorem 7.38) |
| `Expanders/Chernoff.lean` | — | `walk_visits_concentration` (Theorem 7.41) — **statement-only** |
| `Randomized/SchwartzZippel.lean` | — | `schwartz_zippel` (Lemma 7.5) |
| `Randomized/ErrorReduction.lean` | `iidBernoulli`, `successCount` | `iidBernoulli_tail_le`, `iid_bernoulli_avg_concentration`, `majority_error_le` (Hoeffding + the corrected Cor 7.11 / Thm 7.10 calculation) |
| `Randomized/Classes.lean` | `randProb`, `polyLen`, `VerifierModel`, `boolVerifier`, `InBPP/InRP/InCoRP/InZPP`, `raceVerifier`/`majorityVerifier`/`anyVerifier`, the `ClosedUnder*` predicates, `blockCount`, `InBPPWeak/Strong` | `InBPP.compl`, `inZPP_iff_inRP_and_inCoRP` (Theorem 7.8), `bpp_error_reduction` + `inBPPWeak_iff_inBPP` (Theorem 7.10 / Lemma 7.9), the `randProb`/`blockCount`/tail calculus |
| `Randomized/Adleman.lean` | `VerifierHasCircuits` | `adleman` (Theorem 7.17) |
| `Randomized/SipserGacs.lean` | `InSigma2`, `InPi2`, `shiftOrVerifier`, `ClosedUnderShiftOr`, `amplify_concrete` | `bpp_subset_sigma2` (Theorem 7.18) + the XOR-shift / shift-count lemmas |
| `Randomized/PolyTimeModel.lean` | `polyTimeModel`, `sliceTake`/`sliceDrop`, `takePrefixByLen`/`dropPrefixByLen` | the `polyTimeModel_closedUnder*` discharges, `verifierHasCircuits`, `inSigma2_polyTimeModel_iff`, and the poly-time `sipser_gacs`/`adleman`/`zpp` corollaries |

## Known deviations (declared by the authors — verify they are benign, flag any others)

* **Probability is done in ℚ by exact counting**, not via the book's `e^{-2ε²k}`
  bound: `randProb` is a rational counting ratio over `{0,1}^m`; vote counts have an
  exact binomial distribution; the tail uses the elementary `2^K (s(1-s))^{⌊K/2⌋}`
  max-term estimate plus a rational Bernoulli inequality. Claim: the **class
  statements** (7.8/7.9/7.10/7.17/7.18) are the intended ones; the analytic bound is a
  dispensable intermediate. (CH7-Q1.)
* **`ZPP` is in Las Vegas / abort form** (output `some b` or abort `none`, abort
  probability bounded), not expected running time. (CH7-Q2.)
* **Theorem 7.41 is statement-only**, with a **sign-corrected** bound (book omits the
  proof; Gillman 1998 out of scope). (CH7-Q3.)
* **Error reduction carries the Cor 7.11 erratum correction** (the book's stated
  constant is off); the corrected two-sided bound is used.
* **Randomness/length schedules are explicit** `polyLen a k n = a·(n+1)^k`, never an
  abstract bounded function (the Chapter-2 Argument-A discipline).
* **Randomized classes are certificate-first over an abstract `VerifierModel`**, with
  the machine closures (`ClosedUnder*`, `VerifierHasCircuits`) as named hypotheses
  discharged only in `PolyTimeModel.lean` against `Complexity.P`. (CH7-Q4.)
* **`BPP ⊆ P/poly` uses the fixed-randomness circuit route** (`P_subset_PPoly` with the
  random bits hard-wired), not PTM snapshots.
* **λ(G)** is developed via the operator norm on the orthogonal complement of the
  all-ones vector over `EuclideanSpace`/`WithLp`.

## Specific questions for this phase

1. **CH7-Q1 (highest priority).** Is the ℚ-counting Chernoff development a *faithful*
   rendering of Theorems 7.10/7.17/7.18 and Lemma 7.9 — i.e. are the proved class
   statements the intended ones, with the particular tail constant immaterial? Look
   hardest for a statement that the counting route silently *weakens* (e.g. an
   amplification target reachable only because the ℚ bound is looser/tighter than
   `e^{-2ε²k}` at the used parameters).
2. **CH7-Q2.** Does the Las Vegas / abort-form `ZPP` (and `inZPP_iff_inRP_and_inCoRP`)
   state Theorem 7.8 faithfully, with no degenerate satisfaction (e.g. an abort bound
   that makes `ZPP` collapse to `P` or to everything)?
3. **CH7-Q3.** Is the sign-corrected Theorem 7.41 the intended inequality, and is a
   proof-free statement acceptable here?
4. **CH7-Q4.** Is `polyTimeModel` a faithful instantiation of "`M` is a polynomial-time
   TM" (Definition 7.4): efficiency as `P`-membership of the `some true`/`some false`
   sets of `M ∘ pairEncode`, and `EffTwoWitness` via the nested `SigmaP` pairing? And
   are the abstract `ClosedUnder*`/`VerifierHasCircuits` hypotheses *exactly* the
   book's implicit machine closures — neither too strong (smuggling the conclusion)
   nor too weak?
5. **Drafting-time doubts.** (a) `polyLen a k` degenerate cases (`a = 0`, `k = 0`,
   `n = 0`): do any amplification statements become vacuous or false at the boundary?
   (b) `InBPP.compl` and the `raceVerifier`/`majorityVerifier`/`anyVerifier`/
   `shiftOrVerifier` constructions — are the some-true/some-false set definitions and
   the `blockCount` vote predicate stated so that the intended event probability is
   what `randProb` computes (no off-by-one in `k(n) < 2·votes`, no block-misalignment
   in `(r.drop (i·p)).take p`)? (c) the Sipser-Gács balanced shift count
   `(19a₀+20)(n+1)^{k₀} < 2^{T(n)}` and `m < T·ks` — do the concrete parameter
   inequalities hold at every input length including `n = 0`?

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions,
theorem statements, and the `sorry`s' proof sketches. Proofs that exist are
machine-checked — do not review tactic scripts. Hunt for: **infidelity** (a definition
not meaning what [AB09] means), **trivialization** (a statement satisfiable for
degenerate reasons — a collapsing class, a vacuous probability event, an encoding that
empties a theorem), **unprovability** (a sorried statement false as stated, or subtly
weaker/stronger than intended), and **missing hypotheses** (finiteness, symmetry/
stochasticity, positivity, length side conditions).

For **every definition** in scope, restate it in your own mathematical English
*before* reading the docstring, compare against the cited [AB09] location, and report
any daylight. For **every sorried statement** (the Theorem-7.41 stub and the six
`PolyTimeModel` targets), argue in 2-5 sentences why it is true as literally stated, or
exhibit the problem. Attempt at least **3 adversarial instantiations** — e.g. the
`n = 0` input, a constant verifier, the complete graph / a disconnected graph for
λ(G), `a = 0` or `k = 0` schedules — plugged into the definitions. Propose any
machine-checkable sanity theorems you believe are missing. No blanket approval: an
empty findings table must be justified by the per-definition restatements.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = downstream work would build on a wrong statement;
**major** = statement fixable but materially misleading as is; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required. The gate closes
only on a round reporting **zero blockers and zero majors**.
