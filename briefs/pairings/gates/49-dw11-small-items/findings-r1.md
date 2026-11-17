# Gate 49 · round 1 findings (Codex), filed verbatim

Received from Seyoon as an upload, 2026-11-17 (`gate49-dw11-findings.md`).

---

# Gate 49 — DW-11 combined small items, round 1

**Overall: CLEAR. Open findings: 0 blockers, 0 majors, 4 minors, 0 notes.**

| PR | Verdict | Basis |
|---|---|---|
| #351 | **CLEAR** | Statements are true; approved admissions and frozen headers are preserved; evidence binds. Three documentation findings apply. |
| #352 | **CLEAR, audited jointly with #365** | Its historical duplication is a major defect, remedied by the verified #365 changes. G49-03 remains. |
| #365 | **CLEAR** | The generic lemma and five replacement proofs are correct, within scope, and adequately verified. G49-04 remains. |

These verdicts credit the repair at the audited #365 head. Historical defects closed by LE-grp1 or repaired by #365 are recorded separately below and excluded from the open counts. Merge order and snapshot adoption of #365 remain maintainer merge conditions outside this audit.

**Audited pins**

| Item | Commit |
|---|---|
| Exchange | `0d2bf0711bbb88e7fb5edf02b4699495d939c857` |
| Campaign records | `ab17e37feb00a677d69f6abd5ff7e427e3b9ef3c` |
| #351 head | `dfacac356ff1225aca4c900d81bbf2cabce7b499` |
| #351 merge | `cf7d28f7159b46033e8b8ae170954f9575e5d145` |
| #352 head | `92dea4f8126747ea7e816984349b9dbb789f0065` |
| #352 merge | `463f224414ab7615e54104be353bfcda9dfceda7` |
| #351/#352 merge base | `176cfd4a42ac3300d9b84f9045f7abcd0f52ef13` |
| #365 head | `5eaddd171bceccee917929e7f319ff9202994c59` |
| #365 base | `5aed99076d2bd4e5d6f831aed88739fc3ce475b6` |

Audit method: static mathematical and source review, independent git comparisons, checksum verification, and independent recount/binding checks of the recorded builds and probes. **I did not run Lean.** The maintainer's live olean files were unavailable; their archived maps and build records were checked. #357's proof bodies and the other excluded gates were not re-audited.

**Findings**

Paths below are relative to `TCSlib/Cryptography/` unless stated otherwise.

| # | Severity | PR · file · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G49-01 | minor | #351 · `Games/Relational.lean:16`; design r1 §2.2, “How the hypothesis expresses the ruling's wording” | The explanation overstates what the equal-test hypothesis establishes about preservation of an arbitrary relation. It need not give a coupling supported on that relation. The formal expectation theorem is sound. | The explicit counterexample below satisfies the per-call hypothesis but produces unrelated final states. The design's proposed separation argument fails because compatibility can force equality along a chain of relation edges. | Clarify that the formal contract preserves equality of compatible test expectations. Distinguish this from an actual relation-supported coupling; such a coupling is sufficient, but is not characterized by this hypothesis for arbitrary relations. Correct the design explanation in the same documentation follow-up. |
| G49-02 | minor | #351 · `Games/Relational.lean:116`, `expect_sample_rel` | The sampling-coupling result has neither a declaration-level source locator nor an explanation of its source relationship. It has a recognizable counterpart in the cited pRHL random-assignment rule. | The BGZ09 transcription, §4.1 [R-Rand], uses a bijection matching sampling distributions and establishing the postrelation. This declaration packages the uniform finite-type case as equality of real-valued expectations. | Add `[BGZ09, §4.1, rule R-Rand]` with an honest adaptation note explaining the different finite sample types and expectation formulation. |
| G49-03 | minor | #351/#352 · staged PR descriptions | Both descriptions still assign their audit to the bb1-sim gate under Q8. #352 additionally presents phase 2's superseded snapshot-#2 replay as its checks. | `pr351-description.md:29`; `pr352-description.md:14`, `:15`, `:27`. DW-11 supersedes Q8 for these PRs; the adopted #352 replay is phase 2b on snapshot #3, with state 1422/1422. | Update the gate assignment; identify phase 2b as #352's merge-bound evidence; link the #365 duplication repair. Preserve historical commit messages. |
| G49-04 | minor | #365 · PR description:10 and commit-1 wording | Unqualified “proof-only” is inaccurate for a change adding a public theorem. The addition is nevertheless explicitly disclosed and authorized, so this is a wording defect. | The PR description immediately lists `pow_val_bijective_of_prime_card`; independent source comparison confirms that addition, two module-docstring lines, and five changed proof bodies. | Describe the PR as a proof/refactor change with one new public lemma; qualify “proof-only” as applying to existing declarations. Clarify the historical wording in the PR body. |

**G49-01: exact counterexample to the explanatory claim**

Use one oracle with query and answer types `Unit`, and both state types `{0,1}`. Set

\[
R=\{(0,0),(1,0),(1,1)\}.
\]

Let every call of `impl₀` return `((),0)` deterministically and every call of `impl₁` return `((),1)`, independently of the initial states. Any test functions satisfying the stated compatibility premise obey

\[
g_0((),0)=g_1((),0)=g_0((),1)=g_1((),1).
\]

Consequently the per-call expectation equality holds for every related initial pair. Starting from `(0,0)`, a computation making one call ends in `(0,1)`, which is outside `R`. Since both final states are deterministic, no coupling of their laws can be supported on `R`. This refutes the stronger preservation interpretation, while leaving the declaration's precise expectation conclusion true.

**Correctness and edge cases**

- `expect_simulate_rel` is true by structural induction on the oracle computation, generalizing the initial states. At `pure a`, the conclusion is `hG a s t hst`. At a query, `simulate_query` and `expect_bind` turn each side into the expectation of the continuation's expectation. The induction hypothesis makes those two continuation functions compatible along `R`; the per-call hypothesis then equates their expectations. That hypothesis quantifies over individual calls and tests, not over the complete adversary computation. A bijective one-sample coupling supplies it through `expect_sample_rel`.
- If `R` is empty, or there is no related initial pair, `hst` cannot be supplied. For a query-free computation only `hG` and `hst` are needed. Functions ignoring final states still yield the claimed output-law equality. None of these cases introduces a hidden global simulation assumption.
- `prob_simulate_rel` correctly rewrites both probabilities using `prob_eq_expect` and applies the expectation theorem to identical output indicators. `classical` supplies decidability and does not strengthen a mathematical hypothesis. At #351 this proof intentionally depends on the admitted target; the recorded axiom trace identifies exactly that dependency.
- `expect_sample_rel` is true: `hf` and `hg` give `g₀ (f₀ u) = g₁ (f₁ (e u))` for each sample. The equivalence makes cardinalities equal and reindexes the uniform average. The `Nonempty` assumptions exclude zero-cardinality sampling. Its two `sorry`-phase targets are intentional; their later proof bodies are outside this audit.
- The averaging proof is correct: pointwise `−h ≤ f−g ≤ h`, monotonicity, and linearity give `−expect c h ≤ expect c f − expect c g ≤ expect c h`. Rewriting by `abs_le` proves the goal. The public statement and value binders `c f g h hb` match the ETT copy, up to the type-binder name. The lower-bound scaling step does not re-prove another existing expectation lemma.
- #352's exponent addition and negation laws hold also for `x = 1`, zero exponents, and prime order two. Reduction modulo the group order preserves powers; `pow_add` gives addition, and applying that law to `−a + a = 0` gives inversion. Its original bijection proof correctly uses order `p`, bounded representatives, and equal cardinalities.
- #365's generic lemma is valid for arbitrary universe levels and finite groups, without a commutativity assumption. Lagrange gives `g^p = 1`; primality and `g ≠ 1` give `orderOf g = p`. `pow_injOn_Iio_orderOf` and `ZMod.val_injective` establish injectivity; `ZMod.card` and `hM` give equal cardinalities and hence bijectivity. Primality excludes orders zero and one.
- All five #365 replacement proofs establish their unchanged statements. The target-group specialization uses `B.card_GT` and `B.pair_ne_one hx`; the source-group specialization uses `B.card_G` and `hg`. `BilinearGroup.factPrime` supplies both prime instances. The three exponent-law proofs directly use `pow_mod_card` with the correct group-cardinality field. The frozen target-group proof sketch remains accurate when its order/cardinality argument is delegated to the generic lemma.

**Fidelity, attribution, placement, and duplication**

Independent comparisons confirm the three #351 relational headers are byte-identical to design r1 §2.2. The averaging block matches the issued brief verbatim. The existing Games files and #352's frozen `Group.lean` receive only the permitted insertions. At the records tip, `Relational.lean` differs from #351 only in the two target bodies.

Masking exactly #365's five changed proof bodies leaves only two insertions: the new lemma block and its module-docstring bullet. Existing headers, declaration docstrings, imports, and all other text are preserved. No definition or reader obligation is introduced. The generic lemma's location outside `BilinearGroup`, within the existing pairing group module and topic namespace, is reasonable for its two local specializations; no existing general group-theory home was identified in TCSlib.

The BGZ09 locators §3.4, §4.1 `(=⟦⟧)` and Definition 5, §4.2 `⊨_φ`, and §5.2 Lemma 1 match the supplied transcriptions. So do Sho04 §1.1's bridging steps and §4.2 Game 2. The Deviation note honestly acknowledges the absence of the claimed general adversary-call rule in BGZ09. G49-01 concerns the library's explanatory interpretation, not fabrication of a source tag.

| Untagged declaration | Assessment |
|---|---|
| `expect_sample_rel` | G49-02: add the identifiable source relationship and adaptation note. |
| `abs_expect_sub_le_expect` | Technical consequence of the expectation API, expressly promoted from the ETT copy; no additional finding under the glue exception. |
| `pow_val_add` | Technical exponent-API glue; the issued brief explicitly permits omission of a source tag. |
| `pow_val_neg` | Technical consequence of the additive law; same exemption. |
| `pow_val_bijective_of_ne_one` | After #365, a specialization of the generic Mathlib-based lemma; the brief's glue exemption applies. A BB04 tag is not required merely because the target-group specialization has one. |

The ETT averaging duplicate has recorded human authorization Q6 and repayment under DL-40. The equality-state, abstraction, and budgeted simulation relatives have different hypotheses or conclusions; no additional unaccepted duplicate was identified. `pow_val_neg` consumes the additive API rather than re-deriving a modular-power theorem.

The original in-file bijection clone and inline Mathlib re-derivations merit major severity. #365 removes them: both bijections delegate to one generic lemma, injectivity consumes `pow_injOn_Iio_orderOf`, and all three modular-power chains consume `pow_mod_card`. No `Nat.mod_add_div` chain remains in `Group.lean`. No directly reusable Mathlib statement of the new prime-cardinality bijection was found; the disclosed unique-exponent theorem, noncanonical cyclic equivalences, and subgroup equivalences have different interfaces. The generic lemma's Mathlib glue note and absence of a standalone BB04 counterpart are accurate.

**Integrity, Rule 10, and evidence binding**

All required manifests pass: outer pack **15/15**, verification ZIP **66/66**, nested phase-1 **53/53**, phase-2 **698/698**, phase-2b **269/269**, and group-dedup **308/308**. The three nested ZIP hashes match the records' additional manifest. All **25** source hashes match; the **23** TCSlib source copies also match their named git blobs. All **36** bundle sections match their declared pack, archive, or git origins.

| Evidence | Independent checks and conclusion |
|---|---|
| Phase 1 → landing | Source/header/insertion checks and the recorded range-diffs account for the Games picks and group pick; LE-grp1 is the disclosed removal. Phase 1 is not mistaken for a merged-tree replay. |
| #351 phase 2 R1 → merge → snapshot #3 | All 181 source and log hashes bind to `dfacac35`; recorded return codes, errors, and warning counts check. Root and both Checks are present. The merge and R1 are Lean/config-equal. Every rebuilt object hash matches the adopted map `e9dfbfdd…`; the adoption diff is empty. |
| #352 phase 2b → merge → snapshot #4 | All 12 source and log hashes bind to tree `3029d8c3`. That tree was independently reproduced and is Lean/config-equal to merge `463f2244`. Every rebuilt object hash matches adopted map `6607620d…`; the adoption diff is empty. The earlier snapshot-#2 replay is superseded. |
| #365 commit 2 | All 22 source and log hashes bind to `5eaddd17`, with rc 0 and zero warnings/admissions in those build logs. Every rebuilt object hash matches output map `28677767…`. Independently recomputing all **1434** import-closure keys matches the archived incoming state at the actual base and the final state at the head. The per-module derived admission rows are unchanged. |
| #365 prospective merge | The records pin adds only the gate directory to `b31b77f7`; their Lean is equal. The #365 base is Lean/config-equal to that tip. Independently reproduced merge tree `319c9aa00884e38c4f4f73f7f98a718bf496186c` is Lean/config-equal to the audited head. |

Rule 10 evidence suffices:

- **#351:** `Probability` requests 36/36/35/35; `Relational` 53/53/52/52. Whole-source/probe bindings check. Canonical coe variants pass; the two strict `dist_apply` failures match the base and are attributed to the ruled notation exception. Controls verify six sealed negatives per harness with zero positive or stray failures; the explicit scan reports zero foreign unfolds.
- **#352:** phase 2b supplies the complete Group and Assumptions variants, 567/568/567/568 and 644/645/643/644, with zero errors. Whole-source/probe bindings check. Controls verify 34 sealed negatives per harness, with no positive or stray failure; the scan reports zero foreign unfolds.
- **#365:** the base/head coe-A probes bind to every source line. All 567 request rows, term-reader data, and closure counts agree, and passing logs are byte-identical; stored constants increase 82 → 83. The new lemma uses only Mathlib objects; the remaining changes consume theorem APIs and preserve the existing interface. Earlier controls establish harness sensitivity. Additional strict/B variants, paired controls, and consumer re-seals are not necessary for this exact change. The standard-axiom checks and deliberate sorry control also behave as reported.

One auxiliary runner source referenced by digest in #365's evidence was checked in the pinned records' `briefs/pairings/fills/bb1-sim/fill-final-r1/bb1-sim-fill-final-r1-phase2-evidence.zip`, entry `tools/runner_full_gated.py`; its SHA-256 is `9d72e87101bab0e14b18f073868c690124342cc81df5b833c4da02268d71708f`, exactly the recorded digest. No necessary evidence remains unverifiable. No further undisclosed code change was identified.

**Grades of BS-F01–BS-F13**

| Review finding | Audit grade and disposition |
|---|---|
| BS-F01 | **Major historically; closed by LE-grp1.** A directly usable public Mathlib lemma was re-proved. The original minor grade was too low. The duplicate is absent at #352's audited head. |
| BS-F02 | **Major historically; repaired by #365.** The public in-file proof clone required removal or recorded acceptance. An unfiled “ledger note” was insufficient. The Mathlib near-relative alone is not the reason for this grade. |
| BS-F03 | **Note, closed.** The resolution probe establishes the private/current and public/after-deletion resolutions and matching binders. |
| BS-F04 | **Note, closed for this gate.** R1 includes both omitted Checks. The issue-template correction remains housekeeping. |
| BS-F05 | **Note, closed.** R1 includes the 27 added downstream modules. |
| BS-F06 | **Note, ruled/pre-existing.** The strict coercion failure matches the base; canonical coe passes. |
| BS-F07 | **Note, pre-existing/out of scope.** Older reference formatting does not invalidate the new citations. |
| BS-F08 | **Note after the recorded ruling.** Account-key signatures do not identify the human maintainer; content provenance is provided by pinned material and the landing history. No unresolved authorship defect follows. |
| BS-F09 | **Note, resolved interaction.** The disclosed facade insertions merge cleanly; the later cleanup is outside scope. |
| BS-F10 | **Note.** Disclosed evidence/tool nits do not invalidate the final bound records. |
| BS-F11 | **Note.** The immutable pick's stale message is contextualized by LE-grp1 and the PR body. No history rewrite is warranted. |
| BS-F12 | **Note.** Trailers and signature-key observations are accurately limited; no independent cryptographic signature verification is claimed here. |
| BS-F13 | **Note, closed.** The failed probe is retained and its successful replacement is identified. It is not a library failure. |

**Notation glossary:** `R` is the audited state relation; `g₀`, `g₁` (also written `g_0`, `g_1`) are its compatible real-valued test functions; `()` is the unique `Unit` value. The counterexample's `0,1` are the two states. All remaining mathematical symbols and identifiers are the audited declarations' binders and APIs.
