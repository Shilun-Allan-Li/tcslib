# Gate 04 — S2b round 3 external audit findings

**Verdict: DO NOT CLOSE.**  
**0 blockers, 1 major, 1 minor.**

The specific `passthrough_apply` repair is correct, all nine new equation lemmas state their definitions faithfully, and the timeout wording is repaired. The remaining major concerns the claimed completeness of the no-unfolding repair: the final commit adds `Games/Probability.lean` to the change set, but the seal omits that file, whose existing `expect_bind` proof still reads the foreign definition `OracleComp.bind` through `rfl`. This is a publication-policy defect, not a false theorem or a new admission.

**Audited head:** `27ae72da62119ebdde380b8cb2d8c183b59fa2bf`, [PR #195](https://github.com/Shilun-Allan-Li/tcslib/pull/195).  
**Comparison head:** `243598b7cb0c3fdd50b22a92a011f1b77f55c8c6` (round 2).  
**Bundle:** 23 sections; SHA-256 `b5f872b0498893aa96eed6c437acfabdd2827a98ba02317cb7fc6d7b86f729ed`. No expected round 3 bundle digest was supplied.  
**Source PDF:** Pass–shelat, third edition, January 2010; SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`.

The seven supplied Lean files have Git blob hashes matching the pinned head. The repair diff reverse-applies cleanly, and the reconstructed earlier files match its old blob prefixes. GitHub's pinned comparison confirms exactly the two reported commits and seven changed files. Paths below are relative to `TCSlib/Cryptography/` unless stated otherwise; line numbers refer to individual extracted files.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R3-01 | **Major** | `Games/Probability.lean:123–127` · `ProbComp.expect_bind`; `evidence-r3/seal.py.txt:10–40`; `resolutions-r2.md` · R2-01/F02 | The extended seal covers every consumer file in the change set and establishes the complete F02 repair. | The `pure` case is still `rfl`. Its left side contains `expect ((OracleComp.pure a).bind f) g`; reaching `expect (f a) g` requires reducing `OracleComp.bind`, defined in `Games/OracleComp.lean:99–101`. The proof cites no equation for that step. `Probability.lean` is absent from the seal table and output. The seal is recorded at `81e4f4e2`; this file first joins the PR's change set in the following commit, `27ae72da`. The disclosed exception concerns older ch. 2–4 proofs in `PRF.lean`, not this S2a proof. | Replace the base case with `simp only [OracleComp.pure_bind, expect_pure]`; include `Games/Probability.lean` with `OracleComp.bind` sealed; rerun the consumer seal at the final repaired head. State the remaining inherited exclusions explicitly instead of claiming whole-change-set coverage. |
| R3-02 | Minor | `briefs/pass-shelat-ch5-8/gates/04-s2b/pack-r3.md:30` · axiom attestation | The public-theorem printout covers “the 25 changed files.” | `changed-files.txt`, `lint.log`, the axiom-log header, and the pinned comparison all identify **26** Lean files after excluding the root `TCSlib.lean` facade. `Games/Probability.lean` is the additional file. The log itself has 410 distinct theorem entries, 406 without `sorryAx`; its numerical accounting is consistent. | Change “25” to “26”; retain the log's explicit baseline, facade exclusion, and 410/406 counts. |

R3-01 is inherited S2a code, not a newly broken mathematical statement. It is nevertheless an undisclosed exception to the asserted F02 closure, of exactly the same kind as the `simulate_bind` base case repaired in this round. I retain F02's major classification for incomplete compliance with that explicit publication requirement. I do not count the missing seal row again as a separate finding.

The proposed source repair is:

```lean
  | pure a => simp only [OracleComp.pure_bind, expect_pure]
```

The first lemma rewrites `(OracleComp.pure a).bind f` to `f a`; the second rewrites the right-hand expectation on a return to `expect (f a) g`. Both sides then coincide. This is a source-level repair, **not** a patch compiled in this audit. No fresh seal failure or successful repair compilation is claimed.

## Required resolution lines

R2-01: **fixed** — the specific `QueryImpl.passthrough_apply` defect is repaired by `rw [passthrough, ofComp_apply, OracleComp.call_bind]`. Only its own definition is unfolded. The broader assertion of complete consumer coverage is addressed separately in R3-01.

R2-02: **fixed** — every previously missing evidence category is now attached, including replay order, axioms, lint, check 8, seal script/output, the round 1 review, and the duplication ledger. DL-9 explicitly includes S2b's public `take_drop_ofFn_blocks` duplicate. Attachment completeness does not establish the stronger seal-coverage claim.

R2-03: **fixed** — the structure, `call`, `finish`, and their equation-lemma descriptions now distinguish a return at zero remaining budget from an additional query that invokes the timeout.

F02: **not resolved** — the named repaired proofs and new equations are adequate, but `Probability.expect_bind` remains an unrecorded foreign-definition read in the enlarged change set; see R3-01.

N2: **fixed** — `check8.log` records 0 failures and 0 warnings over the 14 `Games/` files. The new projection, sampling and implementation equations are genuine defining equations, not merely similarly named consequences.

N7: **not resolved** — seal evidence is now supplied and supports its 13 configured rows, but it omits the additional consumer above and predates the final commit. The required final-head coverage remains incomplete; see R3-01.

The previously recorded N3 and N4 debts are not represented as completed: the protocol-view documentation remains scheduled for integration, and the duplicate is scheduled for the ch. 2–4 cleanup.

## Changed proofs and equations

All nine new public lemmas were compared directly with their definition bodies:

| Declaration group | Assessment |
|---|---|
| `OracleSpec.add_dom_inl`, `add_dom_inr`, `add_rng_inl`, `add_rng_inr` | Exactly the four projections of the disjoint-union specification. `rfl` reads the local definition and core `Sum.elim`; it adds no behavioral assumption. |
| `ProbComp.sampleFin_eq` | Exactly one query to the indicated sampling oracle, with the return constructor as continuation. |
| `ProbComp.sample_eq` | Exactly the defining map from the sampled finite index through the cardinality cast and inverse enumeration. It is an equation of computations, not an unsupported distributional identification. |
| `queryImpl_def` | Exactly the dependent function type in the local `QueryImpl` definition. |
| `OracleAdversary.boundedBy_iff` | Exactly the universal query bound over coin strings; the underlying tree predicate is left intact. |
| `lazyDist_apply` | Exactly evaluation of the selected tree with the supplied stream and empty initial query list; no reduction of the imported `evalLazy` definition is needed. |

None adds a `simp` attribute or an admission. The new equations' docstrings describe those same formulas.

The repaired consumers preserve their statements and use the published foreign interfaces:

- **`Simulate.lean`:** `simulate_bind`, `simulate_comp` and `simulate_withLog` use `pure_bind` in their base cases. Their query cases use sequencing/simulation equations and associativity. Unfolding `QueryImpl.comp` and `QueryImpl.withLog` is local to this file. `simulate_call` uses `bind_pure` and `call_bind`. `simulate_costBoundedBy` obtains the query-budget conjunction through `costBoundedBy_query`, combines budgets through `CostBoundedBy.bind`, and uses the established inequality to cancel natural subtraction.
- **`PRF.lean`:** `acceptProb_random_eq_lazy` uses the probability, sampler, distinguisher and boundedness interfaces before applying lazy sampling. The order of the two product averages is consistent. `buildTree_boundedBy` uses the four local build-tree cases and the imported bound lemmas; `toOracleAdversary_boundedBy` uses the new outer boundedness characterization. The private zero-query lemma uses `prfAdv_eq` and `QueryTree.eval_ret`; its unfolds of `toOracleAdversary` and `buildTree` are local.

The revised probability comparison still expresses the table/lazy-sampling identity in Pass–shelat §3.8.1, book p. 95 (PDF p. 107). No theorem or definition acquires a different mathematical meaning in this repair diff. In particular, all four deferred efficiency statements and their `sorry` bodies are unchanged.

## Timeout wording and disclosed boundary

The corrected timeout descriptions agree with the actual cases of `buildComp`: at budget zero, `.ret a` becomes `.pure a`, while `.query i x` becomes `.pure timeout`. A successor-budget query consumes one unit and recurses. Thus the bounds remain at most `perCall(n)` queries and `perCall(n) + 1` handler activations, with the analogous finalization bound. The distinction between componentwise defaulting in `PolyHandler` and joint defaulting in `InteractiveHandler` is preserved.

The **PRF exclusion is real and is not silently certified here**. For example, `OracleEnsemble.random_O` still reduces the imported `randomFunction` (`PRF.lean:142–144`); `OracleEnsemble.Indist.refl` uses `simp [distAdv]` (`:325`); `prfAdv_toOracleAdversary` still closes by `rfl` (`:398–402`); and the old decoder/GGM proofs read imported helpers. Those sites are unchanged by this round and are outside the definitions listed in the PRF seal row. Also, `PRF` itself is defined in `PRF.lean`: reading that local definition is not a foreign-definition violation.

The table should not be read as a certificate for all inherited ch. 2–4 consumers either. For example, unchanged proofs in `SubHybrids.lean` explicitly rewrite `acceptProb` and unfold `distAdv`; that file has no seal row. Its new `lazyDist_apply` equation is clean. These older proofs belong in the disclosed cleanup scope, whereas the omitted S2a `Probability.expect_bind` is the additional unresolved case identified above. Successful irreducibility checks also do not replace source inspection for explicit `rw [definition]` or `unfold definition` uses.

## Execution evidence and limits

| Evidence | What the supplied material establishes |
|---|---|
| Replay | 60 distinct module result rows, in exactly the order of `replay-order.txt`, all reporting `rc=0` and `errors=0`, with the stated fresh-copy provenance from `afe5982f`. |
| Admissions in replay | Four in `Games/Efficiency`; separately, two in the downstream `ThreeColoring/Protocol` and one in `ThreeColoring/Simulator`. Those downstream admissions are outside the changed-file axiom claim and are not new S2b admissions. |
| Axioms | 410 distinct public-theorem entries. Exactly four list `sorryAx`: `exists_handlerMachine`, `exists_interactiveHandlerMachine`, `exists_toCompOn_of_toComp`, and `exists_toOracleAdversary_of_bitCodec`. The other 406 list only subsets of `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. |
| Count reconciliation | Round 2's 379 public theorems, plus nine new public lemmas, plus 22 pre-existing public theorems from the newly included `Games/Probability.lean`, gives 410. |
| Lint / check 8 | 26 per-file zero-finding lint results; check 8 reports 0 failures and 0 warnings over 14 files. These checks do not detect the `expect_bind` body reduction. |
| Seal | All 13 configured current versions report PASS. The earlier `Simulate` and `PRF` versions report failures, providing useful controls. The run is identified with `81e4f4e2`, not the final `27ae72da` commit. The final commit adds seven defining equations across `OracleComp`, `Probability` and `Simulate`; those equations were inspected here, but the new consumer-file coverage is missing. |

I independently checked source hashes, the repair diff, equation statements and proofs, repaired consumers, descriptions, and the internal consistency of the attached logs. No `lean` or `lake` executable was available here, so the replay, axiom, lint and seal results above are **inspected maintainer execution evidence**, not fresh executions by this auditor. The four expressly deferred efficiency proofs are not findings merely because they remain admitted. This audit does not certify their future fills, prong integrations, or the scheduled ch. 2–4 cleanup.

**Notation:** `a`, `f`, and `g` in the repair explanation are the return value, continuation, and real-valued output function already bound in `ProbComp.expect_bind`; `n` is the existing security parameter. Other names and budget expressions are the audited Lean identifiers.
