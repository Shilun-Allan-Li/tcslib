## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/pack-r4.md =====

# Gate 04 (Pass–shelat ch. 5–8, S2b), round 4: closing audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#195](https://github.com/Shilun-Allan-Li/tcslib/pull/195)
at its head `a588adfed01eefe6971abd0846e3938ad02e8624`. That is two commits on round 3's
`27ae72da`:
- `947606fe`, the rule-10 re-proofs;
- `a588adfe`, ruling R-04-4: `Games.QueryImpl` and `Games.OracleSpec.add` become `abbrev`.

In the bundle:
- round 3's findings (`gate04-s2b-r3-findings.md`) and resolutions (`resolutions-r3.md`);
- the repair diff from `27ae72da` (`evidence-r4/repair.diff.txt`);
- **the complete seal evidence**:
  - the seal at the head (`seal-evidence.log`);
  - the `$BASE` control (`seal-control-base.log`);
  - the seal without entries (`seal-plain.log`);
  - the cross-check with round 3's names (`seal-r3union.log`);
  - the source scan at the head and at the base (`scan.log`, `scan-base.log`);
  - the named exclusions (`exclusions.md`);
  - the tools (`tool-*.txt`);
  - the worker's report (`REPORT.md`);
- replay, axioms and lint (`replay.log`, `replay-first-commit.log`, `axioms.log`, `lint.log`);
- every Lean file the two commits change, at the head.

The deliverable is **`gate04-s2b-r4-findings.md`**.

## Brief for the auditor

1. **Verify round 3's resolutions:** for R3-01, R3-02, F02 and N7, say fixed, recorded or not
   resolved (and why).
2. **Audit the changed surface:**
   - The re-proved declarations (`repair.diff.txt`) must read no other file's definition and must
     keep their statements. The seal output and the control are the evidence.
   - Check the seal's method (`tool-collect_body.lean.txt`, `tool-seal.py.txt`, `tool-scan.py.txt`):
     does its candidate collection really cover every foreign definition a declaration can reduce?
     What can it miss? (The tool says the source scan covers `unfold`/`simp [d]`, which a seal
     cannot see.)
   - The two `abbrev` headers: is treating these two type formers as notation sound under policy §1,
     given their reading lemmas (`queryImpl_def`, `OracleSpec.add_dom_inl/_inr`, `add_rng_inl/_inr`)?
     Does making them reducible change any statement's meaning? (It should not.)
   - The exclusions (`exclusions.md`, sections A and B): are they all in declarations #195 did not
     change (status SAME)? Is the claim "0 entries on any declaration #195 added or changed" true?
3. **Look for regressions.** Do not give a blanket approval.

## Attestations (maintainer; `evidence-r4/`)

- **Change set:** 26 Lean files, excluding the root facade (`changed-files.txt`). This corrects
  round 3's "25".
- **Elaboration:**
  - `replay-first-commit.log`: the 22 modules downstream of the first commit's five files, then
    `Checks`; 23 of 23 pass.
  - `replay.log`: after the second commit, the 29 modules downstream of `OracleComp.lean` and
    `Simulate.lean`, then `Checks`; 30 of 30 pass.
  - The `sorry` counts equal round 3's: `Games/Efficiency` 4, all others 0.
- **Axioms** (`axioms.log`): the 155 public theorems of the 7 files the two commits change. All are
  standard; none depends on `sorryAx`. Round 3's print of the other changed files stands, with
  `sorryAx` exactly in T1, T2, `exists_toCompOn_of_toComp` and T4.
- **Lint** (`lint.log`): 0 findings on each of the 26 files; check 8b on `Games/`: 0 FAIL, 0 WARN.
- **Seal** (`seal-evidence.log`): 26 of 26 pass, with automatic candidates. The 14 `Games/` files
  need no entry. The named entries cover only inherited ch. 2–4 declarations.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per item: `R3-01: fixed / recorded / not resolved — <reason>` (also R3-02, F02, N7).
Severity guide as in rounds 1–3. The gate closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/findings/gate04-s2b-r3-findings.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/resolutions-r3.md =====

# Gate 04 (S2b, #195): round 3 resolutions

- **Round 3:** findings `findings/gate04-s2b-r3-findings.md`, verbatim, SHA-256 `e20d60e517ec8441e7db380769738423b1219962d4d9826c0bb0c3fc26a075f4`; head
  `27ae72da62119ebdde380b8cb2d8c183b59fa2bf`. **0 blockers, 1 major (R3-01), 1 minor (R3-02).**
  R2-01, R2-02, R2-03 and N2 fixed; F02 and N7 not resolved (through R3-01).
- **Ruling (user, 2026-11-06): R-04-4 (A)**, make `Games.QueryImpl` and `Games.OracleSpec.add`
  `abbrev`, so that they are notation under policy §1 (both already have their reading lemmas).
- **Repair:** two commits on #195, `947606fecf1142997661651701f04c3912ba7551` (re-proofs) and
  `a588adfed01eefe6971abd0846e3938ad02e8624` (R-04-4); the full diff is `evidence-r4/repair.diff.txt`.

| Finding | Severity | Resolution |
|---|---|---|
| R3-01 | major | **Fixed.** `ProbComp.expect_bind`'s `pure` case is `simp only [OracleComp.pure_bind, expect_pure]`. The seal is now **complete and automatic**. It covers every one of the 26 Lean files in #195's change set, at the final head. For every declaration, the candidates are collected by a Lean meta program from types, values, transparent foreign instances and the statements of lemmas used in proofs and in `simp`/`rw` lists (`evidence-r4/tool-collect_body.lean.txt`), not hand-picked. A source scan for explicit `unfold`/`rw`/`simp`/`delta` of other files' definitions complements it. The sweep found six more S2a proofs of the same kind in `Games/Protocols.lean` (three `example`s, `Party.stepT_fst`, `closeT_fst`, `execT_outcome`), plus three in `LazySampling.lean` and three in `MultiMessage(Lemmas).lean`; all are re-proved through published equations. 26 of 26 files pass (`seal-evidence.log`), and the `$BASE` control fails exactly at the re-proved declarations (`seal-control-base.log`). The remaining reads are **named exclusions** (`exclusions.md`): section A lists 48 definitional reads and section B 75 explicit unfolds, all in inherited ch. 2–4 declarations that #195 did not change, scheduled for the gate 03 clean-up, part 2 (item J). Section C (type-level reads in `Games/`) is empty after R-04-4. Check: 0 entries on any declaration #195 added or changed. |
| R3-02 | minor | **Fixed.** The change set has **26** Lean files (excluding the root facade); `evidence-r4/changed-files.txt`, and the round 4 pack says so. |
| F02, N7 | (round 1) | **Fixed** through R3-01: the seal covers the whole change set at the final head, with the exclusions named rather than claimed covered. |

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/repair.diff.txt =====

diff --git a/TCSlib/Cryptography/Asymptotic/MultiMessage.lean b/TCSlib/Cryptography/Asymptotic/MultiMessage.lean
index e8cde0a8..aafd190c 100644
--- a/TCSlib/Cryptography/Asymptotic/MultiMessage.lean
+++ b/TCSlib/Cryptography/Asymptotic/MultiMessage.lean
@@ -109,8 +109,12 @@ theorem eval_chainTree {I O α : Type} (g : I → O) :
 /-- A chain of `k` queries makes at most `k` queries. -/
 theorem boundedBy_chainTree {I O α : Type} :
     ∀ (k : ℕ) (xs : Fin k → I) (f : (Fin k → O) → α), (chainTree k xs f).BoundedBy k
-  | 0, _, _ => trivial
-  | k + 1, xs, f => fun o => boundedBy_chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)
+  | 0, _, _ => by
+    rw [chainTree]
+    exact QueryTree.boundedBy_ret _ _
+  | k + 1, xs, f => by
+    rw [chainTree, QueryTree.boundedBy_query_succ]
+    exact fun o => boundedBy_chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)
 
 /-! ### The hybrids of [PS10, Theorem 99.2], concrete -/
 
diff --git a/TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean b/TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean
index c89380bc..2689e3fc 100644
--- a/TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean
+++ b/TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean
@@ -189,7 +189,7 @@ theorem acceptProb_oracleDist_congr_equiv {σ : Type*} {I O : Type} {ρ ρ' : Ty
     [Fintype ρ'] (X : σ → I → O) (A : OracleAdversary ρ I O) (A' : OracleAdversary ρ' I O)
     (φ : ρ' ≃ ρ) (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
     acceptProb X (oracleDist A) = acceptProb X (oracleDist A') := by
-  unfold acceptProb oracleDist
+  simp only [acceptProb_def, oracleDist_apply]
   rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr φ)]
   congr 1
   funext z
@@ -202,9 +202,10 @@ theorem prfAdv_congr_equiv {K : Type*} {I O : Type} {ρ ρ' : Type*} [Fintype K]
     (A' : OracleAdversary ρ' I O) (φ : ρ' ≃ ρ)
     (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
     prfAdv F A = prfAdv F A' := by
-  unfold prfAdv distAdv
-  rw [acceptProb_oracleDist_congr_equiv F A A' φ h,
-    acceptProb_oracleDist_congr_equiv (randomFunction I O) A A' φ h]
+  have hF := acceptProb_oracleDist_congr_equiv F A A' φ h
+  have hR := acceptProb_oracleDist_congr_equiv (id : (I → O) → I → O) A A' φ h
+  simp only [acceptProb_def, oracleDist_apply, id_eq] at hF hR
+  rw [prfAdv_eq, prfAdv_eq, hF, hR]
 
 /-! ### Strings: chunked encodings, history blocks, mask blocks -/
 
diff --git a/TCSlib/Cryptography/Games/OracleComp.lean b/TCSlib/Cryptography/Games/OracleComp.lean
index f38b9fc3..c8f91d04 100644
--- a/TCSlib/Cryptography/Games/OracleComp.lean
+++ b/TCSlib/Cryptography/Games/OracleComp.lean
@@ -162,7 +162,7 @@ theorem singleSpec_rng (I O : Type) (u : Unit) : (singleSpec I O).rng u = O := r
 
 /-- The **disjoint union** of two oracle families: oracle `.inl i` is oracle `i` of `s₁`, and
 oracle `.inr j` is oracle `j` of `s₂`. [VCVio, OracleComp/OracleSpec] -/
-def OracleSpec.add {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) :
+abbrev OracleSpec.add {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) :
     OracleSpec (ι₁ ⊕ ι₂) :=
   ⟨Sum.elim s₁.dom s₂.dom, Sum.elim s₁.rng s₂.rng⟩
 
diff --git a/TCSlib/Cryptography/Games/Probability.lean b/TCSlib/Cryptography/Games/Probability.lean
index 9b725fca..81a91dc5 100644
--- a/TCSlib/Cryptography/Games/Probability.lean
+++ b/TCSlib/Cryptography/Games/Probability.lean
@@ -123,7 +123,7 @@ average the same continuations. -/
 theorem expect_bind (c : ProbComp α) (f : α → ProbComp β) (g : β → ℝ) :
     expect (c.bind f) g = expect c (fun a => expect (f a) g) := by
   induction c with
-  | pure a => rfl
+  | pure a => simp only [OracleComp.pure_bind, expect_pure]
   | query m x k ih => simp only [OracleComp.query_bind, expect_query, ih]
 
 /-- The expectation over a mapped computation is the expectation of the composite. -/
diff --git a/TCSlib/Cryptography/Games/Protocols.lean b/TCSlib/Cryptography/Games/Protocols.lean
index 3e6d9334..cbe17b58 100644
--- a/TCSlib/Cryptography/Games/Protocols.lean
+++ b/TCSlib/Cryptography/Games/Protocols.lean
@@ -229,15 +229,21 @@ theorem exec_succ {M₁ M₂ : Type} (fuel : ℕ) (A : Party M₁ M₂ α)
 /-! ### Sanity checks: fuel counts messages; a send after the end is reported -/
 
 example (a b : Bool) :
-    exec 0 (M₁ := Unit) (M₂ := Unit) (.pure a) (fun _ => .pure b) = .pure (.done a b) := rfl
+    exec 0 (M₁ := Unit) (M₂ := Unit) (.pure a) (fun _ => .pure b) = .pure (.done a b) := by
+  simp only [exec_zero, step_pure, OracleComp.pure_bind, Sum.elim_inl, endWith_eq, close_pure,
+    Option.elim_some]
 
 example (m : Unit) (a b : Bool) :
     exec 1 (M₂ := Unit) (.query (.inl ()) m fun _ => .pure a) (fun _ => .pure b) =
-      .pure (.done a b) := rfl
+      .pure (.done a b) := by
+  simp only [exec_succ, step_send, OracleComp.pure_bind, Sum.elim_inr, exec_zero, step_pure,
+    Sum.elim_inl, endWith_eq, close_pure, Option.elim_some, ExecOutcome.swap_done]
 
 example (m : Unit) (a b : Bool) :
     exec 1 (M₁ := Unit) (.pure a) (fun _ => .query (.inl ()) m fun _ => .pure b) =
-      .pure .sentAfterEnd := rfl
+      .pure .sentAfterEnd := by
+  simp only [exec_succ, step_pure, OracleComp.pure_bind, Sum.elim_inl, endWith_eq, close_send,
+    Option.elim_none]
 
 /-! ### The traced execution -/
 
@@ -338,10 +344,10 @@ theorem execT_trace : ∀ (fuel : ℕ) {M₁ M₂ α β : Type} (A : Party M₁
 /-- `stepT` projects to `step`. -/
 theorem stepT_fst (A : Party Out In α) : (stepT A).bind (fun p => .pure p.1) = step A := by
   induction A with
-  | pure a => rfl
+  | pure a => simp only [stepT, step, OracleComp.pure_bind]
   | query i x k ih =>
     cases i with
-    | inl u => cases u; rfl
+    | inl u => cases u; simp only [stepT, step, OracleComp.pure_bind]
     | inr j =>
       simp only [stepT, step, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
       congr 1
@@ -351,10 +357,10 @@ theorem stepT_fst (A : Party Out In α) : (stepT A).bind (fun p => .pure p.1) =
 /-- `closeT` projects to `close`. -/
 theorem closeT_fst (A : Party Out In α) : (closeT A).bind (fun p => .pure p.1) = close A := by
   induction A with
-  | pure a => rfl
+  | pure a => simp only [closeT, close, OracleComp.pure_bind]
   | query i x k ih =>
     cases i with
-    | inl u => cases u; rfl
+    | inl u => cases u; simp only [closeT, close, OracleComp.pure_bind]
     | inr j =>
       simp only [closeT, close, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
       congr 1
@@ -386,7 +392,7 @@ theorem execT_outcome : ∀ (fuel : ℕ) {M₁ M₂ α β : Type} (A : Party M
     rcases p with ⟨_ | _, c⟩
     · simp only [Sum.elim_inl, OracleComp.bind_assoc, OracleComp.pure_bind]
       rw [← endWithT_fst]
-    · rfl
+    · simp only [Sum.elim_inr, OracleComp.pure_bind]
   | fuel + 1, _, _, _, _, A, B => by
     simp only [execT, exec, OracleComp.bind_assoc]
     rw [← stepT_fst A, OracleComp.bind_assoc]
diff --git a/TCSlib/Cryptography/Games/Simulate.lean b/TCSlib/Cryptography/Games/Simulate.lean
index e8c957dc..acf23f38 100644
--- a/TCSlib/Cryptography/Games/Simulate.lean
+++ b/TCSlib/Cryptography/Games/Simulate.lean
@@ -66,7 +66,7 @@ variable {ι ι' ι₁ ι₂ : Type} {α β σ : Type}
 /-- An **implementation** of the oracles of `spec` by computations over `spec'`, with state `σ`:
 on oracle `i`, query `x` and state `s`, a computation returning the answer and the new state.
 [VCVio, SimSemantics] -/
-def QueryImpl {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') : Type :=
+abbrev QueryImpl {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') : Type :=
   ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)
 
 /-- An implementation is a function of the oracle, the query and the state:
diff --git a/TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean b/TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean
index c5911eb6..922c55d5 100644
--- a/TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean
+++ b/TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean
@@ -175,7 +175,7 @@ theorem evalLazy_congr {a b : ℕ → O} {t : QueryTree I O α} {m : ℕ} (ht :
       have h1 := idxOf_noteQuery_lt L x
       have h2 := length_noteQuery_le L x
       rw [evalLazy_query, evalLazy_query, hab _ (by omega)]
-      exact ih _ (ht _) _ fun j hj => hab j (by omega)
+      exact ih _ ((boundedBy_query_succ x k m).1 ht _) _ fun j hj => hab j (by omega)
 
 /-- Post-processing every lazy answer by `g` is the same as running the tree whose
 answers are post-processed by `g`. -/
@@ -183,8 +183,10 @@ theorem evalLazy_comp {O' : Type} (g : O' → O) (a : ℕ → O') (t : QueryTree
     (L : List I) :
     evalLazy (g ∘ a) t L = evalLazy a (t.simulate id (fun _ => g)) L := by
   induction t using QueryTree.induct generalizing L with
-  | ret y => rfl
-  | query x k ih => exact ih _ _
+  | ret y => rw [simulate_ret, evalLazy_ret, evalLazy_ret]
+  | query x k ih =>
+    rw [simulate_query, evalLazy_query, evalLazy_query]
+    exact ih _ _
 
 end QueryTree
 
@@ -316,7 +318,10 @@ private theorem uprob_evalLazy_aux [Fintype I] [Fintype O] [Nonempty O] (φ : α
     uprob (fun W : Fin q → O => φ (evalLazy (extendStream (combine L.length W₀ W)) t L)) =
       uprob (fun R : I → O => φ (t.eval (mergeTable L (extendStream W₀) R))) := by
   induction t using QueryTree.induct with
-  | ret y => intro _ _ _ _ _; exact uprob_const_eq (β := Fin q → O) (γ := I → O) (φ y)
+  | ret y =>
+    intro _ _ _ _ _
+    simp only [evalLazy_ret, eval_ret]
+    exact uprob_const_eq (β := Fin q → O) (γ := I → O) (φ y)
   | query x k ih =>
     intro m L W₀ ht hm
     cases m with
@@ -334,7 +339,7 @@ private theorem uprob_evalLazy_aux [Fintype I] [Fintype O] [Nonempty O] (φ : α
           (k (extendStream W₀ (L.idxOf x))).eval (mergeTable L (extendStream W₀) R) := by
         intro R; simp [mergeTable, hx]
       simp only [hl, hr]
-      exact ih _ m L W₀ (ht _) (by omega)
+      exact ih _ m L W₀ ((boundedBy_query_succ x k m).1 ht _) (by omega)
     · -- a new query: split off the fresh value on both sides
       have hℓ : L.length < q := by omega
       have hidx : (L ++ [x]).idxOf x = L.length := by
@@ -362,7 +367,8 @@ private theorem uprob_evalLazy_aux [Fintype I] [Fintype O] [Nonempty O] (φ : α
           simp only [h, mergeTable_update _ _ _ (List.mem_append_right L
             (List.mem_singleton_self x))])]
       exact congrArg uexp (funext fun v =>
-        ih v m (L ++ [x]) (update W₀ j v) (ht v) (by rw [hlen]; omega))
+        ih v m (L ++ [x]) (update W₀ j v) ((boundedBy_query_succ x k m).1 ht v)
+          (by rw [hlen]; omega))
 
 /-- **Lazy sampling.** For a query tree making at most `q` queries, answering the `k`-th
 distinct query by the `k`-th of `q` independent uniform values gives the same output

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/changed-files.txt =====

TCSlib/Cryptography/Asymptotic/MultiMessage.lean
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean
TCSlib/Cryptography/Asymptotic/PRF.lean
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean
TCSlib/Cryptography/Foundations/Experiments.lean
TCSlib/Cryptography/Foundations/Probability.lean
TCSlib/Cryptography/Games/Advantage.lean
TCSlib/Cryptography/Games/BitCodec.lean
TCSlib/Cryptography/Games/Bridges.lean
TCSlib/Cryptography/Games/Bridges/Experiments.lean
TCSlib/Cryptography/Games/Bridges/Machines.lean
TCSlib/Cryptography/Games/Bridges/QueryTree.lean
TCSlib/Cryptography/Games/Bridges/Strategies.lean
TCSlib/Cryptography/Games/Efficiency.lean
TCSlib/Cryptography/Games/Hopping.lean
TCSlib/Cryptography/Games/Machines.lean
TCSlib/Cryptography/Games/OracleComp.lean
TCSlib/Cryptography/Games/Probability.lean
TCSlib/Cryptography/Games/Protocols.lean
TCSlib/Cryptography/Games/Simulate.lean
TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/seal-evidence.log =====

# rule-10 seal at a588adfed01eefe6971abd0846e3938ad02e8624 (final head of wip/g04r4; base 27ae72da62119ebdde380b8cb2d8c183b59fa2bf): each of the 26 files compiled
# with `attribute [local irreducible]` on every automatically collected candidate (candidates/),
# the named entries of unseal.json unsealed only around their declaration (exclusions.md)
TCSlib/Cryptography/Asymptotic/MultiMessage.lean: candidates=33; unsealed for 7 named declaration(s) PASS (rc=0, error lines=0)
   unseal TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le (lines 257-301): TCSlib.Cryptography.acceptProb TCSlib.Cryptography.randomFunction
   unseal TCSlib.Cryptography.encodeList_eq_flatMap (lines 529-535): TCSlib.Cryptography.PrivateKeyScheme.encodeList
   unseal TCSlib.Cryptography.multiMsgAdv_boundedBy (lines 150-155): TCSlib.Cryptography.OracleAdversary.BoundedBy
   unseal TCSlib.Cryptography.prfScheme (lines 498-522): Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTimeUniform Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.prfScheme_multiEncDist (lines 545-564): Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTimeUniform Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.prfScheme_multiMessageSecure (lines 566-655): Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTimeUniform Complexity.PolyExpr.eval TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure TCSlib.Cryptography.acceptProb TCSlib.Cryptography.distAdv
   unseal TCSlib.Cryptography.pushesUniform_comp_injective (lines 226-255): TCSlib.Cryptography.HardcoreBit.PushesUniform
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean: candidates=29; unsealed for 8 named declaration(s) PASS (rc=0, error lines=0)
   unseal TCSlib.Cryptography.MultiMsg.dbl_append (lines 318-320): Turing.dbl
   unseal TCSlib.Cryptography.MultiMsg.decodeOracleMove_ret (lines 542-544): TCSlib.Cryptography.decodeOracleMove Turing.pairDecode
   unseal TCSlib.Cryptography.MultiMsg.encodeHist_eq_flatMap (lines 223-230): TCSlib.Cryptography.encodeHist
   unseal TCSlib.Cryptography.MultiMsg.eval_histBlockLen (lines 235-236): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt (lines 617-741): Complexity.NUPPT.advInput Complexity.NUPPT.layout Complexity.NUPPT.runAt Complexity.NUPPT.runAtL Complexity.NUPPT.toOracleAdversary Complexity.PolyExpr.eval TCSlib.Cryptography.QueryTree.eval
   unseal TCSlib.Cryptography.MultiMsg.take_drop_ofFn_blocks (lines 379-395): TCSlib.Cryptography.FunFamily.blocks
   unseal TCSlib.Cryptography.MultiMsg.zipWith_xor_dbl (lines 330-336): Turing.dbl
   unseal TCSlib.Cryptography.MultiMsg.zipWith_xor_histBlock_maskBlock (lines 338-365): Turing.dbl
TCSlib/Cryptography/Asymptotic/PRF.lean: candidates=43; unsealed for 17 named declaration(s) PASS (rc=0, error lines=0)
   unseal TCSlib.Cryptography.DoublingPRG.negligible_prgAdv (lines 437-443): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.OracleEnsemble.Indist.symm (lines 329-341): TCSlib.Cryptography.distAdv
   unseal TCSlib.Cryptography.OracleEnsemble.Indist.trans (lines 343-364): TCSlib.Cryptography.distAdv
   unseal TCSlib.Cryptography.OracleEnsemble.random_O (lines 141-144): TCSlib.Cryptography.randomFunction
   unseal TCSlib.Cryptography.PRF (lines 378-393): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.PRF.negligible_prfAdv (lines 404-411): Complexity.PolyExpr.eval TCSlib.Cryptography.prfAdv
   unseal TCSlib.Cryptography.PRG.Secure.doubling (lines 493-515): Complexity.PolyExpr.eval TCSlib.Cryptography.Ensemble.Pseudorandom TCSlib.Cryptography.PRG.expand TCSlib.Cryptography.prgAdv
   unseal TCSlib.Cryptography.PRG.Secure.truncate (lines 472-491): Complexity.PolyExpr.eval TCSlib.Cryptography.Ensemble.Pseudorandom TCSlib.Cryptography.PRG.Easy TCSlib.Cryptography.PRG.Secure TCSlib.Cryptography.PRG.ensemble TCSlib.Cryptography.PRG.oneBit TCSlib.Cryptography.prgAdv
   unseal TCSlib.Cryptography.PRG.doubling (lines 457-463): Complexity.PolyExpr.eval TCSlib.Cryptography.PRG.expand
   unseal TCSlib.Cryptography.PRG.doubling_apply (lines 465-470): TCSlib.Cryptography.PRG.expand
   unseal TCSlib.Cryptography.decodeOracleMove_eq (lines 585-624): TCSlib.Cryptography.GGMRed.queryOf TCSlib.Cryptography.GGMRed.verdictOf Turing.pairDecode
   unseal TCSlib.Cryptography.doublingEnsemble (lines 415-420): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.exists_ggmBitsDist_nuppt (lines 648-707): Complexity.NUPPT.coinLen Complexity.PolyExpr.eval TCSlib.Cryptography.GGMRed.coinStr TCSlib.Cryptography.GGMRed.ggmRedMachine TCSlib.Cryptography.GGMRed.histEnc
   unseal TCSlib.Cryptography.ggmPRF_prf (lines 731-801): Complexity.PolyExpr.eval TCSlib.Cryptography.Negligible TCSlib.Cryptography.prfAdv TCSlib.Cryptography.prgAdv
   unseal TCSlib.Cryptography.prfAdv_toOracleAdversary (lines 395-402): Complexity.PolyExpr.eval TCSlib.Cryptography.prfAdv
   unseal TCSlib.Cryptography.thm_97_3_1 (lines 554-566): Complexity.PolyExpr.eval TCSlib.Cryptography.ggmBits
   unseal TCSlib.Cryptography.two_mul_add_one_expands (lines 450-455): Complexity.PolyExpr.eval
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean: candidates=32; unsealed for 9 named declaration(s) PASS (rc=0, error lines=0)
   unseal Complexity.NUPPT.coins_preComp (lines 177-179): Complexity.NUPPT.ofPolyTime
   unseal Complexity.NUPPT.runAt_preComp (lines 189-193): Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTime Complexity.NUPPT.runAt Complexity.NUPPT.runAtL
   unseal TCSlib.Cryptography.PRG.Secure.truncateTo_easy (lines 222-236): TCSlib.Cryptography.PRG.Easy TCSlib.Cryptography.PRG.Secure
   unseal TCSlib.Cryptography.PRG.Secure.truncateTo_negligible (lines 238-272): Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTime TCSlib.Cryptography.Ensemble.Pseudorandom TCSlib.Cryptography.Ensemble.uniform TCSlib.Cryptography.PRG.Secure TCSlib.Cryptography.PRG.ensemble TCSlib.Cryptography.prgAdv
   unseal TCSlib.Cryptography.drop_ofFn_splitHalves (lines 113-119): TCSlib.Cryptography.splitHalves
   unseal TCSlib.Cryptography.drop_take_ofFn_blocks (lines 77-93): TCSlib.Cryptography.FunFamily.blocks
   unseal TCSlib.Cryptography.ggmEval_ofFn (lines 399-411): TCSlib.Cryptography.ggmBits
   unseal TCSlib.Cryptography.ggmEval_poly (lines 380-386): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.take_ofFn_splitHalves (lines 106-111): TCSlib.Cryptography.splitHalves
TCSlib/Cryptography/Foundations/Experiments.lean: candidates=5 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Foundations/Probability.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Advantage.lean: candidates=4 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/BitCodec.lean: candidates=4 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/Experiments.lean: candidates=11 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/Machines.lean: candidates=10 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/QueryTree.lean: candidates=9 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/Strategies.lean: candidates=13 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Efficiency.lean: candidates=19 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Hopping.lean: candidates=6 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Machines.lean: candidates=4 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/OracleComp.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Probability.lean: candidates=1 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Protocols.lean: candidates=2 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Simulate.lean: candidates=3 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean: candidates=5; unsealed for 2 named declaration(s) PASS (rc=0, error lines=0)
   unseal TCSlib.Cryptography.prfAdv_eq (lines 71-77): TCSlib.Cryptography.acceptProb TCSlib.Cryptography.distAdv TCSlib.Cryptography.oracleDist
   unseal TCSlib.Cryptography.prfAdv_nonneg (lines 79-82): TCSlib.Cryptography.distAdv
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean: candidates=11; unsealed for 2 named declaration(s) PASS (rc=0, error lines=0)
   own seal line 68: attribute [local irreducible] uprob acceptProb -> -- (covered by the seal line) attribute [local irreducible] uprob acceptProb
   unseal TCSlib.Cryptography.hybridProb_level (lines 205-217): TCSlib.Cryptography.OracleAdversary.BoundedBy
   unseal TCSlib.Cryptography.hybridProb_top (lines 125-132): TCSlib.Cryptography.randomFunction
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean: candidates=6 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean: candidates=11; unsealed for 2 named declaration(s) PASS (rc=0, error lines=0)
   own seal line 68: attribute [local irreducible] uprob acceptProb -> -- (covered by the seal line) attribute [local irreducible] uprob acceptProb
   unseal TCSlib.Cryptography.subHybridProb_top (lines 238-266): TCSlib.Cryptography.OracleAdversary.BoundedBy TCSlib.Cryptography.oracleDist TCSlib.Cryptography.randomFunction
   unseal TCSlib.Cryptography.subHybridProb_zero (lines 205-236): TCSlib.Cryptography.OracleAdversary.BoundedBy TCSlib.Cryptography.oracleDist
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean: candidates=7; unsealed for 1 named declaration(s) PASS (rc=0, error lines=0)
   unseal TCSlib.Cryptography.Strategy.pairFstD_encodeMsgs (lines 125-129): Complexity.pairFstD

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/seal-control-base.log =====

# control: the same seal on the $BASE copy (27ae72da62119ebdde380b8cb2d8c183b59fa2bf) of each file, against the $BASE olean tree,
# with the $BASE candidates (candidates-base/) and the same named entries
TCSlib/Cryptography/Asymptotic/MultiMessage.lean: candidates=33; unsealed for 7 named declaration(s) FAIL (rc=1, error lines=2)
   unseal TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le (lines 253-297): TCSlib.Cryptography.acceptProb TCSlib.Cryptography.randomFunction
   unseal TCSlib.Cryptography.encodeList_eq_flatMap (lines 525-531): TCSlib.Cryptography.PrivateKeyScheme.encodeList
   unseal TCSlib.Cryptography.multiMsgAdv_boundedBy (lines 146-151): TCSlib.Cryptography.OracleAdversary.BoundedBy
   unseal TCSlib.Cryptography.prfScheme (lines 494-518): Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTimeUniform Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.prfScheme_multiEncDist (lines 541-560): Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTimeUniform Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.prfScheme_multiMessageSecure (lines 562-651): Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTimeUniform Complexity.PolyExpr.eval TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure TCSlib.Cryptography.acceptProb TCSlib.Cryptography.distAdv
   unseal TCSlib.Cryptography.pushesUniform_comp_injective (lines 222-251): TCSlib.Cryptography.HardcoreBit.PushesUniform
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:112:2 [theorem TCSlib.Cryptography.boundedBy_chainTree] Type mismatch
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:113:2 [theorem TCSlib.Cryptography.boundedBy_chainTree] Type mismatch
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean: candidates=31; unsealed for 8 named declaration(s) PASS (rc=0, error lines=0)
   unseal TCSlib.Cryptography.MultiMsg.dbl_append (lines 317-319): Turing.dbl
   unseal TCSlib.Cryptography.MultiMsg.decodeOracleMove_ret (lines 541-543): TCSlib.Cryptography.decodeOracleMove Turing.pairDecode
   unseal TCSlib.Cryptography.MultiMsg.encodeHist_eq_flatMap (lines 222-229): TCSlib.Cryptography.encodeHist
   unseal TCSlib.Cryptography.MultiMsg.eval_histBlockLen (lines 234-235): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt (lines 616-740): Complexity.NUPPT.advInput Complexity.NUPPT.layout Complexity.NUPPT.runAt Complexity.NUPPT.runAtL Complexity.NUPPT.toOracleAdversary Complexity.PolyExpr.eval TCSlib.Cryptography.QueryTree.eval
   unseal TCSlib.Cryptography.MultiMsg.take_drop_ofFn_blocks (lines 378-394): TCSlib.Cryptography.FunFamily.blocks
   unseal TCSlib.Cryptography.MultiMsg.zipWith_xor_dbl (lines 329-335): Turing.dbl
   unseal TCSlib.Cryptography.MultiMsg.zipWith_xor_histBlock_maskBlock (lines 337-364): Turing.dbl
TCSlib/Cryptography/Asymptotic/PRF.lean: candidates=43; unsealed for 17 named declaration(s) PASS (rc=0, error lines=0)
   unseal TCSlib.Cryptography.DoublingPRG.negligible_prgAdv (lines 437-443): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.OracleEnsemble.Indist.symm (lines 329-341): TCSlib.Cryptography.distAdv
   unseal TCSlib.Cryptography.OracleEnsemble.Indist.trans (lines 343-364): TCSlib.Cryptography.distAdv
   unseal TCSlib.Cryptography.OracleEnsemble.random_O (lines 141-144): TCSlib.Cryptography.randomFunction
   unseal TCSlib.Cryptography.PRF (lines 378-393): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.PRF.negligible_prfAdv (lines 404-411): Complexity.PolyExpr.eval TCSlib.Cryptography.prfAdv
   unseal TCSlib.Cryptography.PRG.Secure.doubling (lines 493-515): Complexity.PolyExpr.eval TCSlib.Cryptography.Ensemble.Pseudorandom TCSlib.Cryptography.PRG.expand TCSlib.Cryptography.prgAdv
   unseal TCSlib.Cryptography.PRG.Secure.truncate (lines 472-491): Complexity.PolyExpr.eval TCSlib.Cryptography.Ensemble.Pseudorandom TCSlib.Cryptography.PRG.Easy TCSlib.Cryptography.PRG.Secure TCSlib.Cryptography.PRG.ensemble TCSlib.Cryptography.PRG.oneBit TCSlib.Cryptography.prgAdv
   unseal TCSlib.Cryptography.PRG.doubling (lines 457-463): Complexity.PolyExpr.eval TCSlib.Cryptography.PRG.expand
   unseal TCSlib.Cryptography.PRG.doubling_apply (lines 465-470): TCSlib.Cryptography.PRG.expand
   unseal TCSlib.Cryptography.decodeOracleMove_eq (lines 585-624): TCSlib.Cryptography.GGMRed.queryOf TCSlib.Cryptography.GGMRed.verdictOf Turing.pairDecode
   unseal TCSlib.Cryptography.doublingEnsemble (lines 415-420): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.exists_ggmBitsDist_nuppt (lines 648-707): Complexity.NUPPT.coinLen Complexity.PolyExpr.eval TCSlib.Cryptography.GGMRed.coinStr TCSlib.Cryptography.GGMRed.ggmRedMachine TCSlib.Cryptography.GGMRed.histEnc
   unseal TCSlib.Cryptography.ggmPRF_prf (lines 731-801): Complexity.PolyExpr.eval TCSlib.Cryptography.Negligible TCSlib.Cryptography.prfAdv TCSlib.Cryptography.prgAdv
   unseal TCSlib.Cryptography.prfAdv_toOracleAdversary (lines 395-402): Complexity.PolyExpr.eval TCSlib.Cryptography.prfAdv
   unseal TCSlib.Cryptography.thm_97_3_1 (lines 554-566): Complexity.PolyExpr.eval TCSlib.Cryptography.ggmBits
   unseal TCSlib.Cryptography.two_mul_add_one_expands (lines 450-455): Complexity.PolyExpr.eval
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean: candidates=32; unsealed for 9 named declaration(s) PASS (rc=0, error lines=0)
   unseal Complexity.NUPPT.coins_preComp (lines 177-179): Complexity.NUPPT.ofPolyTime
   unseal Complexity.NUPPT.runAt_preComp (lines 189-193): Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTime Complexity.NUPPT.runAt Complexity.NUPPT.runAtL
   unseal TCSlib.Cryptography.PRG.Secure.truncateTo_easy (lines 222-236): TCSlib.Cryptography.PRG.Easy TCSlib.Cryptography.PRG.Secure
   unseal TCSlib.Cryptography.PRG.Secure.truncateTo_negligible (lines 238-272): Complexity.NUPPT.coinLen Complexity.NUPPT.ofPolyTime TCSlib.Cryptography.Ensemble.Pseudorandom TCSlib.Cryptography.Ensemble.uniform TCSlib.Cryptography.PRG.Secure TCSlib.Cryptography.PRG.ensemble TCSlib.Cryptography.prgAdv
   unseal TCSlib.Cryptography.drop_ofFn_splitHalves (lines 113-119): TCSlib.Cryptography.splitHalves
   unseal TCSlib.Cryptography.drop_take_ofFn_blocks (lines 77-93): TCSlib.Cryptography.FunFamily.blocks
   unseal TCSlib.Cryptography.ggmEval_ofFn (lines 399-411): TCSlib.Cryptography.ggmBits
   unseal TCSlib.Cryptography.ggmEval_poly (lines 380-386): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.take_ofFn_splitHalves (lines 106-111): TCSlib.Cryptography.splitHalves
TCSlib/Cryptography/Foundations/Experiments.lean: candidates=5 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Foundations/Probability.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Advantage.lean: candidates=4 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/BitCodec.lean: candidates=4 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/Experiments.lean: candidates=11 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/Machines.lean: candidates=10 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/QueryTree.lean: candidates=10 FAIL (rc=1, error lines=4)
   TCSlib/Cryptography/Games/Bridges/QueryTree.lean:90:24 [theorem TCSlib.Cryptography.Games.simulate_ofComp_pure] function expected
   TCSlib/Cryptography/Games/Bridges/QueryTree.lean:115:4 [theorem TCSlib.Cryptography.Games.Bridge.treeImpl_apply] Function expected at
   TCSlib/Cryptography/Games/Bridges/QueryTree.lean:115:85 [theorem TCSlib.Cryptography.Games.Bridge.treeImpl_apply] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Bridges/QueryTree.lean:131:70 [theorem TCSlib.Cryptography.Games.Bridge.simulate_eq] (lean.unknownIdentifier): Unknown identifier `treeImpl_apply`
TCSlib/Cryptography/Games/Bridges/Strategies.lean: candidates=14 FAIL (rc=1, error lines=5)
   TCSlib/Cryptography/Games/Bridges/Strategies.lean:71:33 [def TCSlib.Cryptography.Games.Bridge.turnParty] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Bridges/Strategies.lean:72:8 [def TCSlib.Cryptography.Games.Bridge.turnParty] Type mismatch
   TCSlib/Cryptography/Games/Bridges/Strategies.lean:111:48 [theorem TCSlib.Cryptography.Games.Bridge.turnParty_succ] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Bridges/Strategies.lean:111:81 [theorem TCSlib.Cryptography.Games.Bridge.turnParty_succ] unsolved goals
   TCSlib/Cryptography/Games/Bridges/Strategies.lean:175:14 [theorem TCSlib.Cryptography.Games.Bridge.exec_turnParty] unsolved goals
TCSlib/Cryptography/Games/Efficiency.lean: candidates=20 FAIL (rc=1, error lines=6)
   TCSlib/Cryptography/Games/Efficiency.lean:262:2 [def TCSlib.Cryptography.Games.PolyHandler.impl] Type mismatch
   TCSlib/Cryptography/Games/Efficiency.lean:262:15 [def TCSlib.Cryptography.Games.PolyHandler.impl] (lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.pure` could not be determined
   TCSlib/Cryptography/Games/Efficiency.lean:269:4 [theorem TCSlib.Cryptography.Games.PolyHandler.impl_apply] Function expected at
   TCSlib/Cryptography/Games/Efficiency.lean:269:25 [theorem TCSlib.Cryptography.Games.PolyHandler.impl_apply] (lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.pure` could not be determined
   TCSlib/Cryptography/Games/Efficiency.lean:427:2 [def TCSlib.Cryptography.Games.InteractiveHandler.impl] Type mismatch
   TCSlib/Cryptography/Games/Efficiency.lean:437:4 [theorem TCSlib.Cryptography.Games.InteractiveHandler.impl_apply] Function expected at
TCSlib/Cryptography/Games/Hopping.lean: candidates=7 FAIL (rc=1, error lines=23)
   TCSlib/Cryptography/Games/Hopping.lean:167:49 [theorem TCSlib.Cryptography.Games.simulate_allOutputs_bad] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:176:10 [theorem TCSlib.Cryptography.Games.simulate_allOutputs_bad] function expected
   TCSlib/Cryptography/Games/Hopping.lean:208:23 [theorem TCSlib.Cryptography.Games.prob_eq_until_bad] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:209:25 [theorem TCSlib.Cryptography.Games.prob_eq_until_bad] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:210:33 [theorem TCSlib.Cryptography.Games.prob_eq_until_bad] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:211:33 [theorem TCSlib.Cryptography.Games.prob_eq_until_bad] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:220:4 [theorem TCSlib.Cryptography.Games.prob_eq_until_bad] function expected
   TCSlib/Cryptography/Games/Hopping.lean:289:23 [theorem TCSlib.Cryptography.Games.identical_until_bad] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:290:25 [theorem TCSlib.Cryptography.Games.identical_until_bad] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:291:33 [theorem TCSlib.Cryptography.Games.identical_until_bad] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:292:33 [theorem TCSlib.Cryptography.Games.identical_until_bad] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:297:21 [theorem TCSlib.Cryptography.Games.identical_until_bad] (lean.unknownIdentifier): Unknown identifier `prob_eq_until_bad`
   TCSlib/Cryptography/Games/Hopping.lean:297:9 [theorem TCSlib.Cryptography.Games.identical_until_bad] Tactic `rcases` failed: `x✝ : ?m.127` is not an inductive datatype
   TCSlib/Cryptography/Games/Hopping.lean:312:65 [theorem TCSlib.Cryptography.Games.hagree_of_eq] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:312:79 [theorem TCSlib.Cryptography.Games.hagree_of_eq] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:314:23 [theorem TCSlib.Cryptography.Games.hagree_of_eq] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:315:25 [theorem TCSlib.Cryptography.Games.hagree_of_eq] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:326:23 [theorem TCSlib.Cryptography.Games.identical_until_bad_init] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:327:25 [theorem TCSlib.Cryptography.Games.identical_until_bad_init] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:328:33 [theorem TCSlib.Cryptography.Games.identical_until_bad_init] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:329:33 [theorem TCSlib.Cryptography.Games.identical_until_bad_init] Function expected at
   TCSlib/Cryptography/Games/Hopping.lean:337:14 [theorem TCSlib.Cryptography.Games.identical_until_bad_init] (lean.unknownIdentifier): Unknown identifier `identical_until_bad`
   TCSlib/Cryptography/Games/Hopping.lean:334:82 [theorem TCSlib.Cryptography.Games.identical_until_bad_init] unsolved goals
TCSlib/Cryptography/Games/Machines.lean: candidates=4 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/OracleComp.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Probability.lean: candidates=1 FAIL (rc=1, error lines=1)
   TCSlib/Cryptography/Games/Probability.lean:126:14 [theorem TCSlib.Cryptography.Games.ProbComp.expect_bind] Tactic `rfl` failed: The left-hand side
TCSlib/Cryptography/Games/Protocols.lean: candidates=3 FAIL (rc=1, error lines=24)
   TCSlib/Cryptography/Games/Protocols.lean:129:41 [def TCSlib.Cryptography.Games.Party.step] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:130:36 [def TCSlib.Cryptography.Games.Party.step] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:130:56 [def TCSlib.Cryptography.Games.Party.step] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:139:82 [theorem TCSlib.Cryptography.Games.Party.step_send] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:146:81 [theorem TCSlib.Cryptography.Games.Party.step_coin] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:155:36 [def TCSlib.Cryptography.Games.Party.close] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:155:57 [def TCSlib.Cryptography.Games.Party.close] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:163:83 [theorem TCSlib.Cryptography.Games.Party.close_send] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:170:82 [theorem TCSlib.Cryptography.Games.Party.close_coin] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:232:89 [example TCSlib.Cryptography.Games.Party.example#1] Type mismatch
   TCSlib/Cryptography/Games/Protocols.lean:235:42 [example TCSlib.Cryptography.Games.Party.example#2] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:239:61 [example TCSlib.Cryptography.Games.Party.example#3] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:256:41 [def TCSlib.Cryptography.Games.Party.stepT] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:257:36 [def TCSlib.Cryptography.Games.Party.stepT] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:258:16 [def TCSlib.Cryptography.Games.Party.stepT] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:264:36 [def TCSlib.Cryptography.Games.Party.closeT] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:265:17 [def TCSlib.Cryptography.Games.Party.closeT] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:341:14 [theorem TCSlib.Cryptography.Games.Party.stepT_fst] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Games/Protocols.lean:344:24 [theorem TCSlib.Cryptography.Games.Party.stepT_fst] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Games/Protocols.lean:349:15 [theorem TCSlib.Cryptography.Games.Party.stepT_fst] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:354:14 [theorem TCSlib.Cryptography.Games.Party.closeT_fst] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Games/Protocols.lean:357:24 [theorem TCSlib.Cryptography.Games.Party.closeT_fst] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Games/Protocols.lean:362:15 [theorem TCSlib.Cryptography.Games.Party.closeT_fst] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Protocols.lean:389:6 [theorem TCSlib.Cryptography.Games.Party.execT_outcome] Tactic `rfl` failed: The left-hand side
TCSlib/Cryptography/Games/Simulate.lean: candidates=4 FAIL (rc=1, error lines=6)
   TCSlib/Cryptography/Games/Simulate.lean:147:2 [def TCSlib.Cryptography.Games.QueryImpl.sum] Type mismatch
   TCSlib/Cryptography/Games/Simulate.lean:148:2 [def TCSlib.Cryptography.Games.QueryImpl.sum] Type mismatch
   TCSlib/Cryptography/Games/Simulate.lean:154:39 [theorem TCSlib.Cryptography.Games.QueryImpl.sum_inl] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Simulate.lean:154:45 [theorem TCSlib.Cryptography.Games.QueryImpl.sum_inl] Type mismatch
   TCSlib/Cryptography/Games/Simulate.lean:161:39 [theorem TCSlib.Cryptography.Games.QueryImpl.sum_inr] Application type mismatch: The argument
   TCSlib/Cryptography/Games/Simulate.lean:161:45 [theorem TCSlib.Cryptography.Games.QueryImpl.sum_inr] Type mismatch
TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean: candidates=5; unsealed for 2 named declaration(s) PASS (rc=0, error lines=0)
   unseal TCSlib.Cryptography.prfAdv_eq (lines 71-77): TCSlib.Cryptography.acceptProb TCSlib.Cryptography.distAdv TCSlib.Cryptography.oracleDist
   unseal TCSlib.Cryptography.prfAdv_nonneg (lines 79-82): TCSlib.Cryptography.distAdv
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean: candidates=11; unsealed for 2 named declaration(s) PASS (rc=0, error lines=0)
   own seal line 68: attribute [local irreducible] uprob acceptProb -> -- (covered by the seal line) attribute [local irreducible] uprob acceptProb
   unseal TCSlib.Cryptography.hybridProb_level (lines 205-217): TCSlib.Cryptography.OracleAdversary.BoundedBy
   unseal TCSlib.Cryptography.hybridProb_top (lines 125-132): TCSlib.Cryptography.randomFunction
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean: candidates=6 FAIL (rc=1, error lines=7)
   TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean:178:18 [theorem TCSlib.Cryptography.QueryTree.evalLazy_congr] Function expected at
   TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean:178:48 [theorem TCSlib.Cryptography.QueryTree.evalLazy_congr] omega could not prove the goal:
   TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean:186:13 [theorem TCSlib.Cryptography.QueryTree.evalLazy_comp] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean:187:20 [theorem TCSlib.Cryptography.QueryTree.evalLazy_comp] Type mismatch
   TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean:319:30 [theorem TCSlib.Cryptography.QueryTree.uprob_evalLazy_aux] Type mismatch
   TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean:337:25 [theorem TCSlib.Cryptography.QueryTree.uprob_evalLazy_aux] Function expected at
   TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean:365:43 [theorem TCSlib.Cryptography.QueryTree.uprob_evalLazy_aux] Function expected at
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean: candidates=11; unsealed for 2 named declaration(s) PASS (rc=0, error lines=0)
   own seal line 68: attribute [local irreducible] uprob acceptProb -> -- (covered by the seal line) attribute [local irreducible] uprob acceptProb
   unseal TCSlib.Cryptography.subHybridProb_top (lines 238-266): TCSlib.Cryptography.OracleAdversary.BoundedBy TCSlib.Cryptography.oracleDist TCSlib.Cryptography.randomFunction
   unseal TCSlib.Cryptography.subHybridProb_zero (lines 205-236): TCSlib.Cryptography.OracleAdversary.BoundedBy TCSlib.Cryptography.oracleDist
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean: candidates=7; unsealed for 1 named declaration(s) PASS (rc=0, error lines=0)
   unseal TCSlib.Cryptography.Strategy.pairFstD_encodeMsgs (lines 125-129): Complexity.pairFstD

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/seal-plain.log =====

# for the record: the same seal at a588adfed01eefe6971abd0846e3938ad02e8624 with no unseal entry at all (every failure here is
# an entry of exclusions.md, section A or C)
TCSlib/Cryptography/Asymptotic/MultiMessage.lean: candidates=33 FAIL (rc=1, error lines=15)
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:155:2 [theorem TCSlib.Cryptography.multiMsgAdv_boundedBy] Type mismatch
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:155:39 [theorem TCSlib.Cryptography.multiMsgAdv_boundedBy] Invalid projection: Type of
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:241:10 [theorem TCSlib.Cryptography.pushesUniform_comp_injective] Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:286:4 [theorem TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le] Type mismatch
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:288:92 [theorem TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le] No goals to be solved
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:290:4 [theorem TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le] Type mismatch
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:291:78 [theorem TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le] No goals to be solved
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:520:75 [def TCSlib.Cryptography.prfScheme] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:520:91 [def TCSlib.Cryptography.prfScheme] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:521:64 [def TCSlib.Cryptography.prfScheme] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:532:2 [theorem TCSlib.Cryptography.encodeList_eq_flatMap] Type mismatch
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:552:82 [theorem TCSlib.Cryptography.prfScheme_multiEncDist] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:561:79 [theorem TCSlib.Cryptography.prfScheme_multiEncDist] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:562:10 [theorem TCSlib.Cryptography.prfScheme_multiEncDist] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/MultiMessage.lean:605:8 [theorem TCSlib.Cryptography.prfScheme_multiMessageSecure] Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean: candidates=29 FAIL (rc=1, error lines=13)
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:228:4 [theorem TCSlib.Cryptography.MultiMsg.encodeHist_eq_flatMap] 'show' tactic failed, pattern
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:226:2 [theorem TCSlib.Cryptography.MultiMsg.encodeHist_eq_flatMap] Type mismatch
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:236:71 [theorem TCSlib.Cryptography.MultiMsg.eval_histBlockLen] Type mismatch
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:320:2 [theorem TCSlib.Cryptography.MultiMsg.dbl_append] Type mismatch
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:334:2 [theorem TCSlib.Cryptography.MultiMsg.zipWith_xor_dbl] Type mismatch
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:354:4 [theorem TCSlib.Cryptography.MultiMsg.zipWith_xor_histBlock_maskBlock] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:365:2 [theorem TCSlib.Cryptography.MultiMsg.zipWith_xor_histBlock_maskBlock] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:391:4 [theorem TCSlib.Cryptography.MultiMsg.take_drop_ofFn_blocks] 'show' tactic failed, pattern
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:544:14 [theorem TCSlib.Cryptography.MultiMsg.decodeOracleMove_ret] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:544:14 [theorem TCSlib.Cryptography.MultiMsg.decodeOracleMove_ret] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:680:85 [theorem TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt] Type mismatch
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:731:6 [theorem TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:741:2 [theorem TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt] Type mismatch
TCSlib/Cryptography/Asymptotic/PRF.lean: candidates=43 FAIL (rc=1, error lines=24)
   TCSlib/Cryptography/Asymptotic/PRF.lean:144:47 [theorem TCSlib.Cryptography.OracleEnsemble.random_O] Type mismatch
   TCSlib/Cryptography/Asymptotic/PRF.lean:339:10 [theorem TCSlib.Cryptography.OracleEnsemble.Indist.symm] typeclass instance problem is stuck, it is often due to metavariables
   TCSlib/Cryptography/Asymptotic/PRF.lean:360:30 [theorem TCSlib.Cryptography.OracleEnsemble.Indist.trans] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/PRF.lean:393:65 [structure TCSlib.Cryptography.PRF] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/PRF.lean:400:61 [theorem TCSlib.Cryptography.prfAdv_toOracleAdversary] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/PRF.lean:401:20 [theorem TCSlib.Cryptography.prfAdv_toOracleAdversary] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/PRF.lean:411:14 [theorem TCSlib.Cryptography.PRF.negligible_prfAdv] (lean.unknownIdentifier): Unknown identifier `prfAdv_toOracleAdversary`
   TCSlib/Cryptography/Asymptotic/PRF.lean:420:7 [def TCSlib.Cryptography.doublingEnsemble] Type mismatch
   TCSlib/Cryptography/Asymptotic/PRF.lean:443:2 [theorem TCSlib.Cryptography.DoublingPRG.negligible_prgAdv] Type mismatch
   TCSlib/Cryptography/Asymptotic/PRF.lean:454:2 [theorem TCSlib.Cryptography.two_mul_add_one_expands] 'show' tactic failed, pattern
   TCSlib/Cryptography/Asymptotic/PRF.lean:463:47 [def TCSlib.Cryptography.PRG.doubling] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/PRF.lean:465:0 [theorem TCSlib.Cryptography.PRG.doubling_apply] Not a definitional equality: the left-hand side
   TCSlib/Cryptography/Asymptotic/PRF.lean:470:80 [theorem TCSlib.Cryptography.PRG.doubling_apply] Type mismatch
   TCSlib/Cryptography/Asymptotic/PRF.lean:487:86 [theorem TCSlib.Cryptography.PRG.Secure.truncate] Type mismatch
   TCSlib/Cryptography/Asymptotic/PRF.lean:488:9 [theorem TCSlib.Cryptography.PRG.Secure.truncate] Invalid `⟨...⟩` notation: The expected type `(oneBit P.truncate).Secure` is not an inductive type
   TCSlib/Cryptography/Asymptotic/PRF.lean:489:2 [theorem TCSlib.Cryptography.PRG.Secure.truncate] No goals to be solved
   TCSlib/Cryptography/Asymptotic/PRF.lean:511:74 [theorem TCSlib.Cryptography.PRG.Secure.doubling] Type mismatch
   TCSlib/Cryptography/Asymptotic/PRF.lean:565:8 [theorem TCSlib.Cryptography.thm_97_3_1] typeclass instance problem is stuck, it is often due to metavariables
   TCSlib/Cryptography/Asymptotic/PRF.lean:613:67 [theorem TCSlib.Cryptography.decodeOracleMove_eq] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/PRF.lean:613:67 [theorem TCSlib.Cryptography.decodeOracleMove_eq] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/PRF.lean:615:16 [theorem TCSlib.Cryptography.decodeOracleMove_eq] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/PRF.lean:615:16 [theorem TCSlib.Cryptography.decodeOracleMove_eq] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/PRF.lean:688:4 [theorem TCSlib.Cryptography.exists_ggmBitsDist_nuppt] Type mismatch
   TCSlib/Cryptography/Asymptotic/PRF.lean:698:8 [theorem TCSlib.Cryptography.exists_ggmBitsDist_nuppt] Application type mismatch: The argument
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean: candidates=32 FAIL (rc=1, error lines=12)
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:89:4 [theorem TCSlib.Cryptography.drop_take_ofFn_blocks] 'show' tactic failed, pattern
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:111:2 [theorem TCSlib.Cryptography.take_ofFn_splitHalves] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:119:2 [theorem TCSlib.Cryptography.drop_ofFn_splitHalves] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:179:74 [theorem Complexity.NUPPT.coins_preComp] Type mismatch
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:192:90 [theorem Complexity.NUPPT.runAt_preComp] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:230:25 [theorem TCSlib.Cryptography.PRG.Secure.truncateTo_easy] Invalid projection: Expected a value whose type is a structure
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:230:9 [theorem TCSlib.Cryptography.PRG.Secure.truncateTo_easy] Tactic `rcases` failed: `x✝ : ?m.14` is not an inductive datatype
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:255:15 [theorem TCSlib.Cryptography.PRG.Secure.truncateTo_negligible] Invalid projection: Expected a value whose type is a structure
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:252:42 [theorem TCSlib.Cryptography.PRG.Secure.truncateTo_negligible] unsolved goals
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:385:18 [theorem TCSlib.Cryptography.ggmEval_poly] Type mismatch
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:386:41 [theorem TCSlib.Cryptography.ggmEval_poly] Application type mismatch: The argument
   TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:410:2 [theorem TCSlib.Cryptography.ggmEval_ofFn] 'show' tactic failed, pattern
TCSlib/Cryptography/Foundations/Experiments.lean: candidates=5 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Foundations/Probability.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Advantage.lean: candidates=4 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/BitCodec.lean: candidates=4 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/Experiments.lean: candidates=11 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/Machines.lean: candidates=10 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/QueryTree.lean: candidates=9 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/Strategies.lean: candidates=13 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Efficiency.lean: candidates=19 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Hopping.lean: candidates=6 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Machines.lean: candidates=4 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/OracleComp.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Probability.lean: candidates=1 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Protocols.lean: candidates=2 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Simulate.lean: candidates=3 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean: candidates=5 FAIL (rc=1, error lines=2)
   TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean:77:65 [theorem TCSlib.Cryptography.prfAdv_eq] Type mismatch
   TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean:82:2 [theorem TCSlib.Cryptography.prfAdv_nonneg] Type mismatch
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean: candidates=11 FAIL (rc=1, error lines=3)
   own seal line 68: attribute [local irreducible] uprob acceptProb -> -- (covered by the seal line) attribute [local irreducible] uprob acceptProb
   TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:132:53 [theorem TCSlib.Cryptography.hybridProb_top] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:217:40 [theorem TCSlib.Cryptography.hybridProb_level] Application type mismatch: The argument
   TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:217:51 [theorem TCSlib.Cryptography.hybridProb_level] Function expected at
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean: candidates=6 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean: candidates=0 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean: candidates=11 FAIL (rc=1, error lines=5)
   own seal line 68: attribute [local irreducible] uprob acceptProb -> -- (covered by the seal line) attribute [local irreducible] uprob acceptProb
   TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:228:24 [theorem TCSlib.Cryptography.subHybridProb_zero] Tactic `rfl` failed: The left-hand side
   TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:236:33 [theorem TCSlib.Cryptography.subHybridProb_zero] Function expected at
   TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:256:26 [theorem TCSlib.Cryptography.subHybridProb_top] Function expected at
   TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:260:4 [theorem TCSlib.Cryptography.subHybridProb_top] Type mismatch
   TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:266:32 [theorem TCSlib.Cryptography.subHybridProb_top] Function expected at
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean: candidates=7 FAIL (rc=1, error lines=1)
   TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:128:11 [theorem TCSlib.Cryptography.Strategy.pairFstD_encodeMsgs] Tactic `rfl` failed: The left-hand side

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/seal-r3union.log =====

# supplementary: automatic candidates + the r3 hand-picked names they lack (r3cross.txt), same entries
  not in the automatic list: TCSlib/Cryptography/Games/Machines.lean TCSlib.Cryptography.Games.OracleComp.bind
  not in the automatic list: TCSlib/Cryptography/Games/Bridges/Machines.lean Complexity.NUPPT.toCompOn
  not in the automatic list: TCSlib/Cryptography/Games/Bridges/Machines.lean TCSlib.Cryptography.Games.OracleComp.bind
  not in the automatic list: TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean TCSlib.Cryptography.Games.OracleComp.bind
  not in the automatic list: TCSlib/Cryptography/Asymptotic/PRF.lean TCSlib.Cryptography.Games.OracleComp.bind
  not in the automatic list: TCSlib/Cryptography/Games/Bridges/Strategies.lean TCSlib.Cryptography.Protocol.transcript
74 names in the r3 table (13 files); 6 not in the automatic lists
TCSlib/Cryptography/Asymptotic/PRF.lean: candidates=44; unsealed for 17 named declaration(s) PASS (rc=0, error lines=0)
   unseal TCSlib.Cryptography.DoublingPRG.negligible_prgAdv (lines 437-443): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.OracleEnsemble.Indist.symm (lines 329-341): TCSlib.Cryptography.distAdv
   unseal TCSlib.Cryptography.OracleEnsemble.Indist.trans (lines 343-364): TCSlib.Cryptography.distAdv
   unseal TCSlib.Cryptography.OracleEnsemble.random_O (lines 141-144): TCSlib.Cryptography.randomFunction
   unseal TCSlib.Cryptography.PRF (lines 378-393): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.PRF.negligible_prfAdv (lines 404-411): Complexity.PolyExpr.eval TCSlib.Cryptography.prfAdv
   unseal TCSlib.Cryptography.PRG.Secure.doubling (lines 493-515): Complexity.PolyExpr.eval TCSlib.Cryptography.Ensemble.Pseudorandom TCSlib.Cryptography.PRG.expand TCSlib.Cryptography.prgAdv
   unseal TCSlib.Cryptography.PRG.Secure.truncate (lines 472-491): Complexity.PolyExpr.eval TCSlib.Cryptography.Ensemble.Pseudorandom TCSlib.Cryptography.PRG.Easy TCSlib.Cryptography.PRG.Secure TCSlib.Cryptography.PRG.ensemble TCSlib.Cryptography.PRG.oneBit TCSlib.Cryptography.prgAdv
   unseal TCSlib.Cryptography.PRG.doubling (lines 457-463): Complexity.PolyExpr.eval TCSlib.Cryptography.PRG.expand
   unseal TCSlib.Cryptography.PRG.doubling_apply (lines 465-470): TCSlib.Cryptography.PRG.expand
   unseal TCSlib.Cryptography.decodeOracleMove_eq (lines 585-624): TCSlib.Cryptography.GGMRed.queryOf TCSlib.Cryptography.GGMRed.verdictOf Turing.pairDecode
   unseal TCSlib.Cryptography.doublingEnsemble (lines 415-420): Complexity.PolyExpr.eval
   unseal TCSlib.Cryptography.exists_ggmBitsDist_nuppt (lines 648-707): Complexity.NUPPT.coinLen Complexity.PolyExpr.eval TCSlib.Cryptography.GGMRed.coinStr TCSlib.Cryptography.GGMRed.ggmRedMachine TCSlib.Cryptography.GGMRed.histEnc
   unseal TCSlib.Cryptography.ggmPRF_prf (lines 731-801): Complexity.PolyExpr.eval TCSlib.Cryptography.Negligible TCSlib.Cryptography.prfAdv TCSlib.Cryptography.prgAdv
   unseal TCSlib.Cryptography.prfAdv_toOracleAdversary (lines 395-402): Complexity.PolyExpr.eval TCSlib.Cryptography.prfAdv
   unseal TCSlib.Cryptography.thm_97_3_1 (lines 554-566): Complexity.PolyExpr.eval TCSlib.Cryptography.ggmBits
   unseal TCSlib.Cryptography.two_mul_add_one_expands (lines 450-455): Complexity.PolyExpr.eval
TCSlib/Cryptography/Games/Bridges/Machines.lean: candidates=12 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Bridges/Strategies.lean: candidates=14 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Games/Machines.lean: candidates=5 PASS (rc=0, error lines=0)
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean: candidates=1 PASS (rc=0, error lines=0)

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/scan.log =====

# rule-10 source scan over 26 files; hit = name resolving to a definition of another TCSlib module
# file:line	tactic	token	kind	foreign definition	its module	[declaration]	source line
## (c1) unfold/delta/rw/simp/dsimp lemma-list hits: 80
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:164	unfold	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem acceptProb_oracleDist_multiMsgAdv]	unfold acceptProb
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:168	simp	oracleDist	foreign-def	TCSlib.Cryptography.oracleDist	TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary	[theorem acceptProb_oracleDist_multiMsgAdv]	simp only [oracleDist, multiMsgAdv, eval_chainTree, Equiv.prodAssoc_apply]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:180	rw	prfAdv	foreign-def	TCSlib.Cryptography.prfAdv	TCSlib.Cryptography.Pseudorandom.Functions.Defs	[theorem prfAdv_multiMsgAdv]	rw [prfAdv, distAdv, distAdv, acceptProb_oracleDist_multiMsgAdv,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:180	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem prfAdv_multiMsgAdv]	rw [prfAdv, distAdv, distAdv, acceptProb_oracleDist_multiMsgAdv,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:180	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem prfAdv_multiMsgAdv]	rw [prfAdv, distAdv, distAdv, acceptProb_oracleDist_multiMsgAdv,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:244	simp	uexp	foreign-def	TCSlib.Cryptography.uexp	TCSlib.Cryptography.Foundations.Probability	[theorem pushesUniform_comp_injective]	simp only [uexp, univ_eq_empty, sum_empty, zero_div]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:298	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_prfEncReal_random_otp_le]	rw [distAdv, ha, hb]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:358	simp	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_prfEncReal_le]	simp only [distAdv] at h12 h56 h23 h45 ⊢
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:458	simp	NUPPT.inArg	foreign-def	Complexity.NUPPT.inArg	TCSlib.Complexity.Randomized.Closure	[theorem runAt_prfEnc]	simp [prfEncFun, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:458	simp	NUPPT.inCoins	foreign-def	Complexity.NUPPT.inCoins	TCSlib.Complexity.Randomized.Closure	[theorem runAt_prfEnc]	simp [prfEncFun, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:458	simp	NUPPT.advInput	foreign-def	Complexity.NUPPT.advInput	TCSlib.Complexity.Randomized.PPT	[theorem runAt_prfEnc]	simp [prfEncFun, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:469	simp	NUPPT.inArg	foreign-def	Complexity.NUPPT.inArg	TCSlib.Complexity.Randomized.Closure	[theorem runAt_prfDec]	simp [prfDecFun, prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, hr, hc]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:469	simp	NUPPT.inParam	foreign-def	Complexity.NUPPT.inParam	TCSlib.Complexity.Randomized.Closure	[theorem runAt_prfDec]	simp [prfDecFun, prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, hr, hc]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:469	simp	NUPPT.advInput	foreign-def	Complexity.NUPPT.advInput	TCSlib.Complexity.Randomized.PPT	[theorem runAt_prfDec]	simp [prfDecFun, prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, hr, hc]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:482	simp	NUPPT.inArg	foreign-def	Complexity.NUPPT.inArg	TCSlib.Complexity.Randomized.Closure	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp only [prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, pairFstD_pairEncode,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:482	simp	NUPPT.inParam	foreign-def	Complexity.NUPPT.inParam	TCSlib.Complexity.Randomized.Closure	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp only [prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, pairFstD_pairEncode,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:482	simp	NUPPT.advInput	foreign-def	Complexity.NUPPT.advInput	TCSlib.Complexity.Randomized.PPT	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp only [prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, pairFstD_pairEncode,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:486	simp	decodeFin	foreign-def	TCSlib.Cryptography.decodeFin	TCSlib.Cryptography.Asymptotic.Adversary	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp [decodeFin, NUPPT.inParam, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:486	simp	NUPPT.inParam	foreign-def	Complexity.NUPPT.inParam	TCSlib.Complexity.Randomized.Closure	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp [decodeFin, NUPPT.inParam, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:486	simp	NUPPT.advInput	foreign-def	Complexity.NUPPT.advInput	TCSlib.Complexity.Randomized.PPT	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp [decodeFin, NUPPT.inParam, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:535	simp	pairEncode	foreign-def	Turing.pairEncode	TCSlib.Complexity.TuringMachine.Encoding	[theorem encodeList_eq_flatMap]	simp [pairEncode]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:553	unfold	PrivateKeyScheme.multiEncDist	foreign-def	TCSlib.Cryptography.PrivateKeyScheme.multiEncDist	TCSlib.Cryptography.Asymptotic.Encryption	[theorem prfScheme_multiEncDist]	unfold PrivateKeyScheme.multiEncDist encodeTuple
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:649	rw	NUPPT.distinguisherL	foreign-def	Complexity.NUPPT.distinguisherL	TCSlib.Cryptography.Asymptotic.Adversary	[theorem prfScheme_multiMessageSecure]	rw [hφ g w.1 w.2, multiMsgAdv, eval_chainTree, NUPPT.distinguisherL, encodeTuple_eq_flatten]
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:79	unfold	uexp	foreign-def	TCSlib.Cryptography.uexp	TCSlib.Cryptography.Foundations.Probability	[theorem abs_uexp_le_uexp_abs]	unfold uexp
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:230	simp	pairEncode	foreign-def	Turing.pairEncode	TCSlib.Complexity.TuringMachine.Encoding	[theorem encodeHist_eq_flatMap]	simp [histBlock, pairEncode]
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:540	simp	decodeOracleMove	foreign-def	TCSlib.Cryptography.decodeOracleMove	TCSlib.Cryptography.Asymptotic.PRF	[theorem decodeOracleMove_query]	simp [decodeOracleMove, pairDecode_pairEncode, decodeFin_ofFn]
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:656	simp	NUPPT.coinLen	foreign-def	Complexity.NUPPT.coinLen	TCSlib.Complexity.Randomized.PPT	[theorem exists_queryChain_nuppt]	simp only [NUPPT.coinLen, hBc, hC₂c, hCc, hD₁c, NUPPT.coins_ofPolyTimeUniform,
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:671	simp	NUPPT.coinLen	foreign-def	Complexity.NUPPT.coinLen	TCSlib.Complexity.Randomized.PPT	[theorem exists_queryChain_nuppt]	have hD₁len : D₁.coinLen n = D.coinLen n := by simp only [NUPPT.coinLen, hD₁c]
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:730	rw	buildTree	foreign-def	TCSlib.Cryptography.buildTree	TCSlib.Cryptography.Asymptotic.PRF	[theorem exists_queryChain_nuppt]	rw [Nat.sub_zero, buildTree, hret]
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:735	rw	buildTree	foreign-def	TCSlib.Cryptography.buildTree	TCSlib.Cryptography.Asymptotic.PRF	[theorem exists_queryChain_nuppt]	rw [buildTree, hquery _ hk, QueryTree.eval_query, ← hρ' _ hk, ← hist_succ,
TCSlib/Cryptography/Asymptotic/PRF.lean:325	simp	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem OracleEnsemble.Indist.refl]	simp [distAdv]
TCSlib/Cryptography/Asymptotic/PRF.lean:583	simpa	prgAdv	foreign-def	TCSlib.Cryptography.prgAdv	TCSlib.Cryptography.Pseudorandom.Generators	[theorem thm_97_3_2]	simpa only [prgAdv, distAdv_ggmBitsDist] using h
TCSlib/Cryptography/Asymptotic/PRF.lean:603	simp	GGMRed.queryOf	foreign-def	TCSlib.Cryptography.GGMRed.queryOf	TCSlib.Cryptography.Asymptotic.GGMReduction	[theorem decodeOracleMove_eq]	simp only [GGMRed.queryOf, hx]
TCSlib/Cryptography/Asymptotic/PRF.lean:611	simp	GGMRed.verdictOf	foreign-def	TCSlib.Cryptography.GGMRed.verdictOf	TCSlib.Cryptography.Asymptotic.GGMReduction	[theorem decodeOracleMove_eq]	simp [GGMRed.verdictOf, pairEncode]
TCSlib/Cryptography/Asymptotic/PRF.lean:611	simp	pairEncode	foreign-def	Turing.pairEncode	TCSlib.Complexity.TuringMachine.Encoding	[theorem decodeOracleMove_eq]	simp [GGMRed.verdictOf, pairEncode]
TCSlib/Cryptography/Asymptotic/PRF.lean:623	simp	GGMRed.verdictOf	foreign-def	TCSlib.Cryptography.GGMRed.verdictOf	TCSlib.Cryptography.Asymptotic.GGMReduction	[theorem decodeOracleMove_eq]	simp only [OracleMove.ret.injEq, GGMRed.verdictOf]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:103	simp	prefixAt	foreign-def	TCSlib.Cryptography.prefixAt	TCSlib.Cryptography.Pseudorandom.Functions.GGM	[theorem ofFn_prefixAt]	simp only [prefixAt, hk, dite_true]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:133	simp	pairSel	foreign-def	TCSlib.Cryptography.pairSel	TCSlib.Cryptography.Pseudorandom.Functions.GGM	[theorem selHalf_ofFn]	· simp only [selHalf, pairSel, Bool.false_eq_true, if_false, hu, take_ofFn_splitHalves]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:134	simp	pairSel	foreign-def	TCSlib.Cryptography.pairSel	TCSlib.Cryptography.Pseudorandom.Functions.GGM	[theorem selHalf_ofFn]	· simp only [selHalf, pairSel, if_true, hu, drop_ofFn_splitHalves]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	runAtL	foreign-def	Complexity.NUPPT.runAtL	TCSlib.Complexity.Randomized.PPT	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	advInput	foreign-def	Complexity.NUPPT.advInput	TCSlib.Complexity.Randomized.PPT	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	layout	foreign-def	Complexity.NUPPT.layout	TCSlib.Complexity.Randomized.Closure	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	inParam	foreign-def	Complexity.NUPPT.inParam	TCSlib.Complexity.Randomized.Closure	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	inArg	foreign-def	Complexity.NUPPT.inArg	TCSlib.Complexity.Randomized.Closure	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	inAdvice	foreign-def	Complexity.NUPPT.inAdvice	TCSlib.Complexity.Randomized.Closure	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	inCoins	foreign-def	Complexity.NUPPT.inCoins	TCSlib.Complexity.Randomized.Closure	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:261	unfold	NUPPT.distinguisher	foreign-def	Complexity.NUPPT.distinguisher	TCSlib.Cryptography.Asymptotic.Adversary	[theorem PRG.Secure.truncateTo_negligible]	unfold NUPPT.distinguisher
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:268	rw	prgAdv	foreign-def	TCSlib.Cryptography.prgAdv	TCSlib.Cryptography.Pseudorandom.Generators	[theorem PRG.Secure.truncateTo_negligible]	rw [hfun, prgAdv, prgAdv,
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:268	rw	prgAdv	foreign-def	TCSlib.Cryptography.prgAdv	TCSlib.Cryptography.Pseudorandom.Generators	[theorem PRG.Secure.truncateTo_negligible]	rw [hfun, prgAdv, prgAdv,
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:270	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem PRG.Secure.truncateTo_negligible]	t (Fin.castLE (hm n) i)) (P.G n) id (D.distinguisher n (m.eval n)), distAdv, distAdv]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:270	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem PRG.Secure.truncateTo_negligible]	t (Fin.castLE (hm n) i)) (P.G n) id (D.distinguisher n (m.eval n)), distAdv, distAdv]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:312	simp	pairSndD	foreign-def	Complexity.pairSndD	TCSlib.Complexity.ClassNP.PolyTimePairing	[theorem length_ggmStep_le]	| none => exact absurd (by simp [pairSndD, hd]) h
TCSlib/Cryptography/Foundations/Experiments.lean:160	rw	statDist	foreign-def	TCSlib.InformationTheory.statDist	TCSlib.InformationTheory.StatisticalDistance	[theorem abs_sum_sub_le_statDist]	rw [statDist]
TCSlib/Cryptography/Foundations/Experiments.lean:175	rw	uexp	foreign-def	TCSlib.Cryptography.uexp	TCSlib.Cryptography.Foundations.Probability	[theorem distAdv_le_statDist]	rw [distAdv, acceptProb_eq_uexp_sum_map X, acceptProb_eq_uexp_sum_map Y, uexp, uexp,
TCSlib/Cryptography/Foundations/Experiments.lean:175	rw	uexp	foreign-def	TCSlib.Cryptography.uexp	TCSlib.Cryptography.Foundations.Probability	[theorem distAdv_le_statDist]	rw [distAdv, acceptProb_eq_uexp_sum_map X, acceptProb_eq_uexp_sum_map Y, uexp, uexp,
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:148	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem hybridProb_eq_level_prg]	rw [hybridProb, acceptProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:148	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem hybridProb_eq_level_prg]	rw [hybridProb, acceptProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:150	simp	oracleDist	foreign-def	TCSlib.Cryptography.oracleDist	TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary	[theorem hybridProb_eq_level_prg]	simp only [oracleDist, levelAdv, eval_simulate, comp_apply]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:180	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem hybridProb_eq_level_random]	rw [hybridProb, ← acceptProb_comp_equiv e, acceptProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:180	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem hybridProb_eq_level_random]	rw [hybridProb, ← acceptProb_comp_equiv e, acceptProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:182	simp	oracleDist	foreign-def	TCSlib.Cryptography.oracleDist	TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary	[theorem hybridProb_eq_level_random]	simp only [oracleDist, levelAdv, eval_simulate, comp_apply, randomFunction, id, e,
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:182	simp	randomFunction	foreign-def	TCSlib.Cryptography.randomFunction	TCSlib.Cryptography.Pseudorandom.Functions.Defs	[theorem hybridProb_eq_level_random]	simp only [oracleDist, levelAdv, eval_simulate, comp_apply, randomFunction, id, e,
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:236	rw	prfAdv	foreign-def	TCSlib.Cryptography.prfAdv	TCSlib.Cryptography.Pseudorandom.Functions.Defs	[theorem ggm_prfAdv_le]	rw [prfAdv, distAdv, ← hybridProb_zero, ← hybridProb_top]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:236	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem ggm_prfAdv_le]	rw [prfAdv, distAdv, ← hybridProb_zero, ← hybridProb_top]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:312	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [acceptProb, acceptProb]; rfl
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:312	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [acceptProb, acceptProb]; rfl
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:315	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [acceptProb, acceptProb]; rfl
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:315	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [acceptProb, acceptProb]; rfl
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:316	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [distAdv, distAdv, h, h']
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:316	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [distAdv, distAdv, h, h']
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:145	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem acceptProb_tableDist_prg]	rw [acceptProb, ← uprob_comp_equiv e
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:150	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem acceptProb_tableDist_prg]	rw [subHybridProb, acceptProb, ← uprob_comp_equiv (Equiv.prodAssoc _ _ _).symm
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:192	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem acceptProb_tableDist_uniform]	rw [acceptProb, ← uprob_comp_equiv e
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:198	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem acceptProb_tableDist_uniform]	rw [subHybridProb, acceptProb, ← uprob_comp_equiv e'
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:217	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem subHybridProb_zero]	rw [subHybridProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:225	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem subHybridProb_zero]	rw [acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:251	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem subHybridProb_top]	rw [subHybridProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:259	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem subHybridProb_top]	rw [acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:288	unfold	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem table_hybrid]	unfold distAdv
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:467	rw	uexp	foreign-def	TCSlib.Cryptography.uexp	TCSlib.Cryptography.Foundations.Probability	[theorem exists_proverCoins_le]	rw [sum_const, card_univ, nsmul_eq_mul, uexp, mul_div_cancel₀ _ hcard.ne']
## (c2) show/change steps on a line where the seal failed: 5 (of 17 show/change occurrences, all checked by the seal)
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:228	show	[theorem encodeHist_eq_flatMap]	show pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) = _
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:391	show	[theorem take_drop_ofFn_blocks]	show w _ = w (finProdFinEquiv (⟨i, hi⟩, _))
TCSlib/Cryptography/Asymptotic/PRF.lean:454	show	[theorem two_mul_add_one_expands]	show n < 2 * n + 1
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:89	show	[theorem drop_take_ofFn_blocks]	show w _ = w (finProdFinEquiv (⟨k, hk⟩, ⟨j, by omega⟩))
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:410	show	[theorem ggmEval_ofFn]	show walk _ s (List.ofFn x) = ggmFrom (splitHalves ∘ G) x 0 s
## (c3) proof terms referring to a generated equation lemma of a foreign TCSlib definition (collector): 21
# module	owner declaration	constant	equation lemma
TCSlib.Cryptography.Asymptotic.MultiMessage	TCSlib.Cryptography.prfAdv_multiMsgAdv	TCSlib.Cryptography.prfAdv_multiMsgAdv	TCSlib.Cryptography.distAdv.eq_1
TCSlib.Cryptography.Asymptotic.MultiMessage	TCSlib.Cryptography.prfAdv_multiMsgAdv	TCSlib.Cryptography.prfAdv_multiMsgAdv	TCSlib.Cryptography.prfAdv.eq_1
TCSlib.Cryptography.Asymptotic.MultiMessage	TCSlib.Cryptography.prfScheme_multiMessageSecure	TCSlib.Cryptography.prfScheme_multiMessageSecure	Complexity.NUPPT.distinguisherL.eq_1
TCSlib.Cryptography.Asymptotic.MultiMessage	TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le	TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le	TCSlib.Cryptography.distAdv.eq_1
TCSlib.Cryptography.Asymptotic.MultiMessageLemmas	TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt	TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt	TCSlib.Cryptography.buildTree.eq_1
TCSlib.Cryptography.Asymptotic.MultiMessageLemmas	TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt	TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt	TCSlib.Cryptography.buildTree.eq_2
TCSlib.Cryptography.Asymptotic.PRFLemmas	TCSlib.Cryptography.PRG.Secure.truncateTo_negligible	TCSlib.Cryptography.PRG.Secure.truncateTo_negligible	TCSlib.Cryptography.distAdv.eq_1
TCSlib.Cryptography.Asymptotic.PRFLemmas	TCSlib.Cryptography.PRG.Secure.truncateTo_negligible	TCSlib.Cryptography.PRG.Secure.truncateTo_negligible	TCSlib.Cryptography.prgAdv.eq_1
TCSlib.Cryptography.Foundations.Experiments	TCSlib.Cryptography.distAdv_le_statDist	TCSlib.Cryptography.distAdv_le_statDist	TCSlib.Cryptography.uexp.eq_1
TCSlib.Cryptography.Foundations.Experiments	TCSlib.Cryptography.abs_sum_sub_le_statDist	TCSlib.Cryptography.abs_sum_sub_le_statDist	TCSlib.InformationTheory.statDist.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.hybridProb_eq_level_prg	TCSlib.Cryptography.hybridProb_eq_level_prg	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.hybridProb_eq_level_random	TCSlib.Cryptography.hybridProb_eq_level_random	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.ggm_prfAdv_le	TCSlib.Cryptography.ggm_prfAdv_le	TCSlib.Cryptography.distAdv.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.ggm_prfAdv_le	TCSlib.Cryptography.ggm_prfAdv_le	TCSlib.Cryptography.prfAdv.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.distAdv_ggmBitsDist	TCSlib.Cryptography.distAdv_ggmBitsDist	TCSlib.Cryptography.distAdv.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.distAdv_ggmBitsDist	TCSlib.Cryptography.distAdv_ggmBitsDist	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids	TCSlib.Cryptography.subHybridProb_top	TCSlib.Cryptography.subHybridProb_top	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids	TCSlib.Cryptography.subHybridProb_zero	TCSlib.Cryptography.subHybridProb_zero	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids	TCSlib.Cryptography.acceptProb_tableDist_uniform	TCSlib.Cryptography.acceptProb_tableDist_uniform	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids	TCSlib.Cryptography.acceptProb_tableDist_prg	TCSlib.Cryptography.acceptProb_tableDist_prg	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.ZeroKnowledge.Interaction	TCSlib.Cryptography.Protocol.exists_proverCoins_le	TCSlib.Cryptography.Protocol.exists_proverCoins_le	TCSlib.Cryptography.uexp.eq_1

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/scan-base.log =====

# rule-10 source scan over 26 files at 27ae72da62119ebdde380b8cb2d8c183b59fa2bf; hit = name resolving to a definition of another TCSlib module
# file:line	tactic	token	kind	foreign definition	its module	[declaration]	source line
## (c1) unfold/delta/rw/simp/dsimp lemma-list hits: 84
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:160	unfold	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem acceptProb_oracleDist_multiMsgAdv]	unfold acceptProb
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:164	simp	oracleDist	foreign-def	TCSlib.Cryptography.oracleDist	TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary	[theorem acceptProb_oracleDist_multiMsgAdv]	simp only [oracleDist, multiMsgAdv, eval_chainTree, Equiv.prodAssoc_apply]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:176	rw	prfAdv	foreign-def	TCSlib.Cryptography.prfAdv	TCSlib.Cryptography.Pseudorandom.Functions.Defs	[theorem prfAdv_multiMsgAdv]	rw [prfAdv, distAdv, distAdv, acceptProb_oracleDist_multiMsgAdv,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:176	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem prfAdv_multiMsgAdv]	rw [prfAdv, distAdv, distAdv, acceptProb_oracleDist_multiMsgAdv,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:176	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem prfAdv_multiMsgAdv]	rw [prfAdv, distAdv, distAdv, acceptProb_oracleDist_multiMsgAdv,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:240	simp	uexp	foreign-def	TCSlib.Cryptography.uexp	TCSlib.Cryptography.Foundations.Probability	[theorem pushesUniform_comp_injective]	simp only [uexp, univ_eq_empty, sum_empty, zero_div]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:294	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_prfEncReal_random_otp_le]	rw [distAdv, ha, hb]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:354	simp	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_prfEncReal_le]	simp only [distAdv] at h12 h56 h23 h45 ⊢
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:454	simp	NUPPT.inArg	foreign-def	Complexity.NUPPT.inArg	TCSlib.Complexity.Randomized.Closure	[theorem runAt_prfEnc]	simp [prfEncFun, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:454	simp	NUPPT.inCoins	foreign-def	Complexity.NUPPT.inCoins	TCSlib.Complexity.Randomized.Closure	[theorem runAt_prfEnc]	simp [prfEncFun, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:454	simp	NUPPT.advInput	foreign-def	Complexity.NUPPT.advInput	TCSlib.Complexity.Randomized.PPT	[theorem runAt_prfEnc]	simp [prfEncFun, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:465	simp	NUPPT.inArg	foreign-def	Complexity.NUPPT.inArg	TCSlib.Complexity.Randomized.Closure	[theorem runAt_prfDec]	simp [prfDecFun, prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, hr, hc]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:465	simp	NUPPT.inParam	foreign-def	Complexity.NUPPT.inParam	TCSlib.Complexity.Randomized.Closure	[theorem runAt_prfDec]	simp [prfDecFun, prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, hr, hc]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:465	simp	NUPPT.advInput	foreign-def	Complexity.NUPPT.advInput	TCSlib.Complexity.Randomized.PPT	[theorem runAt_prfDec]	simp [prfDecFun, prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, hr, hc]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:478	simp	NUPPT.inArg	foreign-def	Complexity.NUPPT.inArg	TCSlib.Complexity.Randomized.Closure	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp only [prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, pairFstD_pairEncode,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:478	simp	NUPPT.inParam	foreign-def	Complexity.NUPPT.inParam	TCSlib.Complexity.Randomized.Closure	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp only [prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, pairFstD_pairEncode,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:478	simp	NUPPT.advInput	foreign-def	Complexity.NUPPT.advInput	TCSlib.Complexity.Randomized.PPT	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp only [prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, pairFstD_pairEncode,
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:482	simp	decodeFin	foreign-def	TCSlib.Cryptography.decodeFin	TCSlib.Cryptography.Asymptotic.Adversary	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp [decodeFin, NUPPT.inParam, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:482	simp	NUPPT.inParam	foreign-def	Complexity.NUPPT.inParam	TCSlib.Complexity.Randomized.Closure	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp [decodeFin, NUPPT.inParam, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:482	simp	NUPPT.advInput	foreign-def	Complexity.NUPPT.advInput	TCSlib.Complexity.Randomized.PPT	[theorem decodeFin_runAt_prfDec_of_not_wf]	simp [decodeFin, NUPPT.inParam, NUPPT.advInput]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:531	simp	pairEncode	foreign-def	Turing.pairEncode	TCSlib.Complexity.TuringMachine.Encoding	[theorem encodeList_eq_flatMap]	simp [pairEncode]
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:549	unfold	PrivateKeyScheme.multiEncDist	foreign-def	TCSlib.Cryptography.PrivateKeyScheme.multiEncDist	TCSlib.Cryptography.Asymptotic.Encryption	[theorem prfScheme_multiEncDist]	unfold PrivateKeyScheme.multiEncDist encodeTuple
TCSlib/Cryptography/Asymptotic/MultiMessage.lean:645	rw	NUPPT.distinguisherL	foreign-def	Complexity.NUPPT.distinguisherL	TCSlib.Cryptography.Asymptotic.Adversary	[theorem prfScheme_multiMessageSecure]	rw [hφ g w.1 w.2, multiMsgAdv, eval_chainTree, NUPPT.distinguisherL, encodeTuple_eq_flatten]
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:79	unfold	uexp	foreign-def	TCSlib.Cryptography.uexp	TCSlib.Cryptography.Foundations.Probability	[theorem abs_uexp_le_uexp_abs]	unfold uexp
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:192	unfold	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem acceptProb_oracleDist_congr_equiv]	unfold acceptProb oracleDist
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:192	unfold	oracleDist	foreign-def	TCSlib.Cryptography.oracleDist	TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary	[theorem acceptProb_oracleDist_congr_equiv]	unfold acceptProb oracleDist
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:205	unfold	prfAdv	foreign-def	TCSlib.Cryptography.prfAdv	TCSlib.Cryptography.Pseudorandom.Functions.Defs	[theorem prfAdv_congr_equiv]	unfold prfAdv distAdv
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:205	unfold	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem prfAdv_congr_equiv]	unfold prfAdv distAdv
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:229	simp	pairEncode	foreign-def	Turing.pairEncode	TCSlib.Complexity.TuringMachine.Encoding	[theorem encodeHist_eq_flatMap]	simp [histBlock, pairEncode]
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:539	simp	decodeOracleMove	foreign-def	TCSlib.Cryptography.decodeOracleMove	TCSlib.Cryptography.Asymptotic.PRF	[theorem decodeOracleMove_query]	simp [decodeOracleMove, pairDecode_pairEncode, decodeFin_ofFn]
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:655	simp	NUPPT.coinLen	foreign-def	Complexity.NUPPT.coinLen	TCSlib.Complexity.Randomized.PPT	[theorem exists_queryChain_nuppt]	simp only [NUPPT.coinLen, hBc, hC₂c, hCc, hD₁c, NUPPT.coins_ofPolyTimeUniform,
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:670	simp	NUPPT.coinLen	foreign-def	Complexity.NUPPT.coinLen	TCSlib.Complexity.Randomized.PPT	[theorem exists_queryChain_nuppt]	have hD₁len : D₁.coinLen n = D.coinLen n := by simp only [NUPPT.coinLen, hD₁c]
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:729	rw	buildTree	foreign-def	TCSlib.Cryptography.buildTree	TCSlib.Cryptography.Asymptotic.PRF	[theorem exists_queryChain_nuppt]	rw [Nat.sub_zero, buildTree, hret]
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean:734	rw	buildTree	foreign-def	TCSlib.Cryptography.buildTree	TCSlib.Cryptography.Asymptotic.PRF	[theorem exists_queryChain_nuppt]	rw [buildTree, hquery _ hk, QueryTree.eval_query, ← hρ' _ hk, ← hist_succ,
TCSlib/Cryptography/Asymptotic/PRF.lean:325	simp	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem OracleEnsemble.Indist.refl]	simp [distAdv]
TCSlib/Cryptography/Asymptotic/PRF.lean:583	simpa	prgAdv	foreign-def	TCSlib.Cryptography.prgAdv	TCSlib.Cryptography.Pseudorandom.Generators	[theorem thm_97_3_2]	simpa only [prgAdv, distAdv_ggmBitsDist] using h
TCSlib/Cryptography/Asymptotic/PRF.lean:603	simp	GGMRed.queryOf	foreign-def	TCSlib.Cryptography.GGMRed.queryOf	TCSlib.Cryptography.Asymptotic.GGMReduction	[theorem decodeOracleMove_eq]	simp only [GGMRed.queryOf, hx]
TCSlib/Cryptography/Asymptotic/PRF.lean:611	simp	GGMRed.verdictOf	foreign-def	TCSlib.Cryptography.GGMRed.verdictOf	TCSlib.Cryptography.Asymptotic.GGMReduction	[theorem decodeOracleMove_eq]	simp [GGMRed.verdictOf, pairEncode]
TCSlib/Cryptography/Asymptotic/PRF.lean:611	simp	pairEncode	foreign-def	Turing.pairEncode	TCSlib.Complexity.TuringMachine.Encoding	[theorem decodeOracleMove_eq]	simp [GGMRed.verdictOf, pairEncode]
TCSlib/Cryptography/Asymptotic/PRF.lean:623	simp	GGMRed.verdictOf	foreign-def	TCSlib.Cryptography.GGMRed.verdictOf	TCSlib.Cryptography.Asymptotic.GGMReduction	[theorem decodeOracleMove_eq]	simp only [OracleMove.ret.injEq, GGMRed.verdictOf]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:103	simp	prefixAt	foreign-def	TCSlib.Cryptography.prefixAt	TCSlib.Cryptography.Pseudorandom.Functions.GGM	[theorem ofFn_prefixAt]	simp only [prefixAt, hk, dite_true]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:133	simp	pairSel	foreign-def	TCSlib.Cryptography.pairSel	TCSlib.Cryptography.Pseudorandom.Functions.GGM	[theorem selHalf_ofFn]	· simp only [selHalf, pairSel, Bool.false_eq_true, if_false, hu, take_ofFn_splitHalves]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:134	simp	pairSel	foreign-def	TCSlib.Cryptography.pairSel	TCSlib.Cryptography.Pseudorandom.Functions.GGM	[theorem selHalf_ofFn]	· simp only [selHalf, pairSel, if_true, hu, drop_ofFn_splitHalves]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	runAtL	foreign-def	Complexity.NUPPT.runAtL	TCSlib.Complexity.Randomized.PPT	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	advInput	foreign-def	Complexity.NUPPT.advInput	TCSlib.Complexity.Randomized.PPT	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	layout	foreign-def	Complexity.NUPPT.layout	TCSlib.Complexity.Randomized.Closure	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	inParam	foreign-def	Complexity.NUPPT.inParam	TCSlib.Complexity.Randomized.Closure	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	inArg	foreign-def	Complexity.NUPPT.inArg	TCSlib.Complexity.Randomized.Closure	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	inAdvice	foreign-def	Complexity.NUPPT.inAdvice	TCSlib.Complexity.Randomized.Closure	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:187	simp	inCoins	foreign-def	Complexity.NUPPT.inCoins	TCSlib.Complexity.Randomized.Closure	[theorem runAtL_preComp]	simp [preFun, runAtL, advInput, layout, inParam, inArg, inAdvice, inCoins]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:261	unfold	NUPPT.distinguisher	foreign-def	Complexity.NUPPT.distinguisher	TCSlib.Cryptography.Asymptotic.Adversary	[theorem PRG.Secure.truncateTo_negligible]	unfold NUPPT.distinguisher
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:268	rw	prgAdv	foreign-def	TCSlib.Cryptography.prgAdv	TCSlib.Cryptography.Pseudorandom.Generators	[theorem PRG.Secure.truncateTo_negligible]	rw [hfun, prgAdv, prgAdv,
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:268	rw	prgAdv	foreign-def	TCSlib.Cryptography.prgAdv	TCSlib.Cryptography.Pseudorandom.Generators	[theorem PRG.Secure.truncateTo_negligible]	rw [hfun, prgAdv, prgAdv,
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:270	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem PRG.Secure.truncateTo_negligible]	t (Fin.castLE (hm n) i)) (P.G n) id (D.distinguisher n (m.eval n)), distAdv, distAdv]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:270	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem PRG.Secure.truncateTo_negligible]	t (Fin.castLE (hm n) i)) (P.G n) id (D.distinguisher n (m.eval n)), distAdv, distAdv]
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean:312	simp	pairSndD	foreign-def	Complexity.pairSndD	TCSlib.Complexity.ClassNP.PolyTimePairing	[theorem length_ggmStep_le]	| none => exact absurd (by simp [pairSndD, hd]) h
TCSlib/Cryptography/Foundations/Experiments.lean:160	rw	statDist	foreign-def	TCSlib.InformationTheory.statDist	TCSlib.InformationTheory.StatisticalDistance	[theorem abs_sum_sub_le_statDist]	rw [statDist]
TCSlib/Cryptography/Foundations/Experiments.lean:175	rw	uexp	foreign-def	TCSlib.Cryptography.uexp	TCSlib.Cryptography.Foundations.Probability	[theorem distAdv_le_statDist]	rw [distAdv, acceptProb_eq_uexp_sum_map X, acceptProb_eq_uexp_sum_map Y, uexp, uexp,
TCSlib/Cryptography/Foundations/Experiments.lean:175	rw	uexp	foreign-def	TCSlib.Cryptography.uexp	TCSlib.Cryptography.Foundations.Probability	[theorem distAdv_le_statDist]	rw [distAdv, acceptProb_eq_uexp_sum_map X, acceptProb_eq_uexp_sum_map Y, uexp, uexp,
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:148	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem hybridProb_eq_level_prg]	rw [hybridProb, acceptProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:148	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem hybridProb_eq_level_prg]	rw [hybridProb, acceptProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:150	simp	oracleDist	foreign-def	TCSlib.Cryptography.oracleDist	TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary	[theorem hybridProb_eq_level_prg]	simp only [oracleDist, levelAdv, eval_simulate, comp_apply]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:180	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem hybridProb_eq_level_random]	rw [hybridProb, ← acceptProb_comp_equiv e, acceptProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:180	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem hybridProb_eq_level_random]	rw [hybridProb, ← acceptProb_comp_equiv e, acceptProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:182	simp	oracleDist	foreign-def	TCSlib.Cryptography.oracleDist	TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary	[theorem hybridProb_eq_level_random]	simp only [oracleDist, levelAdv, eval_simulate, comp_apply, randomFunction, id, e,
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:182	simp	randomFunction	foreign-def	TCSlib.Cryptography.randomFunction	TCSlib.Cryptography.Pseudorandom.Functions.Defs	[theorem hybridProb_eq_level_random]	simp only [oracleDist, levelAdv, eval_simulate, comp_apply, randomFunction, id, e,
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:236	rw	prfAdv	foreign-def	TCSlib.Cryptography.prfAdv	TCSlib.Cryptography.Pseudorandom.Functions.Defs	[theorem ggm_prfAdv_le]	rw [prfAdv, distAdv, ← hybridProb_zero, ← hybridProb_top]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:236	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem ggm_prfAdv_le]	rw [prfAdv, distAdv, ← hybridProb_zero, ← hybridProb_top]
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:312	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [acceptProb, acceptProb]; rfl
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:312	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [acceptProb, acceptProb]; rfl
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:315	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [acceptProb, acceptProb]; rfl
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:315	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [acceptProb, acceptProb]; rfl
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:316	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [distAdv, distAdv, h, h']
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean:316	rw	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem distAdv_ggmBitsDist]	rw [distAdv, distAdv, h, h']
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:145	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem acceptProb_tableDist_prg]	rw [acceptProb, ← uprob_comp_equiv e
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:150	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem acceptProb_tableDist_prg]	rw [subHybridProb, acceptProb, ← uprob_comp_equiv (Equiv.prodAssoc _ _ _).symm
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:192	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem acceptProb_tableDist_uniform]	rw [acceptProb, ← uprob_comp_equiv e
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:198	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem acceptProb_tableDist_uniform]	rw [subHybridProb, acceptProb, ← uprob_comp_equiv e'
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:217	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem subHybridProb_zero]	rw [subHybridProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:225	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem subHybridProb_zero]	rw [acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:251	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem subHybridProb_top]	rw [subHybridProb, acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:259	rw	acceptProb	foreign-def	TCSlib.Cryptography.acceptProb	TCSlib.Cryptography.Foundations.Experiments	[theorem subHybridProb_top]	rw [acceptProb]
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean:288	unfold	distAdv	foreign-def	TCSlib.Cryptography.distAdv	TCSlib.Cryptography.Foundations.Experiments	[theorem table_hybrid]	unfold distAdv
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:467	rw	uexp	foreign-def	TCSlib.Cryptography.uexp	TCSlib.Cryptography.Foundations.Probability	[theorem exists_proverCoins_le]	rw [sum_const, card_univ, nsmul_eq_mul, uexp, mul_div_cancel₀ _ hcard.ne']
## (c2) show/change steps on a line where the seal failed: 0 (of 17 show/change occurrences, all checked by the seal)
## (c3) proof terms referring to a generated equation lemma of a foreign TCSlib definition (collector): 21
# module	owner declaration	constant	equation lemma
TCSlib.Cryptography.Asymptotic.MultiMessage	TCSlib.Cryptography.prfAdv_multiMsgAdv	TCSlib.Cryptography.prfAdv_multiMsgAdv	TCSlib.Cryptography.distAdv.eq_1
TCSlib.Cryptography.Asymptotic.MultiMessage	TCSlib.Cryptography.prfAdv_multiMsgAdv	TCSlib.Cryptography.prfAdv_multiMsgAdv	TCSlib.Cryptography.prfAdv.eq_1
TCSlib.Cryptography.Asymptotic.MultiMessage	TCSlib.Cryptography.prfScheme_multiMessageSecure	TCSlib.Cryptography.prfScheme_multiMessageSecure	Complexity.NUPPT.distinguisherL.eq_1
TCSlib.Cryptography.Asymptotic.MultiMessage	TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le	TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le	TCSlib.Cryptography.distAdv.eq_1
TCSlib.Cryptography.Asymptotic.MultiMessageLemmas	TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt	TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt	TCSlib.Cryptography.buildTree.eq_1
TCSlib.Cryptography.Asymptotic.MultiMessageLemmas	TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt	TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt	TCSlib.Cryptography.buildTree.eq_2
TCSlib.Cryptography.Asymptotic.PRFLemmas	TCSlib.Cryptography.PRG.Secure.truncateTo_negligible	TCSlib.Cryptography.PRG.Secure.truncateTo_negligible	TCSlib.Cryptography.distAdv.eq_1
TCSlib.Cryptography.Asymptotic.PRFLemmas	TCSlib.Cryptography.PRG.Secure.truncateTo_negligible	TCSlib.Cryptography.PRG.Secure.truncateTo_negligible	TCSlib.Cryptography.prgAdv.eq_1
TCSlib.Cryptography.Foundations.Experiments	TCSlib.Cryptography.distAdv_le_statDist	TCSlib.Cryptography.distAdv_le_statDist	TCSlib.Cryptography.uexp.eq_1
TCSlib.Cryptography.Foundations.Experiments	TCSlib.Cryptography.abs_sum_sub_le_statDist	TCSlib.Cryptography.abs_sum_sub_le_statDist	TCSlib.InformationTheory.statDist.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.hybridProb_eq_level_prg	TCSlib.Cryptography.hybridProb_eq_level_prg	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.hybridProb_eq_level_random	TCSlib.Cryptography.hybridProb_eq_level_random	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.ggm_prfAdv_le	TCSlib.Cryptography.ggm_prfAdv_le	TCSlib.Cryptography.distAdv.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.ggm_prfAdv_le	TCSlib.Cryptography.ggm_prfAdv_le	TCSlib.Cryptography.prfAdv.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.distAdv_ggmBitsDist	TCSlib.Cryptography.distAdv_ggmBitsDist	TCSlib.Cryptography.distAdv.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.GGM	TCSlib.Cryptography.distAdv_ggmBitsDist	TCSlib.Cryptography.distAdv_ggmBitsDist	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids	TCSlib.Cryptography.subHybridProb_top	TCSlib.Cryptography.subHybridProb_top	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids	TCSlib.Cryptography.subHybridProb_zero	TCSlib.Cryptography.subHybridProb_zero	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids	TCSlib.Cryptography.acceptProb_tableDist_uniform	TCSlib.Cryptography.acceptProb_tableDist_uniform	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids	TCSlib.Cryptography.acceptProb_tableDist_prg	TCSlib.Cryptography.acceptProb_tableDist_prg	TCSlib.Cryptography.acceptProb.eq_1
TCSlib.Cryptography.ZeroKnowledge.Interaction	TCSlib.Cryptography.Protocol.exists_proverCoins_le	TCSlib.Cryptography.Protocol.exists_proverCoins_le	TCSlib.Cryptography.uexp.eq_1

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/exclusions.md =====

# Rule-10 exclusions and type-level reads (gate 04 round 4)

At `a588adfed01eefe6971abd0846e3938ad02e8624` (branch `wip/g04r4`), for the 26 Lean files of #195's change set.

Generated by `tools/exclusions_md.py` from the derived unseal entries (`unseal.json`), the
declaration change map against the merge base (`declchanges.tsv`) and the source scan (`scan.log`).
Every entry below is 1-minimal: re-sealing any listed name for that declaration makes the file
fail (`exclude/exclude-*.log`). Names are relative to `TCSlib.Cryptography` where that prefix
was dropped.

## A. Inherited, unchanged ch. 2–4 proofs (named exclusions, not fixed)

Each declaration's statement and proof text are unchanged since the merge base (status SAME),
and its file lies outside the S2a/S2b layer. In the seal, every candidate stays sealed for the
whole file; only the declaration listed is wrapped in `section … attribute [local semireducible]
<the names listed> … end`, so it alone may read exactly those definitions.

### `TCSlib/Cryptography/Asymptotic/MultiMessage.lean`

| declaration | status | foreign definition read | how |
|---|---|---|---|
| `distAdv_prfEncReal_random_otp_le` | SAME | `acceptProb` | definitional unfolding — seal error line 286: Type mismatch |
| `distAdv_prfEncReal_random_otp_le` | SAME | `randomFunction` | definitional unfolding — seal error line 288: Tactic `rfl` failed: The left-hand side |
| `encodeList_eq_flatMap` | SAME | `PrivateKeyScheme.encodeList` | definitional unfolding — seal error line 532: Type mismatch |
| `multiMsgAdv_boundedBy` | SAME | `OracleAdversary.BoundedBy` | definitional unfolding — seal error line 155: Type mismatch |
| `prfScheme` | SAME | `Complexity.NUPPT.coinLen` | definitional unfolding — seal error line 520: Application type mismatch: The argument |
| `prfScheme` | SAME | `Complexity.NUPPT.ofPolyTimeUniform` | definitional unfolding — seal error line 520: Application type mismatch: The argument |
| `prfScheme` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 520: Application type mismatch: The argument |
| `prfScheme_multiEncDist` | SAME | `Complexity.NUPPT.coinLen` | definitional unfolding — seal error line 552: Application type mismatch: The argument |
| `prfScheme_multiEncDist` | SAME | `Complexity.NUPPT.ofPolyTimeUniform` | definitional unfolding — seal error line 552: Application type mismatch: The argument |
| `prfScheme_multiEncDist` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 552: Application type mismatch: The argument |
| `prfScheme_multiMessageSecure` | SAME | `Complexity.NUPPT.coinLen` | definitional unfolding — seal error line 635: Type mismatch |
| `prfScheme_multiMessageSecure` | SAME | `Complexity.NUPPT.ofPolyTimeUniform` | definitional unfolding — seal error line 635: Type mismatch |
| `prfScheme_multiMessageSecure` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 628: Type mismatch |
| `prfScheme_multiMessageSecure` | SAME | `PrivateKeyScheme.MultiMessageSecure` | definitional unfolding — seal error line 605: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce |
| `prfScheme_multiMessageSecure` | SAME | `acceptProb` | definitional unfolding — seal error line 654: Type mismatch |
| `prfScheme_multiMessageSecure` | SAME | `distAdv` | definitional unfolding — seal error line 654: Type mismatch |
| `pushesUniform_comp_injective` | SAME | `HardcoreBit.PushesUniform` | definitional unfolding — seal error line 241: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce |

### `TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean`

| declaration | status | foreign definition read | how |
|---|---|---|---|
| `MultiMsg.dbl_append` | SAME | `Turing.dbl` | definitional unfolding — seal error line 320: Type mismatch |
| `MultiMsg.decodeOracleMove_ret` | SAME | `decodeOracleMove` | definitional unfolding — seal error line 544: Tactic `rfl` failed: The left-hand side |
| `MultiMsg.decodeOracleMove_ret` | SAME | `Turing.pairDecode` | definitional unfolding — seal error line 544: Tactic `rfl` failed: The left-hand side |
| `MultiMsg.encodeHist_eq_flatMap` | SAME | `encodeHist` | definitional unfolding — seal error line 228: 'show' tactic failed, pattern |
| `MultiMsg.eval_histBlockLen` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 236: Type mismatch |
| `MultiMsg.exists_queryChain_nuppt` | SAME | `Complexity.NUPPT.advInput` | definitional unfolding — seal error line 688: Tactic `rfl` failed: The left-hand side |
| `MultiMsg.exists_queryChain_nuppt` | SAME | `Complexity.NUPPT.layout` | definitional unfolding — seal error line 688: Tactic `rfl` failed: The left-hand side |
| `MultiMsg.exists_queryChain_nuppt` | SAME | `Complexity.NUPPT.runAt` | definitional unfolding — seal error line 688: Tactic `rfl` failed: The left-hand side |
| `MultiMsg.exists_queryChain_nuppt` | SAME | `Complexity.NUPPT.runAtL` | definitional unfolding — seal error line 688: Tactic `rfl` failed: The left-hand side |
| `MultiMsg.exists_queryChain_nuppt` | SAME | `Complexity.NUPPT.toOracleAdversary` | definitional unfolding — seal error line 741: Type mismatch |
| `MultiMsg.exists_queryChain_nuppt` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 680: Type mismatch |
| `MultiMsg.exists_queryChain_nuppt` | SAME | `QueryTree.eval` | definitional unfolding — seal error line 731: Tactic `rfl` failed: The left-hand side |
| `MultiMsg.take_drop_ofFn_blocks` | SAME | `FunFamily.blocks` | definitional unfolding — seal error line 391: 'show' tactic failed, pattern |
| `MultiMsg.zipWith_xor_dbl` | SAME | `Turing.dbl` | definitional unfolding — seal error line 334: Type mismatch |
| `MultiMsg.zipWith_xor_histBlock_maskBlock` | SAME | `Turing.dbl` | definitional unfolding — seal error line 354: Tactic `rfl` failed: The left-hand side |

### `TCSlib/Cryptography/Asymptotic/PRF.lean`

| declaration | status | foreign definition read | how |
|---|---|---|---|
| `DoublingPRG.negligible_prgAdv` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 443: Type mismatch |
| `OracleEnsemble.Indist.symm` | SAME | `distAdv` | definitional unfolding — seal error line 339: typeclass instance problem is stuck, it is often due to metavariables |
| `OracleEnsemble.Indist.trans` | SAME | `distAdv` | definitional unfolding — seal error line 360: Application type mismatch: The argument |
| `OracleEnsemble.random_O` | SAME | `randomFunction` | definitional unfolding — seal error line 144: Type mismatch |
| `PRF` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 393: Application type mismatch: The argument |
| `PRF.negligible_prfAdv` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 411: Type mismatch: After simplification, term |
| `PRF.negligible_prfAdv` | SAME | `prfAdv` | definitional unfolding — seal error line 411: Type mismatch: After simplification, term |
| `PRG.Secure.doubling` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 511: Type mismatch |
| `PRG.Secure.doubling` | SAME | `Ensemble.Pseudorandom` | definitional unfolding — seal error line 512: Application type mismatch: The argument |
| `PRG.Secure.doubling` | SAME | `PRG.expand` | definitional unfolding — seal error line 513: Application type mismatch: The argument |
| `PRG.Secure.doubling` | SAME | `prgAdv` | definitional unfolding — seal error line 515: Type mismatch |
| `PRG.Secure.truncate` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 487: Type mismatch |
| `PRG.Secure.truncate` | SAME | `Ensemble.Pseudorandom` | definitional unfolding — seal error line 488: Application type mismatch: The argument |
| `PRG.Secure.truncate` | SAME | `PRG.Easy` | definitional unfolding — seal error line 490: Invalid `⟨...⟩` notation: The expected type `(oneBit P.truncate).Easy` is not an inductive type |
| `PRG.Secure.truncate` | SAME | `PRG.Secure` | definitional unfolding — seal error line 488: Invalid `⟨...⟩` notation: The expected type `(oneBit P.truncate).Secure` is not an inductive type |
| `PRG.Secure.truncate` | SAME | `PRG.ensemble` | definitional unfolding — seal error line 491: Type mismatch |
| `PRG.Secure.truncate` | SAME | `PRG.oneBit` | definitional unfolding — seal error line 490: Type mismatch |
| `PRG.Secure.truncate` | SAME | `prgAdv` | definitional unfolding — seal error line 491: Type mismatch |
| `PRG.doubling` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 463: Application type mismatch: The argument |
| `PRG.doubling` | SAME | `PRG.expand` | definitional unfolding — seal error line 463: Application type mismatch: The argument |
| `PRG.doubling_apply` | SAME | `PRG.expand` | definitional unfolding — seal error line 470: Type mismatch |
| `decodeOracleMove_eq` | SAME | `GGMRed.queryOf` | explicit `simp [GGMRed.queryOf]` at line 603; also definitional (line 613: Tactic `rfl` failed: The left-hand side) |
| `decodeOracleMove_eq` | SAME | `GGMRed.verdictOf` | explicit `simp [GGMRed.verdictOf]` at line 611; explicit `simp [GGMRed.verdictOf]` at line 623; also definitional (line 615: Tactic `rfl` failed: The left-hand side) |
| `decodeOracleMove_eq` | SAME | `Turing.pairDecode` | definitional unfolding — seal error line 613: Tactic `rfl` failed: The left-hand side |
| `doublingEnsemble` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 420: Type mismatch |
| `exists_ggmBitsDist_nuppt` | SAME | `Complexity.NUPPT.coinLen` | definitional unfolding — seal error line 698: Application type mismatch: The argument |
| `exists_ggmBitsDist_nuppt` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 698: Application type mismatch: The argument |
| `exists_ggmBitsDist_nuppt` | SAME | `GGMRed.coinStr` | definitional unfolding — seal error line 707: Tactic `rfl` failed: The left-hand side |
| `exists_ggmBitsDist_nuppt` | SAME | `GGMRed.ggmRedMachine` | definitional unfolding — seal error line 698: Application type mismatch: The argument |
| `exists_ggmBitsDist_nuppt` | SAME | `GGMRed.histEnc` | definitional unfolding — seal error line 688: Type mismatch |
| `ggmPRF_prf` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 753: 'show' tactic failed, pattern |
| `ggmPRF_prf` | SAME | `Negligible` | definitional unfolding — seal error line 767: Function expected at |
| `ggmPRF_prf` | SAME | `prfAdv` | definitional unfolding — seal error line 753: 'show' tactic failed, pattern |
| `ggmPRF_prf` | SAME | `prgAdv` | definitional unfolding — seal error line 759: Type mismatch |
| `prfAdv_toOracleAdversary` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 400: Application type mismatch: The argument |
| `prfAdv_toOracleAdversary` | SAME | `prfAdv` | definitional unfolding — seal error line 402: Type mismatch |
| `thm_97_3_1` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 565: typeclass instance problem is stuck, it is often due to metavariables |
| `thm_97_3_1` | SAME | `ggmBits` | definitional unfolding — seal error line 566: Application type mismatch: The argument |
| `two_mul_add_one_expands` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 454: 'show' tactic failed, pattern |

### `TCSlib/Cryptography/Asymptotic/PRFLemmas.lean`

| declaration | status | foreign definition read | how |
|---|---|---|---|
| `Complexity.NUPPT.coins_preComp` | SAME | `Complexity.NUPPT.ofPolyTime` | definitional unfolding — seal error line 179: Type mismatch |
| `Complexity.NUPPT.runAt_preComp` | SAME | `Complexity.NUPPT.coinLen` | definitional unfolding — seal error line 192: Application type mismatch: The argument |
| `Complexity.NUPPT.runAt_preComp` | SAME | `Complexity.NUPPT.ofPolyTime` | definitional unfolding — seal error line 192: Application type mismatch: The argument |
| `Complexity.NUPPT.runAt_preComp` | SAME | `Complexity.NUPPT.runAt` | definitional unfolding — seal error line 193: Type mismatch |
| `Complexity.NUPPT.runAt_preComp` | SAME | `Complexity.NUPPT.runAtL` | definitional unfolding — seal error line 193: Type mismatch |
| `PRG.Secure.truncateTo_easy` | SAME | `PRG.Easy` | definitional unfolding — seal error line 230: Tactic `rcases` failed: `x✝ : P.Easy` is not an inductive datatype |
| `PRG.Secure.truncateTo_easy` | SAME | `PRG.Secure` | definitional unfolding — seal error line 230: Invalid projection: Expected a value whose type is a structure |
| `PRG.Secure.truncateTo_negligible` | SAME | `Complexity.NUPPT.coinLen` | definitional unfolding — seal error line 259: Function expected at |
| `PRG.Secure.truncateTo_negligible` | SAME | `Complexity.NUPPT.ofPolyTime` | definitional unfolding — seal error line 259: Function expected at |
| `PRG.Secure.truncateTo_negligible` | SAME | `Ensemble.Pseudorandom` | definitional unfolding — seal error line 255: Function expected at |
| `PRG.Secure.truncateTo_negligible` | SAME | `Ensemble.uniform` | definitional unfolding — seal error line 265: 'show' tactic failed, pattern |
| `PRG.Secure.truncateTo_negligible` | SAME | `PRG.Secure` | definitional unfolding — seal error line 255: Invalid projection: Expected a value whose type is a structure |
| `PRG.Secure.truncateTo_negligible` | SAME | `PRG.ensemble` | definitional unfolding — seal error line 265: 'show' tactic failed, pattern |
| `PRG.Secure.truncateTo_negligible` | SAME | `prgAdv` | explicit `rw [prgAdv]` at line 268; explicit `rw [prgAdv]` at line 268; also definitional (line 265: 'show' tactic failed, pattern) |
| `drop_ofFn_splitHalves` | SAME | `splitHalves` | definitional unfolding — seal error line 119: Tactic `rfl` failed: The left-hand side |
| `drop_take_ofFn_blocks` | SAME | `FunFamily.blocks` | definitional unfolding — seal error line 89: 'show' tactic failed, pattern |
| `ggmEval_ofFn` | SAME | `ggmBits` | definitional unfolding — seal error line 410: 'show' tactic failed, pattern |
| `ggmEval_poly` | SAME | `Complexity.PolyExpr.eval` | definitional unfolding — seal error line 385: Type mismatch |
| `take_ofFn_splitHalves` | SAME | `splitHalves` | definitional unfolding — seal error line 111: Tactic `rfl` failed: The left-hand side |

### `TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean`

| declaration | status | foreign definition read | how |
|---|---|---|---|
| `prfAdv_eq` | SAME | `acceptProb` | definitional unfolding — seal error line 77: Type mismatch |
| `prfAdv_eq` | SAME | `distAdv` | definitional unfolding — seal error line 77: Type mismatch |
| `prfAdv_eq` | SAME | `oracleDist` | definitional unfolding — seal error line 77: Type mismatch |
| `prfAdv_nonneg` | SAME | `distAdv` | definitional unfolding — seal error line 82: Type mismatch |

### `TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean`

| declaration | status | foreign definition read | how |
|---|---|---|---|
| `hybridProb_level` | SAME | `OracleAdversary.BoundedBy` | definitional unfolding — seal error line 217: Application type mismatch: The argument |
| `hybridProb_top` | SAME | `randomFunction` | definitional unfolding — seal error line 132: Tactic `rfl` failed: The left-hand side |

### `TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean`

| declaration | status | foreign definition read | how |
|---|---|---|---|
| `subHybridProb_top` | SAME | `OracleAdversary.BoundedBy` | definitional unfolding — seal error line 256: Function expected at |
| `subHybridProb_top` | SAME | `oracleDist` | definitional unfolding — seal error line 260: Type mismatch |
| `subHybridProb_top` | SAME | `randomFunction` | definitional unfolding — seal error line 260: Type mismatch |
| `subHybridProb_zero` | SAME | `OracleAdversary.BoundedBy` | definitional unfolding — seal error line 236: Function expected at |
| `subHybridProb_zero` | SAME | `oracleDist` | definitional unfolding — seal error line 228: Tactic `rfl` failed: The left-hand side |

### `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean`

| declaration | status | foreign definition read | how |
|---|---|---|---|
| `Strategy.pairFstD_encodeMsgs` | SAME | `Complexity.pairFstD` | definitional unfolding — seal error line 128: Tactic `rfl` failed: The left-hand side |

## B. Explicit unfolds the seal cannot see (named exclusions, not fixed)

`unfold`, `rw`, `simp` and `dsimp` use a definition's equation lemmas and work through
`[irreducible]`, so these reads pass the seal. Each is in an inherited, unchanged ch. 2–4
proof (status SAME); none is in the S2a/S2b layer or in a declaration #195 changed.

| file | declaration | status | foreign definition | how |
|---|---|---|---|---|
| `Asymptotic/MultiMessage.lean` | `acceptProb_oracleDist_multiMsgAdv` | SAME | `acceptProb` | explicit `unfold [acceptProb]` at line 164 |
| `Asymptotic/MultiMessage.lean` | `acceptProb_oracleDist_multiMsgAdv` | SAME | `oracleDist` | explicit `simp [oracleDist]` at line 168 |
| `Asymptotic/MultiMessage.lean` | `decodeFin_runAt_prfDec_of_not_wf` | SAME | `Complexity.NUPPT.inArg` | explicit `simp [NUPPT.inArg]` at line 482 |
| `Asymptotic/MultiMessage.lean` | `decodeFin_runAt_prfDec_of_not_wf` | SAME | `Complexity.NUPPT.inParam` | explicit `simp [NUPPT.inParam]` at line 482 |
| `Asymptotic/MultiMessage.lean` | `decodeFin_runAt_prfDec_of_not_wf` | SAME | `Complexity.NUPPT.advInput` | explicit `simp [NUPPT.advInput]` at line 482 |
| `Asymptotic/MultiMessage.lean` | `decodeFin_runAt_prfDec_of_not_wf` | SAME | `decodeFin` | explicit `simp [decodeFin]` at line 486 |
| `Asymptotic/MultiMessage.lean` | `decodeFin_runAt_prfDec_of_not_wf` | SAME | `Complexity.NUPPT.inParam` | explicit `simp [NUPPT.inParam]` at line 486 |
| `Asymptotic/MultiMessage.lean` | `decodeFin_runAt_prfDec_of_not_wf` | SAME | `Complexity.NUPPT.advInput` | explicit `simp [NUPPT.advInput]` at line 486 |
| `Asymptotic/MultiMessage.lean` | `distAdv_prfEncReal_le` | SAME | `distAdv` | explicit `simp [distAdv]` at line 358 |
| `Asymptotic/MultiMessage.lean` | `distAdv_prfEncReal_random_otp_le` | SAME | `distAdv` | explicit `rw [distAdv]` at line 298 |
| `Asymptotic/MultiMessage.lean` | `encodeList_eq_flatMap` | SAME | `Turing.pairEncode` | explicit `simp [pairEncode]` at line 535 |
| `Asymptotic/MultiMessage.lean` | `prfAdv_multiMsgAdv` | SAME | `prfAdv` | explicit `rw [prfAdv]` at line 180 |
| `Asymptotic/MultiMessage.lean` | `prfAdv_multiMsgAdv` | SAME | `distAdv` | explicit `rw [distAdv]` at line 180 |
| `Asymptotic/MultiMessage.lean` | `prfAdv_multiMsgAdv` | SAME | `distAdv` | explicit `rw [distAdv]` at line 180 |
| `Asymptotic/MultiMessage.lean` | `prfScheme_multiEncDist` | SAME | `PrivateKeyScheme.multiEncDist` | explicit `unfold [PrivateKeyScheme.multiEncDist]` at line 553 |
| `Asymptotic/MultiMessage.lean` | `prfScheme_multiMessageSecure` | SAME | `Complexity.NUPPT.distinguisherL` | explicit `rw [NUPPT.distinguisherL]` at line 649 |
| `Asymptotic/MultiMessage.lean` | `pushesUniform_comp_injective` | SAME | `uexp` | explicit `simp [uexp]` at line 244 |
| `Asymptotic/MultiMessage.lean` | `runAt_prfDec` | SAME | `Complexity.NUPPT.inArg` | explicit `simp [NUPPT.inArg]` at line 469 |
| `Asymptotic/MultiMessage.lean` | `runAt_prfDec` | SAME | `Complexity.NUPPT.inParam` | explicit `simp [NUPPT.inParam]` at line 469 |
| `Asymptotic/MultiMessage.lean` | `runAt_prfDec` | SAME | `Complexity.NUPPT.advInput` | explicit `simp [NUPPT.advInput]` at line 469 |
| `Asymptotic/MultiMessage.lean` | `runAt_prfEnc` | SAME | `Complexity.NUPPT.inArg` | explicit `simp [NUPPT.inArg]` at line 458 |
| `Asymptotic/MultiMessage.lean` | `runAt_prfEnc` | SAME | `Complexity.NUPPT.inCoins` | explicit `simp [NUPPT.inCoins]` at line 458 |
| `Asymptotic/MultiMessage.lean` | `runAt_prfEnc` | SAME | `Complexity.NUPPT.advInput` | explicit `simp [NUPPT.advInput]` at line 458 |
| `Asymptotic/MultiMessageLemmas.lean` | `MultiMsg.abs_uexp_le_uexp_abs` | SAME | `uexp` | explicit `unfold [uexp]` at line 79 |
| `Asymptotic/MultiMessageLemmas.lean` | `MultiMsg.decodeOracleMove_query` | SAME | `decodeOracleMove` | explicit `simp [decodeOracleMove]` at line 540 |
| `Asymptotic/MultiMessageLemmas.lean` | `MultiMsg.encodeHist_eq_flatMap` | SAME | `Turing.pairEncode` | explicit `simp [pairEncode]` at line 230 |
| `Asymptotic/MultiMessageLemmas.lean` | `MultiMsg.exists_queryChain_nuppt` | SAME | `Complexity.NUPPT.coinLen` | explicit `simp [NUPPT.coinLen]` at line 656 |
| `Asymptotic/MultiMessageLemmas.lean` | `MultiMsg.exists_queryChain_nuppt` | SAME | `Complexity.NUPPT.coinLen` | explicit `simp [NUPPT.coinLen]` at line 671 |
| `Asymptotic/MultiMessageLemmas.lean` | `MultiMsg.exists_queryChain_nuppt` | SAME | `buildTree` | explicit `rw [buildTree]` at line 730 |
| `Asymptotic/MultiMessageLemmas.lean` | `MultiMsg.exists_queryChain_nuppt` | SAME | `buildTree` | explicit `rw [buildTree]` at line 735 |
| `Asymptotic/PRF.lean` | `OracleEnsemble.Indist.refl` | SAME | `distAdv` | explicit `simp [distAdv]` at line 325 |
| `Asymptotic/PRF.lean` | `decodeOracleMove_eq` | SAME | `Turing.pairEncode` | explicit `simp [pairEncode]` at line 611 |
| `Asymptotic/PRF.lean` | `thm_97_3_2` | SAME | `prgAdv` | explicit `simpa [prgAdv]` at line 583 |
| `Asymptotic/PRFLemmas.lean` | `Complexity.NUPPT.runAtL_preComp` | SAME | `Complexity.NUPPT.runAtL` | explicit `simp [runAtL]` at line 187 |
| `Asymptotic/PRFLemmas.lean` | `Complexity.NUPPT.runAtL_preComp` | SAME | `Complexity.NUPPT.advInput` | explicit `simp [advInput]` at line 187 |
| `Asymptotic/PRFLemmas.lean` | `Complexity.NUPPT.runAtL_preComp` | SAME | `Complexity.NUPPT.layout` | explicit `simp [layout]` at line 187 |
| `Asymptotic/PRFLemmas.lean` | `Complexity.NUPPT.runAtL_preComp` | SAME | `Complexity.NUPPT.inParam` | explicit `simp [inParam]` at line 187 |
| `Asymptotic/PRFLemmas.lean` | `Complexity.NUPPT.runAtL_preComp` | SAME | `Complexity.NUPPT.inArg` | explicit `simp [inArg]` at line 187 |
| `Asymptotic/PRFLemmas.lean` | `Complexity.NUPPT.runAtL_preComp` | SAME | `Complexity.NUPPT.inAdvice` | explicit `simp [inAdvice]` at line 187 |
| `Asymptotic/PRFLemmas.lean` | `Complexity.NUPPT.runAtL_preComp` | SAME | `Complexity.NUPPT.inCoins` | explicit `simp [inCoins]` at line 187 |
| `Asymptotic/PRFLemmas.lean` | `PRG.Secure.truncateTo_negligible` | SAME | `Complexity.NUPPT.distinguisher` | explicit `unfold [NUPPT.distinguisher]` at line 261 |
| `Asymptotic/PRFLemmas.lean` | `PRG.Secure.truncateTo_negligible` | SAME | `distAdv` | explicit `rw [distAdv]` at line 270 |
| `Asymptotic/PRFLemmas.lean` | `PRG.Secure.truncateTo_negligible` | SAME | `distAdv` | explicit `rw [distAdv]` at line 270 |
| `Asymptotic/PRFLemmas.lean` | `length_ggmStep_le` | SAME | `Complexity.pairSndD` | explicit `simp [pairSndD]` at line 312 |
| `Asymptotic/PRFLemmas.lean` | `ofFn_prefixAt` | SAME | `prefixAt` | explicit `simp [prefixAt]` at line 103 |
| `Asymptotic/PRFLemmas.lean` | `selHalf_ofFn` | SAME | `pairSel` | explicit `simp [pairSel]` at line 133 |
| `Asymptotic/PRFLemmas.lean` | `selHalf_ofFn` | SAME | `pairSel` | explicit `simp [pairSel]` at line 134 |
| `Foundations/Experiments.lean` | `abs_sum_sub_le_statDist` | SAME | `TCSlib.InformationTheory.statDist` | explicit `rw [statDist]` at line 160 |
| `Foundations/Experiments.lean` | `distAdv_le_statDist` | SAME | `uexp` | explicit `rw [uexp]` at line 175 |
| `Foundations/Experiments.lean` | `distAdv_le_statDist` | SAME | `uexp` | explicit `rw [uexp]` at line 175 |
| `Pseudorandom/Functions/GGM.lean` | `distAdv_ggmBitsDist` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 312 |
| `Pseudorandom/Functions/GGM.lean` | `distAdv_ggmBitsDist` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 312 |
| `Pseudorandom/Functions/GGM.lean` | `distAdv_ggmBitsDist` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 315 |
| `Pseudorandom/Functions/GGM.lean` | `distAdv_ggmBitsDist` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 315 |
| `Pseudorandom/Functions/GGM.lean` | `distAdv_ggmBitsDist` | SAME | `distAdv` | explicit `rw [distAdv]` at line 316 |
| `Pseudorandom/Functions/GGM.lean` | `distAdv_ggmBitsDist` | SAME | `distAdv` | explicit `rw [distAdv]` at line 316 |
| `Pseudorandom/Functions/GGM.lean` | `ggm_prfAdv_le` | SAME | `prfAdv` | explicit `rw [prfAdv]` at line 236 |
| `Pseudorandom/Functions/GGM.lean` | `ggm_prfAdv_le` | SAME | `distAdv` | explicit `rw [distAdv]` at line 236 |
| `Pseudorandom/Functions/GGM.lean` | `hybridProb_eq_level_prg` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 148 |
| `Pseudorandom/Functions/GGM.lean` | `hybridProb_eq_level_prg` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 148 |
| `Pseudorandom/Functions/GGM.lean` | `hybridProb_eq_level_prg` | SAME | `oracleDist` | explicit `simp [oracleDist]` at line 150 |
| `Pseudorandom/Functions/GGM.lean` | `hybridProb_eq_level_random` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 180 |
| `Pseudorandom/Functions/GGM.lean` | `hybridProb_eq_level_random` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 180 |
| `Pseudorandom/Functions/GGM.lean` | `hybridProb_eq_level_random` | SAME | `oracleDist` | explicit `simp [oracleDist]` at line 182 |
| `Pseudorandom/Functions/GGM.lean` | `hybridProb_eq_level_random` | SAME | `randomFunction` | explicit `simp [randomFunction]` at line 182 |
| `Pseudorandom/Functions/SubHybrids.lean` | `acceptProb_tableDist_prg` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 145 |
| `Pseudorandom/Functions/SubHybrids.lean` | `acceptProb_tableDist_prg` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 150 |
| `Pseudorandom/Functions/SubHybrids.lean` | `acceptProb_tableDist_uniform` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 192 |
| `Pseudorandom/Functions/SubHybrids.lean` | `acceptProb_tableDist_uniform` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 198 |
| `Pseudorandom/Functions/SubHybrids.lean` | `subHybridProb_top` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 251 |
| `Pseudorandom/Functions/SubHybrids.lean` | `subHybridProb_top` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 259 |
| `Pseudorandom/Functions/SubHybrids.lean` | `subHybridProb_zero` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 217 |
| `Pseudorandom/Functions/SubHybrids.lean` | `subHybridProb_zero` | SAME | `acceptProb` | explicit `rw [acceptProb]` at line 225 |
| `Pseudorandom/Functions/SubHybrids.lean` | `table_hybrid` | SAME | `distAdv` | explicit `unfold [distAdv]` at line 288 |
| `ZeroKnowledge/Interaction.lean` | `Protocol.exists_proverCoins_le` | SAME | `uexp` | explicit `rw [uexp]` at line 467 |

## C. Type-level reads in the S2a/S2b layer

None. By ruling R-04-4 (commit `a588adfe`), `Games.QueryImpl` (`Games/Simulate.lean`) and
`Games.OracleSpec.add` (`Games/OracleComp.lean`) are reducible abbreviations, which policy §1
treats as notation (read through `queryImpl_def`, `OracleSpec.add_dom_inl/_inr`,
`add_rng_inl/_inr`). They are no longer seal candidates, and every `Games/` file passes the
seal with no named entry.

## Check

Entries in sections A and B on a declaration that is not SAME (added or changed by #195): 0.


## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/replay.log =====

# replay at a588adfed01eefe6971abd0846e3938ad02e8624 (wip/g04r4; base 27ae72da62119ebdde380b8cb2d8c183b59fa2bf): the 30 modules of replay-order.txt (every module downstream of Games/OracleComp and Games/Simulate, from tools/downstream2.py, then audits/pass-shelat/Checks), in import order, with scripts/lean_check_tree.sh, into a whole-tree copy of the olean tree replayed at 947606fe (the 23 modules downstream of that commit's files, intermediate/r1/replay.log)
TCSlib/Cryptography/Games/OracleComp rc=0 1s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/Defs rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/GGM rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 50s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Probability rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Simulate rc=0 1s errors=0 sorry=0
TCSlib/Cryptography/Games/Advantage rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Hopping rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Protocols rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Games rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Machines rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/BitCodec rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Bridges/QueryTree rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Bridges/Machines rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Efficiency rc=0 4s errors=0 sorry=4
TCSlib/Cryptography/Games/Bridges/Experiments rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Bridges/Strategies rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Bridges rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom rc=0 3s errors=0 sorry=0
audits/pass-shelat/Checks rc=0 111s errors=0 sorry=0
# done 2026-11-06T00:55:07Z

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/replay-first-commit.log =====

# replay at 947606fecf1142997661651701f04c3912ba7551 (wip/g04r4; base 27ae72da62119ebdde380b8cb2d8c183b59fa2bf): the 23 modules of replay-order.txt (the modules downstream of the 5 files this commit changes, from tools/downstream2.py, then audits/pass-shelat/Checks), in import order, with scripts/lean_check_tree.sh, from a copy of the $BASE olean tree (s2bfix-r3-oleans) in which only Games/Probability and Games/Protocols had been re-checked
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions/GGM rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 56s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Probability rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Advantage rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Hopping rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Protocols rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Bridges/Machines rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Games/Efficiency rc=0 3s errors=0 sorry=4
TCSlib/Cryptography/Games/Bridges/Experiments rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Bridges/Strategies rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Games/Bridges rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom/Functions rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Pseudorandom rc=0 2s errors=0 sorry=0
audits/pass-shelat/Checks rc=0 86s errors=0 sorry=0
# done 2026-11-06T00:02:59Z

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/replay-cmp.txt =====

TCSlib/Cryptography/Games/OracleComp	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Pseudorandom/Functions/Defs	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Pseudorandom/Functions/GGM	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Asymptotic/PRFLemmas	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Asymptotic/GGMReduction	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Asymptotic/GGMReductionEval	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Asymptotic/PRF	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Asymptotic/MultiMessage	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Asymptotic	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/Probability	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/Simulate	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/Advantage	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/Hopping	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/Protocols	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/Machines	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/BitCodec	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/Bridges/QueryTree	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/Bridges/Machines	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/Efficiency	rc=0	errors=0	sorry=4	base: = =
TCSlib/Cryptography/Games/Bridges/Experiments	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/Bridges/Strategies	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Games/Bridges	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Pseudorandom/Functions	rc=0	errors=0	sorry=0	base: = =
TCSlib/Cryptography/Pseudorandom	rc=0	errors=0	sorry=0	base: = =
audits/pass-shelat/Checks	rc=0	errors=0	sorry=0	base: = =
# 30 modules; rc≠0, errors or sorry-count differences: 0

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/axioms.log =====

# #print axioms for every public theorem of the 7 files changed by 947606fe and a588adfed01eefe6971abd0846e3938ad02e8624 (generator g03l-ax/axgen.py; print file compiled with lean, no .olean written, against the replayed tree): 155 theorems, 155 standard (subsets of propext, Classical.choice, Quot.sound); non-standard (incl. sorryAx): 0; errors: 0
'TCSlib.Cryptography.eval_chainTree' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.boundedBy_chainTree' depends on axioms: [propext]
'TCSlib.Cryptography.multiMsgAdv_boundedBy' depends on axioms: [propext]
'TCSlib.Cryptography.acceptProb_oracleDist_multiMsgAdv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.prfAdv_multiMsgAdv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_not_injective_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.pushesUniform_comp_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.acceptProb_otpEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.distAdv_prfEncReal_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.polyTimeComputable_prfEncFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.polyTimeComputable_prfDecWF' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.polyTimeComputable_prfDecFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.runAt_prfEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.runAt_prfDec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decodeFin_runAt_prfDec_of_not_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encodeTuple_eq_flatten' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.prfScheme_multiEncDist' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.prfScheme_multiMessageSecure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_multiMessageSecure_of_prf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_multiMessageSecure_of_exists_prg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.abs_uexp_le_uexp_abs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.abs_uexp_sub_le_uprob' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.card_filter_lt_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.uprob_eq_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.negligible_choose_div_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.acceptProb_oracleDist_congr_equiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.MultiMsg.prfAdv_congr_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.length_histBlock' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.encodeHist_eq_flatMap' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.eval_histBlockLen' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.length_flatMap_of_length' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.flatMap_range_blocks' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.flatMap_const_singleton' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.flatMap_const_replicate' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.pairFstD_pairFstD_histBlock' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.length_maskBlock' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.dbl_append' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.zipWith_xor_replicate_false' does not depend on any axioms
'TCSlib.Cryptography.MultiMsg.zipWith_xor_dbl' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.zipWith_xor_histBlock_maskBlock' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.zipWith_xor_flatten_ofFn' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.take_drop_ofFn_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.polyTimeComputable_blockMapFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.polyTimeComputable_preFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.polyTimeComputable_postFun' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.MultiMsg.length_flatten_of_length' depends on axioms: [propext]
'TCSlib.Cryptography.MultiMsg.length_maskOf' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.decodeOracleMove_query' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.decodeOracleMove_ret' does not depend on any axioms
'TCSlib.Cryptography.MultiMsg.postFun_layout' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.flatMap_ofFn' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.preFun_encodeHist' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.bind_eq_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.pure_eq_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.map_eq_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.pure_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.query_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.bind_pure' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.bind_assoc' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.call_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.singleSpec_dom' does not depend on any axioms
'TCSlib.Cryptography.Games.singleSpec_rng' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleSpec.add_dom_inl' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleSpec.add_dom_inr' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleSpec.add_rng_inl' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleSpec.add_rng_inr' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.liftLeft_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.liftRight_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_query' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.mono' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.bind' depends on axioms: [propext]
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_liftLeft' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_liftRight' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.allOutputs_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.allOutputs_query' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.allOutputs_true' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.AllOutputs.mono' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.AllOutputs.bind' does not depend on any axioms
'TCSlib.Cryptography.Games.ProbComp.sampleFin_eq' does not depend on any axioms
'TCSlib.Cryptography.Games.ProbComp.sample_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_query' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sampleFin' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sample' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_eq_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_or_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_not' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.dist_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ExecOutcome.swap_done' does not depend on any axioms
'TCSlib.Cryptography.Games.ExecOutcome.swap_outOfFuel' does not depend on any axioms
'TCSlib.Cryptography.Games.ExecOutcome.swap_sentAfterEnd' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.step_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.step_send' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.step_coin' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.close_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.close_send' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.close_coin' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.endWith_eq' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.exec_zero' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.exec_succ' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.endWithT_ne_outOfFuel' depends on axioms: [propext]
'TCSlib.Cryptography.Games.Party.execT_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.Party.stepT_fst' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Party.closeT_fst' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Party.endWithT_fst' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Party.execT_outcome' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.queryImpl_def' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_query' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_call' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.QueryImpl.ofComp_apply' does not depend on any axioms
'TCSlib.Cryptography.Games.QueryImpl.passthrough_apply' does not depend on any axioms
'TCSlib.Cryptography.Games.QueryImpl.sum_inl' does not depend on any axioms
'TCSlib.Cryptography.Games.QueryImpl.sum_inr' does not depend on any axioms
'TCSlib.Cryptography.Games.QueryImpl.comp_apply' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_comp' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.QueryImpl.withLog_apply' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_withLog' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_costBoundedBy' depends on axioms: [propext]
'TCSlib.Cryptography.uprob_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_prod_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_sections_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_update_absorb' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_update_absorb'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_update_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.QueryTree.noteQuery_of_mem' depends on axioms: [propext]
'TCSlib.Cryptography.QueryTree.noteQuery_of_not_mem' depends on axioms: [propext]
'TCSlib.Cryptography.QueryTree.idxOf_noteQuery_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.QueryTree.length_noteQuery_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.QueryTree.evalLazy_ret' depends on axioms: [propext]
'TCSlib.Cryptography.QueryTree.evalLazy_query' depends on axioms: [propext]
'TCSlib.Cryptography.QueryTree.evalLazy_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.QueryTree.evalLazy_comp' depends on axioms: [propext]
'TCSlib.Cryptography.QueryTree.extendStream_update_of_ne' depends on axioms: [Classical.choice]
'TCSlib.Cryptography.QueryTree.extendStream_update_self' depends on axioms: [propext, Classical.choice]
'TCSlib.Cryptography.QueryTree.uprob_evalLazy' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/lint.log =====

# scripts/style_lint.py on each file changed by the two commits (947606fe, a588adfed01eefe6971abd0846e3938ad02e8624; wip/g04r4; base 27ae72da62119ebdde380b8cb2d8c183b59fa2bf)
TCSlib/Cryptography/Asymptotic/MultiMessage.lean: 0 findings in 1 files (rc=0)
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean: 0 findings in 1 files (rc=0)
TCSlib/Cryptography/Games/OracleComp.lean: 0 findings in 1 files (rc=0)
TCSlib/Cryptography/Games/Probability.lean: 0 findings in 1 files (rc=0)
TCSlib/Cryptography/Games/Protocols.lean: 0 findings in 1 files (rc=0)
TCSlib/Cryptography/Games/Simulate.lean: 0 findings in 1 files (rc=0)
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean: 0 findings in 1 files (rc=0)

# scripts/style_lint.py on all 26 files of #195's change set at a588adfed01eefe6971abd0846e3938ad02e8624
TCSlib/Cryptography/Asymptotic/MultiMessage.lean: 0 findings in 1 files
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean: 0 findings in 1 files
TCSlib/Cryptography/Asymptotic/PRF.lean: 0 findings in 1 files
TCSlib/Cryptography/Asymptotic/PRFLemmas.lean: 0 findings in 1 files
TCSlib/Cryptography/Foundations/Experiments.lean: 0 findings in 1 files
TCSlib/Cryptography/Foundations/Probability.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Advantage.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/BitCodec.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Bridges.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Bridges/Experiments.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Bridges/Machines.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Bridges/QueryTree.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Bridges/Strategies.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Efficiency.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Hopping.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Machines.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/OracleComp.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Probability.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Protocols.lean: 0 findings in 1 files
TCSlib/Cryptography/Games/Simulate.lean: 0 findings in 1 files
TCSlib/Cryptography/Pseudorandom/Functions/Defs.lean: 0 findings in 1 files
TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean: 0 findings in 1 files
TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean: 0 findings in 1 files
TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean: 0 findings in 1 files
TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean: 0 findings in 1 files
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean: 0 findings in 1 files

# scripts/campaign_style_lint.py --check8b TCSlib/Cryptography/Games at a588adfed01eefe6971abd0846e3938ad02e8624
style_lint: 0 FAIL, 0 WARN over 14 files
(rc=0)

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/REPORT.md =====

# Gate 04 round 4 (PR #195, S2b): R3-01 repair and the complete rule-10 seal

(Saved by the maintainer from the worker's hand-back; the worker could not write report files.)

- Base `27ae72da62119ebdde380b8cb2d8c183b59fa2bf`; merge base `a3c5fa8b72e50939822f22364647dc844a3914a0`.
- Commit `947606fecf1142997661651701f04c3912ba7551` on `wip/g04r4` (`SP/wt-g04r4`): 5 files, +38/−21,
  proof bodies only; 13 declarations re-proved; no statement, docstring, `@[simp]` or `sorry` change.
- Fixes (each now through published equations): `ProbComp.expect_bind` (R3-01);
  `Games/Protocols.lean`'s three `example`s, `Party.stepT_fst`, `closeT_fst`, `execT_outcome`
  (`OracleComp.bind` by `rfl`, missed by r3's hand-picked seal row);
  `LazySampling.lean`'s `evalLazy_congr`, `evalLazy_comp`, `uprob_evalLazy_aux`;
  `MultiMessage.lean`'s `boundedBy_chainTree`; `MultiMessageLemmas.lean`'s
  `acceptProb_oracleDist_congr_equiv`, `prfAdv_congr_equiv` (statement's universe binders changed
  by #195, so treated as changed).
- Seal at the final commit: **26 of 26 files PASS** with automatically collected candidates
  (`seal-evidence.log`); `$BASE` control fails exactly at the fixed declarations
  (`seal-control-base.log`); plain seal failures are exactly the named entries (`seal-plain.log`).
- Named entries (`exclusions.md`): section A, 48 inherited, unchanged ch. 2–4 definitional reads;
  section B, 75 explicit unfolds the seal cannot see (all inherited, unchanged); section C, 29
  type-level reads of `Games.QueryImpl` and `Games.OracleSpec.add` in the S2a/S2b layer
  (statements and definition bodies), which no re-proof can remove. Check: 0 entries in A or B on
  a declaration #195 added or changed.
- Decision needed: make `QueryImpl` and `OracleSpec.add` `abbrev` (tested in a shadow copy, not
  committed: 30 downstream modules plus `Checks` rc=0 and all 14 `Games/` files seal with no
  entry; `abbrev-experiment.log`), or accept section C as recorded exceptions.
- Replay: 22 downstream modules plus `Checks`, rc=0, sorry counts equal to the r3 logs
  (`replay.log`, `replay-cmp.txt`). Axioms: 114 public theorems of the 5 files, all standard
  (`axioms.log`). Lint: 0 findings on all 26 files; check 8b on `Games/` 0 FAIL, 0 WARN
  (`lint.log`).
- Method and tools: `tools/` (collector `collect_body.lean`, `seal.py`, `scan.py`, `exclude.py`,
  `exclusions_md.py`), cross-check with r3's names (`seal-r3union.log`).

## Update: R-04-4 applied (second commit)

- `a588adfed01eefe6971abd0846e3938ad02e8624` changes only two headers, `def` → `abbrev`, for
  `Games.QueryImpl` (`Simulate.lean`) and `Games.OracleSpec.add` (`OracleComp.lean`).
- At `a588adfe`: the seal passes on all 26 files; the 14 `Games/` files need no entry (the plain
  seal passes on each); section C of `exclusions.md` is empty; sections A and B unchanged (48 and
  75 entries, all on declarations #195 did not change). `$BASE` control fails at the re-proved
  declarations and at the former section-C ones.
- Replay of the 30 modules downstream of the two files plus `Checks`: rc=0, sorry counts equal to
  the base (`Games/Efficiency` 4, others 0). Axioms: 155 public theorems of the 7 changed files,
  all standard. Lint 0 on all 26 files; check 8b on `Games/` 0/0.
- The table and section C above describe the first commit only; the refreshed logs are at
  `a588adfe` (round-1 evidence kept in `intermediate/r1/`).

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/tool-collect_body.lean.txt =====

/- Rule-10 seal candidate collector (gate 04 round 4).
For each target module F: walk every constant declared in F's module (type and value), and keep the
constants that are definitions (`ConstantInfo.defnInfo`) declared in a different module under
`TCSlib`, excluding instances, `@[reducible]` declarations, structure projections, auxiliary
recursors / `noConfusion`, matchers and internal or generated auxiliaries (`match_N`, `proof_N`,
`eq_N`, `eq_def`, `eq_unfold`, `_`-components).
A foreign instance or reducible declaration is transparent, so it is not sealed itself; its value is
walked (transitively, foreign `TCSlib` only) and the definitions found there are kept with
`via <instance/abbrev>`.
Also reported: references to the generated equation lemmas (`X.eq_N`, `X.eq_def`, `X.eq_unfold`)
of a foreign `TCSlib` definition `X` from F's declarations, i.e. explicit unfolds visible in
proof terms. -/
open Lean Meta

namespace G04R4Collect

def numSuffix (s pre : String) : Bool :=
  s.startsWith pre && (s.drop pre.length).length > 0 && (s.drop pre.length).all Char.isDigit

def isGenEqnStr (s : String) : Bool := numSuffix s "eq_" || s == "eq_def" || s == "eq_unfold"

def genEqnParent? : Name → Option Name
  | .str p s => if isGenEqnStr s then some p else none
  | _ => none

def isAuxComp (s : String) : Bool :=
  s.startsWith "_" || numSuffix s "match_" || numSuffix s "proof_" || isGenEqnStr s

def isAuxName : Name → Bool
  | .str p s => isAuxComp s || isAuxName p
  | .num _ _ => true
  | .anonymous => false

partial def ownerOf (n : Name) : Name :=
  let n := (privateToUserName? n).getD n
  go n
where
  go : Name → Name
    | n@(.str p s) =>
      if isAuxComp s || ["induct", "mutual_induct", "eq_spec"].contains s then go p else n
    | .num p _ => go p
    | n => n

def kindOf (env : Environment) (n : Name) : String :=
  match env.find? n with
  | some (.defnInfo _) =>
    if isAuxName n || isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then "def-aux"
    else if env.isProjectionFn n then "def-proj"
    else if isInstanceCore env n then "def-instance"
    else if getReducibilityStatusCore env n == .reducible then "def-reducible"
    else if isPrivateName n then "def-private"
    else if getReducibilityStatusCore env n == .irreducible then "def-irreducible"
    else "def"
  | some (.thmInfo _) => "thm"
  | some (.axiomInfo _) => "axiom"
  | some (.opaqueInfo _) => "opaque"
  | some (.quotInfo _) => "quot"
  | some (.inductInfo _) => "inductive"
  | some (.ctorInfo _) => "ctor"
  | some (.recInfo _) => "rec"
  | none => "none"

structure St where
  cands : Std.HashMap Name (String × Array String × NameSet) := {}  -- cand ↦ (module, vias, owners)
  usesBy : Std.HashMap Name NameSet := {}                         -- owner ↦ candidates
  eqnHits : Array (Name × Name × Name) := #[]                     -- (owner, decl, eqn lemma)
  transp : NameSet := {}                                          -- foreign instances/abbrevs walked
  privs : NameSet := {}
  nsrc : Nat := 0

end G04R4Collect

open G04R4Collect in
run_cmd do
  let env ← getEnv
  let mods := targetMods
  let modNames := env.header.moduleNames
  let isTCS (j : ModuleIdx) : Bool := (modNames[j.toNat]!).getRoot == `TCSlib
  -- constant table of every imported TCSlib constant (for the source scan)
  let mut table : Array String := #[]
  for j in [0:modNames.size] do
    if (modNames[j]!).getRoot == `TCSlib then
      let d := env.header.moduleData[j]!
      for c in d.constNames do
        table := table.push s!"{c}\t{kindOf env c}\t{modNames[j]!}"
  IO.FS.writeFile (outDir / "tcslib-constants.tsv") ("\n".intercalate table.toList ++ "\n")
  let mut summary : Array String := #[]
  for m in mods do
    let some idx := env.getModuleIdx? m | throwError "module {m} not imported"
    let data := env.header.moduleData[idx.toNat]!
    let mut st : St := {}
    -- source tier: TCSlib lemmas named in the file's simp/rw lemma lists (from the source scan),
    -- whose statements' definitions can enter goals with no trace in the proof term
    let srcFile := outDir / "srclemmas" / s!"{m}.txt"
    let mut srcPairs : Array (Name × Name) := #[]
    if (← srcFile.pathExists) then
      for l in (← IO.FS.readFile srcFile).splitOn "\n" do
        match l.splitOn "\t" with
        | [o, t] => srcPairs := srcPairs.push (o.toName, t.toName)
        | _ => pure ()
    let mut srcConsts : Array ConstantInfo := #[]
    for (o, t) in srcPairs do
      if let some ti := env.find? t then
        let tv : TheoremVal := { name := o, levelParams := [], type := ti.type, value := mkConst t, all := [o] }
        srcConsts := srcConsts.push (.thmInfo tv)
    for (ci, isSrc) in data.constants.map (·, false) ++ srcConsts.map (·, true) do
      st := { st with nsrc := st.nsrc + 1 }
      let owner := ownerOf ci.name
      let selfIsEqn := (genEqnParent? ci.name).isSome
      -- worklist of (constant, via)
      -- worklist of (constant, how it was reached: none = occurs in the declaration,
      -- `inst:I` = in the body of the transparent instance/abbreviation I, `stmt:T` = in the statement
      -- of the TCSlib lemma T that the declaration uses)
      let mut work : Array (Name × Option String) :=
        if isSrc then
          match ci.value? with
          | some (.const t _) => ci.type.getUsedConstantsAsSet.toArray.map (·, some s!"src:{t}")
          | _ => #[]
        else ci.getUsedConstantsAsSet.toArray.map (·, none)
      let mut seen : NameSet := {}
      let mut seenD : NameSet := {}
      while !work.isEmpty do
        let (u, via) := work.back!
        work := work.pop
        if (via.isNone && seenD.contains u) || (via.isSome && seen.contains u) then continue
        let firstTime := !seen.contains u
        seen := seen.insert u
        if via.isNone then seenD := seenD.insert u
        -- generated equation lemma of a foreign TCSlib definition (the lemma itself may live anywhere)
        if via.isNone && !selfIsEqn then
          if let some p := genEqnParent? u then
            if let some jp := env.getModuleIdxFor? p then
              if jp != idx && isTCS jp then
                if let some (.defnInfo _) := env.find? p then
                  st := { st with eqnHits := st.eqnHits.push (owner, ci.name, u) }
        let some j := env.getModuleIdxFor? u | continue
        if j == idx || !isTCS j then continue
        let k := kindOf env u
        if k == "def" || k == "def-irreducible" then
          let (md, vias, owners) := st.cands.getD u (toString modNames[j.toNat]!, #[], {})
          let tag := via.getD "direct"
          let vias := if vias.contains tag then vias else vias.push tag
          st := { st with cands := st.cands.insert u (md, vias, owners.insert owner),
                          usesBy := st.usesBy.insert owner ((st.usesBy.getD owner {}).insert u) }
        else if !firstTime then continue
        else if k == "def-instance" || k == "def-reducible" then
          st := { st with transp := st.transp.insert u }
          if let some (.defnInfo dv) := env.find? u then
            for v in dv.value.getUsedConstantsAsSet.toArray do
              unless seen.contains v do work := work.push (v, some (via.getD s!"inst:{u}"))
        else if k == "thm" && via.isNone then
          -- one level: the definitions a used lemma's statement mentions can appear in the goals
          -- that rewriting with it produces (simp applies rfl-lemmas without a proof-term trace)
          if let some ti := env.find? u then
            for v in ti.type.getUsedConstantsAsSet.toArray do
              unless seen.contains v do work := work.push (v, some s!"stmt:{u}")
        else if k == "def-private" then
          st := { st with privs := st.privs.insert u }
    -- write the candidate file
    let mut lines : Array String := #[s!"# seal candidates for {m} ({st.nsrc} constants walked)",
      "# format: <candidate>\t<defining module>\t<direct | inst:<transparent instance/abbrev> | stmt:<used lemma whose statement mentions it>>\t<declarations of the file using it>"]
    let keys := st.cands.toArray.qsort (fun a b => Name.lt a.1 b.1)
    let nIrr := (keys.filter fun (n, _) => kindOf env n == "def-irreducible").size
    lines := lines.push s!"# {keys.size - nIrr} candidates sealed by the seal line; {nIrr} already `[irreducible]` globally (sealed by construction, listed as `# already-irreducible:`)"
    for (n, (md, vias, owners)) in keys do
      let os := owners.toArray.qsort Name.lt
      let osTxt := ", ".intercalate (os.toList.take 12 |>.map toString) ++
        (if os.size > 12 then s!", … (+{os.size - 12})" else "")
      let pre := if kindOf env n == "def-irreducible" then "# already-irreducible: " else ""
      lines := lines.push s!"{pre}{n}\t{md}\t{", ".intercalate (vias.toList.take 4) ++ (if vias.size > 4 then s!", … (+{vias.size - 4})" else "")}\t{osTxt}"
    IO.FS.writeFile (outDir / s!"{m}.txt") ("\n".intercalate lines.toList ++ "\n")
    -- per-declaration uses
    let mut ul : Array String := #[]
    for (o, s) in st.usesBy.toArray.qsort (fun a b => Name.lt a.1 b.1) do
      ul := ul.push s!"{o}: {" ".intercalate ((s.toArray.qsort Name.lt).toList.map toString)}"
    IO.FS.writeFile (outDir / s!"{m}.uses.txt") ("\n".intercalate ul.toList ++ "\n")
    -- equation-lemma hits
    let mut el : Array String := #[]
    for (o, d, e) in st.eqnHits do
      el := el.push s!"{m}\t{o}\t{d}\t{e}"
    IO.FS.writeFile (outDir / s!"{m}.eqn.txt") ("\n".intercalate el.toList ++ (if el.isEmpty then "" else "\n"))
    let tr := ", ".intercalate ((st.transp.toArray.qsort Name.lt).toList.map toString)
    let pv := ", ".intercalate ((st.privs.toArray.qsort Name.lt).toList.map toString)
    summary := summary.push s!"{m}\tcandidates={keys.size}\talreadyIrreducible={nIrr}\teqnHits={st.eqnHits.size}\ttransparent=[{tr}]\tprivateForeign=[{pv}]"
  IO.FS.writeFile (outDir / "summary.tsv") ("\n".intercalate summary.toList ++ "\n")

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/tool-seal.py.txt =====

"""Rule-10 seal (gate 04 round 4), adapted from gates/04-s2b/evidence-r3/seal.py.txt.

seal.py <tag> <worktree> <olean-tree> <candidate-dir> <files.txt> <outdir> [--rev REV] [--unseal U.json] [--lenient]

For every Lean file F in <files.txt>: take F's source (the worktree file, or `git show REV:F` with
--rev), insert `attribute [local irreducible] <every candidate of F>` after its header (imports and
set_option lines), and compile the copy with `lean` (no .olean is written) against <olean-tree>.
The candidates are the first column of <candidate-dir>/<module>.txt, written by the automatic
collector (tools/collect_body.lean); nothing is hand-picked.

Named exclusions (--unseal): U.json maps a file to a list of {"decl": <full name>, "names": [...]}.
Each listed declaration (with its docstring and attribute lines) is wrapped in
`section G04R4Unseal` / `attribute [local semireducible] <names>` / `end G04R4Unseal`, so exactly
that declaration may read exactly those foreign definitions, and every other declaration of F is
still compiled with every candidate sealed. An error on an inserted line is reported as SEAL-ERROR
(a seal that did not apply can never count as a pass)."""
import json, os, re, subprocess, sys
from pathlib import Path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import declx

tag, WT, OL, CAND, FILES, OUT = sys.argv[1:7]
rest = sys.argv[7:]
rev = rest[rest.index('--rev') + 1] if '--rev' in rest else None
unseal = json.load(open(rest[rest.index('--unseal') + 1])) if '--unseal' in rest else {}
LENIENT = '--lenient' in rest
WT, OUT = Path(WT).resolve(), Path(OUT).resolve()
OUT.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env["LEAN_PATH"] = ":".join([OL] + sorted(str(d) for d in (WT / ".lake/packages").glob("*/.lake/build/lib/lean")))
env["PATH"] = str(Path.home() / ".elan/bin") + ":" + env["PATH"]
TIMEOUT = 1200

def candidates(path):
    mod = path[:-5].replace('/', '.')
    return [l.split('\t')[0] for l in open(Path(CAND) / f"{mod}.txt", encoding='utf-8')
            if l.strip() and not l.startswith('#')]

def header_end(lines):
    i, last, in_c = 0, -1, False
    while i < len(lines):
        s = lines[i].strip()
        if in_c:
            if '-/' in s: in_c = False
        elif s.startswith('/-') and not s.startswith('/-!'):
            in_c = '-/' not in s[2:]
        elif s.startswith('import ') or s.startswith('set_option '):
            last = i
        elif s == '' or s.startswith('--'):
            pass
        else:
            break
        i += 1
    return last

def build(src, names, entries):
    lines = src.split('\n')
    # a file's own `attribute [local irreducible] …` line would fail on names the top seal already
    # made irreducible: drop exactly those names from it (the top seal covers them from line 1)
    for i, l in enumerate(lines):
        m = re.match(r'^(\s*attribute \[local irreducible\])\s+(.*)$', l)
        if m:
            toks = m.group(2).split()
            keep = [t for t in toks if not any(n == t or n.endswith('.' + t) for n in names)]
            lines[i] = (m.group(1) + ' ' + ' '.join(keep)) if keep else ('-- (covered by the seal line) ' + l.strip())
            OWNSEAL.append(f"{i + 1}: {l.strip()} -> {lines[i].strip()}")
    exts = {e['name']: e for e in declx.extents(src)}
    h = header_end(lines)
    before, after = {}, {}          # 0-based original line -> inserted lines
    before.setdefault(h + 1, []).append("attribute [local irreducible] " + " ".join(names) if names
                                        else "-- (no candidates)")
    used = []
    for ent in entries:
        e = exts.get(ent['decl'])
        if e is None:
            if LENIENT:
                SKIPPED.append(ent['decl']); continue
            raise SystemExit(f"unseal: declaration {ent['decl']} not found")
        ns = [n for n in ent['names'] if n in names]
        before.setdefault(e['dstart'] - 1, []).extend(
            ["section G04R4Unseal", "attribute [local semireducible] " + " ".join(ns)])
        after.setdefault(e['end'] - 1, []).append("end G04R4Unseal")
        used.append((ent['decl'], e['dstart'], e['end'], ns))
    out, omap = [], []              # omap[k] = original 1-based line of output line k+1, or None
    for i, l in enumerate(lines + ([] if h + 1 < len(lines) else [''])):
        for x in before.get(i, []): out.append(x); omap.append(None)
        if i < len(lines): out.append(l); omap.append(i + 1)
        for x in after.get(i, []): out.append(x); omap.append(None)
    return '\n'.join(out), omap, exts, used

OWNSEAL = []
SKIPPED = []
results = []
files = [l.strip() for l in open(FILES) if l.strip()]
for path in files:
    names = candidates(path)
    if rev:
        src = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=WT, capture_output=True, text=True).stdout
    else:
        src = (WT / path).read_text(encoding='utf-8')
    entries = unseal.get(path, [])
    OWNSEAL.clear(); SKIPPED.clear()
    text, omap, exts, used = build(src, names, entries)
    f = OUT / (path.replace('/', '_')[:-5] + f"_{tag}.lean")
    f.write_text(text, encoding='utf-8')
    try:
        r = subprocess.run(["lean", str(f)], cwd=WT, env=env, capture_output=True, text=True, timeout=TIMEOUT)
        outp, rc = r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired:
        outp, rc = f"{f}:1:0: error: TIMEOUT after {TIMEOUT}s", -9
    errs = [l for l in outp.splitlines() if re.search(r':\d+:\d+: error', l)]
    sorted_exts = sorted(exts.values(), key=lambda e: e['dstart'])
    def owner(oln):
        best = None
        for e in sorted_exts:
            if e['dstart'] <= oln: best = e
        return f"{best['kind']} {best['name']}" if best else '?'
    detail, seal_err = [], False
    for e in errs:
        m = re.search(r':(\d+):(\d+): error:?\s*(.*)', e)
        k = int(m.group(1))
        oln = omap[k - 1] if 0 < k <= len(omap) else None
        if oln is None:
            seal_err = True
            detail.append(f"   SEAL-LINE {k}: {m.group(3)[:200]}")
        else:
            detail.append(f"   {path}:{oln}:{m.group(2)} [{owner(oln)}] {m.group(3)[:160]}")
    if rc != 0 and not errs:
        detail.extend("   RAW: " + l[:200] for l in outp.splitlines()[:15])
    st = 'SEAL-ERROR' if seal_err else ('PASS' if rc == 0 and not errs else 'FAIL')
    unote = f"; unsealed for {len(used)} named declaration(s)" if used else ''
    results.append(f"{path}: candidates={len(names)}{unote} {st} (rc={rc}, error lines={len(errs)})")
    for o in OWNSEAL:
        results.append(f"   own seal line {o}")
    for o in SKIPPED:
        results.append(f"   unseal entry not applicable at this revision (declaration absent): {o}")
    for (d, a, b, ns) in used:
        results.append(f"   unseal {d} (lines {a}-{b}): {' '.join(ns)}")
    results.extend(detail)
    print('\n'.join(results[-(1 + len(OWNSEAL) + len(SKIPPED) + len(used) + len(detail)):]), flush=True)
(OUT / f"results_{tag}.txt").write_text('\n'.join(results) + '\n', encoding='utf-8')

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/tool-scan.py.txt =====

"""Rule-10 source scan (gate 04 round 4).

scan.py <worktree> <files.txt> <constants.tsv> <candidate-dir> <seal-results.txt> <out.log> [--rev REV]

For every Lean file F: find every explicit `unfold X`, `delta X`, and every name X passed in the
lemma list of `rw`/`rwa`/`rewrite`/`erw`/`nth_rw`/`nth_rewrite`/`simp_rw`/`simp`/`simp only`/
`simp_all`/`simpa`/`dsimp`/`dsimp only`/`norm_num`/`field_simp`/`simp_arith`/`push_cast`, and
resolve X (namespace and `open` context of the line) against the table of TCSlib constants written
by the collector. A hit is an X that resolves to a definition (kind `def`, `def-reducible`,
`def-instance`) declared in another TCSlib module, or to a generated equation lemma
(`X.eq_N`/`X.eq_def`/`X.eq_unfold`) of such a definition. `show`/`change` steps are covered by the
seal (they are checked by definitional unification at default transparency, which the
`local irreducible` seal blocks); the scan lists every `show`/`change` that sits on a line where the
seal failed. The proof-term check of the collector (references to generated equation lemmas of a
foreign definition) is appended."""
import re, sys, os
from pathlib import Path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import declx

WT, FILES, TABLE, CAND, SEALRES, OUT = sys.argv[1:7]
REV = sys.argv[sys.argv.index('--rev') + 1] if '--rev' in sys.argv else None
SRCLEM = sys.argv[sys.argv.index('--srclemmas') + 1] if '--srclemmas' in sys.argv else None
import subprocess
kinds, mods = {}, {}
for l in open(TABLE, encoding='utf-8'):
    p = l.rstrip('\n').split('\t')
    if len(p) == 3:
        kinds[p[0]] = p[1]; mods[p[0]] = p[2]

def strip_comments(src):
    """Blank out comments (nested block comments and docstrings, line comments) and string
    literals, keeping line structure."""
    out, i, depth, n = [], 0, 0, len(src)
    instr = False
    while i < n:
        c = src[i]
        if depth == 0 and not instr and src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if not instr and src.startswith('/-', i):
            depth += 1; out.append('  '); i += 2; continue
        if depth > 0 and src.startswith('-/', i):
            depth -= 1; out.append('  '); i += 2; continue
        if depth > 0:
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if c == '"' and (i == 0 or src[i - 1] != '\\'):
            instr = not instr; out.append(' '); i += 1; continue
        if instr:
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        out.append(c); i += 1
    return ''.join(out)

TAC = re.compile(r'(?<![\w.\'])(unfold|delta|rw|rwa|rewrite|erw|nth_rw|nth_rewrite|simp_rw|simp_all|simpa|simp|dsimp|norm_num|field_simp|simp_arith|push_cast|rw_mod_cast)(\??!?)(?![\w\'])')
IDENT = re.compile(r"[^\s,\[\]()⟨⟩:;{}←]+")

def bracket_list(text, k):
    """If a `[ ... ]` list starts at or after k (skipping `only`, config, `at` clauses are after),
    return (start, end) of its content."""
    m = re.compile(r'\s*(?:only\s*)?(?:\(config\s*:=[^)]*\)\s*)?(?:\(\s*\w+\s*:=[^)]*\)\s*)*(?:only\s*)?\[').match(text, k)
    if not m:
        return None
    s = m.end(); d = 1; j = s
    while j < len(text) and d:
        if text[j] == '[': d += 1
        elif text[j] == ']': d -= 1
        j += 1
    return (s, j - 1)

def items(seg):
    out, d, cur, start = [], 0, '', 0
    for idx, ch in enumerate(seg):
        if ch in '([⟨{': d += 1
        elif ch in ')]⟩}': d -= 1
        if ch == ',' and d == 0:
            out.append((start, cur)); cur = ''; start = idx + 1
        else:
            cur += ch
    out.append((start, cur))
    return out

def head_ident(item):
    t = item.strip()
    t = re.sub(r'^(←|<-|↓|-|@|\(|\s)+', '', t)
    m = IDENT.match(t)
    return m.group(0).rstrip('.') if m else None

def resolve(tok, ns, opens, mymod):
    """Lean's order (Lean/ResolveName.lean, resolveGlobalName): the innermost namespace level with
    a match wins; otherwise the exact name, this module's private name and the open namespaces."""
    if tok.startswith('_root_.'):
        return [tok[7:]] if tok[7:] in kinds else []
    parts = ns.split('.') if ns else []
    for k in range(len(parts), 0, -1):
        p = '.'.join(parts[:k])
        hit = [x for x in (f"{p}.{tok}", f"_private.{mymod}.0.{p}.{tok}") if x in kinds]
        if hit:
            return hit
    res = [x for x in (tok, f"_private.{mymod}.0.{tok}") if x in kinds]
    for o in sorted(opens):
        full = f"{o}.{tok}"
        if full in kinds and full not in res:
            res.append(full)
    return res

EQN = re.compile(r'^(.*)\.(eq_\d+|eq_def|eq_unfold)$')

def classify(full, mymod):
    m = EQN.match(full)
    if m and m.group(1) in kinds:
        par = m.group(1)
        if mods[par] != mymod and kinds[par] in ('def', 'def-reducible', 'def-instance'):
            return ('eqn-lemma-of-foreign-def', par)
        return None
    if mods.get(full) != mymod and kinds.get(full) in ('def', 'def-irreducible', 'def-reducible', 'def-instance'):
        return ({'def': 'foreign-def', 'def-irreducible': 'foreign-def', 'def-reducible': 'foreign-abbrev',
                 'def-instance': 'foreign-instance'}[kinds[full]], full)
    return None

sealfail = {}
for l in open(SEALRES, encoding='utf-8'):
    m = re.match(r'\s+(\S+\.lean):(\d+):', l)
    if m: sealfail.setdefault(m.group(1), set()).add(int(m.group(2)))

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|example|opaque)\b\s*(\S*)')

hits, shows, nshow = [], [], 0
srclem = {}
files = [l.strip() for l in open(FILES) if l.strip()]
for path in files:
    mymod = path[:-5].replace('/', '.')
    raw = (subprocess.run(['git', '-C', WT, 'show', f'{REV}:{path}'], capture_output=True, text=True).stdout
           if REV else (Path(WT) / path).read_text(encoding='utf-8'))
    src = strip_comments(raw)
    rawlines = raw.split('\n')
    lines = src.split('\n')
    exts = declx.extents(raw)
    # namespace / open context per line
    ctx, stack, opens_stack = [], [], [set()]
    for ln in lines:
        s = ln.strip()
        m = re.match(r'^namespace\s+(\S+)', s)
        if m:
            stack.append(('ns', m.group(1))); opens_stack.append(set(opens_stack[-1]))
        m2 = re.match(r'^section\b', s)
        if m2:
            stack.append(('sec', '')); opens_stack.append(set(opens_stack[-1]))
        m3 = re.match(r'^end\b', s)
        if m3 and stack:
            stack.pop(); opens_stack.pop()
        m4 = re.match(r'^open\s+(?:scoped\s+)?([^()\n]*?)(?:\s+in)?\s*$', s) or re.match(r'^open\s+(?:scoped\s+)?(.*?)\s+in\b', s)
        if m4:
            cur = '.'.join(x for k, x in stack if k == 'ns')
            for o in m4.group(1).split():
                if o in ('in', 'hiding', 'renaming') or '(' in o:
                    break
                opens_stack[-1].add(o)
                # an `open` inside a namespace may also name a sub-namespace of the current one
                parts = cur.split('.') if cur else []
                for k in range(len(parts), 0, -1):
                    opens_stack[-1].add('.'.join(parts[:k]) + '.' + o)
        ctx.append(('.'.join(x for k, x in stack if k == 'ns'), set(opens_stack[-1])))
    offs = [0]
    for ln in lines: offs.append(offs[-1] + len(ln) + 1)
    def lineof(pos):
        lo, hi = 0, len(offs) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if offs[mid] <= pos: lo = mid
            else: hi = mid - 1
        return lo + 1
    def declof(ln):
        for j in range(ln - 1, -1, -1):
            m = DECL.match(rawlines[j])
            if m: return f"{m.group(1)} {m.group(2)}"
        return '?'
    for m in TAC.finditer(src):
        tac = m.group(1)
        ln = lineof(m.start())
        ns, opens = ctx[ln - 1]
        toks = []
        if tac in ('unfold', 'delta'):
            rest = src[m.end():offs[ln] - 1] if ln < len(offs) else src[m.end():]
            rest = re.split(r'\bat\b|;|<;>|\)|\|', rest)[0]
            for t in rest.split():
                toks.append((t, ln))
        else:
            br = bracket_list(src, m.end())
            if not br:
                continue
            s, e = br
            for (o, it) in items(src[s:e]):
                h = head_ident(it)
                if h:
                    toks.append((h, lineof(s + o + (len(it) - len(it.lstrip())))))
        for (t, tl) in toks:
            for full in resolve(t, ns, opens, mymod):
                if SRCLEM and kinds.get(full) == 'thm' and tac not in ('unfold', 'delta'):
                    ow = [e['name'] for e in exts if e['dstart'] <= tl <= e['end']]
                    srclem.setdefault(mymod, set()).add((ow[0] if ow else '?', full))
                c = classify(full, mymod)
                if c:
                    hits.append(f"{path}:{tl}\t{tac}\t{t}\t{c[0]}\t{c[1]}\t{mods[c[1]]}\t[{declof(tl)}]\t{rawlines[tl - 1].strip()[:140]}")
    for m in re.finditer(r'(?<![\w.\'])(show|change)(?![\w\'])', src):
        ln = lineof(m.start()); nshow += 1
        if ln in sealfail.get(path, set()):
            shows.append(f"{path}:{ln}\t{m.group(1)}\t[{declof(ln)}]\t{rawlines[ln - 1].strip()[:140]}")

eqn = []
for path in files:
    mymod = path[:-5].replace('/', '.')
    p = Path(CAND) / f"{mymod}.eqn.txt"
    if p.exists():
        eqn += [l.rstrip('\n') for l in open(p, encoding='utf-8') if l.strip()]

with open(OUT, 'w', encoding='utf-8') as o:
    o.write(f"# rule-10 source scan over {len(files)} files{(' at ' + REV) if REV else ''}; hit = name resolving to a definition of another TCSlib module\n")
    o.write("# file:line\ttactic\ttoken\tkind\tforeign definition\tits module\t[declaration]\tsource line\n")
    o.write(f"## (c1) unfold/delta/rw/simp/dsimp lemma-list hits: {len(hits)}\n")
    for h in hits: o.write(h + '\n')
    o.write(f"## (c2) show/change steps on a line where the seal failed: {len(shows)} (of {nshow} show/change occurrences, all checked by the seal)\n")
    for s in shows: o.write(s + '\n')
    o.write(f"## (c3) proof terms referring to a generated equation lemma of a foreign TCSlib definition (collector): {len(eqn)}\n")
    o.write("# module\towner declaration\tconstant\tequation lemma\n")
    for e in eqn: o.write(e + '\n')
if SRCLEM:
    os.makedirs(SRCLEM, exist_ok=True)
    for f in files:
        md = f[:-5].replace('/', '.')
        with open(os.path.join(SRCLEM, md + '.txt'), 'w', encoding='utf-8') as o:
            for (ow, lm) in sorted(srclem.get(md, ())): o.write(f"{ow}\t{lm}\n")
print(len(hits), 'lemma-list hits;', len(shows), 'show/change at seal failures;', len(eqn), 'proof-term equation-lemma refs')

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/tool-exclude.py.txt =====

"""Derive minimal named unseal entries (gate 04 round 4).

exclude.py <worktree> <olean-tree> <candidate-dir> <files.txt> <outdir> <seed.json> <out.json> [jobs]

For each file F: start from the entries of <seed.json> for F (if any). Fixpoint: seal F with every
candidate and the current entries (tools/seal.py); for every declaration that still fails, unseal
for it the candidates it uses (collector's <module>.uses.txt), then, if it still fails, every
candidate. Minimisation: drop entries F passes without (cascades), then binary-partition each entry's
names, dropping every part F passes without (1-minimal: each remaining name is needed). Writes the entries to
<out.json> and a log of every step to <outdir>/exclude-<file>.log."""
import json, os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

WT, OL, CAND, FILES, OUT, SEED, RES = sys.argv[1:8]
jobs = int(sys.argv[8]) if len(sys.argv) > 8 else 3
TOOLS = Path(__file__).resolve().parent
OUT = Path(OUT).resolve(); OUT.mkdir(parents=True, exist_ok=True)
seed = json.load(open(SEED)) if os.path.exists(SEED) else {}

def cands(path):
    mod = path[:-5].replace('/', '.')
    return [l.split('\t')[0] for l in open(Path(CAND) / f"{mod}.txt", encoding='utf-8')
            if l.strip() and not l.startswith('#')]

def uses(path):
    mod = path[:-5].replace('/', '.')
    u = {}
    p = Path(CAND) / f"{mod}.uses.txt"
    for l in open(p, encoding='utf-8'):
        if ':' in l:
            o, rest = l.split(':', 1); u[o.strip()] = rest.split()
    return u

def run(path, entries, tag):
    d = OUT / 'work' / path.replace('/', '_')[:-5]
    d.mkdir(parents=True, exist_ok=True)
    (d / 'files.txt').write_text(path + '\n')
    js = {path: [{"decl": k, "names": sorted(v)} for k, v in entries.items() if v]}
    (d / 'unseal.json').write_text(json.dumps(js))
    r = subprocess.run([sys.executable, '-I', str(TOOLS / 'seal.py'), tag, WT, OL, CAND, str(d / 'files.txt'),
                        str(d), '--unseal', str(d / 'unseal.json')], capture_output=True, text=True)
    res = (d / f'results_{tag}.txt').read_text() if (d / f'results_{tag}.txt').exists() else r.stdout + r.stderr
    head = res.split('\n')[0]
    fails = []
    for l in res.split('\n')[1:]:
        m = re.match(r'\s+\S+:\d+:\d+ \[\w+ (\S+)\]', l)
        if m and m.group(1) not in fails: fails.append(m.group(1))
        if 'SEAL-LINE' in l or 'RAW:' in l or '[?]' in l: fails.append('?')
    return (' PASS ' in head), fails, res

def one(path):
    log = []
    C = set(cands(path)); U = uses(path)
    entries = {e['decl']: set(e['names']) for e in seed.get(path, [])}
    for rnd in range(12):
        ok, fails, res = run(path, entries, f"fx{rnd}")
        log.append(f"## fixpoint round {rnd}: {'PASS' if ok else 'FAIL'} {fails}")
        if ok: break
        if '?' in fails:
            log.append(res); return path, None, log
        for D in fails:
            have = entries.setdefault(D, set())
            add = (set(U.get(D, [])) & C) - have
            if not add: add = C - have
            if not add:
                log.append(f"!! {D} fails with every candidate unsealed"); return path, None, log
            have |= add
            log.append(f"   + {D}: {sorted(add)}")
    else:
        return path, None, log
    # minimisation: drop whole entries that are cascades, then split the names of each remaining
    # entry in halves (binary partition) and drop every part the file passes without
    k = [0]
    def passes(trial):
        ok, fails, _ = run(path, trial, f"min{k[0]}"); k[0] += 1
        return ok, fails
    for D in sorted(entries):
        trial = {x: set(v) for x, v in entries.items() if x != D}
        ok, fails = passes(trial)
        if ok:
            log.append(f"   - {D}: whole entry not needed (cascade) {sorted(entries[D])}"); del entries[D]
    def shrink(D, part):
        trial = {x: set(v) for x, v in entries.items()}
        trial[D] -= set(part)
        ok, fails = passes(trial)
        if ok:
            entries[D] -= set(part); log.append(f"   - {D}: not needed {part}")
        elif len(part) == 1:
            log.append(f"   = {D}: {part[0]} needed [trial min{k[0] - 1}] (without it: {fails})")
        else:
            h = len(part) // 2
            shrink(D, part[:h]); shrink(D, [n for n in part[h:] if n in entries[D]])
    for D in sorted(entries):
        shrink(D, sorted(entries[D]))
    entries = {D: v for D, v in entries.items() if v}
    ok, fails, res = run(path, entries, "final")
    log.append(f"## final: {'PASS' if ok else 'FAIL'} {fails}")
    return path, (entries if ok else None), log

files = [l.strip() for l in open(FILES) if l.strip()]
# restart-safe: each file's entries and log are written as soon as it completes; a file whose
# result is already in <outdir>/done/ is not run again
DONE = OUT / 'done'; DONE.mkdir(exist_ok=True)
todo = [f for f in files if not (DONE / (f.replace('/', '_')[:-5] + '.json')).exists()]
from concurrent.futures import as_completed
with ThreadPoolExecutor(jobs) as ex:
    futs = {ex.submit(one, f): f for f in todo}
    for fu in as_completed(futs):
        path, entries, log = fu.result()
        tag = path.replace('/', '_')[:-5]
        (OUT / f"exclude-{tag}.log").write_text('\n'.join(log) + '\n')
        print(path, 'OK' if entries is not None else 'UNRESOLVED', flush=True)
        if entries is not None:
            (DONE / f"{tag}.json").write_text(json.dumps(
                [{"decl": D, "names": sorted(v)} for D, v in sorted(entries.items())], indent=1))
out = {}
for f in files:
    p = DONE / (f.replace('/', '_')[:-5] + '.json')
    if p.exists():
        v = json.load(open(p))
        if v: out[f] = v
json.dump(out, open(RES, 'w'), indent=1)
print('resolved', sum((DONE / (f.replace('/', '_')[:-5] + '.json')).exists() for f in files), 'of', len(files))

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/evidence-r4/tool-collect.sh.txt =====

#!/usr/bin/env bash
# collect.sh: automatic seal candidates at the final head (candidates/) and at $BASE (candidates-base/).
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
G=$SP/g04r4; WT=$SP/wt-g04r4; T=$G/tools
BASE=$(cat $G/base.txt)
[ -z "$(git -C $WT status --porcelain -- TCSlib)" ] || { echo "worktree not clean"; exit 2; }
rm -rf $G/candidates $G/candidates-base
# two passes: the first collection gives the constant table; the source scan resolves the lemmas
# named in lemma lists (srclemmas/); the second collection adds their statements (`src:` tier)
collect2() {  # <olean-tree> <outdir> [--rev REV]
  bash $T/run_collect.sh $WT $1 $2 > $2.out1 2>&1 || exit 3
  python3 -I $T/scan.py $WT $G/changed-files.txt $2/tcslib-constants.tsv $2 /dev/null /dev/null \
    --srclemmas $2/srclemmas ${3:-} ${4:-} > /dev/null
  bash $T/run_collect.sh $WT $1 $2 > $2.out2 2>&1 || exit 3
}
collect2 $SP/g04r4-oleans $G/candidates
collect2 $SP/s2bfix-r3-oleans $G/candidates-base --rev $BASE
echo "collect.sh done at $(git -C $WT rev-parse HEAD)"

## ===== TCSlib/Cryptography/Asymptotic/MultiMessage.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.PRF
import TCSlib.Cryptography.Asymptotic.Encryption
import TCSlib.Cryptography.Asymptotic.MultiMessageLemmas
import Mathlib.Data.Nat.Choose.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Multi-message secure encryption from a pseudorandom function

The material of [PS10, §3.9]: the many-message encryption scheme
`Gen(1^n): k ← U_n`, `Enc_k(m): r ← U_n, output (r, m ⊕ f_k(r))`, `Dec_k((r, c)) = c ⊕ f_k(r)`
for a pseudorandom function family `{f_k}` [PS10, Algorithm 99.1], and the theorem that it is
multi-message secure [PS10, Theorem 99.2] by the six-hybrid argument: replace `f_k` by a random
function `R` (the PRF property, hybrids `H¹ → H²` and `H⁵ → H⁶`), replace the values `R(r_j)` at
the `q + 1` sampled points by independent uniform pads (identical unless two points collide,
hybrids `H² → H³` and `H⁴ → H⁵`), and use the perfect secrecy of the one-time pad
(`H³ = H⁴`).

Two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`). The *concrete* layer
(one `n`, samplers and adversaries as functions of uniform coins) is new: the hybrid samplers
`prfEncReal`/`otpEnc`, the oracle adversary `multiMsgAdv` with its chain of `q + 1` queries
(Thm-99.2.1), the collision bound (Thm-99.2.2) and the vector one-time pad (Thm-99.2.3),
assembled into the exact bound `distAdv_prfEncReal_le`. The *asymptotic* layer is the scheme
`prfScheme` as a `PrivateKeyScheme` (its three machines built from a polynomial-time evaluator
of the PRF) and [PS10, Theorem 99.2] over `Complexity.NUPPT`. The proof infrastructure (the
coupling bound, the pair count, the block structure of encoded histories and the next-query
machine of Thm-99.2.1) lives in `TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean`
(namespace `TCSlib.Cryptography.MultiMsg`).

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Deviation:** `prfScheme`: the key is the `n`-bit coin string of `Gen`; `Enc` draws its `n`-bit
`r` as its coin string; the evaluator `E` of the PRF is an explicit argument rather than
extracted from `PRF.easy`; ciphertexts are the pair `⟨r, m ⊕ f_k(r)⟩`.

## Main definitions

* `TCSlib.Cryptography.chainTree` — the query tree asking a fixed tuple of queries.
* `TCSlib.Cryptography.prfEncReal`, `TCSlib.Cryptography.otpEnc` — the hybrid samplers
  `(r_j, m_j ⊕ F(r_j))_j` and `(r_j, m_j ⊕ p_j)_j` of [PS10, Theorem 99.2, proof].
* `TCSlib.Cryptography.multiMsgAdv` — the oracle adversary with `q + 1` queries built from a
  distinguisher of ciphertext tuples (Thm-99.2.1).
* `TCSlib.Cryptography.prfEncFun`, `prfDecFun`, `prfScheme` — the scheme of
  [PS10, Algorithm 99.1].

## Main results

* `TCSlib.Cryptography.prfAdv_multiMsgAdv` — `H¹ → H²` is exactly a PRF advantage (Thm-99.2.1).
* `TCSlib.Cryptography.distAdv_prfEncReal_random_otp_le` — `H² → H³` is bounded by the
  collision probability `C(q+1, 2) 2^{−n}` (Thm-99.2.2).
* `TCSlib.Cryptography.acceptProb_otpEnc` — `H³ = H⁴` by the vector one-time pad (Thm-99.2.3).
* `TCSlib.Cryptography.distAdv_prfEncReal_le` — the exact six-hybrid bound of
  [PS10, Theorem 99.2], concrete.
* `TCSlib.Cryptography.prfScheme_multiEncDist` — the ciphertext tuple of Algorithm 99.1 is the
  encoding of `prfEncReal`.
* `TCSlib.Cryptography.prfScheme_multiMessageSecure` — [PS10, Theorem 99.2].
* `TCSlib.Cryptography.exists_multiMessageSecure_of_prf`,
  `exists_multiMessageSecure_of_exists_prg` — multi-message secure encryption exists if a PRF,
  hence if a PRG, exists.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.9: Algorithm 99.1, Theorem 99.2; §3.7: Definition 93.1.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries, `prfAdv`).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Query chains -/

/-- The query tree that asks the fixed tuple of queries `xs : Fin k → I` in order and then
outputs `f` applied to the tuple of answers: `k` `query` nodes in a chain. -/
def chainTree {I O α : Type} : ∀ (k : ℕ), (Fin k → I) → ((Fin k → O) → α) → QueryTree I O α
  | 0, _, f => .ret (f Fin.elim0)
  | k + 1, xs, f => .query (xs 0) fun o => chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)

/-- Running a query chain against the oracle `g` outputs `f` of the tuple of answers
`g (xs j)`. -/
theorem eval_chainTree {I O α : Type} (g : I → O) :
    ∀ (k : ℕ) (xs : Fin k → I) (f : (Fin k → O) → α),
      (chainTree k xs f).eval g = f fun j => g (xs j)
  | 0, xs, f => by
    simp only [chainTree, QueryTree.eval_ret]
    congr
    funext j
    exact j.elim0
  | k + 1, xs, f => by
    simp only [chainTree, QueryTree.eval_query]
    rw [eval_chainTree g k]
    congr
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.tail]

/-- A chain of `k` queries makes at most `k` queries. -/
theorem boundedBy_chainTree {I O α : Type} :
    ∀ (k : ℕ) (xs : Fin k → I) (f : (Fin k → O) → α), (chainTree k xs f).BoundedBy k
  | 0, _, _ => by
    rw [chainTree]
    exact QueryTree.boundedBy_ret _ _
  | k + 1, xs, f => by
    rw [chainTree, QueryTree.boundedBy_query_succ]
    exact fun o => boundedBy_chainTree k (Fin.tail xs) fun os => f (Fin.cons o os)

/-! ### The hybrids of [PS10, Theorem 99.2], concrete -/

section Concrete

variable {n q : ℕ} {K ρ : Type*} [Fintype K] [Fintype ρ]

/-- The ciphertext tuple `(r_j, m_j ⊕ F(r_j))_{j ≤ q}` for a key `z.1 : K` and the points
`z.2 : Fin (q+1) → {0,1}^n`, with `F : K → {0,1}^n → {0,1}^n`. With `F` the PRF this is the
hybrid `H¹` ("real encryptions"); with `F = randomFunction` (keys are function tables) it is
`H²` ("replace `f` with a truly random function `R`") of [PS10, Theorem 99.2, proof]. -/
def prfEncReal (F : K → (Fin n → Bool) → (Fin n → Bool)) (m : Fin (q + 1) → Fin n → Bool) :
    K × (Fin (q + 1) → Fin n → Bool) → (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
  fun z j => (z.2 j, m j + F z.1 (z.2 j))

/-- The ciphertext tuple `(r_j, m_j ⊕ p_j)_{j ≤ q}` with independent uniform pads `p_j`: the
hybrid `H³` ("using OTP") of [PS10, Theorem 99.2, proof]; seeds `(r, p)`. -/
def otpEnc (m : Fin (q + 1) → Fin n → Bool) :
    (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin n → Bool) →
      (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :=
  fun z j => (z.1 j, m j + z.2 j)

/-- **The oracle adversary of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
otherwise (by closure under efficient operations) we contradict the pseudorandomness property"]):
on coins `(r, c)` it queries its oracle at `r₀, …, r_q` (a chain of `q + 1` queries), forms the
tuple `(r_j, m_j ⊕ ans_j)_j` and runs the distinguisher `D` on it with coins `c`. The messages
`m` are hard-wired (non-uniform advice in the machine version). -/
def multiMsgAdv (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    OracleAdversary ((Fin (q + 1) → Fin n → Bool) × ρ) (Fin n → Bool) (Fin n → Bool) :=
  fun c => chainTree (q + 1) c.1 fun ans => D (fun j => (c.1 j, m j + ans j)) c.2

omit [Fintype ρ] in
/-- `multiMsgAdv m D` makes at most `q + 1` queries. -/
theorem multiMsgAdv_boundedBy (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    (multiMsgAdv m D).BoundedBy (q + 1) :=
  fun c => boundedBy_chainTree (q + 1) c.1 _

/-- Running `multiMsgAdv m D` with the oracle `F k` (for a uniform key `k`) accepts with the
probability that `D` accepts the hybrid sampler `prfEncReal F m` (reassociation of the seed
space `K × (points × coins)`). -/
theorem acceptProb_oracleDist_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    acceptProb F (oracleDist (multiMsgAdv m D)) = acceptProb (prfEncReal F m) D := by
  unfold acceptProb
  rw [← uprob_comp_equiv (Equiv.prodAssoc K (Fin (q + 1) → Fin n → Bool) ρ)]
  congr 1
  funext z
  simp only [oracleDist, multiMsgAdv, eval_chainTree, Equiv.prodAssoc_apply]
  rfl

/-- **Thm-99.2.1: the gap `H¹ → H²` is a PRF advantage.** The advantage of `D` between the real
encryptions `(r_j, m_j ⊕ F_k(r_j))_j` and the random-function encryptions
`(r_j, m_j ⊕ R(r_j))_j` is exactly the PRF advantage of the `(q+1)`-query oracle adversary
`multiMsgAdv m D` against `F` (unfolding of `prfAdv`, `oracleDist` and `acceptProb`). -/
theorem prfAdv_multiMsgAdv (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    prfAdv F (multiMsgAdv m D) =
      distAdv (prfEncReal F m) (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D := by
  rw [prfAdv, distAdv, distAdv, acceptProb_oracleDist_multiMsgAdv,
    acceptProb_oracleDist_multiMsgAdv]

/-- **The collision bound** ([PS10, Theorem 99.2, proof, "`∃ i, j` such that `r_i = r_j`, but this
happens only with probability `C(q,2) · 2^{−n}`"]): `q + 1` uniform `n`-bit points fail to be
pairwise distinct with probability at most `C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** `¬ Injective r ↔ ∃ (i, j) with i < j, r i = r j`; the union bound
`uprob_exists_le` over the `C(q+1, 2)` pairs `i < j` (`Finset.card_filter` of `univ.filter (i < j)`
on `Fin (q+1) × Fin (q+1)`, `Fin.card_filter_lt`/`Nat.choose_two_right`-style counting); for
`i ≠ j` the pair `(r i, r j)` is uniform on `({0,1}^n)²` (`HardcoreBit.pushesUniform_eval_pair`),
so `uprob (r i = r j) = uprob (fun (a, b) => a = b) = 2^n / 4^n = 1 / 2^n`
(`PushesUniform.uprob_eq`, `uprob_eq_card_filter`, `Fintype.card_fun`, `Fintype.card_bool`). -/
theorem uprob_not_injective_le :
    uprob (fun r : Fin (q + 1) → Fin n → Bool => ¬ Function.Injective r) ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  classical
  set S : Finset (Fin (q + 1) × Fin (q + 1)) := univ.filter fun p => p.1 < p.2 with hS
  -- a collision is a pair `i < j` with `r i = r j`
  have h1 : uprob (fun r : Fin (q + 1) → Fin n → Bool => ¬ Function.Injective r) ≤
      uprob (fun r : Fin (q + 1) → Fin n → Bool => ∃ p ∈ S, r p.1 = r p.2) := by
    refine uprob_mono fun r hr => ?_
    simp only [Function.Injective, not_forall] at hr
    obtain ⟨i, j, hij, hne⟩ := hr
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨(i, j), by simp [S, h], hij⟩
    · exact ⟨(j, i), by simp [S, h], hij.symm⟩
  -- each pair `i < j` collides with probability `2^{-n}`
  have h3 : ∀ p ∈ S, uprob (fun r : Fin (q + 1) → Fin n → Bool => r p.1 = r p.2) = 1 / 2 ^ n := by
    intro p hp
    have hlt : p.1 < p.2 := by simpa [S] using hp
    have h : uprob (fun r : Fin (q + 1) → Fin n → Bool => r p.1 = r p.2) =
        uprob (fun z : (Fin n → Bool) × (Fin n → Bool) => z.1 = z.2) :=
      (HardcoreBit.pushesUniform_eval_pair (γ := Fin n → Bool) (ne_of_lt hlt)).uprob_eq
        (fun z : (Fin n → Bool) × (Fin n → Bool) => z.1 = z.2)
    rw [h, MultiMsg.uprob_eq_pair, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp
  -- the union bound over the `C(q+1, 2)` pairs
  have h2 := uprob_exists_le S (fun p (r : Fin (q + 1) → Fin n → Bool) => r p.1 = r p.2)
  rw [Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul, hS,
    MultiMsg.card_filter_lt_pairs, mul_one_div] at h2
  exact h1.trans h2

/-- **A uniform table read at distinct points is uniform**: for an injective tuple of points
`r : Fin (q+1) → I`, the map `R ↦ (R (r j))_j` pushes the uniform distribution on tables
`I → O` forward to the uniform distribution on `Fin (q+1) → O` (the generalization of
`HardcoreBit.pushesUniform_eval_pair` from two points to `q + 1` points).

**Proof sketch.** Every fibre of `R ↦ R ∘ r` has the same size `|O|^{|I| − (q+1)}` (the values
off the image of `r` are free, `Equiv.funSplitAt`-style splitting of `I` into the image of `r`
and its complement, `Fintype.card_fun`), so `pushesUniform_of_card_fiber` applies; alternatively
by induction on `q` with `uprob_update_absorb`. -/
theorem pushesUniform_comp_injective {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O]
    {r : Fin (q + 1) → I} (hr : Function.Injective r) :
    HardcoreBit.PushesUniform (fun R : I → O => fun j => R (r j)) := by
  classical
  rcases isEmpty_or_nonempty O with hO | hO
  · -- no tables and no tuples: both averages are over empty types
    intro F
    haveI : IsEmpty (I → O) := ⟨fun R => hO.false (R (r 0))⟩
    haveI : IsEmpty (Fin (q + 1) → O) := ⟨fun f => hO.false (f 0)⟩
    simp only [uexp, univ_eq_empty, sum_empty, zero_div]
  · -- split `I` into the image of `r` and its complement: `R ↦ R ∘ r` is a projection
    let e₁ : Fin (q + 1) ⊕ ((Set.range r)ᶜ : Set I) ≃ I :=
      (Equiv.sumCongr (Equiv.ofInjective r hr) (Equiv.refl _)).trans
        (Equiv.Set.sumCompl (Set.range r))
    let e : (I → O) ≃ (Fin (q + 1) → O) × (((Set.range r)ᶜ : Set I) → O) :=
      (Equiv.arrowCongr e₁.symm (Equiv.refl O)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
    have he : (fun R : I → O => fun j => R (r j)) = fun R => (e R).1 := by
      funext R j
      simp [e, e₁]
    rw [he]
    exact (HardcoreBit.pushesUniform_equiv e).comp HardcoreBit.pushesUniform_fst

/-- **Thm-99.2.2: the gap `H² → H³` is at most the collision probability**
([PS10, Theorem 99.2, proof, "`H²` and `H³` are 'almost' identical except for the case when
`∃ i, j` such that `r_i = r_j`"]): the advantage of `D` between the random-function encryptions
`(r_j, m_j ⊕ R(r_j))_j` and the one-time-pad encryptions `(r_j, m_j ⊕ p_j)_j` is at most
`C(q+1, 2) / 2^n`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Write both acceptance probabilities as averages over the points `r`
(`uprob_prod` after `uprob_prod_comm`): `a(r) := Pr_R[D((r_j, m_j ⊕ R(r_j))_j) = 1]` and
`b(r) := Pr_p[D((r_j, m_j ⊕ p_j)_j) = 1]`. When `r` is injective, `(R(r_j))_j` is uniform
(`pushesUniform_comp_injective`, `PushesUniform.uprob_eq`), so `a(r) = b(r)`; otherwise
`|a(r) − b(r)| ≤ 1` (`uprob_nonneg`, `uprob_le_one`). Hence
`|E_r a − E_r b| ≤ E_r |a − b| ≤ E_r [¬ Injective r] = uprob (¬ Injective)` (`uexp` is monotone
and `|∑| ≤ ∑ |·|`, `uprob_eq_uexp_ite`), and `uprob_not_injective_le` bounds the last term. -/
theorem distAdv_prfEncReal_random_otp_le (m : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    distAdv (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) (otpEnc m) D ≤
      (Nat.choose (q + 1) 2 : ℝ) / 2 ^ n := by
  classical
  -- the acceptance probabilities conditioned on the points `r`
  let a : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
    uprob fun w : ((Fin n → Bool) → (Fin n → Bool)) × ρ =>
      D (fun j => (r j, m j + w.1 (r j))) w.2 = true
  let b : (Fin (q + 1) → Fin n → Bool) → ℝ := fun r =>
    uprob fun w : (Fin (q + 1) → Fin n → Bool) × ρ => D (fun j => (r j, m j + w.1 j)) w.2 = true
  have ha : acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D =
      uexp a :=
    (uprob_comp_equiv ((Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
      ((Fin n → Bool) → (Fin n → Bool)) ρ).symm.trans
        ((Equiv.prodComm _ _).prodCongr (Equiv.refl ρ))) _).symm.trans (by rw [uprob_prod]; rfl)
  have hb : acceptProb (otpEnc m) D = uexp b :=
    (uprob_comp_equiv (Equiv.prodAssoc (Fin (q + 1) → Fin n → Bool)
      (Fin (q + 1) → Fin n → Bool) ρ).symm _).symm.trans (by rw [uprob_prod]; rfl)
  -- at injective points the table values are fresh uniform pads
  have hab : ∀ r : Fin (q + 1) → Fin n → Bool, Function.Injective r → a r = b r := by
    intro r hr
    exact ((pushesUniform_comp_injective (O := Fin n → Bool) hr).prodMap
      (HardcoreBit.pushesUniform_id (Ω := ρ))).uprob_eq
      (fun v : (Fin (q + 1) → Fin n → Bool) × ρ => D (fun j => (r j, m j + v.1 j)) v.2 = true)
  rw [distAdv, ha, hb]
  exact (MultiMsg.abs_uexp_sub_le_uprob a b (fun r => ¬ Function.Injective r)
    (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩) (fun r => ⟨uprob_nonneg _, uprob_le_one _⟩)
    (fun r hr => hab r (not_not.mp hr))).trans uprob_not_injective_le

/-- **Thm-99.2.3: `H³ = H⁴` by the perfect secrecy of the one-time pad** ([PS10, Theorem 99.2,
proof, "`H³` and `H⁴` are identical by the perfect secrecy of the OTP"], the vector version of
Claim-92.a): for independent uniform pads `p_j`, the tuples `(r_j, m_j ⊕ p_j)_j` and
`(r_j, m'_j ⊕ p_j)_j` are identically distributed, so every distinguisher accepts them with the
same probability.

**Proof sketch.** The map `(r, p) ↦ (r, p ⊕ (m ⊕ m'))` is a bijection of the seed space
(`Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))`) carrying the sampler for `m'` to the
sampler for `m` (in the Boolean group `x + x = 0`); relabel by it (`acceptProb_comp_equiv`). -/
theorem acceptProb_otpEnc (m m' : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    acceptProb (otpEnc m) D = acceptProb (otpEnc m') D := by
  have key : ∀ z : (Fin (q + 1) → Fin n → Bool) × (Fin (q + 1) → Fin n → Bool),
      otpEnc m' ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z) = otpEnc m z := by
    intro z
    funext j
    simp only [otpEnc, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_addRight, Prod.map_fst,
      Prod.map_snd, id_eq, Pi.add_apply]
    refine Prod.ext rfl ?_
    funext i
    simp only [Pi.add_apply]
    cases m j i <;> cases m' j i <;> cases z.2 j i <;> rfl
  calc acceptProb (otpEnc m) D
      = acceptProb (fun z => otpEnc m'
          ((Equiv.prodCongr (Equiv.refl _) (Equiv.addRight (m + m'))) z)) D := by
        congr 1
        funext z
        exact (key z).symm
    _ = acceptProb (otpEnc m') D := acceptProb_comp_equiv _ (otpEnc m') D

/-- **[PS10, Theorem 99.2], concrete form: the six-hybrid bound.** For a keyed family
`F : K → {0,1}^n → {0,1}^n`, message vectors `m, m' ∈ ({0,1}^n)^{q+1}` and any distinguisher
`D` of ciphertext tuples, the advantage of `D` between the real encryptions of `m` and of `m'`
is at most `prfAdv F (A_m D) + prfAdv F (A_{m'} D) + 2 · C(q+1, 2) / 2^n`, where `A_m D` is the
`(q+1)`-query oracle adversary `multiMsgAdv m D`.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Hybrids `H¹ = prfEncReal F m`, `H² = prfEncReal R m`, `H³ = otpEnc m`,
`H⁴ = otpEnc m'`, `H⁵ = prfEncReal R m'`, `H⁶ = prfEncReal F m'`: `|H¹ − H²|` and `|H⁵ − H⁶|` are
the two PRF advantages (`prfAdv_multiMsgAdv`), `|H² − H³|` and `|H⁴ − H⁵|` are at most the
collision bound (`distAdv_prfEncReal_random_otp_le`), `H³ = H⁴` (`acceptProb_otpEnc`); the
triangle inequality (`abs_sub_le`, five times) finishes. -/
theorem distAdv_prfEncReal_le (F : K → (Fin n → Bool) → (Fin n → Bool))
    (m m' : Fin (q + 1) → Fin n → Bool)
    (D : (Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) → ρ → Bool) :
    distAdv (prfEncReal F m) (prfEncReal F m') D ≤
      prfAdv F (multiMsgAdv m D) + prfAdv F (multiMsgAdv m' D) +
        2 * ((Nat.choose (q + 1) 2 : ℝ) / 2 ^ n) := by
  have h12 := prfAdv_multiMsgAdv F m D
  have h56 := prfAdv_multiMsgAdv F m' D
  have h23 := distAdv_prfEncReal_random_otp_le m D
  have h45 := distAdv_prfEncReal_random_otp_le m' D
  have h34 := acceptProb_otpEnc m m' D
  simp only [distAdv] at h12 h56 h23 h45 ⊢
  rw [h12, h56, abs_sub_comm (acceptProb (prfEncReal F m') D)]
  rw [abs_sub_comm (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m') D)]
    at h45
  have t1 := abs_sub_le (acceptProb (prfEncReal F m) D)
    (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D)
    (acceptProb (prfEncReal F m') D)
  have t2 := abs_sub_le (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m) D)
    (acceptProb (otpEnc m) D) (acceptProb (prfEncReal F m') D)
  have t3 := abs_sub_le (acceptProb (otpEnc m') D)
    (acceptProb (prfEncReal (randomFunction (Fin n → Bool) (Fin n → Bool)) m') D)
    (acceptProb (prfEncReal F m') D)
  rw [← h34] at t3 h45
  linarith

end Concrete

/-! ### The scheme of [PS10, Algorithm 99.1] -/

/-- The raw string function of `Enc` of [PS10, Algorithm 99.1]: on the machine layout
`⟨⟨⟨1^n, ⟨k, w⟩⟩, α⟩, r⟩` output the pair `⟨r, w ⊕ E(⟨k, r⟩)⟩`, where `E` evaluates the PRF on
`⟨key, input⟩` and the coin string `r` is the fresh point. -/
def prfEncFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode (NUPPT.inCoins z)
    (List.zipWith xor (pairSndD (NUPPT.inArg z))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (NUPPT.inCoins z))))

/-- Whether the ciphertext `⟨r, c⟩` of the layout `⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` has `n`-bit
components: the domain of `Dec` in [PS10, Algorithm 99.1]. -/
def prfDecWF (z : List Bool) : Bool :=
  decide ((pairFstD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length) &&
    decide ((pairSndD (pairSndD (NUPPT.inArg z))).length = (NUPPT.inParam z).length)

/-- The raw string function of `Dec` of [PS10, Algorithm 99.1]: on the layout
`⟨⟨⟨1^n, ⟨k, ⟨r, c⟩⟩⟩, α⟩, r'⟩` with `n`-bit `r` and `c`, output `c ⊕ E(⟨k, r⟩)`; on any other
ciphertext, output `⊥`, here the `(n + 1)`-bit string `1^{n+1}`, which decodes to no message.

The source defines `Dec` on pairs of `n`-bit strings only. The guard matters under
chosen-ciphertext attacks: `E` agrees with `F` only on `⟨s, x⟩` with `|s| = |x|`, so without it a
malformed ciphertext would evaluate `E` where it is unconstrained, and there it may reveal the
key. -/
def prfDecFun (E : List Bool → List Bool) (z : List Bool) : List Bool :=
  if prfDecWF z then
    List.zipWith xor (pairSndD (pairSndD (NUPPT.inArg z)))
      (E (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z)))))
  else true :: NUPPT.inParam z

/-- `prfEncFun E` is polynomial-time when `E` is: projections, one evaluation of `E`, one
bitwise exclusive-or (`Complexity.polyTimeComputable_pairXor`) and one pairing. -/
theorem polyTimeComputable_prfEncFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfEncFun E) := by
  have h := NUPPT.polyTimeComputable_inCoins.pairEncode
    (polyTimeComputable_pairXor.comp
      ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
          NUPPT.polyTimeComputable_inCoins))))
  convert h using 1
  funext z
  simp [prfEncFun, Function.comp]

/-- The well-formedness test of `Dec` is polynomial-time: two length comparisons
(`Complexity.polyTimeComputable_lenEq`). -/
theorem polyTimeComputable_prfDecWF : PolyTimeComputable (fun z => [prfDecWF z]) := by
  have hl : ∀ g : List Bool → List Bool, PolyTimeComputable g →
      PolyTimeComputable (fun z => [decide ((g z).length = (NUPPT.inParam z).length)]) := by
    intro g hg
    convert polyTimeComputable_lenEq.comp (hg.pairEncode NUPPT.polyTimeComputable_inParam)
      using 1
    funext z
    simp [Function.comp]
  exact polyTimeComputable_and
    (hl _ ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))
    (hl _ ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
      NUPPT.polyTimeComputable_inArg))

/-- `prfDecFun E` is polynomial-time when `E` is: the guard, then the branch of the old `Dec`
(`Complexity.polyTimeComputable_ite`). -/
theorem polyTimeComputable_prfDecFun {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (prfDecFun E) := by
  refine polyTimeComputable_ite polyTimeComputable_prfDecWF ?_
    ((polyTimeComputable_const [true]).append NUPPT.polyTimeComputable_inParam)
  have h := polyTimeComputable_pairXor.comp
    (((polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
        NUPPT.polyTimeComputable_inArg).pairEncode
      (hE.comp ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD).comp
          NUPPT.polyTimeComputable_inArg))))
  convert h using 1
  funext z
  simp [prfDecFun, Function.comp]

/-- The activation of the encryption machine on `⟨k, w⟩` with coins `r` is
`⟨r, w ⊕ E(⟨k, r⟩)⟩`. -/
theorem runAt_prfEnc {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k w : List Bool)
    (r : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) coins).runAt n (pairEncode k w) r =
      pairEncode (List.ofFn r) (List.zipWith xor w (E (pairEncode k (List.ofFn r)))) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfEncFun, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]

/-- The activation of the decryption machine on `⟨k, ⟨r, c⟩⟩` with `n`-bit `r` and `c` is
`c ⊕ E(⟨k, r⟩)`. -/
theorem runAt_prfDec {E : List Bool → List Bool} (hE : PolyTimeComputable E) (coins : PolyExpr)
    (n : ℕ) (k r c : List Bool) (hr : r.length = n) (hc : c.length = n)
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k (pairEncode r c)) r' =
      List.zipWith xor c (E (pairEncode k r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  simp [prfDecFun, prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, hr, hc]

/-- On a ciphertext `w` whose two projections `pairFstD w` and `pairSndD w` are not both `n` bits
long, the decryption machine outputs `⊥`: a string that decodes to no `n`-bit message. -/
theorem decodeFin_runAt_prfDec_of_not_wf {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (coins : PolyExpr) (n : ℕ) (k w : List Bool)
    (hw : ¬ ((pairFstD w).length = n ∧ (pairSndD w).length = n))
    (r' : (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).Coins n) :
    decodeFin n ((NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) coins).runAt n
        (pairEncode k w) r') = none := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
  have hf : prfDecWF (pairEncode (pairEncode (NUPPT.advInput n (pairEncode k w)) [])
      (List.ofFn r')) = false := by
    simp only [prfDecWF, NUPPT.inArg, NUPPT.inParam, NUPPT.advInput, pairFstD_pairEncode,
      pairSndD_pairEncode, List.length_replicate, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    tauto
  rw [prfDecFun, hf]
  simp [decodeFin, NUPPT.inParam, NUPPT.advInput]

/-- Masking twice with the same pad (at least as long as the message) is the identity
(private copy of the helper of `Asymptotic/Encryption.lean`). -/
private theorem zipWith_xor_xor_self : ∀ (m p : List Bool), m.length ≤ p.length →
    List.zipWith xor (List.zipWith xor m p) p = m
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: m, b :: p, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by cases a <;> cases b <;> rfl, zipWith_xor_xor_self m p (by simpa using h)⟩

/-- **The many-message encryption scheme of [PS10, Algorithm 99.1]** for a function family
`F` with polynomial-time evaluator `E` on `⟨s, x⟩`: `Gen(1^n)` outputs a uniform `n`-bit key
`k` (its coin string); `Enc_k(m)` draws `r ← U_n` (its coin string) and outputs
`⟨r, m ⊕ f_k(r)⟩`; `Dec_k(⟨r, c⟩) = c ⊕ f_k(r)` (deterministic, coins `const 0`). Correctness is
`(m ⊕ p) ⊕ p = m` with the `n`-bit pad `p = f_k(r)`.

**Deviation:** `prfScheme`: the key is the `n`-bit coin string of `Gen`; `Enc` draws its `n`-bit
`r` as its coin string; the evaluator `E` of the PRF is an explicit argument rather than
extracted from `PRF.easy`; ciphertexts are the pair `⟨r, m ⊕ f_k(r)⟩`. -/
noncomputable def prfScheme (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    PrivateKeyScheme where
  gen := NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var
  enc := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var
  dec := NUPPT.ofPolyTimeUniform (polyTimeComputable_prfDecFun hE) (.const 0)
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  correct := by
    intro n m rg re rd
    rw [runAt_coinKey, runAt_prfEnc hE]
    have h : E (pairEncode (List.ofFn rg) (List.ofFn re)) = List.ofFn (F n rg re) := hFE n rg re
    rw [h, runAt_prfDec hE _ _ _ _ _ (by rw [List.length_ofFn]; rfl) (by simp), h,
      zipWith_xor_xor_self _ _ (by simp), decodeFin_ofFn]

/-- The encoding of a tuple of ciphertext pairs `(r_j, c_j)_j` as the string handed to a
distinguisher: `encodeList` of the pairs `⟨r_j, c_j⟩`. -/
def encodeTuple {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2))

/-- `encodeList l` is the concatenation of the self-delimited chunks `⟨c, []⟩`, `c ∈ l`. -/
private theorem encodeList_eq_flatMap : ∀ l : List (List Bool),
    PrivateKeyScheme.encodeList l = l.flatMap fun c => pairEncode c []
  | [] => rfl
  | c :: l => by
    rw [PrivateKeyScheme.encodeList_cons, List.flatMap_cons, encodeList_eq_flatMap l]
    simp [pairEncode]

/-- The encoded ciphertext tuple is the concatenation of the chunks `⟨⟨r_j, c_j⟩, []⟩` (the
form in which the next-query machine of `MultiMsg.exists_queryChain_nuppt` produces it). -/
theorem encodeTuple_eq_flatten {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :
    encodeTuple v =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) []).flatten := by
  rw [encodeTuple, encodeList_eq_flatMap, MultiMsg.flatMap_ofFn]

/-- **The ciphertext tuple of Algorithm 99.1** is the encoding of the hybrid `H¹`: for the key
`k = r.1` and the points `r.2 j`, `multiEncDist n q m r = encodeTuple (prfEncReal (F n) m r)`. -/
theorem prfScheme_multiEncDist (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x))
    (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool)
    (r : (prfScheme F E hE hFE).gen.Coins n × (Fin (q + 1) → (prfScheme F E hE hFE).enc.Coins n)) :
    (prfScheme F E hE hFE).multiEncDist n q m r = encodeTuple (prfEncReal (F n) m r) := by
  unfold PrivateKeyScheme.multiEncDist encodeTuple
  congr 1
  congr 1
  funext j
  show (NUPPT.ofPolyTimeUniform (polyTimeComputable_prfEncFun hE) .var).runAt n
    (pairEncode ((NUPPT.ofPolyTimeUniform polyTimeComputable_pairSndD .var).runAt n [] r.1)
      (List.ofFn (m j))) (r.2 j) = _
  rw [runAt_coinKey, runAt_prfEnc hE]
  have h : E (pairEncode (List.ofFn r.1) (List.ofFn (r.2 j))) = List.ofFn (F n r.1 (r.2 j)) :=
    hFE n r.1 (r.2 j)
  rw [h, zipWith_xor_ofFn_add]
  rfl

/-- **[PS10, Theorem 99.2]: the scheme of Algorithm 99.1 is multi-message secure** when `F` is
a pseudorandom function family.

**Deviation:** the collision bound is `C(q(n)+1, 2) · 2^{−n}` for the `q(n) + 1` values
`r₀, …, r_{q(n)}` (the text writes `C(q(n), 2) · 2^{−n}`; source error 35 of the plan).

**Proof sketch.** Fix a non-uniform PPT `D` and a budget polynomial `q`. At each `n` choose a
pair of message vectors `(mⁿ, m'ⁿ)` maximizing
`distAdv (multiEncDist n (q n) m) (multiEncDist n (q n) m') (D.distinguisherL n)` over the finite
type of pairs (`Finset.exists_max_image`; the text: "there exists messages `m̄`, `m̄'` … for
infinitely many `n`", hard-wired as advice). *Concrete step:* by `prfScheme_multiEncDist` both
samplers are `encodeTuple ∘ prfEncReal (F n) mⁿ` resp. `m'ⁿ` on the seed space
`K × (Fin (q n + 1) → {0,1}^n)` (the gen coins are the `n`-bit key and the enc coins the points,
definitionally), so with `Dⁿ v c := D.distinguisherL n (encodeTuple v) c` the sunglass identity
`distAdv_comp` and `distAdv_prfEncReal_le` bound the advantage at `n` by
`prfAdv (F n) (multiMsgAdv mⁿ Dⁿ) + prfAdv (F n) (multiMsgAdv m'ⁿ Dⁿ) + 2 · C(q n + 1, 2) / 2^n`
— the six hybrids `H¹, …, H⁶` of the text. *Machine step* (Thm-99.2.1 as an `NUPPT`): for
`v ∈ {m, m'}` the next-query machine `B_v` has advice `⟨encodeList (ofFn (ofFn ∘ vⁿ)), D.advice n⟩`
(`NUPPT.exists_withAdvice`, bound `.add (.mul (.add q (.const 1)) (.add (.mul (.const 2) .var) (.const 2))) D.adv`-style),
coins `(q + 1) · var + D.coins` (`NUPPT.exists_split` with `p := .mul (.add q (.const 1)) .var`: the
first `(q n + 1) n` coins are the points `r₀ … r_{q n}`, read as blocks by
`Complexity.polyTimeComputable_blockMap .var`), and on the encoded history `hist` outputs: if
`|hist| ≤ q n` the query `⟨[false], r_{|hist|}⟩` (history length by `polyTimeComputable_blockMap`
counting, `pairDecode`/`decodeFin` are FP), else the verdict `[true, b]` where `b` is `D`'s
verdict on `encodeTuple (r_j, v_j ⊕ ans_j)_j` (`polyTimeComputable_pairXor` blockwise,
`NUPPT.exists_comp`). By induction on the history, `buildTree` with budget `q n + 1` from `[]`
is the chain `chainTree (q n + 1) r (…)`, i.e.
`B_v.toOracleAdversary n n n (q n + 1) = multiMsgAdv vⁿ Dⁿ` up to the coin bijection
`B_v.Coins n ≃ (Fin (q n + 1) → {0,1}^n) × D.Coins n` (`FunFamily.blocks`, `Fin.appendEquiv`),
so `acceptProb_comp_equiv` gives `prfAdv (F n) (B_v^{(q n + 1)}) = prfAdv (F n) (multiMsgAdv vⁿ Dⁿ)`.
*Asymptotic step:* `hF.negligible_prfAdv B_v (.add q (.const 1))` makes both PRF terms
negligible; the collision term is negligible by `negligible_two_pow_neg` and
`Negligible.mul_pow`/`Negligible.const_mul` with `C(q n + 1, 2) ≤ (q n + 1)^2 ≤ C'(n + 1)^{2d}`
from `PolyExpr.eval_le` (`Nat.choose_le_pow`); `Negligible.add` twice, and by maximality
`ε n := ` this sum bounds the advantage for every `n, m, m'`. -/
theorem prfScheme_multiMessageSecure (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (hF : PRF F) (E : List Bool → List Bool) (hE : PolyTimeComputable E)
    (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)) :
    (prfScheme F E hE hFE).MultiMessageSecure := by
  intro D q
  -- the worst message pair at each parameter (hard-wired into the reductions)
  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
      ∀ w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n) ≤
          distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.1)
            ((prfScheme F E hE hFE).multiEncDist n (q.eval n) p.2) (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun w : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) =>
        distAdv ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.1)
          ((prfScheme F E hE hFE).multiEncDist n (q.eval n) w.2) (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun w => hp w (Finset.mem_univ w)⟩
  choose μ hμ using hmax
  -- the next-query machines of Thm-99.2.1 for the two hard-wired message vectors
  obtain ⟨B₀, hB₀⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).1
  obtain ⟨B₁, hB₁⟩ := MultiMsg.exists_queryChain_nuppt D q fun n => (μ n).2
  refine ⟨fun n => prfAdv (F n) (B₀.toOracleAdversary n n n (q.eval n + 1)) +
      prfAdv (F n) (B₁.toOracleAdversary n n n (q.eval n + 1)) +
      2 * ((Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n), ?_, fun n m m' => ?_⟩
  · -- the asymptotic step: two PRF advantages and the collision term
    exact ((hF.negligible_prfAdv B₀ (.add q (.const 1))).add
      (hF.negligible_prfAdv B₁ (.add q (.const 1)))).add
      ((MultiMsg.negligible_choose_div_two_pow q).const_mul 2)
  · refine (hμ n (m, m')).trans ?_
    -- the concrete step: the ciphertext tuples are `encodeTuple ∘ prfEncReal`
    have key : ∀ m₀ : Fin (q.eval n + 1) → Fin n → Bool,
        (prfScheme F E hE hFE).multiEncDist n (q.eval n) m₀ =
          fun r => encodeTuple (prfEncReal (F n) m₀ r) :=
      fun m₀ => funext fun r => prfScheme_multiEncDist F E hE hFE n (q.eval n) m₀ r
    -- the machine step: the oracle adversaries of `B₀`, `B₁` are the `multiMsgAdv`
    have hadv : ∀ (B : NUPPT) (v : Fin (q.eval n + 1) → Fin n → Bool)
        (φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n),
        (∀ (g : (Fin n → Bool) → (Fin n → Bool)) ρ c,
          (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
            decide (D.runAt n (List.ofFn fun j =>
              pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten c =
                [true])) →
        prfAdv (F n) (B.toOracleAdversary n n n (q.eval n + 1)) =
          prfAdv (F n) (multiMsgAdv v fun w c => D.distinguisherL n (encodeTuple w) c) := by
      intro B v φ hφ
      refine MultiMsg.prfAdv_congr_equiv (F n) _ _ φ fun g w => ?_
      rw [hφ g w.1 w.2, multiMsgAdv, eval_chainTree, NUPPT.distinguisherL, encodeTuple_eq_flatten]
    obtain ⟨φ₀, hφ₀⟩ := hB₀ n
    obtain ⟨φ₁, hφ₁⟩ := hB₁ n
    dsimp only
    rw [hadv B₀ (μ n).1 φ₀ hφ₀, hadv B₁ (μ n).2 φ₁ hφ₁, key, key]
    exact distAdv_prfEncReal_le (F n) (μ n).1 (μ n).2
      (fun w c => D.distinguisherL n (encodeTuple w) c)

/-- **Multi-message secure private-key encryption exists if a PRF exists** ([PS10, §3.9]):
the scheme of Algorithm 99.1 with the evaluator of `PRF.easy`. -/
theorem exists_multiMessageSecure_of_prf {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) : ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨E, hE, hFE⟩ := hF.easy
  ⟨prfScheme F E hE hFE, prfScheme_multiMessageSecure F hF E hE hFE⟩

/-- **Multi-message secure private-key encryption exists if a PRG exists** ([PS10, Theorems
97.3 and 99.2] combined): GGM gives a PRF, Algorithm 99.1 gives the scheme. -/
theorem exists_multiMessageSecure_of_exists_prg (h : ∃ P : PRG, P.Secure) :
    ∃ S : PrivateKeyScheme, S.MultiMessageSecure :=
  let ⟨_, hF⟩ := exists_prf_of_exists_prg h
  exists_multiMessageSecure_of_prf hF

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Asymptotic/MultiMessageLemmas.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.PRF
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the multi-message encryption theorem

The lemmas behind the proofs of `TCSlib/Cryptography/Asymptotic/MultiMessage.lean`
([PS10, Theorem 99.2]), kept in a sibling file so that the statements file stays short:

* **Probability.** The coupling bound `abs_uexp_sub_le_uprob` ("two `[0,1]`-valued
  functions that agree outside an event `E` have averages within `Pr[E]`"), the count of
  pairs `i < j` in `Fin k × Fin k` (`card_filter_lt_pairs`, the `C(k, 2)` of the birthday
  bound), the probability `1 / |α|` that two independent uniform elements coincide
  (`uprob_eq_pair`), and the negligibility of the collision term `C(q(n)+1, 2) · 2^{−n}`
  (`negligible_choose_div_two_pow`).
* **Strings.** The encoded history `encodeHist` is a concatenation of self-delimited
  chunks (`encodeHist_eq_flatMap`);
  the history of a next-query machine with `n`-bit queries and answers consists of blocks of
  the fixed length `6n + 6` (`histBlock`, `length_histBlock`), which the block map of
  `Complexity.polyTimeComputable_blockMap` reads off (`flatMap_range_blocks`); masking a
  history block with the mask block of a message replaces the recorded answer `y` by
  `m ⊕ y` (`zipWith_xor_histBlock_maskBlock`).
* **Machines.** The next-query machine of Thm-99.2.1 (`exists_queryChain_nuppt`): a
  non-uniform PPT whose query tree with budget `q(n) + 1` asks the `q(n) + 1` points read
  from its coins and outputs the verdict of the given distinguisher `D` on the ciphertext
  tuple `(r_j, m_j ⊕ ans_j)_j`, the messages `m` hard-wired as advice. Its raw functions
  `preFun` (the mask) and `postFun` (the move) are built from the FP calculus and the closure
  catalogue of `TCSlib/Complexity/Randomized/Closure.lean`.
* **Oracle adversaries.** Relabelling the coins of an oracle adversary by a bijection
  preserves its PRF advantage (`prfAdv_congr_equiv`).

## Main definitions

* `TCSlib.Cryptography.MultiMsg.histBlock`, `TCSlib.Cryptography.MultiMsg.maskBlock` — the
  block of a history entry and the mask block of a message.
* `TCSlib.Cryptography.MultiMsg.preFun`, `TCSlib.Cryptography.MultiMsg.postFun` — the raw
  string functions of the next-query machine of Thm-99.2.1.

## Main results

* `TCSlib.Cryptography.MultiMsg.abs_uexp_sub_le_uprob` — the coupling bound.
* `TCSlib.Cryptography.MultiMsg.card_filter_lt_pairs` — `#{(i, j) | i < j} = C(k, 2)`.
* `TCSlib.Cryptography.MultiMsg.negligible_choose_div_two_pow` — the collision term is
  negligible.
* `TCSlib.Cryptography.MultiMsg.flatMap_range_blocks` — the block map on a concatenation of
  equal-length chunks.
* `TCSlib.Cryptography.MultiMsg.zipWith_xor_histBlock_maskBlock` — masking a history block.
* `TCSlib.Cryptography.MultiMsg.exists_queryChain_nuppt` — the next-query machine of
  Thm-99.2.1 and its query tree.
* `TCSlib.Cryptography.MultiMsg.prfAdv_congr_equiv` — coin relabelling preserves `prfAdv`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.9: Algorithm 99.1, Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries, `prfAdv`).
-/

namespace TCSlib.Cryptography.MultiMsg

open Complexity Turing Finset

/-! ### Probability: coupling, pair counting, the collision term -/

/-- The absolute value of an average is at most the average of the absolute values. -/
theorem abs_uexp_le_uexp_abs {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    |uexp f| ≤ uexp fun ω => |f ω| := by
  unfold uexp
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- **The coupling bound**: two `[0,1]`-valued functions on a finite sample space that agree
outside the event `E` have averages at most `Pr[E]` apart (the "two experiments that agree
on an event `E` have advantage `≤ Pr[¬E]`" step of [PS10, Theorem 99.2, proof, `H²` vs `H³`]).

**Proof sketch.** `|E a − E b| = |E (a − b)| ≤ E |a − b|` (`abs_uexp_le_uexp_abs`), and
pointwise `|a − b| ≤ [E]` since the difference vanishes off `E` and is at most `1` on it. -/
theorem abs_uexp_sub_le_uprob {Ω : Type*} [Fintype Ω] (a b : Ω → ℝ) (E : Ω → Prop)
    [DecidablePred E] (ha : ∀ ω, 0 ≤ a ω ∧ a ω ≤ 1) (hb : ∀ ω, 0 ≤ b ω ∧ b ω ≤ 1)
    (heq : ∀ ω, ¬ E ω → a ω = b ω) :
    |uexp a - uexp b| ≤ uprob E := by
  rw [← HardcoreBit.uexp_sub, uprob_eq_uexp]
  refine (abs_uexp_le_uexp_abs _).trans (HardcoreBit.uexp_mono fun ω => ?_)
  by_cases hE : E ω
  · rw [if_pos hE]
    obtain ⟨h1, h2⟩ := ha ω
    obtain ⟨h3, h4⟩ := hb ω
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  · rw [if_neg hE, heq ω hE, sub_self, abs_zero]

/-- **Counting the pairs `i < j`**: there are `C(k, 2)` pairs `(i, j)` with `i < j` in
`Fin k × Fin k` (the `C(q(n)+1, 2)` of the birthday bound of [PS10, Theorem 99.2]).

**Proof sketch.** The pairs `i < j` and their swaps partition the off-diagonal of
`Fin k × Fin k`, which has `k² − k` elements (`Finset.offDiag_card`); the swap is injective,
so `2 · #{i < j} = k(k − 1)` and `Nat.choose_two_right` finishes. -/
theorem card_filter_lt_pairs (k : ℕ) :
    ((univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2).card = k.choose 2 := by
  set S := (univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2 with hS
  have hunion : S ∪ S.image Prod.swap = (univ : Finset (Fin k)).offDiag := by
    ext ⟨i, j⟩
    simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_offDiag, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨a, b, hab, rfl, rfl⟩)
      · exact ne_of_lt h
      · exact ne_of_gt hab
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr ⟨j, i, h, rfl, rfl⟩
  have hdisj : Disjoint S (S.image Prod.swap) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hij hji
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists,
      Prod.swap_prod_mk, Prod.mk.injEq] at hji
    obtain ⟨a, b, hab, rfl, rfl⟩ := hji
    exact absurd hij (not_lt.2 hab.le)
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Prod.swap_injective,
    Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hcard
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  omega

/-- Two independent uniform elements of a nonempty finite type coincide with probability
`1 / |α|` (Fubini and `OneWay.uprob_eq_one_div_card`). -/
theorem uprob_eq_pair {α : Type*} [Fintype α] [Nonempty α] :
    uprob (fun z : α × α => z.1 = z.2) = 1 / Fintype.card α := by
  rw [uprob_prod]
  have h : ∀ a : α, uprob (fun b : α => a = b) = 1 / Fintype.card α := by
    intro a
    rw [← OneWay.uprob_eq_one_div_card a]
    exact uprob_congr fun b => eq_comm
  simp_rw [h]
  exact HardcoreBit.uexp_const _

/-- **The collision term is negligible**: `n ↦ C(q(n)+1, 2) / 2^n` is negligible for every
syntactic polynomial `q` ([PS10, Theorem 99.2, proof: the collision probability is
negligible]).

**Proof sketch.** `C(k, 2) ≤ k²` (`Nat.choose_le_pow`) and `q(n) + 1 ≤ (C+1)(n+1)^c ≤
(C+1) 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), so the term is at most a constant times
`n^{2c} · 2^{−n}`, negligible by `negligible_two_pow_neg`, `Negligible.mul_pow` and
`Negligible.const_mul`; conclude with `Negligible.mono`. -/
theorem negligible_choose_div_two_pow (q : PolyExpr) :
    Negligible fun n => (Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n := by
  obtain ⟨C, c, hC⟩ := q.eval_le
  have hν : Negligible fun n =>
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * ((n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n) :=
    (negligible_two_pow_neg.mul_pow (2 * c)).const_mul _
  refine hν.mono ⟨1, fun n hn => ?_⟩
  have hnat : Nat.choose (q.eval n + 1) 2 ≤ ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by
    have h1 : q.eval n + 1 ≤ (C + 1) * (n + 1) ^ c := by
      have := hC n
      have hp : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos n)
      nlinarith
    have h2 : (n + 1) ^ c ≤ (2 * n) ^ c := Nat.pow_le_pow_left (by omega) c
    calc Nat.choose (q.eval n + 1) 2 ≤ (q.eval n + 1) ^ 2 := Nat.choose_le_pow _ _
      _ ≤ ((C + 1) * (2 * n) ^ c) ^ 2 :=
          Nat.pow_le_pow_left (h1.trans (Nat.mul_le_mul_left _ h2)) 2
      _ = ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by ring
  have hR : (Nat.choose (q.eval n + 1) 2 : ℝ) ≤
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) := by
    exact_mod_cast hnat
  have hinv : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_eq_mul_inv, ← inv_pow]
  calc (Nat.choose (q.eval n + 1) 2 : ℝ) * (2 : ℝ)⁻¹ ^ n
      ≤ ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right hR hinv
    _ = _ := by ring

/-! ### Oracle adversaries: coin relabelling -/

/-- Relabelling the coins of an oracle adversary by a bijection preserves its acceptance
probability against every oracle sampler, provided the two trees agree on every oracle. -/
theorem acceptProb_oracleDist_congr_equiv {σ : Type*} {I O : Type} {ρ ρ' : Type*} [Fintype σ] [Fintype ρ]
    [Fintype ρ'] (X : σ → I → O) (A : OracleAdversary ρ I O) (A' : OracleAdversary ρ' I O)
    (φ : ρ' ≃ ρ) (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    acceptProb X (oracleDist A) = acceptProb X (oracleDist A') := by
  simp only [acceptProb_def, oracleDist_apply]
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr φ)]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, h]

/-- **Coin relabelling preserves the PRF advantage**: oracle adversaries whose trees agree on
every oracle after a bijective relabelling of the coins have the same `prfAdv`. -/
theorem prfAdv_congr_equiv {K : Type*} {I O : Type} {ρ ρ' : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    [Fintype O] [Fintype ρ] [Fintype ρ'] (F : K → I → O) (A : OracleAdversary ρ I O)
    (A' : OracleAdversary ρ' I O) (φ : ρ' ≃ ρ)
    (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    prfAdv F A = prfAdv F A' := by
  have hF := acceptProb_oracleDist_congr_equiv F A A' φ h
  have hR := acceptProb_oracleDist_congr_equiv (id : (I → O) → I → O) A A' φ h
  simp only [acceptProb_def, oracleDist_apply, id_eq] at hF hR
  rw [prfAdv_eq, prfAdv_eq, hF, hR]

/-! ### Strings: chunked encodings, history blocks, mask blocks -/

/-- The block contributed to an encoded history by one (query, answer) pair of `n`-bit
strings: the self-delimited chunk `⟨⟨x, y⟩, []⟩`. -/
def histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) : List Bool :=
  pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) []

/-- A history block of `n`-bit strings has length `6n + 6`. -/
theorem length_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    (histBlock p).length = 6 * n + 6 := by
  simp only [histBlock, length_pairEncode, List.length_ofFn, List.length_nil]
  omega

/-- The encoded history is the concatenation of its blocks. -/
theorem encodeHist_eq_flatMap {n : ℕ} : ∀ h : List ((Fin n → Bool) × (Fin n → Bool)),
    encodeHist h = h.flatMap histBlock
  | [] => rfl
  | p :: h => by
    show pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) = _
    rw [encodeHist_eq_flatMap h, List.flatMap_cons]
    simp [histBlock, pairEncode]

/-- The syntactic block length `6n + 6` of a history block. -/
def histBlockLen : PolyExpr := .add (.mul (.const 6) .var) (.const 6)

/-- Evaluating the block length. -/
theorem eval_histBlockLen (n : ℕ) : histBlockLen.eval n = 6 * n + 6 := rfl

/-- The length of a concatenation of chunks of a common length `b`. -/
theorem length_flatMap_of_length {α : Type*} (f : α → List Bool) (b : ℕ) :
    ∀ L : List α, (∀ x ∈ L, (f x).length = b) → (L.flatMap f).length = L.length * b
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatMap_cons, List.length_append,
      length_flatMap_of_length f b L (fun y hy => h y (by simp [hy])), h x (by simp),
      List.length_cons]
    ring

/-- **The block map on a concatenation of equal-length chunks**: reading the string
`f x₀ ++ ⋯ ++ f x_{k−1}` (chunks of length `b > 0`) in blocks of length `b` and applying `g` to
each block gives `g (f x₀) ++ ⋯ ++ g (f x_{k−1})` (the function of
`Complexity.polyTimeComputable_blockMap`).

**Proof sketch.** Induction on the list: the string has `k + 1` blocks
(`length_flatMap_of_length`), `List.range_succ_eq_map` splits off block `0`, which is `f x`
(`List.take_left'`), and block `i + 1` of `f x ++ rest` is block `i` of `rest`
(`List.drop_append`). -/
theorem flatMap_range_blocks {α : Type*} (f : α → List Bool) (g : List Bool → List Bool) {b : ℕ}
    (hb : 0 < b) : ∀ L : List α, (∀ x ∈ L, (f x).length = b) →
      (List.range ((L.flatMap f).length / b)).flatMap
          (fun i => g (((L.flatMap f).drop (i * b)).take b)) =
        L.flatMap fun x => g (f x)
  | [], _ => by simp
  | x :: L, h => by
    have hx : (f x).length = b := h x (by simp)
    have hL : ∀ y ∈ L, (f y).length = b := fun y hy => h y (by simp [hy])
    have hlen : ((x :: L).flatMap f).length = (L.length + 1) * b := by
      rw [length_flatMap_of_length f b _ h, List.length_cons]
    rw [hlen, Nat.mul_div_cancel _ hb, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.flatMap_cons]
    congr 1
    · show g (((f x ++ L.flatMap f).drop (0 * b)).take b) = g (f x)
      rw [Nat.zero_mul, List.drop_zero, List.take_left' hx]
    · show (List.range L.length).flatMap
          (fun i => g (((f x ++ L.flatMap f).drop (i.succ * b)).take b)) = L.flatMap fun y => g (f y)
      rw [← flatMap_range_blocks f g hb L hL, length_flatMap_of_length f b L hL,
        Nat.mul_div_cancel _ hb]
      congr 1
      funext i
      rw [List.drop_append,
        List.drop_of_length_le (by rw [hx]; exact Nat.le_mul_of_pos_left b (Nat.succ_pos i)),
        List.nil_append, show i.succ * b - (f x).length = i * b by
          rw [hx, Nat.succ_mul, Nat.add_sub_cancel]]

/-- A constant block map outputs the unary count of the blocks. -/
theorem flatMap_const_singleton {α : Type*} : ∀ L : List α,
    (L.flatMap fun _ => [true]) = List.replicate L.length true
  | [] => rfl
  | _ :: L => by
    rw [List.flatMap_cons, flatMap_const_singleton L, List.length_cons, List.replicate_succ]
    rfl

/-- A block map outputting `1^n` per block outputs `1^{k·n}` on `k` blocks. -/
theorem flatMap_const_replicate {α : Type*} (n : ℕ) : ∀ L : List α,
    (L.flatMap fun _ => List.replicate n true) = List.replicate (L.length * n) true
  | [] => by simp
  | _ :: L => by
    rw [List.flatMap_cons, flatMap_const_replicate n L, List.length_cons, Nat.succ_mul, add_comm,
      List.replicate_add]

/-- The query component of a history block: `pairFstD (pairFstD (histBlock p))` is the query
`p.1`. -/
theorem pairFstD_pairFstD_histBlock {n : ℕ} (p : (Fin n → Bool) × (Fin n → Bool)) :
    pairFstD (pairFstD (histBlock p)) = List.ofFn p.1 := by
  simp [histBlock]

/-- The mask block of the message `w`: zeros under the (doubled) query and the separators,
`w` doubled under the (doubled) answer, so that `histBlock (x, y) ⊕ maskBlock w` is the
history block of `(x, w ⊕ y)`. -/
def maskBlock {n : ℕ} (w : Fin n → Bool) : List Bool :=
  List.replicate (4 * n + 4) false ++ dbl (List.ofFn w) ++ [false, false]

/-- A mask block has the length `6n + 6` of a history block. -/
theorem length_maskBlock {n : ℕ} (w : Fin n → Bool) : (maskBlock w).length = 6 * n + 6 := by
  simp only [maskBlock, List.length_append, List.length_replicate, length_dbl, List.length_ofFn,
    List.length_cons, List.length_nil]
  omega

/-- Doubling distributes over concatenation. -/
theorem dbl_append (a b : List Bool) : dbl (a ++ b) = dbl a ++ dbl b :=
  List.flatMap_append

/-- Masking with zeros is the identity. -/
theorem zipWith_xor_replicate_false : ∀ l : List Bool,
    List.zipWith xor l (List.replicate l.length false) = l
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, zipWith_xor_replicate_false l,
      Bool.xor_false]

/-- Exclusive-or commutes with doubling. -/
theorem zipWith_xor_dbl : ∀ a b : List Bool,
    List.zipWith xor (dbl a) (dbl b) = dbl (List.zipWith xor a b)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: a, y :: b => by
    simp only [dbl_cons, List.zipWith_cons_cons, zipWith_xor_dbl a b]

/-- **Masking a history block**: the exclusive-or of the history block of `(x, y)` with the
mask block of `w` is the history block of `(x, w ⊕ y)` (strings `x, y, w` of the same length).

**Proof sketch.** `⟨⟨x, y⟩, []⟩ = dbl (dbl x) ++ 0011 ++ dbl y ++ 01`; the mask is
`0^{4n+4} ++ dbl w ++ 00`; `List.zipWith_append` splits the exclusive-or along these
segments, zeros are neutral (`zipWith_xor_replicate_false`) and `dbl y ⊕ dbl w = dbl (y ⊕ w)`
(`zipWith_xor_dbl`). -/
theorem zipWith_xor_histBlock_maskBlock {n : ℕ} (x y w : Fin n → Bool) :
    List.zipWith xor (histBlock (x, y)) (maskBlock w) =
      pairEncode (pairEncode (List.ofFn x) (List.ofFn (w + y))) [] := by
  have hyw : List.zipWith xor (List.ofFn y) (List.ofFn w) = List.ofFn (w + y) := by
    rw [zipWith_xor_ofFn_add, add_comm]
  have h1 : histBlock (x, y) =
      (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]) ++
        (dbl (List.ofFn y) ++ [false, true]) := by
    simp only [histBlock, pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc]
    rfl
  have h2 : maskBlock w =
      List.replicate (dbl (dbl (List.ofFn x)) ++ [false, false, true, true]).length false ++
        (dbl (List.ofFn w) ++ [false, false]) := by
    simp only [maskBlock, List.length_append, length_dbl, List.length_ofFn, List.length_cons,
      List.length_nil, List.append_assoc]
    congr 2
    omega
  rw [h1, h2, List.zipWith_append (List.length_replicate ..).symm, zipWith_xor_replicate_false,
    List.zipWith_append (by simp only [length_dbl, List.length_ofFn]), zipWith_xor_dbl, hyw]
  simp only [pairEncode_eq_dbl, dbl_append, List.append_nil, List.append_assoc]
  rfl

/-- The exclusive-or of two concatenations of `k` chunks of pairwise equal lengths is the
concatenation of the chunkwise exclusive-ors. -/
theorem zipWith_xor_flatten_ofFn : ∀ {k : ℕ} (F G : Fin k → List Bool),
    (∀ j, (F j).length = (G j).length) →
      List.zipWith xor (List.ofFn F).flatten (List.ofFn G).flatten =
        (List.ofFn fun j => List.zipWith xor (F j) (G j)).flatten
  | 0, _, _, _ => rfl
  | k + 1, F, G, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons,
      List.flatten_cons, List.zipWith_append (h 0),
      zipWith_xor_flatten_ofFn (fun j => F j.succ) (fun j => G j.succ) fun j => h j.succ]

/-- A string of `q·s` bits read as `q` chunks of `s` bits: chunk `i` is block `i` of
`FunFamily.blocks` (a public duplicate of `EnsembleLemmas.take_drop_ofFn_blocks` in
`Asymptotic/EnsemblesLemmas.lean`). -/
theorem take_drop_ofFn_blocks {q s : ℕ} (w : Fin (q * s) → Bool) (i : ℕ) (hi : i < q) :
    ((List.ofFn w).drop (i * s)).take s = List.ofFn (FunFamily.blocks q s w ⟨i, hi⟩) := by
  have hle : i * s + s ≤ q * s := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right s hi
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    show w _ = w (finProdFinEquiv (⟨i, hi⟩, _))
    congr 1
    ext
    simp [finProdFinEquiv]
    ring

/-! ### The next-query machine of Thm-99.2.1 -/

/-- The function of `Complexity.polyTimeComputable_blockMap`: on `⟨u, s⟩`, apply `g` to the
consecutive blocks of `s` of length `b(|u|)` and concatenate. -/
def blockMapFun (b : PolyExpr) (g : List Bool → List Bool) (z : List Bool) : List Bool :=
  (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
    g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length))

/-- The block map is polynomial-time (`Complexity.polyTimeComputable_blockMap`). -/
theorem polyTimeComputable_blockMapFun (b : PolyExpr) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) : PolyTimeComputable (blockMapFun b g) :=
  polyTimeComputable_blockMap b hg

/-- The typed head cut `⟨u, s⟩ ↦ s.take (p(|u|))` (`Complexity.polyTimeComputable_pairTakePoly`). -/
def takePolyFun (p : PolyExpr) (z : List Bool) : List Bool :=
  (pairSndD z).take (p.eval (pairFstD z).length)

/-- The typed tail cut `⟨u, s⟩ ↦ s.drop (p(|u|))` (`Complexity.polyTimeComputable_pairDropPoly`). -/
def dropPolyFun (p : PolyExpr) (z : List Bool) : List Bool :=
  (pairSndD z).drop (p.eval (pairFstD z).length)

/-- **The pre-processing of the next-query machine**: on `⟨⟨H, ρ⟩, ⟨M, u⟩⟩` output `H ⊕ M`,
the encoded history masked by the hard-wired mask of the messages (which turns the recorded
answers `ans_j` into `m_j ⊕ ans_j`, `zipWith_xor_histBlock_maskBlock`). -/
def preFun (y : List Bool) : List Bool :=
  List.zipWith xor (pairFstD (pairFstD y)) (pairFstD (pairSndD y))

/-- `preFun` is polynomial-time (`Complexity.polyTimeComputable_pairXor` on two projections). -/
theorem polyTimeComputable_preFun : PolyTimeComputable preFun := by
  have h := polyTimeComputable_pairXor.comp
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
  convert h using 1
  funext y
  simp [preFun, Function.comp]

/-- The history slot of the post-processor's argument `⟨⟨⟨H, ρ⟩, ⟨M, u⟩⟩, a⟩`. -/
def postHist (z : List Bool) : List Bool := pairFstD (pairFstD (pairFstD (NUPPT.inArg z)))

/-- The points slot `ρ` of the post-processor's argument. -/
def postPoints (z : List Bool) : List Bool := pairSndD (pairFstD (pairFstD (NUPPT.inArg z)))

/-- The budget slot `u = 1^{q+1}` of the post-processor's argument. -/
def postBudget (z : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (NUPPT.inArg z)))

/-- The slot `a` of the post-processor's argument holding the distinguisher's output. -/
def postAns (z : List Bool) : List Bool := pairSndD (NUPPT.inArg z)

/-- The unary count `1^k` of the history blocks (block map with the constant `[true]`). -/
def postCount (z : List Bool) : List Bool :=
  blockMapFun histBlockLen (fun _ => [true]) (pairEncode (NUPPT.inParam z) (postHist z))

/-- The unary offset `1^{k·n}` of the next point in the coin string (block map emitting
`1^{|x|}` for the query `x` of each block). -/
def postOffset (z : List Bool) : List Bool :=
  blockMapFun histBlockLen (fun blk => List.replicate (pairFstD (pairFstD blk)).length true)
    (pairEncode (NUPPT.inParam z) (postHist z))

/-- The query move `⟨[false], ρ_k⟩`: the `n`-bit block of the points after the first `k·n`. -/
def postQuery (z : List Bool) : List Bool :=
  pairEncode [false] (takePolyFun .var
    (pairEncode (NUPPT.inParam z) (dropPolyFun .var (pairEncode (postOffset z) (postPoints z)))))

/-- The verdict move `[true, b]` with `b` the distinguisher's acceptance `a = [true]`. -/
def postVerdict (z : List Bool) : List Bool :=
  [true] ++ [decide (pairFstD (pairEncode (postAns z) [true]) = pairSndD (pairEncode (postAns z) [true]))]

/-- **The post-processing of the next-query machine** on the raw layout
`⟨⟨⟨1^n, ⟨⟨⟨H, ρ⟩, ⟨M, u⟩⟩, a⟩⟩, []⟩, r⟩`: if the history already has `|u|` blocks, the
verdict `[true, [a = [true]]]`; otherwise the query `⟨[false], ρ_k⟩` at the `k`-th point,
`k` the number of history blocks. -/
def postFun (z : List Bool) : List Bool :=
  if decide ((postBudget z).length ≤ (postCount z).length) = true then postVerdict z
  else postQuery z

/-- `postFun` is polynomial-time.

**Proof sketch.** Projections of the layout (`NUPPT.polyTimeComputable_inArg`,
`polyTimeComputable_pairFstD`/`pairSndD`), two block maps
(`Complexity.polyTimeComputable_blockMap`), the typed cuts
(`polyTimeComputable_pairTakePoly`/`pairDropPoly`), a length test
(`Complexity.StateLoop.lenLe_comp`), an equality test (`Complexity.polyTimeComputable_pairEq`)
and one branch (`Complexity.polyTimeComputable_ite`). -/
theorem polyTimeComputable_postFun : PolyTimeComputable postFun := by
  have hArg := NUPPT.polyTimeComputable_inArg
  have hParam := NUPPT.polyTimeComputable_inParam
  have hHist : PolyTimeComputable postHist :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hPoints : PolyTimeComputable postPoints :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hBudget : PolyTimeComputable postBudget :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairFstD.comp hArg))
  have hAns : PolyTimeComputable postAns := polyTimeComputable_pairSndD.comp hArg
  have hCount : PolyTimeComputable postCount :=
    (polyTimeComputable_blockMapFun histBlockLen (polyTimeComputable_const [true])).comp
      (hParam.pairEncode hHist)
  have hOffset : PolyTimeComputable postOffset :=
    (polyTimeComputable_blockMapFun histBlockLen
      (polyTimeComputable_unary.comp
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD))).comp
      (hParam.pairEncode hHist)
  have hQuery : PolyTimeComputable postQuery :=
    (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_pairTakePoly .var).comp
      (hParam.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
        (hOffset.pairEncode hPoints))))
  have hVerdict : PolyTimeComputable postVerdict :=
    (polyTimeComputable_prepend [true]).comp
      (polyTimeComputable_pairEq.comp (hAns.pairEncode (polyTimeComputable_const [true])))
  exact polyTimeComputable_ite (StateLoop.lenLe_comp hCount hBudget) hVerdict hQuery

/-- The mask of a message vector: the concatenation of the mask blocks of its entries. -/
def maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) : List Bool :=
  (List.ofFn fun j => maskBlock (v j)).flatten

/-- The length of a concatenation of strings of a common length `b`. -/
theorem length_flatten_of_length (b : ℕ) : ∀ L : List (List Bool),
    (∀ x ∈ L, x.length = b) → L.flatten.length = L.length * b
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatten_cons, List.length_append,
      length_flatten_of_length b L (fun y hy => h y (by simp [hy])), h x (by simp),
      List.length_cons]
    ring

/-- The length of the mask of `k` messages of `n` bits is `k (6n + 6)`. -/
theorem length_maskOf {n k : ℕ} (v : Fin k → Fin n → Bool) :
    (maskOf v).length = k * (6 * n + 6) := by
  unfold maskOf
  rw [length_flatten_of_length (6 * n + 6), List.length_ofFn]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_ofFn.1 hx
  exact length_maskBlock _

/-- The advice bound of the next-query machine: `|⟨mask, 1^{q+1}⟩|`. -/
def adviceBound (q : PolyExpr) : PolyExpr :=
  .add (.add (.mul (.const 2) (.mul (.add q (.const 1)) histBlockLen)) (.const 2)) (.add q (.const 1))

/-- Decoding the well-formed query move `⟨[false], x⟩`. -/
theorem decodeOracleMove_query (ℓ : ℕ) (x : Fin ℓ → Bool) :
    decodeOracleMove ℓ (pairEncode [false] (List.ofFn x)) = .query x := by
  simp [decodeOracleMove, pairDecode_pairEncode, decodeFin_ofFn]

/-- Decoding the verdict move `[true, b]`. -/
theorem decodeOracleMove_ret (ℓ : ℕ) (b : Bool) : decodeOracleMove ℓ [true, b] = .ret b := by
  cases b <;> rfl

/-- **The post-processor on the layout of the composite machine**: for a history of `k` pairs
of `n`-bit strings, the points string `P`, a mask `M`, the budget string `u` and the
distinguisher's output `a`, the move is the verdict `[true, [a = [true]]]` when `|u| ≤ k` and
the query `⟨[false], P[k n, (k+1) n)⟩` otherwise.

**Proof sketch.** The projections of the layout read the slots; the two block maps on
`⟨1^n, encodeHist hist⟩` output `1^k` and `1^{k n}` (`encodeHist_eq_flatMap`,
`flatMap_range_blocks` with blocks of length `6n + 6`, `flatMap_const_singleton`,
`flatMap_const_replicate`); the typed cuts then select the block. -/
theorem postFun_layout {n : ℕ} (hist : List ((Fin n → Bool) × (Fin n → Bool)))
    (P M u a : List Bool) :
    postFun (NUPPT.layout (List.replicate n true)
        (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] []) =
      if u.length ≤ hist.length then [true, decide (a = [true])]
      else pairEncode [false] ((P.drop (hist.length * n)).take n) := by
  set z := NUPPT.layout (List.replicate n true)
    (pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a) [] [] with hz
  have harg : NUPPT.inArg z = pairEncode (pairEncode (pairEncode (encodeHist hist) P) (pairEncode M u)) a :=
    NUPPT.inArg_layout _ _ _ _
  have hpar : NUPPT.inParam z = List.replicate n true := NUPPT.inParam_layout _ _ _ _
  have hblocks : ∀ x ∈ hist, (histBlock x).length = 6 * n + 6 := fun x _ => length_histBlock x
  have hpos : 0 < 6 * n + 6 := by omega
  have hcount : postCount z = List.replicate hist.length true := by
    simp only [postCount, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
      blockMapFun, List.length_replicate, eval_histBlockLen, encodeHist_eq_flatMap]
    exact (flatMap_range_blocks histBlock (fun _ => [true]) hpos hist hblocks).trans
      (flatMap_const_singleton hist)
  have hoffset : postOffset z = List.replicate (hist.length * n) true := by
    simp only [postOffset, postHist, harg, hpar, pairFstD_pairEncode, pairSndD_pairEncode,
      blockMapFun, List.length_replicate, eval_histBlockLen, encodeHist_eq_flatMap]
    refine (flatMap_range_blocks histBlock
      (fun blk => List.replicate (pairFstD (pairFstD blk)).length true) hpos hist hblocks).trans ?_
    show hist.flatMap (fun x => List.replicate (pairFstD (pairFstD (histBlock x))).length true) = _
    simp only [pairFstD_pairFstD_histBlock, List.length_ofFn]
    exact flatMap_const_replicate n hist
  have hbudget : postBudget z = u := by
    simp only [postBudget, harg, pairFstD_pairEncode, pairSndD_pairEncode]
  have hans : postAns z = a := by
    simp only [postAns, harg, pairSndD_pairEncode]
  have hpoints : postPoints z = P := by
    simp only [postPoints, harg, pairFstD_pairEncode, pairSndD_pairEncode]
  simp only [postFun, hbudget, hcount, List.length_replicate]
  by_cases h : u.length ≤ hist.length
  · rw [if_pos (by simpa using h), if_pos h]
    simp only [postVerdict, hans, pairFstD_pairEncode, pairSndD_pairEncode]
    rfl
  · rw [if_neg (by simpa using h), if_neg h]
    simp only [postQuery, takePolyFun, dropPolyFun, hoffset, hpoints, hpar, pairFstD_pairEncode,
      pairSndD_pairEncode, List.length_replicate, PolyExpr.eval_var]

/-- Concatenating the chunks `f (F i)` of a tuple: `flatMap` over `ofFn`. -/
theorem flatMap_ofFn {α : Type*} {k : ℕ} (F : Fin k → α) (f : α → List Bool) :
    (List.ofFn F).flatMap f = (List.ofFn fun i => f (F i)).flatten := by
  rw [List.flatMap_def, List.map_ofFn]
  rfl

/-- **Masking the canonical history**: the pre-processor on the encoded history
`((ρ_j, g ρ_j))_j` with the mask of `v` outputs the encoded ciphertext tuple
`(ρ_j, v_j ⊕ g(ρ_j))_j` (`zipWith_xor_flatten_ofFn`, `zipWith_xor_histBlock_maskBlock`). -/
theorem preFun_encodeHist {n k : ℕ} (ρ v : Fin k → Fin n → Bool)
    (g : (Fin n → Bool) → (Fin n → Bool)) (P u : List Bool) :
    preFun (pairEncode (pairEncode (encodeHist (List.ofFn fun i => (ρ i, g (ρ i)))) P)
        (pairEncode (maskOf v) u)) =
      (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v j + g (ρ j)))) []).flatten := by
  simp only [preFun, pairFstD_pairEncode, pairSndD_pairEncode, encodeHist_eq_flatMap, maskOf,
    flatMap_ofFn]
  rw [zipWith_xor_flatten_ofFn _ _ fun j => by rw [length_histBlock, length_maskBlock]]
  exact congrArg List.flatten (congrArg List.ofFn (funext fun j =>
    zipWith_xor_histBlock_maskBlock (ρ j) (g (ρ j)) (v j)))

/-- **The next-query machine of Thm-99.2.1** ([PS10, Theorem 99.2, proof, "`H¹` and `H²` …
by closure under efficient operations we contradict the pseudorandomness property"]): for a
non-uniform PPT `D` (a distinguisher of encoded ciphertext tuples), a budget polynomial `q` and
message vectors `v n ∈ ({0,1}^n)^{q(n)+1}`, there is a non-uniform PPT `B` whose coins at `n`
are, up to a bijection `φ`, the `q(n) + 1` points `ρ` and the coins `c` of `D`, and whose
query tree with budget `q(n) + 1`, evaluated against any oracle `g`, gives `D`'s verdict on the
encoded tuple `(ρ_j, v_j ⊕ g(ρ_j))_j` with coins `c` (an equality of outputs; the sequence of
queries is not part of the statement).

**Proof sketch.** `B` is `exists_split` (the first `(q(n)+1) n` coins are the points) of
`exists_withAdvice` (advice `⟨maskOf (v n), 1^{q(n)+1}⟩`) of `exists_seq` of `D ∘ preFun`
(`exists_comp`) and the uniform machine of `postFun`. On the encoded history `H` of `k`
blocks the post-processor asks `ρ_k` while `k ≤ q(n)` and otherwise outputs `[true, b]` with
`b` the verdict of `D` on `H ⊕ maskOf (v n)` (`postFun_layout`, `take_drop_ofFn_blocks`,
`preFun_encodeHist`). The tree `buildTree` from the empty history is evaluated by induction on
the remaining budget `j` along the canonical history `((ρ_i, g ρ_i))_{i < q(n)+1-j}`. -/
theorem exists_queryChain_nuppt (D : NUPPT) (q : PolyExpr)
    (v : ∀ n, Fin (q.eval n + 1) → Fin n → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin n → Bool)) (ρ : Fin (q.eval n + 1) → Fin n → Bool)
        (c : D.Coins n),
        (B.toOracleAdversary n n n (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true]) := by
  classical
  have hβ : ∀ n, (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)).length ≤
      (adviceBound q).eval n := by
    intro n
    simp only [length_pairEncode, length_maskOf, List.length_replicate, adviceBound,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, eval_histBlockLen, le_refl]
  obtain ⟨D₁, hD₁c, -, -, hD₁⟩ := D.exists_comp polyTimeComputable_preFun polyTimeComputable_id
  obtain ⟨C, hCc, -, hC⟩ :=
    D₁.exists_seq (NUPPT.ofPolyTimeUniform polyTimeComputable_postFun (.const 0))
  obtain ⟨C₂, hC₂c, hC₂⟩ := C.exists_withAdvice
    (fun n => pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)) (adviceBound q) hβ
  obtain ⟨B, hBc, -, hB⟩ := C₂.exists_split (.mul (.add q (.const 1)) .var)
  refine ⟨B, fun n => ?_⟩
  have hlen : B.coinLen n = (q.eval n + 1) * n + D.coinLen n := by
    simp only [NUPPT.coinLen, hBc, hC₂c, hCc, hD₁c, NUPPT.coins_ofPolyTimeUniform,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, Nat.add_zero]
  let φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n :=
    ((FunFamily.blocks (q.eval n + 1) n).symm.prodCongr (Equiv.refl (D.Coins n))).trans
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool)))
  refine ⟨φ, fun g ρ c => ?_⟩
  set Pstr : List Bool := List.ofFn ((FunFamily.blocks (q.eval n + 1) n).symm ρ) with hPstr
  have hφ : φ (ρ, c) =
      fun i => Fin.append ((FunFamily.blocks (q.eval n + 1) n).symm ρ) c (Fin.cast hlen i) := by
    funext i
    rfl
  have hcoins : List.ofFn (φ (ρ, c)) = Pstr ++ List.ofFn c := by
    rw [hφ, hPstr, ← List.ofFn_fin_append]
    exact (List.ofFn_congr hlen.symm _).symm
  -- the activation of `B` on an encoded history
  have hD₁len : D₁.coinLen n = D.coinLen n := by simp only [NUPPT.coinLen, hD₁c]
  have hrun : ∀ hist : List ((Fin n → Bool) × (Fin n → Bool)),
      B.runAt n (encodeHist hist) (φ (ρ, c)) =
        postFun (NUPPT.layout (List.replicate n true)
          (pairEncode (pairEncode (pairEncode (encodeHist hist) Pstr)
              (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)))
            (D.runAt n (preFun (pairEncode (pairEncode (encodeHist hist) Pstr)
              (pairEncode (maskOf (v n)) (List.replicate (q.eval n + 1) true)))) c)) [] []) := by
    intro hist
    have hp : (PolyExpr.mul (.add q (.const 1)) .var).eval n = (q.eval n + 1) * n := rfl
    have hPlen : Pstr.length = (q.eval n + 1) * n := by simp [hPstr]
    have hclen : (List.ofFn c).length = D.coinLen n := by simp
    rw [NUPPT.runAt_eq, hcoins, hB, hp, List.take_left' hPlen, List.drop_left' hPlen]
    have hC₂' := hC₂ n (pairEncode (encodeHist hist) Pstr) (List.ofFn c)
    simp only at hC₂'
    rw [hC₂', hC, hD₁len, List.take_of_length_le hclen.le, List.drop_of_length_le hclen.le, hD₁,
      NUPPT.runAtL_ofPolyTimeUniform]
    rfl
  -- the canonical history along the points `ρ` against the oracle `g`
  let ρ' : ℕ → Fin n → Bool := fun i => if h : i < q.eval n + 1 then ρ ⟨i, h⟩ else fun _ => false
  let hist : ℕ → List ((Fin n → Bool) × (Fin n → Bool)) :=
    fun k => List.ofFn fun i : Fin k => (ρ' i, g (ρ' i))
  have hρ' : ∀ (i : ℕ) (hi : i < q.eval n + 1), ρ' i = ρ ⟨i, hi⟩ := fun i hi => dif_pos hi
  have hist_len : ∀ k, (hist k).length = k := fun k => List.length_ofFn
  have hist_succ : ∀ k, hist (k + 1) = hist k ++ [(ρ' k, g (ρ' k))] := by
    intro k
    simp only [hist]
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [Fin.coe_castSucc, Fin.val_last]
  have hist_top : hist (q.eval n + 1) = List.ofFn fun i : Fin (q.eval n + 1) => (ρ i, g (ρ i)) := by
    simp only [hist]
    congr 1
    funext i
    rw [hρ' i i.isLt]
  -- the next-query function of `B`
  set next : List ((Fin n → Bool) × (Fin n → Bool)) → OracleMove n :=
    fun h => decodeOracleMove n (B.runAt n (encodeHist h) (φ (ρ, c))) with hnext
  have hquery : ∀ k (hk : k < q.eval n + 1), next (hist k) = .query (ρ ⟨k, hk⟩) := by
    intro k hk
    simp only [hnext]
    rw [hrun, postFun_layout, hist_len, if_neg (by simp; omega), hPstr,
      take_drop_ofFn_blocks _ k hk, Equiv.apply_symm_apply, decodeOracleMove_query]
  have hret : next (hist (q.eval n + 1)) =
      .ret (decide (D.runAt n (List.ofFn fun j =>
        pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
          [true])) := by
    simp only [hnext]
    rw [hrun, postFun_layout, hist_len, if_pos (by simp), hist_top, preFun_encodeHist,
      decodeOracleMove_ret]
  -- evaluation of the tree by induction on the remaining budget
  have main : ∀ j, j ≤ q.eval n + 1 →
      (buildTree next j (hist (q.eval n + 1 - j))).eval g =
        decide (D.runAt n (List.ofFn fun j =>
          pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
            [true]) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.sub_zero, buildTree, hret]
      rfl
    | succ j ih =>
      intro hj
      have hk : q.eval n + 1 - (j + 1) < q.eval n + 1 := by omega
      rw [buildTree, hquery _ hk, QueryTree.eval_query, ← hρ' _ hk, ← hist_succ,
        show q.eval n + 1 - (j + 1) + 1 = q.eval n + 1 - j by omega]
      exact ih (by omega)
  have h0 : hist 0 = [] := rfl
  have := main (q.eval n + 1) le_rfl
  rw [Nat.sub_self, h0] at this
  exact this

end TCSlib.Cryptography.MultiMsg

## ===== TCSlib/Cryptography/Games/OracleComp.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Notation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle computations

The syntax of security games and protocols. An *oracle specification* names a family of oracles,
each with a type of queries and a type of answers. An *oracle computation* over it asks one
oracle a query, looks at the answer, chooses what to do next, and eventually returns a value. It
is the free monad over the specification: a well-founded tree (every run makes finitely many
queries) whose inner nodes are queries, with one subtree per possible answer. With finite answer
types, as for probabilistic computations, the tree is finite.

Everything else in the framework is built on this file:
- uniform sampling is one more oracle (`TCSlib.Cryptography.Games.Probability`);
- running a computation against implementations of its oracles is `simulate`
  (`TCSlib.Cryptography.Games.Simulate`);
- a two-party protocol is a pair of computations whose oracle is the message exchange
  (`TCSlib.Cryptography.Games.Protocols`).

With one oracle, an oracle computation is a `TCSlib.Cryptography.QueryTree` of the concrete
layer ([Gar26]); the bridge between the two is in the S2b layer.

## Main definitions

* `Games.OracleSpec ι`: a family of oracles named by `ι`.
* `Games.OracleComp spec α`: computations with access to the oracles of `spec`, returning an `α`;
  a `Monad` and a `LawfulMonad`.
* `Games.OracleComp.call i x`: ask oracle `i` the query `x` and return the answer.
* `Games.singleSpec I O`: one oracle (index `Unit`); its computations are the concrete layer's
  query trees.
* `Games.OracleSpec.add`: the disjoint union of two oracle families;
  `OracleComp.liftLeft`/`liftRight` run a computation over one part in the union.
* `Games.OracleComp.AllOutputs P c`: every possible output of `c` satisfies `P`.
* `Games.OracleComp.CostBoundedBy cost c q`: every run of `c` spends at most `q`, oracle `i`
  costing `cost i` per query (for example, 1 for the oracle under attack and 0 for coin draws).

## Main results

* `Games.OracleComp.instLawfulMonad`: the monad laws.
* `Games.OracleComp.CostBoundedBy.bind`: costs add under sequencing.
* `Games.OracleComp.costBoundedBy_liftLeft`, `costBoundedBy_liftRight`: lifting into a union of
  specifications keeps the cost.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (oracle adversaries).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games

/-- A **family of oracles** named by `ι`: oracle `i` accepts queries in `dom i` and answers in
`rng i`. [VCVio, OracleComp/OracleSpec] -/
structure OracleSpec (ι : Type) where
  /-- The queries oracle `i` accepts. -/
  dom : ι → Type
  /-- The answers oracle `i` gives. -/
  rng : ι → Type

/-- **Oracle computations** over `spec` returning an `α`: either return a value, or ask oracle
`i` the query `x` and continue with `k` applied to the answer. This is the free monad over
`spec`; an oracle adversary of [Gar26, Definition 3.9] or [PS10, §3.8.1] with fixed coins is the
one-oracle case. [VCVio, OracleComp/OracleComp] -/
inductive OracleComp {ι : Type} (spec : OracleSpec ι) (α : Type) : Type where
  /-- Return `a` without further queries. -/
  | pure : α → OracleComp spec α
  /-- Ask oracle `i` the query `x`, and continue with `k` on the answer. -/
  | query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α) : OracleComp spec α

namespace OracleComp

variable {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {α β γ : Type}

/-- Sequencing: run `c`, then `f` on its result. Queries of `c` come first. -/
def bind : OracleComp spec α → (α → OracleComp spec β) → OracleComp spec β
  | .pure a, f => f a
  | .query i x k, f => .query i x (fun y => bind (k y) f)

instance : Monad (OracleComp spec) where
  pure := .pure
  bind := bind

/-- `>>=` is `OracleComp.bind`. -/
theorem bind_eq_bind (c : OracleComp spec α) (f : α → OracleComp spec β) :
    (c >>= f) = c.bind f := rfl

/-- `pure` is the constructor `OracleComp.pure`. -/
theorem pure_eq_pure (a : α) : (Pure.pure a : OracleComp spec α) = .pure a := rfl

/-- `<$>` is sequencing with a return. -/
theorem map_eq_bind (h : α → β) (c : OracleComp spec α) :
    (h <$> c) = c.bind (fun a => .pure (h a)) := rfl

/-- Returning first, then continuing, is continuing. -/
@[simp] theorem pure_bind (a : α) (f : α → OracleComp spec β) : (OracleComp.pure a).bind f = f a :=
  rfl

/-- A query followed by `f` is the query whose continuation is followed by `f`. -/
@[simp] theorem query_bind (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (f : α → OracleComp spec β) :
    (OracleComp.query i x k).bind f = .query i x (fun y => (k y).bind f) := rfl

/-- Continuing with a return changes nothing. -/
@[simp] theorem bind_pure (c : OracleComp spec α) : c.bind .pure = c := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, ih]

/-- Sequencing is associative. -/
theorem bind_assoc (c : OracleComp spec α) (f : α → OracleComp spec β)
    (g : β → OracleComp spec γ) : (c.bind f).bind g = c.bind (fun a => (f a).bind g) := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, ih]

/-- The monad laws. -/
instance instLawfulMonad : LawfulMonad (OracleComp spec) :=
  LawfulMonad.mk' _
    (id_map := fun c => bind_pure c)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun c f g => bind_assoc c f g)

/-- Ask oracle `i` the query `x` and return the answer. -/
def call (i : ι) (x : spec.dom i) : OracleComp spec (spec.rng i) :=
  .query i x .pure

/-- Asking and then continuing with `f` is the query with continuation `f`. -/
@[simp] theorem call_bind (i : ι) (x : spec.dom i) (f : spec.rng i → OracleComp spec α) :
    (call i x).bind f = .query i x f := rfl

/-! ### Unions of oracle families -/

end OracleComp

/-- A single oracle with queries in `I` and answers in `O` (index type `Unit`). The concrete
layer's query trees are the computations over it (`TCSlib.Cryptography.QueryTree`). -/
abbrev singleSpec (I O : Type) : OracleSpec Unit := ⟨fun _ => I, fun _ => O⟩

/-- The single oracle of `singleSpec I O` takes queries in `I`. -/
theorem singleSpec_dom (I O : Type) (u : Unit) : (singleSpec I O).dom u = I := rfl

/-- The single oracle of `singleSpec I O` answers in `O`. -/
theorem singleSpec_rng (I O : Type) (u : Unit) : (singleSpec I O).rng u = O := rfl

/-- The **disjoint union** of two oracle families: oracle `.inl i` is oracle `i` of `s₁`, and
oracle `.inr j` is oracle `j` of `s₂`. [VCVio, OracleComp/OracleSpec] -/
abbrev OracleSpec.add {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) :
    OracleSpec (ι₁ ⊕ ι₂) :=
  ⟨Sum.elim s₁.dom s₂.dom, Sum.elim s₁.rng s₂.rng⟩

/-- The left oracles of the union have the queries of `s₁`: `(s₁.add s₂).dom (.inl i) = s₁.dom i`. -/
theorem OracleSpec.add_dom_inl {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (i : ι₁) :
    (s₁.add s₂).dom (.inl i) = s₁.dom i := rfl

/-- The right oracles of the union have the queries of `s₂`: `(s₁.add s₂).dom (.inr j) = s₂.dom j`. -/
theorem OracleSpec.add_dom_inr {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (j : ι₂) :
    (s₁.add s₂).dom (.inr j) = s₂.dom j := rfl

/-- The left oracles of the union have the answers of `s₁`: `(s₁.add s₂).rng (.inl i) = s₁.rng i`. -/
theorem OracleSpec.add_rng_inl {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (i : ι₁) :
    (s₁.add s₂).rng (.inl i) = s₁.rng i := rfl

/-- The right oracles of the union have the answers of `s₂`: `(s₁.add s₂).rng (.inr j) = s₂.rng j`. -/
theorem OracleSpec.add_rng_inr {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) (j : ι₂) :
    (s₁.add s₂).rng (.inr j) = s₂.rng j := rfl

namespace OracleComp

variable {ι ι₁ ι₂ : Type} {α β : Type}

/-- Run a computation over `s₁` inside the union `s₁.add s₂`, asking only oracles of `s₁`. -/
def liftLeft {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} :
    OracleComp s₁ α → OracleComp (s₁.add s₂) α
  | .pure a => .pure a
  | .query i x k => .query (.inl i) x (fun y => liftLeft (k y))

/-- Run a computation over `s₂` inside the union `s₁.add s₂`, asking only oracles of `s₂`. -/
def liftRight {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} :
    OracleComp s₂ α → OracleComp (s₁.add s₂) α
  | .pure a => .pure a
  | .query j x k => .query (.inr j) x (fun y => liftRight (k y))

/-- Lifting commutes with sequencing. -/
theorem liftLeft_bind {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} (c : OracleComp s₁ α)
    (f : α → OracleComp s₁ β) :
    (liftLeft (s₂ := s₂) (c.bind f)) = (liftLeft c).bind (fun a => liftLeft (f a)) := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, liftLeft, ih]

/-- Lifting commutes with sequencing. -/
theorem liftRight_bind {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} (c : OracleComp s₂ α)
    (f : α → OracleComp s₂ β) :
    (liftRight (s₁ := s₁) (c.bind f)) = (liftRight c).bind (fun a => liftRight (f a)) := by
  induction c with
  | pure a => rfl
  | query j x k ih => simp only [query_bind, liftRight, ih]

/-! ### Query costs -/

variable {spec : OracleSpec ι₁}

/-- `c` is **cost-bounded by `q`**: along every run, the total cost of its queries, oracle `i`
costing `cost i` per query, is at most `q`. With `cost` equal to 1 on the oracle under attack and
0 elsewhere, this is "at most `q` queries to that oracle", the query bound of
[Gar26, Definition 3.9]. -/
def CostBoundedBy (cost : ι₁ → ℕ) : OracleComp spec α → ℕ → Prop
  | .pure _, _ => True
  | .query i _ k, q => cost i ≤ q ∧ ∀ y, CostBoundedBy cost (k y) (q - cost i)

/-- A return costs nothing. -/
@[simp] theorem costBoundedBy_pure (cost : ι₁ → ℕ) (a : α) (q : ℕ) :
    CostBoundedBy cost (OracleComp.pure (spec := spec) a) q :=
  trivial

/-- A query is within budget `q` exactly when its cost fits and every continuation fits in what
is left. -/
@[simp] theorem costBoundedBy_query (cost : ι₁ → ℕ) (i : ι₁) (x : spec.dom i)
    (k : spec.rng i → OracleComp spec α) (q : ℕ) :
    CostBoundedBy cost (OracleComp.query i x k) q ↔
      cost i ≤ q ∧ ∀ y, CostBoundedBy cost (k y) (q - cost i) :=
  Iff.rfl

/-- A larger budget is still a bound. -/
theorem CostBoundedBy.mono {cost : ι₁ → ℕ} {c : OracleComp spec α} {q q' : ℕ}
    (h : CostBoundedBy cost c q) (hq : q ≤ q') : CostBoundedBy cost c q' := by
  induction c generalizing q q' with
  | pure a => trivial
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := h
    exact ⟨Nat.le_trans hi hq, fun y => ih y (hk y) (Nat.sub_le_sub_right hq _)⟩

/-- **Costs add under sequencing:** if `c` fits in `q₁` and every continuation `f a` fits in
`q₂`, then `c` followed by `f` fits in `q₁ + q₂`.

**Proof sketch.** Induction on `c`. At a query of cost `cost i ≤ q₁`, the continuation fits in
`q₁ - cost i` by hypothesis, so by induction it fits in `(q₁ - cost i) + q₂`, which is
`(q₁ + q₂) - cost i`. -/
theorem CostBoundedBy.bind {cost : ι₁ → ℕ} {c : OracleComp spec α} {f : α → OracleComp spec β}
    {q₁ q₂ : ℕ} (hc : CostBoundedBy cost c q₁) (hf : ∀ a, CostBoundedBy cost (f a) q₂) :
    CostBoundedBy cost (c.bind f) (q₁ + q₂) := by
  induction c generalizing q₁ with
  | pure a => exact (hf a).mono (Nat.le_add_left _ _)
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := hc
    refine ⟨Nat.le_trans hi (Nat.le_add_right _ _), fun y => ?_⟩
    rw [Nat.sub_add_comm hi]
    exact ih y (hk y)

/-- Lifting into a union keeps the cost, when the union's cost agrees with the original on the
left part. -/
theorem costBoundedBy_liftLeft {s₂ : OracleSpec ι₂} {cost : ι₁ ⊕ ι₂ → ℕ} {c : OracleComp spec α}
    {q : ℕ} (h : CostBoundedBy (fun i => cost (.inl i)) c q) :
    CostBoundedBy cost (liftLeft (s₂ := s₂) c) q := by
  induction c generalizing q with
  | pure a => trivial
  | query i x k ih => exact ⟨h.1, fun y => ih y (h.2 y)⟩

/-- Lifting into a union keeps the cost, when the union's cost agrees with the original on the
right part. -/
theorem costBoundedBy_liftRight {s₁ : OracleSpec ι₂} {cost : ι₂ ⊕ ι₁ → ℕ}
    {c : OracleComp spec α} {q : ℕ} (h : CostBoundedBy (fun j => cost (.inr j)) c q) :
    CostBoundedBy cost (liftRight (s₁ := s₁) c) q := by
  induction c generalizing q with
  | pure a => trivial
  | query j x k ih => exact ⟨h.1, fun y => ih y (h.2 y)⟩

/-! ### Possible outputs -/

/-- **Every possible output** of `c` satisfies `P`: a return satisfies it, and every
continuation of a query does, whatever the answer. -/
def AllOutputs {spec : OracleSpec ι} (P : α → Prop) : OracleComp spec α → Prop
  | .pure a => P a
  | .query _ _ k => ∀ y, AllOutputs P (k y)

/-- The only possible output of a return is its value: `(pure a).AllOutputs P ↔ P a`. -/
theorem allOutputs_pure {spec : OracleSpec ι} {P : α → Prop} {a : α} :
    (OracleComp.pure (spec := spec) a).AllOutputs P ↔ P a :=
  Iff.rfl

/-- The possible outputs of a query are those of its continuations, whatever the answer:
`(query i x k).AllOutputs P ↔ ∀ y, (k y).AllOutputs P`. -/
theorem allOutputs_query {spec : OracleSpec ι} {P : α → Prop} {i : ι} {x : spec.dom i}
    {k : spec.rng i → OracleComp spec α} :
    (OracleComp.query i x k).AllOutputs P ↔ ∀ y, (k y).AllOutputs P :=
  Iff.rfl

/-- Every computation satisfies the trivial predicate at every possible output. -/
theorem allOutputs_true {spec : OracleSpec ι} (c : OracleComp spec α) :
    c.AllOutputs fun _ => True := by
  induction c with
  | pure a => trivial
  | query i x k ih => exact fun y => ih y

/-- `AllOutputs` is monotone in the predicate. -/
theorem AllOutputs.mono {spec : OracleSpec ι} {P Q : α → Prop} (hPQ : ∀ a, P a → Q a)
    {c : OracleComp spec α} (h : c.AllOutputs P) : c.AllOutputs Q := by
  induction c with
  | pure a => exact hPQ a h
  | query i x k ih => exact fun y => ih y (h y)

/-- Every possible output of `c` followed by `f` satisfies `Q` when every possible output `a`
of `c` satisfies `P` and every possible output of `f a` with `P a` satisfies `Q`. -/
theorem AllOutputs.bind {spec : OracleSpec ι} {P : α → Prop} {Q : β → Prop}
    {c : OracleComp spec α} {f : α → OracleComp spec β} (hc : c.AllOutputs P)
    (hf : ∀ a, P a → (f a).AllOutputs Q) : (c.bind f).AllOutputs Q := by
  induction c with
  | pure a => exact hf a hc
  | query i x k ih => exact fun y => ih y (hc y)

end OracleComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Probability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.InformationTheory.FinDist

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic computations

Randomness enters the framework as one more oracle: oracle `m` of `unifSpec` answers a uniformly
random element of `Fin (m + 1)`, and a uniform element of any nonempty finite type is obtained
through an enumeration. A *probabilistic computation* (`ProbComp`) is an oracle computation whose
only oracle is this one. Security games, once their adversary is plugged in and their oracles
implemented, are probabilistic computations.

The semantics is elementary and real-valued. The expectation of `g` over the output of a
computation is defined by recursion on the computation: a return contributes `g a`, and a sampling
step averages over its `m + 1` equally likely answers. There are no measures and no extended
reals: every computation is a finite tree with finite branching, so every probability is a finite
sum of rationals. The probability of an event is the expectation of its indicator. For a
computation with a finite output type, its output distribution is a `FinDist` of the library's
information-theory layer, so statistical distance and closeness (`EpsClose`) apply directly.

## Main definitions

* `Games.unifSpec`: the uniform-sampling oracles; `Games.ProbComp`: computations over them.
* `Games.ProbComp.sampleFin m`, `Games.ProbComp.sample T`: a uniform element of `Fin (m + 1)`, and
  of a nonempty finite type `T`.
* `Games.ProbComp.expect c g`: the expectation of `g` over the output of `c`.
* `Games.ProbComp.prob c p`: the probability that the output of `c` satisfies `p`.
* `Games.ProbComp.dist c`: the output distribution of `c`, for a finite output type.

## Main results

* `ProbComp.expect_bind`: **total expectation**; sequencing averages the continuations.
* `ProbComp.expect_sample`: sampling a finite type is the uniform average.
* `ProbComp.expect_add`, `expect_const_mul`, `expect_sum`, `expect_mono`: linearity and
  monotonicity.
* `ProbComp.prob_nonneg`, `prob_le_one`, `prob_mono`, `prob_or_le` (the union bound),
  `prob_not`, `prob_bind`.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
  Uniform sampling as an oracle follows VCVio's uniform-selection oracle; the real-valued
  finite-sum semantics here is not VCVio's (which is measure-valued).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (probabilistic algorithms; the uniform distribution over coin strings).
-/

namespace TCSlib.Cryptography.Games

open Finset TCSlib.InformationTheory

/-- The **uniform-sampling oracles**: oracle `m` takes no query and answers a uniformly random
element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp] -/
abbrev unifSpec : OracleSpec ℕ := ⟨fun _ => Unit, fun m => Fin (m + 1)⟩

/-- **Probabilistic computations**: oracle computations whose only oracles draw uniform samples.
[VCVio, OracleComp/ProbComp/Basic] -/
abbrev ProbComp := OracleComp unifSpec

namespace ProbComp

variable {α β : Type}

/-- A uniformly random element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp/Basic (uniformFin)] -/
def sampleFin (m : ℕ) : ProbComp (Fin (m + 1)) := .query m () .pure

/-- Sampling `Fin (m + 1)` is one query to the `m`-th sampling oracle:
`sampleFin m = .query m () .pure`. -/
theorem sampleFin_eq (m : ℕ) : sampleFin m = .query m () .pure := rfl

/-- A uniformly random element of the nonempty finite type `T`, through its enumeration
`Fintype.equivFin`. -/
noncomputable def sample (T : Type) [Fintype T] [Nonempty T] : ProbComp T :=
  (fun j : Fin (Fintype.card T - 1 + 1) =>
    (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
      sampleFin (Fintype.card T - 1)

/-- Sampling `T` is sampling an index below `|T|` and reading it through `Fintype.equivFin`:
`sample T = (fun j => (equivFin T).symm (Fin.cast _ j)) <$> sampleFin (|T| − 1)`. -/
theorem sample_eq (T : Type) [Fintype T] [Nonempty T] :
    sample T = (fun j : Fin (Fintype.card T - 1 + 1) =>
      (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
        sampleFin (Fintype.card T - 1) := rfl

/-- The **expectation** of `g` over the output of `c`: `g a` for a return, and the average over
the `m + 1` equally likely answers at a sampling step. -/
noncomputable def expect : ProbComp α → (α → ℝ) → ℝ
  | .pure a, g => g a
  | .query m _ k, g => ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g

/-- The **probability** that the output of `c` satisfies `p`: the expectation of the indicator
of `p`. -/
noncomputable def prob (c : ProbComp α) (p : α → Prop) : ℝ := by
  classical exact expect c (fun a => if p a then 1 else 0)

/-- A return is its own expectation. -/
@[simp] theorem expect_pure (a : α) (g : α → ℝ) : expect (.pure a) g = g a := rfl

/-- A sampling step averages over its answers. -/
theorem expect_query (m : ℕ) (x : Unit) (k : Fin (m + 1) → ProbComp α) (g : α → ℝ) :
    expect (.query m x k) g = ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g := rfl

/-- **Total expectation:** the expectation over `c` followed by `f` is the expectation over `c`
of the expectation over `f a`.

**Proof sketch.** Induction on `c`: a return is immediate, and at a sampling step both sides
average the same continuations. -/
theorem expect_bind (c : ProbComp α) (f : α → ProbComp β) (g : β → ℝ) :
    expect (c.bind f) g = expect c (fun a => expect (f a) g) := by
  induction c with
  | pure a => simp only [OracleComp.pure_bind, expect_pure]
  | query m x k ih => simp only [OracleComp.query_bind, expect_query, ih]

/-- The expectation over a mapped computation is the expectation of the composite. -/
theorem expect_map (h : α → β) (c : ProbComp α) (g : β → ℝ) :
    expect (h <$> c) g = expect c (fun a => g (h a)) := by
  rw [OracleComp.map_eq_bind, expect_bind]; rfl

/-- Sampling `Fin (m + 1)` is the uniform average over it. -/
theorem expect_sampleFin (m : ℕ) (g : Fin (m + 1) → ℝ) :
    expect (sampleFin m) g = ((m : ℝ) + 1)⁻¹ * ∑ j, g j := rfl

/-- Sampling a nonempty finite type is the uniform average over it.

**Proof sketch.** The sample is the image of a uniform element of `Fin |T|` under the bijection
`Fintype.equivFin`, and a sum is invariant under reindexing by a bijection. -/
theorem expect_sample (T : Type) [Fintype T] [Nonempty T] (g : T → ℝ) :
    expect (sample T) g = (Fintype.card T : ℝ)⁻¹ * ∑ t, g t := by
  have hc : Fintype.card T - 1 + 1 = Fintype.card T := Nat.sub_add_cancel Fintype.card_pos
  rw [sample, expect_map, expect_sampleFin]
  congr 1
  · congr 1
    exact_mod_cast hc
  · exact Fintype.sum_equiv ((finCongr hc).trans (Fintype.equivFin T).symm) _ _
      (fun j => by simp)

/-- Expectation is additive. -/
theorem expect_add (c : ProbComp α) (f g : α → ℝ) :
    expect c (fun a => f a + g a) = expect c f + expect c g := by
  induction c with
  | pure a => rfl
  | query m x k ih => simp only [expect_query, ih, sum_add_distrib, mul_add]

/-- Expectation commutes with scaling by a constant. -/
theorem expect_const_mul (c : ProbComp α) (r : ℝ) (f : α → ℝ) :
    expect c (fun a => r * f a) = r * expect c f := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, ← mul_sum]
    ring

/-- The expectation of a constant is that constant. -/
theorem expect_const (c : ProbComp α) (r : ℝ) : expect c (fun _ => r) = r := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

/-- Expectation commutes with finite sums. -/
theorem expect_sum {ι : Type} (c : ProbComp α) (s : Finset ι) (f : ι → α → ℝ) :
    expect c (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect c (f i) := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, mul_sum]
    exact sum_comm

/-- Expectation is monotone. -/
theorem expect_mono (c : ProbComp α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expect c f ≤ expect c g := by
  induction c with
  | pure a => exact h a
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ih j) (by positivity)

/-- The expectation of a nonnegative function is nonnegative. -/
theorem expect_nonneg (c : ProbComp α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ expect c f := by
  simpa [expect_const] using expect_mono c (f := fun _ => 0) h

/-! ### Probabilities of events -/

/-- The probability of `p` is the expectation of its indicator (any decidability instance). -/
theorem prob_eq_expect (c : ProbComp α) (p : α → Prop) [DecidablePred p] :
    prob c p = expect c (fun a => if p a then 1 else 0) := by
  unfold prob
  congr 1
  funext a
  congr 1

/-- A return satisfies `p` with probability one or zero. -/
theorem prob_pure (a : α) (p : α → Prop) [Decidable (p a)] :
    prob (.pure a) p = if p a then 1 else 0 := by
  classical
  rw [prob_eq_expect, expect_pure]
  congr 1

/-- **Total probability:** the probability over `c` followed by `f` is the expectation over `c`
of the probability over `f a`. -/
theorem prob_bind (c : ProbComp α) (f : α → ProbComp β) (p : β → Prop) :
    prob (c.bind f) p = expect c (fun a => prob (f a) p) := by
  classical
  simp only [prob_eq_expect, expect_bind]

/-- Probabilities are nonnegative. -/
theorem prob_nonneg (c : ProbComp α) (p : α → Prop) : 0 ≤ prob c p := by
  classical
  rw [prob_eq_expect]
  exact expect_nonneg c fun a => by split_ifs <;> norm_num

/-- Probabilities are at most one. -/
theorem prob_le_one (c : ProbComp α) (p : α → Prop) : prob c p ≤ 1 := by
  classical
  rw [prob_eq_expect]
  calc expect c (fun a => if p a then (1 : ℝ) else 0) ≤ expect c (fun _ => 1) :=
        expect_mono c fun a => by split_ifs <;> norm_num
    _ = 1 := expect_const c 1

/-- An event implied by another has at least its probability. -/
theorem prob_mono (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a → q a) :
    prob c p ≤ prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_mono c fun a => by
    by_cases hp : p a
    · simp [hp, h a hp]
    · simp only [hp, if_false]; split_ifs <;> norm_num

/-- Events that agree on every output have the same probability. -/
theorem prob_congr (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    prob c p = prob c q :=
  le_antisymm (prob_mono c fun a => (h a).1) (prob_mono c fun a => (h a).2)

/-- **The union bound** for two events. -/
theorem prob_or_le (c : ProbComp α) (p q : α → Prop) :
    prob c (fun a => p a ∨ q a) ≤ prob c p + prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  exact expect_mono c fun a => by
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq]

/-- The complement of an event has one minus its probability. -/
theorem prob_not (c : ProbComp α) (p : α → Prop) :
    prob c (fun a => ¬ p a) = 1 - prob c p := by
  classical
  rw [prob_eq_expect, prob_eq_expect, eq_sub_iff_add_eq, ← expect_add]
  calc expect c (fun a => (if ¬ p a then (1 : ℝ) else 0) + if p a then 1 else 0)
      = expect c (fun _ => 1) := by
        congr 1; funext a; by_cases hp : p a <;> simp [hp]
    _ = 1 := expect_const c 1

/-! ### Output distributions -/

/-- The **output distribution** of a computation with a finite output type: the probability of
each outcome. -/
noncomputable def dist [Fintype α] [DecidableEq α] (c : ProbComp α) : FinDist α where
  prob a := prob c (· = a)
  nonneg a := prob_nonneg c _
  sum_prob := by
    simp only [prob_eq_expect]
    rw [← expect_sum]
    calc expect c (fun x => ∑ a, if x = a then (1 : ℝ) else 0) = expect c (fun _ => 1) := by
          congr 1; funext x; simp
      _ = 1 := expect_const c 1

/-- The output distribution gives each outcome its probability. -/
theorem dist_apply [Fintype α] [DecidableEq α] (c : ProbComp α) (a : α) :
    dist c a = prob c (· = a) := rfl

end ProbComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Protocols.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two-party protocols as oracle computations

A party of a two-party protocol is an oracle computation with two kinds of oracles: the message
exchange (send a message, receive the other party's next message) and its own coins. Running the
protocol interleaves the two parties as coroutines: the active party runs until it sends a
message, the other party resumes with that message and runs until it replies, and so on, for at
most `fuel` messages.

**When a party returns.** [PS10, §4.4] ends the protocol when the active machine halts, and gives
a machine an output only on halting, so the waiting party has none. Yet Definitions 116.1 and
155.1 use both parties' outputs. Following the ch. 2–4 layer's foundation decision D8
(`TCSlib.Cryptography.ZeroKnowledge.Interaction`), both parties have outputs: the waiting party is
activated **once more**. Its pending send is answered `none` ("the other party has finished"), it
may draw coins, and it must then return without sending. A send after the end is reported
(`ExecOutcome.sentAfterEnd`), never hidden.

**A broader model than D8's.** The executor is a coroutine model that contains D8's. It is broader
in two respects. A party may return early (D8 fixes the number of messages). And a party's output
is a separate return value (in D8 it is the next-message function on the complete history, so the
last sender's output equals its last message). D8's executions are those of *embedded strategies*:
each samples its whole tape first, sends `next` on its scheduled turns, and returns `next` on its
complete history. Agreement with D8 is claimed only for that class (bridge B4, S2b).

**Traces.** `Party.execT` returns, beside the outcome, each party's received messages (the second
mover's first message first) and the coin draws it executed (`Party.Obs`). Its outcome is that of
`Party.exec` (`Party.execT_outcome`). A [PS10, §4.4] view `(x, z, r, M)` contains the whole random
tape `r`, including bits never read. It is recovered from the trace only for parties that sample
their whole tape first, as an embedded strategy does. Inputs and auxiliary inputs are Lean
parameters of the party. A party's own oracle log would miss the second mover's first message,
which reaches it as an argument.

The ch. 2–4 layer's strategies (`TCSlib.Cryptography.Strategy`, `TCSlib.Cryptography.exec`) remain
the definitions of interaction for IP, ZK and two-party computation (ruling of 2026-11-05). This
executor is the calculus in which their properties are proved, through B4.

## Main definitions

* `Games.exchangeSpec Out In`: the message-exchange oracle (send an `Out`, receive an `In` or
  `none`).
* `Games.Party Out In α`: a party sending `Out`, receiving `In`, drawing its own coins and returning
  an `α`.
* `Games.ExecOutcome`: both outputs, out of fuel, or a send after the end.
* `Games.Party.step`, `Games.Party.close`: run a party to its next send or return; close a party
  whose counterpart has returned.
* `Games.Party.exec fuel A B`: execute a protocol in which `A` moves first, with at most `fuel`
  messages.
* `Games.Party.Obs`, `Games.Party.execT`: the traced execution, recording each party's received
  messages and coins.

## Main results

* `Games.Party.exec_zero`, `Party.exec_succ`: the execution equations.
* `Games.Party.execT_outcome`: the traced execution has the outcome of the execution.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines, executions, views), Definitions 116.1 and 155.1.
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

/-- The **message-exchange oracle**: the query is the message sent, and the answer is the other
party's next message, or `none` if the other party has returned. [PS10, §4.4] -/
abbrev exchangeSpec (Out In : Type) : OracleSpec Unit := ⟨fun _ => Out, fun _ => Option In⟩

/-- A **party** of a two-party protocol: sends messages of type `Out`, receives messages of type
`In`, draws its own coins, and returns an `α`. [PS10, §4.4] -/
abbrev Party (Out In α : Type) : Type := OracleComp ((exchangeSpec Out In).add unifSpec) α

/-- The **outcome of an execution**: both outputs; the message budget ran out; or a party sent a
message after its counterpart had returned. -/
inductive ExecOutcome (α β : Type) : Type where
  /-- Both parties returned: the first mover's output and the second mover's. -/
  | done (a : α) (b : β)
  /-- The message budget ran out before both parties returned. -/
  | outOfFuel
  /-- A party sent a message after its counterpart had returned. -/
  | sentAfterEnd

/-- Exchange the roles in an outcome. -/
def ExecOutcome.swap {α β : Type} : ExecOutcome α β → ExecOutcome β α
  | .done a b => .done b a
  | .outOfFuel => .outOfFuel
  | .sentAfterEnd => .sentAfterEnd

/-- Exchanging the roles exchanges the outputs: `(done a b).swap = done b a`. -/
theorem ExecOutcome.swap_done {α β : Type} (a : α) (b : β) :
    (ExecOutcome.done a b).swap = .done b a :=
  rfl

/-- A spent budget stays a spent budget: `outOfFuel.swap = outOfFuel`. -/
theorem ExecOutcome.swap_outOfFuel {α β : Type} :
    (ExecOutcome.outOfFuel : ExecOutcome α β).swap = .outOfFuel :=
  rfl

/-- A send after the end stays one: `sentAfterEnd.swap = sentAfterEnd`. -/
theorem ExecOutcome.swap_sentAfterEnd {α β : Type} :
    (ExecOutcome.sentAfterEnd : ExecOutcome α β).swap = .sentAfterEnd :=
  rfl

namespace Party

variable {Out In α β : Type}

/-- Run a party until it returns or sends a message, passing its coin draws through. The result is
either its output, or the message it sends together with how it continues on the reply. -/
def step : Party Out In α → ProbComp (α ⊕ (Out × (Option In → Party Out In α)))
  | .pure a => .pure (.inl a)
  | .query (.inl ()) m k => .pure (.inr (m, k))
  | .query (.inr j) x k => .query j x (fun y => step (k y))

/-- A returned party is done: `step (pure a) = pure (inl a)`. -/
theorem step_pure (a : α) : step (OracleComp.pure a : Party Out In α) = .pure (.inl a) :=
  rfl

/-- A party sending `m` stops there, with `m` and its continuation on the reply:
`step (query (inl ()) m k) = pure (inr (m, k))`. -/
theorem step_send (m : Out) (k : Option In → Party Out In α) :
    step (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inl ()) m k) =
      .pure (.inr (m, k)) :=
  rfl

/-- A coin draw of a party is passed through:
`step (query (inr j) x k) = query j x (fun y => step (k y))`. -/
theorem step_coin (j : ℕ) (x : Unit) (k : Fin (j + 1) → Party Out In α) :
    step (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inr j) x k) =
      .query j x (fun y => step (k y)) :=
  rfl

/-- **Close** a party whose counterpart has returned (its pending send already answered `none`):
it may still draw coins, and returns `some` of its output, or `none` if it sends a message. -/
def close : Party Out In α → ProbComp (Option α)
  | .pure a => .pure (some a)
  | .query (.inl ()) _ _ => .pure none
  | .query (.inr j) x k => .query j x (fun y => close (k y))

/-- Closing a returned party gives its output: `close (pure a) = pure (some a)`. -/
theorem close_pure (a : α) : close (OracleComp.pure a : Party Out In α) = .pure (some a) :=
  rfl

/-- Closing a party that sends gives `none`: `close (query (inl ()) m k) = pure none`. -/
theorem close_send (m : Out) (k : Option In → Party Out In α) :
    close (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inl ()) m k) =
      .pure none :=
  rfl

/-- Closing passes a coin draw through:
`close (query (inr j) x k) = query j x (fun y => close (k y))`. -/
theorem close_coin (j : ℕ) (x : Unit) (k : Fin (j + 1) → Party Out In α) :
    close (OracleComp.query (spec := (exchangeSpec Out In).add unifSpec) (.inr j) x k) =
      .query j x (fun y => close (k y)) :=
  rfl

/-- The end of an execution in which the active party returned `a`: the waiting party `B` is
activated once more, with `none`, and closed. -/
def endWith {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    ProbComp (ExecOutcome α β) :=
  (close (B none)).bind fun ob => .pure (Option.elim ob .sentAfterEnd (ExecOutcome.done a))

/-- The end of an execution closes the waiting party on `none`, and reports `done a b` if it
returns `b` and `sentAfterEnd` if it sends:
`endWith a B = (close (B none)).bind fun ob => pure (ob.elim sentAfterEnd (done a))`. -/
theorem endWith_eq {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    endWith a B =
      (close (B none)).bind fun ob => .pure (Option.elim ob .sentAfterEnd (ExecOutcome.done a)) :=
  rfl

/-- **Execution** of a two-party protocol with at most `fuel` messages. `A` moves first, and `B`
waits for `A`'s first message. After each message the roles swap. A return costs no fuel; when the
active party returns, the waiting party is activated once more and closed (`endWith`).

**Deviation from [PS10, §4.4]:** the source ends the protocol when the active machine halts and
defines outputs only on halting, so the waiting party would have none, while Definitions 116.1
and 155.1 use both outputs. Following the ch. 2–4 layer's D8, the waiting party is activated once
more; it may draw coins, but a send is reported as `sentAfterEnd`.

**Relation to D8.** This executor is broader than D8 in two respects. A party may return early
(D8 fixes the number of messages). And a party's output is a separate return value, computed after
its last activation and possibly after fresh coins on closure. In D8 a party's output is its
next-message function on its complete history, so the last sender's output equals its last
message (`Protocol.outV_eq_getLast_of_moverIsV`). D8's executions are the executions of embedded
strategies (each samples its whole tape first, sends `next` on its scheduled turns, and returns
`next` on its complete history). Agreement with D8 is claimed only for that class (bridge B4). -/
def exec : ℕ → ∀ {M₁ M₂ α β : Type},
    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) → ProbComp (ExecOutcome α β)
  | 0, _, _, _, _, A, B =>
    (step A).bind (Sum.elim (fun a => endWith a B) (fun _ => .pure .outOfFuel))
  | fuel + 1, _, _, _, _, A, B =>
    (step A).bind (Sum.elim (fun a => endWith a B)
      (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure r.swap))

/-- With no fuel, the first mover runs until it returns or tries to send. If it returns, the
waiting party is closed (`endWith`): activated with `none`, it may draw coins, and the outcome is
`done` if it returns and `sentAfterEnd` if it sends. If the first mover tries to send, the outcome
is `outOfFuel` and the waiting party never runs. -/
@[simp] theorem exec_zero {M₁ M₂ : Type} (A : Party M₁ M₂ α) (B : Option M₁ → Party M₂ M₁ β) :
    exec 0 A B = (step A).bind (Sum.elim (fun a => endWith a B) (fun _ => .pure .outOfFuel)) :=
  rfl

/-- One message of the execution: `A` runs until it returns (then `B` is closed) or sends `m`
(then `B` resumes with `m` as the first mover, against `A`'s continuation). -/
theorem exec_succ {M₁ M₂ : Type} (fuel : ℕ) (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β) :
    exec (fuel + 1) A B =
      (step A).bind (Sum.elim (fun a => endWith a B)
        (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure r.swap)) :=
  rfl

/-! ### Sanity checks: fuel counts messages; a send after the end is reported -/

example (a b : Bool) :
    exec 0 (M₁ := Unit) (M₂ := Unit) (.pure a) (fun _ => .pure b) = .pure (.done a b) := by
  simp only [exec_zero, step_pure, OracleComp.pure_bind, Sum.elim_inl, endWith_eq, close_pure,
    Option.elim_some]

example (m : Unit) (a b : Bool) :
    exec 1 (M₂ := Unit) (.query (.inl ()) m fun _ => .pure a) (fun _ => .pure b) =
      .pure (.done a b) := by
  simp only [exec_succ, step_send, OracleComp.pure_bind, Sum.elim_inr, exec_zero, step_pure,
    Sum.elim_inl, endWith_eq, close_pure, Option.elim_some, ExecOutcome.swap_done]

example (m : Unit) (a b : Bool) :
    exec 1 (M₁ := Unit) (.pure a) (fun _ => .query (.inl ()) m fun _ => .pure b) =
      .pure .sentAfterEnd := by
  simp only [exec_succ, step_pure, OracleComp.pure_bind, Sum.elim_inl, endWith_eq, close_send,
    Option.elim_none]

/-! ### The traced execution -/

/-- What one party **observes** during an execution: the messages delivered to it, in order, and
the coins it drew, each as a sampling oracle `m` with its answer in `Fin (m + 1)`. -/
structure Obs (In : Type) : Type where
  /-- The messages delivered to the party, in order. -/
  received : List In
  /-- The party's coin draws, in order. -/
  coins : List (Σ m : ℕ, Fin (m + 1))

/-- `step`, also returning the coins drawn along the way. -/
def stepT : Party Out In α →
    ProbComp ((α ⊕ (Out × (Option In → Party Out In α))) × List (Σ m : ℕ, Fin (m + 1)))
  | .pure a => .pure (.inl a, [])
  | .query (.inl ()) m k => .pure (.inr (m, k), [])
  | .query (.inr j) x k => .query j x fun y =>
      (stepT (k y)).bind fun p => .pure (p.1, ⟨j, y⟩ :: p.2)

/-- `close`, also returning the coins drawn along the way. -/
def closeT : Party Out In α → ProbComp (Option α × List (Σ m : ℕ, Fin (m + 1)))
  | .pure a => .pure (some a, [])
  | .query (.inl ()) _ _ => .pure (none, [])
  | .query (.inr j) x k => .query j x fun y =>
      (closeT (k y)).bind fun p => .pure (p.1, ⟨j, y⟩ :: p.2)

/-- The traced end of an execution: `endWith`, also returning the waiting party's coins. -/
def endWithT {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    ProbComp (ExecOutcome α β × List (Σ m : ℕ, Fin (m + 1))) :=
  (closeT (B none)).bind fun p => .pure (Option.elim p.1 .sentAfterEnd (ExecOutcome.done a), p.2)

/-- The **traced execution**: `exec`, also returning what each party observed. The first component
of the result is the outcome, the second the first mover's observations, and the third the second
mover's. When the active party sends `m`, `m` is the first message the other party receives in the
rest of the run. [PS10, §4.4] (the received messages of a view; its random tape for parties that
sample it first) -/
def execT : ℕ → ∀ {M₁ M₂ α β : Type},
    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) →
      ProbComp (ExecOutcome α β × Obs M₂ × Obs M₁)
  | 0, _, _, _, _, A, B =>
    (stepT A).bind fun p => Sum.elim
      (fun a => (endWithT a B).bind fun q => .pure (q.1, ⟨[], p.2⟩, ⟨[], q.2⟩))
      (fun _ => .pure (.outOfFuel, ⟨[], p.2⟩, ⟨[], []⟩)) p.1
  | fuel + 1, _, _, _, _, A, B =>
    (stepT A).bind fun p => Sum.elim
      (fun a => (endWithT a B).bind fun q => .pure (q.1, ⟨[], p.2⟩, ⟨[], q.2⟩))
      (fun mk => (execT fuel (B (some mk.1)) mk.2).bind fun r =>
        .pure (r.1.swap, ⟨r.2.2.received, p.2 ++ r.2.2.coins⟩,
          ⟨mk.1 :: r.2.1.received, r.2.1.coins⟩)) p.1

/-- An ended execution never reports a spent budget: the outcome of `endWithT` is `done` or
`sentAfterEnd`. -/
theorem endWithT_ne_outOfFuel {M₁ M₂ : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    (endWithT a B).AllOutputs fun q => q.1 ≠ .outOfFuel := by
  refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
  rcases p with ⟨_ | b, cs⟩ <;>
    simp only [OracleComp.allOutputs_pure, Option.elim_none, Option.elim_some, ne_eq,
      reduceCtorEq, not_false_eq_true]

/-- **Trace invariants** (gate 02 round 2, note 5): on every possible run of
`execT fuel A B`, write `M_A` and `M_B` for the messages delivered to the first and the second
mover. Then `|M_A| + |M_B| ≤ fuel`; the second mover has received as many messages as the first
or one more (it receives first); and a spent budget means exactly `fuel` messages were delivered.

**Proof sketch.** Induction on `fuel`, generalizing the parties and their types. A return or a
blocked send delivers nothing (both lists are empty), and `endWithT` never reports a spent budget.
A delivered message adds one message to the receiver, and the recursive run, with the roles
exchanged, satisfies the invariants with `fuel − 1`; exchanging back keeps them, since its first
mover is the original second mover. -/
theorem execT_trace : ∀ (fuel : ℕ) {M₁ M₂ α β : Type} (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β),
    (execT fuel A B).AllOutputs fun r =>
      r.2.1.received.length + r.2.2.received.length ≤ fuel ∧
      (r.2.2.received.length = r.2.1.received.length ∨
        r.2.2.received.length = r.2.1.received.length + 1) ∧
      (r.1 = .outOfFuel → r.2.1.received.length + r.2.2.received.length = fuel)
  | 0, _, _, _, _, A, B => by
    refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
    rcases p with ⟨a | mk, cs⟩
    · exact OracleComp.AllOutputs.bind (endWithT_ne_outOfFuel a B) fun q hq =>
        OracleComp.allOutputs_pure.2 ⟨by simp, by simp, fun h => absurd h hq⟩
    · exact OracleComp.allOutputs_pure.2 ⟨by simp, by simp, fun _ => by simp⟩
  | fuel + 1, _, _, _, _, A, B => by
    refine OracleComp.AllOutputs.bind (OracleComp.allOutputs_true _) fun p _ => ?_
    rcases p with ⟨a | mk, cs⟩
    · exact OracleComp.AllOutputs.bind (endWithT_ne_outOfFuel a B) fun q hq =>
        OracleComp.allOutputs_pure.2 ⟨by simp, by simp, fun h => absurd h hq⟩
    · refine OracleComp.AllOutputs.bind (execT_trace fuel (B (some mk.1)) mk.2) fun r hr => ?_
      obtain ⟨h1, h2, h3⟩ := hr
      refine OracleComp.allOutputs_pure.2 ⟨?_, ?_, fun h => ?_⟩
      · simp only [List.length_cons]; omega
      · simp only [List.length_cons]; omega
      · have : r.1 = .outOfFuel := by
          cases hr1 : r.1 <;> simp_all [ExecOutcome.swap]
        have := h3 this
        simp only [List.length_cons]; omega

/-- `stepT` projects to `step`. -/
theorem stepT_fst (A : Party Out In α) : (stepT A).bind (fun p => .pure p.1) = step A := by
  induction A with
  | pure a => simp only [stepT, step, OracleComp.pure_bind]
  | query i x k ih =>
    cases i with
    | inl u => cases u; simp only [stepT, step, OracleComp.pure_bind]
    | inr j =>
      simp only [stepT, step, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
      congr 1
      funext y
      exact ih y

/-- `closeT` projects to `close`. -/
theorem closeT_fst (A : Party Out In α) : (closeT A).bind (fun p => .pure p.1) = close A := by
  induction A with
  | pure a => simp only [closeT, close, OracleComp.pure_bind]
  | query i x k ih =>
    cases i with
    | inl u => cases u; simp only [closeT, close, OracleComp.pure_bind]
    | inr j =>
      simp only [closeT, close, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
      congr 1
      funext y
      exact ih y

/-- `endWithT` projects to `endWith`. -/
theorem endWithT_fst {M₁ M₂ : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    (endWithT a B).bind (fun q => .pure q.1) = endWith a B := by
  simp only [endWithT, endWith, OracleComp.bind_assoc, OracleComp.pure_bind]
  rw [← closeT_fst (B none), OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind]

/-- **The traced execution has the execution's outcome.**

**Proof sketch.** Induction on the fuel, generalizing the parties and their types. Each level of
`execT` runs `stepT`, which projects to `step` (`stepT_fst`); the branch on the first component
then matches `exec`'s, with `endWithT` projecting to `endWith` and the recursive call to the
recursive call. -/
theorem execT_outcome : ∀ (fuel : ℕ) {M₁ M₂ α β : Type} (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β),
    (execT fuel A B).bind (fun r => .pure r.1) = exec fuel A B
  | 0, _, _, _, _, A, B => by
    simp only [execT, exec, OracleComp.bind_assoc]
    rw [← stepT_fst A, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    congr 1
    funext p
    rcases p with ⟨_ | _, c⟩
    · simp only [Sum.elim_inl, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← endWithT_fst]
    · simp only [Sum.elim_inr, OracleComp.pure_bind]
  | fuel + 1, _, _, _, _, A, B => by
    simp only [execT, exec, OracleComp.bind_assoc]
    rw [← stepT_fst A, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    congr 1
    funext p
    rcases p with ⟨_ | mk, c⟩
    · simp only [Sum.elim_inl, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← endWithT_fst]
    · simp only [Sum.elim_inr, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← execT_outcome fuel (B (some mk.1)) mk.2, OracleComp.bind_assoc]
      simp only [OracleComp.pure_bind]

end Party

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Simulate.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implementing oracles: simulation and logging

An oracle computation only *asks* its oracles. A security game decides how they answer: with a
keyed function, with fresh coins on every query (a randomized encryption oracle), refusing some
queries (a CCA2 decryption oracle that will not decrypt the challenge), or by asking other
oracles (a reduction that answers its adversary's queries with queries of its own). All of these
are *implementations*: for each oracle and query, a computation over a target specification that
returns the answer and updates a state. `simulate` runs a computation with every query answered
by an implementation, threading the state.

Logging is an implementation transformer: it answers as before and also appends every query and
its answer to a log kept in the state. Win conditions such as "the forged message was never
queried" are predicates on that log. Logging never changes the computation
(`simulate_withLog`).

## Main definitions

* `Games.QueryImpl spec σ spec'`: implementations of the oracles of `spec` by computations over
  `spec'`, with state `σ`.
* `Games.simulate impl c s`: run `c` from state `s`, answering its queries with `impl`.
* `Games.QueryImpl.ofComp`, `QueryImpl.passthrough`, `QueryImpl.sum`: stateless implementations,
  forwarding queries unchanged, and implementing two oracle families side by side.
* `Games.QueryLog spec`, `Games.QueryImpl.withLog`: the record of a run's queries and answers, and
  the logging transformer.
* `Games.QueryImpl.comp`: answering one implementation's queries with another.

## Main results

* `Games.simulate_bind`: simulation commutes with sequencing.
* `Games.simulate_withLog`: forgetting the log of a logged simulation gives the plain simulation.
* `Games.simulate_comp`: simulation composes; a reduction run against an implementation of its
  oracles is a single implementation of its adversary's oracles.
* `Games.simulate_costBoundedBy`: if each query of `c` to oracle `i` is answered by a computation
  of cost at most `b i`, and `c` is cost-bounded by `q` when oracle `i` costs `b i`, then the
  simulation is cost-bounded by `q`.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (answering an adversary's queries in a reduction).
-/

namespace TCSlib.Cryptography.Games

variable {ι ι' ι₁ ι₂ : Type} {α β σ : Type}

/-- An **implementation** of the oracles of `spec` by computations over `spec'`, with state `σ`:
on oracle `i`, query `x` and state `s`, a computation returning the answer and the new state.
[VCVio, SimSemantics] -/
abbrev QueryImpl {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') : Type :=
  ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)

/-- An implementation is a function of the oracle, the query and the state:
`QueryImpl spec σ spec' = ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)`. -/
theorem queryImpl_def {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') :
    QueryImpl spec σ spec' = ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ) := rfl

/-- **Simulation:** run `c` from state `s`, answering each of its queries with `impl` and
threading the state; return `c`'s result and the final state. [VCVio, SimSemantics] -/
def simulate {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec') :
    OracleComp spec α → σ → OracleComp spec' (α × σ)
  | .pure a, s => .pure (a, s)
  | .query i x k, s => (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2)

section Simulate

variable {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec')

/-- Simulating a return returns it with the state unchanged. -/
@[simp] theorem simulate_pure (a : α) (s : σ) :
    simulate impl (OracleComp.pure a) s = .pure (a, s) := rfl

/-- Simulating a query runs the implementation, then simulates the continuation. -/
@[simp] theorem simulate_query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (s : σ) :
    simulate impl (OracleComp.query i x k) s =
      (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2) := rfl

/-- **Simulation commutes with sequencing:** simulating `c` followed by `f` is simulating `c`,
then simulating `f` on its result from the state it reached.

**Proof sketch.** Induction on `c`; at a query, both sides run the implementation first, and the
monad's associativity lines up the continuations. -/
theorem simulate_bind (c : OracleComp spec α) (f : α → OracleComp spec β) (s : σ) :
    simulate impl (c.bind f) s = (simulate impl c s).bind (fun p => simulate impl (f p.1) p.2) := by
  induction c generalizing s with
  | pure a => simp only [OracleComp.pure_bind, simulate_pure]
  | query i x k ih => simp only [OracleComp.query_bind, simulate_query, OracleComp.bind_assoc, ih]

/-- Simulating a single call is running the implementation. -/
theorem simulate_call (i : ι) (x : spec.dom i) (s : σ) :
    simulate impl (OracleComp.call i x) s = impl i x s := by
  rw [← OracleComp.bind_pure (OracleComp.call i x), OracleComp.call_bind, simulate_query]
  simp only [simulate_pure]
  exact OracleComp.bind_pure _

end Simulate

namespace QueryImpl

/-- A **stateless** implementation: oracle `i` answers query `x` by running `f i x`. -/
def ofComp {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) : QueryImpl spec σ spec' :=
  fun i x s => (f i x).bind (fun y => .pure (y, s))

/-- A stateless implementation runs `f i x` and keeps the state:
`ofComp f i x s = (f i x).bind (fun y => .pure (y, s))`. -/
theorem ofComp_apply {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) (i : ι) (x : spec.dom i) (s : σ) :
    ofComp f i x s = (f i x).bind (fun y => .pure (y, s)) :=
  rfl

/-- **Forwarding:** every query is passed unchanged to the same oracle of the target. -/
def passthrough {spec : OracleSpec ι} : QueryImpl spec σ spec :=
  ofComp (fun i x => OracleComp.call i x)

/-- Forwarding asks the same oracle the same query and keeps the state:
`passthrough i x s = .query i x (fun y => .pure (y, s))`. -/
theorem passthrough_apply {spec : OracleSpec ι} (i : ι) (x : spec.dom i) (s : σ) :
    passthrough (σ := σ) i x s = .query i x (fun y => .pure (y, s)) := by
  rw [passthrough, ofComp_apply, OracleComp.call_bind]

/-- Implement two oracle families **side by side**, sharing one state: `.inl i` is answered by
`impl₁`, and `.inr j` by `impl₂`. -/
def sum {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') :
    QueryImpl (s₁.add s₂) σ spec'
  | .inl i => impl₁ i
  | .inr j => impl₂ j

/-- Side by side, the oracle `.inl i` is answered by `impl₁`: `sum impl₁ impl₂ (.inl i) x s =
impl₁ i x s`. -/
theorem sum_inl {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') (i : ι₁) (x : s₁.dom i)
    (s : σ) : sum impl₁ impl₂ (.inl i) x s = impl₁ i x s :=
  rfl

/-- Side by side, the oracle `.inr j` is answered by `impl₂`: `sum impl₁ impl₂ (.inr j) x s =
impl₂ j x s`. -/
theorem sum_inr {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') (j : ι₂) (x : s₂.dom j)
    (s : σ) : sum impl₁ impl₂ (.inr j) x s = impl₂ j x s :=
  rfl

end QueryImpl

/-! ### Composing implementations -/

/-- **Composition:** answer the queries of `spec` with `impl₁`, whose own queries (to `spec'`)
are answered by `impl₂`; the state is the pair of the two states. This is how a reduction that
answers its adversary's queries by querying its own oracles becomes, after its oracles are
implemented, a single implementation of the adversary's oracles.
[VCVio, SimSemantics/QueryImpl/Compose (QueryImpl.compose)] -/
def QueryImpl.comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') : QueryImpl spec (σ₁ × σ₂) spec'' :=
  fun i x s => (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))

/-- The composed implementation simulates `impl₁`'s answer with `impl₂` and regroups the states:
`impl₂.comp impl₁ i x s =
(simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))`. -/
theorem QueryImpl.comp_apply {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') (i : ι) (x : spec.dom i) (s : σ₁ × σ₂) :
    impl₂.comp impl₁ i x s =
      (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2))) :=
  rfl

/-- **Simulation composes:** simulating with `impl₂` a simulation by `impl₁` is simulating once
with the composed implementation, up to regrouping the states.
[VCVio, SimSemantics/QueryImpl/Compose (simulateQ_compose)]

**Proof sketch.** Induction on the computation. At a query, both sides first run `impl₁`'s answer
under `impl₂` (`simulate_bind` on the left, the definition of `comp` on the right), and the
continuations agree by induction after associativity. -/
theorem simulate_comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') (c : OracleComp spec α) (s₁ : σ₁) (s₂ : σ₂) :
    simulate impl₂ (simulate impl₁ c s₁) s₂ =
      (simulate (impl₂.comp impl₁) c (s₁, s₂)).bind (fun p => .pure ((p.1, p.2.1), p.2.2)) := by
  induction c generalizing s₁ s₂ with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    simp only [simulate_query, simulate_bind, QueryImpl.comp, OracleComp.bind_assoc,
      OracleComp.pure_bind]
    congr 1
    funext p
    exact ih p.1.1 p.1.2 p.2

/-! ### Logging -/

/-- The **log** of a run: the list of its queries, each with the oracle asked, the query and the
answer, in order. [VCVio, QueryTracking/LoggingOracle] -/
abbrev QueryLog {ι : Type} (spec : OracleSpec ι) : Type :=
  List (Σ i, spec.dom i × spec.rng i)

/-- **Logging:** answer as `impl` does, and append each query and its answer to the log kept
beside the state. [VCVio, QueryTracking/LoggingOracle] -/
def QueryImpl.withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') : QueryImpl spec (σ × QueryLog spec) spec' :=
  fun i x s => (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))

/-- The logged implementation answers as `impl` and appends the entry to the log:
`impl.withLog i x s = (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))`.
-/
theorem QueryImpl.withLog_apply {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') (i : ι) (x : spec.dom i) (s : σ × QueryLog spec) :
    impl.withLog i x s =
      (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩]))) :=
  rfl

/-- **Logging is conservative:** forgetting the log of a logged simulation gives the plain
simulation, whatever the initial log.

**Proof sketch.** Induction on the computation: at a query, the logged implementation is the
plain one followed by a return that only extends the log, and the continuations agree by
induction. -/
theorem simulate_withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') (c : OracleComp spec α) (s : σ) (log : QueryLog spec) :
    (simulate impl.withLog c (s, log)).bind (fun p => .pure (p.1, p.2.1)) =
      simulate impl c s := by
  induction c generalizing s log with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    simp only [simulate_query, QueryImpl.withLog, OracleComp.bind_assoc, OracleComp.pure_bind]
    congr 1
    funext ys
    exact ih ys.1 ys.2 _

/-! ### Costs under simulation -/

/-- **Costs under simulation:** if every call to oracle `i` is answered by a computation of cost
at most `b i` (target costs `cost'`), and `c` is cost-bounded by `q` when oracle `i` costs
`b i`, then the simulation of `c` is cost-bounded by `q`. With `b i = 1` for every oracle the
reduction asks once per query, the reduction makes no more target queries than its adversary
makes queries.

**Proof sketch.** Induction on `c`. At a query to oracle `i` with budget `q ≥ b i`, the
implementation fits in `b i`, and the simulated continuation fits in `q - b i` by induction, so
the sequence fits in `b i + (q - b i) = q` (`CostBoundedBy.bind`). -/
theorem simulate_costBoundedBy {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {impl : QueryImpl spec σ spec'} {cost' : ι' → ℕ} {b : ι → ℕ}
    (himpl : ∀ i x s, OracleComp.CostBoundedBy cost' (impl i x s) (b i))
    {c : OracleComp spec α} {q : ℕ} (hc : OracleComp.CostBoundedBy b c q) (s : σ) :
    OracleComp.CostBoundedBy cost' (simulate impl c s) q := by
  induction c generalizing q s with
  | pure a =>
    rw [simulate_pure]
    exact OracleComp.costBoundedBy_pure cost' (a, s) q
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := (OracleComp.costBoundedBy_query b i x k q).1 hc
    have h := OracleComp.CostBoundedBy.bind (himpl i x s) (fun ys => ih ys.1 (hk ys.1) ys.2)
    rw [Nat.add_sub_cancel' hi] at h
    rw [simulate_query]
    exact h

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Pseudorandom/Functions/LazySampling.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary
import Mathlib.Data.Fintype.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lazy sampling of a random oracle

A random function `R : I → O` has `|O|^|I|` values, far too many for an efficient
reduction to sample. An oracle algorithm making at most `q` queries only ever looks at
`q` of them, and the standard remedy [Gar26, footnote 9 of §3.4] is *lazy sampling*: keep
a list of the distinct queries seen so far, answer a repeated query consistently, and
answer the `k`-th new query with a fresh value `W k`. This file proves that lazy
sampling with `q` uniform values `W : Fin q → O` produces exactly the same output
distribution as a uniform random function.

The lazy run is stated for an arbitrary answer stream `a : ℕ → O` (the answer to the
`k`-th distinct query is `a k`), so that hybrids can mix fresh values with other
answers index by index.

## Main definitions

* `QueryTree.noteQuery L x`: the list of distinct queries after querying `x`.
* `QueryTree.evalLazy a t L`: run `t`, answering the `k`-th distinct query by `a k`.
* `extendStream W`: a finite list of values `W : Fin q → O` as an answer stream.

## Main results

* `QueryTree.evalLazy_congr`: a run making at most `m` more queries only reads the first
  `L.length + m` entries of the answer stream.
* `QueryTree.uprob_evalLazy`: lazy sampling with `q` uniform fresh values has the same
  output distribution as a uniform random function, for trees making at most `q`
  queries.
* Probability helpers: `uprob_congr`, `uprob_prod_comm`, `uprob_snd`,
  `uprob_sections_congr`, `uprob_update_absorb`, `uprob_update_split`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2, footnote 9 (lazy sampling of random functions).
-/

namespace TCSlib.Cryptography

open Function

section Helpers

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- Events that are equivalent pointwise have the same probability. -/
theorem uprob_congr {p p' : α → Prop} (h : ∀ a, p a ↔ p' a) : uprob p = uprob p' :=
  congrArg uprob (funext fun a => propext (h a))

/-- Swapping the two coordinates of a product does not change probabilities. -/
theorem uprob_prod_comm (p : α → β → Prop) :
    uprob (fun z : α × β => p z.1 z.2) = uprob (fun z : β × α => p z.2 z.1) :=
  (uprob_comp_equiv (Equiv.prodComm β α) (fun z : α × β => p z.1 z.2)).symm

/-- An event depending only on the second coordinate has the same probability on the
product. -/
theorem uprob_snd [Nonempty α] (p : β → Prop) :
    uprob (fun z : α × β => p z.2) = uprob p := by
  rw [uprob_prod_comm (fun _ b => p b)]
  exact uprob_fst p

/-- Two events on products with the same first factor have the same probability when
every section has the same probability. -/
theorem uprob_sections_congr (p : α → β → Prop) (p' : α → γ → Prop)
    (h : ∀ a, uprob (p a) = uprob (p' a)) :
    uprob (fun z : α × β => p z.1 z.2) = uprob (fun z : α × γ => p' z.1 z.2) := by
  rw [uprob_prod, uprob_prod]
  exact congrArg uexp (funext h)

variable [DecidableEq α]

/-- Overwriting one entry of a uniform table by an independent uniform value leaves the
table uniform: the overwritten entry is absorbed. -/
theorem uprob_update_absorb [Nonempty β] (i : α) (f : (α → β) → γ → Prop) :
    uprob (fun z : β × ((α → β) × γ) => f (update z.2.1 i z.1) z.2.2) =
      uprob (fun z : (α → β) × γ => f z.1 z.2) := by
  let e : β × ((α → β) × γ) ≃ ((α → β) × γ) × β :=
    { toFun := fun z => ((update z.2.1 i z.1, z.2.2), z.2.1 i)
      invFun := fun w => (w.1.1 i, (update w.1.1 i w.2, w.1.2))
      left_inv := fun z => by simp
      right_inv := fun w => by simp }
  exact (uprob_comp_equiv e (fun w => f w.1.1 w.1.2)).trans
    (uprob_fst (fun w : (α → β) × γ => f w.1 w.2))

/-- Overwriting one entry of a uniform table by an independent uniform value leaves the
table uniform (version without extra coordinates). -/
theorem uprob_update_absorb' [Nonempty β] (i : α) (f : (α → β) → Prop) :
    uprob (fun z : β × (α → β) => f (update z.2 i z.1)) = uprob f := by
  let e : β × (α → β) ≃ (α → β) × β :=
    { toFun := fun z => (update z.2 i z.1, z.2 i)
      invFun := fun w => (w.1 i, update w.1 i w.2)
      left_inv := fun z => by simp
      right_inv := fun w => by simp }
  exact (uprob_comp_equiv e (fun w => f w.1)).trans (uprob_fst f)

/-- If an event on a uniform table `W` depends on the entry `W i` only through a
parameter `v` (it does not otherwise read position `i`), its probability is the average
over `v` of the probability with `v` fixed. -/
theorem uprob_update_split [Nonempty β] (i : α) (g : β → (α → β) → Prop)
    (hg : ∀ v W u, g v (update W i u) ↔ g v W) :
    uprob (fun W => g (W i) W) = uexp (fun v => uprob (fun W => g v W)) := by
  rw [← uprob_prod (fun z : β × (α → β) => g z.1 z.2),
    ← uprob_update_absorb' i (fun W => g (W i) W)]
  exact uprob_congr fun z => by simp [hg]

end Helpers

namespace QueryTree

variable {I O α : Type} [DecidableEq I]

/-- The list of distinct queries after the query `x`, given the list `L` of distinct
queries so far: `x` is appended if it is new. -/
def noteQuery (L : List I) (x : I) : List I := if x ∈ L then L else L ++ [x]

/-- A repeated query leaves the list of distinct queries unchanged. -/
theorem noteQuery_of_mem {L : List I} {x : I} (h : x ∈ L) : noteQuery L x = L := if_pos h

/-- A new query is appended to the list of distinct queries. -/
theorem noteQuery_of_not_mem {L : List I} {x : I} (h : x ∉ L) : noteQuery L x = L ++ [x] :=
  if_neg h

/-- The index of the current query in the updated list is below its length. -/
theorem idxOf_noteQuery_lt (L : List I) (x : I) :
    (noteQuery L x).idxOf x < (noteQuery L x).length := by
  rw [List.idxOf_lt_length_iff]
  unfold noteQuery; split_ifs with h <;> simp [h]

/-- Querying adds at most one entry to the list of distinct queries. -/
theorem length_noteQuery_le (L : List I) (x : I) :
    (noteQuery L x).length ≤ L.length + 1 := by
  unfold noteQuery; split_ifs <;> simp

/-- Run `t` against a lazily sampled oracle: with `L` the list of distinct queries so
far, the query `x` is answered by `a k`, where `k` is the position of `x` among the
distinct queries in order of first appearance. A repeated query gets the same answer as
before. [Gar26, §3.4.2, footnote 9]. -/
def evalLazy (a : ℕ → O) : QueryTree I O α → List I → α
  | ret y, _ => y
  | query x k, L =>
      evalLazy a (k (a ((noteQuery L x).idxOf x))) (noteQuery L x)

/-- A leaf returns its output whatever the answers. -/
@[simp] theorem evalLazy_ret (a : ℕ → O) (y : α) (L : List I) :
    evalLazy a (ret y) L = y := rfl

/-- A query is recorded and answered by the stream entry at its position. -/
theorem evalLazy_query (a : ℕ → O) (x : I) (k : O → QueryTree I O α) (L : List I) :
    evalLazy a (query x k) L =
      evalLazy a (k (a ((noteQuery L x).idxOf x))) (noteQuery L x) := rfl

/-- A run making at most `m` further queries, started with `L` distinct queries already
seen, only reads the answer stream below `L.length + m`. -/
theorem evalLazy_congr {a b : ℕ → O} {t : QueryTree I O α} {m : ℕ} (ht : t.BoundedBy m)
    (L : List I) (hab : ∀ k < L.length + m, a k = b k) :
    evalLazy a t L = evalLazy b t L := by
  induction t using QueryTree.induct generalizing m L with
  | ret y => rfl
  | query x k ih =>
    cases m with
    | zero => exact absurd ht (boundedBy_query_zero x k)
    | succ m =>
      have h1 := idxOf_noteQuery_lt L x
      have h2 := length_noteQuery_le L x
      rw [evalLazy_query, evalLazy_query, hab _ (by omega)]
      exact ih _ ((boundedBy_query_succ x k m).1 ht _) _ fun j hj => hab j (by omega)

/-- Post-processing every lazy answer by `g` is the same as running the tree whose
answers are post-processed by `g`. -/
theorem evalLazy_comp {O' : Type} (g : O' → O) (a : ℕ → O') (t : QueryTree I O α)
    (L : List I) :
    evalLazy (g ∘ a) t L = evalLazy a (t.simulate id (fun _ => g)) L := by
  induction t using QueryTree.induct generalizing L with
  | ret y => rw [simulate_ret, evalLazy_ret, evalLazy_ret]
  | query x k ih =>
    rw [simulate_query, evalLazy_query, evalLazy_query]
    exact ih _ _

end QueryTree

/-- A finite list `W : Fin q → O` of values as an answer stream; entries beyond `q` are
an arbitrary fixed value and are never read by trees making at most `q` queries. -/
noncomputable def extendStream {O : Type*} [Nonempty O] {q : ℕ} (W : Fin q → O) : ℕ → O :=
  fun k => if h : k < q then W ⟨k, h⟩ else Classical.arbitrary O

namespace QueryTree

variable {I : Type*} {O : Type*} {α : Type*} [DecidableEq I]

/-- A constant event has the same probability on any two nonempty finite types. -/
private theorem uprob_const_eq {β γ : Type*} [Fintype β] [Fintype γ] [Nonempty β]
    [Nonempty γ] (P : Prop) : uprob (fun _ : β => P) = uprob (fun _ : γ => P) := by
  by_cases h : P
  · rw [uprob_congr (p' := fun _ : β => True) (fun _ => iff_true_intro h),
      uprob_congr (p' := fun _ : γ => True) (fun _ => iff_true_intro h), uprob_true,
      uprob_true]
  · rw [uprob_congr (p' := fun _ : β => False) (fun _ => iff_false_intro h),
      uprob_congr (p' := fun _ : γ => False) (fun _ => iff_false_intro h), uprob_false,
      uprob_false]

/-- Keep the first `ℓ` entries of `W₀` and take the remaining entries from `W`. -/
private def combine {q : ℕ} (ℓ : ℕ) (W₀ W : Fin q → O) : Fin q → O :=
  fun i => if i.val < ℓ then W₀ i else W i

/-- The table answering a recorded query `x ∈ L` from the stream `a` at the position of `x`
in `L`, and every other query from `R`. -/
private def mergeTable (L : List I) (a : ℕ → O) (R : I → O) : I → O :=
  fun x => if x ∈ L then a (L.idxOf x) else R x

section Streams

variable [Nonempty O] {q : ℕ}

/-- Overwriting entry `j` of a value list does not change the stream at other positions. -/
theorem extendStream_update_of_ne (W : Fin q → O) (j : Fin q) (v : O) {k : ℕ}
    (hk : k ≠ j.val) : extendStream (update W j v) k = extendStream W k := by
  unfold extendStream
  split_ifs with h
  · exact update_of_ne (fun e => hk (by rw [← e])) _ _
  · rfl

/-- Overwriting entry `j` of a value list by `v` makes the stream read `v` at `j`. -/
theorem extendStream_update_self (W : Fin q → O) (j : Fin q) (v : O) :
    extendStream (update W j v) j.val = v := by
  simp [extendStream]

private theorem extendStream_combine_of_lt (W₀ W : Fin q → O) {ℓ k : ℕ} (hk : k < ℓ) :
    extendStream (combine ℓ W₀ W) k = extendStream W₀ k := by
  unfold extendStream combine
  split_ifs <;> simp_all

private theorem extendStream_combine_self (W₀ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) :
    extendStream (combine ℓ W₀ W) ℓ = W ⟨ℓ, hℓ⟩ := by
  simp [extendStream, combine, hℓ]

omit [Nonempty O] in
private theorem combine_succ (W₀ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) :
    combine ℓ W₀ W = combine (ℓ + 1) (update W₀ ⟨ℓ, hℓ⟩ (W ⟨ℓ, hℓ⟩)) W := by
  funext i
  unfold combine
  by_cases h1 : i.val < ℓ
  · have : i ≠ ⟨ℓ, hℓ⟩ := fun e => by rw [e] at h1; exact lt_irrefl _ h1
    simp [h1, Nat.lt_succ_of_lt h1, this]
  · by_cases h2 : i.val = ℓ
    · have : i = ⟨ℓ, hℓ⟩ := Fin.ext h2
      subst this; simp
    · have : ¬ i.val < ℓ + 1 := by omega
      simp [h1, this]

omit [Nonempty O] in
private theorem combine_update (W₁ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) (u : O) :
    combine (ℓ + 1) W₁ (update W ⟨ℓ, hℓ⟩ u) = combine (ℓ + 1) W₁ W := by
  funext i
  unfold combine
  by_cases h : i.val < ℓ + 1
  · simp [h]
  · have : i ≠ ⟨ℓ, hℓ⟩ := fun e => by rw [e] at h; exact h (Nat.lt_succ_self _)
    simp [h, this]

private theorem mergeTable_append (W₀ : Fin q → O) (R : I → O) {L : List I} {x : I}
    (hx : x ∉ L) (hℓ : L.length < q) :
    mergeTable L (extendStream W₀) R =
      mergeTable (L ++ [x]) (extendStream (update W₀ ⟨L.length, hℓ⟩ (R x))) R := by
  funext y
  unfold mergeTable
  by_cases hy : y ∈ L
  · have hlt := List.idxOf_lt_length_of_mem hy
    rw [if_pos hy, if_pos (List.mem_append_left _ hy), List.idxOf_append_of_mem hy,
      extendStream_update_of_ne _ _ _ (by simp; omega)]
  · by_cases hyx : y = x
    · subst hyx
      rw [if_neg hy, if_pos (by simp), List.idxOf_append_of_notMem hy]
      simpa using (extendStream_update_self W₀ ⟨L.length, hℓ⟩ (R y)).symm
    · rw [if_neg hy, if_neg (by simp [hy, hyx])]

omit [Nonempty O] in
private theorem mergeTable_update (L : List I) (a : ℕ → O) (R : I → O) {x : I} (hx : x ∈ L)
    (u : O) : mergeTable L a (update R x u) = mergeTable L a R := by
  funext y
  unfold mergeTable
  by_cases hy : y ∈ L
  · simp [hy]
  · have : y ≠ x := fun e => hy (e ▸ hx)
    simp [hy, this]

end Streams

end QueryTree

namespace QueryTree

variable {I O α : Type} [DecidableEq I]

/-- The generalized lazy-sampling invariant: started with `L` already recorded, with
answers `W₀` on `L`, the lazy run with fresh values beyond `L` and the run against a
random function agreeing with `W₀` on `L` have the same output distribution.

**Proof sketch.** Induction on the tree. A repeated query is answered by the recorded
value on both sides. For a new query `x`, the lazy side answers with the fresh entry at
position `|L|` and the table side with `R x`; record this answer `v` in `W₀`. Neither
continuation reads the entry again, so both probabilities are averages over `v` of the
continuation probabilities (`uprob_update_split`), which agree by induction. -/
private theorem uprob_evalLazy_aux [Fintype I] [Fintype O] [Nonempty O] (φ : α → Prop)
    {q : ℕ} (t : QueryTree I O α) : ∀ (m : ℕ) (L : List I) (W₀ : Fin q → O),
    t.BoundedBy m → L.length + m ≤ q →
    uprob (fun W : Fin q → O => φ (evalLazy (extendStream (combine L.length W₀ W)) t L)) =
      uprob (fun R : I → O => φ (t.eval (mergeTable L (extendStream W₀) R))) := by
  induction t using QueryTree.induct with
  | ret y =>
    intro _ _ _ _ _
    simp only [evalLazy_ret, eval_ret]
    exact uprob_const_eq (β := Fin q → O) (γ := I → O) (φ y)
  | query x k ih =>
    intro m L W₀ ht hm
    cases m with
    | zero => exact absurd ht (boundedBy_query_zero x k)
    | succ m =>
    by_cases hx : x ∈ L
    · -- a repeated query: both sides answer with the recorded value
      have hi : L.idxOf x < L.length := List.idxOf_lt_length_of_mem hx
      have hl : ∀ W, evalLazy (extendStream (combine L.length W₀ W)) (query x k) L =
          evalLazy (extendStream (combine L.length W₀ W)) (k (extendStream W₀ (L.idxOf x)))
            L := by
        intro W
        rw [evalLazy_query, noteQuery_of_mem hx, extendStream_combine_of_lt _ _ hi]
      have hr : ∀ R, (query x k).eval (mergeTable L (extendStream W₀) R) =
          (k (extendStream W₀ (L.idxOf x))).eval (mergeTable L (extendStream W₀) R) := by
        intro R; simp [mergeTable, hx]
      simp only [hl, hr]
      exact ih _ m L W₀ ((boundedBy_query_succ x k m).1 ht _) (by omega)
    · -- a new query: split off the fresh value on both sides
      have hℓ : L.length < q := by omega
      have hidx : (L ++ [x]).idxOf x = L.length := by
        rw [List.idxOf_append_of_notMem hx]; simp
      have hlen : (L ++ [x]).length = L.length + 1 := by simp
      let j : Fin q := ⟨L.length, hℓ⟩
      let g : O → (Fin q → O) → Prop := fun v W =>
        φ (evalLazy (extendStream (combine (L ++ [x]).length (update W₀ j v) W)) (k v)
          (L ++ [x]))
      let h : O → (I → O) → Prop := fun v R =>
        φ ((k v).eval (mergeTable (L ++ [x]) (extendStream (update W₀ j v)) R))
      have hl : ∀ W, φ (evalLazy (extendStream (combine L.length W₀ W)) (query x k) L) ↔
          g (W j) W := by
        intro W
        simp only [g, evalLazy_query, noteQuery_of_not_mem hx, hidx, hlen,
          extendStream_combine_self _ _ hℓ, ← combine_succ _ _ hℓ, j]
      have hr : ∀ R, φ ((query x k).eval (mergeTable L (extendStream W₀) R)) ↔
          h (R x) R := by
        intro R
        simp only [h, eval_query, ← mergeTable_append W₀ R hx hℓ, j]
        simp [mergeTable, hx]
      rw [uprob_congr hl, uprob_congr hr,
        uprob_update_split j g (fun v W u => by simp only [g, hlen, j, combine_update]),
        uprob_update_split x h (fun v R u => by
          simp only [h, mergeTable_update _ _ _ (List.mem_append_right L
            (List.mem_singleton_self x))])]
      exact congrArg uexp (funext fun v =>
        ih v m (L ++ [x]) (update W₀ j v) ((boundedBy_query_succ x k m).1 ht v)
          (by rw [hlen]; omega))

/-- **Lazy sampling.** For a query tree making at most `q` queries, answering the `k`-th
distinct query by the `k`-th of `q` independent uniform values gives the same output
distribution as answering by a uniform random function. [Gar26, §3.4.2, footnote 9],
stated as an exact equality of probabilities for every event on the output.

**Proof sketch.** Generalize to a run started with a list `L` of `ℓ` distinct queries
whose answers are fixed values `W₀`, against a random function that agrees with `W₀` on
`L`. A repeated query is answered by the fixed value on both sides. A new query is
answered by the fresh value `W ℓ` on the lazy side and by `R x` on the table side; in
both cases the rest of the run does not read this entry again except through the
recorded answer, so both probabilities are the average over the answer `v` of the
probability of the continuation with `v` recorded, which agree by induction. -/
theorem uprob_evalLazy [Fintype I] [Fintype O] [Nonempty O] (φ : α → Prop)
    {t : QueryTree I O α} {q : ℕ} (ht : t.BoundedBy q) :
    uprob (fun W : Fin q → O => φ (evalLazy (extendStream W) t [])) =
      uprob (fun R : I → O => φ (t.eval R)) := by
  have h := uprob_evalLazy_aux (q := q) φ t q [] (fun _ => Classical.arbitrary O) ht (by simp)
  have h1 : ∀ W : Fin q → O, combine ([] : List I).length (fun _ => Classical.arbitrary O) W = W :=
    fun W => funext fun i => by simp [combine]
  have h2 : ∀ R : I → O, mergeTable [] (extendStream fun _ : Fin q => Classical.arbitrary O)
      R = R := fun R => funext fun y => by simp [mergeTable]
  simpa only [h1, h2] using h

end QueryTree

end TCSlib.Cryptography

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/resolutions-r2.md =====

# Gate 04 (S2b, #195): round 2 resolutions

- **Round 2:** findings `findings/gate04-s2b-r2-findings.md` on #195 at `243598b7`: **1 major (R2-01),
  2 minors (R2-02, R2-03)**. F01, F03, F04, F06, N1, N5, N6 fixed; F05 fixed for the accounting
  defect; N3 and N4 recorded; F02, N2 and N7 not resolved (F02 pending R2-01; N2 and N7 because the
  evidence was not in the bundle).
- **Repairs:** two commits on #195's branch after `243598b7`:
  - `81e4f4e21738e90eeef285a2a88fb7f664918a3a`: R2-01 (the seal extended to every consumer file;
    `Simulate.lean` and `PRF.lean` re-proved through published lemmas) and R2-03;
  - `27ae72da62119ebdde380b8cb2d8c183b59fa2bf`: equation lemmas clearing check 8's three warnings.
- **Evidence** (`evidence-r3/`, **all in the bundle this time**): the replay, the axiom printout, lint,
  check 8, the seal script and its full output, the round 1 review, and the duplication ledger.

| Item | Severity | Resolution |
|---|---|---|
| R2-01 | major | **Fixed.** `QueryImpl.passthrough_apply` is proved by `rw [passthrough, ofComp_apply, OracleComp.call_bind]` (its own definition, a same-file lemma, a published lemma). The seal now covers **every consumer file of the change set, the new equation proofs included** (13 files, `seal-evidence.log`): all pass for the current version. To get there, pre-existing proofs were re-proved through published lemmas: in `Simulate.lean`, `simulate_bind`, `simulate_comp`, `simulate_withLog`, `simulate_costBoundedBy` and `simulate_call`; in `PRF.lean`, `acceptProb_random_eq_lazy`, `buildTree_boundedBy`, `toOracleAdversary_boundedBy` and `prfAdv_toOracleAdversary_zero`. New equation lemmas beside their definitions: `OracleAdversary.boundedBy_iff`, `lazyDist_apply`. The seal configuration's one non-definition entry (`abs_sub_le_sum_hybrids`) was removed. **Boundary, disclosed:** older ch. 2–4 proofs in `PRF.lean` (Frederick's, not S2b's) still read `distAdv`, `prfAdv`, `randomFunction`, `PRF` and the GGM reduction's helpers, which are not in the seal table. Gate 03d audits `PRF.lean` and the ch. 2–4 clean-up PR pays this back. |
| R2-02 | minor | **Fixed.** The bundle carries `evidence-r3/{replay.log, replay-order.txt, axioms.log, lint.log, check8.log, seal.py.txt, seal-evidence.log}`, the round 1 review (`review/gate04-review.md`, defining N1–N7) and the duplication ledger (rows DL-9 to DL-19 now exist; DL-9 includes `take_drop_ofFn_blocks`, gate 04 N4). |
| R2-03 | minor | **Fixed.** `InteractiveHandler`, `call` and `finish` (and their equation lemmas' docstrings): "a malformed move, or a further query after the budget is spent, gives the all-`false` result; a return at zero remaining budget is accepted". |
| F02 | major (round 1) | **Fixed with R2-01** (the seal is clean on every consumer file). |
| N2, N7 | minor | **Fixed:** check 8 is now 0 failures and **0 warnings** on `Games/` (the three S2a warnings cleared by `OracleSpec.add_dom_inl/_inr`, `add_rng_inl/_inr`, `sampleFin_eq`, `sample_eq`, `queryImpl_def`), and the seal output is attached. |

## ===== briefs/pass-shelat-ch5-8/gates/04-s2b/review/gate04-review.md =====

# Gate 04 (S2b): review of the auditor's findings, with resolution proposals

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/04-s2b/findings/gate04-s2b-findings.md`: 0 blockers, 2 majors (F01, F02), 4 minors (F03–F06).
- **Code:** worktree `wt-s2b` at `afe5982f612081bba2fbcec9ab41adcbbc118b13` (confirmed with `git rev-parse HEAD`). Line numbers refer to that commit unless a prong worktree is named. The F-1 baseline is `a3c5fa8b`.
- **Downstream code read:**
  - `wt-prong-a` at `2d7b5441` (`Authentication/`);
  - `wt-prong-b` at `c04d8a3a` (`SecureComputation/`, including `Yao.lean`);
  - `wt-prong-c` at `aa71d0e7` (`Composability/`);
  - `wt-prong-d` at `6ea900ae` (`Randomness/`).

  Prongs A–C branch from earlier S2b commits. Their `Games/{BitCodec, Machines, Bridges/*, Protocols, OracleComp}.lean` are byte-identical to `afe5982f`; only `Efficiency.lean` differs (no T2).
- **Method.** I did not build Lean. I did three things:
  - read every S2b proof that consumes another file's definition;
  - ran a script that lists every `unfold`/`simp`/`rw` argument naming a TCSlib definition from another file (scratch tools in `scratchpad/g04-review-tools/`);
  - ran the campaign lint's check 8 (`scripts/campaign_style_lint.py --check8b`) on `TCSlib/Cryptography` at the base `a3c5fa8b` and at the head, and diffed the two.

  Reads through `rfl`, `show` and term-mode definitional unfolding were found by hand. They are what the campaign's rule-10 seal (`attribute [local irreducible]`, `WORKFLOW.md` §"Standing rules") would reject.

## Summary

- **All six findings are true.** I agree with every severity: F01 and F02 are major; F03–F06 are minor.
- **F01 (`decodeIdx` checks only the length).**
  - Confirmed at `BitCodec.lean:60–61`.
  - The fix is a strict unary check with converse lemmas, about 60–90 lines in `BitCodec.lean`.
  - It re-proves one lemma (`decodeIdx_replicate`). No other proof in S2b or in any prong unfolds or reasons about `decodeIdx` or `decodeBitMove`.
  - No statement text changes. Every security notion that uses `bitCodec` quantifies over all NUPPT adversaries, and a coin-preserving post-processing (`exists_comp`) maps each adversary to one with the same computation under the other decoder. So no notion changes meaning.
  - The fix matters most for the efficiency fill. Without converse lemmas the fill cannot read `decodeBitMove` on arbitrary machine output without unfolding it (rule 10).
  - Ruling R-04-1 (light): it changes a T0 definition before the fill is issued.
- **F02 (missing defining equations): true, and understated.** The auditor names 5 consumer sites, in 4 proofs. I find 16 S2b proofs that read another file's TCSlib definitions:
  - the unfolds the auditor names;
  - B2 rewriting with `accept` and `advantage` (`Bridges/Experiments.lean:119,127`);
  - B1 unfolding `QueryImpl.ofComp` and reading `QueryTree.simulate` through `rfl`/`show` (`Bridges/QueryTree.lean:76–77,103–108`);
  - B4 reading `Party.exec`, `step`, `close`, `endWith` and `ExecOutcome.swap` through `rfl`/`show` (`Bridges/Strategies.lean:138–145`), and `simp [moverIsV]` although `moverIsV_true`/`_false` exist (`:163`);
  - `AllOutputs`, which S2b moved from `Hopping.lean` to `OracleComp.lean`. That move turned same-file reads in `Hopping.lean:85,88,168` and `Protocols.lean:238,262–268` into cross-file reads.

  The fix is about 75–85 equation lemmas (mostly `rfl`/`Iff.rfl`, about 450–510 lines with docstrings), with 16 proofs re-pointed. The full list is in §2.

  Prong B would also benefit:
  - at 9 sites that read ch. 2–4's `Protocol.transcriptWith`/`outP`/`outV`/`viewP`/`viewV` (`Interaction.lean`);
  - from 5 lemmas on its own `keyAt`, `garbledValues`, `inputKeys`, `tableAt` and `answersB`, which `Yao.lean` now reads through four private `rfl` copies and one `show`; these should become shared lemmas.

  Ruling R-04-2 decides scope (S2a and ch. 2–4 files would join the change set).
- **What the auditor missed (§5).** The most important miss is N1, proposed **major**:
  - **N1: T1/T2 do not cover the reductions they are cited for.** The auditor listed T1/T2's limitations but did not count them. They lack:
    - adversary input (`toCompOn`);
    - final state and finalization;
    - exact output;
    - a codec bridge to the PRF assumption's `toOracleAdversary`.

    Eight reduction sketches in prongs A and C cite T1 or T2 for reductions that need one of these:
    - Thm 135.4, Thm 137.2 and Thm 144.1 (two machines) in prong A;
    - Thm 168.2, Thm 170.4, Thm 175.9 and `padded_cpa` in prong C.

    Seven of the eight cite T1. Four of those seven need an oracle, which T1's handler cannot query.

    Ruling R-04-3: extend T0–T2 before the fill brief is issued (recommended).
  - **N2:** attestation 4 ran main's per-file `style_lint.py`, which has no check 8. The campaign lint's check 8 shows S2b adding 16 public definitions with no lemma (`workflow.md` §6: "a landing adds no name to it"). It also shows 8 more definitions that pass only by name (a bound or a single case, not an equation).
  - **Minor misses:**
    - N3: the `Strategies.lean` docstring promises results "stated in a later part of this file" that do not exist.
    - N4: `MultiMessageLemmas.take_drop_ofFn_blocks` duplicates `EnsembleLemmas.take_drop_ofFn_blocks` and is not in the duplication ledger.
    - N5: `simp [Option.elim]`, a core definition passed to `simp`, at `Protocols.lean:239`.
    - N6: T1's componentwise default disagrees with T2's joint default (folded into F03).
    - N7: there is no rule-10 seal evidence in the pack.
- **Rulings needed:** R-04-1 (F01), R-04-2 (F02 scope) and R-04-3 (N1). F03–F06 and N2–N7 are maintainer fixes.
- **Proposed closing condition:** F01 and F02 fixed, R-04-3 ruled (and applied if option 1), and the evidence refreshed (§7). Then a delta re-audit of `BitCodec.lean`, `Efficiency.lean` and the new lemmas.

---

## 1. F01 (major): `decodeIdx` checks only the length of the unary index

### Verdict: **true**. Severity: **major (agree)**.

**Evidence at `afe5982f`:**
- `BitCodec.lean:60–61`:
  `def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) := if h : iw.length < k then some ⟨iw.length, h⟩ else none`.
  The bits of `iw` are never read, so `decodeIdx 2 [false] = some ⟨1, _⟩`.
- What the documentation says:
  - module doc `:20–23`: a query is `⟨[false], ⟨1^i, x⟩⟩`, and "anything else, a malformed or wrong-length string, decodes to the all-`false` output";
  - `decodeBitMove`'s docstring `:73–75`: "anything else is the output `zeroBits dα`".
- With `din 1 = 1`, the word `pairEncode [false] (pairEncode [false] [false])` reaches `decodeIdx 2 [false] = some 1` and then `decodeFin 1 [false] = some _` (`:82–85`). So it decodes as `.query 1 _`, not as the default.
- The only lemmas are the forward round trips: `decodeIdx_replicate` (`:64`), `decodeBitMove_query` (`:105`) and `decodeBitMove_ret` (`:112`). Nothing characterizes what is accepted.

I agree with the auditor's scope remark. The alias still has length `i < k`, still costs one query, and the same move can be emitted canonically. So there is no cryptographic attack. The defect is that the decoder does not follow the grammar the shared codec publishes.

**Why major.** `bitCodec` is the codec of every prong's security games and of T0–T2. Two consequences follow:
- The efficiency fill's machine `B` must reproduce `decodeBitMove` on **arbitrary** raw output of `A` (`Efficiency.lean:120–123`). The fill brief's rule 10 forbids unfolding it.
- So the fill needs a complete characterization of `decodeBitMove`. With the current `decodeIdx`, no characterization in the documented terms is true (the alias is a counterexample).

So the documentation is materially misleading, and the API the fill needs cannot be stated. That is major under the gate 02 guide. It is not a blocker, because no statement builds on wrong mathematics (see "Effect" below).

### Fix (recommended): strict unary decoding, with converses

```lean
/-- Decoding of an oracle index written in unary: `1^i` with `i < k` is `i`; every other word
(one containing `false`, or of length `≥ k`) is `none`. -/
def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) :=
  if h : iw.length < k ∧ iw = List.replicate iw.length true then some ⟨iw.length, h.1⟩ else none

theorem decodeIdx_replicate (i : Fin k) : decodeIdx k (List.replicate i true) = some i   -- re-proved

/-- Converse: exactly the unary codes decode, each to its index. -/
theorem decodeIdx_eq_some_iff {iw : List Bool} {i : Fin k} :
    decodeIdx k iw = some i ↔ iw = List.replicate i true

/-- Every other word is rejected. -/
theorem decodeIdx_eq_none_iff {iw : List Bool} :
    decodeIdx k iw = none ↔ ∀ i : Fin k, iw ≠ List.replicate i true

/-- Converse of `decodeBitMove_query`: only the canonical query word decodes as that query. -/
theorem decodeBitMove_eq_query_iff {w : List Bool} {i : Fin k} {x : Fin (din i) → Bool} :
    decodeBitMove din dout dα w = .query i x ↔
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))

/-- **The default:** a word that is neither a canonical query nor a canonical output decodes to
`zeroBits dα`. With `decodeBitMove_query` and `decodeBitMove_ret` this covers every input. -/
theorem decodeBitMove_of_not_canonical {w : List Bool}
    (hq : ∀ (i : Fin k) (x : Fin (din i) → Bool),
      w ≠ pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)))
    (hr : ∀ a : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a)) :
    decodeBitMove din dout dα w = .ret (zeroBits dα)
```

- **The proofs live in `BitCodec.lean`.** They may unfold that file's own `decodeIdx`/`decodeBitMove`. They also use:
  - the published `Turing.eq_pairEncode_of_pairDecode` (`Encoding.lean:261`);
  - the new `decodeIdx_eq_some_iff`;
  - a converse for `decodeFin`: `decodeFin ℓ w = some x → w = List.ofFn x`. It does not exist yet.
- **The `decodeFin` converse** can be proved without unfolding `decodeFin`, about 8 lines:
  - `length_eq_of_decodeFin_eq_some` (`Adversary.lean:89`) gives `w.length = ℓ`;
  - rewrite `w` as `List.ofFn` of its own entries;
  - `decodeFin_ofFn` then gives `some f = some x`.

  Its home is `Asymptotic/Adversary.lean` (pack 03a), which is outside S2b's change set and is imported almost everywhere. Recommended: a `private` copy in `BitCodec.lean`, plus a requested shared lemma `decodeFin_eq_some_iff` for the next ch. 2–4 window.
- **Optional, and useful to the fill and to prong reductions:** a canonical encoder `encodeBitMove : Move (bitSpec din dout) (Fin dα → Bool) → List Bool`, with `decodeBitMove_encodeBitMove` and `encodeBitMove_injective`. The fill's `B` can then output `encodeBitMove (decodeBitMove w)`, which is the canonicalization step.
- **Docstrings.** `BitCodec.lean:59` gains "every other word is `none`". `:20–23` and `:73–75` can stay as they are, because after the fix they are true.

**Size:** about 60–90 lines in `BitCodec.lean` (the fix, 1 proof re-done, 4–5 lemmas, the private helper), plus about 25 lines if `encodeBitMove` is added.

### Effect on proofs

- **S2b.** Only `decodeIdx_replicate` (`:64–68`) changes. Its `dif_pos` needs the second conjunct, which is `List.length_replicate` plus `rfl`. `decodeBitMove_query`/`_ret` (`:109`, `:114`) go through unchanged: `simp` uses `decodeIdx_replicate`.
- **`Efficiency.lean`.** It contains no proof about the decoder. `InteractiveHandler.call` (`:182`) uses `decodeBitMove` in a definition. Its meaning changes only on handler outputs with a non-unary index, which now take the default.
- **Efficiency fill (not issued).**
  - The round function adds an all-`true` check on the index. It is polynomial-time by the pairing calculus.
  - The proof gets easier: it uses the converse lemmas instead of unfolding.
  - The brief draft's T0 status line ("T0, done and compiling") needs a refresh.
- **Prongs.** I grepped `wt-prong-{a,b,c,d}`, and also `wt-prong-d2`, `wt-pb-yao` and `wt-pb-compose`. No proof unfolds or reasons about `decodeIdx`, `decodeBitMove` or `bitCodec`. The uses are definitions only:
  - prong A: `Authentication/Defs.lean:122,197` (the forger codecs);
  - prong C: `Composability/{Defs:172, PublicKey:382, NonMalleable:71, SimNonMalleable:180,239}`.

  Nothing to re-prove.

### Does any statement change meaning?

No statement text changes. Only the meaning per machine changes: a machine that emits a non-unary index now gets the default return where it used to get a query.

Every notion built on `bitCodec` quantifies over all `A : NUPPT` (prongs A and C: forgery, IND, NM and SIM-NM games; T1 and T2). The class of computations `{A.toComp(On) (bitCodec …) n q r}` is the same before and after:
- **From the old decoder to the new:** post-compose `A` with the polynomial-time canonicalizer "replace a length-`i` index word by `1^i`".
- **From the new decoder to the old:** post-compose with "replace a non-unary query word by `pairEncode [true] (List.ofFn (zeroBits dα))`".

`Complexity.exists_comp` (`Closure.lean:200`) gives `B.coins = A.coins` and `B.runAtL n y r = post (A.runAtL n y r)`, so the coin space is identical and every advantage is preserved. This argument is not in Lean, and nothing needs it to be.

### Ruling: yes, light (R-04-1, §6)

`Efficiency.lean:21` declares the T0 definitions "final", and the fill brief freezes them at issue. The brief is not yet issued, so the change is cheap now.

---

## 2. F02 (major): missing defining equations; consumers unfold other files' definitions

### Verdict: **true, and understated**. Severity: **major (agree)**.

**Rule.** `policy.md` §1 says, under "Definitions land with their lemmas": "Every new public `def` is published, in the same PR and beside the definition, with the lemmas that let a consumer read it without unfolding … Consumers never unfold another file's definition." `briefs/pass-shelat-ch5-8/WORKFLOW.md` (rule 10) adds:
- it "applies to the maintainer's own API proofs too";
- only core and Mathlib definitions "may reduce in `rfl`, `decide` or `show`";
- "an API that must look inside an author's definitions goes beside them, in their file".

The fill brief repeats rule 10 for T1/T2. So without these equations the fill must either break the rule or copy definitions privately.

**The auditor's sites, all confirmed:**
- `Bridges/Machines.lean:65`: `simp only [MachineCodec.encodeLog, …, encodeHist]`. Also `:63`, `| nil => rfl` through both bodies.
- `:79`, `:82`: `unfold buildComp buildTree`.
- `:108`: `simp only [NUPPT.toComp, NUPPT.toOracleAdversary]`.
- `Bridges/Strategies.lean:183`: `simp only [Protocol.outP, Protocol.outV, Protocol.transcriptWith]`.

**Sites the auditor missed (S2b proofs reading other files' TCSlib definitions):**

| Site | What it reads | Kind |
|---|---|---|
| `Bridges/Experiments.lean:119` (`acceptProb_eq`) | `Games.accept` (`Advantage.lean:63`) | `rw [… accept …]` |
| `Bridges/Experiments.lean:127` (`distAdv_eq`) | `Games.advantage` (`Advantage.lean:67`) | `rw [distAdv_def, advantage, …]` |
| `Bridges/QueryTree.lean:76–77` (`simulate_ofComp_pure`) | `Games.simulate`, `QueryImpl.ofComp` (`Simulate.lean:74,115`), `OracleComp.bind` | `rfl`; `exact ih _` by defeq |
| `Bridges/QueryTree.lean:86–87` (`eval_eq_evalFn`) | `QueryTree.eval` (published `eval_ret`/`eval_query` exist but are not used) | `rfl`; defeq |
| `Bridges/QueryTree.lean:103–108` (`simulate_eq`) | `QueryTree.simulate` (`OracleAdversary.lean:150`, no equations), `QueryImpl.ofComp`, `OracleComp.call` | `rfl`, `show`, `simp only [… QueryImpl.ofComp …]` (:106) |
| `Bridges/Strategies.lean:138,142–145` (`exec_turnParty`) | `Party.exec`, `step`, `close`, `endWith`, `ExecOutcome.swap` (`Protocols.lean:101–146`), `OracleComp.bind` | `rfl`, `show` |
| `Bridges/Strategies.lean:159` (`exec_eq_alt`) | D8 `exec` at 0 (published `exec_zero` exists) | `rfl` |
| `Bridges/Strategies.lean:163` (`exec_eq_alt`) | `moverIsV` (`Interaction.lean:205`; `moverIsV_true`/`_false` exist) | `simp [moverIsV, h]` |
| `Hopping.lean:85,88,168` | `OracleComp.AllOutputs`, moved by S2b to `OracleComp.lean:268` | term-mode defeq (`exact h a hc`, `hc j`, `exact hs`) |
| `Protocols.lean:238,262,263,268` | `AllOutputs` on `.pure` | `show`; anonymous constructors |
| `Machines.lean:112,116–117` (`buildComp_costBoundedBy`) | `CostBoundedBy` (`OracleComp.lean:203`; `costBoundedBy_pure`/`_query` exist) | `exact trivial`; anonymous constructor |

So 16 S2b proofs read another file's definitions, against the 4 proofs (5 sites) the auditor named. Two cases are new debt rather than missing equations:
- **The `AllOutputs` move.** Gate 02 closed `AllOutputs` as `Hopping.lean`'s own definition. Moving it made `Hopping` and `Protocols` cross-file consumers of a predicate that has no `_iff` lemmas. Check 8 does not flag it, because `allOutputs_true` matches the name.
- **The `Bridges/QueryTree` and `Bridges/Experiments` reads** target S2a definitions (`Simulate.lean`, `Advantage.lean`) that gate 02 closed without equations. Their first cross-file consumers are S2b's.

### Equation lemmas to add, per definition

All are `rfl`, `Iff.rfl`, or a two-line `unfold`/`rw` in the definition's own file. None gets `@[simp]`. Each docstring states its formula (policy §1).

**S2b's own definitions**

| Definition (file:line) | Lemmas |
|---|---|
| `MachineCodec.encodeLog` (`Machines.lean:89`) | `encodeLog_nil : codec.encodeLog [] = []`; `encodeLog_cons : codec.encodeLog (e :: h) = pairEncode (codec.encodeEntry e) (codec.encodeLog h)` |
| `buildComp` (`Machines.lean:97`) | four case lemmas covering every input: `buildComp_zero_of_ret (h : next hist = .ret a) : buildComp next t 0 hist = .pure a`; `buildComp_zero_of_query (h : next hist = .query i x) : … = .pure t`; `buildComp_succ_of_ret`; `buildComp_succ_of_query (h : next hist = .query i x) : buildComp next t (q+1) hist = .query i x fun y => buildComp next t q (hist ++ [⟨i, x, y⟩])` |
| `NUPPT.toComp` (`Machines.lean:122`) | `toComp_eq : D.toComp codec n q r = buildComp (fun hist => codec.decodeMove (D.runAt n (codec.encodeLog hist) r)) codec.timeout q []` |
| `NUPPT.toCompOn` (`Machines.lean:135`) | `toCompOn_eq` (the same, with `pairEncode x (codec.encodeLog hist)`) |
| `bitSpec` (`BitCodec.lean:56`, abbrev) | `bitSpec_dom`, `bitSpec_rng` (a new public abbrev still lands with an `_eq` lemma, policy §1) |
| `decodeIdx`, `decodeBitMove` | the converses of §1 |
| `zeroBits` (`BitCodec.lean:71`) | `zeroBits_apply : zeroBits d j = false`; `ofFn_zeroBits : List.ofFn (zeroBits d) = List.replicate d false` |
| `bitCodec` (`BitCodec.lean:97`, structure-valued) | `@[simps (config := { isSimp := false }) decodeMove encodeEntry timeout]`, which gives `bitCodec_decodeMove`, `bitCodec_encodeEntry` and `bitCodec_timeout`; plus `encodeLog_bitCodec`, saying the log encoding does not depend on `dα` (`InteractiveHandler.call` encodes logs with `dα = 0`, `Efficiency.lean:184`, while T2's `B` uses `dα.eval n`) |
| `bitSpecAt` (`Efficiency.lean:62`, abbrev) | `bitSpecAt_eq` |
| `PolyHandler.input` (`:86`) | `PolyHandler.input_eq` |
| `PolyHandler.answer` (`:93`) | `answer_of_pairDecode_eq_none`, `answer_of_pairDecode_eq_some` (together, every input), and the well-formed case `answer_of_run_eq (h : H.run (input …) = pairEncode (List.ofFn y) (List.ofFn s')) : H.answer … = (y, s')` |
| `PolyHandler.impl` (`:105`) | `PolyHandler.impl_apply : H.impl n z ω i x s = .pure (H.answer n z ω s i x)` |
| `InteractiveHandler.input` (`:171`) | `InteractiveHandler.input_eq` |
| `InteractiveHandler.call` (`:178`) | `call_eq` (`= buildComp (…) (zeroBits _) (H.perCall.eval n) []`) |
| `InteractiveHandler.impl` (`:190`) | `InteractiveHandler.impl_apply` |
| `singleCodec` (`Bridges/Machines.lean:45`) | `@[simps (config := { isSimp := false }) decodeMove encodeEntry timeout]` |
| `toHist` (`Bridges/Machines.lean:54`) | `toHist_nil`, `toHist_cons` |
| `OracleComp.evalFn` (`Bridges/QueryTree.lean:64`) | `evalFn_pure`, `evalFn_query` |
| `treeImpl` (`Bridges/QueryTree.lean:91`) | `treeImpl_apply` |
| `acceptGame` (`Bridges/Experiments.lean:107`) | `acceptGame_eq` |
| `turnParty` (`Bridges/Strategies.lean:69`) | `turnParty_zero : turnParty next 0 M = .pure (next M)` (`turnParty_succ` exists) |
| `waitParty` (`:80`) | `waitParty_none`, `waitParty_some_zero`, `waitParty_some_succ : waitParty next (k+1) M (some y) = turnParty next k (M ++ [y])` |
| `alt` (`:95`) | `alt_zero`, `alt_succ : alt nF nG (k+1) MF MG = (alt nG nF k (MG ++ [nF MF]) MF).swap` (`alt_succ_last` is a derived law, not the defining equation) |
| `OracleComp.AllOutputs` (`OracleComp.lean:268`, moved) | `allOutputs_pure : (OracleComp.pure a).AllOutputs P ↔ P a`; `allOutputs_query : (OracleComp.query i x k).AllOutputs P ↔ ∀ y, (k y).AllOutputs P` |
| `singleSpec` (`OracleComp.lean:155`, abbrev) | `singleSpec_dom`, `singleSpec_rng` (optional) |
| `QueryTree.induct` (`OracleAdversary.lean:97`, new; motive in `Sort`) | `induct_ret`, `induct_query` (its computation rules; needed only if data is defined with it) |

**Definitions in files S2b already changes, which S2b's proofs consume (predating the rule, "covered as consumers need them")**

| Definition (file:line) | Lemmas | Consumer |
|---|---|---|
| `encodeHist` (`Asymptotic/PRF.lean:201`) | `encodeHist_nil`, `encodeHist_cons` | `Bridges/Machines.lean:63–67` |
| `buildTree` (`PRF.lean:208`) | the four case lemmas, as for `buildComp` | `Bridges/Machines.lean:79–84` |
| `NUPPT.toOracleAdversary` (`PRF.lean:235`) | `toOracleAdversary_eq` | `Bridges/Machines.lean:108` |
| `QueryTree.simulate` (`OracleAdversary.lean:150`) | `simulate_ret`, `simulate_query` | `Bridges/QueryTree.lean:103–108` |
| `oracleDist` (`OracleAdversary.lean:191`) | `oracleDist_apply` (optional now; the ch. 2–4 files unfold it widely, pack 03d) | — |
| `Party.step`, `close`, `endWith`, `ExecOutcome.swap` (`Protocols.lean:101–126`, S2a) | `step_pure`, `step_send` (`.query (.inl ()) m k`), `step_coin` (`.query (.inr j) x k`); `close_pure`, `close_send`, `close_coin`; `endWith_eq`; `swap_done`, `swap_outOfFuel`, `swap_sentAfterEnd` | `Bridges/Strategies.lean:138–145` |

**Definitions in files outside S2b's change set (R-04-2 decides whether they join it)**

| Definition (file:line) | Lemmas | Consumer |
|---|---|---|
| `Games.accept`, `Games.advantage` (`Games/Advantage.lean:63,67`, S2a) | `accept_eq`, `advantage_eq` (and `guessGame_eq`, which check 8 also lists) | `Bridges/Experiments.lean:119,127` |
| `QueryImpl.ofComp` (`Games/Simulate.lean:115`, S2a) | `ofComp_apply : QueryImpl.ofComp f i x s = (f i x).bind fun y => .pure (y, s)`. Prong A will want `withLog_apply` for its MAC game, `Authentication/Defs.lean:130`. Check 8 also lists `passthrough`, `sum` and `QueryImpl.comp`. | `Bridges/QueryTree.lean:76,106` |
| `Protocol.transcriptWith`, `transcript`, `outV`, `outP`, `viewV`, `viewP`, `Strategy.out` (`ZeroKnowledge/Interaction.lean:326,331,340,344,349,354,267`, ch. 2–4, pack 03e) | `transcriptWith_eq` (`= exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)`); `transcript_eq_transcriptWith` (the name `transcript_eq` is taken); `outV_eq` (for any `P'`; `outV_eq_out` covers only the honest `π.P`); `outP_eq`; `viewV_eq`, `viewP_eq`; `Strategy.out_eq` | `Bridges/Strategies.lean:183`; prong B (below) |

### Consumer proofs to re-point (S2b)

1. `Bridges/Machines.lean`:
   - `encodeLog_singleCodec` (`:62–67`): use `encodeLog_nil/cons`, `encodeHist_nil/cons`, `toHist_cons` and `singleCodec_encodeEntry`;
   - `buildComp_singleCodec` (`:78–90`): use the `buildComp`/`buildTree` case lemmas;
   - `toComp_singleCodec` (`:98–110`): use `toComp_eq`, `toOracleAdversary_eq` and `singleCodec_decodeMove`.
2. `Bridges/QueryTree.lean`:
   - `simulate_ofComp_pure` (`:76–77`): use `simulate_pure/query`, `ofComp_apply`, `pure_bind` and `evalFn_*`;
   - `eval_eq_evalFn` (`:86–87`): use `eval_ret/query` and `evalFn_*`;
   - `simulate_eq` (`:103–108`): use `QueryTree.simulate_ret/query`, `treeImpl_apply`, `ofComp_apply` and `call_bind`.
3. `Bridges/Experiments.lean`: `acceptProb_eq` (`:119`) and `distAdv_eq` (`:127`) use `accept_eq` and `advantage_eq`.
4. `Bridges/Strategies.lean`:
   - `exec_turnParty` (`:138–145`): use `Party.exec_zero/succ`, the `step/close/endWith/swap` lemmas, `turnParty_zero`, `waitParty_*` and `pure_bind`;
   - `exec_eq_alt` (`:159`, `:163`): use `exec_zero`, `alt_zero` and `moverIsV_true/false`;
   - `exec_strategies` (`:183`): use `outP_eq`, `outV_eq` and `transcriptWith_eq`.
5. `Machines.lean`: `buildComp_costBoundedBy` (`:112`, `:116–117`) uses `costBoundedBy_pure` and `(costBoundedBy_query …).2`.
6. `Hopping.lean`: `expect_mono_of_allOutputs` (`:85`, `:88`) and `simulate_allOutputs_bad` (`:168`) use `allOutputs_pure/query`.
7. `Protocols.lean`:
   - `endWithT_ne_outOfFuel` (`:238–239`): use `allOutputs_pure`, and `Option.elim_none`/`Option.elim_some` instead of `simp [Option.elim]` (N5);
   - `execT_trace` (`:262–268`): use `allOutputs_pure.2 ⟨…⟩`.

That is 16 proofs (3 + 3 + 2 + 3 + 1 + 2 + 2) and about 60–80 changed lines.

### Size

| Part | Lemmas | Lines (with docstrings) |
|---|---|---|
| `Machines`, `BitCodec` (with F01), `Efficiency` | about 30 | about 200–240 |
| `Bridges/*` | about 17 | about 80 |
| `OracleComp`, `Protocols`, `OracleAdversary`, `PRF` (in the change set) | about 25 | about 120 |
| `Advantage`, `Simulate`, `Interaction` (outside) | about 10–15 | about 50–70 |
| **Total** | **about 75–85** | **about 450–510**, plus about 70 lines re-pointed |

About one maintainer day.

**Evidence to redo:**
- the replay of `Games/*`;
- the downstream of `PRF.lean`, `OracleAdversary.lean`, `Protocols.lean` and `OracleComp.lean`, which is already S2b's set;
- under R-04-2 option 1, also the downstream of `Advantage.lean`, `Simulate.lean` and `Interaction.lean` (the ZK modules);
- the axiom prints;
- check 8 (§5, N2);
- a rule-10 seal over the 16 re-pointed proofs.

### Effect on the prongs

- **Statements:** none. All additions are lemmas.
- **Prong B proofs** that read ch. 2–4's D8 definitions, re-pointable once the `Interaction.lean` lemmas land (9 sites):
  - `ObliviousTransfer.lean:155,211`: `simp [Protocol.outV, Protocol.transcriptWith, otProtocol, exec, …]`;
  - `ComposePhases.lean:530,542`: `show` through `viewP`/`viewV`;
  - `ComposePhases.lean:558,577`: `show` through `outP`/`outV`/`transcriptWith`;
  - `Yao.lean:548,555`: `yaoMain_outV/outP … := rfl`;
  - `Yao.lean:795,798`: `show (yaoMain …).outV/outP …`.
- **Prong B's own requested lemmas.** The Yao worker reported these. They are `private … := rfl` copies of another file's definition in `Yao.lean`, so they are themselves definitional closures. They should become shared lemmas beside their definitions, and the copies should be deleted:
  - `keyAt` (`Garbling.lean:192`): `keyAt_of_lt` and `keyAt_of_not_lt`, replacing `keyAt_eq'` (`Yao.lean:310`);
  - `garbledValues` (`Garbling.lean:236`): `garbledValues_eq`, replacing `garbledValues_eq'` (`Yao.lean:610`). Its only lemma, `garbledValues_getD`, is a correctness claim, not an equation.
  - `inputKeys` (`Garbling.lean:231`): `inputKeys_eq`, replacing `inputKeys_eq'` (`Yao.lean:615`);
  - `tableAt` (`Garbling.lean:213`): `tableAt_of_not`, the off-gate case, replacing `tableAt_eq'` (`Yao.lean:620`). `tableAt_gate` already exists.
  - `HybridProtocol.answersB` (`Hybrid.lean:91`): `answersB_eq`, which removes the `show` at `Yao.lean:738–739`.

  This is prong B's work for gate 06, not S2b's. Check 8 on prong B also lists 40 more of its definitions, among them `Garbling.lean`'s `argKeys`, `evalGate`, `garbledRow` and `garbledTable`.
- **Prongs A, C, D:** no current proof reads an S2b definition; their reductions are still sketches. The future fills of Thms 135.4, 137.2, 144.1 (prong A) and 168.2, 170.4, 175.9 (prong C) will need:
  - `toComp_eq`/`toCompOn_eq`;
  - the `buildComp` cases;
  - `bitCodec_*`, `encodeLog_cons` and `zeroBits_apply`;
  - `ofComp_apply`/`withLog_apply`.

  Prong C already states lemmas whose right-hand sides are `.pure (zeroBits _, s)` (`Composability/Defs.lean:156,162`; `PublicKey.lean:371,377`; `NonMalleable.lean:115`; `SimNonMalleable.lean:173`).

### Ruling: scope only (R-04-2, §6)

The rule is binding, so there is no "whether". The ruling decides whether the S2a and ch. 2–4 lemmas join this PR.

---

## 3. Minors

### F03: `PolyHandler.answer` defaults componentwise

- **Verdict: true. Severity: minor (agree).**
- **Evidence:**
  - `Efficiency.lean:91–92`: "A malformed output gives the all-`false` answer and state".
  - `:97–100`: after `pairDecode` succeeds, the code is `((decodeFin _ yw).getD (zeroBits _), (decodeFin _ sw).getD (zeroBits _))`. So `pairEncode [true] []` (with both lengths 1) gives answer `true` and state all-`false`.
- **Missed by the auditor (N6).** T2's handler defaults **jointly**. `InteractiveHandler.call` decodes `y ‖ s'` with one `decodeFin (dout + stateLen)` through `decodeBitMove` (`:182`), so a wrong total length gives all-`false` for both. T1 and T2 thus disagree on malformed output, and neither docstring says so.
- **Fix (recommended, docstring-only).** Reword `:91–92` to: "if `run`'s output is not a pair, both are all-`false`; otherwise each component of the wrong length is replaced by all-`false` independently". Add the `answer_*` equations of §2. State the joint default in `InteractiveHandler`'s docstring (`:145–150`).
- **Alternative (not recommended now).** Reject the whole pair, aligning with T2. That changes a T0 definition and would need a ruling. No consumer cares: handlers are the reduction's own code and never emit malformed output.
- **Effect on prongs:** none (no prong defines a handler yet).
- **Ruling:** no.

### F04: "up to `perCall(n)` rounds of `run`"

- **Verdict: true. Severity: minor (agree).**
- **Evidence.** `Efficiency.lean:146–147` says "One inner query `x` to oracle `i` is answered in up to `perCall(n)` rounds of `run`". But `call` is `buildComp … (H.perCall.eval n) []` (`:182–185`), and `buildComp` inspects one more move at fuel 0 (`Machines.lean:99–101`). So `p` outer queries take up to `p + 1` activations, and `perCall = 0` still gives one activation. `call`'s docstring "up to `perCall(n)` rounds against the outer oracles" (`:175–176`) is ambiguous. The field docstring (`:157`, "bound on outer queries") and the module doc (`:37`, "up to `perCall(n)` times per inner query") are correct.
- **Fix (docstring-only).** `:146–147`: "answered with at most `perCall(n)` outer queries, in at most `perCall(n) + 1` rounds of `run` (the last returns the answer or, with the budget spent, is cut off with the default)". The same for `:175–176`. The fill brief's replay bound should count `q(n)·(perCall(n)+1)` handler activations, which the auditor's construction outline already does.
- **Effect:** none on statements. T2's budget `q(n)·perCall(n)` counts queries and is correct.
- **Ruling:** no.

### F05: attestation 3 miscounts the axiom log

- **Verdict: true. Severity: minor (agree).**
- **Evidence.**
  - `evidence/axioms.log` has 237 entries, including `uprob_update_absorb'` (`:226`). Two contain `sorryAx` (T1 `:154`, T2), so 235 are clean. The pack says 236 and 234.
  - A comment-stripped count of the 22 changed files gives 237 public and 14 private theorem declarations (251 in all), matching the auditor.
  - The private ones cannot be `#print`ed from outside their file. Their admission-freeness is attested instead by the replay's per-module `sorry=` counts (`replay.log:732`, `Games/Efficiency … sorry=2`, all other S2b modules `sorry=0`).
- **Fix.** Reword attestation 3: "237 public theorems printed; 235 standard-only; T1 and T2 `sorryAx`. The 14 private theorems are covered by the replay's admission counts." When the evidence is refreshed (§7), also carry the source/olean provenance the auditor asks for. The replay header names `827ad8e1`, while the axioms and lint name `afe5982f`.
- **Effect on prongs:** none.
- **Ruling:** no.

### F06: inherited descriptions overstate their statements

**Verdict: true, all five points checked. Severity: minor (agree).** None is an F-1 regression: F-1's diff to these files touches only universe binders.

| Point | Evidence | Fix (docstring-only) |
|---|---|---|
| `multiMsgAdv_boundedBy` | `MultiMessage.lean:147–148`: "makes exactly `q + 1` queries"; the statement is `BoundedBy (q + 1)` | "at most `q + 1`" |
| `decodeFin_runAt_prfDec_of_not_wf` | `:467–468`: "a ciphertext `w` that is not a pair of `n`-bit strings"; the premise is the projected lengths, and `w = []` at `n = 0` is not a pair but meets them | "whose two projections are not both `n` bits long" |
| `pairFstD_pairFstD_histBlock` | `MultiMessageLemmas.lean:299`: "the two components … the query and the answer"; the statement gives the query only | "the query component" (or add the answer projection) |
| `take_drop_ofFn_blocks` | `:377–379`: "(private copy …)" but public. It is also an unledgered duplicate (N4). | see N4 |
| `exists_queryChain_nuppt` | `:618–619`: "asks `ρ₀, …, ρ_{q(n)}`"; the statement gives evaluation equality only | "whose evaluation against any oracle `g` is …" |
| `SubHybrids.tableDist`, `GGM.ggmDist` | `SubHybrids.lean:103`, `GGM.lean:194`: "*Cost.* … at most `q` evaluations of `G`" holds only when `A.BoundedBy q` | add "for `A` bounded by `q`" |

- **Where to fix.** The files are in S2b's change set (F-1), but their packs are 03d (`MultiMessage`) and 03j (`MultiMessageLemmas`), both pending. Recommended: fix the docstrings in S2b and tell the 03d and 03j pack authors, so those auditors do not re-raise them.
- **Effect on prongs:** none.
- **Ruling:** no.

---

## 4. Severities at a glance

| # | Verdict | Auditor | Proposed | Fix kind | Ruling |
|---|---|---|---|---|---|
| F01 | true | major | major | definition change plus new lemmas | R-04-1 (light) |
| F02 | true, understated | major | major | new lemmas, 16 proofs re-pointed | R-04-2 (scope) |
| F03 | true | minor | minor | docstring plus equations | no |
| F04 | true | minor | minor | docstring | no |
| F05 | true | minor | minor | evidence wording | no |
| F06 | true | minor | minor | docstrings | no |
| N1 | missed | — | **major** | statement change before the fill (or wrappers) | R-04-3 |
| N2 | missed | — | minor | evidence (lint and seal) | no |
| N3 | missed | — | minor | docstring | no |
| N4 | missed | — | minor | ledger entry | no (ledger) |
| N5 | missed | — | minor | proof (folded into F02) | no |
| N6 | missed | — | minor | folded into F03 | no |
| N7 | missed | — | minor | evidence (folded into N2) | no |

---

## 5. What the auditor missed

### N1 (proposed major): T1/T2 do not cover the reductions they are cited for

The auditor's "Exact limitations" 1–4 (findings lines 179–186) are correct, but were not counted ("possible missing future prongs are not counted as additional present majors"). The brief's item 3 asks exactly this question ("T1 and T2 must be usable contracts … what a reduction needs"). The coverage is already claimed in two places:
- `Efficiency.lean:44–47`: T2 is what "the PRF MAC's distinguisher, hash-and-sign's forger, the CPA and CCA reductions" need;
- the pack: T2 is "needed by the reductions of Thms 135.4, 144.1, 168.2, 170.4".

The prongs' sketches build on that claim. Five gaps:

1. **No adversary input.** T1 and T2 simulate `A.toComp` (`Efficiency.lean:136`, `:224`). The signature and public-key games run `A.toCompOn … pk`:
   - prong A: `Authentication/Defs.lean:207`;
   - prong C: `Composability/PublicKey.lean:391`, `NonMalleable.lean:100`, `SimNonMalleable.lean:218,260`.

   In a reduction the input is computed from the reduction's input `z` and seed `ω`. Lamport builds `pk` from `y` and its coins; hash-and-sign's `B` and `C` build `⟨pk, i⟩`.
2. **No final state and no finalization.** T1 hides the state (`∃ s`) and T2 projects it away (`res.1`). Several reductions post-process `A`'s output with the state or seed, and sometimes with more oracle queries:
   - the PRF MAC's distinguisher queries at `A`'s message and checks freshness against the log;
   - Lamport outputs `σ'_i` or aborts;
   - hash-and-sign outputs `(m, m′)` or `(h_i(m′), σ′)`;
   - Thm 175.9 (⇒) asks ℓ more `Dec` queries and runs `D`;
   - `padded_cpa` flips or zeroes the guess.
3. **Normalized output only.** T1 gives `padFin dα (B.runAt …)` (`:138`). An inverter is read through `decodeFin` (`NUPPT.inverter`, `Adversary.lean`), so Lamport's `B` needs exact output.
4. **No bridge to the PRF assumption.** `PRF F` (via `OracleEnsemble.Indist`) quantifies over `D.toOracleAdversary`, which is `D.toComp (singleCodec ℓ₁ ℓ₂)` by `toComp_singleCodec`. T2's `B` is a `toCompOn (bitCodec …) z` machine. The two differ in:
   - the index type (`Unit` against `Fin 1`);
   - the query word (`⟨[false], x⟩` against `⟨[false], ⟨[], x⟩⟩`);
   - the verdict word (`[true, b]` against `⟨[true], [b]⟩`);
   - the log entry (`⟨x, y⟩` against `⟨[], ⟨x, y⟩⟩`);
   - the input (none against `⟨z, log⟩`).

   No lemma relates them. Every PRF-based reduction needs one: 135.4, 168.2 and 170.4.
5. **T1 is cited where only T2 can apply.** T1's handler targets `unifSpec` and answers with `.pure` (`:105–108`), so it cannot query any oracle. Yet "by T1" is cited for oracle-forwarding reductions:
   - `PRFMAC.lean:111` ("the handler forwarding queries");
   - `PRFScheme.lean:76` ("querying its own oracle … efficiency by T1");
   - `CCA2Scheme.lean:300` ("answers `Enc′` and `Dec′` with its oracle … by T1");
   - `NonMalleable.lean:125` ("asks CCA2's `Dec` … `D` is run by T1's handler").

**What each reduction needs:**

| Reduction (prong, file:line) | Cites | Input | Final/state | Exact output | Codec bridge | Oracle (T2) |
|---|---|---|---|---|---|---|
| Thm 135.4 PRF MAC (A, `PRFMAC.lean:111`) | T1 | — | yes (final query, log) | — | yes | yes |
| Thm 137.2 Lamport (A, `Lamport.lean:463–464`) | T1 | yes | yes (abort, `σ'_i`) | yes (inverter) | — | — |
| Thm 144.1, `B` (A, `HashAndSign.lean:266–267`) | T1 | yes | yes | — | — | — |
| Thm 144.1, `C` (A, `HashAndSign.lean:271–272`) | T2 | yes | yes (`h_i(m′)`) | — | — | yes |
| Thm 168.2 CPA/CCA1 (C, `PRFScheme.lean:76`) | T1 | — | — (`b` fixed in the handler) | — | yes | yes |
| Thm 170.4 (C, `CCA2Scheme.lean:300`) | T1 | — | — | — | yes | yes |
| Thm 175.9 (⇒) (C, `NonMalleable.lean:125`) | T1 | yes | yes (ℓ `Dec` queries, then `D`) | — | — | yes |
| `padded_cpa` (C, `PublicKey.lean:417`) | T1 | yes | yes (flip or zero) | — | — | — |

**Why major.** The coverage claim at `Efficiency.lean:44–47` is materially misleading. T0–T2 freeze at the fill's issue (fill brief, ground rule 1). A later change costs a re-freeze and a re-fill, or one machine construction per reduction (several hundred lines each, by the S2b-efficiency note's own count for ch. 2–4). No present statement is wrong (T1/T2 are true candidates), so it is not a blocker.

**Fix (recommended, R-04-3 option 1): extend before issue.** A sketch:

```lean
structure PolyHandler (k : ℕ) (din dout : Fin k → PolyExpr) where
  stateLen seedLen : PolyExpr
  init : ∀ n, Fin (stateLen.eval n) → Bool
  run : List Bool → List Bool
  poly : PolyTimeComputable run
  /-- The adversary's input, from `⟨1^n, ⟨z, ω⟩⟩`. -/
  advIn : List Bool → List Bool
  advIn_poly : PolyTimeComputable advIn
  /-- The reduction's output, from `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, a⟩⟩` (final state, adversary's output). -/
  out : List Bool → List Bool
  out_poly : PolyTimeComputable out

-- T1': exact output, adversary with input
∃ B : NUPPT, ∀ n, ∃ φ, ∀ z ω r, ∃ a s,
  simulate (H.impl n z ω) (A.toCompOn codec n (q.eval n) (H.advIn (seedIn n z ω)) r) (H.init n)
    = .pure (a, s) ∧
  B.runAt n z (φ (ω, r)) = H.out (pairEncode (seedIn n z ω) (pairEncode (List.ofFn s) (List.ofFn a)))
```

- **T2'** uses the same fields, with an interactive finalization: one more `call`-like phase `H.finish n z ω s a` on the outer oracles, with budget `finCall` and a `dβ`-bit output. Its conclusion is `(simulate …).bind (fun res => H.finish n z ω res.2 res.1) = B.toCompOn (bitCodec din' dout' dβ) n (q·perCall + finCall) z (φ (ω, r))`.
- **Two companions:**
  - `exists_toCompOn_of_toComp`: an input-free adversary is an input-taking one that ignores its input. It follows from `exists_comp` with `pre = pairSndD`; the coins are unchanged.
  - **T4**, the codec bridge: `∀ B, ∃ B'` with `B'.coins = B.coins` such that `(B'.toOracleAdversary n ℓ₁ ℓ₂ q r).eval f` equals the evaluation of `B.toCompOn (bitCodec (fun _ : Fin 1 => ℓ₁) (fun _ => ℓ₂) 1) n q [] r` against `fun _ => f`, read at bit 0. An eval-level equality suffices for `oracleDist`/`prfAdv` and avoids relabelling `Unit` against `Fin 1`.
- **Cost.** T0 gains 4 fields per handler structure and one definition. T1/T2 are restated (still `sorry`), and T4 and the companion are stated. The fill grows by an estimated 400–700 lines (input threading, finalization replay, T4's re-encoding of logs). The prong sketches above re-cite T1′/T2′/T4. No prong statement text changes.

**Effect on the prongs.** Docstring sketches only, at the eight sites listed. Their theorems are `sorry` under sketches.

### N2 (minor): the lint attestation omits check 8; no rule-10 seal evidence (with N7)

- **What the pack ran.** Attestation 4 (`evidence/lint.log`: "0 findings in 22 files") ran `scripts/style_lint.py`. That is main's per-file linter, with checks for docstrings, sketches, headers and size, but no check 8. `workflow.md` §6 names `scripts/campaign_style_lint.py` as the campaign lint, and says of check 8: "a landing adds no name to it".
- **What check 8 shows** (`--check8b`, `TCSlib/Cryptography`), at `a3c5fa8b` against `afe5982f`. S2b removes `invProb`, `predProb` and `uexp` (F-3, done) and **adds 16 names**:
  - `BitCodec`: `bitCodec`, `zeroBits`;
  - `Bridges/Experiments`: `acceptGame`;
  - `Bridges/Machines`: `singleCodec`, `toHist`;
  - `Bridges/QueryTree`: `OracleComp.evalFn`, `treeImpl`;
  - `Bridges/Strategies`: `waitParty`;
  - `Efficiency`: `answer`, `call`, `impl` ×2, `input` ×2;
  - `Machines`: `encodeLog`;
  - `OracleAdversary`: `induct`.
- **Name-only passes.** Check 8 accepts any lemma whose name starts with the definition's, so 8 more definitions pass on a name alone:
  - `buildComp` (`buildComp_costBoundedBy`);
  - `NUPPT.toComp` and `toCompOn` (`_costBoundedBy`);
  - `decodeIdx` (`decodeIdx_replicate`);
  - `decodeBitMove` (`_query`/`_ret`);
  - `turnParty` (`turnParty_succ`);
  - `alt` (`alt_succ_last`);
  - `AllOutputs` (`allOutputs_true`).

  This is F02's list in mechanical form.
- **Fix.** Re-run attestation 4 with `campaign_style_lint.py --check8b`. Its check-8 diff against the base should list no new name after F02. Add a rule-10 seal log (WORKFLOW rule 10: `attribute [local irreducible]` on every consumed definition, with controls) for the 16 re-pointed proofs.

### N3 (minor): `Bridges/Strategies.lean` promises results that are not there

- `:50–51` says: "The traced and probabilistic forms (views, and tapes sampled first) are stated in a later part of this file." The file ends at `exec_strategies` (`:173–189`).
- B4's design theorems 2–4 (traces, probabilities, fuel; `design/B4-strategy-embedding.md`) are not stated. The auditor noted that they are absent, but not that the docstring claims them.
- Fix: "are planned (B4 design note, theorems 2–4) and not yet stated". No prong uses B4 yet (grep for `turnParty`, `exec_strategies` and `Bridge.` in all prongs: none).

### N4 (minor, inherited): an unledgered duplicate

- `MultiMessageLemmas.lean:379`, `TCSlib.Cryptography.MultiMsg.take_drop_ofFn_blocks`, has the same statement as `EnsemblesLemmas.lean:385`, `TCSlib.Cryptography.EnsembleLemmas.take_drop_ofFn_blocks`. Its docstring calls it a "private copy", but it is public.
- It is not in `duplication-ledger.md` (DL-1 to DL-8). It predates S2b.
- Policy §1, "Duplication": "every instance … must be human-approved".
- Fix: ledger entry DL-9 (keep the `EnsembleLemmas` copy and point `MultiMessageLemmas` at it), routed to pack 03j. Correct the docstring now (F06).

### N5 (minor): a core definition passed to `simp`

- `Protocols.lean:239`: `cases p.1 <;> simp [Option.elim]`. The 2026-10-23 rule allows core definitions only in `rfl`/`decide`/`show`.
- Fix: `Option.elim_none`/`Option.elim_some` (core lemmas). This is folded into F02's re-point 7.

### N6 (minor): T1's and T2's malformed-output defaults disagree

Folded into F03.

### Not findings (checked)

- **No new `@[simp]`.** The diff `a3c5fa8b..afe5982f` adds none.
- **The facades are complete.** `Games/Bridges.lean` imports all seven S2b modules, and `TCSlib.lean:60–61` imports `Games` and `Games.Bridges`. The facade's contents line for `Efficiency` names only T1; the auditor's editorial note stands, and the fix is to add T2.
- **The replay covers T2.** `replay.log:732` shows `Games/Efficiency … sorry=2`, recorded after the T2 commits, despite the `827ad8e1` header.

---

## 6. Rulings for the user (multiple choice; recommended option first)

**R-04-1 (F01): the unary index of the shared codec.**
1. **Strict unary decoding, with converse lemmas (recommended).** `decodeIdx` checks `iw = List.replicate iw.length true`. Add `decodeIdx_eq_some_iff`, `decodeIdx_eq_none_iff`, `decodeBitMove_eq_query_iff` and `decodeBitMove_of_not_canonical`, plus optionally `encodeBitMove`.
   - *Cost:* about 60–90 lines in `BitCodec.lean`, one lemma re-proved, and a T0 change before the fill is issued.
   - No prong edits; no change of meaning for any ∀-adversary notion.
   - The fill adds one all-`true` check.
2. **Keep length-only decoding, and document it.** The grammar becomes "any word of length `i < k` names oracle `i`", with converse `decodeIdx k iw = some i ↔ iw.length = i`.
   - *Cost:* docstrings at `BitCodec.lean:20–24,59,73–75` and `Efficiency.lean:149`.
   - The codec is no longer injective on accepted words.
   - It departs from D7's strict-format convention, under which ch. 2–4's `decodeOracleMove` is exact.

**R-04-2 (F02): the scope of the equation lemmas in this PR.**
1. **Everything S2b's proofs consume, in this PR (recommended).**
   - S2b's own definitions;
   - `PRF.lean`, `OracleAdversary.lean`, `Protocols.lean` (S2a definitions) and `OracleComp.lean`, already in the change set;
   - `Advantage.lean`, `Simulate.lean` (S2a) and `Interaction.lean` (ch. 2–4), which join it;
   - all 16 proofs re-pointed.

   *Cost:* about 75–85 lemmas, about 450–510 lines, about 70 lines re-pointed, and the replay extended to `Interaction.lean`'s downstream. Packs 03d and 03e get small additive deltas (`rfl` lemmas only). Prong B can then re-point its 9 D8 sites.
2. **S2b's own definitions and the files already in the change set now; `Advantage`, `Simulate` and `Interaction` in a follow-up PR before gate 06.**
   - *Cost:* `acceptProb_eq`, `distAdv_eq`, `simulate_ofComp_pure`, `simulate_eq` and `exec_strategies` keep reading those definitions until then. That is a recorded debt line the user acknowledges, and `Bridges/{Experiments, QueryTree, Strategies}` must be re-pointed twice.
3. **Acknowledge the whole debt and close.**
   - *Cost:* not recommended. The efficiency fill must then break rule 10 or carry private copies (each a disclosed duplicate), and every prong reduction repeats this.

**R-04-3 (N1): T1/T2 as contracts for the cited reductions.**
1. **Extend T0–T2 before the fill brief is issued (recommended).**
   - adversary input from a polynomial-time function of `⟨1^n, z, ω⟩` (`A.toCompOn`);
   - a polynomial-time finalization on (final state, output), interactive in T2 with its own budget;
   - exact output in T1;
   - companions `exists_toCompOn_of_toComp` and T4 (the codec bridge to `toOracleAdversary`).

   *Cost:* T0 gains 4 fields per handler and one definition; T1/T2 are restated (still `sorry`); 2 statements are added; the fill grows by about 400–700 lines; a delta re-audit of `Efficiency.lean`. The eight prong sketches are re-cited.
2. **Keep T1/T2 and add wrapper targets T4 (codec bridge), T5 (adversary input) and T6 (finalization and exact output).**
   - *Cost:* three more machine-level statements, each with its own functional equation by induction on the budget, plus composition of machines. More total work than option 1, and every reduction composes three or four results.
3. **Accept as a scope limitation.** Correct `Efficiency.lean:44–47` and the eight sketches to say what T1/T2 do not cover.
   - *Cost:* prongs A and C build their own machines for Thms 135.4, 137.2, 144.1 (×2), 175.9 and `padded_cpa`, and a PRF codec bridge for 135.4, 168.2 and 170.4. That is several hundred lines each: the per-reduction cost the efficiency route was meant to remove.

---

## 7. Proposed closing condition for gate 04

1. **F01** applied per R-04-1: the converse lemmas, and `decodeBitMove_of_not_canonical` proved.
2. **F02** applied per R-04-2: the lemmas of §2, and the 16 proofs re-pointed.
3. **R-04-3** ruled. Under option 1, T0–T2 restated and T4 stated before the fill brief is issued.
4. **F03, F04, F06, N3** docstrings fixed. N4 recorded in the ledger as DL-9 (pack 03j).
5. **Evidence refreshed at the new head:**
   - the replay, with source and olean provenance;
   - axiom prints with corrected counts (F05);
   - `campaign_style_lint.py --check8b` with no new check-8 name against the base (N2);
   - a rule-10 seal log for the re-pointed proofs (N2, N7).
6. **A delta re-audit** of `BitCodec.lean`, `Efficiency.lean` and the new equation lemmas. The equation lemmas are `rfl`, so a statement-only check suffices.

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

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
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

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

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
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

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
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).
