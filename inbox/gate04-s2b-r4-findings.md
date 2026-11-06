# Gate 04 — S2b round 4 external audit findings

**Verdict: DO NOT CLOSE.**  
**0 blockers, 1 major, 1 minor.**

The thirteen re-proofs preserve their statements, and both `def` → `abbrev` changes are sound under the supplied policy. The remaining major is the exclusion boundary: twelve declarations labelled `SAME` have changed universe binders inherited from surrounding `variable` commands. Several still fail the supplied plain seal; others explicitly unfold foreign definitions. Consequently, the claim that no exclusion concerns a declaration changed by #195 is false.

**Audited head:** `a588adfed01eefe6971abd0846e3938ad02e8624`, [PR #195](https://github.com/Shilun-Allan-Li/tcslib/pull/195).  
**Round 3 head:** `27ae72da62119ebdde380b8cb2d8c183b59fa2bf`.  
**PR comparison base:** `a3c5fa8b72e50939822f22364647dc844a3914a0`.  
**Bundle:** 33 sections; SHA-256 `6b19c92c0f94cb5bce6f39d9bee681b8ec7674ccfea3eea8054d94c33070dabf`. No expected round 4 bundle digest was supplied.  
**Source PDF:** Pass–shelat, third edition; SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`.

The seven bundled Lean files match the pinned GitHub blobs byte for byte. The repair diff reverse-applies cleanly, and all seven reconstructed old blobs match its old hash prefixes. The [pinned round 3-to-4 comparison](https://github.com/Shilun-Allan-Li/tcslib/compare/27ae72da62119ebdde380b8cb2d8c183b59fa2bf...a588adfed01eefe6971abd0846e3938ad02e8624) confirms two commits and seven changed files. I also fetched the pinned sources needed to check the exclusions against the PR comparison base. Source paths below are relative to `TCSlib/Cryptography/`; evidence paths are relative to `briefs/pass-shelat-ch5-8/gates/04-s2b/`.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R4-01 | **Major** | `evidence-r4/exclusions.md` §§A–B and Check; `resolutions-r3.md:13`; `Pseudorandom/Functions/{Defs,GGM,SubHybrids}.lean` · declarations listed below | All excluded declarations are unchanged by #195; there are zero exclusions on added or changed declarations. | `Defs.lean:53` changes the ambient types of `I,O` from `Type*` to `Type`; `GGM.lean:70` does the same for `S`; `SubHybrids.lean:70` does the same for `P,S,V`. These binders enter the excluded theorem statements even though the text beginning at `theorem` is unchanged. Six affected declarations have eleven declaration/definition pairs in §A; eight have eighteen explicit-unfold occurrences in §B, giving twelve distinct declarations. For example, `prfAdv_eq` and `prfAdv_nonneg` remain unsealed for foreign definitions and fail without those entries (`seal-plain.log`, source lines 77 and 82). | Make the change classifier account for ambient variables and universe binders, preferably by comparing elaborated signatures as well as declaration text. Re-prove the affected consumers through published equations and remove their exclusions; publish missing equations at their definitions. Regenerate the exclusion ledger, scans and seals. An explicitly accepted exception for these **changed** declarations would instead require an accurate debt statement; the present unchanged-only claim does not supply it. |
| R4-02 | Minor | `evidence-r4/tool-collect_body.lean.txt:26–51,137–158`; `tool-scan.py.txt:57–62,183–191`; `resolutions-r3.md:13` | The automatic collector and source scan establish complete coverage of every foreign definition a declaration can reduce. | The collector neither seals nor traverses foreign `def-aux` bodies. Its auxiliary-name test also classifies private names as auxiliary before the `def-private` branch can record them. Thus transparent paths through such helpers are not generally closed. The source scanner misses advertised syntax: its bracket parser returns `None` for `nth_rw 1 [Foreign.d]` and `nth_rewrite 2 [Foreign.d]`; its `unfold` parser ignores names on following lines. I reproduced these parser results directly. These are limits of the evidence, not an additional demonstrated offending proof in this delta. | Describe the result as coverage of the collected candidates and inspected syntax, not a universal certificate. Traverse unsealed computational helpers or conservatively collect all relevant sealable definitions; use syntax-aware resolution for explicit unfolds. Preserve the candidate tables and supporting drivers with the evidence so the precise run is reproducible. |

R3-01: **fixed** — `expect_bind` now uses `OracleComp.pure_bind` and `expect_pure`; `Games/Probability.lean` is included at the final head, passes with no exclusion, and fails at the old `rfl` in the control. The broader exclusion claim is addressed by R4-01.

R3-02: **fixed** — the pack and file list correctly identify 26 Lean files after excluding `TCSlib.lean`; the pinned PR comparison agrees.

F02: **not resolved** — the round 4 re-proofs are adequate, but the asserted unchanged-only exclusion boundary does not hold. See R4-01.

N7: **fixed** — the missing final-head file coverage and control evidence are now supplied for all 26 files, including `Probability.lean`. This resolves the missing-run issue; it does not turn the bounded checks into a blanket certificate or validate the exclusions in R4-01.

**Why the `SAME` classification fails.** I checked all 48 §A declaration spans and all 35 distinct §B declaration bodies against the comparison-base sources: their declaration text is indeed unchanged, excluding docstrings. That check is insufficient to establish unchanged statements. The following enclosing commands changed in the same files:

| File | Comparison base | Audited head |
|---|---|---|
| `Pseudorandom/Functions/Defs.lean:53` | `variable {K I O ρ σ σ' γ : Type*}` | `variable {K ρ σ σ' γ : Type*} {I O : Type}` |
| `Pseudorandom/Functions/GGM.lean:70` | `variable {S ρ : Type*} {n : ℕ}` | `variable {S : Type} {ρ : Type*} {n : ℕ}` |
| `Pseudorandom/Functions/SubHybrids.lean:70` | `variable {P S V ρ : Type*} …` | `variable {P S V : Type} {ρ : Type*} …` |

These are genuine signature changes: the old `OracleAdversary` and `QueryTree` accept query and answer types in arbitrary universes; the head restricts those types to universe zero. This is the previously approved F-1 restriction, not a new objection to that restriction. The issue is applying the exclusion rule consistently. `REPORT.md:12–13` itself counts the explicit universe-binder changes in `MultiMessageLemmas.lean` as declaration changes requiring re-proofs. Moving the binders into a surrounding `variable` command does not make their effect disappear.

The affected entries already present in the ledger are:

| File | §A: definitional reads | §B: explicit unfolds |
|---|---|---|
| `Defs.lean` | `prfAdv_eq`, `prfAdv_nonneg` | None |
| `GGM.lean` | `hybridProb_top`, `hybridProb_level` | `hybridProb_eq_level_prg`, `hybridProb_eq_level_random`, `ggm_prfAdv_le` |
| `SubHybrids.lean` | `subHybridProb_zero`, `subHybridProb_top` | `acceptProb_tableDist_prg`, `acceptProb_tableDist_uniform`, `subHybridProb_zero`, `subHybridProb_top`, `table_hybrid` |

The supplied plain seal independently records failures for all six §A declarations above. Explicit examples in §B include `rw [hybridProb, acceptProb, acceptProb]` at `GGM.lean:148` and `rw [prfAdv, distAdv, …]` at `GGM.lean:236`. The definitions `acceptProb`, `distAdv` and `prfAdv` are foreign to that file. The body of `prfAdv_eq` still ends in `rfl`, reading imported `distAdv`, `acceptProb` and `oracleDist`; `prfAdv_nonneg` still uses `abs_nonneg _`, reducing imported `distAdv` through local `prfAdv`.

Useful existing interfaces include `acceptProb_def`, `distAdv_def`, `oracleDist_apply`, and `OracleAdversary.boundedBy_iff`. For example, `prfAdv_eq` can be re-proved using its local definitions and the foreign defining equations; `prfAdv_nonneg` can then rewrite with `prfAdv_eq`. Consumers of `randomFunction` need its published equation. These are repair directions, not patches compiled by this audit. The major concerns publication-policy closure, not mathematical falsity or a new admission.

**Review of the actual repairs.** No theorem statement, hypothesis, docstring, `simp` attribute or admission changes in the thirteen re-proofs.

| Repair group | Assessment |
|---|---|
| `ProbComp.expect_bind` | The pure case rewrites the bind with `pure_bind` and the right-hand expectation with `expect_pure`; both sides become the same expectation. |
| Three `Party` examples; `stepT_fst`, `closeT_fst`, `execT_outcome` | The former implicit bind reductions are replaced by `OracleComp.pure_bind`. Execution, stepping, closing and traced-execution definitions used directly are local to `Protocols.lean`; the foreign sum/option operations are read through their equations. |
| `QueryTree.evalLazy_congr`, `evalLazy_comp`, private `uprob_evalLazy_aux` | Query-bound hypotheses are opened through `boundedBy_query_succ`; simulation and evaluation are read through `simulate_ret/query` and `eval_ret`. The induction calls, budgets and distributions are unchanged. |
| `boundedBy_chainTree` | Unfolds only the local chain construction, then uses `boundedBy_ret` and `boundedBy_query_succ`. |
| `acceptProb_oracleDist_congr_equiv`, `prfAdv_congr_equiv` | Uses the probability/distinguisher equations. Applying coin relabelling to the identity sampler gives the random-table comparison needed by `prfAdv_eq`; no foreign `randomFunction` reduction is required. |

The lazy-sampling interpretation remains consistent with Pass–shelat §3.8.1, book p. 95 / PDF p. 107: fresh answers are sampled on first occurrence and repeated queries reuse them, matching a uniform function table. I checked the supplied page, including its rendering. The delta does not alter that theorem's statement or the many-message construction of Theorem 99.2.

**The two abbreviations.** `QueryImpl` retains exactly its dependent-function body; `OracleSpec.add` retains exactly the pair of `Sum.elim` projections. Only the declaration keyword changes. This changes elaboration transparency, not the mathematical types or kernel-level definitional content. Treating these two constructors as notation is permitted by policy §1 and the recorded R-04-4 ruling. `queryImpl_def` states the entire function type; `add_dom_inl`, `add_dom_inr`, `add_rng_inl`, and `add_rng_inr` cover both fields and both index constructors. They remain valid reading interfaces. No new `simp` attribute is introduced. Section C is legitimately empty after this change.

**What the seal does and does not establish.** The collector improves substantially on a hand-written name list: it inspects declarations' types and values, follows foreign instances and reducible declarations, adds the statements of directly used foreign theorems, and includes source-listed rewriting lemmas whose use may leave no proof-term reference. The seal then recompiles each source with the collected definitions locally irreducible. Its error handling distinguishes a failed seal insertion from an ordinary proof failure, and the logged exclusion spans correspond to individual declarations.

It is not an exhaustive reduction-dependency analysis. In addition to R4-02, computations inspected only during elaboration can disappear from the resulting term; an incomplete source resolver cannot recover all such uses. The scanner's constant table is restricted to TCSlib, so it also does not enforce policy §1's separate ban on explicitly unfolding core/Mathlib definitions. These limitations do not identify another offending use in the thirteen repaired proofs, which were inspected directly.

The supplementary round 3 union check is useful: it adds six missing file/name pairs across five files, and all five runs pass. This supports those extra tests, not a completeness theorem. The advertised “complete” evidence is also not a standalone runnable package: candidate files, `unseal.json`, `declchanges.tsv`, `declx.py`, and `run_collect.sh` are referenced but not bundled. In particular, the declaration classifier and wrapper-extents implementation cannot be audited from their source here; the logged extents and pinned declaration texts were checked instead. The claimed one-name-at-a-time minimality of exclusions is not independently established by the supplied minimization logs, which are absent.

The control wording needs qualification. `seal-control-base.log` reports `MultiMessageLemmas.lean` as **PASS** despite its two repaired explicit unfolds; `scan-base.log` catches those four foreign-definition mentions, and the head scan removes them. The control also fails at consumers of the former non-reducible type formers and has cascading errors. Thus “fails exactly at the re-proved declarations” is not a literal description of that log. The combined seal/source-scan evidence supports the repairs.

**Execution evidence and limits.**

| Evidence | Checked result |
|---|---|
| Final-head seal | 26 distinct file rows, all PASS; all 14 `Games/` files have no exclusion. There are 48 declaration-scoped unseal entries. |
| Plain seal | 18 files pass and 8 fail; all 14 `Games/` files pass. Its failures confirm that the remaining exclusions are substantive. |
| Base control | 17 files pass and 9 fail; `expect_bind` fails at its old pure-case `rfl`. |
| Exclusion counts | §A contains **102 declaration/definition pairs across 48 declarations**, not merely 48 individual reads. §B contains 75 explicit-unfold occurrences across 35 declarations. The R4-01 affected subset is eleven pairs and eighteen occurrences, respectively. |
| Source scan | 80 explicit-definition occurrences at the head versus 84 at round 3; 21 generated-equation references in each. The four removed occurrences are the two repaired `MultiMessageLemmas` proofs. |
| Replay | 23 result rows for the first commit; 30 for the final replay, including `Checks`. All report zero exit status and errors. The final count is 29 ordinary modules plus `Checks`, as the pack states. |
| Admissions | Replay reports four in `Games/Efficiency` and zero elsewhere in these runs. No `sorry` occurs in the seven supplied Lean source files. The four expressly deferred efficiency proofs are unchanged. |
| Axioms | 155 distinct public-theorem entries, all using only subsets of `propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx`. This includes the name ending in an apostrophe and the multiline axiom entry. The earlier printout for files untouched by these two commits remains prior-round evidence. |
| Lint | Zero findings in the seven refreshed-file rows and the subsequent complete 26-file sweep; check 8b reports 0 FAIL and 0 WARN over 14 `Games/` files. |

No `lean` or `lake` executable was available in this audit environment. The compilation, axiom, lint and seal results above are **inspected maintainer execution evidence**, not fresh Lean executions. I independently checked source/blob identities, the reverse diff, proof changes, exclusion text and ambient binders, log accounting, the scanner's demonstrated parser gaps, and the cited PDF passage. No mathematical regression was found in the two-commit delta. The four deferred efficiency fills, prior recorded documentation/duplication debts, and the remaining ch. 2–4 cleanup are not certified as complete.

**Notation:** `Type*` is Lean syntax for a type at an inferred universe level; `Type` means `Type 0`. `SAME` is the supplied ledger's classification. Other symbols and names are identifiers already present in the audited material.
