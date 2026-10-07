**Chapter 2, Phase 1, round 3 — independent adversarial gate audit**

Audited material: the attached `ch2-phase1-round3-bundle.md`, labelled commit `79128c7a` on `complexity/arora-barak-ch1`. Intended destination: `audits/ch2-phase1-round3-findings.md`.

**The narrow gate condition is met for the supplied snapshot. Blockers: none (0). Majors: none (0). Minors: 1. Notes: 2.** The three round-2 majors are resolved. One rejection branch from the cited padding construction remains implicit in its local transcription; it needs a short clarification, not another construction or statement change.

This audit covers only the requested sketches, HALT docstring, plan synchronization, resolution table, and attestations. Previously certified definitions and statements were not reopened. This is a mathematical and source-level sketch audit, not a Lean proof submission or certification of repository execution. The human-review question's disposition remains untouched.

The bundle contains 40 campaign modules plus `TCSlib.lean`, both plans, policy, both earlier packs, and both earlier findings reports. Its SHA-256 is `08ed332c0256af58d3c98a7f10bbe885e05b13ac656c82ec17656a52a7b865de`.

**Textbook evidence.** No finding below relies on memory of the textbook. Definition 2.1, Exercise 2.1, Claim 2.4, and Exercise 2.8 are the supplied pack's citations; their published wording, numbering, and page references were not independently checked. The 2009 textbook pages are not attached. The earlier reports record consulting an authors' draft; that historical consultation is not fresh source verification in this round. The narrow conclusions below follow from the attached declarations, repaired prose, and round-2 derivations.

`ClassNP/` abbreviates `TCSlib/Complexity/ClassNP/`. Source line numbers are relative to each extracted file, starting after its bundle separator and separating blank line.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `ClassNP/NP.lean:115` · `mem_NP_iff_exists_length_le`, reverse sketch | The new verifier can recover a unique split on its arbitrary input. | Strict increase gives **at most one** solution to `n + R n = m`, not existence. Since `R n ≥ 1`, input `y = []` has no solution. The local sketch says to recover the split but omits the explicit failure branch. Its citation to round 2's malformed-input coverage supplies the intended behavior: round 2 explicitly says to reject if none exists. This is a local edge-case transcription omission, not a defect in the adopted construction or theorem. | After the bounded search, add: “Reject if no such `n` exists; otherwise split at that unique `n`.” |
| 2 | note | `ClassNP/EXP.lean:86` · `NP_subset_EXP` | Adding output isolation completes the enumerator's substantive obligation list at statement phase. | The sketch now names width evaluation, fixed-width overflow, retained input/candidate, verifier-call simulation, captured output, redirected halt, complete restart, and a timed loop invariant; width zero still executes one call. The cited capture precedent suppresses physical output even on the source halting transition. | No repair required. Prove these named machine and timing contracts during fill; the precedent is a construction pattern, not an already available repeated-call theorem. |
| 3 | note | Round-3 pack · attestations 1–4 | The current inventory is independently checkable; historical and execution claims require separate evidence. | Static inventories and the repaired passages are reproducible. A single source snapshot, without the parent tree, Git diff, pinned build environment, scripts, or execution logs, cannot establish the claimed zero code delta, fresh elaboration, or lint results. | No mathematical repair required. Retain the distinction between reproduced source facts and maintainer execution/history claims in the attestation accounting below. |

**Resolution table, checked row by row.** “Verified” here concerns the supplied snapshot, not an authenticated commit comparison.

| Round-2 finding | Round-3 assessment |
|---|---|
| 1 — inadmissible Exercise-2.1 padding length | **Major resolved.** `NP.lean:110` uses precisely `(C+1)(n+1)^c`, with marker room, split uniqueness, last-`true` stripping, the original bound, and both witness directions. All cited edge cases work. Finding 1 above records the one locally implicit rejection branch. |
| 2 — omitted enumerator output isolation | **Resolved.** `EXP.lean:101` explicitly captures the bit in finite control, suppresses emissions, returns from the simulated halt, keeps real output empty until finalization, and resets state, heads, work region, and captured bit within the timed invariant. The `[false,true]` failure is explicitly explained. |
| 3 — purported necessity of effectivity | **Resolved.** `Reductions.lean:160` calls the hypothesis a proof-route restriction, retracts the unlawful counterexample, describes the alternative direct diagonalization, and points to the plan's human-review question. No decision on generalization is taken here. |
| 4 — stale foundation bullets and decision rows | **Resolved.** Plan §2 specifies effective formulas, the computable unique exact split, paired bounded certificates, admissible padding, and the prohibition on asserting the plain-concatenation characterization unconditionally. The old NP row is marked **Superseded**; the old NEXP row explicitly supersedes its `ExpBound` half while retaining EXP. |
| 5 — mixed definition/theorem counts | **Resolved as an erratum.** The plan's round-2 audit entry acknowledges the category error and preservation of the historical pack. The current pack correctly separates 10 definitions from 19 theorem signatures. Its additional assertion that neither category changed is not independently reproducible without the parent sources. |
| 6 — certified statement repairs stand | **Recorded and respected.** No new evidence in the requested surface requires reopening them. This audit does not rerun Arguments A, B, or D. |
| 7 — evidence-scope guidance | **Adopted in framing.** The current pack labels the claims as maintainer/local-machine attestations. Source facts and unverified execution/history claims are separated below. The framing does not substitute for missing build or diff evidence. |

**Exercise 2.1: reconstruction of the repaired reverse direction.** Fix the bounded-side parameters and verifier. Write

$$
Q(n)=C(n+1)^c,\qquad R(n)=(C+1)(n+1)^c.
$$

The native scan, arithmetic, copying, and verifier simulation still require Lean implementations and time/run lemmas. The following verifies the mathematical construction, including its all-input decision rule; it does not claim those machine obligations are already proved.

1. **Admissibility and marker room.** The new exact-length parameters are the natural numbers `C+1,c`, and

   $$
   R(n)-Q(n)=(n+1)^c\ge1,
   \qquad |u|\le Q(n)\Longrightarrow |u|+1\le R(n).
   $$

2. **Recover the instance before stripping.** For input `y` of length `m`, search `0 ≤ n ≤ m` for `n+R(n)=m`; reject if absent. For `n<n'`,

   $$
   n+R(n)<n'+R(n)\le n'+R(n').
   $$

   Hence a successful search has a unique answer. Split `y=x++v` there. Then `|x|=n` and `|v|=R(n)≥1`. The marker search is confined to `v`.

3. **Define acceptance.** Reject if `v` has no `true`. Otherwise split at its last `true`:

   $$
   v=u\mathbin{++}[\mathrm{true}]\mathbin{++}
   \operatorname{replicate}(t,\mathrm{false}).
   $$

   This decomposition is unique. The new verifier language `W` accepts exactly when `|u|≤Q(n)` and `pairEncode x u ∈ V`.

4. **Old witness gives new witness.** If `|u|≤Q(|x|)` and `pairEncode x u ∈ V`, set

   $$
   t=R(|x|)-|u|-1\ge0,\qquad
   v=u\mathbin{++}[\mathrm{true}]\mathbin{++}
   \operatorname{replicate}(t,\mathrm{false}).
   $$

   Then `|v|=R(|x|)`. On `x++v`, step 2 recovers `|x|`; step 3 recovers exactly `u`, because the inserted marker is the last `true`. Thus `x++v ∈ W`.

5. **New witness gives old witness.** Suppose `|v|=R(|x|)` and `x++v ∈ W`. The intended prefix length `|x|` solves the total-length equation; uniqueness forces the parser to recover that same prefix, not another instance. Acceptance supplies a stripped `u` satisfying the original bound and old verifier condition. Therefore

   $$
   \begin{aligned}
   &\exists u,\ |u|\le Q(|x|)\ \land\ \operatorname{pairEncode}(x,u)\in V\\
   &\qquad\iff
   \exists v,\ |v|=R(|x|)\ \land\ x\mathbin{++}v\in W.
   \end{aligned}
   $$

6. **Polynomial time on all inputs.** The search has at most `m+1` candidates. For each, `R(n)≤(C+1)(m+1)^c`, so even unsuccessful evaluations have polynomial size and fixed-degree arithmetic cost. On a successful parse,

   $$
   |\operatorname{pairEncode}(x,u)|
   =2n+2+|u|
   \le2n+R(n)+1
   =m+n+1\le2m+1.
   $$

   Thus the scans, bounded search, pairing, and call to the polynomial-time verifier all have polynomial cost in `m`. Immediate failure branches also terminate. A native implementation of these operations establishes `W ∈ P`; no additional asymptotic mechanism is needed.

| Edge case | Result |
|---|---|
| `C = 0` | Only the empty stripped witness is allowed. The padded witness has one marker followed by `R(n)-1` false bits; the original-bound check rejects every nonempty stripped witness. |
| `c = 0` | `Q(n)=C`, `R(n)=C+1`, and total length `n+C+1` remains strictly increasing. |
| `x = []` | The intended split is `n=0`; `R(0)=C+1≥1`. Pairing the empty instance starts with the separator `[false,true]`. |
| `u = []` | The padded certificate starts with its marker and strips back to `[]`. |
| Old witness entirely `false` | The added marker remains the last `true`, preserving every original false bit. |
| Entire new certificate region `false` | Reject, even if the instance prefix contains `true`; stripping never crosses the split. |
| No length-equation solution, including `y = []` | Reject. This is the branch to make explicit locally, as in finding 1. |

These checks also show why the original-bound test remains necessary: the larger region can contain a marker after too many witness bits. Merely fitting inside `R(n)` does not authorize that witness.

**Enumerator: completeness of the repaired obligation list.** I found no further unnamed substantive construction obligation at this sketch's level. A fill agent will need auxiliary lemmas, but they fall under the named contracts:

| Named obligation | Contract needed in the fill |
|---|---|
| Width evaluation and initialization | Compute `Q(n)`, retain `x`, and construct the initial all-false candidate of exactly that width. Initialization has polynomial cost. |
| Fixed-width increment and overflow | Visit every width-`Q(n)` word once until acceptance or exhaustion; preserve width, and terminate after the final rejection. For width zero, process the unique empty word before reporting exhaustion. |
| Buffering, retention, and verifier-call simulation | Present exactly `x++u` as the simulated read-only input with correct initial head/boundary behavior, while protecting the retained instance and candidate. |
| Capture and return | Suppress every physical verifier emission; capture its bit, including an emission on the halting transition; return control instead of halting the enumerator. Test the updated captured bit. Emit exactly one final answer. |
| Restart | Restore verifier control, simulated heads, work tapes, and captured bit. Clear the bounded visited region and restore buffer/head bookkeeping within a polynomial budget. |
| Timed loop invariant | Combine candidate coverage, correct calls, empty real output before finalization, and polynomial call/reset cost into termination, the singleton-output decision contract, and the stated exponential budget. |

The precedent is real: `UniversalStartup.lean:405`, `universalCaptureTM`, sets physical emission to `none` while storing the source emission, and turns a source halt into a live administrative state before transfer. In particular, the halting action's output is captured before transfer. That wrapper stores output on a tape and transfers to its particular interpreter; the enumerator must implement the named finite-control-bit variant and restart behavior. The repaired sketch correctly calls it a **pattern**, rather than claiming it supplies the whole loop.

The two-round adversarial trace now behaves correctly: a rejected first candidate contributes no physical `[false]`; an accepted second candidate still contributes no physical verifier output; finalization emits only `[true]`. If all candidates reject, finalization emits only `[false]`. Capturing first and then examining the simulated halt covers a decider that emits its only bit on its last transition.

The time estimate is used with the same qualification already accepted in round 2. Its all-length conclusion is

$$
\exists b,e\in\mathbb N\;\forall n,\qquad
a\,2^{Q(n)}(n+Q(n)+1)^d\le b\,2^{n^e}.
$$

`DTIME` permits this external multiplier. The displayed unit-multiplier comparison in the sketch is an eventual comparison, as its explicit small-length qualification indicates. I do not reopen that certified numerical argument.

**HALT docstring and plan.** The retained route is accurate: membership in NP gives membership in EXP, hence a total decider. For the language `{s | HALT c.toMachineCode s = true}`, its indicator is precisely that Boolean HALT value, including false on malformed pairs. `ComputesFunInTime.computes` therefore gives the computability proposition contradicted by `HALT_not_computable`. The latter's signature actually requires `EffectiveMachineCode`; its proof calls `UC_computable_of_HALT_computable`, which invokes the universal evaluator.

The docstring explicitly denies mathematical necessity, identifies the trivial-machine counterexample as unlawful, and attributes the stronger direct-diagonal route to the round-2 report. It does not present the stronger statement as a newly proved Lean theorem. The retraction is complete for this docstring, and its human-review pointer resolves to question 1 in the Chapter-2 plan. The provisional preference is expressly pending review; I neither approve nor reverse it.

Plan §2 now matches the repaired foundations and the two designated old decision rows are marked as superseded in the relevant parts. The final historical “Phase-1 repairs executed” entry still records the earlier pathological-scheme justification, but the round-2 finding and repair entries explicitly retract it. Read as a historical event record, it does not restore the discarded justification. The earlier erroneous pack count is likewise preserved with an explicit erratum.

**Attestations: reproduced facts versus unverified claims.** A lexical scan excluding nested Lean comments and string literals produced:

| Module | Definitions | Theorem declarations | `sorry` tokens |
|---|---:|---:|---:|
| `PolyTime.lean` | 2 | 3 | 3 |
| `NP.lean` | 1 | 2 | 2 |
| `CoNP.lean` | 1 | 4 | 4 |
| `EXP.lean` | 3 | 3 | 3 |
| `Reductions.lean` | 3 | 7 | 7 |
| **Total** | **10** | **19** | **19** |

The facade contains none of these declarations or admissions. There are zero `sorry` tokens elsewhere in the supplied Lean files. All 19 Chapter-2 theorem bodies are `by sorry`; the scan is not an axiom-footprint computation.

| Attestation | Reproduced from the supplied material | Not independently reproduced |
|---|---|---|
| 1 — commit scope and freeze | The current three repaired passages, current plan, 40-module-plus-root inventory, and admission distribution `3/2/4/3/7`. | The exact changed-file list; authentication of commit `79128c7a`; comment-only changes; zero definition/signature/proof-term changes from `8660c416`; unchanged Chapter-1 history; unchanged admission distribution as a historical delta. Earlier reports corroborate the counts but are not a parent source tree. |
| 2 — fresh elaboration | The current source admission count and locations only. | No fresh-olean elaboration, compiler error count, facade gate, or root build was run. Neither `lean` nor `lake` was on PATH; the bundle lacks the pinned dependencies and verification scripts/logs. |
| 3 — statement inventory and deltas | Exactly 10 definitions and 19 theorem signatures, counted separately. The three named docstrings/sketches contain the advertised repairs. | Zero changed definitions/signatures and exactly three changed docstrings require the missing parent/current comparison. No ordered, multiset, or bytewise drift check was possible. |
| 4 — policy and lint | All 29 child-module definitions/theorems have declaration docstrings; all 19 admissions have adjacent proof sketches. The five children use the standard options and precise imports. The facade imports/lists all five children; the root imports the facade. No explicit `axiom`, `unsafe`, or `instance` declaration appears in these children. | `style_lint.py` execution, zero FAIL, and six unchanged Chapter-1 WARNs. Historical preservation of statement prose is also unverified. Presence of prose was checked separately from the accuracy of the repaired passages. |

**Notation glossary.** `C,c` are the fixed natural certificate coefficient and degree; `Q(n)=C(n+1)^c` is the original bound and `R(n)=(C+1)(n+1)^c` is the padded exact length. `n,n',m` are string lengths or candidate split positions; `x,y,u,v` are binary strings; `|·|` is length, `++` is concatenation, and `[]` is the empty string. `t` is the number of trailing false bits; `replicate(t,false)` is that repeated-bit string. `V,W` are the old and new verifier languages. `a,b` are fixed natural time-bound multipliers and `d,e` are fixed natural degrees. Class names, pairing functions, and Lean identifiers refer to the attached definitions.
