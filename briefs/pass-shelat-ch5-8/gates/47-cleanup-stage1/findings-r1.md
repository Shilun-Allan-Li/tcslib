# Gate 47 · round 1 findings (Codex), filed verbatim

Received from Seyoon as an upload, 2026-11-17 (`gate47-cleanup-stage1-findings.md`).

---

**Gate 47 — cleanup Stage 1, round 1 — external Codex audit**

**Verdicts: #347 CLEAR; #355 CLEAR; overall CLEAR. No new findings.** Accepted duplication debt remains outstanding; this verdict does not certify its Stage 2 repayment.

| PR | Blockers | Majors | Minors | Notes | Verdict |
|---|---:|---:|---:|---:|---|
| [#347](https://github.com/Shilun-Allan-Li/tcslib/pull/347), DW-5 | 0 | 0 | 0 | 0 | CLEAR |
| [#355](https://github.com/Shilun-Allan-Li/tcslib/pull/355), promotions | 0 | 0 | 0 | 0 | CLEAR |
| Overall, counted once | 0 | 0 | 0 | 0 | CLEAR |

| Audited input | Pin |
|---|---|
| Exchange | `eae18c1b2a4c78e96d124fb0433288f9f739eafb` |
| Records | `659542ecd9413b504d30da8c937b9805e6c1f71f` |
| #347 head / merge base | `daa6e173cdd94cad1475b9a96eca613bce53ba61` / `2da7e0f3cd65ec93ed71813b7828c3b66ba18942` |
| #355 head / base | `d3c7cb00092ad5913904654d922f30fc7d5fce4a` / #347 head |
| Phase-2 records tip | `e1d39836ed4a69a34914c35f4c73c71de853dcc6` |
| Audited joint tree TS1 | `1eaf940b938bb52e3919f5569893b58522df599b` |

| ID | Severity | PR · location | Claim and evidence | Proposed fix |
|---|---|---|---|---|
| — | — | Both | No new finding requiring a G47-NN identifier. | — |

**Integrity and provenance.** All **13/13** outer checksums, **172/172** verification-archive checksums and **73/73** source-archive checksums pass. All **64 bundle sections** equal their separately supplied or pinned sources. All **73 archived Lean copies** bind to the named Git blobs. Both PR diffs reproduce byte-for-byte with the pack's index abbreviation. The live PR heads and stacked base match the dispatch.

I independently reconstructed TS1 in both direct merge orders. It differs from the phase-2 tip in exactly the two PRs' **23 files, +1,332/−296**. The exception to equality with #355's corresponding blobs is precisely the union `Games.lean` facade. Reconstructing the five original worker commits from their mailbox patches reproduces **all five commit hashes**, the delivered tree `508f915413ee8ef9f2a37b59e0012c9daf3867aa`, and **5/5 `=`** in the range-diff against #355.

I also retrieved the complete phase-1, phase-2 and DW-5 evidence archives: their advertised archive hashes pass; their manifests verify **56**, **888** and **1,173** contained files, respectively. The worker delivery's three manifests verify **2,342**, **2,265** and **47** entries. These checks extend beyond the dispatch's compact summaries.

**#347: proof/refactor audit passes.** The six ModuleHost additions and three copier additions are exact owner-side typed views/readers. `hostTMView_eq`, `hostTMView_q₀` and `copyTMView_eq` are reflexive equations. The remaining four contract/step readers cite their originals directly. The copier really has start state `0`; making it explicit aligns its contract with the host-call start-state premise. Placement, formula docstrings and the absence of new simp attributes are correct.

The diff is **3 files, +253/−296**: ModuleHost **+97/−0**, IterateFindHost **+30/−2**, and IterateFind **+126/−294**. The two deleted host-file lines are exactly the documented module-docstring bullets. Independently rerunning the declaration comparison gives **9 ADDED / 0 CHANGED / 0 REMOVED**. Rerunning the frozen check gives exactly **one ORDER difference**, with no changed existing header, statement prose or definition body.

E1 uses the typed host/copier contracts, preserves the startup seam, positive-round guards and accepting/exhaustion behavior, and matches the loop combinator's result by cases. The polynomial-fuel theorem follows from E1 with `init = id`, fuel `R.eval`, the orbit bound at index zero, and the unchanged `final_bound`. This is the approved F-03 route. The refreshed sketches describe the actual proofs.

The four TS1 tip probes attribute the original **20 errors to E1 (9) and the polynomial-fuel theorem (11)**. Each becomes **0** at TS1. The ModuleHost **10** and IterateFindHost **16** failures are unchanged pre-existing DW-9 debt. E1's local dispatch/branch/halt derivations, and their overlap with #355's three promoted view steps, are disclosed and assigned Stage 2 re-points; they are not an undisclosed new copy.

**#355: public API audit passes.** Independently reproduced **69 ADDED / 0 CHANGED / 0 REMOVED**, **21 files +1,079/−0**, and **43 insertion-only hunks**. The additions match the brief's 69 headers; the two reported statement-comparison DIFFs concern equation-compiler arms and structure-body fields, not header drift. There are **54 protected names and 15 fresh names**. No existing proof, attribute or non-facade import changes, and no Stage 2 re-point, deletion or blocks-alias change occurs.

I checked all 69 declarations and the listed copies against their intended general forms. The finite/uniform hypotheses are appropriate; the statements do not conceal contradictory premises. In particular:

- At `κ = 0`, the tape theorem's budget forces a query-free computation; out-of-range tape entries use the same arbitrary value on both sides of an update.
- The override lemmas allow empty tables and repeated keys; the first table entry wins, without a hidden distinctness assumption.
- The chunk lemma handles `L = 0` and `N < L`; padding truncates overlong words and claims identity only under its stated length premise.
- Mixtures allow endpoint weights zero and one; split readers allow an empty half; history readers return `[]` beyond the history; XOR cancellation requires only that the pad be at least as long as the message.

The shared homes follow CS1-Q1/Q5–Q8. `Games/Tapes` imports only Hopping; `InteractionWords` isolates the binary-arithmetic import; EncodingMachines is a shared home available to both machine consumers. All seven new definitions have usable readers. All **69 formula docstrings**, **68 glue notes**, the predictor's **[PS10, Theorem 104.4, proof]** locator, and the required longer-proof sketches check out. The source locator refers to the hard-core-bit predictor in the proof of trapdoor-permutation encryption. The disclosed sizes, 965 and 867 lines, remain below 1,000.

The Stage 2 handover comprises **98 re-point rows**, **19 maintainer-addendum rows**, the subsequent DL-59/DL-60 dispositions and all **fourteen approved blocks-alias changes**. The recorded resolutions cover the worker report's omitted copies and stale claims. This audit checks that handover as a record, not its future execution.

**Duplication: part A is confirmed and covered by the recorded acceptances.**

| Promotion / overlap | Record and disposition |
|---|---|
| Typed-view contracts and E1's three local control steps | DW-5/SR-02 and DW-9; Stage 2 re-points |
| Games simulation, fresh coins, tapes and overrides versus ETTGame; extension versus AdaptiveCPA | DL-40, with DL-59 for the older extension family |
| Log-length, XOR, optional-record and equal-width adversary copies | DL-40/DL-44 |
| Blocks-to-flatMap bridge and alias-related users | DL-35; fourteen Stage 2 changes |
| Sample expectation and splitBits word readers | DL-41/DL-44 |
| Zero-cost computation facts | DL-42 |
| Tuple encoding as flatMap | DL-46 |
| getD-of-ofFn readers, including the public generic GI copy | DL-47 |
| Coin-length and predictor readers | DL-48 |
| History readers, word-list bridge and shared machine helpers | DL-38/DL-45/DL-49, including its extension |
| Padding and zero-word families | DL-53 and DL-60 |
| Coupling bound | DL-51 |
| Fourteen finite-distribution facts versus Rejection | DL-39 |

I checked the additional same-name and statement-shape hits against the full TS1 sources and the supplied Mathlib/core search evidence. No further undisclosed or unaccepted re-proof/restatement of a public result was identified.

| Sweep item | Source audit and policy judgment |
|---|---|
| **B1** | **Confirmed.** The extension bodies agree; the old `extendStream` is universe-polymorphic, and its equation/update API supplies the corresponding facts. **DL-59 satisfies policy and G44-01:** explicit Seyoon acceptance, one `Type*` family in Games/Tapes, named consumers, and repayment in cleanup Stage 2. Earlier nondisclosure is retained in the record; the overlap is now accepted debt. |
| **B2** | **Confirmed with qualification:** the FormulaKit statement has the pair components reversed and is admitted. It is not an independently proved duplicate. DL-60 records the Complexity handoff and the post-campaign-merge citation route. |
| **B3** | **Confirmed.** Padding agrees extensionally with `List.takeD` at default `false`; the listed Mathlib length/cut facts and existing padFin bridge are relevant. DL-60 explicitly accepts and schedules this overlap's Stage 2 resolution. DL-53's broader family consolidation remains deferred as separately ruled. |
| **B4** | **Confirmed.** The first-projection fact is the message reader at index zero; the GI second-projection fact is the iterated-suffix reader at index one. DL-60 extends DL-49 and names both Stage 2 re-points. |
| **B5** | **Confirmed as a different-interface relative.** GGM uses splitHalves on twice the width, rather than the splitBits reader's arbitrary pair of widths. Disclosure-only treatment is appropriate. |
| **B6** | **Confirmed as a private Complexity relative:** the constant-singleton chunk case has a replicate conclusion. Its specialization relationship is real, but this is not a re-proof of an existing public general theorem. The recorded disclosure-only disposition introduces no unaccepted public duplicate. |
| **B7** | **Confirmed as relatives, not equal statements.** AdaptiveCPA counts fresh challenges, retains the history and samples one distinguished index; the Games tape theorem advances on every query under a query budget. QueryTree lazy evaluation also has a different state/model and repeated-query behavior. Disclosure-only treatment is appropriate. |

Thus **DL-59 and DL-60 meet the applicable duplication rule and G44-01 standard**. Their closure here means acceptance is sufficient for Gate 47; it does not mark repayment complete.

**TS1 replay and probe evidence.** Independently recomputed the **556-module** downstream set and matched it exactly to the compile queue. All **556 source hashes and full build-log hashes** bind; every record has rc 0 and zero errors. There are **26 inherited sorry warnings and 272 warnings total**. The 556 output hashes agree with the updated state, whose full order has **1,429 entries**. Supplied state checks report **1,429/1,429 OK**; snapshot #5's before/build/final checks each report **0 extra / 0 changed / 0 missing**. The recorded link checks show 556 rebuilt oleans with link count one and 873 reused hard links.

The recorded admission inventory is **196 → 196**, identical on every shared module; each new module adds zero. The census has the same 34 modules without matching admission records on both sides; these are not counted as verified zero admissions. All 556 replayed modules are accounted for. The source delta adds/removes no admission. The actual axiom log contains **69 Stage 1 prints**, split **34/12/6/4/13** (all three standard axioms / propext+Quot.sound / propext / Classical.choice / none), and **27 DW-5 prints**, all using the standard three. Its **1,224-constant, 21-owner census** contains all **80 touched declarations**, no nonstandard axiom and no `sorryAx`.

For all **84 TS1 owner-seal probes**, I recovered the exact bytes by the recorded probe hash from the worker/DW-5 archives. Removing each hash-checked harness insertion recovers the TS1 owner. Requested names, run hashes, diagnostic counts, install/EOF masks and failing declarations recovered through the source-line maps agree with the reported inventory.

Entries below are in **strict A / strict B / coe A / coe B** order. Counts are errors, not distinct declarations.

| TS1 owner | Requests | Errors |
|---|---|---|
| IterateFind | 595/596/595/596 | 0/0/0/0 |
| IterateFindHost | 251/251/251/251 | 16/16/16/16 |
| PPT | 543/544/543/544 | 0/1/0/1 |
| ModuleHost | 241/241/241/241 | 10/10/10/10 |
| Asymptotic/Adversary | 587/588/586/587 | 0/0/0/0 |
| Asymptotic/Sampling | 18/18/17/17 | 0/0/0/0 |
| Authentication/Encoding | 194/194/194/194 | 0/0/0/0 |
| PrivateKey/EnsembleSecurity | 851/852/850/851 | 0/2/0/2 |
| PublicKey/Trapdoor | 1636/1637/1635/1636 | 3/3/3/3 |
| Foundations/BitLists | 0/0/0/0 | 0/0/0/0 |
| Games/Bridges/Experiments | 54/54/53/53 | 0/0/0/0 |
| Games/Efficiency/Strings | 1173/1174/1172/1173 | 0/0/0/0 |
| Games/Machines | 601/602/601/602 | 0/0/0/0 |
| Games/Tapes | 59/59/58/58 | 0/0/0/0 |
| PRF/Asymptotic/Defs | 667/668/666/667 | 0/8/0/8 |
| ZeroKnowledge/EncodingMachines | 890/891/890/891 | 0/0/0/0 |
| ZeroKnowledge/Interaction | 567/568/567/568 | 0/0/0/0 |
| ZeroKnowledge/InteractionWords | 748/749/748/749 | 0/0/0/0 |
| InformationTheory/Entropy | 10/10/9/9 | 15/15/5/5 |
| InformationTheory/FinDist | 0/0/0/0 | 0/0/0/0 |
| InformationTheory/Samples | 10/10/9/9 | 3/3/0/0 |
| **Total errors at TS1** | | **47/58/34/45** |
| **Total errors at the tip** | | **59/70/54/65** |

The exact classification is:

- **Touched declarations:** coe A/B **0/0** errors; strict A/B **8/8**, in the three mixture declarations and three Samples map declarations. The strict-minus-coe request difference is only the ruled FinDist coercion.
- **DW-9:** ModuleHost 10 and IterateFindHost 16 in every variant, unchanged.
- **Other pre-existing coe failures:** Trapdoor 3 and Entropy 5 in every coe variant. Entropy's coe failures are in `IsFlatSource.isSource`, `isSource_uniform` and `le_minEntropy_iff`.
- **Other strict-only Entropy errors:** five already present at the tip; the new mixture declarations add five. Samples adds three. These explain the strict increase without a coe regression.
- **B-only errors:** PPT 1, EnsembleSecurity 2 and PRF Defs 8, all pre-existing, outside touched declarations, and attributable to the only A-to-B addition, `PolyExpr.eval`.
- **IterateFind:** **20 → 0 in all four variants**. The remaining request differences are exactly the disclosed new BitLists declarations and the net matcher reduction in EncodingMachines.

The paired-control counts are per strict/coe harness variant; they should not be multiplied into four identical A/B runs.

| Harness variant | Probes, sealed + unsealed | Sealed negatives, each failing once | Positive checks, zero errors |
|---|---:|---:|---:|
| Stage 1 strict | 19 + 19 | 20/20 | 40 |
| Stage 1 coe | 19 + 19 | 20/20 | 40 |
| DW-5 at TS1, strict | 5 + 5 | 30/30 | 60 |
| DW-5 at TS1, coe | 5 + 5 | 30/30 | 60 |

All control error locations agree with their plans, unsealed runs have rc 0, sealed install/EOF checks pass, and there are zero stray errors. The TS1 DW-5 controls' **10 probes/30 negatives**, rather than the original replay's **8/29**, are correctly disclosed.

The explicit-unfold inventory recounts **1,776 items**, **438 in touched declarations**: **310** in Stage 1 additions and **128** in E1. There are **zero foreign items in touched declarations**; the two owned-definition readings are extTape's own readers. The 29 inherited foreign items are unchanged. Recounting raw lint gives Cryptography **92/104 → 92/103**, InformationTheory **5/2 → 5/2**, Complexity **25/390 → 25/390**; the only removed warning is pkPredictor's missing reader. The two file-style findings are inherited.

**Disclosures and limits.** All seven phase-2 disclosures are carried accurately: TS1 replaces the earlier prospective tree; inherited failures and coercion-only new failures are classified; DW-5's effect reproduces; its changed control counts are stated; GSW 6a was absent; and the failed pre-Lean attempt, watcher behavior and temporary merge objects are recorded. The PR-body corrections, REST base-versus-merge-base distinction, verbatim cherry-pick trailers/shared signing key, deferred-work status, optional doc nits and disclosed file sizes introduce no further finding. Signatures were not independently authenticated.

The records advance adds precisely #357's nine Lean files, all equal to its pinned head blobs. Its merge with #355 yields `20d1101ade46ba26919f01e30f7ee9422495669b`, not TS1. This report certifies the dispatched TS1 evidence only. Re-replay and snapshot adoption remain maintainer merge conditions; Stage 2, DW-10's inventory, DW-11, the Complexity handoff's execution and the other PRs' substantive audits remain outside scope.

**No fresh Lean compilation was run.** Proof elaboration, output/state and filesystem-preservation conclusions rely on the supplied hash-bound replay evidence. Checksums, Git reconstruction, declaration/freeze checks, source/probe binding, build-log recounts, control/error attribution and source/overlap review were performed independently. No PR was changed, dispatched or merged. The user dispatches and merges.
