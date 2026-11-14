# Pass–shelat Gate 23 — findings

**Verdict: HOLD.** Counts: **0 blockers, 1 major, 1 minor, 0 notes.** The major is an undisclosed private duplication outside the pack's accepted dispositions. No proof-soundness defect was found in the reviewed route.

| Audit pin | Revision |
|---|---|
| Repository / PR | `Shilun-Allan-Li/tcslib` / draft [#306](https://github.com/Shilun-Allan-Li/tcslib/pull/306) |
| Lean head | `c1a3ba5623febf318a56a0f84be885f262e0f86e` |
| Comparison base | `a757b6a18785377c158312ed051b1789cf45badf` |
| Campaign records | `b01c150512fe6668ee6dddb1c6b429d1b9c822bf` |
| Exchange | `e7b9e53e4a41ffa84b52deb17d34d144877d31f3` |

The live PR's head, base, draft status and eleven changed paths match these pins. The repository and bundle were treated as audit evidence. No repository writes, review submissions or dispatches were made.

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G23-01 | **major** | `EncryptThenTag/Machines.lean:95` · private `length_le_length_encodeLog` | Undisclosed duplication of an existing private lemma; absent from DL-40. | The same generic statement occurs at `PublicKey/NonMalleability/Indistinguishability/Forward.lean:108` at the comparison base. Both proofs induct on the log and use the same `encodeLog_cons`, `length_pairEncode`, `List.length_cons`, `omega` step. Verbatim excerpts are in `audit-evidence/duplicate-excerpts.txt`. | Remove the duplicate through the existing public log-reading API, or obtain an explicit disposition for this additional duplication. |
| G23-02 | **minor** | `EncryptThenTag/Reduction.lean:82` · `dAbs_eq`; `Handler.lean:40`; `CPAHandler.lean:39` | Three documentation argument lists disagree with the declarations. | The equation documents `dAbs q E hE b n s`, while its statement uses `dAbs E hE q b n s`. The module lists show `dHandler E hE q b` and `bHandler q hq b`, while the actual applications are `dHandler q E hE b` and `bHandler q`. | Correct those three documentation references. |

G23-01 is a duplication finding, without an inference about how the author produced the proof. Making the section variables explicit and changing the empty-log case from `Nat.zero_le` to `simp` do not change the existing lemma's mathematical statement. The worker report does not identify this overlap, and DL-40 does not include it. The maintainer's raw same-name search records the old lemma, but neither the review's dispositions nor the pinned ledger accepts this additional duplication. The pack's major-severity rule and the duplication policy therefore apply.

A repair can stay within the owned scope: derive `length_logCount_encodeLog` from public `NMCCA2.logEmit_encodeLog`, taking the reader to be `cntRead` and emitting `[true]` for each entry. The two published defining equations identify `logCount` with that instance of `logEmit`; taking lengths gives the count. This removes the need for the copied private length lemma. This repair direction has not been Lean-replayed here.

The proof review supports the delivered construction:

1. **Book and frozen statement.** The proof follows the random-tag, fresh-decryption rejection and CPA-reduction argument of [PS10, pp. 169–171](https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf), with the whole-ciphertext tag and parameter conventions recorded in the frozen source notes. All 25 pre-existing declaration headers match byte-for-byte; the other 24 declaration bodies remain unchanged. Only the eleven authorized Lean paths differ.
2. **Tag reduction.** The cap, parameter-halving construction and T2/T4 reductions give the required distinguisher at `2n`, with budget `q(2n)`. `Negligible.comp_of_le` applies because `n ≤ 2n`.
3. **Forgery bound.** `RevInv` separates listed pairs, the challenge pair and unrevealed points. For positive parameters, a valid word with the challenge pair is the recorded challenge by canonical parsing and is refused. An unrevealed tag guess contributes at most $2^{-2n}$; the rejecting experiment's answers do not reveal those guesses. The induction bounds the bad probability by $q(n)/2^{2n}$.
4. **CPA simulation and combination.** `tagOf` reuses tags from the table or challenge record, so repeated pairs introduce no additional tag-collision error. `comp_bAbs`, preservation of `bInv` and `expect_simulate_abs_inv` lift the per-call laws to whole runs. `exists_cpaStep` supplies one machine independent of the challenge bit. The public `exists_prfReduction`, `prfAdv_eq_expect` and `abs_expect_fImpl_sub_le` then justify the disclosed alternate route and its `Q(n)²/2ⁿ` term, where `Q = PRFGame.qRed q`. The sum is negligible; the zero-parameter correction is eventually zero. Budget zero, missing/repeated challenges, malformed queries and codec timeouts are covered by the stated whole-run equalities and cap.

Independent checks verified all **15** top-level SHA-256 entries, **42** verification-manifest entries, **446** review-evidence entries and **116** LE-doc-evidence entries. All **172** source-closure files match the pinned Git blobs, and all **18** bundle sections match their pinned originals. LE-width is whitespace-only; removing doc comments makes LE-doc's eleven files byte-identical. The 94 added formula docstrings and 15 added sketches agree with the reviewed declarations and proofs; G23-02 concerns surviving worker documentation.

The supplied **44 head seals**, **4 base seals**, **551-row axiom census**, **20 control probes / 51 sealed negative errors**, **19 final module build records**, and **1211-module source/object ledger** were checked against their raw evidence and source identities. Closure request sets were recomputed from the collector output, including matchers; the strict and coercion variants both pass. The 2290-item explicit scan reports no foreign definitions. Fresh lint at base and head reproduces **92 FAIL / 102 WARN**, with identical FAIL/WARN lines. Accepted DL-40 and PRFGame overlaps were not reopened.

**Verification limit:** `lean`, `lake` and `elan` are unavailable in this audit environment. No fresh Lean build, axiom computation or seal/control elaboration was run. Those results rely on the authenticated supplied raw logs and manifests, whose consistency was checked independently. The attached script and results distinguish these evidence checks from fresh lint execution.

The gate remains **HOLD until G23-01 is resolved or explicitly dispositioned**. The user dispatches and merges.

Notation: `q` is the adversary's polynomial query budget; `Q` is `PRFGame.qRed q`; `n` is the security parameter. Other identifiers are repository declarations.
