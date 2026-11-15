# Pass–shelat Gate 29, round 2 — learning

**Verdict: CLEAR. Both round-1 majors are closed. No new finding.**

| Blocker | Major | Minor | Note |
|---:|---:|---:|---:|
| 0 | 0 | 0 | 0 |

| Pin | Audited revision |
|---|---|
| PR | [Shilun-Allan-Li/tcslib #313](https://github.com/Shilun-Allan-Li/tcslib/pull/313), draft |
| Lean head | `2b6c29816de4cb1cd0e6b74fa3ae848c9f0f1be9` |
| PR base | `6ce4658db08a1dc2a03a149987197660db078011` |
| Campaign records | `fb8737f827e398fec2f819f89c0416dc7b52f03d` |
| Exchange | `3de4f1a6ee540b13250a6355c92b187878d35ed0` |
| Round-1 head | `8befc58966fd39f974a54250849736df194584b9` |
| Round-1 exchange | `341f61def10e0481a7c29fa4787a80d6ece7d5df` |

## Round-1 findings

Paths below are relative to `TCSlib/Cryptography/`; line numbers refer to the audited head.

| ID | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G29-01 | major, **closed** | `Randomness/Learning/Random.lean:172`, local `hj` in `abs_gameProb_random_sub_half_le` | LE-gate29a removes the inline constant-average re-proof. | Lines 175–176 use `uprob_prod`, then `simp only [uprob_eq_point, OneWay.uexp_const]`. The original `94b31964` patch and rebased `9b40c7ce` patch agree. Only this proof step and its sketch's lemma list change. | None remaining. |
| G29-02 | major, **closed** | `Randomness/Learning/Random.lean:67`, `firstBit_of_pos` | LE-gate29b derives the result from the merged shared reader. | Lines 68–69 rewrite `firstBit_eq` and specialize `TCSlib.Cryptography.headD_drop_ofFn` to index `⟨0, hn⟩`, default `false`, simplifying `List.drop_zero`. The reader is published at `Foundations/BitLists.lean:61`; the Lamport reader also calls it. Only this proof and its explanatory docstring change. | None remaining. |

For G29-01, after the product-probability reader, `uprob_eq_point` makes the integrand constant. The averaging type `((Fin m → Fin n → Bool) × ρ)` is finite and nonempty under the existing hypotheses, so `OneWay.uexp_const` applies directly. For G29-02, the shared reader's zero-index specialization is exactly the goal after `firstBit_eq`. Both repairs preserve their theorem headers and require no import change.

## Changes since round 1

There is new implementation and evidence, but no new audit finding:

- **Two repairs only in the unit.** I reconstructed the head's `Random.lean` from round 1 using exactly the two proof replacements and two docstring insertions. The other four unit files are byte-identical. Thus all 61 declaration headers, all definition bodies, imports and attributes are preserved; part (c)'s source is unchanged. No declaration is added since round 1.
- **Rebase.** Independently replayed `git range-diff` gives six `=` rows for `4561c340..94b31964` versus `6ce4658d..9b40c7ce`. The pinned PR diff matches `6ce4658d..2b6c2981` exactly: five files, 856 insertions and 13 deletions.
- **Base delta.** #311/#312 were already covered by round 1's records tip. #314–#317 are new. Four changed base modules enter the learning closure; the closure grows from 138 to 141 modules through the addition of `Games/Advantage`, `Games/Bridges/Experiments` and `Games/Probability`. The pre-existing imported definition bodies remain unchanged, and the used public contracts retain their signatures.
- **Duplication.** The new proof lines call the public lemmas identified in the findings. They introduce no further computation or statement that re-proves a public lemma. The remaining headD/getD copies are the disclosed DL-47 debt, including its Gate 32 extension and SG-F04; DL-45's deferred learning overlaps remain disclosed. I found no additional undisclosed duplicate introduced since round 1.

The round-1 correctness assessment of Theorem 179.1(b), including its edge cases and the deduction of part (c), stands after these changes.

## Evidence verification

- **Pack and provenance:** all 21 round-2 `SHA256SUMS` entries and all 17 round-1 entries verify. All 12 round-2 bundle sections match their pinned git originals, apart from framing newlines. Every one of the 141 source-closure files matches its head git blob. The verification archive's 21 manifest entries, LE-gate29a's 254 and LE-gate29b's 461 all verify, with no unlisted file entries beyond their manifests. External manifests and PROVENANCE copies agree. The round-1 nested review/reuse manifests also verify.
- **Build:** independently checked all 66 LE-gate29a and 268 head integration records against their raw log hashes and pinned source hashes. All return rc 0, with zero errors in both diagnostic forms and zero occurrences of `error`. The 268-module queue equals the required integration build set, through root `TCSlib` and both audit Checks modules. All five learning modules have zero warnings and zero sorries. The supplied 1,253-module tree check's source/object records reconcile with its snapshot; the pre/post restore snapshots are byte-identical.
- **Rule 10:** both landing edits pass strict A/B and coe A/B. I recovered the exact pinned source bytes by removing instrumentation, and independently matched request payloads, actual-name components, catalog eligibility, stored-term references and installation/EOF records. Head request counts are 1753/1754 strict and 1752/1753 coe; its collector stores 11 constants. Both edits' paired controls each have four probes and exactly seven intended sealed-negative failures per harness; reader positives and unsealed controls pass. The head probes record `maxErrors = 0`.
- **Carried seals:** accepted for the four unchanged files. Their source is identical, the imported existing definition bodies are unchanged, and the base additions do not alter the relevant public signatures. The added definitions concern game expectations and generic-width PRF machinery; these files continue to use their published readers. The head integration build validates their elaboration on the new base. The seal instrumenters and control generator are byte-identical to the audited round-1 reuse tools.
- **Axioms and admissions:** head axiom prints for parts (b) and (c) contain exactly `propext`, `Classical.choice`, `Quot.sound`; `firstBit_of_pos`, `firstBit_flip0` and the shared reader contain only `propext`. No `sorryAx` appears. The campaign census reconciles to **39 → 38** from the merged tip: learning's target is the sole further discharge. The earlier 40-count issued census also includes MAC/FromPRF, discharged by #317.
- **Lint:** the head, parent and base retain the same 193 FAIL/WARN lines: 92 FAIL / 101 WARN. No new lint finding.

**Validation limit:** no Lean toolchain is installed in this audit environment. I independently checked the source, git comparisons, manifests, import relationships, seal instrumentation and raw supplied execution evidence; I did not rerun Lean elaboration or the seals.

**Merge condition:** the integration rebuild on the merged tip with #318, #319, #323 or #324 remains the maintainer's pending merge condition for whichever PR merges second, as requested. It is not an audit finding. GitHub confirms the pinned merge bases; replaying the merges with those explicit bases reproduces all five supplied clean merged trees, including the records tip. I found no concrete merge obstruction. These combined trees have not been built by this audit.

The live PR head matches the audited head. Its description now includes both repairs and the rebase, superseding the pack's stale-description note. No repository source edit, review submission, dispatch or merge was made.

**Notation:** `n` is the security parameter/string length; `m` is the number of examples in the helper theorem; `ρ` is its coin type; `hn` proves `0 < n`. Other identifiers are audited Lean declarations or supplied gate/commit labels.
