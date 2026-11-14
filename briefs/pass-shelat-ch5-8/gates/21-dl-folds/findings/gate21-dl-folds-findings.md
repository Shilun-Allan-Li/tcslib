# Pass–shelat Gate 21 — DL-36/DL-37 folds

**Verdict: CLEAR.** No blocker or major finding. One minor API finding remains.

| Severity | Count |
|---|---:|
| Blocker | 0 |
| Major | 0 |
| Minor | 1 |
| Note | 0 |

| Pin | Audited revision |
|---|---|
| Draft PR | [Shilun-Allan-Li/tcslib #299](https://github.com/Shilun-Allan-Li/tcslib/pull/299) |
| Lean head | `fcdb65794698395f8eaa377df0789f7552681633` |
| Lean tree | `bc738121c68729f6b1172cc10cf7b559705a52f5` |
| Comparison base | `934eac64c410ef69a2f52eb92b91e501c655ed2b` |
| Campaign records | `b2427e514c2eb73d71dcbd7e2e88f25001f35592` |
| Exchange | `64feab16512bc2ba7fd69c67088d4c8ebdda318f` |

This audits the pinned refactor, including the disclosed 13 NM-helper header renames, the three `ChalParams` field-type renames, and the B3 escalation. The repository and supplied reviews were treated as evidence to check. No repository changes, dispatch, review submission, or merge were performed.

## Finding

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G21-01 | minor | [Games/Efficiency.lean:754](https://github.com/Shilun-Allan-Li/tcslib/blob/fcdb65794698395f8eaa377df0789f7552681633/TCSlib/Cryptography/Games/Efficiency.lean#L754) · `InteractiveHandler.finA` | The promotion drops the explicit, documented equation reader for arbitrary inputs. The new home publishes `finA_finInput`, which covers canonical finalization inputs, but omits the named equation API required by policy §1. | At the base, `Indistinguishability/Forward.lean:225` publishes `finA_eq (w)`. At the head, lines 754–762 contain `finA`, `finA_finInput`, and its polynomial-time lemma. The census confirms that Lean's generated `finA.eq_1` remains available; thus the identity is preserved and current consumers are covered. | Publish a documented `InteractiveHandler.finA_eq` with the old formula, without `@[simp]`. Observe the pack's requirement to split `Efficiency.lean` before growing it. |

The missing explicit reader is:

```lean
/-- `finA w = pairFstD (pairSndD (pairSndD w))`. -/
theorem finA_eq (w : List Bool) :
    finA w = pairFstD (pairSndD (pairSndD w)) := rfl
```

## Integrity and statement preservation

Independent byte and source checks passed:

| Check | Result |
|---|---|
| Pack `SHA256SUMS` | **15/15** entries match, including both ZIPs. |
| `verification.zip` | **1,104/1,104** hashes match the manifest retrieved from the pinned records commit; ZIP paths equal manifest paths, with no duplicate entries. |
| `sources.zip` | All **197** Lean files match their Git blob IDs at the audited head. |
| PR diff | The supplied patch equals `git diff --abbrev=9` between the pinned base and head. Exactly **36** Lean paths change, all under `TCSlib/Cryptography/`. |
| Source metadata | All 36 source hashes, line counts, and width counts match `source-head.json`; every changed file is below 1,000 lines. |
| Independent public-header comparison | **62 added, 81 removed, 13 changed**. Each changed header equals its base header after only the disclosed identifier substitutions. |
| `NMSim.ChalParams` | Exactly three field-type substitutions, each `rdU` → `rU`; checked separately from theorem headers. |
| Frozen surface | All **86** declaration headers in the owned `Indistinguishability.lean` and `Simulation.lean` files, private declarations included, are byte-identical. All **16** endpoint headers are byte-identical. These are 102 comparisons covering 96 distinct declarations. |
| Reader/block bodies | **24** source-to-successor body comparisons pass, allowing the disclosed reader renames and bound-variable names. |
| Public name map | All **110** rows checked; every removed public source declaration is mapped. No stale fully qualified old-name references occur in library or audit source. |

The 13 changed headers are exactly `altMsg_eq`, `chalRun_eq`, `idealView_eq`, `nmFin_eq`, `nmOutL_eq`, `nmOutput_eq_entryTails`, `realView_eq`, `recView_nmOutL`, `simCt_eq`, `simFin_eq`, `simMsg_eq`, `simOutL_eq`, and `take_eq_flatten_chunkAt`.

## Refactor assessment

| Items | Assessment |
|---|---|
| G1–G4, G7 | Promotions preserve the needed hypotheses and conclusions. The generic oracle-computation forms retain or expand the former specializations. The list-valued call lemmas follow from the vector-valued lemmas through the supplied length equalities. |
| G5 | `ChallengeSim.expect_simulate_eager` genuinely uses the promoted generic theorem for the unused state. The recorded-state case is handled separately; the retained statement gains no assumption. |
| G6 | `prob_eq_until_bad` follows from the promoted expectation theorem, using an indicator for its first conjunct and the complement of the good-state indicator for its second. Its header is unchanged. |
| R1–R3 | The reader bodies agree after the disclosed substitutions. All four answer-reader copies fold onto `rAns`. G21-01 concerns the explicit equation API for the promoted `finA`. |
| B1–B2 | `chunkAt` and `coinBlock` have the same body up to parameter names. Block-window corollaries use `FunFamily.ofFn_blocks` in the required direction; retained public headers are unchanged. |
| B3 | Keeping both aliases follows the stated escalation rule. The listed four headers and the bodies of `PRFGame.pkTapes` and `Ensemble.copies` explain the obstruction. The deferred work is recorded in DL-38. |
| L1–L4 | Shared list lemmas cover the deleted copies, including both ZK variants. The universe-generalized forms preserve applicability. The existing A4 lemma replaces the padded-list copy. |
| E1–E3 | `logEmit` and `chunkMap` are the advertised `iterEmit` instances. The generic encoding theorem supplies their list-reading arguments, with the step count and orbit bound accounted for. `relabelN` and `relabel` retain their definitions and gain reader-based bridges. The remaining promotions preserve their statements. |

The shared homes and new `Games/Forwarding.lean` are acceptable. The facade exports the new module. An independent import-graph check over the 1,234 archived Lean source modules finds no cycle. The `BitCodec` dependency increase is justified by `polyTimeComputable_isNil`; its new dependency already occurs below `Games/Efficiency`. The recorded DL-38 follow-ups and R7 no-fold decision introduce no additional finding in this scope.

## Rule 10 and recorded Lean verification

I independently checked the submitted probe bytes, recorded insertions, source mappings, raw-log hashes, install/EOF records, requested definition sets, and diagnostic locations. Removing the recorded insertions from every seal probe reproduces its pinned source exactly.

| Variant | Base passing | Head passing |
|---|---:|---:|
| A: `PolyExpr.eval` exempt | 39/46 | 40/47 |
| B: `PolyExpr.eval` sealed | 34/46 | 35/47 |

There are **zero new failing declarations**. `Games/Forwarding` passes both variants. All 48 failing declaration/variant comparisons within changed files, covering 32 distinct declarations, have byte-identical source bodies; inherited failures therefore conceal no edited proof here.

The raw collector catalogs reproduce the requested full-closure definition sets for all **92 base and 94 head** probes, including eligible generated matchers. Recounting the **30** paired-control probes confirms **94** sealed negatives, each failing exactly once, and passing corresponding positive controls. The explicit-unfold scan reports zero foreign definitions. The runner's numeric error field counts `error:` only; the independent recount also includes `error(...)`. Lamport variant B consequently has 15 diagnostics rather than the runner field's 12, identically at base and head, as already reflected in the seal table.

The following results were checked against supplied Lean execution records:

- **Build:** all 226 rebuilt modules have successful records and matching raw-log hashes. Their source hashes match the pinned head. The latest successful records for all **1,199** landing-order modules also match the pinned head's source bytes.
- **Axioms:** the raw census contains 2,037 base and 1,974 head constants. Head constants use only `propext`, `Classical.choice`, and `Quot.sound`, except the unchanged admitted `lamport_oneTimeSecure`. The 16 printed endpoint axiom sets are the standard three. The axiom-set changes remain within that set; the A4 replacement for `NMSim.ofFn_padFin_eq_padL` is axiom-free.
- **Admissions:** the 45 issued admissions in 24 modules have unchanged recorded per-module counts; the source diff adds no admission.
- **Attributes:** no new simp declaration or instance, and no changed attributes among surviving census names.
- **Independent lint runs:** base **216 FAIL / 103 WARN**; head **216 FAIL / 102 WARN**. The FAIL sets are identical; the removed warning is the ThreeColoring file-size warning.

**Execution limit:** this audit reran byte/source checks and Python lint, and inspected the source proofs. It did **not** execute Lean locally: Lean 4.25.0 and the project's compiled dependencies were unavailable in this audit environment. Build, seal, control, and axiom conclusions use the verified submitted execution evidence.

## Evidence

The accompanying ZIP contains this report, `audit/verify.py`, its successful output and machine-readable results, the two independent lint logs, and selected source-evidence extracts with an archive manifest. The original pack remains pinned at `outbox/gates/21-dl-folds-gate/` on the exchange commit above. `audit/summary.json` distinguishes independently recomputed checks from recorded Lean execution.
