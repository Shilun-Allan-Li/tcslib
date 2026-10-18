# External audit pack — the specification API (contract field equations; layout and record facts)

Campaign: the Arora-Barak chapters 3-4 plan, the machine library (`machine-library-design.md`
§12–§16).

Two fill deliveries escalated the same contradiction (E1):
- **B6 F3**, `audits/evidence/b6-fill-configclock/delivery-review.md`;
- **§13d G4**, `audits/evidence/s13d-g4-fill/delivery-review.md`.

Their briefs forbade unfolding library definitions, yet the facts their routes need (record
cells, layout boundaries, contract fields) were readable only from definition bodies.
**User (2026-10-16): an API PR first.** Published equation lemmas, not unfolding, and the rule for
future briefs. Under the §13d rule (every Lean change of the revision gets a PR the user merges
and its own audit gate), **this gate audits PR #112 before it merges.**

| File | Additions |
|---|---|
| `Build/Contract/Basic.lean` | `Contract.trans_{pre,time,post,lo,hi}` |
| `Build/Contract/Seam.lean` | `Contract.{seq,inPhase,branch}_{pre,time,post,lo,hi}` |
| `Build/Contract/Catalog.lean` | `framedContract_*`; `seekPost_*`, `sweepPost_*` (the five `Cfg` fields); `<row>_contract_{pre,time,post,lo,hi}` for the ten row contracts |
| `Build/Catalog.lean` | `joinFields_nil`, `joinFields_singleton`, `fieldsTape_of_nonneg`, `fieldsTape_of_neg`, `fieldsTape_of_length_le`, `fieldsTape_nil`, `fieldOffset_zero` |
| `Build/CfgRecord.lean` | `recordAt_iff`; `record_pos_lt` made public |
| `Build/RecordTable.lean` | `recordLength_eq` |

- **Generation:** the field equations come from Mathlib's `simps` with `isSimp := false`. The row
  contracts use `simps!`, since their bodies are `framedContract` applications.
- **Evidence:** `audits/evidence/spec-api/`. It holds the patch, the generated statements as Lean
  prints them (`logs/generated-*.txt`), the elaboration, axiom, freeze and lint logs, the screen,
  and the replay order. `NOTES.md` has the design.
- **The bundle** contains the six files at the PR head (`lean/spec-api`), and the two consumer
  files that will use the API (`SpaceComplexity/WindowClock.lean` and
  `Build/ZoneRebalance.lean`), at the tip.

## Brief for the auditor

1. **Faithfulness of every generated equation.** For each of the 85 names in
   `logs/generated-*.txt`, the right side must be exactly the field of the definition: no
   strengthening, no lost hypothesis, no changed binder. Pay attention to where `simps!` reduced
   a subterm. For example, `walkTM_contract_pre` reads `w[p]?` where `walkTM_run_ofCfg` states
   `FinTM.bufferTape w p`. Say whether each reduced form is definitionally the field and usable
   by a consumer that holds the row's own hypothesis shape, or whether a bridging lemma is
   needed.
2. **No behaviour change.**
   - No generated lemma carries `@[simp]` (`isSimp := false`), and no hand-written lemma is
     tagged `@[simp]`.
   - Confirm from the patch that no existing statement or definition changed, and that
     `record_pos_lt`'s statement and proof are unchanged apart from `private`.
3. **The hand-written lemmas.** Truth, minimality, and docstrings. Check:
   - `fieldsTape_of_length_le`'s boundary (blank from `|joinFields fs|` on);
   - that `fieldsTape_of_nonneg` together with `_of_neg` covers every cell;
   - that `recordAt_iff` restates `RecordAt` verbatim.
4. **Coverage of E1.** This is the main question: does the API discharge both escalations?
   Use the delivery reviews' E1 sections and the two consumer files.
   - **G4:**
     - the layout facts named in its review: `fieldOffset fs 0 = 0`; blank at `p < 0` and past
       the layout; the empty layout;
     - the row contracts' `pre`/`time`/`post`/envelopes;
     - `Contract.seq`/`inPhase`/`branch`/`trans`.
   - **F3:** `RecordAt`'s cells, `recordLength`'s formula, and `n + 2 ≤ 2^posWidth n`.

   Name anything a continuation would still have to unfold, such as the fields of another
   combinator (`Contract.mapState`, `ReturnContract.release`, `Lockstep`) or another layout fact.
5. **Naming and placement.**
   - Are the generated names (`<def>_<field>`) consistent with the library's?
   - Is a `simps` attribute line, rather than hand-written lemmas, acceptable under `policy.md`
     (attribution, sketches)?
   - Do the module docstrings list the additions?
6. **Duplication** (failure mode 5): the screen of the six files, before and after
   (`logs/screen-*.txt`).
7. **Records.** Check `NOTES.md` and this pack against the evidence. Report anything else in the
   standard table.

## Repository-side attestations (verify or challenge)

- Built on the tip `c2897d7f` (#111 merged), against `oleans-lf3p`.
- **Elaboration:** each file 0 errors, with warning counts equal to the base.
- **Generated names:** all 85 resolve in-module.
- **Axioms:** the ten hand-written lemmas use standard axioms only.
- **Freeze:** publics added only.
- **Lint:** 0 FAIL, and the WARN set is unchanged.
- **Screen:** the six files, before and after: 711 → 712 declarations, 350 → 350 pairs, 116,080 characters; pairdiff: **0 new pairs**, 0 earlier-only (`logs/screen-delta.log`).
- **Replay:** 89 modules (`replay-order.txt`). #112 is stacked on #113 (the cont5 partial,
  `CodeSimulator` only), and the two replays run chained, by the user. The result is recorded
  when it comes in.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into `audits/spec-api-findings.md`.
The gate closes when it has zero blockers and zero majors.
