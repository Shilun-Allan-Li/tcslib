# Gate 106 incoming audit: independent maintainer review

2026-11-07; Codex. **Not yet clear to merge.** The received HOLD is justified as a
disposition/accounting hold. The scoped Segment replacement and supplied replay evidence
survive this review. F1 is mechanically repairable through the current public API; F2
extends beyond the auditor's seven confirmed pairs, and a separate dispatcher kind also
needs a ruling. No debt is acknowledged and no gate is closed by this report.

The received findings remain verbatim: 9,822 bytes, SHA256
`f6263c500ec7496a8867b7652bd44a1dbc423bd2711d5c6268a40347332b058c`.
The published bundle matches its immutable dispatch: 5,288,598 bytes, 166 ordered sections,
SHA256 `761c734d37963fb19966cadb48488350f84d9709a16b62fe780aef1e28f7368c`;
Lean `ccdc033f402781ecb4bb5b097e4018b8d9da1b90`, records
`d857c6c8a195b388079a8796e789f9852c047815`, baseline
`680760723d72826469d0fc294e4d7ee2ecac3e6c`.
All four audited source bodies independently reproduce the Git-blob SHA1 and SHA256 in the
current msg3 receipt. No Git command or compiler was run; the full bundle hash authenticates
the supplied package, not an independent verification of every section against Git objects.

## Crosscheck of every received item

| Item | Independent assessment |
| --- | --- |
| F1, cut-only composition | **Confirmed, outside prior SG-1 scope.** Pinned SAT:4076 and Hardness:6414 have identical full code after changing their names, each 14 span lines. They concatenate only a strict forbidden-state guard, with an endpoint seam equation; they do not define a fixed-parameter private Segment predicate. Ledger:617–620 acknowledges the latter kind; ledger:640–642 explicitly separates these cut-only siblings. |
| F2, generic adapters | **Confirmed and strengthened.** The seven listed pairs total exactly 62 declaration-span lines in each file. The matching correctness/frame companions yield 22 exact header-and-code correspondences, 298 span lines per file, under only `sat→clA5` / `Sat→CLA5` prefix substitution. An additional finite-family banked dispatcher kind is discussed below. Existing acknowledgment scopes do not cover these kinds. |
| F3, SingleTape uses | **Confirmed minor.** Six consumer declarations contain twelve old calls: `dg_init` 3, `dg_collect` 1, `dg_turn_with_growth` 2, `dg_end_with_growth` 2, `dg_step` 3, `dg_simulate` 1. Seven matching source lines included the helper declaration. Preserve the dispatched pack and issue an accounting erratum; update the ledger when authorized records work resumes. |
| N1, input integrity | Bundle hash/size/order, pins, baseline source population, and the four current audited blobs crosscheck. The original change population is four Lean files plus the blueprint. The current post-NatBits tree has only three Lean diffs because the common Frag repair is already merged. The auditor's claim to verify all 166 original Git blobs is attributed, not rerun here. |
| N2, Tautology bridge | Correct: endpoint equality plus anchor exclusion strictly before `t`; the Segment head relation is `True`. `segment_iff` preserves exactly those clauses. |
| N3, CounterLoop bridge | Correct: both done/escape states excluded before `t`, counter interval and one complete body-head relation through `t`, actual run endpoint. The conjunction distributes over time without separating witnesses inside `R`. |
| N4, SingleTape bridge | Correct: exact endpoint, empty forbidden set, one head in the closed interval through `t`. No liveness condition is added. |
| N5, boundary checks | The stated zero-time, forbidden-seam, closed-head-bound and joint-witness examples follow from the literal formulas. A forbidden start is permitted at zero time; heads still satisfy the relation. I did not reproduce the claimed 8,420 Python traces or treat their number as Lean evidence. |
| N6, approved rewrite/freeze | Independently confirmed all 25 Segment compositions: 10 Tautology, 3 CounterLoop, 12 SingleTape. The retired helpers are absent. Four-file source census stays 287→287; complete surviving public headers/visibility/order and definitions are frozen. Exactly the six disclosed public proof bodies change. |
| N7, seals | Each whole-consumer probe contains the exact pinned original source, with insertions only: paired positive controls, irreducibility, paired negative controls using the public equation. The supplied receipt records all four probes passing; raw final outputs contain no errors. Frag's isolated cell step uses `bufferTape_nat`. This is supplied evidence for their stated targets, not a new seal or blanket coverage of other foreign definitions. |
| N8, screen/cumulative debt | Saved headers and parsed edge sets agree: 1,561→1,563 eligible declarations; 1,583→1,583 directed pairs; 492,990→494,011 characters. Exactly one edge disappears and one in-file near-match appears. I did not rerun the screen or independently reproduce its outputs byte for byte. Unchanged pairs do not acknowledge debt; cumulative scope needs the corrections below. |
| N9, remaining evidence | Six axiom outputs exactly cover the changed public proofs, standard axioms only. All 293 name/owner/kind/internal census rows agree. The blueprint's seven old-name references become zero. Current msg3 order matches all 329 successful log entries; artifact hashes match, zero static mismatches, 67 admissions. The original audit's 68 is historical: E-PAD removed one; SG-1 adds/removes none. No closure/compile was rerun. |

Supporting data: `crosschecks.json`, `additional-crosschecks.json`,
`composition-call-quotes.txt`, and [source-quotes.md](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/gates/106-sg1-dedup/review-incoming/2026-11-07-sg1-f6263c50/source-quotes.md).

## F1: mechanical repair option

Keep both private helper statements and callers. Convert `ha/he` into
`Segment tm {some anchor} (fun _ => True) c d a`, and `hb` into the analogous segment from
`d` to `tm.runFrom d b` of length `b`. Construct/read through `segment_iff`, compose by
`Segment.trans`, then read its strict cut. This uses no new public statement, import,
state/table change, or extra assumption; zero-length segments and forbidden endpoints retain
their current meaning. This is a source-level repair plan, not an elaborated proof.

Basic is available in the audited PR tree through the already approved SingleTape import:

- SAT → NP → Encoding → SingleTape → Contract/Basic.
- Hardness → TMSAT → Encoding → SingleTape → Contract/Basic.

Thus **recommended option: maintainer repairs F1 in this PR before gate 106 closes**, then
refreshes affected hashes, freeze, screen, probes/replay and the audit response. No debt
decision is needed for that routine reuse repair. If Seyoon instead retains it, the proposed
acknowledgment must cover the cut-only strict-guard concatenation kind, including inline
forms, with maintainer ownership and the next 12.2c window after MIG-1/before further
SAT/Hardness fills. Neither choice is made by this review.

## F2: five exact kinds and a separate dispatcher kind

The exact correspondences extend the seven-point minimum as follows. Each listed member has
the corresponding `clA5`/`CLA5` name in Hardness.

| Kind | SAT-side members | Per file |
| --- | --- | ---: |
| Uniform clean-module contract and bridges | `SatClean`, `satClean_install`, `_emit`, `_stop` | 4 |
| Shared-bank padding and its frame/run laws | `satPadAction`, `satPadCfg`, `satPadTM`, `satPad_apply`, `_run`, `_seam` | 6 |
| Positive-release stopping adapter and correctness | `satStopTM`, `satStopCfg`, `satStop_step`, `_clean` | 4 |
| Finite one-way word transducer and companions | `satMapTM`, `satMapWord`, `satMapCfg`, `satMap_run`, `_poly`, `sat_pt_head`, `sat_pt_tail` | 7 |
| Polynomial bridge-overhead bound | `sat_bridge_bound` | 1 |

These are **22 exact pairs / 44 source-inclusive members**, including helpers too small to
appear in the screen. They are outside SG-1, D-R2's Primitives/Catalog inventory, FH-1's
first-halt family, and PL-1/WT-1's fixed-word-test conversion. QF-1 schedules in-file
row/field-conversion factorings; it is not blanket cross-file adapter acceptance.

**The dispatcher is an additional kind, not a harmless Fin-arity difference.** Both files
construct `Unit ⊕ Σ i, (M i).State`, embed a finite module family into one shared `K` bank,
forward output via `emitAction`, and lift canonical seams/runs/clean contracts. The concrete
differences are module count six versus five, and the anchor's routing target two versus
three. After those explicit parameter substitutions, the complete code agrees for:

`HostState`, `HostEntry`, `HostRet`, `HostTM`, `Host_seam`, `Host_call`, `Host_clean`.

This gives **six non-abbreviation members per file plus one transparent state-type alias**.
Show the alias separately; transparency under rule 10 is not an automatic duplication-census
exemption. The concrete `HostNext` routing tables are client data and are excluded from this
generic-host correspondence. Full evidence and original line ranges are in
[host-source-quotes.md](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/gates/106-sg1-dedup/review-incoming/2026-11-07-sg1-f6263c50/host-source-quotes.md).

**Item 13/MIG-21 does not cover this dispatcher.** Its explicit scope in
`AroraBarakChapters3-4Plan.md:604–617` is the 17-declaration `clPlacement`/selector-certified
layout algebra: replace it with plain `Fin k ↪ Fin l` embeddings and delete selectors.
The dispatcher/clean-call family around SAT:3982–4203 and Hardness:6321–6528 has no
`clPlacement` dependency. Accepting the five adapter kinds must not silently accept this
sixth kind. It needs a separate Seyoon ruling or a broadened explicit ruling.

**Proposed retained-debt option, pending Seyoon:** scope each kind across TCSlib, including
its matching correctness/frame/run helpers; maintainer owns consolidation in the next
12.2c SAT/Hardness package after active MIG-1 and before further SAT/Hardness fills. Alternatively,
factor now through a separately approved shared public surface. A debt ruling is not approval
of new API names, homes, definitions, imports, or statements.

## Cumulative accounting and remaining candidates

Current wt-sg1 source snapshots retain these correspondences unchanged. SAT remains 270
declarations. Hardness is now 544, versus the dispatch's 545: NatBits removes `clCount_width`
and re-points retained `clElapsed_width`; its BL-1 copy debt is retired. Do not carry those
two old BL-1 members forward.

With the dispatcher alias included explicitly, the **known named union** is:

| Component | SAT | Hardness |
| --- | ---: | ---: |
| Five exact adapter kinds | 22 | 22 |
| Generic dispatcher, including its alias | 7 | 7 |
| Other named active correspondences | 5 | 3 |
| F1, if retained | 1 | 1 |
| Known total with F1 | **35/270** | **33/544** |
| Known total after F1 repair | **34/270** | **32/544** |

The other named SAT members are FH-1's `sat_first_halt`/`sat_call_first_halt`, PL-1's
`sat_pt_eq`, RO-1's `satRed_one`, and the separately recorded `sat_live_prefix` watch.
Hardness has `clA5_call_first_halt`, `clA5_pt_eq`, and `clA5_live_prefix`. The live-prefix
pair is already recorded at ledger:312 under item 11/T2; do not call it newly accepted F2.
This table counts recorded copied material regardless of whether its disposition is an
acknowledgment or watch; it does not manufacture a prior human acknowledgment.

These are **lower bounds, not an exhaustive cleared census**. All 86 supplied directed
SAT/Hardness candidates have family labels in `family-accounting.json`; their 37 SAT/41
Hardness endpoints are not debt counts. Wider RO-1 machine-step candidates, polynomial
field/closure readings and statement-specific run/congruence scaffolding still require their
own semantic dispositions. The identified new kinds do not establish a new one-fifth
crossing. Basic's `Segment.trans` is counted once as the F1 source if F1 remains, overlapping
the former SG-1 source member rather than adding a second Basic member. MIG-17's SafeSegment
siblings remain separate.

## Records action and validation limits

F3's proposed erratum is: **“SingleTape has six consumer declarations and twelve composition
calls; all twelve calls are re-pointed. The former seven counted matching source lines,
including the helper declaration.”** Preserve the original bundle/pack; add the erratum to
the response and correct canonical ledger accounting through the maintainer's records process.

Current replay evidence supports the old audited source scope; it cannot close new debt
decisions or certify future F1 edits. This review ran no Lean, replay, seal, copy-text screen,
cache operation, Git, push, or delivered script. Only this incoming folder was written;
canonical findings/resolutions/ledger/pack and sources remain untouched. Proposed ownership,
windows, scopes, counts and repairs here are review recommendations, not rulings.
