# B7 fill, continuation 2 (partial, target 8): integration record

Brief: `briefs/ch34-b7-cont2.md` (ancestor `8e9a9b7e`). Delivery:
`infra_local/fill-ch34-b7-cont2.zip`, agent commit `2edcc7d1` on base `4aafe9e4`. The agent's
report is `audits/b7-fill-agent-reports/fill-3-REPORT.md`. The earlier records are
`audits/b7-fill-integration.md` and `audits/b7-fill-integration-2.md`. The patch was applied at
the campaign tip `635afc66` as `55166461`. The four owned files are unchanged between the
agent's base and the tip.

## Result

**Target 8 proved; the running total is 8 of 12.** `implicitlyLogspaceComputable_dropIdx`
(N3) is proved and admission-free. This is a partial delivery under the continuation provision
(ground rule 9):
- no escalation and no obstruction in the frozen statements;
- no admitted helper;
- no target proved modulo an admission.

**The construction.** `dropARM mode : ARM 9 2 DropState` is one mode-parametrized table over
`![inputBitLang, inputLenLang]`, for both query languages. It runs in this order:
1. it counts the host length with the landed `inputLength_loop`;
2. it validates the outer pair with `alignedPair_loop` at stride 1;
3. it rejects an over-wide or non-canonical tail **before** decoding the query value;
4. it decodes the value boundedly;
5. it validates the nested pairs at strides 2 and 4, through the same `alignedPair_loop`;
6. it answers by a segmented lookup, using the landed `dropIdx_prefix_address` and
   `dropIdx_suffix_address`.

Registers stay within `4·|h| + 4` at every pre-halt step. The dropped and retained payloads
stay arbitrary words, as gate note 10 requires.

**New declarations:** 58.
- **Six flagged public exports in `InputAccess`** (`Complexity.LogProg`), each with a `## Main
  results` bullet:
  - `register_update_le`, `registerCopy_loop`, `registerScale_loop` (register arithmetic);
  - `canonicalTail_loop` (a canonical, width-checked tail scan, for **bounded** indices only);
  - `boundedDecode_loop` (the reverse binary decoder);
  - `indexedSeek_loop` (a bounded strided segment walk).

  Brief rule 3 permits genuinely shared exports in `InputAccess`.
- **52 privates:** one in `InputAccess` (`access_width_half`) and 51 in `QueryReshape`. Of the
  51, 44 are target 8's program and 7 prepare target 9 (`compLift(_mem)`, `compBank(_mem)`,
  `compLift_query`, `compQ_host_cap`, `compQ_query_overflow`).

**Status update (flagged):** target 8's "(phase P4.4b; spec, fill pending)" tag now reads
"(phase P4.4b; proved)".

## Verification (maintainer)

- **Integrity.** All 29 `SHA256SUMS` entries are OK. The zip carries an environment shim
  (`evidence/lean-self-path.c`, an `LD_PRELOAD` `readlink` redirect), a Python freeze checker
  and a shell sweep script. All three are excluded: none was compiled or run, and neither the
  patch nor any source references them.
- **Integration.** `git am -3` applied cleanly, keeping the agent's authorship. All four owned
  files match the delivered snapshots byte for byte.
- **Freeze** (`audits/logs/b7-fill-3-freeze.log`).
  - No statement changed, and nothing was removed or renamed.
  - `InputAccess`: 14 → 20 publics, exactly the six exports; 57 → 58 privates; no existing
    declaration changed.
  - `QueryReshape`: the only body change is target 8's (authorized); 6 → 57 privates; no
    existing private changed.
  - `Reductions` and `Mult` are byte-identical.
  - Imports are unchanged in all four files.
  - The only removed lines are target 8's status tag and its `sorry`. No `sorry`, `axiom` or
    unsafe token among the added lines.
- **Duplication** (`…-screen-after.txt`; base `b7-fill-2-screen-after.txt`, reproduced byte
  for byte at the tip).
  - The before and after screens are byte-identical to the agent's: 273 → 317 declarations,
    **67 → 72 pairs**, 17,169 → 19,550 characters.
  - The five new pairs are all in `QueryReshape`, at 51–89%: target 8's preparation lemmas
    (`drop_u_prepare`, `drop_z_prepare`, `drop_lookup_prepare`) and its two pair-scan
    dispatches (`drop_inner_run`, `drop_nested_run`).
  - **The highest, `drop_u_prepare` ← `drop_lookup_prepare` at 89%,** is about 310 characters
    of tactic idiom. It bounds the registers, invokes the shared `drop_copy_run`, and takes the
    dispatch step. `drop_u_prepare` uses that idiom twice, with different registers, around the
    shared `drop_decrement_run`.
  - An intermediate 91% pair was factored into `drop_decrement_run` before delivery. The
    report justifies each pair. No cross-file pair. **New copies: none.**
- **Lint** (`…-stylelint.log`): 0 FAIL, 3 WARN over `SpaceComplexity`, all size warnings:
  `InputAccess`, `QueryReshape`, and B2b's `Inclusions`, which was not on the agent's base.
- **Size:** `InputAccess.lean` 1,569 → 2,016 lines; `QueryReshape.lean` 297 → 1,208. Ground
  rule 8 sets no cap, and file size alone is not a driver (user, 2026-10-11).
- **Replay** (`…-replay.log`, user-run): the downstream closure of `InputAccess` and
  `QueryReshape`, 8 modules at `55166461`, into a tip-consistent snapshot. **0 errors.** The
  sorry warnings are exactly the remaining ones:
  - `QueryReshape` 1, `Reductions` 2, `Mult` 1 (targets 9–12);
  - `Path` 2 and `ImmermanSzelepcsenyi` 3, out of scope;
  - `InputAccess` and `PreimageHost` 0.
- **Axioms and admission walk** (`…-axioms.log`; probe
  `audits/evidence/b7/B7Fill3Axioms.lean.txt`).
  - 47 of the five files' 51 publics print within `[propext, Classical.choice, Quot.sound]`;
    that includes targets 1–8 and the six exports.
  - Exactly targets 9–12 print `sorryAx`, and the walk shows that each rests only on itself.
  - Censuses of every private constant find none that uses `sorryAx`: 365 in `InputAccess`,
    80 in `PreimageHost`, 487 in `QueryReshape`.
  - The agent's 18 prints agree.
- **Pre-ship probe** (`audits/evidence/b7/B7StatementsProbe.lean.txt`, rerun at this head):
  0 errors. Its output matches the continuation-2 pre-ship run, except that target 8 no longer
  prints `sorryAx`.

## Disposition

This partial goes in by PR. **The remaining work is split into two parallel batches** (user,
2026-10-11):
- **B7 continuation 3** (`briefs/ch34-b7-cont3.md`): targets 9–11 (`compQ`, then `comp` and
  `trans`), owning `QueryReshape` and `Reductions`;
- **the multiplication batch** (`briefs/ch34-b7-mult.md`): target 12, owning `Mult`.

Neither batch may edit `InputAccess`. A lemma that belongs in a shared file is written
privately and flagged, and the maintainer promotes it at integration (`workflow.md` §4). The
two batches share the order list `briefs/orders/ch34-b7-cont3.txt` (105 modules) and the base
sorry set `audits/logs/b7-cont3-base-sorries.txt` (21). The B7 fill gate runs when all twelve
targets close.
