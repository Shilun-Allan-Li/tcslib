# E3 continuation, Batch B — completed streaming reduction

The frozen target `Complexity.SAT_reducible_SAT3` is proved. `SAT.lean` is
admission-free; the predecessor's two membership proofs and all previously
banked declarations remain byte-for-byte unchanged. No statement was altered,
no new axiom was introduced, and no continuation frontier remains.

## Branch, base, and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Requested upstream branch: `complexity/arora-barak-ch1`.
- Sole working branch: `fill/ch2-e3cont-B`.
- Required, object-verified base: `f57cf9c1f0835a2336b93a61c6a6e4c9b1b266f0`.
- The upstream branch was inspected at `61cf595831e920854f4f047796478a8913ad90a1`;
  the work branch was then created at the brief's exact required base.
- Sole modified repository path: `TCSlib/Complexity/ClassNP/SAT.lean`.
- No push, PR, rebase, or changes to any other branch.

The requested path `briefs/ch2-e3cont-B.md` is absent from the upstream branch.
The committed continuation brief is `briefs/ch2-e3cont-batchB.md`, whose target,
working branch, required base, and delivery name match this task. That brief
and all its binding predecessors were read. Its referenced round-2 finding
file is also absent as a standalone file; its complete verbatim attachment in
`audits/emitter-infra-r3-bundle.md` was read, including the binding finding 5.
These path discrepancies were resolved from committed records; no contract
was changed.

## Construction and discharging lemmas

| Obligation | Realization |
| --- | --- |
| Canonical persistent state | `SatStreamState`, `satStreamWord`, `satStreamRead_word`: nested `pairEncode` of unary fresh cursor, consumed-prefix length, and a five-valued phase |
| Re-find the native position | `satStreamPos`, `satStreamPos_succ`, `satDrop_*`, `sat_pt_drop`: read the stored length and skip with native right-boundary clamping |
| Whole-string validation before emission | `satStreamCanonical_spec`, `satStreamStart_poly`: the predecessor's complete `satSyntax` test includes trailing data; an invalid input initializes formula control at its right boundary |
| Invalid and empty inputs | `satStreamRun_fallback`, `satStreamRun_correct`: the first invalid round emits `[false]`, then every remaining round is empty; `n=0` still has one round |
| Exact normalized round | `satStreamRound`, `satReq_round`: the word program implements every phase of the audited table on every canonically encoded state |
| Chain/formula output identity | `satStreamTail_chain` → `satStreamClause_split` → `satStreamRun_formula` → `satStreamRun_serialize` → `satStream_output_identity`, using the predecessor's `satChain`, `satSplitClause`, and `satTransformFrom` recurrences |
| Fixed fuel | `satStreamCount_le` and finished-state padding establish the exact `n+1`-round expression; `satReduction_poly` invokes `exists_emitLoopTM` with `R n = n` |
| Cursor and state-size bounds | `satStreamRound_bound`, `satStreamBound_size`: cursor at most `2n`; encoded state length at most `6n+8` |
| Input-length-bounded chunks | `satStreamRound_chunk_bound`: every chunk is at most `5n+11`, including the two fresh-index serializations |
| Native input in each temporary request | `satAppend_clean`: marker-free append to tape zero, then exact work-head and native-head rewinds |
| Clean finite modules | `satClean_install`, `satClean_emit`: instantiate both audited clean-call bridges; emit preserves its request, install replaces it; both have positive tape count |
| First positive exits and returns | `satStop_clean`, `sat_call_first_halt`, `satHost_call`, `sat_guard_add`: release flags support entry equal to exit; live prefixes stay outside the unique anchor |
| Blank scratch and no permanent marker | `satPad_seam`, `satHost_seam`, and the full endpoint equalities in `satReduction_poly`: only tape zero contains the encoded state at every anchor, all scratch is blank, all work heads zero, native head one |
| Original-input-only polynomial budget | `sat_request_budget`, `satReduction_poly`: packed word length at most `12n+18`, complete request at most `13n+18`; every source argument plus one is at most `32(n+1)` |
| Final language reduction | `satReduction_poly` supplies the actual finite emitter; the original all-string `satReduction_correct` closes `SAT_reducible_SAT3` |

The startup maximum computation reuses `satRed_start`, but its raw marked
configuration is never a loop seam. `satMaxTM` captures the maximum before
state 9's original emission, and the install bridge cleans all of its tracked
scratch before installing the packed initial word. The predecessor's raw
streaming states 9–34 are not used as the reduction's streaming proof.

## Exact chunk table

Here `j` is the current fresh cursor and `ser` is `CNF.serializeLit`.

| Phase and next item | Emitted chunk | Next phase/update |
| --- | --- | --- |
| Formula: `true` marker | `[true]` | First literal; consume one bit |
| Formula: `false` terminator | `[false]` | Finished; consume one bit |
| First literal | `ser(l)` | Second literal; consume that serialization |
| Second literal | `ser(l)` | Tail; consume that serialization |
| Clause-level `false` terminator | `[false]` | Formula; consume one bit |
| Tail literal with another literal following | `ser(j,true) ++ [false,true] ++ ser(j,false) ++ ser(l)` | Tail; increment `j`; consume `ser(l)` |
| Last tail literal | `ser(l)` | Tail; consume `ser(l)`, then the clause terminator on the next round |
| Finished | `[]` | Finished at positive round duration |
| Invalid input's initial right-boundary state | `[false]` | Finished |

All intermediate function outputs used in startup or state installation are
captured. Only the emit module forwards a round's chunk to physical output.
The loop engine handles accumulated output prefixes; each round contract
starts at the clean empty-output seam and ends at the prescribed
output-updated canonical seam.

## Polynomial ledger

Let the four cleaned modules have coefficients `aS,aP,aE,aI` and degrees
`dS,dP,dE,dI`, and let the binary-length fuel machine have coefficient `aF`.
The proof takes:

- `D = dS + dP + dE + dI + 1`;
- `A = aS + aP + aE + aI + aF + 200`;
- `T(n) = A * (32 * (n+1))^D`.

The appender uses at most `2|w|+3n+6` transitions. Every startup and positive
round, including request construction, emission, state install, scratch
cleanup, and all rewinds, fits `T(n)`. The audited loop gives
`c*(T(n)+1)*(n+2)`, bounded in the proof by
`2*c*(A*32^D+1)*(n+1)^(D+1)`. These are witness bounds, with no time-dependent
transition table and no unproved cost assumption.

## Verification and environment

Pinned Lean: `leanprover/lean4:v4.25.0`, commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
Pinned mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

`lake exe cache get` was attempted once. Its ProofWidgets cloud-release step
failed; the available pinned dependency cache supplied the required imports.
No `lake build` was run. A runtime executable-lookup shim was required in this
container; it affects tool invocation, not Lean source or kernel declarations.

The final sweep used `scripts/lean_check_tree.sh` in the committed
57-module order, starting with a new empty olean directory. Its complete log
is `final-sweep.log`. The axiom audit uses that freshly built tree, traverses
checked kernel declaration types and values (including opaque proof values),
and verifies the target, the two inherited memberships, and all 153 new
explicit private declarations. Generated auxiliary declarations are covered
transitively. See `AxiomAudit.lean` and `axiom-print.log`.

`statement-freeze.log` verifies the untouched predecessor prefix, exact target
statement/docstring, sole-path scope, and absence of admission tokens.
`patch-replay.log` and `bundle-verify.log` record artifact integrity checks.
`SHA256SUMS` covers every other archive member and excludes itself.

## Shared lemmas and escalations

None. All new helpers are private in the owned file. No shared statement,
previous proof, import, option header, or existing docstring was modified.
The existing large-file exception is retained and the exact final size is
recorded in the delivery metadata below.

## Delivery metadata and results

- Delivery commit: `b00d437311792cb6c07e1844dd5bb1cd1b8a0873`.
- Final source: **4850 lines; 256889 bytes**.
- Source SHA-256: `8aee157c95f63e36f2045d8e2d339e7e872137560462adcd65df207f1af0cf73`.
- Fresh sweep: **57/57 passed**, 246.5 seconds, zero error diagnostics.
- Target axiom print: `[propext, Classical.choice, Quot.sound]`; admission roots `[]`.
- Inherited `SAT_mem_NP` and `SAT3_mem_NP`: admission roots `[]`; standard triple only.
- All 153 new explicit private declarations: admission roots `[]`; permitted axioms only.
- The bundle is incremental, requires the exact base above, advertises only `refs/heads/fill/ch2-e3cont-B`, and passed `git bundle verify`.
- The format patch applied against the exact base in an isolated temporary index and reproduced the delivery commit’s exact source tree. No other branch was created or modified for this check.
- Repository working tree and real index are clean.
- The complete replacement source is `SAT.lean` at the archive root; restore it at the sole owned path, or apply the patch from the required base.
- The ZIP is flat; every member, including `SHA256SUMS`, is at the root.

Final sweep tail:

```text
BEGIN 54/57 TCSlib/Complexity/Uncomputability
PASS 54/57 TCSlib/Complexity/Uncomputability
BEGIN 55/57 TCSlib/Complexity/Formulas
PASS 55/57 TCSlib/Complexity/Formulas
BEGIN 56/57 TCSlib/Complexity/CookLevin
PASS 56/57 TCSlib/Complexity/CookLevin
BEGIN 57/57 TCSlib/Complexity/ClassNP
PASS 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS 57/57 elapsed_seconds=246.5
```

## New explicit private declarations

All names are in namespace `Complexity`; generated auxiliaries are checked transitively.

- `SatStreamState`
- `satStream_parseLit`
- `satStreamRound`
- `satStreamRun`
- `satStreamRun_add`
- `satStreamRun_finished`
- `satStreamTail`
- `satStreamClause`
- `satStreamTail_chain`
- `satStreamClause_split`
- `satStreamRound_false`
- `satStreamRound_marker`
- `satStreamRound_literal`
- `satStreamRun_tail`
- `satStreamRun_clause`
- `satStreamCount`
- `satStreamRun_formula`
- `satStreamCount_le`
- `satStreamRun_serialize`
- `satStreamRun_output`
- `satStreamWord`
- `satStreamFst`
- `satStreamSnd`
- `satStreamRead`
- `satStreamRead_word`
- `satStreamWord_length`
- `satStreamBound`
- `satStreamRound_bound`
- `satStreamBound_size`
- `satStreamRound_chunk_bound`
- `satStreamStart`
- `satStreamStart_bound`
- `satStreamRun_fallback`
- `satStreamRun_correct`
- `satStreamStep`
- `satStreamEmit`
- `satStreamInv`
- `satStreamInv_start`
- `satStreamInv_step`
- `satStreamStep_iterate`
- `satStream_output_identity`
- `satPairAction`
- `satPairTM`
- `satPairCfg`
- `satPairCfg_input`
- `satPairCfg_work`
- `satPairAction_apply`
- `satPair_rewind`
- `satPair_start`
- `satPair_replay`
- `satPair_copy`
- `satPair_computes`
- `sat_pt_pair_input`
- `sat_pt_mapSnd`
- `sat_pt_pair`
- `sat_pt_append`
- `satMapWord`
- `satMapTM`
- `satMapCfg`
- `satMap_run`
- `satMap_poly`
- `sat_pt_unaryLength`
- `sat_pt_tail`
- `sat_pt_head`
- `sat_pt_eq`
- `sat_run_agree`
- `satRed_start_guard`
- `satMaxTM`
- `satMax_start`
- `satMax_prefix`
- `satMax_finish`
- `satMax_computes`
- `satStreamCanonical`
- `satStreamCanonical_spec`
- `satStreamCanonical_poly`
- `sat_pt_numVars`
- `satStreamStart_poly`
- `satStreamPos`
- `satStreamPos_read`
- `satStreamPos_succ`
- `satDropAction`
- `satDropTM`
- `satDropCfg`
- `satDrop_move`
- `satDrop_write`
- `satDrop_double`
- `satDrop_parse`
- `satDrop_separator`
- `satDrop_rewind`
- `satDrop_skip`
- `satDrop_dispatch`
- `satDrop_copy`
- `satDrop_computes`
- `sat_pt_fields`
- `sat_pt_drop`
- `satToken_literal`
- `satToken_shape`
- `satToken_failure`
- `satReqFresh`
- `satReqUsed`
- `satReqPhase`
- `satReqRest`
- `satReqPol`
- `satReqLit`
- `satReqLink`
- `satReqPack`
- `satReqFragment`
- `satReqEmit`
- `satReqStep`
- `sat_take_one_true`
- `satReq_fields`
- `satReq_round`
- `satReq_fields_poly`
- `sat_pt_pack`
- `satReqLink_poly`
- `satReqFragment_poly`
- `satReqEmit_poly`
- `satReqStep_poly`
- `satAppendTM`
- `satAppendCfg`
- `satAppend_seek`
- `satAppend_copy`
- `satAppend_rewind`
- `sat_call_first_halt`
- `satAppend_clean`
- `satPadAction`
- `satPadTM`
- `satPadCfg`
- `satPad_apply`
- `satPad_run`
- `satPad_seam`
- `satStopTM`
- `satStopCfg`
- `satStop_step`
- `sat_live_prefix`
- `satStop_clean`
- `SatHostState`
- `satHostNext`
- `satHostEntry`
- `satHostRet`
- `satHostTM`
- `satHost_seam`
- `satHost_call`
- `sat_guard_add`
- `SatClean`
- `satClean_stop`
- `sat_bridge_bound`
- `satClean_install`
- `satClean_emit`
- `satPair_length`
- `sat_request_budget`
- `satHost_clean`
- `satReduction_poly`
