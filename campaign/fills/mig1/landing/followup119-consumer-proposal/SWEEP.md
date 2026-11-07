# Bounded current-MIG least-entry and absorption sweep

Source pin: `b1f553b315f31b949076e91119473ce4070e7d53`. All twelve current MIG-changed Lean files
were read and captured byte-identically (`sweep-inventory.json`, `sweep-inputs/`). Nested comments
and strings were masked before matching. Declaration context snapshots include the original
span through the next declaration, which can contain trailing documentation/namespace commands;
these are context captures, not an alternative strict declaration census.

The bounded patterns were `Nat.find`, `Nat.exists_eq_add_of_le`, `lt_trichotomy`, and co-occurrence
of `runFrom_add` with `runFrom_of_halt` in one declaration. Results: twelve actual `Nat.find`
declarations, zero `Nat.exists_eq_add_of_le`, one `lt_trichotomy`, and ten run-add/none-absorption
contexts. Two of the latter are included in the twelve least-entry sites. This is source-only
candidate enumeration plus statement/premise inspection, with no semantic completeness claim.

## All twelve least-entry sites

The definitive concrete bodies are in `generation2/inputs/*-after.lean.txt`; exact old contexts
are beside them and `generation2/all15-bodies.patch` contains the complete scoped diff. All
current private/public headers, caller sites and hypotheses remain unchanged.

| File and b1 line | Declaration | Canonical public API and literal mapping |
| --- | --- | --- |
| Loop:3620 | private `emCall_first_entry` | `exists_first_entry_of_fixed tm stop c d T hfix hd hT` is the exact complete header contract. Retain the old decidability binder. |
| Primitives:5882 | private `emitter_first_entry` | The same exact predicate call and retained old decidability binder. |
| Primitives:4468 | private `catalogFirstEntry` | Instantiate `stop := fun r => r = q`; turn `⟨r, hz, hr⟩` into `hfix z hz` after `subst r`, and turn an equality hit into `⟨q, hq, rfl⟩` for the returned cut. |
| Loop:3005 | private `emCall_eval_first` | Let `hspec := (computesInTime_iff M s out T).mp hM`; call `exists_first_halt M.tm (M.tm.initCfg s) hspec.1`. Complete equality transports both `hspec.1` and `hspec.2`; the returned live cut feeds the unchanged evaluator run/return proof. |
| Loop:3806 | private `emCall_right_endpoint` | Call `exists_first_halt M.tm (M.tm.initCfg x) hc`. Set `c := runFrom init t`; `heq.symm` gives the old `runFrom init T = c`, its state follows from `heq` and `hc`, and the returned cut feeds `emCall_right_run`. Retain the exact `T + |x| + 2` host endpoint and final completed-run absorption. |
| Primitives:1823 | private `lenStart` | Use `hspec := computesInTime_iff.mp hM`, then `exists_first_halt M.tm (M.tm.initCfg x) hspec.1`. Transport halt/output to local `c` with `heq`; pass its strict live cut to `capture_run`. The capture/rewind remainder and `T + |x| + 4` budget stay fixed. |
| Primitives:4893 | private `splitBody_count` | With the original arbitrary bank `c` and endpoint bank `d`, derive `hhalt : (M.tm.runFrom c T).state = none` using `hT`. Call `exists_first_halt M.tm c hhalt`; its `heq.trans hT` is exactly `runFrom c t = d`. Feed the strict cut to every `splitCount_run` prefix. No source-init assumption is added. |
| Wrappers:701 | private `timed_start` | Use the singleton computation's `hspec`, then `exists_first_halt D.tm (D.tm.initCfg x) hspec.1`; transport `none` and `[b]` with its complete equality. Pass liveness to `timed_capture`; retain the physical branch start, bank fields and `2*T+5` bound. |
| Composition:679 | private `condTM_start` | Unpack the original `⟨tD, hDc⟩`; apply `exists_first_halt` at `tD`, transport complete output `[b]`, feed the returned cut to `controlCfg_run`. The original arbitrary finite controller prefix, bank data and branch endpoint are retained. |
| Simulation:1199 | public `bufferedComp_start` | Apply `exists_first_halt M₁.tm (M₁.tm.initCfg x)` to the halt half of `h₁`'s spec at `t₁`; transport output `y`, pass liveness to `bufferedFirstCfg_run`, and retain the exact `t₁+|y|+2` startup bound and full second-phase fields. |
| Primitives:4675 | private `splitEmbed_cut` | `exists_first_entry_of_fixed tm stop c d T hfix hd hT` uses already literal header premises. The returned `he` replaces the fixed suffix calculation, and `hcut j (by omega) ⟨q, hz, hq⟩` replaces the local `Nat.find_min` inside the existing host agreement induction. The disjoint anchor/prefix proof remains. |
| Primitives:3439 | private `fwdMap_launch` | Set `stop r := ∃ q tag, r = .run q tag`. Convert a stop-state witness into the same-home `fwdMapEntered`. Existing `fwdMapSetup_stationary M z hentered 1`, rewritten with public `runFrom_succ_eq_step'`/`runFrom_zero`, supplies the all-configuration fixed-step premise. The existing setup endpoint supplies a `.run M.tm.q₀ true` live stop. Convert the returned cut back to `¬fwdMapEntered`, then retain `fwdMapSetup_run` for real/setup prefix agreement. The returned complete equality directly supplies the launch endpoint. |

Here the unqualified theorem names have owner `Turing.MultiTapeTM` in Finite. `Cfg.Halted` is
the published abbreviation used by the NONE theorem's earlier-time cut, hence it fits the
existing state-not-none guards without an extra shared API. The first three bodies were tested
in the frozen generic-header generation; the other nine are exact source-only production edits.
Neither native checking nor full opacity of those nine legacy remainders is claimed.

## Other eight run-add/none-absorption contexts

These matched contexts already call published run/absorption contracts. They do not choose a
least visit or reproduce a strict first-entry cut, so this pattern does not yield another
literal replacement by either first-entry theorem.

| File and b1 line | Declaration | Actual role of the shared calls |
| --- | --- | --- |
| TimeConstructible:522 | public `lengthBitsTM_spaceUsed` | Split a native generator run into live prefix and completed suffix, extending the proved head bound after a known halt. |
| Loop:2276 | private `segment_heads` | Induct over a supplied sequence of short segments. A segment may halt early or reach the next seam; public absorption fixes the terminal case, and run composition shifts to the remaining segments. |
| Loop:3507 | private `emCall_track_run` | Two native trace steps per source step. When the source is already halted, use `step_of_halt`/`runFrom_of_halt` to retain its min/max markers and complete tracked configuration. |
| Loop:3856 | private `emCall_prepared_eval_first` | Consume the already returned first halt from `emCall_eval_first`, then identify the completed evaluator source at its deadline using absorption. It does not select another least time. |
| Primitives:1110 | private `pairExtractTM_fst_run_budget` | Enlarge an already known exact halted extractor clock to the existing larger polynomial bound. |
| Primitives:3481 | private `fwdMap_reject` | Rule out a payload-state entry before rejection using same-home live setup stationarity and after rejection using NONE absorption. There is no successful stop witness to which a first-entry theorem can apply. |
| Primitives:3633 | public `pairMapSndTM_spaceUsed` | In the malformed branch, extend the finite setup head bound through a known halted rejection suffix; in the successful branch, compose with the virtual source run. |
| Simulation:398 | public `ComputesInTime.spaceUsed_le` | Prove an all-time visited-set inclusion in the finite deadline prefix: later source positions equal the halted endpoint. Then bound image cardinalities. It is the canonical published space consequence, with no local `Nat.find`. |

No different existing exact public contract replacing these complete arguments was established
by this bounded review. This does not claim they cannot admit further abstractions or grant any
debt exception. Existing named acknowledged family statuses remain unchanged.

## List-order match

Catalog:927, private `compareStop_unique`, performs `Nat.lt_trichotomy` on the positions of two
common-prefix comparison stops. `compareStop_spec` makes an earlier stop contradict the other
prefix or lets equal positions identify the result. This is the canonical list comparison-stop
uniqueness argument, not machine first entry. The machine theorems' fixed-step/live/None premises
are absent, so no mechanical repoint to them is justified by this match.
